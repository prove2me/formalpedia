-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:12:53.787417+00:00
-- url     : https://prove2.me/submissions/1f063d90-3edf-4b75-a249-29dfd12171ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942266187 ≤ n < 942446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942267437 1250 942266187 942266189
    0x1308090a030b060a0e19180c090f0e010e0a0b0403170708041208071709030927130c05010f12020d0c0e060f090d2a0303030b400e07050307050406 64
    0x111802c500f00400003000c5581c064802c1f00c00b0040c0002040070192038150034250b071030b03100184041c0c3e1140d140d0f0302e8408500c42d9a1107812b806000384200040080c0d03003661a1008040541021440c03000f0804150140e20349030031000e0900c0d9010700700c0ca0410f101600c0540100d0b070a0708c1d17510130390000b00c0240d442107840c20b102d5003594443e143e030781140b03007509000d49a0081c407a6185100c1040b010035255215000c402d110104c10040345043e15007100500fa403000081e2203018040140180940058900002d51060302c40038a000700345c0881002044071040c814402c00850b251000900086c203041d145c0080d00d20340c0540d00c510420440c2c1c581031100d2031003411418807204100780005419480c0145107550000d016900140211403c0c800c0c41d008041e106c84000e0f602540b0704410002c0580500175040b071040101c0744c00103200c1a0f1141c1a5690381c1c810811141c4c14580b024540f607001511007008010244000104100e0810580303660799107103d8022a0300c40c0c402c0b4000001c16107010b000381d078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942268687 1250 942267437 942267451
    0xe0705030a050901180f12051e070302010b1203090f0f012106050406080a050d030b060d05270a170414010804060902031207111005031308090a030b060a0e 68
    0x16185586102034240204406050340c01036540700c00640b1803800802802d03907174a90290f00700e80b0710801540350a80c5100c01001003007060290a0020707020b540714040791b02c101e403811004610780c6e402032803500300d00505001c2c00b210382c403110f44142e50307000030780c0003010301034198064440b410f5441c030f50001c00440480c1d03a40540e0009410840140522210408090070300344900c0d0080303109500c90000034182c030b07225001111943c0c010030801c020301c1002c100302e06004140381002c2110a031a4804243c03507200c0c148000130416294000302d1101101e6803843c900c85500c007400e0b6a04070a42401c440c0e01c0c2c0d48002c0c015900403100b001c8090004140c102203400311804448200d042040890040d00c114800410603202d140d541c00c0000d025803800e10607880070440d1610f1305540c8e000d00c0d141c405001c2e2000d0201c03502130414452150241a00501100e0b000740000c0c401c00c1c071030340052401d842c2d14481c12403000d070045880c13140001000000d14202c1e0003444111a841125912908041c40b0302e036081344c0c06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942269937 1250 942268687 942268697
    0x30f150c09081e0c0d021915020607051303022209081908090a0f080f040e06150c0a0318080304090c0311071e02040e0f0c0109140f06030c040e04110a0e07 68
    0x142d640d80c40c00f0b01c0b0241000e480582102c041007d4004401e03184012070744141c04580c400c800c08150b980d41802015803014a60810f02d003800380510707844030440c01500000303009280d83d2981c0c081a000501c0d07022400d6200810510802e6103d00e044107158201c80c190220516880722688a507034012150f0922a40c004001000d91080340d80728240c1c000340c645000c0c2c40713244042020b2049554103070014000307010002e55003d40c9090002c14009070300042c1046c603044140510955000c02004140b0074180d54141c074184171003015412068544480310380c0310640740c0c400010b001561342c03c0da400c0980e55003070341e4500704000c01151074120b0b054401e00c1c0c001820544502408160344144010404120340050700000d01c142e080c4020601d010501c24410380140d0001e800b4023090b40e80f01000901500e01c0c144041404051074000c00c40d01f5110019040c030a400201c00101448102c0003a00e004042d02ca1680b0003904007402c0c0050a00103da604500902c0742c918045030281608100500441035a964 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942271187 1250 942269937 942269953
    0x1308101b090e0f0604021b0105040215070308150f032b03050103020a0b03070e0a0e060f100e04020306040e070b04060e060307080109020307090f151215030f150c09081e 74
    0x43c4400701c401070607558882c0d07007400003d58107106203900c110400d40003000000c0381e042a0040012000c2402080c400c007000422500c8002980000030320340100b503420040c100303081c070440002c00303a4a43caa215509031094040c4110360403c8610240f03148500000d4500041d0026130b800c80540b0b0f0709000182d000141c0c054100005c001c000b0086038018601d1610518240d0010001103065006910001c4031109940c20710000d843d140c82158003080045501c40303020741c03031804064410f1148020142c400d5a002c40001c0c05034442e900640e4107030880c2c0003980c1986031106003c01c01504140a45000036080082150f01410b01c80d003103a00410098440c2c60440c0e2801e14010040d51005110108001c800d10b80003600341e594000c9840582041c80c6812080c1041903c000c001728014220134400506068032112074901880c01385090340e8010a0750b429030741d424200b083c95020f92103504200c640c54070800300c6640d5031201c10b802c10365020300c00380d4035111000e078148000c4c41d114100b0403809800544c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942272437 1250 942271187 942271201
    0xe0a1d0d05090d03030f050109020a0f0c030806040c020a060204031202070f05030613020420340f05030712091a0c07180e06040f030f0c080f1308101b090e 68
    0x10600741c25220b843c5c0414611403003061041503030001e07817100c10100d80124008001640081ca455040c299925020f42d845c8440c0d00c000b004243c000e4a058010340d5034400b0b40700400d2003400802c1755541c00480c20356a0b5540c0385005515980407408650040c002c17200c01040d424203c412280403503800400030300c0c55441c0c10003003990702c1c14105001c0780d000d6540c0180400141103025041c45404003000050307200e2070718040003800d1100401e000256502d07009a151301d00f01e04450510651340d0005003442320704c2d41b10f10b060380c518841e90a005d000d03100591040582142c0c0040032405032003486441c8442584442c0c4200b400b802010b040020f039411468043c00722581c000c1030800074a0080f0f801054542c50010418140b11068078180d591a0300d009c515400c1c5500040720044140b02817501401030b8056403105110380c080e214400c00d10b500006121280032480e5003104005e0305084e01600c40d82160950f400004201c0c10b81d007050700e0380405001603410790251503000c0c102c6040420600a66071011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942273687 1250 942272437 942272449
    0x509030f18010903060f061a090a030f240608100608060708090709020406080f060f010c12200a050d230f0403060204062003070807020d020a0e0a1d0d0509 68
    0x1010381d81000480d441c00000f02d41c4034000c000d0468076074480001d8650400416031011490062081001d900c204603103480c5440d140070144c12250001907100e05031082d072a25409400c854995107001c40041520124100c1036580316008a80340c241c01c170340c1c41c043d801980d0010b84078540f00b2105183c100000250350107005d169841e910078113003001d880000d0b4032180035904981180c0c01101c000b4900c58200f01080c0700010b5070b182c021204031904000380a000c80001c00000711020020101c240302d030640d01010b0b0044203442c030100201410340d10030250003040290344840c02d4400343d81d640f142010021860380183c001e40050b02c3d183e802000300300c08541030b10310280e10040800000e00c0c0100400004140c0c035102810141c01207640d010030f00e004070032500404100500070090207030030030000c09000803880403c031918568151141e0102003010b00000d0b50200065014078000d8441d42e0400082182d03d0f40800640c0b0278083c6031181c1e07240d1407141c15036106a24440c070380101c0c4041200050034500300d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942274937 1250 942273687 942273727
    0xf130203100c030e0610081f0e0703110438060705030a0c12050901021e0f010c05030601020d1701050d1e0606050f0f0a18021e0c010509030f 62
    0x50101e429080c0380076603030411680010031040c00a0b980f101d00078400ca10600103190010349a862030403c5500348103500f9161078944002c10303c8000c1c400e588240303007113040c0c2048600d51109415100f405a80713007013181180f6607a04000b41302d94601118104942c1c1466155160760381c1c0075060f43c4682d5040c1404804032251442c400d0303400341c014401c1c2000104100000c10300c00c2c505940c2c892144149140c0140401c111461503400d00900f0b205800b160f0b640000c0c0242c8403c4001c4014905076040403005003007040d2a51907245550808611011481c0c024005601580b400e9086448041e07054900305e604000c000a001c40c104000001045149485103410784000c1c003c10141e05041d1618540e40441820100c00721641500d4500800c9545428007500008420540e03a82c07040071075039800510703892018040d850508044440500c10340001c8d038191035080400107003132414140e8040e80c04005030000c2400c18003640c03e00c0b00160b8440b6000c000da440c5c502da4100503505100994050607505085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942276187 1250 942274937 942274939
    0x2070f021c02040f09020111030403080d0b15030406060f1d0f070203090907080703050109060506071202071802180105040503102d0507030507090b0d0e010b04110c01140f1302 77
    0x78008001d0150340c95100d030060300ca1110000042504440c0300260031000001c2c0540c04941081c00304002140d288411218000003210340014803520010019041d90b01c00c0815440c850382c00b004000130060345a00401c2596180c0001e054040c0d03550061702e200303401214032003c0000607503000c81c541c058442171081d04100d450054900f008442c4000c00e10034041103a0780000104950244030401f0340520400e409000301010511080f400e04011403070360301c40c03200010400385510705030b00071840c401e000c0b03000a064024101d00748680e0304019031000e90000c039400540c0b80d0707176400b07207501c1c41d030141e0125400c940f000b4001e0101c200c100380600c401044070202d28010102109078030000b10a4000c3c4c900300e04003400000290500305400f00804649004003d40144044000306001e03600030002039419102d01da04000c10004400c140306030140115403a8540c0045c14080049210302400000d00204010304008103d5054250181070074501e069500b0843c00c020000801c0b00c41038800c241485145c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942277437 1250 942276187 942276229
    0x60e09040f02040908180402031012050a0c09090302010e010b010c021201140a020d180201091509080609010b10030603020a03111215090c0609090705131212080a02070f02 75
    0x1400d600810b0540302c0d041c0d003c650340e22001500080a001481b0701c4d409000d001c1c0c5086045180c04580d00762201c016008003e10744911010340c008100d810000100d150f03a201091251495031441868060a1980d00c22000765081c10300ea5001c80c48144251504000165901012041a5000c0c0a00c0000300740c28070400d5500c41c10b0345600541c0302102103000304051381005036929074003184001103c0d079014001e10340d8402c0c100c0c0100580e074840d110340c058071103001c408a04030590000c00e0f501400d0341e5006981601801c030412110307600650100e4010380c7c0980c0c0c0c0300040c2c41140700441c1104e007140070003036002100c428140f022030001e032510100700c5000744c558000a080041500d291084c0b059034429090094020040c45030360a2100c408440780a5540b1403d20f00e201001449813035004085800700407022416406900c0a0800d090040900c0d83c01d01020110390300308109071202c03100200c0d02098800d008100d140090344211200740f60801c4038115404801d60803c1001c101c51022100105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942278687 1250 942277437 942277463
    0x10e010504030501090308070e06090904060e07080a0f170a08010b0d020f070c0f080d0e0603101e0303020c0d02030a0230100c0525051e0114060a060e0904 68
    0x100f0074400c0410700c0f4041d4403146214134007060014407100c6440701044c02070800740520700490710381c408078581050b40b128002c80c09008000c801c0e031a200043d4040780c4540700d07002601c000c0c03240d00380748102440d01604010403c0f42090f0400c034120310800c41040000349858004100e5003602c040039080980b1081c00c09441d0201d2038004880e0f94104c8081540d4559490a08020001006450600038190381000c0c2ca680c0500c41e4000c0c00700d0f040780114a00501c00040040c1501f52070403074000140003a00b40305090f403086041046140c2e03140e808120050300c1508584100e81c80e0001c0d000c40400e030b00500801c1410100c0e0f00340541d04544101003842d0707802400119401c04034030002460544003074001403003007a40c22502402036411000701c0c00709000041084a1a45200c40d02a07095482e500c0b610b030798031410a151039403901803055010986c0942101c9c0c1000034000641003018a40c1d91540d0012b10768603820104103840c0c3c914820743c004a03401145902e110308007005d0a0740d1180c0140154180a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942279937 1250 942278687 942278693
    0x80705070f150b0103060611030a1209050106060f0e03120f180307080c0f0a290c1903030c08190c0207120c0e0a110a110a0c170c0618010e01050403 65
    0xc4124110394107078543c168914203580c17500ca024000c09180c9800b2201004142d40251648601100b07881041010f80c1d0841003c000e83e0803007480203030301c000204942036490750028100c2405c40360f44400961000340007820340c0340025588420b154020f160358505a0700c10304440c01c90340300c46050b070300c0138070440c08044c41d6030b405012441c001c15502d4081c10500851100b0440c0800100041c144031f40b01c2d03450148000340c2e80321107050b60860318802180001c5100394442d0300a001d0712911030400e1007400c10042040b800d600190300c1c2103100381c50900c0400329007a025540c5000840f07032682c1c0e034203401440520340c410982006503612000d0041d55600340d01c9503462103d451600c4030070343c1c25020684003009445504141c665002c100c105040150f048180300b00f10103440b6201c4400100603026426284c14801070059032061a84426020061659003034014240309100c2047c00d105c1c001c03074108208a0500350200e079102030826880036004074001006407808028046080d040100c184004400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 942281187 1250 942279937 942279953
    0x50613030e33120103080c030c03160218040f0206250b09060c040609050405040c0902030a0b030c030c060409050709030c09320a0506010302130b07110907080705070f 73
    0x980c0e180750030a003203110654126a0352414a080045410788020021540da5030b0403c0c0e29107041da42c2c0302c92030599074030007094240d18500605070751850500000a0810681517000103032143d82d407003900c05003500301070381c00113800758902140d0141860103080d01840041c540b2000401c1ca040080480340c280c1c04220038109400d81e001d00040702d140d8884424030005550800a19074000a015202841d2905101e00140120303d03e1142900440c2c85101050401000c2d406050140202013030840d00d17460b048614101510310404c040c1e0181c020351901c101c450602060b010303190240600243e20745480d050142d401482d005000c901080421900800012020807041d00203041800c40030800328180b000201c40d003068200d142c80c0a000c2c110f00c002071602ca41d8061507100754a540c0000d2607a0b1110010780c0030b44905445880c01e98440c01020405107a1349001d448c6c042e000c1c2c8004282e41c2000300c1804543c0c00290b42c62004100f80301c00190780e5034031420052403d40d2081d5111188a40103642c0d13050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 942282437 1250 942281187 942281209
    0xc0203030c2406030f071a12090a03030c0504051e030a0b0403020706030c0513211b0905060409050a08030a090812070e0301061a0d020c060717090a050613030e 70
    0x1030b00303149140e200008041c0140c0c2c00b58100c401107000d003840c018070118580c0e0f0f6100a00c240503580f0f0104e200c21210000e51419100d142c1d0104030321140601d0070507401034032041042030403800303c1d1410403504010703403140040d00c0507508082d041380b250001c07203654200d6840c3d1020180381d0511030385103441c0000e40008100c5010b05d21075002030480324101480030701550801e48100003045000d00512410800c10b00c090000c607030368459541600755060440e07182c00210044080c0041d01740074000d106007242d8944940860349039800801c11600e804013080b0940d5141070020b4210381c041510840403504400007107400080c04400000d82d0f00082c0e0b540c0d4007540110344146810488041004483c0d5000b42c00c030981c0c080b084000308030940c01e014441c4408001004809003242011458600350701ca240d04075500e01102500300c421074501490010082c2c1859100c00c3d05446010b408251606e80015115050f1548000076045603a541104100130700c05d4410309900b08003001d03d207004640c44440a8270 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 942283687 1250 942282437 942282463
    0x40303030209090c030f0610020c0d03091701180206030603150a0203040c06030b030a170f0c010f0b0d170a0302160302070801180203150c040806010807050414070f0c0203030c 77
    0xd078840000d5410010f01440090102011044c100304008800d001a80b46a50141049403040e03030840550a0407441d200382040900c1c4c0000d10418070105050300040c0030000c0722680c51134110090403208a0394203a41d42c400f10700300a00e0507112000d0052810001860b40034501908440c450450380c42d80c0c1046580544d000401140d00005000502c03d10280340005002e160805010700d2424001007680d894102c80d024240d400000407000c1409610b4080f251039001d100555502c901188100b24004c0100458900b0100c9c50102e40038114103007246c01c4410160000201041d200d13001c2c6004030385500400001040550820001402e040c00c02d0024940754040d50081404c18149607100307003118001a080d500e6400410403031030041e5070002e40101400c204169003031458a17840b0466925000c0c1d034002c5405c0e40035020001c6081c0d600001c85104032001200e0a00603c18128502e01c0407041c1590220001051000c001d44aa8040c10803400220310150469180150410f0181c1c20a01049245 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 942284937 1250 942283687 942283691
    0x60406020a0206062704060b040c0504171204090e0a02040603080309120f0901030209030f012d0c05220b030109022a0c01080c04031b030213060b030105010e040b030304030303 77
    0x180211650411125a000700280c444100c2080100c03003101005440c0001c0e90b2506814400146c01c204850704441036500c070140040c041d00341080c2d80039290790060300500e05640f08114094480d51000200030b42e681e0303a27201940b4074086c06c2000720006485119031240c01442264050300050b1250300c9401c008501400d202134503810030070500f6081c00c007030500450050405210088030410320400f10b0703134011802d00700181d07208070040112341041011010f042240d480c117110103910748150340c8000d41c070309031601ca00d2101c074500340001011503c2c0810301900007401070041e50740001c40c510840c4034010200e0f10015429540b111001030940c0260440d0a405d90081036248101c4178400340709800b40c4e0810307402d20680d003080580c02e98030103261080604220603032000c1440002038034102c40c09184c104182d10b03c1c503000086201100d42d51840f08a004054010744840c11000511130f150546440034840351a691800d0011100d1507103080342c00d83d10607582c003071070001c0740d030100020300c019482a240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 942286187 1250 942284937 942284947
    0x14090405073201020c150d090204020309011b050c06010905070c12020d030c02010b150702011103042c13030f03060b0315030d0c2604050306070809011b05040510030e06040602 77
    0x24032102c0c0400a00707a40e0640d413014170840c50301e580700011483e500e0030302122503840c3c04e0f18400c404007800104001035045171001042c0050a00103400868900002541c09000c094192004468a01c940c9521400a03044180103120404058010a03040983d9240c80070b128140c0d40c94801c414000b070480348002da40011002c589140e0540039040c2118981d00003004084c40410200d4056120722043e40b000c00000913482045a000304010000e90084504885e2220b0b1108100419051003041205101d682c001045013003010008407240b041e012200000142c201c29030381500c0c4001000b5803282031644400c00440c0c500302030001b46202d0012001d600904010141c280b50808400742c145070200100340042d1004180f00e00710001050034012101d001c0c0884811194400380100d4000c1a4140548030034880c2ca01e40c080c2c00305004010207402000b4403c040000c034190081c032040340700040f82080c80104424600455210101c0ca02814082282d100c3c0c0180f00c0e050a00407142241c11030780c044bc0f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 942287437 1250 942286187 942286259
    0xe0103061d0328020c0a0b030a060305070f1412030d090201140703092d0e04020301090611070605061e150705010c1e180506070311061815011409040507 67
    0x10f40c0b0b480b10721040c0050803150b090400461001c003658066a0b405d01c1000011580c40c6805910001c021504402901c0c00c00f81c4407114600c10f0307015840341070220325000c0190202c0d450700040b0074401c883c1c00001540f0f803007105170203031001d4403a40c00240d040c4040e0081b404450f54034000200301d514440d5851440182c200103450a0100b0401040300c80c40300c5030410300000a5014107a00241e41c00101c10054541e11407001a026129908000f0803960404408a440c1100400a00307030591090380309001c41e9481c035052140024400d586001e807000c50b1a0140e00c1707400c3c0040f01603246038031400e440b80703403000c0ca8881500b502d0311041c01380b0005201010660095200d08800310614010349820302020135031510034075200c1203502070940304400000d019410140140504011a0011415030320a450070400075129400340c0551606c243c01200c6968050f915207003c0c5c28140c2d95004414030014480809109003014010801c4440740f0400310082008507007031400001c0500350701707200800b05441078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 942288687 1250 942287437 942287497
    0x4051023090a080115030b040c0b04090f240b18042d05010608011a0c0106060806011106102705190e01142d0103110405010b040e0103061d03 62
    0x261110f1166407500c40002414100c00102104403a0000b0790880e103621282802c44425032654071103401c140c030006002407106440e4102d18082c1d14002010411220089032907500e00c841c25440f5800c05900b154180004002c00c0085d190100300f2052807418103420102050403540100000307481b107040745400000e403242520303120951170360300d1409110b1940760650217071802006005803000380035601e00f004000080d40003503804110052009100701035440da0068190841a105540042d00c0000e0f2118003140000740140540704585510b441c16280090760390b40e00c040071025001c40b103001d042a030790840581c002c603800741d401c0c00040c4034015178809004084400203081d42d1444d904040b03001501c901844003880c1e120700389130301041003a103d41d41b54500040a070003035107411940032000441840b5001e51550008602610f0401c081d91301c545800300f1900075846214070b4800d01e40300520000340c95030490a030341c6030310400403002000300e910000e04680142008251401d001d404d80c0c000b04802e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 942289937 1250 942288687 942288689
    0x3121d1c0c05031c060b121627050a06021b0402090d050d03023f0709210506090105160309050a17070606090203061e0f18010e0702011104051023090a 66
    0x200403520341400c50081c01c0c4c2c40f5000034210500c0c1d4071100561710115011312440d81e162500710301c4202c034070003271380d00b9044a4825a015031405040011f1004c42c000d0700000d00189094400004840210101d10802c0040d500c950055500b0001c2c2d59000400076100300300940000d006511b001d61074200c0311407811110200700c0c4d003040002c80d00001c03d000304d604029440c818010141d02806c02c03070740c44000a80d11103070320780e2010701245400c0702100c090f12216502d00d00c0a52260b07060314503a44800700101c1c00d035441940c41417445803000340310100250083e840030806510540a4034806103582e00c52815004030042e21410540000885104104241c400c131000b6205414046007903080c28004980c28443c40251108001c0c4114948802e03070391211441000341100405040859080d2072240102c0d00080c4240c4085d402c0001c0401e032031500601514602002160040741440d241c8002c022010040d02414020712001103081500f1045980d101f90030f40203401980c0daa0b850711034041c00300a05036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 942291187 1250 942289937 942289949
    0xa0627060c03050a09150e1306030b060111010906020a0804021903110111030f030702011d07031a1e0103080a021b060702091e0403121d1c0c05031c06 66
    0x8612028010960007101c0d081c01c45070140750064450502c42815130701c0741c880f50080600161588000041d2540c006c40e54440541c06030344040215205010703403000e64059000c010b0810b841000000c500c1d5100d00038442c50650007600210f00800641c0300c0c4012a80003108001c001a4800e0410066062800000100d030348140e1300224014959100c1006050303404040c603040002101010b02000c0301082a41e1400c1030140303000d5608d04103032101030b00803c00407000b1617070044000800c1d8070b0b01d100032600304212038104280c402f80064000303139100240e5004080906007400700c644000001020382d00c07103000e14801c1401c1a81c2d0400014040d14085041d88203800b490700101042745540c54400c00d50308070700e078140c03002e8030183c64010a000c3d11a206020044454030b4110402c001d140e40b20304101c802d821020b8081140c0e27941c7d1410880d40003003003103800d0310b20343c0f10081112502d80c602c0b4900030061407c2c900300c3c1c0c1c120820303aa00c0341598010390480003004031590000c8040d440610a18006000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 942292437 1250 942291187 942291257
    0x7170a05100621020a0306030c1404141501030b120d0206040203161a0d02090d080405040b0d080316021f091a1605070507030f05030d0f1e09020303090a06 68
    0x2400401d001c4003c1c01e1074081e2100c0760041110801c003170003900150065588496031012407615408900054100c07103841900c924100306201d0545403151078080e00031042100300049038080c810054002d4803c1c003035040d0700304e4180340d071076a03130703030b0811b000c04008401e00798094461407c0c01c1c01094500090a210070040520709901004400303040c40050440807041030007191200030302180c4a00038012003040d0741c2c1004403d00c0c0c100420000c1e0004200761034045508200d00800c40c010711850480550004001c50401c05c041180240340b02c0d001c100c0c1c0c1045d4812240b0f800320094001d6441d280b034480b01c80540f03880d56015400c001c0640441d403080d824610040125240441d500011400381c10340d00301c148040000c021040c05400e03c02c2070091500000c0204510000e80313803265076a440511003040c81c42c0750151011851009004500313100e8091031031000c418a560802100803c42c2400481e4148020031644080d82c90700c00420004200c681c6407469403d24500c040c03816100c00c00c0707003106108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 942293687 1250 942292437 942292457
    0x20406051b010c1b0507091b030f090308061e060d02070c140306010303051b030a09140a0311040b1804030c03200706030c03090c03150c08060a0e07170a051006 70
    0x2943c01006841c44658031000c10069130042d0070500e08002d007581105001a04000380503044000c3c1c55120307041441548e03070800c074101c0d13022120000c486610720000c2c00100e004020820901d4000d00701401c50410808d49120101c0f141e0010b402c5500203c6800a00703038002c01c4001c1840590320400f80204080b1110034088051403000944850341404010203122001ca10301c9924045c042890303100304010310403a6078076520008054400455440b0710b80d084041070112400c80d0818140c108101c982c09005050510454010800034000e248655904050401d10300074040920845140c01a4025140c40c240000c25040080100401c201c0d40d10101c0e1580800c80700042001424030225a06450005020350000308101c0c050403a501018002140041011040c045002c124605419040a01300b00c40b000110f000d60750b1241c1195013a0740325414010420120140210380355200c83d1a00e40810103d5204a0b03982c81490705803403095000b40d440082010040b04429810058004d509114001d0307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 942294937 1250 942293687 942293711
    0x1209030e01030b030102030c0406052503080f1f060509131d0606010c031215080f0105091b03030f030403050403230723121e10050c071a0415020406051b01 68
    0xa403003540b040000300200000c14cc1580400c180c40410129070100014042c00424100288010011340b03a540b404911640800d40310740451015000c4801e200d645002c07000d20340103090302d8541080b800c880d04100c00040c0141c1030b05c0c040c8140c0d0420980e54081078031002c21042964030302440244154141300c0c0c0c800300880400d401800f0540110103040d404100104504070000400c0e0950b03015001d07511454081c07400102c07040d08554840e4601c001110542090722401c0c4868601d082d2040360107802c100446200c0180c2c00000b55840342c007030b040c05c0d4a07141d5a0f64504c00c0d0002d00000c078120601e500210003c15503401c0c00524010090f51595079442c0500d081004041d01114140c244201300380c0402902c442814060074414003400a0320070100c208415030262901c084030342d0503020601d040b0000b110f07102214203480d00a6002481710306180305000400d218200c0290065803901500b1518102d0a41d46000500281100c2d03070702e040c1c4658090f0401c840490f500b066002040c2d051074105100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 942296187 1250 942294937 942294961
    0xd0e0a12020d0c111f1d090c0a180e07050408060609040309170f12041d01080d1b050709140f010e0c0901050c0106060306080d0305090606101209030e01030b03010203 73
    0x82036400488808401030454000f450006000a45c030103c4954010b01c1200240c01110180c140e16030800399a013081a028100180f038502103840c1c1103480c00070301413904030b948544200004a00c2940c106d15900e83c0300e0340034103400da1303088400c1000248000790074056800c00303000306c0f600407a0696000300301d03040550b00500050049d0203548040c1e01d0800c06100034207410014a20310611309000d48111200007003d005903a44940158040c2d100c00440c07400980e4800300c0018100c4441c4009840b260201c0301d022910400220401441d40250618070350201700309100050041c512040f0004c0c80016240302103040c03800c0188001040307069003004202241c00c101c802540865a92503a030b6881240f0030040c2c032035005046241c1855032031f102c000f2454079090340c0710000b81d034440002c8820601101c001141603a400b00c0310038050790407000108240d4142294082420003850410500f1119003082d101c00312881c001c0141c0004030409603004103540c162040042d81c100980003949103103042c402c0402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 942297437 1250 942296187 942296207
    0xf0d12140415021903050a0606020c03030d0507021608030304030318150b061204050318100207060e060c03030f070f020d0c23030319050a091e0303020d0e0a12020d 72
    0x2c8240110400e4040c401226812210340b000c0101c480007100e65600401002010112016401280341c00b03004918180001056454100c0040080d480d0100e84229140500005054541035116030308000520680f500030103405441110010750301ca20741401d004080e5109c0041ca6008000750b01944408500f14079621100050089070220380b038500e03840891800c1c4901905c1400e40a8904140020400080024070005a00000d80540d0030036250800c240304c0ca0032641200581e100e03140c1042007500803890002c3c075040c0103001c44d00302659014240c0c2154401c4070030160304031909040120b07070b0b904000c00804540651004000f000601d900217804040340c0c0d000a00036818102404038925440d20f00c030702508403038230152612401c08000b6440041e00d14030440b0300c0241081e0015803103040511400005030b40140000881c0c80501d14004060b0741b003420242d04040d000c01c080c410080306801580c40c0c1013000c000400350902e00b400e28074148261060101d04541002c00d1441d5a1340e800b4480403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 942298687 1250 942297437 942297443
    0x16080622030509011103300603070b0711030a0b0901090627080309031306050a02071415030a110c15011203020d1202040f060509181b0a110f0d121404 66
    0x108526190017181445c45c09041c5190480b40d0798084044200382410301000391401042c6400d600a440d207404060720703143c45010f01c8100e0035042c00300c01c001c41d040c2d080c0c100c0440800b6042d104040616160700c000710ac02140c450000341e441d224800c040200d94820301031014502210200e0380030340003c2d810902104400041c0c801900400440c0d14079000740100d401c1c640240540c640031301d680f40c1c800b501c150028500c030b0780035009441c3d00185584400170001184c0c24000e20154004500f1480d0400e6500046c0001c880550f030743e41c102030b450a00070010101d9001c0328004254844d0709039102144680144c20900c0c03042c01e000e0b00000003a1300050306541000c3c44d41070590030989100308600080c01250300070311082042100002d030131500800106809441680e2000004401d0000b0b58808402501d0234240041c0302030240c0301c4010200082e140c0740f138441c540800c001c0300b21034115182451003580d62a07203030403661840d160141c120402c06200408100d003031200c2c510311f85040e107410600500c06 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 942299937 1250 942298687 942298697
    0x306080d030f061206060f0f0f1a090a0e0a2703030e0a12120b031b060a11011e05090609190602071203050105120102041a0702031608062203050901 65
    0x500c1242d005811075400303002e04d5000b11240d6151828494043d1410f0b20990007041034420700400c00300f0f80140008107989008501615140c9060303814183d000c0c4000400b001c1070414461030442d45e940010710001841024051801810000f90f00f03c00c4400303481315004040c0c200070036844004070f6507842c4c801c40c41c1c2501340020508496516070b41070035402c900041c01c20300e50402d100c010725003004041c00c61243e030090800801110405041d030300c490000030800014100052421a890441c0c0200842c690740e01d003c4a44844411481d82594501941003001e0031300032000052000032840f8040e400400c05000304140e0514013400b42e1962084044088070854204e101c5091045a40446013810703804010b00201443d411f8001f0000c040c203028061240113000710301303400b0003014000e0b01d050b122507088000502440c1c19625000b81d2200038200e815000b042004401100b61400460040c43e04034007620725440c092501080000c01c1c244150b034101030a100000102e58004203880750a0401c0c03c02c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 942301187 1250 942299937 942299951
    0x801030b060a05030d02060f06150d1a0d0302061b090a0e070e090411120106060e010c0f08030c03010603060815070309050c09090d03050c04050f011b080a05040e06010306080d03 78
    0x120b14060560b82006405104908001642507800100c00c0d104081240e01114192180000c01c40800101e4003004000c0c1c00500541030510170962044c1d03c00b4580081c06c071150151a804a207020021403815130240e0000f604000039040e0008401301d01d03900718112940382c4000100050752207445030140140f009548030010300d40900844880c1c80441006202044500d0a45844a048014210341c02d0050300c0d100b64030140402d0500170b600a40e88152542c45101c0d503000011240d00c0301b1007005640002c4442d51000114402000560040420320b5003240c0d03d6060420160942e142c560200340207621240d0310361202804000b4080c3c0050f01803030081024441c0b07040c0300f4070302295000c050794003141d040140520058000b44584102c8850717101440703695074040900e002c03400b680c881d00f0b8110421400b040c407958825001d00e000340c0c0443c2074200c0d0104179500c82000e070f82c04c040402c601181d03000074107102091084504a900c405c0c00d180034002039007010111511900d651000c40107260300c4100b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 942302437 1250 942301187 942301189
    0x406080411060f041d09030405040b0a120803090d0207060c02090415140601030b06070b1501120c210903020a0204020c0a02180a0506011d01120209041b020d0201020405010801030b06 80
    0x129000c030701a00102819107880203249606a1603000744500900000000c4c554150044032041703107072042941c64042d509140c542414003004d0301c003804031580d000e081d410f030100f03106954141d201001c50140da802e80d241d1906260441c0340c03040c502d644409540c0642002c00070242d10220041460344c0c1500e416216495500e803a200c22a80c1c10404c03498141080995040301d980d0b2004a8482d039800da0307080c41111246800e000c003a1181d480c0140114400500098111f054440810101d001c10724110312a02c980c010344404072211400808001040c81610041c211425240c181111003d01c00812000c40169006503403600c1d0010020b001d0fa4020540501e801802d0004103d401d4018002440c840545640446503803811100603801618040100f800707544204d4000304522100e1015184e0410180c005403232130b00f17100260b440d2082c0c0800504040d80c8642c0900c1e80b19480c24101101e002160600103800e0000050700c0c44116031060008229681e1300102d51030449030010803440f03560300d40e40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 942303687 1250 942302437 942302453
    0x3030d02210f072a030c0326220f1a0a0203010e1803131206050f0402030a03080a1503031e030213050d02030102041a070c050303041401030c0c1e1401020304020604060804 75
    0x344e900c03401c01071105484c1450382140809503041e10a5440e0040087d06075107180400d1804072000c500f0212440000d1201d0248040350541c0407200190400c007480d50765280300a6207040c1008941046e001c00306086d1010100003001d4010007241c10540c21503041000030501240300070042900300100b503140d00040d160901c103c1e0b10014584100e840340ba0346032070384110396509001702101e44a21f807100003a003585098040768003039503000b0060265180c81d82c500702e4810a0150140c1d1400d555182d603128a00040c00141000b90306c6500c6070700700d40701c80c01c944058002c000251a800c2c5801040b00103107030702e0700010480a90b00f040740c0305a980310706400403034028015600000528015a095503410381004da0107000700764030030310030b0714542907c3d002419181e000705d1040c1801e112500c000001e85601a4000d845100cc140c41d00120012682d201d40306044c501c01080040c0355040d039009414003041c046401030b2407c07420b009625600f0282c3c0490000d2255104910800580340b02042c204a000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 942304937 1250 942303687 942303737
    0x30f211b0c0801060801021c020903030f030a0b0301020d0e0f01060e01120f2a0f140409050c04051602160e272b081b0d060503030d02210f07 62
    0x80c1c0004c104080d2264803480c000d520842c141c9044400f061a102044e08840c0203d036184480030700030798204002108007100e03540024110000d00c0d82c5590b4002400e031030074405080f840e0200407020610040c0f08104504040a0181c111a9030b41842800e00c500b8010301500c41c11144408403070f41850a840c10704950042042000900303040c01c404030b140e401210b8510350743e01c00481101860000e682c0300711b20805460107200f10350084400750801c21075440d00d984001030803030051080c1c074410003091000801f11801110100c00581c7c40100d80240d480d810091040301c03103078681c1c206000c10b09080542e10440d00040505030004080b0b52600940345440f0400020310f0110320845002540407202c1c00d160346661480380c48000c9049030018611882804540d0040c0c0400c005030a901244882100050380410340300f01826885503000a00758504000800901b000e0300001070303d070160b90003154900710422801902d039403407940c00e003c0340041810030650000341a041501c0c11044000507840700c0404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 942306187 1250 942304937 942304949
    0x6070c03060c180e0109050a0b120d090b0c060105040905070e0c09040c0f0507020f06130b03060f010509010f030c1b060e060a05010b0f0304150204030f211b0c 70
    0x4810010400c00c4a0300004841030194445043e49200c076010280794060a200d5010000e8403080104801c0c00194051904000081342c003203604451000130910341241900c41e910503034895201141c4107035019842c00050080c88136917900e414401d03907074036507078200600a00f441070390b0b00e04188042001c01c002100082541e840703080040d18050300182c1e081c1e0082c0741014005c9041c126500c0d5041d11480c1800d1103150140c89650074600145c003405503c2220841c810f811030820030012801e00c0910ba442402030014104c41960303803400b0340034400183da00510b190b040c458140b2103005183c3c0c000d0a400003401c8180303000100900c15010403241c00124a40340390000400030820014410940c00950780c1c1d5003000115903454507502030741012198240b04000f451034040c802d180380400e11100441d0030602444481140c041401c0354070003240e001d580110341c0103020b0780e51201044000038102e018182981e84c200541b04c2c0b1064082c019000402d40183d920b03940600003410426950040c4c005085 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 942307437 1250 942306187 942306203
    0x3020126071205060904330f021b0109020d0213090b040624060912030e030601170f1204031e120306091401050303041a0d090506040606061b0209060607 67
    0x410703440c05000035010401214480e814140081c2941c00c00446181c002c0741d01c2580241c0c110301481d001a0505802100c6000500c0e0301d000d03076080004103004009030480c80d240700507a80ca03424044c2d00200d5038003104510969044c4040c04000d41d4a92814040813501a56080b901e4000e000880c4020001d5800007080c040881041c80140f125031780c810050156040d8042288143c17106a83c42e01e48014402d00740051a0b5000c10321100c101d000b0344500d0300d03200c0e00303154002114400000341424030980260920309540320740d0038598501004144403e01d1038501802c9820500e0311403952a228500025014032600302d684081d0528564071240e040350004040402895400c1004025044902c2841e00032810a50301c50042c4082c41405c07812980018001c500d45894060908080030b00c15039200c5d04d420040c4910784a040c002c5c081c148069104a02411041c03600e8600f010072524286c102e541001500415110b000180c0c894080e40e05c0c0d01264011400e0381c6407400207109102c1c100000700410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 942308687 1250 942307437 942307441
    0x412180b07060605040525030f0216050c040c0f09140d02040f15090b2b08131508010302100c05190515070309050a060506030a0c0e0711120403020126 66
    0x20406a01075004e5880454082c0f080340c40c0c0340c0f803c0100410b103800032140c403028030200ea01c14500076441000d41162511000d030070240d5031400c1940302c880d41f1000303a6035500980b20610035480c01e8482d40000001d0307410118140011118000e1081800f80904415003a05000ca80c6540e03582c80d480348042c6030300400074811400c0002c00d003809400010f44042c2104101c0c0d0010500320070b18020040102000b900c401e800c01c007103051034203540c001c480b40144e021404040c4400419501c40c01046c0340790480c1d020a90003860600301c407012a12428049041148840060005948082e014182c01c242c501d8450582c0f200b40c208039082220342d0421061855401420104102c80882c0d140c4100044454410255035110001e0f4155000c140f0010f0640d0002d4018800288003a80400d0304040c01130b0440b0403103e69507444101c04a0349400a0148440b450308020581d030b44075600149840014025004650300398911140c0c600031800001d0511000603400c00525201c0c290700450b08a20018011042c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 942309937 1250 942308687 942308693
    0x1206090507020a170901020a0b04080f040308180d0c0b0c2d06010b070f02090c0408010c03020c0c01020a05122808040506011707151704030806010e090412180b07 71
    0xb4845010100d4200c815511103c140d280c1134015201c1c035810680203090486072541c2e42141c4240000c000f1101a10148100004141044040c002440c403604401395190f081c05000c0c560a212261041c1c0310f061312003d40c2c000650046c2082c000c80d6613506c501600c48840e03000c03d5050044201d0400d100c2d0f02e520750410341c000d0420040a145000c035000755109640c03101c0d152410303442041405002c1d001c0c812854401402d16414590b400345401e50302c60b0400707446040c3c460130340328001d0b001e1000036000710302102d4002007030003100c0191100340002c2c1000003a96880a88542840f00540d002050115606400480340456080e00070107003040300000710343c08200508141e074207480907500703886030800100d00103401040b60900f501c03000004048140c50010a000701c1006608080200450007855041400240c0c3c030080c0124400d498404080c50101c000404040048448034440d1001100b0b00c80483c400c0600640901c400340340c420100c080960f04004a840c1c0da901400425000140035814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 942311187 1250 942309937 942309943
    0x6130206030601050c161806050607021017100e0f150909011e092607021903140c0405330d08030f0a0b010e10080403030b10080430120609050702 64
    0x1e4605007100308050740c1d805e006071030440d102409501d4002cae904004007005840c101d20144101412843d045164016004159488000c140d030a0054440031031401d000740c0c4c010040c401d9000480100c0041c1c646080240040604014004140610700720380104103030780c40a41205202c0e140041001b410500c0310400c2200130704600d0800e6501206440300c4a4440c2a0310400f0804000f0001c0349500380182c5408214801c45513404020690382242e40000003e5049140d4050090b00c64006d402142501e40c24401038440c001c0c01c0040c00d500d14141028610461840540080c41402440e5070800c250004158100c41110003d4420700e03002c0304009001100741540c41c824230400d0014003081c0800401036170b4080c1e002500d2944003c044040c04102449043e12513403080c02440c0104036501c0315004952904854a0328038001070401c800c01c0705100301e009034114907007401083e500f80f60680d01040c036025a40c103903898041002441c01801d06e500d407a04510094103050104000c0c5051007680a59 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 942312437 1250 942311187 942311189
    0x8070311101a090603010902010503011502161805060910290c030a0224010e060a2301030510050612040f12030902120607050d1808120402011106130206030601050c16 73
    0x4031030b1904100050300f908040c003036507c002d5810384841c0c0c2141d0034070034507131105c0301c0c580c1581c0118030840d880c40011083d25208030005285140c8005480710b00fa140d0706040e6075000780741a028160036014840c8441945c10310302c3c01c94916031403541d6110325908014000c0040c3c401a800881404a80f130b264445000c001804540d03400d0b0200e0381c5035622000364440314000d00e142d200b000d1004a0040082d0145442099405080105012003c545500a502d0028100070714504581a260001d4005581510865400a019400342000d4a01e4040051198410000070030010111540443c04202c0c060381c40806c1e0b90b5001240c0c1840368080c800060003065600c0c000c1e4880d041030811040d10302d80c04240140180e5080d41c4241c27800c07036206855400703030154494854102d103504600402140622020300701d07003060401c4050042c1054000100301035480c1da0000c041d07400c101c1c240b0808100740318505520540c1951444d0316a66403600581d814000d4003c08500c40c001c4281000c002001401c0841c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 942313687 1250 942312437 942312439
    0x70606080105101e0605070b06041d0102130807030f030327151b17060a09090602030603070503072111040e1c26100312030905011808070311101a 64
    0x540000c41200b13490407481074910030100860b50800414001c10b10082c4002d80c000340c041d00105400002d004140300c00340d0310b100c1d0034000d03940c0483d03082c09178880c003282200280080030040601906649a114010440200090038182e9543d04400300200d200c40b03091014103c148002c03140800b504000552070101d000c41ca02c6945004185041c4401a07144450703912081d50342c6426010f01c8200202c20514054070859102c0d0f608400000c410350700340251070000344620310140e26421721360306042c900032468100c20312030340004509100514242100c2d602040c1c1d000c20710003003082c05003081c64200c074850072182c0d005824890341e00c9404900162188001450400c10306801c04080d0044540e612181840c00046c0c0c070b00038515070701902d00c910305034204456280c0030f01410b507240d54200100c075290040c1c40209072240c4803241401400c0c840c1d02800d000d0008002c45441e49561405040e02c0746400c01024040119041820321208024a26102221140810440355008084404a0343c2c4000407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 942314937 1250 942313687 942313709
    0x51b160b040e0a090b040b0703060819060c02030405031002091f020a03120b0a0e04050f01150311010c0b010909050a0501060605040321020d050d2c1507050f07060608010510 76
    0x46903480390b05101300f03160250000b4210300d8075111a9541460003001034070b02003c06886c1c03200803d08140074048034588101d81c1c0c6000c200d0600514201050360801c031007940c295042804200081e80300440c0001d012415100016682c0c03405c500011000320035102d641c0e0b80c9410045800f08201c0e00010620301c464082c0c0c1ba15410242d00024040c03d0b05d81503108250400e82c0050b040240c1030b0102101c0c0c1d0498410340646000321445151a0f084498415010607001541402007041c4450004a84070b10310302882c1101c0c1c942d245440b030912505042c858261155600d0104409000080c000300c48410350150082c800d480d40c4000081290b0002d00090720403004d2400d44d08141805c0c04240d0002d00c05039005020080144142600c482c2c000680442202d80c803403c90398504036500921040880300705080410740301c900d401c040c0ca440c6107180041690020a428824029004410350700d0551828201c955110003c1c50405c0140c8003e5002c44581d41c01c00c01842003070703401c626148054a101540c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 942316187 1250 942314937 942314941
    0xe040b040b16090501030b03120d09030906020115030f0f051e1002040f21080c07090e2103100308032d0f060418081902010f060501051b160b040e 64
    0x640680c2c0c000b44103201c00314076118400c000d107500070307003000316854801001e030b907411440300c0c4588056a20070031a0b500355556428540b0105074001118074080c28051000700022400102114a20340503404007821a070920780603002000090108c500200b035005060390952116800214110744100c0083302040c000c5e41d4511556000510a036003c803494810a004407629202880203100c1a018000300300c4141a046003020450b24001040a0b2104200610209261044e03850480e0110030104500307800842d41011604d608103015154201601c001e640c4c0d039101e00d511850b80888075403005002d80e0001c810001c08403425401c43e062040455081081a2640700c001c2c58004012901c4a4002420710045000e5003403940c000d00a61082e0f8100f05079000071038581c03019540158141e0a94984400e00003480c5c2582030150f081d80000407001440640d0520b4000f0300903004180300001d115081d03e020307a00c8900100248038080741c0891844c02503030b8858030440f00c968014091a40f4000100300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 942317437 1250 942316187 942316201
    0xf050a1b1203090b0a02031e1207030b130b120f1b03070303020d0309030210020c0d090806130b060a1a0403031413140d0c120b0606120705070c0e040b040b 68
    0x1454072081075050b501d00302418148252911310b600704648400461100b444480b0349410b1401040c4010740001203410344941100e0200c10300041c00620410405007040c0c0d0039003c0e501c0301500005146d031020404074451500c4404641c15100b02d009c03003560391040d0200304150100106480c10800344080c5002640a00601495030702c80300e5110040050384000801e030a018480d5000d8400e1522074415150480912a001000c0e604880003120742034011805900800e504050b03164000c10141c000380c0460b1500c008000e90044488101421000031840041e01555403000b2000242011170244038580b00a2603107158260041d00048020540d010b50385115118050b080c1d65034041090000d090041c204605200c10419a402440d08801204903e038001170201e800c5001804500c886610500e5403414148407910300a402c41c0e004440c10410115081406110141e21510304c1c1403c45d502c1070b103807a00d0b41ca40480d690113401a1b040280500c4200080408090700031402000c0714441a1240b038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 942318687 1250 942317437 942317459
    0x15060f1e07020a15020c1f12090b0705180603010308190e0d121e030c03060504060509071112030f07031a09061009080a110a0f060c0f0f050a1b 63
    0x21006503010000c0c2c00100000d42c180d88106600c08150720586da150200440455400021064000d2901170880207040110780d124510381c1341948880401d022802e80c584941d900c11401800140c00c10030001348c62080c2d9452010b02c12481c50740940841c4e560341c0d4900b0010780c42d42222080d9242c00101201102255100d03203840d4902c0c48004060300c0b40490981c1e1410315a408001340c070001d000001340c00081c14840d4010700d504207811600c0204210316510401402c03510681c005502c243d1038440240718540f0394110042d408145420b060700701c0e030f0008103998506400c0c1104203514000c0001002080b00410010798060546500d00344800c1c0032088011660f130134041030781c130f420050240018120f0315180901d03d9200300c031824010f028607220300140e41021140d030429911040f01d03840d60b200604007008000028114200c407030749081d06111000707041d41400e420192036100011206030600c0320150f1800449a0702c1001c40381d201042d80b4201110510041034082e041703038484800120304070b0364 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 942319937 1250 942318687 942318697
    0x90e06060a1404020d0b040507021524130e030409150e07020319050912030304150522030302042303010615020d180f17190c0302060315060f1e 63
    0x1202c0d40074440d8640081c80025046440c03a80d01d02610340d0100540c035110b52040a0040500340d0203031180134500305065040b0710b000303070880303c40c652030f1020807480340795018804800c20012540207510700d0328100380c0009840c1d4100c0108030340c00000b40c0080c01d949503034022190b040900c40c80040710340c1e551401c6c01032140100c4140015800030001c1c40280318065070382c4121504903080841c1081c0101001c038410b4002488941d060b50300000c180030501440c404a84039410969006105030b203440c00c03865041c04200c2c0d020340b03148040a121901014040d8040d6405000600c2045540c101c01d0340011000c5204100140c0c043e504c1c08001240c54200808078a5405420703800508005202c110200d0b040041c841232401c0c804105440450701d034001401c1d0301c0c01403e001c1c041c15549551040180e04101d100c807100405604030900040015002c9081e090440b601252034a860381d03500e010003c103045001c0d0701e1945c031250020701181100d00d03000180ca21100c00311414046500c41c819003500c2445a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 942321187 1250 942319937 942319949
    0x120f070503092107170c1c090e2806140607021005130e0a0c1d010e15090a08010207140607020a140f070f0f1a040b03102705280b0109030c090e06060a 66
    0x907048d014004104003585403608040b0031444050703c4210f400c11420070803040c00544040e13544808040203810303e0851050385440b0111030031441e00111351f0008400440007499a418410003042040ca901404124a0002c202304640c0060500d40707040850b0040c00f050512501090400c14035040c071501c641c60803100c0343d80607100e016001c4404810020000c0e05d00404000c0d00108104021040d207518000742c000304002000036840d00b50078503055403901c0c0c03000665101d950140c13040100840e40001c0401310300b0382040c1841c1d00a00a0500b840c04d040502003d50704511499034005200701c24080103204031280448160305058460500089240517204e440030a05018042400310300d0000e8010340d00f0404010a0b0078103180d88941d540d0b100c0c0040b0000011802180428940b07025550090b69446000e16240402c20504c13a4001c582803d0384140e00001d00c0c0e5100740100ca1a40600007000165400624207882166600100c101030f10303007800040c0031801103401003182e6003070820004083d100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 942322437 1250 942321187 942321197
    0x5030403110111150c09060403020418060608030c1009060912120c03021e130302220c0c03052a0f030408010b0301050105030307060509030d02120f070503092107170c1c 74
    0x88800303105c810340d000940d0b030303585c0450304001c00001a036940c45004241e404190300b203100700c80c40d824448101d54942d8080602504100f00102c41d074600450000c5030402010000030350401a030800740024090404000c10b2848078041c01c0306082c2c1c11203d81a0300800b6a1ba091041040c0d01c08100c041c0d0142003215840c40000a10750659841c02c103019295010107911042c0c0b02d1990b0781c0000d80242148005034480b0207803c2000c1c048401c080c05000080d54181c1011801035400c0c1e13400528030300c541c4010b000c0e0b15449031600045403144111149019400100b1181d60410004075607071268400d03c903400856182c040c2090803801d06010b828121180140a076042a006490792400340c20002c0c01440d0301d000c2044000641d096038406040c41c0301400308100e50a29194812070707450b42016121000303005040c030401c1440b840028040c9004901a91520915800246455220f010b908030041c6064007010b40c245c1c5010f110005082c202c02c0d40390881d030426680040095100280c49000c00020f070f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 942323687 1250 942322437 942322441
    0x606030d02070e19060e180c0127150e030c120a0201080a02040e070e031005011a0904020d09050a0b13031409030a051506190b04030b060d0503040311011115 69
    0x102e8009003095200c401d82c58844c41e8001c03481000c030300701e8100c1e03040039807001561000e120000440b01c3d000d044041e00c90b00180320707201e01c0d04006048181941c090f034010040301c40c0d00303c1c00c10541c035000382700404843c0e05000800e40c04a40c080d1800c2142c4402900038402c1c4298070100c0d2a0810110300100c800b80d01400d5403d509400444074400020101e40c98240c0822002a010404010591148006a803400790960151003094248565a480718034207504000060014a4400012000c001000001c3c00c0d60b5010714008500a80035000703001d4001460310901405001c80461429021071103004502055550518644840b5081c0407010340025101c001b50800400c040005110a4400800311303000704856a13580c2c0d240c00c017514007111550070007005106241c00c0c101d240665900703944051550382e03400c240c041826030103103200113043c015a113008200d29880d5480200702641d0030100b500e5650303450703080022071002800c0e120b50001e061401040748002000c0b07000a4a1064610005926 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 942324937 1250 942323687 942323699
    0xc02150705250b0a0e190804090e1501151b0b06040c0c0f0f0204110d0c0906090b0904020f040e0a020309070e0f060d0809060703080f0912160606090207140606030d0207 74
    0x1005e043c2c05080e0944114103200e0b42c40700c1c44c80c0003074468071b00c0b85070b801b507845040c10090300580360050030789807d45c0e020303500700107210080e28241410351719410300700001c107039248030221100d01006030031700c8400501c01c50020078000002451840307004192410b2044007641d410864400b001071802030242c160b424500e00009840c02c2c01c4600740d50000380003103109001c54010320b14a81c0544c51506c400c550700c3c104003011580001450000b4031a90900c0074240e440c0010051a40c8102022644030b10380c006001e08030041400b0603200034100041c9000c1c598901444960000c0d4800c0da42010380744030b1340d50001500d40004404901c6814080e1552a140c5c4660301800300d001020081143e829609010318001d91f05c900c0090540b140c000c0d9a10549403d006e428402c601c44058200841ca400c16020311560a400004444040d00c501041200d0502181441c0c40102042e80200e030035240001f94900500442d1900181403151704002d4544c5500c40000b0590354001c06130312003000d40c00100307042041e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 942326187 1250 942324937 942324941
    0x152d1032030a02090720011a0d060f180515040c0e0a11030c1209121b0a2103050a050108070b09060c071502070f0e0a0c02150705250b0a 60
    0x30821001e0100e50408606a0010f416924100d50050000310421076009155080d8000c0c0726250655000030440c0b43e0026240c0b4607070060100206018410203500d4108009140e8000b80c6030550502d4100510000c0404034001710401190980e190301c0741100c021f058070382c60034015008903408440c08070703403500e48012408185002454000b03019514580940002101001141f00d21104c2a60568448401010f199042c0c80a40540c50350b41c0f00084064150b22240101d0b050b5505402c10040c80c03400c01508241303400340315107004262581c61540060391222039000c028039038001c0d89080c1f0103030f505c0002034802c48000344200d207041c0c1d00c2900f04000035083c1c00020003818102031701040c036003800184c101c2d181410903481800068201031001480c59410b01c04034000cad022035036010f101e940c94144001c525031800307070140c0081c0e075441c410070441600802c220081550b000203092410f10306048054010f070004d0b088900320300c0c003008041903580c81c3c070815080c40b079a020350081010f459003284000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 942327437 1250 942326187 942326279
    0x6090918030f11070608091002030c0304030c05071a1b06040f030e04091703060405090d0906140d150f0602010905030d05060607020d050604110a08152d10 68
    0x42c8083c010400c842c046007801a50f0203040030391100c07101400d080001d5440d0840131009850503900c1482840405c0304040b0480340c210b03400d441c08100e010032500304542003091a50100e600745041c9000d001c400259100034202d40c1092040e030030055801200d1441d21500125801070001c1c1030f6030b00303036000280205c02e0740d07180b1000504001010300e21a524214900c4118482484010000c420040f003031a00c1c4c094240e2101015020b0b268025400c5000340c1004101d003c0d000900c40e030043ca00800030003107001d0721350100402c401400988030030103400300e12260030b01900ca0000100f55021074400d005010310700b030301a401b200551074840d00c0103c1e4030003020054406d60740450704010305800f5030b072101c01b50f141c071034015009000a070426103040c4070320940c409103442c0a501c84040c01c00203810089286000205003401140056071140e0301628800002c49803030150b0669000e005405440c45000284603164036150500780030740f140303507078488151180c040c1e241c054940580051402000e1030304003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 942328687 1250 942327437 942327467
    0x504060513151d01091113091707020d0b040807120f050d1802032506180306020c0a020405070905011704081c06180c03150f1401050702040e070609091803 68
    0x800d9894683c9150035203140d402c040d11040c2400c03081d40d40e146000c0803100c990340c08980080000c126640c1e500e040f52499819800640080412480255260383d0034007840f0691040d1241e980d46001d140107032141d004840207440f10b03021040c4120b0030702c0c060140101003107501c1d26a80c0c00c20310320070454409002c0d442c48584c8440c00e90b003110030050f1810401c4900c00d00c9019180d41c640458902603000c0424030b81c1c032903010420324440c9103048140000c0030702c06881e0465009a80d50f03035140e14851500300b240b60000d40047c070300000c100c1200d0740480803000f56035007645d44100d214860301410b4941c10b01030302c010380b01c1c9404100e140900c1c00c45a251902c456085140442c405554603803d40110a1201c620715606403030340b800001580e814458183d11900384450b202d80b550812640e2040403695000300c4031105200100d01e505c0303a0081c0165140700354014014032500a081d080315840326200e10550f000700b02c140e000864151030728020f201c00c5400d20380300758501d030355103440454000070501414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 942329937 1250 942328687 942328721
    0x1031406132307080c040302010c0209071701030803070e03060f0a1806110901030c18052202040b04060807050403030c080306060f1909050312040b0903010e0303070201050406051315 80
    0x156028100c440b450942916110381c5404452030203400c081e00c0f1800051101c05403003001c01c800d01c0141c1e086966500581d4056401c51101e980ea6070b02501c070300c09492886202c0541c000c0000080089140041d0f00c120040c1e43c428100c0602c9800749662503206854503c0040c031004001542280241c0c44a45401d401e9200d51440d00050b4035000206d8a8840503c030103900001007001441d40c041c019200034501c0c1d45001c03001001d54400701c0c100300e000c82c054a8030556448007403101514200b02400e124840c1503900319a81c035650343d14210b2944c42441800040b51340d42c800921510302072402d80d81201d405071200400103050f41da43d01320660004099640c0501300384920340d40348000b600580311108010700150024200c200f03025201c21540d40c0202c0c480c4e4040d01d01c1105c043c090388151811100b00da070680d038072210241d00081c0582010300c04444540700101c200180e0300e0341500080e00450050008201d2515981c110120921007240050040c1d243c02a2142c0c082040d6405541d001f0074034040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 942331187 1250 942329937 942329951
    0x20d0803070509011815031109120a1223070305070609030e190f0b0c030712020a030e03010902061b0a1b080609070501020c1003060806071d0103140613 67
    0x2841119410a981c0400041ea0110b04088156006002500b0604140300a18071301c5240800c03200c04a005c440c4402e04040c0c42e484a030010080c1c03407007500e004500041101c1090921030141c650345d50500d90342920b84415174039810107814041c551011606050314841207a0300c00d0901d0003002503000050480c20040c00b089400042195031207010307013035817090b0790302d850a00160b410442821000c502c210010f01d40703007004004031a01d0603082f1007120281d0800ca92103002c40c3c28a03a00754020320710040d28180314003a1000241d0307408101c0440345d1f0310a031541c0c0c61200b030380740501d0300701d814214000303401000c100210f07250101520780d0000310300340d500b04a4106c0c4401d0b90300d820400170242050fa0004d074070000c003448610810700140c2d500a4112000b0010740f490940000d681da030990603414007906049252001d000d10070b0b008000507201d00c02c01c03107010f0b05142e2001020040b80f030000003480b11140283e05d215600c00d02484802007440d529803802601c0703e204001d6903182410780e82c0565691100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 942332437 1250 942331187 942331193
    0x303060f06023301170105090c100c0507051008100b070b0a1a0a0807050f0102030309070e04080c030307020a0c080a02031b0301091707021c0c0e040804120f03020730020d 75
    0x311502a060b009640c070402c00c00d51790014255000506401e4040d001f110014030507441d80070300502c40801c0c500d004002881d0a00f446c50500348580c2019802a91515000007640e800541c038174010360500c5c00442d20170307583c1e4000d00424050010020102c0c2101c0000c1071044005400400c06180264410100740c158180000e242c0c45817944403030960303040310310300304a81e10b0049184280da9600380040d44c65450710380b0310b030341d00d601e40d81c01030501000c0c40304081400e1100a00070b907200240381200b16941c83c01c203044069075646020208413900c00d060302e00400d00010101d2104121940640104124110f240e034024403000856034450701b43d96034407050008101d4a40408210b81100c54590387c0d11446401841f030b030398a01000700310300b03208074146810000725840012421078080074a803d09030703103e6103091400f5124691021100400030313040e00c8284141684030f014242c0c40781d000c456895a07a00e04022150920701c119612030070a0324000c0b48084000720900d00e425100070440f054442d059030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 942333687 1250 942332437 942332533
    0x1062625080a0b01050906030f0403140403060516030e06180f0111070b0c0313170717090406140310110903030f03040c1202090c070c03080d090303060f0602 69
    0x200e9580001040356003409481481e522442041810130b203882442c0107181400f1400c14070016007654201e000c40300003d02498030400b68040d0f204480081c0390341d920750ba814860003400060f101d071031290300039804e004100e90080c400c540010300740c44040c0c03600344d40d030360358420110070b0180b4411050f018425400c8001c5d04288604014050040c02440d160895800d10520406005003000214403081003072144103103940c041000341a90000c4a1007640b84d105c0060011805480401020310000781041c49003211341c18040e060070f001c255820006c080d640c42a000401070000d100c60381580203442c13261901d0f50160040304040e4200340d101460705d814500401d02d56030000e0b00e902c0c1610000702c00d01003041100c0031b046005000c1900c13213003030001060b000100412030140034102c08520024458003044022403c040c000d5400005007500c1341035a2605030081c1840d01c070100d0009107051804038a0030a8402103406660b1507a004010000203101c540e54840c804680d400c0a8051080350341a007101c0c41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 942334937 1250 942333687 942333751
    0x60f0c020f0114132103170a020d060306021209010902210a1202010606110f0c060c16060201051e090c15120718140f1c0602070614010626 61
    0xc0302010310660b117055401c244000107480031840c0703403a81c030b050071003c03960210070000e0380070181c01003402d1034440190b41c8000340b058401c1e0b02c498a061a20000078010b10f503000d001d0046408840f103129079502c6500c2802c071401148000d61040403503c030215401e2051041041000c445401c07a401d006103a220f9004000d000c46200380142c0d100c8006201469201c2160440c3c0d5034158020000c405038001034545408140741818080d5601103400f981c1840c00b048050601031603820301d1452140c440000034040d20040301c7e07600804061002c0d500c000740823003506e20b04c903401220140038801c0758041040765030080b5507480e4081e0001806841110320084d901c182c0140407070b41b82c1c0c040841c459403540300020160307030040c44581c62410407525162100084003070848400ca07441c05c01480308068444668400300701c064007045c40421000100200d0741c0c040441e000c0700340031070b200320380c0d0f14401110200b5984e1811040d81441307520640c00b01444605003900050300f2410360940c80001100c0c0c905810403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 942336187 1250 942334937 942334957
    0x31605071a19051b070e100f0b1e09040203070207030b0114030304030f140619060905060319080c1002040518160c030924030b0423040c0e0f10060f0c020f0114 70
    0x14500788000b140318611000000c009103640240c04614004a08414ac025401d02c951008025441c10180c0f4007883c04440342c40d10300034800c6407a4101032000941c0c0c4c2130103006c100e8078a840140040744902480c0740b036001007000107004615190560741c030ba8110911030781086507a82a001a0a000c107401030080b64440c00c804450b028076601e41900100a0f200340e1b234031007402540f400c024070210340c40115082c00e5080360a1580c40c0401c140345490003161141c030708500346901403031214400800d469001001161402c9030030300c20840307241c500c1a030311090a0394010074894881c000001d080d4014a20391400c00d001c1c0c1803080c042503840211080884001c103007040100e90024070192a5601440b81d026004c10554007080610840601d030100403014000000e100681e140020b0104800040c0d81c04c00f604080002c40c0550510b1202c4100300030050301c004603111800d80c40032410030f100d2100d180808880350356071204a030244e02030080038042001c0e220b042005902c826061056010300a044000d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 942337437 1250 942336187 942336209
    0x906010f0f210f03021f05250c1209290324060d0e011428060909050d082d1302221107080d0c02031605071a19051b07 52
    0x1260320401b00312190340c45440701402d00d44002d00c4070018601e07540c02800c0c0040800703000d1103025a001074034100340c211002030201071151640c03c2255441440e101c11252100d40c20300e160f42c04844150459041c1081800c1160810b100141a161603032514044144030012411030a42100307000c00c0e03503030780007801c141985500c1d020031081429003481100c200c4444007201141900304031962404030300d0465a0741c00c104003400041d03004d0a01e03652084000744110031301040409140d2070496203500c141400c140c0400d0324440001d0715846810784117115400c25aa00c54000e410a4800000452018090074910218500c8070001a1510188000102000b0b5032102d030203161050385105444540c0010b11180b031052004000103107400042e10030303910030440c0110342140e40301003c914501981a03c01c0100c4d404410f400c06004000c2490410f80c2d45081d000c0041d0440c0343c42c11340180c03140000800e940c009a1020403031451203003019164081c0d80034103010105039811040b500c0e146490b000451080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 942338687 1250 942337437 942337453
    0x190c1508011a07030f1101230601080705040e13080c010f200703120207050c0a060909110406021005060f12010e0d030b01080406050606070b040302060906010f0f210f0302 75
    0x1000c018500c40b0720a800c0c40e6041c1c41c0001568004081d0481010941c0502c41201000b1981400a4100c110017240c44c1c40d00c0049a4446d16980c40c0445c425280180810544004140b85520590440b4103840c0359001144017a15503201007511442d103600d0584580c20309001c02c40e040c51003030241d495008000040802c20400701c1c214514080c28264010b810124204100c5d0006071308007000b1007000c05407076801600c40e40107080060501000d40302895000300d2807040422003641049520090701c80c0e078a410880401280b54203140d0344154050341c070159010304080b032000019030f0480c59000001400c501044849400400e10842c0619080b03030881c1d4403140f02184a010030804801c5e000c00c40e113401d10110710080300103001d00d20042e0020f00596240c1d400248251140300413259405c1d030022218566207028100252180c40548884040b03008940000130100c2c000380d00a01600d42c2000c0120a2515240071140400301c50980d804035080710a024038007240301d081c805902280680c0207070040d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 942339937 1250 942338687 942338699
    0x1060b0c1e010506130f09050f1005010f050d230d050a11010204050d02120c030a0f0308060f2817030703020d030533090412090611190c150801 63
    0x900400c00698400d40c0c03503e400c119040c0d5502c110050b06080000303001554003801c210480217007420071400351141c4121a1032034014040000c8160151181c000c04100d03598a982e0022402240c620515a00c151a02c6648000c0340c400f82e0545104180c07100c201200e82c0c0855991414401c40c0e4841c01c0c00300703102042460549070001d00b80b01045020310b008525080c1002c0c0000c09001a40d10080d004449441c2264007104042102c0034030342100800b140c40b07036030051405c01015507054000301c0018207004081080c9051414040140301802882d1015083d200c06000c0020f02d150801310307a031804d140c0d0001989203e0002076803034085811010b960740f14603d040103072924406a100c20200f600d001e00304101520794051468046440c2d80354440c0380985011100070300300c00c4048030740c1e101c107600e01030204000c41e01400714000240f548170340c252940d80d41f0041d6000c544890001c50300e0b40040151102c0001c0a01305564000e204640080c000750b114039078128541d45181d001c9000c01c074007000620113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 942341187 1250 942339937 942339973
    0x906050117010c0e060d0e0f100207020f040506030d0e0f19081207050705091e1501140c0604020d050f0708010e07050406081908251104090b010b0a0201060b0c 70
    0x344200744c10556503034908100440c610748282d2441c0c01902e139403203110407074002c018402e03250314900c2441110780f84419540480000c1d444040103d10880c0c8805144005040c1400307407d12801000b00170300460b0308440000d4821168030b084555122030300800580050350784044c2040724444410140d841d56040c80d03e540c0ca04540000d2001d54002c080c0301560001d0000240d1806807201a100c0c00300549440b450b8144140705220400c0e111400041008a00240030041c040002801d0ba03980403a50068440401e440c07046d807080300d91541040f40010058104118213221461054040740d010b84041803855081403040c1d041044a07035168080c0186400c17040041d0710103040708480c01c00c445403400320000e44c0d0f44e851103401420600c252510b28140709594003907900500010280665102a2800001003910350100c00c44828841c00411290745c01c1c103120302d8007c50b500c203100c0443c5034244240e087d0650801c039207140856481d44400b180a60281000c0c026801c502001880200301c0500e01d441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 942342437 1250 942341187 942341201
    0x2406040b0411030112030909050a0e120901050414030309210d0e011e0c1b0302032107080c0f030a09050918060105190302030d170a15050f0301090605011701 69
    0x712507420a095410342e200c44008a81c1101c1540754144c0101c2c0796854144d40403402c0c3d030f10044c14146000d00b00301030380342c6e69045400c45046800688080c0b105400e6001034138010031442038006642800b0134455007907a0314069400c028014201d030304001400002500c4203246112250200213074000b81c8005035002c001c00000521141403842d09821311100003400e5096915030b40d07410904111072054401d009040f1150403d401000a2020700820b0100401c0b131801c521040b80a0711494400c0816964010100000c0389550290315281858540360307006150800314003412140259281200f82440820040010641c01d13211650030038a040100101c9510007405101c1400c4442410260b00070045080c6042d00d0003100e1602e280000e89015401540650304025010721909201d00d0341e054222080300c071140b0540c004000a030342c0e1070411006482d845201d2004083c00340c0401d000300c2c0b030480d00c42c81d1164405000060628500d40b5407005940c2c080e80032030340840081c0c0c0d10700062442801649 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 942343687 1250 942342437 942342439
    0x21093412050d030e1515100f1d130c090e09060601080703090203070302011b1a0919050a02040f02090d03120506040614060d15140f040615112406040b 66
    0x46040c10308025200d1100300104551200420300141c4002003440030b003038041c1e401400047c0450400040a03091041d100c0c551000305001072801e911110510b01c0e00001010003800c01041c070303840504080c01900201440c03c041c003102100114165403030b0440e6600c51010784c0e004100d18180100090008003024016100305400c1c2000c00d80540c0740040d2050031680c3c203191100d0026000229034491001c00c01c8000c00c401c029203202c02c5400204c0c40540c0c0940041c0d010342e9181450b01c48083c1ca40003515000402c03640065046034090300d440d034880054004a940007510b012201c00009104440c0c541080f1b0105142c001800c01383c00031840344c281d01941c00c1c1d408024080c20a100ca12054050079101842030000055024a542054008081c0380400c412004241903c500e00120565400380b100c1d8000d00e5004031004441c80c150140500300d0b80d8104c001c0008900c40d80080b5070150310301d042e41541d4810005c07555058154184220500c004501a440c0b050426403300415510640e0301c82d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 942344937 1250 942343687 942343691
    0x307051e0d0b0a0303050711060415020616020c030a0602090d0c080114071404030605060d05010e1b0105070b070305150a0b1c06050f0d03020c0d0821093412050d03 72
    0x600000740c002003140c205680004808c08005107100002e0080e1180d90031451082901d00658444150001880e50161f404020034060b104010304040780e840311480d0050758154000294072000c61080e500a14120101900022505106403140b002c42e015a502070300542c1c0d511501480c952583c1c0c280c207604a00d0610382045402e00c100c4c4111480e01480c040541651382c1c90000c01c0306662500000041c0075032200090004e000c0280c00c6603103e28a0b4a040312100b2460702907040d1070b40c0700b40110b40754241d00080300d44030b039207815000718000c00c401002c40c040003200b012404000e0342e8a640e120001c0c044c0d80941da64a00581d04020f4520304402c1c1c103107000c2810032100384415903440808030813070300c0142c400b020421500c2c2412803038000c1402109030001c0d000e0440406101c00032005080c002e2408030030710142a810702c03510074220400c0740c11660503040704481603030038000a450311420002003d00096401c0031880342840e051000d5101c1440da002d480b0030082084000c0c0003a60740c1200604007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 942346187 1250 942344937 942344939
    0x510060203180406030c080a0507080316030305060d02180601120b0d1101051306120c080f06090601020115090518060f010303030f06121a090d140307051e0d0b0a 71
    0xa5500d004080025042e20040d900e04201900d481c2d000c40020343e0480b0501125903641e44055450380c1094006480500460a022402d20350000480350700000f607200504186c0501d44044008100c058000c561081c1c1d5684400050b0b915841c243e0304104a10441505504155002501aa40c2038050f01032090400d21522004d070b540202d01d41c069074003e402c0001c1c1142100c0125414407895130002d14070b480340c19000ca0880c0c0d00c00380010900c0b103400e8080003605864481501d03246002c0b10200c00303a4440400003042800c105d20340507000032040c0004123503090505040130043c1035a40280b4502e5660391b04101940c03401000348004c1c1c0c0c050401902c504c0c1031100200c2c0240d10140009401d1549480b5032001c1c52103540c0c0404010043c2c0c0007140d0352038940d842d220320240080d04003140c903990701d034021a0588801160700c1524541c107403180404600810002030094200600c04014403009000c0c010078445840d44051803070010351050307951038210440c0780b021540360f05070741405040c000c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 942347437 1250 942346187 942346199
    0x405060a0513030c150207050d050903150f0a0c030b12060f0a09150905030d060305010f0f0c05250203070803120702030a1d12011a030c040b180406060b03190510 71
    0x201003c00540000171103217190030b000f040798041d100301000204039114201d4102c0b22907900034058404110110141c58030300316042c0007400c42c4001914041c0006400300041401c0240e0b40d0301140400901d801d012644190540000324640f480f19010800c54000c142001180014901c0e0703158041000e0100300203c1e4425220005400702e0b00942da60381c2c0380d0780c544150a00c441001030b1603280b92000f109020854403031410301e000e03240480314001194180462208a42d50380e000341200850507644a5003071400400c110b0500b540e45c10900c480f031103c0310800102507201400f1400143c0401401180e40e0b101e0b405d13224403071120050031a0f04541040c0300c0e601000d40c0c0b10070350341d03441d0101c0c0c20044c0000b03031030100046110100206558103507203071201303001114100c0c643c0849404412015a041c0482901c28401500e4850000d0b03503115000c0d18501d410a0707080740b030a64100c1c1c015100054406d489034100c0116074029a08021111004250034001078441e000b0a5480940035030415601441e2072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 942348687 1250 942347437 942347447
    0x9041208040c03050105071707030902031207021305010905070807090311012f390d0f060c0c020a09090302061b0d06090b0a06050f070b0a0b06030405060a051303 71
    0x2a581104201a000106080c0045611500007441e003200081001e8200800c0107002c1c5282000302c91680b08114000408560003446071510f11500034002d000c903c022950702905680c001074041340e00c00b0b0000701c01ca20b000310600c1910302800c0842d500248a003080d180240031100000d00000803c458900c090000828503588943e851400f03003804190310142c44a95101c103d180c4982c81300304045001c800031095000a119503a0002800361860084901050101a01134510803c08690141c004030400c5040440c4c241503824007560701056a0030241d6910300c1a60300720410140005c0c02040403074198070705812524024541c100c010460500aa81c1c00380d1140002000301888c0d440c009a0000121000b400b150807840010b6030402c00562917440041c024041e500e10113008604440e40403c12602640840d4403d40c0301c99182404e00f12650f6030551400801424014a41d0302c1e03c085032011748494000e140518803540203040d85103010301d1080c045500051580710075200038404000425088 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 942349937 1250 942348687 942348713
    0x6040f0f0b0a2903061c030f0e100203030c0d09050604030906090b03060d1106040504090c1805010f090e19030309061b0f030b2e02120301061b1716060b0904 69
    0xd0103e16880c1d075901400900101034103903807061903031210100c000805a1098106002d1052910703145142200401440340742c4a0300d0703a8000160b4001c002280e201c40d4014050b026528001402043c400c0c2c0d503a4030039040c20415201100401d10840043c4245c5400c00c104030701a10545092a0540c6407030700c00680074400050001c0c00040c1001d40308016030310340c4030488010f810083c0040c090074085103442c00480b50184188400144070084604031078450307000f01d60403602810b210509103420300c0141c800411041981d03009074460920040e1110255010102e6003030f0290724001041d15590500034103803482003d00d02c3c900214040209042c0f904496400300340c6119140000e090700d00039010070320b482c0e174424414044403004441c3c3c0c480c00b0313024003100101c00c54940c03d030751f84410030980000d00c0b0301003802014003051416a409002c803c14000d12104c0a00503010a0321000c0140c400204a520510414900c03810348103900702480050301540c01d110f10240e81046003490a034646030781c68216 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 942351187 1250 942349937 942350009
    0x71703330d060b0418021908061906031a07020c0306070f0516050303010b1902070303020c04050a15032105070f080a11060903030106030b1c030806040f0f0b0a 70
    0x31401d050824040e40354090080700c1c4001c0c10070010082c46401c000c00709a40b004080b48201c0c54900d443c040c44105c03901040454003800002e180a480e9080c180e1940d202203115099015920900000420441d0910301f50329001c4a11005490610400007401c00e01c840c0061800381d4010300c2800300d22a03000154001d840e03c5860225102c01d0740c070041c0315441c072600c07401409038480440007250103180c02004100b508035810846400716542c081c01d07600c0382150b100160158020403090580750800d50445a0701602e0110006000c003103c2c0003a0745520f41c130f0780040d95001082105501481e61a6460b0640086103040590400090b41c0d69807100c480e08040040c41d07103001180050413240074500b1036000c124130405645c0145441c80c00b01c1e5680c1c10910401d800a403e00d4191a200e0030310000344020344250b41c9079440b00c1c080645003a10008009803200342c000d6941c9418103502d910502ca07014440d5034a500105007880d2080030400d100a498006030300b01c00d11010ba44d450119246404145640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 942352437 1250 942351187 942351199
    0xe120a0c060302090d0501060312030b0a060806010503060a12120f0207052103040e1e13020f0111192a0501050d05040812040809100810030b040807170333 68
    0x4d94101140c1c004600240017002c42d0b080503004002c0008040b001d0514072030641e020056410100100600e202c6140700310300c04a80c800300814034552040d4015030307004002605030100543c1c2d408440e40d6507105480180c0d1303103001800f0517249590748480c80313236207143c894802459400e04100006521400f900301004031140a0707804030440c0350042c4260703001800241c68840031841c1c89a0a8071038a200b809241741040702540c0001c24154844000903803039900a00440700350549100151581c1401c0f030f45011031803060a04102e47d809180e40f110340083c0c0700d88980c40f0460300d594500c400700140c2d174207610781c82100c0450900440c2d9101042d03d4411b09c10f10f1300410b0076190350a14070302900c654462074400c00700e00001c11062104030b10042c98030010a40f00707100c84c2c03c9034010442d107042040c0c1c1c01000c0d01c805054100080b070030940341180c009002d455032a207801420b90344c1e180c04540750380d5548640d410110800c94110340b205003240281080b500003800c503401f51030301003155000d12158940304103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 942353687 1250 942352437 942352447
    0x121506021509210a030e01050c09040b130c120515010813060209060d06030209130201051b070801050403081e010510120209030a0615050117041101050f0a0e120a0c060302 75
    0x60400042e01562080d8020403215080f100c2070303802590100b002840420f040207101ca4100205118161051b5800000c0d54188004502040064401613020355402900c0903103914a01c0768038032801ca802a0b064540d01008481d41005a058400040c00c41d045000d2640000c40a030b6000005a544220300d1005155035005074030703200c00203020390b030990b07600000b0214401b07020010700d50141c82601d0007254004403a607601604030034900c00941e402800103000b40481d00c070081441d08030b2110099450203545505d5200c002560844008503815800a01080b05104015140903103c013074090798001e0030002503050501190711841c5c003401c203004004180e420600400319aa0549040040090039185023051505243c802b40c044540034440102c452280001c5541c0203001000c82d0040f248001441980e980d03d071403241600860009040c050708101c0341682d4942e6400800e42c0755106d80f00c044000e00d001080c880500002251540c0a80c0540d2819003c950045080400c0310b046180141e070f56 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 942354937 1250 942353687 942353701
    0xa020d0203160b030703060803031611070803031504182a0e180f010b2d15070b060603040807060b0f062b0204061d0d080a1215060215 59
    0x1807900d000700440020b071920b012440341c0031200214000c040f01d40c5d040c001d00c2d46940e1f45548a00c01a0380b00114001c131258910400c238065016000204c000b182600d00710341d070700c4c2d05050465104842c0100440f0300c403600b44016140c1307845010003d100c40d01c6030401401003540c3d041481082c070020410010403541000f5204610304044d50058054001c40760460705001d0904d00c00c40c2c00c2002c20040d41c0c002c40410703c1c42c10005224040004200404e000340007204054114480040d0103050706407807810551402e03441d02c13581c10001810443c1c0305071036038810b11414080310060303025248910482c810414000400d0080003079407800340e0080c40c006500c04104c0300241d410481c2c80030103a0000f0002c0303070407022150130440c4110f8920702c4032120040d03644038460740003c0f88164050f010110f0302e103541003440c8540482c41d0308401900900003158903000c5d51190a115003082d040740340040d91100ea11040c0c081c050003090445002490141c0c1e00e0b40c100b030000b944030502460220040b4040d08001094 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 942356187 1250 942354937 942354943
    0xf03270215040609060c050a0f0609061b0903080c030c120a080c03010b0301050906300f0d090e09030d021801120b090106050d1b031b02060c040509040f0213060f170a020d0203 77
    0x20f182d40034034482711055845c03801c030000d090b4820b4103540940c6032650032012020501e0640602000c1c1c0d6032148034803070175913407094226001040340945610091203643c220300c0d41000b20000c000b200340801038580c215004002c14000d80244210031034241030004001703512401050381c0c1034400c12540840c1560b01e0a005c50004400c20381c14500c21046105c1020719003c048030528482c145440030740f201800340d84d00745652a482200c0000008410000810000398001c00440d00316044070250703442e00308515154000c1ea0400d1150030007440509502104542e0030a02070342980b16516002d201c2c1d070801074006280c4c50014840d800910070001030803c1030413444d41c402403100340c00e0640700320540a0348400800034176000002046400c01c12030100c14040c00060705903c03899020304421701d80703400c0006003d1030b13843c041c000b00c8811005104510040e83c03000380c1c00c46c8071600c030322000809034501030154161101b0782d0701038480c034210010380c0d040c106004a0355400440e01030b5422030500c4150f10200386 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 942357437 1250 942356187 942356203
    0x9020d020715061505070b06010e1203070c0f05091009021602040f06060905030f0d0f090b221401021002090f0d060f05180a030f03270215040609060c05 67
    0x4036940c0b080d08000145611a80820107950344070001181c48103000034140c0740d80c0b01e0b00902030500e0381c1c480001061513100340014400803402610b4100030b1190303898104c0c650b802002c012104944060014001c0064240c01c41e001404100d8600341c003400d01aa485505e000b950051020290700001d0864545141c20003008159074054403c1040d00b80b008088001030034640909000100b101c1c0c4005a030b40f0740015002512405040503145545074880282d40500c0400c141005001603e08000382035070b450006040f58421000d5154848001d141580d48668043d07082184a00c0030b1141448d0b0030f9070300240490701d400c04c40740b00595814400b400100c09480c8085400d92102100310040204903040e008241841c00c1c3c814107100076160110091480d90202c0c00c50081ca03030203555404003084c440c0c0310780c1506040509000030fa807101d280000c3e041ca074030800d0b1801c1101c0f042410f50110708000048a4000f854100d48509107400c144000301440c0d400d206210030002d5031420b140c1031241c1400004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 942358687 1250 942357437 942357443
    0xc060b0303070c08070618151407050d230403140c0402041701151d071205090c031516110c1806010810260708121314010909020d0207 59
    0xa40b607a00c18a0a04014406401350401a0180303080c00a1064000c429442c0303003074800070880602c1804c200d03200c070b020119180f40b50200468090104070b041024030041c050180100d000d0001440d484402414208151548503180007240c040c0358000c2038000103403400c1c2e035880560f40b21501100c442c03542c03a00396886c1c2a0341d402480001c002850501c4083d031481c0c00d080c2c141c02481005486c1d40c00e400d81c4000751140104004107a00050445072180781d80950100d21420450300d5a000e4102c01c108490040741c00421070380c07041480310071900e0104894584005644003102c040d1402d00410051141c1e000001414000011581c110508003401070892120340580f160071140c1c4503400001d1480815211640070503809004142802e4150001d1001d403800d80d40203004220514400040320306110000365a00d000300000801c900348244020000b594003250469103668241c040c040502000da03002140041e81d40d4524505a42c11000c00011101c800b40010303107640440749003d01a01c01c141c401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942359937 1250 942358687 942358693
    0xd210915090e0906010609090209031e0102040503010e0316030c0f05030f0a0905100e0613030209040b01091104080a0b06041113030c150e12070312031b1e0c060b03 72
    0x400c00680c4032608404890810902c1040ca850784803820fa00c0710028000d03680054987c107001d003c0000540c0003084558030160031603143c120010742c0d0208503450000d202c080c90750006030400491500b409132210182165000e54035200d402c071040c10401006043c01414000031520740300a02c150305600e03082041c1c10600344c07542d13541e108241505540c4065410004a41d6806001c0b4582c10082307500c0c13141c000d070b40d2601c1103c0b4452000b0002d494124025072076407144040004070060300e4080b0110301881c0b250a41341c0c06541090f4030541540e110106c8403ca08400b0f02042041000001d5050304158000d041e44d0302d280c03904401b1a0103080c0e054408a14050001040c28400c180c13686e024003142c0c01021000c1c40c250700d5407600d2074001d10b400d0790f2400040141500345201d150090007000311056081c11107003011740da41d40304d413101c0341c0405410012980d00c801c111880e0300c4041c1e55803400d003541c0c40c041840704624803620f940d81722100c00324001c04c02e00883c0c8000300070083d0b2152080d04402012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942361187 1250 942359937 942359969
    0x4060e0a05010306051005060307140f0a0203040e0a140415020d0207030f080702030f120a020702090403050715060501081501020a0b090a031d030304051e0904030503150d2109 77
    0xd10300503000a1100700c40311480c10f0005081c501e80c81a020f0183c50000f0301f01451a21201800c41d0762480e040114248620200520903080d15020000c284001290300919101d034505407541d010744000620003814103080400d102030300560b41c03e50781c2d44540d2000e0440038035454800020000d0144682081c0362502c00135800e070906422812100c6807071200c3d56401100d40d00c00c0002ca880780a281000c0b1020381091245012203505020403e41c0000d02010060030030005070006500101d06035016000b0503000134580051196442200d026071046030b005104e44c504e081d0000382b8111000306059001c41080382803860aa01c2444488202500420400c42c28107080303201d2070702d803000c070201200030031801c4000103580341044542c1e162000005001c1c43c103240c80c000500c295032821030360050030303821421540709280e50340c0c0c03002c54041c60003a0388490b207a00d00720030700f03040c1c03402c5650380c0030704c035143c04141e000004000208407040c141c5041c25165001c1050001603881518940110b042e040088107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942362437 1250 942361187 942361201
    0x1509010f09180905100c080a0b030c04060603021306050f0306040b0d02040507020106180b0a060c021f030c26010b0906070c0b0c0c1215070905030a0311010c030b1e04060e 75
    0x405010f081c081c0050300d030f04400e0701070b0f00403c0b242280d028401194600000550400b40e03940a03c00c00c081c0075003651049441c1e400050111411900b141e0b0109501040849400740c50381c591002508090a0203031030a601609200303c2800000d00d4a4400d50321403512003400d840351002e0051a07a4040e01c1840281030044001e0701800e03050007260b28001c1c2144000441081d203005561070610082c3c414004c1c02d0a158080f035850007a49002d03608801c03403160303861502440086d201949101d9560008125000600041090f102c403207618803600f0b103401c1140410bc0c40c4481c6c0e00d0440e0183e52226940349040c0b00482d040307010300080a041040750010025a03040d03078000420614030164156904401d8110400c02596620540d020b026440144c0c0c400c00445440c9105800105900f04540c0d0305650b100068902003030720700203c00007020030300c400310482402d01a45600500d00e007014486d0360b00080203d0f407403c248d007100d64080508804107074640c0c0c40756484076004e0050402501910301c1d01d02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942363687 1250 942362437 942362441
    0xa0306030506070903240b120606011814041d0703050705180c03010b070203070f0602160905010b0d021309050f0121030804020d02030c06030916051509010f0918 71
    0x2100c2964075019850005600900c00c800c1c80054951207003201c903581d01d84181c51080b10740f001032040b0b850380da50401c0644569501e994890011401001001545481c50004202c00100c034071200b103400781d04905008a251200c140f4a0070311080d14006100c03100004011018000340541c0c000701c4c001c600c0048107010b800f190000543e107060b80c442c034901c40c90720491000048125001d0700702e00f07000d000510425000b00c4c000d10700d01c0e0008080700c582c82c6e1502c4030030105081c1c075030107540580d10000c9101c16501c4884040b00007480000020401c0b50b00d400c0c82164244a50000c001e58a82c1c002800c11040c0908580b007005414030b610108030603d411111002078200a0056020702100c000d03411845210320030281c1042580340d5540300051310756509103d55403060860407603050103490304281a42d11000091071082c0790762402091810181c0914070042c0c80d56402c02c6000703400741c0c802c044401c52007030112002c801c000c0c43d00030b5419100b50403c0740c00d1001e54011041c815201c50740340705241c0340c1e6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942364937 1250 942363687 942363689
    0x3180a1b06030614030607140909010b03010303031404030e060901050705010507050c1203100e04020609131a01030e03030c0f0408010609020901090b0913020a020c030a1b061427060a0306 82
    0x10b031000c00460352100701ca02c2030070003040a166070650010b000500c00a00c00c581d40403a20f41204070450402ca8180006851500260050040b91002000420515030316016854210a286004060b10304051b10300402e07800c20f1414540c040c03e40040c1070380c1c4591040c41260100758010000b00080d0500000052403980b00c0d5420340140d1180c490302c030790f9420302003003242c3c01450400c002501c0782e4070305894650380c402c0080059074015030a1203182d1181c3c0390810072020f4145130220000d50241c58085141200c040760301441e04251030050508103030300340081101c0e04400e1100c40645c4500308000ac400d8240301d560803802c00740d400c2c00c03c00625102d968000d0081080b003605d404000d140c64000403c0325000340c04440f94481c00d01e24264100c1c01c4158000d0803043d010b031065924141c08c0b000031900d4048107807001c40351030a42c0000d10000680300e23803244002c0d1602e403030403007140450540c24883da800740281c0e0343c1002e0070100c600c0303a841d0121142c148015501030103490f265000c1c500064010070342 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942366187 1250 942364937 942364949
    0xb07052209090521120604060801240f1202040e01180b06150a0507060b190308040e07030c02121615021206010f0212090f041b030b030102090603180a1b 67
    0xc2c001c1c070040000000315021240d1307140307028801e052013070f54000030044150240815411594902c00070621290038041c520082152500610800301c4005100c5c180403101d5000001c00c0c16848000e00c405a5412131501c4038907012280451b510021104190040001003642e129090304540042c0802200041091145104840d9801e20800680314814517214012040001441c10403070500000c0711a0711240e561600500412140074280d0810802512035410584999401080c00c00000c060716500e83c1d0721011074503003480b40040c10f120107947c1d045074503d4003200079000b1482c0d429810418841c1500e00350014264001c030401d0448401c002c1d404403d105454a6a02c80003ca0325401200c1b483c003400403aa005140403030004aa007102504500e9a035a440b5000306186c8250b5900c0e8000c164454002d46011400b03102a2034021702210380d4004028042d900610080c06103503030b14829607601904041146060214840b002d60030906000d4004003d4440710840880300b451070300c90003081c2c0300c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942367437 1250 942366187 942366193
    0x10020a11060a0c0201080a0e16170106030804030b04060f050112060c0c2f130c110607050433080a0e0712080c0f0d1d09040b070522090905 61
    0x4a10028445207105801050b0041441550a00b005520030140c80d5031041000d000000c0280e290b42c8007504000d41c45011110324039125206011003480d10140101180c40c010007004040d166a4865215009038440500b54001003400a000d100f125000101d0f4a40d84071410800303503031242e0031f09144100780c1d40d098650b6842c007500700c0c5447c2e010710418280c0075004103808001500c3c030780742765040030b01d03407010032001550011071885141ca92801003140d05141030340c04030720800c0d400c01c0140705000c0d204000b5142c1c0c2c0440300344204150420212010769003070310000c80700368090305102041c5044040500720f143c24017462061000d0b0740907040740d00801c50514180500e031b440703118841e5518007500511710380000084080000400d004000c0c213682003410305031401452072002907070821590094120118880c00602c59601d240000c805001c8041202c203001503003001e48404240703110041c000001e01200042110000080f9218000d0406515104e003400365101c04002d030203840280c1d000c9074188 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942368687 1250 942367437 942367463
    0x2040603050a1409070b18040e0a0201081b07030c0311032b090b1914090d0807140a0305060a121103060108010902130b13020a020312010501020f15060f10020a 70
    0x2903200803c2c5409502034500416019040160080b52540003501c1c1d20011020400c960741a17440d5402041c1001000101a2580c0112400090318100000340040160200d843c0d400d088110f40009803001c07507825150200c071400320b03841c0c1958207150004a034000c0780700c0401e191440c0058aa00045070040c081c282604154035030b0090f2095a058030310091085c0d50071400240a01030500791082ca40010034000300304480305104068100da8141e880c1c0349240c0140d4205a002034000f8102074101d102032600c0c2000f07419049009549000e40741d80c0104042d2500b0114806035240380034040606108842e03d04410b04616004070420410f160442c00f03030003110300000341c0d01c1d810700c00e950034590003411105940c200603040c0710003000103440c0340c0d03804081c00f24074042604440c8054590703d81280c0045948400d0340c07003003103802c1005078000390440d0f00403811440051740216004640034281d0729448090f80396000000c10b078444215071242c00030500c40201031501c0c0c5c0020b501003140d00070b01c1a12026 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942369937 1250 942368687 942368711
    0xb01020f06161b081611011b1401110f250c1206020d0f02040e060d050706120e0a0b2e1202010c0b090c0111060f0604091502040603050a 60
    0x36600071a81c000e408881c10401d002954010403c054502540d821100f10081255454030103a030000c681d0a2a09880010307000c04012590f610b401d05200d090a00c65144201080c01c81c007102c4003294020041070032440340d8610414250054503d048100300000d40710030141c0b1802c01d143e00400d4038200c0741c10240b04011030150002c1401c0074540c0d00514039807140c5040002c24002d011004c071044034416030801c0703487e02041103446003440740c645c1d1010150780c49140c240400700180010741524420b24552030014005640002c11204682e0181006144004070031800700c01802d020030740c407581d0700440410030104010144010311072001d9900da101d08045123217881c040001c010b4803411942100d1107040c07240740702101100742070610504d0208a85c040e02ea58480400c541512212040da100f802051515a00030710f0040845100170003c182c1854207806c032403d42080a802c0c180595902e203007040c140842e81003000c0700005084010f40d510340c0e454200400818080700d48032861840c0107003104d80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942371187 1250 942369937 942369943
    0x31608190e190e01090b120d0e100f20190803040b070503011409100902160c140d060c020f07290415031505100305090c090108060c0c0a06050a0b01020f 67
    0x41d210742c19503d84a0741e081640282c0141000038805500205c4d0000c4502d0a00c0304110045900025a03a8a810792003600706104282c4032030307000c580500c100c141913a2002d591007095030f90910200044115840c07403081c24141003600c84e2400d030a81e007090450000500540c03000540c040d512411208040380d4035400c1c00c80765400b0a0040e43ea41c044245075000e564682501c005801c080c484464104040c0da52505600301d9102291050119000c403071008103002c005604400200b0070403c105d41604030280014500c20412400100100e6a80c400c00e11641c0c800c11030481540e0f1590220344007142c4030280344200141d4480c2c0c07000030301c8103254078048140300c001c141c4080310030340c00d581960303041e0100d403e07806802a11160840007844100c0005c096a40001d107000c0c080994600140900300030b2501030511702c1d2102c0241c01084040c0c0100181000011003d1344801c0010070f09807a00d5041c01e29500b800c110b04d00142506091000744869201c043c2d2104540c642c098080b1001a420b144031551 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942372437 1250 942371187 942371189
    0xc0706020a02281809050106050a0501050906030903120c07060b0f0d0308151f1202091c1a01090614040603030801060c02030a140102030403080c0309031608190e19 72
    0x500310400c0c5001d900344424298250f80050b046040001c56076403a088100b59800740d21400c410703055102e19204040c03210038421440501740c241c5428080038244400a04241319111219020b840008009011035074188141c94120420080103002401d0004a41c1303001d0300403c00a0320741c507107807420200c82c524006580d12902807014088030200e0300d081e10241e0311980300403c0c0e030005400181d4048c5040c1c3c1c403100f4207254001c0402040b40700d1180d82d000103020419000f01c56406038810006100780380c0d1101100c510000c000f08483c00100e002c0e251010703040040c2401028041192000442c200985030004001d0300d83c510752104007020b40804100c00d0383c8162002a02003441d40c1c005204052061920140c05070015040311348181d91959017031481410b545605055960100600c4105580100c02540161107140c00b0340c11401e01829044d10782c0f0030404810010f004103144101048241c0055445141ea1020140007240e1126005801c0000360300e40c03140b19a40c01107000800010302c422101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942373687 1250 942372437 942372439
    0xe01060c0b13121d0105030103020a030b28060e070309030e1014040e180f07060c030e061201031502160213110c031e0f0702010e040e0102040305030c0706020a02 71
    0x540108094561640041d00640309680b42c803030710321500000c941c910402c00640c56150369003c100483c0d0103031131003246140c0084281040010401000035a50700c103800c60580303400c0302d0116072a0300d505404501407441d82d540648a8402e0f040c8030002c03103000c1e074022800c6503080d0804800036618200110100c0b040000c008011403818000c2000f681403050440d0306000349406c101e8501c01c0001410b62090300590710000025042100b0004810041480d00003035542c1c2c440180310784021604007548800d41800707032604000c5901c0d43c80062521402044050300c40c007525150b0343d140b8014202c01303004000d0205844a0000b006106109071180c800c0b11441c0c6d5013401c011102c170006900300031221400c03407010900d06032a01c42e64100c2a152070300608044030a10025540c17201003400c905102c00d10180e61f00000c007410b0000c01c6040000301e00b150710582d170901e0070481d030554550014004041d000e41031b00166101207004010048004018070110041d20101c1d01401da03240c0c81207a03071300d503814002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942374937 1250 942373687 942373697
    0x3191d0a0606050a0518070917070f0b1306120603141c110a150b030102190f0201110a0c0c08190615050109060804060207050a0821251b03030608070e0106 68
    0x110b4801b0404011441e0045264907040c8041503440e400000710110348a0340d80019004010104802080d2640e400c006001800d43d190030601204140710b021202d0340b081c0c009000c641c0000d051020700ca07900c46d4001e546c1c062441035142c2444a00d15580380b1f814040291002210701d10036400d5030059440f07440403a02d48008240d00d80c41a030358588071980f00c01d0440302458981d000c107400c3e0340d401c0c00540b03111250080c02c40c2e0500d11040380140fa841507440401c0541e490030021205803d0030800700d80441d991824404089801440d040d060315101ea40f0224403030103080349000d94041d42c10800e0319840d0149505110040349203030502d0703548038940714690100c3e22050301040104d018003a030544c0305000300300042c06d018540e2601d0742000016071080380d00580000d050405041442907159448200032251910303031820200e841806007013655040c01d503105c0c1c1c1e080440d2080c8110301d4440140301c50500c070000200c00385000380150910380184c0d0503500072202c001c5240302d03048003680e0481c0c400b0303034030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942376187 1250 942374937 942374959
    0x12090f031201150e1c020a09050a02070314070c12020f090106080105101806180b030408090108090a260c0f1b10142a0d020f1203191d0a0606050a05 65
    0xc01a08002c145c600301d0b0440541c46001030042018410f15201d8246100c0c0980d4480862800409005c500c840c074298509081c0305200116145403004801c0c0d42451783c542c0b140e1300303541c00060403100c5008a1550700c440700d10008590341d90701c04600ba04880302540c4500b860030070248142c40442c00704226009541000b141002a640b04403203101c1b121140802c800c0c1c3d15608e80c0401907160f0700803202031300da000d0700003082140384d68003540a6510881380005010120704d5942c0c2e5000d20307086449050166100502d400d20308170040e0b0f044a4181035840d044034005d21030524000c0c0c44051a0540c91040740024210b10074600340710603c651007590690301d80d00011307515901c10a00f600240a41e0403901004c4c1e11441c0c3c096074800380b0000c200d400078020f05240000d06402458484102e1a0780210740029007001506002c010a603504092280d01588400b047d400640340101660140f4030520a14601c46401c031080c04503a0844460058034140056601d640500803d035440d485600e400c0802001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942377437 1250 942376187 942376219
    0x907061409041b020303060f060c0d11032a0c04050f1329040605060f01090b1c0507081e0f0601030c14030a1e0e0312090f031201150e 59
    0x802071128040c01400016005068141d031402041d40c8002240503a000000380b00c4245400c001d400c80e00202142d44a01e00540c0e841c2c0240c40c0e0082111071001d211801d10038444502041c0144c44001c4206d149603584e0300d1202c116041000f8111000255600408000c0740a60915001f1980300e0702480302180745648642c80b8941040032500000da03002c2003102140300ca41c0f240001d008200c130400081230b003000d08203420143c00b110702c044c040c01d106644030f03091021266040b440311400c44480603446500c80140b2140f14101c0035a0381c0552680601d405c00b041511500840e104c2e01805002241c5c221850311000c480189800994000310384214050001c0c45a40c801e8000d44900c201900c1d240c1000181541c0c0303009d2a03042546c8484203d9282d465204000c40203000d400440c1e5026001442001100b211a035240c0c03069114605800160000013588840d0070022050140c1c0000212581d47c62181d5006060710020f01403244818080700d0028215486038042c101c690000030100407020503000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942378687 1250 942377437 942377477
    0x1502060103020d140607030548040305030307170c16233306090f09030415200f0c271905160c060203072007030209090706 54
    0x903101301d600c00d1601e070080804030002e0101ca800781d211502c021940c0d00381200442850440e6070b90b2024004a6008055505000400c9031200701e040309a00e01141c01040750510124825504054601c0c03000100380a00c10358490260304c5ca00040c05c010086039142d14400c03610b140b281c5000d0000c0841441c11140220f010b03503044440007100c04030000d054078035a18002d0b080440641d041a080b014402182c4a61403054903000703520b2461145d56045031404c40006014540040c0070200d2042c980030000b00c041c40100b003210041c3c5030f8480c06032031074000844010010b80c0b00741d0509120030844880d481208400207a8584409040340203005112000d03003c4c0a0780d03100708540840145a124245c040d00c044014485000b8046080151070400355121810107a86024150041d40d103c42040f6190b0700344c0c0055101103841d885000540d4070748800c0421960b081b90101c0201d50880e100480e01442c080010306041102e10981d49044659603250600c0e4686078180f10f5500898802c04581c68450122 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942379937 1250 942378687 942378709
    0x1030c0603050a020c0607030615052502040e0a060c030f0e060f04060f0e0627060705070c1d1509011401050d06321f0c0302010b1302070b01150206010302 68
    0xf09001800d003648494443c0c5001002d440000119984903070038130400341c6040c41c1440320302c014107000d49030198214010300403120340050550300e0303404c254a03e0110342d40c0b40c0002104991003c12110740c1d1040b403d00e44004c100c00045640407134030344981540c0d0311440703020780459003024030007400c11a03807408948000301c88000d000b12034a660f50f6950925120a511070149044404001801c1503d0300c02040042481510424a0001001c40c880c8054010015081d075100d0362603c0d000791142041d190880b10ba01701a002035510024240043c2070315620b2000280c41a0301d5152144840b400381c000303000310b444081c041d8406182c02000b5040e0503500482c001e00c00061325403c0003500e1a0781d003a0760301c00b01d841c00d0a40342d0183c2403500c04484040c50f030038420075003103c00c45480503809440e001107001c0b81104140b08007440346007031510040c5030007940a10100403000c0d140c940017540034000f1034000e42c0305640803210f80000b18000f04149a610080c142c0d203200c190024140e80e403c54003002782c003540d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942381187 1250 942379937 942379951
    0x105060f0d110d0209010b070201030e060f0c0f0f0406052104030f11070f09051e060a0302040908130b0408010609110d0e031c05070801140a0e2205030903010b0901030c060305 77
    0x140074119005849000940b4021f2500030b6415441c0c9156200041c290b90410248007d1544004180013100a00744c0c0240d400500c1c1c0688165104c44011200203640039410f03104c10b00750404100024129000720060580c6039050000251100140d8040721202605680140000d1529100203100c6401003c0c24040b050f145401c4a00680d03031403400040c445284d40042d0790b52920340c0203100c4090082001c55100c01102d0781c0000807844d01c00c02044c0c520b1002d1001a100700e854509030400d04c00300c0e0302180e04a1041006c014401501d84512291a41c0b2070300c00c0004a62800d080040c01c05502e02c0391951901102c43d0561030320880c04a080050000140d5000d0907003c01c102d504480341415800c0441c11444100108183c0352040028210f090160700c04400d52125908950741c0d642c070360010320185c401d400401c00c2c3e1034a604042e2682956100340003500180182c41c01c0e000e0210000c068000d00b01c00710000e0102412010074458034003000e1100038041745011505100303040c000e801895005403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942382437 1250 942381187 942381199
    0xd021b06070b0a0911030304060c1e0b07181406270d1103150106050a180b16061107050703080705100603080c06150a120c08010c110105060f0d11 64
    0x3100d444903402c040342651031041c1ea9696121000801030b00300c0511216100c100c02943c240792038035030042c003110500c0c0b900805c584651640c00c454001403a45688075142c00c08000249858075080282c8210070010107500d090b815100001100c1440784801002c1030006451181004400381400d241d81160401c0c10b10700040d4407040740e040c0d8458240a2000c280035505080f00104182c2c18181400600c01c01903040708403400c0180003031504001112a041c405140158150100690207600d0000f960030402e1001d0f4002882a284800b03010411461030181c4010441c440411004554038814094020003a4000b94000c03c0401d441501804d0954090b40550b00d04944241c003e600729540b6030005c940907200400c0b8025503a400700046607008132490844a4503541c48000903041c50913038880e0314405045003604004014801d1301c100001d00e084030090103d594407003806404a4130b0391821b54459840c010010b0709600d04503110f005107480240000700b1814054884000601407030481c0c0d60005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942383687 1250 942382437 942382447
    0x5030c0303191503020109030b06030c06030c282007082407180504110706020a0503090f060103030f03050c0910020303090115080c01050304020120011d0d021b06 71
    0x2000a0008500c107038480401d40000960040300401101c198021101c0c054608400c24030050b42c06c9480e80b410307640c2100b1403030340703070b80d284400286000840400c0e6500410040103120b00e800891000d001541c00c0c084140d82e15500d1034007c90a0f0b5a81d40c0a50304c00a0f494850720850508141c490305240150a000d4a90403034485003a00e1610303140240c0054030b0545420480e05500c20303402119000100780c03400002c1072800003100c02012889006140c0b00b6070791001c3c80740700d1880360422190b03001d601c11820341d11944030020151064100300c07401500360241003d108100d900200e02c040c1030740d034992108900000444400c60040900030301a411a0004008031802699408038103404280709600450392480c0149242c1d0035101d42e810780c0c1c400111881014001c0c11000702d40c040d40750200b8a002912580c0e80d000484002c1080381900a4120020220038980348041d0000d60130b01031400092504081004403207603503044001d283e040140c110041120400134144000c100407140285050706103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942384937 1250 942383687 942383707
    0x3010b130b1201140402040509030c0d1214010b070b090d050d050709050315090d050412080a1701030605091209060d05040c1502061819080a120509030a1d0a03020603040503 76
    0x4401003850a00120130030b100300804c61609010b210741c4010f02c007000c1c5091445000100382c1d6009030800c1e01060000c0022241c121400b180d005d0fa0b00550200034581c26540c0d41d0700c2450495000c144203803040050100041c000d403900041c44e4183c1070803507480da4a01104d0400031401004060080307420028006000100755904010103d04107551401c60b000d1810210306e420701d0414201042414042c040c0000c10038030050503100c1d10b04a40244400c0d1b9110300072082224070441030035041c980714020b100084103100c403aa000f0b9224a071440112001003000e440c8d0300c4104e0154405039644a41d0410607417000001d6508520b4105100300040b000b40340e00c41405541d10b243c0c00311101c005a0002c2d04200f0711840c070030b005090920f540b0f00501180f0201c0041021203883e00c25000c0e04d50480012081c1300b0600c280281d0080b0860708204200724209075040310340720b6100e2a0301c030303001031a001e81c0e501201c030090f01500030101d0000d048181d61131460b404c1c4501604014000d0307445010070b100f01140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942386187 1250 942384937 942384941
    0x1305060418060203150f0a26012f13180608030f1806040b0703080702070909031101140105060318030f04090e1504050606040207050102070c06050d0b03010b130b1201 73
    0x1c1441a400542c032850840d010b007044600c0e00207094400c1000614003141600c50609034020b03034280c0010300c41c0f418455903d464850180c4000c0d005158a000100301c02d550540e422542e07501c08501410002070007007000782009000f04a8407412011840030100544044441064080861780d800403c80d40d5130740070014117541100350348003182074000400b192100d01c4504403107110f42080b03a045052604180d0785044d903010700c100090521035128082101170780200051f00c000c00d40c1080034001c003055850014010f00401103000015030800000c081001c1882c45214141d40300a070209055544d140d21044140310300c1d040c5050b250004000b00455046104000c0001c0c1596030b40101c1d1a40b00748001e035103403a10000c611001c0310341c00c00134080002c2000c1100c6411110485000d0385403501810117500900ca5484001e20030b05000700000303a06034100340946a050b80114081088403242020b15081c0d03248500c8a42c0d002015003c001030a40380e96000c2c650300b6102600400116000e01c1265007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942387437 1250 942386187 942386231
    0x10030f0603030e0f01091203050c0a0b04060f050606070203100f110309030316021b2205070f08071107050603040303110d0902030c040b030d0f021c080a1401030213050604 75
    0x303002241c0f07140080c1400700d0b00010340b40080c0703045140c241c9440c0104890350301403000101000310009440241c0b8404100d1307422202d410260311400c034242403904c80c000381019054030b80c4503030409000405920702036050f030b104590082c01610390300c2c488081020080216002908005607112034a00c1c5401920010b1889a0003880082d40c0d2820100c42e17560842058200780821507000c1c65900303803ca501051a0f0240b044d050310b170041842450805449131341c480400010704940b4107402c0000280d0301c036889401c1c510701a01da5005a031510b640464006110321407001d801c0e840700108100600300030b0b004584c050b00a10700010030442c004403900175507020341500304200d501c81e003000701581340070b00ca0040142c104940c1007003503003800808280c1314100340c610041801003c0b8007040e0a240244282c52000000300010392400b8548400a8520344064501444182c40c12040100110561600c0d43c10313250004c01124a048600c5190009881c0062039950480e03100c180c4403d00c0481e500c0d0b41c0b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942388687 1250 942387437 942387443
    0x110d03021f09060e06071e050909070806120d0f080a0213081501050a180e0c030f0f150103080430060c170f01050f0f090103050a0323040510030f0603 66
    0x110310304200f4104482621a400030040341c0b50000c03410701c00c0080c0c004240f0121101c40e4054280c07941e03c0c0311003c1e9034500a464141e50001c42010400c640ca650100700ea622072101110800c04441e1044907041c1c0c0d5026000d20140410341c1042c54040e847d01070000b13260300181500f400352504000d81540d0840c480d4990000300140c0c0030441204090165004690243c0300980e0324200661400c0c15200c1c94003542c0c0c451000965941c1101c9918440c01e00040300412000f508039402c400301c45812075503800740d1500301c1d601030240700c2c000009029998415030499403c4440d0303900b007a04241d00b0030007426803040d0780160a98808007a200b0071031424028481c07580915000039031a40484070150080380d100a04200702e203500d004000d0726134500c07117001c0e0540340d040c0c0b106403c500c0b0b94004103292001450030554840c207500c2c000000c0110004141d80c0031486035592040da082c0b41580c0101c1c1c83d038001c00072003840c142800148040e003485c0340b031040300846918001c1030224400c0c03620750440f070b241d410903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942389937 1250 942388687 942388691
    0x30f270b03070906081302100c02192102240c0f0d0e220f0603080c07090e1902010516120c03091403070b0f0415080702070909110d03021f 61
    0x12420641041c00f90707004008904008107103280900305103150205d040d20091150608502010b072092003a482d40480f40d070f01070419a080e103040750941000c00380710703c60403502c0d4600c01e410b00d90409855028502443d4040c00c5a0070908a1401d4800d0f801d4019101c0c2d01210b5040c080c04041e120f04101c0d40410921407406010603c41a610080c020040108503d02808018204030381c00d1116007100c071600d402c0c0c03540c0040c243c041200504060919540003501701100840c05080071400800e01d6012928052010000c0800780520b150b155000e4807035105500410300440005540168001c018628001940c1c482c1680942e442c540c0d0484a4000e40c40094209140c0a040507002540a005426100400400000b0800000740d5035441d600400340c140102140f0201d54101c2c260960b009002198084041c201c50004003e080304022180ca2005110704a0001007031a154401c001180c0e0b0082e511035181c1d24500c003440f1a003c1c009100710304510032609529019005560443c200001039200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942391187 1250 942389937 942389941
    0x40209131a0901060f08030309060709030209150d0605041a1b0406051b01050403080f0a0c0905121006060c02091b04180b090109061e03030f270b03 65
    0x1804119000108000c048680c048044800328403403a2585a0328040980c8100c00396441046541c05800a0391280043c3c480c0610045002c01c004000345106031346d1402200c032640c0c0c034400c08403613621040c80007039048000d0310013091124003c2d10712414481c002030804494250365580c0c110840e002291300f40d5900046001c02c5003074408111282c0d070400400a9101e50b80c072481002034825208038405d900c28000b001540385c1006203080310002941d515240200500d00d41400c001c1d040c0705080301e05401e0030084000150342080b01e40f05498560074141c1d601d00c0101d05000a00c1721088284141c940d861054907482d0070452183c4c00342d5006006280d07101242c1d07501900c10b004424802505645050400c0c0d16100c0340c060781107040e80c040301c18a544c02c103621f00401c082d450040560b140c60300d800c003074194004514800a500101c0850f00345400000c00c9030b5108150508940e180c1c08001d00042d4010865095584103809039514003601c9106003501c4800a00400002070b072540c0201512070300842 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942392437 1250 942391187 942391189
    0xf181815150f0612090b07030b0d05010f0c0809011b140c0f0f12120705032e051509010f03020d02040503030705010c0f0807020613080d051005040c0c0206030604050a0902180402 78
    0x2140c404c0303071148400140004041540c58244403e03006040c0d0082607624044104250307203140703201c0845500301c00200300301034010300c00b40702401403860040c002c181490003050f6007100c1440340c90900e11108007180265410140201c074150440a600380801038188281e081004007404440e4030030b00303030000812903925001011420001c90240c0f00308420ba048c82000440806044031070f500c07080b02c1c0381180d0307a9623400c4245840c0c8020300c01c4105da102614544500a032521103104030950300100c488402034807041c0084015031048140d82800a0540300310001064020b030083c2c00c2c44070400102500b040d0b2136102103495a006048195881c1e9120313030b105002503400c21382610000c54103103040281858070000c041d5540d1000380c000082d21040c00344450600075018143c0301045c1c003001091210f4144254090038003085070040610a41c038006080d01c2c9a405407041800c000c0c0c0c0a08507a0442d9140c00800c002004000c200d9400d442d211204600184d488800d46462440ba4080800c00d6044c540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942393687 1250 942392437 942392447
    0x8011e092f0c06130602070507030b070e0d1e0309081005011e06020d0e01180b1306090f1e05060a11120f070204240f181815150f06 58
    0x1060410200d10810803194a0800482e0f810f90210081a2480500d0f4851821600038400c5240180c841d000f000c45c084101305012036003c0c001c0c000b0b9554480301e64620000c00c036000d407010300d00800108a0044010034000d5000b200e020b0640a82401c1e010a81d48204507420200ba00c88000041b5540c0d10040c8000e0354410386101a00003448405403500307060040107980e0f094144c1001d000e00c210580c00800c01c0e803203052003541c00c0c21050b0404030161380e58440e11040350480417251401d84072010300451024400c1410300115070b420002c5065052800450000c4201c4405081000c203110100101d419103442004114484c4941d507014031820101c1c201c141000c1c1d035400f103074000785000c0089078080d8400344251103503240c0490340013440801342584c901ca60400c0c140e8100c0131442d8000001808108030401208407407040388800740c07002c49503e8003000c5894966100904001d1000702d0b20100c0d0380d101540307903881c440020014810f5510080e12203011141d41c480950030945070702c14400e0365845 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942394937 1250 942393687 942393761
    0xe150a060608070c1707080315010201090b0c0904020d0c090f0608011401080c0903010603060b1804021f020f03131a130315060308070b06120d08011e09 67
    0x45081018500301a0010b01c8641c0141c001c40c2088000c02c08101072010a00c1544003a000b6005250b0b40c8140070f25201c3d90070b0b0000c980c0c06d0b1411449682d5940f42d94010b020b5104966809000a50107594400400041d50400403629400a03030030f024003403100c0e03503a00c00d00104803101c0c1c4481c1da0309440c00c4407201080300384bd0091410088020010050302d8030042e0418488002400d200542d581e800120440c640074840c5000d03490340c20020300006010103680030603201c5406480720b001c003650918040309451402d541c025004190500c83c20b01c02d10b84d000400503240b810384151350043c00403a901a02e142c07c11b0a070034040319440e603c1000100c40564103014203203814083d9a042034110f40d08440e003001c903448007603c0310700180c2e405903042d5519808180515408905661141058101107041184c01c8450902810300d220440148800019040810710003d40e036440c5c040c0e0a203524024a103c0c2e201500e030450382e031080080784040c020702500d010032442ca1102c015402400240881246203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942396187 1250 942394937 942394951
    0x90309091e06270618070e0f0f0d060203040303092a061e030902060c010903090302040b03030c06180a0803040501090b01090b010e060c0a020d050610050915010f02100e15 75
    0x10a0716564a0302540640c80c078480f8025011480c0555941808035102800812030510000c03550010440040c0c7c200c016041003c90a86803030411890200c103000702c130440601081e61000d429080c585c00620150000c0d98014801e00d0301040354449541c0b6844060070200c00c0030348000000030411480380504c40d58500500842c07419004950103900e42c00c80613460542980201615080b03611b00795265401160303400ca0322400208103031300c0f041c02d0007001c400041c0022407107581407004d03c0b4414640002600c00000010001e4403141e25516005000c0c000394074003140d441e00030742081002146080000e50711450248001017039980c10f9162076030324408142c1040705d0107450149a240741e43d900141218014000341c030a40d95401c40400110315080d1500b40003503000401c03282800810202281c2c03c0d0007188070b0700722a1156078940d1300f04a0000012a01c01c0900e8042e260240380541c0f007464a000d03508060f0058500c0841c1c8492000c0503034025005070301da182c0c4101d690303141c518244030a00e03500c821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942397437 1250 942396187 942396199
    0x1110406025802073507060509030c1002060f04050106080105040809030c03010c1e1b0515090303040201080c0703051908220209011413020d060303080705090904020405090309091e06 80
    0x42810007644c0c107500420300640400f501d100703040f04105c4000030b00da103084143d0380403501003e940d203200900c15032000040c0e074001c0c000e1840105881c1800e80d0b14102d0b0070943d130054940c1c0d544418007414903610052081e1070f190348400f40012034480a103e06801640640c4a0703c3c1e80d281c0301d000340b40c03608495280c0305000b0f81c907000b40c1031040b942c070950086420b542040b0b0011802c1c0c40401c21504072041d0310340b040018011030300b1102041000207a02440724503c4a4003041d50340c955100f15220302049501a001c03a00c5840083c480040240013001c00c4c074440c1c02c20600f0645049090700c100703003403001d805c0c0c0402c50f001e0070302030f4580d024901c503c00106da004c00480b0340d21088e40442d11074003042c8181e48020f494244d00b50f01c5941c03120b06c1680742450800085464114034106c00014010a102c240c010641c44000b16002c039108108a50640001400c9030040340c81e95401d010003094000c040400700d0005000c90302d119691090003034007039049203400014124400d45801007141c0080c080c680324074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942398687 1250 942397437 942397439
    0x180807150b1f050306120618010c0203160632010806060d052d0d020304061b02030a0f02030c0415030203010b040e0714030a1a090111040602580207 65
    0x14002c0b034010103500101d140a613126204d4a0120340a0300c41c440400005004030f40c01c1146d00c0300741503070080f10604440024488046450300981e200e201c0c40386c410000d030420307450100104049410a5800ca0302d0b03072500c0c0d500d0200c02c50000210700c1da200b40104a2128140040041c3d8504000d2150000000c4500392070080c19a5522540c03100c0e40740c80e40c44014070580c4950b410056000c0440141a5405d0998030140c0d20804025240e51050240c600441c1c000b80c1580b52484d605400744000c0c560144c02805028040d031a1403000442c4a10304030307890b20a10f44802d6403030721a03006100b4296a0808655002400c503c109820744040740c00c0746029906d001c505d10201c1e400020614101c0b405020081c040409280c040390928600c4000913068207556400103840c4c0c00e0b01210184a6880d280082020464020a40301c00344680c1c0b19040041c0d01c8600180340070a03200c4485031304015019030103020218050500504c0c0d498110f94665091900746607802c82140100802c42d8441c040d1024040319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942399937 1250 942398687 942398719
    0xf0102040506121021120311070308090c0a06090303031a0619021c0c060e06190c0504051e1c0506040605060301140f0601090812030a180807150b 64
    0x94000c1c00510030503c07400e00c021450401c80308262601900348082d92102da601e403070240456034801c01000715140b180010310704110910034410000303000a609407640c9032040e2078a044070012400390440f101d502400b19002c1c01340c1d88142c0560014200c907126520003d00c0c50801904980f0040c0c40d030841e84401c5c00b65400c559807010101c03981741d41c03940094400d10244200032807900480d030250810081d00c959103840480d80105d030034010140f15201c288161113806280c540c4401081d101c0c12440d4003040341c01c840c00402d68001c04050347c6289440f03818a940c074400a441c0c50881c43e08124421b0050030b91022a0034085000d040311541d003c0c150a94002036500d05a4030036004002912b079035940c0c03000c5203144e502904803513000f0001c1c21910005086c92062320900c40d40c181c0c1c00d1800300303007111000664600085111140c46a4140c0542d0540d43e504080f0300240038280e8000c00c02c4401c0100740d6000828000181120601661000501c07140540c1d06408031841c11000d20f00c80c9412110700740c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942401187 1250 942399937 942399949
    0x1819080d11070b0c1203010b0306130b0306150d020a15020c0d05031c0605041a10030c050306101404030809090a020c0c0d02040f020d020712030b091506070b0f04050f01020405 77
    0x80720102000c29580b090070329156400c2c030100440c9174460358000800000e464a908010314012a012502410115603d814410407507001600203034242d08600000380e100240784180300e00011020741518110328a5500083c0080750fa9005a00c0b2890300c5003c0481465040100c00a1000d080c0c0d403103101d07070f501a16526560301500040d0700103408181403032000009680c00640c010038001d0024811080150b0a030b501300b144683e60940105000c5202c640c00a01c80d0141c1800326402e40c45081ca1034031007a00384170a8144587d84541806003444081e07002550803802030000318001c2042c1c0c1c0d158840c650401800040c090100f001c0c1a005000c180c1700d41402140095441d4400c5800d503a4260061000c10081c00c02807100c1c1c5000392000c036096100c40c0080d0000d24460340302e5070a030015010710000070b5003110f0304803801d580c100750107c0000d42e650510700c00f0f81801d140018010390800d06169201401e140301100d08550315031000040c4400c000e0200300c58843c0d900c40740002c2d400d01d801c2c1804111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942402437 1250 942401187 942401189
    0x102030a2d020a020111071a0a051e090f0609031b0c01050a030203060a0b04060203040f05041a120a05060411180f061302040e09070302091305070b1819080d1107 71
    0x6003042c0c1c00070319041200e000b5441001003490f11a14581c4844650a040030581e4206070402c0c0300c24800800505281540d204451082000040303900b10003810036a0003a05003801011000079101c1c01c5101400394008011080c80340d00520f00540d40c440074012003000344850788034560b905600000c0c2085250b83c000040d40c00100052900503101e0392000f001038031004050b030000140305070000303000c40c081e540800200169096400c408800c50740d55030a00085410007485042d8101b40302c0d81c052514545000c94058461049007260f45481060320303a40e007000800d4400f20307080d00c3c9001c0c0c09807050500281c812540b4045008001e40ca2900c2c000300500c02030000c1c1003602c00c0e10107505e01c802d40c0010354140c6001d0103501c800d001d443c0c03510401d820b0b44d4144901080e030ac00c084d10750003d41c0900c184a522002103078418043d00d0040c3c07038075030504169000702083d900c0e0f000c07039144103505a8603040a111403420361000c5003481d0701c5c506880345041c5000714402d0020060740d10098404c9800004040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942403687 1250 942402437 942402521
    0x14060306010e18040c0f051504051507080309010b0a06080910050c13080c04112514030d0b010315121202030f0a0507020102070f0e040b180106080102030a 68
    0x40b82281d0407000400441d0034800800c42d1144520070f01083c44180751074030050318542410809030076145e00c1081350000c0031410145410000300000c2c0300c035007041c10100040344500200641416003582c0d8410060704100c4940c81660354a0440b504580b034a48031010040c500d50900e0ad415040200c1126103e007100b102c1d40066648850104103404400411184811201c450600480d42c0740c007140c1d6114480d01c1f1140b8030440c01c004400c45194000d02c1240c00c0380d150100d8503000c00308500380c40000d1004412040c0c44030425034680340103569081c00100b45e814400306000508084840000d41250000072106c1c801d8040c6072824004020072800600d403a50704200c00c4000d011420000300c0c0b46101c2c42c85880d0443c1004940c0a8440e50480040c1c00c045200341c00740e86c1a152141e0546c10003001d980315141d040340c00c020100c2c01040c48104025045804145000ba541614581140c01d40d040c580c00030800c3da50000070440c50700803030700c109444c07000b441ea03c81c031210010302c44074550292840686 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942404937 1250 942403687 942403697
    0x1106040b18151b0f100b0414010602370501090203010501140310180606080601061b0b0c1303060203010f1a04030b0606160204110a0f08311b0f1406030601 68
    0x22105040c00700452428440180115a0031081703032010303c006095110f130418000c5042121500380462400e4556068a61503030052040c00b5a00c4495011311051603e00240340d5400c00c0c0d4400054185407492003010b001e40008105030b00700d84181401c48605900290f0a0940003581e92038550380411840301c540e080e140046183d407040041440e051007050710003003c642ca8003d0004044801080842c100c881c140c842e00e454044442c4600350070300d00d01c03c00821640c000e00014070300860300806000790310b600c2d40354184030b140c03640d81e440c040342d10030707000080448144181003007a8098420369001c02d590b00c02d886402c0620710782d64003030401d0020340316a03ca0b40f00800c02d100d00354074ae24280a100b9400500600004c00740e0b2003481041e5000f4000c0c500018002d881041185008aa215001303d4001160b400c105001117000d1006440905820b00c0c00b8117000440350200d2070040105054007018413510184c2450490380c5814009154420184d6014480040d44107aa591040e2a8841e10a00b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942406187 1250 942404937 942404977
    0x31b0216150203130f06020f03030c0a0818070e1b13150c0f0309050414091b0a0b18030f070e0406050c0c03210703090506060d1106040b1815 62
    0xa82c01c502a52030150081e07084c42e400054880c1c000d4129900b00e600d240c082d9056400d402803141d440e03110172600b540700b080e010414007984a210743c511a0b400001307410b00b5000718403004501c5007400c03600d52100010801000611075a80554925120384100c004419440d00707020150380d15400b1075604c26142c03c034030041e8020804a0296401e0102c081d800344e40ea0401001501d8060100003490103454004c0e460910030081c0c000e00c401020f0700410700c0b0f40c001c000d600d80c00c10403207402450001c56542c0285130610001009410702d0050300c0103200350f02d16000400304160505180034800206000355612040f01084031659540c03600d82c000c3d400803c0410543d448107403448440c8540d0343c0312203144c4030000340f07451140341850740c070101c140802001903031f04c0d140d44004030180c90018001400310740210b800b1580910b040c662140d5118494882215010b1801c400901300d038000b81d0000803201400500d411303190607a82c07100c0020030800c036925280001c40e038802040c140540031010700200c540f594 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942407437 1250 942406187 942406229
    0x801180908040e0f06090f0406091112300d050a0902060406051308011b05220807030c081b0618100e030106170c09180706031b0216 58
    0x41440c62035001441c003961641d507640b0685100c10300710f4400c000104040c0c0425154034007006124025215508591780645440c5c803106c1c014203044400302c8804444500039102900d07003c540303e43c41da44205c09407450032402182c0768000444500000198440882610980425081518000348003464002074680c0d41a010500509007084043c0d071040707011400064042c2e220009151058540da1f9441819603500c3c1414240c90302d1b400e1003007206460300c1c0c0941305031380303c1c602074003020140e400040030030b004a0b12003943c104480d400540546d042540d040c424080d14880c03260003040480700810100704c1111110150180c5450040e1042800062110041c00e0311840c1d40f9003c80000d0110103a0070248070301915020081c0d0302c881c025424010001031a520001b02c0c800c4880c07542c0003400500c40d501e070030801c00100040440350499204820444c10450070480200613200d2524005031078008004c51055148092000d03104540c010b4106215000c00e1801400032281c1010910780803030034105e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942408687 1250 942407437 942407441
    0x1615110d08042915030c0f03060a09020d020d0606150912080c010f110c07090e0c06250302010209040612020f01031a031c0905011403060d0212010213030b01050d03080118 75
    0xc10f041e80040140d07018002c0c81c2080045840341c511040b405c880c4407034000340a0284140c110a90b03035a054100200095020240c2e8101c1c2d10858401084002e203401d5036400030b00315142011090720312a6446c0424008441c01000c0292102140c2c200024601e141c40e070412503101010134000d003140760210b03288400c62800d4000701c0c0854610300d802e11031072035200b10303650711070704800d032101c0d400c0c407400000048540da41d124a40c2804080405081840700345018002507500c41340c141c0c00400c020b0154242a00780c0c000950403902c1c0b19500150761505c0000030802510b4842d0406035146058200c40c0d001683e8400346204082428200070440000e00007002d94480b1840f00460303094060144401c06862010f2a1442070540685455142a85440044407030481e200002411300c1010404610700785031514a460030a84018a5103044501052407075007a41c00c50504501c1c0c1c035400c910b050007003050049000380549010f480000c0c0140a40d180148250018030681d210398070704180007100350b02c0b19 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942409937 1250 942408687 942408743
    0x605071214120a0c090501090f0b0a020a1505071403010b0703030f2903010c020706051b0c0a0321021b043603020f0304261615110d0804 60
    0x1c2040745440e0143c0c035034026143c034007190741c0002d404920100d415805103034000241c5040c40c02601c00b19040620050b80d0b5441800d10a0640c85036005160000e0b0454506482440e080b54003c06c0700d040622002c3c1c01480000c207600082c4030140014091190b210041c0c0d8401905031601041d042250823803e40101700d00b689006481c41c6400d90505030140501e41020984410b5000b001003004c103500413a00d48509000b0303d800158100a00e01c1180416006d40082c1c0503210103940680000500251038001c069008032000b28102d00100800042c203500750b042c800c890b0025090001e0b0b0b403403812002e100e090a880348950740e41c000e4460f2140c81c1254400f04200c0008003c1548120704080500003072200c0001c0300180309001820b40002c10120030b0360b00b10f03150001d090212050600d4590440b4080d0088100180708945061800d0413441c40c8a00c01000c2c1044c1c80c429800070303642e00921450942405110603444075030300c651429400703410f8980c07080e00840d90300000810b428109040c4201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942411187 1250 942409937 942409957
    0x1b090c03090b19241a12130501020d020a0903151103130807170304150e0606010c150f0e010e0102160b090f0d03060e090a0c1701090f0c060201060605071214 69
    0x80600c108a106148182c01003d44a07071017003640802a07200b003c100c070f520910000c03071111020140810907070a01590b411030313080d1052001500f132403002d00e801400c0341c11402e03440f00010005a02041408400044422050800d8a0a00c443c442891a44d0310034032002d0540501c8000e8003000a045c024100d081c2c40215920141e030101e0742c1d40000307040c903258005441c240e5111152420044104000d445040600b42c262070142c40107a48803401510302403810f407025211403400e01d2031600800e40c1ea11422380d808411340030000c0c0c1100408422821940c40843d00c01c00e683c070412400440074044500405901d41c860910130080d91520803070303414007c10488013100b031b2180b8603280220707035003582004c021342c0c01428440386141d503001c1030340c0d40d10221060064401b26411400303002d0070722101540c41c600c1c0c100c00300100307200050707a81d040b02074640310800392200c201a0070140310380303039080c0540e10007072913186801428031825072184a90b6105809424027801800d800c2c602c9445002c1c02920202a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942412437 1250 942411187 942411221
    0x10f081f080a08130e01060801050d0c0e091501230d0206120f06040c080402010509010c0c0b2d0703141614030a27051c1b090c03090b19 60
    0x71145400340d52504151402024001100130128400e00c0d4001214121030041e922000517910300030910009905000007540d10300b801e204080364a540007650700303010701b02101c0148016005c21020011146041c0c1004032a01d00c404001c03005200441d00031100c0c1041100c8114501c1c89610021f074052042000541c0204080c004108c90221842e50031803107510180c0d8240661041c2100c12625040115002800b00350b0501420000394411b450f000b01d5540b281d28059045501d425103252550840110801c02c43e0300350f170282e1b4410159204020707146449101484c14a0726965003d823400c54000b054110124ac085141005040600242a081600b20205001411680a48079100d0f400740d449800403500740441100f1001d00c0070128200044d60030451a0594148001c024403681000d502c045100340c18090980480c25441411250382090018021003a01d08003a2409484090803144141450114a4408118044201ca510061040d90b2207035008450003c4030040208481c410350845c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942413687 1250 942412437 942412453
    0xe100503061315090c030b01050d15090e0a050c0d0b0612011118030c090402090115090911040f061e270303020309031002070206161509030c0b0105010f081f08 70
    0x41044032010060320307040013061003882902e1000384d0955202d40c3d201c0740064400c1040c5070030340d501a80056200880c01d10410b80b101c1d500d129400c1500c0d0700215500254100982d04c00070010f04006601c17814030155504801c040c0f8685488441901c014605401411140d40050b201748080d03005501d03c40d00d60b03500c0c5c0c1d219802c020b50311714000b5404c00058028030070421802500d10703201b800c1c1c178481c0c0d60080c5041426800c1c83e65111541145c184a0810b200c4041c00103c2e80038014010846858021600c15440c0c0b440c0142c51600803c0d83d9210a040c030110241c03c0704108002e40121075260007038101043c3c003035042c54048115010128000301074141e11038021040541c044010100310702e04500300c515401c12400e010080740304030785001b035110108000503800c07030201d502c2d440840c034001c3d070500e583c981620407207100340c0345005012000100d104105500304007815100c180900340a18007016000d43c0854041c10100300640136090f191014540c40c40c074140c054410f44040c042000942d0046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942414937 1250 942413687 942413711
    0x203070c0e1009140402100215010b0d2f070201090b0a08010905060f030304030b0a02220302090a0e060406090804122001050f03040803040204090803071e0e1005030613 74
    0x101c44142c58140d101910300c200001c030801c050003407410341400c021400600e07480710b03820420101f40a6210354154026144100c20343c10f090501e0a008085106081b030390f407140180b6050841302c50540480d0458282d101e15103102c82d10b40c080360a800709030034410382c0e01c919074001600c3c403202552103d0038540b00010f00c202c4d640d0380400704504071a40c66200b445030351101c0703040010003006548540d4055200303000410100e00300c2780d40260008600d540040c40e000062010342c40c04a01d03195951242001410b0800860400c0d8507080e83c0039200c000c08001040307450103070a4a8182c0034102030311032500c6400075803d01c102682101c00130149401c0880c1000005d180640b1190482055000c030010680d40004d12940103104461b030f21842c0048291840c0d0712070f0380b0440160070180c016a00b0903640d9a40200080e47c00300190b01076001c0e5215403680115582510351104c421042c00020001941c41c40482500da0f4003140050100030309100d600c954070304011864007695548900340c040c0c201403001e950 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942416187 1250 942414937 942414959
    0x6050c0702010e03120d020d020d06151107030807020603190e0a020906090c030f250908010c0306081b010309080d09020111010c0905040504062004090f060305060a0c0203070c 77
    0x1000e8400c0e01c81841d9105540100f580f520500000303914151002c01c004042903101e507000b00100e21031030710010b04095103054910225140d07a0422041601480100d03811103400c02500003002c1e83e61801071004034195500c0c0c1c0060b0290b081e0080c002c04020010510900c8c0c464281010300f4a0520100180c180c2c1d100259614842142d05070f000c1c14018001c00e10342d00b46032102510490358103203464036507120a204030035400030040421020402200406844a03070a01d0b010003d1a40c0707aa408401a040c0381e50300e0300311240c0f1031807036061515103002003086890202d114401884604005103040240400580181101003001044020000307140d03003010041d503111400c0b150003aa9100c036200a4118030b1400c0310f2041016a0120f81e1101c400c00143c40c0c2034011550042c4240b6011410b803000400542180111100e074298400c4089002e12407405a07108243e5003d44408081c448240346485040d00c0700005007049040a868402d40032020f4000c004941c0b1141d440128441425039420750100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942417437 1250 942416187 942416197
    0x90f0c050a06051204080304020102120d1d0c010f050a03020f0d0207110d380406060e090d2c1207080c0904030225080706110d020105010f090b0d06050c 67
    0x700c00c41000c000811814820400d072290543c404610008a45540c0c8401400360001401203045202d0345030b08105100100e03024111280445002003400261050a0782d80c20404000651a80d4044c0b000145203a92200071206045501d050042e40c0d421200c03000c5010b071050b0031410180c0440051880b40440381d650040a105008041070200d6007041c500300302a81009a4010700458a00c903d0380061190140c1f0150424140301c03c00ca20407a12a030b40107181001c11101035624a0b82d400c0e0411240140f0040c29501c540620090051a00085c1010f01220451461907440d0300610a140480418401c0202c48800340204407400540740000042da64005500079502d07207000d460908500d03814141003c500440e8107801810800c4104401040c61800c03c81c1000008c0010380c00000f015802440b030000a03241c0c0d503a500e44104100da004600e42903a0251a4045a1500c03004001c0581e80d1010704050381c4880c84c010407840b022000040d0107405111010304100d2400f0203001d4650310040080c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942418687 1250 942417437 942417439
    0x9050703020a0806070921020d030816050a0f030b03010902060403050a171206010e13061508010b1206090c0d140411030624011112040816080d0c0303090f0c05 70
    0x11a03c8000c0c07580c80324010b440e08004a080c0000501c00000c1900404810150484480030b1000f80b64002607104130341e081041d800305a9100c1445220b11404034442001c4810f8142245000b5044000a015089a401800c1016070b07543c46942996029000301010708c1e00142490389464807400c146449181d0310604450209860300000c00c0107a2140a8400c1c13219101c0703900c0c41030381e0783c02c0041d544940881e03489a4081002450840e135540144650b81c003a2060500d12044281c458002504550301a005518008814442402c40070003034100240c0c00b00d0196034284150b1100c414031500f41c002c01000007101424041d44100300c6a80d111101d00c00c80c040c520740505180c0410070315403200002c0e00c0c0c00d818280003003e81d902854000ba1540c00144e4180351046160813680700007418802901207181d402e001c000741c01c202d42e950401107503812a100300c041c9500c8501d404041c40c0d4a122600f1140284105003a4080c10305002ea40100c0d902a0020045040c090180c0380c05a03c92130540511 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942419937 1250 942418687 942418699
    0x1a07080718060e0603130b090f0d020a0c03170c1c1e080a050c07020301090f060c180509071709010e0d030207050c0f0406030510020d060e041110030b040905070302 72
    0x110058241d107984110344240c0c5030050410a10000d10915070300051505000140c8810010005500543d5880c413541c160341c0580340144031450380504200031184a102190300148004012039540f0070190100c945c0142e82580c41608500c149003540101d0b003401b0b50303a010f01600000f5071941d950108036840d00719640c02c102c0c00c0500c0280c10716203000d110050001440d02c0f001a840c081960710145e04501000401800c1032080d0b40000d00f52000440111808000e00304900100421809500c1c0049481e00304011803039500c1403c4d85842e03da42c072410340f00d00c1c148408134a1035401440c1840000e00c0071064607046107400540c00d80a842d800c2980c4520b0b1045024900e62f02c2e1203031080d501402d07404070142075880c1c041010086802c81400442e0707881540c440000001520411101d81d0018490310050f8807400c1c10540c0c142100c80c1c3da03004000c540d043e40100400924a0802d4000e41c1e0411200742c60548500071044000b01142c3c13250b80d0f005442d08a100051040c0024282d0440c2d200703c81f8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942421187 1250 942419937 942419957
    0x20d06021905030f2413060807120816031701030b15092a162906010c0f060905061e09010b061903110f04090f0c0206060d1a070807 58
    0x812503561000312240c0140008200105031109051005d03070121181400c01107060008802c0090741c1c0d000150940700900b9075800701008505010300082c001408034007907203c15040f0070b84940c0d050b441221500c920310070042c50400d0400d030090500300d00c101c4120210341c401c0d613101d01d04100640710946070b5080940d2a0034003400c0a19040003481e11900c0c00711030308054a1040da244420144444c0703c0003802c00401d00c01100300d8a00b5258498205001c1d04907071003001c600242e0410208020300c00308140a4140702000b416981156512400b203031f2102803001041194140400148081e4200922034066441840b042202ca0080326481c417103003240900240d111200b0250885070203407243ca030000014000b5101c9040d11790030000c00a455070401081c00c08a0700340030503040d803211000d6026203002003805c0c84030340810f01c241840d8492605007003141184005019580c0e503401440d039880b5a410400003000c0141c0d2042d800c19a0b00e4501350120181810540640300c2802150720000003000034030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942422437 1250 942421187 942421237
    0xc0b0309150c09040b130203040c180b0f01140909040b011a040302030a0227091b030c090402060d090206030c030405010b0a060f0f170411030c06070c090c0c020d0602 73
    0x340d81c6028140c000c0702185001111024000039141c00645290310100c0303560840b5102e103d60004600c0f461150a0503c406824203007209110780380c48243d08601803500e4900f82040c0c545640b00703030284100342020a84004802c280714518840c1034512a000400a003d010403c140244440e06992596045120b000180c9090764058000c0d0311010794598015240107000d81040b258410030076820040c0302400c07060100c0341d160248c50555100d00300c0da11540443c1417820020343d03c4820a441103000e061000c3c0345000181d4001c0d800f42c8060b1081c580040e040007002429801000c3c550b502a007206c0d1285020701c520b00c00c5410440302540c65500b052410340303003072400003e4541607070603584070f40146107800a000c9413141e50300c011450602caa109081c100c0070708201e0550703200318031aa84103e20b0600190605040000100190340159010300961000a110310111000d1b42c0780d901c400503000765050004c1354400300562010b504488110034840c14016590000d2100c40c00e940c0305d00e07010011201c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942423687 1250 942422437 942422473
    0x1091703030a020c030909010602071a0418050c0d0c0305060a0503070b0304140316050f160b071e0b1e010e130f0c050a060f0201060f032301090c0b0309 67
    0x4408800d03001040041d9001c44168013500501c1c07004400c0b42d04020034040407800b02c0000fa005980540d21005d810804142d4151032499400b5200400300e09092800145036036104007046115011038403400003425000008054400c410744084040c0081c40001c2c40240080c841507a10f20300035004800007040c14100096800102c1d03031004000f51541e40c0302e4844400402400c81d241c2c03000c4c0810040c00d611044440c0301426054082d1028040c04011840050f00d880843c0e140c1188901020b081004510101019500d40c6904a01c0d08803080440162322402074002e03040c0200422849818403010000c001462461900030700c00c40380c041d0340c80714201c09015804031401c00c2000d4100940344000380105a212424601c07405c42e52140301c0d10380000a001142e50f0b005030001901d011a007540180e0b0900440300146280c444141d011070660300c480000c03403d54014101000d220074590a03000303400b54440d403410f030b8009000b00981030315103c0340c110940c02175420140d640b040458001505000c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942424937 1250 942423687 942423719
    0x308040f0e2503201c15290d060311090f0106081602011407030c0f020114010302061b070b0a020d031104060302032a1305061c0b030307021206061f0503040b130218060109 75
    0x40b100501003d841464008050401400c0842e0000381888204244080327400350801441c4110810111201420140080c6c60002000d0703100504d1440010060280c0018039250480304141030300055460080c4268058080000390b010215101c0c0304012000794568802c20024800d03986503081c4980b005401c900781d0303008580040c00110031000410042c03422000400e612404040018920884503034900d050080d544d10505d070081000a058680641c140000d88a0540c81d040421601c070080031005918000d030302840050540c0040810607025080301440589480301e01c0215002e044c1c0d072416001a084244641c1005100e43ca02240700e1503c6000d9030340f500304502100310a07100009105010b000c2c401241a0103000801c02000940c40380daa46614010f00c0344010326282c00c1010910107a95443e0a201d400144440c4442082580c48001c8035002a00101c40d10410b4940d2165040703280c00c6080002e600c4000c5204000991250440261003404241c903298482a80e03032907460303219049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942426187 1250 942424937 942424949
    0x210f090c06070c050306041a09030a021b0a050a0314010f05070203091e03030a09180504030c060c03140f0406060e06010c0602130308040f0e2503201c15 67
    0x300d0450016103051410141c5000742c0552003100c600303a91040441e040c400182d070f05540700b00081c054160b01803070040c03840c0c2c0c00c856943d00a52406286680c020744510410582d580c03000041101d407482541d40301440d8024010042140301059600c2c98507150103074498003489001d50a040c03813200703c282e076031080c0c80c0316910f150046c600e032802e0102000580400201140c0e080c2d840c1038480c0f82103440410103800c01c0502da4840010b202c0c20318500c1c5c5400404a1851000b080c14a030030000025446940c0721000c4d0703400308000c5130404c8001d07400c0d00945180c202a80360b0030b40240812124802c44449039000d00d0041404100282d20380b462009109401c4a07440cbc086844142c0540004050b50700624210404071a030707a14845c0c40f91b94910581d170140d0b004000351204101d0a000c100c4554000da504519101413070200f041144011148000c01d141c4200241540c4007141c9841481d00000c0c2c0b60701c0d1641485481c2e64410b5054520794000c0b03020f0b1155141480e114600764034070070103110304040e605 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942427437 1250 942426187 942426193
    0x3071106040f03260a030209010306080313051203070f060219081005061c0507030204150219110319050106080f0609120c0304090606020106141f0f0212210f09 70
    0x800c3d41c6444070813056100301000003840c0340420f00808a81c0a010f8903100e0500d54000d80ea8014a030300060954440790401000d6400810880c0503d8040c4803045003110000d0320105046080b107002a400d500079001c01030301c07000c910070320481001000e07070040201c8040010803240f00800c500302202c80140454400020141840c400c1c8050310300940941080ca0708615004103802c07a15064070265074040d504180801e4010400b0700085807076180a14054165200900c07540c4081e40c5005d0305110352500241240d030716006800410703201803180210b0038125030310625409041b883c0040c001c00342c138840d0450601a121110f400e1510100b40340f8020341d103940092021200da1400c0c091513070702001c64003005202c10000040e0f0301d031041c0558070003800d858000040d5a440c0841c806000c5102100e401d10440304460b0000148281d4180614501341914100c031b1204d440580a901e040d0450f900c42003901808509103007100b0228149201a9960030350303001c0580c42c1c8400c0c130140d04205a03038209917070f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942428687 1250 942427437 942427439
    0xa06030b060d151a03090a03030b0d050303041115040e1503070e040f051207031e21020c0c031f0905071703180105090d03031a030d0203071106040f 65
    0x91103508800361030300c0c00400481c94902810040401c9600c064810074050b14035503002c000d411400054028140c00001842d80746141516019488006005004040c580e44c0e01c262040b5440d08109003e4841d80401180d036207041500b05424074121003d100ba10840440714a243c1d8100c00300c050707a048440042c0b52001517102e641440a80490030030304170360144078400001031282c9403025074500640c02956103800c80171080c240141401198074003618030810822007035000a5021000d16135164540103e0801d091190404482040310a11000180380940c1d55000202e815a0300815061104c0c03001c8400000d4206c090641303845002003051301c00110a1000c2a510344903800c94403d051044054941580d1a4445064410b0044d207000c581343d88082980084880c00218402003131809003091810040765800165811194044c010100361726a48502006da46207d10042000d2004003a21840e00321840020f544c0d401000b4140c4101c800200000424106a411101078030000c00300385d4001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942429937 1250 942428687 942428699
    0x1b010e0d08090d06020a11010e0d050306010f110f01020c16030c0e0a0e1225151a150c060a14070507050c0301141005151602180a0203011d060a 63
    0x40c2c109030081500f0140c0421290300040180c0300801803c0b486072600f0035000341061980e800c480010700b500700582d00a0240e03524098102c4d040d2035004d8400d103400c188000d1503280803500c58540c24403010440c45500b1800950a0064002c0d156504003003040700c1010919030001880c5841d01c0c40042c040d407000840c280110561481c00365409145080c0109501c4070740b084444c5003141da29440903102c0d90200d0280c40c1c41a0310069104034060b01000e0071543c0129844a2010385020034950408564030004418000c500d0020303680304110042042160b161441c480c0b0803140d000d8842d142141c02641d001a850b52041d114060044541d2410b00d181da43d035900b000c0e5156400101c0a885500c9104a180110390b400d00031390b4444171030035890400c0f5042210045212034103607000507104003110590002441204822381d1180c444402d005c080c0d010650002c1ba140c020700c80481c41420840c01e04200c035150440c1c0042d412144812400821616200c0c1d802001c023000351441070344407a10315002c000d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942431187 1250 942429937 942429953
    0x306090a20070303140c18040e0c06040902041401020703030f0c02210a0314121f050603092506210f06090b030d0801030b180a0c081b010e0d 62
    0x50304034a074079603007054490201d5480064108090480c0007a40750007080c0b801020320200590445108444281015840020031a400105442c040c0c0200d560b480d000b01080410024036001c060080e0180d55100d46603240080654098001c2e8a44080070200c1c503005944005847d4003100c0c4c00d0380c0e400c03810300c00e042011200f4a0a02d10181c1e44021070341802880c80d4400b20900710300d0500301004188008047c640508016003050408610b441e01380036072410f0104400000368080d4010030320703100490001034006001291508101d412440c00b000b0081c0e000030004e488517940d8400e828071400101c07507156010900005000b0040021503041a0300509101030789181550182034030042507060640d80e2040842d9455445102c0550311038024024906081c441c0c1100c4020514081030b03550306584508100c810040d1402142000c01e009a040011060002da5462603000c40d80e915255540c41d070b09691940500c1480b1310302103840810a0140d8004c01d003040303940c040500141e040302865290016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942432437 1250 942431187 942431201
    0xa0e060a12081306020327013e03040e100f06050306010903150b090a050c031308090d0303060512060403020606190902070c0608010e010506040e060f12071a0306090a 73
    0x1a4002c020300500072440b40901c045405840254020f5803690b0074010826400a520240f03a0600140013400c00d480b668020403101d01091000102c0003500d100c1c0d0030355860100d401e032a49011842000b003da19044001c8008c00880740c804c4020101921190307218800f201d090f1041100720480c5c040c08014242c00380020310340c0203105040141141c1c0e92604c8504600c00c83c1c5251404a655560f200b0a2034917154003000d0300a000d01d0800c0102e480c02252961051002800c90701d181c4002d80010b204011441c000c07140b0075900030309a50010388686c9400b4010740b8041c01110310459415825401c00040019124807458140d4014907403a15800c042c480b40c1c010180280640915400000c5117030446130008014a500c101441022039240110007454950107800412800c600c03100100202e40e03610058074191020000c2800c1983c0715040002c1d9450b00c80c40009400c40201031130124801400f041c0001101c4103581c0855481c0030f552001c0c003540c44115109030303100c03150101080c1070507000d901a031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942433687 1250 942432437 942432443
    0x1b0b0c0d24091e020f0c3d1e021c0213032d2d030801230a0b0a02010b011d0603070c050a0b04050d0f200a0b10090f051522020f07020a0e060a12 63
    0x152003c900c1c0d91401c050990a08034050751270300080d940080c00702202d908090400040d00031418030955854450080001d440064840b5a0032401d9458180300750100000740d13404441b00c2240c200103481c1802080602d0382c7d440c42c040741c3d4412040c080481c1800c8425200c2ea15540e0003810b42e09103500e070180c41030b4124040107602c228400340c0e0b4090311003480c40805489030003419615118034240007429a201208820704005402180f0040720070b0002c0050740409003151055142d0b0769580b000c644a103900c40700a043d604c68520103205000c00c0f0f108585c0514000c0003a10b03500340d0740e0340b4251038003008602c1800008010313001c56203031000300c0c00b0f0800b0300000d0384081e10b502803072030b880c0c415031303100c0984200c240e01d40e070780d074007000b0030541e6100341281400107038001e0011b40b401311800007160090198050151242c0c543e100305150340300c0390100000b510700070110340342c001104105441d070f0010f145c100e004020048000c203441d40b0001100d44520707002081035003100d0a1001c0c07441c2c0103011a00031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942434937 1250 942433687 942433691
    0x15050405390c0304082b0302221d220f05100c021f0614010e010e03010e101503080702011b0b0c0d24091e020f0c3d 51
    0x103281e0440340c21004015403004803000f1903d803800c02072054140080001d036405203903c10414580101c43d42c20700092103000034280161940382046140f00e4142c1c071544542c01c950560b11020034108241d0200414880051006041c1c0d551001644814146003001030500f101c3c618196030002100000f0090107540714005840c814509840b21000f0740b00d4129450003d82c20009858038802d010000129100c00841c800b404442c0ca0004c0c010400540000b44504014403001084140e0340200000d20304400c000d002000425044003010340c07100f00601c0c0c10400c0c50305245480cbca104138460441c0d8156031b0001002c03840c0508030341c0103540b12440030400c02051411089a440401c4034880218401d0200981c120b135110b044409800880e4641c02c0d0211402079a40445403284d1860300d00d50f000c2d294040300c001807550710100743c84074a0b03c151000c0840305000040070b40d4a102c805011301407241170b60044500c401d0070318500e410b07842e8048803c482440c8900300f100b0a080280c2280c038200400b58040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942436187 1250 942434937 942435031
    0x2030c040c05070f0b0f160e0f0f09010b3703050417030a0b0f0105070507030314040905090c040e0d05120c1c0c0e030f070e09070e01060315050405 65
    0x30321482c2c021420303080e11018005410800c00340320008840c1d5007c450000c1c6040340c0b40079094090200406011064068601d2424800f21340c0c079040c2100c5c1e02407070001d0241445680d0f03444044c4455000b1803034048a01000c0c00800740f203415a003a800350001840845500038140494203c00034000104151034407025031440e00c5080810000450090701564000f0070b040031036805022000090111042c1000020050040820808200c0784181c3c0e50515080c1544401e8441480c01d5014030b400c44615030746002c041c001c40c4480081d050f8500d00d8290b5040c0014494801010b85400d0381e0b0001401084007000982c052443c1e144602c2c0c0c1c09401c800050703007098403c1701d40501343c0c000002d038001e000c2c0d42c4901da41103050b0008500140aa81200103000c542192030042c0c2d11842d807807081d030420807459000306030b040c4010b002c8200507040b0211100d15543c1d440500902070440d074210508820340655001c5120704003800ba603441604291a02021007510b000c40080c107001080342280101ba10100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942437437 1250 942436187 942436193
    0x71a090a0804080d02070e0103080702120c0a060e100309030f050310030b01030803180c18040c0e070513080102040b031612062c060907180e07121802030c040c0507 72
    0x503201503c100c0c0024403c404200c20044d00d459059003050600400000c010000140c49104540059606484c90300000d56042902d615001e0000580d0354045000280404d0300c031f40c4900060309401c1c080710440c03880100c3c004150211045401e0180004d5072000135210801d00a100858001d0700008130589055a40c0e1582d0359070308020b030022145614004107100503882d20300c9440501d1b20340c100c0644020ac0311400001d44031406076420620304d20286000806000a01408800900b5100d0180403030786400f040042840d4400e4142c1400c04d6055a008034017000140b081e01c0c00e8850308058a491074644698507298072103090143c004124441c80140c0c8100401d008040c01072001c808840386948502000e45040700e45006050310b554622400c210b001ea0358840c4187d00001e66050030800c4027204410711224521036009054840d00070800e000300950311080814034000408004c000100306083c510038214005030020798190301c2103c50821928141d80f011042c00c240d030030070f40c0c070f840a565 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942438687 1250 942437437 942437453
    0x203060f16110a06050705030601030b01090b0a0e0406050d0609140a02011d0d050d030501050f0d110d02060d0c3506040c0203091e010f170c1c02070507090c05071a090a 74
    0x360300400047c0044280304480d6054010840c00040900301409002c1c00c055003901035001c1c01202da030412003201e8000b60607860381e80c400005130902a02c4100e43c001e150600c40c000e03140b04a02160300b1491034140d0400d415002c919155403503416510048600c0b4040100c0402c0f802505401352300490999401d00014010841c20324001c8031500c01080d158034040800c01520000c0c10198001c99500b00c80a000903403880000588d05000c4612003000d40042c00401c1d00e3b4003403200c2c4028410f2909040042d0240c01c101e400700c0307a0805985840c00d03c2c101d14400343d02100c0c030112026900742030501142c503a00c2c041d0002c4400d000144112401e10704044c0c0004d102c0c001d0052003004d04100b0303041c00380155a204601580d5480181049036520038859081280e824000b45000901d680215640c5049601100000c8088001c44001c3d91604604e084ca02d481c0c510720700c5400602ca00c1c040155001a00440c165500f85400c142245e0781940d126582e011404001018140180135003004140010209 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942439937 1250 942438687 942438691
    0x110c0d030e030d020c0f03070605030609040804030c0909020a0b0c0d11100c113703021f0b0a05040513020613030f050f010608011503030f02070f080a0203060f16110a0605 75
    0x1c0c0d008007a6410045c0070b000c0c07030001182c81c3c640070303420240c0280100d942200840380c000d401641d50201658032801d1014680c0113941000780054814100040c03c003190b50481547d0328022601c00088590f182000166440b0b01c1e200482960000300140c0e940380c0c0100755071400a16000203132518680c0080310704045070201c0c1c400f0008500031841e60080a01c08110100c0d41041042043e128221444551000300d05d5640140d00c2c2041103a102d001050b10a00075a2000e80d404031003181001c04850454014120b410140c9010310000400010540f515000703040c0190402d0021308a40401602031040c41da00054142035441e100040c00030026500881c402d1120f40508081c0084581d00c501490035501141c2c8051510381c1003450300c17400440303844489003c0780c0d41824424000468518141e040100ca544944120310300c2d540001200c050104110903510b10071400d8030307520b0b0b680308001d81d100341c0e040d1211103420910b61001206680200d13144a000720841d0202e5140c3c0e5500e58802040d81c1d02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942441187 1250 942439937 942439963
    0x5040219080f06060f01020a17120c180406030305030703150e092b0e12101b031808092b0f0303050f04030804150f020705030403020f01110c0d030e03 66
    0x100758030010042d8024003460780c00203421502e1401704011000000d680f415207010141a40c2d43c41100c2900b01c4429804071641004024041c01c5549000d20601085420404000201c0500526029414541480344070141d942c592942c038110703110244118000c2c0b4140340c007610044205c607000309109803641d585a108443d410014800b642e80100c0da800c04010342e006118503000c2100101941582100604a000d901524064a4001c03607486d4903262500358424010013901e801d0600c0e03060304a0000b90740c1840d0031602d0030300802c0c11025140c10354101c1c001000e8820300c1c0500c0400206e01d040185807100107001c000303519400c20b640e02c40340d40601144904844001320f00c0c0c0035004040e0140105944030321142e00340c1c0401d1804c1e4078094a2803000400081c10301e0168000411001c1c1d46078403201d0041c40d003040441d210141450429940e621600041c1d20442c941032003170b60386600c038101984403c11250080c02c105030a5500740085081a140d04406001c04a80a0455514200221502000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942442437 1250 942441187 942441193
    0xb030405011505090705042102190611030408030f0904061d1012030f0e030f03070b1906210203010603080c1c14071e0605010303110c061305040504021908 68
    0x940d41c2c1841c80c071145580e00c0316004d4401101040081500300090b030342212100e450741480e000d4104404003d00080c1c00c0c0080d1f0200450420b031202c04520401300003550300c2500c50350000250b840c0116900d01407845105000d41c41004214100c250f03000250040030300160000c01c0880c0c07074410340e4400d0b400d003198030354001114204204550781d0505840c1c00808820301049100f003000e071001007011515540920174040a016200c02645040004642c605004070950b034503040b1341d03c2c180d0f008003400e4800207040d84c0362168640380c410103845042e048a01c1510b811521800c2e11407054044d040c010026a8103550340e110000200781100014007440d62040060903449504000314072054418212007000c002541d030302d68900400e44400c5540460308409900c03080f40e40444080d24000b0200001066142032100010825811042002080c2d6901e030642d005900d46105025031801803d803d01c005801c10001003246042c50783c02240c0003070001e40f10201d0fa000300c119058100c18654403511041c0c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942443687 1250 942442437 942442451
    0x18030f08120903031501050a080a02070f05120a0905040c0804030f02030c060103081b010b01052203051006030b0106080906042018061806061e131d07021c05030703060b03040501 78
    0x50742c1702c001241c0c408090030007900700f41c1c180300c0003084464020521303150940d0015048080c0501040300150b4294007504880e002e0180402d946072680082000e00041014980c010446180500543c45c025910399128071055550340c404464442403c0b045405602040040000351a800d01c809406140030f80091a900d420300c0754030f1501c0d000c5a40701c140c01030340740555011a13682c0c0700b0b045400b410000050407030007902404116180380e0141d400208a4403a0b04020701a0318030a80111040b00d000740142082a82e8594095070310750011210358080703030803040000d400204a515544a0070a141e800448026185c0d800f040391190014096003124800404014041c40c14100c44060501d02c421101503c0c24514041a4240101803070a900056510075084a1150900075154000013003021498020356070101c20132410703175401d080c41514441c0000140c1c610300000c1d1030040104d030b501d090355401c60614412212a0406003000c010181c95400000c5c0410074417001d580158014000000c00f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942444937 1250 942443687 942443701
    0xc060c09090a1503110a0902070c0302040b0d031e091e0e07260a0908120912030c120403090f140301050901111c230402030c0118030f0812090303 64
    0x41000900510b4414200f0b42000c070f120351000f0a0000b2643e103c0180b04500e90000009222050203401504030684007051010031b1003100c04a86003168020b840400090505c1d400b8450241d09201002c3d011490701120300f458000a60750780440005140741c299034194499a140700002125541080403600034401032090311070030715210340c024840e41040603071304001c3c402c40444601c4101d05246085900000984e090741140c00c000e00c0198000c810583d541e13240300c04243e082c0340665450455125200b0b018500c3c045140c11a03002c2d00c40d5054060030308036007994515100d1001003046040200c644000141540d00081d0074028001009500008546000a042c00c44000812200d426810004220402c40a110454001d00348494008601458040b08140a8411060702c601c50b40668503c8216440d160400390740140c0c801c50685507411603c400444604080c9090311950a0004904000040c581c3c41c40078002482001c90303500b030002010344820181c20440d80300b200350300000100404c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942446043 1106 942444937 942444949
    0x60703120c021917190f09140f06070c210203011a0d0308100b0f03091b0f01031e05070e01090806040c05040c02030705011e06081902150c060c09 64
    0x188840301c003001b804072481c0030306240001c0300c070030010506154000d0602c0c406280189a003c4071162401086217540c4084811503196140440c001500070441844207100c00d1000d000f0b1440d41040c4c0189400d407401d5181103004140007a40c100b616544441e54103c22a4040c58011265039550118490503090b40c1c101c5d6284240200f0303400820280607004502c6441050140e03140e40100c0c4c26055039803541c07042c0b21640408642c440700180c2d442a80709030703000c4d01006103640b20301803650101411224181c494a00146022050341420b50b00400c420005200b03520090a132880d260321040940040b50049a105644130074102480c2c0340f081040c0c42504d44c1040c0208000040b4401c0140002c2c90210580441820600009040c50010489074000769440c02e4901c0300c4042582044015a20110803460002080c070003001262020060300d4814540e4400b02c99a40c1d00003070822903 = true := by decide +kernel

theorem cover : BRFrame.Cov 942266187 942446043 := by
  have h0 := BRFrame.cov_init 942266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942266187 ≤ n) (h2 : n < 942446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
