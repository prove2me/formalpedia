-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3878
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:35.612852+00:00
-- url     : https://prove2.me/submissions/71507e41-f5ec-43a7-be31-83c8ec67f081

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 697302158 ≤ n < 697482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 697303408 1250 697302158 697302181
    0x1602030d05010906050a09180314040e07020a020a1401090501120f02040807050103110f04050607060f050a0912020304030201051206041e05100f0e0612030d0603031709120d05 77
    0x11403005100c2031500000088a00c040e500c44d80844038203981d120702151350b4a0711041201c080c8086400140a03040d072101c0003910a8a07407400c1c1001d00c150075810562940d000b03141d04001102c5030000750740041c1c400c00c11361a001c117064005180200410308400b0070000020150840d5110700c0781400301c244001140740d00660003916440c642004115100d55840c200e003651740c0c005124082c0404d113060707080940c900030306088850311044c03140c0d40d6107018540400d0150b190b001983c1520203503500c00310111f54841c0760141a00030040f5100220b040c5019040c541042900d84446000350342c03003004104010b0760060142d88260a03c0c0c10360324030b60b55809001c140500031780c0c00100340c0507514507101c050100036a0701140c00b802204119060780c54842030044141d8205d401013a0100140c400050340c03602d441103600d0b07210b800030f505a9042001402280042d0340982c0c2045000c5044000010741038041d183c015a0300091240080c2401c00100340c9044c0580726a0781c21002664688002441c800042c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 697304658 1250 697303408 697303417
    0xb0906030a030e13140115020d020a14100204031b060509011205040f02030304060f030f0c0e0402071502130e0a051005010809031326010e25030c080c030f03070b160203 74
    0x940b04e040c401c3c143e40c680910001402406500c2c0011000001815035a00c0011000b80030011a0000c0c5091003450300c42d486810135018100345544207a100020720f56031140068802103120380031030141c0e1113102071245045800b40d0004800c0003020b024041941e83d0000d0380c00c5c2d1202c80f000c1c0c0003d51761214202415510107040c4040d405100000e80041d02d15031062034003080d1403050b40c04105800ca01851401a555151945d1001950041d4150322929282e40240300d200c1c4140d43d80100e40719441046026a00140d0a141e96803140344000c01c10001075001141d0301c121041d60411842c0f0307010790140c1b84c410a5016881c10411001d00240b0b502e02c0400880d900c1404281c03d8000b160740d1590340c420502c0c0c190780c11040d01a40070491fa20b2180d13050081f100c01c20109001350404142d50454a8030014114544803510204120000046480048240050240300700038000c8180401e003807601e408140c0c000219254401c0000201044110080c3c0c2d40000710134000e45d85120080104074558040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 697305908 1250 697304658 697304689
    0x801020a050903100b03060403030e031201091b03021315021e070303030c020a12140d140103060605090f0406020a03020702060c0a03081f0e0406060320040b0906030a030e 75
    0x100180801266030804068416000c08038112400c0c1c003004c20042c0d050759000285d031501130380500045030000b4001c0d0818802d403440c2c0803c40781000000d00e0724100069007a40189a4680c0d00c5480900e0130080b03041107520040d0741d04056140010490301603174001c4441c464014556071031480305005034424022200030002005414a1141982800c41d4440500d484100d01080c60301703040b00b00c2180041844e0075116003104540e00700e802c0316102a58100c0543c0c443c2d440c8c448041202c018015034030b02c00c000b02001402440c2c0c44540c1949004411115181c2100c0e20601c1554100000c02080460a03076003e588024051384070181040207070007074002c1c0c6200030340c008c0340800e040b5800030340003a54074682030083c1d80d00c900a850b0743d80d212182c00c03115810044a620841c1d400d004a0b904a02855080381c0b11b16070001d251640c7e40c68030b041c1160306400c1d0824107149902c0704000d900e424000d0381403c2000712110415807c0c60400282d0702c28406400a0a100f04c03107030f01030080d07507412901035107608 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 697307158 1250 697305908 697305911
    0xf0903080c0a1506080106090905030901180b0a022404080403200d0813060516020f0a170303010810110301050906180c0904180b010e0a060b040b09030d030b030304050d06060801 78
    0x35403400610f002d403110740a203501640c604100000c080e02d40340a00e403103843c0c10101841c5044440b4004440c0300d80380303050f40100d002700503500103114004080108010091030b0f02500030300103401b02661003a05a07140300c146181002c800d20010503050340407035084a0703110350060b5400b00d241c1d40b5180301110242109a001001c9003c10041c0504580284140041d405180c000e1035160f540c02d440318000c0410001c0f185042ca0b000e5001424941000b01060b40c0040c0400e40f010394402c8940d507124000191a0b040341c00102c010040010104449440c1c44025031040c0300b03c10040000203558041403066504c502030390b0002c5601c1c2d45030580c850000b000007080000962501c001099a25844005868022450b145610005010190740c050250f0741c030038048207c9900c0c01e901d0001d0004082c000e801480d0b90b644000510500a80080000b03021304c40b849500c8414400c10181484100c3e084a42458201110000c0ba640c011080700c041d10021141070300040010b0038080020004d0360040c240c1503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 697308408 1250 697307158 697307183
    0x6030319090f030f11010804080301090b0a080105150312090618040f0f0b031203040c0603021e0712080610210e1633050306121b0306070f0903080c0a 66
    0x5421001c61300c100d405840902090000d0a0045501d80310407240034002403010300040c0103500160f0060f544050000702902a100e1f00d4031192821a02c1c2a10743d05104401424014003904013030040004000440180301e0402180e0310224032940300da1404218140c100900403500c0396034503404690a84d010190070010030380c62580307480040c01d03445240344c0b0a10030401900a83d051000032244a07980c066410005c440c80d007a81900690040026880505201c4a4103915110001c0c040c101850182003c045225003102c0098440800580024010190802200061600a075400a03482503d50b10010121140b4002400030200c09035030f404c0074081c219000ba00301b08c011201000341e408140480d4141c1030a01100c00c5801000101c440d00300d400c0800c1699102d0007040a545e11283c040e040d00c032804202e80100b41802d060180c50303a06444030200241c400e0404010055002156044c410301145802401601e20889407000624a000000310b0000710702080c002100c3c1e40d5130002202828 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 697309658 1250 697308408 697308413
    0x8060906041b020d030b120c040903170c1201050f21100e03030105040e070303022a0603130506330a15050403050d0c0809090907180f05090606030319090f03 69
    0x84d441109000741c0003070705014010700701d40f80c03e9546c03814044086000b891440001014000681078014090b401d010b0600500c4138600329110780300384103a54421500d0b40c0c841406104455052042c0c0041e07008010140d82a0100e48a8001003840750b0840340d00d022100808403002440c00c0c1d445020360084500f05046c442c103c039000405141a0307081203030107004085840b41400e036284024070000c0c00503400318002d8064000300380c425905210151040000c0c48640c0740202e9100d40c4103441ca00765000020300322034188001440001e401c0544002c440d441441c000d000112642040002c590308100088219030841e503640400760000c094064480b40e040940410143c02500f2a101c140ca030360144c11580020b407441021850306450707009283d5810030000303400b80008803c00500c8590a88a044400700d5072201c038041783d540e1140700850100320740b10030864003810713180041c0c054451580090b0071711000e583d001c002d44000c0801c0960200905048803001c56038080a640891200520305c00c0101c10b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 697310908 1250 697309658 697309663
    0xb03060f12100f271b0f1202041d0705060a020f0109060504120924110a050303150603060607020d15111b0f0705120a05060a0f150608060906041b02 65
    0x601d4034000c00100062102034013280d03a224180c182018000281165400000f20403600310a01964207070036008502d0f0721654648070440050700b00a402840d104080021860140903804820115400000d544a4a045038582d0b500c500c0c01114401d0b000414200700203031080140f95802c1e46944003e00010f802400c0444c020142981c05840c00390310824002c0c021130140c280c9408849503140480d00e580e40304041001000024401c080804c000e10380599508a410002c0300140790041024590b42e0a2415042d025401940400ca0040c1000d104121159441c403080d00c07101178054902030036040d59441c001c010b180c06031300801c7d11203143c04040c2c0c072401d8407003000d001d4213000811624800f41c80411400d03940c2000030440c080300d41c4052410300480c103003081a02ca40340e0428040f00c2d860100b1783c1d5842c4c01c05c074080764403030030305a6030310501d00d001662400b0306070280e59076191141e19181803032401045c0c0ca0000b4199800b0300d03159400306446464070344c002c01440c40038000750300c0541d410440094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 697312158 1250 697310908 697310921
    0x9140a170a020c091f0501050a0f0315030203100506040c0315090209121b0310020301140d150e0f0c01090305061308160305090a0f0f03030309080903031912060b03060f1210 76
    0x4805000d52100480c80f540154115807401000340c4465084118ac02e01c11405854000000d40d1140103c440001c0142c03000c000e4041da83c880c020001c80c50340340c18400d0004913104551a0010542007a0001c00b40c601c01059403000c2c1d513600b48015950700f03065400b2610b030301c800c60481e07483c43c03040c82c4044802c0c1242e0b188040c000070003102561010700240d4821801ea00080c05008019803000031240000e08d00b0794001c9089903c1011905081c40141d5203c10480c1c003860010f0303a0b11b410054010441000030701104031201801d09258800d40d05544907141c1d9a00003d06603014169003070281000d005518040d1004808520a0b141c0c2c4503050745402042d9820502a19008040140e00812070444038403089041c4c4220704400385d0000c0c86c1d620210302424810206464000d0200320101c0c1075101840113081c243c1c80c103c1c01d249500c050590080c81e11064031841c00e181c0345440c1040c00406c840a0880707070428030880b030449a404400b0300103807104c041103003903a11a22900300390b808094800d40205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 697313408 1250 697312158 697312201
    0x612060b120f0f0c03010b03070e060406090f33051228050c0a0c020105250b010611071403152d040209060d0c1809140a170a020c09 58
    0x30000d6101c4490030f4003804426601c00048050900052015040c202c028591141080c0741c0171440c0e107554400b042840d80243c02580008071240300501609102e054200d008148481050b40010030900c1400c03088585140d016107007808a01c0da4468042c42402525031280b421703a0280740504080b451941c02968400c210705400380740b1501e03c07000301820710401d0304c129450121a854041d61000860310788601d1101281800b8052201812016641400c51056000c0c00301280782c5103180d003420240301070140e00c1001004142003001c8040b1001048010855018104250aa0038900006400c1140140501707882c6030101080041c00b5003289080008015680c00f40d402c41448414490150201100c002e5000300030000415001e0074801d80c2040098040c8055404e6551640c3c250340d80d5003800001070416586901c003000c00c2c00089414150100400e50041081d04e09076651481c406140442c0c0400c00c0d00049644020f25009009800e410903000700401032601c0c0c402c1d224840710368000501d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 697314658 1250 697313408 697313431
    0x30c0b12010603140f18101a0d1109100e0a050709050a031a0604021c0903090e1e0a0b0d030504090c0306060504120201021011091e06040612060b12 65
    0xa80a010f807240d000a5400180450010f50790151050007121000c0e20309402c46d00600880210300005000071180c07503205182c04121010040c00003800074000000d8a0302c40c110407007200d80082c2002c410b00c0112001582ca11030a84c0d602883e00e400f40383d40da801011820300711030410844003290b42c4014824011621040013981c0c9039800e00030501c04c00e0000a04010904070f07040380d90961500c8007170340b09000404c054503110001c0a50244411404512071251f51145000020107400c0261080684030b10131002d2a00d141860b400040e1000000d4050814210207001c1501c00e4041e400004400b00003400c1014122030924008080b5445031041c1c660951070040c3d08180d2504c00d0240c2801c4403003da5507541071905042d65400d00c3c808010b000c074103510a031a204800d440590059411504100ea95140c030780c00b4000900c561a46002c2803006140d02900d030314000ca03511102a2010398243d4138011000c1d00d03d01001100804040d0803070003510382d012405810001642c034201348a4800300b0741 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 697315908 1250 697314658 697314661
    0x13140315040618050a23250b0f04030b010803090913020a08071503050a140711070807060503010905060a06143103031b02030d03112a25030615030c0b12 67
    0x8846d03a15241c5034030741c9000c0d402c2040500e220002502d00c030b40030040b0b603d15101c2c001c1d6890007158034640c02100c81e6020f01030041000c0050081c1944818018881e00c00074629110302d80000403982500103011058924000e01c581d400d54446001480240140c1c1040b18a41a00d40c00c3c040720121341c00e01c5100001c3d044c600040c543c0c00705805050804010481d18050980784c1c0c51060310364106003403501762944140080051013020420058006002c00c3c0c4800d5643d5051a4881058800c001c0002d40580b13030131402007000b2a40145084602d2840800382500c0f000001040c4040d43c4580001c0c503400ca00303856030007004241411005003145c0c4280c403102c00e188454607070520300703468901d800381d455045045040d192600035000384000d0b0a00c821818a4500b4084c28060403c05406c4200c00043d400e044000003424108080e5079200c05491394a8041c400c1d158044a0641440c00024900c680b502c503000100b50120885401456010011180468546900300341310b8103c038426150010f10b460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 697317158 1250 697315908 697315943
    0xc0e1b12281d240429061809070308030c07020429010807091503180311060a061215110c0102030708130503181203040b13140315040618050a 62
    0x64046844210b50141103014038103420100383c50800510940d94010702c0411411100c080e01c5d00400c0c680b64070fa0710500c0c281004000d00000c544400e2a01c0f1180745014103200800c4030011b17000301201e500030542c0d5a40d54401200d0280c5000e034080094020742051007901c0040e003611540344260050b901c6206903190a0401101c80840584006011641c07001c01440b640c16140307889270f04220340c0c3c100410455600c059010100001e04020b070000b40106e08070920144017402121b810040c240d0040c41300d14200035071109500ca4040d001000a10303503d004c11104103003500281c0c1a0645100700e00d0302e80401c00600c034042c2d48220f031a02c000580060014100142003030000c0d10007a0844000e50400c05d50030280c2c20181c00c444c003007a60010392300302041e050142c1000100080c00704c424000751035035500020181285c8554101000d80c1da00e2407080b80980d00c0000329000e104014502c4810745480e44d003043c5000b06403410210044010091101d03040c0103000881c06015881001c01400ea00b0f60319 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 697318408 1250 697317158 697317163
    0xc0512030901170a090c0e0609070f050a0507110409030914010201110304060e0a12020709050c0c0a0b0703090c090501060e010216150203160c0e1b12281d 68
    0x141c03115000c100d05960325003010007848107141d8080b007440790010354001c1d80c2d00e400b41075540c00d82c40051303030030b940600b009818140415840e0b08000b0300d0030310140f800c018042c0907045026052110301000b60215821040c0310703160040b040400f102070000c11007481242401040c80d131081c01002582e5400080420413035105209130045c01c80d800034520704545031907072084054501401900882d129921401011604400300f0382e8402c0c5050300148406840c01d071844c0251117000384030042c8402c0038014180d800402240d0031000641c000340864a036a510b0006070700401407a0000350402c0c03c00d60001c5590000c0c1d900042c141d83d140d446019014100b0001260f4450714468021014202e51404001c140031891411002d484680156414241e12007100c4250310071200c0c090b650074000701e030200040f130003011003142c01080a04d010f003018188030b940d8006502c83c0c00149040410400d0004044444240072858105e420201031103400c2000040e0038050700c0c032400c4103c0b07017400b4a004202e202100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 697319658 1250 697318408 697318417
    0x4020a0b0c1c0225030206040302040b030109150b010207050901081903021c09031119091a060c15010b030f070f140a2a0f02100e100c03020d050309060a1113030c051203 74
    0x7e02d03882c0b03403c1c1580d0a00028000a0481d07580640d01c0b0b0038100c0002d6142d1442150f20b000c070540c0019103541c0900024504092940500e002d080031200600096a0110b02c5d81d2441003500101414902c2a1604a180214050a2194134201f11410803d080d900280c80400c5a0246001e240241244810080c209681070b90400c43c0000105007004035203016040340d211050681c0c82c0001c000014404202c0399485030844803c02d030000742091039200507080440d40075214100402e4110302d8020302c0c0e00c00d500006031030541481101c0030181c001c51300c9940b51198403603040e4806910380440150203004c0041c001a2001d00f880d03040c00681c00c101c6052100c08943c1e0f0082c84004480080d030302840341c7c55582c407544a0410032100c8160b00700c0d85914894044e400902d0b81d0711014241c041c00c0080c00c0c201001c41100c1048810400d010b8222800078000e90054003d000c0024107215546c110401ca1180d0403c06e4002c2c0c052580002c1480040711205046031404e55a0311030109803000e105859206 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 697320908 1250 697319658 697319663
    0x11040608070e0105040b210901110a0e2205071403131502090d050714030303060609010f0e0a1e0f0b0307120f0f060302130504020a0b0c1c022503 64
    0x480c000207500280728500915510740c1c10b0400074030341515100c02181a5000388005203485052142c091204880c4101d080e6014079160000c10081c1440d40c40d0142c10311882e0144001c1001900c0b41c0b80e004e40d149218051501c09400410a0309105a0641000303030031704846a00228090703015a1800104000c01c50b4402c808411030300c480d02c00d0340c4c1c0d1074900c850040c1100079001542442200c425032520189001114051001030110914200b820b0030040090500307280203400074000d00200e5250201030307812098003400c2c4140b6041d4294000c5404510001d46194048122000002c1ba42c190806c0d0101c17250050b1100c0140984401cbc03802c072881c449224121002d442040000c25007440303401640c501c6019803402050025000c1003410907201d010310500000d950b45c010410443c81c00d03801c141620340d050f074018040c030300e041d4000a0a1201d20b2003840310200f000260311840d06000c1c85144401c25500940000000b0850402981c48050103601e501c804401040d401c8408a83d032045070803260b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 697322158 1250 697320908 697320917
    0x41803110a11040f020c06040317010f0b0313150c050a0207080604081206010c051005060108180d03020c120d090302060c040305060a110f03310302340602030c01110406 74
    0x100c2c1d00041c00010920001c2c40060503909125000354108280705141c01203009690b4050403602c0c071900c20010801c1a4403c1c1c40550240c542005940c0b610b5081c0c9601601000d1100c0e0088000e04080155185807801c21461901d40058a40c40d140c1100c0904086501c5508481020b9140c149031540c070b10040d41d01902448082c0510010341600d0700c0d0040c0e01017010300d0b080070000c1c540c0d500e444c9800076281e00c0180300c1d52280100107003540d00006180d801104040c0c051624103d0344841d503140c6114030780500400da00000c505040d810104100c1682141880c540340d40e41520621050003050510700c100c0050003400c010134800340610050742e06594105c8003904a0361030b82c1008000409014400e00049803040c84044028208907018607c5046a503202c60307075202e0710721a124084400c440100c0341c0303150005000d40c0440d070300150301509080a01088040142c40c0b005004807400c4002c0f0203000100c62210101e0304035030100283c00074030101d44c0240900e005c06410042c003801030b4003603c0c0c0040e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 697323408 1250 697322158 697322183
    0x219140609010c0210210207060b04091505060105041701020904050a0902090703091b1805180307060203040c0b07030c0506090c0d0807020a09021801120b0a0b0315041803110a 77
    0x185445c0003410f00201d42401e0100200c0803540d0b50b0410902001c0e07040c250030f60f02081e0441444620b01698100c440c0407102000803031003694944400c2000320040d43c03c025a660005905c69000d003080320302510002c049900080d00f45000103000c0e52100180500603428080460301d1032031680120f02c4c0711940100005403a540f117413030490050419050075103220654102c0500394101040e900c2004c2d0081030042049007a1203200c400680ba8054503a0900d01512400c1e10320116001c81640c80f49580300c2030241c0da94855081c0311a03150100c0e00906250580011040300301a000b042c00700707055109a0542d81c0341d69520710420f840d405a84c01003908840c0303d209020001d42c60400503c0300610003084151349a49404008c0220b803c1543d20b0410582c5814010341a50b80205e03102e141d0702541401030080c171034001c000c02c2c801803031032095100035000030000c0b0300f1881c0d801d100d400e407052010304104418540f2091040c12400c00003000d0f4082803942c080c0d0003450b01d02040703003403102d9000582011314 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 697324658 1250 697323408 697323413
    0xf03030e100e09070c06050f01180c020c060f0a14070503071e05101d010509072603120109110703080622090b040201030509210f04030219140609010c 66
    0x10146540207000304107003500e80c2c00940d960301610300c3c00f80030b85079100408000c03203242c48001c640c006020204111018801000f0401c00d114050302000b080881c0030418101c00385090389890700a031702d043da22004c0450702d5103101141314082c180d00d0580d6914514009100b0051000f5445100009015500100213440210b0401e0000e44052035003040c20240240035a2151810081a2501d00e0f15803510b480d00720701c9001406200d181c0e40881d58000f0402420904d42255407101240b00c1c44591644030020b100e001d000042208107550000001c1d80e9581100c440d81302d8511409000b417408092802007801c80704003003007054801650b0b041d2941d4200d500d60108200c0d4200401d00740003610801c41400c2d5002d61003e0045080035407103400017103e1410544009003e0307580c010140c1069030f1125902e034140812200404090f00c5110324116038621300081c28200a108942001c0d4110456408142d110340030a03003504110b035141c20035003e814101008110091003001c410900140642c81060702 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 697325908 1250 697324658 697324669
    0x10507031b110d0c0302012a200a060f2c09040618060902090708160e0d170c1506060a26070c030e0a0e0415150b040f0f03030e 56
    0x40c0c070307004910720052182c1c0750001400000744400116180080400304000b1945c2091401f8003000c003041d113610102843c100183c099417220310000c1e008541c0d10301340d540488220340d1621417141000e090707044904d1b00c600c4007404244041002500242c134400f5a20a5418221841c02c030244800c2058050821074104014600d01e018000741d8000303aa441000e481110248010040c1d01d210742000b1070b0a4109004210071500300500b12002e02a100c41003110240c1c0c41c0510326250b00850901080258400c00881c0c503810310608000c2c9401c9a09900c880360301e400c03402038540441104221290700098038000810b4803400d403211034028500340b0020500b9401340707403000d0180c500440840b00440c9045015440c0740030654600c40480c0c0d611035464281a070054030200120010f07600005070341c0c9400c040c3c400400d0024805480922001a038030040a0140c000d102c41d54060b0902c911030303980360312417190141e1241c4140000e041010030001031180d449407000d1f084036016210503010036000c109200c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 697327158 1250 697325908 697325957
    0x50f0901021e0d0e0409020d02060c010e0d0306080f0f0c01030f0b090f04020a0f051c0206090409052518020703090e0f0406060803070f03112103040c0501050703 71
    0x1410341c0070b6841000c555550011249014451001c002c0c22401c0c08080081c107400303603501400f8080da04005003030000d41c89880740416843d9060f111550344005038082e49004190782007401e9058080d410034241056810303000f000c20740c1c5c088030a03141c5c843c20540071540c0e1150000d030b0304a10740d04107800d9240e0f00c6d80260b002c00e0b50005000710200c0c589090300000b0b103d80c0301c1200c07884200240700d001c2c0019406d1268a000280021001a5455a0400c030002e01d41241300180180c42d004541c907020119203501c001d82e87c4260700a001400300d0310543c0740040e220030b600c00d85100100910112441e558a0000403541214409003034a5020b0180c2d08185001c2c1d40185400c0c0d082c88501880015400c5203146c00030710130140495200454203091800e00e094902c00c2d841441d0030b80c02400b058000c21036200c0c00492543d414204942410140030550341040000c1c10b11000c544002c2c07915007405c281c02c00044d44a148103000305071210b03440c0c0c001960280104903003c0c00240d2038001001d020140e481c03000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 697328408 1250 697327158 697327177
    0xf0f0619050111030412060e0c0d03080f040204090f031e0e011b0212060906070909020705060f10080106080f0114070504121e080c0c01081b1303020613030506060907050f 75
    0x136860580ca41c11a00300000e5000012928a541c0d854070180f006014011590080b07401c4901c81c09903111034500810300c0d40094003c0e0400441d260100f8115621540440400b952001c0048070680d00341c01c0c094410b041d008003901070080b600c110003c80e20f110744070f80d810158050712500482c100745014100500705580b8126080034418945100ca07050402c030407441120114000c114034500a14000c0c07150800c0d0340010b000c280140504030000c3e2002c00d8159000040c15003a02c4550f607058040200700319643d03c0f0304440d500e4104049507000e40881c6607400084d10b0310080c400c0d0404031400020303624044440d01e000030414442440900741030100702801c28058400024507009080c41248c842c1280e40040b201c202e4005440d0815803c02d12001d00f083c80b00342002d02d2245011486550200744168440c0c203400e00008545918840001a940c059070700a043e85441d24240d01409480303038580c0c002990a4800c00b4009a014034055071003d200701c22680d646400d2005000e4140044d42047d03552 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 697329658 1250 697328408 697328413
    0x706030914070e190203070f12060e0112030917070302121606080103021201060e0606130b0a2a080f091c0506161d09060a0e0f0f0619050111 62
    0xe03881c54050401202002d0704820b030488610b0f0912180e03070008110503009001810b40140100246650405211034541c801c506044010248070480c540003840b03590001d44160a83c00008034a840b840c00c14180400e200f51140d00d041c6858499010b04500310408504440d0721809080c00142483d18200300116440021926034241032600a2051610368210100081c40c030b10040044d0310740f080351498030b000c90034001c1010703d0070650605003011006212501544000506c40b00d1000600035003002043c4541d54103440341c0241d5401030980c001c803126030b00e090f2503403907403c400400c10311589075040707502004542c50096030b1941c08999030003400c4c05070341c4825120000c1d041c1e109007000c0000843c0c407880292070285403420600c04002e056004010401403544100e0340d0344240c80002a02411003207074031000a540d0000080c0341c45020790004411a0140c1c000d0220340110b6060640c06070322404546246952007009002100d541202d8049445c02c4842d0708120b5540200c1284899031555000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 697330908 1250 697329658 697329683
    0xe16110106032409030c170d02040b030403090e190b04111c180803010513020c0d030c090506070f17251202120a0e0a051002010905060c030907060309 66
    0x419400c441c0d45920903680d12070500c15500303212010710300a8a0380a0340b90820465a202a02c00a144461080c1c00422816443c2e41561100206409035030760070300750304415951541c448004030f083d034100740c4044000c20955030000c00c45000004006200e80d00407400200c0308111081c0400180c425005a107400c907a4940741d103110480000e0040250b8000716007180c401d50396003110a021601041429603000a20010400014191004490440d98200c075a04c1c004815818903100a2184980503100c503c141c1c2c448285603601900320f035a2a0403113450f0744880958135014484035204039417006140206011500000900701041d0b00803503109103560605115211540704044001c0c0d1095440ca1050030030020b08001c10f1440c409102e40091003c1c004410403081e4a0312680501c80c2d102c01404040041c180c910b441e000788800043c10028040510030442c60f5019000f81561001a2114001e120004e40c0840b01c03001186c2c0100148001411290303c2c19600f2130040c8503140d4104d0744c0820000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 697332158 1250 697330908 697330937
    0x40510020717040305060714091011101506020607081909030c0c0612061401020309062506050f0f01030302340905060310050405060a1e05010311190e16 67
    0x6030025505c0381d40141040c0c00c1c20040645032a074050040e000d220010001c821650b111480d005590035101d00b003808120310340c200c0040c00d100c00d03001c10354034140c174008010b0040300784103c124085035240d40a035403041d02c1e204012500c01204490a105007600005401d00d128015800039032000e00900d00b9928546840d07455041c801402e6100c9030010390400f00e444050306091090a00400d03012610300400941400040e4590041000d0303075110341d1012a1070406c0c5841401c03108207a070800c0700c0c24001c800341403802d0740040c8801e96070b002130402e441c0002045008941020703070590350182c00030303c1140d9907841440540c500e040d001c240f01c50003c0441070390141807415240040d0042d03a0000c42d6602e005c0d000e00d49000c0602074039403c4a8204000c0c44041500403c1c02a000340c00c141001c41c052959840e48654008000c1010303148074a01000002408180854412410307801c8541e0000c1209a61104002801074003c1604403100382c404511a45558200340c1d0391000b07242400118148110b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 697333408 1250 697332158 697332203
    0x2180603120703172d190b0a030b0a05041103010b0d1209050a0305070806060a0303140703110d03050a0e0304051f1407050705011218030f120e15070203030405100207 73
    0x1541c20000300801e4031103614244581c01101d20b00301085c02001c200503e00010100450100662901e01c450354811600000c1d845018040c40955041518140142007100301240100022242510801c000c24201142884c060258a60011000f0f045400340e01d0b6503154402c8400f072200901045c032880c0b48000440c0d4959042c03010055001e1009810402d01d04414942420401400305128bc445403034148006a0010380350011920703030301041603d502c894501030b100c200040c0551011032040016800840c2c2c0d0580010b8418414108140840104419019524000c901a044d803040290305003100b00a41c2142a009044492400a80f04a1805c0b8130040d15030106005860720717007001ca8107026a581010f411020000300040400c1081c2d80e084500000c014071030801810401c00549080409200c0e0443c0006d00350741140800500001c4d5100070381d201d2001c5d020f0807143d0f20510000307030701500100649100c0e6800001403c0700e400c50f50802d50081d4015001100c0b810100005081c660040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 697334658 1250 697333408 697333411
    0x103140903120c1e070510060602030409020703090b12100501091401180518041406070518040603080d090b06090610081003080708040e090c1e0d0602070804030218060312070317 78
    0x30100e8003a903400f0755007015818041d1f0b950715000f00906100d81000003540c00001c9904481030620010f03210701c0c492808448003101984a90312000010034a072490149001750395000394a08880d1400041d41c4000658122100e40300744013a800220f00c0b000d8855029220000c1030340b101420500c8106d4492000440320450101002a4a829681040108000740d89020502440c140c02070985261036100200345100c0c0c640c00460078600809820800d8a803a00301001a5601141260711842c1c691240d0f0014904c036101034404100751000f06950303060004034a4080d0340054030311589500081c40a90307486102034103d0401070441034001011901e00c0000d04250b911450310075545510302000300c400440003404e81040c603017190b00d004009940d002030411400001440030218000500d0024407120000200907284600004951040201890041054030b00c219801c10006e01e04080894441204889642d00340d40040035500d03082d03191030007074001a882481c020115200711004948030100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 697335908 1250 697334658 697334707
    0xc0f07051f05070f11030714160b0a0210020418020a0507050114070f0e0a0e1003050106030803010e0c190309080702060d0606020f1b0d030314010e060103140903120c 73
    0xb40c91052001c9598040811340703240d8030750302c1e0200d000725a02208036242c3c400c42400800c102191000c05d102020700340036403800c40c4042040982503613900c040381b901701d90200303c10000500403544960020b044078030075074003600e40f84102240543d40a0120700300030361220324920180607080c0b11000c0010000d00a2210f03010f126500c4403880c0c180701001520203d0160000000d1104074040c11406440d662180011110034248901d2580c482034220084150326030005052035080c84004428810700c07100441c12039a061808156503030355072900030001e0050f20100e4922410082e2407100032440f0b40c010310001801500c50700e180c03115980c00240780b03501035612114800d883d01e004001c002d4060145401c40154007010b00b01c118801040c2903240c540d000ca14a10072403003151481d041c10311030b61046110254100301040c5070b58449640340030a1204070741d1280000e0901c00d01100080400c03c81e24011155040114101004c2802c1003840071401401050551030511030b50401c680201c05101c025503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 697337158 1250 697335908 697335911
    0x1020a020306010f090605040507170a1b09030b072a0c050d061a03010219031a0a080f1c0c0201051c020a050717030708190608070f09140c0f07051f 65
    0x71700e81480c8034191a1241c0c0011f2140d480c180402425940006540c00e003031120b200c0035152943c524480d4001130900ea0420480c02e0a48807589041c15003120f480409d807409100d62400c00d50303401c542180c107140400c0c0031009120402c01c17000038218541502000e180d210308481d852884c2c64402180c95110342c00c005440031030701e4141800c4200301e80081070701c40e15000c6e002517142040302d040d034680074581e0182c42010150b07650348200010340c240d0010104c2d10802001030b00b42c25600c0c079000e6660014004540c1c1c040c0142c90011440580e138020a03800c0600c95121000c2d83d19aa40041d111030304036031005d05c004401440261640703c050b10040a00c0611a01c031b1035102d403401e09001403004e80ca140301040011b010000d1103900e60b00400d8456000044801115a443e03060341d112019058540c045c00e0507200d10074001ca84032074480d600d48260b540c070003010080c0350001c0f107864180b01e806403404641c40900b00308182501c4c1c880c0f401015104e00aa0813251840390045c091528414081d01c0020840e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 697338408 1250 697337158 697337189
    0x10207080909070f140d020408060406090302070e19021804090309080706140304020f0d05031630030f0b0303031914040b070c03030603050607020d020d11120901020a02030601 77
    0x9241c401825a0846030a150405010054000217400310030303a52940d03003048a0214a1000000e1180c0448018100100c203503007140c28986030085c040d04000c4c6003100503009001000c1411502031074071038816020765149204098900f071501000f588042d0303100e921903040903421030007600c0d98002c0c007404610035a2810707513091800744202e01b890340f250403a6040100c074071090f9144825071000e4940003501114003201d0b2600d080005101d500c180c0100426502000c640d80b0b40c84101050343c0746031035004411034004a00600400100e0301101250002807501791031141c000c01c0d00c264440608444100000035104116100091030340e0070488111414810310040300d05201d2036806001014a04001d03400b0701820a07541d901c00c00c000003042541041441d0001d1410f151098124500540e0407400380d81d003900f04210b009444075854017103070b0b01510445c0c41014070703284914910411903d41c0405800c50800c0d5501c01116940804c0140c0d0444c8a1441024050794041c032107280200310f410b203041000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 697339658 1250 697338408 697338427
    0x311120106030e070303090b0a020717030901080f070f18051315050a0501050a03150329090c030c060d0e0607020615180a1805070b120f1e090c0301020708 68
    0x5803a1003020f611407035000301100b0400a41c008010304295420181282c0e00c600310307004100d223070401d140d009601c03601550300e65000c0d000002c00240001c450a0303070303441010756410580c0c0400c007009480110001e280c00404c005240e100306407020a0031821f080c194866566000042c04101c060307131515022550b0b42c40b15204040e1045410001000255081c02e0076514090010f840e03030041f0000141072507120760b0a80c14ae445128265800741d80d20807640e41000403c2d40c3c0c442d0039031091700c03c120300c2429594046100d01400082c64041110001d005080b100b4000e81402140c4c0c02940003088102c0d01c4109006c401c030410703c0040d00c0352525600400f40c1d0700d045035900489210103c041401081c04004280c003e40c1c04006a60f0700a490340004071342050f0180620361011400320002e003a5002d8054049510042e48000b4101c0740882490140d0f640c030f807010209984002591960350400c6140ca501150301d417140c4000fa40410110b0a0300d550411200100e800d903070114008468002000444a00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 697340908 1250 697339658 697339661
    0x8180405010e100b0c0c061b100e1b0121270c050609010e0a03060c03060f12060509030c060405030310080f06182103040204061a09040b01031112010603 67
    0x50208001d20342c0319003420425010a44100d0207100014480092603141c14002081114070850019101940e540c10254550001d0041c124104050f4003c44c510322586560b83c0c0142011945500064030900580c4023000f500e081c03040500d6418002c4e8240309040140d10210244008104010301040301c2c0360147e11000f44401600000c52a480513201d9140450031100e5644140c62050314403558800c440c4005803072002d2012079090b40403114a0000c001c00443e5044803d001200f1385050102e1030300d460f40302140c6001070103248150592a840100460915000340350030080001c241c91910384003500341824140304840130784003a072000040c0034001365010143c40007080904040d0100c858141144c0d07454280107000f0074070300740758540d426808201c18015070030380100c85901d1490280c110034148210f60000c80d802e92096113094000100100f6404441086c034031b40100c150f00d03281828040100500c1200c22880c1016942c0f02815017440d00d4500400301c060502150038803640c50007000070b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 697342158 1250 697340908 697340911
    0x1f1403070602150f040f02060a180501020102120613090b0412120207050d080901020c071806051f030218090408030a0606020c03100908090a060c15090b180a08180405 73
    0xa0440d808411a0310f80c018192000f10380002e04040c1445403070b140c030709046d00c4041c20984083c0d40b2110010308982d00d035420001131502031604000600080c0e80d500016801c03801650f8a0086001c84038002564074581001e00c6450340301c1d000d00008404a807500c8080305803a04031411a40c00035001914100c0d590015032000b6900302c0e05006528008180d9203c907150010380e40b0341e07824404004086242401c0030340548143c4100c0c00111001c880d40c940d07100c1c81c2060010f01c0c1c1041030f446c0c100007142c1818018240b07001038862001c050110504600b0803002903025401d906000038000c058151503640d1248a030b8000da000b20400313030b103c4c18010644400c454042d8040e101b075511110420070162008200461188002040081c80c1842402c208805105074814558030000c903c0c000714407036410059800710345000f4080350142c884070210301422544140360240141c611040055101001e2807008010741c86e48206460403c050f81e034400c40d50740c2140146c101c030200d540c204440c45081510480c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 697343408 1250 697342158 697342169
    0x30d0e0709111602040e010b0402180a09110a0807020a060c03050711060f07141e03010303140c100b0d0f0821040803070c030903151a04090c0b031f140307 68
    0x9510f4224545a41082003400020080c0541d444018117050340c0000c0d44058640500900b043d551813850041110724030300c1ea641d03024850022050040303142039443c4502204c40c00103a0b0b10625044000c1030544034030200418580c21482046210b500181440c0030b6100707002c03d00e0b10042101d0071b00c0d06015000c80310100340c80a03550b01c40400c0000388490594036541115a40c10300403d80c440040c603183d028490f00031203480e440f00300300034007110511000046040781d000c0d64443c0890780c0c103009400105d101c1c0c0ba0b1900341c1540b0001010100c8070f19a40031076041c910043c4100340103081a03031040c4207003001383d100341c0d1b83c50000300380d000e4023030b00c80044841030040002c0ea1560910741550717400400d000c0078080104103c0141d00300701c101401180030304050342c0c1207100000c0001400d28420040c01400090b2310f990f00c1791032400754090070300d4011181902e038804d041d4140e16040103025803e5400003004002d035480d804041e0240110500c480c28098224903045400c41889401418542482c03035010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 697344658 1250 697343408 697343441
    0x15240d0614100c2402072108011202060306060d0c0c0c05011b060506060c15090c18071107050d030903020411040303090e2a0304020a05061e0c030d0e0709 68
    0x1801091548403c1401ca03142e8007040b03001200031070440592004c025580c95858a51001035a00e09200c05008030f10103038004d2013841c0c0842ca0304103500301c1d500765081c4900c00c0d06d581d064000c0d100601e00700d0042c1d80c0c822030260610f81080020703501281918500030310400803400c4e0403e1030381400390440c011005401d0030309280c001024094401100b004000d04e0207011155580049485a600e4804480b0304a04d1101200da84a1801c50400d084200595050700710f4491111410194100400380c9580f080d255442c1003296580e0b61000d40740c09021030a60240303809103085c0807505d5a50f4010001900740070742d4541b541c0c1c0b4254030520040300e00c0d82011000e5003505100407c002a84035070351009407540c1c1500c1490907101c00912548014440c4c580113400440150034a8143d5402e1010314440e9000300c1c0d04c05003265940c0c1c02e001c414031a49a40714080503401042074000c001100007400040009400caa150400702d903511401c650300c882103140d5540155400704011780361b9000394603189030110329 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 697345908 1250 697344658 697344679
    0xf0d11044104020c010605030706090f140a05010f0309140a062403170f03010324091205130308040f06170106051b03090405010306021c020315240d0614 67
    0x1d0741411031046900c152040f90001103070500c2c40020340204004000c0582141e1150784c0307403000902040b10a0003140c0340048510000280d0f1000d080400400c2d0304003800d12900b03141000011101280281e101c1014580c032040b1280000384041d85172190313980300b40007402414840385840000d841c80c40c4c501091540c008001203603020f4036241080c0450350b00c00811005185e0101a007003103401204401c03419204040000818422141507020001c44078006a40a4101440313000c0b044403115280581460b18070705002da000b900400090100070a4908a540c10741d90f030740d860704110391040d000020028000f07541000015000012804100e400b02d146000c90760400500404034012481e222503d83e42c4148030103045a0300340104c50342b04c032000c0c2040c8080d684a0400101940c000d4025603540c001001c1c902e821004103200340d90050041203030041520380e9020030841e201006ca001d80c02e004030a500d10b003220000c00c2c00248dda404a42c0d4021078403600c3c0900c0a0401e001c3e04250900440040c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 697347158 1250 697345908 697346009
    0xe15031501090f120201120e01051504050708180721050114070e01080712092307061d061209010b1926011d0109050c0d02060f0d1104 59
    0xc28110548860a0300c10604c401ca038001201e4030a9404a880e080034603100d60300ca8001d00c19000389101744a0141c1100d110300e010001d00044500485080300010700e29004107189044000800d048900c161007164aa0354480001e2a804010580c80b450b681440c0d485c05400c024003801030070076034644101100c4552404c010041d044011485006040243c0d00b000682024060040d0030f074141c4031220200700000c02031426004800c202d0601030400c44628840074000e4100280f504281e9150faa43c02c00d2604200c0f0021100340a40550b2941c8240248466403071524401c0117a03104400c4400080b8052941c2c80c2413010700202d10441000386c0405640c20311a0984144507140180c0c03581c0b184101c0c0c1440001d10318014041100c00d83e02d00c1030128001c0794945015044207010f280203030140c426010908007004001c2251080094005505000d45800880f241014102040c00700c0400300310312070385040b07011403a8002d4000509011140081040c101041c0749a105102d006010001100d035000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 697348408 1250 697347158 697347179
    0x6030204180b01030f080415020d031a1c02030a0204020a120b030318090405070312050c0c061912140f150f0303160203030702130507020f010b0d02060a0e1503150109 73
    0x1400b000e000c9507843c4441004000c0910101c074014042080b45101c103002854000b903c40b5540ad070780c2400281030149803c80b0014080191140c1c0c14010a8040206601b2041c3d1a40b451481401d9074140541c0640f480903849500040091400654174051400c41095400c2c045a2020b0f500600070780c400e0085070455034100d4200f4607103140407208101c2d65551842c2c242e1400c10150001012841a12f1981c40c520307801401810704580c0b10b2055541042980c07052249601500705c140c0e14583c58100000e03801c3d40903040e88064214a06004186800980c1c5514a640c138281d410f03040126105c8100030322052100544203a511003140c1c00000d03290700d1300002c0c1d9203010f042120402102201040c02c1103542c20800c952006601500750441e03550450708100003002e08a0329030000d4010b0480e544100361043c4160342402d08007c00c4142d03030803a16001c3c001c1e6a08a1070440341804200003400320955200300d0850590281051500e6130380c60042c030b0800c03106c181403640074103100f620f050600500060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 697349658 1250 697348408 697348411
    0xf0f0f0f06020a0b04051e1f050613020a051e2502090c09010201090213020d15030302060a0f1814120c030f0309032a0d091409060103021b0106030204180b 68
    0x20003608130701601e80781405814480031f014138102008002c01030b50741c41400840d0b82c10343e0001020300104a9499241d0000583e442251625070014041e01c60a40215040d405480b0042a0745000c0d0308005a4020034410391110300c005284460001c242c41e0f4071120012100d0300c1d044550030700c200c1456032603030208452202c05000080360030340c04204200540d100350f10001c10181c0060191b1040403000d4130f603400035802048600b061743c0c20300719501841c0209050340003c89504d603004010300d6590b10100d600405e602d43c6013a084907262007013004100c51010000e43d05600070900d120b0316030021b00b03126151411130301c0c145203030400034005c0c14440f94012041d1055200b0000c5a95646e50b42d90307010f5400d40c0b040980364003c810458010141c50300480b02c41e8500c1290b0030003182c0288007100002d40c1c0d10700381e600c2444117480340c1c0a010100740c02c2108503140c2011060401604200600b241c452243c0240c03004051039030765404040056240c54007461000c040c9002606035030561540381c510b20f2420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 697350908 1250 697349658 697349663
    0x173a020405010516020310020f121312032003091e0c10030905010b0a0f0608090115060e010e030715080a330f1401180e011701060f0f0f0f06020a 64
    0x4c940c085000e54400340200c0c2c0e290710b85030004641d00c2e40804000080c582004400e04c2503030000c0307000038001000c1c0c6442411030a4000600d440d040841c0102100a00700d050710511880c0c00892070030703030005a160041d50265000360082c18542101180c402158041501c05090302d038000b0304181030316240c2c2003081c002c05000e403501041201141c10f0542c0503103064000d0a400014100001611401d600441c00585078540d4411102e0b44070154007900744e802540c80700c0100c0c6014072040001d03502602c4041031042e8181811200340c883d007000241440d1040c1e104500302105c10392201c240740c1c5d003c08031551101f5000c8003040207011018281d505010060345020452a105403003160f0324000303e24101c01054881541084070703881e0640b50080340113910cd5140031a210110021011401d403603224146d0b0240c03400f15400d6864500d84a12014082d00b0000e125546d4100103e0050f05078810940640310040c1d28140c0240340c0403084143e04003680c40581c2e04059140e00b80041680490070018454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 697352158 1250 697350908 697350937
    0x1151404020d0b122118040228050301080c1c060b0a080f0706090e040b0c0a111e12120115030e10060603050121173a0204050105 57
    0x20003031002c074000d003000c01e2465400401c0ca820205076140016440104040d030322014640400c00034140d40d41c031301a22075000c58200e90f10391100c0c030600300340e400703844c2222018110282c13036920501c1c00005030340955100f8000030b00000041c80031040410003558800381c2075441341c0a4076080c000e13102d010b090780d200c000c000c1a1241040d0140d5969020300c0c1000c0d100050036120392420100040d46c0d00e90480c49540c000c2014008000340100b17503a030303c40d0310698100b03106800320f03592090740d04160b07809aa0b03607a0a1152182800865140400c49080320303180e5040f50030706040858203094030300500521010000b0508022909441c03007140b261a044a8289400302204a6225400c0e405031020705100c00c0c1e540300b0020501130050b20340d04640c0c01c0700c0f01503e0404c42640c07211000011601c0a403848101d40e6200c0d484100041c10701c01c04004a4010b04005500703050704c0e041401c1c55038111080503a031070202c0d0228156402c1c00201d07250b8040d040000c08500c3c02c0d1400c80080c1c644d0040d1804440e001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 697353408 1250 697352158 697352167
    0x60216111e041d030d05160908030702040504022409130e15040f0803070e040e03040605040b0313050102040602030d0b0d031d01031b020a1509030509060c070e180115140402 76
    0x301d481c0c0542c4003034501c0c3c407420b6903150f0460321340410090030126402c2c04012000358055000038010000541070710b1911002c1c5103841102c0d0240f02c007818000c0c0040760800c14a0003841801d602d0004402244c000c0c03420702e00d03130341c0103400204000220041c038a00d038036502d044181e0800c0400015001c424104000300b90a09a603a82840039549060b140050580f07180001000100c0c0e40c00315000083d440e0481d020051001403810f0b070303556030186000e80400b041e0100414400d012403440650383c0100784050554418805540302405d90b00254090b00140e0303c081070107200d15200340601490740300d0985034200c1015690303d0080c00052040d04144890714031081030750103a4401d0b00040e400b000400e901103143d045210000750b5030501d1000030f0b54400c0003030960007502a40b0b03000d10039805402d603a0b400c1c1070104ca441000040e0f800140d00d901c50340309035a00081c40c02d900e004050b210f25004112141001d1002c0383c1e02d82034030010081c032500701044000900881d1a00f8001c140174160075680103889 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 697354658 1250 697353408 697353431
    0xb090f0c07080708071407050a06051c180b13020a15050702040e0c030c0904152f0a080c03070f0503102301020f191e060216111e04 58
    0x114440c0c1c220240000c840081d109050221a00052840522540a0003080c07035030b0040050b00c0b85a180a22540600001810070859100310090306400944c1c0d8409510019080c9402c41128421038171202c0300740f9041526818025140810b907800000360407a44a442003a074002800c1da4800e00070603105000c1034a014070b0051188043e14911a0b0242041000c070303101c0030340c9641d42d40421f02c0395482803080860041803414131030419402654030000c800700d80d14081f04894080c00b001c1e0000344405c48180c1c109401c0f2508440702a18414924041690780c0300c05840c01041c0c0d0b6002040d550081c00c0801c00e0003005a80403900d048400c0b12841d205031a900c542c0006c89100b0516808905880702024000c4c000c142041c0c404c2103414400d0302110401065140250b48581403584401200d03000d0740c1c0c9441c08290540074a0350058602d4040500402c50759840c10104c0c0c1004100380d01425441d4020410402054580040031404840359203000e4220541c008070f041a850313a5034000c0b42c88040d1b0842 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 697355908 1250 697354658 697354681
    0x8030c0a030f09380c1c05070f23030f0a03150b190e03010e100b09090607260c130503070f0605090a0b07050a061a060d02180603071701090b090f 64
    0x30a4400109080e944940c1d07002c845030f4400d11000b141c1d20310104051b4407440240034100b124102c035405250160305071400c0e1280740b01503502440507070280040100b51480b440040c0002c280001040121a4460507101402811540021040b039442c001508080c450480141d054a00040c010070700316850b20504102160510048243c5607095800c1c8415a0205030010814881c480c4000204001c1600d105040100d0b0004c20340300e008494103e0004078004511400407210a602000e00d80d07200714100e04001e400070807040318802c0a0b540d012034450050040360345034100030401280108030f2141881504584181c0501c58101445400141c0c50740740e032103140501004015004400b9210202804d0268940c069088105d40e480d06e0039040c80d0141d080190180240c42018101343d0503d04000ea01800950101518506484234884c07070408581c1c030320004500c00c404554070740d10801108142006e0034041070300144480c4c1d06200d480407058540c040116400410380000405580303d040007182d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 697357158 1250 697355908 697355999
    0x10b0706050a06030222050a0908031b160b0601021006031e06091a010e0f0112060f0f0c3207021018090203041a090a021908030c0a030f09 61
    0x2034102c0642e21a8040d8464440c0202a1002c0940c201f4031041c3c3c1c4290000084070703d00348000302440c20900205516001e103010802115607400c3e031143c54507130503420034000b15540c1070080f0b50300c2ca040f03020000d565a05010600d00e90f500c1c9001400160304690394140304450420f14440c554200017891f10901410b9004000c02c250424078103803080d0f000280401c00c0d100309014921501400c68042080c14a03502c114504a0704400845601c1c20350581e100310180600910b0350221a855440b00c1540d501c0621800c80220603544a1807186070a11040b01c41e00c4060b80300d841041d0025141e0503160908100c1100c503020750458101101c2481c40e0030940303044980d0b0541485009140c80c0200e000e82d40741c2d008601690150a00c541c0d421480d12150300c038101d0031500c0c107a098012305000d50041c10f11295072400340c21001c0600c180a0380369460b003899a040303a10b4020b115404803035008245904400140207503091071410341a680e041040c80f02d007d4a03d400c1440850700c17440c0e40002034081c02090403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 697358408 1250 697357158 697357163
    0x150c090901030b25090605070206091f031b0c020d08190203091507031b1e081206090c041203020115060216050a06091e080607050403051203010b0706050a0603 70
    0x4440c41d5850b03040031030b50b0160071940ba18400107402000e6010218022403030426415945e0742c28603060034120103d58542226008036003004044c0920401036403498501c41d0b62411700d008940c2c400c000d01c040101a11031984000c004c02911a4400080a601031110748082e601a10001e010451900c2c040000b84034103c520070340e090300161040e2110381c0c007000801f02c20000300c03000900c9030765100484100744900a0020042840f0f450407050345110b0511110903540140002c907908130f1142d58049019809032401c661111002681c0c1507213020803400242c21290130754440c40305141c140c1e130b050030f10700c500d00075000b15680c0c0b03a03e6681010310075006400c3e0030140c1400b42c940d00b03541e203802139594441d201048442c1c0e668010f0100340b500340700c240c1078111040c666409513641c2c600f590341d00a00d000c10701d844414441030350012482d00d00400105020384146d030384095403a0700d9410030b40e080802e001c1010010b603204100400c003044800c0b0965071100c0d0408000121600ca91217030030004c003580c1d40f00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 697359658 1250 697358408 697358419
    0x70b0a061d180106080708150c031609050303190305010f050108041b081506132a050409050117060a0903020a060c0e10110d02063c041b06030b03150c09 67
    0x2046004011500c40304582102040700c0503250603d0015101c03d50031520031030740303207002e10000e1040c40307104048510304bc1c800c0c2044111a900e680101c0c1c1184d10149261024440e140c0d90f4101d440d601d40305860040140c5032003e43c02504100c002010b50001400141c011840c00d10501050b00d111400c0c5c200600c0040704407002542c07507a1101045a02c101c80c010312030801001d03400d201040b24028102c104040d0166000801d1240b12001500300c07820082c10308100040c070020407001d54601c500d07400780c080005010b1094000c0c1b109540380600082c0401042c60501400c3c00010b80c0018094003036a80c03000010410352122a0115000f05824495075030101d03c0c141d49106642d0055003c0390076014a00030f072a20324503140426695203c05450000a42d50002c02c070300c001c031040c0485c40f0804080348241d0785190a00c402c1002a04000360341c282c44407129595003210480415a407140204a503003005e1000d00c581800080e00c0d10315010718041c09800150014100c40f00c49411605142001441c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697360908 1250 697359658 697359671
    0x30c080d0510050405180607140d0f0204050a0f0614031306020706090302061e0414070b040f0806060a0e04060f0b03030a050c0706090b0304080a091802070b0a061d1801 74
    0x80403840102284221070007a441e01e070200d114800744003080385018800171b0047c140380e03c5000c0d0031188400100c1c060414030005214030300300d0201d140550405040c00c4100961140e00301410860801e00d07640c800c00382d81c00000300400002e40c101e0560103400c000200341c552a03503150f6200c102400d0751144001c0078180300240d50010048268400c10070302d80a6400c8881c0d0742d0f10203900a14451103a44102c001c1d10350140048c000601e03002200c00b00c034407045d041c0d0f802c481d13441100071190780142d00301c004d4600148005001000c01000b14961004040300c60f5111103142c41c12920104001400250080383c0f00c83d03c2600030445078103c060b103907001408481c0da6100a000080c8642c10928070510107010701070000548034804c041583c00e55850300b00040ca184c440f5a03d185459110100c13020502501d070900017049900d0856180d000980d0301c01c0582d0341c0b44c2031300d00790402e050020081d2082138074200050008aa210602c8003684042103101809900c1d018810b050510030001380540c123609040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697362158 1250 697360908 697360921
    0x7020319050d030608031c0f022a060702010c0e011209020907030b030f0d020c120111030403030c110a0312020a03140903040e0a02070b0a1119020f0f0f0604030c080d05 74
    0x41c2d12008466296410406262900c0c0980c1d01c901c0b400052080f0070482180f04018a0030382e9004c9164002c0302c0c00c0040c03621208043d2040281400221000701d0310280111036441103007401040c2c1d000c2001c0c0f0007004142101c14010f00010580c02c1d5450420000c12580390b00700314290b01140321950010400c000f545008e00f402030140543d04100c900034001c80c2150041d20b200000c030910040c159802030701c140c44c030308800e120149800c07510b585850764076200003242c141001c000840c0078074003070743c0c000c161081c8090015042c1c441c90304c0200307002e0380b1007100d02001c0785c0e00800c03c3e006200112400b580d2012802c4040740548805c14400c000d002c0008280000c0c035000000a00445c0c003078441c40d070307215a5150b0303404040740204100506041d01d000005408100c49500c02d00400300e03000191030520b40c6800d15420303840c110703921420160740040d844441d010010406c40301c1c4009150000c0c4241c15104010170f4844102410040c01c2c01440081d24013089040000d440d804e450840c0100310a19082 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697363408 1250 697362158 697362163
    0x31e040f0b1f1401030b01081308090d08030f0a06060806030d18080303010b04030b010e07050708090111011e0501170709110c100c030606110312062101050415090510020702031905 79
    0x1c01d018007107031602c013158446e035010704161449400031303d0100309004d0458403a080d030f544c88150348980c8602c1024800f0001040b02d4003450040c42045605109882c005450030100e40c200c2d040181070000b400c0c00c00c1103036500002c08082c6440c2e94942582c221960380a0b0749102c0d503260700000789138080403001042038000e034006042102e0007214214804c6c0da0ba0000c0400d15041610329400181080114401103005000103066146040c07412071a030481e0080b603903003111045003466806d00c5480240300010503c42c0222400342449030041480c842140901903079990852007108a83c80c4c0300c000100b0b03807036480c20071f54105410b400e083d5442d10000000000040c1004891240403a2803344e010510350b11031160072424500d041c2c0154905103807034032401c1144100804280c0e0128407054100d8515105c0e14401d01040741c4030001080505103440e003240c42040032421038070110310380340d4040045100094001c221440d850703001079880f074035400400d0030140d00300f51141e81100b900c10340700d0821100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697364658 1250 697363408 697363439
    0x80d020307210221040504050f04050d020c0f040b1f0f09230103150b190207091401061110020a080a0c03140c2508031e040f0b1f 57
    0x8045244541280a001e81000c1842c10b00503801680300c4a0345040c1984000031038800065014021800c3c00d0740c1d400010141c4400b103401d400305400b0101403000f04041000702000d804d85e43c0c006080c5041400c00410712070084c90650707500c280d442391000b04407038841945410300a001c01034441c1804a501c0000740c1690509007280b0002f1352203a100085405610442c684040e5440581c1ca12043c45d490045015211592224400858103c000540b00540f14020034842841850601c13404202c075602a0030082d080e802000b00c2428601e14100180c554103659040d1044c50902420640c0b10030b2181c0e00d004458890541d48a20002c1c42e82d07507850b0002a80362162254800500080240c01d4044041d40ca00c1c680b2420b0503020003000c140045101c1e80641049992500c132080c0940b00c4039565000e0015800c800c1c1c0b0403000000501c0160140c10404000e06000011100d189040c03641d10f1800400c01264064051030325400412540c10345241c3c03031110160400c405010007a2039a1740914801c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697365908 1250 697364658 697364663
    0x131803170a0e06010504020d0b0a060306080f070b070f031b03080417120a023603160b07031409030f0106052d0d03180f0e100b03040f0804080d020307 66
    0x28200001200790815008060200e06108090310300d991814060201070b42001e003e00568039220603010f100c3d5110510040b000700350550300412003526100035141424440310f01801e40c1d400c200d9051188408000440d07002076444036805115030010f003800c88801c4804560a06915001760301c0400b41903001c11828080c0340180c55550720500d4001c0762010b40d2080c1020810011000300008141c0034090303018080804080500e11901016013005c8290040703e220701e0a03030b1501c01001c50000381000c0260000c8140310403001803030282044207854041c001c060f03000701084036034160303458440c11000648401c50005030444184004543c00700d40608403034050b0368082e00f068403201449080010a01c00303101c0e58003088480f03481c004070600c160040b407080142d0620608480f14003000740d003000d450380240b031128607031031109081c8904084901e4010b000010761504c00481400301c24000c2c03040f03d8102c1e902115850402d0b04524111441d8011680251050702489139441a02c540120050152a2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697367158 1250 697365908 697365947
    0x3070b030103050d0c170f03091005071e121a100e010f030911060c0f0106080109030e0f0a05040509010614040905190804090f0903020d020a02010e131803 68
    0x98940111454502091101400310b6121401c074810050007400d4043d1a03e005007803125082440031444007442d8003a100c0c1d41c0290320008104503d2000a0040200411a02d403081c0030341c1c2040b0400402c04403e4110713001c03400007511000e080140c000e130740342c40704a500b246090140303d6100c014243c1c8540202d44442c001c0380c24410556105200b00102c1d040071070161034030002044600021001407a81d000300b15445240380c2c40c0e102250b50f64401400001c5601e80041c035914145407805400d44407a90300c0050540c0c1444580c0000070303001b5210b041400d009451a0212241440001e9481e01c0c052788100d1b002031408081c408604810340141050302e110004100010a00d5000d1100322108600c0207406c42d0401c12982e208091020300d82e2810501800b909420251642c5030042100c1c000c80f001890956980305c45000c043e01406120903500950020701090070180e00080d0511580548143c800c0340c00003035408001c5456404081c58000c14100c1c01c1d0361180d2807070301400003c0c681c0150702c9400d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697368408 1250 697367158 697367173
    0x130e01060311040e070f120c120503040f120507270c030203091212070c0f1a01051c03140a020a050613030e030a05103815090d02130b0a030b0603 64
    0x284000295607040325000035000c46120b07e45071340d014211444103011150102d0420001034490306901c0c0040722240100701440da56841d00211015082041d07004884c040c021158200c0401d4010650808641a11290b070780c040310aa006012100810010740f400c141c5055480d00e12540c1c942c1c0038603c075160450403108000e48000c500f00c40ba0203081c00100c141050340c3c000440307407440b407810b5081540c4109124a401c40199a81c0c20740c1d13046994050b842035442c00010081442e14500000c0900040c940041300d03403030070383c40c01407041c004080724000e84080041c101c506a442040642c2c4100e0700305040c0c80c070500f080480c901501d175081c4010303800164902640111881d02141e020851940b140c001e01407001310150741400751078426409803004018501d040c3d00328825140200c00c5490500400704005450400c0112905001035a00000d200901200c2c1c15500c58994981229030115540103a11252700032031401340600036034240d003128101c4000010810040741180c0903d500700c080c2d5021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697369658 1250 697368408 697368431
    0x131b030e061b07260304050a020108150303030f04031e030b130e190204060302060301060f0237020424090e010218120f010515040b09070e130e0106031104 68
    0x2068120b000c52018281c2000408001400c4441c0b044080810312a00b108011542d130f41c12540d40c00846041c2c0f0143c02c41d812210440d81c0c0585415400510141c0060312885550b000c25a04d010040507110740100071030200c1c045c107010b0071000e0301d40311503c4400080d00f20400701c01030190100210440c00303081c1c0200c070400c4245007401084203c440701001400600c450702c9000c03036003284011703003660080e03594000840035031940d100841c040d00032074a51f46044448684001e180030f004038003500b101c0269180c400710125a402400c1c500008480b10b0720170f49100e500024000781310380c2c2c45c0b414445209a10489400a074180002c08466551004001d414081d0f010340c0e01743d2040c07400030020340c100407455080610300556003020300580d000440b228000500103103401c503003041d01d00d42c0e0106403020705512180341900032005070300d5040e2440b006a09003090040c040b6070001e0b1020b4861007210380100703245542c03075011401030851140280080f581c0c2c1e0502c2d038221400e0b210024000c80c00e0190a906 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697370908 1250 697369658 697369681
    0x90e160e04121413060f0f030504120e041d0a0b09031309020a0c0609060519020c061b070c181b0c03031d01050f33131b030e06 56
    0x81203030400120418007011440807160325000c1804404604020710000c20900302d800e007014007405560300c81c9071106c81880e0000d00f01d840e03610381400416090808202c0015015822040c400383d450404903020490309000030040d20300100e85007482082e01d5495a2010b00025944c443d15004440007006911000c80103600e83c410f0801801c44421251000c202e8226141d0003410040c1d41c5252802200c58607071745200982c0d01c031103001e542040e100c03020320402c40860294940320481d038460440c034009407209030725101d101c0203101020341856400120782e65200b640403942c59543c005492130500b5103c81c3d07405d04042c1140c48003004d03c2d00e045001c960080320303031104080042003622107505460161794100c02800501280c544015201d0f42c6042141800740200c0d805441928001205480c0c80030000039640692049901e141e0031a1070b843c103c40c8201d5866a070748000c02e6a9881c01010b8420244000d400700360340e45048030b03400a80780c0c1001e540c1540b020341d1403a007250540d0302036110b80c03200d0b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697372158 1250 697370908 697370911
    0x30406050a05010e040b06150d02030403021f060e060906011b060207030e121b01020304092904020a0c080f1903020c0d020106060210020309070b0a0504300b04020109090e160e 77
    0x2094007006c40c0204003a880c1415041c400c1c4134440d00c115252200f84007100c01070781c00685080300580c0c41542a088102a5000100c0d001087d03284100102d40ca860101101c195001d0b21041c060001000451043e034855005401c8c484184581040c41840d5131410900a50050700141c1c0020039111a0b407210b864040c03130b5517400220780801412039010400138200440d40000301c1d41d0561004100004401c00d0f140180049038070601a0b5404d00c1510b410000c84501000c450f0038801c1d4030400105503410780090154030740c9604200f100c0d03100c0130514201900c501c02d002c2c0044030140400e032904c6400754160024030f400d1410806403903030010441c505070b00740c030160300440703002da08111a09000c484040d405951302c200303184200c8000c05da44c0d0602e08150307400707401004001080007605000c0d10f9802008000d609000b01d9400e1a022076080903a10400b1102d40700400545014020409680c840c2ca080b0000d010940001c1003980300c8201403d0b40c403046540702817525015100000b68a40400c4100b5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697373408 1250 697372158 697372163
    0x703080c070b01032010020a03080a0e0303070c050a08030f01062309011412070e10140315060705150a1d0a020f1503070801031713150212030406050a05010e04 70
    0x402c2d00303034219981c200200981c600c03108549244c101c0e5550450b580d02078003031000c40300354003d0303c02c0402500700108400070080101c5012810088030740700c03401c000412660700c100c55182401d00c0303640b10f141041c200220000040c0c44014048280001103090310301d60b604840d25030301c81c0804151051401226202c5903340418a80301c20700c4480300950051651303074a403031001d003030440c50310b49410a40744903a04207803001c030700050501c40d261015042206010b89200c0007814040105d0100301048040740c440141101d1400c500c0e00030381c00607a03d5500c10ba60340280e0000a603001d00075035180c22510840b0803503000061608010514030b52640b034408407401009810701401c041ca09a4080c00340050f50151059005076026801400418580340550301848040d0307107500c800d51460801444d02c588903155044511410050b07001030790a07607035900c1d041303650180301d00d00003107400d80b01a0f04180c0300c03c01142003031900108100070881154800303445100e11074404c005990b01e51340021031459049800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697374658 1250 697373408 697373423
    0x19020c0907120b0a030501020405040507051201060f1709060a060f03050303010e0603070312050309010c0306240905102c130f18080d0c050a0f0305090102070f05030703080c07 77
    0x1140496124024041400641d071401103000524400404c910070401c1c1d00c16100c69602007410f00c41d500d0280111a04255a0300d403260400340440c0990358040e4040c13242c50300388613004544d811403602179080c0244208d4102250900d91a180500301d88804044980700900340c41c0c0074004c0f0707054000f02280800c3e81c0c0c0000040d403c43c0e0803c5034280c45072001406043c2d0611403a80300000203030b00c1c0245400d00c4202d59a5840d04da0501c1e591007030030340d041c07a10010305243c1400c0041c0700c07100e4000360080c5030140d05038580710898841c10040c0c41001040d0000c40e045164660824800741d003104030f030b10040104040110100a0035807400a17401642401180e02403001781c03007115444240e400880b84881490400071340800d070515299141c4d5000b1904845504010940304484146403150007100ca0050600a160846040000344604803c1540340c042c581d4500118103441c10075070564142c07a500201d96880c10700d107410f103982c1e207130001c080c105c00141880000880f840101c0b020b80e00280c2c0c5c44001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697375908 1250 697374658 697374661
    0x706051804050402040e0102030c0706060b1e030a240503160605031b040b181c231c03020417010c050f030919060608100b031c021e0319020c09 63
    0x7000041c2901400c2130740e100351204002071440310b007031000314050304451040c10b90f074603502c0c89c01c80142c0301c2562103900d150790284000342c01c280c2010504e040b840c10341c030811642d039558031964000520f8032041200c42c0c0384000c0090606040141c0c1c88500382c8104604490302185d000c40340341d6100040d401000000390042c408506541c080840c242c2c1030030b0001c0012400e0580300c40944196801403a014000c10701d44c58009003a60901b140b0031150703e03004101c0c81105800984500040c0b01c0f82098034000200c108600a2640809001c01c2d01c0180c03004040728490002900010041d40083c01540e552032082e4480c60340f100c0c4140b01d1782d68140f409854940c10f00c03054140117a0710780c000522481080c00f904541e5903e40101000601149105410008405080c00070140c60034014000307031102d00b4905201a02c15540c00180c0243c3c2100f29144010800c62485080341882c0b01c0022810206a00c5010242180c4000c0301414580318a0010101184026181282e8580d4650032441e0000c60400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697377158 1250 697375908 697375957
    0x31404050d0e03190308090703200a090b01080402060d0204030c120c0e01080a0f0606080f100e0c0a0e0709051c02040b012c040b0d05061005090f071b0f030c05070605 73
    0x44181e80d1004110b8151695180d0300c1d180c840944000212b5210030f07400d01403240300c142c900818141e0203058169802c0103c9a13141c8000b8000c1e030005007000c0e11501e40803c2c4406240e28a804070703005198001e295480aa41c0d40414021107070b680042203480102d024000b044070b885820165040711f00e500014403030702d400c9448000c0040c400d0303103043e40d085841d08408181c9000030010380c400c00071114010030082e2110304082049496100381003c068010081189541d600c500368201038918201080155446110003036a03003401590145820402d221910455401d01c1030114521030300942d000e0120f04142c00046a0301488503c281c0702400d41d160507200312200c1c0c0d0604c8100700102801c002036142e01200000c02c100e40c00b4000301c1e107a6100c0c004025048030281c01c1e00c00101402d84195031641040b00080503020001010310701001a4420611f1130114801003035104c003500622003210342c503440d050080a100e101d910545071441010310010302c0a00c20380032548031845441e000a08000b400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697378408 1250 697377158 697377167
    0xa060e1e0a18060314030306032109010509040212340c03030207060608161703031005061c09120e09040507050d08070b070e1201200a031404050d0e031903 68
    0x2081e110450b207681e10000300025040c0c0d440c42810032215402940c891030800304052401020b8456620f4490006c00a042c07503801120980f10f000d032003424141e44800180001c50000c0c01800c810384c60a082060074004500c1c01c11202e1b02080c2c00d0b584444030750020840408040b00340070000c2100150603002c0001c08240b0075800740411910946d80440c100c0d503501503092030607240c3e90000c4072103c0d807504104816282c290400500c00c800c0390295066282a01008200500038481c0a010751800510211804a403035411042c5561000c010448030200703040116480071646a0717107021840c0f8010402051400d10443c40c030981d808801019a01d0900040c020400d2204004035041c8506011950005241c0d10130b00f846480c0c2540c0c0c5040ca01487c104201201b081810002d0341a403400d9100252407890004066040341e03c00b0031242e50b82101c501c00c0300140082c04480d05201000c0c414030003008000b142810000c00281c4d600459061003400305911101c403c5d115089008004150300c0009014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697379658 1250 697378408 697378439
    0x3050403060209120105011e0509010b220801021801080f04020d06020906120a0e12040303140915070f020411040806240307090902031c1b020f0a060e1e0a 68
    0x10b044041c43c03001d108130980c291942a000b082000c2c00a55071400180c3c101664200101000c440f00080f95162046030304045c4242075504890700002129281d00e8100b07000f8440003000d920000319a20072130900702c05455503058203498002901c40d00482c0c400f03012048140c1c01590020084203c41c1c00507666200290b02c0400702a0b0001c0090113048507e000c6158020301c1498480c4021444a42081030203091000ca41d400217880300017403100380003299000301c1e00c1e101c031545c0d4051b007940d80101400260181c4400c2d8620000514005090401c1041f030710703440d040491003994103110b4000402d540c040700740640c0c02108686d40c802000100d1300d09042c04480034040b451078a1344661203098001c241004110380080c01010346501440c000c50804114004810700e141d40d284124000030310000380a62060308246800d10400c846c010150342e03900410b8048804018543d4501681d035804c0913000c9456410280c0c8a8400c2c0d8140301e00000e140709155031742d420f004001954907401d049a88417023240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697380908 1250 697379658 697379677
    0x1a09190b0406030c1a2703010b13090605070302090d021e091014060703050306010c140d0201062d030b0a0f0c030e0d0906020d0c141621030504030602 66
    0x100c5451822480d2a1032091501641c01400740410241c1020b0306540743c81c0c511401200c2c0d2031010040010b05407050594440c00101184c410032040240100180c05443c424054647c00102c1d48014454041c0741d5116001a5220300b405000507501c0390020380480c0074860b950383d00b00904c0c0300403074014548035001b540da2800d0061002120304940021a000203011220300c2a030600c4c240c0c06001601c040c0f50b0b003404820003294690b1900721143e034000c0007808058001810b01c00c25203070110812900f0400441410b1038a811180c66001d4290002d01030400b51040a81800207040441000703030304da023405059001108001500700f4a56921001000710080c001031082d9600d00d0022500b500742d008401d881300b15a40d003c58403e6080d5002c3d4202540380095005120360840104078032600458041a510580c0c1050b40d9038003101c0c20448240c140480004c10103005000940d401d48820b47c1002058405440c41070b130100c0565441600a41110400500840d6040c8000c0001981a0700101400007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697382158 1250 697380908 697380911
    0x1b0e041103072d09060312020709020711040203070201091b14010e0603010b090a0902130e131208070e090109051e1e0411030d030c11070f0306020304020a030b0112061a0919 76
    0xb640c130f00c000d00071200e06030030841e540c640350340c41c0c3c6040e241e0411444015200a400071443c2440c1c9549044291100b8100c55015540101c0011310560003940141c004c02c1e04242c00300d032062400c00c101d40c0042420302408140c8440d10040c504154460289001e0104020740317103600e182d007070181203d80b6401c16071080c2e03800198600e020450010500107010b888540107184801941400b40d0655807210003004101011521440f000100c3d040e007a030814007100f241072a08040e02d80d81000c4070f51038919581c00d038000156100004207002c0c00c0c0d1105200754038031420702c0400320412103241080f10003a80c00384034080100000945c0104844000d50700940b0503d15090825600c101080c248821200c050740801c0d500d4030080502c5070042c0f000612604d4560103054481d0426288104400d400e010240482e0741c00f04c0003c0454540e440744c100655000b080c440b61740c2d030b5600c030b0440340c60b1528034040710f040e0b0402500414280a5009031070003418010800001c2d96207071101c801c610300c08400d841100c40d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697383408 1250 697382158 697382249
    0x60b0903121608040f090b040c020c011206091103060f01020d09060807021e0102030a0516020d03022505030703020c04020306010f0503070306032004180507121b0e04110307 76
    0x252400d00a200070300c4005c0c4421000c83c84d00d82004112140c42d01036078015418850050340d030399404500b010301c401d024280740c00caa9040e02190300050031a0b4018a00bc1072500820b6649003440c4030266204210498604d4000c01c01e4200481e03c880c905090900403c0103120240320403030150442d00c2e4401c0c442e10440e4003002025410280055001100b0542651b0004c1404148580303805001c2e880755a50001c040540c05145000f903903002080c0100b010940c0c04603240f03410148041d06036520070100301c039119580d622403d000d502ca90044104501600c00d189103580182024003c5e640b0540050b102c86588c0d0b00d4000c1c080d540e662004000a042558078040407000580c554207052014030b00c0f1408140c2400c0c00c1c000d000c2200c20f8a000c04200e40000b244200010341c000510b00c0c280c42205001c103050700d000b89000d000482004003076815400d6030318004113404d03021008031032085000742015001c403840a4181612402103014030b106400d03040b404466014860204c070181240d0224168190 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697384658 1250 697383408 697383413
    0x10801140402062b021b16090e010f02040608010608100b0d0e103e0a050c0708010c020303070917060105010e0f03061305070605160f021302160204060b09031216 71
    0x2080303100d00070504d8003503002c941582c003681c00e007039070102d4051800014008500740702c2c141c6907614050300c162040184c90f25020301c200d000a401511202c1500d090640d00c954443c403000e8901d40c0e09009640008603a00005070041c4214039007071007101d01102c100c9144c0349810051602500341c001440da414800d031070080c0c248003410f120704811140601410180100b910000c0c2040103000700110001c1c00920002d150b055012a046450103260340c01c00c00c3d035540032928120b0429403194400300581d460716000310750580c0c020008500c201d8041ea0703403940a41d19030480d2440102d90b0400c1c84025400341c001406654065000c68100040080c1400846010074000a242c11030444003004810007085519082000410021340640680c1c00c016040904402000700c26003d4200080d0400544101c1181591078081c0d9007003408103940c00035951601d21018038200d060403950128001c0f4946140018842c0c0c40d4426140000001000b030b184030320030485154440d4000441003150f8550a82c0b00000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697385908 1250 697384658 697384717
    0x5090a11100525030e030109050c0409050c0901090204090c0903050c0906360603061303050a170a02090f0f0f0f2707020d0206010e1303120c1701080114040206 70
    0x102c100f41040d0202e00700501e001050403864100d2139010760305100f20302000403c08241010102d2041d03a0001d00401a030410303502d8060b4000c06aa04681e0f5403002041205403900203000b920301c404030074800e060007143c0c22212000310784800792407500311030098201ea152502c1241d8120f5401003030314405940001080c010013000300c40588111b04000884030400d141c044020364044c008074042e10b0309103004094408140c05140e80201003040000f190a079040c0a070740540342c0183c600000b03a425107402c9a150380294000402c242c458a0010104040b500e803404da035400080d006030546000c00e0001c030500040c6008413010a5004000d5115140ca40818020194003c0c00705141c10400341488a0060706181d0300c0c0d0314080854006400520003603002854a41c4c002c1c0b6082c80b00c14468501d400c0803210100d01500b012000381c20a608181c10640c410400016203c180101e4005079170f80b2102c560807901d400360000407000502000a01515210020301140c1d03146600c16a901c40e0440411364 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697387158 1250 697385908 697385947
    0xa02040629090603010614130609031109040c09020a03020c12070b01120309060815030d0f090b0c060403141210090506060717130302120f0105090a111005 68
    0x904040d08001100d10801c1514030140040321261003032880d09503200085000c501c03050140c2828080c0c8a19208540c00510b411200000264980e46180703c0d01c0c0e0b0b10050585010b84000e075009000710503941c04915142c0303541400b80394455208580e044c5030034110000b035004810304200307140d400c0c481c0000104040c80001c09402e014104203680c0c01c0309140c5900c06100681164130621074090b00d50f400240c110b214038040d5207031401d0803d11548c86080b4000e443d241c1c0b8000700e8060013030b254400c04076600140031039449039040d01d83c0c0315420340302c40414820780508607135030205610040c04900840e00030b89d4600608491402070b580740c01d021100d100c4a401003652480201c004c090003c100d0100c440c841e040d000501114480e140407040c0e2516500d802034031030720701072054000a02d07204c4540c0342c061b001e00035035010341450b0b401e224140748541c0760700121000304095400d140c0000d2460502017030765864580d000000e440502036080900c0210381c9090310b41804d000c02007040000c00c0c00b0355040b11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697388408 1250 697387158 697387169
    0x3031b0606030b06040507050711040203060a030206360f09130503040b0307030614030a14010e0a060519060302010206040f05030409050c0c071a0d0b030c04151508060a06050a020a020406 82
    0x1c5454248001884110342d1b000f404070381000707008d1200302c000a82d40300240c480d20004860168a903143c48000030401401540001e500c84000030300f9080c440c0c00000c12030403401441e2b90103540440c441104e080320b101e070703c400b05501511280b49000360f45010742e1104d4204280b640004a0743c40e541d600c561550f4419000080c14490100030000d43d1036040c0500c101a003032426081280289207800b0a980e4240c0d01e4004005810151001e58600025400003085800ca1401c07200c11100c1703401c00324010a010b4840b540080107003074000003800c0703041c010003003144e506034014000c5a441d40c5400001c0725800d02c08030342a000402c800184c04426005490081c202045043d0b5101c00d40d11695141101c290f01003848880f24003081d210031b100440588001c1000341a000c5202e0300240002420041c0007003140d41e115207004030390306109040112400070b42e40c1d51151100c889144080503a5808001c80d80950f2120a0030000c0c400f141c818006005503c0203401107030004a503070340c0004c00307a82240d0440c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697389658 1250 697388408 697388423
    0xe010204031b090c05040522060b120c03010f051513060e013f020c1207022112090d0b04060f0b0a03081e0d0203040b010f09051003031b060603 63
    0x11500c0566080400b100100a80c00c0700700f00c0041e068201070078a0003184203043c49070301b019440d2801060744590300c107500b480b5003404115503920354501c600340341c104002a2140244401c001000c2d44444030840c4e05a0b11008034440d1020700d44001c01c1015081003038041ea214605100052800342001c00507405030810740c80f2092547c040900041c400d4540c22105c0244203506d1030759400c9641e4074164804540001c042c1c03411900441c0154001078130031010098454030412a0380800743e507404002e00b0a15100711815000b90f80f8404220005200700004413500340c2141075075082102c0e80c0b5000740b0088001a00203d900f0320360352903080320303003000b140c040e100306441d10540403030f040041c4140f0990510846144812504688513140d01d40540d00a0304100210a4044102d03c3c14040503203004030f01c0110159500e26203882c0c820303004035082c89240d403d0910b400c2c010840d4880c42c0601e03482030014040c6070a649103961412649074030780990450b88105603440350000b0544a005020286005c0c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697390908 1250 697389658 697389683
    0x902011707080a0b041a0f030304180c0f17012102090405010903030c02010c0212030405070e041a0105040b1f0e030f01090507060903030903081c0c17010b090a03080d0e01020403 78
    0x70603058030b1041d1251381c03140d4070700800c0100440c07007040d1250840100741c85288a001e4160046851480f8a030028140e00754250040d491013805600520303c951402d03501c0f40300030313400707020103072611810546072003500440280188400182c0e41c8940c0d081c00001d0b18982c0202c07149401080c40c070b000a540548460351254204c0c03003855050301404245103103d200070448200d44080c001d48802c0c01c10f1420302c3c4588000b02003001d001e0f003046044081c0c03008021542041c241490801c1c60002c07401c0002c841c01041c4c03000081e461800d031081c1e00641c080075104202c81410180321f040a201084502c0b020303c1881e072004040b03174800700102490220038000000d903204040c14414078018040e0300044c01c211310130a007030000030b90140384001180d40c02450035440b400c104403011107503c0d001e91604010340c9003400741e5108a510094500402c5440b4140309280e0f6200e83e41d80c002032007403040158010000300c1c400c1000844000041000c030749640800950b0058040b46c4500fa68400d52050f81c49510340103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697392158 1250 697390908 697390921
    0x12030703020d0e0601051c0f12020a031107052206150302072f01080a06030f0b0f15011d031608010507120212070c02060705010c051902070e0a090201170708 69
    0x400c402c01c1d50f007039030001c001d5503141200140d61602c503450603d1501c60601d402c0030400991072683c1c848254401285a100321410500959940d036004080d4002061210600c0303001d60046240d9041d07510141040d0b01c2c0c4c4810f1400140e603100c01410790721203c0c0d80e9050010310040b07030302052011a00b840d075016030307100c4071400d01c242c11041d4140058001c07100707030842a42c044098401c1002c465002e00340100720356201347c1d4032401400c16500c0900204900c0001d58104400d0302c0100e8070a042e82c0080800948410038940c200b8410b10f003429011802c0c0000f410600440140c299a100c94010225030040d179a00e000c07005804845c1c0c1c03111205a4441041c48901c503000b1039041094080310f2070450503c14000401012504098650014005015443c0095454402c201d0382565003001c001c2c8911440d007840100160701c440f60980c5210180c022444080b407010868034202c510084090706182ca801544200910a40700202c0c10310060480c3d11711030824500c0013030310030300703a5486a041d00d10b0900c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697393408 1250 697392158 697392161
    0x10c050105010b0405241210080f01090201031d0706050c07050418120c0f1e080c0606011e0207170a0f03090518190c1404090614220203070212030703020d 68
    0x46c180800000075003901d0142c0349070220240c8184154021495075651185100780c84c030450643c02141e06801b5a00c001d0303090400c150000300c0080d04c02c0c2e0301048000760907081c1c600342a0030008000c185400400042203c1c40c443d1015003240c1d8000c3c0c0c11b40712915556000601228440d5800021060040040005000e02400c1e5a050380003941404143c44004e965041c44d40418890000e251240c010000c1e200c1d00425208421681d901054041d070b01c619446045659400403584140011060340100424007000c0c51303219101e0301c1580003040e400342002d00318161104031214020b424800c00300d000011400c03090701d81280354002c1d01c4030340c40a07003480d0510a001c0c00d50340802a20f0312400342031040034155101843c4d40601150000564460182d8041b101c1c003180805040d0a076101040200b889411503003c2c0c0e003203070a083e21081c1ca00c82c2e44002d022800e01519080540500301c000b4840454030660000c5034040036500c1501c50700858108001c4141d0000d40d258000641e012401d0301e070075440d9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697394658 1250 697393408 697393429
    0x40626010203070c121b0602130902160f0f0512040e011e1206062408090a0f0b09070308030106050301170708030a0c06020c0109141603050d0e010c050105010b0405 72
    0x80900070341c9140b80100c1c0240c0001804400100f150a9110701e124a1912481082d00b40420500789aa190b20081c05c0c984081e401096006200403644040064134080d14401c541650b03045280e100104904c988400d003070007078400d0090311a4812040c0442c0028401c0c4240001008594003582d120f5060100811814505800041140d10344401d6130303840440c2f503411541106d000c1481568640704614003400945601c0c0c1c091095410520720080074584a8a103484964050781c0d28030328181d4a84410035511125000082d01da0500d0300700ca0400700300d912496550001c46481251011952960b4400da564003d901c4480022004001445090406030442036028180f40c0105441401c100040e9264454034010405104072490b40d042040301d1034042c5e42d0f469406c2c40c020040d401b000c2c18009110045805040102d0003400c0409002518005903102500d8100c8004c140340c3c1c82070003050f80d920003d00b0b84107060003942005000001c40034084ca41c040c2940c40303203a6031035074505000d20000b030340b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697395908 1250 697394658 697394729
    0x5031f080307081b0f030c0d0e0f2e020a1e020109140a0314250e0115032a08060a0e0c07020d0c0f050f090403051902010b0406 56
    0x5096404020301100001511001c60b0800b08490b5180100300220040c48600f142101050080c40c1030402c80000c08000780c4481030b10340301900e01910b0a40c108032807440914516a9002101034080380f154202035141c0340030021902895025654020102c01030110302803030b0800181d0180c51020100045007400501200740c41803000402c00c0a80d0002e040483d880c0140050008196840e20300d0f0396400c0400e034010b58014a00320b48009a458900b92150302c06034401503940036640c50b2104030056038002070f0464000d4101c480103642824800d41c41020204c5102d010181c8031028450400c074444a07807480b0b5040084601d60841804102500d84000148098420305100c5e400b005810041059240d1011002c0001c0b541c8160728030004451428041c0c000e01140d0b0070324030202c0c112a43c031102d40203541d82210150303043c0b481c0008206001400f1600140094410b00c61a1050681000e1026510000d80004105d410020010174100c800c660302440700d400220514140da50900d0a03400e4a201 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697397158 1250 697395908 697395961
    0xd05043c03020f120a260c06240105190306051f0314130b040c080708100e1212060d060c02011d030901020a031b1707050d0207080606150705030a0503 66
    0x71481090a52985c6041030040c028000d404a00d4591a405545c021600f629200c2001c1d1690380706c0400320350720300c422564000c030300410f20b00b0449640c0c0310505076007101405940d0286803183c20518440d064013070340b452a0a2544070080030400390b40e8121949400c2c00e600b06503e030207038144400141607c020300400c3c0025440c0506001d9610085060444526003108900c0d999440768940140d00741c2165002041a000d00400821201ca0209440c00c00610000d02404801c10000301c19486d6080001c820109410030030207214038500f0120354503072201c1c00405002031014992250810307520070400c44801070b5580d600740100301c110041900080001200214140310700040040c1d595841d1107c06000d0001440c0320581c25400720345890b01c0d1a5101c0b42100e03070b044d104074901c000c40c1c03c9000c04540602504142c19180c9100080b00e8080704c8201c0d00070642600c40318144034850001500507d0078100401100c00421707401c10003400a03a603140d40707003aa00c3c40d040722502a84804040d4642d0502c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697398408 1250 697397158 697397179
    0x110607031209150c031401050607261b030f2b0c030c021204030b06010e03190c0302090105030105070f050d0e0a0c1d090601090b012c0901080d05043c03020f 69
    0x102d4402001b60540e101074403250341e66201402c140415101165451500003204614000c03540c0908015143d0185580309000000351081d80c4107440e40035280503200b01100c14000c2c04240d00303c2c01090b40c9444510860b80810b038500031022000e03201d04003c800017080c0c41e190a07800d420b60400000300d11051115a4a00307090440d5203110003841d020300f6043c100022003c16000d0fe40d0103000b4000e0840c0f025100100580c03040c60b1441c0d40e1900b0303200a900c0740b442107000088078101030280c503120b14030070390340c20004c49144001602d107500311080d0006910b82c0e41c01c2001c203590040100c1c6e950715000c0c0e0b450302d0006151200c00d407924000c400040c0407000b5204140021a0000920075054078005003020510b80000001250301600400500c0c0148000003074050074000b5460120b445800190f0302211540e032181c24075235540d043c806a04001543c02c000801500c1c0e203a0b10807011824100090906004042280040b50641007550000d820741d2040100210300e0324071640300804d00280c40f10790381c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697399658 1250 697398408 697398431
    0x806060d0203030d0504020102011107141527070801060e09071e030b060114040603050906090c0d081b160f0e0c04090f0e1f1404110607031209150c03 66
    0x7a4040c90904566541e11175001c1001c681c000c0d003000d0702c1d250003400c40036165981814154103100c2c84041c0742c0030300e01420700100e1101c048c0c100158480c990306203003904d1650a8241543c0c40114500440c100d41c01051b4020405c44070a0089500801110f10103408a0401241c003d0404040e94400c040c1038022182c680e0702c1c46980303081d190889421216007815980c0d502c0050340d02640c0781c1c0103d000b19a0024001c100d60b601070b40140d00543d56541101c9066407050000d0307076252002c1c0c290070fa02413501c541d032100261083d0010071034482d03046e001000e8114007941d0301d450400c988000c0202500003580030f000910580c40381c0f400408540d11004028100707062911041e10660080031201502c0303407515568040316803c0741007060b100c40201c0d0790034003000c54200300900c46414001c11507414444420200800c006400c1c0c0601c1d04020095107000300f041c00c102d0320750700c502001c4091080114600d04900754510640c0c003014014080e0900c2e4052070600d81040b01d0000b0b5003141894581340d4480f29 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697400908 1250 697399658 697399663
    0x5090105030a021018050d061a01080907050618030f060612031305010302090f03070e070e04090510151a0403171603120213170d0906050d052805010806060d0203 71
    0x10b081d002d0b05000304681074184245264060a4000681100303901f480700c0d082084952081c0e11481c42c841841e0781c000050b8004598480e001c2d1110641e90740928003d201a140c044020180300c50807856801c0400040c0002c0b03800c00c6000e0144030f0b51034012000308181030601540b1040303c0620080a149440050250500441914000c15040580c0424009640e032210b004078159005c0c01011a10a00d590340000b00c0c40390000c95200000408010226503d030420780184050658444060020341c039088400034002c10350b24450950001a000c000591115442202d40b00d03558001101984c85040d4100000075840160081e40026800c100c510f14400502801c1c44540d41d240c030b4403401052074840d0b680040d000d410101109801024800200c4204da42080c0c5441e40584042d40c425110200e429a4119501d11900000c19410440891608070507880b207540a003900d03840149260361001501d5051f201c0e5070341540e126507204014070029104203c0c50b036200c1d10454001c1e0f0070100c00d078007103074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697402158 1250 697400908 697400929
    0xb07060c17160c150f0e030703080a0b0a030b1e070504080c010e04020c0f0c040b01020115030327060c1b0803040b0d1d1b040216080c0106030602031005090105030a02 73
    0x1900d6610001c90990300e210f620401100c1d03810405000f281e880901c82c2c40f00811044124070a014500b0340c1070302280b03401009642d2034a401d6100d0080039960468401c014205402080d0b41c03200c50700c000440000d20720403507180110710024400507020344005200c00441d8000d03001200380b1509100400c044880000e44000544003841c1c410034651a44000c1406802843c1013046540221920b80103004000034074003603900c8044a080c499010343d400164200c074007401d505100d094141700c003803010034001d05a803040700e0204400c00806583d071071001752440a040d017000e4009415201c0302030a22566030b00103042414609800251103191100302d50756449a4810f4140c000c8002c02c1601c4400041c4d4042020100602c0065a00300005803a0740d841d01400c5001480c03e50580c1c0e201c100c01e06040c800d9408a002c0a01882c0340f580b011b8469110175000387c0c250340341664a6003030110016601d40060b502641422141c4800360341402d0800c48416416003001d07010754081c518080150381c40310043c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697403408 1250 697402158 697402171
    0x30a0f030207320d0e012706111002070c0518010602030315060d32010b030c1803010c110d0201020304020d0b040f05060903070303111801270b07060c17 67
    0x20b102144039404038928100d50851000070700134840c01c0b00d50150024090b2450310000d80e1740b04005020701c800420b100e0004150481502c181d01d0741030001c18098200a51107601c000c04541603880540b01c040c082e40e102c602d0840315046007078000c208a080c03030380786030321040b181e030400c00c85035810010000d64a00004091481c8a03070304542800d00c6444080403242554030010341401141400f00d4507204081200c01c10030081c4c075180741f8950040301c3c16000681a13800300320b00c69186445280c0702442ca504840011404024207a2141c510303036800f4818000307540c80a46405d4047d41c84500d07035504200c0711400f60300a59004108200046c0da4010a901205034480f0002401e500c0b2401e02c140719a0301da0030001c086108903010302052180c00005045100d110790303000c1c03041c10011400305070a409220b0030040d540206862210030b96000706001040049080c20280b0f4604080303d200ca04058154041c110355480000c581d801e00006004080700000c3c542410103840074092207111007540002e064 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697404658 1250 697403408 697403453
    0x12607050a120603080c12130b0a031d0a1b1809050309032a0f01050702090c09040f020403050c030d09091e0903021b09070c1509080408030a0f030207 66
    0x1d5a81c000d018400c100241008403004210641d00d0f85031a03041c030ba01507551000c00e80309002141007503c04240480795080e80a890345001d0f9850500460000e81180d2080e07401e06488008158000080341890b502194005c40105054105400e01c1103103651144280c0124140700c800500405043d44a091084e810303040b40014610321504020b800e6000d5010165130501a8020703008403031300f071030b130001c0821030b170085c8240d4014106808011004010a84041c007156050012034090700d40308c2030007540203c030b102295140c80e42c1c110001d8212000200c045010540c041010f00c244401086030420321071055000b059424110f6001800d80e507801d12030ba088541c0c440c4103d2101d4a400104aa01102c0d0316001b4029041c242c80e010b912082080d0200071018030a141e0082c562420881c5140200300c15114180c00100b20b440303490644c9541c0015642964903800b17190009101700c1c00806c01054003401640c2c03600c41020380100072840c081d04840405006215420208884841480b9a00031940340d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697405908 1250 697404658 697404667
    0x3160503100305030f03040b061c030309020a0509090d2717030d020409020417060c03130302010b03031201081501180f0f111306080903030a05071e090501260705 71
    0x390150703407092500010414003010030b510007401c28140c081c5000718801c142c5803005644840c280119050403032000c2e00400010020040440c0c025486200c8890002d021b000c91107031103001040c0240300c00ea5642806610007500c007004158002042c409490105a80d18022001c20381d03011055000c80c01003002c0840c8580c4901070070314081084405504c100c2105640b180d6440d04040002e41040c03040910145c00d580f60011160b8010403114451801200c2c0700341103440c0d108039105141290282241990340c1e070103000d0041d075000c00141c03100d41800201c6d19250360401949500f412000204070a00c2c0040d8001441042072403122a01e29400038040000d2201c0d2084094001d440b010107120400340c81c14051001c890106001080c107000c01055117414987d4a40d0300701d421010440f9102002e80043c40425002c202c107030080c94005595181c0700da0711503110300b0900e0f000e440c0844139001061400c0340411855070498030741d413051200708009114000480842141a07c001820901000340009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697407158 1250 697405908 697405921
    0x11703040f06030c120c0207061b0c081e150a110405220c0c0c0312050c030a080108060f01030b040b09010f0e0a17040302031b0117071805010503160503 67
    0x1950020812890520307100795544030003400422162013500000384010b0101c200d109a180900070984609074000c0141900e000421180384442d40401e0407076084500d4641c0103d05881c05810203042004003802100035071901a00c0c2404114480042d250001041403811f240c4200669900440e40000420a506125078a10f103070b00c01c54011651240d40018480c040e5000f400354083c480c2ca00f0b210400a40a603010280e1720f9054010008042800c041018400255004103958a0f120309085c05420025942d54042c210b80201c41c4580000d2403032001004404010003c0681140461898445a50441d219a54000700040000e03104c40010000700300900230944c45092a01038492040240e049282d080c00e1711100901f0050b2004084081c4a950300001c0b06c00322821203038020001d00c0f810501030031450150945d200302505104500b07030181c0c401c42031074110354828030840e0794055022903c00004148900281c04c050f040103001e01c204041e100445035007180144050511070b45942d50f5a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697408408 1250 697407158 697407163
    0x3150902090f0402010311160f02062a011b17100b0a0c1a0108070510030902090412031b320c2d031206011808030901030c05070203060117 61
    0x202402508584400100103040c0880c0301c1d107034001c5100740e9050006043d001c1d500280d0380100440220b80c1010079036400b0003d80072290038038a2900c00b03401c540c03c2c2200740911642d001869581803450034400c404025241c0000e01c10074484003908a54001725404425004001c2282101c8403e2640c5000012881c024000c1c40003200030200ca54a540e07603000f420300c0086c00d40140b000c4c00c032021016401d100e4844014681501d050f01c07447c20007450250301d000204842002e0384250f420902d0354400f001d1000d6190164000c0c400d038042c0408181601c1c0041d0010103c5440c40c051070700301d8036100c04642c0c28550180d261098980c2030a001003400044008603030b038036400d80340d0b030000c03421001418005800c1c001c525001041310b810200c50314910b420003a0000341100c0c01c145121500104441c0804501c0e42d40516044070b0189030004c101d280070f03407061105c0c01482e000707a0b245a0001c606010320350791501428031440c3c0c80341703800ca08011070743d40425620107040c0621510300000c03030600c1c01518001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697409658 1250 697408408 697408421
    0x10504080403200a08030903010c0e060a080711060903041a07020906090c04080f0a0201180806011a0d02120a2007020405070309081605070608090312091c0e090a11040315 75
    0x103180813052681c4100281e80c0f035010f4030155009500780b01205a400b03014001070509560040c2200e441d1a1a065080300c000c100244000c0034466004000e100002c010440b003803144020800640d500c60808a40142c5c04030120003c907080b00d0100500d00c01a20b941c8945034000c2415201021580c89500c2041d042e4000c54111210314030680e07440c82540c607000620441264001e88416500d221a01d403e0040110180142001d030740c4004010801c1d00c080e100f20310044480b420303403581841503003e04001a41c0c04030b0304821804e20840107014901045100c1d0903001c2051000050380700c41e2180d50340f0001d01071500c02078807440d6104001100d040c02070b0032880d002503004da2560303035811000d40c03040310320040264241c0d02032040e0305003c1074880c018813a060043c800d401c0210b080c10490205503000600c024280c0010b4020782080341d000c8204c0d00445000a1142e44803088095041405e0040c5494000e240303e80b00d504010181c0b4655800800300d80030b581d00580200010883d030458000602074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697410908 1250 697409658 697409723
    0x1a07030c0201120c0e09130308190b0909060907090e0c04051009060b0c0f0111030f1302030708010e01050a09030e010507060204030c14090f22020a150309050708010504080403 77
    0x20480b0044481e039100c11700c060b0160003261601c46c584c440420080000141802c0240411229404180f55954032082c80d0810400000701081d021076080201d0b8882d4400e49482c80550302c0380d01403001310349061005001904a056003008148904050b10755140c142118182c0500d59620120b20000024181704c03000e0081c42c0300602c15256a6090520a9441020069074500515050b61050001070041407441c0803210003031415900c030b07500c405014420252407420882c442c810f02c000103840070f02c0007600034400c080001508910014056003500d800800e490103842c604840100000e07000703544100141d20070b01c3c1c820785402280c0741800091140d5000508490008100001d410004508100c0100001c0c0caa42d1119100c0d000c81c00101d5405890b69412407a001c0c3c0c3c0842100800c40e0560a40d50004090700c800c80c0e42d44006e01da10f07105545110001980790402c003000d001080040000506100008000c58905500c40c03070404e00803404010020101000d40203a400701c11400d0000a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697412158 1250 697410908 697410911
    0x60f0c03191503030c050f0c010507060b030a0b07110d0e03060103061d01020d091106190e13020301030b010518150f150a030522020112020d020426071a07030c020112 73
    0x15141d0801a1208815400c2186d10b8454a081c0703010144011070742e000452410b0311102e0804001c2e13910340000c5c0100740505030300352245504000103d004801c815004d02c2c4103440b200404114503108500702a90a140b82d401e200200c2040c09a80c2c0380000d074181101d41064002401c02a02500c52200d04600c0300107104541c008179480c4000c02240d0320402c40716115000014000c042c0d00244290360080e00207074005441c4000886d0003441c015820580c0004d00101002049049808003500301d8100382c005650554414006101d5414154980300301d84803802079104031032516044c2d418801c000d44549a0003101c0103401790a0a4684580250520408006441c0c0b40c00f41c403080140106801c903141800e0302c82070580c180341c1d04000c072100b807107581d010f0b17448104403103254000d68080d5000280507182142e0170270002510b140120050400401c00c84040d483c04120308409610f0560150018840c105500d442080341100600454403441d50504020400b11441c1c00103a07106001405580c0c00075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697413408 1250 697412158 697412201
    0x9160314010e1906031e230f0c0402090a06030e07150509040b011110021c090503031506030114130f060b0c1203090a0b091c080405060f0c0319 63
    0x20200020b140d88940340740303203110148000390110941900c07040c0c480a0a90f01070200340ca0010400405001c0c038035030040350700c2450201035104034005c24010000640c07981d088200e1162420105004402d00d001c0d04030307003e600b04640d003000110388820300d204010506a03500100181c4a00501140000f024000b107090740b0026440006440c589c84808114451403078464915082d40c00703802d01c4814900042c000308155034111007034000a60100d114061101c4012140d181401e09074002c1c3c0e8152072103103014503104d0030068901c00301c00c400000d8482c850302041c001803203404807100b035942c1b0005c0304440001000c219402c401d4010b10030740000c01c0031241042c0000c03c04e10703d884000d04c83c1ca400b080855850103044158140b07940025031b5103035450740042c45103502040d400d550060f0001e84040640d81110440c14916940300c0c041c1440e1400f08000707008000602c14248211076103c140020b607040075141c001941c481c0c9200040491404074040711110984c050254040d82c040c1d03300030f12202c03c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697414658 1250 697413408 697413419
    0xd0c050d060f0513050d030216050f0d08100803030f06060715060f290a02030d0515131407030c02010e070305070e0c0c0a331b0e0916031401 62
    0x5049082c59180040c0c0c28030010030841e1303011402c510b44858211010300748a142c00001100070758841130310302c180c40455284082c0410410302164138200082401400844100e1501600700600181207030710100700207604102c4404003100301c0380d02841550341e040d656a10280000e505000c4c4803805003412000714021082c0000329031006054880180400500c1983d40c107031041c000c4104280346285c500d001900b024402c02d0300c4040e001810080c01501e0505c002e29600108464007111035504d40070014000390594140002600815040303010240705104880121451008018101d0780070199214400303041a40300790700c4589412154002d03100d8090f0b41c0c0c01c195036038120500a0404092403180400d28005080080325080785801001e0200940d194490700c2c0c0c04004121820341540403a01c100d07200208840e51003e04500c242000101044003030600f0b800c0d5101c4100f10010310044036080042c0b039440ca400c0c0755010700311081c4402c080148100c1103020b0206e508402041401f0b070305c004240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697415908 1250 697414658 697414661
    0x20d06060306090b09072c0402241c060e04030e151b010b010201020703021207033e01020309071a040504021911070e13050c030f03071b0b090d0c050d06 67
    0x64000341003100c4071551101040d147c40c010711001001260403a0b849000203882d08080d15500c40c0c00286102ca08400d010134401c03580d1800c60550308850303c00a40c850204060304250400d100310402c00b000244e0900d85503030308a88000e44043c0c140541c61560032450350780c031042488004427180703442e501c40061054801c02c9880e0b00741080c403c1d500f4402c0d5a51a94070510a6039030840c1c268ac0205402c0c071901c0407007203103980310180a0301041b40c4840b11a090001d0b61070140c901c0d1a8056404000003a0b00300720100c1c902c441074441405034010414172005c100d00160000c00d1341d82d071141c100220350441c0041c600c64801c0d580480d400c0303800840c03000c944001c0711b0a500c0f0a00c00340c2d00c50b04021004040c3c06900d4100601540380a5044030011078100b4030701e00d0354105c109200c0c90440b41181c83e1440086d10740b10011500040580c400503c02042040445a500b049107901281d10324013410001c1d80c20240c042c1c1840580140b401c3c8401c1c4040c4008142c8085c010000501807034042c00080c10100d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697417158 1250 697415908 697415911
    0x9171e0309010305011211090a0b0616030e1e19050909010501030c0b0c070b070305070b250201020301080a1716150c0e010f052a06010f0b040303020a020d06060306090b 74
    0x14080303803404c400001d02c0c040b131071441a80f95521041001c603060940c1300b00004404064400418651364100c0600c084d112000148001c558111041400031624640101070540e900c00581c000d102c10303040c4d8411034400394100b0b0003920301122840c020a000c0e03400c5047c0c0034010f90220b5480150b0105020b0780e10410f500c100d050300d00a600c0b40c0011504c1d48002c2c18036114200c02480d0a901280d803c00000040c240038188080c07003840c0c080d103008556240c2802004003601e0500c2803018000c0818155018940d00f0152041d040c0000e45c00e5614119203d40c9a07a8a500003500300000f1240307403002004c0b40021150b658141903515020840e840c2088410515600c3d810b11100380781c1201e888515004000c0f500054205070344110f5642028601105c40740c101001c1c03542e805a00d07000c0d0031090542007819040306072200000345100e600d00420700348000e41d175901440340f5076800c110601c0800d60208005034115015500304241003a60700e00140184501c0c0d0016003c6882c18024800300b03c660b10669 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697418408 1250 697417158 697417177
    0x310020a02061006090603021305061b0d17060607140706020a02040c140a030902060432040b010503041403280210050106050403020409021f2304030309171e03 70
    0x1a26030b0f5540701c80d0201a00f0041c0034400104000c1841001214400d070020102c251200002c05070b0255600d010414603004441140f201480340300500720b4aa0003002040e50028543ca086241c0c00b8044001a642d010013420050144500042400610800c40d500c4944914203400702c0e142203a561000070348403841210120301c01c40c1020104910f040c403c0000b4080e52003c00805464611034034800e5009010054040740c202805120024050400c2095400c09103940e008041c80c896864000c440014401c07206603100c0c0c2c1c6800040d410590740a42a660300541c0a5503c040c0d4084508181d45035010b002c407085021448210700c007140090f01002031104004503003c031540710341c0340c00810082d03d400f4010300c3c001a000340400c001518040d00410f08290024041030000c10996001d0002403d64580303c00100349545242100944442012401c07000038a100504080c1141d1340241031141500c14074040b5440969044200e0701c044c441c21440075100c6130352101c0881600300f000c0e1030f6040507502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697419658 1250 697418408 697418413
    0xf06180601061e0e010c170417150619050406180c0e01141809040f02031005040803160e130510080613030309150603081305011b03030b0f0310020a02 66
    0x5642c0c0c040c12010703883d9211140905041d42601c64225101500c0380040d6042100c040103034000703d0b45081d000080c4a000c04200b0f82c3d16814081c1c0140c941c002c54030008003903807000d8000b1005940020040390405000c45c1c0d103221000f52003618420f08400d54001590040c9042d10004001d0180c1412601c401d59611081c080302c503c40005a0f28581d200c1c8101e8003140355003112000030710130200180520445545848221104132000c46c26447c000c0f07800b2608164032484010030f40c81c04102444585078108000d0040d40b4150759090a45c0c000640354030080c8040128410846000703071440703a6041c5c8041c0103400d010341c084000c00c01414065490074044508000c0104488901080161044174905001807070302149580480003800c0c1e8802c142d8580301d401c0b6a841410702203015031001103000c0c011103900d62a51104d040c1181031140d100a052103c2820280d04041c2145030f2800c20075014240000d90300e10007800318280c407040d101e0095040c02148140d4441da810380e4094006501705508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697420908 1250 697419658 697419661
    0x30d0203010311040b011e0c140c0301060b070804061d040203040f1b0302010512150a170c0409030819020c01090807060b0f0d060e0a08040305010218010e1e030f061806 74
    0xd100c210354070146101c0c002809001c447c1a4220500060300c0c00051610b802d031015180303511079400d582010a803000440d0010741c091070032441c09008010180c00c000c0d1003689041013954441000740304501c141f40c10f1200601c50004050111118000d46040192047d503603441d080c54203101005203060121202c4030b090760041d00038104601d442081e6039042c1c60345450005001451307686804000e0071010a1045407010b4507490720b07a911080001c4c0140c074130004807030300701e0710707029042450003411903018516012524001c60b44c041c008982081002c0340055283c040c021060019104141400e104c0303600f0103003442d0822101100400700d43c3c0c05514104684204081040318030012aa02c8079404901d200c1c072603002c038401364000080c2c0e01585088481c800056550120390350081e40c01650940d601086004211040d410546e4000c1000d203050180009000b000a040808403025a00c00106880321005103450420250240c540c00804407001071900c45848035040d08401c240003400e018160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697422158 1250 697420908 697420943
    0x80c010810080705011b0c0e0702010e0105060d110f10260f061908060c0c100902030304140f0d0501090c170309120a0b04110109050a0803030403050a11030d02030103 73
    0x34203490590b1007182c090110a031070000119485032a0540c1d00740f001d008056400002a24140c8200040000900442d2280f40024000c1d0860b0300c000c0b96003d059060008000055480421907544c1c294808041c0100260300030204044030740301103115411140981404d84c0a6422036024a4030110f20f20008003034103108800841214020b40c1c01c1d07440c600d0140702043c1c80303140c00780403200c984191100c2034150300d9aa03102c1c4d82c074000044c0c0d4100b200c0200000c480d50b80040c144800b00d8040300c500014490b030000d650119035213100302c0c0700e2540c54901d50303080103900f0b43d20f0606503200703500001d1075030680d06c0381410800e000780b0103054211041404024001407154814502022884005010310f080c100e240c024051151400c00b0640441e005807009500020a03810006001d240211600100c1c020740a002410100e00760300140c1c840c030a41c90b400c10940e17100008681c1d010381c1c10b240c00c54840401c21030030707502490501da0b0075445002c04903454510340785d1075010794102c0e4062503100102c5117411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697423408 1250 697422158 697422181
    0x307030f061e0602031314120d0503160309020330070606050a060c1a0403050c06040302012f1e091c020109050906090720031308060a0204060210090c090501080c0108 73
    0x40031b05c1079094070018000c00c185c2c0d54941020b0810b07500601650150301101a01d90308210762030010702c3c0803940c044144180b005842d43c1045000c0d1150030304000c218090b0300044e076981080340240301d190445803c0805502e00d40f4250507401c030039070341d680c5440e070000d40380500140a00e4010f40b03014004241c0001611441070400c0181035400080030949a901010504420701c0c00400540c02d00004000c45030302c40e2410002c20748107030300990001a14072480b8040d060b08214601f0300904aa0000240c800b8100d580e200712903800800750200f0941e862450007440045c050032615990011200d1481800b08001d124010301d1280b00f680c410700307056254020032500d01c0c4c040c0c034102c1d00002520000b8110381d004448503014180d60701100352181c40016102c0385950701000503551140004c842c2080280d5081103241c5d000189074405500302414201c000713594614100e80700824070349901404051280c03504504000c0c110081c2c2c02d000710342c0c4a03000c4940d00d080c1e0003021400560101300240d40030350035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697424658 1250 697423408 697423417
    0xe041a07050a0f090b040603090b070801080d0e0a030803180f0303070c1506050a0b070b091504020d0c08030307081f0506040909110402030f0717090a03050307030f061e060203 77
    0x4a032a10340c01c20780e4100d000c50f41c059040007400184a000103000c1030910000e000b40000305220303a0007050380421807518820106018010f9020311643d140140589075002c90301c440f40711100d2800594414449000035850105a440a0603c5a000051004904100e00080e895034411002c407034886003441003c0d590b07440121845c00005401010030380014601c0d0102c00090588400c02045154884002500e643c020358490a0b40340c10024a050030032620743c0c100c9504c4424000607181001c0c500003002d92804000300024031030f038403904400040002e4050b2440140c003049049903100d00e03103203201030300c588000e07211710021030060110039010440c603009450541e200509158106403070122044050f21064008035181e14040110a09680781c500c040c2d4030804040d13070300c02c000382000803024200302c005181c810343c10b02c203443c100180b240340003401e154480d501d0314100c4e9880c0c3c2d40c1c00c0101c1c028460a0034585802e414106d0005d2028204615808001c00031420410350f1542d5100c207a0350780c0b28 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697425908 1250 697424658 697424671
    0x120e01021c0e131d071509180b06070f0501020702090c0a0903030e040f0e0304090506012d0c0b0703090b0c07110f0f09010602030d05160206040b0705130e041a 70
    0x3502c0c4211902c1e00745804502500e100311403004c038a44106822201c00400300d01c0e10b80625034000300d01009070f00c0c43c03510000424150f82c2401a0041e040c031180041244142c0070607100e2a80f0344c00700030740c04c2e110101140e841c190010007041b81d107000351903e54040d47c0041c02c143e00c104c40341c002080405200390129100c441240c2c43c1d8000040c9180d40540e03501902010b420340c0a03a8030290600d01101c0e5001d9000d240300d200002e16070b5141013414020031503001825250402190750407180e8a000000d417022600c400b0724846044508040004640203141c1087c0244503207203d1062103000c0b90950020020f0ba4800e040052580d502c0c1d02c0390b00c20038000c0c00c2000e4404500055040d59030700301900800c1483d007014101104c0c403d41080414043c3c0002c0c0d2101c030040e403000500c0c01e1407010310300ca0306800c80c056002d130700e441a07000340c00256106000b50024140210781e4001c43e1500d4011006c440d04890702034030703140c0070a80d905d9a000007424220b80a84a200004a50346207500c2514100d0380702d0036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697427158 1250 697425908 697425917
    0x12070512060d0309120f1205030408180607022d030f07030f050708010207030504180902130b010e0307060306030203060f010602070e0915010906030302010c0e060307110a120e01021c 80
    0x40c0d4600030840b25451401c41901071082200c00031074551841d007207070800c450040b000742148030194540a4801000001035004010050041c0300020709040d0031620b11034450555824500780f040000303201c41c03280c0c50009611509e0a104003005445401c910b24415080c43c4410014521032020f1540b07420103051540000c0d00500e0702400040c00400c05030380168007401c12120b2031138403034005074221b0340400c1054000c12004a020002d121041800b200444040c1400340081c8400b079002c5001c011000c031503200041c0d1943e110003050b920600c0c900c0760945000f0101c40c0c58a0f986d40014006042e1070106034068080c502c00201025210382c0514100c0b00d4950003401c0003440c0a900003208500034003080d01500964009030898201c3c400070398007901c149000011400d181d403030040e00b100d05006c01c400902c440000911100d0f643e6400341d941c03003442c0d802c00300c202c5404007d2050602011042c010000354080000c0000c0e11f6201540080e6800282c0860b00c0e180066a2100044440c1440040018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697428408 1250 697427158 697427161
    0x804240608162427030b070c0314160215030109140613111326010c0e130b031c140403081e2116030c021207050a120512070512 56
    0xc0d4021120034040310342034503280c806103050701c82d042e0010049500525940a4a400a10030b000184c075040387c0001842c00e001440ea80c0c1550054404064a20740c114443e1001c02c4540081d03042da9812900141e008041540d905001e403d504c0c2c45810a0080545441c5031011070100b4860344010540a550009c0c12a200c94101c4480b03580038010020b0295000c080a100c588145914106603c01170024082030746010116080c0002020301070003001c00941c2e05080c8400c005035000800d103810385500340ea034121024020720a010281c0500310200390988030b80340101c5403514844400c03914414190313a0385901c4a8030500e61038034501840c0005055540100442c1d45031200514415200900a040b220b05043c0025881211034202c000309141c1e8002c20302c100402c00540f41e03041010614541010405100c0241d0000e55071004181c1c19184a4000211441400310401031034803007030750180e603070050300c2160078000304a0b801c18031420300f03456003800100f032009001e0702c255021944c25010a441a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697429658 1250 697428408 697428449
    0xb090a05090c1213060f02071203050603190302010b0a17060f040623090f03031b070606080304081c080103030804060911090c07050c1503040201080424060816 70
    0x88030700107004501000b104010494881c611078201c940304020040c25190120110f040c01c030159107421052029881c4108220f00c0064a03d807044109206a4030b4005a04e50380c4c08040b03032401408101c581200400c0030b03e02010968150801c840010007910f0050f041f540d94641c02c10020b0903414094041e42140d00010442d131101546594460300074035011440200b03420f0280210340d04107410058913500e8004004503400c00304080c00c224654840110b16600c0c0401501d00c0781012211003c6003400009148000e0100640281d00640405010380b90740e640d441d504681d4513602c84d42c603a458181c40300d0400f0703100f138040e11285040720323010744031a88c1d19590340da030324801032600305001c0390382a50b50034414140b45c4403015050300c22541001c1c000d81c0c03030003182000c51405e817000c50300901c102c4203c041c9100c1d5003010000c0e00d07045076080c28480c0303a40e00d440c5003080400bc0c051110351203081803400140c40d2040308c0d42205c421910b040b015210716007003246440600084a0003421100c80804028014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697430908 1250 697429658 697429669
    0x4110d06240f050f04060804020414040b0a0c02030906030a06060f0302070804150315060305010f0b03040807171b0601030209092e1e0b0a0e010617041e06090c0b090a05 74
    0x140c82c0c0c6103140c440d143c21660010981c20f42c102e604801c0c00182048100000c6007030502c01c5202c5542e03000e4802003145402d690310300300880000c040c03400f8503443c0d440812030f23580200240d9000000003440d8503101c1c40c06c1071801d001094a031103018005080d004c500081e0300c0c0a442151041c681140540345002d0074081ca0040601401a5036408c2595548100c0903d509210300600902201d9501047c154075048c440c07030000030240c002c910416800c00600000903c0c19088030303a0703076900000c2d880c18a010700c07203403501900680d041303820002d042d80b25214500d2400b10b0316034142d070b100701d50b110011341701c00000f00d03a1000c443c900e109003030300b044c10488003109659101c03019170340040d1800f1400500c20000384602000860386c41400ca42c503402e070750156141480c418000b90241c106d1300c2449601d03281001b001da00a10610307901c41200b41012500f407090b08207c1d40c1c60001c000d19980d902030800d1406200501b83d0450030354500c0082140490980c000208640082d02c000708155202803c0c5010006c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697432158 1250 697430908 697430927
    0x10804020a03150507030e070803180612070206061306051008061513231804021818060117070b1c09030f0e0d0b150a0504110d0624 58
    0x81c0d001d40311100002c00986a81c1c048038004002d09404116401d201001401340ca60542d250003d03034100d4441030025200c000701b560f61801090280700482200303034000c00c10520401421001c40c54035042000b514030340000b507142c01010295175005400c1c029071841d030211550382c020640d0000481d060192414810b400171a04844001d224019804491110f020241c1c001040300301d149540201c204204c4402240d1502c0c9202c20704440c0440301c24400000e1460780c810006181042c0307101000c9400d640b94604620706c0e003d1841c2003a201401c120303959510514403032050b02c070240b28510001c155444070300f0300403501c2c42c228001407080c0d504202c407403070343c6400034507814020503e034200c01c4e5080e4002d40610709129009441d06440d141c03051200401801c0800446402800715843d0140010305078580958007120000b05100081c080500154a2060700d0780304a50250504582041a101038002400052000b081c01c10805940f48407441703060500403900d1052100040c846601340d400f030034460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697433408 1250 697432158 697432163
    0x30501150806150a1706030f120a0203041a07020f040b030c010f0e040c051306110d0332090106050301110a05090a21060c050313080901050706060909170a050702010804 74
    0x40d500340f440e00d00d601650350001c0703900d240000c0e650013031550a044a03034419900401d05a020303151164400582540d01c504410100c2555400080d450380e55500c02c0c002c0c0c0b0083c18012602d1695120f00200e00503803500200800e91081d40701007280e404614244c415071507c0103000e00504100d0501c80015520a891f004402d401c0c0200d006604442d80c0da81d1096200c01e0960361100c903200c100d0300c00e95944400701d80e00320341c05000b540b1407a100803035030018845e40e18418900d03012079401340006e60720712031003403d040c0b0400c1c80f03002400a43ea00305400d4803003442500d035040208045aa03c1041500380d44103400d5038030381d06004000003190248984000d20005c003010701a030806940d0340d000d081000e50101d1035070100181c41400c1401b0001503000e07040018400d0b00c0c105056080143c0d440d00d800d04c081c400104415800202c500c0e05074062001d8800d0307035400c4102001203030394a00d4000094001c200301242c07007503814484402141c8442d415100c44504039514941821480e03070043d030314054060001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697434658 1250 697433408 697433419
    0x31504080901030b090103080c15090606060a03091b06030c03020a08040f0f020a030b040209060d0803070f1206180f180611040e0c0a020706050301050d170706020c07030b07030501150806 82
    0x204c00399440b4645420300a500c6014401d0b030341c0b10b003001c045080600401c10220307006000c0c8140f10750454005440d43e04441c0071241c00750340345a003000940051042000c010014480300e4030403500c0109075002d00089410315202440840b80303440b021002c83c172911000002003200c5030041008a6859940160f44c14407401e29003424400340c0e0001342003d0b003154000c4a48285000420045040200a09421070780c166554a1b00c04c0b03440c2c0d01c1041c4ca003c010180020083c22a11031400383c1d2241001c1c140c800803075034040081d561620b140e03400c03001400f820b14480d103080c051144c0c41e19001d480b0b240b0117066601681c0c8500101c560f0390f10060402d402d00b0300000041888007003000c3c500c030280b042c011500d07600a03987c0ca01023800040d042c81801d501040c03d001c424401000a9200c03485904a06c2d039002012200415400c04051180e025050b405800f240c4082002503051000040050699004000410345591400230441c25a40d00340600c07001d00600002c4144103e0041032080d03000301c401040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697435908 1250 697434658 697434671
    0x60c08061504061b02091603110a1b0213180516050105030103030f03020f12010e0f1504090c08030a0206011d0105010e0405070c020d15110f160212030c010b0a0503150408090103 78
    0x11a100340554422060101e0031f007882c130060b034051042c90700b50000a400c1600f040c00021000d030000341d42c210350812a40c0707c100c0c3c010031542c0c0c0030b0f120400103c010104100d0398904c04800d030081c3c01016400c03991031040c0705c28440c2004003901000122201650345504e142c0c01c50790210307a054220302ca8002410380a0280d4040200004040c2160840c081c071132600302d40c500b2607040c0f807042004d02180c0c04600c664080c40000c0c2096003801040702c03416500400ca54842d4904144490350035803090742a13000103c0c0d003410742c55002c980541203881070300025100c01c0183c5034500c030380d4070300380300b502e0100700c40017402102c90a248d00041d501882600300640302d2117154000c07980b501c030848822919040b40308409580140706104801e6403205120105080c00115a02d01e00301e845207d02c40c0d04100c41d54030b070042c119030701c140322180d040b01d101082c0e80c2c4800c000f44602d0301078141e106020384a00c544940104072030500003251340301d04071240b050080c9500c680c1c5442e982a17201400d0300e4101504d484 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697437158 1250 697435908 697435913
    0x1119141203010b1903022118061305070512061306060905160908030a0c1506150201090b2d060f1e030c0d080301030b0703090f060c08061504061b 64
    0x4001e14000e00381c507036201d540c03a4890702500c00111260150001450310620000c034014451740280009031180030302c10882c54031080c110681d90101401007103910701c254000c00028829110314040c2c258441e90840701c0040d00e83c41004004240145071116540c04240042c021814100e21108803c1c0a80000288242c4821281050340c10485000d100e43c14201500c404c1140d1242038640200f003040302440c2001004a40145002082240901050304002e100310a10400d40c0c811401840c500d4240d54443c0c6403090068081d21708040e041e0743c1c110f0254001103071040019520314401c080410391403041380001054551060340940600c0c1c1044800c0c4808900362a5a024854140c251100704000e06902c1e0041514000801c003200d070151241341c03180d4000980b20010b59040d80c0d4042200b5074166200b01044005141e0b8031809042881404907a03401d00c4400d50107486994450760318546155074507000c0c03002d41f11840080c44070390403080004008013031041d00c81007035100d1079401281520043c0d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697438408 1250 697437158 697437193
    0x3170406140f09070b03010812070627110a060f11070f0602030c06090a02150d0b0a14010e04050c0307030b0f06030a06061214061e0306040501020a111914 68
    0x200d4460044107803280900c18443d60420070940100720306006a4503541c14428440c0c1c44045940f0404200a0701058000c2040010b41001d1001c01c071b80d12407200300340c0e502204060300c0e114030075054901c0c100b610079600403800c0102072103060f074116495903091044800d00c1215949105881840c0314000c0010120f2140d2018000b8401405941c0c01162a00e42e5258070398105000603003208010313401003e0f503100603120001000c6070050000700d5540c46000c8001e0780005404880c00c1c01e58000c0450001240303204034940d401043e40d1083c2d0301c0c015403801d61814003044650540b948c02d500c2c24103000044001e4841d41196401e81340103071031001d950217290081151a00305507202c4851644602040c4a07031903010540341c04203450a941486450f00c054001506414040c0009005a4100c0d07450104840031400341052654043c040b2511440c16007000790003074010b90205800078615106081c540b6400217400c1203c84c81c14240d0082100d05583e50b840c8e50280151139182c10700540b80100d14001d903a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697439658 1250 697438408 697438411
    0xe0f0603100e060603070617010308030403052b0b01080402132012010602060618010b03062b021c05060c09120708150c040602030a0c15230f040317040614 68
    0x81c50001c3c030007414803204050409482d500090200108802418100c110903801c0c541104d4200c58580d6590b191410219610310076131340c00440c4071078003a90403000302403c1c010321a070369403014504002e80115807004680310b04043c5c601a6024094201c0840d0386111135004440f91008091051028070f1440c60344032840d0410001a0660078904004221311501800b109520020441d420030803002050f0303011400c8041030284055940303010001541d581ca45441c1e00c3c9080381c900c0200c021021400c48000c4100401440c101c1c0580c1e00300301c161200e002c038140070911460f0b206010701901c0d50b03840c0400030b850304480152644000c0c028410b480e00b40c000d0118801412042c406007450350303001c01325032500600240c9500c002c0802004100103035640402036a00038409403900d800c02d40d10781c1c10503010706400e407081030244500d045803070743d03130207143c3c40585040c00070ba00380c0081d02c2d65520050311154201200e028002c80d1180140d6031040903050203150740184a504000399452a034040050001c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697440908 1250 697439658 697439681
    0x60e010204230901085b0b09100e0a0204050a0e4309090516020115080a030c06020d0f020c010506030c0f010c03021e071d010e0f060310 60
    0x111190803004a007803250025000d03040140041c500000215404428815080c40006c0103c10510082c0c005200982c4c10010a803031810f4007049103842e400c95944100e140e141d0b10080fa42c41c04130b040c515402c3c214103052080488c64014a03060345424800ba08107040144005482542040041041d9403000b81420250005000071201e603d803946804140415800481003040d614061841a8412307101d044c100b241842c1d1605654070041c03070401d5884e001a504103a10103400c00040100000002c9010b101441556009000241041f15101c10a013079600400a054104140c0702d80400d000719104130005100b07510052900380701005003022034280200040c4a80d80018038410f081e4024000c9039042401100038080d8010b1910000e000807900b0304400381030101031000741c000d050083c40355201c0c05056001005180d07500190041c3c0b24007450050442000003900301004440185080f00e05881c14200c20200c0e0362128014400c11780e000828580d8180b003422900100e00d107503400381001717062 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697442158 1250 697440908 697440959
    0x9110904060815070c171b010f151409010e061908030406120219030509030c031809091c0e0d06020c0610080a0f06021b150412030612060e010204 64
    0x126a0300040e07443c480040c03d800308000002441d8000300d848240c1d01c90860691b22141e80d03540d220341920050542911840084951909492003c0b015140d080b03c20000380340340c000c100403900c0f81c82d1065450a0002c01c00c0d004014030700140b1803021035036181604038100401d191007010717161a51100d1000244c01400301500040307000c1281d07a4001e2408201c02d091200d055042c03641101c02d65640040108110702059150340c0880c2c01100c0a008445156842ea01503035562514a520b0f0311603400324008040c016400100010703601140070030700e0080580c40760410120b00380c41d008104e40300404a04401e0b48070803480180d02c002406071006107001c034080809003200d49007075515001001c5032544001c00703135006140f21100050021000341d890a500071001a01d40e40001c050f82d2041c2c1c546410082184074030680c80e4a5109501c1266104901c10f24003800c05444000d01201030b00c2044c03084104000d40d070364001c0000380d515048640d642c9200390005050aa4490301c9040404e0915141c800c0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697443408 1250 697442158 697442173
    0x6090901180507081504020609150f0d020417060f1506120403110d091508191103090118020a0311040e010510050f0f03030f030c04090507120f05060a091109040608 72
    0xc130500c80c0c1800400b04012001c882c1c50641c000c04c0711445481c1e0303190310400c010440041d2004000081d507060401e40070141ea00d41035100c01c0b15000394858012500c404041001444511000040140c4280403003001d008840e11100c9080a1800c40c0a50700ca50150701881034151082e14541c07407038455070203643c4104a980482c50600d00300445d40c8062010000c01c01c0040c0300204445c52409803c00a51500c119113584507031030240100c2c031106045803258141031000c20040d103c0c3c0b02541c0604458402000303401441d62141c0d0052050901c020340010009008101191060303005844059019001042c48002582030700e084440c215003001c00b1f1030400700c0c20712413810506c03410310350100199442d04d104031611000a59a004018030405422000400102508a52402c6e02c0007498041d000303200d103042015000c0c060100d20038401611078601018a00d000140340502d0303000e140060f0481000c1402c001b801c601409440d09100d00300c80d000c114804403900c641c0314402c000d240940144c64030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697444658 1250 697443408 697443419
    0x1207350a1107030c14010c202e050a020a0204090320012a02150403030f1410060305070207031a06150a05040506070606090c110d110606090901180507 66
    0x8454503038090a101c0d50004900b0300c0080e0303108901e070040c0d0300b4401c5814018041781c40100c2d81e440b0001c400800c0d21700d040104c08070216000d10030190482085400800746c8034400d03820f030b21040074420100000030750a440030b522613006030700820f1850b901e0710548981082e10b030045000d590804030104e001501701040726040008a0034101c81c0003505000a00c00341e0284101c40c81000c820b540b03000b00540d021610100c07514001c001108000036041c108062034585410040e005012070581444602d040a81c0710016066240320244a040440400c81c40c890400c1d03030407002420010030180a520482c100032000c10b0599071125904541080440c40e6440d010003440341501400040008024040c41031698158000080c0c90035220140c4185448481904044015000e1a881009000c1c0303068210311a899000e001c00b401e00300007100316040700c40d0714041110f00e048010031040d81504072201044540ca848601142c1100140d4008201911103044251520350f00504c11130301c3c0d50207278504200c07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697445908 1250 697444658 697444667
    0x310120c0b0a05161b052d0d0b0702060108060c04030206030403080a0605130e16031e03120c02010203041b14060d140108030703081b070803100e0c07020109081207350a 74
    0x1340c901907c9841b00000c0fa4040e40c5828001c13000740e400c9000c40110010450b03210f40400401c42c3e40c020860f0151030a0071540a0b440304402c0c041c0c00b45a000c0c5100003202c40f11044112422282e02400c01c51540d521905c3c201c031003200141124427520b0725101c2c001070590b216001288510044500000c81c08000702d2a545001c28807565541c04080d00d030806c001041e01090b100100c480030001230507595802c2e01c0c0855039100155401c40086140200c0521941d90541c055481f940c0f0401118410140e2100403040005043c803035802172404104200d074940c10000080c09034010ba154003c2041484440c0080c0d0040342601b11250035030011403c40305165020b070206410400d94035404410788454903c0242034806d217080a010b442c0000041144c025200100000400c03209940c0e2009007860303020620968087c030390a0740041c003000004541d2101c0410700d2545038030924000b84c5400c0180c1e0b02d64080c038400000e20444091890034820010f170002050140320b9440711050707a626482e0050142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697447158 1250 697445908 697445963
    0x5221e090b0a0305060f07020f01020a030902030c090c0301090207050a1202030a12050c04090207111801090c0e060301060320030a1514090a0b0a0b0408030310120c0b0a0516 76
    0x240300320050740b010404200080b920b10f030404114100f200c11583c84040c280d10f0b00250125a500540c4005030b804c1116a041d803200c40503500c21415540c95518185c2040302e002d00555a042d0103501c00c100401821007942e0082c808107100c2c1c1c050361001506900c6690402d01c0003500c0c000541c000103040c0900c02da0101803910b00d544d2907601040b003800c103400d50b000c40c0d00890040100440e4006054001c1c04004245030260460042c42000c0c07180f01c1c8103c0e069180801e2140c591124100002450320b0382c000c2254000340d6502801c3c143c2103a1070b04404401a00c0b4480d04240640f00c0700761180b640c207103520f0042d8401c00040201180c4100010403501c0303800e070b00b5800745214802611b201901ca0b91007074100340d000300202901050000c00080043c9100c0041d500c440b41c0505c00040004920320b02001451040b1030801010721752599482028045a0000c40d00800301896a00b00380107104150003e0309482009241c00340c189020a10313215014189080c0036990000d02c064545d2400d0f1a402002c3d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697448408 1250 697447158 697447181
    0x510021209121c06030203010203070903030e030705091f0b0c030c0d0c050c0103111603030e0c0f010804151107030201090624051c050114040314040605221e09 70
    0x14000310380400c06018550140c1c41d000700c85040903c145411401090f00114081d5800400866507801c2039040608a83c0d16403100300c0100d4040444003009140c0810344100321340000d403103100141e81d00900c036031942040c0303041851078856288010603d000c0d40400b80c00c5180d840c030011550b507201001098903160340f92852008201405d41c2c51707070010340042040d2009410178200400c07850240080031820740a6040f0086a0740c1580f8060000e169040e08000c1c1881c089005584c0d0340c1240900f800030344071400b5400b9020800070b40c0421b0001d01483c0ca036000e85404a000001c9603540c1d042e0383c40c85940900c400360010703912840310340c00744251403082d05150486401c606101c2c03603184031b10400c100414071a0300c2c822401c03400d80482102d01001036048045d0b004000b000012441102c41c51030010648069001488032450080820075031000c55080d926186c4071941044842e1010603401d4004507010030025454110004400d091002414044048540304040c0503007006480d204444a44504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697449658 1250 697448408 697448413
    0x51e040f0510082509200f04090b040515011b020301050c0a080a062709020a030b0f130f11040e120a030c2f031210170105090c100c0510021209 63
    0x2003290006880c2c0d020021a0b00e900340226040031046e014107400c01c51005800944100020803007480c0081e034004206548180e481001012070800901c000c9510456210481960340c2c2181099580100c00e680e44041710380c06490120081540030a007514401d46606104007008900c41d01d20a0300020000d500903100d0301c08101c1c0300d140c0b5000814a036110518a090103910f00060b00801c04160003856140b500a45008501607683c9401c481e401c0d03084405101c60000c603004a400000300c0d001d07814403140c022070100040d21294030b9490050300100401c0d50710694400781500d80e06414018079044148005003541c40704042d110140542c0e40b15882c100410801083d20324401c11080e0841c44d54217524519a4850002400364170b195224440c0d00885601c2d201082121641e000ca07107501c203854107120b00c0240b04904030681402c1c0c0e01c00740d07a0f400040d0000840e0010500b092900391105607598030b0140b0900c0e010f0749840f400c120510701c0c04100a41c000800c0108071682c00c8646420202c0c0500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697450908 1250 697449658 697449703
    0x43003320601090902133809060c060a0e0c03010c051608090a090209040f021c0b01022a030c01210509010603140606011206051e040f051008 62
    0x240680403408600800c0308180c0000200e501039109207084000390102850442d994071501c407051001564911480388502c07545050305508400d98200020844070600d20040901c0110f6030540c15500400905600080240402460088100a824080c0b44540f900140c03041c3c0084201c1c0c11300680c40d01141c0a681001100d007000c075806000c507202181c07a000d00e00e400240c14544201c0911400d900190721000c1d42d4030100d103a4489034020480e0350011039081240402d003140c0401680508071000e4090350810709401c0c03800c2d41c560007185034a00144180c4840703e000d07040d0b43c107042c4000003072030b4070034500b5242c00c0f9901c1c10100000038807540c09007445405980c111901001c1d03240080d201040312503c036800308003d44800d4200201555014001c2611804010181130f500c4004407101400116a41888200030b88507219803000d0f01c81c05400740c144c1ca010b140c0040c111b004400d80301074200e07a8843da00c50301c0000300d12500340125064001d600c0b01d90f1500d4605494074020400035601c0851114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697452158 1250 697450908 697450961
    0x4182a030e19020108040c03051606030c02070f062006070918020313030f02120f0c061015050a1701080d12020f0415110709150b190503043003 63
    0x36410754210343c1c24070300311449607142c1ca00b00c20303c03e134580d00041892142040c040f07038140e1a030812034180c880c00e5800f004004642c3c04e04036681c410718802d604020591104c10f01c1000e00c05e80c110b1403210b09070039140c803000a1501000345400340440703e11f00060714000c2c050110301c3c01e0b04114a0312464944066045040c1145268400103d00c07900409010709070207040c120364003c0c0f101c0c0d851100c90910464031071800aa5001c0b09620222207445640030f2000000c0d8840c2406000d24140c40103104804202c192500b4141c5403503018038544401c0c411150b122604045204c0e81880c041d200d0400034100044901704090902c100243d180f61985005110760181801001c0c140d41c02c80344440c000b0031461048210aa5a0358403440c0b111046004181d000300d81c0081941000503240788108038a50034a9607840140708501074801841a0702d24072a43d0f20070340354440c1000d103820a0060342d1401900309003001040c003c001500b140c04010301c014a00e50070440e058416000404905505d0380c3e807540081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697453408 1250 697452158 697452193
    0xc03060f06030a050a030503180a05060a0c030e0601120b2d0a020919170d14090a0f0608060f01050f16060b04020720040e0304182a030e 60
    0xc01a80101003400d00291169500b0058003108540040a0310071103241c2c0d003001011680121803407442c1c0306007010400030040c4002075500e1030343d400901500d01d07a00c8191442010301101c3c2c842d0fa04040d103543c10016400414083c1138001c03d401c41a8991a03a001c0c9000400218000e2400c00c400a410030001060781840043c06100322111800803180d9940c4443c00000b8021008000e40000c01c012103c41116000d10000b030590300ba04121000100b01d100030a41c3d01e038140d015200010b02e074244060340f0200684040c001c280001020386a0881e1034800249511000b81d10a00018010006121860a1950207840040802e00e030031440c05404000c44115482a40319038070782410400b03814018062141c3c0300801e83d050080040d9030302c40c5a410318040c6400e01c174864040c82040b40d041814035240c03e11481c00764032017420203181807900c0c0910300100c800326001000741c07031a145c138415550702914004402d080610031001c81f2040c4050783d402012a225038103882e41c40d80c400c0c0040401807100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697454658 1250 697453408 697453411
    0x180b0a0203030a0905030f041806080609030a03051b070309170304030f0305090d080310030209010902090a0e15041b0f09210206070c03060902090705030103020a2d15020f0c0306 78
    0x3c000c901e400c024a0000d00c2c1d03200d01d0030100009040403c000c9807116110701c011040c60540001441141c3d20380d14401d44641d0192440c8050340e00401ca086003040c083d8000f2548000c2c0c04a280d21501d001283d41c01d0306034096501200000d0100b40305100d4130100c0c404180030301288800450925040d41e44086000240c3d1a014061150120341c410240e6692401c1e4201c0c91707406083c4030344038203201c42c04504208040c0001c0344104042d50001c02d0800313884c07094482c2e401c001056404110b1800a40b58a0110054040010b0141420a40ca0300ea180c038040e031100e140c0b8400796501d10424480d0000c0c40c4c00d03a440703020010002032030300820a000f104c90324450707103500c80d85103403200c40207504c00511a4401c410380184000d01c1d0607000028041d4503800040b82c14000d682083d03440d5604042204d4038823003400002d60103030700b04400381300c0c001c40000645884181043c001e00d20140401e5480b00d4404036900c0304080c607140c00e2110944035414001c00c14043d000600601c6841c101d880000c0e142c010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697455908 1250 697454658 697454671
    0x705190803191e0801050d08091203091005122d040c2607090c02100e070e0606130e04030e041d160f0e0402011404030303090b0f0c0a081510180b0a020303 68
    0x3511f040d01400c2c040010308070740e22038034024036020059000480068494000d03a02081c07084c12846a030100060003402110344003101c40001c0c0103140c1c0c03107030404450000b4203080c7c42c0c0d15961301020704080000c04038802d40502c0c02070500b41d400d545052540c1c1500c2400120742c1206241034000a924600001024820348040c031101003030001c0c401d003040b80350110300c5480d05441e50511141102c400004241d8500f95502c1030030700460390ba40c1001f0700500e4840c0884081c090350220300204000d15510420310b41041c403900d8402c15145107040041c0a60380e84010075030000ea991004802811010081d41d1100350007034020070b84092419a60480220884c403807100b0a41c6804001411a8410800ca00d64803810810b040e441e0303601c1e03040060040c400313400115420720789200410348440d51800903d10504018120501d400000c03141100c44003801740200c0089450900c3d500c13501d50350b94174100314000e03696071200d400c0a8042612000191254840707600010700304040c0300d007183d010040782e50004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697457158 1250 697455908 697455919
    0x15060703052d040603020c060109060b041712041502060a0e0a140307060e071406040b04180b0a0611061003030c02010f170f15040b030705190803191e080105 69
    0x348141c4041001211007002e0400400009000b00354150558094510340150500721111603803134030172810440c0e081d8040c8481321135091108101c0b15030a64a1034100d41d00040039980d01c40850070080304ad6400a030000420791801c208003054031981041f038550711400064080c08600d07100c1d41c001d41c98008201010746910805100380e01c04080420072940e81e1070740f00b0010441e6165071807525440d08004c0c001d90099a1142503c0112441d02d00d040ea4103031504102410300e002d1400c1c8009464551002c02d2000003500c9220000040d0b507400c80c81310050169844214002188040c22410144010304022a4101e05003081c0301003680908040800f0341d085c208400402c40c080c10503180303000a408010007075400d5804100000990800d12405507511001d00e0b8682c20482c001c00c41a1503402c8001900760344215010425850704580140440500c0d1110f521210b440301141400c681c4029854404415980c5a00c0d66150b0302103980c0c900300c1c4820007100640d0710040700050240314181315062082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697458408 1250 697457158 697457197
    0x907080109090305040e04120f0e031507020a050a06050a0c1103120603100e0d0f2d0e0603010308070b010b03010f2619030801060908060126070b031506070305 70
    0x60207a0101e0b4051b10703480c509400d41c2e140c42d10300110301c1480c6444000026070588c2c0c00c0c2442600980340c60140d2040180a0f100c1014140f900c00b1505200612102c21440784c04034410200d5401d102500e0414000d80010072a881d1218090341507500d01a074110400441603401c10001c800441580e404103039001d21008a0784408000920300308000301071814030f41c0384c000200030490300000d4001e40e40710140c64910a07051080d4041d20f00714460003900300c41c2019603481100010180805034400921401c0400428500102250590300240c00890f171561000421000b84652181028010203000804501d03560400c04080e640605910440000004020800f8000d0541c81c5815102c10800c4044442c0820000741c225000b17003007000160082047c140010541612500c00001540d00d2400206105d07441e01403070300b4405504129400c0304c40407458040900240c2480ba14000301950311106840303003480301e03202641c00e404036000791180310108402d000080c1c1010958010000d860b01e100100b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697459658 1250 697458408 697458413
    0x1202030403170c0a0201110f120414030a08060910030314070f06020d0c030b0109050d030e04090c120c12150b121905060f040506040210031e09050c090708010909 71
    0x442240c03103040c00400a00d0030002000f241d40050080c441030343c1d000384a400100c1c4074944180c03050400b0745500020411000304100346080c0d60340d801c02e10400c2040410091100c45504642184182d440015420000d000d0f0926143c1801034100d402100700e40101031541d40d0250030b2081c403040d030070861400403030000144a07080c040c021403e60010001e540e0b800b56280c2040040910604072404280707009c004141035445907004500f610405081c00606001a4a0a440618400d650550b00a4503812500002206e00350700d40c00408160041d41c0c5001700d00e2508098a50154200f02494154040e032100494803c0d440d17040c4180030310400050750400303038020404d080e9030708a40b03001030300c908030341c4903c40c2c1c1100e940304000c0c501640039a0056210f40c40c8107420064151806032940d0700c08808a0058608040fa001c1407951908001400100096020f52995801c6081d0100d1300c0d9034280041c00c0c450300744284440e41c8407c079030b0480c1c240340450700600201c0041c002c0804142e91001640f04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 697460908 1250 697459658 697459667
    0xa080304060807110709060305010f0e120f0d15050a06020d0503060f0402120f0117011505010302030910091505150d110f061c1401032109030f03080a1b1202030403 72
    0x202c8003514140d030101502c031b200c010050085440308403029881c11481c0e0850301a10301c100f0011000040280c407160720066840c0c04540c102c0162055170407010011068846401d1040d225503055085502c0d5807140f40004000140c520f80d4480030941d0400d01d404400310340e0000499521003411500c1d421400b001e1008580240603030085505042030280c144001014800b5116040714019030b6031050004400030720b1401c0c1d030307840c0d2100f07110200043c000f84055030082c0c002e5940089644c0071a0311074842c0a070001c0581c0c06150007581e600c45c42c0c4c07800480060b00d0340a141d1384203c80b16495440002c510001c100341040700710007d0080680f170700c50300d03000c0d036a0044110800b5000401403a11001036045022500201c41558101d0902d00241266202d0590501c58100ca4100501c00c406480801e1981541c3d031080d00924204142c40c0702c0440014042030a4031402802641c4580f02450800e160000315042555054200140f607131270520080e6200c1410700f8021000d003009070b00d94071241750588 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 697462158 1250 697460908 697460927
    0xc0e04111c050303040c090c051c0506040b030a1101121b0c02060408030f0c070603270203031312051e0c011d04091b091a091b0a03020c010501050a080304060807 71
    0x10a01c1c0000011700062012248008065906031a003c001c144410030080d25180700e00d5000c50540c01c0c0ca640143c0300b0485507400154801c1000d007011500d049074500090400031007150071240340803015165685568005410a90150310510420a00c003502101c5c080c20900749a90380100b203040384404045440700002d440051040c0340890341c5580d006140104a40c0118101c403101e0701c02e0000014505201b80541c240c000e28072100c5a50310006e1202603c1103000c10b02c1c042c2c0e0184030400c0a982d550700c200710500000d1060b45203540b021402490305034203014410300780d2840210080d01e00c20601c0c0c808561030a40703003000d00b03102c1c3c13001c5490188500382504985880340c1c8180390581e88002d10442206440000000d40900c0c03117a1600da11291044552503406001c001f0800b034104055070505d48000307500000e8621a20f410505010303400300c00c55000810040c0003d40218108101c0314007406201c0c00b6080c100d410300800340c00d0820361aa02d00a51103070908000b01c0307a000c40c642a0107108000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 697463408 1250 697462158 697462163
    0x3061e03013b0a08030f2212170708010501110a02041104030c0b0f0d0c0c0b0c09120715031d15040308060303070510050a02090d0606030c0e04111c 65
    0x560342e07450882901c1c0b003030100840782c006580030002a440d41100403030041c1485074041203150031a12969040c4440701e00c02002141c0552201d20004070b1108404c4070b804485105025000c103c40105500400000c4011402035024580c6000d05c40302079080b10300c69064400c28a000c800c202d940340110f510380800c0c4a00a90070a2510304401c40d080350040050003524080e203081800256940541402c521030290300b860640f01c1442600c1d1808015040302d00a01c40b180380c8800c1d9078005454028900074151440a001540061820714500340284242203550030740c8040c1981c00d20302030342180030102040001d01056590389081706072024601100380740901d44400c55026080003c0c80d246c503c20306540540c0400c442c840000c0652400104854409034400041c21813080c03000e1420f8090070000d0031106c0c16540034440203d0720780b0780d94400d04126004000115070f032840d40c00e2110700031055410160f041c0c800442003001003880b19280401104054403890b50424107441154003540412600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 697464658 1250 697463408 697463441
    0x1101060f170d0c02060f1b010f0e19030f050408060702060105120d050f0f0f0a0f1b020607023a1e02011b023c060c0a031b21120203061e0301 62
    0x110311000c14154080c0141c141c5002c4208002100c009800352f8a1040140380000600c0c94011880004c2c0f10b00548015500c1c035050075401c00307071120423850070090215809801a400200100b001703103054600c04d130f03c0c1c01451020b00240d07134100350002d009101d0140c140415070800030340d840b20101018221130b00f030001095540d89403800c1c4036006200303a124035080000900010a910003180030103161044c101d600a007a517151140b02c1d4240a19040ba080011b81800b890840030803580242228007440c59843e000c442c4103402143c43c20914100240c2400354407451050807000050343c02209900e4007410b44100c101002c0c1c1d035440000c02d001c1c00c940c0780d100f135491640050b1100619081f060004495260072545210703a0340307002d2050038041c80852801651013401c0440201e4007030001094000380201c0340303103280407181e03d0301ca07441c0740010112001c0d000302c1c0354842e0340254008140d290400d07008000b07510b54145100013801840c0b007070042c85413803401c20b51b03220141d690951040700e03850b290800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 697465908 1250 697464658 697464697
    0xe041b180503121201091b0305040609020a080706090b0a08040f060e030a0309060e0109030e010e180f01030318080309062203111215161101060f170d0c02060f 70
    0x15030018940222090203110413401d0300202e010030a6001d083c0d00b40480c1050003295025200044001c3c00001e0010f84025545940010243c1c50f610500b40103050b0050050210918062008141c659283d11860003120140602c0f866103900468054006400031381c548090ba0440c14010014038000d4800b040c507210000710245c000b0b4241e041b540002c2e014000800c0643c0407600b6003420f880e49800000c00003801080c85021a60061030850400203003d00700c50f2041d400c04c855040d1941d0240c45220101c2c81a200400070590320818030700c0d51041007418600e8a900d48520580d0b24003034440704902c9110041008001e030404681641e904101e00c1c6040b05555580b8100001c0300c0025a00c2c041c09119514141c403000c5800150f50580c0b040d0107030a07951940d4400f66543d44041c10b44100ca820006c0711803018605180034010134000c0c22048a061404901c0e108801121440080901e03465401a8100405098000761410720068064882c95600c0581c03454100581c8101410350140c0f285460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 697467158 1250 697465908 697465933
    0x130e1e03130801061d0405060105120c09010b07020f0d080706020f161112030901080621030c0303070e1507060f231006030e030304060c12020c0d0e041b180503 70
    0x100800210b4191205d1801c00d80b01d01c2c4450300304030108803406000d42d03104030010016801c00340a1101c28040e030405580d07440a01c0c500258042400707034844651002c0105008c001e44c94004011454610219280c01d42c4e02941e560748201030103009e80107481d141d80410902000703170407941101d5280700014016884080342d4505880307805201316805000701401c0401c0c80c49c501c0004200c550245050f1510768441e511801004004840c410301ca80c2c40d0b000c02268203011640070409420f0034103032000078540740d2400030001015070b8250540c00c4d00c111401c0d01803030340d6000303213008545207160805000300f404001d08005030080c0200000d03c0400c0c074a0514540240d0140800d0341f40102c1e00001c0d06404940e42d0b070000ca05682c80741d41860116001080410001038103a8045c40c501e02030360412104210b00410f00c6000c0303801240b00c84840360080410144101c2d0304c842e143c0750707c84086a041083c1c000000400d000442c400c8203240600c011740460420941d00040514010103004084a22049055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 697468408 1250 697467158 697467161
    0x3603021c0512092a0301020c03120115020105011206090507031707170903121c0501030b01060e040c02060106180e0907081b0f1c050d0e130e1e03130801 67
    0x782003035860b41c1c2c12000c0b074000c090220f4071301c02e00c1401d0391030310752a141c0c09011100a081a100784c2c03a455075003042170b4000818240045c00b0141e80d01040098103615181460030031101e0104030200f16427504005005e40c2d00500c1d98280740076001600043c03441542d10f0640e1a1481d940c001800c2c2a01d450b19160b1038a58140080074264411140f0100c0b1040c80c00c0d50055900038948103036030580181a206c609508528041c2034003019404021102c6209803000c1d0003207440070b0300184e404110404c014050f9607044900d81900c48001d071030402070701c1c0035800025250141030042c1c10030088000f42e02000c0510700c500400c003078015112b40c4ca1140c1000c0d8001d80d0b9402280c07140f802c3c81d020b0000703080326054881c040103000c01009082205449a40410802242c2005220105002030003141d000822070410141c030b005505501c90803692503411040190509500e8071486003507007010300f40c030486200170030701c00c808944d020403140171007041940c410f06600445400c0c1c50b098051800028504105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 697469658 1250 697468408 697468417
    0x8061b03060a03031110050c130608060901050922080d05010b070c03140c031006030b06010801150513180504032703260d06031a010605270a06030504063603021c05 72
    0x10050075150b1681e2b09030070741780c43c3c0d801c48d1078580c0581d01c180104210300345290080d501444080d110811a250f4100c52207660400e0001a11103040108800760304060310301c00c7c079014200710218075040c046a5600d0f0300d400101c602008002e0b810562155002c80010081c5160050f0001c040c1e40c5012030b552400d40051082e031005440c040048000b003602c6500039640c0c10306a034414040181c000980b518113541c0c65015060545114980782000224000301c0c103c0d0341c400c1515030b6008107550070141401000c450350009901401400040c6c05901c001480030a00b0480764466203c0884510f9080f00c130b10781a66040404280c03a0b4001046400160603900c28400e03030b4400c10404444110000b142d0820f00b400b4042c001c04200b0400c403000002190080c03101e2030201c14003010761445034403000700e03103004015400200480e403600c091104016843c0144544801c8244818a804040403c402500c0c10000920b50707107035814003159001d140c4240441c802d0783c500550341000440000390018500d030700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 697470908 1250 697469658 697469677
    0x809010609020408060f06011803060e10021624140f01060f08010e04020d0503130807080d1e0c020d14010b01171b120108061b03060a03031110050c 65
    0xa486404901c0049502c00d49061340c0d0010014105aa40e01005009a030005000b81d41441101c140420703511a07035040c0c5402440c03003081c0c0894240d000d150140d1400f80311302c803c020700600510800b9690340d10301184030070445d004454840d50956a00413055200c8941440c030340d80505001260021307503d0059124061203038076110302c05a0f0703079910049451411030702c0720100185034403004010048c07105680c2d03904540010b11440094680381c1d58145107622040c0d0400080341c90050400000505004100050080c1c02c0506114200c07030f903004080c4280080d425480c900c074120708007081485411280300465001d070000081c9030140c149480082d01c001500e03001e0350301b00881c1300c03203c0d4810303200355480d0440c43c030700001341e41c0f216445103170400d151a1181c403100d41c0c00d001286407804100c0d00e850007850760070060005414182417032014506101e4014140f0481001409002c0c0c4881e030ba40021a80c052421030990340101c540c50741040005104451410b04007002d11851001d0300006104199 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 697472158 1250 697470908 697470911
    0x303030702010b090c12040605092b0e030a02130c02070f0b04090c110a0b150301090b16140a1407120210050a0b01050d0c230903070905061e0619080901 67
    0x1d4610b4540e4811b88140b51200348042000c50100b40000c030f0542196401c80e030035100f902d0340c4450034611407048042100400c058004804140d03501d140d004032460004100960140c0480c04050b008200d6400100d24001d512690322442c181280348280003510142501c4001020441d0b03640c4032982035038001d4000d00d403050740b400080d4460341d03028508144400c0c00d00300180c00b07029807a45039540c030f0700e8000f00440d80c012007200d03520000390307028850036800303074440c0c2021103150070302c07552004c90365801c0c03a400024401d00c0399010340203042c900f040d90b100345094039120b100c041c00300d005000c1d00d00403100014030203070350b06440b00c0b007154003c200242010b01400040295a43c1e261500d01070711010001a404240c080068800300d41d026000001c44441c941020300740040b201c403a50211618104403035520b0540828208040c0c50140b1581b0001d00030b03503c00b40403074103100000450724580b00d070225032010941c07440440c031a1944002d0700c100b01c100510b81080340c07580701405004000110799210065 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 697473408 1250 697472158 697472161
    0x50a0813140108130204110f0c100501080a030c0627060b032b030b060909090304090e06060913030212040f1805071b0809060d0f0507030912030c09050303030702010b09 74
    0x551003203d01500c81c0e01c84801141840020b80c0034071000f00204200351403020b00800c005044184040300400c4081c0e020801000084031042c0c141007180d0041c2c0080ba00c0b6080340b140c00012075445800d0005068208a0024001315044608401300c0d04a40701d03190340054203128102441400d034480d030a00e54043d81a00e1480c140030005040302c020524920b00004801942801006e1281d4415248041301502061401280c1e000142e2034240840d0040f80b680c0c0005420310036404140103082d4840040c6d0000c1c19a4200302000844030b6800420003524840103444e40002d1500c00c000b0740c19807009844405650b203481d095401c403089514000e540c2c0404d000003110800c030b1213511440e4400d058a0b03807040041c1c10611142d0481080d8020159800b83c020301265000380d41c4c00004081c40644400d001500140c498040010380381c000703110f04285403901507020081404e0040d050504045482d0028003a03000e40310036901d4030781f00d421540e090f2001100700908540c0540c410000d1210031a00d01c001c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 697474658 1250 697473408 697473449
    0x6140f010503030414030102040803041707171009030c0b0906010f0b1305010804050703060f090201080610090e132301060e070e01030f020405030d080123030a020d050a0813 76
    0x40810030720595406900c204410403020079401e101210350840100098a41503880b80ca191031900560015441003c8840c014a021081003001a00034031090010b02d042403139a1020742e488410034110411419240c8000c076080602c1100302c1d000513a0322a940c0f00c0c1c54104031810a0b5559424011140d203511206404100c16401100382c84e071005811418100d003e00307200044640d81809042200e091091800100008040c0c0c010444199140c0e000000c2039081c50000605c1e149011709414001c0c858507441c112181c1d071000b00303e016904400c4440d00b441c0c0b20403e041702a59032400f005440c0310700036000c841080c001c01800440c403c4030b2000030301c01c10740c603103840b0305030140182e03500f20200d01c00003540143d81d40070350020584d4084154006040c5503551300400e0030a0700000b5041c0000d92a28010b02c00241c40020081c054040500d0b40212001490003081e1f43e083c1d4014048d1180e04d07100000010420100091040701e80d11040041e100c00b1150961215100340c0d0191071414140c002e440004d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 697475908 1250 697474658 697474681
    0x60527091603060c1b03020606030c0a05031009140a05030304060f022506060f0e0a110a050403020d05071a0316030c0e060304170406050403020114090d08160605040614 74
    0x1c9a2045030325426a031895991180010046002000240520030880a29103001403a0500d0013901030340281c842880c1c01c00815040a402445ca40e2041220a0b800c2c030064030300040c1c600075414943d400055101c00d50403c800c04130080a40c0c901248183c440d11020858080080c40c0607034030070030f824000d02c6051707150042640180f022460761900701641400b283c0c0d6142002564050140100190003500ea90844003d900e0f541c1100c01d000c1d519800b409540744c1c50784540640889003240c01c508003140940020414495440040d210700c89545884081c40307414880a0020480c1c0307205c00d440002c1c41c840d10202c40c0c10807076489038540e081c4041920000c0c005d00504080408590307421495100000820a060300301400c1500d800600c26514000d8100c1e0400420203000252a041d03122465407000402c48c075610a0a124184010302c8060078a032103281007a840190322190841d200d0705030028413100001c04070300152070203044c00c0170305c814041030354000104056199200c54950340d486c0310248 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 697477158 1250 697475908 697475923
    0x60402031521060f0610090f12140304151107081e01090209070203030a11040b040b0f0c03221401021002030a18060c02191208040606052709 62
    0x1960032000880e140c0d031415503550b6000c14180e0100c003418034912400c0034501202207626000b8441040180449803515685a0b140c41c000c5180800d40d05040141b140b54000251040320464804840d00c0420850804210f04884a100040302d80350780c1e454208000715405480c0186c0811240f119240c040d00c00850395074142d8540500910403107016400010308507400c1c42114800355aa18070304001682d80041d03090240c55541d006540324240701181c1000c991422584a0300e00a08100401c1002d0741c80301502c00311046400000e8480c0741918018201e0701c14259407648501001440c0070601409143d020150043d800c2d1170003641c0d44500214030000c14008406001d07038400f044d0844050341d00c0c1c004591000241e64003140754921203500170040000403800b281c011f91280070400c140c542c10401ca00d1108c10548544150900316144c04003201c1038070703400204004681c00060309000719508184020b040203000b407164920240c01188110b144619452404404840803c50b00003000403d039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 697478408 1250 697477158 697477171
    0x30203040506091f0309050d02071409040c08070f09380a080f0102190c1e0302071703070b0c0a05040902031801110a030b090408030a0f0902031f0506040203 69
    0x1180340c1820842080741070382290786030f00d50214000b40241c0040e0014084010305111544010801c010503142140c1485201101202154040304081152101202e5544142b040a88001d0001d440f80c1c2070025600030160031040c030600c034102c000910369019171000c034100c4003a05005c20040c6951240c0200c10b0703500c030321100c0107068825032800300250b0001c12a2071001c8001e1141c01199030b00c107411420280c1c0700e110103840ea5804a10405d01d41d03841c0d940d040e07002c2e00b40d2421480d0350700156100c002c1e010040d00c0d042c00000d440704551040500030003141004d0158405071014844403031a006540e6404045d00715126180f0384c011403050a092410360f03629800a4541a0501d0304101c050300c0207400050001c02800c94111519490100a01c500d4503094031018401d551001c8669024066a00080c1154000e01d0000300301300102e8410400d8a03007104d001d89001c10424020408440680410500694580905c090340d2a40c000000e5059100a20a50091045070b40b07010422049020441d002c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 697479658 1250 697478408 697478413
    0xd06180c17070b03150f01110d0504090f020304081b012406110c01230d1a0a320f10200109050d0e030712110f30031e030708010803070302 61
    0x1409030701d240072801c0e00505803040c502380301c6a080f1400305a00e09103d400c0c00c9004620001400e20032b41e480d83c01060700100001c0da0a618608159071291070358070481c9484c0f203449144070380c65920b01c0000c0d00034048a45101920f100114669038204140c1d00541c8581e04c00b15070175400c0703001d000401181a09a10700140c55052080c1d4034050b4a01030040040c00101c110b01081001c000c43c13180e644104024516034035041304149030140c052000c3d221241e004106030441c07050700c0c0704260925541194200440c0400c0070100401034010038002200702401642c886007490030141c1c5d290b8130882d505103c0040034108540c43c0704d0361035218200c440e40d2401400c01d8108075100300546014880d285d00340000507088414107170b600c140c00d46024048110444801c0355040101106141103050b030054800c0448440a08101c826540c00480e02100c85410500944074012a2020810f1041c2c51890402d80c0000d82d04090726200200154012500803000c900d07408008611250008180d40a40d50316400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 697480908 1250 697479658 697479691
    0x3050304180b150f04030501140411030f03070201030b0627100903053c010912050a120e0f030d0522020604270606050d11090d06180c17070b03 63
    0x420f61a40e011204c401204041000b000001501c01d1040c0c024814140035010440d013002d140c04010341344805006446540b1105031000301501c040100d424403036090070001094424400880c800b40544034111141c1000450070518464500d40100134640d800c4905071010210004190f034220035034000608154044082d10180c00d060750341c0145041521038404507207152624201d40000c8038a000d40040365110041c0c6002c1003214514a03a1182c210308125040540600c002032890741800c041981598580080ea005048140405a4803a86d140280e90b0350b151582403444c09040d060b203449030a4212003a1005040038000c04860016030b00808040c40c00d0714180901200301414103410741d200c20100c20340f0310f10303550780d2291600900e259106c03e6110554100f01d807044684a00080c2c1d40c2d40300c100310402c15a0744500492100300d52140d8001404241e207910030054031200c504c01030410286050208600341020074070241e101c1c1d06002c8030030954840c1600061030100b621100c012201805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 697482014 1106 697480908 697480939
    0x40b04051603050c0415050d060f060c020a2c04110a0306090b130203030d0908040509090c0a060e030c100c120f0e01030e06010b160c03050304180b 65
    0x3281382c20645482c510b20000850340c0200d004000000441d2038040c1c0c907d0b40410041c10704d442280b482c5544411018290841003d800c0e803140050000024144c1000540104441003400c4506070021004585400b0540040d00484a840c108a40d02402d5103070681640d000f94008da801284040d003070f0515019250001c8c009800c40d01e1803520150244c1c40c00801c0313503070032200351000090b040203d040284480c0209c1c1c0000b40d2142d5104248106844001003101e59054100c4514071100e585480950303d00708103800454054104054903401442d02c0842011a0340c01f90400302003115866485c1c0100903150240318000c0ba000c62600e10703020764060040d030f110010a0808020064450b001c4c0c964590381480b0307206641d0702c0080c1c10b481c0e059040c010300c0821a4070400e0400d03015141d183c0a5200e030414010b81101ca01c1e01e84140706400450b01904148040207000b40d58010080d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 697302158 697482014 := by
  have h0 := BRFrame.cov_init 697302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 697302158 ≤ n) (h2 : n < 697482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
