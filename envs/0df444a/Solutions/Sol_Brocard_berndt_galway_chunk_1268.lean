-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:05:06.545755+00:00
-- url     : https://prove2.me/submissions/9f154f49-aca8-4cfc-ac2b-34f9c2543026

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 227877697 ≤ n < 228057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 227878947 1250 227877697 227877719
    0x14150a05030601050909030d0c0e0109081f0b01031d070617010b0a14041205070801050a020901050d090f02031504020a120807060e0712050a140a0f0f02030102070b0c070606 76
    0x16164081c00502d4241e0a24084c00010303034000d07010205510050016460304005401100640422969201d6002c0c1e213290001d00040702c2e80d00000c806402010741d0b21111040401d00c520004140007011030b524210f031005074003c00e01d4410140c100ea142d000041824900080c07404125495983c0305840450220389a924001081c043d4600b141800c01410a526102d00300d8042d00c80284d0015071702c0d00c3d6907260000b4910040350030441d410b403c840c13800c0010b6200ae1040d203600500c070034010740c54824a140000e2091150290b001000b07940d03010348000344001e8040c1c4841842c3e004d400c41d1606404440a01051202103c040b4440c800d400d4022416503d95241d444089501c200c040f03060810b156113070700241140e42e100804174442e41c400090350220303003954410454090790140051003c1070810300702003001d000c0d1007421907001c0303003680d0001750050040000d00c2d03800c16016030154510348006400ba116601002e440317080c40c01c052200040c0d5107401014074600c030b00c0003000301590f03c4003c10a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 227880197 1250 227878947 227878949
    0x103090308011802041211120105092d01021c1a01080103060504110915180403080115050c03031008060601031e0c0c0b25020c0904060f0f14150a 64
    0x2002030700c00001045000d4001228100559440c800581010f0312070000031030f02555240161540a00382100c02e42d90b0038013030b40024003c45050000e001614040c072481e541c6000303500c46001c8000103085d08284201352032901000741e03450040203565901c1c1070104040d40304003d00c2c0c2444042d02e840c4045900ae6124941c0f1502620117031035039401070b8a1525010010b0000800940700807160322652201c030341c0c0e00c2005912608105500e9407010001d407081c800d40d024501c0d9030a01281d104001c1c000400d0b0001c5140c2e0448400c02c44203a00e030305180e80100e445000d400d605450a00c0080305124983c0c50000e0160140e408600440d0326555030f8400440a5400980f8805003040400070301c0801888140c101540700309941c1004d901042c09942d444c021801c2c116041d000002e040c0a101c1e0100189924030341034000c00e44004c102010010002510b007003805400200300c5940d403041400100d0f91600140c20b806020b090070440701c10420f002e21400d00003141c181075029140440d1074128642409008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 227881447 1250 227880197 227880203
    0xe07080f07021203130203010609020d060807050604050f03070305010603030e0907020319050a2f06060108160305150d03030515240309150405011a010c050a061d03130e0105010309 79
    0x9104281440442515032010b0507014801700100390900258800340504401005460001a559014010040c040382c0c282d030001030140d0441001044651b440100b60382c150b40084628948403c211000a0316080055200402c0d0754241200001410f07084601221029003c0d105c914680d03031080c00480c1c036440b82401d81c045406001d8100d5020b41c1c4544040c1440e509075041c03081c0c040c0c2251030344180d8004402c80e1082100b44000001101c1c4500380030303407604140b082c01d10f28403c0c1004620f84191490040c001d40425940d14001503028480808440e150030b00a010800381080b02c1c01d0080c040d02003102e044a1580c8600c2a0b12814180000a219408019160680c07040c4602940c0b0310700d5031000d03240007080e205d082c2c0c180003c14010400c40740124454000001c1c0150924601200818280720346410f0060300058070002c60000710380000095400400003444801e42100c98250f103080c40e182d0080c610004c512180d0054095540009840350403640c00f46907079850380118140e0725008002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 227882697 1250 227881447 227881453
    0x130e0f10150f051c060f0503030903030403060b0d0206031303020c1207050d061506051801021f2c0a0203010e0a02060a3f0b010e060f0a0e04060e07080f0702 69
    0x11000792040d103000c800b1825030b20300189400d00d550700e100c082d000c1c035400b001c0b80f0035a500c1d8100102e50000d5205c00003008241c025600700a06a0002034503070007280700c0500707800d0721009140c01d07680d0341c164848215a4014a4246c6909201a442981d0218101e04030058419040360249a1528040300c2c0413182003440148a16030a11b000e04c00702d07018a0408a1b910751303c4552800005803d41e4203000074100e503030345241d1920301c081c4840b802c1034a51040241950084001c24541d04079070803514014602d4200046070010010701601e40480145d8403c1d0100d416400d041c640c146008200210304500840c02802100310020285440d0104400700070340c00b0404000d4400120702400c00e00b82d070070707030740356003103200003205480244c034082c0a81c040300d068400e0561100c0e03134034840e44200c0c01002d82c00c0c6414005c284000010981911504100c2d4505400c08100c141040e4450105840d41000240060190390390325140103c15180903507810f07012803c044009806007040300440f5100d9507035070707000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 227883947 1250 227882697 227882729
    0x5010f0b01080f01050a0605090301090c1d01090204060206040f020f040f051902090d02010c23031e163302040f0b0f031b07020415050a05061e0f130e0f10 68
    0x1e4401d9130124270b286805540b0f9040c0c00c1c022800c5c0340308aa00408a800260900290f501680980640141c1141d00304520500c400d0003403a41c001240e41e80240d10003800303050b0b20014000144000145070250f5802401c0840c2c4c260102e04075003000740035058240340c0d80c1080001403250b00c00c4c0e0040c020003d802032804510a0301540c03155000c080054040d00080e0820220302070282483d0310301c401c60030503039400000e101201b00b030744800c80e0800c20b41d003400403800d14081c40c03411a0080c0701000c0c00b40c101d005400c00c0c61012810b01000e091001103541000240340f0744401480f002c2d400521600c10304118000380012014251001c0790102108046070501d555200101030600641d00e15504007200f0f0148248001612248900c03521222099000c5520310300c0c013000c100c0503440320340088e80031b907401b031207540001c5688520820302c4d507407442940e6880d03440000c83d5034013074001d5000074141140c015200040361170305050703101d028901c1c800070060641d0f5010b402e07505546181c810044030080d0410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 227885197 1250 227883947 227883959
    0x501120218030318010f08130320031b060108060103020a0b0c210304050f0d050d0e190c080115180509120417100e070e09010905010f0b01080f01050a 66
    0x1009248542003225030700041d0a201d40460b2a50300441c80803032a0040b90115900203603000708071130035401e4685c64040120701d421000c084c400301d40920004c050124841110034548100084210802c0403075044035100c46640c051300fa14104540d8620380140a001c0010841c07507004210f03d410f0300d40241c0101070b00740c0f8000a424071648100460000d0380038441c98040544203602245625044a1801c0342d201c1c2400c0c20003500f4405400c07401d03d401d80c41034001000e030300d410006960030925020b40000723000007165541402c0103401640c07400b40365498200e48003049000c07070b000350541c1c452030020009224544120b1108403280c0c0240b0b4400c083c50303ca83e245000903a044564080700c103009982d0840740c0d1a40380c8007aa04150051700e00c030b810f590b046c5e42c14010704006204107030b4440d44003408090305215000d500c0d00014000c0150300101200090a07402d02504100649a8400c0081000d4401600828000c01e070542c0e0075030002d4520070120720301034000e58041d4103803140145503104482c41c03d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 227886447 1250 227885197 227885201
    0x130b1e070503040f030c090f0c0e0d0f080f0307140306060904090609021201020a170f040201081806010b09012010052d01060305070c05060105090711010c0309020a050109050112 78
    0x21901c40c4030800c4046400300a4121000040d44900700001c00300d03040958203000d42d109410400e0fa40c62505588034444e0742d00c4003c8080426003503641c0c0e284210141030400048900c030402412500000440c00e85608260005502c85e0030182d8607901b503444108951941c1b80b00c140c0d04c1c1a8404030502c0480801d15090340049a8140b28900020b1010226400f00e24444510b0030150b803565804103000100d103800c24070301a0300901c5207015418611b0031380052440e03003c02610190400108000155a1800f500c00304440300a58404991071903a44903014041680201000784c0000d14140c0e090290000b1000d5900146000501500407144a4500040149002440302201c07003c10000102203201504400f900700f180300c03e050b42198142403014080d02c0c005400c800421030710990103400b0a0000c248541910f008413110112612400e030b0844401e6043d4812038465482d02d104000f249403d5842843c40d0303842500c0ca0451560364000540d003440083c0f040c107000c41c0c410542d00345032082c55 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 227887697 1250 227886447 227886457
    0x161b0f12050c010e0c01080a38060d0608071505030f3612030903070f1b26280c080106120317010f060809070302030d05130b1e 56
    0xc1d1034564142090340c0a964291034011441201ca5000014175a001d540d000c00c5803607021200c01014004503100e29400034604e01c80b0501e1740e001064480c005070130348201c0003400e415154001d02c0c1c980c03030303021031800c5000804003071060142c0d900c111000042c911160459031a120903094981605503916110840402c50004010203141d8080e85414900b6403461034140303191285a00a4103a640c03183d1f00110710300451a10071001c0e00a06004100c2c500c4000003c03528183d601059400e403180d03962601c08100100a040c4000c03103842e6a01c0403402a502c4144c0c0648404600f2030300882003886034100781c40701100ca0100d2032007401072031803140355402c02044241303541c81130a105001a607a80451400c40d80d90350000c82d030030304039030000406255009924005e448d0300740781200400d501d40548410b003804548100740921009a0009008070780038440d0a006603005002d80e12400100d10300180a98410800000c054070aa1000308411143e00c054402c2220080e20486d10701601640f019115000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 227888947 1250 227887697 227887733
    0x2030703021302040f0b040f0b07050304331728051005030601090c0c03141605030a14040323030705010c03050105010f05030708010b0f040509161b0f 66
    0x46440000060b1544006842e070500740b1a030058440b8102550000d4a1120398031203200a00d0610003800f80e240d282c0140802c8800c81510140d03a00d42901e13041d811030080d40d10501c031030194541040c801000340c00c0311400801e04044124865144008107486001240070058080105880050340d44d140385910110340210104014804c10b404141c001c050f540c00700c41d0710034103461814041245007010008580506185002801585c40901006200d04920000501004646055031a503400c2980488642c1c4e0b01d640ca4460902d001e50030401e40e01d034040c010043c00100300030401d200fa00111010f03203060341d900840f00740c01800c3d102c4451443c0c1491201081c079601041083d540022401d11460891000035100840c0c0e81d8500b0b8000b418041d0380c8606842880000c00400003010b45c015549415520350104650b1100070000e80e0f48028000e682000c1c1e00301e031514060048110080000d415001d000da80c171031042c80c90203203180321821401d039002007848611400f05400588031003505219100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 227890197 1250 227888947 227888953
    0xb0a0509010e0a0c05011404080307060f020f07061505120c0d06020f040603061e0e060108040501020f070804140d05060117032b05010618030809040207020a030c0905150d0602070203 80
    0x401200c1c03d0500b10510401c45103c841a20204100d580017071265000c2e0f800400701c2c5e4101490700d600c0945074032503403000a0190360b07100d0749451804139a5040d6070070001c1c0034410302d480f514145080001442454043e212404190000180f54078144c0300703c0d0383c81007075003014080e6098004184011150046807c41e0312903024440c50035081e41440160004102d1030360301148861802c0c80501c01e90001d0315040d4681c2428010130b011081989031001c0d040002071030f0803001640c0b1401d01c14020300030040c080809500000b00c0c2070074050200060016501c88804014004840c2003c0060343e56a800000303107103400540c010400205007020b02c68188c1c0c0300000392071600d211580ca501e14141a4000d0340c013585041200c116040c00144a01c0d4050b083c0e40c05c1400911070b54400d00c5a10105522000f042c160000030640c1e1907454580540e120f07543d0240501c100b26813246000d0304418424011100d2892070040042c0e400300556000701100f46020b00302c00c440a00c070380c60340301c00313540803c8048c3d82600c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 227891447 1250 227890197 227890211
    0x406051e0f1206040c05420a0504081c020d080703090501090f051c08060d14010f02030915010f0303050d0b09090309010e090108060105061e04030f03090b03040b0a050901 75
    0xd01c810005400381e8001e1400f800c010b19003490000030312911034209034061212883c21600c80c20349107a903100010000244e030348050048558842d030000000010220021000c150055055045405072050300c03541f0050f5045181000303218102c8018507104580140e01210b18145241d00a40d040c82d04540c140c42c020421200a4039020b003034494400084607003620511010301403280901041440908120814426411804c401003a0001c050b143d1441508901c0c0207404000160401d091255440c00090107100800480031009420031180504180207290001e0b01500d5140000d074181e48000824510031760940c1c4040701e030707034010b1403601d00c0043e85d5141600d49562002e412134032503500c0800969403910114001000c1800301c0c00581e01651318070005004000010800c2811750710103640864031780d01000c0c010004120310340360201d1007000001d004014041d44401407945e480c002c0e01c812056540c0d66007400130074842150040c1070704c20395001050083c00c0b0768101c07036008221040013140e80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 227892697 1250 227891447 227891449
    0x20c0a0b1e0703090f0501080f07030b04090b0f04110d05030a0c03030e06270d080c09040b0d0b0603070b0301180e2406041416110a0c0617060406051e0f 67
    0x340c2d1201c401a4040b41c21100100015001d4446003800783c0317000e2078030000d58140300c040e50410300b801400031800d2584680c001403854480d035011060090304102d0060032820448180c420101d410f507819a8411512803281b1414182f03050b42d035441c2d0794070034002c61404002640444411303605250840c04c0585030b885544032400104510f9000d030201c000b801c0424008013810380d152990400c0c513a0300541026002d001003a03007001070300360f111141e00711560f91120040c0003d40180250705c140f03030b44003014204030410321158a800c0d42c480e0b1030590458444545840045100340000d202d04402ca0150444141207070803290048a0303c000c081c1d040b104246058441c803256007503010b03001e0300d071030300e00b81c0400c0742c00d14250103072244440c1040c2c41c1040754140395031712901e0081c0c001070460034442c5201c941200010100081c4886c0350700000325007038a80c2c0f07404009000d02e00a4030300740154620701d00403441d1490a84100300496030010140b404172041400a0442a1804140c1c1c80e4071480e081c10140e41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 227893947 1250 227892697 227892757
    0x10e0303040609032615040b0a06030203131b140a1203230316091502070515130902070b1b040501030c020102041206140f13021309060906020a0f020c0a0b 68
    0x203031170b1070700c0d01c8900c45151180e0107020035890350301030341d100c1c07410141026880e03101e403c3c205c000d4408500d0003594940e60700d5a04a482d030b81d98400140301001000d0f40103045003014551009450308140c400f41110403000420808880b00d0241001c030345201c410100003c0e0042904923001412116400020004031480e0581500101ca2015020940a4000403416481611403020f009862403000c0d0211101c038000b940c41000d070003018041c0c0e241480407500106114161542c00301541d00c41903c540e2115640f201a412446040755074504400204407951001d0700240c43d640d40291078141802c3ca003000440180c11181000002e44d54200000b1480710b032003100c0c1c109140d00421010404841503d4448072000c40100341c030705014050f009000f440451212082050340d011101000741e201880b60080003005000740051425190902caa0200500d94010700300030200ca0b1a0154090107020301a030b160603458510710b910880300101800544c490001074655241e4200e003c183e03520110a0801d6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 227895197 1250 227893947 227893997
    0x4140d02010506030f010504200a171b030a05060a0b011b050606032b030902131401080c040605061b1203040606090513050a33090c0602010e030304060903 68
    0x182d448000b04242401d01300103015925503680002c1100e40f91039290b4040e03441c00f100c3c983c084440c03200b0100000e03940d03000c0400b01a00c005e2103540b901843c00000c080d660342807070561003014044546058a5490041400e004168004018054640d100406000100072a500c501c0c18803a4902800241095001d01c506a8600c9000240300d079082ca041014500034a1160140095100d0b80c0c003400c0c0c850341c0c40d8207900180058180816034444d05d00c00071b0040041c00100300501ca1400c5560041900c10b0301c403d60490722100191450085003105001c01c0e0f41c45070240d0390b042203007041100b03403c24800041803002c0c5040020ba50900394440588081d55005590035101c0c0c1c0d846100a1000e69800d201d003982120507082e01c0c9010035901c0d076130a40c4a02d1504000761607140702d004ca007041d00c02e4550204841140b104405030050000c070000c4070043c084c401050329441c1e40c040c40030030101e0052242c3e44031003020900550659545540f603101909403140101d01f08040514086500041082601b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 227896447 1250 227895197 227895223
    0x406090903020a02040b0405010518040201031116030e10020c0607020a03120810061803080304110402190206010803120c0703050d0f06032a15090f060f08010b0f0a03050414 76
    0x70b00300f4240c01084251303401604524030036494880104442c1d40c42c1c00016102c44001142c50070556918001070b00100307079a140b00100c00f0000120042d100e00701001422819209894030b0884401c880c2c1400005402d00b2074101c050b81c40410402050715241001c0d03e4440d00c000d05420016440780c0ea4581098600001076001c036003214248501c0da90324110081c0131b42080d1a01c52420742118403c0c4100341060720015008081c000041824460444440b01c040b8802410940d0350718039841100c030785000c2860301c00c001805660000301d170b910400300481e10305a403000031542c62034460801305103041d440560110b09116041029100501550055402e44041490001291451801c100da003c0140302d220004107001c003404180415600c6c40e215050b1032403055030071410044242c082c0c810302925044400c00702d00c40000095150381c07140090200081d83d0340c6012070747c4d07601d002d031002034000e4121404982005100d034001c414030940c003581d406402000303100c1003608881440790400002508007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 227897697 1250 227896447 227896453
    0x126010612150506031005070e09010602030a020d02010e0c150d110403020a050301050610080907030b04060c0e06030403050702010e06070b1e090c0a0e15060c07090605010527040609090302 83
    0x2040c000700b404a1210040484014019071903c50002600d40034a00729802e603d9a580d00440c21f014840c0c00041e40300d50020b400c0303100070350311000040e43d01d412011203400140f19062500301d1180c41805085600250782c0000d1051607071034800c1000e400c000380b480d130a400c0414080000511003034000c2c400b1100340c03022070310b5071142140140101c034509900454041da040c0380c03d104a42d240d8802d00742d800302d4503140200d80d07602e41440050a105240e840a8440f19041c0103010601600341d0080403041416103480c40c8030032050090068034002264081c010680c10301c64400954001e81e814610bc2900500740d07403400044d41d40c2c0201425042d1f030a001c807030601c1d0704400c0251400312000c94000c0c12510042110611010001d41c0c0342c4814041d2112481580f00030440d2590044019000f8000c0101b2094a48900188c2c03184d0325152440340034025810240300040c0e03940a40d084a6215940c655450203c9400c594090000380f10f850982d50010790f80c034000520b83d4241c2c494000214800c1c1c0c05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 227898947 1250 227897697 227897729
    0x1002030907060c050d030e0f1f0c0e0d08180d05030a0206070302040506041701060306230f060904030e281418070f020309090726040b01260106 63
    0x9014603000700d54102100340402c030400c1d100811000124621070303015915000c50a031a0b0700a60310304018401126100d1440b850003020000d41003c0004010880c0c05041008a880104400c8400400341880103401800c00200303036000c50310320300041108400c0b10341c0e510444ca0580c0080390320405801029130362a080803c0450b18a039040c0034132900a071040c5029070903d402d000002c0e6041c42103206581140d075980f031801d454840f00b034100b1801550880420400f001c102461007500881004002400005410004004680c00155107000c0c800190104010756900e6a05544070054010540e074010125554002040d001d8a0701140002d288840d4000480c0b50002da444400c01511000e40b041e00f02c0880e01d0f049001030070381070340d005a851410b412218101003050b401d6110b00c200403900040d011040100030394002003403250b8580c202c00c64580d211a01da00d2400182c0b02030720000c0c034505200b40104040700600285c2d014000c43e00c00e100c244142554255421607089512420020a81d0344c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227900197 1250 227898947 227898961
    0xc21040b0a051b090d061a10031b0c0302160f0f0905160305062b030e030c300703120905100f050307050705030d0905060c04030c05060a0c05100203 65
    0x25034205400d6042446681400050000c51040143c0300381e48050010840250550710a9910034081b0307000807080280d03100c0980d5242d030782d412074114079005503030881d904ea0840340300380300305040951aa0b0340c4121458a803c8200d0b9040b01540c41681140b0500e0320400340d03420191401c000030800e50400c00c4195140080d0700d4000300c0305500c080441c0d45420b0030441500714000210071007803910300e800121a5100000160700c8500b04a040600400d007800402d90000507409a4114034040e85401d408050b1120030180d6541c10b100d2810703080301c6c4400201e8900716002040c1e548050a01e4200c18528640644152030f0280c0d507801554404204252401c00b0340e009481c0d41c02802c3c090341e141c03600515001001d0501c612011010040003000000151031074812000e07520035641c088160395998080e02c0500d0054050b03114203030f034240589800326a106085004035011030b5482100700c080203141508110301c9400c03070071290301444101145000042c100340143c98400700304039001030301da0410740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227901447 1250 227900197 227900213
    0x30b0a0509070f0f020a030c0b0a0e06010303120b0627041b03052a03071103040504020c030304050d09050d0816060204030b0114030312011203020a060c020106091a0d03080c2104 78
    0x103629070217540055450781c01081e8420301c11001150801002800d5469400000005042220165819015060000c002c26602c2216021800d40002042c08000700150400c2410301c03c4410365139640c1c0b0701400c4e008212503801084e00c1c80d40401080010350720a02103014044455010103880002c0e81c6504108504000800c005000a072001c011010304030410385868207888080c090f40188400c0b03458011020b03100700111406000058001d54461304521106036490308107860480340c0b401061502d00c14540300d400c80300119100103082c00c461101076110190315038000301c070040c10002c0b9050380002244d03543c00204000c610448441e081d0b0361504000584501100d2310300c42c4a40c02c02c0100039808450020b03000d064584143c1d543d0b03c1c0a4807490140e28020007a80010324040c10300d8080d0301000e4041d0300907000c5403070a072824801c100010301c00000d180c41c805c849a0703015510301c2807100480d1094402e560303c090354060003481c0c00c9040c220b95021681c1c00c800d500c0f501c1d000601700400c1120395 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227902697 1250 227901447 227901467
    0xb0f0307090207140604080a1107031208010e0604050403021e070911040806090307020d022b03030209040e0a12080c07050312041202010e060105010f170c0702100903050c01030b0a0509070f 83
    0x2000d805c0c1341c10180e40d440752a103c3d440144040003031040800c010329a00b4407880c1c004541c88008040c18a0107010040c11011007442034500c2203d4030000200141068060726128a60541c081d0000101c0c4d003501100440d044440850b9070310507038001155001180c130550314036101203041582c8803071500fa146450400300a1444200e500148450f000586031901c1c4507030110f504031000d14000480f20a20741c04d881c02d401007841c1c0c0c1030340d1140031024560503074000d0640c600b040e1303401d03c5000c44c6ca0f03500315a41c1c4880b41005240ca078040b40ba500b5118480d81403180c0018200000ca45050302940740d052443d002100c4030120f0f450528280001c21148814440941d800c90000384012444070b0800d5480309014841e05040c00160400084060b100303c9115802c00c44000209103541088825180950030540d0b0480c021200131122441c0f02d4003a2000c00b048a80c0200100503545600004402518110f03504a404c69002c8501260320380e10240500c0c0309040d41e560384100c132180050024000011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227903947 1250 227902697 227902733
    0x81213060c0b04020409390819080c0f0f0d030614060a0e0402090d0f150905060a230a050f0a0b06040611070806040804060f09050f040b0f0307090207 66
    0x44007900100140c5145602580150122000030b804c60300d07414518008a40740650481c44206d000e9a0a88040341c1100c100c1c60304d281b245840650b9459020f5590340c0d01001d56099500c00005040c0303400501c944000700142042402540c1080b40d400c9078091a28814484200c0c10b0740100c182c50800d6a81441004024089042d005000e1010140800c0542c4600b418043c00c01000034275031f03055500da80d0110382002c01c010303001c030001200d00d04090100000d285011126601c41400d000f21926407070148008441c1c10030041d100e5610741d25201ca00401c0d5186885004c3d54803e031403c0038450032000100d204034000d0501203410315055000d8154001d00800807800a441c015140c48140c0700d041c183c60a494903420030303001a0314183c000501e4416581e0141c1001c0c401d2800304010060044068030494103180c907281c84617500080156501092405450741003403e840105c0c0e05403500303401400034880081d00da003a0002460f00840e003800080e81081e0161500001c1010811055001485003522 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227905197 1250 227903947 227903957
    0x3040b070801030809270108010e1504020108070c0309050901030312150806010902070c0302030303010602010903140915160501150602100203040b0403031d010204030b040c09050415020d0608121306 87
    0xc11a41c4401007030280300d5203240070f9040c10342d603054011a07810146c0402000071085459a681d00ca840a01a00ca0000c5151260040d26400116411944c00039070007180e05841d40c0042c1e54940c2001c03140070460b01420707410030004400018594503074188040c06140250f54840a8880c1045d20744251303025074011101c0c480c0c0c2c421040198050100e2443d040d5110940003603516071981c00e1441100c1070503000030f90b060000100000e1a40c1d015404070720103500c41e80300c080e1203000094034042e440c00344a9540350040e0100003580e0103210300c03000400c814400b00c4203010415034103032222401c40e128015580a4056001014001c194040201e08140620441c05520b5417816660303450007000003400040038944c4a4018814100c2e08901d154803503488a002152225500c0c100020101c10035101501c0d9181d060101003420032150041c14403584d0001840c0e042c0c00d10025100300291300c04e201822b11546c3d14070020503030010a01644020ba0300c8884142c3d150740c050281c489140c540e551000341400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227906447 1250 227905197 227905199
    0x801050f0a06110a020a120204050615090d02011b05061f03030905060322060b0103050a091e0c0906060507050106090e1f02070804090504050d020111091c080f03040b070801 76
    0x1948600721042079038001d1030041e00c14221800c003d4038104100c14025440030b807080d0f0100e0503403503000300400040e0080301c1c01c0c001d40d100d840c144043c07003250b90004803202c9020000c03c00f003424600182c4151a1061400c0002c200c440d10094003c0181074008681542003a014001c072401481b0b00d40542c4603590504820141ca1a034001d842c2ea201441007601420f4080300045500c400b11440c50707124084044001d04084291810200421800c24624046464240071403074454081c03040310b0f01d06501800344805d4030702694400c3d15000f0500411240c8007081003021681510f01d002d01c1000300210344807952034800a20301103094800d641c1048943c2d078a80a00c9520078000050703c42403030440602c1c80f070a0440119882400391040850151170290300140003d80c1c1e251640c005803107280180f040c2c039040f00c2c41c1e050407426144c07400404100c50501b4407480c2058901801003154449540c854280030846540c7c807001e040d040010400007003030000c4204018400b00401041c0d022085141502d019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227907697 1250 227906447 227906449
    0xa020a020706030b0d0506010e071101060b221e06110303101e03061a040c0e03061506160b061c022d1e0f01030203101205030d0c02010209010801050f 66
    0x9040030344078840070940c44802c40001340d103c0c0c6203600c2d00c15820400796900c81d0385500505040c11000d440b0300d800185540c070022550710f4103103c1c48054541848459160068030b02403401407503814030b11000061048900058a01c0290060100503614507683d42c4c0018034008024020012070802805590800c1040000d440c02c01808030003980c29840da4009510a84800c68083c0d248503040149605e10b094481044800b03545000890010221024080070005c0b400484070b070b840501e2110381540c00400401d0707040050601d040a03903c40580a43e0820041e6002c0c0384078a250f0041c241c0c0c4032440f10044c094541040400388654001540102003200310329804591800f0406226180c890821030103101e400044125041010302c00919440503080301002151540003907544940c818224940c034010154081e0094030f1085960b94460301500e41342c01640030600138400f0742252035000411650710011880c0c840c4140015140e8001a141c80c6484005060340906811441c400c0e8005074514502d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227908947 1250 227907697 227907703
    0x9010e07090b1c23030f040801062103120507140d1515020304032012060601031b020c040b0109030503040b030603070914061e0622060807020a0303050402030a1709090a020a02 77
    0x401c0b14a015100b00c4c41c0c0c00007036503d05600400001c0d002140f0300007000910850150055010740d882c41c3c0042c400100290ac40c0c0070f004000c2000200420b1070600900420519030340060342c01602130502d2100380d0b00325018120607034086103203044016035403171144a2484240030741c84060154003072628020190004060340d139018070300c0010b012116441c42220b65072024040c1c240302ca08060405608400c0100101b41c030350742d080360300c1c0b40028900301150868545500c07846da54030350190047c0148019070000e000140c070608050741e0500c0341c4001c0010010300100003c000401c104110552241441c8081508002440d808071600314101400d522500c00703000d010300c0d008402217480c00381c40c2054032040d11080c043c0070030056101801103a6020461554065955944078039070717590180703c1d100d030802d4440000c01c0e00c10b4001640440d070a030002038004e81c0025040350006081b0313251521599103c4804500001030b44001210200e200b1201d0300b0716403072254100c02d8596065003041c41c0c00c000295 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227910197 1250 227908947 227908973
    0x70207080714130204030f02190f030b1b0a080103030207050f060405040b040e011a010e030d0c03050a091206091a071b15020c070e1b0a030509010e07090b1c 69
    0x10780340d2601e0032100c2c856503a0454100c142c0c540d07a40039900c603035881c1031400004107d0f032426802440740540b204059480e1255101c00c2d2046810100101415a180c032040170200510070b40d0403070106014046400d00e420041c003050045651a04d20960441c81d0003401c00e6415400140121700411074640c031139440304243c1e03056550035540004c4058014000901404011138130240c103510f0010301160240400d100807554a8080e243d20400803a4801455610b0302801400d100103040d0112840000344140300900c5004080e1a0440c04651280121001c03130031200c0c402c98079681d5507103507441040f440b40c01201503500c5194214106151241000c0d1003150000744184401d070440800030100b000b03011814102648020b0119214100100d034159030348114015010301036500c200041e80e1056081602c268a5802100e550901b800401c064000e4980036101e001070303540300c2d104101c030000100011300040079040c00116030b0f2203940381805410107501d56000c810440e0300d403281021810040c1c081d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227911447 1250 227910197 227910209
    0x50109091a0105090612090102030601030e19020f0109091506030606020c130c0c051f05060307031208060d02030a0302011401080c0a120201021501080705030d030903020a02010c08130f08060702070807 88
    0x10b54485144001034003a1040420045040c01e200b02882000c90056014520bd1031081e01c0802041590701103181c0e17a401e20700c00c00a608180340740d03c44010706129504262144041c180703401159104c1c406082038585050490111104041080240540c9401250000d00306800681402841c03071001c14240ca4041a4450704d071926902c2d100b1381c1c1842410061320355604602070b1010002c01205038000c1d402240148804242800c003c500c00d454041243d5044136070010038043d44007a50f48043c0d82e60b290050480307510180e66003d40780585c406010003171106100c0d41c00000d250061044076041c0203010b82140d001940705407020706080d00ca2052103070540b481421100380054452004078039006240c68140c12200c4d04000005001000103400c1082c0da00440a0306c0340000c4c0000700310104d4202c1e200c042c00580c06880c00c40c2c0594019a4584642c5003d000964940200700186c48000c0080d0b0b400800305410301d0f501001048800d10480c0c1c0c1180561000c0c0082038600141140c1c1c626040c090743e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227912697 1250 227911447 227911457
    0x303020c01080903040b0c030705071706010e0a0906020c0c030615100305090708010c020d0201050106020115170f1f110909390c0c0901030803160c0f0c050109091a01 73
    0x22900300700f020401c1c2d40091102a4180c0c1d640c1b036080ca602c503102e803c1000c00300c50707d200384000800d90b4480d094520a8204407640140303840c1e0710740f02e4070a81000c0045e00d6120100d80d142101008a5100c1c002048103c65010080c9262480c0a042c035140c110001c0040e01c030100c05400704412540c501000c0c40402c0b5007450701140c26220741516134203200d0709030700000441d860501c40784c030040c2c0c0100b078103503000d41c40d42c000b006103a99076407041e0309071052500101190710302c1400905c0500a10076071004000c034041c04996200e0b04444e00745103022240201160074500e83d1402000315030301c03406081c82d0260412165400c0810030070220304034000160603c41e030b280703850f000e0718400c8214510300d8a80d49040c01c002e8002e080e01410040840c0d0241c0303007004031401215440c1616080165003c0e040701d50141c401482d42c1d90b0751500c20704d002200c030407400c20401100500030104100880c0c214103580582c00310705140d4a0038001402d5080140d000e50b4409003056600c81c48800c864000c03d480031401e02748 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227913947 1250 227912697 227912701
    0xa05100e0901060c0b010f0b090d060b1509040e0a021c030c1e0b010b19111e01140906070903110a0503100507111609090f020d0501091101090303020c0108 68
    0x1603a0a00c50392040c0c0c0e400c040750100014503550700c1005040c04e24085c044024084c3d81b240c2c20212104268045c030464460100028040c9080c080c0d094204c1c94082c81000518998010000d203800015401d0449064004500011076140601c200c3d058201e050005181e110081d5020600100e51802c0789101c1516502401d000d150040992344561036024882c10304425401e8034075016403a40c084140c5050b1150b200100e03807001d03040c0458034600c21100d4810f140309000e09045602c0c003094000f212080c010301800c942c609007604480c40d410300540340003013000e51402e01490040078004003424000d034016414000103580091419040d00c0c0c100000c000c00000b08004a081890f42c2d80c45a03406202d555158030143d610f80d44058080e40f4281d882013072002c1c1d040c40c1540d0307508000304a1805a81d8103481000304140650150003c2c2d0310591000002c140142c0009110b54510301c404d8030340e42d4680c85039800b04040000b85104009090801710011030554900075610392280082c01e0503c541500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227915197 1250 227913947 227913979
    0x20f0d0b011814010b070303050a050402060712020c0301020c0304090c0c0305030a022a0f010605010e060a120902030d1d01170103020103092d1704061704030c051b01110105060a05 79
    0x2803c0c910841c40e080603525695911180c4c100d9104000981c0000d241401180d0b4004150003a140680c0d0000c1c03c1d85d041ca00ca541369a003d40300c0001041c0c055121341c498603003da403028005040040b00e00b201441d196850850b00005544500644c2c2e410411407600c4480001d4000003a2030b08003040038401030301d40900e00c0c00450b44c50700c1e2860115414002c24103031038042038000f03216800c1c10700e81710003440131a55510056031825130000c0320350352084040c000720302c100d0f10a030076100701183c641d100403a04000f681c001c03074102600b840300540000c0d40410520b441406411120400031020719020038100c0d120705a0380422401804005c1c101030316030504c0340902503480f00302c00308503403200015044614410483d141590380c86804503021801521040d070310040300011784c0c0490711191605940f2100d5510320030103e0340010400c400307000c50310880c200816410060403d21380d41da00500a01800414009020003105000000c2c0683c100004c002158403400c42c13502c22580c0584042500200d010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227916447 1250 227915197 227915201
    0x521090d0c0c12060203090d0903030f0302090a15080108060708070c08070203031c050a060509040b0a110f0403030f08090a050a03050313020607080909130506043002060103020f0d0b0118 82
    0x580000c60001651400c3d00a200f0035078000c60054501108560050200c0482510100c44510018001c102596100083d09000750005d146008009080440d401e0302e5090001020641080410001d604080148100e14040000c4d0b604100366061929051602480c002c2408000000080c4018008078591045440070000e0320400c0c500480102c041a182c54500e90041004a9503009520b080c010700254a082081d18140a5900302c080c40d0003554404c11040c01410b588603100d00c14500402140c500c1103504000f600185100ba03440b80024904a00c00424100d800f400c03151250f00040301140c00542d001501c00d06403513060404a480396203a50300c000c098040b440300a9080800050803000b0008144000c0c49549000c48008010340c07165051001d0750b03000039500030700ba5401070b000710f004190317501079044142c004080120207203560080c0219a0464034420310b0301607440310006004514010108182e5190141c402c2404c194060700c49440b0a101841890b0f100c2c494101240c407403400907 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227917697 1250 227916447 227916449
    0x3050408030a11010515280509070801090b151e0c07060c02030618070e090c0d03020105070e0927010b0619031410210506070521090d0c0c 61
    0x8101035948540250901400d400d46060124030319520384000580c9040c1c0c00b121b04043d901018210030002d10b4400c1c14065406006d9401040c84030404500240359903071f000501d8450a016900c1c16015450500703c0c409480320901d41c3d500c14140240c054a44420f084155001c98150a109070f0701d510314400803600310700c202880c090090040c0030021410079001010030803128829821524156501424075005203c0d50001c00600e400400040200c0e489010f50309401c0001032080e0b40400700000000340c0c0d1a59112004c5016075196000c01280d9500015900380302e80098032140c14070325103a20012285640008038102407000322010392006202580010203001c8058641035071894442200707005211704003069000641801007842c3d081885490450069082d01502d0f00c41d50f045c9010b0301d2400d0000c50080e008105500140c5010070400c000b128060030701030310b985603640c00340f0403180c2c0c01c90018100550010000d40500c2103002c400249920040101d19201c502100c440c41d019800c0703001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227918947 1250 227917697 227917709
    0x140a0b0604091b12030e0a0303050a1101020d090b0703050603060c0a110c090a050f01080102040f030f02060c072d21031205100518130212030f04090b030106082107030504 75
    0x31140820341a0f14035509130611800f80e101c00d000184071a00f041460b807418040100022400d010100c1401e003c0d000100100d45010005030034007640c40304420448000d28000e40e070490005061000240d058030486130400400e6020f00718a103060318003d0414403c0807001420000d0301c00c003e0600702c0c0d003840a507260240c01800b9103002d0601942a41c06018140c1d000d01108064600001c4c90142c14405c03903080311103d01404a1180c07071030b20303074511107a207c0c001030742c01400800000070044014042800500380458240c060082d08480764400701d04106110700d03400c1401d841c140105440d002d0140d2030407010400240c4003c03814a01190982d401700c800901417810001400400c820300b0402c00c043c1c6000355110742000a00d8000c0d590f40090940c0e440524500d13076094100035050110004030701c4140c00f41200d1802c10700240e266101e502c03a07805a040141d076164042c030945001c3c001c440003070072024010001e2a02180d09800003a80c0400f810f0f03803a280003c0d4840815000700141e030001d01c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227920197 1250 227918947 227918993
    0x30421020708011a09090f070b0313060f061404060e06060307110d030e0d0306180b01110f03030a0f0504020109120c0e04050606040f0c02030702010e0a03020d030c140a0b060409 78
    0x908441800140c5448080c0a4403c5000000086e9000b0700000d000c000d44000320700034a0402c1c0b91900c4252581d001802910600c07003440e56070b50203d2410301540d90480c502c5031000034024504000c500c3c0c020703424200d8a1040d4100141080340558100100c3d4100804862a60392912442415500d0019411004500b40612103c1c0d4074811f8141c0e000310b54110a000540e4000080ca150850403581c06c3d00440c204600d0218480e0300324a403582c410100c00406061406e11413413090401450a1000c421402c10f03035000004001c20030005001c0d0100100c1c210b401841282010384c00a440c40105000b41c09045c05006656418010300705a150020101d5500d03110040c1800e0510030744800089070418000c0342010384508200c1124411450701c010701e503014509060955004513031880d0050f4259034861008600071000d07a0301c80d4505141e05106c0d40b141709500d034503440c04003441c00e48041c40e41a560071104d00c15010422600d207907a40f1440480700012141c00616204444c00c8014880703103240e20b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227921447 1250 227920197 227920211
    0x1106011728021c110301140403113f09030304060f05090d140c0102061015031b09080d1d01030216050604030305070e030c060702060c07150302090901090203042102070801 75
    0x11000f048100503c0c0680018404050302d001450701380c071110074007000302c2040d400010300403e11401d109040341840310103031590a0194511030085c031401e100c40c0c40e0680543c40030026034905584400c1e40c0080c042c0c0020341071540100000f900c0c2e000b5481020305004000380c0e02c003001480391013112444000100365440e4038515080c59100d040c21041e801040344145410304101d0340c000501c481c805d110310111100b2145c180304001d007002000307160030800d150300ca015209002d00300c0d1014201000300c0e42d641c40003452800044500d040d00340510442030107000010903031801104c00c40300011000078200940e40b0440d4000e540900342011201811602684050100301035050b00114040d42c1d603030340c40c6030b101500c074020103803120580a206980b03c1001c000c90001810041c0103401c107404000c080d612881e90b18010100b0b80426291003100080d4000f8010b00300f03140c010310346805480030712030441c1985029503c40b42e07403006030500074403005a0b84489212240c1f0802004010b071071500002c0c0800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227922697 1250 227921447 227921479
    0xc0706021c181502100c170a0c0c0204020c06040c0608071407081917060406080303130602070507030b0a06090e03090112060807091401060521060a0510110601172802 73
    0x40c511041d0100c94890406e40e50700400c1d403140074520102440c2a0384801c440e140e00301800010b000131138140043c03010b0071442902503981c030300c00b400065003201c000e03144a141c02e14041c0c3e00910160891020b0003043c01c14070112039440030001041c0200b9944566480e4452300b0004414000c1005440c12032442100506260b40d02c514042c01200c42482200f101e0b0b1151000c0106440c1c0600034122541d0040c400115908160803900116902070341c00103162540c1c50301d40e0b03418148940c0040d82d45100c82c009100b5507483d24420480101444802048880d00340d040c1c0701e48910943c3c0301e460406c01038034420f4513041c46a40c000d8004159010480780110350b00c084440c0600402040502449219000001d0090298040392030f0904240c2101c180310a490b50255200301000c0c0140d80c200c50550800f00725503c43c00e14a000401032525410070702d04041071011f1901724160040c025640e1503082e0784c44c3d11500041c2d4419407804c0200d081c500440c460410340307116045010042e51161004612041d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227923947 1250 227922697 227922703
    0x190b030f0a0c1d010c061a0108010902041a0f0409090308040b070912141f060303020c0d02010e060d0f11030f0603010b130207060e1002121315050c070b0901020c0706021c181502 78
    0x14200c1f0131380b9031180903a40c60b8006401c1380528400d50384c012060f1640c894145061000402a82011041c3c00d030800d07803109085030403600c1c8403108030080f424a1041c0014040e20304c0f0322561140075032411000c01418007150050b680c20350b00d0001c1c00000d0b000e0038000d40711024014100e101414020900305480d00744498000703030540e84030a4015001c0c80007904810300b0710116106016406071265a0b50540c181b00340201584514820b070149a611208070000544a0161884110b0424042d54032401c0c080c03c40010100043e21840c82030313150a00100403078548810030707142c02854810058498100c0e042c082d001d400c2002e0101300714003a0a032004e686440d15406041d000380e5a50303594000e03990700d0900030000d448074900030300070a0008030b621081c1030b940d07040650f20004040b900e41c14405141c1d10350740202d6050f120540540d401040300300074007901b0004040281058070060a4035804803034621244442c0582c080204900f20030342c103001d0710401420780028885284900381c1032409c7d02c40251 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227925197 1250 227923947 227923991
    0x3020309190f05042a02070902040602070e06090f040b060103180c03060e210f09030a1110021f0c032d060b0403050c010e190b030f0a0c1d010c06 64
    0xa00802c40c440d001c034040c280307440f8a0f002c0c0c0101424203413085288694280e4540c601c005414210b101d16000440d00d0119030000d48010440c03a00248011420540300071061400280301c1d600038100703401000100d4041a04180d001038104009544070703250000104c02418104514802c18440360a80c2030401058182030800ca9008001c10013449045c118210749604a03a407a0041044c10a10b180d2031904c03291000b42607503407904000360300e44141d50011a003880c82d17000e016190307601c12540010103810403070b9000710441000e20180c40248074131100c0c18082400f081c071a1040c6503580a90002da0b90207035104443e40c041c4202c0914145554607000300d1000e6203043c05030009402c0c80c070001802490a000d980545e82d004004e03050056284004552801d0b03261074480d4014050003101001c0000a401c000c090030103890b0280e0359142442e106544c0c0927018104d94542d52402d014401280d80c00403000c2e451510b4a50000c480d4558400102c03a100c00010000e0080792a01101071101ca4000714042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227926447 1250 227925197 227925209
    0x1801030f1d2401080a081c0f1d010b0604121703011e08011406060309012a0e0307050906191829010807030c120e03120a0e030403030c0302030919 64
    0x310300c00610b0b100948106030a104886917076008000f207000103200725018010003844104013130f040c00020f0940c1010b8802c9014842c00306a640c107404070742c400e981510310000c001030000a204114948010484138856480f4010501000c0700b04e80341004600c2031503040103402c640507180c83c7e584030f1413841420f210b600c0d80c1d4101000740260001d495401809082c6140c0300203400c583c6655140f40078015280e000034005c0d242956164011007044a842078001324680260000101d04051440f01404102040159501c01d6200c00e004011b9640ca11908651000081d0b400c014094610500304018000c2a008241c42d0100030103a2407840b2126482003420500354244070381138a525200f002c94052031302c988a07000404010000d2900d9000e600700081580317130b40c43c0c000540f000f05a081001c072501e82c4203141060f0070018002c0e034044000c440842d004070212800300164044172070480c0e90780c4285e1000505000e5a41c441d030062500a03c280c50901c08003600c4891414060160040c5549490187c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227927697 1250 227926447 227926483
    0x40e010807030305030112020118080609070b03010e04060c0203130306020d0c0e0f09060f060403050331090c0c1407060206090a0206180f0307091a061801030f1d 71
    0x348490000800d282102c0d01038031514a942d0030484031030340e102d00703140c0182e040c003a41000ca05d100704500301c080c0f4010500d200181c942d90800780c9086080c0010383d488090380d0382d000d00045c00070942c44004140c0095000c23400203140c05151a060b402c41c001c6600070784041140c10703000000c0c44115002002e2604c05108200820744007610255001c10ba02d20915810441c6001020305a00f06401d4054000c0e03001402c03450041010000503246601c2500103c8640c0c0011072601481041e46003040d0034409000b41c0340354544610001104181c000c0d204800e946516401c01488040c064100c2549039a045030010710200c03d040700c4603645010700d224072401803180000080341904046452520260700030203403484c10007011242e01024a40520150f444210340c2e05da190556020499040100b0036140c010500d604603d02c4e02000070350040c3d1090140d502049848241004c2002450791601c090034000341210410803280010150428070392950800e080900c000c00f0030004207a6810b140007184 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227928947 1250 227927697 227927699
    0x6071d0402040b09010804060608030c16050904080a1211030103061505010f1407050f190302070e130308070311040b041a16120e0612011e0315090203010f0203010308040e01 76
    0x1030204a1086220b000e070f10b0181440184529032151952907089806000302146440e1110b920900b164090400307000140d11441c0c00000c400600b08803800100001c0743e03101c0703440c60203450b40a00340c81001c51283c01c11443d0b01040321366011607070142e40c1460a2403010303504ca684074604180103107030b002c10300f01c0720450031030300001c40390b200700c20500250034681e0f140000281ca80c08002d003142c1110108840a00944407001d00c0e00f082044111016560010003040c07485203410064280300c0f454100d5954807079040c2c2000040c01104405401d378590528108100d80d03070311001100100000300342e0025014000030005813501115018100342d6251401d13007406c1003110301c41404c052050342c240500741c0108440741e6010400031308131001c4241880c203064250711a440c0000d00e0350f621100d441c41960120030018009001c4052604200d03e411a02d5180d4441c2141c6400b08001000b072412403405403103040300000c5480079000f03a009038000c0103040d5160b50b140e1901044030381041c040c8074210600200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227930197 1250 227928947 227928949
    0x7061401050a0603110d052805060607141e010e0c041e0510170d031406034305010816050a0509040908030a05010e062d030f06071d 58
    0x2503040310300040840d00700c0c0346480c1065018004580c0b201404171414054091071040c40c0c052503200358450244010001c451802d030040d00c0c04c800e03004106040c501810003a6949696040b164400e821008005d0080040e4103890f00d80902d00c010000c5c1d004910203078200b0f02c0f00541004a802d0860000d07a004c01c0b00081c01c0c04210b80340207401240b00c030608400701402d00842c1d0300c0b46070020b507150306c0850040e0b12034040070000f1146c0329503c9055800b030f1000048071036040c4030b2640314400d03e01e10500e0f02d003130901c0081d035503131500700d03403484007104005425401c001c074a411031024403420360042100c008100340c0301d11425450b10506001c81c0996000800501c2802c0c003510b505072054840c1400c10b0002c0c24101d9040d040503220f03981056940071100003080c03260f8090b51180420010201e83c560414044508002c4068241800b41940b021039041d40855216101100f00003c030311602c01640300d00001e403500072181c01c904d009008030300a000c812540200507614516246c4c01200c9000c5842c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227931447 1250 227930197 227930231
    0xc0c1c02012403080c0309150a03060e040f0b0a0209040c1713030c0803062e0e060f09090901020702041d0d02030a0f08070311040b18041406061b0703080706 69
    0x32000082c04a41050a02c001154807010b011001c00500880b030400d83c081010407420501c9054a0088102c0814219601645406844064514184503000c142407990710503000e801c000071300500700700c254000200500c0032035058482c0107000510a010b4205100e101400c1d0040100d0350b01919032114000034020f08820748550301d61903059869071070340305068440302d007207801c090102d0ba40140744001024201c40f43d880b50452107004d108092000307012421018004c000710302c1030603000d42d400b442500c0d86500c41c072066901110b81551043c074a507445402c668024429400000d60180ca000c004201554148080c1194480396038200d070301401039000306030b90b0f034010085030800107104500041d4050b0301c41c00280750010540e09005c54041d2020740300b25102d401c1034000c40404400455204104d010603882a0384144d019501041150180782020104000042266000303d10004940da03062451101d007400841c4440e09817250f00b40c40e0f280a00340e5506c402c1d401d860050a02e00b44600e821504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227932697 1250 227931447 227931491
    0x22101050d030c0507030506010b0414090c0d0e10020f071707020604090b120708030a020d0e030703060507090312080a050601020c09060f04060801060906050406080d021002030c0c1c0201 82
    0x7405010400096078007181c00d101d6a1404075070314060201c00100258041240d1806881c200c41700b2a101c60611110f2441d452651265500c034806003024041411519000c07107082c04058480804c03018402d498036031400640301c000340355452001500504172039080000c1c100080c41203441100340c11440c9410703140e40c09004c0010354000d800700004c012210040c0c3c454285180e0242c0b028030410303c1c40c040c3e20700f80300136548109850f40000a51206e42981806990380f4803505040c1084144100c802103940c0c0c06040c0002440550385002080e4414090124000207540c0070000041004884400404960b400d90301c451410b4106008a601d96001040e0b8400c80c040c0070b03141540994421003004a400100c541042d0400e0707841201040001c030a004000c00740c0b041e00c0c0c0c0400ca43d890031083c4003c8401c035910221403500000c12484c00c040d40440d07104006207114401580700e84900e1000f072418421070359080c00398843e0072f81140a0000320302e04000b01c4041c41d00200b020101c1c10340d524200791a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227933947 1250 227932697 227932699
    0x5010801060e040c0c0503030702070503190510050c0712091514070201080a0b0402071b0803030403080c030403031d1014090d030e0304050409051f020405090403050d0902031002210105 81
    0x9054002c0101e09003540401210109850510314540c841c1d2035907801c2d40d0082c1c1c1c0c4240160003511041c03007281420404a5804640002085000c41c665140c0c1521501200e00d1400303c10745480204491442c040c0a03610340036005440301400c008208000b134000c1205201d04032451a8454070550900c0c09881e84406002d400706c1128a0b2042682c0116100c0000611007400d030340d074400f83c215141d01c4901c0581b070154030441c004110b0100d014a0164035441c1c660201405500c1003003004000b03948115126001030002d8045a101d84480c68150042d02c544902c800100010000d105000c410001d00c6942c0d04804500c1004010880880d0490307009044450000e60f9111880c2c02141170f00c03a51007070340340e030710700f001660306154580c0001001d464040d103094070300340e000c1c002c0042510400c80c204000b031080201d003107203402d03c1e190100e08034200040c00502440004565213245072041d8001024669004040c2e40030510305810781c0c0001c0d0030154045181c1042402060348449451300c6190581e50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227935197 1250 227933947 227933957
    0xd170a050d0b01022404060f060f03020103060e06030d081506132414090a150c1203150b071a010e090c12060109020705030d0207031d030a150507180308040e010501080106 75
    0x5c1100c84024101c00f42c02200c2c0b80d42c0d030710003440c2c644249102d080e0141c0f182c108030128040c0765000040540700c440d00110142c000ea0010b206556400181905403101981000845517a607108001c514580441c0b141d5008070340042d828a01c0060782c0818400e885040b000792070072044c4802408440442c460141000c05c5400101c5018048070780080c01e025134000741840d07455078541800b0780000b035980700b030300c400714440b1482e0714100902d0400e41852514585007c000f03000d06c0200c402a5090b02d48a8042100e41c001410701c14011004001d50b0001c801c01041102569a80000c4044090072201980940115a5801c00515048507940c1a8034600c20041000b80d0031305101d0002584010380444052104101c09030082c0c0d954009450394a009403103004007942020076071101450110038191107504090041000582e0b007500345d020301c00748620000f81030703507440d07206840d94105011a0038521740d031140000208182c4500030803e9809090008495036a01c2c0015203582030280150300c0462 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227936447 1250 227935197 227935243
    0x40905191d0a03080907030516050f011409010c03110312040c0f030804140a1802040609090e0a060504140115080d05090102030f1305211c020a020d170a050d0b0102 72
    0xa441013094580042c080030503070340f00507600d0792107901e03003024520802840300c1040c1c0c040003145090905560103001c203003800c0c4413141340c1a41d0b01e10305209503001c80d410b001902c11000709161049101441c0c8407550005c690b50341c54081050380e0500c000311800c5035844104400450601603021200c400c1300e610044403420305080c0f600c01146600007110003a0843d9850343c000440000040c840c1c00f12102c92203005070703143d08081008000c89015046221258201181d00c0b80802c03002441d0000e564105100064545603464410307034800250768450b00560074490103140d4682540c4c42e01d0700711b844290882d240386440190030740d024029030700c0150140e00306001c54030003d502ca04c01043c00354502000c4919054440001400d14414060305440d0011641d4080791340c1e80c001c12024000c15000703042c20f00304c41d425030b070001d50750038044070001e0181c500341c0710758000c0141c50107030040101c95400702161078000d1148002e020b0f40041c2c0580c4ca4a500701481905a940085140c8950840d024409a880707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227937697 1250 227936447 227936453
    0x6080321060d0501140f01141806220b03010b0d1109090102040b04090f0c08040804230d0b04030215041e080d050403031b1d040908040905191d0a 64
    0x400020401c60300704014902210005000380310303c012003c07000c5a820103904050705070340c40c120016084994001044000700080c1c1d81d40d0800701d03043d0340c44091800c4040c0d0f24000801c15102550000c4210080320a50112600d140740e08001d071120310541c0200b041d0303a201410003101d00c20b020000381c082411079400340300f0341c20010501980121884005454184e4031101c82d44541d03c02d51284060b13580d6400e030801c9005640c0911151101039280c00d009504142c1c440da0064071451249041e95000d950780c01e4a90b480821a40f04c01c1100284445400c03002030401000d00802203c045005001c1c1c60b28222a410b40340001074000d641142080031400a01044a4a003c000e40e009a907842c00030b2000b2650741c815806247d00c02e601c40c1e600850f050542000144806680403505400d000181e80206090706180d11510001501160040b800c2034640c14440001d01c2150014440716043c50b0800814400000d0302070402e189900041200c802c240032680b503072110304441104a500020418008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227938947 1250 227937697 227937757
    0x3020f0405040203451623131a031903140705240c0405010507060b041107110a0509041130011a01090b04030312020906030c0c01060803 60
    0x1205100340b80d001180d411160344c1c843d549120107401910100c408403101d0f24032002d41740851003075034450b0040c010044074603416001c0b6407441c020b017165044d030a0108024100482850320b070310103024208c55603000e01c9101010192106446000549902049840050400144c07a10b0442c485000030701060a15540854030511401124007803040c0501600001c59810b111200d0b0183c004080321001d2135441e56000f201081c0108009101d000621080041c4c5e43c0110894108030381c4980d00050050815001500405219841c040c620f40c001c94010300b0400307408007201c0d207981c04485101d01242c0e203204200100100700c50060041e100b95502e00c0031400e000151810704042d151880d0707071010f01c803a0000681c65203100240700e6603445044007000d8042a40c10070041d46400c0c80d10707040b20f40c1070852105081c460381c4030090400c5062515031007090400d606030740c48090300904465407030600364405982074001c858400d800b5440c0080020380c6000000840304100301903890414140d0502c42100d130 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227940197 1250 227938947 227938951
    0x20060a0605100525240b03064503031b030103020f0f03100c0f08010909081b0304090516030e0a0b0105150d0c090e0f0c03010905060111100b1003020f0405040203 71
    0x1410840308a00c13000017030741070089600c1c089241d0b46030030914059000f0070303070a49602e090044e0194124600b40501c03a200744079004900d0440500101440c882403010740f0000c03611004003a03000700150341e80d0200138000300007503006800786003181c00040d00c1402c0c81e1806100a00c4000d501807041c1140d235a182c10a013410041c0c00b10002c003074403400c05120315100103840740440c1420005151f08148010309400c00982400f4215528041041d20003d5072103201d02d1080300d0b0310202e035082d0445a41d020754800c108460280c030b082003061016040011040141c0c24039030348084080f0b0308002454420321000940700a001e03070410032501d40ca034030b00000e001c0c40c8101c3e143e00b10a07441082105040d410018022554031303222a503501802a0301d01a280e000901024090000140c908030901c0118030b00c09007600d05440081800240700d031503080041c0c4500e201d200c01d10351540200054400030b981d00340e114503961003094445801207110004118200c1c440c414514010351014030084c4003a05156000d59 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227941447 1250 227940197 227940247
    0x160b160609170319020f040303081f1d180d030209010306120c0302030618030a05160f050106080706020d140901030603020904140709020a1205040320060a06051005 72
    0xd0700c14401d4541c0c1842514481c50280e42450020030710038600c0b05030f60300c1188103140850031030070900c000b122040c482c0b10390b02c00902005071841c0824104400303120081d02c0c0f1800b000884050590721034a40e903104030074940340008c0802d064006105040c11100281423540700001030104682455402c0d0001d410000000d03040540d110004503180807691103846050703001d220203007009499441014604600100a031000281e1500030750381c070700c00010560305181000d0074a02e80320000c61003501440c400d0407030081d010f0120050b50409010066020809031010541540c82407500da05082c0ea40da005481e1850000c0c034910071507144847d02e4006070801075414500403800c07e0341c94002a0038501d06850a0314103081202c2c003941c0010040240304018102100e044d820510001e40150242d0304007102c4411494441c0001401c25100e130798208846080f9101c00089904590103403503680c00700700c8082c0701c00c4c2d2070716201140710710700000200401840c950b2a24a0926031902ca540004055040a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227942697 1250 227941447 227941451
    0x605100c0524101424090402120f060a081207050f03031014030601050d060c03091403040603061d1602161401020d0305010b0904020918070c020102160b1606 69
    0x36030000325079810034540e02400142e40282030308260140d09003506140d8441c4c0b10014070007a50100c0c64555103c000c402195136886000f16900610600040340301320051175500c144005401c61400030f4550318907009040c442e070b42860954400c0103018075011980502e140b654440c4107101d60f0024150000d10b19030703128400741c2d50766403219003040f86103070070a41c2c1c00500790a8402e028041c5a03142d500800da800c00c2140240859450100880e4200c04611400b40000342c50780c04606101e4008d402030401d490307015600c2100042c0c078048664072500a07000e00d900103403d207000003512905d10104040305e110b40c85581c500ca5240d810150301007084407070100c01540900c081c1c4d8142c80015400300760003844c4440568956010302d0000a04190300320b5140c07000d040c54000140014501881075444d074900030f48004ac0c0d20032881c0300082d400b0390381004500d1030710340210401c42460b42c00800844107610030380031640403010b00003140c0c80303098490281c900d1045003804889000c8440300d41e010314181c058480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227943947 1250 227942697 227942713
    0xc0a09050a0e090f070f23030706080108070b0309030a110f03070c140d0c0501030209130f15170c0f0609060a0801050118050d08030a1409100c030605100c05 69
    0x300d21800346552003140595080c60403c001c0b1441444501d5001c80f45130007410140782400c10139800440f090080200b0400000010601c0c01c020120900b0b01d880002c0c12079156982c0c4880042441c1000d00a56401d4010800e0001c1c982e6482c106036402141d010700610b003007481201c82141d6981c46000740038420311a40300260b01444082c0300524009004120410701d19051003010b0880d90100d11031580a0214a03560002080150b00000159002417801603038428403040055107021114003404001071619a20340040c11a541c4001107400b01d20601d1411b1a58466062440140d01004e011903030f001041d503441c0e00d150500310448490f038000c04403070800f6000e4000c0742c45504613411101c0422003150046c0219078101c14420718240804a90641c00c030304050100d10510408040100b4022020010440048440d00600e200b0b9280360003207203940c90700c0b02d5041d41d901c1140100030001882c1269807600544280180070944a01070203030101e5500480c1b0456900f0060700c4147d40f02e0084004c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227945197 1250 227943947 227943949
    0x50109031a040c031424060d020108150406080703051908120712050a02031015050a08060303040b160c05010912020603090c060a170f010e0705030403020a050d0c03030e070605030c0a0905 82
    0x105004903041035009000000501c07491506d2841d2440c030b692800e80e0384000b0401e980d038500600340c49286d420b19040740310740c13161030b60502c1c4444c21444156215084c5a0045a400000103051080ba8041c50403101006002c25420a080d00002009041920200030350315200070f114542c50b0f001041460b001c9020a4000307000e17011540181c0e184010550004140000e00b40c0c016030380e8028103c201880b1081902c1c03482d020702030b407088135802018888032400041e0385550500588008008800000e50b4510040b840b405941011840855800500070404200d0754401d882030002e60398600800c200540c0190208052600000c086514500c6035151901080d21f1760720141001c00c0603911903030f1002340c0b4031000d1050f5600092101002c4140d070780042084502c10702e40aa0865503604140742d8941f034a050403810300c1d0401001911510030110022109c5078000090800c0902030756003001490160000652280640e00c10000018824008140160000e200525207844141020800d0700d03910300c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227946447 1250 227945197 227945213
    0x60203010306021207020606032805060a14070309050a020d0203010b180604110304110411040803070308061203130b030a14100801051e040b04080d02180109050109031a040c03 77
    0x60402c565280c0c010078500e0f00340030710008141d0400001c4c00079014a00c1c10001099403070740e0028215085074407001c4500f000800c490000d0050039001402e44100d071414a902601030000c2003002102c0480d0900000d04c041d02c02c0c030803441d5490b480000341070340e00342940800240401400c8141c0c1d00d0355890015013110760302d401000800d056031400c556260721f04481048200c070319180041c00c03416400c000b048005000c51000c404441d9084800242c1c95620503803900c000e024a812951a40c84002040020f258103c41c1d520300c55801215410703c0b020b00702000d2600c0e402125010611021a07400c1848a2145c99002c0e44d40460300701b4000030401c1c41182d440260000a640031020142000c0e009e0040c40b200b1b0003003d81c8102c2c1e141ca910540900b00c1103c54034030000610213040082541d001c1410801040c08403400b02145580039515206021080c80540c40c26192450128104640008055004214580c100e82d0801e0703401c1950300300e12a481d80c503034400820894003a40103040110000f0405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227947697 1250 227946447 227946449
    0x20a080703110102180406080c0a030816080f0304021c05210c0a03090f09020c03121906080d08010621091505010810050903070c060c150c0507020901091401061b06020301 75
    0xa000c0e8070301600c0003442404112030341504000e123030b500518510700c03041d140c2c410340342c048a038880300b80e56a805080c80800c0d00e240270303c48010064500059451080c0a004014600032402201d08262414014001241220b01c0c800c0c01425034000e500407244950004290a0300103a0042e0712030b01c0e01c020a040117090200c558012008036001441c2840803401000642c005091104411403521081e6005030780e403801039003408021303500c84030001680e10014404a444014200c5800d000c140d40380c40c2d0050f203070802c410310100022121400098500d03c41c600d0b170884a0910780e000b40d411480c0015010250180c44805d640c91081c1c810038880991883c81203500030a021f00140851070000f030030301f0058440103007151031254403d20848022a0f000c680c03040c111803190402d07801190052500d0341d500600001002441840d2000618906401400602c0d03003d108503040010b6a03251032032441184c0c44001c0e0008150709035001400054021070148420302c48102900710b29001c0c0c7e9890005a80c07003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227948947 1250 227947697 227947717
    0x203010528030c090c110a03050403020613030b0408070506070c02060d1a060a020d0908030f03390301061701030c0509040c09050907090b01030b010230070809031c020a080703110102 80
    0x1769080c070b0b8072280d0380003003818030b5040d80c80043c05030055151002405800f0303500020388507260000e102c98108502e00902001036610802594080ca800c1c1080c404c1034102800554031801003000003040c241c8500b80c41e18490758001e00c031a041c0380314500c00360020052180141040040300385500d881e60b44000c06084600840d900900d01d0100703440d4010000c00041d40305039051340c8244811034068503014180da41c0b040921074407c01480006101512562354101c2c000004216521800c40c440580e01c0103506039007054a8131140b00580c40400b030310310708007407101505c1020701420a0000786040740006800034050307441e1002c2075807030f000f1a801b22981a220402d2584c4102da00b002080d0301c500513100500b100b406c1c10040c1481e2540081e456104424100700e1907883d00c0420307a0071310215010401480344691442d515105c8c5842c4c8034143d40e0003911580c1c4203100b44c900419001e15400c0500100580c55805000780c0c654555621842d40c0240c0070482c2801029903106100040c248040e000e1000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227950197 1250 227948947 227948951
    0x102090f03120414010e120706090b0906040e2d060f041b0f02010e15010906140607030305070516110108010602030c120702040b04050c0c100203010528030c09 70
    0x5010000c22408800d4800014040c1e0482ca10350750060340ba07401a2021a400e0403040c3e40071111311401244c1603a000380c8803543c070a000518000c0349001c00554035043c2c40c00e45d21018040f545030350a525590085220296200c901000305000031942184001e0304541c07030740c220003042480c1140b941081002400203120040b00d40342000b9a030310303110250400c01a020b6030100024000e5003070340c00c650040c043c00c010a002c46102c0154025200f5130000c40788c1e100c07203000e854907203000100c0002a10820701c9143c01c124284071002c51460b100624142030350100070f020518100355564258060304c2c0003007941c8144003080c4004c00c516091010100340c814841e6049000b41241c01002410403001030b00100e08561060103140450100001d20060354011000e9164940200e8400100500010f01a243d002800e20b070601080c0312110024004240003603050b180340040b4a41000e0880c007003482081c1d0b000f0400c518a03002030700798107622074008400500000102e502d81d29081820788031a03010300c070815 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227951447 1250 227950197 227950207
    0x30702010614010504050f030f010e0c01030b03030c1f090b0403050a020d020a05120f04033f0206070804061d0607090e010b0d0c02150a14010504020a121508010e0102 73
    0x1a4203129035000b4040504859800225140c002007a500840c000c0034055066520b0f042015079040082c0401161014000d0001c6a01c0440d00c0c0d454901c84004240030a00b4189220003c3c540841512946034141c1c009117401540c20031030720744c807250b14004400c40c140d46204100c0804d0000700a148201d00035201ea039a980c1c07541c0f1000749051940061081150402d01082c0002480400c03001c450808000880c0d03190320300b040e4a0303d4244501d520090880e1451801c0d07400040380a00500302404168080e10521001103100750b54041a0000040058111100080c0a00d0107903103034079001802810005001400580900d40109840c044100c03d940243c040001040d400801c01c1c014010007003920030103515004c00c002d05805400c1080c69100d07210101820719520800162503000003240c8079804070b041801c00240101801c460348040580c0c1000003140c5070404c0d000722120440c5c2551440d550000034022240104940060136043d82801c01c000a28034400b40184100da1104000041eaa6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227952697 1250 227951447 227951461
    0x1a06060f0f030f13020d12030f151505030702060609070903020d030207140d080904020c16241409190f0306060e0609040308070804050a0206030a0510060e1c02030304090207050303 79
    0x103181c440c161a10382a81c00050300c8070541254172a03072020200101c401f1651040d8040c0030030000c00104a4a015682d2818402c0002c0c0e460480d07114608905400c041400c1c12140707880100c0e42000036900200200b100d5040185140e46c1c00301061405012107620703980002d000ccc1c00c03103010907001a88440070601c6001d02d00f00540c0d000aa00300c4918580901e10f544041c25402181689440789a02180d401da200701c00b445280c2881c00d9004903429400d45440320103030721b0f8103c0d00d4100c1c8040085031000712151b0041310900842201403c08034100390700780c801c000e00820b0720320540740880340000d00050030a82141190001c0e40c402d48012480034280440ca0b8030f801e40081001c1d114010758070911012a40005107181c005001c1c2ca44a18946d546003801454014a0312000750020400800c022002400c0e62001d4010000741c070392502c80ca81c2d030783c0d003c507100403040e440c80b54068045151040c04220074010307025041d1002d02580d00b07159541c4e0518003240c100c404184c5458000004220034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227953947 1250 227952697 227952721
    0x3020a120209011710080d120e0601030b0412140a02030d0b03010506010c0f050118030e040507030516050c0f0303010902091203180609040e1c1403041a06060f0f03 72
    0x18148210401c5040c01c90010008140c1c88861204c0300e81148400041041d0001030000100941108000c076440c081003410000c01d00802514955045031070704190000000c40480e226040b00e401024003070b1592100d450b980000c149010302e010502c42d80d000c12100c400d140501a1003450302a0300078584a00010044100b035034481020300b4405d915000070001075a030418000c0e54055000043c1c403658000310715005004140e011026110b8554050200003019880101489100d005550500c6603844920007074050760030a4822041c0c1180e15064105180e2184028103070030001c5504441000d030154420703908541c420780003d44802c0c7c001030185881d0a001c26585959080c180055207020701c0e14021094118900e0259413043c0d500294200950b9241e810403142e44c2e03082c0701030741c817845444101c6d850309000c001d51003004034500e000c41e101004000360076a4401c0d0781015007a5074510784000d5248000c20020155680a503003400f1300c00e980902c101c0584456040409090b13680c1c01c0c08a14040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227955197 1250 227953947 227953967
    0xe031005010e06030d080c03010b21150a0902070b040201050a0e0a0308120702150c0918070e0301150b090616170a12050402010507060f06090905030909070206060a0311030c1003020a 80
    0x3090042000038042e041f25503500f200c2c1120b401c051500d450715004d20714800456060400da10040c100b00c1c00b40003070120b004064003c480421500341c001d150741c0f001c07504141d014008010701210040400a405175004600805021481e8034101d200803081c000001c03289181c540081d01d0302e4901180912002a0590076590001158002003002d911410359040300940300900138409900e020500c615642c885d007034003030b0b00c05035440c05004251900c58401008110f0b4442c1d00d5110790b0074000040031614510852509450350b28032501d107404400c0c41032041590004105000d00180646110085020a070700c130b020b103481c00c01e5003a03030741e511030074004050303001442c2a003421a1400c2c5c24000140c0c0c004003100c020a42c081000708401c2c2d04034000d24020101d40d0711240c5000d0501d1105d03400c00101000420000004036002403454a13a21b0003260391300d1003200c150360846805601400403810281401c4900f00009041b90250a005070228412100000420300400d8004c0b07a003c1c2c4441d080f40e4406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227956447 1250 227955197 227955223
    0x30203070203240121140a02010207090501050a0515070519140d050d050709080d020717030a0e060f0d090602030601021c050d0e03161b0f030c060e031005010e0603 72
    0x2110100e00c40c6400e02e030f658018030500940c1502842401d800009003400810079540006e40a00940f00c555a25921110072a070100c0c014054a84e01080b1032a0074880c15040c1d40028207400c0300d040c100024001007440300c04801d4002030060112400058081050380d0500b6200400751152a0440c43c7c60004020b02e4030708841c51f90000c4000300d03844d036840400d442c4d203a90003540121b41900c44240a540888440c2c01a4189006030040100c0140e0001221011074807050000d0a0040d2030002041d260f000d1058001e001400b03410503082d03c0e28220001c1c2c480000b801d0141454040c070351000200303c40d240501110500d030003204010103983c0510005146031014210b00d041e41c07010350b10040c402d1003458002d1600036501d111420085404106440c243c4000d076480c030103810650704001004802e00c8699005041e8a1407000c11940b01c1d5820f0f0504480d841018900c4060401c4001d468032820700c60001c1c0c1611404200666400850040c54024207443c0400341c01c50a00900f4181484030b408a07607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227957697 1250 227956447 227956483
    0x23041e0302060910030b0a0b03181207060b031f0b090c030f04021002070f0b0403170c0a060f020906030f0406050606070b3409140d120804080f07030203070203 70
    0x100096240d4604a4034018000c44881980c805813001c1a0010010b001c00c103600040503c50106d1030400c07150045000b0b101911700306a00002d110166542c400c800000186500018059a80080c0c031542000280e45001400d4905201e405000e15220300030700c040d4516036a4884d40c1501e0345003056010541c0000c0b0b101ca0851451503c445403403285070020b030000780660248514800d0341442400100082c00a034200145800d0344c0301da01d640103800c1404251002056041c021949010300c9089800c441c0e40d030005000300240688401c0010034200701810700c86071302000108070903902c0343c0065210b501a910b00108a0909040440481e1070080091340510020480742c404202c0190706c1030f6200c000400a1000841840010001c1511014400d00f01c460300c2c0c0e078002c2d09240c1080d50202501c3c11005100c01c0c1d810b103081002048010607030302400013249005510b01d054030407003200d5401402440c0041c5003a0303406500642d20f611444e02900140c02c04a041d00440c40c3c00d000b2000c2c000481c41c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227958947 1250 227957697 227957699
    0x2301120606020615042702040f15090c0905040905010e010501060813140f010212090f0304030803150a03120e0f06090f090703090204050403090303081e0703090323041e 74
    0x80a503882001820210b038150b80042140103990b180d400c1001c1b904007a00d000c1b03588800b0101d016a400e024408124461400c1141000768a4000c1c4141640f5804d00e01d100750250745020703441c02c001c164804420f000c00c0910000402d95032606c6c010701d048244540000034030804680a4103007160b4041c5c03c0541000344410a1050981c0b4030f80c60010071580200051407240000c88105162651141480c8075070b50001c581041c0f0180c520131b0f01c51081404000359541007031107480e86038a0703201c0c9002c020030b011414000702d600140d020104a8000001811800d10303962251114410402009801000124907084114290070900146c541002054406a00706001c0700c00081d807800011101c28010b152700d40024031490b110350449000160050810002d9003442c2c1001006840c241c04258046038040740800c3c01800c1c00301c10142d50300c020b608154126100c00c1421005004141c100b5810007102c10340e107800c800d081d0395100c2c44644010001a03030311441d007014002041c0741424042400165050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227960197 1250 227958947 227958959
    0x8030405240108060708190b04020c0601240e0d060b041509060906091509091704030b0105090705130e09030405270c070305090d020a0902070501050103021c050c06090a23011206 78
    0x2a80c2d1f10343d48014400031610b8040c0601290081c020940c201589100301c40001074680036038403009071805034140494103050050700040d00c000d0404400c180e0411202c0900002248865002d1003003554001c00c04170703d0700e6081840d0201c0304550340241150a80d58801017141c0e404d1881920300504e2124024404182a0341d140002c10f00d16200e401683c6850314516800c01460200d00284c02c0901c001944c0c545440b4200140d2884003401298059103607600824003e40c01081990810094400e41c0d0b404d0900b08210021100001b40228499200c24000421541e8501821100720b412001b08006902c2c0398041544003000007030642c01c840a001c210380804664090200d6020402c1030304c182043d4a070070f02c041002501181d110800841c8007107044030410006401142c100c0e07008650b07140307950b0b00e08045c00b003c2881c400c200070690707070101c1996661030400b0805062088801000001e40d00d0b550131000501001c11100b40b044048410005e00c076940c1c000098800b8601c0120f410001c19007012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227961447 1250 227960197 227960221
    0x10603020609150906041d1b160503090301020a030203041a07050403170708070609110f030304180e0601170d050a17100f23091308030405240108060708 67
    0x24242030007440c0c07402c0300d000507a0034882104d05501380039098590340e65031416030703e840c1909400044003084000700070400000b03000c01d031403212940740c90005244c0006400000481c5107452412905c5002c04c0c40121030a07a0300b032024001c1c40c292500c0150756480e092406103800f80f001c00700350000c0d00400c010722640c5540201940d0640341d00a041004038903503120904a00d0140c410010059a40018400d04114186d0040c50402c0e01c0f0345800c1c00200402000c20003541251440981c050f403090000f04000a114400e2110550110100203000e9107101102c3d404c0000c01d80104040c02030140360040345080070401d6010040742407078403d0620801102c02003805100000d0008003480f2080400d502c0600210040c00810760106c11030741c001c0d035440442c18250000803144500e6015019100748900740808590b01c81c0ca8010301c0d20f202a00d05035210314a43d00042c0090300c0c40d120b1000e40d680c0c081c140c0d025550700d8683c5142860100c0d0314010006140690013492041080f45001c18001410850 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227962697 1250 227961447 227961457
    0x30302060f0711100c020d03050403140703030f050103061514030304060e190303110f01020f12130c0b18010c02010206011809080d050402040b01110c0402070609020315090f0106030206 81
    0x20401c6003281c803003190480d4103d078003031849001c03400307130b44642d403074500741035124480002454080d1224000d01000c00d500b04c0b0030840c2c0290210b000100170010300c048210040003e10311070704000403071034000d40010007220340c00d8100300c2d5452360300d400b00c0102019004000004200f0340d50490101c2801e240400e0301c030f0146200791818059124540c402e5642c035110740d01040344502d114030b04a01d03074900300281108102c0c0c819200c64050000a0103403540c1c103008a41035190101030041c68607806898501c20150010920072300c80751808208400141410800401400b440303901d140c071642c140c15500822613241c101d4505000c0c6072801840188d0700410b01c00c1c111543e040159407201254901c001c00b408102c00b00030300c015000120110040701e42d500043c083d2740242d900b000b000600400550b4103004240d004a46940003c00600451410303400600a4034820000030440060399404170b85029008064495524207010401c503c02c1410440f03e00c000e11004000c1c001d061031034003c98120320031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227963947 1250 227962697 227962711
    0x803032719060c0903150609060602070303021b010207050d060501030201090f210203030f040303081005030111180102010f06080109060e30070b0403021005090706080c1e0f040f050a03030206 84
    0x243c1d500702002034001c803203200046402982c9403068040d401d078400007c12080c0a04c91200d450400b000c140d2520004000701541e9041c0c005107411042c0000d0480c05a5060018504512507020003064580718243c0c1045058400c02c00858a54114030016088145c035400403a8000425003040225190300c2c0140031240414503c0f007940c4204d940080303411445004013001c44000c1c00a070000405a1000b100b1348100307190000302480390344070304c205400d03951510009600d2800034402c1c00603a030702c1c050030126410814000021191030034540c4001f070320f0080d4000701da0b81e5901d00c07088090201a0059040644104001d890002010344d40000a01c855280490403110356074442e2002080c040c00320b0b143d42d03411103554107051900f490029034a403005541d40c104541031001041c250312002030403030240c54507511001010f40d200341020312507421450b103440e101e072543c00028445101d81002410b5441c800c4203d0f641d114144501d010541c451684043c0c002d100c582e10400c04654082005500501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227965197 1250 227963947 227963951
    0xa030201110a0f0c0f0803010f080105090c28030f0b0f060a03030203041401030207170705190b0402150d0f0501060306050307051503040f080a0f0e0916110106080303271906 76
    0x213418100f41c5001407000e44000e20603080000041041d0000c04400700072100d010009000560b40d0714580c507140c000c100342c0307244c120041918000700c2c4442454808019660000c43c00c4d000e95032a169544440d41442c0242c9080018405000400b0704411116a000406a404040702ea1465078029507a03c40c6110760200c802040007441d01503131183d01140c0d0041c4d00070761101e110140e030380110012907110101c00c582074442c401c03404110100524030300c143c0513081072084080c2d42e900d8090000b4900040100d040c0b108080103020902080ca20501e80883d2007034100192540c10840003608468007900058840c0d40480001c2001d82d13149603e02c50605102c5d40c10300e89907190303031800c03038030b09000c3c1d0000414102001c650040d04030750040d4010b4072120395680b00c01400303142c2018044c0500082d514800c071030b10b0707040d040070b1454004c1a10000341c80707190000041c2d00399603140160558100341c4215208904058082100000d40740041c100c4400190103080c4000018030b9200c3c40c0044194020101b036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227966447 1250 227965197 227965217
    0x1506010f051314040f02040b0405010e011107090225050109020906042d020c0a0f06290409141b0406060806030304031b091406030106060e01050f030a18050a030201110a0f 75
    0x911360b50003000021003401d8040d03403183e48549070b01c1c420717800c40d000301400100c0c0d60300b0802c030f6580b103016a003440c401000301500030359041c07051076006076001900a647d07200c001c07521400d00780c0c2003003a0040414000c1c8000200042c262041101040d00030340b14611490503c20181c01e01d0640800c003001107200d07208121494480c11080d04080c1c0201e80102c040c501685000030140f10381c030032314a030035184546000c00c05008000c0c2294840e0849550240d40039101211007125400d05500c0840c10f07500640007408030700d8202000f02d161440c65905140640c1d03a24280940b9030809010f541c000d400c180c11b000c0b15a00d0b1a00200e6a82d009520016011060843ca40b1940070701c8000f8082c003500d4952414006805424441502e0400541d0914002c2d07280042c00140740c0c1c4141001031041e20141e480c507280c400c5844030b00b0403541020b8603c1451a075036240b410110b100c40000c03680c07036034800d8000d08041e04103814081c0c03c4844500c046581c40a0802c518001254008424040c944082c00c00382149 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227967697 1250 227966447 227966449
    0x18091005130209040c06020706051204030e0a09110901030e0109110114040e0106031b0f021f0213030b101509090e1006030c140315060906121506010f051314 69
    0x81c4800e068041e411a018000b0320060088400b40c0758252a810b40031110580e40d140411a0340d44944c0b0980403465400030007040000c1e225140300140504010500c208003900c500c10304c0300710ac8000d05841082d4100090180700c07960907004442e4a004108000c003c60445901d4000030742e0864122241040940200c1d14040110074054401420300000386c5061581c542001070020301d95030607a0407010011199481030241305070b0008000c1441c40e40a01507117500d16590f1100190520f100482568007448400f01074484034075584000c5008803104242400c002c002040b5002c1030b600410201d04481120b2400031383c00101c514203c0c0c1843c6000152072542d4245503041c80e40400c003c1840340d0622900201f40842c0f1101c580a07107010800c3e180c0c5011190041540e1801030a10981941072082d0002c0c1070f80c075001d4072499011070090b08950182c0a0348018a0802c11520a200642c504000a201180d40d208040800000c91703402c00511701407500320000144851407044002e00c2e00c140b80c452001e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227968947 1250 227967697 227967721
    0x1b080306012006042f01080a02120c0417060403021b04020d2f0a0903020d0f02100801140604060206130311030714060c0915030a0b1e18091005 63
    0x2811820079410b160120b000c9240325200c2c0300c241d40a40e4602c10701ca0b00d80781e90310013150b178081c201c1c012540314140c10001100156030b82e080050800403130560910400c80075081c5c450f5114880c441c0410b00c16079407410400c90003940311100903111072960100301048000b03078000034081084803004140b08095031a100c005800ba10650002072421820a00704281800c007030b02c0c010081403103400c0c52480041440d107245035940180f201110000b48007180030030141c24080011400d0b9401807200c100c1c250000d801103170200551510324800640d4000040010b01c040c083c2d100c8560341c045406500c1c041c9072400007940e5000150140003000100d00c2c510040501500d21140c0002840081d291208081e05154100034030041850b205030044400103120840c175141260ba0310840105520445207a0200510b072582000782500b1940c1e60701e14003000165a800000109000018500303514070701c070034090081444c086010b030f03201641000148880e0b01030100e00f0350b002e440075a40000d00369480845500f2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227970197 1250 227968947 227968967
    0x1032004060b07020f09070e09041b1203090801020a050403030323010909020f0f090103140304080102041202041a012a06020a020f0d18061b02040e010209101b08030601 74
    0x1502610340640000c41102e090040c046460003141d42e1007001c0810310078401c4c110421a1801300282e980640c0b00d51074605000804c0d001800303408c00052010811b000f8140c42142c9821500c1c1404405961400b0076921100c00d9000c3d103040c00080d41045011030001e000ca0007240002070a1544a40740f0000c441491456a00c41c81c2d01065101c4040d69102007160040c02c0c0904240d0180720606001d030300a00b4018000105143c0c05003c04405a2940d214113410008000c158041c40c0000c010000c4c2c40368090020300301421106c0b01c919080055807040008440048103034005140b030078000709040c0d1780c00001c2c0d503044002060382d100041c0414034407920000000040105a184080307907500c00c0f01e5000030722036110310100040b01c68610b210319080e241180940410502d46507445002c0c007049110745180118414620343c0d080261b00c5590004050b900c00d4103028400341c2d03011682c2e050070318052085071b1000012b0309250303c1c412100c0c0c21a109210480d0400742100c43d000000c2440b503481a090f0803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227971447 1250 227970197 227970199
    0x7050a0c0213020418050f1b130e0a1b0212090411070807020301060b0c0c010309020103060806040605040519020109090c051201030b09060a1a0d080d020d0e0d09030b010320 76
    0x50480382040b00610081d0090702602810800c2d00e281090000b4451040c503029420f0140c0d15a1144e9418269102a000304031000856000500007410519194448000940160a000e803414a80541e0361401c17a260b081c043c654400c80030b400000015004104000940c0c00c1c01c2d444c0b9070390360004001c28050840e034602c001401e04005050014030100310042c0222a200320000c3c059140e60f807c0103842c0e0b018013038242010360403029a850300340d07002e41c0c40707052060300c10b0401003038142e0345d00040c03410000115801c3d200d994541040000304842440680004010031022070344040c200d40001380180101c0c0190030660340d443c050320040314010003d445c20000440f099071055a120b142c00942e01e00e040d154003071548500d10201d0181c00c543c0c010040c140300b01d019181c820310001401c00c1704200300010281d034a0101000100020301460008000307400003010046040d05a110502d0f14101d078181c1c009042010028061000551158140341103e400010010079401030030010001c00c840550f8103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227972697 1250 227971447 227971459
    0x1060e071b0308250810080309310501090209040e010e0c06070c05031c17041505061305090c12070501081803130f060e0a05100c0609020414061507050607050a0c02 72
    0xc080c164045480c82c800c03e0280803420300107644108040e6079002790208d040d44140c4484649a46607c40050882030b041512000c800241d00300301d0032421500d003a0004100709400050101d55802c00d8060f100030074142100800c1403114940107152580c0a0850b181c0c86003500140d007005001c43c41111001400c802410f403031a0000c2c4080241c6150700182c0181c01251149000000c2684001400c40c8900c1e0000301041c2c4000d41a03a032100144030090030a54060244155407450041c580301c0c152150200300c0051500c4090780c001c01c2a0707140010315144541c0d109031400c0c01242d0344042c0c201d4001c16100310401c0f101c11a42c1c041c0307045000ba030b80454103000108000081e000351921b0194100c030115113031000d0703081006090088a80340c50203000d402400080100c041940300d48451090240103240005010640b54006000c1c1c0c2e41c0c540481e81103003c858284011407824084c080349100029940c5850491259941502e0b440010701110604c0008a0f01c0c0b00d07e1030091601e41001c5038010300d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227973947 1250 227972697 227972761
    0xf070236040b2412031b010608031905120117010b032d150901090b13020d1e060905011d1501052209050f010c0f1d010c050307030201060e071b0308 65
    0x144d950f0703400c004000d60301c036000c00121025110044c404d49054401a81c090340ca40f1644100588103180303c1e50301001085000c22400b21a1500c801c4410302810345070f00307401045643c0c0c4600ca400e44028140480c0720343c001040c40c980b40104990040601020140700202890f980141d23203003801c1c15001080d070750034071200410100b0311042d407240344602d00c02c015083c026264541c80e010388410080c1c000f074128030401c4400c00800c1d0341340160202101c83e044074042c09282ca6a402041d1100c02d0402c85181e074440782140424070500082e8085d2150b2100100b103000c48a06440c0700d03210040c4203280c0103940e8500c10404c00321010400b01040655983c083c020003460746485540c601c035555800e4040d5280c800942045403040e0039400380071000b5900d0919200508050307042008032032100300e0500c280005400b00244091000d80b5025000b5000020741e14580000c0307205000c80202588100859181c0ca90350403110342d414880801e4061410394925a9412401a07445070a980e1900c2260728580c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227975197 1250 227973947 227973979
    0x6010311031504050309031e250513090203100506090f07020c06071110050f1803010209030a080c0610030f11040b09010f0501020708060403090b0f070236040b24 71
    0x17005003078081d03040c0c00700c40c0100f0450f01c2141d07445c040e080041015800c44d041e02081040342c0d000e11109005806d181180950303a80002420131061036001f90041c0b61a40380c19025841c081c031134001c0041c1400303c140201c0c038040300019906500103000c400791030b2031000480d050620800c07600c100d0300e0015192580e81c5e403040c1048180714840115451140c0c6518404c0f5006c070748941e00352072014428000c0c1a0803c4a929010410b10072030602c040c3e01990f0a00c0303444402e650402c140503049008420255a400c10840c0103420444000c105107504660400c080000808145a01001540101080542901e0b081c0020302511140ca07046a00140002c0007240300c41c9060032810858400360219410300d6500c450403922520112806404075003040e10402400120400a05080824485c040e01d01280b60f13001030b2843c040d01d5005a503020117030365550300c4603014003414903015003a00c03548281403034603681b21030b9841310082125207200c03282d55221020031745800d58000300c0800103160aa181e80944 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227976447 1250 227975197 227975203
    0x807060c0e130b0916020c33030601090b0f1204050304150c1104051015050a030b0d0209071803020a030f02101e050a0c05010507020a05120901020601031103150405 72
    0xc94081e216456800030207400c0040d5210b4002d078020054181a0f0300d85e0b58501d026025101e05e11410194019400d1701b50301070750f5440711810000c003100120b84104510520300c00441050918110715180100f0a000450780c0043d8040d040351084080d081c0e5404030003a14400718022040c04203210001c44050008002c0080082e0090b201c080079070035112440084100d5814949100180041c18130030300b008040d04240c0c100742c3c0d01c000034078a41c801080d500d4840001001040060100003040400c0162007036a2600580c4e60b0514103d0b04030f01200040d400041c42c1081c09013114061042c04d81400311644540e5a140f001542c000380707000d5103640c2e07900303080c00101c0812004070f10410940c01028851070240da03038070b01484409141102c809243d08015987c550007513918009121180080300001142409800e100d03001981c090305030380340c051800903d013002c404016141781f24203002c0c2c00b1407643c5c000381990450f030700302d00782c880302c5610703100880d003008400c41d280000100e42c01c0030803051200c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227977697 1250 227976447 227976467
    0x20d110d06030204050a0902090f07030b1207030b06010f050307030c0e181906030c060c0f020901081606140a0e040e030a1d0d0f0803100f080703061b14070807060c 72
    0x36a0148040d542d041b01420032240030b807500951142401001c81e031103d510410b0b85a0016a034100014000b2001c0c0010725104103914032201c107540140418410403501c1801c09800240c282400700d134088600d1030181107404010001d03801c044c2da521040c2c121910441c444180148082c0c00c10002c10483c140101040000b1207004641000303080020800b405544292001c80343c104020b02c141c0c6042a00c11100c0c0c603403c080540340140380c026600c015903114170100e1300070148040104040345101c1d04040c1c0001483c0d00c031000b4009028421901d50412400b100c180d50500d24042203c03440e91030006e4020300040301d5480301ca01c40130038035002c0d16402c040c00c00c0c40405000220860510b860040080c070082e42c0d0030040001540e4115800001e101d60095604600842940000782e500c1c0c86640742c0042e40da81c0a41107907440702d4010000e0003128866409980803456105000590510002d01401c44690080d0706614000810b401807200301002d071075065500401c1881460107038207009080c070f181 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227978947 1250 227977697 227977699
    0xa0c0c2f22060807030309170a080d0501050112090804091503050105151201110403122007050f010c12080910110a0306060c030f0305090102120903030a0501061d04020d110d060302 79
    0x10300b200200b0350007000a00001140d5142d0381e40d10380f060602450923180b880c1101c00707800764440c15118a00050461020f0103901c8904100080e05615002c001072a0410000440c11110300e0081001c004c90302d480100c2d026140300d9100030078075060001ca100500f4200742c0c0041c4c103952078a000d004194080080d5060008408c44d8240c21041e000c042203401c0316011952819a100e04210800000740061800c1045810310704000036031007180c000460f950701021180403020703003064106110318940074824403031040081c03070a50030003811a99015070110349030102e1428466140000780d040042001802074030ba4240703106214443d400d0a498070150886218980800d0a108010800c0d52144241048044c0c040e61800904000100c041e0005c2c40017420f07240d0315540030403210b5a045d420b403040e070740035107000300003140d40e403a207084280c1c200e0b181078109004102e28004240c00081d03020b00c0f11f1820b207104860059541c88000c1c00c4800520702c402c0c6a1141c20000302c0d4000c0c8030055a4040303011030340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227980197 1250 227978947 227978951
    0x3090319050a02030403170d02070b192304020d05030a020c090c0c15070302190e040b0901051f09050a0303050901111207030e040e01060e0a0c0c2f22 66
    0x90301590a407424042c0c030344000e006910a000400206840030a0001c0c0c4403102206503141440d103000d04410fa80c02004c09035040d1088105006007295005204410f15004240030441265034188201c01c0c03041402d1054911401071000c40c0c05d650b2034030540e0320090f40c80022250b85003035084000e03485040c0c0d160054440c442ca100000c6c5040800000c840d0548081c80142000070340280140541d80700c080c28020401d5030901c440c100707071045c07400f0344001a560360321804107000c07940b0100f0046d66041c0c2440c5014101000c01005240c96020f031110390405170b00110040c451340d8000803201180c8903481103901c407400010010505421400810a40c4400ea032035040d688249034002d540c0d40982110250204070401c2900e0100784141020814020300070004144e00034103601c1d260944020b5009412084040380c1806a2131f0200d104017606040355052810b5482640c0e220640c100b0414080c910000c4140054a0401140e07815124a0080f0050103c0d500850600040420b4079409101200c00380c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227981447 1250 227980197 227980237
    0x204060f0f030309060c0b0403081e07020c040e28030e040f090219081e030d050108010605030f0604051207050a1208070e0a030503030105101407060b0f090f040813030206030903 78
    0x40c0c850881c00b03201b40d800242c40d02c0941c0340e60b0b0741250700f0713000103005c280d0214440c1f00c02540c0d02600080c450040e40c055004244128261082004468240910030441ea1292081d845100b411505c440f10802ca0042070000c1c20705242010b50762030b07080303e441d240e10030720780740048482020313039880300340c1443c000c1d43d01d480c0d0b9011080740c0042100d050f02a003034056020300107201e466215411100c0840c5501d42c10f0300d04100881c0307004415242c0c280c0203041d0750b035101c0c40e0a0055040811a21850fa520b40c0d00030040d41c141501c505442d4050b200c88908001000038030803041c45010441c1d06141c41c3c2c84001b901100140007001409814203542c20b600050502d80440c02c07d281220a00701034a800c5000f0354030b141d10700803c00c41e520211802007401c0c840b000d004410f5012a46010700021800b503100400c00c030420100b005002170706039000703038450400f0000388400500d070080000d034415400303100540e5902d06810844080c2d2a81e0b440294448800010000f0004005c0098955184030740800c007012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227982697 1250 227981447 227981459
    0x1207030f0b090c090121090b0705030403050313021206040302060414150c090f0910030c0f060503180313030303061505090315100b041707080303060d0605040204060f0f030309 77
    0x6564003086182d808281940421a4840c800d00207280041d0141801003481c00b0f1400800d044010510600c85490b41c1d80e80c0c1c0c1d009202c0c0c0e8070141a0702c0781c8246403042c6585001e07030700900300d4000541407081108803402c0d44030454550114100403604250122901c520f81460b0080d51034400b21421141141403038881803080b0000500104041c2d90b00551824680d510011180300381c02100710300703500048071340840e61151610412540034807801410307043c18500358101010f540d000d50b80080540907010800304a09135000302940e4100341e2043ca4081009858030f605499806400440b20415554450000401d40c0660040d0100c0700400714185c07114111107401d48150050080860301904080310801d010000c1da401a588a400c600414544584508400c0581d4000341c20540f188140700c032074803506003010840d50b0000c001e0304005520310320300440440c40c00c4030220002032100e89c540c1c020500b159255000f26000e4004400461409592803081122683d182e203c15800318140c080003184e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227983947 1250 227982697 227982701
    0x1e0b0c0a12060f05060706020409090302061b1207080703060306150611030f040b130801060b0a0216030c0b0f090409050a15020a05090607060b03060906092b0302031008031207030f 79
    0x803107a5039100030720001e240c43c0a024180c6c3c0503220403120b10303508001c00701d80548035106110700c49029074010301003854807422103a1907142454540015920610089d0840c0190403a0740ea0f010109140c00c02c03d81e120444140c01400d11034200800903030903c5078101c6821a9020b811048030025a103059550304880030305500ea114540c09246c189000308002d0041c0400c1380010035202e260840c111040c1d030350f91a41582140d07a25003210400d0074000541101c41c6038104540d01062030104480b03c50285181d0313842c02e4440e81841902c0c000100440c64403c482e003964280c90050700c020703105101d401e41ca4a03202e0703298032480c84100d81d0030392214001441c0445038402d60b080c03058141c444d240340039143e00c00c108040d003081c9011661251104d0500302725403414071540e0b0265841100800c0705040030340c0154100205501a1249400f42b424601300000c481076402c460007072a800c00594a484400201669030440c0d000041c540c03000051007a5600c800098141c07052050366000c00081d100340e808501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227985197 1250 227983947 227983949
    0x605060a0b190807180e041a2401021009140105101404021303050d030e070b25050f0618010f02040b0d151703030919050601031e0b0c0a1206 62
    0x902101190344039002d80503002558015915040c03d81d1a050310b4050044598480d80141c640210700b24103210821401102908402940c201461107501d0304c2ea104006103250103041c04100e180c01205180c803a402070100d40d0908100200511822055040101c0e0f14008030041d030710590b03c0c2c10700003200c02d0107140503103043d1984841c040740b1440440003048040d4004c81e41c0c14143c4115910004002001000b1400019680303441c0441c1c21131810780814104210386d0701103118a00d04202200d2844070303554110350803408083c0f40c9040c006240c207000f4900300c118807080318244a110706000c402c08000000005408800380240941e041c03046249050f406544250720141000344508402a0000d421001004e050008485111680d805580e13082070781481c0c6545541e0000801c1c003d502e501404031109008580c0051900d81e105540e40d141c0d528070512002e8155803c501c001003d00400a04092906030087c22000d40307800c021084100540c0300450140101c0c860110b200659034282c00f40307030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227986447 1250 227985197 227985217
    0x319060501080c070314040e10080613061505100c061b0c020d0510050a090c050603060a050904110904150507080118022a012702060d0b0310090605060a0b 68
    0x482c0d441d81c202060143d0041d4400302c040c090302c6514120910724110181c001028040b180b40b0250600d04004c00c10141075070003000054020001b007007115454100311281040d40014005200350700d032030060800e29216000581d00c403420724104120305074000c0228035024010318041141d682c0e0803204214101e082d4010101040e00045280058a04030940703419040c010000e441451610307030760f242d0888008442c0c000c3c007990350300100403d1241c03640c9180302411045c0e0b0f1003403560600f140000d02c0c10845200c0c8a1160f410f2400080410501d4150045c0380c5002825200c1c1d07a00b8207103000701c03402070540390900c0124030b04000030340414030a100700d034121180034444a0801e108502c4401c069400302128002c4010390b40c040c0852007034507115204800d0f501100015021400b02080c0c9030080c0c03030a1040352001741d440012009a07403613804982c01610020000a0a144250b0129041403c4d1700071420b0f150740741c03054400602c03205421a606c20303681245e51158090322001025441d01440c5c031a8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227987697 1250 227986447 227986457
    0x30305030f0916050f030a061409071a030412050d0f05061f0c0305090f130609060b07031e030915090b0a0c1b0c0e0903040f1502030d0c09080a05030319060501 70
    0x40184c3e00f0112690380300c041c00a000d440070b640c2c10351106001d540d80d010014004104d52420480b040070180024000350800e2710900d0012040c001d0001c20500018001420000d5144000c25081d401030f0304640c03c642030460280000304040140000505089600764052540c2d031840360102b21100040c01c0340c500454940d84008402c546044450350400130985400034548641944a50303200311030342c1d004142914001c104107040050352015912030758003c4011600501c91400065003040d254101a0800e8664074044c18040400b140035120b144006804181c840c401c1040d103001039002500c5290044425880031307110b170103100e0202c506001c02800003c030f01c0f507004c01c4600c0c0c51802c00d00943e0700880d4180b103003940f03401080148040035162302259078000182003100762816024807000703000441241c1c0b640c01c2490400394992143c5051b13005482d035a03405802426004008820240c64044100e59495080d8500103689501c00e40310b1688500020703180580005050155405403041a524 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227988947 1250 227987697 227987699
    0x50907120b060903031602040c09050112050c0d0c02031b0c18060409050d05031005060306010c0303021b100b0a090e03040302060c03120f0402090f0420031204030305030f0916 77
    0x600e00052114144071075004008000003001507404201400207054100c810f8281059184100305c00c69210320058810700c1144181002a41e0b0840c0740507044459035000070965a450740c2e00c4100da48545d01c00c14444a00e01280c0204250b800400b4040201310f10a610042250381c000d41540c900d10300c60381130303030043c00036410303a003031140c00c012081c0c100c84041c002080c85452542d42c0c0d82000c9403502201c00041010080008e00c1100011401c0200710680e1a03504c0c6081c4040004d140c21324825025081c90740000300d62050340201e0345c3c00116241d000b01603c0718641b080030300c83c0103080414079061003400904d801141c44c14480c884c4c05074030402600213614207450f55081c04102d03089002d02004a0009020381c58201103400140e6100702800b07078600e103561400e44100700c0d2036000a00240c0149809070200000505c000c10110b42d00c103240031203124141001c1d000240b8000020100901d0190040390020406030003002843c002c2508925414880d900c100280740d4400004c18008503407082030030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227990197 1250 227988947 227988977
    0x180b030604021809131e02090a050612070b030a0606051309230108010501060305130c05013203060108060d0f020402030403051b07080d030c020601150201020418090507050907 77
    0x4003e00300080c9100b8800c078045403038000101160421994000f4205416641404021511010b031184800d907500c140c52005c440d40100e80c4482c40100354417a01552940800c90700c0e5245d481da40d0305d45140d94200c1c1c120395102c07010510203030029144014220300f00321011070140d000f40c00307a4060014012103512a01d18081c0010301078808080b100074040e0100308003080f1174010b90034481c00f92486600205142d450100c008040f260001d120b02074002000d81e800000030038841e8210219030782403138050314a0321000c0020840401c44500d84003400e0a03c6038204a040c09a0301a42c400c43c07090f200d01c0402d65406061041043c0802030081407102c03040081c000502d055409142c0180c0079142440c00c02a982c041c0042c0c003001042d403050035500100b4100050001000b020490b00032516003400344106500000c0c1d951401030155180000010b031030700b03150038804d5041e038004160740c106010303000d440c2a50768002000d40c07079020b45107801410300109042c1032564542c0c0c019141c039600d1101041d80c8503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227991447 1250 227990197 227990201
    0x100806040b1b070807021c0f120203040b0a09080606120a06110d0f140703110906160c0f060810060905101107060314131110050405090c0307180b030604 67
    0x107206242c0209001c0442e618403045030041d0480a01c9007510607594940350040054404c21407846020401c801c1c82524009100c01c5408606251f00140f07034208100411016400e50089800008442c200800c44034152544000c014088400707903401d8506c01d4030380509000140409600c480225031050110a0024000e41e1242054445014000d410071800400348015140034100c803000c80340d26965140315441311064902c1d009140e81c1000c001e0b0f504c0004c14546980035685007180704030310100e90600c01d21441c403041001c2907800400c2520107910342c2a01d082c1c484060062000107030009000800c100c41906a40061741c0a50300d84900c0b0a19040400404080408510007080085651400f5200c01042900060212614040bc040c4040c0110703844c8035400400c0f07406182b0200c01064041070711010034040e0a0805d40d2a000311241c6100c069800388666400030740c00c04070740410051600c0340c5501450050103039a5170508014440c1414427442c96030390140d0014024100702180d014a001d13 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227992697 1250 227991447 227991451
    0x3020f0a0e0c0d060f3003020d231224010509091e0c0405040c0c17031b040305060f09011406121f05060f0117060402070f0f110108100806040b 63
    0x1034801324855440d100c003855480311552002004520000c461103880204d00c2d0448031006990510440382030302910000d507159451500c040a10003203034004c10500300c00c251106001d045550240d40c0d15440c0c188011074604045429001c2031b07440030018662107550392035007614001c2c142d5603942008034001c100941600094900100740f00d990b03509411a080b945555449201c0c01041d8a07151813401c01808141c8154140d01d104105180308039100140c68204503c65802d48195200d40b80c1c1e40710b0361411980400314a00100d03681002c50b0010070040001050352080240c0c00020240e500c54070300e05426248104020040d80344000009038641c04c00e590380c1540003640724100c8824442030491800e03600780350306010703070015100e5040204600f0300007500b40c84035100703180a13007256101005030ba1201c44080d00e1144140d80010f03d503018000e4074541218442e401030074680700c810b00d43c50803003800f400c110702c21808140414000781ca11085c0c1d4002c3c6003101c440c50098070660b82c035503851500360200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227993947 1250 227992697 227992717
    0x70b0d0b1c03030603030306080f030d021e04080303070e0105040e160e040608150f01081e0705280519060c060e0111041a040b1b0106080d0903020f0a0e0c 68
    0x204015008103070701001c01440d060103a1000600e982c25401c0080c16100c0680000c01d141d44502d940c1d150300c5400004030f80f000d041c40d0800503190000d030602c1c0c0d010b000ba40b4000040813540403801250040d0040001c0d40141d805485814040d0f941c4001074a090041e40700e01510304043c54001902d0203503190703418030340b11030f186024111110380d0700004049807c0b5400c440c2407944a0080d20314014a03401030b1542040420301700000315858900320b070750760f2042c01c1a00407400448020182040c80104424000360000031300100d447e0b030705e180f58030111201050a81140701c40f0000001340c00d0811440407000101080740b25040389080444c240c80c2980c0c048011100d1507980c4420313811021080c450407245901c6201c0c11a41ca80c5044985640d241e101022107007088410441001945e1040b000c4a0720b10030800700000c01003040300345603401052aa4010b201034000c02442c604c040341c2c480740c40f8064034405c41c1c1d02c1d0044050712007401031a2041e8042c002e681000400800c0090403c4000343c607140c15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227995197 1250 227993947 227993959
    0x504150e0a081e010e0c1c06050f160e010203180607050307050706081e0610050d06060809160506030c03040507080a05370213200a02060702070b0d0b 66
    0x4100400316031200070039804100190081c0070041c0040486400b42260502488001c0c08592031485a142c0c0340c240742803d40e4841c00c40b81080c01e0120317407101c44850801d80c10a504100c103147c20420070300240e070100c07400f40400400004000c4054000e50056146482c1a4011807c1c540c3da24903034224055209800e990094050001c180000ca003000105021361180000e82410341c60704002900ca0600503004517904416041801c104090340981c503a406541103540359132144000d5420f03a15880b805000310074003400c01402280880c1c01a0802d80519019411144400d444074480008415103008155100f102000031403a07000600d0040c5030003074010019102c0c0d2580c1e0306225460b00148a40480342038100c80650031010000c0001c10610019581240c2804891751807611344481417110000d1040000140ca0301060b105c0b6802018415262075140310403a84c0f0151005036a00f01d442a04010b1141d0710004082910200ea007008a5568400e12030130070003000d03c01009040e2024000360890 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227996447 1250 227995197 227995217
    0x30c09080307060905210a050a0e0d110a060f090b0c010e06070c210e0d1b0609051017070c02040f2c0106060f08130c0b0307090e0106050415 62
    0x504188002d00000744100703000901d018091501605002c1c0807807403030041070540052034100e48a9807080b03504d011356a10f007050b41d4082400c0300f50b411181241080da000352070300035010104450304a50b040c2c6400c0031211ba03440196100011180c0c001699203c1c8002030140c0d600300202e40c1424054082180e81c01d00100795240300ea03408501d00102226520002020800c0480a0040e81031000c0000c905159244054059100001c0d0007400f01d544140d00403c800522081802641034407081e0b194801610000340d5691203030001d107100310601845104081c0c01160120750380c0a0314400305007403035081c00268a50398020342540d000d4902c2c02d0030307a00162101060400703281e241c420300c0c42050864007a141d9107523443d80e03241c215545201e40300c045a858440c041c40415040644820b5210080c076140b2644c0c0d40d40c09000500e440354a0000b000601203020125500e0015000b441c8101c03e030790f41b030b01c0394240d940844c1409000284038140105408100034440800d0b0440c032061480200c0c20540307603403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227997697 1250 227996447 227996459
    0x5070506030f070807090b0301121407080c01110d020c0907030228030c03090308060f1206042102011109121c0f02011a09150109031703010e06010c050706030c09 71
    0x99004440040681c81c840003044642c1ea0410441c541250f00c911b08941880d090441d000e0f01031006002d0740e070120006015401c104211220703203452941100c401c0e60340090780c030f0005550b60b04c403a40c3c0090102d401d1300741044462500045900c84040b540e401400c1c1d201e08101405941c00d400381488040540810411503166556940e8000303450020003015a01c4580750301c000c08032450605084201400d050829020a0303011814603007003102150395014103004080042c00e000c102c4c80308240c950040004201c00d100807040c105c2c0e600781c12181508142d0149110403401c03a8168901815110003e1041400c41d0420654900488543d44211400c06085005044180403107035021000140400340442603540e081c029203100d04031010029031001c06034800603003080e00c01800c0041c807001402103541c85a00c14200c80000b55003024100140c502941c41c0302009071b000b4026009020814008984c80e54401e00d91003140036005009010150304005045002e1700c0c600d9401400c04c100c2c4d00001c114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227998947 1250 227997697 227997709
    0x420010c060e070e01080307170a050c06040605010e100308030118140412110102090906041512030306030c060806221b03060305070504090c03031101021c02090108090f0304060c050705 81
    0x2c558081d0050041e1843d100c4c0074004084160081a01034000348200e00c00600a179100480100b03018814036165542020203c859024071200c0440911409080c08184482135210505030b90310004c2e094030f280d5851006628143c51440010f00302c101c02c000400440d0134088032003000000301000890300806074185c0c0f4403003400544082d60200c1001c50458880e070f030003510308001865488002e5003000f20400014451160007400180500e0715100c00410ba60300d5445e05c600a80100c040c2405100c0443c1030090007030010307000032900c180e00c044012407114000c84070300c2c1c8141030040071840403081d029011440350310b0700000050b00f80d403181401c17508031515007803c00d4170b00000d503000211685941449440c190a9171b200500a600e41050040407030341d1100c008050700d0f0141806901e4034449810240240720705041103203212842d9650310104c030084d0f002420b426000366240c0c030340c1e40c40d44032001c0c3e1150461a80c4a101c0d070320401040104a00038600c06030002e020344240c0b42d08c16511000720310703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228000197 1250 227998947 227998961
    0x1103010e100e09010209030607080105100e061e070c0501050301051c06090c14040506090709062a08071103072303030d05070801240903230703080409140420010c06 72
    0x141d80e17500030600e0813403810b007000f0700f03640310906150121055141001040790300100312428000c01003c81c0c00100729482e058111444034010070460035900c0e8080c00001455041944226440d5040c00d03c00140c0f50f10035000d50b0b058030f100030841914180043c04206074000080405c0f2001034071009454046401017007203500824001c892240c0e241041d80400c401c40b00002c15091240c0c0c0301101380014070380e20502d00000c0c0d070028104010100340820203403054290101d20040c00c00d026a441c1070030480803801404260b0301c00c4203a0214107405104142d291211402030700c9003c0c1154040e1000103107030341c800ca2000c400180c256031805240d05011410303030700201e80010200d2181001000f6089500e10300b4100540844c00c040f508008004000301101c07042e02c0301601060b0035041c03000c242050340882420308501c580440304026038900c0d1616154001d07100d100100d80c030b820398824000c1c1200c250244216800307411004846441d084c040600701c00741503602d042200320821000007407100e00c102c1c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228001447 1250 228000197 228000211
    0x70c02030d050d060e011508060117070c03120c020a1b090908090a050603040302030d0c031103040b0403020f03091c030905120303010e060d020616052d0706031103010e100e 76
    0x1640c0fa29180d0341c52040e9002c507404041c0c3c01c130000300100140c41c0642480300e9901c62902d0040490388414004032000e82ea40905920700c500004140301241d44c000c00c18882d054405e488148001075900ca6140031a050400c01c0000742c0c000404040008200c0d500807040c00410301d401c000000d0300c5014000480f0940007040744e04400025824603a86040040c0e80010082282c8541c958641654000e449014400390b108040e91144080c172485030007178010700d030f1110802140b2510b038a031500700301681e05c80aa5003035000d400380c45001180070b00084102c40728044041c1910141e48440e4000708044035030708001f6030802101010208295460103423102e0881d801c400190b44950400403107c44214003c0c0c51148079003120041000140c82c0c0d0400d54a41003190b00e002003400200c4c0c01c05600702161603880c0c1c05034043d00c59041131202c1644842e440c540591600b19152141c0368034081d01201e42c142d400300c1c075243c41407004012203444c8181050f4000c0741d0000e01500103031341d41009200001c090b900320b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228002697 1250 228001447 228001457
    0x50115090203041401061505130302040f09020405090106120f0c050a29030402010c060b0a09050a0c110a020603270a0c14011701170114010e01030203070605040815070c02030d 77
    0x80802d1009504400c2501c1441c0002008040c2c90013691104c1f20680341440d0043c0100070032200b04948100c04080021a0040d006010344480986a60010b0030b80502c204d02c26803602e401304944003030511032802541d840b180709468a0559480d0203441e100c0180d01262041185000800d07203480720041c11004202a12551504140001584040c119181c005e0049860180304020160307902c40c040e0200503421240005109210354046085074142c1e400c40c0c0401404c110900a60000d07560007108000725554a0500260420f02902d0b10707895000000796111006002258003102c03038070070300a50000d281d000310f1400030b1200301c050304000c421081540e42410440007000100101210a2814042440e0980142c00b80e5000d0071004030043c010391415000c00f40140101078004d51018a001c03039081c119102940c1e60348100b41300d00402f400200d002e80034500000490a0141098506031445c03500540f444214000c4807168070000200110100f0070010700340c40150b1828459460000f51540d58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228003947 1250 228002697 228002701
    0x60d0c0306140709080c03060604090602160b010f06172d0403031a040209030703060213030f050105060411030c0d09080412060507231e0c150f15100804050115090203 73
    0x1010700501013591100002d030308402e40b0790145e0740d800b0554640c0110100c0700022082c0e82403c10300020300401840c01211341c0e28401d03000a0000c1c0d9681c031030403150382034500c400d029110380c011140624400101d01c030b008600400306240052281421401d080b140c1c411003c0e4914600341030134005410394055001c2035503211007140c1c00f0010fa61030713213984109503801e600d82074001c0007096862040c0c4c13101070b202960210702d00708501d2003040b00d0380042da00215040000700c182d003440b078000c04d4181c1755180715602c0d0a440a00d104c00c0d10003a00d100d4490094198105551042c015029003207882d421140e2910800c404210143c54800d1403540b91b01070080050b141c58000b5000c4d02d01d10003070803103032100c40c0c000c00c4500c0c800140ea4219928a1301c03040b500b000e040c4440c68a80c91078010154550b49600070f00590418460894004903c610b03140340c041d0711980c80d0300190190000e4a80048c070b80001202261101c0c450081c1440d5070424030400000442c1c0d400c50100b90040f03103590f001a0000f81d00042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228005197 1250 228003947 228003961
    0xf0a09020705061006020c2b061e05060a182a110c030a080f21150a24021018110307150c060b0402070b0a05100509060d0c030614 57
    0x101a44c00745072565003c032598103125003e9603804034692060b2186034001d08001100c50885801c9030810305c4d01c50041c036100b06d0341c54810081c0444c6c01c4110000003100240c0c0f803114501c0c1c0121400740e2000f0f03010141140c104950208a00e52480d03079a00f00c1e03034807140814500300346140702041d03441503250401d600c4942da11000b03000d490000c0201940360b0024a4070042e69034081450f944269028205030303038519100c2140241030203071920307600029038852640783c40320001d040124460101c0c0c40003210110b4840301040031603800360003540c4040440030081441810040a44080c1d21594011150f1002074481c0b0f81061703074102c802100c00c40d5041440d0310100000007180c8100250228041c2c5030590400c4c0170428038801c607074050740400800c1e0000c14140081030380100342140015100750341c3c900050a11000c4d5200c01e4501d601094079000020320b0300f65000f201041503400041c0390003075584444081040c0c61081c1d060a945d150704046000002600c0ca110340e000c50780e28910007900d40c0c03038122 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228006447 1250 228005197 228005203
    0x1205010c0207050924090109020a140a0e0906040f11090f0303250f20090610020a0201030f0605090103051b0105070c0303140c03030708041e03050906090f0a09020705 73
    0x211005640c0070590038042e41c0d0350001c2d1554070100114040b00c82d00301c049400b620b641742211030107401008070800403900d00d0240d0020507107000c60391540c500100c40411002d44c140f01d0351210000051b040e903104400e034a03141030b00f140c2141e0001c0001c6010020300c28450700f20f42d0130041c22104208009032001705428141d046007a1841d044010707504025501d850001107140d01c0554412400b0816444001c001d0001108030000343c0054201880d04c00b00042011800c280d40c0c40035101d040e103c00000c080d843e00d8030f00f4144c01c005560290543c203105600650140c1110080e41000648940340800c7d51346461513494000c5005d1001801804a10000e003040c007207644800c02c0c100001005001c0100d9001e074040c0d0308a0390f1502c1c1c0301503e80000043d00c1094002d4106a00c0340d40000800c2c080c0315548544024021400344040c81d0465180368400c0c0c00c0b079420302400501082c5c050011503d14540100505030445005d005020900c0904000602c00061a0881c150700ca5000c9030351030500c6420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228007697 1250 228006447 228006461
    0x90402210108031c0b0105120708040b0f010302030d200d02061b03060a0b0a0e040203070c020a08210702040b030a0c060305010b0304080417010f1b02120405061b16120501 75
    0x4600654500600c56044502144d50450540c00054658035010504e900ca00101d4501b40050301d40c0b01c1007410052002060601d05950583d51a40460080750311301000c0280c20781201e500800918890308200313025103440d40300b41004034265a41625154420340709210760b202900d40ca501420907403804585500240003505803490b840c400130b00c100080e5803901c442d5001a02c2d2060341e100e4075039001a2085403011600700c000394009002209101480340c03c41110f040c424404c540c0340e4a5552148030aa0ba00d45404501003502c0946040604420380c07004024090540098000b0031074001c8100403d2404070030707100407100c00c0840041003040a9051040d00d0240c113003030006515500b03094542e564030f4022806805204403241a80d1480e05c0401d501020748001c0800d000c1c0310110f007840d0f9107100500141d04004c054080d1034429880354000c90115070a03500f0043c80103050007481880000400c81440c4c031240684101c1142041307031818803090300024610313900782429841c1103150046c29240d030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228008947 1250 228007697 228007709
    0x140c071b0b04050105221202131e0c0c06090803070809070b070b07180e060f0a0e1f0b030c0a170615030a0906020f0a021507080412050904022101 64
    0x1404001c1c0a061081000c81c2e04590003441c000da26802c103800400c0c0101302e1411541c0814100c50744c0051a004c603100c0c0402501c3c000c542d0190860800d102a100b0b54882074100560581d2a000045c00340c03800354401d61300101d00745002c2443c220740b56290812070344001c109561307044d001710412100c2d0307503c682447e900c074604101030301a0521340f40d82d07002640030b0350100400140f0080002801c2c0d511a4000d500184010f1103a902c156550302c4100071019000d842040c0110031050b160034081c00c201c9000c00840302001c16414407a5100f101e00d03100941d03060b0003600f03192518400002c9600300000594069240340607003d039600c064103009410610054a1016005a400204109543c50b250b5176083e800109019a0f92641c5002a140c0104500301004013a107202103400004840c40201518000c406a02120f441940700aa241001c90044460100060300e980005002815400e01d4655012160034210b041030f007c0320014042c0d81020b00001000d10000c0143d0300082031170f580c000c0c01456 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228010197 1250 228008947 228008993
    0x50603041a060a08120d0b04021c11070c170a080d0506010909090b160201020906040e0f09010e07030809030a0b0c09041b0f03020702030c04060e04050c03012d140c07 73
    0x482c14001680311006441d01e05c088480100d0344095141c03107070300b0980299400030070865498070300407005044100409101000249022000c4c0181802c0034202e90303a26801680000507203140c1030a07001158a00403e5982d24000c04649000045900c4058440c29581e010089514603240c0001455020300b9442990410b091000e007001264683c05034a4100c091003054480d1400308180aa019116628209410440c00107000640341d00c0010310380d0044040f6506841103490380d610b503a0989074024154541070f00158401c000049005c2c2c014010000041d042ea528100c9a8030b480181c11801c54801202c144000f8800703000d89007034455180340e064106d514468114014000400038610748036403a040c141d0019180055590400c90030180340e500510038400c07540c888071a0b901413603082d14100c0d1070b41310b6110090903514041c0600590f030101020744441589102c3c00c0e880814016131078103040990798010840000e40401d0205101d00e5202e01042e40e00d158600c0c00c02c850302181c0c0e0341899084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228011447 1250 228010197 228010199
    0x70807030c081305120d1d010905030f0a090f1203031b0915140c070302030f01020c06070302070f05010603060e071703040b030c0c061512031e030709050603041a060a 73
    0x141d04180c0b0180c02c5002c8400440c0c5410003440c280313181128605200c0300b8803001003051540e00c11950000202400e030740001d0020421030003541400d0741c40118000382290001c0c001d8010b61186c440251401c54054030703008454030b0307032852071441c54080c40d01b207000c0740464802d96400381034040c040c4850021022842c40018601d003a4005e2400540c0c0c001c1848403000780d5181c034111489011041d80c0304503160102c03503076030f1075224049a07a2201c900c0124080d0040c1d03101c11030425070600c269009081148080d010941e50080110001c0d4003a9000725a0402c0c110442d402007842481fa201c09148100b80001d615a80084094039100e55039100301c514003900381503024420706c0803082d07404a070003035020300d0340b20313143c21409041d6030140400d910701503c02c14040250181500c180070405000c113030741058100d902120842d40300d10401c150381c070116541400c000b5030411118019036101d10340d4500310300c0050b1100c001814581c004d0354282c13064010700050081285a00f40540c2d000441150304440003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228012697 1250 228011447 228011471
    0x1027030606031718040f020f03100e090706020706030f0204090c0c060b0a060c02100c0f0503030601031505030d11071d0f0702030301061d011b030302030907060203040f0e09070b0f0307080703 84
    0x184d2030800711207010300d440b0726034042c20718503e4040d00d903540b00c070501907a01d80c60048032014080f030f510300c60000c4e40360310f0002041c0703051030218010058900720760160050504005e01a4043d2410711410141a0750801000a5184444c0b01d10038585400d40d075070740481c20080c18400c05640003404403e00c02d54104408114594015500100080e4152020790040c2c104040540707000c40a01806000c080e00b030321304035003041408030046210f0a004d032020842040150346050200380b02c2c0c0910764050348a0b103540401c0c4c9002da0604189280d07e44100c030002901c500203400c4c12001c80500200350b24201061001815803903074466407140641c80107505540c90b081000f000554a20b8202d005050b0300c80c1c40422036403160100d20403204900d80c99100011040c50300a00950007204c032030040e4007983e180851002d10100840341250824042070311f416040c003044030460000a00f122a02c0c0c07054502c0059105400c40140124122285102d5240d1a0900c000b43c12804010030003020140b50000481203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228013947 1250 228012697 228012727
    0x302010c023913091505090307031413210218040209060603041a07082212050d0209041b023306120f100c090510270306060317 56
    0x6080407202426140d411041c000c550000990003410406608013900c920a00032120014030181725000340400030f03561050034007a280d0041d1400103000450b00402c000341c01d04080058203030884000d0005a08550b584803920b0f56003025592038815066605210341036203403502c540c50f0003503089914104580380c182c0c00220641c00062210b0703c039a40200200b801d02620448402002800ca044019607044c05100501035103011500340040445a509044818035450004003287d036102100305c801d2044424196456000350005401c0d4550070300c980c5a040d0380c1e40c090801c1405800004204d22008518020b0400e00d950010034038480c2560045a2705010300000036000d4080350100310401d441d03400004100250320030241c07001e40310303003d540507032034001150b40325031018510700401030054040c0041d90250042e101c0c440d40304e4245030b910784011340a55001c8031001a01ca0710824000e175801c02242010754140c10984074030350355890510070060221448000d107200081002d08011207103184140d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228015197 1250 228013947 228014023
    0xe19030503040b1c0501030308060906040b1036170706020705150c06240409020603220b0403031407140a2a06022d0a0804110d0302010c02 61
    0x40f074000042c5010700d0006004e05101d4a50036101c040c4915652810001e10008050b00c0c503c1c481e8040740017141c5586064403400064a4019020310f40c1d1410003001031311910a408508480c11601302d000c0100c62a0041d043c18a601c0c80181415101c1d080082c2c5d15040700c10300201c910154000e07031040c0811798002845004840702240c45441d205e540b218034001c58081c145260107144111418081c844006913400c12200e402c000d0040c0c204003c0c04100820303242c0c00302000c6c2d0800020404100b03020345860340000900d095400c000003001c41641c424000c050116000e40019566201c240c0310314040c01c2c0386507000a01c82c80c000c0744010589410350910f00c1201c1242062109050450980c00b415480c1c108407100c178040658124459401e00c28040d62000ca820100b030880041c20306902c0e40594108128502c00e900c4050034808000410b44021030043e1099461030403000d1100f030541d071030003007e1814500c00c0d4008203000500207001303840c020400090b03d034038601100c2d0100074442c422402c54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228016447 1250 228015197 228015209
    0xe030c1207060f1409010c1e1b080c061501030603020906040c091505040302181506070804180b03010c3f020d02120f011206020702060c0106060e1903050304 69
    0x1aa541614030380b42008225880e40c003450f05080560443d000740d0b5030762480c1e10030340140000b0f001002a480e012120070750010341d54086020051001c56000b40710b01e0480110b000420940c01c005a000c0c1c5403501250405050341c085948420104800c0d41a0802c1c01980a0000c1c281849050300b0b40c0d000460190004124500882d516402402e445104d810088010591420b600310184e02c1003900605690180c00164010308c18000ca141100382281c849074402c075503101812800f400120200306050748410360956082e00188004100b456500683c01850710100d034002826111040c141400d4a0407036025070248400d030b0181d01030000151420800081801400d02c1484e0b0070115030007850450340c840062854404596604098080d1b4018003031829580c0003140c20755207d480c0000408801d00036502440d00d8000d4240026103260041d04180d48000d16150824000801590856120741d0040002070102c50084401d42440e2054104807802c401c04031030442e0551f10340e0f0f42e5a1086124030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228017697 1250 228016447 228016483
    0xe0a0609050c0a0b0a2c100206090106060203160f02030f07060c060c020d0c020f0102070f08060a0e060709060804081b0718020703091a090604030501050702010f0615030908040801110d0e030c 84
    0x752510002560000aa61401030440290200301f41c40250358501c11152400e45600c0e03c000424510f00004c15641c502101245c20308880c1d890f9900c030000c10f0302454040b07030184602d60415111000900902c805030540e030360360740b903541c1c004d090001c281c0c0c100440c00415504041407c2800c03030b0b801170f4480700041e015600250310090b1100102e01c1e00b5042d031b01c040c0307007480c04c0340000c1008a00482d00500449030a1814403401d8948107020b61a60020f43d504400301e151583d081080d940900d5406601c24018440142130111041c2035032600010f4120b02109508400340502c610710480514550040c1c0b00c5904500b03282d03107035801070320102c0c650003000ca00319203516007090007070719010032141c0112003c5c2c020354840344d6a1800d14040e14081d501040507500302054001141001d1043d41c08882c8038513484580c241084109400a001030b52003611151410000414011024014000450001003142e0340e1901c01c0309801c82100c8508035110f140f9042040300b000032100c000303004000303124002c6d80707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228018947 1250 228017697 228017747
    0x3090f060a270906080c0321030f040309050607110102060109062601180510060602030a09150e0411130b0f0304150b130912080903030a0e0a0609050c0a0b0a 69
    0x148490001c241e00c110083c40c1800000b15541e81c01240004034000c042e0101c9092991800c1c51a161101c131a0b508640b01900f0300c0000d416211120759250041c3c041c1c1400c1c46046d8969020680941c009482641c00f500403881e540001d5904101c424014a0940b070100320842c01e01c640c01e0384400002c20800568400812062300d40e110070752000c00c41c010407a0685c0000e141c68a000b98a40003080d408001c69490328400141003400402100c4403c501e90b0b81c4c100321700381041f041c60b000710a0301c50104104150110400c05544a41c841e03024200f20b6240c20b20f4a800d6403500c08010588240c01501116105100c04500d401001e011340781c000741e002a401079600700341c6010741c004000e11081c0951003150744003440059241603002d031021500803101580c58002180003600d0702c080580b1042c8441e402040004e00c800071a9110b034450450302003e0b90300c1d04086459103421b94240d1002600c403a00301c14501c403500d280c80d520400003132240804050074080210406880c0c011b404e04058002d02c00004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228020197 1250 228018947 228019007
    0x131401090b01090e040609120804020d0609051504140d0504030c03140307061a09070c0203070e07120203010e1f150315150905030609010b3d0203090f060a 68
    0x104042d280758600060700c0e00e17043c1800e074082c0151010a42c3d45a00741115101d815104160051050350058065803051401d0350382d04000380401c210544650160180001090440c0883c11717008034002e0007050000074400b1941820400c45044020901204210030400201402e190f60212900a01c1401c030b0340c424441d025055101e0620300800c1d99240581105203000c500749000d0682c1c905903a13a0001d42e0310760900365160488101d0196040d48070007020041e41c0050b119513940101c540c6401c01d1886c1d2408e80c030720142e8000784c1081d4041030446081060004030076002400800c40c4000c010807a81ca0840d1800d803140448507104100744c0c17103003450700e0350100242c001c60090928656101040094041c01011303141c20303002d014802d005500202c0d151240500540d00c1c501d600400310b0380c01407109100485484100110400c1c03021801c91140c81101400384000f051040039000f66507212484c0040283c4070300b11f0086940705001c00d210006074241d0042c00100c540d10307604041c2c1d4610300840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228021447 1250 228020197 228020207
    0x201090b01120302070e0c07050705040501051305060406180608012f0309031e0304120302030c0904020319060303021b0d031202090103110c01061707030b070503150312030402131401090b01 83
    0x2401030503946e00808248001903500d0801000994010b0f016540d17840d0310b400810058a40a1007019800040b606c0f0516910140364001b641049006000141d07103680c03103c0042c0061281da83c0c44400981e40c1c1810803d5110070301412800380c0030a002140e0180180c1e0302c0b10a504214080c3c1d4909220110010f44654401c10440b001c9111303c6001c00c00d08641100d0010056200712012210058a450f030803444130b009000b0f03a400390200da81003a00b070500c1282400002d4100510708150600d031800512440e8a161091001a5009a02401c800342d0030080c0c6c031044508034032202d80034220f5540c0060103c1c0d03210301160389c44001c215001d607403a061280101d014041c0303550b80d00c4031030320006200c80f01d2030310544c2311400f00c0e56911031494028441945041c0c4034003e920025108003900b0300011020341c440e400071035022400c40d4601881140c1c1030007190ac0c03c1310300e50f60700c110244000103010035841c0100d0402c0c101040040c0501071148820001c044400f0184141c2d440c8940303c1c4191071440c1e000b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228022697 1250 228021447 228021449
    0x1a07240b1507050c030a020312070303060504050103060b15090603010e0c071b05030d050c0309061b01060306020a0e100c0212011e020712090f18060305030a0e100201090b0112030207 80
    0x2404079880703451403185030400b9404000222114418544041c000c1d08010404103050340e0028040c00307e440b11114825059404810105c04040d0b8510300800d540e500d5100d02806140541c0c80060000112028011001356500e40c4980c0d510b0140070141841ea940802c40741900e41d003802e08a03040d21088050a50303401100750061030041800c0e5040315008140c004041207401c00c904a4400c18152042501c07030b0b22412140d4811500100500c030204d0800e54000c0c0b400c03102d003081d010007000b2034548160850700150800c54001ea0002045400c680d407140e0503d2903c5030480e0400700045a4200140c60b0042c41c000081c011089543d1400f0b017818203503c0010100840c0300c02d0031815200203101c40003544058000ca4200808200e0188221701c0de8140c8003c3d1045400d460800d60304180301841d1320440301c40c0820b1003944030100400020400d1002d80000101c3c0e85502c00c40740303140c60401010044410300c10045a1400003803c000c10003c403410ba045600b5200002e80c049500c3c00d08908010031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228023947 1250 228022697 228022699
    0x14120610050f0c0c040b0d1a060105070c0b0306030d03020306100c0813170f0a030206010e061f0302180913060207020a08060403050309010f0b09010308090a0806101a07240b 76
    0x10108002c0050000440c80084c140e01c01c5030700300300002018007082011400004080e200c804400c44030740c0700407880220150410f405040050034041e10ba9284020f038140c40d000b130340c01d012003c000d000c0241401c011503491b040b8242415801c61500344041843d0000080600082004810207602844800d500b1a81d200103e0b0084444c040d0311404541010941c14402c03103400d118526011046480104850507980e43c554007404541c1d1908890040364040641980da0000c0b40383c00760f4581d2480c950034200c3d07031100743c1ca000d601c07151280203e60484915005060007600c1e0101007003130141810b00300c80d080c282d1141c00180c035403200340040740392900c0c036400018041c46540300b444180b54010015603c00c3e284400240b00c508180003040050742c1c08182e103140c0100440e00184001003000c4040c201e0160060b100f0140280d0700c0c03243c6443c0c0501550350341c0c6504984070781401071402e0100555140c4820050306454107902e80d665200900d401c9070741c00a0311003034050541d00401582c2004210040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228025197 1250 228023947 228023977
    0x80604060e1e0a0504050624060406090806160f030c0c0b0109140c0a090308030601051c02031e04020310020318070b0a09062d030e0a050d1412061005 66
    0x1900c16902602401030020710000b5502c18800260f0705400341c004c0c0c40c4100d9208001d8841e540341ca42031240440c0c0244d40400441980f188848010745030b10005d000180a0741c1d0b5007420541c45c045084d410064090b140410812518902015054004c01c0402c8240002d02d4002210400e13003408541c0350312914030003014110b08000004455515401c07800d20a10303a20040c44460722000c8400549102d80510741b0042002d4110070008201014055940040c06050071031403c0e000c1c2d45580382100304040c007050141e070b000c03062100c1500c41415114201800032158a800d04090300040d598010382880c0d1078442d50008000f07025030720000031030f01c5aa0710400850f0406900da134420740c0c45411035100e03174001645040c0c00142d900d210b0072165602c0c41c4042001a841024101031031426540e05000c2001d1684070801000a43e8040145104050043c4040c002022807104024040304003e208110118001e000d0341c1442c0208a900d5074105004680c03051218a40c2c12054441d401400550344c4148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228026447 1250 228025197 228025201
    0x21e030f0f0c034b030304120e0103152303030d02041806140103050903090d08043f0c031e1205030c09040b0a0e01060c0c090b060a080604060e 63
    0x114001082c10181104600352440d421040e103940080701a400c1d11070540c0e8625440b10400c0034521030503440001c0c1030180e5541d441100a82040c916403064404442403241c640d2071003652a480700304000700e400c09107001d0068541c0701e0b0840c04078504d00e0107117a0380c50203011070007003254007819003540c0303ca0400b070203032621021200b2208009401511820000d080e201000d20034081203403160305c007920641c2800d902243c040d0001140180001083c1c0062880104100030240e0f680c40d110602c41e41c451146150f44500342014960699100c0081903070020448602c0120744914041071040d14846003002010301c0410b05020410341482d5001400c1a0011100d40705c0b1075800602c8510018011500309c0c00c51304a050040f180d522040314034010312070341400030b40d01d1071030b15402006051000401044c001078903a009440c5020080c0e120001190b002158602003080c1d030100c0b44020600c8000400c01c03c2890400f04d4068032440700c40c001040b001c04009042c60790380750302a03c09012394010580b07081c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228027697 1250 228026447 228026473
    0x100b06130807090b0628090f120203010e030307021203040309150f030b030f0601090207050106050603180d030e15071803050c0102210403021207031a01090b0d021e030f 74
    0x39280a001e1801c3c81070800d0782c803850504020084072120014100c0300308004d4409120860001d0b0701030000e50800084130000540040c2040303002c005000e04071150601030f110b40c0304250866190b12180c03110f43d0818000c201029401283ca4078014005000035a96561076240031107085940b030f0400901c013030000020512041d403003207040f02030b007030b09840400c580e03070840040543d2038461140f2a99290f10460050022120b140c000c1c0c00d80d00d10030070003ca110390b210000541240c0040f1100e41c40034418001c40c3c0500502003000b8648504da80c1020860682c0b842c61468a940c464a044082179140402140f69184994504610b6694480c050040c41c1d4880c94010b44824060522500600c039002000b0008110481600400004a80e8062415203075609002c00c4440a201422884c002d00c007000001c5002d90a1840d090008075081d21085e40c101000781f0222100711984600030160a000c070001621402c240c0106801104141340c120190100024581203400501c0503003405240800950 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228028947 1250 228027697 228027703
    0xf0a031d0a121103040302040e06040219030b010312121b02250311012708070608090a06050a060503030d0203040b01090c0519300c020d02100b061308 66
    0x205240c203561510034802062a6640c0c0d109420050060002c030b89640079800d006001c2d00b5890072469090b241003542d41d40000d03084581040082800b40c008108100031460304626240a160300100722401680c2503440d20a002e2105010040400c010240080c44640c080c2da40300400c5a07040100340700e200c80400030350302d11510340307000040948a00d0814240fa4500c4000070640e204007802400c403240e1450b1030741c0c0c1e83c4490b00415503040c420001c6880210401003414464200d107055810035119261100442c50003807070703074480301c104000c14090159412010401040c0282c218101288071f803a8006400001c0100c2d80c0301c90b60602c4001081f54030501c45401651080b03004600c220440d0f80e850089c101603451a400318000190100058000b00c1502d031400440d58000d0b207000803001c03690f03000290544031141c0070385200904c204041d10b0009020b0013a03001c080010710260aa03003241100203503072080105081103d01e92522545903030344e01d03200300741d0305104801ca076108a90769441d035250b52 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228030197 1250 228028947 228028961
    0x406060e070512061023070516150201050103230f030a171302090609040317040303020c010b15040b0706091a0612121e0d0e0d1206030c0605070203030f0a03 69
    0x80c10901d181e0003d440c0d8500004640b001d41750a445211071020907502c0a003e46140340d034403014100d13090209001248042141858a00c2d40d922008032242c04c0145410b414030304c1c0f02c4103e08682c1031200600c001166041d5403032000c00a040c2400e01104d4404085061502800c6000c00600c404a200c002e003da010b81c034828425413421445a9035109e5130140b2150300c0c40700708040e41140300580850b1240c01e2402d84198010b009141003d07026681c400c0f540700b4501c1c1550f00f640000e4001c5100d241c400704c05e214140c008103003140c503507048100555001304103002e40c1c400d51444180105070b190030722885820600e030320b40d400300d4440101100c0300c0e10b048007520141c035810700655003403282c8202203200242c2c1945c1d90301ca810840d030400b101c2d80001244c0c3e00401680c1400640140504032104407180104a210301c1440c01828104041c0400141582c030f058008032112402c025003000811280c1c3d1900e001c2c0c640e2450001c1d5900070070300100c1d14500c03c10101d2117061200148828030b103a450340c0100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228031447 1250 228030197 228030217
    0x211112103602030a0f030c06060605070201090e070e12010f0f02071214030c03060109120b04060f0c170604270203060114010815130606080610020706080109050406060e0705 76
    0xc041140d051601c040141e4680000940542c004407070800403031010303029202a20301c24545000881000c0d81d503442a90041e41c04180400c41c0821104215a01310041c000a490140c502c540d051a01b000010030035a60b9071003460040006410000c0004002c0d0000d0442c400941d006002002116075010020344c4900c4003900d008010403100031980e4825a600300c00c40d840724100d182952036040700b100b43c0764001340100d4188003030851300080c3c1101c4429100380460140700042d41e1440c080c109981614031030640c0b0418580390405070241a50010121641884a11011566681e500011500070200d00a48a5520740c680c200ca118003903207aa00407112510940607150b02c0d0344d850300da2081400f0025032903030100d244480000c03e042c002403030042004200a0602017100c0d92110030904484440d001000043c1110042084c1c40c00c100301c80601142440c801000031601c0e114005100c801d06004101c040c0740c40b100420f082c0811a0030050141803013080344842404c03c4200a8032551104043d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228032697 1250 228031447 228031511
    0xc0f0a02180405061b070c06020f010b09060a0e0a0b040e0a0c0803090f0f011e02010e07050a0509041502040305070e01030b060d0519020103020c0102120121111210 72
    0x18515180081e4014003032644180140429120900164034100482d520f489007071605028207008680c0107419000180b00d00c1e00a00f002c1c9241d94038542c02d440d0111405070040c50007d082c040b00303880702c1100a00b11035465400c08207680350070459001904481c070003164460704246c6000e0569501280d8400c60034440c1e20b83e56051542d81a02d6030f1240034071541e050340320615200d0b0320342505240d0075082c0b001005141c1219a44480401c01000302e140030300000050390f46c1c01c0001d00b1440e00300f101c80081d1604032920b9003c1468400000c15448005000500142c4c5502d4008640080e83c0c05541c05190300c041921105078850800000d1210309200c15201c8420301e401052846c01e180c88654882c0350000d024240600510030901c01441030030404904241e42002071070170380a000e1014202e10020f040e90020700d5403511254490070694101b6540464010030001000a2003007211402402c1c41500d80403020200d101001d41022407018164202c54203011301094030030040040c401c8124412101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228033947 1250 228032697 228032719
    0x4170d020d02010605210307020d0303051504020705060c0a1b060c09090b030a1101090f081b0102060c03370606020d09211b060e09070309030f0806060c0f0a02 70
    0x490a0b01c8284c4605c0f50819042e120480035440b402d00d040307404488440807645442000c0c3d011940350704030b4010980010b81e8881c1400026050b243c00215000d20444055060030310710b0320f6035510384501a0a101c040000001c111102071f020f0040c003401c1c1810703880780c0c8079510000e080140180000ca000300b00082c195980101e110b807518480c0700f64009000d801004a00d02d035660b05116007050102c3d140c144550a40c0c0000c2041581d15240080c4c22442c018000c0e07062107400d007031141d101c000c0f00c00e41550401c83c10440208442000d032a0700c0705400c8a6002d0194200b9004403400c1410415007600c02c00380d800c00340c550030854000008441c501d40c222aa400c00c0f1900450b1071924500502e880004a82c502c00c40324518551884200c82c0950030b8600f626414000c020707803501e480e62249000c40d5414100c0c2406142170a845540b218403402c00f8441c007107882d50001c0a80018061103824003a0101c042007454982006176140c408400c421609048001b600490f569540440c0c22072180b0102d1340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228035197 1250 228033947 228033973
    0x60a0506090f0115120b10020c040507080708040f0f0b151503010f060302131d010602161a03270109021c0c05060c1203040c03140106080d120204170d02 67
    0x101c2181295080094644802c003013080840d0242202130020310b40340d403107040c1001c49076100382c3c0d90030307066105400a000d0a600001408283e0b240102900140b0a07054100844a504158843d5000d644460124004841490005840000032001401c03c802006c10880b0b688200f088401400c48112182e4804400030599401684000d020300956506d041208000841c026009440f41c003002d14521451192254140d20064081d0182032525000d600010001c0d10340500070021000380b08041c403620507080c00d0080b6001c00d85c1e90110410b42c0000400502c0d198010314882e24040300700050700f406a54a9807423580038180f2400c00780d00c01c4840c2c0c07449a0200003c070441001c034a03480012400454540001c1100c40d41100c0d49c12190303402842548420100b160300290300c0386100782018503100c1c0c114240078101e170120001e095032582c507200c0e060261142c00510490409071a19094035420b020140c0880a40280da02c54414010440c1441c1c404010102c2c400742d0040b0a030f0301315030400c2c080f05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228036447 1250 228035197 228035221
    0x30f0f05010b0a1a1803030c0307030f020c0109030807150e01020c010b011e030b030319120501080a05101a06070503040602060903120408070201050c060a050103061d0709091103060a050609 83
    0x2210f0490b0910a5403484a51007940c00003170545110101007050306260034501003030450780408519a259040001e080c400c16800503540d400c0645144010082c091a2000180545405010190104d0b0700424200100412081d03900041d80c010301c014003074040d44900c00d074040d40105152845030b50a0201c400d034154030555618074054407401c5039101e4900c2c034074400d070b00925850301c1c265094001040384050a072003441c503180060280d07544000481d05e400c1401e204607001a08541499042200e600000c681c0005440ca18101c8466002805a441004504003400c8130185030703801500116005050000c00300180c0704480b155004d4814640c1c5000e442a100d1007202c2134030f1280840180804d001c607800401a014551040c1002481d001c3d09151091030f1202c2107541080c45500d0313000500402425003e52a0340c140400b1136203a0340342010303500b203845070024020b00c1d0005584070030b0751060161004200e01c41c0d4a001c1c040e5802800d10031308440180030111182070080d8010004101207003806 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228037697 1250 228036447 228036449
    0xb09031201090c031d0304031b120b07030609060b070210080108060a050604020f030a05060312030c0406180308040803071e0807080306010315060908010e0106060206071107030f0f05010b0a 83
    0xd01101452a802d04100000818607243c046042590310412011066155400100100c0381640110380b25481d614105411916580c4641541d154092041040040b800403070142194024841519a0358541084006050503801400c0301740c200003000039030411050042590700d00944011051084000007912220310a2041c00010b911020000310954a5540440d03088a4010009481d0541c00304010301107401c25030701905803543c0c6105002c00b52804100e56540c20036801d18a030300b10314003090102203d00441c072502082c0480c3d0018202d944880b05c42c540051540501c6850300c03203469403001f9503250454281183c0c580d813250341c840b491062603910844180e61201949280c0026666401c4941e0401342100d41816111451400c0ba80f020690140151000d43d4070700c40c000740741190303003400d4443d031015040003a40b6254042c03188981c0814202e0340100b16040030ac0880d80184126031a02203d5440070700f10114155600d4100060741c0b90011403207019000901c43c201d419001c200c01c10340d903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228038947 1250 228037697 228037717
    0xc0c14060405060d06030206030c04150e01120e0708011409070f030b15040e0604112821080f07140d020c010e0d021f031b0c0213020913090b0903 64
    0xd0204002e02d180081c003d00d28040100c1c40840d01c60f42d02d41c042a03880d001641c1c0202c174103d010a00340802d650910300598652203903e080402415a00300182154400864213030032035841d202e40c0c0d80341c04000c2046500810f030f0000204119005610042a11002542d040020b80620100003464021811020064980040180c1e11980b41c01c1188452100300311100c907040b5480c2e14000d00344170018070a03184190300681c0980808000b1404005404043c200660310901140c1445003881d540311204000703488803800385911100d03600003c0308011001d0320006050f10000a1080c4030600c4d10005030040c280300b800010b42a4000542107900d58001c07850000c01a448001d80c492190b2080e01e851071080800340c2005404080c5070003203a460403407000224140001d100110601c43d62500c42c00c02d0895280c181e454042400c0071000f440705c118440c01a10441c51580484c00b900c60943c100d48001400401c031030300114080b03000c40b018100f00d030307815224450a000040d50440c004003c503151000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228040197 1250 228038947 228038959
    0x15070f030f0f090b090c01050f090402030901270b011a0315010e03030a1d04060609030605060a0e0f060907020102041206150816140a05060f1e03070c0c14 68
    0x14404011001000952503684039942c840070895010441c80c0b203495800c1d8050000e030000b6141841002d0f00c3d114080309400d042200411410380048290750076601540c008460241e070766200c141da81c80c09006501503200948803180394481140000302c0c08207416a108940381c0c02282c0c1c0e1040420840c3c41e603400b849010032030070800140e5640c00380100712240c800504009000c1d001400100b899608a40d100b00089541465400c03100960401d400184040858040c8206c0e800c00c140100900702611004003400c2d2a04003241059403003040090150030064007140309464450b010764500201540d080380955003507001714144c01c0c4180215001d6801802030380d8440003044c0c1c2e440c1c000304001030912010101d100d00105480d01e050068455805032001c0d042d41c01420002d94a81000590b0442c51107034900301c85c1006662115070a40c3d002c4c185001030144c40b40b4204807014070141e11704c4160a4142070000810040641054844075418000c03218402559100c5106441c0301c0c190b0071380ca5034021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228041447 1250 228040197 228040217
    0x1e030f0a090f02010e0d06110912012a03090f0605012c0c07080408030a020a050d090503070e090307060903030e0115050603041202070b040305030712020c0d0611041806081507 77
    0x250161580d20b501401c00b0307260428003071054640c1000c23503484182144454400045031981450301e150f80f2241522a03400800505510790601004038a040380c080321000d41510400015074029800f00c43c0158011101c8140d94900780b5107800144001d0080180c0a441040c045072254141c0983e010942d00e2010342861301c0c0c50744540f01d205034101d00f00c100e541c000200404100b51409001a0000035416001400d402919180c501d0030038100740000002c02c64440d10401580d6400078894084508480b2905102d45580300d10506501c15980003900c40c0b4101a5034030100b503819400220902100c1c030082040180a0956040310795079486040d601c0881030010038041a5954580c0f19810218012602e940350345185644480d0401c1d8800e6419400c040350704c4060000c1c45d00103502d4038005102400c5981014400031f50600c0e600321000d440969a0680c40a01107240d03022200034008001d05000210118044000540340c41e0042c280319010f18500c52850105908010f8052030705611548080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228042697 1250 228041447 228041449
    0x100606120203090703030e030133080d020c0402090f100c2604050910050a060c0b0c120403110c1507060b030309060a12090c082b0507060504081e030f0a090f02 70
    0x20400100c7e00c40c3d0705568031000356a030240600950700b1401e81d440d01c48100c2d4010020350352864151a4040e200c9504000c1445c000c03e41e0114034902141300407113005032199074030300108448081c840381881d0400310b0100641c8030b45c4d40000128442c58407961a40b5807011030386510b411031045150105011a20500c42400546007140d01c5603807010304185440d04a9580380d00080201c003581d800a00414403841010080c0704c0f508440580c800c0240d01c1d601d1800d0800003110a60794001800581081480d2100e02c000310428000c0c00e07040c10004010045032011800c10103442c0e4440181100c1071494280c0315020740c1404820341e8554400141030307a09110440c0f60a60f880c0501501c2480c0080d900c01c03d03407001820007106000a00704542c010719006401c0c2c400c00c40483c510341d4088000d1b10030b007801d1102240e880021240340a51001c0b0200b42d0fa00d69240c410818081c140c01c40c4290508601502d607000442d1020b544580c1d5804c4095420352950030014040360200702c0080d00314800c0c44024005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228043947 1250 228042697 228042707
    0x280209011d2704060b040903080115020703080a09060207081c1202090d080315010c0b070f020c030f012003010e010911120903040614130306150810060612020309070303 74
    0x1003070030140040c5154440010b403401041070700340724404181000c0c024001400710604c52442c1203141500c003003040e100640c401400350781052182e0481030582415080781d0510a12840c00115440800682c4030301181c034010700411440d0107108011f01c01d1260000302003600090040841c8044144030b200d180c1c05000448000c0007030002440156001c10100c580ca0b00d603242003602140c054281551a41040381030f1080b0407481c81d02d1a41001103009012010892214607140c200001e400e01580391681548240e08010021034007650600541519002030751064111945080e548056035010180d1070300340e0016400280a140c40e54584000144070381d43ca04c0e4401c0a20800380f011a13800c1c08504034070641100340840b0505026007003c0f0341003015a81010081c4940545081d402d81408032842e55000c52007000c0c400a0103d946804900d8000621540d20201a203500c405466283c08400c0120018100714441c0350001081c51140410300c01040c820703203000704c1340800078102c024650340f41110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228045197 1250 228043947 228043997
    0x1104020702011803080306040f090506010605031e090309040615051c060b03040f020306061210090212030406020601080c011b030e0303160b180105130b090703060528020901 76
    0x418000030500220311002840030700c3d001144121481a502d02d17104081c04240c0e6105002d100d00a0304040d89640040c401003200c9056034079074074026450b40d507049040f840800080c040c00407640c070703044280403003010044020070700940c00f9130301840459a60070b440f0455034074601146000910602a0006ca00c03043d41203030150314100c80002c15220744074100403401d0307030055404886003108a00c002085003010b00034141c1c004401c40750750b81c01020031500c05480d819440035001400d6520340c1d894085580d01c0c03920741d18508495085030b80f91900c619019580301401c4c080d901d0a41709100c1422010341c401d010314079006d880500c01050110169509407a081c46100105034140002e201c50f0740519000807600361550f000b4072010805051580b60381102ea492034044441c542d0520b4100114007a00c4103165480a602c024800855510b01001c1801d0a4207078000078a21820b00c1e007884141d44901c0c496441e044000c001503d84107005813980c03070403403040b052a9400301d50600400e0300030400c0105100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228046447 1250 228045197 228045199
    0x30512030703091e0203010b010509010504030f1a13111912060f050c040f150c170d050a05160c03140d090f0f0c0b03010e01090f0e0f0d1101091104020702 68
    0x7160710303d07443d034950840c80421055076450680030168982586824051085403400030b0900d54503140c0c030324000805503c1507000191030700b032441c2503450812091203012003100a43c44a4080903080c107400144c000006600305940e001d03140301814a841c945030b0b0701c41d0b9010320322140500c1304a241042e10b07004201e40c101c0503100d09560712000804c0b01c0305400b955100b9800c0d03030ec25a1f80d850401c1c85120000a243d00110b0014512095a4952540190201c1492070700301092144030114403c00e413160303209641080da0543e040105020082590340c101900403e07010110580004101508480441e406000603000071030b5581080030880d10b0743c0c000d00051035140c034045000400ca0700c43c00b22000341c0b118110746c00200a12380388148840c041c400e1025040303064071180b55514200440360130803418020745001a0341e40309080b420000903400403001e4112402654581104000460740b504400001c040100355003070b40172910701006100340d0340b21550128814140103119001c0c08025044082e0032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228047697 1250 228046447 228046451
    0xb0408030403200d14010e0102090d0f0c0810060906080a050d180305030c031b0607050d02090a05041406100509010503040f030e060301171b01050702090c160501050609060109030512030703 83
    0x60360b03d61034001c0310b2281e003401142074040c1094900045400c43e4000c0c440c1c061640d105101c0144a60394100c03500003501e8200102c0d206801c0d00d420200000290741e030000f07006120f03844601c2d0705840c49421800403518411010051590340b100000d80710004140001c0968005006c070401280c0128046418011030b00f0401c10300a89945d1401d2440c1e100841e0b0301555400800e040b4141c4c41d06019056001040c480941000e003000400a015400b841008050464000c24043e00e280c072510403030001032400420901c00101356042c2d400001c0070a460140c010309456042071040e84c010001c0f24141075041e0340d01407a507075464440000b500190700d011001c0051102004e40c0780c0d6034103c0610b0103005500c0c9819080e0b24019404c624000490440c1004080e1400c00e0641c0c5a0704042600c22498058078440c203142d41d4050034620340c1c412999950391902c0441c4000041c0901544035510942c2c3c1500e0143e181c0d108c40c40191000415844020280d500c5488410300805916020b035030090324600340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228048947 1250 228047697 228047753
    0x3200702130b1c0210030606050d0c02030d060312032d0e0106031703070206090a03080117010603060f0608160e041e05061e10140d150203010605040e010b0408030403 73
    0x251900f0301040381c00c01900d1140142405601e4110a08101c06031a41020001d051405501504501074020a0709032140e4a0101103c643d00a004440d1000034900040180c691203141c00c180c005501c240c03460010b840c0200480b0014017040e02d400d00c0c00f00003082a0302001070a080c410240903040d446070840d5494180000001b101c8405040103a0040c08155480380f038a103500070300d00900140b41c0c480662101c204000866002110031b81996203101d41e603501c40c00720362402405000d0b254002480f85150814201e2149001d610010582e00c080d01501c1d1900f03440106d6205901c02406649000101c2e4402319002540c86c0c9180d05840824604241d0100d441d5110a8100b074421a6a0703d14182c0c00c0d0b08041c10303604054022a48845203050752401e440c1400c0c0d40c0c0501d0a000040517000e00c0d0300f40d54600078001ca5000245181c40c802d0400c1d540d80d070b1a00c0f00203045400c544146a400e999203c000b00f4850b017404140c0e0b042d204038900541c1010324548600b41d1104480700d003400885d0300082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228050197 1250 228048947 228048949
    0x2e2301140304030c05060c070210050711100302041d010b0a030c1709060105010806010c0b06120a0803010f06080c0f160201140d06050306090c011b0302031c050703200702130b 77
    0x1841c07182d402038407401d000d240c413400c005080070001011007405050800482d00140d4440d03821702c904072030600c0c0c0640c444030980740655441c6041d640c0145c2c0105c40c0c4c2e6a00e24019410340081055440c0440ca03902040f100c190189203400c400e0080d204454400c0c804803600e03920a5001e48011340203860a005c41e100076503091140c1c0c0310152803030106a00a00c005000715601701c1140d40d000003007841d14039554445a1a54601b801c0c01130911486041c03c6c140d41c0c08900d40411484440c1d03508008400d07078035651a0045942e14065204013004034001c88005100004900c0584030303100843c1c0e11061500d0140f241110403038950007030480c10310044000a0110000700d801070305999500c17500000703c1a0a1108140c034014000740183c00300c1d400320814041c00c2e64444606a01410b0340111080c0c0103190340340c01e030f00b1030144035000c040b0004030003043c01104642e60881400381d0b03603680f42044210200016121a1502c040d0070034940030301008240d00604101c00c2c0c68505611014001030301040c098 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228051447 1250 228050197 228050237
    0x20c0f0c100915090b0708040e070c02181005060a08040203071401051c020f040b0706060927080708070302060712020301030b06090601020a05010e01020406030f02180d0503040306052e2301 83
    0x91090747ca90a0105040c0078856040110036082600c41c103050511002c9030340091460f40d69407155904070401500820314880104028001130000102403540b280030b590700041c452070b0103c1d030903403013841a2400043d4050f04642c41c0b401412060792602d141c840c03000c0c0e0703884c070085102c0800b24144e039080000e00c500d081140c2c040e00240888802030355541c0c0040c140700040d00c42c140c000c040018a03181044150002d86961100a80c0c628100c1906031001c50804034198042c0c2071002d0f180700e030001100010550f0115401d03110302d9454455861401a48203400c049000c24000204400c0b40340c0c0100b2210b180041c00c0741da20070070500c12104071482c03643d12182911241c0100320116034022a06201658047c05408070500840504604103984400c8802c0716140c540002c6000b41c400304500000d210081c401c44000c0d58200d4002d019600305801ca800d820365501403c00c454070300c600400029440c645822000300c80003a00000585400c110003440001107882c151410b02c00101c0d0a148060404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228052697 1250 228051447 228051457
    0x30d051813060303030e16060f18030c060206010608092107050d020d14120c072d0b0606070c0506031f0b09100c0b0c1c020c0f0c100915090b 62
    0x1e0394011920501c1c40c0340140590b035100c503140d01642c12800c07094420825620485045031a41e1605010078401680d054032052440d0104903401c504d505008800d1080d08071041e07046910b80c1c0d08942003680c0e0740c002152107002c19038001d54240c112420606960664921030f80c404038a90140030314009055613000e03c0c144a801141d00540c2000a01c040305982004941d81903c811118140c03038507808480c82118183e00500c0040412030208a00050002d920780000b070558052600441c1400242012a030702c03a0895800c072140b5401a0010f41c041c00c00400751007441c0e0b4003401d4074103114141800c10101c3c0c3c000a012007041c0171515009024500b22274a003000903e0001c058664502010051003a031601016801c8180000c21100ba0001210311214075030203950106201e0702e0303610002c10301e1691500759031041c0116002280c03c070300400f00401e1440d03503504480c003215041004e00c0140408946c03545003d030040fa11001d410415607000d0560f80304a020341d0b107000b08009441e58041c13010340d081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228053947 1250 228052697 228052729
    0x305090f0f0423100509042012060a11040302130507050f0a030b0307091103010e040503040b0d140a0513060513021906090b0415050702030c030102031e0c0405030d0518 74
    0x4143e00d441407448032140d51908100303803e0100982c9810900818003d5101a100030021260203945400d807071541182c45200003c020542c000c070140b0104410b41d41e03082034600c2140d0602e403a4ae0300d104003640004130f4044035405080340000421904815005103030041190052201c1043700104900c90030b0010502c0a0050301c0c00140e035803007103052615021140d0402d0341d00500d0404646542032801058a0456445c0c3e900c0d1000e03652145407450035800f0301d03030001103064004902082040d515401c040c0b60308820000c4542d25a4800303041400790f42007620750682c90741d2002d184c1004144550440396010303c4080d2591a83c80256000c0b0300b29441c8450360113241c801c83c0700d046c400950700080310700003007202030201c3d41402d00740203254500000c0c03626034105002e130018000341103450501c440b00c09010018000c44d182c1c540102c006016824240c484501c040203880042e503070b20308400c280c1c0d0a07100064001e10b20b0100c42c403800d5036680d201c9001c61001c91103c900110300c40d5945a01d51441181d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228055197 1250 228053947 228053981
    0x1009150509090a06050a020f03061909050708010504051b04050607060b0a0303051e120114040f0f050603010c0c0c06030203090f19020907081b0d020408070803070201080c03040305090f0f04 83
    0x3d460a0050451710302a0a0f109800d00401510a00c00205400d0f01e8118404407814101380c0070400c215202c1003680d500c042d480d13504280411101c0d9401203c2c1604075203080d5418451555801010351041881c4130810170200c40a00045c4034a05280c0040c105091061000081d440e811800103107010b00c040c5e10487c006000041c90700541c02900f0802200c046268041c00d00707120340d00d0b141c44401401405042d260300b4001140b000c1c240c0c1e07103402c28066444004420880700352410b05880290804540c00d41c040d40c2400f0794500b4980c410594441080e4000741c10702456410300e101140a51305c064004d40c0b2922072100d440d44050800d0000141c448030000020213034001ca88144400000000c058a0521005c0c2d000c1100350450242e240c1100b03003130324403015a513040076003400c40203018542080185110300c0034041201000040140300a90003602c44c0e000540d6441c00300c0400d844104d80044c0050000d12450781c45050a54080328100001844481c1451f141d8010408403000040a00c2c007080f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228056447 1250 228055197 228055213
    0xe12030714030906040f230f0c100e120a05030d0c080105040c0c0308060303130303090503010509011e020d0b061c0b030705010c151103070f090509100915050909 71
    0x290852107240d03207103044a020a0a520b0500b60081c0c450303500a0001c0d2040c2400c504900800c11607800410306519440501508000a085030b01ea646203004401c07400e82c851103402c02414500380c601e404180e801a510100000800c1e018000d00107070010b09a0f20520506d461040011014005003407008404c4070002205042c03410018105401a070016000e1458040c080809640c0002070071102901400d0039045a203540e03012905d1407141e030854488001c803811000c401c240c1d0121040040710000c5009002d0368407410521401c8480c2403087d84003042e440d15000b28101115000b91030000c0c0c0d004000a02c0401800c040380155008003010141c02c42d0391700d20403400040911442c0050352094004207076207410070303002801d402403144019110343c4400c21303000c45012035134111b44070000004420303a85031700741110080c00400c44484800045800c428010900d8108213280c00d216881c0b1041d081051458003060600138210101d02c0d001d150743d881380200d5940c5800e541c40340a0544000146050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228057553 1106 228056447 228056461
    0xb03061c080a030207030e0a0833070905010f090b1e04030c061701080f060c0c010b19090c0221030712050a091202030a090311040e1203 60
    0x1e0100000c03601015680740d0050041035120303440e40c02131a40350b5020072580051600940c0940d5100c900c40040329511032441c002c100341140b030482540480407500a40c0707820100e41d01c402060701c3c20007c02855a0045030000030080c5031034662104c07410b181207150a07103e111003c004169241e405110f43d0039500303080f03500640c1d0041c11140082c0d0766200c0503105d08641d44180011032580c1e00002640f0002250482c40b91524102400b91540c80728100c0160750000da0311084c07030350340e220403007103281e02d0f2b200b22144130710310382e0680e40750a62810420106460a469100c41150894403107180c00c000c480d5501c1d02243d070308184094481c2c0c2d48540413518141d40300010281d41d82003409100766134003a54032100307046000d00840c0b40e00954001050765244a030400000010300549810404104c0544400e003200c0c0c0010700110740301007020380852900e00c81c981407081c8010004140500c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 227877697 228057553 := by
  have h0 := BRFrame.cov_init 227877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 227877697 ≤ n) (h2 : n < 228057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
