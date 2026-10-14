-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1678
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:11:22.815913+00:00
-- url     : https://prove2.me/submissions/85bd947a-72fe-4d7b-a326-07a8f12f035b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301618705 ≤ n < 301798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301619955 1250 301618705 301618729
    0x604260a1e031404060513140307030f11040207050f060a0b090a0e01060b0c030c120f030f13020301140f091501090e0a02040f020405100c05031209031c061d15 70
    0x3e1001a10348140b02040340e10281c0301604094440964801090841d0010b083c081e5010002d00501c148001d01b06440c00304800c000c913584803040c00c1210205150014881041c07680c0b0750f420034404224603007400000148804a01501400d5440544030510b4190030b460804040503040300c1054082115550a0303482080054081c000000e585512a07400c4d0f5421b50001d00014225400803540c114880e100340581c420440312050500c3c60102c004160600b54000200310100c42c500c110300140e18612024240c0c124181d000707000f0480d100700411003280491098072054844016800012028a07000071650031030701b503641400703000742c0c645140407014001c0d07000c58003500e000c0d100103000140c80e10300900880244645015844508081c188003d083c20700414404201140c0301d041c1c007080e0044116a0030312405504d8910b1543e4040440e855441102958a1101c02c00400504020100d920110a986683c0c46022600d01c0a02c405880d074181921040241c941682c14051140b030517005402e8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301621205 1250 301619955 301619957
    0x405061305030909010f050a0609150c080409050c030414010902010215060d021504030506060a0b190302040308030a1a0102010c1d120a0309061407031706010e0604260a1e03 76
    0x450803a00d100821340c540c6080c1c1c00b102c8682543c50b0148024601032400d20094441807500e40e400d689400c3d5070f5103071107029030914424400c07209014010300c00140200d03009449048010b00c09030500c055100000e90040f82c0c151a8840166180664298180242c2d8004d0360140c3c01031200f40f480f01c3c6034503180340f0090446a48050803c07d4000161214031500b940a030a036050540c42c0c6241d403e095003030a00041801e840f500704114144503105203071081c0c4000b01c1c000c03078030b803501a000c2139002e074000c0c4500e40001d800318801008000d0200c080e81c00c51560007d90300170b00b90310411030100580c241c4510302400c1000c0307820341544080c032714015490a01102030062680e4010204005810f05220480200f60005034041c98240181604030a0f0a10b001903010109032804005440042007052b0390921201c61040c22008074030a03a1040d0300305c94580c040184102e6880e0307a00e0a0781020b9106500840807400308000d00f14400c290701094008025400c07503c0750181c1c0b40c5441e103240b40f031030490b40218 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301622455 1250 301621205 301621207
    0x20c0307090c08070e0a08070e06100e010507080a0e04110c0d0e0f130f0c1709030a170603010b04020f1806030c070807060905060403091d0103030905010f050912071805040506130503 80
    0x38210010040300d0012700d8640841c90103400c003982441011807079145030380117103c6c030382030b120105984c0b0004450a07241c008e0341c0c00b0b031290750304001100d10341c0700744150380e80c400d007000703008500b035410388004042c188244400c5550b10140300c035040d034013000d41010f442c3c1d00651142101956017489200c00207910000080004c4091280c503074141181c1c0442c0200700000c150346420a900c11100000c641c00000340802075050044c41100100794000c58003c030440581c21201144413078600f500302402d40310004005540340d840c0301a50700066005840301c010b00c000c01c110741803814109142124051000080030503d4400b440d102c3c6101e5501c14a0b0844170075070380303581003004075800340f16031030065101c0e030340d602c19240c603200a14116501c0701c65090b0303038503040100400000750006080812a88207003030070403a17a042007606946501584142c0d580081c2c0210340203034161004a101815900e03904c1c40c00314020365403805103040301d0b808c8400138034507404040807076421114543c81c003065601c600116 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301623705 1250 301622455 301622459
    0xb01050a030c090b0a03090506071d040c0216180b121005060d080c070611060609040201030b0109080709050901152d03050a030207030b0a02070209040f060615020c0307090c08070e0a 80
    0x1501c00359001541715000039580361050001c01009000310380c0c11100c98500300341041c402100d1607242114005107288103a90b28211a40d00034024440801d42e0b1003002c0392a4080c5d42d450004140c5062007007802003017a8a4000d42c920b0340d207085c0301101f4030030704271300000c0c002400522800c10040001038602da42c08180e4040c84000034142d500200460b090740030103044107501d800406001081155000c000542203442000607036294100700a81c8940c0910b000300e8110500300060b03a01c1e01c0d064100c05041e004030031001c501c0307203810b810141c000d80d12640200240048006e98140e50120f6010703601c0b00d1111003c04011041d40c000505420300c0d98000030b55541a80c030b0b526113181c2314000c0c0d0214056007100c20100280007154000f03a0f4403841515080d8500746035940024450070008000801c03000e180e2603854107000080d48010003600c0c1007040442940c015000c041d540e1000d0f07040d00c5210380703d000d8011030040150700844204195985500b002c94503000400d0b02e168025281d078a801110700c41c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301624955 1250 301623705 301623719
    0x12051203070c12030506010509090a0f0f1a06031b3004050d090b0406080903390304031a040203100f0207060b03070506030c0d060302030726010b01050a030c09 70
    0x103500403940d40d251001d02c040c0c10715080d000d00340c008a02800b410f141c10200055660040c0440d80d41000c02c40304221640d892402c030b071000703100440f01d5030b0038070340340c01840c10880c07540b58003482e403a220b2050560702c010920380c200403c2c0d100880e0741026010000702d04603a807410381c10140c0303210b4603070062000da5564020800e50003060102181044200c00d0000e1006101c018001904980c105103020000720b4140031007541d041c4601d00c100c070100141c5400090a0080038015500d00f061004034149601458440017000d030304101c9440c0a135500d145801d0040d10000200f180e0440303078400009042030341615041c0340aa43d00500c1640c043c0103502011900452622030494502c105150068455415082400841c1da10a620324040c0e880044240540eaa071030b01039903446642c107100b00303544400e10660a4003601080e0700081d014481c055004c030350400340030502e0303407008200803000c0d5284038401e04075030a0310b0714400c1c16400300d1001c101c010041486600402c003c000d2500300721080030354440d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301626205 1250 301624955 301624957
    0x1201060302100804112d01020d020c0f031e0c011b020a03020409081303081c0605060904021303050a080d0e012d0908030f04020a0e1009021e03040b2e120512 69
    0x840380a2a1b0b183d00c140002160310038540d03e03030381c1000e02c01042d009030000300103561400103c0d81c4520a804001c1610000d6400b000203100c010180101195510040f0601325030350841520311602242d80a14003110714282540100000d0790020501d800700c41c695024480102a14441941e06203070401c10418402000804030f0015031260103040c0e0ba5803a102d0240404061041003004418140322007004156502c2d030036125010720071140140c0d01c44e104841192016402c1e40000c2c40da000b01d955050a000112020300502d04038040240b1001e0001d644450807107031072000c20880042001c500c524800c03503084840c2003644464000142070500d9880d0158240c01c129044030303245000c08200400c60074426480401004030041c0c613030241c2040901ea2040b000240540340402d940451071108c101e030000c000c041c000c20054096035407403c1604000040e4102103e010204801c032200400700f09518104da940b501442c601d80019060801080000101b00c4110036540c5218401c00f404807040c0e640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301627455 1250 301626205 301626229
    0x402060f180301061208041a2a16031e0305310e07021902060f03011d100b18060405030f0616080712020912011a120106030210080411 59
    0x8440e40301e030303007654040500b0342e202c903002600c021140041d07144c0054486c00656042d80c0c7e0b54034a01000c0801d2085110144c01528440b810b220f00c41d20a0352407400301e0751140c0381c0629031501078400f034180c0d038104242aa1483d1000900401d556241d48400c03900000040751a00c1c401e14080f450b2280c00b614241c81e86003a0303c2c420700101500c1002c0300d40307000e1a540317010080c007030303040e22009500d005400a500c45440e405085e09510762010041c0440d03075440121090318008400301034807035840f1100681150a60910660f4000d00b510200e8003415185111004460b086c544440c13420103100c00f040e02d10345441d500f030383c0c011005120218071564288500e030601c03004c58004140501d00080101c1c10007021001c08424000100c082c42445580151840807800c02c00c1d00c0580d4808600300851001031070302503001c01070b5103414001c80c1d28003400031a40c40c14100460711824401c0e00407200310700301c940600c002503201060070b401c1c0104078003400c0e145620a004000d6510b1080c40c020210f5440080b403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301628705 1250 301627455 301627477
    0x501120b13050a0b010e0910230312120711032208070306140c0a080c0f0c15010f0f140d050a06050c2a0c0909011107060603020306010b030c070b0402060f 68
    0x110160113065a0100211101240c01c841c892090300b8211003102d100c1601c0e000c1c40e40d2841413103091100c0d07802400b00c007800390100901103d0300e5006a1506441c5e42d040800c4c02d00011000c0402b14405174800c40c036841f107054400300a10714204040400c1050f03c0100c000c3c2d041200a0300100240900007403003480c00460143c00c0116503c012003801c0032007840000c152240d0180c003405482c0286a1154180e40d000c1c210300b003041c2c1d4800f408076151210f0b00a98039207000a200e000010b000110608540c18103c1e6468006000815161070801110392004c1c01400300c1511040350811483c50312400b004505030240058900340c80b82c9844c0c03c401c1c0d074411a40c05e0b80c0c0c0080080c82520110421201039091050a048100d524082e410300d2a1520300481f0701603c640741c00c4010550f585402e520040601c0c01c2615180c2e5243c1c0701d450508040c0545110581c13003401040000200b0352082c600b26441080124111460f24214bda0b41521540024200382d8002c2001e004081c100c150901c0200307694441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301629955 1250 301628705 301628711
    0x3050a06020a0e09040807020f060f0d0b010e04020a1403100e070504030c150203070b0a0b12060a0f0c02030a0f0504030803010e09060106050405030d1209081903060f0501120b13050a 80
    0x1240800f60080d0015000980220103040411022904c01c109464003240d0488407441c2002483c00000c1140c0602800c504000100040040041c0560351003486010001c0c1c8806501d5125001080101e001d0b03101400b01050030844007c000c14900001035034801d44200180290b00d840c0c20090009402c04c0b266034011030380009003070083c041550000401002001c00107401410200c0713000b0744034060944014020641c00003c5050081a41c10810748000054101c42d5001e058138001541c0b000b00303440c080c54203032808203950b0000702940181100c6000742c1d00210318000070000300705c48240b1400501000c10038248008800140e202c1c0045009000c40240c04d03006003003606100341080700c1a03000c00140036040000f0082900c0c04502c10441c0840c1c2d00707019a90034005c001080c00380a18101c01480c00f000000e40e41180790310003201d02c8040002e540c080000c0e130382f86d01c28060014114001c0c103000c10001c00b00903025101a400ca180750345006007a4940b18003140801005580080c0d800c2c400413a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301631205 1250 301629955 301629967
    0xa06060b0a030e07051c020d050d0e041b0807210f0204090f0504020a090209030f063d030f0303140702031c0506090a1d1605010e061c0c0903050a0602 66
    0xb5050048a1200034824003510046240c02c0000d00082e10342001d901609440488000030343d610504440320003a0080c0666403588600340300146180f01000d009442075207031200140c09694440011081c91807140c941040c2901c0700320017500d08081c900d9800d640d252500c086940c003110540108540240b24440150301d90b414014a8010348540520700c0104521700000c01c4003580d540182c00007220704120005990b605008046400c014003801d00068034071420050004005c01d00b0300804540e01441020fa10244031a069600a82c020101d1031041c4902c00b0b00a0010403030609000400354803c0c100028000f1a0480078103000030100c1e015809a000441d00f0340100c4aa00d1854400d80003a83d801c000c0e42c81c0420004002d20000381003800740075941c650340600030b50464980700d0b8003c44c60702101d603501070440720300c00c142c80e050040790f00003902409080341c1e41c10004180c4140c01491461a961044140c070380307500a0060a40304000c102e140b12001010401c1403180086582c000c10025940d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301632455 1250 301631205 301631207
    0x5030a031a040c09091505030105010e01061e02060f0705040509040c03260d0f060302150403060b060c060a0b150d1a060415030b06040b0309060714030903040e090a06060b0a 76
    0x103809414058011400c0007503140f45194400d209006171840600001405041c0e0003003a00e80d00e15541000e6019031901e800400c4d04260300e41402d0484122383c0d00c0b95140081070180640302550346000001603404030300444d510584070784042d94028160300e0b12070308203a507450000d0a401000d89094a010b14840000e00c24021810809240407041541c98046e1451225100c0030521071492205030b074079600c500e6010121081d40103c3c0080d43c009221030414450030100007940d91040c40116501403421100655608001b825140d02d107c540c00034025654490b00450050107685510660090303d4043c10500b180400300908240c1d4429000001c423a0449030100214401c3d8240d424031448061000300001510705032604014501c52802285003c010001f10300c1302d000c0d50300109021440072007002203005000484504c42e0b5980c0d680c3c080d0088107841410703403030b11080d81c015403d81c00c104818000c2413021040581c0290341d1804850488445480d038030122001c1b41c02281d0304000008881c030500f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301633705 1250 301632455 301632491
    0x60e030607020610060e0a0f0f06020f0c0109090b04200702010e0f090612011407050903060f010e150a080609030423090f190f050a0c08040c0605031305030a03 70
    0x8071900780010300c107508110080c044140382902c01c00c01008442d8410804503198661254000c2c80b11a0501a145d5201c120010a440e400e005d0440140301c1c500300b0050001c0d00003400d030300d11001a12943e80706800d180c42c1c03002409403071580640107502c504840c0f404034109001c03010680081c0c10382c0e545407842803000401e00c0000101c070070300c590340754980d00c1c0007a69680803a80d04a5001c403407088000382c2a200c142e0140008001841c01e01d1a84010481030580140050031520411400d403400d80d03441c04400c2488050038040c01d00c00140d07c8001882805110010300954180108040c0c260f640c0c80c00c40c02d140003c121070154480e04042020410051120710800010b4142a080c0b00c0a00103100030800003200144094810b500c5000481e20000d0507902c06644c003041803009020714480d01713146a0103400155488007099160443e0188034511804a1034001c42c0d0201c003010849240c244210741580014000c045a41c0030b9900c02400207004000914510505031404a028403401c2001914 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301634955 1250 301633705 301633711
    0x1b0815030102030408121017031225140408061807060521220c03031d0609060708040b04080c0301050105180f250509040e12030a0c05070606060e0306 66
    0x1036030050052200142103601a01c110144120b45040d0950303947d0104400007070207a0040d940b484484840b41c1440d14048000d0042000000c0021383c25140c0150b00c4681c0d00d42d030503440170700108109103001e21031302c551078580580c038064030060306054a4100301c0e401c1a1090310b5003003015169241a4080c200c0500441e00101a641440ca0926000e03035040b01c0402c3c10340318050b28803c4c0d0000007a40200c40c0780541d907182402214010349014807132805100c20b04250100303401040c1859880810702407405844002150064502400d01003a803051218a401040044407101d00a0002003030180880c40900014148040204882a24a000c0c1801c407641a004640602e268815416840010668040d080200781c000003000b0340d1400311f0038071440351038540711481c80c0148946004c0e16501c40302814416208030760400602201d504000d5503a200442c020f81200014000181d10030001d6001c440310081504000c0d203020180d0b51058119051a00024013041120a240805003000c1000c294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301636205 1250 301634955 301634959
    0xf04170d050c06070c0203011104080109060b030c1528020d0e040209090c0310050916080c040518090a05030708040e07140d0f0b0423092803031b0815 66
    0x118010041ca0b00b641c032144003c2c8604280418080c8a03402c64809501ca0602191040701c8151515103c04a06001c2c060000b026540103041091b01c80140c074000c01c1041d18902e00074502a840400805041001d030020110003020000e02880e90000700715031000507103840801e0340507100006074024060103060325025050300a40c414082e040b920f84030409030036085001a98030546035903070708091101d0020710390801a00009840148110820300007202d04001035591250541c0c0c3c0c0d5000348120060003188181540b0583c01c0c4842c900450841d04d01d0354011500d40281c9200c0a05529120320350760111800b11082200040c04102c890f5850224a801c040d441c68501054217070764070074603510b0080c80d150280f0315580d80d00c049180d04281e4818201014040c00138802c1c003d0390321080030201a08640f000e52030100700700045c0032000c045000f141a40342003201d40410b01c0390502c0e2030641288000c046051581d200c91113511030000c1350403001039019554400c0003d203880c1034981200c40f40450721724 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301637455 1250 301636205 301636207
    0x80108060118110c0a0309050f030a050613031107080318010203090d02090a092f0d0503072d050705010f09120206030705090603040302010f0b09090c01080c0f04170d05 74
    0x1020a680100303100c02d49604869000c1000900e12407007032140c0c880e8a002e12124498034034210308050304800c000307003210740031580c028591804005160700d44c0050100180142c000300d0004141c401c2c20540c1c1c550441c001e1400301015440703030107010b240040c160040002a44086224242c00006180c6489000c41c20f02c00f850612160401050110402c2a030081c41a0070220004001c0c00095110650380d68100368910324034a0b020840c001c40d184015851244811840c6003804942843c07041a00d4040d03003c4010362510742c594a03880c7c0e890750182030600c0c038401e070b41c0c803210f0fa0b410424501d49880c50003403028000407490500003400c40d034100d409000c14420302c40010440d801030340e40044007094040c1c40d150741c0c0c0d41c0e55480480b410721682c61216845400441031005040e41544040f440529001c0b0410100f050300c01048007120341120351046940c0041608509944991745144d00b0031800c40c003075414164404a860310350741058004c8840c0c1018441d00c041c0d840002c010301580d21849003001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301638705 1250 301637455 301637459
    0x307080f010f080607120b03010f0902130b1804031b03030c0306080601060212031003081603030b040902060901030c0c1217060d031e0207080a03050703080915060d060b0a030c03030801080601 84
    0x2d84d8440100402102c14881c84003882140900b0a4128004200004008114101400c55804002c01e00300b03c050340114105071801281404a02c2522002000101840740f0f60161741444022020000d00480800081450403081c005641000100540c403a0700e001c504427506040080466007941d2040442e5488180100902030700800d403000c0c2801601610350303699881c4445100c0143e0650b100520001000400704582c041c4001561000c0e4800d541c1400041c0e180810041610b00d0b203d80030354040030420050041e5802940100d50220403402c10b2280760b00951540c04000c0d0f072043d0680040365000b54280300d00d00d28040346a83c0400c1c01c0740c6081541c03540351002404802143d1500100302420306940c0c200600800282004161150858891070903915000304a500814011070110782e45401140a001d000b140760740c048044041040e48076030b07a41c4104002d070b143c07110741070f503095a40340011255512080800d074003650151111401091441c5802003013004141d00c1024280c1040c801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301639955 1250 301638705 301638719
    0x20706020c0c103f1b020303010602070b090d0204110903120f040909020d0b010b0a0905040e0c10050405120601060f110a0b190f050402010e040c120218060307080f010f 74
    0x610900400307650356030749180048800541c10a604e151805030076400d40599600f80c080a034020200c4250003401100340c48401007000d981e280002c1c010040980c1000000784540c4844102a00091030014040d080380c05e0b0940208084503000c0307185041c0340e48000359900b0703941820000514051001d24219107401f0712107003105028000c50060741d1440ea00c5005150a43d80e1383d40001840d42c2c1c0002d403040e40d41d42d4a006400b096845a82e4210200350000000181494680b140740d003580041c81c0680100d001d104100802e241d0000046000c5c010107002c0424541c480b141c4e07491060000780c000745295410040043c04200e02c441a01003040201341c0c500041e40f43c00702d142003843da0f001d400741800f82c49107284202c0c41c6088000c00a501454000f10500d03004440e04034a000d00d000f80ca4803042d1420010a00094541c0c031344c906400325500c0c4c0180442401c1e16401400d140e6021002003542000d103d002a40070361003520400b0015913032005005000ca81c501a803030051094403140a409441c05030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 301641205 1250 301639955 301639967
    0x14090d210507170114010806101103030f04020405100312140c010e0304050a09050c0a210906050612030c0304170102041205061008010b0a05060901200f100614190306020706020c0c10 80
    0xc01e85002710304000e01414892b02441003c6145c0c003505050b2a00c80c54480840c9401e00c5085406a00c180d0a180c04140092250301d001019a83c104c2032400542c4149001922481e4142c9900740201000700305021400d1000e125500180c4402006141e0721807501d8100255807116420110345d540c6442c0a1000580340c40c0200d90700190141013002c540000d0340140108142c1900c45000d5084c2800286403c000301c03548481d10075103041b103044071a00207000c800c0c3c1d03480c0588041580305034800c0100f0300031110b4881d043e52800c0707141000540381603140c0c1c3c0b4060301c130b0f0b0440e541100c1c103602071400d1042d40004046041e0241a100c0002c009094206000076602080c2c3c1c03080901404002540c880281d00c1a103445500001080b044404684004205d41c1c2d50401c180008910b40104202241d00303040c2d070b0141000f201e5031308440d00f001d045882c08200610140700040504184208000000251540082d0010314040c18006844507404540f46082100d020359040c461001100c18881e0350303030400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 301642455 1250 301641205 301641211
    0x614100504060c150f020a03180507120c05060c0c010f030b03030307030f1811010f05090907140c0f0703031b030f0302130803030406090614090d2105071701140108 72
    0x8941603c140803541000c0054a00c110310003428a41010109070308110316400a00c1501c10030340d0304001d856041d0300c140d450b134520040e0040041d00828800c000f102026190001c65500070790b050390f40184c0d59800102c499010f00e00d42549500181c95894896800010828030302c0c3c003508081c0806190b107070000b5203c0c84010604000d040c1e83c2c3c0034841000103186d202c50722041c0c440c00e8181802d1f2860034403d074596841103000d800269120b405041d264811810303201c000c44c0141c00302e5080e132940c4c0010744600c100e202e1440500da1042c0000c401e0010f0401c460301410401e400602031440c1541002000c907102013035038892101e41044444002a448441d000a0002e1842d005860700ba603262242400c4e0703520340c080d44640c4408801c0c002400141d5000c1840184241e1040100514403036203500000c00488588000b0b4103d030300303480c5920740650b1011541a440441c00c100324802d040250084a0065481c1000101400120f4000d01e0110545602500d840f400151110788540002003903d41c0003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 301643705 1250 301642455 301642457
    0x905091605150f0d0e0a0501050a0609020408100b01020327010206011203051218250510090b09012c040e07051003020c0304030b070810050d0308041101140c01061410050406 76
    0x1048907000e40740e6804020b881d954401906c81c1141c6608100c0e019107420344213540c00074504000040c0308042e41c400c44044580750f202401404440005a1700209080070116041d070104101d80d41c1034160b2840340180610b56003c1603d60741241200091030118141c1080b00c41e807803801c4804001c80d4001c001c0e91844420100b08001580d11a0740ea1076030380e03041c4ac0d541c045074030410b40c008004c030795010f07528145003442c12181150b296440b410400e4509040d60b92401280039000140074505102000b0000b450042c1405080c0d242c681003c03c0404083c0b0a0790640482811842e00052500d4011581c14850980007050303030500b02000a07031403101d004401820716a002078908000072040c825100107640182003136196160400001d040920115840650100c005001144600d000c0400d03010309030305a601c03116242c0d00d903641c25600c00c805101c0c080c10700070302802115035003018400074207001c0b2000d0000300300355282100f10f481c3c50a030301202d103124103920107d444505501500350b42c100c80903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 301644955 1250 301643705 301643707
    0xb0612040201090b0406030b01082202010f0c0b150301150f050607051c0c1707052137020606150715061e05011b1103070905091605150f 60
    0x540d10040c0c0c0c4001999100b081394070350108000841c15010b45c00304848440c2a00c800301242d880c2c04541d010b200c102200f80c0c40300140c64602d000554481c00b0442e400401606000e502503c01d6100c003151070808860342c0c0005034401c0342140c454142030049503035055243d0602d80101d070400c1c2244d102d40815000b0f03107009813008500368040c80b2081042542e80e1610146400140c00c69800081c6980c08146060b5000c803506201407900300b00001c01c61315043d4106006d030001c00f903a010000d920740510954248006400c2c45040303101d014420114100503040100000c2510011401800d400e8846021200f90740014042141544480d0109a100003070000c03c1a910340c1d0a00d0410030303110407011003000305458000c011032004400010001044031802d2406601d65488ac011100c00441c900400f440c092016161000036480d84501c8034107030700040075039180ba5250b200c0c0c0780440713404440301403199008480030100000c840b51060064007007a0b501442d41c00035440c1461052250411007920160 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 301646205 1250 301644955 301644961
    0x3300402090a0906180b0903070309051c02090a0f050901090f110103020c1509070b0405061b0f0a06061715180c1f09050306060114130f0b03040b06040b0612 69
    0x2500d600000f011544000100040e4101424054600d40c00720400c8401c41d500001007280268000b041d1080c495040d45c8401c0320a041000b4860020000c010131440f100c3c0d0360101c0f90061b600c006645100da60a00c2d4005110040e501c1a0402d90b000600300d40e280780d140054a001264104001d07001c1c440e000303844103007075809100040b4001c4c0b00700c40c40c96845010b4a41c81d0250801c0c40020203001e8000b200c00c0301c64541e214548070b10244036600c101903114008119100801c07915000d000c6e0104004026280e074a4030103180513040100700c0c00300315207950b918442480f0b00340302c51001c2c0741cac1034010400401b0044c82d514a691100d040107000c1c40c1c80c1d03600390740704055040010010007280c08000b44c2802200c0710415680782c0c09110400b04a40030804441011a480c01c000490350300c5124165658070180080e151703c80c04a902c03104652240402e1520040f901202c10311075480145071405886a0b00d00d8a814400f80241024200a02c00d505042c45c0c02559940d000a81e41303061003000f401001a1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 301647455 1250 301646205 301646221
    0x40c17180a08220f030312140f0603120a03021c0b09130c26151b071112030903070f0e16030b030d030f0c0507080f030c07050304080330040209 63
    0x20140f014000d103d922100c0c00318544180c0d40543e81103d21944540300c3e6581e414a551060701e103c60405408018000001002c02141500c0d05400000140544055145555111000c0d5100d004000c000c60380001d61105410569040345a850819040c20000308690100103140701c00003034441c0488070071402000c401d11904607214401055802c1c07149040d100c20106c0f503c0c0311700c146030340c4c0d0500340500f800c440d0000c00720182d444d101c0c031403600d4400e034140800c2007002659005000242c856000c4004810315644500881107880c15521300216110611001010b10700300f0350b0340003540d046080003820004d9000382c0074030a8100e0a1000c000307041d0b02490004038010443c0c01041d40c2d140c0b0035400b0040500381c00d58489282511001c5050100d80d051201c140c6240c8200000100506030030480860512100c501039604104084446442c0444c551281440c60b0884d03001510715401c0000c0d5203074020b84803640c5000b009803c8c09441c50709035000020403100754004002030702984210000030044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 301648705 1250 301647455 301647487
    0x1a0d11040207080f19080105100e0111070f03080304140d1416020d030801030203060c09010c0204090c0b040602100c080112061a041515031103150f040c17180a08 71
    0x40303500055403180e4a01860b40f105117540e180100109500741d002080a04080c005145030002d96100d800400503104011644c00c2d22080301c0d4403290140751000310b4007060000190340118001d8561503160700700350a113600d040005c0b050401c040c2d84001d20791010550001644140001c040c85083e0300c660325140124440760100c40300039030018030100c29400309038001c5600ca041c0c80c0260103c800759a652485480d19114054000d40803684006501e4014501600140825445040130f041d060390703201d01c407010316081504660003603000040c030004061101d2080c048144507d00d001c200a51404050182200501a02030903942c4c5889040ca00c10285030104c05064002401c20082c0400103069500d80600d10700800c2d0704040d81c85048070351302d4807a000304081d0420700400030346541c41e010b2400c031000f01250340240d0005800c90703181050307507942c1c410500e1060301c07502c58400003c03140c0b0404100c1031000700401d0b10298070984607584e0a50000d070f14203a640e4880003950342e8100e059110541 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 301649955 1250 301648705 301648717
    0xc030c09121b0602030703030b01050406121508150f1302060a03150b03010603090c09112d03040c050f0a0e1605090307080106030302060708010b2703060702011a0d1104020708 77
    0x3100b902c04000903100e64000020709046029540030010302d1b03481401103c062286200344000200301d40310072041d4464561201344038030341c0b8407606402c035951001c9803400c1143d01c0030503400302000c00342040003800c12100d0155029124144001141c800743d8002100c80c040c1d11031540402d541c030750383c1e48403180720104081c025208076040d294407980e4030080100944904101120746c40311019002070f041405000e4407841c4100780c002d031410306074045043c06402115010a131a0340e034000d2824000850002c0065019a004484e103100250030301e000d2001100311045650f020b031000540c100685007421000540108503030a03850302c0702442c041d08071003034011803070b0460f81805055000140031f84d055100e242101e200e40c0039101076507903206042e5044d50b004d200d017038402d803010090011440c03400590340480d991a00c03c0501d2100c00d1002085c94000f044401300d0250b0356845d040d501c0d100c43c00365030b210303540002ca170282c000300312540d18142c451549120f6103000d550046044010040b8510903501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 301651205 1250 301649955 301649993
    0x70609032117040602220501021e120c070905040c0f142803230c09010f060c03030204120b0901050c0708072010020c010f11150a1e0f0c030c0912 64
    0x5180b504c1031b50310070b40404282c4100c60140c400c20b65001030080d91031075003d007040d0780c044c040d105903030b6008800d400540c03082e40003030350300e01900e840030070300000700d00c2658000c030300030031800c94400d04103054135490110a401001c08100116a0243c00b0755442800c1262600c011a200504a401d140c0a0b030b030f0680c40383c00c024040182000d84d4501e441e2425000c400403488801100c0e07066101e46c00340146030000b0700908081642d9220248002400b65604140d0b031807080c0f074010f1800e070b929100c07c40020203100d01100c00529071030511040c0c16090082e15085900402001c0c500091540d64020038850000e0041c00d04602140f5104c040e41e140c42180400100a0035a20071280000c100035103a0380c1d01403200e80030404840c503409a2906c1080722065500060008182c04142040b07030340ba0442e0020101c00e807868a8201c2c1010100c05940810440f5504040110b0b2090a5400ca002954020641032007010310303106000444a03800403007142140c440c00a940c20141d6141017808001106a030020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 301652455 1250 301651205 301651237
    0x3111606060f140f010c0c03030f1b030c020f0609130b0402041208070b07050a090608090f160f050f0901030320160305151b130305070609032117040602 67
    0x80000740344082240c070320401c855402201d0750f4039006480540340341d03201601e55181d247c401d00000e03026035019020f54140c0c0c24074001c0036400f0358800d480d0144160040b030014117000c100f4011800c051208076003942046641d5803c1c0352002022503030701620300d1002d000c2140c584284500549880e4104d4025241e140302c032503810b00d0781e41031107000365000b8003080350320070402000240c1451092040e158048500c0d603c1543c1d042c503052046481d11130140c0a9451405451003000c5824001c0003891030440c0614450044646003405003417803125641d00a6000e00600e0750b1541e000d40d03035042c505054035070504080081d001e1480c903c040d01c150a141207421441202c411440d004120420321044038403540846100c90300401404036104426a108a030b4812090045003c0b0366241d00600703056403c07514030341140c81d0342e41c4420785070051a07404580440c2c641d500078000d002d83c030000c1d0f00891900380000c0070795000120700280620459181c0741d00030000e81c400b05080010390340403600314103d0001c0c00c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 301653705 1250 301652455 301652459
    0x60d110301060810060f0e06031f03150f02030610140d0905060609011d0412170f09210406080705070b0a0e060709050d1403040e0903091003111606060f 67
    0x60100740054440c05803101441a002580c01c1c4144d210703a006d07000955a41c43e10170700a03400d21030f654001901040c2c4043c40500100d103102094450300000711f000d10840c903661410750400c50b084603d1510f103800c2c000e004004100141c2c544139401003248a003407810701802c0d100c3c403004c80321f86c2c010720f4035015100b4140f03400a41840740000c2e501d401400120b0f1403a4207a43d071110107035241d550540e100c00c41d0184100004c0c0114241d14404a290b00642c203084001e502c2c0c6460000c4200310444441440300d98100920450103420010181007a446880300d0200c10400c4107010454000c501c2505e0800c0704941c0014074623403107407040d280d00b954400070044d610f0038506a0368001d03001e07003805d02d580b61065a0014142c584160805c0080b0346000d02020780341c80c49a101e0340c10401d201144000c1501c0200000610324100503440381c4103000d0361010f1500c078640d031820050000d40d02441c7c0800c05040142019030b0100200450307074000040340c10440744015614003400178089907800290500903030000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 301654955 1250 301653705 301653707
    0x41b03060c1e120b06040b070303050f0907060801090b060d0f0203150910090b0d02092a070b160c06020f0405040f201809010605280509060d11030106 66
    0x8404049140c98582c145075044000a80480c807841201c82c50001c0c1c000c0b2a07a20036120203502c040c42556014250510f8191188506070541d40480011000240d6502c104005031400c041002c0e005107151001c0c040151a00200904064041c020b141c103003651071012080650319007085030305403a4020030501c84c044841800f1030080d001203511a0304001c005495000c80e00d410000355220708031104410720220f00345800e140c014020745141c260801800004c202c056500c09240500c101d143e402200701144041a0800c02040610900ca0000c0814012100081c004c0340200c1e03803102412610f0303441510120411a0038131101740024009500c0080c10b0444130300503130000c100340e5000341c80c180109621107043e10200c41c103075801e00d91a140c4840000e03101c80d0900005010803403031000340010595110700060300d46c44082e80083c000c264000307140d2030303100c40054040c1d030504a422900c1c261028110006071080c810b40420500c05c1e000000c40c18110407032a84078148006501509035100d42e11298 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 301656205 1250 301654955 301654961
    0x60103140105070e06040611070b2206020a0506070e030a06150f0501020f0c0603040311060a05011409090a150906050f01092904050c07060207030f08090a1a041b0306 73
    0xa0401038650900e000540c0280c0100c604040a010203841145014a800c204407441c00310840e40c0720035805800800030756250b80d00e01034551a034200280380c081c00305211400244a0300b5600000075500240d401d0008039501180700c990020150070420b8200248a00082c01c00c03c0c5110014010340c601341c803c3d051040040a50742c1a5010b040c01070071200e03103c00042e032796507018280c5041c00b50f1102c400c840072410504041d5411034403a00f415071110145107540390402000b1070b01b13900ca6560303400c01001302501c02c82d01d040c400e04044d0790380d01450411000041d00e1b0001c94501030010054016510030b07002c8a94003802210b50405410405070900c00900c0c40b9143d401c1c8101600e00b1b08202d80c1d040b4507000b0307080c18401398242c18207440794018840184400f60400a011003040300b0103020840224449000400550b8820380d5040d03101c07503582601510300345019100b120aa888017240400085c0c03030b540103c181c50352041c0c05411580da60328119810070b0b081032b444074030f03011070040000801c01c00790 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 301657455 1250 301656205 301656233
    0x12020a090e010e010b0f030304090b150c0d030b0405010b0a03090503160b090601050a1503050403020705040f0b0a0f0b0f090409140f1018030f0c17040305010501050a15110106030203060103 83
    0x4001703100e03a806180811003a54030382c200c51540742e001000100000c0390181e2050000c03240c003610301c5000e5540f402d4044400d80124070f201e4042e400100341c000034a90702d485241c881c4101208c08004a504006900c151401128416414507668086120904c6020415950300c1c0e40341c03840d42d0315043c20615110b03a0064050b40d586900d40f040000103c0d20b45008440030064900190040d81c1011440004801070b0001030001d6080d03003d6250f0102d119101d40c010a9040b0800d0b4501040f080540c50034031408401c00d50000f410700500c40403c0c1b00101e184000c58440d100c00580c1103481d8528940007030020100070701e00401d8001ca124640803003040204900700b03400b0103801500c0c00c0d81c0001068005032591030803030340c07003079000d140840b00000d005000c120f01c0c80d461842d2030042a210381d03941c0f03454280c000c010b0701d030900c80220b000c1041040034014103002d050242c40c0c1c40e151030329207284800781d032500150000500440c2c19074076180f00005d501035802150010704859070795943c1c0c1860111101c140b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 301658705 1250 301657455 301657481
    0xb0414120303040b070f0905100e031902090118060b0c07060206100806040308070309051515041506030209060c100b13050403210e010f0605010f14030112020a090e01 73
    0x10300685040500401501c1c425500f161043d5195a1400c45c116041e800c440507500c01e20100f1600440c0549403c0030211a061450300d941081068060405103010400783d80320700b5090f9400400801601d800b0662411542c0e21600002550310401c841405000e05400c00c3d01c29803000b042c0c0d0344644000103000d0301111400d40a46050b9103c400c0f08005040590160000b65031100c40483e000034070a6944540c032a005140001703003020b0590b0f0340c60801000e400d010b0030400c5540d060000d1548814185400c0e007204a84c100401d548064820320a0685032103100289030707002c00c0a4516440e00700880e0622248481a1105143c466040303800a1a070000c09a016914503404000103201900c078940c0103a4058841c3d88101c8428001c0322401808822940b100c25190032510118034001d0064400705080b0318404200141800001401c6440300c5402c241000380007400c048444860b4403c8905640700c09004400850300380c00801c021581580c0302c40c68180c580b1150601c1000194807820305840c203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 301659955 1250 301658705 301658719
    0x507030b0c0705120706021204050a03020c060406020714040e0a0c030b010509091507030e0a03080603060702011104090b030313030b10080718050a0b091e0c0403120c0c0b0414 77
    0x1c0301e4030144280034494004045601210f036540c0d01441c50400f41c078038103100310409480d215800701c5440071140c050340c0888003544080640010143c05111a00f803c0c407080d144c09060a2a0000095685c1e210b4480c4100e0307092188201d0342c2e00e450365042500315021ba0011a4044625460312038000822444107031884800400046000d140c080c1e80d19001300f0041000f0088440c60b110401c210381409040c900a041c5d4540501a031840140091007816000351a40480c9190020606040420041000003113901d403140ca08018a080c5080d0350a03601800d40001d40010303c9030102c0c4c91481480c491451410044130004100012010107900c5080b141441984545e0b403030400c00d0390f40802d80580c1c60300c0401441900380361401644040d41c451651003000c0b808e03403405004a1b02c2040f00340c034001d00100e0740070340c080030020245d04010b401c020440401450301e0b155894000d891004188001d0402c0501051041030012500c0104013507d2018042680d942e65004c031000c05402e5070480b03a0080e09 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 301661205 1250 301659955 301659961
    0x30e0c0d080406140a171512010c0201050604090f0f061401120201180302010f1101060f0608040302070e0106050f0307030b030724021906111207020a03170624040902070507030b 78
    0x3150002e4840450703035900c80c21b40e280b941c0c111440b21144010441c2c104201200744120b100e0382d841c40da000107038a118000254040103100c000b070a68400501180c040c50030000d203a00001c015050143d0f8441d00012800c0200307815140900241c0342113902c032840c0710160300011440f02000395200040d070340300743c03500148449a12040480b101c15888003034003203496006101134640c004c41080b82c0c0d032650080002011503c074200c540120310b95420000000794070000308802c00d50104036460203002c20300d01d628000e61410030000c0640c4907400f0080f2071603a0100100762020b000b034010b0300e1035000090664001c80d40384d00d40440000d45604120704a05090b1817550640d82c000b08036050201c4102100c1e42410005850300c01c007600c4070b00720392a4880c02c01c11800c0a503505414159009413103580c09002c00100c0390400030078820116844d03030543c0381504140b0045030382d05a5038010102d40601d048a403404441402007440c020341e41702c41000b50000400c40700300324020400d01c058905c200c0702828151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 301662455 1250 301661205 301661237
    0x501060f0806150103050703020418060512030304050309010e0a0504091113143106051b040b0909100b0d02190e0d0b0415060b0c060a05130201030e0c0d080406 70
    0x100b002c1c0c0b49118943d000d488040c0f02c079442500000d90044040c100540b400d0342c0c2c1d5003809403c4180a0099000e10340c1c1d100184094541124500306000c0c2ea400154154141a101c00780c91b40306210701e603410300c010602500b032961a000d170900b0041c0310052003001885441d00b00750340100d16404016106101060b0b45c5502c0d05860712500110b071550103150105aa44c500c003401c00181d21a000ca010082020041e800d44500c1e0907038511601e04c80e940110342e0303081041c0c540040383c051070030804c0034031800d003c14041898120280d40c076a0a04032414541030311801110a003203126078008004c00100007030100807103074080d0010700740901c060344d103005461b403c05001c5405203054103500d40d0200039241414081035848030354507046400740008155064500f0401c6040368a076038428101140042000d0041c1031040c0009603101c0075921052000c0d19000140402c40f085004000341850713070310205041610b100700062400c00300003420700c41b404629070620010541203441a00001010240712901030707 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 301663705 1250 301662455 301662463
    0x18091e0e0a0f0f050610080d0e06030f061201230a050f04121b030e03100504020a090903050702040c030905070f030c140f030709050a0b091501050c031201030501060f08 74
    0x3089644025003214892076039419141e5081410940e04488010052801300d1010300046010300000c018012030f0382e191250050501d02c00c2c03480d58060090b200a070030116100d080860b548882c4408960320340d5a912000140d01205400e00080d035503180c80c0b00200710700102d02c1403a120031861242d490301590b840c01040c09403141200c595801303021150100740025803001c0d0302031010243c0d040015a40d400e044a50080d00c4000b0400ea000414480079680c3e1814180116003000851a00c2440240303400e4000c58980c0c5401e210f481101d540d238007680d20600d0b108109540f82c0703d82c02001030160340b4076100001d0142c01c0440d4250303154042e140000902c00d80307240e020340032254056541c000e51450144601c840081c000012a007101c0c0d1111000040c0e03134281304001c0070340b01d000c000003030b141000c0c08120100d0340424041405a080c120034050b01000c0b43c0d144400c8440c0901e00300b5a0784420081882c110b00032401c011000d28150070000c2304006042d000302c0e06440c0642da07400c8003c2d9845049a035070b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 301664955 1250 301663705 301663721
    0x9020915070f0201180801050907060801170c01050c070f0308090f0108151c0b07030e010617150709120b06031c0f0f02030919090b060903190318091e 66
    0x101c411405420019401030200c15002d005c468004030400e0340c4c8060741c6003034400464600039a504040c40c00e202c9990440c564901412240258202c02020b8040701c0c1e56507206000c0090503c41b0120700604483c9003081010058000004140c07166603403842c0101541c0c2046044030300c00d5004030500e204952252202d54810348ac107040c00b03500c4082201c20705c40d815034803101070303084054907030041310100c1e020301c5006000721040c3c2d4000840c02c400303d03121401c44140d508082c0540b82106540c04020341c000462641015042601c0c0b200d0380c8900e4000d0fa6102d40a52000c40c1c0c4c0c90320030301220280400401c0080c450b0310300343d0698a0404201c0001400720480900c0b000c04035001e0051441d801e480f070700b0003c030501001c0c0112850284002d0020f1804001141c190200c0c960303000b41400148003038080d03540324071810341ea040c2c1001e050600098950603644a501c00801e010101c1409261083c0b541c4c481c58002c0e104800e011035280d42c4c109000d0441a451502c0040302d003c98030056002034450619 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 301666205 1250 301664955 301664963
    0xc27060c010c020a050d022a030307020402040b03191b030e03090406120c0e041a060307030212010902011421090a02130f150e0a0b04020c061501081308030a0f150902091507 76
    0x30802c140c400400710003c54188c0c40300d40500c070510000c80140c030b41d84010006130142d01003c640382c0c909401502034207100305103a151a00c0c10039944c903004001c001104c1599000c20704002c1607041d02f0400c801d04d10300503015042d50181c02c0c0000003422480c118600400c0314000d8103c0301c0c8803521400011014a0300391001404040210701c0c0582086003040c511740c00160050039541000d07039940000d0040310b8034032000b0390503965410b0080c1c219a0090215051034500c544d2880c280108860050707201c2001580da4028159030200040c01f400003404203820345540146031502c2c015110f28000001c081482640f1a00f0740390400c01c00c0e4407220030b400441251341d401c03008441a0303902042e400141c00300440396034002d9000d0000004080c01401003a01c03940300c034080c40c1040b81c6500c0005001520140c55888086580c5016030003290302e020459922440312440843c0304030917104218020201d4510b54a40d205001602081e0110300e40c000304450a021070305220400282c07103000b4203510400344024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 301667455 1250 301666205 301666243
    0xa09030204020f07051608150103050a020d030c12030510081902060a180b09100503090304060e0a050315070206090c01080a11040e0a02040305060c27060c010c020a050d02 75
    0x10301e0715400618101c2c2c48545860b08225184d81c0e00340c0391500c21041030341940b40c80d90041c054130108000003482245650143e01070340d45503858154903110984806070007032070711010210505006072407c02246500421a2201c007000150040c001d200030385e1044504100064001031001d000030304a00784c2d070500c41c02e6044401d8180d003000006d900140440041c05100c244090405c1070800032500107041c8800016540c500040800100083d101c582905008040c814004035000000039101504c4040c10b212090804040c0058013500d803d5201e25810700c42c440c03101000000c0d41c4681402540c8a1302102c0043c2c452540180d19090a0f1984131300050120700081c2540709581c010300c0b402d50340c3c0c0d58503624150f2034040c41002a04101c440028140e0002003c000300801042415440503603100701c0350529a24581501d002c0c415501d0520428144001d01480341d902c40c01120a8400d80074001c1086e80d11080002c0d40b03802d0026400da07464090500ea0b818084c2c00800d101d650000104000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 301668705 1250 301667455 301667459
    0x105070f0305070f0c1b03050c0f01030204210f120216080c01021218101d060f0403020f0f0303030106020d090b0a02070501140c0115170c061c0e01050c070c0b0a09 72
    0x80300c83e0750800e1015500300003600705502e6514a0540b561000e94019000327030120301c0c050400d0210f0754203e2200e2a0400d84100001c0044052940044000d0103480c600031240c0741140c24190003520203a04050308441404241c02c0749690001403a02c0600814140c05545036170301c3c000b040d02d0b2207054404a0250b0840c410055400340158010000c90b1007803c0c00804590004010503020301402e004680070690302c252101c400c0071515141c030070850701100c4484c904550720000300741502542c80300900603841c607000d000b0640d8402807a48804070000c1c04894072507946400c002d551b100f888405d00041003004001280300b101600854000301107540003842800c0c80e04c0d0044441c500340380218840c488051224110480d028050540c0c4691409900d07161705003454080442d0200320b0246043c1030b88403102c5503080e5182c0310199085109003202215420b0703441095800506540761441c1265481d0101f00a28006010054140d29008540000d446a20342e81d000c0503e2140c04017002c0800c8402600b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 301669955 1250 301668705 301668707
    0xc0105090a03050a050a021c0507031d010f03022104050102130b030f060f0a0803040609050a1502060a11070c09050f06100801051c0b09070504150518090a0b01080105070f0305070f 79
    0x40011000c6d9104450b5800d004402c584011803402c920361001440004424080c10f07484600504240e080e120820810f40104002070045109a0b45041c149900401c83c185281034410200b0043c208142d0641218a8140740842c001d42c0304142c00c0c049081e01c00b601040c8007821905691251a5441ca40354690320366070200980a0b0999144a6105031000c001080f44a82031025000070900c80d00c03004016418841085140d0109401415803055240340c00b8495550000f4501e40010f00c1140016030444d0245a64146108000001d8100301000740001100e90340c5600091050301201e481c0520342d100c0b101000801400704906400040c8401e00600c564500203141c2424001a60355049104d40d49036103640b00e00707a08442524140c2c01a4800f040903080c60300400e941c26000e07a02541c441824200002c01c181c0032240701801e203410601c00104002030030440c1c044541d40180ac500010360f0746410301400380c4021646000002c181c1d045c00307a51607000b4020140100300752380b12600b034995a250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 301671205 1250 301669955 301669957
    0x1101020a180605040b07140a050f1c0806090403031a180405060f090d030507050d090605090c0a0b0a05090f0a0305070617060a2d0609031406090705060c030f03010b0c0105090a03050a05 81
    0xf400b1038a03000320344640000a270104640039016000c107015182140a401c0f8035020441111030020a01c0915410045165140d1031020392255040c20002012180351420700101b0782c00795803494200403030308060a06500d4400d4080e1040b0f105004441e220b075258000d5401061007074404500720b0303014000c0112603030f010f0b400260344043d541c9040c504021046180030140c2d0080035040d250240c2e14400c0c0b219040f01402035805c8400241c0700016258541340e800031700c42c4121100b0b0703000c001c03020030030711415520540b07054510070740102840801510707801e0a40c3c030341e040b0348502800300300ca400d54005c0c023021360540039100788002403c28401d217141100750a10080a08140b03881815003009448007031042054000180106548148000b41140341010221403418a0744440d6400300c0100002080c1c002507420980d202641c3d8070341c47e081c0c82d135505843d600500e0001c4000440100011840309104070107003c0046081c4000c3c411034403590400d9882d18005400600021000c0042c0109940100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 301672455 1250 301671205 301671233
    0x80307051c0212030c070b060108040c060e010216080705100906020c0d0609020d080d0c02150115021002030f061f14130302210c01090b04050108071101020a180605040b07 75
    0xc0103031600c20084084003e055402107801940f0158041106800e0043c070100d1540e00640030b00346030007642042e4445184c3c8044611422007001990004140d290b40b01b80009003503107100040400425840310842900c0c0c2d20726000ea00d00a06c4031041d00100356110b01d94200c100e820070340182c00d00111600c184501c4c503c135854191021900c42c0b1000b00140c84403e26446401e01440f1000c1d1590b245005160607034050300c41301e40841d4040228200084600000300d411610302600b02595040343d0a8264184043c83c0e101804440c40030081080c2c0316001400c452240e0030458074081c081484461200c42e2001c180c00a01c0020282258000c040840383c0c020b080c40c1500e54003102c2441e98a900103003688845124000000901007100031240d2020044103201c030743c090a000c12030f9400e01214100e68011032044030b0411501c280070aa100c1d020b0300b0314026006a04000355500d800121010703000c070b01c80314109401c0d404220000a25103114106403400c0c2c400710107401c1d00c1c2164580300c0c9072816040c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 301673705 1250 301672455 301672457
    0x121504061503060503100e030f0304170c010c02150405150901020903010c051c05040201050319180305070b0709080705152b05091b040e0a2406080307051c 68
    0x80202169010a1400c4485280e9003a0b80c04109507080005150402032144290005541068100220800b0203c01e540c8002580000d2546070341e01e60400301e5000e0780c40984525028400640f0701d50300c85040d0449940407102e50203da00c2d4a041940c3c1814584040310090590f40001d4040c666002d445072a1316002000d000026060403103a0000a00316215140351102003480003030660800350109183ea94410100442003110340f0f480c2c0c002909501c00100903000c84004000307041a03d916644c010f80700c55508800c000840700d40307440d004c0e01c160301000050354404504000159007a01c2846c5050503a60990086e2110320301d01014040391041455108c1900c3c541230110b15286000400b416180c500140490078110548402c804c040b00c1d0068001d040304e42000350140c0303103032491a0387c4644414099a00240c1814404607003820050904401421041c0d0010030080c21340c2204050703030242c04039080411100c0c1c2d5445080e80d03217120f502c1d40100079030000391203100005054060311003004a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 301674955 1250 301673705 301673711
    0x6021f05041406150a0f0b0a0c03051c020a2705010c140d0302070309060807050313020f100503090d020a020306060105070c0e01080312070513090e03040509130611121504 75
    0x42c86600300e0030719000f00c400d0203801c4940c0c1c14802403841d0415414005004915603031a4150030b100c020000d604c101c44980050100b1b4500d11b8040600c11411150180107130495900710b003101e07000d43c40196100704c004200050241450800d003d80c190440001d0b5031900003004401c928100055170a0710000388140c403180c083ea0a20070402c0301c24800000a409035507001a039800f0940740217804031035250426420040950200411144c00808a94000e00c201c0780c50300c0246040d10014036001510560a80c001940300d03161200d1603089405940102d8800060f15080f0072a03040c00c81c0da581520801035855441031010612650103840101807680c0600380840b112511038845241d00c0c1402ea01107140c2e41c1c00066842c1b0201030800380260000f12514081d80703004000c18400c0b00f0002d035809401c000740c2d601c03120541c642e8000c100712001490094000e000c0c0303145c5a1036080c151039142405a9803541084001c0c0d2600004104481803c154100c60040580300c400d030303520b4a008000040c4c0d40042d6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 301676205 1250 301674955 301674983
    0x90411031006081e090604120504030302060106050d0e0d0f0915020613030507170403020406060527130c0e03010f0902011704020114040806100609080a021903020607080d0606021f0504 81
    0x9144c007100c0d1250301104001c00140c24946007260300172048254010400c081840f040c00043d0340402c590b4115881031038100d8880034160019002019803094401c41c902c20154000d40960304041851514241505c8074484c0c0b564503d035602c10102c0c10074100e40140c0042c0001010380f00440c02580080d03000740381144c1024580d0340e550f480d1442e20440c486002c5c102050402c1186414060346002c1d04045c948103080c040608110202c1540d044800c00111b000098242215140d0000c42c4200c101c1c004014018840e4518020b8011845417503580e0003035003061a11b06420303146004100b1031030b6041c2d6030003403041011164160f04210140c01203040100c04014441c801c078000c0e0150000e050944060811424840200003500e06140d10032001d00c41c642d1401c100c0d88101003150400550191090003040c120803240342c80412094100035400304000c82c0320018081180c002e45900ca1070000c00300400303078991400341c3c2e48880c5c1202c1c0362440c111001116400d10303469040160040c0c0720310b040400c144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 301677455 1250 301676205 301676251
    0x2160f060603050d09080d0c03080412121505120a050d0815090411010e0a080606010f030b04020409060e01090504020603130f1a070311031b0c0307051209041103100608 74
    0xa909031540050b09845d070a028070710003030012070390035400780c18101c40103c1c503560080c01b0400010030240209503010385c0c0141c441e00401c072140444011704010440483c0079043c07041c070007180e405180d00410803910341c004501400910080c1c110342000c01030031485103800049498800c01409a00700480c44111082542c1720300c280ca5002d03d00c40c10b082c01021a600c0b00040ca200300d0395003194030449405c1410401d84601007032241e04402c1c03c6c41c012400c549104400d4015005510b40160054400900003402f4840e036405042620014515080c00340d9031940b00c841900d4043e107019501a02c20404124143e8180041d0340c2054407440840c400f0001c0764a03621660380b200f40c21800d82d0404103040100b080e078140708980717819407110000f80c15804c100083d078800503021226440c03542c4001840142d4080d041040d42c1c0e00344e0340304003261012800b040f07030002070742c000324903450041c2e04029003030540300e030004280c9105042d90f442e05204c0703502d040d004403171400c40644111900c3d140b800407040e00c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 301678705 1250 301677455 301677463
    0x30907092d0524150a020106050315041428022b02090a1404110a080304290901050d0f02090409080309060604020712032003011d06030102160f06060305 67
    0x1601070380c100050103140100685107412074004541c6581c10340000f02c00019a1a400d801040e4124501c0c0c080e15025802c0302070340180029000305078144070305040703c2418840b0300661403060340b00d242010004403100c1c0c0c11551751094410004008a061814070b980b42e100c0d001d00e05416400140000c030f42101980b55044403010005400c0c0b4a55405d0b1070020070360802d1a0540e80115104004000f0311407401c41c54549040c000c1c0004041042c5000c40801c41d40d1405181c201400d13441082c1c0e40d8560b500d015071203c0c2c1c04c8685059032006605102c61032000010b1040e101850300c10384801789800204076880d0006e00030a040450115400e015030400781d150742c4a441c0341284960181aa6810304c5200c0b0707868000024903103442a80100300c03200004013400c048050b00383d800c0c20301181071003d030b590003805141e00820208407550084000076164800c520341c0c095810010b6290407035515a08107140c03d03803217030002e8106401d8802d180d002c0020314000d400c80051740240710000c2c80c030340c507035580c035082c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 301679955 1250 301678705 301678781
    0x181501090219081005060715020a0c030315050619020708030d0b031005100b0706060b0f030109050708010308180301090807050606150403051b0310050a05091203090709 74
    0x169000c0780380c10000b0100c008614030540282410038151404a100362900c1400e0701031140622400b0a0940400c203540251281c0c05525010964a6200e200c40081c400b40b0300302001d800090404a01d04d095500d840b82e400d080ea8009880c140c83c0c514606445102010000411802c42c42451800100f0203011301c040e00101d2140f440124444141c4020140f60014030705d40b102d1030740e00c2c10061000e440031041d564003c40342c0503d607aa0f01d80b1860b050242c002d04090303101000401d80010b51000d19855400110f068890400d0104016100c0d98000c0724054400d00009107908020820029000036102080d1a049401800425588401e43ea03507401904400c1c0c08a880e84e000c14184241c91510402d601e030722103509641c0e142001e1440e1242ea644040d14500d2891001e41451000c090f61010700c9149414441c4100034000c43c1403010034800213020031500c8039802d001c1d014021103440306280c200c03400782c070610000705092801c118a039402850000118043c0212001a20301079908202c14500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 301681205 1250 301679955 301679969
    0xa0c030203220f0b0f07031112031513050610050c01200403050105180d080a0b06070b010501030b01020d022d0d11070b091e01121a030c0307030506181501 68
    0x902c41c0741ca0843d03540c0140036044070304529000e000600025100c5800da41e035440d010f1031b2580c0d83c45003107071080d400e244040f50310250b00c0d81700004200c00d41c0012643d0300c0b1002416103450b4000340c1c0002ca62030483d07205880450b884802103900401d800d10510241050081c800d00026501031052010080c08022420668500c0b00229081090160a2040c6544010702c80d41200210030300303011311602d410071045180240444200840d20a200d0340e0302c8502c1c00e1802030706459841c481420442c1100c60240f2819002a08020a480303581d440401c400c1520400e0703130000c1c90824140c5032400f03400380e8082e18445000c2031141304640c0c1e0450811218880c1c207840c2c4c132004118008588540c0c00c1c10005d0b00a608050400c200042d10750315084156400401c0c0c0078a011075008083c00100d44400802039001e007001c1c10003100200840240c15a00001c1d2400c4041300d07480c02c0d031101071603101e103942d00c4040c0c03054100c44c0000303125040a07407010449503802019144004488140c859080c0401c0e00840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 301682455 1250 301681205 301681267
    0x21e030708010b090109150308070804050a0602030912070501140304080f3402091504060504060915050418020d03050f12012904060c0203030403140c090a020306060a0c030203 77
    0x3d680ca0030018030b102d024201401003884215040d11a45801180c10300c4014181c035000a6400709101c41d0744180c40c0901001443c01c2d0750187d86200080d50b03600240c0d070351842031500b01d403440703e076032030025040084034010703125074801034000341420a5036000240180c07403440080051415542c0c98000a062110250500010711409140703550050302d044030003185407451000003c000360780e030804243e902070f04e1030102c02132201e2203c0c080340241050342d2100350424104403010035030710001c0e0864031035108220121420195900204426607000315103035110041800b840c1c00150030507141c4003e006000381852843d24030468640d00d00c070b03400038225401d21026000103000ca0040a026840801c18600c0844a8501c1540c112042489a81700d2481803081d4142c0741c40864400f48103890096420070240318240110110f0940c0700c03410348030100d00c90106480020039010241c03003600d0003003401810990400c0c030550350640e01032203041310580940c4004d004c0d00c64a0303601042000178543d0010090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 301683705 1250 301682455 301682471
    0xd03050907080f0303150d150204140108010b090118240f030e15061c0b091608100518011a04050c0702030a120c0506070e03120306010507021e03070801 67
    0x80e050120390b8000003a00c1d00007000d1010042400402d603a000540b40c011148403100e440d0005a0800103d10010801e2100742c500c100d680392985d000d00104ca84014000c58089090401124550030074018042102030070f200215043d4465480f900e1034104161980314010f858024005032964085100048400c400c201d0701001d0382d2040c090503140c041030030700b8070140d00030503c0306444904141308182194010381c00520195541c4070550141e62040107104c40c4c451041c1001c0c000c41e00201d4440c0350a2003101d030001c0729000c0440d984800c8401d040301900700d1504030319210000d01406040d10710007000034105020200002e1140351050903a58032002020310450080c4400e4560041064030318900c00c2c00740c0d03000340e01c0100b175062074039034080e1000604003039803a0166556420588094054411103081120681c1c0112101c80350100171001c584d84403050a4001d566480212a00e0b8001041440031400604204968030700c203050f48845d01c04400c0c403030800b192a01c040b652041140781c0d100c600c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 301684955 1250 301683705 301683721
    0x512070315020715200a02150114030307060c0c120f02060a020c0705090402060708070b100b0301060e01030203071403090109030e030703030c0b070c0c03031205250507030507050d0305 81
    0x1e480e40310001210640c10003074181c0300d2440100040c0c1031100c9140d251003600b4146000001082c6000c008044031507100e805c900c50081d0f460748039410411001c103031140003040c1c11040c0c2d82e000f40d070501b004000b540380c15099600c01001e05807101c1c4010500c242812201c000440c0c0c50404146d501241d507440c40c40050081000b80741c10400b815050000c0d204104001e14208081240c81c10755200b65088031183d221403010510612452070f000e8051040400c26104224a0030503060148a0a140135528103845510040441c4020b2146101280b000850301030300d54002d4018542c4800282404d1014110b00e104190060380100d071000c40341e946d00d4100808052300070301d950212400513402041c1c90360640e076000c1d21001074010090840224040007901c0c19100315850310f05140c1c8a282410302580d2490003500c80c90360a1090300701d0b076050000041c1c6481000f9208400f10200c00140d62500e110800152803e90101d90150700700001003100c1d0b804180100400000e03502269030000300c0e031070305c607071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 301686205 1250 301684955 301684973
    0x30303140a0905071202030a0803130c06030b0102031801110a140709020f040608040c0f03050601050906030109020f1201140c18090c0307200f28081b01020405120703 73
    0x200c2010914640800b0b50003007040080d032201601c100300031026500b00c0b140000b92505004c800d0040100e8400002c00940500441c0404281c501c140644401c40e91107000913410f82c3e99540c0101e0059005121b07458260040007ca694100300c1070600b6000707802d16000203414903425600035642000940b0010081e03090801124000304080d103021410240b101c50b54085912541c0300b600c04002281c0045018891103916023001040b405c040000d0f045c1d039925203187c13561001d10420348150901d4000480391708040c05142c00e416401803584066400f44010004803c105815041c180e6580b101c0a91031f0228000e40a40030720200f00d580d03038407400301d440d1045000e50300ca20218010030820307050107505e1600d113064036040700d658100300700d0400158800b88c010407007282d070602c1284030340c001007c0307441800f065501083d1141c0c00243c1d2103680381c0000c031208802c0428020805c0c481001042e882104070f4084500600c3ca41c0005442c065885000a540c841c5e201c144d0381030360b04140c00030001c0101c01c3c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 301687455 1250 301686205 301686211
    0x14010f0b0a0b0403150213210303060e04150905031308010b0306100e0c0c0a060504030503070e06040825080f07080709110d09030306050a0b090310110703051305030703030314 77
    0xd01443d00d070a007141d607000c050400203909662041e801103580070311221141d80c9100504070084040d0302192940355002c80c2a40701d80d01c2a0040313413900c2800702d14403000c480403510407500040c2000c07008400c0c00040c001040c1011003039030b060209100c5075500a607005a078000612040e0b0000c1140744c1500c08042c240f2402400096940184000c1003000060010344140e01104482c1da03140c0318201141410b09020505500030032191400d0304210030160080c0141d40501413917610442e050424030188502e81c401c0380240d1000d5800005c0e03da0002000900306d82c85000400315401030f00b035a4000840c80c0109400751165140c00070711040c07054420400030704005005070340f000c0c40b9507003621004198a10802048142240e21840b41006041c001d4120500a02c406030001c8401550340c1000c03220bc1c2c10414075a4443d00803c1c0f0742250451440c0902d0091141d20200d2524010b0303031b5a8241d64651140114008100041d0700c001655642440750a0003140603441c08950030007a96220142400c0c02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 301688705 1250 301687455 301687469
    0xc010f0513051c080403081302040203100e0901140c07020a050406081c0519050d1e0e0f0309030c040b1c0308040303060509070906030c05280908062214010f0b0a 71
    0x40d10f50051400c3d0300904098005070941418519510f54201e4070b00701c6410400b010b0742141c00003003400805981c1e400c0340c200711807007800304c2100b6803503c8515500f6944400c0703180b0584c004a9000c0703012032003a40020072000d0310040440e400c0c00e554101040c1517407041d5201500c00d800c90348110000030b04051034410560228508503142109090310700b0740e4500e206174480e04000010a10754580c4001ea4000318502030120b4034421145115500c06003c0c0910340c94040142c000c500c002c0003032410000075a040e4101c01805000e181050000344401090310901ca50340c801e0782180c242103646510190091054040d55610a280c60b04d401c0190a488483c0d1003680215080d03810024a25031080c10903098031060f14001c00e0041c072154049030b440c00b807003000282d240c0c41c1c038041c3d02141201e80c140050540d00c0380c903143c040c0b96031441056250031003141c004004500007456100c10740080d0000001452140e115a8045070f00c0e804141d08580036810341614440c0c0d20440c203500c40c54540c4005000b0516 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 301689955 1250 301688705 301688743
    0xc120408120306010302092107230f0415030303020a0e0f06030402041508191a190c1b1113020f0901050d090215070b09070510050c010f051305 63
    0xe024099940c80318800c00c25000020003002141960303129030119611001c00901e445000d143e081403000100744e000e0450000c074440e03104009281c080301c11900c1c00c1181c000d14109643c0200d0310910024031240c00c0c2c003a41c05580c48140c2c1c4541001c466002c00690700954005807034040e1500017501d090440b0300503510845d0b01c40c603d6021a903951046a03840f680c15600801c0000c030454600d83c3c0e12010303800480340d034081c940c03101110305c1c3c00f003400d803052501407620988011004e20141510f0705081d1012600d45000454a174205030b15600503540c070103541e1800700c111000420010780d081d01001d60486410402c0220000c203854440c0304030710504000d0340114504178080b842c080035440f0b0711300c0c59414402c0c082640c001c02d001c2030740b06241f0315030040c1075200031007140d404000711540300c040100c416141550209001d0800041c140096410240c0f0341c00f400c01c8950415501600600101402e0759222554481100707020300a09001d000b62080054181456160150420301d10b40011040c28034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 301691205 1250 301689955 301689959
    0x708062202130b1201020a020309040b0a032a090f05160215180c15070203061003020a03020d081603050915070209010b0f0d0c080709120308010e0711010905030c1204 73
    0x1032980750b500780da0741d601280001c3c01c0c041000852000909400a030310954400301d00c00200725008802418800022902080b6100e420001c00048507000e00000c1c020440440301c2514080d0702c05005000d2450340c0d074003c030001b070740c810408058581c1d4207240300103c2e4a907824401400b0070800ba40d45801c1c2d0743d001078040810a42e11090b00c5c07035401800300f40068005803005038040000c0c4a120542a40a40704100344601c0301f41c204610741c800c580032030103842040300144141d00d04100c00c17010f480e402083c40e218907180d9001c00818060700343e000d5a010300e040100b600110004103003408164030988455032180c2c40c180030450b030a00075150f06c03c0308c0c00c01081007030016942c0d011100e054400b00003e0b01d45a2000c0301004000d0b00070750814641c4946049030044649030414840c0e84604403070369031020540d40300d000301c0c40b411404d1180100820303081c00c0188640d070300c4082801e502000c0d0b45052641942130100719400d48030030380016202508002000b14001c2000c0c0403203000c0300e10103c581841d180c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 301692455 1250 301691205 301691209
    0x31a07021b061602030111071e0c030222090c030501051b040306020f070c09020d0506060406120b1903030305160806011b0c09020d020a2a02040506030304080708062202 74
    0x480340c100728620602c1c001030a00c00315015a20701c0d152013a00030340208040340700c1d1514801c40d98418003003036850141c80c2544010f50300d0300d001d07100b10f07855000211000b050b1840c1c0c00e2000700303001150065455007859007558007215403440381e85c40d02070060040c01d962034030f0350801c2803c5400140c03480300200790422070030704150400e00855086039800f080060795400b14402001e60341c0240c5100400344100c003000081c224500341c000c3c00f0514000d04e4100210749030300040000b07511980c4910380c00b0801d000c028888000c080c2d482400d2105000d00000800400303440240aa031808da0800c5010a5840d0144000903402500300d03254030025041c419114200440060000ca410009190199540308112401c1000301c420200003800284415910349070000380f084040d400084464000800d102610550b0801420286803a003c050903400030100c1142c00b4031014100040c015501840100000184102d04115808c020000d250141440c1d0814041034103041c2558114488004003800141c0003603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 301693705 1250 301692455 301692493
    0x250f0302150f1b0d020d02041e05060415030b0a030b0c0a260f0403020f03030403030c0f0801051518060a0e010f02120d050a090c060905010201180b130201120501031a0702 75
    0xb18500140103911481207800c0b20b8064846c4042c80d019860000c00d00044c0d80140310800003c000c2d100e07030324652042c0c55000703011880c0114420750300f0080c42d13100d40190940c000d0313100c1968085c0c068201030310561252a0a60008400e6800c0e900040c000204202110b5210b158840c0c460413510020510590700203d001076040098042c01c40a41c0003404101094002c00c82d1219020380041981d03224509400c0140007428a4000103011610119582d5109803244294a041e250028412088409800300e0075405802c071840e07840001400d4508030751b403907580c03030042e2690322800d0b91102c8414a030b0000040c89800b00d00e030103000355840454280400300d01c01d03090364850081d110700011166036424112000c0c03c07000c1c00151040100c8400410701c1a2f00c038421000741c4000707800900018080302c9406540c8110894094084a007210110b03047c1791140c010380b80020300502d092500e050b10307641c2103811a0020780c0300b264a0801d00d00f2142e220b410246140da800032a600280203d891040c0c6100c1708 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 301694955 1250 301693705 301693741
    0x1a030106031203142e080106060c02040614031e0c03010207060209041118040903142a0f07050f0625030f050307121e090b0108071505250f0302150f 65
    0x2040c0380305c00f0843c0203402804110001000c6006c024090310342d9038440a41071010440d0141d000d50300b01b05001c5114609050f860030511000740041000c820100240500840102c01011640c000d03c54032413200c2d5000d0010700341035070040c000103942d000b10604100480d400c209406648210901c070303110704a1a042d0140301c0c03c2000355400b16a4a410340780844510020612000f40c00e40041a810400c2e07031060000c10000b07160106d0818188100716503a682c07061010701c210301550110201740007500785000c0c0c800103464050030300c1d42001d841c85880f10450802d9405204103680c80c42060781030540c001d401e00c090300c1c050b0429a1460a104200038040084a800c2e041080e88403142c02040e030480c000758030722412490104200d20406881c010070600420b200320040c510800a000c581900c0000300b074441d055050716210300c4c000080d5044030120720005401c8655a8810b0143c0b40401c5021041401c8588280c0c060302d01d860b0140c1d00403061407005007000402d1142d500070400032040032114200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 301696205 1250 301694955 301695001
    0x60e01020c160906121403040e04110f1e040207050309040608030a020105060109030b0402040c120e0d02070803040e010303080a060503120c1005010510050d020c0a0b0702060c030c0d1a03010603120314 88
    0xc0c2562020b0300c0b0500d184160740c44144280080302c1004103103d9042cbc101d50040800701c503000360301714410081015403500705e0181d050050740713a00c018249180c20b078010080f5504c01c3c13058904201015001078112582944030050540002070840412603080c40f92591004003400c20303841c3c9500b541c03a43ca140c2c03a00100004d01450303440c0d46054800b40600c48130741c2003450f12542405010748500925882c1d00c600300c4100094400c7c40c401192003000031050303c0c103032001c41e80580d07442d81c13864400316103042c000340258002e283d41e01c0c40070031642c50601242082d50302c0d00d220f82d9940d486406407289490817603000e501e003143c502030062220b6038410400030350030000c1e0300d0b046480da80d140321400020720071420f002685205001b82c2d6020410350035080c0744a16210303020b0b1501540c45140b5000140310454400c3c2c40410104408000e41c55140d00c281440306003d4500c22603441a1400300b801c40381660003c0e5458130380050043c1ca00c0c0c0c4d144c052040c81d0b09032545500150309144001540705100780700b400b6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 301697455 1250 301696205 301696223
    0x308090d08040311030c060703021c060503101d101b03020c0705151201030b0601030e0a0b13030c0b09011401050102011a0603040305071a04021009060219060e01020c16090612 77
    0x20381410208182c80c014810901a87c8082c2000030b8080c0c02540b101101c03401c00301e510342800b80401c2592090a00300c4a0180251521650f08210f200003480c06120102c030303d036006100301544610800c000c854040080c2c0e400100b00c443c00020829040452600300201070040081080036800414440112003083c1c1c1c1d80c4030b0796111509000c00e50b0181c0c031010714803000b443c0000824010300302e060501905c42a02e04006110708000d9031a00d81140c580094014000d6401244640c00035139500c00c503481c0245001d1071048030650750b11418242c00d584111003a9122100900011a0b4110480c0102001d0000300481c0c084501089904050080c0562180d00c0c040001814180200200e0b01b266030310a04480d025601248482c880708000d07541030340a042244d085070841402184403000f038541c1c0703400603c40c4c51807a00500c0100045104111071443d00d50700714a9601d075090001c0c04511001d1400703003030003111015126000040176403040722440c2c241300c0e0030403040c505000d40445058000300304c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 301698705 1250 301697455 301697477
    0xb18040c080a06020d05011401231e09040608030c0a030e0d061803022103040b091e010603020f10080610020a0c030605070e0307050a090b0423040308090d080403 71
    0x4065140c4a600845950080340090010040c3c140d00906121020000401c0f46980b10b5010102e60f0740c00c00030803400305010558568030a5400501e5486000d0400d10207860212500448100b1000e00c92a0342c40c03045001c1085101d500d0700c0d005c2c150203008510700640c10a420143c0c03035270345d41c04440809010b10501200d0180203455032202d2041c0c0d40d8100e0403e01c140114030000d0442c0b03040629094005000d581260505000254000541c0c24103140d00b10341144c80320345500169800c0075000f0b490781e00c2071035608500507141040e0000746c1d059400000070407a10f1801400602821489124030604082c0c61070f032040358001d000d25400c294160341136680003260310000c0c0c0c07030120b822070081c08008c0e02910010400c01160044d034880d0b4402e980e0300d0000003100341815540c0c440c60180e5030744200318141c244403511443e0701c521013902d030080011900d07000c000614000041138810b070590003044c0c0800c100506400281c81500a11103000030816110300c918020b01984003d000181003011007010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 301699955 1250 301698705 301698713
    0x30e040218030601030305070515040807080906070b010b13080606100f0207081f0c0302070308070e062109010b0109030b0609040606151e0306050312030a020c150a0f0b1804 76
    0x10301c00105101600b100c600b941c40e42005442c0b0b070800c2d035040b6140d2068041244004210a00c942c0c011980144000e05260407a41c4071f14803500031103041a00140140440008604090540c0d402044440c040658520342c0c91644486150682c11030110303644100c041c88641e0f100c98841d040c1510715132503c01d4800203503540c1281400f640340d0050b4482d20803416100803400c20f00d032000080341c04a1104004400b083c00e03050b0164011a940500400d00f000b000805440c0907140c1c21850358401001c107890412007402244010341d80e032188926a208000800c205080248601d030700c40c840c01d0030b0241d003181c5581d54203528100001c0225000f00d42080102d02046500d41150000e040350081c030361032550388820000d100003100c50900f40019600a12100743e613000f4881d130403d0364030180203400c1d44000c00300072600075840034000c8000117600b040011500c0000b80f00a1200a54058505029003050120704058a84260740d490f84c062502c0e00880c000d566201011602070303425004080380daa11420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 301701205 1250 301699955 301699987
    0x120b0f04111e030105090106170403030c1e020105060f121002070609020a080a0210030c02190f0606060504090609050c07030e21030c01140601020304052101181103010504030e0402 79
    0x1c00740c030b114034210b42c018001ca20b80e00c0c09541a03a80030b403003500d2140c1e0b8070081200d4440e4a4040c84080300c84440206010a10a030800b100c0d050080c10130a0480c0b11036078420156207c403440000050b507403442401054942003808070501881201c401e850ba030040c841c00c0c0d2316002c3c60076903881001d50000e240d5080000b246c01100320190018030700030680d5a2008a180c0b42c449804089210702010802104042d0223032180c5c1100d40e090754004e10808135200c0170200c42c0800e14106036016018100d1100014030075018000162105603642c1e52100c0c82c10040c002503802a070030402c105404c0408000c0301c09520410f4810b51034041c80c1860145980034040b502c0350b4101802e41401d4800300b0381c0c3c6444214000300030152030425070000c102140840c6540d00000c0c0e001d42d07440340107070001c200410281c41c0002000005900030282030b04100e00b1206583d0071141c15032203003030300c041c11540e00c0c074140b0100701b203000100c2d4826402800705260560300249000c4104016178451a404503005612f519550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 301702455 1250 301701205 301701217
    0xf060417011401030b0109050901050f06100507060219081605070609021909050105122a030f0d08060114120103030503090703050f030304020a24031a04051006120b0f0411 75
    0x3501040c0b807541c6a0401e000e1401c03007406000c403c6410b10001ca4469001441070b0780c0b040d503141200d01c03100d0703c03100c042104182c40303c5000407c20070144141d0020034581d00c0200051140c9001400c1140c0900101030004030000b490020b41d0b00c0d030003500044054003e0211080c0c1d40d030110002817040031a100062110043e42031a0691200c0603001103003420340c03540031718140e400407107841ca80a02c00d0110507030395083c01a80b003c0d000b49080e80488281d100c0303600701d2010b00f00080540c1da2000713910880d1407404101e5000000011a6030060169030350708a1201e140c620039560717069241030503012030000c40034018070008041040c0000041c0c0c101f1000c1c00980091580103054070900c0441564140d6a0380094606030f1003102403a4001a10140b840105011a15030040d40703400d03280582400c0d0000d240512686841c41d04442000d40c141c0e0301c5119a40c4241e00c012009182c0c02c0c10600c000700107540400782245000d00d01440c85030b0303e0f540c0d03000401000b0b00071940407030614610800100c440c0121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 301703705 1250 301702455 301702481
    0x606060a12020f0c0f0a111e09070e060703170109090b0714040b070c0302040501050d0507090b01121d0106171905010e03070c14010206010e040308040c0e0c0c0c0f06041701 76
    0xc44c100055080125022607514010320030740381180005801c2103140e205985230342c031072001201c0c4d510030300703092a610f81640003240d400d018980d01380490100c0c406a01042c41140054203480041948450741074280d4094a400e803001c001741d01c01580c0f400e8900c0300c003030a510244030301c0a520340150760000045a010703024070796405445401c1e41c9403000300c4d0741039400304130b104038203000001c9450b06020760f00580c0d040e0014000d01c0090729004046c002801824480c5040111405c420701d607003441e6004100550043d004c00031701905524192a003142d081d81c11038400740c0c0c0417100071085c0343d0000580c84440c0104141102d190941c5d403401740d005000101c40c2c18002d010104d188020702c40586620000c82e080341074050141071412004a85488090040e103080120250104011030302c99070a244d809407040d480c411020b519940a1054a0b5084910050750704000450400b464000d1200441d84070040d00d04112a4280c50005481800340340600b4420304601c0212101042094101c101000d0786 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 301704955 1250 301703705 301703713
    0x5090a05100e0105060d17030a29130902150d1410150903030c170904050109051006030e030f030c1306030605041a1503130b0a0e0606060a12020f0c 65
    0x10601d20700502079802c0003841e90751030000000c10700e003011143c02c40c0319588100c144803d500398151504081c0c10203407141822654071103c0c210071070098184080303529240d00105100d5054107007002042c850f20018402d81c10f04100e941c00c0161034010300440006510201943c07140b26907884100200700c041c00c80086201c0080c11710840c40c40904c0350300180d401c1e81140006001f940e01040e07c8885da06d10000f0006010107681201240d541043c04900c0d4840b06842c42c03401c0503040005065030000c0c2c0110b641c640d0b0341c0c0c1c284a1440200f400040c000c00d0181414443c03003400d0b4482e16124040c0307118450201ca00040040c0c2e80d014088c1c22140000f502e134069002c080d03141c041c0280104441d016440c000c5141480d6405080305443c812152481c0051040e5054490703180340d000c80da0809803080015400900f0103100007024104018415036414400151071068411a24527120018140e01e0107000c0410203040701c1c1b5880360030700f585801090400350f0303121244102c2c071000b0b125400c108070301809 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 301706205 1250 301704955 301704973
    0xb0306120601240203030f1314061006030501081f0906061a0d0f0b06091002010f020d051527130b1303030f1512050c04091506080105040f0605090a05 66
    0x200342c45803030807002c0c2d2500c00440560940306080c4d03900d220903141c02411f00764920014090790740c02d101c45901103125044100c6200040b00740d05250210a640d0300010b04045041400120351500c00e050040090f0030040c25002c8002034180e102803440005155000d485221003001d101c0c10390030403401003000f848140b205c003024141160541d0001255014018103018913180c41c8100c6010304040e4400c0180b00a1801d00403000700400d540c5540c030200195502c5249076000d0071001e2010f800c0d405000c0750007188a141207010100b203000c0a8960510800f1108000501d0405201150404641c2c00a85039096100d2030401402402040001400105004100f00d40d460591106100a91103a00e0a011510f42d8065010031340d400f824070000d0040c2400d008103c10300c40a03180c580d84a01480c1038032190102c080128040d6407c0a0003940d00c000b81002c8192041040e00c541802400300000070003c034106a81c640a0340d007002d0300d000e844951907101007440040280498140190312104850381c0d48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 301707455 1250 301706205 301706219
    0x1b04060509060d11030408030703052409061f02030c0705030f12071103030414040b1f030f0e01052e030b01090b030f011407020f0a12031d0a2006070c0b0306120601 72
    0x2e44110b681400103410000030410b0333003400c8503200031505140340b201c007038503103001090000c7d0200051080360b02c800c42c0003811031184840e955880c1030086c0d6a000c0c581d15032612a4403031500c0e0980c0d0226010303600801c40000e2000c404213540308901141150a5600c08007401c04000710722030b0305180c07540340c000010002040e0a41980c140c3e00441c0c10b84c1c040c8050301c4001c00704032800c0712048403448800e54007150307803010358860343c000400f0412488c0001405200502c1c41030840d0340031500c0141c0b807007603515075000c0400c030300a5a020b404202c00001c0051801e642c1d4030b41e1058811700c81c01380c2842d2100c080031429a000c3c800110300c045480c3c02000713035440880c51001500010707591076016000c1c4507286000010f000c10803a04560308100203858521141c0c0d000c80007004166044059000401015807407401d0030311444071081d001d1041d0b24614903a9160381c40442802c211400e00c112000c0150380c0c00501c11001c40400c40d90100069070b10381d61560003103402c20180e4980e050640c040c0b0000880c400e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 301708705 1250 301707455 301707457
    0x100c0203030601091203200a06060f08010e030a0207181e0501050405070e0d110109030b09010e1b1806030106170a12080601170c09181b04060509060d11030408 70
    0x2580007644d0f070510059480f043c00f000c8458510001d000030390006c2c06031116580206000e00c0461182c01190203179105d50710b903070b4200d80c510b8109004142854004001401003400b03060388170302c10072016618004800b48003a58a4816110350291034441044001d070107102580400e500218070b06480490000c800d0b000300081c103007401454800c0b407504001c01c4200f0f200e0340f0010b02410780501650004180e0b0f403034455070481c6411a42e41084020800800000d0070f20301060b000d400d2150000c10315000ca10011410180002c103405000d215000b0082d440340d4400e0440c0e4800d90028280c29604d4862101103809007009400000c010382c881070f58580c0a04002034200d003118040e204251180000c0e40040314000350035107040b800202507080c0361b403030061840045c036000381074070108a18003002d402c0442c0308800814191541801c2c003104100c0c04c1d540c0c3c18a081001c3c20b01e80300c0355203410b041a0024103503006404140d40100710115070590b0f100680d40c0002c03020055040d1840c1c0b02d10b0186840340035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 301709955 1250 301708705 301708711
    0x1f021e06061201060f0504050604020421060c0212040306150f081e01050c030f0c09030a03050406020c030f0715110106030605100608090601050621040b0105030c0a031109040302100c020303 83
    0x2400e0907402016602c1c4061003a0015a8108200103040c00e2134002000050400501380550040c0d0030080001c610b004c1c400002000003055000301406205400d1040c01c0704c4a80c8a4501550412000070441c001c00b182210300707076540702100103032404070b10901d219000203942042c0c6800300036240c0401ca070400010048444c0307070040d11001010304100003035800e840082e00c0b200300350b103010b0020591603105004030a5111001e1005141001c014000203481c01c0100c85080e0081540024240718180e410701031004401d00a400624001c1002c94186a035440144a54140d01148161301c50700760b4841c02521280700f0303020009000c5c450b04ca080002c0108015a00005072a60328080029583d018410030741c07141c440c01d001382009030301e81414001c15500000050b2800e4070f000b0b40807000a414003407403500541c0981c500109640c1408141845c2c903007141030b140c0c481c464000d002c10000e1003010400c0c2c5205012b544084080d00d03245800e9141c0350000b50001c0000e424002820030103079000020310300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 301711205 1250 301709955 301709959
    0x90a15060905040c0e0603040f1e0809090108030306130b0f06120709060c052e020c0a0b090f0309040e0f0304030b060a090b0607020409031101111b0c1f021e0606 71
    0xc42c51300d04095440b000c1003080c80f038004109000003404106192503040649010301201503e80342c100304a11050345602c13400b2034901320301140d0705c0d10b20300b032078980300d4003400303016000350720750b00f820400104125600c600c82e520396925213414a000d61a1518101c070203207405000503855410710010019441c4040b44d0942c0000d10016001859070301c82c1445440041e0000003074081d11014800140340e0030b9402101001c902c490340c2c1c02c1c40482d81c1900c014680d405000e03004d03100706c030558075005156042c0504003165640c0702c03403101c0d001c0c2d01002c8102d8041c40b4007102c000501510344c06c507003408c03d4551401e4456900003c80c0c008103100b0980c51180c41140101c520030f25503501d0340c41c0541294a04400300d50400400d01c00398005003466441840705a001382494107011b01201071031400e50740301c100444004c0f007012441c2c2981501c4130300c07451b0303400740102c0286c0070615507503011485124240d046640e019201062071040c6a00a000b5500101005a54840c803070108103226542c801c0c00b038400714 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 301712455 1250 301711205 301711211
    0x160f05010b030a030503161b0f06050703020a0e061c0e0709180c03060b040626011503050307031202270f04050702030d0c030b030a06091a01030f02090a1506090504 72
    0x45007900d008621004a1585500c689003140c07900b81c0c507900c082d40d40301d0302c5c030303080c402d008a52141e400030b8014045012480358010b405400c1091900711300781e8a001d40458145801804061000d9400601c0c1e5a8403e01c10785005440e510390b80c3c0e0b0040c40311000d183d4843c2c0d40e460203010f294440c0380460b003c070941d40800b205110450301c480b44c164014140c5540a040d100881d0018000140c2c60b0704a840139890082010840d1500da00101e504052203034003040030241d4030080121030850078003400346201032940c1c2591030309155880d19a203e200c0e651004041014824042010325a545c0c16602c40c201c3e1104007010381e14070380c0340c140c3d8540440754480c0c0c4074890700030700c00500e03203418040c10344645541e502645c10301035a8003400000e400c0f0745800e04245071300d80001c00c0894804200700c100040c010701011602c1846420103412003020b455005141d10569001440030808182884034510380c191540c0455076540803440c4000c003c241c003811610000c0c12400603d259000241c0c0050f03402c200c03130030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 301713705 1250 301712455 301712471
    0x504050d02030906070f291006020703020307060e1315030309081606030e24010608070c0803060628031e020c191412040f1d130206160f0501 62
    0x40c0da5902030030070f000b80d00840410a01c4006510921207500c0c2c14403806110901020202c1ca91140c4a5007100b8091610400e40400c41004201004100100750600240a1481c1075401083d00c03020381e0300840050044030064004c0311340319080070100c0040545410044990440b40c0c4084d100c086120070b03800660f00748804251780c0c0f4086010348800c9c8101c0300020500d0b19020060700900308906550010b0b000c0d500403c09600380b0b8a1100d04840486403004000d5030400c480500104009031290b010440d071202c080000a600c0401c40c1e4000008070b0b12961203002003044ac241300c606465207082444c1d0310158644400e50150800c0c42ea011400c1211100c42007006e060740c0c201d005246c0c5d60700090384400703d20064400d01c0d50040460360700030080030120034580d58850340350241e12911103c4001d00003030100602003100880d40041e01410018450039655030700c5004000c1c50203807103801d02e101c0000b902421036a401007114041c0380c02c01e100c00003502140c20481c9212040050a8905509007684 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 301714955 1250 301713705 301713707
    0xa1e090e0c091c020418030908010c080103030f08090a020a06170105040e0a022b0318060804030f0302031504051306060f0602030a08040501150e010302120c010f050c070906090504050d 81
    0x160340c0caa4101818a1503d5071201c002185648800201640c100390f0710040303c8640d090f04103040100d10300a8441d848034900e8079010b5401c45081e12908030811140e58010f00010798011400d140c0313807000e0b01e0070111603100e03c0b400d00c2c10404201c0000790303c680c003032100142c0143c1203100003948001d05460340711560390341c1041c001a2a1040c41042494024030003007070042ca0200350054100e4140d00f41208a083d0b080e4802c07220100740c41040c0d0100341400c101c0c0403801034444400020b07140514018095051a58018001c0901c1c070000509164010000a1920100d4044000c003160700030002d00082c20101080c0e503803071501c042d054408508008001c160481040c2c2c5160407208507078000d40c0780c405010812101c080b80504100c55554845205810010550242d80b000e044210840c440a5145104020b1003085d114079801154010010801c034513030b0084841d40b02080c9905046903500c080380101400c100142d08080c207610324007000850b2010050b404076204138424411145410700f403243c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 301716205 1250 301714955 301714957
    0x30920010207090c0309020d050a0b09121b0a1505220804030209060d0506010603020a0e030c010c0b101d09070501090b0a23160b07030b030709020a1e090e0c 69
    0x905015a01c5003500300180c410715030142010080600e00001c0104041e40028504c000d141c1096489511582040092128051710a038100c5803035401081c1d42040103901c0315040c0070f8042c0c8180e5442c460315042542c28010b101c60800c00b680140c060781c000940030703000001804291003660203425281c1045510b0500c03004214070307240d00708820504040c40c56080051804000300b4090300140d4881c2580b0020b40300b001107078068542c80d200541c480c6020b0500800c0c200c4120240ca100341e0002d140700c1a580d80158642c1480342d084003500340075940c0e1681084003140b407a0310060080703c014081d10280924010864040d040150544004a50303941c0111420030300b07401000c4000307030100a010303130b441d00a406c00c2460540c0040084210010b0403400c01103a00722001030044244d142d5081030400c0f0807140d200340e110b0200c0c1000c0202c10080130109a83c0d9801c2c0c02403481c05a400904515814011040019a12146481d0200418074004014640b8400b03102d02e114604005000c1043c04a00d0700c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 301717455 1250 301716205 301716263
    0x6041d150a0501140904090c090c02010b040501030b04030309031b1a060402030c030a090c030206030106021b1c0816020a0f080616080c160206030a02070b1303020c1315060309 77
    0x6541c1c40c40701d03502e404c88900180c1c48010815445a030364196400060500311659000301020a400504e040002401a0039510500c516074800d600d800c0040c0000f60300340d20b110b904103415150018040e40d0030b15054640a82d45078083d0111010b01840100f0850080c0c0080440e400003881a1595100c603020b01059000035074550005c080203100150b01c515965210090a9000d041030344011a80c07134000c80d29541c0280c11003401a0801840e0080142807041900c440c0380050701d0043c1d11010408080b1240d030000e0500516030300d80000c0e9003100d2240c00b40071000040d001401c40d50074503500d2418481c000c1e264817500f10540100000200b040f80a0311508800c800f0b1501c8203043c40c0d4031034920141990290541200007a40103042d580540c031803801452094001e0000140e5484e554240034880e004010441c500611110064800107540400c01c0c2c403000c10143c801001100752230050a000e807401c4c4107a444015411440052000e503d6000517248a0040c00360048840e01d5480e1031b0102c9402c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 301718705 1250 301717455 301717457
    0xf0f0909030c0b0702190c05040b0a0305030a030b0103020c12030105010809031801120e06010902030717040f0b18100c030b040b010807081e04051c0912020f06041d150a0501 76
    0x4260901c0100e1808002594404030781e10540e03440d1b0720b0f00c0d001440d0650250100707880341203403900140083d0815101e02c1101120850f1507101c0741d4951b42d5025074030b2143c1e4441d11b0402d51100c0ba2074007030340d001e50150b070401c0d40404240c1d050188c602c2c21490b05500244146800610500e0200b40c96440100c1241c22074843d031000406108203c2005644841400d946030030303001d0343c0741b8010242100c1400704031702a1011000141c0e07282821540100a079030f02c3d09004440c0d08040302030100190281d202c1764030465200d00c464020365100e03410b00d00342806412030900a130041044807030500d2120703800f036a03207165035840400844000d80e0a01045a06004c503040c01300b019840480c1036180155000d581c404021700180341100c8010400c61003050050702c04403900e9100c001100c400342d000d2800d0300c811042904e840c10800707191030303d0040258803483d0040c1c0244200b045401603900c99104880180c5088542d6444504041c0315003100d486084035641c4000014001202c1d06240c0030200e03008807001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301719955 1250 301718705 301718717
    0xd051b07120e010e18040b1609120302120d0501090609020a0e010c140a03050403051e0d050c070306090b0a050f070c02040b0a0f180501060302130e1f0f0f090903 71
    0x8504001e0350700301c196a0025040c000070b04d000c03021566a90000040c8402100c042403414205881c25000111010b4075030240c081017080d10241150344030701300b8000c590001c50f004509940c00d05003a403d2074080540032441c0040040c1c2e582032503903203401213412101080010410640e0300c0706450100e0140c1d407034950006510360841483c46d881501c001d0480c50140104c81c81d800603260025242040d4820700300c004c01d902003401c005102d424420b02e070581d888843c854031001441800c9a44401c0005100c1e42840404225090380700020130010303014503440b00301002450001c1c107005071000f00445201c0b40c221b050000081d01c030400303690710038011942d50b26910741021403a42004040d0055501131604a201c810000818480b0804810028048001100c007070b034126405e04000c2c0d0750140c01c40c01c1414010000c41c61703a04c4014420b0003c0341d5903ca2050080e4840030558403030140308146041400940c07917000b0039154045d0342c0314001c40303541112683c0c010b550b494041040e41c4030f8003000340204003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301721205 1250 301719955 301719983
    0x20712030902120105010f090e0601080a140a05060c1c2f12070314010f08030a030c1205070908010e0105010b0f09061210030b180d0f0c0203030d051b07 67
    0x100036000910301c244000e11809030212415412400c5403000da0040c031101c802e5081c2044008024481c0d036038400c0c4050090300042d8180040d031079490f548041c0042c40341029103002ea804910620542d140b07103a001c0150b8029060400800e92680c00c64803160320b41e8611081142d101c095540301e18048003040c5030b030802038403805454034484000d107a4695423481404011405030f000c00821070b144102ea00c1e03100000e00088258154a141405811000d16100c8164051195090000c00c4d1000610180743c08102224690422101410000746440c002c90820007032044064005003400142d80ca441c0c000c00440e4076a82d003080c240c070707828820900f44030401c0110001c400f489030b005003901c0034040c0000d854200c3c0009500c1e81d9010880d00100c1055105205200300101c84984039049100c120001608000c9007906a1700d62010303c0c03043c400c2c0104c0f920210210381c060145203070380a8000f020b03a41c884c4000302da284054402192020010100000075a400c156100150b80002d43c01c8044102419 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301722455 1250 301721205 301721207
    0x140708010b13090b0a0f0b0714060c0f0f0904090308010e071b080726032208090f01020c031002070c0603091707080d0e0f100b0102030a0810081606020601050103020712 74
    0x100100145070080500e000108940f0b41c00b000182c01010131f080d0306940d481281c148009000c00004141100c0d402200030300c1248030380b00040d544032804410f8425038480d036200204500344100c0011580050400707045800f4150808021030480d0003680e141081a1b5801d10211184130714803055508a8100818505c041601c440142c41401c2c4a441410141551400c45070b00b140c84403469070880010000070031a1204100750840510b00c0456600407000100ea55002820f006101b81c10b4060b03c00800104901d078402c1111000f0307000b006d41a00c081490325681080603500070a802e03109a00b4031075001800714400d00c03030b01c0340440d001400402c21034205040300300c0503404000155241c00091180440d41c049612840c03c540a1040c020500c2510f4020b21a080c031220401c800d440720300e01109480d450340c021040b141010600d24060b00185da6141c40340358a4035183c2c211810f58841c1a0745800c000c4440074510055a0480c0c0803030f0540e03a0b94100450a13486007420013840b4091b0745002200c12 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301723705 1250 301722455 301722461
    0x10e0d0f0c051002040f0303020d18180f0f0f14010503060105060f1312020f04060509060609011407030e0910120303020309031612030b1903031110140708010b1309 72
    0x580c81201030790f260020000104003a600315800c0715408841d039030b00c100101038040280b60710480250801c04c0000d9091403100f48402518410165056411602d0340c480c5c5c800d0354041c4c455440323122030401ca100c0c40440e020000745401104002c03001e00c2c0102d00100e0b444801d080c68120b0b00010700401075a801c100501810350480b0149a00c0d40c8028060f0000b01060701503800068007200401c0c0c01c01000e5801000708024010701401c0c000c80c6403d5041c05507403a10030000d584460706466203a0341c0c2c000d080c01210907149030304120320f00600108507075040507400020200001012070300c0f00325546030040d42c910b4440b00f1b845007a402a43c2c0001c11030009010743c01442e80500080150707800d01c140080180c82c669a41101211200d0110245a8080e84c244c80b40e814003103030694000c0b0010900142d501d020f041280806018802d40b01c0400c00704d01010805205880a81c440a00041c0000201c3d03080c8140b081e80c1c00700c04110600008a50000c4000582d011740d65280110906c461802c1c52110003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301724955 1250 301723705 301723727
    0x5030325030c0b090a020103142a0c06340518040902090702060f09190b1506070b0406050a0203060d0605090c0406180e0c0109090c030204030b18010e0d0f 68
    0xb0310146000030000b02d68004415403081002102a140400c881d1000508071101c8011810341018000300f8010002814500842094103424000f0b02d810000300c81d004207030240444280e100e12540b010080440505078204800707800c2c202501e100078203415080304407603400c0d50112000820600140a01080c034808007071490b080644005020071700780c0c005c60744c04841100d8000259019000b0b0041450b00b0038500c070b03449a0b40304080c10001402002c005540b19105001400320743d07442d030101d020120410a214058038004140b83ea880c2c40c1c904d4110741e07104049409403075242c0b4001c00915050301500880c1c0c4190780081c001c504254a079501d0400a101c043d0044d036103446000c41048907600c49100c1c0d6406000191081082c2c00348046060054a600b0b0031520701580040c11002c40e0b0b660420910000d4500826004c42d806c843c0007411030003401941d0007d86141d80410900500c005a07103800f0b01c0d02400c1e18024406213003640005a602c80342c203001e090016030b500080030b044600c10219884 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301726205 1250 301724955 301724957
    0x714030a030206072601080102070506070906050904050916030516060e0f091015120612080403031b05030703030c121406120a0f03020f060f010b030f130c030803100503032503 77
    0x181d070401e910b14600145d101b6000811669030000d849018400100a16540818146400e04181d410008010000d00031a0101401641c90740d0128400c140184041104030181040c548006a81d03824501d07600e0301d18003a009901d034440600850b0f003e11032078031038110a001a0020f800e041a040c2070104001c0010b00000d59000598004111981400c8060300d05e03030140d079200016585443e0b80071040f51820b03070105010802100c0d60f140003841c0d0009440407a50541461500d244000440000d00104004020800d0100040f00010140c0640c04050941e1080e030351030b0040c01c440030700442220a03504185000f10703807060015110f440c01503800c103003a00101054800c10784035a550030790f9840a101044001d6000a00340005061007001026848401400f81d5800d075490a4400c160328403000d40240440400740c40003d019070090009004007541c09045816000c3d0b480c103260707400c0d400c2070f03c001d590105444000591403500106035440040c088055150f00781424002205100004a04078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301727455 1250 301726205 301726247
    0x6090f21050f15010503010b0d020d03030b0d0804030312110a020c04110d060b0405010201050c0a08010501030c140d050106080603070308030f130203030703020309032a0d020307170714030a03020607 87
    0x307118200903ca01d0030300d0307007292003066160b505040c00c0500351040308002c0d90007010002078410160752650350080a4641509000401039211000b007402c5800360b44010781303448400503002041580c0312081614044840004005003003020400301c400740f040c03414040042c1c0c4400d000700d6103841d05910958603141900d480b289806452071104080d100c15a0015441010200e0104100c7d40c081c044c6d103900812050805150284452014200300c00c18043d00741003564441c500b00f8a076000320628585000c03001c0c01c0c691140760300d00d13011004d070509001c0c00c0300248070f0790045001c0342000240700060720760198210b41141d543d44000b5a0015005114516030b0000003810405614240018100c00c0d010394040e581d5450b54500703062500c10382007132104020310a050081c901c80e10321001c2444a0000b00d5040d64506298000a03140079455041500c80030741103401c04144000c0000d111040b9480309800e22030066200f0200740d201d01704480094056000701d1300003203843d40314100081d401e01001f0004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301728705 1250 301727455 301727473
    0x11040c09092901020a080f0706022502030d050f07030e0310020705030d050705130504021602030d031d01060303020d081305060f0103060b0a051507050304030b070906090f2105 77
    0x5a420380d201880c800d006820340c440005030004400c1103a100707402c0c00713000030006640c40703546154040c4140322100c001000e010031440200089501100c66a102a40d0a00707a800c80f8000103030a240880d01080388a807003203001c4420810700400955a4105d0f2068000d420a489910151180000700e030140d68036020b002c083d90744040d00c17840034052480c000c100860311002c01541600480d41c02030070040a000b810b00a0740d182620300303080c490507a242507a015840e0100c2942e0415038a84100740294103000c0e0b4945401c2460385580851070800481c170302c4c50403548401045608a81e001c1c080580140c1001803145040c0d030103400c580760000b1040c00304a01c12079150300c030241407940a542ca8001c1110500c010403d0104d10300803081780c9501100c100010500d0a00017824006102d0070b0050945c8000c02d0036000c0c04028420b950046802c40c4c04681c0038a450391000b0520381d9680a040c0206190070710101d00a00e0602007203065850007035404000c2c0360441e01c80a07403890195021102d070720404001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301729955 1250 301728705 301728719
    0x2030a051b0a050726030418180b1b2a0316030503100501030b030a0618140102040305061f050913061b030e030a14070f02061605160311040c09 63
    0x9101e0606003d03002411400f400c0c404851400c0c1710b00300e1a49039821014818082298010044800703c8009161544034079940510180103000400014481007090200010500a0300e55235180704540014a000003100c1001114500d40110106204a025181188030803c4510f4072852031403024030084a0a02003100149214004001b108600045020062200d181c0c0a1500b0310702600090900f80801030100000ca5550004c004001c3e055503141c501e5489184980d00705e0410141d04044010740320000070040b01d020390307c5440200d405124880001d402a00c14250032022541e0002d942904240f4100c00c200301c000019103044040c3d610b400201000400e50311507484800c0c141750342248030a180345c1001d0111000072020a8094204000543c6840e80c000b6050b4031860140718400e40380c00c55030a0403660091050402074100400041032101d040480005c08002e0b0710850880c1c0389036a606400000910311440014411105c03101600d1300c924081d042002080003078540440703d542c1e60300c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301731205 1250 301729955 301729963
    0x6010501092d03051b0a05060c1b0609060a020f070b070f06050a0b0a060f02060702010203070203040e090705191e0510120e071701110a05030118020903072409030302030a051b 77
    0x100705885542c49110060503d0000b500c007e2030201e03105428000b6014a40d07031130705401144150100000c00d05280344d99200012b03900184800f41020342c0b55844c140001c1c1d0788440d40d0420200c24461403000050400541c5e045074940c40d4012102144600d0580d02c04020b8040036201341110364498441c07103203580b40c0c665040000c01c0c42c1d40d1a0000ca91040c071000c0c1c00e05201805030403c5900400c2000b0103150000100d03421a540212109034960f2101595814003c0503006154800c0d1946410601d00294441d1030003940d4200d149944040c0708011000307003c0000d0b10850703421856160341680100d0007841c901c1e9440035112000724011400b03c8215040401d075802c000420b0782007a0401851134400d200741c11211701e00800319403600031704440140282c0070521506211400307132490301c81c2007116070b01523800740b5002408540c401c5440d810502c4900e9403100f05542d036084405000301d61036104200e20421650140c000c0d5150590281044130590b21031050f4440d110440e26025041d140204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301732455 1250 301731205 301731223
    0x7030c0f0818040b041415060d090803180115090c0c140715050c0a02090405030d021207030b0316030206090a030c0b070606150e100e041a010206010501092d0305 71
    0x100c0400d501482d00e041004494001550038000d030301d030020103003a20180c200e65903001040e01071030048452045001450720312803006015100c5080009100400c181d51001d54040c2c01400c6a0429a88942852500301d0701030321800900500c0b0903100300302d405e85c0c55005041106e010300c0c0c591080c80040c3c0701c0300a4884c0808400406d603100c21402c0120070000c00d071882104071245050f51810200403186580c4561303400c406071107100070f200071070304101080007124035203190b48034207540719940c031b2407030307200074074007102c0c41c9021030b0804060038175a180c0401c01606645059109003950350541d02805240d4102100d500e030081e810200200100b0007440400005203c86022203a4400c0b5614001d010344141d90308c500f211002c0152008a50b940008141c0041d400a89000c4ca10081e0300d071045882c00c00456019400c40d00d03024544050180400140740646000c0c1c0848400e45da070b80d0b0046854100c00c0c8135541d8020340c0480c071054020030042c445c8a03201e4101d16003074415900c83d00c5403801c000300309c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301733705 1250 301732455 301732477
    0xf0f0d0603050a050a02040f0618050603150106090e060d050619020f180a0801060501090603050603100e25080c010c06021909080106090b1e0a0b030a0e011506020307030c0f08 77
    0x21100e1102145001d01235501d514214010070b00c801e52802c6a181c910b6005125032044d2651204002011030300d0420035146d032003200100009180d65030317002c06031004140c3c0c02040c8602d030030318002501c40d00300441050016a4030400802c0390b60b941c2c40704803440206400342400c07040c1c0c080016840d000040700242660155480300d04034111700150030481c0c421003584c440031140c0d0410400b0003140c1e0304010000c003168410f06020400303a4901e00000c0c04c20f1003451442d50300c1403270000ca00350b1400c2c00050b80d0110800030158072102414030006865210030500c201220303644450704071080d5501c2205000e0f40644030316005824183c031540c200130001c5015030040b001806806003000325030000d0103244001c24040c5001c010340140e50300807514003555441c42d9110b4000c15441c4441c0740c0c6801c42098024a250307001d1503107d003001b06c50f19014000c60480d0300c0096080041080c040200081e58130202c50344d50700158603003440b555080c1ca074000341980940e1062189200703080400d2010005000201c0c00e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301734955 1250 301733705 301733713
    0xc050406020105010524031305030d0b01260c0a020f030a0201090c090b01091403150c1803010513020d0812130209220204020c0a020310020702040e030f0f0d0603050a05 74
    0x9103840203086070030580c072440c8101c1d91980610043d6440c010307020130000c040201d032546d0b07580e514261202d40c00c2010000704144400540ea0500b580558007600030b040c4243d80d4000d20403000d0189260240c0c0e004013128a090100000c20b2240780c03e940100307403003031490060f64003906619503410b0640c1c1106401002503515031030310408210b69180303201e01400303c209007004503881c80000200100054001d5002c1e8060040c450095580c0400142d4079003100c02030400101c0c41c0c10800710f420b0381c1061000b40c1c40c3c0d0304900218042c6150600a5078070030b074054800000c0003029a0200190aa6900e806459041d0304000044c07203002c0100e4100c0c800c0f900b610b01e15841d00402e10511140040007000411807551a01e0780111a00114085948603a0101d03400b40c2c0390b2554120f05030601d41c2c40036000394180318000c601052410550064911107008507001c11801445807003058581c0325858480308107440411010b1841d076000d102034181c0030510800040c7c201e4030b80d40c616141c1028544180c445d984 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301736205 1250 301734955 301734959
    0x1805280c0f15050301032103090f06091502120c182e05250501150e0108010c08162a0503071b12080913181202031215130c0504 56
    0x1144102d400600b000518000303141d585552248800103044c3d0b000301c18648400d0099580544c0310fa08103040f0150007060502a00602c1e15002005250112044400c0071900641c84801d00041c03090f91030502003c2c2070000595188216035285610018134200b080d414510310380e45a444d43e2403000b520b01c1f0034500018402070103007070f80a040094940000c08020302000300070095100205058269554502a5000e84130545442405810f084032544541400e8540025100100e561000d0407584804001c0040c0c040d00750085030146170864015019040e00c04811a802e40318075141d000300d02000c101c00040311024070b141c0e051000006000c1e11241e20210351041881005102d998040c980c00310f164101c00e282800740e660030103010f10060a00b440c0410501110b46994070b4901c031240c48804100003410000c0180c6c15482086001919203201d8840c042411500005c12100209191140c01903903903a58108409a19503a5081c036412201050039500020207901812000e45002e4031007644480c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301737455 1250 301736205 301736219
    0x50f0405060f041212110f21010308030417190c030f0804050601090e190309030308090115090e1f0219170705090a1203030b041805280c0f 61
    0x4007002c0c282c82c510003041814440010002009103220250320300b0300b190100500c0343c00300000d00155041603e501c1000072081e000c41440402030440180c41141d80c1d510a01003440d103640c401090000501001081000c54003013000c25023050074501101d080030b4940341e141c611052000301031450480200d10b8090345007007019000310210001e4501807406804c20300c3c06407243e80c0e07a1070040c030032456050756620a0720388040007481883d42c02c000859002064005c00c0c41e00410080282c4400d03000281207002245e01800e041c0101c2a030300854a040901d41401c042200006006810702c04031903100701e0510f0810208109180f000b0310300d0806005844445070300c01c049110514003a00020050300340c40c1d0504400384000300302d8100285150007038172042100049a003015071074020240c841c1110004400309541500712000d8450245c030248241c000b0130742604440c500300f000c01800c0c0c0c0c10440400703200e81600c0701100d031100c540164043c01c80d8082d8440095150b215000360041c584541006c0c03103c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301738705 1250 301737455 301737463
    0xf0114061c05010611010903450509090619150e0717011413050612060a0e010609020a1710051905030609030c0304060c050304170607020d090f0504050613050f0405 72
    0x640d4514000740301c803600d150703001082000e0000c02402940c5010500510010f50101441034042200000542a240e0000d880c27000d803c09102e01c5105441d0b1100082b41448081075007130181141c1c140c035080c07805e4554811000342c41c04200540b80454403e900140c0f00440715042e50180c50b158441c02403004011000085124050b080003044203d090140000c13521010040b100700240f91100081546468000034419030f03442178058983e101d99014481c1241c003560040c9a00303c5800000c201007551004604143e0040d040c504011402c1d41c80039142403010b600013aa4001190342440100a440d9030015000c00e60360300400c00c1e070300c0c2109000c2c8103030b0508100300764024000074001c506042107490030720b0b903910460154100700841902040200714080003034801030701c111441c440510144100640e503492080390060010b200c0c40c007100c08074034000c083d1601540e80d01c40711484028240010301001e000003900094020f5102d0301c1c4818080f840d07114050280e100340c4550082400c00341401d0b450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301739955 1250 301738705 301738727
    0x60f0307080a0b090105030c0409150501061716051603090b1603030b030309060306100c05030307080403030c09061e050408030a090f06080c07060f0f060e01060f03050f0114061c050106 81
    0x11350600d401841556800140750046d135070f084601007640c054900d80807800240f051f40c4030b4100342c105000841e100c4c1e040714000d000c250000c25000400c0c1c0e00e94400c04009820001d16502144d800c0244101080c8450302386200d99000381014440540c0d00c4400401035030046070700c0440020f566561408265141c01030285000c0c0403401581450110703170000d0254400545403a01c5060048039902d107031806114010070b0389804c50240d988900e00004040e24401e0700b221708800013031420300d8900d40301e405149440c0913030f4a44d607241c1c0c00c51603503460580c0e078080321340888400b403190901000402c400c04000400f41503409580324030031107140645520100180340c0000e000e210b032160820038400000701c01d903020b580d0007680226031150310000210050200388002c1845606007800895030800940314241210b45654860414681100d421412200d0a540135008038400b2030040296440784d440805038041b0080041d40f600d52071b2080e0440500c6c05020900559072035000402619812001c0c4d4a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301741205 1250 301739955 301739959
    0x7080c10020318120f010c050315220e070b0d060602010e03041a0a0c1401060611010b09040209060f10020c010f030216021302040f030b0405100605030a0809060f0307080a0b 76
    0x410300fa5a044803044880e210074550f030007104040c0f80d030910014100102400700c28010000c0081c22801c0c0f000800356801140c071046590183d600b0300764182081881e08035414011202170746150302012011002d0410304861807000d01c903404003c02c100400d90000c2c031680600c0720002445c2da00d07240000c0d0a503500e60f02060307407c0c2c00c00d1208020b451b031904904500401503071101503807404621401d459103140a100034040082e8088840e01c8080150302013421ba50030780d1902922100c5401d105070a9500c1c401b0b000d40c100c1c038500041001814040c2160350131005c01410f200e800358030b510104078000e50300103c07400142e20161310310351656001002c200b55607009160035480c10780004003018450000c0b11000340244103001222884c1c0081e6410b42d406444000e0145540310365134208001c82c06015078098400d030003180602447c0340514401d420440d100035001d04510714140d212010542c00005020b03802035030800180c2c1c400394094008502c28412511050703810305050540c40304442c04121454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301742455 1250 301741205 301741207
    0xc010504020a170a0f0501060902030711062805060409020306100306111306080901060305010e070e01051801061202070209010e0f07180b0c070e040602041701090c06030509010e07080c100203 84
    0x3d203150750203d100e48049400c000205031440f8907103007290041c0083d50250841d0fa2011090042103940405c0c0001110340d800101c2d403071500c0c1c61040a80c001d400060040d502c0c4080c840daa0101450703500001c0c1d02a000810000708050a80c001c01c1c1000e1044990000101c540d05040c800c10001c6d01c652070100c110f01400c9810303c4000b01c9054003c02c0302d4010389052181c02c0000a0f41c010003500003001440d4840000c0c030403006100e40803641c54103140200c00240101800104081c1042050041d0744901020402d1059107000400c0d2141c2044005030380d01e8680810407040941c80d0251014000c08809500055500e42940b030000e0750200076216004110325541000c29001d42c034450142500c819034695940c9240760b528142c60a00f56501110440b2156000c120030312506a000e00b04540100d11070a65600150a24508860a2410060030b40400302424040a44a07500150340000c08200000b1180c903010080c5d444c007007650340801010f40c0104000f0596050101805801180c1c42c0011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301743705 1250 301742455 301742489
    0x305070608090a06020702030f1f1a0a0b0903070e0f010f3c030c080f010510060206010b0d0902060c0f010e030705071208130b0904110322080c030c010504020a 70
    0x2078480e0440c0c640540f404da00410b40a0541d40c0c10700078103444500361400c645030134001c800b02c1e5440500d0341c051060118682382d0081348110040380c106088040042060207614200340c0030038210340000700c0030b41d09403181e4140484c2110300e6001440c0640c4c40403564400c40d41c945445042895815001103c079640504910700810703590200c0c090b01e681040b021103106005042d4002c1c0c1c01001030780013511685510100180e9148086280407600940708001d010581ea5295558243c0d00144180e80060340070600400c441458000581403819501c1004100c0030f0480e0009040b94100e0340c001c40c0709404c55144d004020109120304c05c444000080510b0070440c0c0f507240c564480e41503100f59000c107220802c09004008103030741250b0b402080c00d150048806e1712902500c2150b009a01e466004924240750310f01408481001d032486418403054040c051b82031b02000c14020300c03104030b00b01e078404020b00c61104040c50070b00140101d0001000001854a014010400741c01465409030500c11402a20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301744955 1250 301743705 301743721
    0x409020619021908090301110412140a0c0803090a0504050c07060b04090804060801030b0717070e03101802041a01020a1709091501031505061c240305070608 69
    0x35105041035008552594206009003070f801e000c200003a9000320003c64818004000303041015090014080c0c008001134103020320000c0e49032045000700b841c050b0f1418080400218104a032588220501d41134078031001c10b642c1d40f864801c2254120724056000800d0280d040d041c5001040e0041204880901190170134984800c0782d489503402c00b0700020384941d0200c2945d00c0e107402812503164820011941c1d15540c1c280188281d81c00c0c0030440310b5001a8010507140da01c2030025051030380f21044007144a4032001c82c1901c02c01c6100303000c550103005000900b44240c003284107003200300c080041e420008001c81c1c410842282c00c2041030800c02501207030000b41a0364001062402c040e402031074844060880140c4d94414003600c400a64040009010004801d03100c40e4030041c0b8000c03c0e00c0c2800081ca18580e580c40d0303d5001e01485410a0050200415101e50300b01140115000300c1000035101c081c42c0c1410300d221000c08103c410310088403504104010381000b0000090003030303141042050810b602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301746205 1250 301744955 301744957
    0x30f1103061b071106210a0207030f1b1403030a0f02040e06040510081b09060102011a19030c14010f05040e1b270109090902010504050405090313030c031104090206 72
    0x1c402004140c04609801000b88501a4032903150000b031402c0e440d40c40c900c0781002c01c1b041a80c0e404030070340d00c40d10102d030010340d00b4000e503000f04c5c0d4103449001c101c16042c60708407468007010804040301060f03400510003203035800312908500400c503800740d9664605000741d5002e484100988585051040108114a4100c00072103030b0080000c5038049403c0e180e5238600031499500e0b40100701036008038003201e9688400d18140c00b043c510295180011644d43d200168200d070720b00030003c0411094900c501003240b41100e11016005d030100031b5008042d071070ba01d606480704090303004040500300082c0c15680d6980c21140180c1d000c10146420b03881d09003050000c46469002070941140c2030b039036030710b03003005561244140c0d050200c002a010144071b6080e404229108003000e044c0380130640d0000c010503045070354011041101d4042c0c4440780790a03c0e05050200812004006449500090000290201007825140001d600a03500d00f40701ca030550510540300c02030005001e201320301c1c1031b1414006845a41c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301747455 1250 301746205 301746241
    0x6060f110a0602090a26160302091321020a0b1018020a0507150b01200a0209061f0c1518060c090308031003060b04052815030f110306 59
    0x41070140e20303449000041450f0079017540181c1884200c541c00000d80113505003415107640904421150fa12561141800d414040c1d80400303500311290300c0010b424846c003815034420081c0705815150108118003103d01042011141c41d40c0144c00c954444c82c1480240000c00c2d411940080040b00ca292400541c1100319500080070401c80d90003241080c85240144140c40060340c02620000400600c040d4003002042e60040032408180001c944250b841447d18805101104040080c00d441c203c507001c100074414020000ca0b0311030300f04100c440001d0144511303070114a1540c5c0710111000018580014508030641c840301c4030b41e1500311140580030340c05200046281e0070500014400c103a0200440f0300040641010b0045240041848480480501c1c8481200d004080030007281582c0360402c400d4036425115598018440000c0c1180a00f0182034804403081c024400602c881c0c510043e41c5410100b54819200024907118103010300c20402103404444804401034030740e500d0101300d0381448886203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301748705 1250 301747455 301747463
    0x30c070515120703050a050907033507080417060f0103080a03021207090f080304050604060e0a08070801361704050904060e010b030307080304021c02120106060f110a 73
    0xc1d580380d441c120085800c495014048030601c850350f14210310041c2c0904004c1d958016464071345400214030035404595442074951041d0110a440e917012111a20302d120301840300f03000003203820640803130261440140a498401c1c0410b548445c13074520003004881c900000042250040010852009882580181540d501c1002c02e0b8440c180c2142c01c600038050701c101014001080c5060040c0540c20100550884503140c01b8003c600740c5a480060300ca000754450f45130441424001800721502a001d40d0414810207000d0540e040d0b40d50032180d103496040e0b80003c038165980c9c00b010300703000104499042124020305055844807011002080001c040d4000a0300350078101d1018040d1040041c11100204001011540c003170400b810580018003915888000030b62034409080860b09010003030f2418140c00101190942e80d23160284000003480d82000f0140840c40c41d002030042c4c1c1d5401d20250107000c14000060300c82c0c202040605003400d440580b40601605c2d0110f00c0e983c4c0d9000a103268000d0740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301749955 1250 301748705 301748719
    0x3140f01050618061b070603020703080c03060d050a0602090103200702100e2115070203160501090602030c07060f05090a0326011e241b151d030c0705 66
    0x5902a850000071a1040b20f41e032104000401101201720380c0100c00340c812610f01510700b0541c0d540c81c05c2c1c0880c407840c80300401080b41400044c6e40c20340070b10059544440044e1000301d2040315035884500302952540100d6203d640801c801c1c009584c1442100d4050780905c070814106c200f110840b1106014050000b071255404054002e0b80300d100c0c20b24a07400320806000c0c07012208804a180c8810200c8800b0042e4074410b0306a02c0d504000c010f4800c0c4d002d41c0003a0013940c40d207010781007a04c209c18075502040e92b2940d00c1e001c9101c0094480d10040d03104030f01c829465601c07a2402d00d000e40642c2c11890074044a641400140010341c0c40203d944811030307a05050807011072401a4401c04400c800040c0c0750130803800740b03000040d40d03499030982c0700940310104000601c0c2c948404a841c0404490312000780340103490001e0b08200c50054034881c2000c0354482c032800240d2002e540b0b115030600440c000b04460b83c0c580600c051268000810390702524100c0380607504000c440441c490342d0340303403500c10144601c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301751205 1250 301749955 301749967
    0x2a0f030c0721020f1c081605070c060f020c0a080c1905040c1806031104171c05040815010b030411180406020318030717030a0e030d06030303140f010506 67
    0x1850307034108030394040100240058040d1440d00a501e400741d1428008071405101c5c51820070744208142011107181e503886280003502c5150030303d41c4050000f48030700284103003084182c020401c254403200c028095170f0703110381d001066514004d04005041c4585402000000360030311110348003080e20346648400343c0718048007848042c3e104404600940c070958000d0318150001c040e0300e03030140003507004c03080d01800e00a01d81d076111801c5044802809100038000000d020038850180800100c0c01c8030800e003021103401e8903080010360b5004441000384404034400240c2044013003404d001001005040120074041580350150300100d600c030040004215800c00e020b041180e0f6101c1160b1400c41503101d29021207440e00e0b181c01002540140c0d07a01074070507850f1010b110703584800412101c1969009080040350585a820ba000c203400142c01541203903150f8481c00c00390402040580401e88468901148a5142d400c0c06421244107620252102c170001013000303c00700502e48024111a0140c626640d143c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301752455 1250 301751205 301751213
    0xc08183c04180605070905090403020613081207091e0807031403120a050a1a030c1e030f03071403130605090103090609060c0e01020f191104052a0f030c07 68
    0x1c0320100348110011880040b03402030180e294030003440348102c2d84408110945501c100400d580d400c80d40100144c2c00280041c1d20b4408134081304484612550b107c038102284c80500c06a200f00442d107000000300f00c110204011000448803145e1900c100c08807165041c01c0004030354a41403180405413101d0602040c03139036030001c10412038411200226814001d410f00c90080c80180000352080e81c0d8417810302c040100a85128150f90004203401002001910170207814044011a911b8540743e40b001200799207100358034140840b501d2407014801455884c9080e183c4016503181c40702c0400040d41c410b00007034903900b07041c44038403041d500642400c645070200e0304012005407014400c0103040f079060420640420134207812141c81800b0340e49603c4140030104004a80c1d03119401071440c13041c2e00c030f00e540d09004050344000d13641a50107403010b44441d04403c0e01250580350207480311003465021360300700024200442e542e08508600080e03500c3c949000311458030b0712800007a0844541244c0051214104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301753705 1250 301752455 301752461
    0x30803040b0a15121b0602030a09050411090112060b030c09030f0a020f090c0c0109120e01020c010801120206070b16170105221d0105090706050909040809010c08183c04 74
    0x550031174902042203a803a114001d45941040c241c0c0004100c120b04041100e140070f0046a101038142c0c4545410700042c600110b644c107198000c40c4800366990b50303000c942542c11200440c41003e0702401d0a6980b4100001c1c0340c52700c1469285403a554103c40b0a42e00141c0d81c11081c80400b01d01110326410a8aa81c0e05845940c0f00740403040103107601e8034444404000b4030000d6550b55410a40752101c80d034951000581e120b0b042101100e000424000050040c003514012000d80d41d4000b6040c1420040c1d5a901c9050060060350484070441d150a5040300d49035202130600c01403000c41030f80c01c0103035140501081c0d00000c20150302e0710065000d030105408503c903a00540c2d0342c2c806074041c09808841903558a000741000d07113003503115015850780401c4040c0141c089400103400074002c0c40c010382d01d50b194600035800450307080c0c1c10001c0b1099047c002c22940310140122107160351450141e00e00700801c2110300c8607031208222424034054044800c12a21188020303d07060744890341400340c0d9100d030026000b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301754955 1250 301753705 301753733
    0x2040e06060927070f0e09041e02040603111c0302060a020313151d0a0816030e060304111c02180411060a031b020c030d0c02010e0604030803040b0a1512 67
    0xa00f041d50f201c4004026440b070711030190150340c6800c0d9041200305412030302da201826a041d000800540071070b0024000b910f401d850350000042c0b00e505000c0c10b50002d070175941c0c240d005580d11a1903902c0b12042d490300e000b01d10b0004540450002c28210365035406519800c00400c203004150380800010030703141c02038046801d10390b44803415440303d0443c9103c40b0020034003445904180c6a00301200c0700c0074040003038128642600b00803001d0809158850650300b840c49032100703c081095856001b04941c4070301014501840c4280840301c0081c8001c0d0501c980c200c03180c0340020060003044144005070b222000d000d10700c407011001504c155603403800d00e02c1c48803070310505007900000d001074070b5099554140d201c4030003140e00340d03820b00e401210b1840880e0384884842100341e054200f440e140c1851405204086615841030410b020852140320008100d9002548144c0b00c40000004000400101d5201c895100c044800d00300a1641c034a1800d0903030b92110700911707100c6500306035100e003031150041100c0c00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301756205 1250 301754955 301754989
    0x6011403070b0403060905010e06091203150307081506090601050706020c010603151d03040503120a030e0304030605092b0e01020a020301150f09020a1707050712050414030102040e060609 82
    0x41c1e0f0740d03030740e24150700101742c48441a0380c0c3c0e519107803a0614070700c00450114054003112009201a10001c007444001d07a201801118031004a68000303501070300c091011314010f1641d0b401030b010480d801ea0504480c0c2c5d0300200078522410100c0c080103100c0c0c2c0c014040d55003d03904a50010b898180724203080b030043c5003917040500030020880c2e000c07040d815190002c0f4040d018860004030700704290780403a03560780100c0c000c0380e5058000c1c400d2080b11010250103840c00410350701d0085a42c4007280300c42da080d6070064001307076031003a299010850304c4230040010320030018185040302e00318500460a803401c8103050032004200480040c203140640c0c42003201e81d500c260024001c012000f001480841101c1a42c810f0120014514400141445081c429102c440e03035142c076020440d88042258000241c0014200018004284850b601260300c080e0f084030013012986a1540d0f031800c00345484142c40b04120054400d030300402080c4101014402425000801958000c0d160f440b00070001da40400b10480400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301757455 1250 301756205 301756207
    0xa03030c02010c200f01030203010320212a0a050111030d0e0d030e06041104230f060108090f0316080405030d030c0806040501060804030c052e0e010e06011403070b 72
    0x281818104c48060301c0040d81220800300c21078610740190b050340424440640a401940c01d03428030620b248800c0100c2c420000c100d541030b031781840024440d0808900381403141d03038455880c503c11058920342e4442c0384511800c48120034800100042d00030070003030058604004480c2000b0002c0101002610441060030505108140181e00340300d90321100c0b00440b8002a04040184801007001704040b40151303002070049414094000c28400a098241c0517500c500d44180c08001702d080f45501154041d10b481100007526040940c00101501006030006403035800826040814600010803140b4180612894080800b0309041c00301c0303140583d030702042c1c050041c0f2652911296140c0c1c4101c40a60b1b00c0d44461000e512000180800ca820900885010502010108001c40d015814001003980b240084458401400c800901090364a06004c03070f00703150790090b4503038007803a50058a0450151000070420303071300745804085d9234440605c90210140002c1442e80e00e9600d00b80803c201401e4504066 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301758705 1250 301757455 301757483
    0x1416230a0e04050c0a170c2a010515031e0102130e0403140f0f160615030b01090c20010b06040308040504180804060f0306030c0b1b0c0a03030c02010c 66
    0x1e0409064941c07140d01c507620380000501e5a0116505907103080c07049a507444c0540c10082c20900725442c0c094070400c440c0b00700740412101020010000c45940340410182a43d54a0800000d803c1d150050810b4080c210381c10084012a180001c000302c034810704140c002d0201400d0741c00c0c240203201c0d011089200b03031101c0c00c0101d030303641e920300890703014600c650f07182c0540d000c081420311032034091151307580c501d031400300100710100c664030300a408250400099420550a81e554010845040001d2103d190500e11800c01c24000d285141600500080d2020b000c0d000c8078140c000c00e00b00c2c1d61001c1c80c101c102103d0f070a205400003540001c610740300240500e070b6070300d84074203000005801521030280308904100c2c5903c11419079450084616500c030032038508050500d402603401c04810030403a010507913a2840080414030804014004124017100659280300d80070904241c052801c404560540c8140100600c1c0d440301700323180088941514011540e820640300480e0701c000140c502500000d07401e114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301759955 1250 301758705 301758707
    0x1051c0908070b090d02030403080901030203091623120d08090a0b07020c0f0f090103120c1502030106080601090842010816030b01091814010506041416230a 69
    0xd55001d654018101ca80102c02031170700320fa4a01c2980070041501c4001d11407268194081c0c0c01540d0811a80c00c1501d09030300140107410401c1800b94042454100c040354a4810580544c00a4031000c40980701726024013031184031207039101e8103444803400700070500c400580904014461200c0302c0d40c0c0a50705074403d06100380000e585030f4484400c02d1065031340341e0b420344461502d100000c0550a02400301c0742283c2c80d5444100c04001d60944410a008414440d50001343d41c0b60381080407001076039001601c1e54104a4010300a0100030100340c14045a84002e2090020005100d150007403c46c01c4a801c580c006a811180150703031984541c0441c500c04420442d5105412100d41070380d0f0341c00d0442d40c001c140c41c20548500340709407101030035040c80d1400600c041017440d007284502e264410010101801e16a8668482d001e00500941169644409005c2d103450607014403048002e0400c0242a6421b21040441c00c0c40040d90b502010300040a82205000104441940700007c2c0348480076220038005034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301761205 1250 301759955 301759973
    0x915030d03020c0607051614100603080d06090207080f03040f0807030309050c030106350d08100f03030f030b04090b0903130f1212090905010f0815040201051c090807 73
    0x100f0400c85000740ea0008801610031010b0301c03804400b070022240641c4042d1500404580c00319100b840501a06055a8a81041d40901030040d841001501d41c0d8041003401d900449440c0d07000241c00070300405c64080450070210075551054200d01c01c0315540c0e204c03480c0120008503018001003281c030001c45e0740803e060b015480031000b140a48150340c400b812031010107003240e20f940030300c5084e1010803003142c41d1318410400b00c00042502613000d091940303485d000300e03107481c0410005400103449a001c01014ae058840d00d01c0080031601010105241596800303812952116401e004040e6034100c12245c50f6115003140200c107810a208551a05021a03803549a9000c401d4620060f659400e0015400c00c03142c0f92401145e02e00c00803d01c0b00744c00ca030b070348075814100e4030079010030844036000102e0440d8543c8161030007420b02140e40c50010b80350a107040e0070501d50b202c1c0340d070550540c0c504010250742c004c4200c9140280681c1d1510f0203d40740c2070302e10001e18503110b024104d05804a40a0100700b4004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301762455 1250 301761205 301761217
    0x260706090c0501031b0503180c0a09021c1503030c0f020a09022502090411180901020703030b0316050423131103070b04060c060f181b0506090915030d0302 68
    0x81c2e030500c14145c0010f01d200c1c0d030b0800d40c110719002850402c0000c048030070b01c04c00040ba0204a10550740310b40414800619010a940c012001d03982c1d0001e0528906806400c100446018180051009402e500040d50104450344409428012224005820405030310310710500c603a4010003446400b502d6038070316002900280c09005820f40007240710400d80c0c21100031a0303d003075401008ad00c1a551541d8a01080d28050480103400c003e902d04110840c0a0041e84d031441211201c0c001600c0f1401303400d00506176101d9402050090701302c1f02d40c1d44c0802d500d00c09508142d82d0144c4005c030b00d689500b104501c00000d0721079043d02c91640c2d00c050243d1200c42d50b00003850640282c10340840c044241c81010380321102c40c440c4a409000c20042040454041c9159021030340c01080000f1708440c030004c4c801c0c141d81710136103400d0240215034409030801942100340d0206240403000e80f41468244000306442c0e1180c440b2030b5100c1c205040c0003605201c00e4003034004c1150f8000e0141c800d42c2c0d003c4030700580650011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301763705 1250 301762455 301762457
    0x20403150f0605010c110f01050702030a0b04020f0a0803181c0804240203071205040f080d0f030b2202090a0611010c08071d0a0b0f0703110307260706090c0501 70
    0x100c0000e1030b600c117003100b01955400502081c0310ba0004010480c40040c00307291641400f4040c41440b0143e50140070500039240030300c1140c0e81c280340510400039914410781142d48104103411041c891645d00100355038014004600350301200c070304080000c00042d050800741841c4502c50030000204403d40028008659004c500352540c03501d01000d0900c00440780c050000160b106000e0000070540c08060450b00c00032500302140307480d4907034070041403481082d0000395990384640f04151310160300c412219a4400d4918003000340c919010006000840006061024940c4540c09150080340301c1c2d049409a110080c0381000703003650340101038414520201407502c0d1b54a040300d44000503000381a800c2c032400280d9949020100b140880021440c542140e076904403104a501080c82c2c0b0700e0000518014600d420b403070b5125031552500802219040311100041d4000348401b81c0095681c04140003034050803903030b64204000b804004111400380303060242190342030202c80014002100002d80c255182 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301764955 1250 301763705 301763711
    0x4030c2306241005030601050f0f030a061d0103020307051201060e011e08151308160605160c1109250c060b060304020f04050c09120705120a030f030c03020403150f 72
    0x148420003c1400e80800088041001000010420741c4074800400c3c3c040c0d85810400d062402005652000760000c59000300070315070b114002c0c815170020303004030300d108084082540c04960650f40429180c540c18132500d401001d5004206c030328102c00790050000f0708441c0d440c000240da583e6120301c1e0003041318150540b500041c0c8102281194010480f05030a01104542d4201c07600c1d041c0f0740c40f44040304038006450401c81409214940314140380e8072450580a1301c0040355505200d51550484220503844400388020b900c2c0355070020b0b403075410003090400c0444885c049036881103c00c10941080140040240c11035048044625800c102d040301194080c1070308208860126050101c03d100c1550082d60000a84c004a402440e09800081e8000520300e001c034208049030b004142008908080960960040ca1083c0300e40c1c10b002d9001d108001e02440200000c8502d0b86000e050010342611403c01c050711580c2d00720885002e501218003d650201d401c41800d01440080740060004549c50191710341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301766205 1250 301764955 301765021
    0xa050601090503030a0f0507020402070b040c030209010803070c120c050d080304051204062f0d0503040501111c0b04060509090102070302060703060b04170709090f050601080604030c2306 82
    0x40001c03d64000c128142c5800d1b210640016094440c0e42010804980c0702d9020042e801c005121300c1c134100d00270b81c482c00c1c844000f24154810020f208005070001d8600358814880c2030040b07034001107100202c1d25010454040500141084840c168494100035080100c6605150070404200300651046004505803122044881c1e00700c5803074800c1c1e107d0310f4009030382000c4046035900107403070070741d050002c0b510081c68020302580403e0400c503501c440900814408001c010a1041c01e00610400480c9950018982040c1d205031007810500d00070150181956405031110b1a11254040c1010340801891202e8074940349680c1c501075441200200d005000300408501400e019000b01e9080c0c820400410703040600b00581000300a810b90385100c0148610300000900816522403d00414020002c0c1a1003403081d0411500e00f01041c0e1200f87c15522503002c00c404607901c500c401401540c40341010314658088480d1400640d0030000b101024010041844464610109503e030404600121428042c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301767455 1250 301766205 301766209
    0x50f04030b25081003030e0409060c030917040302030601060c0c08011416020c0a0b0a03020f1935070c050607081e0402060f0a4107050a080c10050a0506010905 70
    0x5a00703a404911214407000c0a000103401041003076000003008d000000c520400792206015145100041c1000c80d0b40c4620b00000c0c02107a030760103030400c0307550368078946064a1580420340e210414410b039010010034003413180412507840c88036001040c07110001d202c21060611a03880c1000c064800c140300500d00d4829005080c000724080946180c002c00d52036030315140c405040f83d240e00240510b81010b90800c03400322002d941c40c010b40302e8400400300c5089858000c0c0806000b02d082c0a10508407866442c0000c01000d000414400641070211000d108940711071074180d965182d010002040d60040804200c03105a000450a1040548454414015014103694a45070500740e0300070750031001c100301d81c11100c090140108030702c01007450905c003104e16041c0c0701e044008131644030003000000300d643c2203842d412801c1e40e00b18082800910600e04802595540e90700c1d00d202070000d04000e0302246080b170f21401440801e000d02d07042c3c1c50034407403858001c0c40341c0020281245d056010580d000300100390380c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301768705 1250 301767455 301767467
    0x803060a08010b09061302090a080604051509060601050a0e210d05041a030403020a051002070b060103050114040b010306050d061d0a02060a0c080f12180f0a03050f04030b25 76
    0x240ea00580038404c5034803007805005c000c1c0031005808044603000c1001818a07114014880020032040c0c0103000c2c14103061520a00307141c07199151140c02a0303001d00740848002c0124003e5005102420150340c1c51f031a080e400e88100d00128842d9a000c030843c890f480000301d44a14410340400100255680d600f41d101041e61103010394005c990b60143c046c01886d040c114000025034029009004075003c0200c0d80d41c49500e4400c0390b5501d10103098000c5401010400d0a580f0a60001824241404658103043c801a1114101307030381d081c030031381e2600c00201c0543d010764051009003801400b065844041810a04007810f4a24640b0841449200e2036031003e4030007086001d8155401401103282a4010404903604030040300306503145401001006030210350329000b0418943c1480b6103050398501700d02490104401c01591380d0850304010365000c10309001082c0146050b43c581000c41c0c80f4600400068254016900010110700d01c03003042c0240620302e0307490440320003181d907149110072110f81c0d4100c0350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301769955 1250 301768705 301768721
    0x90d0305070507020f030c090405030a0201051005150703030b100c0b01050f0607080f04090216030e01020607022503020307030f0b0c0f0a030515041b09050109030c0510050c030301030803060a0801 86
    0x742c0c1070000100510f070080440f151381c41d0040484001022003000190514405d880c01c40329a4000251000c00540a000e413985c8100368a140c02811407034000807070b854040282c080c0c00314000001d41c074801c05019038804c0e0a4604d014050794407070143d40101034030f280031312842035800c04140700002403280350be142d6807030400b04042c10190800eaa15500c2c1c00d4240c201403000340b82210180404244e442091000e00498a402907105110101e03900b00548110303020500c450454000b2404c218407a034000945540c0c1d041c0b070503c6861405680c207018030745200c05d50002541409032501c00010f204d410340701080503d00640028400e500e4070124201c81d0b220714034901c0c036066024058803400c01c3c042d0340047d90100344040b00c18804400c0d9000601210000b003200000c04140c01d4404507502d50146022014110a0070441d89242c21a1039003000709403540704540c4070b041d05618403800346d8400c00c1640ca000d120081240e0b00c03540c4070302e480fa410760021030f00c0702e0064071034a2000075444c005010343c0300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301771205 1250 301769955 301769957
    0xf12090906140f1207092a050a0815030106080f100b0102060702100c0302071b080706110304031b08060403020304061404052421011401110714010c0b0708090d030507 73
    0x2c410f0f03590600307100c1c1d004400c00201c030b62070042400c00501202140500100364107085d0090081407861800a280b260701c243c2e01b98104001880006510303504800c034a904004450000364005400c03030002405004c80d50060302441c060207102c8402c074000052514400007414006020060021004a9540a0848451700168030001040c040d0600b280d02550140040e0300c5c02625020365601e64040300c4d01403280d213040820040034104100d02d42402044050701052404e0505598441e02d0b4a40da402140800b4201c80b1005010380e040385140c1850100605000003501c105103003509010b910f90300644600c10200c0c4e0740c01645aa035403040d4007140c05440f0014951400703204000c811041c141c10141d4907a1841004000440007040d00083c0148583c001460310226517041508904000c01148145414056901c20400040502107048801d484050055002403000c1400403142c68116003000f9000382c03205802d01c80c14a0340030300313114480c1c0c41c030360200d40d42944072272821011a40c045503000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301772455 1250 301771205 301771219
    0x8030412092309011a220e0c070c240f0309081914040b040611190308041e050303010504020702041401090203040317060a05010c0f1209090614 63
    0x1a000444855022000ca11245010300c040e0303450700e86a07201010900140d11203202c903641d41d400145441c4a055000d030424016030714100410505100090040441c40007480c0c0c86002505802800300c08404020842c640009410b4101103064500039442a8000e942c8007040305e40c08150842d000c12100d4000c40742d94401c014907078280008490143c0103140d410101921125220040388684010b800d5980103123000c2103400d04124800303007200c612400280b01062040c4408c2044034990800c0e58201c0d032940c203040030400c940c007036803900742049040c212901380304041d403040605a00102c0c1c81e1162784208070850b4590700564114089103043c03240108190b00c204014402410290081c22115101500c04120760b444c2c0f005e01c2aa0741c50903040310081c25404000c0000707069000011180104030359524a100e0300b0124003044030300806e401880d06210324030312904101b0240700d86040b00d054012542c99440d40c0704903001003800041d0b12640305110300b00000030501311800014007401c007070010158 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301773705 1250 301772455 301772461
    0x70b0103320d111507030213090504020d1113060b091002030306130e030715020c061303080103230d031e06060c0f080403170a0f05090f04050a021b01020c0c0d0803 72
    0x440d10846a0f007038140c094012010303488141e6140d01049409214151405a110249501e081000c0042070b80911480707404c2c4814800540c485492071070099401004503c0d45032040004070300c10000c8080c40d400102c0c41d002d4001107551190000d8140403000706c03000d040b00f100310035040b69a40801d441d0780c2d5001551590001112030240e00240c5c10381c80c2d41041e2810405991111030081e03883c21240350b0299000134101c0d40b40300d028003509030300c042c01803242d145009030750701c00401c95101400002d1034614a001e0003c454030040e200c05051080300012541c9840f5007101c001c0c06029043d850b892786601240c120f00d210440c80c000e800541e40c0982d9420399845131500c2722414140f10300c8050340e000304100300100204181d61074003268901001015980d901a880c0000c0240003290300e45010420144842d10b92a42d808a00c0490200100c8022030b180e10740d11259002886424131014800a03e0307100429807030010740103043e0340203480040d1500284030200388444450420030043c0960410000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301774955 1250 301773705 301773707
    0xd080103020916030b10080f010819060e03040b041d01090605030d03110c03120906060a0f0501110c03031305010815100813061d16051e06070b0103320d 67
    0xc8078940c0350644c43d010515054405c0031400c03004540c0000c000284070001006001c54400e80702600400c5100000c16100b50003081581000980c0040141070b183c41c0e0b04031751800c0c8810000e40f40613084030103034640d0b62503540361070344041c10907881000840c2041e80c000044149140c41800c0c111100580503016a00d80d1400c1140213000301241031248501c1400f540c20441c6003080901310b50703c010780c01c144042c00c1c0031300e00710b00c2c10304010811889544e0100301804201d091190100c101e440c2030901014104007281c0c040c0c01c0562810340700d90544030100d00c0140d007800080c40102204c1003a242c041041e154048860310815a499a1700e402008202e4040c0072588a54601507020b00303402c84144041c4590360740c001c207484010b6a841c1401883c80c0300d4071b0b242c10f03040c021900b00649160b0b020055914200114000d03081000001d041d41c1261400c2807100d0f15014110b41e24568450521401581c4a00d041075100300070b070603440003007808002c055a801070301032421014003658074001d003038015000c88 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301776205 1250 301774955 301774981
    0x105220c0306021206120a120f0c120e121501060c0f0507060801150807020a02010e01120203180706020f06190f1404060b0f010516170406050c0d0801030209 69
    0x140440366515500e4000000c5205032015015802855a0100490030b0000130850801650190b490319030304004101c4000444d01a000e04170714926003402519040300007002d54032404a0700307020300541c140d444003032607041e0b0000e099060340e003080b0741150918010129265039440d20f09c4505840f88542001404942e000c0c940c07410030240300306115a18100b0650310076040503099802000461a00401448241510700600103114042d1510003028504060f009644450b1414007030705000c40074039500b070306e039201ea80c800040c1c8088000c25952402c00f070300d40c09244068512110001e0144440c0030400354400301700b00c2100e0303034b60f0402800d094868141c4854034504081103c600c40d07964009501000d2114003900c1a1401d22b114030003101d1903e07060080c19101021141c6116458915052449a03040400c0d22a2540b02e1841441c404a5034a802401086603181c080d1002401090004115a110006003841c8449906680952400036000d8401420a000c000c1d8040c0b4498001118101021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301777455 1250 301776205 301776271
    0xc140c1305150303041706010506180f040e03130e09030309030d2a0c0b09030903070303080915090709060e0606040302040b19180b030601060e0105031003170a110105 73
    0x2001d0034048803900c2c0042d180d507000d90321008520000746503941c1c00440611086005041c142d8441d0724280c0b03c0e07590680d602c0500c00486208840c41c004000d415180c0d980408400b02c01c0300120399440e6244091800480130701d120785101c1d0584040003610060000c4103507402160f1000c01542080016036a40340500b512030060108411801c0002071412421469074a80c00801c7d00c0f040700a20b01800d0074082c10100525140080c1e008125601d45070300d001492808803a0140b0300030010b5102d404140f0b003400000c0c1c2400c000e680e070302c4090102e07034500807815100b2034404017410000c6c41d5880d0141408030004803013699000e41c0920042000d4145904900c1ca4440005c042d201e24a049481c500c1080440c0d03000314225860700c03490305034040350b6403041524642049000f803440c0c0d0b1400070000c01450748403252a040200100204c0c000d5410101001c0c05503038040101540c4c00c903030005100064120300c1c10130300090144104005007003410710503140039203103602c003a81c040c18800551007a208091 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301778705 1250 301777455 301777471
    0x1404020918063903070f050405030a03020d20120a031508030301050103060608040c0506220b071a0403080612070803070807020a0b0418050402060c06070c140c1305 72
    0xe2080565020030910049115140448a018800e009080d82001c91508030a01e40d07034018400d50004000f0012206499002050b46090190403200345ca04036140d0142d54041c0381c06205000501c0704164004c0b1b01c640c624417242da641e03000460984070ba0240e10640e481e0900c0250081e200c0390030484900303002403588064608011030030201c80010200d004442c3d605c0041c0542000c00103119540e8107000c2c1800810361490000101d0506403154000c040080c840c3ca4850000002c5a82210306540240641840d8500e60340d410b4070303603c4081206a501100003180c40c20411421884092440030000b8003864040c1ea031120b056441009001c40f1504240041d050b51040c00c01c001503004040009000d1148501019070701d4441038410b210091003160040031200c50203000c20b115840c1020040c0b10000d00c10000441c007502c0303e0002c61150b10034260620b8950080b0010862000c2e00050402440e910075140f52070302d000b02d100c540b0344652541000e01c3e4042c00e500380440a488117a0000ba4200700b00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301779955 1250 301778705 301778731
    0x20c060609060603240d0b04031e0512370c08060a030b04140f0d0c05070906050112270b0f0705030105030a03051b03040806010617010b160f02060c0309031014040209 73
    0x51f200c880355000202ea044000420301d0510070032400500015040e0f90301181400781c10700080644441070b041000f0607105d00c082203001500c4400d200c40c01c0c200c0f03070440c2c118441011020b822054030080d002c1c2581002c04900c1101c0412524181468500c2c00c0301e800c00c3c4404150344407941e410101003132000c03060000c1e100e040f2041d40e10701c90611130802c0386040b40e21040c40d040c54600d001818042c00c0c0d031103410132614000c03040120782d0f0413000001410405480c0013510000340c8242036010310301c0300f1140d2911844c0741d00400030040000450740c0652809251020a555010700480c0c592209025050b0940c100c440c0000010b4000c0b0b01510003619650118000c07014400d881920310341107075001400c6a44008010040c40d5041400c25541303a403240b0101c0207030b40c14690840c540384039141e5401e1909100c041c0b102c050107c26010b00000c03980c000d02041d526015400441c2c1c0c0c6e50000309000d8441c0c0540d41c0402c1c1d401c1c0b100e04c6040448540340094129950b034903001c00008147c010f04150a8040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301781205 1250 301779955 301779979
    0xf06090f0a0f030209090610170a1203091e110d080f0708070318030f1218080d030b01091d042303120c130b0a02010e01020c06060906060324 62
    0xd07400166501030800000042400d9195004104103044042c2411603941c1000080c002510a40c1807400c4c165000f441100c7c03080c041070b207509494104a00b402034104484012080200c0742d15402c9130070f8640c000c0c41420303040550880c0d10806040c0502c1e0040101000300290301c02400e120500c82c030440c0c01038014a0400d005e42c100222141c0c850740f0304451034400003d06001700760300311000d45040c0025001c8000301c0750465072074058072803442401038501e00e841404c0c48202403181c00f5000c1c03c0c800594485040c10ba460032a240d442c2116580c00e004a03040c6080114254401c4c000714045071840b403444052010230000640d00761001420580b4244092a00c050407000e0702040181440705c520300542e560914101581e0485002a01c0c000004030104120680d070302c2281c101105a521541d800b50703492510610990060900301c90071000303940040341c00c8540c9500840e210703202d4034054523002b8060b600c0301c080185d24842120444002c04801c1da8988072001c02d80f41504042001030200b40c0c0c0c3c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301782455 1250 301781205 301781209
    0xb2a0c1b13051e01080f0303190621062301180605060310051306050906040c1b08030f01050103060305030d0216140303040c0506030717060f0409030207060801080304050f06090f 78
    0x1e0b80c1190031400e804000602c0c80b44220303c180e100d600410708803001d0108400214041a1248006024075101c100541d0300203a83d40080d9201200405211444505a004c501054003207034000440070748085182c41031840b8448101d400404503080188940f007110303030a000c44e803038841a03803440030750056545460101e01340d124a4000c50194801140f000700c040c0c07804042140e5415029520a10141401c500b003186456120840b41c210804441c08a4140003c00c4115403c0d195100048414000c07030030302c40c2c103000c1200c0045000d9205509003883c0350781c840380150b0580c1c0346880024284e600c104070031603101405601400598501c01e2071301d9001c0301e90341c503a00c0c24008010141040341c2c00010910042281c0d0f8111900100405e40710030b42140b030881e401401c2010b03920100c0c409464108009a210794622081c3c001c0d60f400140104040d6003c0e00707009650340e001c0e004080c0800c003624008a80100004281c8040faa07005008090803215503042c490705401209446400c03020f0503410099076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301783705 1250 301782455 301782461
    0x509060d1415010906050c010f110d060501020d0f0323011403010e0c0d1b1505091f09090209011101111b060c190e03010e030d0f05010e010b0901020a0b2a0c1b13 71
    0x11044040d4441d122f0303151041031030880740c00d0390106042d541300b01700c407241c9203401c03144100e1540c03064100000c05009854504070f0040c40e500074250410b001034000714504d106c0002080c80d51005400800001d0a600c2c6113961b142c100c0f040c2190b00030542c8022200085c0021205000120030129841c80e4564540c4212421800d841e00100802d0700850b0540c6d260401021031015000e040012a002442904014182c498240554200310750001084844c81e402003854041c0991210020896001d40c424800019005204029031201d240c4040985030a40051101d0288940d12101c40c41c000c5c80495503070340a40c05500500601080c46401c8045a400f071007050640c400e00c0d00a1981c64161303842d640b0861b00d01d080080c01c964541001802100c4000300d045042d152074003259959a900640180c3c42e08416050040480da603a908001542c8886c40d42401e807a0310300f2a42c00d10401e40008030400174003c140c0d12003070b164413807100d046a501840780190110b05003d0005050f840700c64410b0011b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301784955 1250 301783705 301783721
    0x24050c06070906171b0a030e03030a06080d050c1f23010906050d0f0b0a060e1302040b09221e080903060606070f0b070509060d1415010906050c010f 65
    0x20490311003003001000c2d000b444481d80c60365584402e24040c6040000c41d2103a000c100145c0078501c0740410601c5907140641d0011704103086003c00c40e5102d2070954a4803000d07042c54015842d04d80240050315403024010819100d443d10100c001e131108031002c56054203c401d481c0b40104c90a501d480980110019000c6440815a40040c2a8089604100040c000d440856000c00d01400308108440041000e00d240041010740c0101c2c001820748442451001501964010004880c841814011403580d004030b6091460700c2901e003801050100001c0080340002281c102c202e601d200c0310701c501600c0346640c21800013407040508031080084590706121107024900308855401c2d00047c0071005280411100303070310420480c1e40b2403910f841c0c0e07078800141d002c2016005200f80c4c2030002050b0000d000700c05032140c04001400907615401d80c8844440900018082a0b5000d00c4a001280c00001403081007882c40700107840b07982c01eaa02d0301c04103e40035802a0720a11403556610b407403e030f00130114054454 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301786205 1250 301784955 301784957
    0x41b05090a021b0c0f130f240e040b04080703090306020d0603140f1203131e110405150105070302161d07020105010e06060d141f0b030124050c0607 65
    0xe2100741c02c007840d0f0040c8100c1d00742007501d580000e82c0450603940e211680c13500900b0503031700441c803084902d040d100584900e504181000e0306020140f1000045511546c000021945000d510b881d541e4045049c2c02030b0030745001d050600c001e0000380101d03028900804a06100b841e10480003540d03925083c049030024138034460881c0e100c080420a000243e0408050115058090b107c080c21601c5025901c0307d8942e1040e08680c00400021090a1509041c903d140e420456985502d02c0404d03040c0d0400181c100115501e40c1d4090f110042414140300c0c080c03040440e0218640d107a42e0348401500c440d00b004a0480440c8946440b21013190402625400102021609a01140c40204208a5406d801000038045a140000400200c80e25030306c2d00b50040d005032800e90b5504003028609015050140844488011100500c02c03025000344240521100300380a904c0f90b95103908001c07406110a20501905100081040400d1020b807109221004420300f003c030301c1c009030040901d08100003250200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301787455 1250 301786205 301786207
    0x14030a020409060e0f01060e06010318150906050c0a020a0b0c040909050a030e010203030c041208091807030606020706020c040c11060f091c0f30050a0609050103020603041b05090a02 80
    0xb04c130208201000340314460100900007142001c42c08503c41900400e03203410141c946614040c1e00c54103c100301c14040d001704c2c00680102e100784001002c3c2c10821000c8944a280100082d02240c14500361703442c0104039809031451141d00e80750400080c501a00c00130503940c04100020f41d4480342d10031202a248214007800c043d400e141009045610102d000c1410341d007040081008403181c140481d070a070741c032110382a991403400d8102440c4601600402e103400084034599240140011043c161003072400380e07424040d160b02c03400700300d0301c45401c0c0c403a000150f881400304155600d402c0c0c0150007420200d140443c00104400342040c42d0140603203013030239a510850184544000d0500c285081d032850311510302802040c8180081203072003074201c81410410060b9203480c2d8441c00e6103c5200701d0101d021100c0c4400484503c400040500751495501c0d40c1c9066000550300805001c0c140c1201d400900c00c82c199690b54480503d803401c0e4240c865a400c2550300e001c00d01e0b642c2c5140841c01140d0b840401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301788705 1250 301787455 301787471
    0x1020c0d05030c030a170702010b0a0e04050c0603070513060e031e010b04090c0602010f02030c04030305072307180c090e130b070f1d0a051002030d0908130b0a0914030a02040906 78
    0x3040d031b5501424000859051108001d0261a012401350032140c00c0c003140c59080d500c0e802c010382028554440942d110400100307104031a548a0040c00805942d00340c14903a1035510b09040d1807001c0c1012100d0f0701900440a003040f41c0c201005054a640c40072030001c6031094007100010100c840403a0125200b41118000788113a6034240706920b49009415070851450606450303141e030318055448020104480046c2510401c6445030800c500c150304014058000000015040d480702502d01075050311201101030503541d03100034051000e408100f40c507050a80d60a1071180d6494010041c004450a2017490a81c0e00096240c03030b11034840c0744140d541004809410000030480e144c402e010000a42c2e454000d0301241c1e0381c0c5000581280c0086940003024101c4a1059056014a13450f0f2000c2602e000184802d00c40b6480c000d1010316081400e803031940341c80b003c43c82c92300c1c0106401d64000803031904007840000030b211121a0a041e00a0071101419020780c0010203803200d0030012a0515111010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301789955 1250 301788705 301788737
    0x60c060906010909110904081308030406030f0b180702160308121501080609060d0501050a06030203120c070b1b0d020c010e0616170c06010e0f130201020c0d05030c030a 74
    0x10b405444040030510481e559900c605000380c504201007840f8040c148082000c100b122021106460002c2c1650340080d90788900d015100e40251003108080307410b02004680c66603042c458500d000b40c000706101c26201d035814a6045450008042c00190300c00c008000b1060704119400034000e5200e541450364030038010050b0154140e0150409003c2d21014021000c281c4c1c003e5195540400280e402400c0f0b540c91400003034000380343d40d1018010317500e44000d005035050140c002100740ca000b035040300d5001d104260407110500c5404058003003508589000d00c1071020740401012060241d480c18000003207605400343c189500c1c1d4040c0005603104500750a00d40d41c002f0070394481c0c0c22017203550ba804c10180c040040c0348094810001081500701080c458112090541541c8803c00d410044601947c0c541d0404080340400791160312031a0742040000c0e194030040f81c1384864050b4103902401c214035001c0c1c2032001284c0f00700c004031200d02080c001c5e211503c07010005880e250b50281d50340e040200100c08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301791205 1250 301789955 301789963
    0x70b04290105150309060403080c1303030206060405010b0301030c0e072c030705040e0c0103020304020607050109150f050c0708070f0210020a031119081c0911090702012d0b060c0609 80
    0x180641d4090070134000c00030016000718201e43d0243c0c1500b040c0c1003507515844002ca030740c0300d00f02080810410452010040c154000703155481402c06480402a50341c8513052042280002d01c0001c0c2600d003190070074002c1c0030320f6203001a002003090601b50480515440000c418928556854028240345405000380385402c0003c40300500056a0401000300e190824640724449221030307505154000003c40e0440d100c3c1c0c2e085480c0590000c00820214010b803038958407010300c80002540711814a1701030980518981315042c019410701000700c0c540442580c0d9500107400c02041502d0044080b000f04c40980c0701c02e407484010781510350207400d850030189000b40c5101d002c414120b1b04c80e4000003c45280030004002046040e401410950700d0340e10680917131410520200c80030301c005003800346140070003109a5120b4085881203030815010395824bc801c074226003890301c5d4090210040040d241307404c0c549400d81103410a00700d502060480d50040424041c1e48100c200c0c0185074490000c0241d01d8400744 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301792455 1250 301791205 301791229
    0x3072010030e101a0604080303181515010e10020f1608070b0f190c020f040509070603020d090506390307032315011e05070b04290105 59
    0x30408204420a4002c95640c0b01c3c2c1c4601d00d500a1651542e051014502c3c029000c00c10100c028200b0b603449840701c0d0640c2d241c0d00159460100c1c164a4002d11408203004254007155114521402a050340c44040000c055440ca11069042c01820301100c007480d02ea2095818580307000d9001440d40810700b1800c581f900f8500e840380c180d001e00b074040501210b4800305010045038005c44913542c4584c00650110311500c259a140703040941054022000e40f0703000190a14201d008580e1404248988020300068071012140080c040e0800c490a201d014084d501412400d804404005800c040943e1014a4100196a40300801c45009000302089141011481241901e1207480c6040c0410812440d0140409010750051584550992400c02e4201603c224950600310312a600d609145162290810078001028000707442200c1616403a1603000c10300d84c00c00815a0390502e0f00c0201c1d00c91b410310b00b034050012915142404001315041c4960034030104c002c000c5509910340c1c2d500d01000c2106840040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301793705 1250 301792455 301792457
    0x5010e010f0b0301141f0c022e030c11070303080f090c01020307030e130515011706011b1502070b01090f050c0904021b2a040e0316030203072010 64
    0x266000c2c030400c0000c1042c2c9045903c2c80c071807400302080120001304110300000d04071100e220104800602c1c142e201d14a69461402a03490000c090800488240d00a400c400c2000b042000291044990340c801d43c08282000194903181c0c0041071121452400e1104d50751040d00040c0f100c205122503992084030302a04a0f1241c0001e1160461503c00070f5141e001d030460180c28000c5116104189440c2e41c3d1800c41c019580c4002000036103010418040c0e20b412012800340051020f01c410305192003100c400d02c0c06040140c683c0b40302c80681112041c07460411010454000150181210f590040c600140c004e075032041008001660405259034115844044082c400e9070030725040c4030f0747d50141c80440700b05a10650300581d4581646610841c004545001c1c101107104103041411080c441040c14000b820301c091104030000c808008000a5a98031103804040750410050b802d50200c8200b2541a0301748a401070300e0618030310361030302580c804d00d9500c0310281040d04090f240451a040d00401031900b25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301794955 1250 301793705 301793729
    0x206100303090b0a090b0d050f09060609061c05060a0902011106010612021602030a06020c014b050103110f030604030e06030a060b0f0706111c050a1e05010e01 70
    0x24544004040c851180f0880352880c0000803030620740e42c8501008000741a030740190f150303150007031205040140000c580301030080c90244d0100d82440c8010480034014117004015104a4071000d0030444009850035284082424002100000820a02c1020700c60032201c040022a00d8007400003400504540e0507000c0150807080051041c81c1d0440407407403124009490068079129801907844404010000c042c1d45845403404400802120f500200403102110000303010488032000151210aa80c4125103004c50091410750041c400b08203440303055468a884065040100864080c2110000e80064411030155000b40718141403e030514004402d00750010800c920702520010400060042c00910400b0000f02040b0595260740104000c4d0a100d4441c0ea40c17400449201601d5900c0b644040300c0a90500081058649101c01640c8a10340950b400da0960b182143e080001054020098100b45644031000008511404851140070b072040c0c50024555041c490b0403c240c0d00b05038044480307815 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301796205 1250 301794955 301794959
    0x50412090b2b0209092802040b1b03070210080106020105160e0d0510110409060608011d040507030c03050d020c09070207030303020310031a010306050601050703170414160501020610 80
    0x403850b1000c16402602800c6a00b60460241d0300064440c00c0c02c200e034086090750a01584210a549014480c40410081780000d040e402d408000d0f40210b2080d040213200031301030644078600ca58034a850701c80595003540d00d064140ea000640706201e4007003c4001030039210050114076024407425400c80720711001028030000c0c0300401000001100709241c00788074250320300e20803c10104000310740080444002c0c45481300010a00c02603800c80d01c40c8100c41810300f00005591400343d505075050792800c1142081031102c00610211300070016004071020710070420008089602042010b01551080000d00403148907041c000707103480005401248203500c41800c1c0008130787c000035148101c03585800c02684a6542e0341180c441b55016501c0604441c5a000c00c83d1055040249114140e83c440c0500300329913114440111118080c000c0c004000c508005221108486041070703056019102d6003280c040380351b034a030001d400d1114820242c820140102000d001030341c1c042c014180d107c6101030300102124 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301797455 1250 301796205 301796227
    0xa0902090c160507090b131503030c0c03080414040b01031505011d060c160609050108040f0629030c0d02091605070c0602030304060f0e0619090204050412090b 70
    0x3960181c0030820907500002d400c040301032200c10710300007580c12006030380c1ea03075990300d942d40090700910100381d20429411030740039902845841520760720f9006031148215541942d400380c03513211400c0829624003805110010000b0560700c02070000d001d01207000072149200409100c161030381146d0650606040030342403002c0425024440b000c9070780034605040800d50f441101c0707680541e1040e08130303084880003d585040b20b0f00001d120854000120b010214140d8801d41128200014002c1c180011100c8000c41c0110307030340380f0400000c280a00310009041c602c5021004e804420003038650011034490408100910301840103034140603042d206481c0783d5a0a500003010000020a840c418881400b01610202d200c1e00a50b00b10030342c0070304840d0446803140c501950707070340080701c0c219022410618602800e00103401241d520380201d40040c000c1b030315444110a07007020704034604003505507122101e0000d640c4034018540241e001d6005150b51410b105e900502c1095142c0202c809403104001c562000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301798561 1106 301797455 301797469
    0x8011103040515070212090a05130603110f1f020f0316060b0409030e041a1305011a0c071403030d1d0d0306140607020f040509060405060a0902 63
    0x290140400010221004580ea9801a0086226030b1b03240c0c1c20600c050280501c00803c611107071500e450125480d101038441008079591184010814080c1d545514051320801760340010380300c1050000301c1d0b004441340580c06c001e001040700c11900c0c41e1007440517401100c4403c0030740356140f1554010b413004545842056075058501a001c1d05145803600c41d030b04032558541c0b280340c401c00c1c540c0e04000c002c180e03250b1103e8499150140105090b6201841c18034030f005108000540c0d54100f603001810b003910b0f442418500310003009220030000c4002144011140040b0251300c28050590101c0c2c11802824418507149e4140010002d48103818059038034280c02c1c140c104d076504001140c04034240c1b8060301c40c41c4416010003211800c0f504244004240380381c00070300400e52929400d07002c02d0031214102d402c01d403036420100034401089402c0c420b468000350350700428080341e00650002250 = true := by decide +kernel

theorem cover : BRFrame.Cov 301618705 301798561 := by
  have h0 := BRFrame.cov_init 301618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301618705 ≤ n) (h2 : n < 301798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
