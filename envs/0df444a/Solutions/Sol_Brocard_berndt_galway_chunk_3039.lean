-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:54.28216+00:00
-- url     : https://prove2.me/submissions/a5784dc2-7b45-4741-8aa0-39f1a2f933f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546402877 ≤ n < 546582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546404127 1250 546402877 546402907
    0x1e0d060b03060a0b2d100201020c071202090c09090c0706180f020906040509100b030a141b030105061c0c090510050103050c0f0a110708030315030c01031e02 69
    0x50081c0c1501c240c0d000c02000090f2a0032143d04540c080d00e0302c0002e089a0301ea45140b0f400b40c912400c0044444008200c40e60414220001c1322500078070005042c103402b2010766007010b00541c802941ca5641c5c0080720b055103843c5c901e04e0303005240c80d10031601c0c10601801041541c2001842d04810000115014082c869290425003944852035600c0c140601c452600d450400ba8400c3c0c241c0c040e54403200065024201449001d005030500c80041901c02100203141d005415070245584d054003c00424000040462900f0707000b42c0c090340003030440841e0b03449020308251094080107102e80c0c1040107201e425214024001e03842100d030b00a00f003854110341410880c00520790b00000040d8503050070041051651a03000040c0d89003623809104039201c0e00c050540600501a018a980d14108440100e4074044e030b07041464210f002040c5c801d40307a50750002c18255007049400704a4080701c1403020700949428804040d8411090a0403c01c5841c20502e072040c880c40305c4d40310f190056001800c1007001e0641 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546405377 1250 546404127 546404141
    0xd1b0510050f01090b04090b06060903070b04081f090b072006090d0306060302132612071118011e12110301110f0a080a0216061a1e0d06 60
    0x15803418841030030b11101e440c4000780300344509611145441c40b260500e2a20780500d0b499940c011401c8241380d103801040040660001c662968588035822001840050345030140c03004200c12400707000a1803429030340c0d240d42c0800d07031516064035280415142c0007541501c8615085403061800d24048020044100c03482485500c1e020260b124810802824800c0014000110b180a076001e002156641c5000c0c1e0a074060450080c41d00c148288007800603109104841c5102112031030118950034030703051000d0808401020201072010002000401d0040d200e8442d181290141c4408100541c545004d0483e6a01030090550305211903818010143c040e103118409450794064250310b00c00706251074081c40e10805040c0d4007035402e11210034003001403d000d942c24624080002031400d040340c40c040300e2a100041103a0001d81d801d00030310b520f80d045140fa201e10244034038000200c03c540003007000050000800c07190b00c2011041c00d000b85140070300794449044079050b990354400000c0c0740340040180c00e0b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546406627 1250 546405377 546405403
    0x3030513030f12110d080c0a0216090605031203130b042102070815040206040e04030c0f0b04060b1207090510080f1629070c0302030316060e0d1b05 65
    0x107218140c01804558070843d0b04003141ea4842d108050980c0400c0c50700d52920813407281c0070940440026985e03400300300040010b40c1591040c2d03414004007014011b40509260001f05d0001d982c0c040c00d03c114103082148030749200c04842090305602d0001c9050806050b0b0314802021b101844001c41c04102d2082c0e0800d070404158440445410348070070000356101c0d03039480707020864441d0241c00d002d0400b2038504075000d40c0d0091704985c41c25082c0000c121002070302038011820020340c07a0b506004150b83d4440c5c00c801c240b041190007420306240c2040001e5460398808c1511485480101800f03d0b540000c5078030407150103002c082041e58420300e0f048185465603128400a006a001e0842d061102003002404e2199000c03244480c50f4542920228a9080542c0b005904000c24010074007500320001400b8024850100c45403042d4407a03010a0440e04007802d510424860001148100040d0f030046170a41c81040f0001c0012001d451401000840301c0040036580300305005240c0213200f801d100011700c00b90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546407877 1250 546406627 546406643
    0x60f04180b07050d0612030f0c210306050306070e0f1003090b0a060f35010b0a030302030a2304050609011803030c020f100f11190506060906030312010303051303 71
    0x1a1502015180351301c40b514a1543c0c031300d08403010a6032010020104a00c54047d0f80e4995403140c0d501054506211001c1c0554407a0202c00856820b030b0424400b400c250b241c00e07500800e0709403621090519004024042c001441141184454039840e60300900f21185400c0318940c158010000007030b4010010643c01400070280003042206039240c682200c0100c13a000399552142c255103c04506040b03902c8588040342c00710100c4445102e03402ca010020201d407109000144851000c80080c08030031030f0f580304501582020818a40117504120003502c00c140c854484010039a20613007840c204e00c206d018840c8a07072000302d1407104d05d920070f0307a0159401c2c00b503002da401c83d00e03201d08000c0c02c00c544400c400c03403140c4900302c18800641004205840107090315162400703040139004c401d40c0c40140900511505104080e03640c0001e070080c4005009444c01030b4003604460400a050042c4603800903e054042d50042048070300074a80c241100381120b4161030400d468200083e0300b080b4411041d4006000f0b81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546409127 1250 546407877 546407881
    0x2d15090301091b06050c0303040f02010e0319060510030c0b0f0f030109060305190203060f07020c0301090308091b150f0d0c030c120510060507060e030415020d08060f04180b 76
    0x1421000d02e207503c410090660504507a07038442102d46220302950301c43c9941060000c10000780030107008a007168814100010242c1050000ca850410700030b14200c071502000d20700005004c52031190540292895142008090541d00e0360158425280f00380f42c0c501c0340008810101145100668941c03080552510341e0f6941d40c1c5407400042c0400e80816101d03230040c0354032000640000c242800c0321075400350103046982d1f220600c070f41c07102e03100611010941c01281740d440001d98003842081c05241c400d4960201505000035072600e094180004c02c0e80410800c0d0041c07072240d41c0c200c0c1003540c003111303180c01d903a03070340742e40c002d45a001d0103410208443c1600701314035080e425030540c0014200d8500c60390768102e40b840c0c0400303e03804d50360180c1b110001036003000c5c428031210784620000c040e03c41c0074110105084040d02d405078a1a4007582c801c1409003003110401c0c15281c0d05001e103c1e14510039180002a41c1050307000204015160720100d840365a964070014600700040301d000c104140c005a14031028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546410377 1250 546409127 546409133
    0x11d150f1306021b0a1502100c02010c090f0b040e0702071a0304120c0b06060d0b030a0c0f08160611100614120106031a061305010803092d1509030109 66
    0x14010340d000c1c402c054094000481d103440300c00f034586038440a00a0060032007034030381130750f0803240107000c175242d0214081e0800704480e882c890300950881c001d40790700004d1004c014880c020400d403103035000101049501f401c100b10b43c0a1581c10394098074041003050b4103c6e00c0f039035003da03e01049035000d200040c0034003040d282c91a803130300d018601c100d00664401e02c107441407480454900c0d44c0740c90010301e0040304001107402803c041024181c01020f0410000302201110b0000b840e200c000d031703412260840100c4061010341000403441c8003c01c0c501c0002c0900d0303904680c489050170f00b036004e9001002000c84001456a00400c814500c20002e000100030761900e4410f03014180c10003903070b4940a01e01d6100c005022820520500c0c04032a0002e0190620401e21168628082d0010f401320381c0c81524902c414861031814400c45000b08104402107560303155000510040218243c00220030005c940b20281880a0f04038401c20300b48030031650f00c0b0400640b140c0e00111405621a11078240d860b00c00a0410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546411627 1250 546410377 546410407
    0x60f2508010611010203040203070902030a0f020d0501050a06020a08090d020f040203040c0509010510020703080a0311040b030402040f020313030e130212090115080a0311030714060f06011d150f 85
    0x141d5005607103040f2002c0c1c1c0d600155080c2d100c00e440007905540300f41c00801c0a0749a96000c0c68200320030000c0032880d10819100074091b40c0140310386071155652407004124516140e039401300103082500241c9124030f000d44484c2458043d5070b40c85806019194002001c40d40c0d680d01c0d17203850803c000d000719181e0500c0d00341126030b01020300901c3d006820759800450907144c084611500100742d0b6000f801010706541e10034516400107225201495242d58011100c5603401c000390000d00741a5034059241c1c82e007030041205403118403d000604501c1002480042c4035078174272140009030581030401c0d1364520b4001196080341e2071101d0000c82840030401541040b041080140201d0f80a0024000080030f40d1142c4010100341c4941c0800f0fa0159034200300190140b061084a4a00d0000f542c0c01d10f070f80c90311280d000340c07011048440c190b0058420850300c0e160314004550001ea081c40c0581d0014814040f541c14448980003603880350b4000c61400721041201c400701d603114030b29021815203800061580c0c5e0a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546412877 1250 546411627 546411629
    0x1501181b0e01020106060e0a23030a0f11010c1104180b01121103121605101803170403020c0d050c1009060801060e030d030903020f0703081e030603060f250801 70
    0xb0065081c10030000309607101d01c00b00c08039000018060070340f4900d0950714000b2580702e2241e10002030140402000c1c42d580a02c0400341c25800340002c208604070920b401203203c0c1a01c41c075113041c00b22403e505c80c049961180410030768081a100044c4284240910f505600520307075000b081125007400100b0700b840001c000a00d00c62103000b0000c203040c100420191605035580e0384c1c076003400c010b10900b808a81841e0001b03035254007950584a80b8800d0f0b15100341916850001c00348483c0d11140e421080591104200b0035180c090141c0e0141403d02d41e4009441d080e030034146030b01c2040c918030303240c09011083c000c90040c1c0350000c04900c041c44056a0150280c41c06201d02d10105850f1000021118059102502c1018000f00500302c6403181c1c01007034000701060b08064007103108a149003030724140204882000346009800c2d85807156080c00d011203004485150300521410144148141a2400214180c204502e427010983e82d41d40e040043c418801c0070030802c25038540325002080034a4001c20914 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546414127 1250 546412877 546412879
    0x1905040809031212040b040c0312021b012102031b0d140609040f12030f02220b04050a0e04050f0709020a09120201020c19080307081207021501181b0e 66
    0x20302c3d035012880c4109890700402c04000f0074103080304000b9001500f41c164031a405403003003110301c2c0219180c0d110401d6854800702c0740e8003d607210031081013010b141d2001000d1f01d40424030b021401400701681c2c240b20346258100d58840c281d004008240d140100300d810140c0c410002d020320b40c0396088800b0900c050103480d4550b0001c8907076040030071a14104020441e01c12600032a024416202c20381d201030311881080c079000304055603141140b02da648640000c120b414280c4410b92074540f85000c10b00741041855006032a12082044200400d45540158800b160488004500b15940d01d060880c104000d4080c0d10015000f8640045022403655010b802440c0d041d40e50400341d00d46440007040c482801c020040c2c0583d0002140703180c14548122692034261000c01452a8030717035180c1d9242d00d036801c4040c0c00c4400d280c000c110700320091040b1340100d5102506200070508802c4002c010050741d203040c00342d0100e040d2041c101021070b404a801c01c0d62010351039451345c880201d100c00b00800b07002500f008a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546415377 1250 546414127 546414133
    0xf0f021804062411030723060f0907050d020d02030706120e01020306011d010329040e03040f210b01090501081c12020703110d030c1106100e190504080903 68
    0x4030b0580b92840ca00500d00301040c0d01c0c00ea0b1040008004d41d00d0300000198075800d488104480c500050007100c3c800102641c0084201615030000c0c94035040c100004c014036180402c0104010200500181450461b0001d41d1000100c844600210302ea24036481c030302079050711481800191513903000010040c0c3c80f9940d40304100394184680d002e401c0c4d110940314240050890b81c120031a01c41c4440d07078028600c0c0c05060009030035400056200004102042900400710301e5007060620f418a4000e41da60288101c0107107107014241035060300c004621b40507801c041c548101075200c0c0d15188940b00401c035504000e42401755a592244080941003d0182c2076140c0102c0107208422514103030750900c14802625540e07a804000c1c901b070342c02504440d005408001035180b207102c82ca501800f980d17900c540141e070080b44080f600c6030083c190740031405c02c0c0c2010760301c45002c01c51100030385004001510b0071034018508580b40c0b9035440301000100e0480320540c03031030002444100316000000f485204000e03819 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546416627 1250 546415377 546415379
    0x603151002011a09070302070506010311040f0501030b0f130501050c030103110405070e0108060613080a020901060f0527040c1d03030403081e04031403030702011805100f0f02180406 80
    0x108a081e40c0603010300c428074003c0d41c003035030102c0e15140e289944d01c40414a4018200140d41d11954a002e4003a0320681e01a0001c0d01d101d00241024007502844003a00d6005110552450b5201280c0300c0b03008105130b0f51014050b0101760000100150100b050b6041030007404a4140324070032001c1d540c400c1c402118200d2038101e40640c241083c0c02064414021615000406c140a05c01502c10000003005c10340c1c01042001155103110710144039802604016000701500c00316841400004101030304904280840d6050303e2400310741c404101c407500301c0c01305602180c1001220007054614140d038601a0301030704214568080691040718011702031912400c04420441013030038140c881c495030001900350f003010040008403000012480703000c502c0b404603440c41c160341c90315003051242c5c40c03030742c400c40c0b0703400c00001d011105909006a20000c6e1400d02088003e0240d075541c00c2e80d9031904d030341c8811040c0c0c88259403c4495583d0b0311211603020440800d41d910086c40c1003000d03900c1c4a062115126602c2c1c150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546417877 1250 546416627 546416659
    0x4030201180c0e06090c03181f061701020301030510020904020d0501031103120f070602090607050a030c0506150d030c020a05030f10050f070c080d060b070c1503050609011401020705060315 83
    0x20525000710031b544070755031454a40703824610000c2c0c0f010070048031500c51100c40c420001c40603c220310349860684000103019042490000c500100c014075448240c0c010301c014404a08080356400032a04000401a52541b940c80410702900800d820075641902e030400000600022030b4900c180d161048013a1205d4010880f00d02415004641c86590000e01c14840c55001036203550040541441c02031100e404e1000030b50701e252a0100d00a8103d000070024002d0804103e01001043c0d00000005200107202c808100822603002c11542c02070f0411501180303420a54640f0181036018050203000d0340c0400c5510707501030380c2c4d84000c4100144024035001c0010a00c182140c5c0da50300074440d41d6184c0e8010b40c0e0310344170031409030070808603c00c2c02d55440d007000841c1030841c0020310300248540c540c8113466161860385195000c401304208245800c040400c200e0f9a1400340c054152258010b034021441c4920004034030f05103041d000385400c4040003080c03020701d20754a04203d081010460301080d1203c8111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546419127 1250 546417877 546417889
    0x409060906240b0f070507080304030c0e1e150307170f0f1231171f020a0912060501240c150b06070606051e09040b04030201180c0e06 59
    0x2900c52040e030314111040c848500f00c14000c1c503102480103030142c20b040c000c3d1929820917480b13070b026480310381c0300040c200100001c3c90100f2004203a1207003580710f1380c64074042c10100300190103c00710100321110002100030025a42005a508002e0105d03a0b809441c3c0720b000e00034000e8030a00c01c00510818840000c04000042d40603241c580a0000e040e00c003401d2202c10b00940c00100440700c080b14402603646c0204010203407100d1105010040007002450f05485003103080e128840055150080c07420b0400710b0010100c20241c82124a5005039102c420000c211000c581c00e13000500003051382031986040c040e650300704e5030580f860991070105840c070348804802c40c802d4003481c04020440603100c01000c624000c801038160900004003040c510134403c00106c0e6503105d03001c2140e54942c2e03000f06000a090034004030f41d280071090302240e054100361000030035580000b0b00c014420401000040c0405101790070500f03007843c4181912010803030030701e065400312026008109040412400040d401d10f015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546420377 1250 546419127 546419171
    0x5061306030c0b07030e0d08031b040b07020d080d020708041410020607030504030201090b0f041704060c020603040611030c030f0703381203040f05040b030303240409060906 76
    0x114240c1d0180c03c0c501a401c55264104000a81c1446010760007502c0c1030b00c56441c13920703011b482214081d40d070f07161009100711500c000e4407058191810a0105001001458044400031074049400e5200c81c2405e10302500584500303103008021600108408040000200c080c20945041c80700d00c50610940d2000d1240743c0780820104001a0b100030081140c0c00d000e9400340341c00c40e000c0d200120341ea19180d103c0700c0e400c0e24243c40198403007252030104410f0017000c030b85020340074400e00c502503e464501013004100612855020340325140c004041800c200c070941c007036825413402e101d150f510791415558400302500110364001e0004035203000608d11a110344602c2c500f444200c01880e43c500c0095100001c904610a81854190200121720007103a0b90b80128003243c1046100640d0b460f42000c0240c03880550f10b60049000710f0510b08460700c5a1f6000c4181c990040c07420301c1080c0710751007900003981d51035034010702c064005181c140c41c234080c040950403410509004080a1049161340007080c001104a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546421627 1250 546420377 546420383
    0xb01020f0309101b02030d12050f0903191b05150a0504080d020f09090c18180703021e0a0207210c090b0d060f061a1306050d06180506130603 62
    0x40a40f6043e080b40c0101c5100080410001c40138418484503408070786002c80b90401c1401090400d140503000c40401e0141e20f500c4184035403015105e00b032001c02250340c0e0084007484a60740747c04526407112280b02d080c0c22040c211910203160622005410142c0d102c1052000042528119200080012171580103050249074007010b4146804c8402c0351070700094001c000b01c00030080b8100301521041e91200c030300750301a00c0340d801c9440d652007800000c2c1c481200c0515074903004000750650300c500144401401e40e80b1003618200940d03240450b0b001403055801140603110022004034810900540c009010004d840c40010038100b000750325124007903543c00380640244807510080c0207000740300c502e400c40f04140501a00c442c50790069551480d003070b03ca040c105d00210594070f600c2004a055400e2440c60b18003488032200d4503285103641030281c1c4052030f00580092100009006543c40702988c8242e0040a044c8419100420b0070010fa2001d0002502c0c2c1d140314207940b4146205d030000d45c0c81180e045943c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546422877 1250 546421627 546421639
    0x6050a0903120c0b10090c020106030b0f1509011706070801051e0402090d06150905070f0f0c0b040812010605090d110406080706080412020303060904260406030b01020f0309 76
    0x100d1a5a50215080c10707030700030b0302000b01056031000080c01074002d141c055072000b0014135500e41010443e07000c03103038104000021a81000410404218a440c0c03d40d0010a03070100280c80707503101683c50045406180120360800c4103a400000e10810b48192600b001300401e041e5a0151a10b480842e00c9840c280a000d40c0031000c90a0041400f1804440d95810345001c0d00c0582406907410010700005100d4205503a015201d6050007240c800310751035074001d00a071510410007801d04441c01405d1501c0300b00c01c08144182d074505074402d00d014a0044030b0345640011298820b180902e0507032a00d0300101440030102c07610703400105446005d0015103280c070034054040484900e654481e44d40800046003086c0d00300d82c0d215000b0580c000c0030701152000d440e0b15200e5404908151a0210030380c800d00104000310740040c0b0174807045a65a0503604d030007076007180000d02c9007003040c0040004240c3c08185c43d4a10f2000107000140980c06801c80815034400340c095401c6264540502a102d02c10081c0c4980c4c050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546424127 1250 546422877 546422879
    0x206030601110708070f06080a090c0e04051203070f0807080c1c0905030a0c0c06050f0d09063c05220c030b0c0301050406170705010e01020109061104030c06050a09 72
    0x1502c552a121410b02c044000c4504443c2da0700c0b181418105103410900b00c15225400038411180c0000c411504480b12075010444041e0f41c0d11424140107083c010740006c0d5204401040a1000401c8801c40004000c45440d0b0399040c24a40a411a498101890003003080714000600150040c07540f03902c20030702d00b11400c0c0340030360f4941c6603408c030010260030011441e034842511000c5074041000d002c140b402510381c82c5c0f440442d030424a6032141e9a50106041142c108020110b5000034030035140e5017840389070b02040d40f070300307600e00700014000c03042142d8400103000c411081074243c00311403100300c0c2e1800c401c0c128003810012920000d445088409054290244c4048241500d48a00050213940140e00138003145403030740d07102d540c04d82c415a05050403020100c018019441c2030f01c01c800080c68802d080c00d510041400c0300c552266504d1041310b060089500103903c1590007900050401a4440020400c88041c0022100c4c1e90704940425201e900301802c010540901520480d040d060881e01d4119940d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546425377 1250 546424127 546424129
    0x90b010c120e010c1406150a270f021903050106030c052a0601060e0915280902070501020403290f3610050601050a0c0602040b0703051804060302060306 67
    0x10300030a000c01d80c104102049440d02040090259445e0106403001408441c20030008203444004001d043c54821403c41c2070800c00a8415081641c4102190060070607945a07540f02e18028501101c0c8450140d000292047d010011110700b0318155805031010091a6240c0c00101e0844d031800c0b0640010030310030004150300308601c07030340c244680c06003103d43c0e61b851490500850a000d4207030b000101291034030034882c0d5946002040e00307070f01c01c1c6a803040110b0345100800080f40d0b11145110700f200d2200c0c032a15461408050200d60003d054089410b40da108481e2070a42e0003544640300540da0300480190328650142101c2d84400568140001c1807003949074501402c5035480046c1c05414105d126811421a0300c4030380c001407620301202111208601303038401126090908a04180300242c0c40c2400f0044d4580c2c11a0584856142d9413815007051a1503250440092250740c04c4011442c2002c14001c1c105980b00000f800c0d003001903001c04140c4000c2c2402c0c8000e40322140002940440140006005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546426627 1250 546425377 546425387
    0x3060f1103060f0d062408010e031204060f09170c07212301090f11181603062321030f0901050904061503110315210303010609090b010c12 61
    0x244d40100400980d1080c07400c0307036200c440c1030f444110320f00e040e0841e42000400c00a103c0c114060641c84050b40c1740c1040849a82855840208001e00050780e03403001800010f0154424134455601014001002c0d90840da940b0950b081305400c1c500354440e400004c03502d0002040c42c200641c002c10b01a0a006005507103554012800d26100803440d40041a483c3c5801400d000c0d151a40c6e0060f9a8161407417102e041c44130903d4070103071805015801c4064692000c030a01c10101d5402403903d01c808208810444007140503005c90b9002607806410310f18a0700c01f880c0d800e1200c080741c040403169110403100c0720b44410004070340010f100316035070828003089207001241e00003012071040c1494402c2c0303400b11940c00101180e40b10340203105520010741c5d61400d03441d0144030304007c02c240001940e00794076240c0091203200f116502e0030b40c06220800f074070030002c00c032002c5910b20a40581c801c0da61250384442008104203500e1103601007081c2030103072003449540078044105100350070444000001060040c2690 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546427877 1250 546426627 546426649
    0x6030506061c0213060503090c21060108060610022b030608031c05060a0324060f08060714040b1e0d021605010c020c031e01140103060f1103060f 64
    0xa0070000c00c210006020710b07005058819414002e50044c0c5804000da2203801074901074000c213042c070808005000c18440c000030104244201190442480e8a0800d401c4062411500c80c85607240300d0b940c0042503070800030402e076100e4102520110010341c42e00f4022a600c0703079410b071010b4408d40382520350a502a501c0681c0d24400c0c0742c609001c0303425a66550414a142d204400d184400054142c15034040106030044540140044800300c010f20704540340d0303044280c1c09c0d286103071010058a1000d00b01c0c408d40d03086503004003030701f8078140040c941d542c5c0041d896090032250f10002881300c0e00e0b03050b80785412405440c01e80340c2801d1120705111441140d0443c1d0751100340000614603080c00100b140a9281c001071841c10407070581c10805250502e4141c0c01e40360b280d200401035400c1b074280390f442600c00044e0010055601c08070840b02c010300f0b211250061991101c1c1030304040440001106002040e0888200d040600c038003000103400040180d9002d004c03d80e030b8550711549400c0220b441e4070742844000307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546429127 1250 546427877 546427879
    0xf0703030c021903030c020714100e040b03010c0906020709050c09060309011e060306050912120c040504060b0306190506030705070615030605090601170303060603090f0d02030c0f07030c06030506 86
    0x520b11603e00306040c1c2c80302c2d0292000c030700080d1a904103419003039042c8002c0d00204240c803106415080000d00007034040313241003240000c0018002c01c01d0016940c98001c5540400007070020460805e00380d2004062000c58000c007800f40c40391000c00110b1a0f8075100d480d1007404803220007810a00e42500f080f5490340064081c0400d50b40f03510080403071800031420740281401390000002c800d4698a0054281c2d90001d000c0c415035003101304503402a200b43d01c00c03101f15414840c44130003141c0d550a000340e410300881e00044d4000d4603000c4003189215802005502803030040301c2549620707407075540c01d451400f071f2800341e55003002050002c201e00d84c0c01040605406480348074041819409281040081d2540d9441034894544030024131070440000c0c040e0b540075107500700b00c100c0303108221011a6645d00c00600018050000000003610880041c002c4855048414003a07501018100600070358039002030010610340e00840c000c01000040018103802220303446209000c2c0a49801426070041c40000d01365 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546430377 1250 546429127 546429133
    0x70c0314131509060e06040303051308102c0a14100e03090406050d17030408040305012406030b010207090c021c11010c0c150c0905061314060f0703030c02 68
    0x410040440001c50001614041d0407601012600c00c074014012046940120240885030300020015154101240e082c2c0e6050b04185554200314016040313071a015600426940c050036403030512242240d0810301d111082550360030050b0046991150f0b268002c0290010725034462500c0800152021a02c4c140b0211680d0940b400c5000090400c010b0356580210310a5641000841000520705886007002401c000c1e0751209040804d80e8809091071100c5c01c5250703c402d00800007804000301441260003465000c00244229669071054600c42c45e0036030003071400400c051401086075840780c81036100307100c416070003407441c28a00007041e4000d0818240c081c086005540d0381c0351480308400e2400b950448030f40d0340c520320038040460490844200b54034042c10010600344800200e51100d6007000600072481d80000c40d51f81d281401d4a07014481d6003e50340040300400c40c503490081e0b00804074101e5070703454008030b1555034103c10070006205503815000c0b800802d0280c1000319100303900030f1549440900403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546431627 1250 546430377 546430387
    0x20f0a080c0c0f1509150f0c09040e06060901050f180613050103050d091a04032301060b0c060f0702032508030a0c0e030106061b03020717030a080f070c0314 69
    0x7010304058074140d0441955101501c10004a44130507203455200340c0303050140c41c411102d40c40140d41d420000e42007075001100320700421200780c1030908031011910001d104002c07880740d000006488480c2150000d1150400800000b03047c00d1503038540840c001c00401e050303829942000c0e0b08a401401510094006200c2d4042c1701b1503441c00d02c5024082c40c000c00040030a1418800000c1035a8801c0e0051400c00c040b54103030780380320030014080e50140e81c1c1c00521101ca03804451a080392009034408021050341c20100001880d401d02001440401601c5043c1c8202da81c0b4070404641c3c05009641c0580141c3c410032186912004c20000e0702d801204030b0b040b020307980d0302c00d03220403045400a40b03803407a125549080d415455908041f074031544903400d500910000d0300d01100079003292422500c100c0140059801c80303081610078000800900030f8162a400b1040700307102116680c3e04900310078400300703070201d000c540d07407501501c01755210310070f6a542c02d41c03d0000f5a03011210840010000d01c412141403003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546432877 1250 546431627 546431647
    0x30903091a0301150201020414060304080d050114190302180c0c060a1d0105060a0306050a110d060303110312060f0f04050403020c030c121506060f04030302030913020f0a080c 77
    0x41c1c400040c22212000307450b5410030400b0540d400d44141c81a0a40e84100300402c001e5140000f07940620804071131403500c80d81c0e10b080261241c495009e40d000e406e450180040383e0108401240484a0707010303981000c861104050401c001403290001a60000f6074581454417140404031180d40000250200da042025616a007440c0c13500035100340d24110740b075844608034200120800074090034640d0080c01a4249000400c05418450002520180c4c5403800602d03070405580004000f14008070300faa5907101040a514000d1825020440c009981a5003040c80701e04004180d1307034810311904191046407a1030082100d8140855141604800442408502d0743c2e15031042911941c042c0d00076000f0000800200760418814581c00e92003181403007c20340c0100130005002c5081040782020400a4869800081c0f00d400341c8408070107203c4c000500402010350100260035400420b81c1c184e25070000c0000c45071706034090a812a00240002d00412101c135215040c0103800c516041881817800718500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546434127 1250 546432877 546432899
    0xf12141806210411180103080d0902040e071e0f0509012304141b0a0c031b050d0c0606050619030513081b070e06031905120301091a01020c010f03090309 67
    0x181c083d142c226035513040c9200c80c1844044144c00000c1100d20307a1075581541d440c001280210031000e0b2040366075440301421512554405407c241e140801c540440381e407060307103018115142500c0010307071821050001d0100800c540840039030b40c00400f0302c0126803c008003010a00b64180100540e82e40628910440d074646219005c08403045000c0c110380f52030054194104a001c81341c3c40c03004848104180140542d101603400c090540c5881c010740d00600d101c42081a455202402400f02c0c045d611000b4800707500450070f1035401d13201d202c061107525907641c200043d5020b002c01d01211103076000e062030503c5e4420783c0080e500a80203d401d803000300e00d54650100317a801c480503900131201020300074000030904203c610700414140455101a192880201c0c0e150709500c004140c2e000d5590200404004060000c800070103583e035855600d0390f0755003501c2070240580403c4400091402040d0889a5101044950000c070042e11540480d40358140201d00401c0403103011390401a1014002c0b4911401d030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546435377 1250 546434127 546434131
    0x5012105010f090b1e012303090a0b0108010509031207053c03041a0603070306090507050907050304051c0c05030f0c0606010c0b130602070f1214180621 67
    0x4210784503040c100b00c0c4040440d050b4031101340c0700d80a44c1d02c440c000c210041680b21840b060038a0000050012042001562080ba40c1d0341c14065201004101ca6290005003203103215009442030340445c0d9a079144a8201c90043d1403010482c2c1041000903003169240c14115005069440c08600e400c52808d07004490204e464102000c400c07101d40403085800d00008280c1081800100151450500e6900d034220000d864003003078000b0140700c4c0040c540d03070b509200c3c00b001550443d13000d100e034081c1d6250050b00c83c0302a000d520b1184c00a1404034803064421010b0741c2c4078940c4a4020905e1500e04c3c003440c45e882510700c00f58030401c800d648811000031402d02c05003966080c4040c200d078540c081e40ca81c0c0d60810000070400340c1040f40c4040e0320808640c4400c019500144110301c508403510043c10107a010b48a0031a000c4c101141c104a11010414258000c28000300389603102440142049980d01c254416402403d1078014103000d40e42c481d2410900400d40321641e005882c1c0c5504210021103224042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546436627 1250 546435377 546435389
    0x1821141501030311010209210f070b090a0e0705090904020a12210c0f030503040503160503070203010b06090a061407020d0302060a0501090c2a0b1618030c0501210501 73
    0x320380c010010140c0180d85260b4444441d00254148403d01c00482c50001e10344103030301c8101902c209030602d242e106100c0300040f078995030306032078805071502305a00c032590000703040c140540341083c000a141c0c040d40d009103016409070743d00c05241140745c600f0003d02d51000340069901c40548070380012003400410820b01201e1044156800303400600354561401144040404280f040130030404000814042c2d85041e11641400c00f20b0300d1740c4640c1401c0d490341c0034188003e00300310000076510f414464000b01805019200720001e102440c00c1000b844074501520201d503411680510f030602c5040c0c001e070f40030503141c000034000a040104a4000034404d0203184420307405600541c0502450791700d180130303260140c589054140007011810b030009050b45c00c07801c0c48041008404055005112180d000e115800750040c2c1c132010300e4103005095101c0c00c0010705018010a8407043c2c4083c00e80032040e10042103e400417681214071b4604001540c3d984811b80d21003400c40c003d41c0303c10041c40000d11500380a498 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546437877 1250 546436627 546436663
    0xf061302181c02032e150503061e0a1a03060a09030813030f1b12080a060f03020904022704061a3a051c182114 49
    0x295880c144840c101c4403000b01c10304849440003a60141c0c03400145546054252000c00307181904295a440703503104910180030260781003e00392070800d1581945842030315411003e84400380c541508803485507450800c46450070a4035000640302c4401907100c1a254201000c1c400c0000c54441d00090038100304490300265a9590041c075802d1680c0300c050590721505c400f581c0140703e0720341d07207000d860001e0720801c6400300b0a220400c8442d4810403160610b130030f80d000c004400d2100350224042c0500000f165420289880c04000281955035441800200e907005860b08480d6190307071702440381c1c070012010b405840d2155035a12201e038014140e05940b04a0080c02c0002b00c114194034003a803014950484544a8019081110000700b400c07541075000c0d001071451103401d15000c003070041270920a0400030701940220380c485101580c00b1a40b504a40e0896910800400f001044031002d00e24203007d50440c017500e01c150300c0c0d4910700b0400400b49050181c0b505036100030410381014500805400740f800490 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546439127 1250 546437877 546437917
    0x70e22021b03040614090409021003140c040f0317070f0b2a0307081005060a0201021305010903030801120201030f050403051b010c1d0a030812070e010e06030f061302 73
    0x35009801450056401d0051494145010b4000300920201c440080304500005000d204d00d40e51540441d0107554068404441c0c01184000500107241601c082150034a0b4000081d9800358a08212002d85564000600040d41142c54013500c40004205c1440f0b084000c00c0240082101444440700b11449440c0c0c00005d460109003c070b409082045414006c03418144224055481660075250303c6112880e01d041160b9444a0191220b00720743d01c01c581090f00010091042c80d4107400620184500340081d400e825950401140c04101130f100103800683c1d0b800040c0980c15120384150903081c0149804501e010300d1800440455006840860100d0000540f40c000e00e07980b04005441b034a1440002c101c1407600c1c88004d8480c4681841110b070400c0401000401c5580e104074003c084c6070411401c548410403000c10404100d429108d50001c22280d200b030b481c242d80f0903120100d134030b88040c0c29a800c5032100c98427904204406021342d0f500440d80408200070402c40c0c40a01726400c5a07114501b40e103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546440377 1250 546439127 546439147
    0x5030a080a12020306090a0e01060510020a14151816090207050114160c02031606020a0b091606110102070b0c0301091104150f09081f050717070e2202 66
    0x1d020641d03000e102a00600400044d503840c400c0d400d0340143c048002158500c0004c01080c01803149800c00c5331b1110b1702c0300141485079400078609468078840d80381c0d18803618004103881ea48026203040a5030a0000000081180c10942c801e01c0002800300f04035111941286401810740211350401981c240c0d010a4078004d1142c00d00401082c0091200c0055840c18041082610071060660640501007802004400c40d201003040031003280c0000c072140d1020b070321094000c2d21004c520704240d81802e085404104d00c120f0100390030807111a81c40240345117501e4a04181c805600c0070400440c41d540c240070000c0811aa41252403040001d00c1c3c5840c0d881d81817500c0c6600301d80440149a09141c004d00c001c2c4400306032000308820040b55410325148206807903904490854841c0c10a04250051801020505041040d843c0116590310001e01060780e82420440c2c0750309a040c14100070011072008102c2681c00b41081d07c0d2058800750a41204542c0c40111640042112452885072070b8006218004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546441627 1250 546440377 546440387
    0x1602120c0d090e04020a090507120908071226040f05150f1303020606060d02160c050114180f04020c0f060a0c02010c0507030809010609050a02030906060102011b0c050705030a080a 79
    0xa44650801010f4900745074000c5607001c1200e00440200950702e030080342015000360303800030140401d02018440303400c035450000d049820800d012a0501d401502d003850541c0148103046036520303144446d41818440044088850b040944196000f2030481d9050300842c4090001024507050560f455016003440002001017080081c085000008045083c01c002940403800580000044480603121580ca0584100078401e081d00400d0502c1070240520400100010701821a9402d0702c403d4025081c1c0d2100030751500c80c00c10310444e0184e800303039480f42a01e400d400101c01880041c10060508600d6880b291504c2d021016170200d940c0b00c102009034005d2140180c18006401d840240490f0309031840150050040540060900c901e80300012000c03042540300e04000c05041e4414007840c10901c401c0b400943c02039603d00c201d809144009601075005014400b845c894281041215280d0301070225002200420212400d005046001130b4680d0108601618180201c0d16240c0d20b00f80008041c007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546442877 1250 546441627 546441629
    0x120302030c06162c120a06050a050402060f07060f050718120b06060a03020f030c0a0e04050c0901031503060c020708070e06060f070f050111090301060605030f1602120c0d09 76
    0x10703000180c1c165520203140c0c0040d801001580c2c071030716000168000104c030032001d1803603e0419040400141140e0107401e001640e0030001d0b021300001c02c03076900c80851207016500110f401a400110030018040103442c1d1900900365180120300024984245122400c25543d060310010001401d01080c6240d070400a41100001c1c00000d02d58140d008943e544c890405000601040c415200401e80800c130b94040d0701120310200007070302d10607074a1410032141c0307542d80c001c45140b40005012030390510490816101d154001d1010320303141420704498200450141c241e400c003001048900250010020b1005d00076141c8402544d000380c0229424403070260301d800407503408000624400400d00c846a2140307001c035810302021495081c1c0d0792a83d801c000c040c3e0043d41000802640c038008014144040781d001078500d88200314000d0150325a19601140c242c00181c50407030003061186c021844a004506031207040151030700548411406081c1001540c0c0c00518024040d904420740e404526548400114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546444127 1250 546442877 546442891
    0x110f030102182205010305010204090b04152312010f0b1009060f210c0210020c031803010608030c01050a050601090305060f07121e060e010608150604120302030c06 72
    0x41c20074590000b5022024040800640110300c0304040d12881101c0050845001429102c00c2c080c0d9690307458014000d41c054460307265a01c0c175064007421146802c0c0503850503070310101c3d10903008a060842c22419928840e242c1420084260280780d0551039010100b104070300540c5c000515034001a1540041d2600701707206c24400e00a0405000c40b103500419584103681c000d140051890624180960300088840f01e84116143c22003200d0040c8032040c3c1108080c50350351f42c243d031000d1021007015000d0b800703984080e00054201b03001704a00c11103080f00303200701890003c0000c10700c2544d0380406825580480002202d50b510307a0108802c84140703004060300201c0038039064400c1491512202d486240c0900005020303e40000420506440790421101030011441d0070000f0704480b118500248290118210110342805030015564080e070910504895140e00c4002403641c6180c40030b02c0c000f0800607010b52103074051201086d1004140104c0103200e2013a001565264140c42c007861505400414207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546445377 1250 546444127 546444131
    0x10c08061005120403050306030a0605090c01090803041a210106082e05040c090918020109080c0108160203070c0f051e0609100207031202010c12050709120609020d110f0301 76
    0x703034201200c3e55036040d51140c0c243c81e00607165241c0000003414501b003107201508980c04d040500404520202d10903d6402007600d80e92221075031050039603145d0003148101e068081d600200d001105030030720b0040001d0b20b43c5800410035030381d0400a045c007912007a048800020b00138000c00581d500741102035101a51039040e0211010b45168a086000d02c0500405000710f807600d44681c00c05014040400143c00c020030184010740c1100e1904001c0954580180e0010f6240fa200054810300800d298105240680d50200c0d282d0300d45081079810301c3d4440c401000c51204006900108103000507c00c05800c040c880c040c205442c0c0804c0000d5100c11542d01c001402145003512000d5480d8401c48030380d140305817000d5195142c40d50081c1d007400381d59031000c0c08000d0b080c00c5c0f900501d03a045d4411002450b40d038071414580301e00141c1030340c102d56007240c40c03001042d00c00d881484400c5481c0b658030752062240d500868480c840c1c0c0e01190010b03440380001c4070a50701d01e07001d400b43d078a041e25098443c02400d03030007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546446627 1250 546445377 546445387
    0x913050f0901110708090d14060912071a061809010507111605010e0319080304051c0f03020310170a11010e06090d030905060708091512040b06040e010c08061005 71
    0x3281e043d0f44070309a001064120005180c18041d2540350380f02da07a058210710001291001d400304039440d080c04440c9581680150070810700352801c42c105071041c0b280c0045080c02e5456034040d0b40d40c3c00560140c003103584600c0c800f107012940344400400501c0348003007a0011400e03060100010b40642949180c44055400440d80d05041d9203442d60040c04940003442d054000c002d450000c40c0c282000d64621810120401c0000d00520a06100440c040c41c468000c58000c0210f6540303500d01a00761102c3c1c1c1c1d0004080345503103502144250080e58100b101544240030380c139900c070000082180004030000e100d8001c8100e9405108801418404100d0203080050320f00078080e001035450700c10f0400039032040103d0f01c2840d003410301c1003170610003500c0080c200c0c50341c83c0711600f000c11140e001034102c0f6126050105170005615038000a5450020300c424549d000741d00c455468032120b41000308020b800655400b41c0c0301c1448424040e500d0102c005469101e050304000c410302100082c10903c0c01d081c002c04120b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546447877 1250 546446627 546446651
    0x409050f07082b1d13020d06030c09020403021f0219050a02130612140109080a1d030c010c0305160b0115020c03120f03041a01030c090c1d010e060913050f0901 70
    0x711000c8100162030513030078050300c2c040018411a0140c600c074884c10b10100b54004400ca0950158050300d00034840c0745505035803442040242d00c140d000c000d401032804032840f52a54420340c032a403050201d47c01590404004690300c250302480c1e82c6400d81d016030103c0c10001c1075080c150540e02101019010910900341010200f800c1c251860100605000d19413207607025001080d4450100a0340c0800030940da4450800c2c001c107010f19503013a4020b903202000140f000303450000f98403d25803106841c2c403118021251400d5801e5000b017030045080d50144000c2d80001400604564081e000d060840a00754091007802450210b10110140c0a03911907008012081c40703d07015100c1e884680c0d09026a04da40358034003032903201415910f08600a038030100100405c901c01ca001c5040c0c4040007010091000b80720300031207075102501c4c9007134041c031003001010a86500c5603646a4600303401500b0989803002200c00306014407a020b045843c030301d036294140141200c000c0000c0342c004001c42d00034054600c00d12 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546449127 1250 546447877 546447887
    0xf04020102250b2b0209031203060d06061502010c0207030519031101050411040c180b250f0b0108030a050a030b0f060705070e0703090b060409050f07082b 68
    0x9800900400140c402d0038040d5001405410162126580c801e07201c074020385002d820081e4003d443c008500c80a00440192540c0d0320954100c080006c00808001180410090070341e031024140743e81004140806c10007040716401000020943c40c41a00c584000c2c14000900311498550b00f102190081002000414400280c8951541c1481d440080303d8074146020f80d41d00d1078103684074210b5400c150400041c032000c00181d401541096805010030045540200c500442c0003c000f907a118a06405000c0426a10054440c0341d500340b0040180e090300581c80100c3c15019401118040c2e0007101540401040e0203000b80100201d10007035051101c040d9018042d805042d101d5410583d4a4002002c80e40d04c0703030128141020f010700f02c00d41e40c04450504c56159196406081d10090b50b01c404078008074420320905050940118240d01161210030801c07018000c0142c0c02d4600c0d02c2505007680789014140007000040c44610002c000300303519010b200300168408600b40a2030102c0350944000350b40c2103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546450377 1250 546449127 546449143
    0x80a110402090d0506100609090c08070c060b041107051009153204030336170c06070318020d0201030b120d050405010e040b011b0c09050408030f0f04020102 69
    0x3103030056220265100440d03030032442d112010707046100d030105000c08990780940007400ea450640d02c400d0000e440d4420f6800742c1d20420407079800034000c1400240070324030811940c0302042c41103c02064001007000020184c4e0030b1110711000b01c900016181042040410003441e0211102d03005000001c4140c45080d003550b105417440c1707d110344900c0c03d0f04141c4c0c91088a052002c01600460b445000c1c60702c4e00b001036600449049010a1404281441c1103112a8085121280c070421420b06844051940350030b00c1d650007021200240d81d004d010707180384003001c0644500c0950100a084510f44101d0081c150b03429192030350030111075840c0e010f0150302e4514200308042c0e0207080c0860807501d14400318000c2055100100d03050700500c107800c0545948240104100c4000741d850b004a1500c8200f040121524901c0c281d01007804854407900740359081c001030074130901500c10340f000141c0c1c422480d4240d8404603412100110000200818800c078046019044500ea251308030551400d6400030356038000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546451627 1250 546450377 546450379
    0xb030613030507080405100c030f0c02092a030705070c0609050d0605090c0405100906060503011508100807080a0c09020c0a06020306061606051b0c07060305060406240306080a11 78
    0x2043c0b0140300d401c4003228001c003406010801c000c80e041e200105004a010700440005030a5020301c090203228503200300000303030028103460306511440315258100c00d02130343c0d07600b4002d80d00300c00c40c4000d40d80e2405540f080c0c90f03946034142c7d01e20707561510303228590f500d0700b10000380700203000b0903c001d40396000000344081e1b0141c400621901e520852521309050352144030780c003a081504000c0c0b2543c400040d6000c0b60702c1984144070154895005403603e001c03d0052070003c4820300d0582ca5800d101eaa00c0540280294480095040c1c8500c3d81508207000ca030492109036000d01e07603640802940100500c0140210b400440c24040c0201a20351140d40c41e640140c144c039000b00c04122160780310b10840d044605a0b0220341c032681c1e081c0c43d1803405040100c40c3c6200d000c40b110111207e0320454002c40c1c690361901400b802c007260605070180d005040151003540c1003507a503480802c12022244000000d50049099412180d18088009042d14065005002c03d07400150b01c07800040d00d0120319200ca100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546452877 1250 546451627 546451637
    0x32104060e0609040510030b2d07030e030415093c0909060902030708240c041502030c0f070503070902160203120d0b06071e15020c030d0b03061303 65
    0x22128000b0310380d801400c100d43d0b0710503d8071301808509103010b100d981c1180c0c46004034010a544031006085008d00c0c07031400751280400081501200650048040e030b0100d01801c000a00343c503400711852540d0480d0300552400301d640388801801d503401500950042c6604070503400145214a154103251184c200b9034411020b44075108104152002c07543d0003c0d1200c00070400c03655290f8146000078284011782613000e80140c29006c109008040391990b610003a6285040403149582240582c0c10001080404084024400465107141d0700c004004168156030045d901c4850322000a420007290341e05107074181d400791201b0441c035140400e51200b1039002d10401601d480c180c226084c0d0404520314000e6140c010551403040642201002c0c004515400c9410004030340300800740f182c02e04c80d180c000350441008406000401d170519a440c141c0a204401c1000d01440e40084d8900340c1c0c0116004c407510760008921002094450b00c034280005800300c00030050307814802624104540603403409000c1103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546454127 1250 546452877 546452897
    0x1030905010b0301020a03061a0a08010b0a0302222412020f07020307031b0605130504020306060c0d030522170f130602030417030a080c0a1205010f0503210406 70
    0x50079405140100c2c40a4000d6588030110200140180220b008902c3c59079100d07140025840054001c1d00d010340c446460b010000c0e420580315100c65003240c010301040507002c001001716020030300c0c800118002d64041c0c0004181c01c0c1550a0303212400c66041c001d002142012a2012035409250b0818480c100400160344104001c486c03c050310030320718045d405204000002041080c401c03000208810700d5130400107029107504044895102c7d00e0441c0e00c2a400c0d50b501480035140c01c1c0c1c01503070880d00041c02c05103040200e406650601d0301d61428140031036a21030400605203030034070b002c0c0807000722801e402107044030503a00d191140045410190348081c0c003080b002001103490080303810103000c6001160300c0e01c1d580c20340255a0391180c000c0c4594400b540220b4852007100005907591501141c842203240d680b0803080d58229001102c0100030011080800400703440b051043ca03003e03040100c0a480c8140c249401e040c41c082020305c0204012001600170ac203080e03e42d20987e02554160700d0322001003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546455377 1250 546454127 546454133
    0x9090402091503060f040c0f12060b01051b1b120a0f29150a0b0a0f181d090c0a03110a0e0108060a1a0109031401090501050f15031209010309 62
    0x150850b403440c0c2d014032811051151452182010503c5644100c010203030302522510f480c003110401e0711a5210024100842d200050b0040d0011115890185019400c14070030300715a0044048000d281a80b030740164416600761251078040ca82038110595014010748855022140c0c0c1e1071170b1010107000550781c0c4241c881048880c5d88190403220700790000842103046100d810140d000196080014803e541c156801c2600700621040200c8124210f640c0c140a403008054035416400c031b1903081000749110000003401c20303800b2803001030071030100c01d0030380da10307174030526010a480c0a442c0c8400350713001c1c0345508026030b14030a0300c43c2a6548511051140005040813421400550300300e808486401800880c0f004000074440d4400c0501c15810301c4981d40c01014501449131a0710010f0000d10f01200601c00b140c0b0911583c0001d14050000107034001d04c588482d030031030b07400f6100c501c03c580e541014840d03050400702466841100403006030841c080c090342c0b003888900c50000a90305042d1150300c1031042c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546456627 1250 546455377 546455401
    0x50f040b060f030405031b0a0b190f06080f1203010b0f07170301090b010f0305010b0a050c0a080406032f03060d0201030b030d0f030f020405060f0c070308040303080109060b0909040209 81
    0x80003418602c54a81c02c1c14600a5101e0300000c0c0502c44282503100341c811001c0c40010000c0aa6400c0300401d0701075100c140c0d4203e0b1300300740d091003c021241c032070306401c00115061190340000c00c11030b00074002d10740001e05032074180040700345280003030441032005000c0d03a00b40008907080e450000d55210b0b9161200d1400e072109051895000c0b04110020000082c0e001c1540c1004100000990b03451302001075480b800c0d4100d0b03100b80141c903003841062041756402070040005100410a8508882440f1001c1d51100d8081d44140c1200c000079841d080e1180c50b200c02e08080d00309000ba24500c1411403004034000191030700005007510304c20101d01c070307050042d03902a9100c40101e10000e0305070b8461030305a909c09448800310b0450b82000074640264078890000300c1c0309450584034020211440c0c1903100420108a4016130100031090180c90303000000139002c440180300079840b13502e17030014075890002194111080740d0301c0544c10000c200124101c40d070b50882a59402a030485001c10035450710481150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546457877 1250 546456627 546456637
    0x18120201020a06060321020a030215090c1f030501061106060d02041e0c2601030b04021f0f121103072d03050f06040c050d0f0f2d06050f040b06 63
    0x4030040c40c4c0304000c13045c440d00c0704c405c1c10200c40404e60516800344500d01281c0e1201500c602500581180d510080000c4211010a40040340d801c122405101000c002592440c1c00b0294544101c010000c031029658141c000c89005203043d00300a4581c041a04640c0c0e110070009015500c03c410034140035003190345551190401020941c0c05484d80c0740840202001007103120958030218654050101d1904248810308600745081007000ba91a403841d55401c40318400a041283c1c80300b55544600806422070b21800941846a82e4107600e494140c038000c0d001c8066130301915070741402c1c50340410348145401c003102c1e0445800d10702500812240e00d204400c645520354410560800d00000c110a550b05800c04d80c000c40310405020880e40720b000410040b221511308080202d0400e1098690030207655010220381d040012000c034006944000c00c80484900030104008000041492000c520080714800040d452411041012900b01800120f0314041a01d01c1031145440e1f6450200503160790082e22 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546459127 1250 546457877 546457883
    0x110304090207030f030b121e150f0f06030303010f230307080d031104290c120403030305070e03030f07050f0a06021c0612080c19030906020d18120201020a 68
    0x1529594140760060002603c40c581e81c0020f800c00b07886e40351514120f24039801110405d00241742e8501180c14600003208410340000310b078001c2c4e5200746002042070140520400742030307035020315034540a00d100400c0c4d8405811b042c02035100b400140428940d03152054107445840801c118440307507a00700789101c0c071402c00141d03405010350f507000201210000b03200d4645c0310a58500f8080c581e150b42003140d0a00607489800d00d61038a130b503004544441030500d510740c59518040c01528103180c1c1045185000100301c0f01b0605400c1c00241001456450b1040d00d8110b40e00e031034503003082000600020340c0c078055542d58071070702800040c00c2003c1010812540030305217110000d0b95214a02c50804c2e000941117400b484502000c00c420f100107824a501ca0002076503284191141c400c1c4064076400f6240d0004d00502501e40724030340801e1020000411040724261003580d5141c0101e0802e00000e0526a240d00c081085c030030a0a0561240d51044410f002030310401c030280c102c4103c4a000407881c0075005000a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546460377 1250 546459127 546459131
    0x50c0d060b090f030c10050f1204111e0a0314070e012d0e040f080d021c06090902090f07090f060507030801050a0b1c0b040e031305011103030711030409 67
    0x168407040c00001e0542148110380e0b0701c11402d001e0061648034111206031560001d4030b41c014000c220300800141908815401406042c802c0011490038105400e031410758402c4420b00480d1402d140421003240082200740c002100900c0a0000c1601903200703000040c82c0c171031801d046e0090b4500c01c100040003403a0f01d50403082c1c556910111b40c4010380300ba44c1d05260149421521002c040840300c0c0c6030f411100c09545900055640c1e0b21018110208104102e601000804c501e01c07440c00c44c0d0001e8000303000501c00004010140900c0031040303514650000115a0902c0d04d4030300565584894141d200c0140107001c1c00d141c0d201c1c04202d032801031270381001c0b080a41c4540c0200f280ca84c003002810171607220f912101701c20b9803500b0810070650080e210303285401c8030401c00c4000b8031040c064084c20740074400c1004641c403007200000505032590058141015840071401d0f100e400b072403a500308010a0282419a10f5210404900c0d86912004044500348040540618040082001140c0060030036580c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 546461627 1250 546460377 546460379
    0x81b010c0509030319050f131503021e030606090d03031a0411040905180a0503070c0e0f060409060e030f07020f0d0f020d0c03020a0f17061618030c030b010501140a02030a03050c0d06 80
    0x1103061607020301440003013450280e90449c0b114024400c6404410403031984610081c828414140c261340020103090f0032601c18000b0310000e44440c1e9895104510a880100700e007078982c288170032007006040440344620700b00400c00a1622181c411541a150404000301e11681c80039190034111100c804903080c503204a1801c0014024080060300442c0d120b9030f024001a60398842c010f9480e40140c1780401d40000400210780b2501c0c00382d010100452040001060050800c000a821900042c24000140700002130001c00c5150600000010003000c50f071154125440d9101d0f000d04183d4a60000c2c02604845900070034000c074080644001d50b401031004c003000d61603804081400000e0b12601507101c4c4204030001600c840410198171540d92003103540e0108030031003411690000c416041c480c0800d000c0341d001c40810a070100004c0590701624a140081d4508400188080010740c01ea5007208001e1204084a40d0b01104544181101c2d00c0c000c9a070740c56492a100d0705110b90388131009150300c1c08074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 546462877 1250 546461627 546461647
    0x206030a0e100219050a0c1209080f010203040f02040e030d02160b06010e011e12050c070c05090c03130c0b03040b1506280c081b010c0509030319050f 66
    0x1c0000072031052025030b08019484030003941079000d43c80405440b103940ba5162400184200090400441d103483c02c41d119030703166250032001c3c3c0d0401000301d0014218079018040c103542082601c0c151300c07100c0000c61071840c0c5526000030788022500028401d40d1030b48803c001c98141081960700c54491170388111340d03d4951340f4030401d40b6007000c4800c855410b0b07031b40d0006900f0760241c2451400d408060b1600f00005035001c459000ca445142043c1e4140a04154450100103862040ca40319801510216039200954207004018140d1540810300c034110100800400e809800c0c02d4940001150f4109a085c0c02d0620309103d406106800426480f80301000700300a10080810160080601600b87c070701c6844200180403541c442e003492848050007400b00c0c2212a045103001800e2032103640350445020305a5030756401d0390f9101140d5041180d00c0c810b0000702c03000d028400c86260328058182145010b5501c0c0109403280101004802d45140700e1104034a100c2c0907404072022414494034681d1740b40c003030407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 546464127 1250 546462877 546462881
    0x21225140f0d181404092a0906091104090c140d051501020d140c0a0804030f17040315090f06050c040807080d081315020a0e01020606180c160206030a 66
    0x2e4021000481070509140958561011902a204c100300c841c4c800702c89020522010b0b14a1140440742951000d80d50748208816525a901000c4134100e0b50f0b01181c9041e003001d007a962141c10500c1c51510f0500004d82c0c11180b28200c1e01110401180030407102034031a01950300031104060400080030002d451802441c01c3d0b8040d6118078420b10705a8280102180126074800b6031b400003c021400a0003512140745100b0054240300f00b503c3c0c1210301c4840301d60380d0221607070015442240c204031913000d240100301803011912071070382201440c40e08051a6890704240e0400c0c51030100e515079070343c000000038802c84514080c409500440c0c140030504100500c0206a070091140644034051000080780b04400420000301c05000b41e624020252164194490071100003401103680100309040081100400d002502c443c0c00591511543d002c441800a07040500003408607100362111403000013106100500180c000795072032407041d1642c1ca00201100140e15494010f0b43c0080007108010750b4030030315 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 546465377 1250 546464127 546464143
    0x60303030907260d11240a09020f031005190507021c02030909010611071a0d020a1709070303080c070b0109020a0e0a030503030901290609040921021225140f 69
    0x100200c810550ba0300546c903101c00f03001c0c060f100101c0d03a4040420618522604134801107400203010720700e411828000689490b02d17489509103413903100c00c100b00c6c01e00350805201541c5000c0d540c0c14041c80c40d1182009403201110044414109032003d5145002d520030015a60340727800140bc03a00f095615030354064044c064030025001c60703104200c00850001090f5210070f440c00c0840c410a8146010500c10002039001222000c0c00c0140381c1d203410403140e03040c1003510b0244c00a40e0240c80546d065040c001c1a02d00004e044180840c02041900000b80711900e60504403000034400684a55040c9000c60f400e144400807582c0c806948013021003440700c0031000b180181d1415000f08800340350b50111a250400700241c0e9000148140c0c16140d140c1403003002440c042d08014000a01c1d00241d548900080e50441d0060916500c4440341c54003441e0108903141d220804c0d50011402c0c960b1715507031032280c81c04031015021011100c050020030000000c49000350085407100b603030200490225510355801c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 546466627 1250 546465377 546465407
    0x9030b0a090b090c10050a05030a0b04020f040612140919062c010c03271a04060b0f04020903070504180b0702030c0105060a0308030109090c08010221060303030907260d 74
    0x109800341c17074805021b01e0480e108000240c0b9107900310b688050b0003400401001d000360740c209808010f02c402d040e20752030041c00a807036a501c07030020504004590908803031a001213a40d14201c0c642c1030020510f00021a0f442c40c2c00061003100d2075002600d4101c01400c401803041d001c0711900301040340e001451903070690040100c60020401049100802c40640341100c0e42d90b46001d51070b1020b070306c294030a003021204260040c00302c160120000b59501c8005a022202602d0f1140d44030540a158940400411804a4100d60650500d00c1078000030b0740b60000b9129540c41142e0711041050052074051901490301d80064030742101f481c2c50603005e902c079404180b990004d9480d240009070355142c41c800110680b41c10001c02400d503800c1481120081517108000d41e60302011400000d2000301c00d000400d419040b441040c224054180b02248200c4005040d840c441c0d00f041c403c0114802000400703c084449904003040c00c1c220342c050280d0345280d05801e42d01c00b805905425003013190400c0c0c02c091a491 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 546467877 1250 546466627 546466639
    0x11d0d02010f140708090c0d0606170d0e12120f03060901170303010b0307030e070807151d22060e060906060703020d050d1107060b19030309030b0a090b090c 69
    0x2140b4034030700040b140307034984441c101200e110116806078030a040700c503480414181110180032408001408080d8498000c80da89511590b082c08000d030140301d1f02240010b00c0000702014810301d0f8000d070516042084048c022a0710440405208000f007004500141880304440da8841030303001440c010780d00480701e840c080c0380031100006040581101d107906400710139001d181181d003440340b5500c20788d1014164001301a00c800003b40c035030105105900081140070018804140703004503081b000401044d1900a002003d03c0003103403440140d01c00c040c036000c100c034100504043c501c00c3d2000b01c070425800060491074030f40003042c45c0382c0c0d0b144800d0007071104686c8500144c2c2c40300100922486006001070041c2c0143c4132105646010f040504481c60350703c100440c1103504102900d9640e001954240c0e0800e0319098418200c1c03c00d0744204100009480ca984242402c585000e0a2a0b4451100900720a030020005281d85142d510005040e5840810711128ac10300c1d01d8443d507074040402819200310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 546469127 1250 546467877 546467891
    0x160615050612070507020a080d030e0606040c050d05070314100f09020309030d0c210f05010603090c1a1e0d1401050a1701020c010203012c040309030f05011d0d0201 72
    0x700d0080207680c50146140400c504950740c1140c01c44854210b0381040380c020f849550041240207051006444003042650001a12898150074500d40440a0f2200c1d01540c0b40400c0d214070705a00004480504108604c0426547ca600004800500746c802134080d483c000b0109102c210312000a0f128110f42d40074014000a984400c48403040740303c103403076504035607100b0014241d0111044e0402001d1551504180c442c40100c84660703050328840140180540da640c2c4802c9442c04410311516000d840c007460304001900d003da4941c40550b2950048000520115007601c0310000803000b00d60011000254800c4403280008a035030581d00103401a038415410102840c80701202008614100c440040c04205114540720711390240b40b050002d0601255000c0204803a480c500340000c50003030244ad0074900d090010700e80d0f150210850308031082c481108103001e00c8042944224550b060300e0700140c151005405074a844c900404940c203046149041408103101400004203a038042074660350000e102003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 546470377 1250 546469127 546469129
    0x51c020f2d0306310c0225031b030206070b0105030c19090f0f0203072a08030f090c03010609020a1101141b070c0e040c06030e0604110616061505 64
    0x140410140070007107980c14070004106240440d0403600b403500c10501da401201d0940b49000d03000001c03680803600c44d5142c01801c0203041c1d041160071907800090100c20202a580d10030308207a20110f1101400d05003046003074600106001d0000e40007503a000b040165200400e140446080300c00f4803d1034401d00942c80c131180d080c1804070040c05600d0601c0c00c03c01002c0e061800036070060403100303503005086035240304400c42604a0310003540030b0101303a210340140e0000305501d44000c2c00b01c100c0b00914011b9407061080090003030780a45e5000607144141a502c2e03500c00819514041d09002c24590541c2444000128040e8070b0713004110350440c0381d455025003642e03e43c0080c00c0e600c840d59a880000d2198000a80c02c16642413080382040c81d181d1404e28000b00354423040c100c0704c800d801881e4040d022034280020041c481d40303080003c00c0141002e100d4020b402c0d14040d180c5000400141080505401d03e142d2966100102e03107103201144030040034030a00b810800300800c141400610036007850034000c185 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 546471627 1250 546470377 546470437
    0x1090906181a130818120a15090f0204050a0c0f0e01050d23090c0306070309030807080907180b0a060318030e1507030809060711030901051c020f 64
    0xe1590001403494684844881c40100072000506083c1c83c080d10402e1040050013441c0201400c6480c543c0c0d081e8440c9a84040050800300308400d45900d074402a6100d0004032042c4400030020010b80c4c0c001889981d40c2400044e144070124005c0d0321074135040400c01d241540780d110048412450307035100003442003580306554101602d80500e000c182c00788140d0000e1516030b0400030307a001030050700c0da036140c2e034050310505800000d0b100100c041d005000950118202007050643c0303c2c04a14091140711000c0d207001d4407402000d00780a040005100014081d044204a80c60040a4041c0c40c0010450303401d03540b500400f0340380d410b20b104d90b14441001032500c0c844c2c014141c102100d5000b01007186401d0741c00b552840d00c40028560045031001881d541c8500c20406840014003940b41c4129a00d03100d2801c81c20404020000c006101410103001110580001650000f81007800c000741c1d01c034800e8a05020342942070648404507800001c02c0c1c4281d0040030701a214507001c03030b03c005450280c01084440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 546472877 1250 546471627 546471671
    0x309120201140f0a08092a040617070e130f030806150d0606180605030c03070201090c091a031c0f05090a0b070302120a0c0602091815031501080606010e0102120301090906 75
    0x46018010080c11f40f070b5242c0d014010055400810025030f40713644070481392032000e500301b1141c0b10381c1096a04001c3d690f140085c03198401c0310010040c08020607641c0e031500e0810010070103402c121920780000c03c43d84400a08072110300c007426032240c8400c055480100603025601034000001c4210f04800d40203091084103005840964580500310398a085408400e50001000c000c02c542d210b05108000c2250103064401030a000c0801280c04003022120070801d9280c40c19a50003a4050381c0d032889102420070341a29103a81074038014520f8441030600b21040e0084005550384684040030000e00c4801040040a0080c800e8007074580400c0d903d58028800e0140404101c041600060140c0c0001c421b540200400b10001b043c464600c141051100104031b000c0f1005043c08804442169452501300000392010111482c0507101d50304111a040d183c0303070003400441c14482d170700c0f054818a0f80203001000441450007501c50716980d4600940025140e03141c0c094950502c0c0443c4003803da141043d45403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 546474127 1250 546472877 546472903
    0x14071d010302090601090b070303150b0a02060c030a0e1504062f36040b04201312110f0a24020304080708010204031406040309120201140f0a0809 64
    0x2046a1840d02801a40380c00104064100700c48000c022a401c1400e0020f04600e82c0269000514136808400200111b0310b02c0d0003020000380140400c9030550360020343c0c643e000122012164403a1181180c210142414500e15501d600407400542092018220994880c0f03000b644203000311200840f8485c400e13102a1420049640c40644400040340040000d02d10450103030700003c0350b420089030b43c00810503003800344002c180c1d1f02c00c00c03041146000d004000c14402c00701c404000c0140c21100d07a846032032000d445000003013001f048105000d001d081800000f007029007600809008076252004c0d0100c910302c00180b240c0f082c90310302c5241d0304102507444151140c20f01640402040e1864801c2c508850320505000c5120400000c203420406008010080040000241e05e550961a09428120030001d0740c0c04198013030b008100c0441d03882818281100c19550180c0042c040a000483d034a00085c07030b0b884201c00d07000441c4000d0849a5000703081d110007550b40d441c0d480d10b61500154603140811400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 546475377 1250 546474127 546474179
    0xc07080a062a051c0608160e010617060402190521040f0201210c02100f0e0d11010f150819020102030f160b010b0309060108190b09191407 61
    0x1000da00e00075401085051000c030003413070f0403000c0d80768003c2c29603080c0d81003a1001e40001030800846007132502c224014000c030361000340940d07041c05402030640c040c1d801c0d00c602c2c0c007042402045854035582d0403142c0108a803101d0460034006480e015040b5031002208808008400d0401880c000a50044c2d80c040c40d40110f840714408816001183d02da94410034140340c04001080340c60600801d4401c1c4298010315401070300709007520032010411541108030070743c0309504040c5180841800800c84411020b018109540e1000b00c01484034014007081107079407100703072511418004e142e00c1007030030000301d50000046032805111803c0d181200380b48030380001d025910501c010300500d07103000090450310751030f800f401d01004110b0b19942d00150003070b805152070045c0041030100e00c035414030400d40035042c00c6008141c2d0041088400285488400c07018041041c0300c400700b0070800b828400400721002002c0806900b04c9681420f000c1c21052031441d111a10605900256000300289409451102e100388 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 546476627 1250 546475377 546475451
    0x70503090d03030f0e010c020c0111072c0702060412020a02090406020903011e0e0c09010608010b0706020f1c05070c0206090d0807020d030c1b03081b030c07080a06 72
    0xd010030070210060490515032030721640d006102d030754402c83da0b02c40322040c0041921000c141c40a4201059901a0b50412500841042001c1c0c000100c08044410b0b50101000d2022590114101c1e421551043c1d11702549507000d00c10359650000d006c0f401540218400318016500d0703502a83c1e204a0385100a4005502074001004180e2650240c1192130000d4000301c0c0340c3c01c0d4600d0814040c01c03420440b41806554440204103a441000450a0414142d03001e460700d505211004e056610144940c2454100019500d000c12544e40c040d03d54035800c1c8100355441e9020000e0003480c0c42401c8d02181c0c0b02c1f070b1820001130041c2c0d1007402503409140d00a0080361a00c1c4c0c1c2c440034071050034105801500d01d00400c0103400d0041e150010007100d401e020b070350b40c000d01131210300e400200010b2882e224018058498002c1c40400c2c03003003080b101000d0076054540a440c91101f0719070700358080c010f0782903801d0142d00700016800b000460980032041c452001007008080700d44d050003413104061a00307040c907000254 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 546477877 1250 546476627 546476629
    0x206060a050d3323010504050105060f0f0915091912020f0315010e190203010501080f13020303130617071b0813140301050f0402030606040c09090908040f060507050309 74
    0x40e1440c00f045050302c0e240b6008821400c40d20075502209603842c1810303e0100c0e40c0d2260603541059901510088500707026139490100054028000c5242d01c80b10000000340c00d511043e448400c40380c120b4405842d140300040f004000b450b944c5c0100b50028050010660700e10009111a5161340c2035507054640d20058442503024420001203140310320380c15106490101908841035000c660003800404031410882c600128840c039400c0700700d205c1c1c01d4a180180014002aa04544010342c4440c260407009007a544000b103038000c080c04110040d415020014655091890401980007558110717210714644c03450445e1100645001101c07204005440410303030464100f40030310003001c0d940c00b4448503403d00c01c01005080400044d684110049c1a0405211b040c0307050038007410381e00040300d40c085d00c107a02e041d0300840e440703a1000701881d02c0b50b6030300c0060f18002802800a80003170300c03035100100302c0f010003842c0207807081e44030f40038002c02180c2500700025540d2180c03040304d0100d035009019500b07111243c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 546479127 1250 546477877 546477923
    0x34080103140a032001021c0b1207031106070204140108060a061a12250c12020a210909050c0c0f0a03050f090f0d1b060509150d0e0d0206060a050d 64
    0x550b40c4c0f55502040b858010700300c0c003600c2142c070003c0d4500000710100e004042080075040d085200c483c58000300000c1000c140c41400014031201c094a13503580d100c48038800035000341003024001031107030f45410000ca44070740001800340c4110085841080143c1d1038111040400134049600d0340720160070401c80030781c0c0c540506140c2e0011900047c131030164507101d14a008001c0c1110348a40050080a400f01c180613030b00000300c00c5c171142400a8201682d2a8a0300129448280380001c6544440451928018800c01c030300c0009001c3e14104101c06c0c00e01024103000c61380020080c1c5543c0c841c44481001180c0045a074541035039241d255546040e854800078100e43d081100c40b950f01c4480d0302c032118515112000801c0d410b6201e401030402141069152641c4400260070943c100101031002c45a00e1304c81140c00b80144008080381500c40a10030300d104003600303070401740756181e020300c00e00c3c40c00c401d400044d902c4c0074580459181078015160341c01d1000005000001505407000a0380d0446412494 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 546480377 1250 546479127 546479177
    0x2092101090f0b0403080a0b1e0a0b0f1209011b03180f080c06010806130201081329060402090117130804270e0634080103140a03 57
    0x14000030800e8807203a190014208028241540c3c4007084500304810144d003c0b4a071030380440d00c105d0410401600c003000c141040d980030440c04051402c8503a25045503654940c40c0e0040c10070620031a03450100a595400c00c0e00320202c254103c0f0092804107103400410f000e0b1104a2a0016407040e134502d042070308401400e001c10b0300f14000448000d82c8000319280c0601d08960394000c00d10103036207140d124405442c00740142c1c01503602d50001c0040c050700c20000000704406580910708103009450719528034224445040e0020014911040d0301c400806840303094101d032070f6038418500d02c0c41e0391780b40c140303c01c0c0d104107003540d400144040104d0514a0710b450380a50050f0075403003075005980141d030b54100d01e036100da00941c2c10944c101c0803590380000510f00c14003c140343c4c600c1c140400c480b0f00700001c0e602c2c04094292410454000d0209940069408034072032506c03e102d40302501d1840c1c0c580050701146081c0001d81310440da91982c1c440880d000522811007075415034541418800140500301d42c90b80d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 546481627 1250 546480377 546480439
    0x501090504092a081005090c030105090601060f2a0c0e0f01150e09181e0706050a110319030b1914180a0c17040308010b030a02070605090c010e040209 66
    0x540000490440304c00c00c00316610462607200010f039824868803a5162402c02070000340b02e0713030500041040000d400302d41c3c40c0c110b030200e0614064002d00c017001980c3c50f4154806106621030300e5403000058040394104034020f54060002a103980d41c80f054401002201150090750240682d030041040d4020b6a6141103070300c0b0185015840d240b6694009003020506949001d0526841c0ea000840c112041c8440710318001ca80b45c07a499a205411141070f00d8202e03520540080c02030100351703860b445000d000ba400b5010f0b100c20659075200540002c80310081e80111034400028135241680c805410301300c584100700002900e005085902c0c0c814100a5a400509540c3d00103488060400000506180440c00303008811400702c4c201403041d6000b88181050107241079090812014030010a400032156815103a40c1d4190581e070713070344400c41c8001a02c80c0f205d00401082c80d104c100b104407180492185079154090381d440c84210101c10401050b4003a13540c11640c00b0726800d19030b1ba080c4910751140850101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 546482877 1250 546481627 546481703
    0xc070c0503030a03090605090c01171b04030c1a070f0f0213020c030d0b27061c0506060301060501090b0a0315051908060a05041109041b0f050109050409 67
    0x52680d0210341150400081140426240c0d120a41000082e008090740210301c44001e01c50b01c81d151000030306034a01c40d0f402421034540d02d40451303590a2602d5452030940001080d0540d50ba0b0b41e45410480c1c0b68540c0b003000c400f0398841100c000c0e4185d1080440d080c8942007101d4800400807901d410b10409100b20007217a004000d0b03880c0410300c034950300103000100c0183c401340d912170701620310000640300d00f1521144038446440401c0906030100f1b200d41c03031152000408070f0940e5100c601107194003145003041d000d080300e0310b441141045030005d401441000103500a00c00302da912801901d0403580c0c1e02400184a00c288003030140c0710b1080d8407912165401d143c280c2111a0769002045a0410032000b000da0502c0c00882802407400421019070002c001d55810429450940c807100700c400c80302c04082e88105031400c0801c0a00110142c0764085061003100003030750070b50b64200f0340d1180d0442c0c130405000c924583d000003a00e02d401d02c103003038000750403da0300d10750750822002401189100740c12243e03d0300707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 546484127 1250 546482877 546482879
    0x6080d0e10090e010f08060a09170f0d111b070303051c0b060a170c2104140d020d0e0402040803040512100507090f092a03061d070311030f0c070c 64
    0x4043c9600300c2e00a1041e030310040d80e00c80c141031000d0f042200042076160b02d1400d00311690000781070010024001000d202d52079441c1c4600d60640c411910071310a21500d524108800151b000e03142d0401002180086041d6517102c0040180c5030b0b8880130309100140201e1000d000c1400c1110355500c0d11920250744120000d8402034020000711290440c3d10b4207c0003502e07605900704000648000b513600031184600c1d460401d060704030031089202c20303005091102c5d0104000b16041091300d0300f10202800403842a40c103c0428440000d681e410301c4000d00c00040d440740c802d80c4686c01c291003100d0655a0b80005036107858103000034071021440314005411144994008241d0113a4603208070303800f89003d036882441c458030341a00c00e85201d40540003281d03520303d4680301001c032a411112500c90620b200d140c6446841c01d030b003415801009641d100015002e040c1e012201101c081c040602d1041050741c404000c03290712120380503400e010403941c0314112078122002c40e0082c1c103800081c1010502c5607000760349803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 546485377 1250 546484127 546484139
    0x20c010603081227071512050f04030e1207140105160827010c03120b030f030d05070201061d0603012c0c010f0207090213080109030f020106080d0e1009 67
    0xa07800200c0111032a039071182806450381144d240c006600c0410007600326806401c40910f516a140d502c2002a110b61829020307403440d0048440d4050a62060000c00c080e11380181540030305c1108541c01c40000c2c0100844004900d00000000644240341c0d00a04c22a0708045004800b034101c0c20307403d81840402e020b1441c180441e00301d40005903104440081e02c8014810060a400c9003106c0c42c049190f000180520860340d003c680070450380e030907190102c0d00c591203505005c0145141440c90360103008000ba1051000d40010040c0503001c5401c40400081d603400d00c0c100d0807a2028021801c40c851004488071403070414144058000c03800400010303011841c54040c0f00c140c0c3e082d02103038102082e50030741d2001c411030611807411280b5003802e202500c040c000000944a0000340104c032a0154082007000000c55154178403405480c000008001000650401a111040700703004940150300700840810002c80120700d82c0d01c640b00c15140e401c80c91052904011f25402c8445052040002d8a2800224 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 546486627 1250 546485377 546485393
    0x3010b271f020f0a0b1f030206131d010b0702150903010204030605180714120a0f03030504150212180a050a081b19110604081516020d0210020c010603 66
    0x24091060780100300030010008083d041c030007800d5082c3c0013508411981e0703003c241e004280e10b42c800c2c0c114000024032103560440d031035200041c0d040690880c50100e5401c812484800915003070750310120000342300c19200c1c3e00e4014540030034001c0d010051400e0002c900141401005460080c24048c00281000f4103800400d007240c11584c000d03515151164140440d0f00c00310303011044211040c6c00034048043c10100f1041d20b070100010028002c2e0341e1864180c030401418840c07101800e80c41000d5890745c601c02e08000300501805e64050b50f00c0341d201840d45c21200f0342403080300c01030001500c00c032800b9510800c0300904004144458481c0b4056000e1010010300144542c803081480b5001031900c0f80c0c006201184203010b1b003000c110460740641400b11211060b0780f0300c1019140d00c072285602d00d040c00170100d905402941c1c0b22001c103100382a2003a003100e84107100c0611072054018011399844862600b282c0c0d40b0710256012000d40c100c010094800c00b580e4000f000381b9a02034001180c1030f0340e0f036030b16011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 546487877 1250 546486627 546486649
    0x4081e16080414060901020606100210050f1605160314070f0c0905090c0d1211030a020105011d010b0304060504060b060c010b10031103070c0318080a11010503010b27 73
    0x8102030000790900614840f041c404000902c180d440a00300b9144200103035481502420040c42503603c0900d0701102c3d0300c00c001f05402920007402c00d2000317040c140c0c408080840f040ea4421950302c403030720f141007080c2e104034280e800c0250710180a12108006032801c1e6982040e07203a15036403952080000c080420000d061104020784a200800f0b40d443c6032240a17021034074041c01d1005a40c21540352805181c0d680d01440c480107400800001d00e80f28801e0054074141041001702c285404041000f05009806511140c100c6080810100e921454015504003039082400b4000070314105201150102d00c096000710791262085500245040d10400040d5080c0c200234400c060710780d12800810020300b808004481c880f082410240190300910003003002a010040004040058001a07401854815000100c002e0012260307140f1854440d8081c07030300c0701c840d00340580f00c810018554900551280c81264104d6058075225800c01c40415610030b04408100d89514070841036040a240a60764110078034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 546489127 1250 546487877 546487883
    0xd0905030702041103100501050c010212040f05070914010e0a0e031801090918030503070c06110d05160e010c08040509010b0c06010911030606160c062001020304081e16 74
    0x588641c540e20400c0142d448100d02c0b58031500d000d1061010070901c100180d4150380782400c045840b8501910254024040c084044444c1c0c00d54005100034030140240d019881401107064404e110b868840040a40b890684040d030b007121040010041c0c2e68661001d15008980010003103980142c2d89141031868100440050b039803141000040c01a40c0c200c2c412100512096400707201c0d2040059607455040c1d90841e014003840400000200d030b50384250100304140340d102e83c0030800540140d440ac12207030049400c01400603d00000b144080c24200700c1000d03000a16502c0b440c6401c1c0c01001161191741c90304088a8200e024403001c1404d0303690b40d01d150302800c2403400c03154844081442017032502e807040c0d000340310041c5003011a04075514030404880c1e002900b5101130750345144207540f48040e81c44441018000d0418040040b61503a449403074481d5040400000800c88040c1d80c002600300c0c48150b80051800f03500300260001109524229040720307012052071802c0c00030074091f400729840f05040c22 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 546490377 1250 546489127 546489133
    0x14091c0f140c0f030a110604080f0c100e0a050f1512100b130504230f0403091d0a20040303111612170418090c0b1603050f0d0905 57
    0x300078001000c01456268990444003140f0030305420300400d4441005040181c441d80c1e5081480b040d544940c0f0861f030003071403008101da00442140d24495118060040c172280304025513100203034010b00c00c502441045a0007015542c0300c1c0c2c42c1200b00060340070806a086d0b00400e5100c2402c1c04c952040c409481e07100b1021542480030325040d020890480c00f00d80203c9031060301407200c43c649110b605449402d441c41511700084c041d81c283e44840c0d980c40032034101c11181c4010020081000807240403a40224401d80f10b68035820780301d41010101780344c00c00c040c00382e040c0803100142400043e81c2000c090b0b4051101101c20030310360319800c0030250b03025030015000315481c4000400d81041c1003141560703030035080d90400f429034201224050103003040c0d000034104d0300c400348840c40881000400c54004001e0b00310024140d801030b0f034003100900080c8005880d030186000002510610080032034119205003040a903101c1580c0d54240c94640101000c240040e2051103214440106071003003ca00724018002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 546491627 1250 546490377 546490403
    0x10f0c0804020a0515040b160b01090f0f200714060711151b07030239040c022503020306070908100603020604090e0c041803080714091c0f 61
    0x6104a500003580311501810311700d010a03100301c4035038040d40e0655045882c982c1d900e00100002c5401c00d521040c015103803000c0400000350101159106500d44480f0702018007181c201005000115885080001c000d12458098101d8145041005111251080c10700446244160780c10b2841d000c41141c1e81800318200009000303018104000401442e8030307841d0480407601e814103040700c2d542a040c45420400c9030100e01c2408140c001e0211400c0540005000b614099540f441500d0f00202314414000d10f0038050f141420a08050103144003004d8190014600c041c88400011541925000a02c805500c90540800181c0e000e0101070f0007080c0b10342e40d0406040c24406031905240744ca07c021205c1038585041080141c8800703003540c0441e860740d80c000070a045d940c55a03906045e102e0442c0359010b0315000e101c0a0b0f5641c1050000342c082e0107580c0e214041d6807081c1c401d03903807580f600414401c007403002d01c1602d5051404042d1091600d440010b03881c100c2e8020394591220030b8500d03c044400c0e00e24012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 546492877 1250 546491627 546491629
    0x9060602070611010c020c0126090706030c0207030b0705071e05060f0601021b10030e0f01091b0b180103060b030a1a0105121b162f090612010f0c080402 67
    0x140c83d904461415008000300900741c0006503075040c0e0781851605011090f41e050003100c5200902c282092101c20010700c09103411104561668110300a41000c80c2c549039101104d54400a464001d8a90006160400d41c4681300140c2d49030b000405c0844003100440c0e407d04144420030b5041519600c41d5000304150b0070007100300085144014422811948203180b085040f4604162100c403407842540d90b091088042502100035109000020901d07214912440240060540c042c5171440e0080194000603010660041d60b00c3e400c0b44030700044154280400094ad0204002000043e070050500050b031a03522a00e000c80303074104880d403072480c03507641c000021007030720001c01188040000d28010b071410a202d502441241805041500a01e03030b0b50400076821000001100d02d150350000306580059624a05840005101c00c21a2001515903240d003184018007034150100c0000140700d50b44230340d1000144603419103549040c041030b43d21040b00c02c035510990b00c1900e91000d003a655000c0140740c140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 546494127 1250 546492877 546492887
    0x81b0c0f040b030d121d070305070f08030301060e0a030b04030c120e0105070618081903060b13140406050a15030e24070e060a09050112060501050d1104090606020706 73
    0x324001d014604041d0300c10b95694002c1118201d203104c0b42400c00b0321002604075200245141c4094185403015001c19000341c000c001004011a8403580c21266144d440d070384170150080503413080d410540c1c8103000500030701c1c3c01400d01050080020b003401e2012680ea845030400700c3c40545003500440c440c01040000d00c0040d040290109003541040ea0550b12482c00091252052070000b60100e43e68607070303000c5102000c0224490043e08404000d03140c881d854040050f121941c03041102092801c040019440400c07410760ba99500c511181c0c4454526280c010f40507014441d0640b0340c426074515000c609640e5900e1108040c0420406902c0800b400810180844440c1c2000d19420391100c0c192140e900c01c1b00403402e0716900c10240c841d036640c86684050b680e0200d8884166030000d00803c00e02a503a51044412080380d4090f0f0303c9020f00042081c0d08821202c5a000e1103001550401c0f0381c08183c655a00304c2d88561070a288c0003032900307a4803900e240c00ca52103500108010f8200c0241006115403003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 546495377 1250 546494127 546494149
    0x20301060216031e06060504020c060f070801120609060b130e01060504090b010b07140129060306100305180f010504060b060c0601140402090603070c14030a1b081b0c 73
    0x30b211040469819074a61a240030481034085081061a004040401c0110703080a4014003001c0c0c420340d102c2203602c0145444690071203c0450089181d00012052807088040703d0403182051200e840000040d00d070a4042d008000003030b180141c8480598145880d643e6110241c5c202203140011041c403040700030360a4908640c0b00c00d03c118181401080400e6030520702504480e040300b54160798200c0345c80d00005005441c0407a040c0c1c0c1d442c007200f854030070113a50514038071a86c00e070501c0701c222452082003041a00054403480c2d0001da40c1840700050030300980c130017600558450100c2003000704c0c10084500d00613000d555a112a5119000d001c00c016850042e02811842237075503900b00300381909410b55844051044d82001c181c0090394030502e4407907604440401201900250707680c038203000003411246c01c0030021113209240c0c3e45c104c50b1b00c0d800401510b0841c607490340c440c074070b10b62841c5010000c0c0524140645083d942003000744000d41c00d0313034a4050580740e40c0c3c010700500500802040851124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 546496627 1250 546495377 546495403
    0x90b090606031209090a1802030a08030901180b130516081507030203040f15060302092701110702011103040e100806060103110a08190c030f0f02040e0106110a150203010602 76
    0x1044c040c2c50426500d040c030ba20340c0701c85903400c0010f00016560b021100220007010180d014040d00c140d05d820300100d40029481490303540c00038481c1e1001c82104050750308460b9005840790555401043d0302440885200401901400403690a11000040550784905e960b01080c144e41c00381084a0041c680c1854083c0d002000c0e040031819440c040c0c8566031242183c0c2002407090341c040c4444c0c0c140e0700c1158030101c05940c0251454644d403410a0300410070703408109000d000034615640d1010146c205000703010340ca005030150f040c1495615030042d04d100206480007503046c082800089900000380401c2e84c0b1a002c2e600c9109046490320405904000001e02120304050411000c0e50071070700340804660108030b95281010b995074404600b501a4582d10a03240500c03428168071124060341034015000391513205208010700046110f1a004910983c441c0200086100c0010400da6000741c212a0f601c100b50020b407040c004240e80e54103060442d0b0818011419030101c0180044c0e9810403c045110348 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 546497877 1250 546496627 546496663
    0x161e0302011a210102040b070f061415060702040905161502030415080a2903150f0a020901020325030816092c0f040311032b090b09060603 61
    0x2101c80420980c400c0101d5083ca03080d03802d207042c074004000358111002090b0061030345e51184580c1c580780d440406c0d00c1d08165804e5080211a000d0851414559401101203076a25074000214a0500286803c006000e07070384141c0e03a080d801c012079428081031b181c440200d800b80d2101070900700c52500c002010003c1504550080c4010311201c92925046405800c1c9424800c0507503070380800400c094407100e0480c0c008282c41c00480400e014542a105000003422002ea621448240d1248104c2ca01c0c2218040b42048001000c58003120550707000344480070041c4192840c2c40105488103116150540d02111184034000e940720500d036020705c5194001407800d00d908680304001c500142400702901881280d04000e485111034400242c0da00e040b61400150400f11a15109114140509044a058022905c100c417079400c4c03641c1c003104841211a1003c5c001c005c0740c6403510022142d1100110f5009041d82e9103d1410105819040349031140c1102402803140d46001000d140c1849102c6c013407003107024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 546499127 1250 546497877 546497921
    0xf0f030a18170306150703030c030e0a170d2003090706030908120c0c01090302100c090303020709020a0504320a150503131a010f0e060a0902161e030201 67
    0xb0b5261080c0300011055641e80b9849844000002d1030340503214038030400050000031600c0c100740d00354000c02d0500c10642c60800000208100440c1c860081c88402000e1001c0982c0b4418818003801c05841c00e034414000c00581404084141c071001c0050700429054a10b0120401030344110400089020700070701c0c60184054443d5a0ba00c0806d0b028001d003013011260b104002038088880a0b003a5104800388030001d000c0c0003d00d0401a4851f215600c001403400c0c2010750b0030b40e2040c0908056030803640d0690083c0250342c50001781e800203402c21103600b410440200400150041e00404107c1004085e036a071814502050140400c04c040c2030301e48600403005820200640804800300d0500c1c90020b08002c1c3c1e507966681c0000100e020031000040010200c6501e4803000d0658404d03090589000c840c00c541c60a0f00d8003d6804040c2c2c04030340885d0310450a19043c4040c8040340c021b0035603040b003842e85804a914075910160040d60304086002d04d440c0030040801410750901a958141d0000740c0b910350f0346 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 546500377 1250 546499127 546499133
    0x20c0105131b030b15010e030d0c0309080304260f0307060212061f0302070203030c06040c0302030d0302070804090b0d0614060f0a08060c250506180c0d170f0f030a18 73
    0x2030400280032000017204500480c15590180032400c0b84004010103607503e2a04411007e403c01c000b40b141030340000c003000700c04540c6104c004111425075014803038900e2140010307408005050390711500b100c0b580c0507180921024440c03c02c05082d060344290000350f10360701d6080360706888884c01060300c0c0c031501c101072001e03100186c2c0107400c29441440d0b00c5c016a035210503002191a600c9102c21004040c4141400c0100b440440f070304140a0700c2c0300710300b5581d03043c030700c1c903c1102a03004040001c1c004107005c00c020001c10813540c0c0912031031074000d842e2040c4565151510400c8420348030305140400341d01d80030010940380c218011a40c0210440c6d03200510384c14044607130f07581c0c1d0004108030095030b4005034800e041404040070001c81941c6901c424000700c2145840e40c0c80c1c890540745040605803614a1100b00040443c88081450000e44080e50713502c02ca8541401544c64580c00b42c080036001c01c072030969080d0400003000205808010385590313041c203940d200d0485070110040b8581450300a401000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 546501627 1250 546500377 546500393
    0x20304020a0530012a1e0e090a1508012306150309100f0524012615010513180609060e04060501081603020112020c0105131b03 56
    0xa5400603218080c490400004040c56403114808443d0750400400d000314082c4415040b503036070203124071212000341c640c048901440c0c0041080200215081c4a4a42d0160440015a4494240a02d490b411041c0001e011844c250b0040d1045202c0f1521852880141180d0105034001060218000c00c03c0c09040c43c400c24000300c0d41d521b441400501480030515641c0c4c0d1041c0c40300390f00c0c1c002d0b8605a43c0e00b4041c441581e12101002d40306030860400d20340034106d034400d10805128401c0b0494002d28003000d0744009210030000c103a0641800785204020070740c0c1c0c043c1100c220f20480101c150151a0400002030802d2081c01c90801e0704002c07040101d03143d040d01c0d40884d07000711528641d901100d0102003000101030001908408000751401c2c00002d0586880480240568026034042080d03907200c072141a01d6040e850642c0340580120310303040005510403842e0030b8459111070001401c04115407851400c0d07070020390b451440405400c050005224829041f5006084803015084001c1d1031a580c203d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 546502877 1250 546501627 546501629
    0xd020d0806040207060204120b01051509010f020a08032a03090c0d0501090b13030314060a050607060209040e0601180e100e0f01090c0f05150f03090f0a0b07080604020304020a 77
    0xc000942000c20807689554060703408040d88840d041d1b4480d501e419004caa100303a24a0b044d5840f004510000070750741003800c0c0d1408001d04600e100d92070032010f84019260811400c02d0030085209080d07090001c01c0f0b03440d000d940035625102c110301140429448418000400d240c184410003410400d000c1d03178880000311841c00085c01e4403480500b2109040c081e0040c090440090005040030081000801c2d00340444003041d807090701d08100b451440b69000f2000141110b000707403c40c0580700705118610745070014095407445044094544540c0b580420203131800b1020006844d0302c140c00502405c4041000766120800c10b860801010782c0c628050340e0307180320356160001c039103a030b0b12410042002c091121326034489503d0300038000e503199413502c0d8100e140f284c0b050b0080d00040100100b4946000036030703c220725151140702824400076041644281e4005040c200c0541709288a040d0075a0f401d2101808540c010401e01207149005074000d400401c00420441c8070b140304008200040c1d444149401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 546504127 1250 546502877 546502903
    0x40203060f040c2304050109080a0203071a0c01020d0b030f060f010608060d061503121103040504020f090307060302070312090222022506062106050618130309080d02 73
    0xc20f50051854050f03512102e80540c2d02c003215400c00c440740104140100501c1120001e907180d0b80300039610040951140700d0010003d40c036800042c0d08101d07684007170411640b2200b204c2c61940c505007a141c6420f08980c010040290390705d4076007114128602d01413060306000c00394440034046500c0d024031245a00801405010103201401c0c02064460311912041c1001552001080203400c0820501420900086c8009c685440d40c00d001c2c40402072107094200c0003160044011410282402c0800010b500900742540d084401807007400116a420012040100807a407001a039400b26410010201811103400340300103414810381800507215054503100100c0c00e100c0e81c03a4003140a0081034007a12860036441c00310081c81415030741d0300c4034070032090340c003184a0f900401007142d42d071500c0c1018034a041c8250074140380c0e1007031075000b094203900100d900000040a080840342c9050081105510a82e0107905000e907500c0c400c02015000610003004c0c0a0140092000e002c181000a65410358040f0007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 546505377 1250 546504127 546504131
    0x120b0a0305060c0a0527130e0d111005011203140a0f0f0201061a0c06090c0306040807080405090c0403060c080108280b04050a031d011407031704060e0c040203060f04 73
    0x36600610417002d503602980d00300c0a2800f120f80e03a103804802c0201c80c00189220700070741c4042c00e10b114000d2254149020440c0c000c0d00056610039000c6e2506d6441e81c40303c000d18024145089100c0c68ac5202e000c0c0600403c4480407581982c0d41002000c0c418444210203d0321000c12503540c100b900060340c42d6501c415844c1ca1017003c6001c0108034050a02540000d40b50300c00240c07070307894440041c8080c00245541500702d8009980312090342e0f554110203203030640c140e001170340400c0c0400c0b0384400500819000b1003009141a50310400300340d04030400c0319801c40080c0049414000c0000c3c60190055070305079403038005060b5060202258594050554500f010840810307100b01448900000c0440d403a08070b0881a501e19240c2000e60301c0c3d00d8240e10403800034a2150300313100c82da500d00000d4018001c06039504141c1050b400703100320166100744410350a000c0211084129860303222461441184190740100702d00807005040e03881e120110080c41d2049005208002581c0c45040c0c50113140d000131180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 546506627 1250 546505377 546505387
    0x209060402070507030605012c06010809070b0d050103170306030709020d090c090b010f0f05030402012a030f03060902040e0c0a14070c05011e12050a0605030d120b0a0305060c 77
    0x5002071160b85001481d40c003a0040000c10b11a40303510690490f480080c01d1000000f8007803020304110496100c0d024820703842d801041c40e551090810541c0150840100c1d00f82649400d05042660411991050380035110401401001550321420486600640e121821410000000307600c848050040300751543e40810040881c07a207a03009002e40941200d2041116a2a890395102403c3c04030f10603408901c1080081c0c855030b1080c024442c10808582c2d5450030341d1140e90044850348610144060b42e04030990b040009400c844044542c51480b9860341d0841550200d005026a4a123074000c00707846205000c10403103420090b05036070f0b11071452642595584251202034039250981865aa10001c01003150010440200210000c3da1002d803a2109154882d000c00c05400780c0500f131380e100003036507041030200d46012600100d40242c00d5907000300d02540c444001c0781c90400918a41350000d0311940c880d0001d050180300d02503804400380c491424450854071030980c2c032540507090f41200400001e03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 546507877 1250 546506627 546506629
    0x120c030f1101020d06060314090304080706080a0f0612121d060f160813080106050d031206080d02011a09010605070212031e040e0a0e071715011d10030f020906 70
    0x10440c0c0c01307a0700e0600e0400c001501c680c0e005004040030f02030000b024802c01d01145c0c85c1c040010039a011940c1401c000c09400e03080c41d0046030110744c00341800300e00e0303510f0b10b003d0440c4800b01c0c01a030380500344a401c900032140b0340f400c04041c10305a00d410305081c411002030000717480640503804404980d00365141955200700646c0801c4900c03c207009001208402501601004000360080c070030901c6005c43c1494031625281d020b42200e4851003a5035005055560701800640034049682c90042e051500043e02541c0300f1a00381048424514040103075500d81400e0744003400c2e00c2c6840e0901c01d0540c0d050190f9030404001a00c01e110328500684500000c0c21100031494040003152640c2c2c8031160480301c49040040005803d030418001c82e0003800791280050220096846512501c1c03025000030101546000050f0003841380500342c0f192680202514103020102400485000700090200300310484601303034060007604009013291007212103403e010804a03482000307010b54240c0445d4803120a80f2800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 546509127 1250 546507877 546507881
    0xe090711120412051005270c130c0f0e0904080f040b0f0a090e040b0f0a02090915010905010c05060106080c07140d120b0d0602032809120c030f1101 65
    0x64180700302220006030105140c04140e10740600d9602c41c02c00c48007018044615181034a04c200d41580e401381172000980d40d030282102039640f01e40c210170166490305640d00c01203080d090f401100c3d110096126003403180706645c00042e003800007485141441c40c40d45400d00144c540c0d800907202811881c0c0100b469120104003070200c40c0101010391104d0b40d40e00c032041d40e4100c90f420282c3c038800420901e100000c2e02c00d4100c5c01451245074001d2103a510740d940c00b00c070000d41044c0601401c070200d13400c0c040c5a12613210300301302d42c1c000c0010b24113640140940e03100040c901421500b0103410488508140c2002600c0040c0080c1074401c103041550300b55981c0000315009010304800076104100c0403003040e1034104042101c8400001c250344051240001461030703002d840b8055545a0020010704480010540340d42c003841d000311001c1c00c05404a0358101034020408035090100c001d00360b0b520500001c0180c550050b802000c0241090b003c10003064801604894140d10760409001140600d031030348007400c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 546510377 1250 546509127 546509143
    0x506060415170c040605030406150909030302040302100908120a02011b0809070b160201140d0e07090e0606010507140f03190206060315011e0509070c120e090711 71
    0x281c81e04000c041c0860041c007118140c07149910764140c1c54045929901143c040b0740a9589944030980f5580390b50fa02c650080140304500620384100d0310000c42c8000483c09641032490195134050303103940c1503004105d44612600b00a030107001800c0e100304071500000c51110130301c0521032845511046010b5041e809002c03120440c1c0b41c11700380340c1c42003080c0903004164103004105550488031007681380c001e40111403140c010f070003101c80203401a60300158440c1c44d02003101c060711309020742890341c41506501a03c1503d40204081e82029005001410b100d206503841141120001d00746424048000b0309107119400c03018040c8080c501c0d6401c2c2c1c001040192000d01c6856004603507462925150040044007081503a0700140a103c002c5500d07440c00003513050318842600761403042c0da4038100a1000d0312480e10806140513914000c0016245d642c05040c42c49038420703440b110110700043c41c24100e10390119605800f80b1035203181d100d00c07d07240c1c224401d80c0100a4180118001c2d440c1e4111882c107420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 546511627 1250 546510377 546510389
    0x304050d0b09031303060c0e03011a04090303060b0304140f0a080712030e1e15041709130603030e040b19030b0a09081b0606090c0906090a030b0702010c080907031505060604 76
    0x4c040008100040b80c0e00c13500450150307580e03002291000e0740406081c0d9120000d40140141c94604840c2546099842100e6062003400c0c0000c502c1d50b69030302d034809500120303030039524100701d05408102e102051220640c0c40d8484000350008004a503501c2c00f02c2e000b0540e02030180020403450850f214000e0380708022070740c60b0303904032010344000d003048042030103039441d202000e800b50301c042e015003070004100355014275070042506580b090340c0c8a00d00c8030b54100c0d12030954000c03035401c0120b403110400e1081c0b002441c040d9444881c0b0700385040900054031030702a0605e008a004401c8107141d03d400c2e411010a4903440350050b040c5856407011540a0070844401070401c1d00c0005e0602200140c22100900c0d8042c80c0b81980c1142c0d50314410000c180344120b0780c20f0356a00d020001e8540b14a4610000c000d003040090042218544940381c2802e800720131555400903030356409444203025041104070341d000803c0070003001180d055960786103807010440c1e00c440c001070300e980c045840c03581d400041c0e5000d402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 546512877 1250 546511627 546511657
    0x60c07030e030102031f0501021212042d0b0f1302010e0112020c0304050901050105120a0e2b080105030309010e0d1103060f0403080f011d130c080c01030b030304050d0b0903 76
    0x10610046d907a5981c0d441024028419042c0d80000e5950000c01d1540b101220510310318140b145040000c01c107120010000c5600c0c1a060580c5c42e5000d00c02202a000d00180062070b001a58103031400c650300d801e01601129040403000100306440c44212082c281042d4280f80182c0d03244104801a100700d00140e000452141c008540300c01d807800c00102610071a4401c82d480c000e16680c42e401074420380702e01540c42021903141030010b405071055402811240d0580070864034000e030781030344143d00701c21005040d4820741c22542c80388480c140c0c0584c0813400340c24100c01862401106100280144004208030790255205691540070b11500c458524030100c0054150707002031420a5502d802d0781c1d41100c0883c007241c100c502103000c0071503061303101b8103030f81e03a58620041e100d08510024412071002840a14010180c010f54000100b01203d40d800601e240347c01403d00c014124005001d0398000d01c1403500903481448100503030342e0f454600794041900311340d030f0f20030302c0d207901c100303030b4158803410051034040d43c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 546514127 1250 546512877 546512881
    0xc0207080105090a11100e061303080304030509030105070f050a111006030b1f050a0302060c190b0118020c0d050c070f0303050307120207030206041b1d040b0f0702060c07030e03010203 81
    0x520081001001d451041d05103102180702001040212091b044014002404440040c0d03441d080860050a14180c04408100115540e607a040110391040381c1c200d00150001c290403030340381024090160440070f40d0070715949100311240d00a10a02549413400c0411558403400003002c00309000640d0a290440710610100d80ca908140025620a0b03400d00054141a40c60182110405d640001500c07402003417040c025245400f00041500700e104909401d015802c03000030704d43c5d084a510324005105540e0010390f917160043d545800d81d0712114403101e05004000700040800c0110749014a101181001c949880700c04c5050b915028150700200d903850b8031200084140f542040c06036204070719559501d01c5198180d072103901039010700c00b00100941e1240e8017203800121448140880d6074102030300789261594940304940d9000c1428a2002d00c500400c1c1400700f030054404645500010b038603030f1003525041c00140255525001403843d0710790b10003c00e04100f054424802d0044004008000759124 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 546515377 1250 546514127 546514141
    0xe060a02040e0c031605092106010f150e1203040308120a11070305092b030804050105070f0c0b06010c0b01060e011706060d0203041403040b120702120301090c0207080105 75
    0x7948580210420300c50300100188900c1d240c001204e105010305100c02c1c2c0140098802590141c00841003168444204040e9020042c1c003103001d16032a017a0000104520351500b2141d24074480927070007003094110704070b045800b0103400c54580b1040b030380203441d40034000c00104046821401035400081c908480043c0191101d4088000c0c140104a11401002032072911042c900c4203204018009002c600140305d580e00600d0110201840d542080c0620074130415056048900300012403821004142c615050005000092188640c80400d03410143e02401d42c0c2003015102d8056020300030304050380781e00003c1d00ca9104140c03010206a1040343c401103561a030030058850440c0500c4580050a02450200e0400d00408268041c0074080c7c01c01d03140c0301c51101960080c0d8001007003034541d8070400200c03900705681000100000c0205108650315500c042150606021018140301c00719802038042c4180700b08603400301c0381101c004050000e0110715081c004d80c142062075200d24629440c2c8000c20445e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 546516627 1250 546515377 546515381
    0x30f020915090d06180b010807030f1104060305030d0c09051806090411090f090d0201140606090a030c0b030103020a1509050d0609061b110601120f150203100e0105010804240e060a 79
    0x4400d00c2188400003580c4c03a003001e60f503109c00a00c0080c1040c20014090804942469030b41040d1140141c0042180c41d03c2c3d4032070310715550014600806c003a545035042da000a03800300504010340300031541e9542c1d21888015017100f40c9009026a807043c207041001c6030400c00070780e980c1800c44102400000c000e1604101440d0407030b00807035088150340034020092101d03c2c030600c0345a00450080c00744c006140c4400042c00300a0304080d100f107410040f0900080302041c45241e00c0d50081203e2100d0a95942c110b106000700801c0c5c503401100341001c6200622101034200c003000d000d440c41555400e4800115081000c054000003201600540c41c014040d4039000e4034800040170000d03d0340382c02510031802d03c10281d80c0c81d000d104d483d008418105100001503241d02401080d00d02940130090030840150001d0700b01c0e402502c0e80e00d071aa044017404c018155030203540900516090070081a1460319448240350000c00106015842c1c240b1518181500d035240d01400c6000c9500b03040701c0c5035250030460400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 546517877 1250 546516627 546516671
    0x3150903091e03120203120f01050316030b060906040209041d010c020a05070e0907030c0909050d0905030a0f150e0a0b060f060f0c010b04020c0d030f020915090d06 72
    0x41d001c0340c0116480b0401074000b0721001050314488035052031070301d4861110703003030b41041c2085000c100801079809168910003402144d00b07000d00e4034194900420103203041010b064000805629000400115845c5ca0003150720100c25214401c080d81c40d140024001d00c10000700c1707a4060b180105c050301c54114000c5009a0405500080140c40d07000c0da0141d03540c9064100c02091603100c1c0c1e01c07d1065501461599800221900c12102d440d5103a9544000c3d210254000070141035840294100740001040400080e24032400d01c1070342281450701103520307a11100e42c06001d4454030a44030007000000078800709014a001802c220a00742c006020780c685103203d400703031240003542e40404e00c24902516800189600181002d181621a0030b042c130031074000c2444803520355030725100310038241c0342c9000906140800300e02070f210364030204401904441e040010207000034414407864480b51a010880300341c00021103080c40d00c529050000440400b1201002000181004104900c003444428068 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 546519127 1250 546517877 546517883
    0x180603150f0b01091511011b11070b0f0a05070c0329011a0406180e010e09010c0f09092403081306050703080a0203060102150c0307110c06090910031509 67
    0x482100b8901c001100c1640950055403200800c0c81c01a54405024440071012800c115001013442e50510200c1d450340705121079038a010800c0701e03508504d04c4400f400301101411901d22240d0801042c0f62021250303008001d00c10041c4803000505030b041c440d17941410402560700c084411410b145074868000c0440700807074105d00c00c0e000700c400450b0503141c001011b0fa50601060a2a042a02d401c20807034205a40810320040320034912004121a440c1e00940c0c5d01801682a60004505050075800e00f141c40c00c6000348200706018014400c440e034040001c20454851280204070850982116500d5040034070309402c041a070010004100409000075003804040c0c0c0c0344070340f00c81c1d0b03890b482070702d440c8150040100019009000100c10b07210541c095a00b0441c10300c111942004d040c40707811a110380541c0c01c528402d5000c0b04000300c950b444103851070070340030040103069001781c03c40116625028140600380300d0013080c00006d045840048408e0011a00020004440400c8a0740b00009040d401016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 546520377 1250 546519127 546519131
    0x3040f0603061431090b060405040f02061b0105091605030318041116051e0d120507020f03030a021c05010b16140f010e0c0f0a180603150f 61
    0x152080c0603209840031501000c80d003075002e01ca001e04101d4202c2c090103031190401c1403400f0303c06000d00241002c0c0004d4041e040005000303003190400000a48008104a00c2941400700300310004040c11a425022641514115100c8010041c84909400d00c4400b400c19076181034200031480100003001d041507520204501d210a44650902d5228415229507140690042d61400c1881c1400d40c030860850030340d1a182c03402c0040d0a05c02450a4416030b4094409a2020500c540841c00f510900e5007a6008000100700c180c0d081d0b10081d00c3d03204030300d00c1c2c1b801a50343c90000402c894028000380810402c0201075030742e603180000e010302c02900300d220703c002c25040d100404801131810f8402d0a041c0ca48040e401820701c60902041021a02c4203a07084407018480280402c80a00400144440b441040300100f980504030051170300d071000080105101d03400c0001e81031460344403d800c90f800e40f014482a801000781014860f00031f0003041c1d0006021100707503200030202d8070072903000000c490a00c84d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 546521627 1250 546520377 546520379
    0xb04020f0301060605040b0c1603062003090a08070809041103180d080a0b132d110a11010e0601030c030b090f07060c030909090503031e091c050705070803040f 70
    0x51600f01c3d81d0a01820000c10801c0209000350959180505941c0780202d04940c11840120798244000b011503200315602912400341a2030041c0c1c0c1c1d110300b103040071001039890551030245655a501c82c51540040d0801400150000910004004490035454040c0085c820300a170421182d860b580100c130080105036041800c401d49410128150200f00f083c1d50350640151960000315000307050018456030300c045107045000c80640c050044410944240c40b450341701601117464203012400ca5680445194036160340010603074800402d0703a40c0007c09161034104c62103403417280d60041c5141412080355200e094000000c0100961701d20003600c0c45640c203494141ca501320595910410140480160340107200c003801264402c1c000d008106000c0d240407204180d072801078004031843e82c4416120b40c3c00000400c8420a000501039459a0244540e603d051401803083c0d6160709108a100411100c1e600107551002d100e0015108500d40200c10303914a540c4c4c0361a00340d9240d2041c032420748040740680d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 546522877 1250 546521627 546521629
    0x27060d0641090a0209070507060c0320040503071403031c09060e01050f0a051b0301030c030b0603031804090f0b1006020d0516080a0912050705090c19080a0f090b04020f 74
    0x50780c1401030450b9801040d0005041e4204503044030001c04400c200a410300100c000702c1c4070717402a0071400c005c6840014020b140c10220784481010000040c078a5507003004104210b072000101d4004445070052a14032140e580c0740001d0540c887c001100c01f400c0e180124081544446510040712213109950401050b04102d4a0600741c031800c5a841825080110001c1d0103007038140c1010fa885060313605002100c007102c2c040403003250070030b1f08207403042a8054024001c10000408094000c0803c80040d410301c80c0c58500b40c8008064000801e01031900c4807171000802c4155030143c02c6850344040071981525041441e81520341e42807081d9001481031410039400140031384129401d4044503d006001c60109032107541095201450300b00401c009102c002a144c0c3c00300600c082c1491042002e09852440c5c101045034001e00a0071142814900b08000a268002d2505000e002849414800e0306540d031004508001c0144420240d403c03820001c0010800c100d0b076030b10354440d5108491115510071404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 546524127 1250 546522877 546523001
    0x50a0b0a05130b04061a0c061b0703050717030717010515070f020f060a0810060207060512070c1b0e010b07121103040b120627060d06 59
    0x4440c0c19044508010640c0000c811500051081d800150002c0f40c3c20391b0765944009503c448500195190b80045018620400140541500103c3c101c035520101024100108582e100d01c07a4000c0500a000820f00104000f04443da030a150080d22680c0e03d074640404c01405d902c49001f1400148000c180c0045428945480c44011038004071802c9414042140c1d640507110031a40c6d030a90344040c1c032161b1030035a0741d20b810040c091b25046980d41840d5041808030820042426040703481035401c114021b00c20103511105660f811a030780445c400b010345a2090a0719000c08080d406002d5520941c044484540c141d88001c0071503101c4e03030001056a90300e8442ca42c8a01070414020022444401d25018480c86200700c1c1ca031a0041800303591900b03546858070303000c5900c044100400c1040020070000586458100303000c01d9010401d90341d1a00022001d1411b80010041195204000070b004902c184212640403620321207082d07a0b80c000007001b412008035803103215005000c013a012005a2056401e502e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 546525377 1250 546524127 546524129
    0x20c16030b0105040f09020303070614010807060507061a031c0908060f1602100e0105040b0610080403140702040e010905060c0f0f030c30060312041202030718050a0b0a 74
    0x8004a81e00a034200710400c0007034610300110141c611303161055000560344c184001c020311482140009513a00d4182c0f88182c103010142c0c4000100e400072903003003002a412804490390300d0388c000740000f5007040c5440707003201d01b00e20f0300380040d054440e10340c07a2940400303440e680300108000c544036000000d0f90740d0300056440408607544604100b4000c042043d5260b19400701381850b003607005940c00d100c900c114800440f034120300c034001c45a44500a000c103200c6025181d603000602660742c1c904201041700c000e8900340340540001e04111b041291140d03a0b002c5001500c044640c014810300c0007904d80310143c0e02034542810241d80350702484010842d03a40e6100101c480d44a50f40d140c2c0b50402c0d4218280d0051500028502c035032001d001c00100e07400c7c402e00300c84144480603000c0750340300c08480c0103d0b800c0f4655004299500940c031902610b0102040c2d4016a812a0b00503003c00300b41316441d2000c24141809a4841c40700340d419424090004085601b10754450044c3d021f0400a40104408102496070700b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 546526627 1250 546525377 546525383
    0x24005010507060b060708120f06040c0507031107080d0c05010e0c130509073b06010207121103030703091505090d021003110414011d0a0b0a030f0c03020c1603 70
    0xc01040e40020f0b080c1c1c01c00142c40c030009041d14100080e60711603601d1076000704002c0c0383c03151840f410010204107020f801d68000d84c00b95010490001103010140c5144102140601404410062a001c9a10400c15000070b04100300c00d50700030100c0c000000e846d03000707034109c120307115424020b42c0100c10707000094044000074002c1c0342e1034142d00092131920080c4ac014142800d54001d280f4041049042e01c02034660001c40d10030030700040808890012050810804a03080d50443c0e442805207580e800204d800694505511a500415070b41c600356086030241000d0942501010441c0c0c001d05810600300d00031203002900600744070340d904408840602c25800b0060384501c0032a41400036080c484c0281080c00503d0900181d405010101185c0941256100e0316492014903104495035901501d100c1c00c4405807540c40c0300c010301e0a8000784105035030b805003000780000030500c6a0220b1290300140306014018500304180c01e030b5900c0041c043d5101c0c12130000d039441f030044032030041c0465000307100460750 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 546527877 1250 546526627 546526637
    0xa0b0a03150b0301050117150105220e1c080f0f190b030f010b03010605060301030203070509041a01080604120c03120c0302040506040b07020f06250602400501 70
    0x10541d07481401982600e18940c015a42d164814103480d2424407540340078001c00046064800700c0401107616180003614902d1405d03500314010000e035116a440449170f00751040741628000190003010b002800b100303100008600c0340b600d00041d41d09160805031240d01aa030f075a8105650f8681d84200c00781420351382003445415000c001818414844200701c100242c25501091b541e000754000303440e00303a2a01c03a07610306035580d691080301c924007403080b02c0081c0801e451a9081d50314540020b52180078902c40d0a008030850340000d81000000011219a444c2d175858030340e4156101c690403941e8400841e030403500c01c0310340f0151400160080100341c6289600d651450142d908601441c800b800282416409142d001d01000c80c059803004081c1c00074140e040c90141d1102c40031300401050303c1503040c041d8082c400c108010119008055131540e92740b0784070b40c068001e40c20740b4580080284a02c0440700708082c2c030f40d060ba04003949040c0b62000d00030942054603031000f82c50705540340314100324411603000c03030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 546529127 1250 546527877 546527879
    0x130504060e191d1c0306050319060b03120309011a0d08030406090c05040c0809060a02120103030509010504050d080a020d2c0a1a0c070b12010618030501020d090302060a0b0a 76
    0x1c51900000482081c8803910a03c0c225160b10b81c03840c000d07601003c42c9024440d032078030101d0164148110f00003004101d005042e008194004c1e80429154607002501c1e9603103074664440d16440c1000f02034000820180029600d18003561038038028003681c01c0451404085001020491a1003040454503640241034503182d070b21180ea9130310003080c069004841d107104501c00000c890f40c9600c203110072440c141c3c403168801d10300390161504200009190030386591060200c0c9c1940380070315818605581d81801c201d83d66640000041c2d4250003954415540100c50b60300c00d50401c14600064110424190220740849209810135254031030010a03c41180c2d07402c003028040d00702a5a00500a40f1000d01510f4080f038407402e080c818164229409120184c0c00181841c442d0310400080000302601e00f4031034100460b65010000002e01841a1420452160b1440301880f0b00507140500079644440215a0307010080600b4003d0301c00e22405a0241c040d001c0000c120511b80e000da8181510001c050f91002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 546530377 1250 546529127 546529171
    0x81509090a0b1302150903070321030e1203071d13021c0e0318010e0402120106020d0503040804090203060102100912090503010608100207081b0c12011404080f070206130504060e 78
    0x81d00b011190710750500c990723007000022515501210340300f41045c005400c000c1d003103414058203440041e02e4011590f84240c248000c0d03000e030002613039040700c80e07490052010708000c1c03880031b0705030350307039181182d01880d10181914001c40c558000e001c4042280748614a2400c00030349174048540d48030701c1820a400803c59400000d40400c1c1551490205040245101c0c480802040481c1c00c0409100c4038031003801c00510480b0780400024000d140315161092a614103652840000c0c00b80e13104c0c50b00da26030040013144560f0300900c03e401c1c1d0381c0900c810800844016040202e16003080c01c103d180800e50400d000703e868107040c002d9005541e0100000d000840e1880d101000035885880256038005041c800e01400294003030000041c07200c50002440500395020802c1001020001654000d80c98150b24003c0d40740c207100010b5010350420030f055101c515140c000500703880b031080001d512440014510401941c8880a5001d07104103807403c00c091525004100c0010740151444107840d003c07020081c0e01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 546531627 1250 546530377 546530419
    0x2010305070318080301062a06050403110d0e1309050c0d030e09010905010816050315100f080f0706080c04033c050f1606081509090a0b1302 62
    0xc422030746800120f1507140240390260400c141c4080741d04500010040003e6644510b40b001c201d0920800700d4883c000852114001d01c201c00c1005200b0790b1120009014140141150744446d501601038424400d040c2c0001002d019480000b030f80b090300b2114090045000520940f041940c0c000c2c010b20b148400242000003291286004070308201002030050096100d043d5401e000b07100e00500490654100a006401c100c880d030744409040c40c1c1d6040401543d9400201070120004070300d0701c92602d446503100300e044c0702130a8200070b060b104084d2001507440000210b04c40d004014400340d500b0580c684d00200da11500544104007807400034081070000c5204400c2d0300151303c1501e040c00480c1c3e090030100351130313510381080d10300f90780b01d41d400c184000c1c407405001d40c0700303a8a0071034060081c14a5900803080009494003481c4100020304000503181e01b500c440320300744510002c0900c00140345c80014541d481040f14000c454442020b4003142d050b6100300aa4074202d035005000e0a001c5202ca401550 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 546532877 1250 546531627 546531631
    0x907030b012d030b120d080709060813121202041d010f0f06050a120f09060b040915090201020a0212030306010224070c2a2102060703080433180f02010305 68
    0x20340200040d92404903003e0400102c1c200d1120303038541500030700d0b008d4005449840254072280070b001c0030b01c0400400c00819000d480c1d4881e070003070b28240301c141c40c00400c0b00e0702a0345801a01c03e2910000b401b060750054240b2503116640c0c8a00740c050640e0b294121071002c00c0582c41403403102403c00100b80302d5030b40508085d10f031000c500d160800520070403a00190555020401c0070344a036660325032880c203200036030040031400d0005070390602c078041041e030314000004e0980412081d080d0303070f6820307840443e8801c0c0301602031180c008200c54900c49040d295079441c0e60080e03400502510a8419051504080701c0304080f09840c1c158030b560716541d602405540312140c51004407010749580e07039140b42e00010b03840c0350040d803800f071000114107901700b0110811103040c04001c62a0f50350320080800050380d428049690315a07052074500d1450712241340035481184856070300d201c003e0958034100000e80c4d1349046a110b2080d0308506003c0400114501602032040580c0944030b60003a1040c02c026501980041e9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 546534127 1250 546532877 546532879
    0x120906040e04170711010f0509131e05160e09040302060601050a05120708040c090e030304300e040c1d1509030313030c0e06010912020d020907030b012d030b 69
    0xc101854182c0c2c03103044690103550110794680120995034900d5900c551403140c103014508088e8030b00480240000e510100c140201030300943c8031000b003011046e000740c0c0000d900b0590501484103060100920f0300d45002e03040c05d00001079841d00e4040c03da15115482900550301a0040c0c0101d844040046401707910003030101007403140800020a2100240410701d11910360b560303c0e03000307908280c600f80058240940c040c161050400d03943e010121800310032241c000d5070100104000c040304200300e4800d1840c0c080c40d81707407500401c198881d817240c00c00400142040d04480400c484100c41c803060b04c0c2c1a21100c452400f200035901c0501e00303800d180042c402904040005241005101d40000c1d107941d0013070704080c1480c008904200104241c1588202c090000c0181c0b1094618156000805020461140104005400c45c1c03460564a0703840c040c0e0421a005442c424030380c9403695011f00580307190503007075001590908500c2d0100c2c1c3c01c4e00f8180d101d90942c904040601171910340450180c49000390321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 546535377 1250 546534127 546534143
    0x5061605120712120e0d1107170706080105040606122f1201091109060a050f07060219080103030509010509031609090b0a0b06090907030917030108120906040e04 71
    0x2101054044015201e01c42c0310340d0400d241040e07020401011a080280fa25010b2405c040a074810380401040c010101c02c00c0349040040305500d18502440c10055502c0300c41440c04a02e04a012008081000c0064403415101c284003079994800340400c490182c030410300003401680a1131000f01264101400e552241000d08a100a41e2140c4064042c0150044d159010000441004c01ea014080d40740c010000214200410b05a104240c5014852410164420b600000321507440c240528147d0705c41c0035020a22548034181441d100e0001e600c416012584000c25000030300e050340c030070030b89641038036031680d10107040c003201e40010346503508004205607041c01071840102190801302c2d040d0005000d00c3d607010601503502c0c28030718a58040a03000281e40c50402c0c400c0a2580c4511040b2000c100c0d0540c3e1050340c03944c03600c1040b002044401d1004000c5202e00300e03c416800e00f10380196040c0e0b103010f001c0e20303040244070719802c015105403480f460700040c0c180030400c0f8400542c00d0031076000e405040705d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 546536627 1250 546535377 546535393
    0x219020d050409020918091c030203090a121106010f03020a0b0715050c280905030a03080f0c0f03181c0c15182a23030f1506040506090105061605 64
    0x1a01c00800c86d68404c450f40301092300341002141d0b40c1c0d00761418003603040852039814044045034031814000805803044400c0888515014030441480845d40441750a81d051035854111841c40c4500c0342c40143d00c143d580d0740011828041500c1191007196110805400d181542c00c4118040c1c10020089a007013481840034118524030410180351192030b84e03002c055841d070550000b40c10700c0010340040f8082d17405003002c5000070347c0000b0415006242d002d45428590303150b01f240b81c0d00f031094104143c0a00000307c184269452032801c140d1060038458103039004002614a600ea8160303504881200091601c508080810250484041d0014034a40d01240840795914100c2d007840308280111000442e80e05010300c580404200050014440d030031154180d45040c07101e02c01c0c5400d0101000c41c00c002c84110030207130341e001c009100b6850030132400d58440c4144201c170b40014013811039003a03000c1e5082c00c0004000380387c084030303290607030b44014800c80c1040308010f10610000d0024504031014851815 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 546537877 1250 546536627 546536659
    0x5060a05030a060207062d092613091e0e10110d06050a1a0a031e0204080106050906060a0f0509220f15141908010219020d0504090209 59
    0x40c2411903004400c0985e90340141e10f0110110384803000d6a098031a080503004051000c00340001d420841c1d91100424000b80c43d0810744848c0c0700e8265a60110b1000b5804d18a002c140e803405800c080c440c0388c0718113590305e6903002c0b00801e486045001590004640c0840c0700804119030180b9680c600103001c48440c0c01140303e4020845020a207003420710031011441349417008841c0a0440580019904040110b14100c6940d10644510300200c09214000c40c0c00210a8403903440090314401c09600b895202410103002c5000394824050b521072942003030008552418581030090113031901800d0503180c108004c00840d02071480400d494200801046540ca485c0e8030089112517001c928000300b585040d4520300c0c0411180318510341e4903040d0411001242000035081c10b0002c8404000025003e2004200000c02119025280b03c0b0584106480403d00d001c0541c003404009030042c2e143c90200c2440715040e80c2e656000038003132001500800c8141310f207619603001303000c43c03040190507144c0c3c005000c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 546539127 1250 546537877 546537883
    0x52205010602010227030c131506080a06091104030201051c06081c020c0d02040b0301090b040606080c120607050a03020c0f0d1409030a0b0402121510090c1205060a0503 74
    0x780c02440103039008034041640585100203200e17840b41301c01440d2542c03090100031036150300200d41801c1c13080462210080725003480390040c50405a1b141c01a1404948488000d05840c100340c0d01900e08a203801000729221400f489000e4109980805e59407c0070b1440d40111255808082c5905840c820029800d08841103070084001500302d98001d031022080c020320b1000c405034959000700441d402801c42181c5622508007004182e038041e64003140000740c00d400309024001c002c500505014000c000c010500c600360348070005940200c01603a00e840203480c01c0045220801c4591a20b0b6004000400c904c1406040200740c409218240541071035152202d03e81085480384408103070390051315000c1102a0b0106001500d18545050241007040e5100487d5440201541c000d15107203120340420f0940d0748803502c1e8410b0031055001c88a2034040c800131294442415a045040308940c40800b20b0384d0340075030143c05440a010760f5071040481a0104010141a0280199400214401000c0f800307403400c3c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546540377 1250 546539127 546539129
    0x207080c0a11031b010f030c0302160605060f01020a1208040f021512060415120809060c100e192301060f05010815060301300b0106080a140105220501 66
    0x11015035640080c0841810300306410548401654103121203c0c5490f40c1e0044c002c1b040c036000919000603025a41c0710250001c2c0301e90401c041c003803118005803804000d481e0300402d00c1494250388202508200303074010383c0d5070796a181000f0800b4410000300381290348152003490340a401642584014051500850000c3d0908902c10010003000625a840300340c00030007450700320b0000c0d513082042e80c8107110f1440d44509079019100d0804440e401400500c8405000c2e07602440380140703540e03034038600e00c0c40c1a80d40d804940c03825203001d803c04080d1b0031482c02c041390800080690311509040100181d840c56485500410f0018441c405c1440d00c24424800f4451030000c1c00c400360007074140c5400c1c03400140210100a10b9400c007000c440c80400503d4a484c0e082e60b044414081605800810401d07030f0704261403150300a80240e240100d05039050000210394203040340d0864072040c00c6a00c2e088501800d03505401000d07030b00884480010030440c1000e05050300364002c0032000300c04007209558a2001d464003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546541627 1250 546540377 546540383
    0xc030c06090605040b1f0501020303011208040b0d0b1206010515070602120708090705030f0318030f2e150621060f030b010617010608070903051f29040207080c0a 71
    0xa001d0400c0201410746011b030f00c0c40088011001a01c070324020000b0b5491105018034a2841c81f8004144200b012a400380c40c0948030050b20035485a001a851000514000c0300f407520400c0885c2d0f81820450010803034a068500160040c640501b4232045010750790301100c070840304680d08000c000703101c600078907005004c1c10581d642ca240e44c0c14035020452402e101500414030030307044610500c01610000048500c43e055001c45d1301482825880000c3c281070716240c18202c40d00914911060080c1c551101d186030504c0f5060751804c5458061003075081364002c9514003d003420030035082c801c0a016800d040d20f0f500c0041c01102c4541064078401050b00d0322648200045141c00c07409100300003100058501402d03c3d85804000c42903c4c1c2104280c0c1c0c10107118402c288050300000c81d100d14424000c503405140c0080407108144172004808048815200603850310611700003040d8021414031401c00d1301c6031341d007219001858111004010007944200340840754000204603003a9502c00074000300e204180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546542877 1250 546541627 546541643
    0x5040213080111040605030f130209090a0519031211160f05010c0c030519050f04060215090f0a0818181f060801030b07090905090f1c0c030c0609060504 67
    0x45003503003103400d403051822070700f075070400c2031000f400f015a028045c0d0b6071101c08040f404007140c469400c016442120040060b411013100c0080120004001980c005668846d104880b4014030035540103821034418130004000400009001003000031503001410350240c02d126903803401242c05126525000c1c140412144000c191000206100c2c00b0b101c0e101d031070b0f501400c0c4194055140d5800a00301c0c402d00149c8107141c1e4040c200301340310794428001d0782c0701c0015500380c20b9503607911000b02039618400580801e90855900000400d042c401162001e00d100c10040108460f411940c3d8442d0180c00410302c840145c0c51082c1c1410140c0c1d20310911035031140d01031542c0750a5042c040034a8000c060b24109454a414501d8000c010150788200c503c0d04403a001a03048203540c841100c121203e41e01640100d2841d4240000e11804a001140d880390030180303002102c0c120340c15451003030780c541144034240c400704103402c5410010a010302e47c0c042046c0c1c89810001260110b070780d101000c84006640940b6680 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546544127 1250 546542877 546542879
    0x609041104051311180613060504020f0c0610050a17120d15140f0d05010207150606171015090f08060402040b0607020f040c020a0b0c070b010e0c0304030509010905040213 75
    0x4c14000780e044c50b500c07415904020039000211224200c1c3e1000703000d4901440039400340c1450a08254400340113494010015543c401c085a21a9060780044d04010060b000311408103561000070b520301c008039940900400190345c54030004290409400000042038020149400b80004482c2c000341a04100d002000428903404019426011038030b40040040300360501050245959030201005d0f03000040b201180f4146191078164060b0107000700c001e008200054a8034602021030700042c040d25842d0f03940500c1d400020581d420f2141081d00c0308695210610014408202d100b032090b081628241002e030a21a43c1d00d04103280d00c140740e848240280c004005100071843d15004d86050000308940480c1020001d80001d0111441d01c60741d28402d9517140320300500e945c02401000b800031341206000c41079141440f807001d1540d024410440785440c0e0107002040003109003c00c0c41c01500d805c104203085641340d981c01e0f00c165029100c15810b0012075400020f481c0d90300d0000b054409082400c2409007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546545377 1250 546544127 546544133
    0x605010806092107020d15050417091e180c031504060b0306010f090f030c08010b040c21110d1e06182003180d02010606050306090411040513 62
    0x10034050069150b80d0094200e0400c1c0a1802420300810703580200303855511003842c40060440c40b0016401050060248211713207124001da44098810380c060040040c08061101002d0309505c03c044c40d40740e024071151214500c05013401404050044041d00d5510704a0880189104140701104d0110200718000704201e0380c0181e0007001981c2d80070564081c0003050030a40155a40c1c00000d203107604004500700400e0050f07101c1c08000c0020840c148000d011a82c69017802c284032912406141904c0d03003007da000306242050700c20340446281c503944d041e0b0324580c4101e000c2d6040207003a911620303207a1620100315101501a0040c0711160000d000084e0402031761615000f200c41401c20f00000510700708080040b00182d629100001c0d00b0204001203941c14000d241c014080c00d0b20304000000c0001c02040400d020301c2c0844010b00703621004844503501522001c82c00c2c6c44160064000240b0244086003903410100e5006410502c1280114000d00203000442c04456045030800031f10011020221b0034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546546627 1250 546545377 546545383
    0x50102071407050a0303120b01030f02040f0e0f090604030f020f010c0c1b030c0512030d0203010306060f140d021c050d0905011229060706050103150506092e030c0306050108 76
    0x107200950b25a04d949146840152503031086400082c138154551382c0f00d00301b684c030990020b01c1001030301c14119184c5403a0340102003503504502592941560100200d9166010350b0040c612405500e0000d1400d0f541d107a80c1212402421030503103095204040541076521004c4c081d502888020313607500c40324003483e41005260003031003503003444202c41c00a900b4000b040018041c00b058604c00c0d42c44249420070b20030300c0d5245120b02b0300400b0301e051000c0b001008000080d0481c004a801009414000c02d80740c0640a10700700c112206190b122200942550050601c000e8443c945480090175144498540c0c03127890411428460100c002007482009000668025080e4400c801c40034408001c03400c2641c0541c1c60f0301002c88842c007a44181029000e480d552a0400c5803841d56007c40c007444030b56582d1504610b9210300084a192003820240003e056007064a2040d1050041401e280c1176810401184400344801000c20880403c200304044080340c070852a0200552040c00c000901c2d626050585017 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546547877 1250 546546627 546546629
    0xf15040b0d061509090c1505040b180d1b05090717010e09160806150108130b090120090906030a05030a0f030b0405070e1f0c11030a050102071407 64
    0x120540c5014100501621110095007030749070300490001d600240440d681c1d0030303001d1560022218900305000c800c10440d42280341400c581d00821401004240c2c00c0342600d80e40100e015a80350540c00b03100309600c01d00c00c98150220a00003802000c034a600d0741c0c8642da8801606415102200d003d8081003101741017031180198070111601c0c01c0365188000722030801c1842d4061050b07010300204d100c08030b141c5580912208949003030000b40c07076001582d80c0c2061522480100c6034000d00c1400b00c40b2803051035014081d40e501c10303160005121a0703072559944030044401e01400311440ca642c4c65800042a1003915442100c6403003540360b450315195560b04000003440e00904842c003d4112008600003e41c0000030f840001189082142c56003407408000c81c028000c1541d002d50050404007407283c00c540150b0000c0100d80d00303886038a0f01e0032890a0b8044c0d44007402c800717800081c0382060b060010403c031862030f02d840300c070060071b441c01078410751552400da13080715909071144403103418820340c045401c0000d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546549127 1250 546547877 546547879
    0x70c171207030e100519050f01081009080f0c0f1009140102120103022e0903140c090a110405040518060912030f07020f071e0501050702060a0c05030d02030f15 70
    0x2004800c00c07442001d44131030b49524002c00c1e003500d84020400100f9050449482082200010496880c0c0f4490315503041c0400e02c41c030141030081044540c13194500340100e40003035400c28444c80c03419404600c1c92650b580801c000f440e0314080c108500000c444180714100c1c8000000b1400714490b03c44c3e0a02668052408520081d968410040c903002c580c150b0414030304507034048a02500c07864130075000302d19140320801000382070301c0ea801d4082e0420341c0010302a401c0e24002ca00e0b00364401c001006071540ea1010309400c940c884002c900003400e0f84c541c2c1d00102203282c1d04000940c02c150392480814142c3c0c00031344035001d003040c12003480c46c0e45103070803c1500d5000700494020444400f02c0d4464940611014049141c01141680005c14440c02002002840c0030390100300c91006607141c09040b1094490020b41b03400300070107540022a90310071025200c0e6540c00409044c601504030358245c0d5101c0201c41304807061301003888100300d41c8000b440074501c030711000ca03540c5500d442c00c8081400b41c108040e0100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546550377 1250 546549127 546549131
    0xc0c011506180f0e2a03010e0915041202010608011a030f07140402070c050315060108060a03050c06130f0f03023c040609020c010209030601080d08070305070c17120703 74
    0x10003e1028001e91070341224141c2ca000002900c4246242c1718010004420b101e07504100f03032405042d115100025030490b0200c00440d0815218503404c50f07112800a5140e01c02c40c031f03100d008140410325603120b80e09640142e000000301c0645e2440c44600b03542d02e990f0300002d0000b000452a0b000d060600143d48a090b9000107040c0301c03414051110a0b491000f51114011030f8041440c600f000000801400a401c0040c2200c8015101400004170000d080b45e0f841e0001d0800b001052041c14001622400e6a503c0000f5081ca140c208043c01216040f072014440c0d6901307a0180045d05030100814840500103111007200c5060450050250074150000d00c40442050380c00303020034614805800030354a2038040b81000c200e1280c400042c014027025002503e2483c07000540e000c40d500154010b000c02e00e000c3e01960000d07039996040544810100f541076001c02d4507200098500c6100340d0007958040d002d81030040041c002038443c114401640c0044401c800c200156200c1410b420724170040d07122005240c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546551627 1250 546550377 546550379
    0x507020d2003160e1008030315032407030605040209010e01030e010204031e030224040305090301200c010f0615050a031401060309050606030f1b040b13021201060e01050901080c0c01150618 83
    0x1540740c7d01e1200400c4641440d85041c0400c4c03295030305100040c00d4071a003240100c0030401201848400e860142d44807c0400c1c07401d20001103a05143c002d0f590150416196413442c5a0031a0054001d0040381b80c00d0761155501300008000901001c500840365181c00320100b100364950306e0060b18000305101c00900890300031101f8101540d010043e141d020f81e00d85000c540b90700c080c10100740582080b0580400d91844100040540c008030400307061220070303200080c0407007c003208056085410070f02850fa0801d842d13164084544d8082c0005100010403440c0029071175640c40420f403104102a041000000e440351581828403408104403500200110050606119034480301581c411201582c4404014216580c8110b03642d2a4002c01c1c007800701a11b8048488007103a03080009500003170402d58500502000450980c0c403450343c450b0101c4040c0c40d16840d0403406401580c46030300041c05100c505204100e9069216428000d41c8100301c004018100c0440c1040005801c00c2e071034108007005102c0d0a94 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546552877 1250 546551627 546551639
    0xc01020f0a1211150a0b0333041407030302010f0f0507020718060509010305030706290402090604170a02040b01141b0111041d070507020d2003160e10 66
    0x15001522402818148400c0c0e00b56400581080c1101c282d1041058000c02041003140041d00482d00e01b2000724141c4d22202d218038a1120940c000301c0f0f142403080d422451074036203046030031342840c2c00c81c1c02807400d094504216004949002500d0704100c0040c0d441e9401003201066900a41cbc6031500418001d01c0180b0784244002d60700c5404c0d10600d47e80c80300454481d071000075541d00003000f509003d410400c0542c1c484c202161b40703601c203940444850f07180004c2249181040442c00ea0403060031020442d2140c128020440a508000c944560240080000060b295803100d4040341c0b500c10480503110350300301b80c010482100c2e605440755051100050040305522135540c2100d96400e02c0070300c03000140f5040c2c1c090500410030950142d85204000501140070b01c001c2c429030449082c40d00b241c0900e42e492240841d80c03801030020003504a508250008006a2060000018805c0d4030a10207140301072000020316058050a03500c0115030350310b40500c6811481000a0b9014403000e54903600c0c50702e446 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546554127 1250 546552877 546552893
    0x250e07020c0906040b0d0c050a0b0a09141305042609010f080a0908160b070c0c0e13021f14090901290301180b0a0501020d140f0c0c01020f0a 62
    0x29050501c02c880440000d4569030b155800000034030301c0600300b0105e280d001c1c98842c0c2454028020a40304114116000500400c4081298007980c90346c0e42d1500301910300155644050b03600750403a03501000350343e0305412401c014070545202d58000c1d00d13449507008001c17034220b2400322254455044a0000c10080d19582d820406600081040d403921419030350b10141617100a048026004025a00016641d80060310a842e892049406440b8011203074541e500e050381c0e249a4910700600d0110790440820860710051623482c1d006006c640300b14070040285d400075204512156903040c0102c101402d0000c2039921600703c080900000c569146491040d00000f050b8240500c61100d92034070b210308078071060380742e081241c41c08d101aa6449442e940c640000103185a13114660305881e41c9401c000c00070914002e2a01000c90308107070042c1914081485048402e03029080880710190402c1003880c071034886603001402c041c00d111000d0070324140c05e400020306011110300281130580c040d66116010407000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546555377 1250 546554127 546554143
    0x7020118082d0604050604140708070612020912030a02070905040b06040506010c120905121c0e01090f09020c06071107150e030a0f051207050718020c250e0702 70
    0x512424105001c40862050b02e25114a07500c541a0040c0c5007071008005001803080c1c0681d100708d010b5144920701c4440107980d00340d18844c181440d44510001c12600d0300804000c408244000405464040c80102045907418250003515496100140035a0441c0d810b200300c40103802109400c1c8181c1c01c20740c40345214860b000c0c0005220759038541c0072070042c0c1e00552010005980c0013495100175422588050f0008003a8814180200000009d0803052500031443c6880340800010154038031403000c200b212082060928241807100110020612003a20380046006004038140981d0359000300c0885410f0010280108080c8102c040d82c59106500114604042e10744160003407400c0c00c02e401089443c403051101d0700e86c1502409a24405110b001602c100b80b071401241207a00707492016100380100d101705900075000703402442003802420f0221240c0328880304070b4903026003410398080741d940c100308460103542c44d071108075035049604501c1880f1610007407400010083e1035140010001e501d610007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546556627 1250 546555377 546555403
    0x10c080d02070f060228050a03090203070b0d0e070f0510030f090605150909190b060f090c0a0906050a3204080d02100504020f010c0609080f0702011808 67
    0x49180d50010200d07505035800990442c910b80b01880d160b040100003980000d01c4500703954000700700c0b640401d46071114141d024500b80d980c0d1340381202500d030440c01402c1c0900100da06005850700000c0351103800300030f4490111f0030a4005040810790b08000c1c600755040d800b0f2003424500003810001030303607200301001d48208642400f003a030500c500344000042c500040c008140c14034100500c8054084454900000c001c140d0382410240c85200141d0b5071048c0c0c094250f650446e038034001c900007480135044150028005401d103c00c94402800040d60035900b264858000310b0003250154103194412255001003105003040c41c901004020010561610200800c072000c0c0510f6203040d2586a084107408443c180404072501c03907865850003622000e1352500c1c00014410070741c03080e040110520a042c06035030b000303264407070b1050034200642d42101c1090058581c035940e8800e03100850000e90051262401250f031117039542e00513100160004c40350a032040141c800c005010302500000261951103890 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546557877 1250 546556627 546556643
    0x601030201111207240603080415050412080901080106080402010c170c07090501060e0f130b06130e040b010603020a09140d050111041a0f0702041e05040c050109080c010c 75
    0x794a0799914903010b540b0618052880f0700181c50814445840480c41100d81118002100b03a18101341c80c1040e242503000103403100c00100402c04c00c3d910b0206010480710700d00c0c00e00da418141e07510103c00ca80da005220950b001c01002840e8030303031981c0c4004807501408943c103040740750b0b051640000345480081c050040040c022024240181505101610011003e480c21214102d45400084010704400c0c403c00010941d0464401c2852414440c202103205000e4905440b101103628200042e100c50261241c001c002084842e4401505a40701005005691f060364014200b5242940301030905034030142c100741c8180000d800495218a800d0b0817112012811041c0031000c2d0002106040c500b02c00506a6180c02c00c8012121b0701c61006d40112404c1000821901c0304910480d02d4500c61486480341c1c00c541041081c00528050b4420740d10549280c0c10b1040350343d07c84a42d038003220010789040e00c1176605400100242e69100048030007030440c080180c0302507075030140003900c0094042d1004103d94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546559127 1250 546557877 546557897
    0x31b01080a0e2512020d060222030809010f030e03030412110f1006091b031a0d150b1e010503040203010207320c01050a0503041106030108011d0105090601030201 71
    0x10741c039007012440b16003a82c280d50b61240c00c0e000409140c0448501ea01c0c410203d840d000030382004180850302c0c12600030b41084503021a9039034010003540071311222039040c04c440e9031800c00d05100386054000f0303510506e10705c0c0c3d072801898005480b10a00f10400320406040088401c4022804400c2d00c0e000341c0e2110081c06c12059072001a640340304140c84503202c40c8682c508040c0010400902c0b8100032001100410500391680c144000351610403a038981101094203954228502c280c0c4440c000382c0560060039203820380003000440110540c4003c3d115070444400c1d41c5200784d032f00d208443c01410202e0781a1240c0210010340406400207803012414010048002419514290111402c565018003c8080c01c14561110b0117941e250705814403d40d000905146616440000c412000c03000585505052045120003150542d0008004942c50075030110b5540542d01c8130f102440c0030380081e0340085000c1c01040319010401400107a48080b5a042a06200c20010085626411340750203103001c03034500d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546560377 1250 546559127 546559141
    0x2132610020f042c09070f051009060810030f2d1205070501020c030412050d11060c090303163f0c1406090d0801060206250903020918010605031b0108 66
    0x1000740c5192100c030700100303080211101740450b203038003a80c081851190107036444409101e0005c0c0c003a0b60301400700e03200754010700c01540100041c41d40118868032182d0016180e51325808240d0404108a41c404034440003413201e4402c131414000b000c0800074504001d8503041e01d03030320000007850040a0500200150a0081c441c0a4040381c00724106a821a9503450b40c03011040d80c0c41c1d54104040c1d845002d0102074148031072040340710745804211803006000c40d40342c480141450354890300308180d040c0300c10000801c1c5070403414450103240d8000c05469110b441610b03440c000350820344114101d880d0087c03c44000d044c500c2401c44105825030701d030150000da0a441e0286c0e158031142c2498800748581c10030072000359000110b14034243c40302c0d81c8002240e40c4e0382030f0a90b80c4840c10f503000310401d103a007406082c0d0300a500e02142c0300c5c840d4500d0801c000796507070f4010555146040d0394585c016020b80c5000039100d0400d000f0303d401090142d00801c03d02c10302c44000900c102018103c03904002e40f4a011503d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546561627 1250 546560377 546560429
    0xf03070308090a0b0c0c03061303050316090504141008012307300b06070209070c02060d021b070506040609180219020f010e0f070902132610020f04 65
    0x5403109840b00380d90380e140e41d4145c0e07940d1610b044404d40700303106a4002540b1000c800c06400c2c03002d0342c141c942e9030841d1210003d841c0c07240e40158080041040403640001c80359a5406000c100c070031040d0201040e0304100700c07490300481458001c0d4200e6810b080301c0c02c229a4024241100da103c401c25011026121303824120b850081c540200c0c100302000c0e08040301406581d000c1070580f034110000401882408005200c654000c0ba0406540300304040001901540150501000d40307200405040c5040342d1010128101c0c0c00032410245c0e01207020080c02e0f00c000341000001c02901d01220752508007460410300078880c00545c003e00d281001c0d013100344440d8001a8054a880d0030045240d8020341c008442d0007562112200c00711500c0350f00345078413481d2450340840e80440c8134020801800c1550b0420081002a511005c22003810403562600020b100300c0f0700d80c40d00200c0703042000780d000755400048504c1c034041c4400c01c440001841004401e0a40c0030083c03c03242111400b8501701007070f005080c10b00314 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546562877 1250 546561627 546561629
    0xd06050a02040312051306140a11010b060c0703020909010509030a0f031e0c120c081501090906120b100602100b012609070b0c060403030b0a170106060e0f03070308090a 74
    0x300c120b24481c1307940041d031341000180c0b6050800011065150b0b40e0ba8800b210881190992070302031240810003000200e10500b0390100c2c003004c900001c116000303603401090b850760200d1501070391a00688002e004610380208000e4000c00034500900c41d03420704c540c0054480c8901030b43c0e40306118802800b1054140681c00213850200ca44000c420310b84020103140d400390038551a6038000030b000640e11060425a071061001c1c4000903500c111181c2d544030346220700c00310324010460520200c030074001080702143c028030002e00b00b1046012040702c3c0c40d1502d0302000300302034000d401c0c0004661b00cd100caa40c1c001401000e1041b640c4010514000305c1c401a207140fa0f40b9004020080800d85138598640c0d03540c1810740c010300d20340e000c6455491b9104800ca600340980b20081d0700c1c80d04103c0200e00401d02c00d400c402d088501c001c01030f650042e0740e418001c02d00c181d6503406540e0b594403500c08101168221600300040c00c01a5000002d001040e000251500850300004104040200e882000c07904c8605140c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546564127 1250 546562877 546562883
    0xd0602040503370219090b010e220203060402090d0c03030806010903030212090a030b07020a050d1d040902031f0f1a130c020c0a030c0e1b03240405070f020115050d06050a020403 78
    0x1041c2c0c2a100d1a51b03401034246181c560340442c1c1001c034aa003090401c030b0b02c810348036405504031640742c1c144500e541000e540040d04595100340c092003800c40a5a0321000d01d500d5502c2031115140d614614507001d08040c01c010050b9060000180040020940211b00410303482c0d0300703008140d6101c030307a580003a411109076040509005e0f250340800491a40014000c0d810500501c115070341408100000c03075100c03100142c86962898100101c51503405d003900208015440101695110b100f40d1000e40e406001d840742d07551030f8035212404404108402d10030f200803414414000388039400c2d0040412400e07811400b4a0260955980410340000d200f84101801840020400c8400d190f5904200d80c9070300c000d000e87d01c06105024007041107030481c59402c0c1440d507007420003241195142003202000d0920840241031300480c0c001700110315a55031050078410032041c1c0302c0107025402c55038001c2c00c44e0507041c15503070003038502e0405010603955507248003515640210046240d80e2071222148c064050f5034001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546565377 1250 546564127 546564169
    0xa02030c07060207030201150f3203031c0b040203060603011203090509130209090601081f0e030a08010311010f12090311030403050102041706070c0605040f020d06020405033702 78
    0x1002c10986c3c1034000c070420302d040b0718020349074507290703402c540d000d804070711508100c407805030007030840e0284000c0c940ca400e81108030311031140005100071a08503440f05040349a0f1045507103154a11549074440c40160141c2a5030841c20341c078084000c03c4580c0301c1805060708046030b01610718105803140d03c1a00103041c000c1c050307490500304030000108044002c00c049128100183c0062000300001940a040b40c04210080c017650030141c0c2d04454a00e1410220286940c564640c921401c0040004000704101ca5407003807015891800c12a0010703840e4084141004030718450120403561140801044000c6620001440328440c40c0030303038161901c0b0202019500000c0707000814844194043c00031500c0e212041c00795090000080b54403454212800000700702912100700204032650700c0a44e01920070b24403800400c4940c0c001a8644038030074811100250001424000c2c0c0c01c0501440c0e4003c42400404544a40c0c82c005d98502e41060300d28810001803030103400703415980d81c140c403c00045c55841c91 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546566627 1250 546565377 546565387
    0x70b0c09040b121f02090a270c090501030c03020702030601301b080604150c36060905060301050f0103060e07090311062107020f010c020a021311030a02030c070602 72
    0x1c2d9940b120741c03100d005040c2c0848120070004c06040e5000300c9030480d4000f1300b8250381509040c0c03601840b2240b6002c10308504c0ba80410b03000220220310850305681019214501094507002c001825204a101d48004241c014848100103813030002c3d40a0560701001011f01425164071180f1045c001d0290307020f64164814503608042c88022403007240c1c844100c468100030340c1e8451948075038030796040ea402450b0010451040e00641201d0f84800281c000c0c41c601006621520800305444009007280d007140082a5400c107141d6070b00c0309000324000c0c45282094106c0a1900002621a0005202d01ea0044021800060040e0302c2544007001502c1e420f12001e00c0303410044401400c1d204180000c40f58680880300320a52445c15034140d43c01010422100140444048008446a00094081415446804050142480f080c0102e000b03000d840e40c01849082905c0c010403100d22031548140351032605e02a403603140a00c8075070403a0b900c1304141d0350241e500d403206140c0301c61034420400090070782c42c4045a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546567877 1250 546566627 546566659
    0x15051902071b0801060305060f061903080a1e09090e010219081501030911010f11060c0c06101406030915010b040905150102030a0f052703060c070b0c09040b 69
    0x107048000019040340110b41d00e62145099402c950340b41c040944540d11140c0054081e11801c1142940080090301102003a045d0a900c4804901c15800481e080d44010512480326035200c52510024910210b881044038240345010780f0b00711290041e210000d0f00c0b15040b140c094000d40403980c0c0e0b54817002d824004c00c12440402043e40d103095903400138140050401c166958468000d9943e843c0d0072282c220581041003005540703452248041b441409000e080c0582c1711001444039900c1114042100d81d034842000c24600d080082c02440005881c003042030521103500891800c4100c0082503a88550340c0e1940320050345050000c182c030000080d06c2d0400800c94038040e034094000c03180300040610054036a540094103c00e1080c07941c600580c0f007841040901441000031510380001ca0a0261070311944000c032168034898002c020044c0016440c4d00d00041c10204611940302078038800190401c0d81c10b6071011860b80c4003800b03400c01000040785140b005e50b40ca81c8403010002d0018a09403400c2c1d9028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546569127 1250 546567877 546567893
    0x50f0d03090b12190506090109020c0a0b0108160504143d090507080f0f0c0705010207060504050f0706120203060a0801020c0a020306100f051005090a0608150d1505190207 75
    0x1941d000c05000405250b4000d100d1307030b004441c006c49000f13040f0020740e8204581c0c100203400c0392414407041e1290807001c0000ca0300c8001d0250190404c0009000d403024603403500b682c0140c1d182c1c0141d000c1c0703160003241100342c06810300180e0021076031030720100c4c08403011446d441c002d400880756090381c40009003480c0082044503c0002155400702c0c00784a80d50300c4a1050b079a4400450b401900420840300043c50002c0c00d50b4030903800100c12000d5401d050180e21307002c0c00c90700103820403900680e8410500051240c10403844050747c100ca0300500c411030070004001c01c0a121903008100d002d03008408100c595407440c402602500083c40219214003404010769079520369410280d000c1d01400001c42c0508007280901e800f910002840c0c0ca6000303103013400b07002101c032103003600204000e800d000c060220b40d54507440c0b00003015199135582c0c503420600d500c0f4440041c030411b2144600103180e40c2500040110701090b0a80c446c403200022141c1d02e248205182c0400444203a442e01d1000810004021100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546570377 1250 546569127 546569131
    0x3b1509012403060509150a0b0703230702013e01020d060504020f090d05101104030501140411040b13060b0a030518060105130207020a0b1210050f0d03090b12 69
    0x14000450300402072850503801c0324403500407213070001106000940542101103a80a2019014190481e095622020046d490b00030000031400114403140c503900b070a050801540c0c40030402e4100720f2400b00a50b0018010710f104403408940040f0200424a15000390b005107c14161242110304154210005040c001e52103407044000680c81c004001c501070801d4825940c074266546403091801c02c41d20700b0084c0044000d00100c6242c0b081e5038480b840344d07880b0300414079102030141603140c80382c1c01c600d055800e643d4002e10f110110b5241108200104002100c00368000c1025600054806102404a52a8083e201c4155078060910000103010090745004249056065030200100d4441050041500802c00d1044400f0351022005001038503040d131400c3c20042d9100030042c606501a40412100c1030294800080300c807000c503114500c1c034013844240d58000c1d0030488407141c0c2c2c0c3c01c04000500c042000300c01c590180c1070240b000d204060144d51501c004e4030040040d40d40715521041c29007103581c41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546571627 1250 546570377 546570419
    0x180111160218010f090911030307121101150905090c191409060312090a030606090b01030c170a0c020114040b100501020d02190809100206013b150901 66
    0x12094a82d00c207524407111180c142e40204030105141c61901407045c0c050002400e0a4601c402ca070408000b00360307810030041c0740071403254041c003240000203440070b000d000880c1442c45169042c08503c25518544481d0380c415a101031400080c15214020340e1032800d4070130868641c03c403500302c500720f00809401d42c0780c400b22581c4041402c1e106e10130305d091048500c01a507401d505540078400c101800494180134011000000d041141d40c266a91070340000c0e901c44c2e41c40302200959900d510030b22075a150086060710380c12410300c01d4000c03188061501010200a0201101c140e580c041014464401e4015000c100e9a0303e2009446050030305100d040c0349019100302c00792102c8440001090b50021034100217244464001e821408484840981030072900e00d0200c56503d01002010301664a0b00000981c444040e80180400d40c18410805801c413800c0501050200da4001034141da16080202e4060080d84034400c3d070074540301d101003805c0e40c0caa24141e070f650164101c17001050610b074041c103626000c04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546572877 1250 546571627 546571639
    0x4050708010216020d0204140c030f06060304150504150e0304090509061303030b0a171e010b0f0f040b100f0f03150605090a09020a051308070e1801111602 68
    0x350310035480e4200c0c4160000340d40c541c8500f40083c80940f07003541c1150900350015001241c01c0c0340440c2c140c48003910880f079062a155011052000816605480d241d00140a0314602c0c41e50401c0d407600700085500c079403864062500c99000808010400139210200d80901d2418402c1180807a03e080d1244c105000f00d10b485860640010f1036610000f407034500442e540c401450310f500381600c0c1180038202e803140c1c080c1c0090200200103002003e24072004544500c0c134000d0b08854050300c0700d402112110901d0f420700d81e81130a9843c449940c59008900604a045541405071408500800c014080c04080c00b5031041c001e80303601c584250000c1240d40004029528280c003030540e80b40542c00c50390a0b000031410203090380f20a11101d03001d6070060080343c06c0100400603075668cc5514805a0380490034120001301c01280300c400e54826075180b00c000d801203001411006e4104078106800b03410041c15050109a100d031510542542035100d80b00d00b801314005682e03250f2200d44c59240d11260207a049008031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546574127 1250 546572877 546572879
    0x403060b1005030c0703020703150501051002062e120b040302120c060c030a090c0807050f061809100312081b0a0212030c09040615170c040b16020315040507 69
    0x200d06000a41c4000e40a92141ca0842d1285402c400300b60b008042c00301d066103d1110044003081c180711014003c3c580305400032887c0d41c1008140544c0760b07450000762007554428402e10900400602c00c0a580180c0f1099840f12544c21091055105004d0b81c40982010002d26031041800340c0d00701c5c0315202e640603400300e038610440c1c0b0b40d41c034006e480364a81c4004203421050100e0800c6a052004542205184001081180707440d100c0c0451340d20240d00c110255880079100708100e051140d074500c10380c40200c5000c4e00382141c1c08960030850809002c480d1249040d4000a1049101c10100700f01039a000a00303d580b40d40055000b500340d602c03e41d1000200c4440b403040c0c07041c0e40e45840440d034100065901614081446901e545001d42004d0411350809001f80400d070b0540cac4591048070020400c00002040c0c408031600060007a61400c00c841000d1120740040112140300030089504039501a49981c1d610051942004035003c80c3d00c4000358035014810090100111b1841c40c1d0380603a0056060f91022 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546575377 1250 546574127 546574129
    0x90304090513030906050f09090a06141905090603070b04060e0a0f030809040c091a1206010923060f0c0a051209010905060d1103090604031d010e060c070f0801020403060b 75
    0x5501c2d10b610040c001801103c050050f140b00e8405003401c01c0722201c3c1242080c0c052000140e0700c410880d880364003150f8070202080000300440c6c2d03880c4400d8098072000d9030341003030302c01c030704019074250203101d004410010100c1d502da101040300c003004010a089944d204c50b103c0c0740040910613040307030b05403060250b10030204421500403091030441e684040150718091128003400007a112820041045c0702a0000000f800d241040502440c806185407841d07540030180342044001001900341030405c0708a1070180301d100007100e802241021880c00140000c281c010000d00d6a00c5601551100c43c10049070381d40da5a400082c04e054600d01c594142c5019101c1c5428034200780c0125603580e030004003492010401400d0042c02001d0340c181000d070210703440d0041700281e1070780e0344296070810995202c1030400092540c4400c03914002800201180d02e1191000002422400c03401c00f41c5220b80c074001081002e612040004500070002220002c0100e0740d00c400040c000e400500c41519420b003811003841d49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546576627 1250 546575377 546575401
    0x503160e07021f0b0a032405010e0f27031201030b13080301060309050102090405010303050a090801110f09010519080709090509061803040305060c0d0b0d030c110f090903040905 78
    0x40c0480c3e80c601c0505401c0e103a0205006050082d0140d5000101c101000c00030455690907044482e0740100340b410070101a030015000c8540c142d02c20761302903140710240020b010810403040d80002d442400d007010848030890101040c41040c0c04508940b000107444034034890f0140c4010304980c044d1a41003003c1d0b0f91100c054245580d000c5009160110420040c015035000b94802d4481034080c000050615440c100820110f400a030003ea002c1030010402e8480140e10130241d1000d041010001d011008031424040c0b1903000d40704c010080c180d0085076004139030f4480c0064621120bc645501907002c00010301c0034090300130654280f00050400c01c1d0225510301c80e40103c07406a1410b00003403503241e803061881c031940f5400242d03484450004100000c0030550801401c2c3c020483d08000c01d0381c03841050400b00c111800e1014650090741180c20350401b0079000a680300070a60084444428440142c0c0010424140c0340a40e0394444095810b10141250000180c020750340b03200410441a1200400d03181c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546577877 1250 546576627 546576643
    0xf03080f370206270a02030102131401090e060904080706021207020d02010603020901120f150b01030c080103110405041e0308090d0e0310020c150103080901022802060c070503160e0702 81
    0x2000c4081100c00490802111368041507086840c040c0c80701e015150b400242a03074003034900e10715600e0704500203212010030301d0f40000d1900d509003483c2c015035240400f9003c11351001403000340b042c0140e000040174400ba000c00ca071801540843c0c215600c0c08d12424034507850b6010b580e40070040c0705d0f061600c0181801442001c003540e800800002d6207070300c0e101c4030041603034580c0c0040341c1666400741400001350b103d04910005560244020a02c0442d940006040700c4550303000a042010440042003c20404001510400340644001c0f5031a030300c0342090501002c42d084d242c00c91250840c000b0701450f500c145000d00401c940c00542d02d400c04483c0d411034000e02d0040100d503140d0461080b084403960140e00a01624518805451300d0030040c900c50303040d00c034090b40252410302000640301000d680c180b00000122100280500b10080c000d9181d87c00c0804040009006080000d400d8050541c10000040101402400c40e1050a89620702c04d10071000e61045075a003409a80100700c1803400401c40074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546579127 1250 546577877 546577891
    0xa11060105010e130f0f2a02060123011e05070b01080105041703091c05030a2901030c020307151e0506010e130902090720070f03080f370206 62
    0x40b101d180c10704e8001030110380301c840c01240c0d58140c80a016031040c0035008800741160018600c16075203214100007100c49a4004086401020041c0f000b03100280700e81c122406c5100f800003903403540000580e1042c181791020030b5400240301410f44525407100c01001c00d54855040a003660b642d4040b21070903198196401440031001c45540441c200c07801025583c420103c0c0d01311900c07840304800304131180340d14009060005200000300400445180145e02804103000c400602c441500420400c103444859401410580c640744001142442002614141360308072200042101010701e11100070310144517184040e2009c83d0280041d524a40b16441c410f06c4180c4621b00300300706070303410001c031100d24500102074140c1d02c40148000d85c8481040c684607003005d80317502c2400135401c4240c0e00c5528080e6074020440e40003030414405801c141c1505c2045a88c80b030704640d1120242100c0c4079090180c0c1d503040c4020303004402d50408520440c1ca03116501c20365044d00c0550ac0406034001c03a01c540d0704484203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546580377 1250 546579127 546579139
    0x30a050a03110c121c06080a03050307050d051303030506030f1b0301090501110c070605030f06090a0603060c0810080a050c041d060a090b06090708040b060f10030504020901050306040b0a0c020a080a11060105010e 93
    0x6003001c01d00ad0350096521200c07600d455460301014900c00c4045810941c3c0749500e850540d000c01c03040682622070517401103000c40042940382501a80c10b43c1c2d44d00f008508100d1840c04915400098a00350043e05003564420020b004503400c191b410006a00301f4401120b0f107205130480080c64601034001c41e4058014412000c2c001c2c2d03120700500a45140252401d0110780d40d130b40000011588610440c0407240e003913640c028080c00c1001e1546900803003500f011416412001c03c400000d080017400508003c402d4a000c00c090122070303030050b40e61000c230381d211026005010403c0214045c0303520100d0001d00c40d80c1071114648950040c40f000100c02c6490b035011840a10109001c40c08503400b01d64041401001c1e14180c00d501c03800318a14a40c6840200701194072034040c041146070480c059405450250300502e000d00d019110400760401c040e0580021555800d034460069100340003400009411030351061b5600011b4400421800403809200030038050341001098544c441d183c580c614000041603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546581627 1250 546580377 546580393
    0x10b03100c020d110721020a1719150c1707030b010f0513080d0302090301060b0a02030f07030e0a170c0f0f0f0109050d05010b0111030a050a03110c121c0608 69
    0x30036101c0c0004e250350b00805100c0e2000020b00e01424121305070b07400d050041c4904d450841c6105101140710a44c01c8204031500001040d9590100018035100188189084048031012070038800d041015800070503201c1801c04160b0b80482d6040105d00c41414902c66021046a81b0880201c0c100c5400d0214940081e10009000900d00c0c4508040c0424600040c1601d580c203503034062182c90141c048659002194011400f02540d28080c400e00c002170044075500c0d442c050100740029104c1c810301c502000c05003404500c140a051061004aa62800207001401030b603480d40e6442c09d40c2c00355200c000d40c0900c00d500c80508541000a4140d03803405001e40a41d5256410000300844206840d0a8a041102e00c0300c0014180d9107076400c04e54035501070ba00004511048200040080448480140081d40204080b68440d0fa001c01200ca1003141c070300d000200540214081491391051010380f083c0c03480f400901c802c4240800b802408007407954000e030348030a2641028401541c0651061540c59040014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546582733 1106 546581627 546581653
    0xa030c02031f0b0f0901031a3705060102240705090618180106080402060702040605040f050702010e070b030a02030c0417071a030c03043002010b03100c02 68
    0x40e41c2517158150b40701e074040c0503600c1d8404590030301490001015006400c0f950814404c411603a01c0940000e09074880c0c800800c95580115180340501040c9203600000b00c1d20500d501c91180c4080c0c0702102494132a22800050090003400010413540600303a1720140205480300b48409681030f426154001e0112030580c8020611201240d02c0052101d140c0011b0241c2e031055045481641e95400d0703101160191442d98450b54200d070400d44c0400e9080115040745100c0c41c03095000b0000f0903000030b1110f94441142c8112041c40c5010000314403080c290360001c0d540300c80c900c941140b50561741e01e4440340f103000c00844001d0903000254280441d05525070400301852542c4286070960400100000040c400900020b205d0341c2860400401604c19044000c2c0141d4115101c071070211002101038081d2802c680698840e00941d203843c1c4030456203100303e41c28900c4079801000c02c0c4401d62 = true := by decide +kernel

theorem cover : BRFrame.Cov 546402877 546582733 := by
  have h0 := BRFrame.cov_init 546402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546402877 ≤ n) (h2 : n < 546582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
