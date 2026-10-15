-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:55:38.002552+00:00
-- url     : https://prove2.me/submissions/2e625938-3887-420c-adbe-f6ef91658fb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926618705 ≤ n < 926798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926619955 1250 926618705 926618717
    0x18061505090c1e2d070201032d0b010210230a1506080402010e0a150e06030c030103032a03021515011d0607020901090209040e07080604060f0e0a030f 66
    0x2e04058500c40d4030400003e9081401041d0481d415a02030f08007074001c80540301e00e044401e42e84050030400b0100602c0880311100c0010506008641e814011200424038244059a040304109030100d2960584d6208a0030583c0700c0700342d4003550348200b2204403002550740c014021000000300c0081214019011407809858103030000d0f016a0b594041c0103000d440d441c000c2480310340b40400440380d9520140c0200d04204c1207184200a5582e01004503014200510203011000e180340b1000d010954110b0b10709000b68014810040100d150300305481c112600f50828410b00c02c1500c95034282c100d20701c0a50080c0080a06c1880c00b03042d0b00282c070080000380744c144405962503c108c4c8101c1c00094448560004444442844c030f00125007002070846907000d80264203210040c0d0003d16262003d03044507130141e60115a1034001c1c90700e406400c1f291030115000d00201c40c24142603940f00c9400400c09400343c1d803100078094000c07149520100d104c01d03181d0182c5081ca40c81d85401040440345070b00f013100080d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926621205 1250 926619955 926619961
    0x4020109050904050a11150c07180612170c100e01050a0204120f02031002160c1d04240c05070203071e09090c081e0f0604151806150509 60
    0x10040c80450283e504100100101d448955401d0214034442050940001540f200d06c5075215040d80905800d43c039440107032000340d09014640c03561001510540413280d05140b01005070800c0c840224100c44d8012410510318061001383c0b144030301c00c41840384032900c0382c001c40c1c2c41c024840d80e1040445a085800902040d00c95044841c10b0740141d00a400c0080030504140703001840503640300c60003d101605880c610000e16140f1801c03a000f4202102544141c1d400000400503c145884042c0000540e080c165410303012140748003e0300108000c017211415480c405808041c2c821500403c2002032043c000c1040b00d141c0103100d0741008d00c00700c0c000e1061000c0800c0040764032010b848405e00103019400481e14101d506006000d101c07070f082e65a10046034000c0b4010700c0c1400081c102441040761318582c40d5404c2501450302007185514201034110030148400600c0c0f100700c111902e48000d10220784800d00d0b108058103407400890003005903250480408000410040f014100c0c0d000701d6090308199 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926622455 1250 926621205 926621209
    0x60612152e09030b06130f0501080c01020c0405071b030207050301181109090c0f0103090c171c05030414010b0a061d011103030a05100f0305010f06150210020d0f090b0402010905 78
    0x8a1140002003e000d0a10300080701806d2902590014824603000030904505440015048500030b0b04005841d400c614003032031040d40c04100103002d0107000c2d09c04014070b103030100c0000c0c1b40000001090300601c00d1400a0300030325108118810181900800070015002c1c40c0d00010300c1407401c03c2046602c2040420348140a160001080341f1686134003028240340c80c1c1e240e041291000d50000d2960525139620b0b14040415610068100500412280341c02c004265040291503c207040080907a84c155842034814107951290603240c01c0369000e01c444e004110030030101400342111100c900e0b00084482e07000a0740940c0514941c0e490403942188581c0c43c0410001150809085c078083c01190340100007041ca814180c0d8071050b4498087c0b18038140e1213440305070061750080641d00030303601c0d69119a5150791500c554450040184044600c5d12040f095038540a52201c11500040e50702e540e02280e400b095616a41102d1122005804100310100c064504400018801d035820382c0003e060f10400f0a840c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926623705 1250 926622455 926622467
    0xc01051503011a0f0d0f06090212030301060c0b0a020418051503160e06060705060c070b060d120c0305090307180606020105040f0602030c040e0403030f14060612152e 73
    0x654480e803040c40c0f2081011051050554543c04001d401607032100900d000705088030f15028006100341000304800d0030318010028801215607030b8072540d07002000100041c0340c10203100c0303910b60b50003042460650b031440312880c001d016a034000001400e017250b0403056180c407940114840d40c40701c41c00b011086841c0e02859030b9a10032601000075100a03401c24071000b8402100c0f5607111600070001c034503158450b41d9150030164155141003c5840c0810601c0400001014440d4843e50540d2008014610340d11b55141c5002c1c421203001c180a9213403240e405051260080b20300c54a40038049540c0b4940d07031184581080701d16501000c0c9640b031b00b10041038140c410300640307000b103800030440a2001110f455a00013580045d1001040b11400c0100080e005140d201c9a0b00c90340c00780d01c00044d03030304c1c448409900307641c012480b0203d03052507082006002d544100c240e420025061860415642c0c1d40c21038241d50001c454101c030307403244641040700c911001d0300500c01c60b0035040c01400550946210750940c0c070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926624955 1250 926623705 926623721
    0x913050a1107050c240d1503050d05031503032a01091e03080108031e0c0a02090c030a050a090b130303060803070506040c06030b060d0209062b2d050402060f0c0105150301 75
    0x10340601081101c286c08290707080041a01c00400b0746c072003019940c3e502d080c80c05014941e100c2c0403030004020003402c9098000c8400c4110801c1d00910700e001c0d0b2a01821034040400d8801201e41e5881340210705e14100c00350b114840d9268003a0740448000d03900f040001c4500e403410b104900003108c0000200c1c000601000b555080e202c1d2000ea01d1845c40030344080d101c00c0d006043c1c20302c218812100c01e240961b03079103940c40f0b003d440f800c10315a940742807440e000c0013580c0b80203104a200c2420b10801000140b54100090741c800000c0c000b1080d00c450701d02e0124050030040c3d00150091101141c3c01c0103010020500c240600d10604000c0d81aa41c0c5032026025510b2411050b94044401d06c45882060415001040a100300400c41c0d89046280406003488600b44004201d254240440032456810a0311402d0b1004604604022041843c1c1d0468800894800d5000c1c1041d80c580010908648590003912100c020b20040341e41c84d00d640c960400e00815003215007041001c10760f800b040032414188905d0348 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926626205 1250 926624955 926625019
    0xa091b14100207260a1506030210022109030a061a030d080405030306040507030b060304050a050111070b1b040e0f06010906050a050a0f0e060c0a0203120913050a1107050c 75
    0x7911601044d110409104041420b26090249030100300c005417a440f00c6c40c1030380c3c0500c000010700e681036005002211142252500940d8040c0c3c801c8203210300d509410b15602010301d95402d503140c44400c0401d00700258400001e000a08000600b040707512a52403020307640c4000d50841d80d82c03000070070088a94243c251006003103500100080b0380c8c1420aa0062039002c0b001d810080b03251541100800c0489d40304071001e440c0354104a4943c1c007044020300500c4031480c1c10200c0d141c148800c40e01d031001d441c600a403080015282d00d10310301a00701c00041c103980003003014100b03140b44c1d03140528202095485c100c079003500007038103090045507842c06801600c2c0015459070b5030b81d0130642100d406484c0f0fa02185d18078414003608562196043c0d0303440c0010200442814042d080c00c02c0f0034418140b60103d02c4600c0c2107501c605000b0403e9a445980340c203190703d4007603c004a0680c64801d1800d008110b580e041000343c0100103654024404001800d84420b0f60039254120014590003c00c0c1000e040c08200c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926627455 1250 926626205 926626229
    0x1403031e0a060f060806130b03030913182006030103210e1c0303050903030702340f0503190804090c090801060602011b0c03080a091b14100207 63
    0x9501040880300c4035404030190600040480d1120040000c030703030f5aa400000003e84e1a42086103034185020098600b064211007031040401d1403000030346a0080e182240c3c0980d424500da1642d00301907070001c2c1c1070000081204900304e0b46e5030074504071500e00c80408040c01307210080c40b45d03418140b80d41200e0490b90004102504034400d40c00d44140014090720003000c0001c80c01a0140e81e540d0799513600540c9090042e0ba8480f4100c5240c05030036203100600000c0700e500b041c405c11010503000f04211f0012001002d03030740b104904240700c0f00f00c920781c040800100c5004412010401000040100056500071000c03520b10302001c1c04803141510607800018444442400b0400154030700d50030020300c810007420310f80441c03501c54401c00e086848562008005030744a4500b6603500c8008442211450400d1030030040012094402905a110140001c01501e941703042d6841070000c01400030010544120103d89101d9680c088468004030001d440d0b84540258940d0f049071600029840d02110b800c401c0c90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926628705 1250 926627455 926627491
    0x80d02250312020d0902030d031e0e07121703010b0406122c011d01090b06120a23030a0909180f0f060b0d06090308010b04180b0307170109140303 64
    0x46010b034002e040e9000c0c1303607a240e41c5d0303203001650103100700d0401660541d0001400c401200c9126824403101400400c0145003410b4801039000205031201503902c2c907040791045000500c1c2414007001151111401c0810210001c94401c0418004000300c40903030351028011880c410020003264031107500000201900d1001035040410b040d042d1136150304907400011448001104a3b40c00403001904e000143d540e03107094402c03c82800c0c0610307005902a96200b9141e030304008481c0e5181a23030940945409002e400c135090f1100d008190302484207070f500a403512942000006031850680d40907072250236050541e00301c01c100b5500400625281c203c403224640c1609901c0c1c200c503034020714000303036903581c0c9454201c201511640b40d100011842694005940d1030742d4200101903c0041e0003000694800f004100419060364804c0c1c0e8505c9588900000d034414804001391a14040f54030030b2080030380c4900b510003119019400420160300600c3c41d241d405070640c4400703441e484110f55007080216501c40c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926629955 1250 926628705 926628737
    0xf020d1109240f030c130509061012030e0d02151b0c01090302091905090619051303030513050105090c030c0f1c080409110307020d030b030c0f0a03080d022503 70
    0x5451400f40b002e8281c038000313042400030070444005154180ca406880700103019140c50108450b0350b2054050015540700d41c18000801144441c07039001800308040e50740728000396507481b0f810400349030340203280c2c040101026400a4403038001a01c2d80c1403205215000c0c2494082c00302e00507043d61016564a0308280c00c46d4204180c0c200e0241c0034041500ca0f2140108840c00c0c0e80c07141c0703805000e01d0002807040b403038210020703030380800854200f40c07090b0704020600c401c03820141030201d0815454200451030340d83d00c8101e02200324422101505c0c03907081c0b6040c4802c55602143d494002c02c015030aa94115004c0c0003402400511075118680140320910107624295012441d026882e2041d00040d1919507206203a605640520400f072202c41000400d2110594040004100480d408c4c00d050001090703844c0040d80342d1003e116000e00403007030407001184c1c0e56144100340020350740c01030f280e43e21014803990010003074004c000c002800c84d510059121000d000120b04016047e8103958030070000031316050b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926631205 1250 926629955 926629969
    0x605090c150d021809090115080721050f060403030f060b070507090c0c0f0606050a05010e0a1503110c0601030b070c050619021b010f050a061409040f020d110924 71
    0xc0f920844d22000c3e00030136a140e40c1c00592134000c0a0a000205041e030741d81c2e100350060400340d8080e1181f544406410403010b140c10008a054060b158182c85200d6039a05109040c0b091903070b0005490300803c02008101501940002ea56646d01c0d03100b00704131911005003400c030b803182041c05851584049810004140c0a4000300d40c841c2c22071600011082c2180d40300040caa0030490200d80a648585050126003400c1c12a00e005000074a44040300c820000c0103c1e01c101914024001d01014946100401f80c0c029080b9001c60351303c03004072590390709400e1400c60322035100f800104c032100e4402e400700d290248107542d44440c59130014080d009589807240101000030503400e008000f20713020b01c24010f075000c52642012810110800204d181c0c03000340c080404550000340340389802454150140300a10300a82000c01c0944107661556964580c5d042a510011440030000d601441c680304420401408440c24145024107580d1501c241d21420011035907000100d80c246405003040081400d1803524003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926632455 1250 926631205 926631217
    0x70f02010c02031005040506060904020607061a0a030b0907061106010e13020a060206070306090608150604090204060f140604030b150d171803060c03061909090605090c150d02 77
    0x106241c685000680c2c0030904100b0a10146214a80d03100b00300310901c00c0c01d000081d030103441150019410300c0c0039030001d500c1d0700031104045d090941c0d03101d80c41c4d403034001128038050480d03004002d800c09540e2490b10031140702d000c8603c01e54500441c0f00000d119805880d181440e824081c000e4402c607820401c0079403159200900812903940d0166034040540c560030380810180242d0b45c0581054a00346d10041d040e00e501d0340c40500034a1411004002c07140002c42c4408485149413107607002900c80e0780014024080170500a544245070680009600081c910790720b0072505244004e05090102d001004002c1c022407001811001d000b00003d141d40910032501207000100505200c039030461501c8001c1e10b03903103c002029600e0800141002980d54989400800358170840040280303141510340c080d060300026003076502032514200f01c0b000d900d04401410010f44071603801002070008500307140c40035101c1901c010489004403000b030020750404c0c1c12018007503951012518600100742c1c1410307000398000c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926633705 1250 926632455 926632457
    0x100b06030117010609020a09031101020a050d0e0d0210020319031a012d030c02120f040603180501090c0f080109051b012f011103190f11070308160201020708070f0201 73
    0x3031140405e00c41c01034030140c00d005d00c4a548441402d070462500241140c07000c0b001c02d05560241d08040d00141002920204d55403080c5401d0901e4403015020413198030181c6c1009612010100c06600140d40c0000900b50118620310b40c1d80310020101c0096040303031980c00000c40141e17440319031300c0f0040d4003a48402c40004180e0010038020044031549000344180001210300107603c032403000d9082c503410011081c0102d50790110500c2c04919034440d025910840c85001c003071685136038151120b0744540840100c00c0750450000c1c40007803100c2c40d115072024828094001784502203080449c400f94144140811154064000c02d41841c24064920f04101d100c9100e40c100300780d1200000d2800c8000503104004000800070170150078078081076a0075201c8082c82014603640030301c10403a56805c07440b4145040071040c1c2000900e44440e20800c0080e04280059030081c510028a6604059212075003030710420408030032501c6a42583d004074240d04c540b0074050702c800c905120f51004100100c150302030711441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926634955 1250 926633705 926633711
    0x50403170f070b070e0301020f2709010f0608070e10181511010b100f11071d0601030b120d05030a0f0603080c071514030a0f0609060305100b0603011701 67
    0xc0e031a4882542c0d2010004403107006800341444038264024079007200703a10089000b0760405242e400c10200707601484030181088070000c500c030320304805203d10301045500c020708a841607684514075421100914030490b030000c0d26810020b038a07103201e68912010250001c00c44c114501040c88111484565180e00c480c4044090400081311010f070b2901b24090880ca440d50a0250b07065880e103421902414080360058208072140614070b0b80c444480f00030f081c6181490b00c104c0b010402520714006481c1c0001c0301019441030020f042c0c02d00320304254400e0009076814800c5040e40c0c03041c001441c0e0030203442da40349da1014120b505030031300178406103910035142e480c0000d42d80c030f200704144199000340c1d0040c1c034503039000114422042024880e94001d86000b00700c50404100000c0c0007425004654551100d041001c0041034040c00a80c12240321410300300810311001c1e0b00d03912920000c2110740300c211024825000128100020740c015104004002007009045a2074015043d0384541e01d1080a080355503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926636205 1250 926634955 926634967
    0x1b0907050f1c1a010206150f0108040f052b020114150f090c2805040504020313062d060e040305070206040e0c1b0606031b03070b04080d0e1005040317 66
    0x309031081940c503c08865841142c510a0800a0b05150024012668407146465a10380799200c9960102c41d46d142860950b08542d201c0c00e114079140c50810000702507001e05603800900e60b4a0121070b01d110311551000b00d08040040b001a822142c0811031441e0812410000444103c140740044280e14806031448140016000000e00030107004c8959854005010401d02840b81e41500210380c0441c0b10303d051341c1c8880c150301c0060914003943c403038584100e4001000850020300e041404200540c00441444880000d444810000750852515030205000f0308684440c007d550190500322064860301c0030302910303280c07800c5441c0e511010050b60025000c000019041c0d000441951040c4c81e8004000c1d00d0301c1c0700d07400c941480c0b042080080001c1d4003a00a0040940e000708007440390322505e000c10031652286501003414007019600ca4602c0000104000800c2d803c081070701000f50b0344a54070305808218420400494107028074044000440c10b10003800019000c01d1203502504900d00e040341001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926637455 1250 926636205 926636257
    0x3080a0c0e090a1505100909020d09080c01060812160803040c03050d09030303320405071d0907050d0b0403050a021203010308090102060f0c0f031302090403021b0907050f 75
    0xb00c080d1124070349180d07030f035070b4144c0807640621141e009080102c030b0b0710560f00b00001c8020800903850246030381d0f2590006803541c04241e2513112440041c0e011150700c1e2030f496201c2c610390090281d8840d000f5540289588800c140f03c5900494520005188103c44402026107030081300b40c100410440d40400001d80201c0403500c20065840c100139540c0e42c0d030b00c50303505600d0000c0555a0001e60070b8110f00210a01c2401007031401c94051190302e4a0f254035103195210b051941ca840782c42e41c80b81c0311903005d140101d4024070504140c2c9100c1d205140854603031303941d5042440b2242c80c0072240074242c80184004180040e208400900c5c80c0303241441250001e81e590244212107500c03e07401210060000181c0305c00c103503010710000760310000d854600459850139100c00a100c3c1700e4a1312410110000100040a180c46031610140564000e011a244c80c5001c0c9006551012410326100a40244400c80701d02e62030302048061241c130003a81e075241020315226507070341c0c140c010f104a4200c04100c00885900344c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926638705 1250 926637455 926637469
    0x90f090e030f04260111040e1e070c020a0f030203150a1410090c08010b1b0304080313030510110d050a0b030610090c02011a121504150b0d03080a0c0e 66
    0xc0e162800381d04031480da40001c4d02800f0490700d00145803690420207038045018440c1c0c00c1e20300b1185190201c0b1050f9a807031010305500c4114503c400406c1f507031002403140780d03a48044802e9066100350755180f14503880726151503030301d01148002581031740026240d070102c8440c2e000302038003c0a40400403031040b903580f1000010311000c0380d0310f1041126259040040c01ea150044a8900d1598100928594180700441c000c9108401c44c0c0940b030041c46140b0030b507d51041007250024170050302500d890f000b28101c901d141c2c01c0b40340304c141c03002d03c00c18410343d070f10450300e1180d6140e084607000034038602203050441802400004202c1a00c1a503150b45012880d103003840240c0c410101240c0c2201b405041c01241c80884464014070000c6a00d0f144680004e2070301c2c18030711102c910040320840e031002e5522800e2441c2a5a0040203500c0c2009841800104100b01b00303042c90031003c070002841072140000034070210740d02174038024002603120000305007541802d0340600b40111a0f81b401100c50703816400400c0312 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926639955 1250 926638705 926638709
    0x20906040b0f1c02070308041b0308030a0c030606050406022509090506160905011b080c07060c15050613090606050d050304150203030403050724061202040c090f090e030f04 76
    0x10b000004142d100040c1040c0042d03400300f5031850850a01e00a84c41c000d190f0300e0000c200418038503100c408607190541d865038260055500880c09641c91410794040400340c06251710410120742001c0012480b5401801642c040d45c032542d0040106042e41c5098003880424411088509040b4000105800b441406024036460260004015a00700b4003c040c8d40e191410b140c1c002000401002402580e17441011b00c0c0d0840c4030070a4844412a0a0906001621035418000007501c241070340000c1030703900300000d200a10b018603005110700c44c49084450030b49000720b031500e030b2040025400c0000c18031300d94050200b440c000ca000169054446011070800c03603035150b00b500c2c2035001140030030140306100603911700c22075148003443c21400c09a030058035501842d0401050000d1400500300101c1450b84401605081500c041c440035668140364401141c040c0c506a014a0a002c0f00c40003840c0201c04900403035003000d1090218918003c00c2100038589020b00d11100d000400c08004c0c994922805040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 926641205 1250 926639955 926639977
    0x270518040b0105090601120203042901090f05060a090e010b03101a04020c15041a010608090d031e020c0c0619080a09020904033204231003020906040b 66
    0x20a05160030603249451050380018440c60201c0208802030340c0c0021200788034145002c1c007588944031451b065002c600a02890680340c02c0c1314036403100308000344100034102e03072000d5820007601c1e0b00942884c054950443c3d0741c5030425800003081002a20310317401141c0e020b60100c00000c4c14410b900001c1d041490504024406903128440d03680035005101d43e5a0100f0421101140707055005440c19880300c20030582c0c0c84d810b510100c0080c09001441c00c0240c010002c003245500740e50303107410020b4030ba60025100c2580f0362042810a451250180c030035001145000d03c00038000030020f803e500c010398020024000d071409580e0441301280c07241e001520005051700084554a62040b00040241500404880c1c0b064145566203015813030306940c3d01e40141d00361501e446400c1d03100c06078260904000c0307000428035800812000f2400768200180043d203000a215020741060080d0305c040c9900280306080e84181c12080490348140a0381c01008515005081607042a94402c80c00c01d02e130300404040c1c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 926642455 1250 926641205 926641249
    0x90109050a0206030702010e06273d0c050d05071716120e0309040c09140402130302130e0f07060212161208070306060813060e0309130605120601062705 67
    0x2d01c9810000d00811010b0503200a0800410701d041e005182c401171442f000101c080c180000d40aa00490140c10b049000190705024100d07046000502641c00400005039540c42c01d004608024072429690200c0d41801441e55466110505080080417aa103001c00034846d0320070381850320740c07001d010700ca000f160401c02441c1c8490028040c0300540e0014000c210030016040d02c11f000342805046005200b090646006849401035506a15480d105420280d4802c06810b0041c3c1c59201c190080300c4030a140300181e41812084100165441c00345e4007810000d6000440244160301c5044c0292240c00d00c021701071642c6202c0c0da02c402040410700082c6400058140b800c0080ca5901030084070002c142d01d01e446076480c64907a40586090107030000007444161140310000700400c0c204281c55090341c0050603082c2c101e11149440c00200b00501c1440e028901030b6109201c40721021031580c5c101d0b199034680000804030210340610382c12114030090407680301210040f6640d15030b0702c940440c109210282c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 926643705 1250 926642455 926642491
    0x50409090503071506080d2106180627090204140705120106080c0418090b2410020303010302091f0e061e010f050f070210020312090109050a0206030702010e06 70
    0x104ea0520401c1c0d0320b68465810700c0e904000343c1800080d43c40f294266440c00020700354500c001c0c2510b640561112058181c203240010980344212031400c51404a070030020040b01f0b80d5090828022105a50401c054014600c0111703103030452030308540358840c4002e01c00a0011030320407200481e03040c00d07a0000005000400d48403078415003d449039000d0940e905001c2d08911306170421103854800c0b4040c40c20316400d05610f0f41d65400a54002c030001e03e600c4021141c075480c00070b451540c145150800c40301200030100c403a000b2f60500403403600351181030341e02540c85e41e821a02449a2098003502d003007858230250540c40403c140c00b020352000b4001120220036075040250422144084043c803910300700c03199006070b800c030382c0c0c00c041152072050060408640b601100d1207103000b030740a21400a50071035610034800c8200c540c08001410320030741c1c0200c0b1486c0340d01c03200841c074200c3c0d603202001095907100311b4099000d4500803010f1a4007050f184004106c880351070f0784043c2070940a4400d42c2c0341c041d983c0d400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 926644955 1250 926643705 926643713
    0x10f170615040b0f0a11061512010b1324031a222303120f18030c03130b1602300d080a02070308010504200711090c0903150705040909050307 62
    0x240044140010004026a0402308001864600e250641510034a984100c04c1608082904400034080c401407004544940d1184120080c6c07031815100d088030741c500384040a00d1601d6003524415241c00c0200d510f00807682803414a1109006400b401000c02c4045443c400c0c1c113040704958120522500302841c5c0d008820701c0e80301c0120360300e410320080780c0c006106d0b03015003607560b0003603135400318921549541c4d5495009c01d1a8007115200c4141200340400034104502190020080c141418000c8624050035581d0461000501a1503500d4241d145c0f40514607015281504d82e804a802c1d100040528101d0302d400c0c1400001c190801440301703130f00030b03422851149421120302c03540040c807510103526164030355400420308481405118400c3c0c1d9034107802d8908410403040b01c2e400502c4410215641c403410b0800034120204a00c8040c46085060300142014075404207507214035030041e008060241d03400780d40d07200c2480b00070601003c0050600c000241508140030709000140110301869580e00700c0e0030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926646205 1250 926644955 926644967
    0x7030c0b070306080307150e0a06091b12032303010e0f24011407050d0206150a12260a210203010e0f0a0608060a0b010f170615040b0f0a 60
    0x8021810b040c0391020810401e80080b04542620380d0241d03007207901070100002c21b0018100340400f081207108002045041100d560321070b203106400f41000c0080d00725540f440e060131000e01d0007140f140c492081d21100000c1c0c01403a204540307170080942c3c0942105511401c10b240c0d0400d0303200d21300c1000c040d018807076020000035030340b9000b111101c40180d01903070500c107000b21a500c0320110360403c01e40f048a03040c0c4401d907005807100140e1000586800d00f04002c07000356a00783c1964040910049001e00c039032075161000740b45085030740e5540603042c80c1400d52900d100d0b0042800880b0042d00d20b40b41c000c00003400b1040203280780c2e100e684942d551008125047c0d880e9102c42da250030881d030307c1000103025030a02803541070ba11a142205000c940d545100040018152582c45122070303124131401d00240b00b50356001070307603005000c0c2c0ea050070032010040102d61802c00040700c50b21483c125400318042d404c0080704c442038003143c0c0d123141d807600b660741a25000750351122030012400e00000c00c1143c08140c2c844 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 926647455 1250 926646205 926646211
    0x4150c0507060b010927020d050a02040e07090e07110f0a0501060f09150e0c0d0507080121030e0603101703030a061205030319091b380a031107030c0b 66
    0x31808203601811b0100c8181c02400360041c50051003088401000180e0340c4d601254400e0001034002c0c0304500b814041080650400c0c0105c4c00318403591400550518400c1e0419422070f207040384450080c3e2a0b41030251007900c80031141d0703400c5004481c10740c08001401c00c9040c41c0d41c0d2141c4d00000703820740b602c00718855102241d004100072074180317140450402100900354083c3c40b100248041c150f240c401c00e41c040c0d0300c0345250035510541400208811150400d80300d078102c40c1e07640012894481c0054070100c031310f11700100c01000701e807055060032903d0a240380603550020549140c032481540391800742c0d446c0b60001021403500e40c0004204202e03181036010f98001440d0007440039000200968400d502c03400020a0b071028038042c500e1840307100703025402c403d02c941d8010441165a03040c0070051043c0b5100b5004041950700f80f034114180018861242e16107044a071140301c1c0c201d0f801018150110b5104403043c0040584520b012064000d10000402c507082c4030b6140d09405c0384070362038203108107c401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 926648705 1250 926647455 926647457
    0x1e06030c02010926090d06050106080703050402130e0327040e0d1e050f03070509030c1f0e0d0501020417010e010204030c05040915290301200304150c0507060b01 71
    0xc01c1d05000007440a0150032100340452102c0704c48070b09110301002143c0500c416143d07120355016219411301c2400c0d8030440c10b1340c40c0703a03441d581e0942c3c640c6010b0342a100d0558000750010881d0410280da54210303880f020101e0000b82c2583e241c03d07041020300e01004500c480058070b003028165030b03c1540ca00b900c10340950040030400b412050703110f08000f03070408516503481300e00b5503491032142c0790140c23140c411944d440403464402500c1c0e050800c0005c240340c09c50000c260082c461440021618030b000a0002840c0b01c0d60005503011403110403085802d0a091499160010016600070000a4082c005400688107244c3d568540581c5c40340c2003425150500c601c2c2045074410002403001c02c17504042041038880550f4045902d10140c40d001740d90300c0310381542010080c68881c044203240031005040c050705601d030702881075440d4108101401c80e080c42074001200d9104002014001d501040910703802030040415511250003606050151a810f0700b140c00020f400098120070001c60b071240442528007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 926649955 1250 926648705 926648711
    0x1f090504060e09280c121109041101030908070605130314070506131a101d060303030601030e0a120210061d0103150e032d0c190c1e06030c0201 63
    0x85149000d49416141a0400494004005403046a84c403c00241c04660b4484050a04684d4483c18136080d43c0548804031420007101403a1a210320b403001c1058065500a6521503840200718015801004168022034160105200407070104160f441114800c034003182c10704017040300e90728000301080500a00594400d00c180a001c012540029a00741c1c8101c11400201122180f401c04c1d924040200554961140d61001007200200c44134a815080b0384580a4000011180098007001c0c1c6900300c5e41d480d010381c004c0c0001800c0f9807080d044a00c031490160144e8421030180d80750106032601c4000900c0141c1d0001c00484440012481480007c08100c440d0302001d070381404060440c14010711024100c0c160441c0d01d44524080d82d8841e210360103070318084a03074904080c00c80485425904c0308003290301c1e003030244554145078204c0c100c400e8481e001c0041d040075420803d48940100114405881c10b42c03500c4004285c0d0a82d504032000c000c00b01d181440c03040b07403410340000c0a80d28045100030842e41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 926651205 1250 926649955 926649961
    0x1407020f15130c180605011b0b06091f090b011b030206060d05120c0601030c0b03041a0c07081b010f0e1e10180506010609060503010b091f090504060e 66
    0xc04840203030800b607034081207107041859080c0141c0d2030311660803403080c00d140303000c0c00840c10100e503000b01c0403a003080e2540c4011455041c010000c0188002c00640701c407081030005103291601940d00d0341d006502d029080030440d0400c1c184600b90f44c16030003074090155501c0c4000c0c0c0c05c0da04010700d84500d000d44200e860420300c0b0b5550003500c41401614560217110006000d0f001c00c101400071040c25a544010182c4500e4040c4c401903075258280b100b0307960f0002e0300102040001800003204c0c400c5800c2110400c0000c1d07024418524890010070910100d942801020005100800108000c60802d000d040d6140c01681c506400c440c01d1145912080d41b410550040180c0081182c604080702c204149495102203462a42484110405900405d1806122102044040c0380092006016000711030190313803581c401703694101c100c1c056840418824001006016140030042c0072856000d0b02c5c007080c841d0f11118180b441002021401c012480d440e00500443c00c1c54820700000709091507011103d03003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 926652455 1250 926651205 926651233
    0x8070c051909020714061608011d07141903050430030c0e15030702060906060d02060c0a0b04140f0304141c0c08011b0827101407020f 59
    0x10320703901c5105032880c0c001c00c040f0706021507001074030b51030000390b41600c0c26460301b0b40580720f0b13241c80401c40a001c10200b00011601101c51201c86012201c83c418149681d00d4000040d1000f00880140301c0b4070f4041048807803088603140300317248051015030f14042521304152504a01854200c295001c40b00005014585500c80208407511745500c60300b0b00184480c5249000c90351290803440c040c0e0806140c42000340e00d1003600e0021403041c001703035082d111142c5403009135a0b200c21040e91195030004044c4124400b601d8000c2c02004101d1809084401800941d550948951000c880542c0d1010f26010110360105c4148480c580691610002d0751815007001100c0898441203820640079044a051074004580c15401c4c0707208043d044580035080750b5852400314003030070042c0e11414505c0d8080182d100d009014001c0300c2e01030b00ca0800300c3d0503540000901d0030681c22803001143c40910820206200c2c2d03a480344a00310780f220b0904004992858510000f030b150039030b0803680083c00c0d448460725982130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 926653705 1250 926652455 926652499
    0x509030c06030a1508060a0b0109062703060e100b01140f07060e0a0b060f01081302040905010615020f0106080309212406030106060203131e0f0308070c05 68
    0x40000c458036900d945940c04103400420134010803000602c8242c0011515200015016110302840a814852a181e12004444541c0f40384902004102c0800304100c038514802d649082c0300d0305400351880c4081d5a03031165026108240c038040544c2e001100f00c6001c0c41d20600858003c402c00382480d42c03600004000c142484d129130141074041080225201c0300f04a52a044117014070316110031181100ea02e41000950248159013840c4514484c00000e4001e501a0030164403815000c5022040740b5440c1e000c1c400901001c0c50101d0707442d5654140031400064121902400341c00990040104500214040382150295081070455034418064140c66a07264030344d200c3c15400c0f0100c0c0c1d039241c076440700d01e0034584407070303114112041500741c1516030714440d00c0e5481c070f48100310440090080607920181640c0704c1c414100c1d4040c000782d1216061010350304138007910818400b1184504d210740d03600c02c6849554038803504100c480a0000a03403505014400701d141d0050141103075025601b0b050242c4401c0c0f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 926654955 1250 926653705 926653723
    0xa0503011a0906030a0f0803011d010302210a120504170f0607050a020f0303070824130e0c0a061716020705010806011205101a0306030c21010f0c0f050903 68
    0x481d01d1110002283c5031018018200080c1d40880082010445454915865003090041842c01c0200090320305908141415050407284c000c4c150f003001d404181030390076000d4002254504607100341c06050300081e00c581500d0105020703039070b500d6803554100114040c003c0e4612807403080c3d55024940e03002035442c001c210650454118100682d43d580b18103026800e141e104c144006040c0008003c00500e50f03004044640f10b40d40c9171000d251401c4c031900501240309046004142c200e109041d06840c00700d45a0f00c080e1400030200c00711010441b204000509843e125040319000a8900a180401071084202e0036004251010450004840305034025650318961040504200310100802e0160b4086c4200781c4c80314034620818841490701c0d203107100b1154001e2140307848001c205130340c0e181005054800d036030081030300034054444000300703204001c9106800c0c91000020312001c0800c02000c4400d1042d0000d031504490302040c09120544050300b0710f102000c04200780300040145007210b560129000780c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 926656205 1250 926654955 926654959
    0x304050d0c14010606030204060306050108100303080c1201081e0d050306091503061e130816050705032b0503250e1c050c040b06030c0c0a0c140a0503011a 68
    0x1801209090000440b0460441c0120035440c2030740100344a40d050300104156005500e09020442e039039001100c801d4400c0790f4081641900007401d0000a00c1103003107035000300b4441d035841e041500c3e00b01c4410820200703901489559221040c0e400c0c210f80500d90200107181000050250700039400300c003401d070b03200003004184508100300000c2c4c640c2001c0c2140140c2000003404451082ca02002150300005c404142e4000108002000400454100004090031544501101d09240031501c00c440c9111201400329403074020309101155540b400c01032681c0050300c41c035048130100c0907203483d4101610000440c50812208008100c1d80442d24220045842e09100607007141c5071070820304407103100410300c0b03642d4000e0f4120040b01d01440340c180303080005030040c0b05844400e51200b0411003190040110706400080510001e044803c144000c1c00d00c15000c5015203590111aa8500c002c008040d001110401d030103100c10201403c280351880c010700300c25402080b411120358030b42c0d0311b0b100904c500d0b54 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 926657455 1250 926656205 926656217
    0xe1006080708040c0f0b0319020405030a1b0b030408041a1809040501090503040b0d06140d14070f0e0f091b10020307150e190c0e1305161404020304050d 67
    0xb07420022400d41d2900117181242904c480c06031520f139101580d0b4000c0d18000c94003a20800c811051304d41c3c501c2141c048840040c002c02c0380d018541d1f2070001115025503001401036000b0000150000d0100c0110300c941e1007240c40e103a41d035041c40c0d04e820013240c00402103511b45030140300714031030080c2680842c0c0c0080e45c100c841304902e2703440b0b28000f0b01421095800400714040030500054004141e00a4081c1002591090148940704c00301d5050740d95103042410b900480080c149000301c4c07011b500030340c0c03400c1882096805164032411080240d5241c0d03441448030100c00800c000a540344080500d0f0440c0c103e00c00382c81c0c0200100c1c1001c070900005115148070707403a0051407641c154000c1040b200792940c803250714030b58500c1d5800f54000808030400c40d81c2c0355004030070524080258070000305c0889a80081c070701c80c5507400e0110a41c02c4d2030000b0080038408202212840c0031400400c0700ca004030401c0d880c2051381d1810501854128600822200d0007540107005210000d40c0225415505000c02d01d025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 926658705 1250 926657455 926657461
    0x8010207030c2015030603010f05090d0f18080c040b1e040509010617010c080919171b1c0306050d060e0109080a09050f06180d0303060b040905010e1006080708 70
    0x400880f001e0110315640b007098161201c2e06000a00051481400f0840007003100002052400c4181d172000c480c84046601b20743c814070f030054020307142e901d032058841c5000020080b40c0304125145046030303080050643d0209000450600e0a4040da010300d480070380d04032607240c120007000c0440011035640c1078400d58465000427032500096101000801c1d100038850f42409404100a0081c071b1900f04c580700280d81d910000c1c1122400064006071480c0c1c01095108035286074845034101070b07202c0c1d02d9802d22794080055403d8031a1813640241c2d010052000b400b04042c8035940200848856240f6a00749410500d0030000d40d0b4030041e1402c00150400c1020401c0d22580006c02d00409500f8002848040040382e680507955103c1d104006403102a555000102200010040305000c0c03404580005840310103501c0360b41c01c208400329000740c0700c1c0c100464010b840302d10500050b00660803220203981d0b00d84c010400282042d0340c01c0e4101912802d0100e407141010b400620320000101082c090040075008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 926659955 1250 926658705 926658743
    0xb0c1f023132030106030f051b01110d030b03010209090123011722120f2d0503190c112401050d06090b07020705010908010207030c 58
    0x45444503542603032504200d8903100c803011030708095410000072100581401103844803861100c44090103024460510302e00c1030b0025045060007900307010b80c055403035140000c0001c850800405040344940c3c0030300ba20030350407400391080c140303502982da0401594a4056406a2000c034080c5007015a03840c0c0820340509030700c086400380c413482c0b40664004134400f000260100821504603102c8200116015000282000440d4501c07031014100c4480c0002e8070100789480c0d42540c1c07042c0c149403e030000d060910100d403200e201c0c83e0796020701c11020682c1d01383c82e080025032100001d002c0e10310070b0b011100c1c50500d81014a010301e1058404000b0b011001011840d0410b03030762660b28044580384030a2110391005070340144480b48118003101184500001d003a0400d484401c0c50900c5240301c1d001503070303d80c030f400104245081d18072003c1e10469980d04603036000c102124481482055260000c00d03002d40342000040461240c1e600c201482c0c2d2051109600195220445c48169030704050058050203805038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 926661205 1250 926659955 926659957
    0x150121150e04061b05040e0c09180405340b0a050d09080a14120f0a0e0a0b0402030601080d050a03020a0905040213050108150d02040c02030c070611070b0c1f02 70
    0x801e00244804204110400066420144105400e107002041d030807085607080c3c800340100c5c01a1003220403040005095651448054181008018a8521034a449100c4c0e1420140b0503981510070390401d24403410200940d035104400c0090b4440080e04200481100344428507890003a00b414140000c0e420813514805c1c025504140301c00a0104040340d05450b100d130f1550710001a00e8080350700141c00c484100d20950070703161002081c441700007003584c0d408500f0141d100014031000030140da506c007150b01401e040261a010038841c1100043c0c1e41460700415240c420140c0c089891030780540c80e0781030074540c40400d480840c8450306026071282c1d0300300c9040c1d0b203512880e04201d4006201003600d140071401c8450700f00440d5400e88800005844014108005400d08058507403c108070001c1d001c018102544402620304107441602e0a00e200e81c80418241846980507900254030003d25403400201030203c10001d01449820615100300c02e16815242d40c03400c166803110282400c41c646106209030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 926662455 1250 926661205 926661209
    0x80703020a140106030618020f0d03030f02070501020c010b06160b060f041a0f03030f0a051c02040f03050f010603171b0303090304140f0d1407080102030406020315012115 75
    0xc040d942c038120290240c5402484d017032006a4020381401c3d94100c0700c140f00d40c0184007c43c0c014156545440341a8144244044a00360031001c05599106000c03400c081071019003030141c803038400540e40d500c242c0c00c05400d490039030300841d02c43c840c108500034690502c081840b40707030740e4000030038000c0303554500010f03059619000940d038125042601d07000d03a901110322900c0808030125842002c61003424141650b0340135120001c0c451110400211042078004e1029000501c0c15070354040321a4220014030040e070304241d00100c500442840b0a204201084c451442c500190f80020080b0038a035450307071000c0040341d454030000070500150132034003081c851180c140b80703d49550480e076513402d00303a406540d81d03071041c840d281d940142010b4500840c076180c0c1e5031415003400140030310189070f06034075104610103a0503031881240c8500500010a0340d028005584030b10f001d0302e0010b80340e151402c3e030710f80c3d0140e00b00310032030401c940700b01140e0052007941000007542e1800a40012000c040746000305240000d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 926663705 1250 926662455 926662463
    0xf0412020703081b1c0801060e0604180902011215030201030f0209190626070509120f01090606051017090f01050f010f0602030f07030309031e080103020405060a12080703020a 77
    0x140001c02e9a0180f601050b0103144c0e60460322004071036070741c1c00c0603945141e01c80300014074080010028607204c0c6204a44082001300141c3c40c290780c489500400405c0c0d50078002283c2d03200c4e864001550303000302c1141a070b003102c250300b44400d00a07100b001c11100424040241030613521030400d031040c000eaa05079040031101420340b868411020f0414281002e06204002c00901280020116944e0790380c401c001c0b144030048030401d2612541c8054416400c082d000541000d140c1c000407206500402c46815501c0e01980000b400800c1c81c00c0850a40d002900200e000f028040812140750381c1c4000c1d81290748071045000500e0fa25101c550500307000c00450032000540c00d01041c44a05d510300a040c6048404050041d08801d980360810303030b164055a083d90281c00b000b4401c190200740a0f4114541552080c5886003034a88100c20340e001f0000b41000010004880100500860519119082d0499404c441c0100d88602e0220b50a9200c2e2410b500103194090205d01502054000c01420b105c0b9540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 926664955 1250 926663705 926663707
    0x80f0304150203040b1009090507260a060501050306011409040b0601030e030a081504060f030f020d061d07081c050d0e03070308070f0c02010f0c030908010e030a03050f0f041202070308 81
    0xc1c05c3c119205a002e039090303481c0e00f40005000501e100390b031041d0288680c1c0207010700907280c549440720003c0312804c0029110504003402c4040103d000323009a646042c8200380010f4154106800d140c41c0050580000d103208982040541451740c849010650241e44545400030540d030310300048001c0c2c00301c0c000030043e178440468808010341d005540d4902c41c0d4045071004040070384003010802580d8540c410040c4000c100902403000c2111080b1403542c0cbda0028002140221090303540c402156880c0742100f0a40c0f1070816990904801403084000821f46880140400401a00c811030190300c0c800034001071010020310881801c2c1190040c2d4144050103007a40d4071b03181981030142c05800d048980600148040d40e5400940b40520719820005406a4031007800c0f10081409a854050003002542444958400040c60103070074002e9040503510304014649824070440080e01b680d00203891070010280c03900801c031403410491001a40903402003d5940078540c0c00c80203a003415103070b4001401c0850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 926666205 1250 926664955 926664961
    0x30c11030c100302070203010b1c020d21090825090e01060b070c050117070e010302070206070b36060a02091f0c1110020d180806131a0103080f0304150203 68
    0x18044d40a414072500a034002d010410306501005044d00c2d5507151500c110104000c91005030510446450043d44038200001043c880c0c4040c0030b07081d14400d01803500040e001c034018448984180121000c091941c00b06051070500c00c0310708401030342c9a0060b6104c0654424070355401403401d412100040400307040059071210351782000c81506000340101030216200c500304100180d081c10459115101554844a65101c038400440180d40030381000ea9010006104040103e1403a800c5640100105600340e4020114001ea86040c40e07d407292505458200e5510030070303080e070042407070ba6000c05511001070751990350b01d00050440316040c20034600c0c103400590880352907400c182659003107406885020010b400101c00c0280700c07001102034a0043c0c001c0c020005540c3d000d42805051003d4601d6122071070358454105d14944a4100c2c2e2000b103094008074004240700701e800880708507038060b542d8090f6a6056407140c42c1140326040091071450000000079062103110109411070320503603078043d55241 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 926667455 1250 926666205 926666207
    0x403060908091c0f0f0c051801061206050a03020904050703120c02040f05060d020d170a03021206041103040308041b03030f02060105190308070c0e0709090c080103030c11030c10 78
    0xd004800c2c1140226500080c1420818180d1a40c0400c15401080c0110f004155600c0b0b9140220380701c001c886c5480c0060001c10203aa511840780c819890000e0960000d6160120040001c90a810b8000b410b500d044028051621090f10700400d8030b8060320402032a8482d850002d01e03005041d0700181400780e00b40c442016042d41b20300f20110300c500031103007445100d1034290582c048900a80d51245d111005085003401401c01c0441c189000c1d01410006d0700034070b0100c401d590b940c0e02540110380020307800500004207022845003560810400d403800c105c3d400101c0317000c014500c0060405024001104002002c002022000f25a0304115002ca45038039582ca140190907540c051510b10f016000d4500041010b082c90082c940020301c2c0f600c848400c1900d1500c3e421003951100342d081d1401038281d680802c41c88004c29106000c1c020b9070755182c441c00d00e48224242120780080c14401080303404801040403942c40100c0412503a00000720402400d031040000e8a001b02d0120310f59080203007106898291 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 926668705 1250 926667455 926667457
    0x1b0307050609070e190903030905010203070c06061a0f07050a0203010603032607090b0a11150612060405060a0203070e0d03020609151b1e07080306040f02120f0c0403060908 76
    0x240c4075800c100c50569071600300c510f4050104885c41030b2015400184008032416030740112950ba4001c0c10001a0000c1c00d032540e42c01da030300489520011071119074005007081322500c1880c009062155100305000355211085c1400c1c4180500b854603a0004542c2000744041071004524082c1d0040007001a03d6503464064007030b4844079503680d0440602c2200c0c150554841016920422007561040c03401c0e42001e00d2028550041d03481002041543d00c43c6503540c1c4400c2090301601d2850011a9856260140807c9113100001100f1981604501c083c007000481c00101e003034200c2003507507026840343d8a0360703400c407540180340040381c2d40800c030b0050a005040c2c01088003800f41d188a030980b41400c0d45046420302000c0e040e0b480044043c9100000d00c400c3c0303484000b9001400220142e9420300705100a0540c0c1608101800d58402c00300005000c4d80380390611502c504402a0881541007280c0300340d030074804190003400e515450340000000b440c161000d4003103d0280d036000401b0442d001e05400d00d605a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 926669955 1250 926668705 926668711
    0x140703110405150307150908011a0312070b0103031b020306041223030105040914030a110d14031f15120c08010b0414210a06060b0f0702061b03070506 66
    0x140e482d04000c90118960304122000340e000141c01420001d1409440300c0700105450300390b03420040c584202180010342070203101d0f0310420b0340c0030050542c84580300305801c0042803000151282020003c820000d085d041c1d0450443e40c150800405817141e00c03424218251644000951600424080004002c24180c1e04a0a80099074401c0800300c1100d00b00303042c0c2d040c6500d0a49036940c0a200401c600e10301034010826161240000b46407100c407920700180341d50820a0ba5102051884c00d044464135810005180f408c401854008a407000c400b00103045844045c180051003000140d100c1e2500f134801806030020000d5148081b0505000d11005006074081da032a00d02290911080903609032203260442d060702c0001209078681440c1c0030564841d10000d0300229007000001c801e0f00400c520780e2424140805110300500001c840e5454190b0880745a40c00100c2440c10a0085228808030641980c1420354151003066a0300410040a044501b40c4100041148000500d080400c00e0218950380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 926671205 1250 926669955 926669959
    0x50d0b0f100302090705031b0c251205101116031b05100f11210a091703150114040911070b0a0623030d03050c1b0105151c080714070311 60
    0x900c2000504200c009100741d240310700296024040942c400c049001148011207001880c50ac59540ea88c1803d01c821060210241e0b6550032030900214070b0080c50140c1c1804040e062401e030716104032909038940d030864045028041004080314603002541d040300501689030094116800890340503240c1010b400e090140c902200d00701100070f503c45207040d0079182c2400810190302c84001c0503d0300019403c1005000703050441e103604041011524082c0440c0c00b21444842d1a9505c0c6001e82d00c0781294104070082c40c3c108080840030300210f001003800d4400f514500340f400b00f8060400c24821030580218040505005059020300450f19859030210741180c0320b17000d10301e140a94038443c03050407400f000c60464054000111000780f032442a80407550050f04000034a0518039028407503041c000c0c444401e103100703a6486060000e440c40043c02d0000c803041c03c0b00c0240607072101c10f0001c1c141c12401c0700010542500469020200705c60240428000c2111804581d0181d5603410040c0420381c10000d124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 926672455 1250 926671205 926671231
    0x20a020106080a0203070e0613051501170402030c1212040b1305060307050913020d051006080c0f120a091e03080601030603020612060f0315060a050d0b0f10030209070503 75
    0x540c4550101c2e01410711134004024040107032034010306501400008040340e074808038a06d00400982d207103201e00303806000e014074091503500b000400500070301c42c2d054070700c50300407400c004020050380c0000b0881030f0745e6002e5440c2c860600815040030b14005030001314540a000120340424070111680251000384c111265503a20303c0d5607002401114803042d600d04000800401184030a0b003031410740d0540b003080c8050010b20703040081d81104212017043d01c80041042340000b04100301c50b0b014580d150042c000c8681c1514100d520404101c4912600081c10188040c82c400224400300d80e0f4424005c4035001a12412909414090480100c215080072004074422001003104d5510a1003840f06076503000e00341525003e50000b60000744440200080e41c0000b010b4290714035038600380880c01d000c10700d0401641c41820300404000380c040301d50300b0082c0154134041108001ca1960500d02703420020b035410525035503c45505036240c0d00d08641010750840c004200b071060003a807207402140720340b100c96603003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 926673705 1250 926672455 926672459
    0x7060207294518190e1014090c011416021c031101060b0301060e090423010204031a0c030601080c0409090308090124051e030709020306120c010903081c0609020a020106 74
    0x54207a070f90255283d800c0c0c0c600903074a2504007403c1e540501e240c00c035034108803800203903c009405c054806003080300d61640021401d10204403002c001c12605d00c1c0003401c24200b1107030119034920041c0202040320400c10306070400801507442d2141031544050f040e010310391601341d4600b4043d2204400302100c80c00d662070800e001502607507400030b03070707059498980d030b000000c0c07641108108150300003a00c2624161400180c03000c80304074800c034034802124040005a221752442c20139610204082000d0b08040c0802d90820104858020031240d01943c00d080900d0705440303003880003200380070700e811040d044c0d45000214404d00d504241084d00c00c954240c0280805450000300340d0001c001c9148002403000042014002403030708044284030035685a500e109102402c00000e4a884110340c443c2d08155400001d100040c144802da0f01003070700a60008044200b10341000800001e04c030f04c405059818003140c001901c9a0324003c2140500d04180c081c008540c54680e010001d40c4250b461030055841e0401c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 926674955 1250 926673705 926673739
    0xd020f12011b11100c030f1517010501030f0602130b2107020a0b16020307061506090515092b060b03100e150c040503070602072945 58
    0x8001161030082004e04902501c4150b007001a001c0e1100310400d02d606d9130480201214079200f241d0382c104d1480310100300a450519400c1240548000c071540590504c0b005002059400e095940319a0b40700e035005039126202c110300140b0862940150010400004e84048000d4444804a55104d081249160b050b04e408200303a0366400d291100900f0040701000003030040c040c10224011034182401528a00b159030303500d0104544950000f882c40d0f41d14820305001c011703401501d80016120a0f52120468003403409281cac0c860203901401846100032a408018028084006036a4011003410080d000d20103450600058410504402d000e441411b08509409070640200c1d24441004009000f0921200c5000403415000401030752000404102c002039585007080602d00a14003035001e844007504010035521034240340107003001444c00b08801004129080c108440c0c0e6030300d40580440d904500b005080c1c00303002003084100000c066961600d060071029509425020608035880107540c1c0080070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 926676205 1250 926674955 926674967
    0x303070f061a0f1c050c060c030301090e01152d080607020f0115030b04050c0a0b0c01110406090b07060608100b19060c1b180c1806020303060d020f12011b 68
    0xc00107510004c10100d4030b4090b109070400722502c9014600b6504000e48500c0482c035a54000c1c0701c0044964000401080161010b2140e1401d00040d9402031080f03081c0f620031640018814007901c1c1e0f00c400141740303c130502a0304040050181c4081d00c84400126950402241c80d030344103c8880340540103100380e01351040b10600c0b801f000c1252541c03074110158115200d1166450000b0401c07a1a84101000700766107a6a80000c40014041507864075941d1010001d041d0a4420b200765a0304e005074240020302015401c050400f080d14076202500e501c851050030f01038040e12007544600c2d00c0d0300170080f003040200207a41246130244815640d6682e038180d00c41d410a580c030030611640000846503900500043c0403401d55110034031103d0080700e065a2901c2c3c0c542240c00003a08050110345ea6000c940285a41140f6600b440081c08a080c0c400d10f450400007a44a1100030416071207840010703c980119680c205d070086880710060f01a08007503900c00c4841b802414550100721800b18a81c2034500518400c1c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 926677455 1250 926676205 926676229
    0x607023708030a0e1f1b1215031b03030908030306030601091e1104091107211101020307020706091e09020a03180b3301200d08071202270303070f061a 66
    0x11fa2400040454a0f003c0b41c020203103c1007200c002d640404000003c0344050003441d10b14401e503101807803418a145009010340201e40d01c8400f5a030420300c10001d16a402080c010b044905100022a10750a4408690107114803d40c074188131900d04140c2890380310514000e4016241942400c0241903040605100d003401150002400c0614914607510320042c55004456102c81c01c0c108000c4100700c0d20545426608101c80040041e40030150821100b82c2c070100032401007240295031048504500507500a445550141c90365944d000500300490500c01e03408100d42c0014104490482055864944580318040d00e4a980d01d001221135a00c1c0e640260904440c441400e28455400d44081d0f0015910304408540701207207a00000c4075900d01040602403a820481d013580d40c45d0413483e100c14050304650382c002da503030b03002441800185a142d9003403078442c1460300c0d00003504104602c1980041d00d1441990801440c0703080340e030190800c0043d103803c0903008000318009809035505510602205010305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 926678705 1250 926677455 926677457
    0x9060e030304121704080307051e0d03110910110708011119170405060a15060903021309140604050c030a030e01110a050607023708030a0e1f1b 63
    0x410041240030103215580c1c606031321502007400d5505001c00e00e100c42d60000e600100464200050010421005000030329100700e0210041e018407074015420340e9102d00512071041816519840a62142c4804081d1800204000c25024100403072401c000e007191008050307080d486c4142800824106418010803000c1402000441e04103840b015241d00610803100c0b4050a001400c190303071811f003c8042190344214018001040b031400c145040600303e441070380d80c03140788143c0c40204ac0b03ca1640014843c0072240c0481e45076440ba9031440a50000700801a0014040f03d812901c40c8611603022812500c40d60040041d151700d40d40b120107043d00c81404140040000e1181e03900d001082d802007440d0050700c0c8090382120300500890390f0b41450100192044409a48400720200c514000c085901800d84c640b680b401c1008181c162203100150600b18000382005004000107103a26400d500c01a2000d04141c00c80700540e0482c80ca110011a01c2000c00009504141100c02c3e5000503010f6000210a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 926679955 1250 926678705 926678707
    0x17030c03031f08100605030d08160e150d0603030f0f0207180f0c030b0f0a0f06140d11190806030a0303110705071403061308030402010f030e0a030f09060e0303 70
    0x142440c4a07090340304095155500081100001ca49183d080110840c54007800c0b00005680d410301c8105072412200641017402c022036001082124406071040161164113400c18442a1181d240015562007150240c0c04010101140c1c1f54400002c9400000860380241c4a500c0340108501c02240c085019005550250341306080030819003029401c100140000d410001a000805154a2040d80c4030803103048001f82d240d402542c2e540c942002d041a40b600b080310b400f08204d00c0e11100d00800074542c42410b0a000130601030403240700d1240111001442d0444040100b003280a60301500c50300302e03000e0300c01c104d10002c400021003800740c043c46004842c02130092520100c2a60210050280900e40c000c0243e018000080021001c0103001c02070034100b0544008920b0620505103803000080403d4100d5a1401c08280491900c604403900640c081c608030034a8840000260301520020075246154032030b0910302414140d001c20000042c0c3c002d95901040c07581c0c0c841c070450708071090b548280c0c0c2c5500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 926681205 1250 926679955 926679961
    0x50d09150b190e0613050403170114090c0901030608030403150b0103020a080f09010204090f0e010c05040f1a120103060f05010f060f08270703050f06010e040219150917030c0303 78
    0x8514038030a0381c45131004080ca1400a20010048260791080c2d5045010444507000d400f004880061440d0141000c07a1411400442560025010240140510300c184100040b80089644282c0100015060590032a40e545560b031500c015041010f11110328150f260504204082d0b119000b150056145552144490784829195240d02c48001e890f94031590340c20400000c4a1103180682d440c0c2c1444410300160181da400300243c00c5d01c0000d030f2180d003008000c010922405940240c1041131b41d818069041404540c9405109030784140300d0076070a40581e5100000810000d0f0700104076068012806000326680d80301c240810010601038640403410002d90546518031401c03007141e1181e81502c910300b0060000c4407070524107452800c4152140c01c030150504c14030008005600000350810020302c86c942c94607245203c88500544002d10a1900400100e82c03188503030320050144c40c01d500514820181500c025241c95401d20422403a0b0036812680c2400c401c0c04070030384d01080c0c1391201451640d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 926682455 1250 926681205 926681219
    0x3080a060521301c1b081008030f07030507020406091d060103030203040612090b0408120f011212030209030709050a1503020310090215030703090614040c06030507050d09150b19 78
    0x500244851409040419148000b68003140100d080c01801c0700c0e0a02600305c4192001040854010300781d1a520940d14410008210000200c5130321031900d0b00019160101807408568a12900310040c0d4400d045c02008038010070f0b1580a25010080c0e1b0400c0d180111140303403a161a49001d100c050090b0300180000c01c006030040c40b600803201c001c07042c0080c034651140d481d085940b0054505440c1118082817004500c00d8003c6542d42113900da025041b01580b422030b015a450104040041041c03c030f0789800c140f280d0081d015a1048800142a29440313030729a030144005045c00c5440300f2417a8140a40704032007040c140c0482003513070b801801070b050b00c01045606602401c3c0300c2c00b04a800c07150045110301c402c080c04020f07500940b80d42d075011134261070f103042500984203400f94543d82c2c503100000713100019100814a404460660070702090685d102030741034139280101d02c00490100e0a1911110411006031458582031860ba80e08020207503d00d01801401e000200b0720300c10150740c400c0240000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 926683705 1250 926682455 926682457
    0xf0712230703060b0f09040506030a0b060f0636040207030509120a02120f0601050f03030912070b0705160e010501080a0b031216020a050105090a0303080a06052130 72
    0x704034100820389a44d10344110051341d016840301910300741d02003610f0340145014041c154005508900500720208517440760081c1120151482e0302c0b0349849074040750f00d510384100790350a20300f42c109072240b00e2000e06900e082d401d11180c0d4265a80120b000c4100c0d040c600341c0f0945d1403e50701951040d0600254000b40440030020f151607540d98840c0d00701d11401691015428003480d840000a0000c4030342402240d860018180c00207881402d5150314804142c40000035100d8064040f14003007261110040c0303d0b0b003000c0140d04003810003040040c201051041c001614118000c4821105e0b59440d642c41c250580b44200307015550000b83d4a8001c1440c4114941100f4010b040c01010f446041948020700c01048d4440c0018049c0401c00460b8501036251a85c0150f00800007800d00c0ca16128102d0001140900d0600005042c03090800c081100690710f9840000034001c080c0c5030001c480c0d0007030580003000888180d00c2c9485d1080e603482c000c400e038451042141021441d120413040124410440c043c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 926684955 1250 926683705 926683711
    0x7050901080d0c0609080c100e0106031a06040e011d07140a12050c1305061215162718060b0f0a03020904050a020301060f110a11180f071223 62
    0xc2d82d201c0c0e8200f400314000800522007140081f00810303034402e641c60113074240e6800c3e52182940d07034500102040420082523005404c144040240101a518280010b00410070005209031a61a00050356054000c40302c032003942d45d503540111814aa41d8148952140e18640003454100d410140c08101490081d81844900e034401c400303807003403401e5140c0451240d80c2c6480e9441d003000d8503101032002505088501d1280b0307401110240c0780c2c1055211251403910409458600a10003c4034025615032050b80c415445252498000114903070b02c525051008103680140200100905190660704031280300c3c0c0070407940400f4005090200c44000030010360407040d40c1c442419001c008203100b507911841100d225041c102e10058495050041c001c01140200c07040c401030005021901410036070000700c03c0b0056074489000c5418841800200e20280702c402c0c03802e140b4031060400d0125130709044d0100703840bc0d80541d6546000321091100c4c00142e5003516485004000300780c0403140300300340c07400c00c00d80c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 926686205 1250 926684955 926684963
    0xf06030f03050a050d050703020405040e061b030901060b030a05250e09070e1c030e01030204030803130804080d110c010f050a121e050114190b070303110c01090507050901080d0c 78
    0x4180070180000205a4104881000022740c0c0040c007802285454410380f041750074007000501c01031400c0c0340141007214038605907401da03071000f2000540441027500200050034203982110703220f0030455205400351805403607c001e0304e14451100384220144400c10604600207542d0400d5600c1003c051000300300c0090401d4080003041000d00f01c0b0364807110f551000300d2010b240c2c560310030402c074100184015a100207031410180104000c201107282d40f01683d400103801c4140301544259442e10407030314401c55002031000d000d4039540007541c503006081c9000d040e003d82c054411810f8070000440c0c180c10040f140101041052092005487c89096a00c1c44080b00324400100c004020a45841c0c00101c46a0242c1c19500c50b001440b1040c500302d51629a400d081d41e0b031001200b4541d100b10310171500781c010031441c4c00020403c1018180700350406a03454003040342841e620580c00c41003a020309000b80342034a151240480029040c14280b401d181250a42c1000d468101036000b4121150400071000356 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 926687455 1250 926686205 926686207
    0x10120e03090a140103110915221e0501080c070b0916080a0510060303020a1403090a09050f070e01082a0408070f061407120c12020c040f06030f03050a05 67
    0x10010761180b01e20384000d080d2280c003690603a4100400181610b01c5446400400f0300203000b42050360b2104040040c004e40c0703a82c521921103123418006080c0c8260140e10a510f25038040b000565000190f40c4903421601e03816840610a80b84c400540300444190780c401d000e100d0400c507000c081011501810b40080d01c0100342d491b00d1001900710442d0785225009413010390000214541048400c000d4803415101114003800194a151000303911040900340107001c0e000859850f841c40d890030300c100d4000340d00040000f103501d501c0b000d540f8024001110921034802c0303e140400c000900a000c480d080d03e1050350b52440d9680c50110522100140b00182201c01d00c1c0c845001c1c1c17100d0224030251018100d10001007400915104070031203c142d0603804102800420310100000340380b40401c0714642508680540d009001c007060850b01e00c05012800344c03a4440c00e080c890020b55002c220204020803c1b5401d0002802550342141112501d11005040003450320300705000038011405004500b031541000b0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 926688705 1250 926687455 926687467
    0x30d0e0307051f0c090302100315091505040f090b0c1605010f090b34110d0e0a1418070509060409091e03051b12040e011410120e03 58
    0x1039140c005039a80901d06180388800141c100c00682c030500003155074605d009400503103160040740c3d00c04100d0070f00e81e04040d2520340384035558414074104002407042c1c0c00c04211000324905504c40300030b10b83c003c1070710450401c000042271030310350b00a4803921504203c00302e1864440076110b078559481064070001c2c8100c101d8804011500a03c91a200b07203050020114000e055460142240040102040080c0119031800c2c0301450f00480c04e803544035200e03110038034600300a000c21f40e00700600602052036882a1b6410f12441a44481c62100520302520724140c01c03074490a20302c208144100249810038400c0e0610180100044812034000c0c0442c1001d41ca0903c00c00085015944983c000700900c5484040070b070f0801c00c0c4c03400f0801e5008074007405100c0c0d10030180d4005206100342c0c00185003912080d07030950b402190900001e0548480300440542e550354408001142210034492030f50b04240310b0319005141d06001c1d00c000c0001c80d06030740d0140c003035074000c8a1000500790400e4128080c8024420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 926689955 1250 926688705 926688713
    0x10c02010e0316050307050a030503070b221a0f07021f11070b090f030a1e12050108070611030a080105130e03160510060e06010e030a0c150f080405030d0e0307 70
    0x3d00c0b101c244098214006030402007403600d0102190300040c0035054402c01080414400310540f800d584c0e028401c0242030b151160b40c0703180009004035140b1000d003000e07042d00c10080d840c03410f90851480e446241c911035a406412042650040728408007580042100604a2615484110702d0882d602c400180d0906100034080ba150071503141100c90341c000d04240003041c00b0811210030a2680d1800540c03810700000d90052980c059034000b145412950a00360b00340902982001081c00042002003000d07695501a4550707401e01481442c0105400750410300f200c09020086526410071030711a0b4909c1d9180c4400d0001080b110020284085d6480f620b4460801042c0002c0c0305140e454298000900000d003032060810800141000145103403120800000348078600709a80f114090800040d50380c1d032080402e0030000c0c9002c0c02030484050384004528000919130b032000e5075000d5039402c2e001c020810000d07100c81c0303016a4054001d174000d1000211603c03454120388015182842541d04221681d56 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 926691205 1250 926689955 926689963
    0x90b030103030c02030f06060a0302060705010b15091507080315060c0307060f060b0309070b0a020a020d0b1602060114090a091a0a0e12090609030a1704150801080c010c02010e03 78
    0x70072800900054100b10941c602040b100c8030b4008140c014290f1428080700103090b1250501c8001e00400c0b01240d03e4051010a50059489840c05403040d0b401c881021000900c41c0d012446443c0f02e1009501445c5141d004a000d0b102c000e540512824139589818031000d094101442086501803010022066501e1040c0080c00b0120b200d00030110700e581040100351700341c3e140303a0441c0c50012420710030821114000a121000c4402008801d551900c4042049040c500314480181d00100f0b000308402c05c104650483c1d40c411078142c00702448484100034102e071038403401c0c460441843d01b80380b9000054038000702595000070b00424009610405640da042400121082012245006030208520540180034407103240c50400c02400303001c000001b1040392809007a008a0090001003652010358504022000384560406032008010104610165a50f481801089508400728a10300022402507200794169a440c0001d0602039a20b60011611185401c10980c100704000c0d0301c0800355203081c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 926692455 1250 926691205 926691209
    0x2120f07120b0f16270f030b06040c08011403070e04050d08220609020f030f100f020a1d18010801090c0b130e0a020405152110060c03090b0301 63
    0x1c41414000841c41c107003242c0307098008140441410400040202d040b6642e65541c190401d64182482d40340000c5166071401c0c0b105620551041045101c007056007501e01c12068100d034403c0c01c0d2410103070780308005d110650b4051807001000c10640d90040c000110b03000b0140102110240489980c0ca5554500300503826003074405483d2600716000d44000c02e41d02019660f80b000058807034004441503811010045409282d015001e10381e9010b07078500710355030000d01540060b002000c0b24982a4210f82d41520381e8180840c1d016013601c1c0101069101040e80265180001035885032200c8904040280b101e0390b03020321550742d01082101c1b8100f0300185008100e030207014444000548c811081c5171035121201c0f03d40000030550303000e100300009603001c0038441082d503010440b0b6495580382d000d021806406260400d541c0316003145410034041141c4d0000d0281164148140c1000d500d9450b00090513070700aa445681c1ca034064441400050300a50799441c009200786032140c50302e5502e940c1001c00742c01c2a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 926693705 1250 926692455 926692469
    0xc022101021201060e01020c0102030a03020a020316051510180203040609020a03030f0f021204050f0315040f0b0c070f06150e090c01030c0203121603110a090905070c0f02120f07 78
    0x5100520a95900103c0e0842c2081700307000411805070143d002130b5482c011400400105034000860620042c030038020381d116007050030000001c1074020b180c0b00b9125081101d92150032080b0100240980315034100a4040301c088186690352007011701c0588001c4d51000300b05a8655888249400050729400402ca006601981d200260490b6038840105010718040c111030455100c403000002120f084070845048910464038011200003c0d404a41407481440c01424440d0f41c1904100c1030000005c649a1a41e124058614880c8c0c0c0382b41c0e0300394040c0207010f4060f0407411500d0481001501300c0d4426441d0b526100c1d40c2c07602c640c4d512202d410b100341701261034081f603403c148110881540c01d03005003220510b942c000b170750a00e441c46120520010313001300048031054036148030019880c02580b00d100d145c4106070160381c1c2c8441c0c461004e0004065131040d010590725140014440314401c1522114150740490061064840343c0c0811418406151500c0c926008a910744c098014003002030f64010091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 926694955 1250 926693705 926693737
    0xe1003020108130c090b190315110403052d030a0512060418031220071b120209040813031a06031518071e0f08010209010c02210102 58
    0x440c8001070540d0030140600581c00a001d0350000050041e080340004e45114a40028482500d00c1c009002940b01409210b1390b002045004000c0c401044144010300b20710550510020001e403490b860f545c8030324807025045070450001c18003c3d032a80704140c20103e29001c1c5243e500c81030f030380145040d54010b601070000b041c400111210414034500c002d9501140c215810406900c0090340d01410300c10302800101040300b00c00740c098102490f279001c1030084411020300582a2424424103409506c4204181c03152120a491204207000c1c0f10400c4090341c060b0300d100d003a481341d030303509110403500081e0048032003081c04e100b024800c6908542800080d8084d45048c280500700031240300b840070018040c5802908443c40c0f903000e4808400d1610313001001c1c25000d60010798204401814a0000d4016000007100c80360700034a103c3d400502c0c1c8080d10000d044809400799582000340c02c0340710304c619031070203d009941c900c000361801c000e0124a208041c0c189000d40c0f8105107046003281d000401804c0c803001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 926696205 1250 926694955 926694959
    0x110a0203010e07260309060a0201180b041e210e03150718060f1b05120901021015060309031101060603021803211e0409050912031905100e10 62
    0x1a258000c80d151a201d0516030701c640c010034007940c0c0c4900c201c0350300347d005200000c0c0095842e4070075480303903010710101000d05101d940c603813900c001d400d4015a8155825500e80280f5003441c514030402d054126802080030030002681080c142000c5071680800041c003401240ea2035050b2014082030603181600c03680c210207868804030240400768540420a008094044180a041d8204078440f80700003c5080151a03004020f1808242d45072200c0c00a015005143c0303100020f01440c400b40601c00801d800345c0b406491440d0000f01150404260703021a800c240c07100300081c2d0300a0784200b001a0191030014846036000384001c1c09e588540c2e2006c400241c0c00038207201003102d00e40c0c01d507000807400c40203840d84441c44402054400ba046195004507040040c40340b44480e4580e0028940c541c4000381c050f12a69900a100f00800c0202c800711013600440240803c40104602280c0c030990109401100340704035001188020540100b03004080c500701030003c500c01c410007000e180300d14003011251070114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 926697455 1250 926696205 926696219
    0x706050f090f030d0f02040b0a091724040302012306100c030503070305060319050f16050102070e040302070902070809040b0a0f1820130b0a0f110a0203010e07 70
    0x2850003041c40301950002440c1c5249080e02104440310026240310105844008255a1009209a6201c00c0b9515000680f10600c1500545400d08131130007007c80e03110841c2c8100c84562558006100c4c001030032000122030300540080e280040c0c1050191000084a50b1042c8500b0401c0010704050803103401c0220411059140210314030516011500d0104003901803644c0141440c000600003409143d122000910350f80c81c200701881007108000c250850540e050300b019920741d01003101117503040c040c100c2c7d0302e000300f40700084c0310b02150f406a004101080c5401002c080078403002e0320850031401782e00d00000c0c13203000d03500103006428010800c00e03035503281d0305040000706d845481b8031034002c1611210400c071445080203203404907900806100c0e075940012015000800f02522080d402201045041c40003050440181c2280515030f50360b00310003510723460204003502610020f01d001401c0317201410600e038400c100208144100d44115010b4501c1540041d00b5034401440d29455644103850420a00f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 926698705 1250 926697455 926697481
    0x2030609070e07031a01030903030902130f050f0c0f0d0209031f05090708100f0f0213080f071a09120f030d0f090515061c060c0806030610061112070605 67
    0x3c641d00c0e080030403480c050030304040a550300560145d41407541d00c2c0c00000c10b041c025006041142d0f4024030075501e54001c20814401058010300d640907103440d180000c0e050001250845008103d003075005030030041c00c0f19141b9082e03400002c860402603024004e040154504001d0314008003540b052580301040b1302c58904080f0383d401020903100703074003d001c1000049c0010861802e99801050081510034141070b40303101900c00045035080b61440040c40705052812400c1d84401c1d21070407015a0702041c521000390782d460040d0b006130f890180d54a029290211020401401d1014003c2e00c0f44002c01e50b00340c002c0303040c40401c0d010402c484c0c00c00980c030191030704c0b43e200c3c91550004400c0304001c1d049251b01d840d595540c1880128102c03810642c041240c03940c0f1a0352442c1040c0c40e41d41c0044203603019240030000b4104280d050300c007003141c05000c01c40a10300851003911074480c000d600e01906142c6001220041c3c0448550099400b8544010200e4003003e0300502101e07008480114950130040044884 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 926699955 1250 926698705 926698711
    0x25a030a0525081b120f100605071e020f0d06050a0b04060311040f14162a0210050c030f0711180703200412020910082802030609070e 59
    0x106020203580740c02c0c0a030700b0601da207801001c0882c8100f41d81021454007013551182800c0d070030703e0180300d030b080100c04d0100c042030b00c2c415086040082030043c0d841e407069902d030060840051500d01020180c1d01903408040707a42e805a400140703058041d2110401041751140594016154079847d4420070110b44054004d01b10003c905580801c42980b640c5c5030420452010a0300c1032181c1e442c0c0300b180d00040715a03048081440e0f140c002c6103160b400d02d000041001001280b050300400d80d2080b0164001d10581503404102e41401012269401d240d402c01404010009030740080c0708062102865010003000641401c80541da08144e440b502030818a6601041c1c6903000d100301c0e0080284414049011201a0050380c1414042050090841001106541130300c10301040c42d40400c0c00900e05d80e0800c00000754500036070383c8a88946a0820044800f10309025070100307640100407165002d000040c004c1e004080c400842d0070042283d6001a00b00340341612405c082d035004460600400c1c0f00d1910050b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 926701205 1250 926699955 926700001
    0x30f080307030b120717010f0c020708160501050304080a020f0d1709060402010522050d0305180d021c020a03150507020d1e0f0c0203060109025a030a05 67
    0x82040707602000c5c0d980c0b58180200b50600400e10903000c1d0002003500003220740501150709000000030b44800954506852141c00b00a00c2000b80064401d1000d40d510f000303a8006075030b070501d90380e9551140e80c502e0340036101da0701c1103101301c1d50481d041c41030900544001800a684804031030307110403584180144080c11400f0709801c80d105102c0141e03084812100020a800b07000705680d1603d08a03039075840070303951007103070000c211140c48070400d5803140051048141c20782044401c1101001031054a0f44101300c001d410410080000c00c1c0c010744a54001c00d2184000c010514280d10b940c0d0f10001520314003124000581c4030402c0c865029014001411582001c2c07600c058081c0605251031058a40d4541c0441400040da504d14030041c45503910400a54026007200c81d0b55a6a01e5884000d40c450345a0041409640e208600b10306992510180543c6002207440d4514003140c0c01d02d05504030103100d4254101200403042408424440610301c81c60040c0b030001a54a06545c8041e082c1c000004055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 926702455 1250 926701205 926701219
    0x15030c020c1e1503092a01120f0f150302090924040212030a0206040b10032316030308041703010b1b0f070f080c03120414010504030f080307030b 64
    0x240311910303202c16500315428082e00d101c600390500c8001c00e181c501c0c3c2c5400320100c0c180000401000800000741d101d60003108040d101003d00b040000700700d41c042605020b500107012041e224118030f03034640040344407441a4000148884d01c4004400c100c550051010000345c07280081042940752802e090365000441d800a019541408281107420301048421b000394550b420001c5015034135081d100c00c1d617441c1c405c0c003180d684c0c9000b440042c2d50b03490304a0701150f240d01c8000c0020541c00551401004480e40070ba0003a04140e07013000030590303180051842d8142c038440e500a0840c4501c00402c80c0008601a80b035020260806041840e15401400105e214080382000100300502c0703c48100c55010b00c200040240034241ba17000c2c1810f00050001d0f10005120b0b071131010800e500f103c00303c40d0486140e1011a0620025501416140ca140b0b16032030382d299009010400c4000001d0504001e00c403014580f051030291a070340d0340c0703c110107540400c2c0c42912006c001c018103150035210380a03144000315125 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 926703705 1250 926702455 926702473
    0xb090303030c1318050a0e0c03030901030203090f0717010b0a03170327010c0e0d020109031e0204050709090b03011a011407020402071a0a2c150115030c02 68
    0x480d540340300103070111404400c00104806603840d00e045940c05014210301c0030b00c580584042d20005001c05171000000c403813a1040750010100000780c2c014002d080a00910704117001d040040d4001d400003000c102d801c4c01035652500c0c403000140310800140c0800300c40c10b1120a1181c0300d40f82103a1702c40c4950790003956040004d101103a0500e00045e1420150b080789075490366868403030003003a25020178000c00710600c010070304540b820640003582030b4a200e82d9414000300c917000030440c661000c0c0780042c1c00305060801c03c0c00800c2080c01c21400814071882c403c140380c69251301040071604220391716030014109100a00c4900c0b050300a0031a0740070102c000f840425190f4811340314140402d5605818048004034910101401c0d500b40c44942e50010130071511003e242c00d10884610b030190b0342000440d00da17000140041a5880340d003880f80c1a50a4680101c0c401240c42c1c0041c198000a03a401d0b4070030b0f0020341900004d5884010b001e0000c1d00c1482c201c0580741c0a028040c4c0300481420742c1550800c0c528 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 926704955 1250 926703705 926703709
    0xf2a02030403080304080d0510050f010801030213020c19060524010f0509151201060228120e040f060e16051c0209030a030801050a090c0c110a0801061403070b09 71
    0x60380d042d00e8004104550b00e48640c80d00c111036104803841e0340780003400c140400000c5c00900500e041101c0b020b50f1b143d0b04400310035004480003031090100940c0049001c0150a0100d900d45c00f5061070521801103654003014010358001c3d4840c52241140d4441d210000c20070321013200c2c0201d50700003044c003a405090010042c000303417015a9200c07000007046030102d8201c4440e85e80c1040a040034800c40c002c4c0d951200c0c1103031400805502401494090b100b0580d035041003521121440003105a00c40c00c400d0500b44036a02c5101501035100c10390108405640150320320303030f0750384079400c0ba000301a1000106a40381c09007066070b00e4002130640042c1c540880320640007581003800c440003100b000413542d410104000c0c2d0200280103245880d509481240040400c040c1c20000440c181c41c01110300c100850756071103155061301e400320201000a10045201400548040c0000c104a54000c03e0803040a450301c04031400c459443c2d000c80b050b250394002044a40c00c0900c800000742200b01c2641d403406900d000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 926706205 1250 926704955 926704957
    0x160305010b091e061b06010803030702071205010b130b03070b16240c20030a0906050304020f0616032703080c12031302040f06060807030b0a0302040f2a0203 69
    0x41c09902803080b2003181885100f00802108032100000c01640d211030360070310701c48181c0b401c14503c0c0542d0720038000082040d160000c1513920550143d80140911420000510210580511b08481c65034807514412602e0b5503030041d01840d0341c11a20001110701d440010185042e200340d028042c16403007008001d00500d5840c4c04440144d4000c544800180d03492080c40d24180810701a0050315407a0404a01072260700c400d000c419440140d500541903401d1151080d12880307407410b41c00103e08030081c00c0042074050f0028550190008200f5052020400080f600650000307035035183c99503403401443c1c101608040080d0083c0d806000218070100800d2206601107403030b00000e40840000b240200e91000100042c041100d10303140e642da142e061184200d803008022407001c03480b50381814811b0b030941080384a018101c82095840e0b203050b40b070b03840f8158010100014041e07084495081e01001584490250b1002e400e140040024401038071020955562542d81d1030840b27003150208401d241650000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 926707455 1250 926706205 926706217
    0xc0d051605030c07020d1403070b0718091107120806010f031a040207050a08071217090c040b1309050303010302040605100c021327051b03190305071a160305010b 71
    0x4983d00c0d034550160000400da010360030001030503a80720075010360000102202030501d0b10310841c2880c01c103460b100821f0b250710201d24981503201c00600c004006580c6c481c1c200703103080c0d80c0c01a5441c0c50050b50703494606650b117a030044900400d400760240034007540c0c0301000302c2010041d4942002010603100d1200c40c504054040244200c0c2c01148400601c04140b2400c80d05c96801400c45070746c0d80340343c0341c1102020408248040819440010480340c04500d643c824403800c440d80281c441e03043c032601008000c010b01300303005400c52002105002c002072144105081c0c0b5014000030b581300d40c51441000159004d603080640102c0902020040b91078102c07a004400c2c540c111054085a003d00001c070004040c07508400e0b881001c4900126031811200c07030003242c40742c01001582d480c282465011808218100c6415405074406004244581c0a06e0001d032486c81c442c3c5480fa10313240240c0c80710383c0c400391110079141c9024110001c1c042d03680c000d194001d4281020742810b0142d9032401000e02400e000b08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 926708705 1250 926707455 926707471
    0x10c060e03131e050414130809040c030f27030c080d0c0809060619050f0a0f0b0301060f030b0117100e07031418191103060c0d05160503 60
    0x52406024000014000e031202c030540000d42a821554640b40340380304100100c80500f54154442011400d401c060040516002c1c545280012a031600102240400360461040e174201105000500300c41c0d40f14080e07400c81055691740410b5141d013406141d411104044000000300e10723140050b820b0365002664409606030103046c03a03c0101e40d14103025040744603050000784440c0c41d2000b02e407019900104c4490190780b050741210349a550b54010301002d580c481c203e19000e44400842003190380741040054402d102d003c2c2c401c45106076158072a0b4501510303a081303940c0c00e490100c0144080d40d401000020312501e149400c0c40b49180000019143c2010108a500e40070720f000f0004444480703442c1b43c0c6000701360304403c0c4c1d900c6140640005001b400d00c0c112071108005010007164a10000100e00094054420098580500c5011010218210001e0200c9030501303e480c1142050741e05216091180750f0031140503944102441c0300000b2035000134101c40e407240802100703900e4107611100740c0b0f511101c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 926709955 1250 926708705 926708711
    0x60403121b050102130305060708010b1c0b0406080c180c03010905040f0c06080a0b09097005060901020f0a06090b0c1204060b1512040308100302010c06 67
    0x721215904070903507100c001070400c3d80001a0010220301003030156007180e00920503120710b034441c030b0030858040707000f031158110102d010b01400a041040011084d14a4128207000a2001d205000700d010f80700c40c2d900081c0c03d038109901c00803490400403000320b0704d01d0019444041d03600d440408000c0070b000601403440495900c5001808000111440f456015000004620020341c2da010081c402e1504542c0d0310001400c0015001042c148000000d0281c039810014045440c0050031624840c80c4440c0c0c48a9040244401c0303445509c812201420041c03181c2000319480c0e8014031a0003c2c032400c4403c00c048100d081c0070010301207907141d9858400c0c0c800c1201c12903540c5504000407460031206841d0f03010389005880d8514104009541310980e014441c0d0300034601c40d551b1602040450080c170588a095541c0e440000300014003aa00540c1c1c480030003440c08807500010400c1e420150030400c03541c0030852a010911050507000100d2541c46106020200c40b01c504503070000b481e901405030000c0a00e0340b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 926711205 1250 926709955 926709977
    0x4110c010c0c0b01030b0c1c1b020102070209062b05030717030105220f0609021803010506181f06020a02181303120209090910060f120f020d060e0106060e06040312 72
    0x11400480b008c8411112010f00c0070036204c2950030003000d0519481c075900c07003008038241000d80103000303464007250010500041540c841d07041c010010b0002c083e130301c101a2035045411000d101d00041c2c034100c0b40244000c64941107280340002c059205112203061250050004201a42d910305081a003a903031240e09151004d40a6244c1c000380c0f4a0010559940307082020101d120720040c0e01030501101454100c10903020b10b4020706003244c1c026900780d40c01100080c5000c080300c07020f50910f42c10545000c4440401d03106102103196964403600508016040000322000b5441c040c002d102e40c00e01e44042c140d5060130401100d45a02c690208000d081c030030301c5400c0c405083c0840e4151520000c001d0403c840310f18202c031003152150105c1741c10083c03003840c00c02c010603040d54411110042d01c40014000000e03134600c4e181d01420a56412040368001c40b01840c0400140340d6005001c603041d080c7c0e0000c1411410410043c1298100301459400341009102c10808115616910a04802182001b03c0d81071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 926712455 1250 926711205 926711221
    0xf010e040b0126061503070b04060f080c250201170c0a031508010c090e0c0306010e0d2604150e0609040506011416140d0e0402030604060504110c010c0c0b01030b 71
    0x240050f0011900d0380506130800100d02c2600c00c0ca0501c0510490550f50815140c07480c101081c0218001c0700c00140b480d01400600c140604040c0e0f800403901d01101d405c01d034130409151745800e00039100d0000c140c40707506608115604044181e00b0201c607103460482038548944802501e0007114845000c068a9808240ca4241c064a091014242010091100800c210005010022a807203001c0c0040300c4a0b00151000703860005480c0245070596400022241c100208075600c168400180d50911100540010081c0d6200b54880400c0e00d404419455038903105210b44200b40c0907240c0024000240448a45581d881003220a0070408840000c4e403526944012240e0100c82c6d441f0345203a80000550b11204400c00b2680304090344141134031110500706001250f15800f84140003400728806295154035407420307402035a40000d01130700024002c0d6031000010151000f0762540f1043c001c0014920070034120070302909440b9107a0742803030542c1c48800e0f541c403e00340c0014440980080c0000b00481c06d04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 926713705 1250 926712455 926712509
    0x13110403060e0a120c050706260a0e01060803040810110c06010803090f01030e0a03110c06070f15020702060301030605060a031205210c07081b030703080f010e040b01 73
    0x140da00800304004400c00118030580da6040d14400741d8142505804690315503219181200e0220f900102400c5480c0c901801621400200c40000103c0f10315040880355508a210005200d05112403020904a0101140f5070031124140c204040c140c0042200f800400350029040d81111420075000034604030ba00e005200368001d0302801c10103400303580c0c0001003204c40000540b000c85002c44041c1400031a290066044030740380f080460003a04010102d10100380a0410007044200e5001514240e40b400000100d455000c058112800c03080018080f05000d0320403107404003010000c130210315203c0b0039000070b180340c003051100911403921355000500540b41d060034080207662201400081d12030745d1601400030f8100c11196002c150404c013040071414072001c00f441c0108081c0c0103031881d010294071a10b0300396118040c2d0f014400414031403503040c6001040108245402640e8004a6003011100c10407440c0c01a80958800b003080f00038480480c0e9a00d070014111070b003912958410074140c428030100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 926714955 1250 926713705 926713709
    0x7021c0f0207050d08091017102709060516090e01061b0c05090c0903060601031118041b0203030907080a051c0e1806122d0a08040b09100e131104 64
    0xc00320b1f8078580f404543d0044844000380440c00b45100c110b82c0c81e00b810301140c8100f4881c46a50100c03884403401c17903100070064640c07041540c0001240901080c1c8524003500d90035140042c10a01c0c4040e1000e640783e100340440e02801c00001e20354029450300c40020300d0b06680913040710f82e4050188004003005250f2101e03000900002d062000140390140716502240c100c014014002e0040600090396980309114081182901c00503842c00c1281c0600030b00207030040b222005412550342c2944c0c61203413440004101803640a03a00460b62441e0504001d4203000807544802070503804000c0a60000c2c41c081800d00c540300e2240c2d40c1c00304070310000e1421a40010302400c1e19402400d44014050f030903590070b40c403503c1404180d58000013010f01701045560b951409030304038404482c014054482812103d6890420003591080b10914222034864003503a43c0660302c804840340c2c1c0001c10100034180352840d155032150505014260b0308010012031030920720300c290501c40540d149442c808560a080a07030780 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 926716205 1250 926714955 926714959
    0x108040f080c1c030603060e0c0904030e060c0102301005011404090e010605040612113604060506060a02061902041d061c080a030506030a080307021c0f0207050d0809 73
    0x981203031103143c0074005018a000c1618801c0c01c010900300039071000070740342054410150020b04140d42d00d4504950f01d40c3c1d10030590303610003000c200364241c05d01c0900141c0001c4d1800355810000051a0303000600a80d200c501c1c60b00740c1c1c0c0c82842000384090b04403419200700c1d01c0a0920b6640e582e068486900e8a10840d0041440707145030074034030001070005500c010b0540d40144c5040004584400504808444550303004103a0341400900312190b050500e85804e10b41e000d00c00b4149010740103101d04112428800c59250410f4a140403c4103020b864040d01da00014240e94682c908120703800001e484800c014892043d00d003024885008004003030341294000c0a43c1d10341c03441d8100007601212171180341035800e075201c0c10000d1811900c0492007420700100690001c2801e1030309074505010b9010307050013481e031503042c081d40101c1008525144000e5200d50718503030291005000c0ca2607070002c0b0044030044e100070402c030181ca60848540000d5070790b044e59400c50304c8149030103803444c1c220850310500b04829 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 926717455 1250 926716205 926716243
    0x111f051015030f230a142406040f271e0b0312030702030409060b0c0a120221040501121401140d02030703050120070f030f0e0405070801140108040f080c 67
    0x12a036244e100a10340c0203d42000081c01809407004501c1e030044416196200080e0354080c0c1100b20740d400d81c0100f440c40c0f00c090300090802e40e4030307540401c2c1c01c10280d00903c01c40340c4041440629246448003200c5400000004201000c6500c54080c240c40400010703013103065440944040a0703030200b001c020403500038066035076680f602c0c40000707440e074020384141c2c100d550411801003801111501519050401c0400901401415496602c11480c100c0001d03000e50240c8203482404200c600340f041049410100b000c0d43d6146408001005005503054449580c4d1501d0f00020011a0404a141c112140c01042c1645d03a0021400185141c0389600c0c02541407150384170010070040d06400c407284040c220b01e1195031141740000415902c1c8607206008014034413212030000081d01440b8a24000400b900e4851004403820f000300341201e0080e102980071480c140c004001103184244c07514403000d028a00300500f4202030340c0d480c20942c800e4030002e110000c00308107800340c40010000600e68250b03e036949 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 926718705 1250 926717455 926717501
    0x10e1309060b0118034d0922021002030906030f1609440a050705010c0819210915060b0910111f051015030f 48
    0x70400522040d103100303010416032444450304151401d24a0103d039045003c1c03000034410541ca500141c400a4100c075802604d0810013041e0302050908488004c02c144410300504400c4810001a150020044001c040c0040101603154000c0000d10204690564200c180c0b010b540d80e09a06500072140415080000070003001412803803d681c00c3e0042803882c44102800c04010380803910b01c12540a44081f01c100d00940ba000c1104100742c13100003800c0b00c581d110f00340e4041d10420080c00c88030500c50f01542d0110107030b1801d00405006150040c002400d040d420300e0030a0343c801010b030007080e122920503842503211486160045800240411080a071b4094443d0307032261240042060003420b80d8003800c1c2c2c054a1031810440c0c41003005455188d00c805040c090303135400b00b040318030074054034004200d401010400380c10010843d4038128076503110215510021803200c1c40c00ca44004100b49080c1441355400c201c244081c1400d42c001d20b08515002c105144034040a038060700e50864684c2c0d1001c408082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926719955 1250 926718705 926718713
    0x30b120a150605040504030f0c0c0b040e0412020c030c01030e01150b040609082a240903120f040506130e0103060203010e09010c0906120908030a0c090807080606010e1309 75
    0x100141d40c1c007071000100005521001440101c031411240240070507241e8404860960243c280300a0701403144c8041e03420280c03552031070243c1d0341046d400081908900b500780420002090a00d440c40752041c8014205081030600090341c5151041042e4107159441400b007030104000e412000d256405101c1c0c100203181d5038555481180e000d481500300288202030f0120340034902003107840040c5281e03401048140c030f00c2c050340014008040016680300003612084e00304084808908003c05888120540d1035500c00742c24542071995408111a078810104451211071046c1c005403001d48800b0f903000c0d03464096040080c1f0b4100a140c0194440f062002c0c00001003281d10b40003036040e505c00092803122070710b0320b0120500b62600d0610740c6021440103403052268601c140407050183e80c501d0804103541180b6150035015510a58a4000361350b1991060140150880c10032801841400d00400809290500064448001078452410000360721189403160340ca010310415290240c450800685130307d0b01d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926721205 1250 926719955 926719973
    0x1101060b03100501170f060603070e041b0f050301051e19080604060b06120412120f1a030f120306040b031f0f11030103061d06130b2203030b120a 64
    0xc00c40740040c0005c10700f175441c0480c0014050058030b400717040117647e4945204024031508000c5c0540708200340e80c8080ca130786503158014041100d07070003024102d40102d0014000c04040381c01315541e05120040004004035141c050a0005424008501401030f805400002d0382c0500002040380005030200004154050042080ca000300e1142c0d0081224038501e4040c490140540040308440340350440002c5c010552080c480642c806892070b03c05143c0b5841901c142c204e13007402d800d1241c010fa640c2a1002d11034151840311502c1d16048005040c0303601800016a038440c1c0703102110b2410107011001c0380c0d41d074607560231240c11483e00030180e0313800701581c910076800f0b907000c0c4050505d85400e008002890584620a00b503c07810030484a601e56070964031000040c104085061018024140d05d50f003030b03075000f445020700890340d050072003c00c40ca050400515104024210098289240c595610f500c410520355510b01a450b0901040d0400c0e03000c00903099180c100040c0107103004100c465020401505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926722455 1250 926721205 926721209
    0x60c260c01050f010f120b0c0f16050706020a08340b0a0501210b040c0e04231b122e0e0601060509090406020903011b1b121101060b0310 60
    0x200031040181c5e03948101c202d2074040382c40b52041c0e1404011046010403226190194007103509140075191403840d08180100c3d07800085540781d4800020b030120f0401809018040091209200500483c005d0b41c031142c4941c880c1b120490900ea44540000c2602c030400003c5098903409034000c5d400994807428180e84d00c0404032094544145840000f140c8101340300916100d07000c00140301041c0d0811561261b588031400746c000d40d000d07610200c0000300a116010004c1c4034a2080d0454000c006840031003002e580a0340c840020b290308610803c1c4006420325101101d40c40d07044403550352605400d2513031800c00003841e130240d120300c046180c1601500c500d4001c10040940200080000b20440c000081e1039160a002e032400041c4108003070000d501d08622225080f5005880051406c0b0b80840002d0848203140d4440001002040382040b403070307170400103031108400700b58400c0d42c480c0115901d403080303002c00c8440b1005004801d85c004000020075882480503210340140c2d40e940b41041450303000941c03d28 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926723705 1250 926722455 926722471
    0x6092d070f0f0c050706050d020c0307080408060106031a01030f0b10031b05030f0c0c1c09030c0b120a0203090a021c020406060f020316080c0d0305011e060c260c0105 73
    0x4001c04042d0780e0300c506640d004181c3c100d030140c03051034101441101d0325070140b0261a8110f80902210b0744035a814401841040d00c01c010301c030781d41d80ca0800c4003420041c05a10500c00c0c1031912024043c000020140400d05110910300040d0410384081c032007005240075140ca030b8000716140005048990198005078414629080c0c0102003e50441c04403103d1000300c0d0320404041c80c1c5404902000c0c0244080e00c508046441541d20f07481c0f110007030208072100900030800088007840b08101341300f08401420058100045214500300d0304080800c05000c0191078886056800000100301500070f010210005900070881001003440c10b002c2c1507030070b0a41d1030507440fa40c6804da00260103401646d400701d2164a41c0c020718240000c0e22011306c40808401070648007480204550300017600d00340710040c103c41c05a00c0010780c550601c1003081034032544401002200c1ba2070501401096042440c01c0c501950068901a150150030030807803402208200e070401d02c90b80850302000c042c0040d00041c2c4590750b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926724955 1250 926723705 926723717
    0x32b051009060b07082a030f040905060d0503120a0f11040518060d11011202030c0c01060e090a0b06060427140c0403080d2004050a080606092d070f 65
    0x4442e69400300d44604d90004107070312402c01604548185100324500f21b03840d1794451800c0311000096807821a03101410010750540002024011452244280c075000b41003540c45100c5000d00350f0b15181e4a118212064041b0481c9c140020350032145600480060700142e80705200c10441c540b00308805800034000c1c2ea00c925551040d405d01d808041e80c94610450004041001000b110386811500306038030600301d810491611030780c45140149000543c040c1540b01407081c2d45d1412a2000f03401c50b0707990342100050300001d00c14800503450001d641010303035410222f60442a16000e0000d201403041d41c0c0060102c07080b200f4902c0000082e84020f041404443d10144510109030a90741c0100e501141c41c0340080f04103101c10710101c5c3c42c402c083d041060840300000f4070024001420f03d02c800d2440c0002c264083c0004090245041c203580420080407540001d00c0300d420a03400191070500f000300039a07100301c01d800b0002011214491039010100040500405600b0040d4006208800042100d004540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926726205 1250 926724955 926724959
    0x2180a0605040303120b0f1203070807030e2818020403060614180403020d11100510230d0201050705100212011a070203061f0f090507020f0708032b05100906 69
    0x217001d0250100b401ca0050039020b126030100300b0410401201240b030341d140d100c1030081600007503118004010250003500c450300407041c800100403151440d0f00411240c2c070701c20520300362051448406501a80c42060500b1f40c400c4181880000034000d59002030f1445007010030008042071203850340391613590107840c1c00e01064601075414116510588005005a005100e480d047e00d201d1080540d0310100758003600c41d5103041c40480420f552064a0703800d5280d01e10b0104002513a499103007140303010b006201404128646c80c0024000060710000039041c4180020b030b060401ca07042c48041c1484c424000219226007148954111508090007410307407c03480d01c900c0010b0503220109a48001d13500500400c0140d84421520801020403940340000c0d1803101c03004900482d01e0300c803110107403c00c98000a107900c0c020340c0003403500310f4a0100540e00c0d08445010b20140d2008011640280c0000343c41c442c2051101e03926036042c0c0c0ca2542c030340c0595454a024400780780e5103444d0800c1140d1a007034017442415 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926727455 1250 926726205 926726237
    0xa090b0a0f0e04021611040b01030b0f0f12120304030212071e051f0207050606090f0a1e020703030b1e180903041a0d0e1f02180a0605040303 62
    0x88100c01040010403410440c181c0100e10601e902100000c0c040c02c094102481d06404040b074840c405812148441446010030540c01d051055900d84582441c050007500b8803100400d0440564045050140d06c0010104102c0d490b106485170f65208104203c0b8501c002c0c1440c0c511540e04190b50440c0103005150b002c0151050f03a00540307681d41d800c240c43e200443c1061310350000e0841d8140045a081c040c5020100b0b00031109504000d654030714060144c0c5d203502510300705041c40c60040881d031003174440c502071191114400440c568014410100002c0015403401c50f0481c044204444030760160000506104066260f00701106a9070195043c00400d80042500f61002c1400d400441c2c000c0b03443c0c581d401e8080e1030030b1a12500400343c8400c0d01e10b015150340c034403030340b2012040b010380d880c0c1c1c0c00181030341c1c0c0240d8600c41c0c1c0141200c440c0142c880c05205205810300c01484a1802c0f880580200340300c0c1055005550340c1403844001001f59031683c0e520000940f160f00140300c254082281010118011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926728705 1250 926727455 926727457
    0x603030f030a05040201090f06051c0e06070807270602010f0c02280209010e0609011202010509060c010b2206050114070201031e02030f0636070c05120a090b 69
    0x1038002000e034a81035503a02041000180401402a81013040a200c0080d01b40280c42240c00a00141d43d1010341d5000d100018400d01c500800702c044001c3d203001d90341284000040750090700883c65280103595600c52000484148400f0008002a4810685682d049800440c421401c4441d580c001f48800d1001142c01000c641c41130442c6e002503084a90145180552110951031012040120810960302c90700450f10040098100c030003c0e401c6e12003803000c18503104411900405040040b508002c880d0f6000034030718040d10308494001e0501050710302c9000000c1d0460000350707501500508c0759001c0b441d14010700400c14061412514600b01000c502c80d4400c0d080c180da1040d102560501d00308060b4011001890b000d0b40259100d035402100d40c4d01185030707000450180381000500045400c000003042180c074882c100110141903074100112440920312030262100f40700140d40384080c1d0f5903980596a2811120000b850b90103045407040c181014031015001c030150544d100c0d42c006465502c0301c00d803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926729955 1250 926728705 926728717
    0x4031806020105010512030a080f072003030615040305030f090a05060720150316031508010905070f12020907051b070311060a090e070306090c02030307030f06120b040f050304030f0b060303 83
    0x491120029421044412b0341d280c00110364505a50400a4a40e078a140c07000d1498000c1c00f150400001e02005141c24092210300100d0f01881624240c959901ca5589c1d00c6581c1c1c070304017213010210710920f5035502c083d2141e00403c1c0261034603075900c0842c079000c01d201048111440c0c114420031281847d9040c9060042810342cac544000714a07548500c11001107a150100000c1304058443c2803c5440e039007a5840500140780c404000304503024103141003414695503406c41c1411405240c0100300c0356040e22604a07005406030b412030315540b2419011142c42c810300014100b58003031000025000c880014045007124020f680301c1986101090400c141c0f40721741400e010001d805a0801c1c011202c14040c04c5801800724100000c0f22030352000f90009845e941e0b0003070000b40c0c001204000c98035815024010407401d615078200103907410410000c3c084518624007070000300300d180c0000c040003503000000910503000b0003200c0c1c955662b46800d801180051004481608a00c000b1a100d81000025160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926731205 1250 926729955 926729957
    0x3070b0c0f041703070512040e0a050610112802040b06070b070f030e060406050115030b01052205060417151603050424050709050307150804031806020105010512030a 73
    0x101d0140f42c0b0154030701c030804624100c9034600041141c10002402001a5080c002515100c96210380c603069050070301d542d0003041480d11078200001c002c1e41d95a02c0c0c584001d201d14504206042883c1d40340420300e844480503043c481a0700c441c03024840c110900c19000b0160f40b08a03014440107001c0001d12030b482c054041700801401004000c40d0005000c0e0040d01c0108005150003c1e80d1098500740500d0288180c6080d100c1d90b0340e50f8014498100d06182d100540049400c09000f6050000b000074100e210b80d4400c4154092091035040000701c00800000007800c00500d040c1e220781e00c0d1900407122814101310901c241c818200510002403091030458422034040702c5824240800b041c0503009003100520445443c00c2019108514944c040009060103000e151300082510704104060075500583d040340380f1039403145c0002c000b10466160300d40e1400701180f030001155260b62900350788503808140002e8a040c400900410351507415442941262021a40c8030605c50224100540ba4458286a54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926732455 1250 926731205 926731207
    0x1b100608011a010c1a040303090c09050405070b1809010f06030b0904080d0218060304150b0f0d060f021e0a0801061b02010e0f1903300f050d0e03070b0c0f 68
    0x1030b40c039800f401c1038805541c01540d62008642100c108043e04070000c036022408259180407507014808080794400103082012420040307800c281e1941c079906c02e224030450f1000c69001941c3c5000c0318022201140c00000500315104650b11401c2d50b0914221074062540001c2c540b8440107400c2c909007900c3c5000b40c2d04400c03e18079041d2801c1c070000c00b9510400501040000241089046072030b007800851240b80500c1c408401100c2d005501003c0e65900303031103144036480c840c0c1c4c1c030316041d07a0b503200041c00c195100f5030008450741a5090301010b4010200c41846013405090116400c1d50070f000103100004907982c0b206281ea0301d5010546189400015541d85c441111a081c40154010500d1814600c001019082801d0b007040000e0301a1301090015419041e110f402042041a44480207503481c840042c070a00c030402c007904e003011201d41d208280b020040183c5181040c58001c90403561100020403041c0500910f200d40503030340f6413000c1e40c01c4683c1c3d03000d0f60004810860441c161001d4510040c102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926733705 1250 926732455 926732501
    0x2111010e0a1a16120902130e0c12030a0315030b011d16050d051009051003060e0f062a070809011805030c0118080307050c280e070201021b10060801 65
    0xc6884d02840d08000c00c555945031003110269a6010707c0ca024507175035140220f0001079840b062802e0002040c0e07000e001d20314141203149201004000d460612400b80341c000381540060082c007214019907800038100c07079401e0300049900d02046820034074140342d42180300310741d840d104010ba204402c50f0204200159051100650300c0d00304d074100ca6003040f1514450180d0b00e4a0328104000c86009071004102c400012404004001c1d80d07028075101c0c400c02c40003401982108540064031000c00501a0900c44c010041a80700440440c0103a0307000c030041e036285034480d1020318080a036540406d80346400700f80c550a180f40c0c8042c00d1010441540e40c05405442509901001910080c20b030038034026115012030b10204454408101030400c09004030300802404100d0400d0181c00300190b400900101d0007141030119046c103810441c011030701d401e861581549d441c07600884c02405403103c40c1d100c168440c59116030100c2c002540201082c5010410004150780c1c0c5100c60032115a505a161039801d040c81d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926734955 1250 926733705 926733707
    0x150902130f1d18010f0c02070b090d23160501091710111c0f23070c0326010e13390306020a03182111010e0a1a16 50
    0x1c1030f08007911403110032403041640340c00350035940d00d814036042e443c0d071b03d4040a4015034100140001031501c0b03140945045800804a141c2503090f1401821000b00c400d140710841c64004042991444108180d0b406040720011010f1403040364468640050080b580205440412195114030340c61004010103505c0d024100346e2001d080b045ca60044000c100340070034402c12000564030300c8001030000c000100840340c030f940503041340c4010282c0d0032001e0703205501422055001c0c90131508400c540c1400601e4040c00e1600320341c0c28464502204079075000301e036411029400030052034143d4050000004c0c0d2aa918900404c2241c500030000c0c010007241030700080d5807940c0c40408061004c1c107496413031450244051400781d16100303a004480a40d40050409007072681840f0700052169540c03402c46d40b0342c5041d1102102414454442022584000c020908460003088000b10008441000340312071844038161b603861b010b82d50815600c0e00300c140311000100740b4a400013885002510804110081c81502c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926736205 1250 926734955 926735009
    0xc05091305060a051003050a0e0105070f05131706070f0f05041413020723011104090c0c050105090f0f030901170a020c0105010b07141f0906150902130f 67
    0x1014540040c3e09250124950f1158488162640115200840c2909140e45010129082c03040b901d45d07980d2400c82030140282e40070132054020134003407501a46400701d000e10200806120352004400008100041000309000b040365031050015803180074000d1242141500d01d080c13010740740c4000550400050090300c0c100f14080024010103481034080f5015a00405c0803079000440c2030310301b0003075001c0350035080000b0400c040045000400034000042010941100350190b40204e0040984800318200704510032002ca61005410500a0106041854000e40c40d80740302c0e202c000c8c0c14010b038001c181c1c0c140b2001086403c0c6200c1a51101c001d007070801400041c8401c05016441c0441d000c001060034040b09019550291a001c4861aa110000d1500f909024403515000c072007038001d040705e18140303054184045041003040c00c020500705118507140c4010070350000c880782031480300c00010400c0d810079806030240c08251000000b9280e00c030301c92605440001d00c40d2220244000034440e99404480b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926737455 1250 926736205 926736211
    0xb1612090f06020a0c05060c07030504090f150b0d060504050903070308180105040b15010f0207090b0315040b100503070b1c0f1a010f170411030309060301090b040c05091305 76
    0x49400c1c0d000d1520760390403040e64030000d0700500185143d03c0078028083c6c14804681c100106040b0f551902c2c90a030341c090715038026032103100c0805580304640e807500713080d94200c0681d41c9084111100450f03212584070229402c5840704040300307490f043c03002c1a00e0510b44151402031321000700450512046540c211800c0c14014020501c2c01c40c4215480d940d40030074000c49000d503126411558281c5400360040100b0583d080c40c50f0304000034400080c03081500816010151030840001140c12443c40c40880e141540001c01001038030040000c00040c401c05241c0507000d0100300c0d20040e41d4682c0c500805684207210702036a003031024204440500f04034105540100507001d08070104d41003902000c014100d9050340c805900404490852011560740182031110160040c01d02c218200440c2481c49040c1d04002c0c0300510650003110581c41e159010000e9a2820703100a1182d940c941e1101c3c0b00d00083c10024491a0242d400e100020b0141c1e0301600544140f030802030041c00422541c0240980901409 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926738705 1250 926737455 926737463
    0x24060f02010c1d03390108070c12020708030a120c0908061513050702030c0105180d080405070e07180509160509041506030b0f03010c020c1003021210030b161209 71
    0x41032044d81c1004000800c3d520b00034401c2d401d00508800000b58142d4801c0605c074881c1000250020045095041081c00501a0308030500d0007a451591038164502400b5400210080c40b0110b13803040c00542c0705120f80c00403a010030b400c0c012408010f03001d807514441c900800034076401c00d0b0005000352040e0000540015030040c1200c08000c01e041008044520a446000050300300140a1401210034001d15400080c403240c00404070b249009242d0b2100342c2091448200124400400c0c248101040344c0405058104e100182604000b0300c0901541584000c0b550010600140001d680c640b12142c0c81c8a19a614440690300c408404111b41e80e40c000400554820f513034201107107010180e06481030150001d601c1c0065080343c844200401d540d81055450311070380c105000344080070f0313002c51048074084040d03c940b07403418001d150030ba020b80078480340d0750141b100d180c0401c81c0d03140c10078080808907030040741c042803251600d0002c2004480c44bd103580c3c003c580314078072180452103d9440049003a0003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926739955 1250 926738705 926738713
    0x5041e0e0c0c190b0103121e030603021008060a05040c0e1f081b0306060a0c0c180f0b030c09041e03210b090c130f030b0105030f0615010503060424060f02010c1d03 72
    0x102c1e42c00d4000b0016103000f41d00000f2b69581d014401c41c01c01500c0707456500304a0800800500c2c0c4607000070130210b074901809004507107405082003003501910001c14014802000700c14103034003043c69900038107100b0100000152020010608101d203186039a4545a0f6805069180d5510301c0300380400c0d6444068103100700403a05200303c004c5000e5080e0344015140002c4400d41c0007081d005920180c5508140d8811454a030802208280d50300044c40000c101c1c003620501c540c2e9446041041000c00c1e00000c129a4500502d044420140d01200c605000703114400440451102400300c11308541c101400150040e1000000ca03c1441140001d800c0c4422018603803424262030711031000000d03036980e1040701c00010703200040c0580d11f02402800419200f4000821791490b120380b400038283c8004c40708906008001001c9195905d460300201d412600e401c84c0c0b124141d1000c02911100e84c03543c8170340e600041c140b51020305c6091040c0543c250218066a0301c1e181c01d820401010109462505070b107070705100b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926741205 1250 926739955 926739977
    0x131502030702090403171609080c03060f130f030206040b151008041b0612060e04050303010306020c0c15030a0b03010501120803090304091e0c0c0305041e0e0c0c190b010312 76
    0x10b007108846d40308015451550322007410710540a0402e12060300010f01079002041d05449640700042e40a41c0401024206c820b9070702c414030301c41000c065803280a0300c0300303082000c1c2201345500080d81e1030050307205e04681c0c0295520804002e582c0d68103040d11950150b100e60b0200e143c284034010b00f41c1c1050040c081100302d03081d1240c101500d20b00d03e60145010641c2e613036440311111854420400146003030680000e80d40340954500f91280310500000700101e074040b03900a0103507010840d40c03000700c001903d046000b1031952070404440d002221001909030800d00300605d40e0406000b468100d0300c2c414a044400c03421507880d03003580d8100610190540c4424000000c65003003500811070302c00003c1c28507040340152582600183e0305e0700000d00040c004021107040000307611a08075400c882250160000090300c1d01c104d0b00158845600070071821920300d05001000700ca0320010030313040a071300040f903008814501c8183c02600c64010050141c103004401080400d29500b01013001d0300e8103140101d1400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926742455 1250 926741205 926741237
    0x10503150a080109020a050901081e0f071d090c031009020d020d03081602030f0f0d020c2a1f180e0702010606030f1503080c03120c131502030702090403 67
    0x388503405810940c4d1244450019410800300e1600680000d0f94440c01c0396043c810010758890143c94500c6001d0b840340484580010144540000d010025082e1103800780c7ea001c42c00c01d0b244001641c0c40d0600d0100c000700f0a54000000c100a0390b14020700501a08083e40740600020461080c0036600b0040381118900141d8501c145600498842d80360b03a001030410030242891088030355200400e6510411090a01c141c4106c2030b039150324902c0513150703075403c01c10b140c54000c0e0003103550f2845c062041e100d10300e01518030b403000c66010b20075500042d029182d4601c01c2113018201e42080140800355040c040c2201072144002d100c1c18200c0f0300d030003550141d442507115a80d05044615400503596204d082c80056814004c000015085500a102003480075040822400d92031200400c88400060f00c61440d20041c03080e140c40c502030815644289c50b04c200700000c550b21401d41c2e041d80f071410203c04944400441c4000c0d410700403a90042d400c3c82015802e00410890240045c0e090100c45080401c1007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926743705 1250 926742455 926742469
    0xc17030721050f16210903121103160611040f0504180203060106030507031404020f10110d0c0c0f03031d040b0603090309150301050121020f070503041503050c070201050315 76
    0xc5404444824440c40403418074104a00c2d909120140c20340c045c0b040c051845521000100649800c82e0700b90b003450040d11170654520303650001c074500a0001042e40580c0440d66000524914003da00c24000d50b4001642460948268000d860514100060030310590401d41d001541c000032141241419840a80019140078026401000000c4c3c480c401c110070f55525000300c640d40d032506c0300da0851a05040c0c2c000344005c644620840d00502c3c815030900303900c52213103400c0f4059121340320a50b10301c401c1c200402426200c05440943e0b40e8044601c00060107511910786000701d07030305551004011000c1250144010118044032a803040c1c80b502c01c4885640d070400110b02811000c00215940c070041c0007841180c0c04401c00783c1c1064842400100705690b004402042041004102603041a40d4281440300034050081109850307000410101c00300300d0008010400d0380d4402e007081c440c6542c86007003201030341c0045071b41c2c0ba88803800b40002801940104050354000d840c0801c070b03034001c1c2d010308080790030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926744955 1250 926743705 926743717
    0x1508060709120215120703140709030201081e07020c04060e01060804140c100806041404111228050609030c15060112110405010e0609090103020d0203070f030c17030721050f 76
    0xc521703920801c1c4400e4070307050301c251411320078590350724080d514003203801420180c0580300103810310220bc00004c40c2d00c444002e901000c607084c0e204d540d55600340b00000030f46d2002c075aa1080e004074a4080082a84000800e050317040318a41e071b41b00c400030303501c1e95900c42800c8050400401c4c54469040000541e82d151410550289040d0342d820a081c5801c03070403c0103030354008034002a0503002505100106c1c11210760050322110565084081c40701c005041442d190704800400e14040101403022211140d00701c0058100b130042003110026156000500c0e224452200040407580c440086c14840c900010f2415034072440504081e0070b16000040700000b0f88403018082c009207400040c0a11496030800b8030403450403015591b0500f82419030000c1a07036005d041c000684100b02c2214040c045540402030380c805460459540c1c0b0803607a80349040c4943c2c0d03045015200101011107a108000d8000000740d480845d00b0a25820501ea1032208016002242040080400204009a007640c070301080007455 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926746205 1250 926744955 926744977
    0xf0501140f0c0a111f03020f0f0f19080106210608011d1b01090e0c0c0a0b06010201110c0604032a031d06030f010e130f061508060709120215 62
    0x10f08240c80303107001c040360103000514500c554100340341802c0c42d00305038071800f07005041c1d81030040e0b580442401c5800785004180d181031040301d001550b0211040141d001d001c062012200e02c10089252000aa40d402001d01501000510720184641f11400c0101d1892800010b0400002d00e29182c0300b0107420b60b044424054484501c0b180c4041c440d420030031006582c0b003024280424405100c000007070034140c841c401c0211524071440800c4d010f45080d4100c80513510b40d201107501d00700b65072411120002c821100705001d540382031046d4178400140f50444d1000464000903003400c0d5110313078082e2440c4540380241014602d03011035000c4254404d00140c28201c8c000d465030340c2d0445c902c0e111000d1003403034400803a010b40f41c188184020307a082c020301107064842d85981b03c8a0380e6030799100842c2c45102c0e00800340000098010440c1401503d52111400b08043e0b0712901c8800d44819600f41d03202e005452000004a001d0000c0101c1b0f00d4111061801e68802080c50050410320440b18170540c00c9407100c0300c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926747455 1250 926746205 926746213
    0x40506030c0d02090411120109020903030904360c0807120308040f050706020a2307060c06020d05042d030f0c11030631081c0b090a20040f0501140f0c 66
    0x1011f4030541400841c010304407000c05524182e403c00110b6142d0056000d4203002e5602c0307020310903090300395070601692000c215041500740000002040b041824007001920000c0312501c02040100c00454810700f5621401c500c03450848066404641d084002442a00c48009182003200052402d02401d0700401d9903500030141c520050521141030300d0070034054030010118100c44c1703181410115a41e4200c40441c00c113281203011900b04032010344602401044000d03d40b00400082204202455118605030a8000b01c505400f0400140c10480400050040780704801038454040c440c4e6400044140b103558980308070312040010070300d407110641d0640c0c1080866840390050409951081e000f6900c611800000b14905032620b00031413150380f8241c0078030741c010000304441c0030854100030a440c2e80902100a685001804030004045c0d0988403c000d484400b160030b0b00d4910310f801d5805580d240b02800340041d191034015a480d200e0b030f00743c500306008140115a820690030010340003031280f002c064 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926748705 1250 926747455 926747467
    0x130311030d0c051213080d030221060f0405220c1502030403031403340305010f14280303030504150e0d080c090301060801091403040506030c0d02090411 67
    0x241c00d281961240c0c40801100d200c2c014081000066240043e04802859560f944038403801c24120b8403c3d5001817850740701d44400f0928465041e8000d001010030011014070b400300380740f1120f042007070585d08694490819200111140780c60b510564000c0c0e0406d007180d0b000000c10034000003e018514058840081020081043c0ea648031600b89010b41d0510155180030b0456401524180501040d103a259201000150b1341c0c03a00d8a9801d41081c45010b0f01180440d012810142616008002180001d04000001500040b031031101030560b803030520a6003aa004900074015034000e412200005201000c01042c0340006402500c0c0196000f9500800e00c0d02d4a402c100c0c9140034551041c0d807181d840e000d0003030324035a0045580b0b10300598910303110758a525032001c4840207006140d001d0398103520307210000584c00c005520541c6c0c00c86c45040b000d13180d41c0c1c207480181c0e2a0b0103a8403542c1d03089503040000445041e1010010094250f841c0300050804081c00081800c5a200300c1c0c019200d00fa0001c2c407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926749955 1250 926748705 926748709
    0x61e040f080d1b030c0b0c0d0c030b060f030c120412030c140703031a06040620070608040b2a1c0515010e01020a060f0b0a0605040e040b090102130311 66
    0x40c40e400741c44400700501c2c803000c5965000b480010400d030321221800701c4601a0381014881d0450004240d04003000701e00e1410041149a50f82c0d100351070401f42c4924000d01c1c4110307503000340242d0b511050700400d0b80d4180101d032114403099600c002d019034200710040111514074404d1180541c0110f00412151001c220240d10107802c50f40c4501111061148c0c0c2030210f140c03001c03c0c100701e40c07001e84d0502d4086440c1034415007901e4161140191072b64481130100b00818050f601245580019101ea508c4013414400c054007181c60710b00074018480007807440c400040128130820007079a000180030241d18203c00300c1c001000c024040c6816420810a0001410f52220208044c05071038918040020065820030b0014006011030a03440ca6043c40105550303000346a00900030203a4050300102c040c0540d200c0895035400a01d03090300d40c144905006000819064420019242076401160180320152240e49034802d64250003000741841d503400300700c0c0c100000f03030842450004501c20032001c80c03e40c1c16642 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926751205 1250 926749955 926749979
    0x20a1b050d170c03011a190e010212070203070303080603070f0803070c09140a0b010216090b0a0b03070819090510050703241206060e0903090306010e0c07060b061e04 73
    0x341800442c40b40e04140007003140c014003268119044000c2c03031511540203040e02c1c61140101e00107800200c1031403082c9124280c1120aa55a40c0826400d465050a5820300e04003240141c1c0c0010790940e0182d402400042e01590070342c0e8004000804070784e0f442c0d0b6501d9621480341150b41207889990230100c1c50390108411880c0001c06045040000c0c01010116074111401c030800501100300d05440d00c912400b1039000707120140c410000d441d4100149522164140c025181041f940c44c00303110401c40000780030000c0800d490291005540310f05c01503d5071f904020f802e80d0400c46002e040c90361031038840b002800c10007880d03404281c840c03004500340c03500003005821944080280d20340c00c0e18011401c280350050349050f1080e2000b90000444d844e416080200c01480641c1102104040307140074007601000c004044c01c812107003101112031070382e05d541c058005580b06541641a401c01131041c200080e40c00c0c1c100d40c0240740080c0206c1d052442c3d0300560b06180b445d0341c0e0840800b810005090100182d085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926752455 1250 926751205 926751227
    0x1e0c04020307030605101d101d010306120b011d0603100504051603060c1416080d020910020312070f1b062c0708060114150c1b10020f0303010504020a1b050d 69
    0xd5140c8c0380c072134001e100642003508950325030400303a0324071082c210b5a80c000c0d0f00c0310001e491301011074102c02c156454505a407210030300699030001c200c0c5c2c0302698012014140c16200c0d54010700a011a102c01d0010240982000750086441e4080c00c03040291000703817015035400460241c0404034002d0741010001d00718902c81d1468080c0d1441c10001120420881e80140340d0707440d40000b03075030303030b40c20f4003442642c028003c0b140107680c002d0b2015401c969a6500101411540800d10007204094031407890035524254800c8001000c9051540b00381d80d0007035184a10180c00703000d03850214a080e91520600c86608215241002c165200124600110740401140010340103003801403046504103010490b401035211a920300c11003480441c42110071030344040d180c41010141c2240d401e180040400035820040039001c07406200c032198109103891000440102841e80c00c0007840c0395909040610003e940304045a000380003403502c1207009901400e41031050540141c02400c0401040e04005001b16020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926753705 1250 926752455 926752459
    0x50708040507230307150f09030b010b0c010219180b030910050417040b0a030b0f01120f1d030301060305070513140a1d010302031e0c04020307030605101d 68
    0x19020040020400146002600c401d40c2c1c8802d003400d1000b160304000c0c0404900d0742d81500482d00c00040301c1400d801c5024007001d05803600d086443c01420121282e52503440301500a1440500400034003440c070006000e4040d50b0000546800031740d109640309103501c3c1508400051a0b07030600b85144110b2400b1034041e01e02e0740ca43e0351440c20212a5140d940800318014042180e440300403c040001464a003e10042d0500c0c0454989036074a50701c031810b4010450b0400070a0074680c1a4616180c0500d000d881c6100507140c10840061084c6c90304014100155401c034100d80c3c90014100e007031f4601f42a0030460320031a0046580b5810620010306956000e4258020311406020790071812125a0300402510940501c0310180d42d000300c001551403100d54000400d000000c0c8007080800c0746448034906aa0098046508420500c1c0c3c1000d00c0340c0740b030881c00d6102d41150600c1c06c5946410b80056404c074a440c500030800e80e403a003001981e40000454034901007803140724440c02d50b01461511000850302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926754955 1250 926753705 926753717
    0xc030609020705070e09011e15051201020a1d011205150a14040c0908070e091c0302070302160b04050904020d0204020a08091504030818100203010603150b070c0e180d030207060507 79
    0x401055510b1704130368440c0150140d4440c915900e109d0a5910328800410700107244404006405007564003e5000344003600018005802130507088585410501407407806a4074000a42c07a4080700b50000e05008d00413009524500101114a5403080c1c049000350450701c0c0c1101c03003000c0f200200000c0b40e42c00780c803401c14046501020040c0100128640c000c4072111000c2c46065582ca44034642004550322000c40881205200e59680503815030180c00894803940032212a80005500700fa88004284104040800100010700c07050420104142d040b40c4041c0c050641c110305a070000c0c0c01d03038010f5800d00b0300045001040280c2807008004070820102110211800b600302070320020038002c1d0060110b4140301500c00d0f60621408100000c408400c1c0d2440c1c01c64495854a00041c06000f00354001c102305a02c1c1580480c00306071003401c03194400e07406250311100341d01c0e00d2842e1035103c000901102d0b0051a5024080c803801082c07000510029141d5401a69400d00e07140c08001c23104054260810066 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926756205 1250 926754955 926754971
    0x2130509061c03020a020d0c140a15031104080a0b0f0c0306180415050106091a090307030210110105010306090b070e1318170a0201050f04150c030609020705070e0901 73
    0x448102d854036124a8401c000c40b15a1181000da1a001d10401c00039000490004070009006d0080c3c16102036034444402041403400c988104403064240b800791000210716501407003141030096121994101450034194105a03407111541d01708500c206080c3c811382e480c0c5040007444500c0300ca030796501106c003945082c11410f116000c603647c1d19035000002c800c54608008102031204501c01d405603c000c1d040148903640e1a00b4000307045040c13510402c0c001e03901708001003032105900e134282c84441340c0140003030402e20320356020815603e04882c085000d1100c1e4490b101107181c000e00a90340138601030080803d070b40c8003038035002101c40ba00820030020459000b0600c5420340d201d840100707515161034400f0034003084014042c0c0800306012001000864040f849025892070300000e080c01c403023190020802503a070a28076182aaa048030014843c21036000701c40206240c541c0003c01c5662140340c00030718551120480c1080340e0083c403064486500021042000000e035120043e8030405041c002d0001c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926757455 1250 926756205 926756209
    0xf0609150e13060e0d021b010504050312031f08300a1808030c0a020307050103051614040b1611040b0a03020d060e15090705090105011725030213050906 67
    0x40c5020b00444030b5840501004418007160b500001e0031070952006480060384107100c003a5460741d10880c10105c104200c1848441503001e401602d00b00d0343c0240262203111000f0b105030706186d0004100070350f040c4512007080c000a0000141038040c101000080c0b14817011001109003a00c203041d40c180111114076030b80307241c4003c020107484d550800340c00c001c07840240360b0b4624540c2040c00d4100490510000c14514480b0500264541e1000d0094003902e0329607844000440c15a8401c031510802c40ca01207a0640b2203074401c0e0402c03004441030b01d41e41d5043c607498100304000ea42c0541200100311810140120070f11843c5401405040c3c81150308001d880c0303800b40800d01c0301d0b0080c80f010740b00384250704100052010035000694202c43d020242c420780d8090742c901c2c0e2030186003525140190b1142c548089414101000c82c1030503100140c4400641c00701d131540c440c0d0b0b402801403e00402c0804452560040d07444441920074061068502503260a110441f5180703ca045034400c42c4501011030902c8155 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926758705 1250 926757455 926757479
    0x120a080903030f0c071409010f062f21072f0a0b0307020d020115051c06140108160302031c02011b030203090f011109370315020c0706110a060f060915 66
    0x1d6000e420003828560740744bc007540c02e41107008201d007103007030001611819051000c1034148000d2842664030343c180014501d40c21407400380034001018114440c4002d0350404114003071034800b01d420011000040000c4001c150841d00030f0703025044220011062201c0a6014441d00068111920080180c0c110700c1c026521544210312540e4041c0f005001c0700030100c00381010304a00303035400000600c241e640100328030781c0880c0c0911540c06940240c0c02e62111004101d8801070841c0c1c0c0003401000e0b0b00069400c4013440800d190000030956507124a400c84988180888200d40c03c421380780142c0701d1038005a00c50810914050322034450340340c102c84141e0b2182d0402955440041500c861180d005059010075001c0e101e00302d0280150003401c080020303908030f07001e000143c030301c01c1c1c28a680b103804a031000400e90080e0040e0400d582c1004800b40081d51050082103064030800084441c01c8109071940070403550b49010356042180c950b10180074101709801514a240121a500d1142915000c0c5032018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926759955 1250 926758705 926758709
    0xe0a090f15020d05090303060a06021915141305101107200307090c031107020105030a1505130203040c0509070903060c030b1f0905120a080903030f0c071409010f 71
    0x4211002211500000c1965040e035114501190f0f0820040c14070110155998104071b40c2d0502c601d080201c003040f182d00c081000e640b4000070f081e170303440300064907a00d42c01e41000c200030803158150382d003091411307501c411900c0d54090a000c0c4090303a042011814107070705180d00c0c060301010040c1001c90000f2541c201d1021035020b03d4005404481a8602209284800701400e41d00e95140c40b5407032011491034501d50201c5a514026181044008044a9603c03082e00440402902190b801d01c000380345002c2c1504440480e24800d64992003846c1c071040041d250030b94110f80c0300d0f00079a010003003008100e00c032843c0ba8080c02e02160040030914004100801041c000d001c01001c4076103420402c2c012500903000316203943c8005094001d007140d60a6100d07880d62602c0b600a001605011000419082c07221146001c24003880240840c01d20039240d03008143d01160145e034051108210003040103441c14050014001d02c8c80c050004c442c9412801c6845101783d54a8030701c5001074000400c100d0f200e502c0c030801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926761205 1250 926759955 926759963
    0xf060b09061e0a051206090d02070f0b0a09030203060a020d0f0207350304080309010c090b04120f060204030c0e0703050613051e25181e1706010e0a090f 67
    0x410200c030b40c0e01059103482c80c2c0e4416a04a0200700348000c51a01c003244440c4119400c4d802c607403407091109400c90f07a0b14043d00c10b0b24a500c101c480c05020706003500c001001268103030b0070603401e055640e41c040392408108039080c051140d4085000b010b3300d0490b000b40c0396451001e58095003401c0300742e1211078445460050b0200d02041040320b10b41480741440c2d594014a080082403078480c80c1504016506070301c2243d00a03801c0d460102c0c40061a4011150341d42550540761045041605008107203014000c0342c00c00f81e6480c03c40076030314000202e40b03000800103188a0a000721043e442d0442c00c2201210140c4800306060400003080210b49421114100c0d800d0741110101f03043d1100c5c03502040c400c0c1941e445c1074185280e201004210408212010290700e44190201e08052130b003902150088000c280c4401c0c2e92000a000b0001420361044a0030026a030701e9040c036030740d6500d06007104c4c204141c180142898204600422074114000a15640315580c0e500c1446502d00580c0d40e102d45071700744c0e50010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926762455 1250 926761205 926761249
    0x70f06110a081911060f011a130f050901120f0f1112070e1308070b092401080607031802040e010213030302010608061803030703050a090f0f060b0906 66
    0xca29000208403509100360030000c015594540005041c0030148401c0c000004256108290301d906030001410a1246000c00000030150342010403d0210140ca2030801c945100180500c00c032032818000d414009094030303070364401140d2a10044c0619031071b0590040d03081821400081011074800078081412a5000100704080b49c25450030320340c0036182d4011560412558001441c514000042c04000da81c081c802a80c2551b0350200c2e040d0074103640441c000d000c3e00090114100041001c8401e46d00102c6050a5444101c503444040f08481850740020310b40d000f0700c6004100e0400c01b0700000f500711101e0310741445141c450041d4107056111115000b8021942d61900b02d452441c00e5055850180c1e114107500039032a50307820028040c0c035003405409824040c140100b0107078070340701450303010303c402c0d60014504640e1041015402000003c20080840e900d8811090007d8174071420010018440c201c05c90703a501e2941440c1e01141d06040c840d901800f0180d003800815030b80d01d4410411015a1a441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926763705 1250 926762455 926762477
    0x304061113170f010b0d1103190b0a0c0e0a121a09030903010b0603070c030f0c020306010e22030203042102090c0703080a09020a0501111e1c02070f06 66
    0x14514600c5030200401d42010109404100a002444560301c000d101400720783d02008001082d5080340c0d0b04d01602075014192600c0880086c910030784400a81f0130007001d035080820820101c2021481414049940f5404441008511401403040c10032041092400c0c600710b19190001c5135650201d40521202142111900d1080124680114034503a2442052200f1390410b15592507494201900041c829403c03c140c0b0b18140c140310044d607100700310b540d60ba0103c140054500faa06105c501040900f00000c51040f4005030310708108150081c00c80b202078038403c1c036000703401407144100c0c0e5001c2d04500007104458000320b6400000e540c1520951000e896060038024a113482d0050b06600c025040080c840400c01440008805818210302945804105540c1c5109074002c950f102e400003544100e26801c140300c2944692080c003102000c0f9000c0320b4400c8000640700740c1700000000d901c0850fa10442000240590300c1100c421407840500003080c0d401d0401d000c1003008070070750280b2410800c0480f41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926764955 1250 926763705 926763731
    0xd020f01060b09092502031804050c030a0b0a03140c150a0914040603060e0f06060108091002030a0209030312040c0501030606080c1305090f040b0105103014010e0106020d05030406 79
    0x11066811444001500c5c00541c3c1041c0039440c2d4000c851a4201c034002c0301d1030000f40c5d0505014603842610480c51607407842c0d0300c00d00500c0091640c0820150082d0b10303a40003100045880e0f8000040601e03007070040000710703c41c0040284914a00050101c442070600150420907081501c0d00c040d03a151480b01e00504a200c80414010301550380040e15040c28100c09078800440415102c1c00e0340e068500780c60380c56840700010741c2c0b050307000e480740c01c001d51244440764245150790340555004001c042025107019140b0f00043e1558111100040c00080700105200030402c850159100405083c241845094502030010b01030250040c03030704508090004000d8205e09043e24601d01800700140b0072101814002081d5000502c02c03281200c50101e03071030021409207480000d413201c40d0381d0341e0f41d40804e0500002d02003104000312039540000078136040600c810754440340034401c500505a0300c4138143e98940030707140030041410380c0084159045450011000d80e40001203903803103a0411004075a19250b049 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926766205 1250 926764955 926764981
    0x6080a0b0604050d230304090213080d021905010207150203250903110607050a0c0f05031f18050105090a020f04050103050d0c0812070809010b15030114061603020d020f01060b0909 79
    0xb85d00c00160200040c049451009a80a4040d0300c00d910901034240303840e00c00b956a140000403040025900c04144414a054032003a1855002e1003040090704021ba0742d0350f80d0316031111181280c44119000b1040081c0703e00d840d49840c1282c3c0e03900400da402103804a03c05030405405010144c04000a07813602403131703074460004407000158000c00700d58000c556130800e40180011405110541d5031080c42c00161440e002030710107a410003009440429016200810f0001c0510310004000300d1a01300c06180411070a2050030710460844c00039010074000c0384100240c0904407042188140d160000500116900044020410040d800c2c2003402083ca402c21842500a4490301d10912032002c041051080d0b00c02251401030703510714000d020140c8070340b08000326820117022222010100384010041031403074114035000c011010302210303e00102040407218100114000343e015a01c071040110245034104002c0c0800708440f0002c1041d50b0802e04d10007007505c00c00706503503c55104e541c0400d1400c02011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926767455 1250 926766205 926766263
    0x5092e060f08010515090a03080c01020306010f050c07090c1e030e100510051012150f170c0103021e0304060c1107080a0609030e1c03120c080a0e0a020303030106080a0b0604050d 78
    0x249c00151034000816080d4003130341c011079086000a2040004030480d0703000307805468900303c0140c0500095428a0001710041c50203405030401c00403488001a410303c85408195800d0305640c0e404907a282900b400540b402220400d4202c441b440e07c030403c0000502c003d010003e9803012960b03680b4280c83c1050031160352038074806009100f45811a014020030307208244808642405c0201c040701c070f507202d080e940791400b41c180000441d04100c50150056110f68020440fa207040000c00da8240c00b20f132601c881580040b00c1c1143d50683d983c1c46551003940000ca00d9801e102d018000f800e9050a0a00807900c6e02d100000c01010140c86402104c105030151813086035140000d0501403052441040300d074149401081c059010490540c0d0340d81303000340da6001d01090360310f0903120488192907410380d0000811000c074042c03081c0d01545000d540141e8080c0000c40c000d01055079403510500b80303803500104981c60b401c0760740d01c00c64042004020603141c621596110a4100700302072880e514a4202c0b2694094117 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926768705 1250 926767455 926767463
    0x20c06030907210c15020616020f010e0c1302070c03030c080424080f0702070e19020a0f02070906210c0f1e0e1005092e060f08010515090a03 62
    0x58403546410b810b0500a040d6041d0040c4490140c1c2666161041c000c00c1490201c003005030800303400124000b00b042400345500688d841115406400340d009607084442180c8400c006402180d01062289030443d4144240d4007a6001107240c00490b130b880740c80b00c0b134052100809100c1004404010b01c07181c002130f100103002000758022405074010300340070b140921001a90104007030401040300c420f00c6406040c45580640c004044043c01c0180c11404400024252200e0803001d034541c010405150020f410f1a41340303501c403892041c94a420107170a000c025000b5580141c540002007100010203040f200b8265003c06500010f80381300d04000c01c030458540c001c0e024039020140001007141c0003003003807000300c03946000c3e40c2c80c025110b0303690350003400701178544200203903e01e0030500c22482c11a02664201b14882840c0d28450f160b110180300c0982c000400c1c1c20410f010724002c1001d10381140d41c55813010381900e8140a0766061070001003c902280251100003103004c0f4522200b5152442c00d88065500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926769955 1250 926768705 926768729
    0xd02210a180f180f0e031602031006030605100b340b0f011e15110a06060e04060e0f0d1d030a0c08010b01090e06130b130f060f0303020c06030907 64
    0x301c0100d45264280b00c14841c0c2c0701c03403030803013400001d0311a44034641040c00d80c60050752401c418908084081e00410b20160303458000d190040c1c407008010f2240c04011841610007248624150490302404800703584030b001c2c4d420080001d80113400020255491980208441002c0900c2d10784003031041a802c1c041c010001c08a05040c8003200c2c4820440c941210b090b41e454904e0081d56129080340c482442c8107141054084030b0060b100c0e01d02a501200c00113038440d04072003904660742c0710042640c2d01c0b944607000c69044203041c40184000d1740212815014130074014070000301d503d5011a27076001f0034109a4200100c2e4500c1c00c103035440b040140b010740302d0300400311002c120160500e04c440c000c04e0b114505c529031803d0740602555014500a904450105000c5c8006582c2da034240070040840e00c1c140b02c44c0650710104201141c0d20b84103010f0100c5070000c0001103a41000ca1181300301e400b642c0014204040308101000007a80c0015a07142c880030650f10952a915030000c46031a005440d0403c400d0300340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926771205 1250 926769955 926769959
    0x100203191b1103010b0301090b060d0f02191a0301210611280305040f0b0603010b0d2405100302011101020906041205071406120403090312020d02210a180f 68
    0x850403181c01c0302c0d610120001c2200b450b02d04105402c0303424042c4002c00c038100d9003000036054605240a9080325018011580d4018234070b0307000071303040c0309041301d40040c1c40383c65807060042c403000c84048051b4001c3c06640e103240d07506084007941070b170b0001c022038000c102c808290002041550b40105120117140104280c4803106000c128022003e95080700241c1040d9002d50040340d48030b802214010340e040603000f10021402c0e250f451100760014100c540564888000e83e4203911424080c3c501c03e80501009465100c0300b4028210401c00c00300418103d0b0708080a00104409403814502180d81c2428260707600c1c0694081940a40a01d0318032a50101e0082030000d41507014403080951644280c05607207a0360b841d4404500620075031520300f44c01100a203d2401210710303044615801c14040e0078145000c650300d0340d0b203000ca00c1072502100300580090b01c1c0d190034140c04001c00f4900c0c10f80c082403101411007101080d0ae6a001343c0c01c103001085070074003001c7d0140d500c54214001801c2c000189118881d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926772455 1250 926771205 926771213
    0x5060f070f061d190c06080c1201090204030b250c020a03060e06100b030106020a02010c1e11040606020312040308060a0e0c031b1806090a0b040305060114100203191b 73
    0x400242100052800303141445803031401409441013a081c0d000d034000e0803003400d04070308442060008100440300441046207850b1201a500c0f01c030300810304502c002d640c543c11071821171604003010b042610048049038118074002e080d4100882c8a050030f10307046540c40050700024600c8445540060305451401801c80352000b4042006441141040402c64480396200f04c081c1541c8024403480c80140c001660110040d07109040140681c1d0041500406d110040c244140d04894402411a03201d0050011444981480d0282000070a9540051802d0000f501d1300780c010180e004000408001d1080c00007002d0303548603081740e8080c0100c925401320a02d8001640c0030070b94001d40b940d812040c10700d03c1102d0315104034400c036509850b10142000440d818041030051681100d400168030240110f0045025031509002d4001940500d000f81400e514082e00d40788454640300441e0f0090301351003840420140c0004c12550826003c0c45101004201160200c03040140c012001c694600c2d01b80600c0144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926773705 1250 926772455 926772491
    0xc030703060b1b01112b0212160e0f0a0306050603070b042c040f0b04030e030f03220509040803040201030f0e010c0207051c06150305010c1110020405060f070f06 71
    0x44514070340200074210485e03480e8103981c09018002e0b0b90172109901c41c0c1c40c641007054040101c501d01c0440c0035003040c00302800e0005001e000c03118803540001c261864a4a942d0001c0181360a8005454540d100c01700c1c140403c56681c0365010140c5203035200d40104010751010441e50000303005e8100501d07145c41c5c440380b4a600a020240d01c403c1039000009040c6c0c1c40c80c40c0040d80031700981e40600048002180d0344e031030b40c455820082c8240c00b440b8406038030308140d40b4144104180000210042d540c0d031440d8268101b2180c0041d030382050000300c240c10900c21074031040112074000b078001864503225038441c0b0048000e00515010081440d04046007440152015000300b10000786580a441c0c41e60385900500000b101d00c0c8280a100223070280350714012410340d92090740c02110300e4015035002c80d04c07503c0e85400c0d280325000e00300024010a0800071055003e0140c4840000644400e501d040e2409001540034050300c04407032a0f000c4009014410004103884160b081c9038095000c4c042c101e000c80c0100c8507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926774955 1250 926773705 926773747
    0x5041e03021e0d08060103050a0b150d11040b090d060932060702030307030e0c030610080f070311040c020c122404120809100f150602150c030703060b 66
    0x2c1450044203400b11050007040b00403048007180d8500d451555400011005010b01500c0d00b1b400b5039a50f03c0816507a1100c0c01c00000c42070f40000110354601e00041da80303007200c00d003040030b241300762013803106000a948000c11102c00010884042c0524503042c10700000819940a0041c150340040d0030788948280001e00c14114005014242022590003602c4a42c690b0b00c102c0750000144c0042000842e000d00a038030054900c80d006045034107000039000801c0c900340d810385100f01815003154081048100400070920011031a1014004040c03850341c50f5410803c42d518118407450b1036000070304283e0700c00c01401c4800680100a1440b4240d05038169446426031014159080070fa4880c181d0100340b01d00905005c0d90340403101c1101c07090804411909000c1c0070b41a140c1c0c80c01180b50740182104240a21103221450000009416100d02903001e204a047c0d4881f1043d17400c08280382c0410020142c089501044598002d03940c0c5d514020300b10001e24507138200400031178000c0380c031003017200c1001742c0c00b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926776205 1250 926774955 926774983
    0x80402040c020a050a1709040204030809031e030901030c050c030d06050310181e150b1e030d12061205060115090305070b180d0b0618150405041e0302 66
    0x48401c007250200d8480141c041c0c00340259000d0029540001c4080c58500401d8840b24200c1c0e0031b04420000140030b030380c010b5200b40c42e0604085072a8079546814000da03520500550390701804089c2250006850740104c0c4e402d281419030710540040810b004000311b544d129451700540c0c0e030711024414460001c00a5001e014000d21807810300390640035003441680f0851241000c161500310712030b52015284101140700101c0c241c0041200000038100071110720b003070404200003181455684050042c03204c038050032499040425020160b0b191000300b294a80b8050910f00007281c81401c0403000058400c907802044880b16035400c000074440007042c46070503100c0f00198401b0441c6000e900321444807003404050001e401c604810000340034448004d004001481c0a00c100d20070102c4c000912580760b038541a61486418010098103103000480545000d0840c10b16601b1400c082c1c8441038200b9103001010701a039035650100702030000303241c03451440000c40400850b00c02c00d68035009450b9000340402e98 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926777455 1250 926776205 926776211
    0x4050403020f060a27020411070b0117030f0f0d0e030d06030302011103011a0703030609050f0609070c0b070c081303030203040501021908071205090a0e011e120b060a0e0708040204 79
    0x95080303601030003401c80f008a503142c0900c40b002191a501040c192500c0120303406035841200309001c003d994049c1070304900901d002e410a6150240b00c000f140300040b10000306400030055040c1c451040004d4941549a14074065180c950161001d0300070300c1c400514004900c03000c26410f0500c0001c0c1c00c45400c2e00c2c4641e00074031140001400d00141c9000070b02a5882c0f1100380d154a20207828060f0140c18401d020340340200382c0c10340e0b80324aa01150415511590366505440410100e401c00f4100a60004128907100c1d4149940e0385030102601406000c04040044441c915402c2c000c40340c0039600c90400307091610180f20b540b80390195895001748581c9000d0700a24018400c50080d4080d2210416000008030b45400b5496480082c00440d021041c1c05120081c0412013007501d076a182c5601401500b0082c40c07542d410300a06044d41c506c42c61070140100b6000c00300744032170f600c100161080c4540c001c60386181500d6500000f4a03401040d0020030201402c4810400d8182d4050300490103a8000d039020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926778705 1250 926777455 926777461
    0x3010e100c09030213240609090c05030f0613020408120d200f03060112020c07030b01092a020a080a030606080105060703020613020102100f06030c050402041208090f04050403020f06 80
    0x707440d1030140d844040c0d40302c01750018050098205030800e00c1c00300e02000d294207840e0008514441c0c40b42498011200054980c101401060300610840296000c9810700604610f040c10350000f844a0041c419405841010100c094100307481d0162006440000261205c0c060b03140c181c88404e40106c2020039044d41007410000d8126601104c100c0030f0403018001525084001c1119400c5601c0584003d0420207000303034104500b245031000e81114500c08028200013440c42c18811000507042e007143c2074640c5080200c0200c045062405841103c0181c0c10743c008881d0346a090f0f0410006840c047d1034036100041030112294587e010030b042d101c1c1a22000c6250f40c89000740200d40c0202c00c002405640b00c03a01148101610401040032103205204440c2c841f1040c2c08128291411180c60302d201c1c2e83c4400050080060704840300c0b0107008103840c11410145081c0001680d4285204003401c81d070000a50341455031281c03402e84100c60b2014009000e581031905d0003c0d5240c44903094000240561307008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926779955 1250 926778705 926778707
    0x503151b0705030d0209010e090103150b01050307020d0e06090a0e040b130b180f0106170601290a03090506130b130b1602030d050a05220f0803130203010e100c 70
    0x989204542001c0114105138550015400070745c05541b009041c4081d0f0000c83c41aa41c42c0d075007080c007a52090f500d120000d900c40512805481c40b00b000c20303050100500402c40d0b810750014200d000605149030003400701c18803401090040c45040d40c0350350880e403030341e80110f0b00c402c480b030405002d203118080003515a0340e10700744035a0940440ca002402000c8183c0442c4820503035071141c0b040d21480c01d054840303406000b0102c0b42110039940c0804844050000d4440c5114018807042d03004190b1000c4034180104100c000441c110310a000c4200400008940e00300414806c0d031040340704903030080855031242080b942c4202c1d030b444a0328044a100c00180300207940c95001260080030180c1c0302a0003a025112240e5080002c941014104214030003840303104d9902140f80030301801407a0130b0720f0010f55401c103c4542015a1851900241c0d40d819140003003000580031142004460340040d002c43c3c030f90b1a62080c84203404502c00f0f021390700d036007080007864841c140412100110109460100401c0d021044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926781205 1250 926779955 926779957
    0x6340303023c0a031803091406090307060318080d150504021c050c1201031101090501111902060c030c0d0809070f0909020402190e0901090615180503151b 68
    0x1000d040c490b0085400049412407078015040d03030500c1341004034035502c5480781071000c1e1018500c00e500141404204000440b01403038004900c410940d011450459440c004c01c0d0755591522a610400d41e55030188480004024401c581003a07004021544d5000c074480c48002a1090000c800f00380d0281d000c00003480d14107442180d001d5200c422501e00c08091015005000b031400a0140b03207614410084d6259038407001c02c16070b0281d8454040d800c901d000120005008840e0340d00208d050040c070342c1003911702d03c00000c2c040f126120702101c440114141032011507014083c024072882d80d48804580c8400d10304c00070460707078010b4003640d6844e0b903035550b01c0580c0d990760345040c8100307a14001c0d084800d0100320181c1e004481c8160018001619011410000001c0107000e03080340c000240441c1c111783c450f403801c13140f1070340101150b440030f0011038240850810203202d0f02401d0424405c2d4205900c1701c500003110700d01d000384401419651115480140000300c1d04003220700034002d540c103042c801c06291683c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926782455 1250 926781205 926781277
    0x9050103050c09090c0607150501060e0a030f11090708070e03010b011223040c030b071d0d171303020a0b131e08010516030c020604020634030302 64
    0x10042901c1644035090000f2040c0240485030103000341040307100c0f140c861400621509109a128556000c0704420310300440d1010b0b000303041008021f280c6800255641c1c0c2181d002d994001072000d105080c4c0d86040c4284102c00d0003020f4002074401c0c10800d00c15001840b80c0c1c803955103912010846000303042050b0880b20801e4285020807a035524818035941581d10568941c1c9110740c048070f025152204154000504503000c984c0c1812585051040010a81c40701d03801c880542449418101c0c204c11404419090545d0039003c0c25014a251050000000ca40035a500e40424510750b40c00c2d0400e00050003103001d01040c1e004102440000030300c4800801103404040500c5c0d079030118241880c40f030b40c6203c0304404031383c0c5030064450800700301da000a11541c3e0051540304001c950340c0400c0a00501038807802e981308415900000100030241c1c442d41c1c1141c20710760400407100e04402c1c01da544000c00c050040c6903000c0203461444600200758040e40100f0100101c480c14140580c10031000140d03400c00c1c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926783705 1250 926782455 926782463
    0x604060b2404180f06090204081203090a030c0f0605090606030d02120a030b13053408060103020a0c061b080907060c0f060f02130e0109180b150a060f030609050103 72
    0x1c00081200750100f03505410b0381c03091000082550f401d552001e2094680582080760f540c1c1d400a02001040010840c07640b01250400170305007145001c0449a0b1a82d607808805030502c98201411001c0016405a10600036449842000745082c0002050758651040700c0c00c9019104c0e2303e40400030f441c0009010f4409040700301aa52a003417101c2d80880142130803d00051b00140c44820f001180c1e030117401a540305032410300c0886160301883c50440341004142c108413544411000c40744000c603a0001805030b22010030f08016079a4003068504442b181101038015020f18039003c03c3e07100c5200080c40f082d000e401b01c0e903101ca008d51907064032142c070b03401c16100d8440490b20302241b81c400140440c0c2e01e240b0a03405a10000b641800d042c1c480c0042e40e00460803980c610f50551800d01081032015000b07405002d42030760030071286070002c6c1c140c0505080707000c0c050a21940c0d5400034071001010708401040203c01350041841e19501d69000d03201081c0d00c90380d070020a040c64008580d40e0224401c0d03504803908 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926784955 1250 926783705 926783707
    0xf050a0605030111090d0c17060603010501050a0b0d0b1f050c120301050d0b0408040b0c010e120a0207050409141c0e0103110403141e030703030b061206060a110604060b24 75
    0x2180c1086601030000c1d0081700c0e203407401a800100c8100d400c44205103c072024004d000b150ae4010700305800c4a0b0160402072041180e0f901c2409804c4962090b0703404042d4a0500280c05901e24001803001c00220400207403078034000025001166120700a052409080700844811492004952203580024050290001004501440400c03103003a10307990424015943c0c07614194aa00301e60716a54410a84150242e440c0c030300b08141c60f94100071410288098a05050800a110030001d440f00ba0b40d01c14240314039119128401484100d5200102d009150300849500c20492030550910104e00350709403021071011210b000b50395000340543d4084111040500385820308555842c3c465100008840f02d062050007008500c0f010140c880c0998071071008001c40c2c44807190b140081c1600c0405640c01e005420038400342a8050b44041c01c03541040007141c00780d40701d001d010002c4480d1030590454102c603203d62428002800660b034005103d03483c0030740d00380301000745103044107003400d401d0400c00e011040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926786205 1250 926784955 926784967
    0x1805060c03070e042a0804050619060b0301090518011a1e0301060b1902070b0d180b0106090e06010507020d020108070c050f010f061a090d11040f050a0605030111 71
    0x440d40103640c002801e08107000f8012242d00450203d07000034484516004580a00b64903080c2c8018040c8415034451070200c0092a0503559039881e00006030012100c959900000640d640b65900001d01400305000600e48a6039946226006850305440d420760301c489865031034031154818005d901028149003a1002d0303000310a814825080b14101e000d146107481c02c1e900180aa50a000d01c50062480c18030098480d20741d0b03d03034200c0c0104255800000d5503c90030301013000341320346d4096500c00f120142e400107121088010301c0065550f00523004110b401d201002240340e07600000c1d8001500c82c801c60f6000c0079900d40006449178400e18002039404609066420b00540c8122281341e030200140c0f41c0030030a40c440340e85461414601c4210010b5a945071703420500c0041c0310744100e60090164054910041a520038407031450f108144415000316044a0058107000d00c000d40210007a401910030001c583e107003900300d00100400d80f0078035110f500b03008000405281c14081d102158800c101e00382c1c42c04d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926787455 1250 926786205 926786221
    0x1207061707050906030412020c041a0d06021c0f0605040623030f010906091101031e0e0114090d080105190512120a0512220b070903080406050409180506 67
    0x100074082420048100901105500c0d0a405940035902c58078a520700d1001c0030b180070341004048038560b03004500c1c100056001c0d21aa045550004005440d005075142450030054060310848140c44107045000d0301c580d0804016500a0030302c0d504482e0300b007180c03540b11000c000c04ea41c598461750012001c031150400641d0145180d10f0751401000b011076480f43d00d4008000e00f540c030084400c4d03450300c3e941c060781d50503c100d8450410360700c1c50900c1c04200344510750f81c540024400d9003080d890101e44e1419800900c001c2503000e0340c0186081240980c4a03d80b141c412980c0b1640303c0b0100000603104400010541405110070007041d111100400d001e030b003040d083c41101c00f02c0b40c90080962203070601200464201c0c0780105940c000d15580c1c1035640c0a852005802c042e4054000080381c8500c1d20f0042d58030002c4180c2d01e001e5540549010469254510104d071501e44d50340000d00041000180020150b800c04001c0040325440c20060250b14500c4c0e03900c904e043c0ca516405006900f040e40001e01403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926788705 1250 926787455 926787497
    0x11805010317220602030403061103040b01150c020315160908190c050411130e070c060b180a0c09050301020f04030f0203160902031e090a0308100506070c05120706 72
    0x81196521003210000070090640d01c0e8603d560b2101026820004051007401034078001c0b42246500b9181c41490360600381c1d40c10214410501c9240c04c100d441804140e1582d01c0f070340814449540007412520034880c0e00c2c000382071038542540c60100b040110602c006040b8043d0004108540d01000501281e42c484401030412b10075074103003110340702c201910108459549114031900d0a1000da031403a144c0301c0110001c1403502150300300b203689003c0007080009441e4071100c422291640620b010840034117410110750340780241240d02403004440010001c00440345e5111141c261070941d0751080c074030342d00c0e8103040c00c0348a81500649400000c00042c404110306a00f100c2080b440501101d02c4140519480d0718402503513000340c81580d40003c140400a107140003078103140e00d0040c8003400c02d0300704400301c1030b42d40744841c2004091151410001d0342107600d41c05000014075010700b0701d560722101e91514000154140c010540304c0c9441000c0e402c040140042c4000070398403d902e400700185030040c0b40c0e40c1c0c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926789955 1250 926788705 926788717
    0x92c0c060d02211f080a0f0804051012180201020307141e0d020c01031e090606090f0608070807082e1b0201060e090a02011b060212011805010317 64
    0x802502005840841d4141c40981400901e0302da12884003400c00c0800040004c0e11107601c20181a10f807071040c0038800012410703070b081076400f0414140105003490102610f0040b81d00c8154803542c4d46545485103908050b901481d880001d000300f140800c0f6031440f00306074985c2d45029005030b0040c48001d0004e03802c441d00221204410045030301d29642c03508900c0d18604051500381854001a80e009580c2d80c0401c6607102000007400c0c1440203004042c4894400c1d50520103040c0c455450320001c200740166680001d000c2c1018440c1030100c240041c0b0680064074a5214110041c8268080080d00e42004039556094400d0342c0082c2c0581c0c21500021f00000c50340c040505182a450b070300369a142d289a01c124400003840c0690358032030443c0008083d08440103584240078810301e0504010352703a0350210703175035902a0342401d1080d4032a00e400190054512400c0d001400244000f401d1107581a40b03004050407180314030010090511000c000c0340a8036002c0c070004010700302c030041c500704c103c1c0340788080d101f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926791205 1250 926789955 926789977
    0x9010c0f03020c0c12030a03051501210f0c0c0b09010501031e053c1c031a040e010203040212030a02030339030105010f02070b040308030c07060501092c0c06 69
    0x5400b500000004d841c040c5d42d5180d100752a4030010381003050075010b000ea070750f00440401166002c0c0120704006085403811170b80601141c1d01c821480040204540e01c41c5a044038021400c1218041400004e840a10000390555080340c41c040064000d00050281034140e07072f4000c550b80b0000021503800d07107061100030340032601b5008503801c03e24001c021400e103503000c02c0300c3e4443d42140001c841500800040c9420045102d4002002c140420a003c0020081402141c50001360090140e1480d21000745010819640305081042c032101d0840150042c41c05076000310344441600d914025003a07a6031141010041c0560030a00015040c405140d4048160b039906000d4421441011410048080070180b40b00b4850040813006000c1941c0c0700c0200c41704c0f5071071400141995401e010415140e400b880c4001000040c002000941d409444000d5424141e48827200f8485561985032006c041c041d0304001c446c99030340070307004072546031a40005040a201d81c9800703010450452800d02c0441d50000d60b01030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926792455 1250 926791205 926791213
    0x9030708011806020906070f0821070e01230f041a120f1305030a02100b0d021f2a022e0e120f240c0a0c0c03061404060509010c0f03020c 60
    0x8000300302e40020080040f4414480107582b00440001642042180c040c048020102d1380d0810954030f4002180c5052011300b403c205401c010301c8000c01c0e1002e524202441c400c00c5010074224144405e80001c0d00c01d4a030139864031400b007107810889095600a0f0404012841c000d080464003040c1032864903608500f651103256a01c0c020b0382c55a501c0c40d80100c1003400180d0020070840354000d858440c0801403070301154614140d1105800003802c49041d0182e0200001020007400c1c400390240d0000c40c174082910704241c42c2c02c0010300d01111001e42d0380d0400c0e4025000d1402d200fa400690310201e00c5100c50f10014000032000ba0507040b00c881220140f041e82187c8070008041c0703822020008001040802c0c0010490205844029a40880c001c0050103880c0d0480e03051240c10001c80c03041d034001c00f14a00e00491a0210350400390301d080000d50001e4a02403400820f4a004c0c5403c0d04e03020310540c00340d0020300aa45603181024222090007004100003207845c0200c00790385100740c001307007842c01d150402c035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926793705 1250 926792455 926792467
    0x4030312020412210905031b0d050d090905060109030309091a060f0a1b020315040f0204140916050901090207020109181b0c0b010b0708070b0106020309030708011806020906 76
    0x14502110a082d02582c9403402215100001c1106100909070b030241458811032452500000c60794910144005800303140403003201032300716140c245644d100185c00408462440c25104405400842d050007030200860400300002c0055003e802a007040382d6156a440300b8548c036041100e4000c1061841d40c0712100114420071100d541c0b000c0c0905920703c19020860356440240710042d02c0355010207180d0000028418025002d41c2d8085034001c0e40000f2461450071564881c40c20052922045070001d601c80d01d0000200c005100114015114441329421030701d9045148014200c04541d502c80c040c0c0c0000c1d107100500061841750003508505206061418a0702c0e21402805601001f04208004013a0341c0e0340b11941c440c0765030324207250350707251401c01c000c800070913884480003501e050007400f5800304001030340d800708000d401c210340340c564103c8414041561030b0100207480c1e0384002c03038880c46803049850114460a040c802e40700700b9102100740c52131401d0b05076201000b0307400412a03241e10240038400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926794955 1250 926793705 926793719
    0x2010b0406031119180e07120f1208060a0303030f0e0708010903080c1801051b0d0c03180b03061905090a2903060615041e0504060614040303120204 65
    0x38500142d80b1032006001203c2c401410702540701e940c5804559080740e020420461034081d0001450708001d071204c04140e41c41501c0140785024110340c40b0301c400600340c1e2003082c1484503101480104078469403d220b00280301150850b00070030203451080e80700d003000710b0400003740a503120801407040314002103480740c500500282002d405510001c66651581c0c000400c06500210786580315080f45921820100414440b06903814140d14003418098002112200140d0815001c0094030121048078103655030898010203840e2810707012008140741c041600d86080b001920f08090329000724000c2d003980c3d50751007000000303d00d0341180108040c0a03140412a904d0b158039183c131400c2c01440114044840001c4030009208060f0607111000d00b5140f044050b40d00814080c2c1c214204403016941744000400e81d018a100701d46c08040300b60111032a40b0a006c2c010490041200c0c4211030410103030380d0f520002d0f19518011031440f408040204028000a4094520710000b6802e1400041c00c103a204c5070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926796205 1250 926794955 926794961
    0x20f03040b1207080412050304030207050a09020d050603060c224205190e120c030f010212010312050d290a050604061d10110601060e0d030f02010b04 66
    0x520750501c0000d40034107100080c072090360003403110703d003e00062800c0d48a0035000b07011103801101f0450300001144c10f0510811552010f0240103007141d4031076549001c450000d40c4094006001a03040200246241c41c0114034141714000400c00c492512005100c001c9040e00783c1d0700240009803e42c1c0011861601c12284149a02c0410b01d03a49100ba03031079102e80d0780c0d00d42403400c50300a140c03036400c00300145517101058413045a03881c1d50701c4a454145080c281c41c2c0542d9500b0681d00724410402c10304c01860005100d40780f0301d0701501560309041d400c6148500b0703807050030004000d41d05401c00400026805021010b0b05810a1400d0750900c000c01b52460300b80c4480070074103180510151080710418030104a40381d000d42045075000c14043c50301002c190207000328030900c018004c424400600c2416035803520601c00000901411090200c1003024010a1129101554a2042c44000f013041030007840d840c6403092000f0160b09440e143c42ea07080303914018060b2804119520741101070a2515580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926797455 1250 926796205 926796209
    0xd0b04060909060527030a03050919032a050a020f030f031324020c0f0114070623240a090504050a260f070c0f060503160305160f020f0304 61
    0x10007240701d0800405005c0000090343c0c641000805c5040480c244400000840344c05820031f040114143c1c1d1056081400c154640b0320214440c0c82c91610a002c0607170000c0300c0000d101e442d1144581c4d48004074000e03000301c90000310062050b804450b640c80903150021003038040000041c201d40030490001280d80c00d68018902540074607041d0041803058444001454540306000721940b840480c80c0c07440295035454030010302d801050040d1012105921480c02c800030b0002c640b41082c0d40303030301524200000309210310030b00f003590300010410b840346842d05d01c0c0c450248818116a00e05240b5641044d0841130310b51805507070048202d0760020340c1448a00801d071186026034060249504c882c200004140f4000041a650703180c00e0340203c1181020300152481e40d03840c0348050b03454034014030341048504269080204c0d414010301c400900268403000840c0320303201a44245c5c1c0005030104094040d18000d89540303101c10241032043c14002d10484002c0001d0400d03104548042c3c101204031402c5600c01c5d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926798561 1106 926797455 926797463
    0x306070f0f08070e0604030305180103091203020f21180705150903012c07150503040f020d14010e0708150402090405030405031209030c150d0b04060909 67
    0x619104e503103c86015000c0c0c0c0d920341d01d9003000b03400e40d0464100540c00c0e5001c00303180b10300e552180c000c12a10903809083c00302a04804442034020790000d8038003c40607103080c0200c5000609117010040c0400d002c036181c0c5000c0c189403184000030700c511541072489620094080046031221282e107040006500381075130329005498000b0f070240070a501d080712480d950500c4c0702641c030300d81c41020724900d0176101107038002681e6416030304071108440009800b060381800020040b40700ca55500c07452510080401f82e0701c00c032540da42451400ca610601c040d50799110440200810300304040d0000e001e480005080380e00344105100c040100080009004032060000701c1d0401c1402c00c207680181074002d00303480c00300c45560000f038256000081c00c1c910034808d90701c1b251014102280001c2d2003480446446292201214080000e840ca50060a4000303a0f22074000032041c000d44543e808003231007 = true := by decide +kernel

theorem cover : BRFrame.Cov 926618705 926798561 := by
  have h0 := BRFrame.cov_init 926618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926618705 ≤ n) (h2 : n < 926798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
