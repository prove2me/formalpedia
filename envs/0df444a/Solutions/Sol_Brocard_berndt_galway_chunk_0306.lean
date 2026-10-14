-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:06:09.905272+00:00
-- url     : https://prove2.me/submissions/16521a9f-bd69-421f-9bc2-41912c5773df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 54856118 ≤ n < 55035974 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 54857368 1250 54856118 54856121
    0x2070b01030b06030a0b0a0c02061015031a040c0206010509070302090d0809040207081207081303020c090403020309060f0409050a060e0106080907030b040b07030614011d0a0503190b010605030601050706 89
    0x100f043c2e505000b802034480c00076001e100d1040c00f4030b00c0540006442248100301a10b00302010700400c1c0c1321007403290100311040030b050100d5205251803034040f49551643ea64218803070202e4074416401414000c6403d5401e90002c1c4a50403a282151310300c038940c54500d0254124862030306020340028600301c0080205140c0401440f041401601c014a896460f031580442508101009034441e0b02000c00d10028642c0100003c2c0c0041360800091502100b6031350103503594a06d070320007a002c0c0e90320100003424940244242c1d480c500016205694408014001511652180c02102085450103010544604030b81c80b5010550741100381c6c4502513400c2803001c3d2441d290040c03c28000740b01d03051001c40041e004040c4d03103004034424004d80e4104c2c184000b01030142c0755203070082d02c099504010740720044d0f03174060801c50f8400070000e10000340401c0a0042245036400c0c1d00943e8041c8100800c051414400044030741c0d0050140c04110080d0741c90318000c860703034401503035024002101841120007040c051f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 54858618 1250 54857368 54857371
    0x70308090a03080415080c03071709070b04060905150a051204060608152502070605090a170309030f060402030717160b0306040b0901030b0109020307050c16090605010302070b01030b 80
    0x3854010102da5030b03030701c160050340203800911060501c906410411900041042d4021880381806419407800b00c00080000c0c0c550700c900c81000d82840081118440c041c0084405012941130903540e50781c81d0303040600000c0840c820680501003814101201c0024001600e920304400e070382d407620f0044800e24054001502420540b6481e50714640050f0846041006084061308035410581d40d15010800780c400108581450b11103c1a0303141108825a012624000fa9481400c1c5251903e03524000b00306040b00329000400c07010007000032906a40c1c000005000b4030382c011403c80b51000011541c098607820291f86c02034040d40003035828402c170781d5480900d480c00c0220030f003158810060300c0e00c0c1c190700c4407895122a0b40701c8000001d010f5582010300851418900a49004005504d10f50700d40080703003014030690079942d0f40030020800c071a225074200c403145241d0908a80c0315a2402ca03054030804014401c000c0003034030f403020000c0c0e254020b000b41c55805400445840e8180e00e035441c0d082460705d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 54859868 1250 54858618 54858637
    0x302030a111201060602010f0b06120105060d0b030303040501060311030307050c1011010c080105040b040b0603060d020414040b010501170c0a1d03100f061202031023130b0711070308 80
    0xb010355005032800344200002000541c0c004240c25803504d21290071a12590001401407001f00030114891915010381c0341140c8c4143c0d04c9964641441c1140001040c00d10f06a0b5454000082403005122054128509490064440300c214913040010140d50b84560340740204241c10001c204000c40c40c0507030002505400d94145525600c8a4409180c21111403900c61404104a00010700c5a4101481500c81c0325206507000c0082c035001d000011070a000c020203c902c04c408883c994021034031160818103600d03030600d000114900705171a000c0c107601c03424001c1e1800a0207170300051808198245c100f038001d100d4a48920300d02010000c003200c1c8c03000c45440201d4012640003510070b0701d85040281c0f517041d8140d00b800240e50048090020207841096000980b0a40c1400404015a03030100f808405203147c0313080080c00081c0c500d041c19040400c0408501210004801c0040c062401510105664440e4640c00c400f039072240d0017501c5400070945e001c461540804001c0c00002c59001c0100114030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 54861118 1250 54859868 54859879
    0x1215010909060b0c06090d0507060b0a0f08030301080d020105040f021c14071802090906060309150705071a010e06041104050901030602070b070e0607020607060b04090501020c12040302030a11 84
    0x1900c4054070415200c1c80e43c041c1e0090360002070081803144040c820540c200d50100040d01241040410041250003a0940908a55036038011118507039105100c4000514008096145040d0b50310081916a0402d1007408800d019100d020790050384188035141c03080740d1001c0c09503220440707034003030125001614600b48003c0c0c0070900100007081c3c041d2682c00008489000801c61641800c00580d03d440e40980c40079216030041c4002400c0d5607501c03114070352000094489940b0303036403034094640c6400104405240c0032056041444503203036100d801020581c0c090048413165802600d15590750314024814080420011008107615241640104040c0391030282514142900e441c001a481e40081e842150055030000300e01c0b0070842400c400302e0340103119051901c10001c11001040b890320034004c00901c909000100c480400c0b00701d50169010400151080040b00302a20700340307000b035002c0240c03a8401d2060142c9650085600380486066aa0140c00380c03e500d24666030384481d00c00c03400c80c05035119 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 54862368 1250 54861118 54861137
    0xd060801050f010605120103031d04050a0b010906020f1902030703080d0b1509010f0305060613120b091614010302040b12010f120215031005220b010504060c030e010e0a0305030306030f03121501 85
    0x143d0b40cbe40607d41c040c1c071000000103201c42a5000251401049621003c00d54024803048009101c0c00300b40c408a0011042407410700407200d200207402c0c200c5a8100401c0d603280461010001302050f40016162103054840301c80010f0701c6d07481410350303000309600540003d03c0f4101d09060310b40329411007904100c02818141c10508181c400c80d200710050f801c002c1064002c0c3c18100103001988100070303001a504d2000c1e000c4410707050900030001145000b0041c0d0041c01c890854016482079040707900400d064105642c45501c1d40d848881001da00317204038041c0903a004004110010840c066200305035000304005000781c00344850342981d81004040900c29000054002800d45800d00000e00c05900c0307081c6007020905042510007180c15088640b41040001d01c402e000207500526003041c0740d500b50610031404180b5400498008650b50000c680165100c50004100040040550302610003101503690401031020416900d02403003c10411010504000c1025440d00840012600c8010715080c0d250 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 54863618 1250 54862368 54862427
    0x90b04150b0a030510050c04030215090d060e0a02030f0601050f040b0406030c0303020f0f160b07060f0c0509031c140c070302030a0f120f05030a020f0d060801050f01060512010303 79
    0xc0c6090790050704e1070f8001c0e6660050000c2c543c41941d0740107078456a200d050a086070080342c05001e141c01c5c4840c0c01c0d10f00062160803580c6103580c006026078402001d00541410b0740300e0540301c05040d98101d0080c402e0f80c407909100e03400032855178142e0300060078099201e00d0300c200b000041d0091445054100d41e98a90100104254110f280040d500030340050000540840042e03243c5a800000c042468120201c0c50514608c2d2440d48400c4400a112481d01c640041c1000e1004010349003c02135030398506591010b000e50400041d040100c021003c3e61101300440302c0011018413a42521400030342d83e61b290f000c4c02ca401034041c2442c01001c100300c0e860251603901081c5000b00c1400705568010703400c5841820442c40142c9990761100d540b809081190740107034090300318000034000c400d1168020415140d01850707a41502d07507501202c58248481692940e5490080106a4191403540b090000104826000d00100c90081c6003a10b012081a031a540301212220404005840f0000c07420010540c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 54864868 1250 54863618 54863629
    0x1206010608040b0a0204030209060103050405190507081006080c1002070f0e0613090201080c030a09080403080318160b031314010c0206160c120c020307090506040f090b04150b 77
    0x203000c0507100c1c0e1045080c5070030150100c000040896513000c2c0104000d100507150180e10b04d400680c2800c0100c0c01c1d8480c0d107800c0b0f082000c0d0340c00c21b1080c411042028805d100000800c501100c21610503030313041c0b0f03c00040c042c060343d0050180d4030b0035900c24041024542801c030b5000720b005215106554101d44c4982e0310302c50044859101c1d03100341c1c00503401d0011038038007012031843c600c5070740d201040040781c0c3d54006413000350020001400e000003c40014842c02c000d0f0003844d1680d80c403007102603444ac0c49190814550b001a03a41d20b04441442030008405d1030300190b020743c04490f480003061802d20700000845c15600081c000c16402c1c806188086c0014240d101d0b40d040c0060f641c00229421202c160024a0410300410021b10404d40b600101001c42e00140e200f070744103400034404681140310b10b00a4400609101c4003e4151213452000036007040c99510060096504840501c083c0c0e075003240390070584804040181c040c041c0b40011800140740c40030b0001030b2034840800841c40f111858000340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 54866118 1250 54864868 54864871
    0x3191101140a21050402010c0609020604080f15010504060e010b03040303182003010203060109030f0501020906032a030c0406050313060c0c03080f0411060a0e06030403030605090f07021207021206 86
    0x401141c0091101e401e980985020104100f02c840e008120798a0113400003040c0511a030700c06080c89a942d070340b4100b1354598504a4014152a0301207c82000c0c000e1112640c4d5000d0403450078103d40014004039144c40d00d0302075070302251071000203075004e6401e00180085036030018ac0210f0606660300d480d00014850090801c114a004241c044100600010600d1000c0c50684010348280d10410410003980e802c407904100380e036001203100c00b00c3c01c0c081c0342ca07600911400d842241e200601004101c1d100580044000c1003030b00c8a0f02504114491300104003c40c041522410040b01050006000d00d034403500103183c0c018146840c94400c0c0102e62141030480b061444494000348045820609042c2c1100e4855000300c0f0510400c8054642502c3e18002c1e003590709802440b41d9000105d500d0414800c001d44484204010001c503540c4c28180740c094010035140c4100781c0034561101c0080c8419030018012417140003680c014110880030b20059004591048000300da002c0000c0c00404a83c180411003203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 54867368 1250 54866118 54866137
    0x110a02031203240105030a18021306080d020703030e0d03020c10020f1e070b031906081c1106071b050102041502060c16030f03020d09061a0319110114 66
    0x207039602c1c2045101c608001d6030240c8140d158904400c2810800d907441011179500c00011900024075150030900f00d1000c001c07002c03001e58020082542c2c00b60a240310f5000340115a4104201c50740380e062414240c0e21800948009004204003084140f203908200300d01d041c06038402d1041e618900000b0000910000483d40a40b0042c0d02568540345029000c02400d9220209040100740c294484101140d0b1200903001c1c0e09a9100040040340001980810b803150607410004e041c012030b0f03201d605089e0b071002c1602c1003899031032190124402240c001c45d02504030400c00b001800c5284e40310312041e141960031216104c2c140d0342580c080c00c0803550070300c0a0700252520b49110321b1805102c00f0002c0c40d280001c1c01c1c0c04804001048034425002080310f00200155160514050842d01c0040544c000c3c000c00002a807024100301e808010065903600c0f175160207802d02d180d400000d18240a150f07441d8101c410008180110b03c1d0361102080340c03004502c00c00c0b507051401c102400c4040f01d442e55650000d0240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 54868618 1250 54867368 54867403
    0x1b010c030e1506150909070309060b0409020105090d020102030f0a020109020a080601080a11060910030903170c04140f0a03050d11030f03011701110406020703031803020a06110a0203 80
    0x840401640360180e440c1e0500d00d9401003114040c503809030440448040c182610500c0001d882d00700b102e007400c0c19184883c1c00207045882034507050320040c002c1d040f110003c0b82c0c0c442c60481e482e105c1d450030340700301100150107030b44240c00c0008050074450ba000300a00164103500c001c1c00703c81521010100140002502c0c0c0d0700100e150a030600c1444400301b100e4100c5043e941140005114101c400a17039820200d401070010449801030ba00030501358070845084941100000074542043c0c4d4040d040342d00028440e641c0c0d8001802006080c1d03140200a0382c1410f0304540400c420080048100000d02c603003080106058001a10400000c1c442d464a620880b0240c214540215100e5009031126003c3c40903040610301c0d00005c400044000d1105010302c2800c4c42281100c00302c000400d52011400703409a0074000da031283c42c0e51010390348442d5480220300145001600c8008494810210380440368090030b4120b0389420700c2d5096821030201058003c883c030032038221401607a010009000350100d080076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 54869868 1250 54868618 54868631
    0x7030c0506010b07150b06031303112a010e0a060c0501060e0a0c0207080c0303040e130f0c170c0d06020f0f0a03050f0903031e0612030f131502211b01 66
    0x3041c0260b94540c601417400c4514085c440e800036100c01c02100d40c00750701521310058540d010f00e41942c42040d00404103d0900c1200c00b51286103410110803030314501c005400081c0c4443c030310011918802ca5081c1d603070b0407a0700880d08100d0795015010000b5020312503000410355030b88500611404c1d4408441240391240c59070814141c40d501401800098a1854080c040b043c41d0360020035a030740b190388110540f100c10000003403128840310340d1421020381c0c412410842d40050f400c0000040c03100e40110a8121000c407074280824000141c5101c408001a012010106030760f1900030094008002c4005512401c2210719054486c2000408000c0045d40300000d80382045624408a050b0052400003298410001d02c100f141c2902c1e0800210300303000d9050280d560711440454031040c0001d900d60b65912020855a0045800c03102600c6891001521908842c2c0d0b960341c0e411200c20b504035080e0160300b00d06904007070080e2420318031954640c140451881c20041070005650a0401440410265540c1030b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 54871118 1250 54869868 54869873
    0x109020f01111216141b060304020111011d060c04180506010509060406080915330d0b090d020a260412080a091e050618030109080304120915030207030c0506010b07 72
    0x1550804a629114000c3c00103000034606c1c1c0503100c4400049500c2020b020000504680c4602441c200d030381c144200900a2a070746002c910010b40b8242c209580038001c0038005524201080e060310119070110104100807100550200c005100140500d0304001007084a000c1c152105002800201840d0f038602e000383c40c1c012881c9040262040c0d2107603071000a1418004a0703080345003040602c2c4525000c81e1101020340d80c015501d081040c2c0440c2d00081001039000c14004400a00d9104040c5101074031000c0c2c000e85001c903191002d410740200340780c0100c0041061860307901000c0719840e1668070014a015181c0058600e02d03001c03000d003201d01040001d4404550769204055000800103040e00c044a01c82c0803101c0204000035024143c011480414008202051204181e4100750050000c01c501d8003681840c807826802104c0a9071080203003000c50204178468441c440454034080e014940742c00007840220045d500004054080000110040000c140c090080600815158000680e81c1c503092 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 54872368 1250 54871118 54871133
    0x3040b07020307020f010302030a0b0406080313080f0703032615030c0406050627061305120f06010303141b06010602010c03020f03040f020a0320010801080109020f01111216 76
    0x10005811508107000b940e006885e80861781c800c0080908026031070b503803004c600340010310400d074540b940709060480008070744102100403d5000c88900380d1f560b866885035100c90b42c90341c3c0c0312007005542c2d100c010108040780c41900c0140b00211400044151180c940480403c01c0c80180e4541d6400203004040c2040c40c9010800e01602d400f0030744060000358a8240015030358007079805c521010102240d001c05807071403035100f020f0310010014011a00c5040003000842c01d06031a000d1a4002c1c007110380340f1480c1c101d00082004070000c1c100c004184036800c1da0386c204c0700c182041150380203124080c08070381e0500405032031003015808880f00529003503140c1b070f000a081d1900c4d0074140c0c06141c8100600041c40d4208402c40343c0c41600308200c0803003014648080b4054010950002d08041c40e2900070002c04d03401e0030b6101c5950700007640d070a141a62035004480c2210701c0d4910096009500c1c0c2d4428006500407d100c00032032409a064079110303d54201120380580c450304e699a003101001c0c42c030700c0402041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 54873618 1250 54872368 54872371
    0x507020604051b01020102090316050108100b040b0702220e120703051e0909040c03060623010f09080f030418050606030415090f1b050f060a0305061f0503040b 70
    0x114802040141816112152645500c03001074101900409101e200369000350100c40ba1400054116805241d042e00c0040f0052010b004490001e0308040220345800d03416811001a511070f40c01d400d2a26144c02d5910758594810007040707803c042080700c080110b40036440c0040700c0000761880404c80c1c5110a08507814641d044510402221080c080c00d170100364490f05440413a880300e80700c40b5044034000141111401441d098039402041c1c00200410001c6500805040b00e01c207030014844251a40180f0001c1d01d054240a1510f502e2001106050b41c4100c90118030740700309090114080e82c84e4549942000481c81e071204c401c1c1d0001408012480c00d205182004c080002030803c080d0030241d001500b94803000c0e00145c14541071041800c0540d40b00c0c1e1201da00c01d40c3c8100c103560b54035000d150249000f450020401090640030800280794203080c0b00741c0f030107040002d01c40c81c60b22840c5903094006200140c106504003642282e510b5400d02da00180080481080d19031541741c1c60645404400d2120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 54874868 1250 54873618 54873631
    0x50f040c1e030b0912030103051c09180203070c140102040e0c1905030a1e0501170115060c060f090501051006170115030e0106150f03050103020913051c0905010305 72
    0x3031909000c01c0400701100d05000d0ba580f0024501450b1515982c0c40c1c5014000540c0300340d0280000000810040e00141d04281d40840c403a401c0c1c10003c3c1124290380340343d55441800d140d035124001842e80e003450f9500440e0701c448107040c040d440009a8407090030340340541c00202c0d841d81d4005801c3c49a201071607801d039400640780403600d140c903410303222106110b1107422940c01401404004100726900130341080381c83c1902c86500109940b00c025848010f044203118103000d10401841c0780303041490600907543c0350404441440d052a1030b1000071640f81019034800d954040d990b100105a041c140d0003581d15003402480040703501c0c103007448440c8001d0803690004040c0541c900192203003140c174030301e00d5044800d5840351308420482c2c4801a4040c4c80b5014800195521341b207030102d0380550402c400c0c440c0840301c4d92810b4030500d450005070205c901c01c2c040a50b00c20700d190009400400360000d011307402449101070300d80e40c2d02d41e6520030402403110055007011568a03002400309582c14071420380e0228 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 54876118 1250 54874868 54874889
    0xb0114040b0a03170c0a0309031a0403020d0e03010e10020405040b0603040507260a030c0b0901060b0f07140d050d050703050c07031119050304080c1f0804020310050f040c 75
    0x881c60300028402501c41c40002d1030754040e1100403030541d80400607a00c0060b43c500640c1d558820515000705405000e010031203d4030b116050303511030005c1d003081903449194141c000b0030400351016029201c0120340c0c4640c96042d07490b003a04180314102805100300103d0f2040c0e0158640342003608000030784428024090150b1810b20400c40800c00c0002c0580c00c580c90008403a404214418107006001c2811580601714410700c0303542004c160b84060203504441c090100301c4880d031a40d10040d400d9840c1c0344100d9411002c14441c81c003d104166005119061140320440c1e244485001c0c00790400342041180360208901203241202c05019010b243d81c017110601c0c0402c01884c0c0110740c01a42e000e14440035042025824100a0086080054800584880104040e10501440c0030340d0740342d003c1d00a00f80755024080e224070280c18851280c81c003100c001c41d030302e44c03402d040c04c1400c88003031000900a0341e040c071071030300c045254079280c0c49081d015002d01816100720740380c54240380720b00e20703100c0d4812400786 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 54877368 1250 54876118 54876131
    0xf0303050c0c1203040e0c040e010806060102010b030102041a1b0613030906020309060304030c140712050708010e0a03081009050a020d0b180606090102030c0d17100e070509010c0f0b011404 83
    0x90201001711826140c011410401c0c54440d00c039a0205c0f03000c1ea070400b00c102c0b044800086090728ac0010342a02c9102c099000340f00c0c0d010301804bc1070030b038041c034820301205428118070a203090781c080700075085a00c62130304002d00d080140110310381b52200981c0d00c8598080c0c1010820185540590740c5070182495000961802000d400800d07114800184090300704000d032110042040030008481c4d15101c4803004503445141c5449804640c003405990881d00b5125003640081c0400b81070041100564615018104490007a10b0503104080300801800200040300c4e40400d1541040c8106800703962881030050f00d641024183e10111010b081501d0300c901164200a11070025143c0601e9000c0025a20340b43ca802e1041c0040c2d21358050b42104110500a03140d0b040840799028043d01c203d1051400b203440c1546a0311080c0c0c1c102807d41c0101241c10300c450340080d14250140d00100880794041c900f54841039010707140d1640c80e403a4071400300e5001d1654030042000800343c602015508804a0701000310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 54878618 1250 54877368 54877399
    0x3010605040504180606030305030106110a02030d031107060614120606100509030a02031b0a0605030712020304020d0813091b0203070b101206050f01060305060d0f020a0f0303050c0c 80
    0x441c081d038424140301d180c41e140c1c0d050004c140d207800c6012156206900f4081c0d00d44a150191541d0002d006020008507803800844040c400040c12042caa41c010b0080e00100e103500ba4202c01410b002c034026800098100700e510000b88603446108003c0c108a403201000c402c0c81b20800950075020b15400f80d10742c2c019000c0c4505503480c0f030a561000d04640c2401c80e81c54000801080c1400c0c88210060b42c1402740e42035080d1545c00141c1c0c01988904211001c88103103448003c1a200d03401300b0344001c0e0002d445081c00f503510382100e500035904580014060000c4011956942c0f900364004181c10305c840c20303114000c00c081781850143e8a03401c4203844000e41111881c0c01d00a40d81c0c0551080a0090050240400e0920a60746a85070141944140c004204207850600102400c803c0e94003170300e43d2010000015848d440b030b1088902881c4014840003a150003600d0300c10710030701002816a03115140d1040012071101544442c2d0003140f281d11250b499001c0950803604007138420355514020400c18001654 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 54879868 1250 54878618 54878627
    0x80c01150819140f011e020a090b0c0106050a14010809010e120706060f080f06010e07210b0402030a0b0a0509040b040312061a190306030c150c060507170c030106 71
    0x10201d0004964040e81d02d050802c2c11654400100344200c0f400781c1425000c0343c540641120b148114200740320940b0303507040107050f400ca1140800010021f07a0821060105205042c020314400504400100354652281300041180b40c407980148842078020003155803a5801030446c44d4810741000c001c01001e40c90007000d9032901c02c80c03003000140c1d10000510004020b400e91214028110101ca01002d003501d42c02c14640e00c22100070184402d2040c100001030b5200c003100c0040c4500d207240c4c4c49081456031400100140307818100e8680c0101d03100e50070203106440e14805548607600100004c01c08110748030500034441800c2c1c0140f402001c44004000210740e0900040f0307000750781454842d0100d4000e0302260b00a200070703000318000c402080c0c582c0b05001110f03409403400410400103030711071130b0103410207078100c40c02c0b44802010701c8829042081f041688841514101c411400d180c0c0d11b1302039507550481201c17011610403010038201c5604583c601076015000e0342c003003c0c00c44090b20b5941003000140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 54881118 1250 54879868 54879883
    0xf2115011d01021b040f110a12020901020c060a0509031f0e010902060304020105130308071b051e01051602040e06070206060303070b0114010509180f0903071707020604080703080c011508 82
    0x11344030000840140d888580c000481c0200b070480800030480f0415087c0d8907907118030711030030000c0e031300500c6034004100a10171101c4442050300200410b80c00b02c000d0202d0f64100c80c0e403c106025041c00b030600f580d04c0c01c0c003525841c80303030020101101b01c01441c0713039908884c042c4c40c1201c131582c1340101560050b1161030488dc1c0040d02402d00c192103140d2100c0b101c0071130007130ba00b0041451001085000401200c81c02050381600c040171382c2d900194031002030241224a143c1d8143c245140c1d1041843d80354003c50003400c144c940703280e080711214159000b01b01924002c1c1050011a40610200b1a10070b506120140d00302c0e5044002c0c42c46c1151588446403054410b01078a04941001c0d000182140c0c099401c0721101e030000390401d40c1b01aa90036040c80c1031034040f11041d040d54880000582001c0c00402251301880c2c0c04480e05242c0404020018015001b02c80c080381c21000c10440070605590800a80c5d001318803034004030340d0f60000780c912142074949030b001c01c81102401c000700b842410b10104400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 54882368 1250 54881118 54881143
    0x21315090807121e050c1e030d0c111c020a0f03150b0105120c07030f08091203090304050406180b010305040b010b0304050a1506081c050f2115011d0102 67
    0x140c0701e0f151581060040d0303008007403104108080303000f003010420501251490202008452131409400c0303040b003082c1c200e00c0450340310b54181c10041d8803141c554020100c4480c0c01e0300412102c0c1040c82084080781c01d601518180811512030f041050742145401501e9001900f9000b00009040c0e1442d40c0310003188541074038074600c050b2200c0c0e6221660744108140c0d40743d060b0300314610500d41028142d60400e0b03400341d1016070008284400220078280206032032030050150340010b2030b40311401c030700000a54101420383c0c1403074001088000b455a4981c0a120060a8041100001c1c00e401c12140000c41d40b0020140b03040c036041104100100c3d403940c044504507060004515541ea440746003550405010b11401001203414050a00491206600080036241c040c0201d8038150443d400e400310340f102c000002d4000450400040700c00e994524081e091403400c960302d04004c00340c84043c080545504403000c404405c02c04569040301d40c4d00072843e00120021701c010309400b00070b00c00000c0d19016101c081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 54883618 1250 54882368 54882389
    0x17070e07050d02090a270506150a1e02010c0206090109110402031906180c050c0307020f01020f030d140123040b060c030318121201150909021315090807 67
    0x842500c1d240c943c0455044420050540340b0300d58a48000300e403150a600c4d040f000400000d290240400042d12030036014040081400301680b06032041e508882d0320500c10b203410403400300b0b6a4142e04100c0e071a0407808035480c2c0c00103c0c00d803015110003460140d008240040c50b0307042c20f00500c08640e00a0380b10002100c262b8000d82da039900c0e0120b6801144003040c40280c041d2402d80000707014450b141841c0c802d075403c003030144032460703440100303c030340e40562020216940c0080000200510704030100025141040c015680700d034a600c0021411500700b2000b038184130303845031000d000c818280600940500102000c00d019170560b0301080300c0740990002102e00840e602c00f803180741544c1c0e80301511052800e540c122503403841e108080144044c03c00c00602803611031020510200c0c11058181c4000902c2e9a051412503841c00c00d64200ba0005005c0140c144200041c0210388151107000604448210b65003060a1621b0010303448115100c8401c074408001071a8014898020042454411608071006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 54884868 1250 54883618 54883627
    0xc0206160f1713020a06020a020619111506030736021e120a020304120503040204020f030f0709090e0709020903030c0f100f0c120c020a050d0917070e0705 68
    0x340c2e0004800445020241e4101c420461028000039405044500c01e03115058802e5454809980c0c030a04118001e50010701071003c100d001d401c0b50203540100b049850f04803d03840b01440305508000d2080440010503034070070204035590800b0001e59009010071280302c000c001500902c1c0f80380705241c080c5060303041141800d05034050070f40d8041c0d40006801c0074108c00132414241d0299019440241e41d540254002e100103078519403680b080d0307489150050300554656404c40c1d8219130a900040040740d01035401d11400e050034100c00055841120110b500302d415050561001d8a24050396124810352801e006880b003800c0c07400304070441294008600562540b48240000b4113500a00100548e68400d9004e140309500000805054020b004c080401030391a9590910049e14960603521001c1081c0c440c8258256400e0b0340a0b0042e003030180706907071410f20540e45440c20003002d5101382c1d00107071609a050082410f8043c0200c03911079032500501e0032900c0c000251305c08031401020034041c0440890b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 54886118 1250 54884868 54884897
    0xc1e0603090708100606090b180d0302030d090f020301050604090c05040b0d060906020405010801080309010207060f170103060e0c010813030507140105010e04061407090314100203010e06040c020616 87
    0x2111000d07168003000c1c0c0e0040715041310900000c010504c075801c001080c0344800108074885038100c9440b01c0600e01c0c4034070b0014824040c00004c60180000b2800c51104120841c1d00d0a120710860301c005120300b03048181d1103040d00400d030035150050040351140780342c008090700085c2200504802c4800903280804c10381c00e1f080000e03005001c00c1001400712420003143c0c030304100b401c0d4018020303984242c9440d025030341c171220507540d28080ca2951a000d80e10840d0140b014601816080305851118642840181403010307151008072420390085074043d403281508030300c1d01381c28041c280302c3d04000e10b011001440d01a14000381070504100280500000062010600140c81c031100000d00354080284481d50f520128441c600030f080b40c0981e0481e10f001d4003c1c01103c4912222405100182e07a100b101c0ca06588903040e140d10712800f034604500c14060300c481c061000d8001b641c0201013070010030700b5918010b010b210a944174400d1420464201504000c03201da810000341025180b0f40c600160341103000e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 54887368 1250 54886118 54886123
    0x115030603060f09140715030b0f120705010f39020901030506010e01051002030d0b01020708150105040b04020c100b0109120503070c0602060108210f04030807050c1e060309 76
    0x107800103082c2c03906040f05600540702d550010002c0c14441c10414004c0380c06104001e440d40b5180c085d440001c1d181c1c0511840103072207074000202180b0700500c015480c100710400111a2070f45031483e900c080e00008810422980c03c48040e01c28078400781001d004141800c102500d4074841c00180390070380142808041801d404442d00001800e40c041d007038042c0d0796180e0400b5607650009120704801d040c02440085000d05040000384100741141e002541031441e0440800c0140108008150451041e10380c00502000d0801c4001c00f050308514188078594144000c0c401070700d9010003294002c1c2c2c010481c40e0803240001620095410381c590b40061000703000c5004030f614051640c0f241c0b601459412284061020100c01090700511561507070700c8241d980d84041c0c0e1074a0091040c81000d40041c8695070030030030510184070a50212441d01c0e8545100707072100740c18030b42050300283c40c200c074042425410032070100040b03a5005412640c02803008014140070201c414403005003405105c020020680c540c808 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 54888618 1250 54887368 54887381
    0x504020d060f0803030f0a0b010509101206090f0b03010207240e07090209010e03010c080c0f13062007030b06040b03010207020d150b1509010f02120309010c0305070302030f011503 79
    0x79900b0000c141d9a03845459075241c000351944407086885002103548218140714500e8842c0040e101c0a040c080740c902007054004110400409001240c5080b0002e4030940c030402c03010f807007042400202c200822107000704645150fa4200d00aa00c1040b00c82c0c046071007811690210041039090701302c03241c1c1c00034003500030340703080b1065641a104003140442e83d10714075005083c0d030803020380c0d07810350901985080500781c0d2081c607500001304141101180c9030021100003041c5421007480080d00c5c15140c2d42c660140b842855000c0e40004040e404a43c6460007a0b459110030000d450303005000281c20341d241c1c62034444002d03240c0c5206540c0ca0740c0ca00400c1c1c800390140c6004507001400900da4803403d08040c0545407043d12035114031440d200c0e80501714504a403100c040c05141c7c440890600d6810780055454035000308a800c25071258a44694120054100451091100344000302d02c2c0c40408002806407600548018141401401000302c122038480c01ca50440304030708000341c07440003903031025002000d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 54889868 1250 54888618 54888629
    0x51e030f0a0309140613050603060f060c07060801050105071502070c081911030109080f13030209010314061803071b0914010e060d0b0c07020a0e2e0b040504020d06 72
    0xa8018480e0526810049600c101d40c140d001d841319007060403081220b40d00c5400c6055400041c41038044c052800c09401175540702c0300280003003540680ea0000540c00d5040401b20344d10301c0e40203690510906a21002181c01040c080c02c3c190b00301005a07845c03100040155061840c15503000c140842803100310f0603028014250304c815141802c1c07018920303025902c0009401e0350010380c18042e80405e030805120b0740d51083d0300005081d00344640c1603882c1c515940212190040c0081c00103010025031f980010150003507105601e04001c12100c4082d150030318000621201956001c0c40010001440c04000c0740c4540340d1004a148980810011b00b0780080c5075500030031a5240b50906820302a203200040034145e8000d016442d00c2c56540340c0401c003075502c460b840108001c05400c0490b0b40c06001c0805442c0d0700e48005d040f00c020a0712040702c0e108e0b03808200c8050742c26003c10f0b28641401010882c032680d51101d4102c40707108071410210715810038890ba2081c107010b160f0001b4500d4034030a4a61003480a0706 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 54891118 1250 54889868 54889873
    0xe0a0204020d0c02070602070803040515070615031209031a06130c0e030c0f03071e05100c031b020102030a0c05010e010504210513050d05100e06070e0109051e030f 72
    0x1030b0081d5140024010f001c000e1016110302da070046a0075000040c45012500301d04015858242007000b8071508a82c49034083d0542a0203001010000e00c11b40182e40d82d4502d0408900c800c1c0e80b035070404800d281d8408100714103201d400c210901c0401c00c00d0410a0300282c3c04c0600212507240c1304007007084003510080e0305142d146481c010303100d22548410710854920084080f10507102040c400c208805800000c11a455441201d00f0003010049500c220603144a1142062405641e48c0200349801e1488403a640003a600c0d2907064101508110080560044d01d0010340c00030b5001d600207944c074490781c1c0e116001c1c816001d1000c2d04002c401d40000800c132031414000e120508162800126a047c0c0b0005203054480d00c0c42e0b00988244078005070740d80410344100580f4580e02e0a01030024010b42072105079483e0160000ba5078070814140a1508002c000d18001c00262400366001003181c88172980d51410805080c0003000181c0c2c078101c544480c14a500d45885040ca03803000002d1074501c0c103440303504160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 54892368 1250 54891118 54891127
    0x60f05070c060e15120601030b0102030408070308030f0108010b0a0e0a15031a0c121306020702031603060b0109180c09120308010807060507050a030f180905060a0501080f04060e0a020402 82
    0x1d0381e03c0b910b101c01e11442660b100c0d60741d0825800142d00c074000c502003000e40d080b44500141e040d61194200c51600c400c180142c1c0d1810742c80340c0e030203030a10406400554010400006001c10650002c3c146070040c2810350080016401c0303800058168111481440c44100844011541c148010390080b1209841c907825203440640d41d00c2c02d000300550704c0c040c2c04d100000850010b04441d0300001204c0703e020110003c02e0a503510381c001401c10041d0100280c0340560b00780311442c0141c41c100310342c0d80c0761500141c3c410710300d42c0b40d882c00e9402c0e2201e0b11402c0d410401d2054080040c1803000401c90b2403034640c40000700d10103201d52422100100300d64004200070009030090710134940c1142c20207050f2030300d01051355412506c1d0201501c5078400d124000385030340d20018101022030320a41000f99001c105281c1842040d42039400780180203040c3d0091044250764000f80a080d15041404100900f82803c0881e1185441c138070100d440d25000b4009420252500400c0c500014148001c0c41c080da03008004541302c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 54893618 1250 54892368 54892379
    0x2180904150f14071806050a12050a0b0f0a050d0f050a240609090b07110c10050d0e19170f0a09030203011a060307110f01060b030609070903050304060f05070c 70
    0x42d02d403000c0140c00003c200710108150501c82c000c3c0c82c0000c020741300c2d0515010304d052422078695000c11000c0701003000c03810000582c180f45006440c041da140d0ba10208540004a0801903c0c02c2428002c510410000001b00800d40366408940c074629080000e44019040904007503082c00380032800208916200702001c3d010400414114881070012201002015164401c0404696103d0300c041c0800300078200090180d4070400256540b0b0f4140c07000e841507200f04102060800e494802d000c000720300003092000c44d4200070b1107001ca80400c140c0c01070101500701d52000c6083c110085001c2c082d03003500c0b1055441c3c951042e08440c0d030045400c00da10b98031010034500520000c1c003030004078442c2d42003c0000b852145406240c0e41d41da42c00620052031911403090a441502c7c081903c91080e0090001c40034000d4401e201d01801000001c001e15030380d142c000100410032070000d142d041840400e8600b400440e00010075101610008d040c1071040700304440b8181d030b540c01010350060001c440100d02007034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 54894868 1250 54893618 54893621
    0x806060d02120601090203011701020309030d020c03071406010617060d03030902010912060516210b0301090506041b060801080d0c0c050d120305060114030f0c0f031501090902180904150f 82
    0x42700c0a920002c0d01d030030001e9190030300340e10055403002102e5005001d0429280450f078000d140524407203007100e20f07080b602c0e510349600c0d1003100800c030411340160300100006034100c40200e202090820101d509868240d001407100c2050700000f070b0400d562841007174116400390800134080c00384100b140f02001d58500c1c107a006800100d805465141c503920010440501070714074500260074040428600150304025000204540b640e81507041d03480e40d0356900820024041c15008a00a5070481540600100703031a82d0340b00c4550112007003002e100d00400000c6030106441214110a15145030200303030794102003000b0261a0411680000010405c5003004522000d1401c280d40a407414041552410010744901090386042c0290712001c02c00a280d0340710382c0c0520340d40907000400c2c44d030405000381351000840c1c0089842400a00c140c0840e00310307540c0c0041b5141c0c024405200250725000d20044001e14242c0015030490060a011022908000c400683d100c902a00c0780e00c01c00c40115000340d10030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 54896118 1250 54894868 54894871
    0x30b011d0307030b0907051c05060703110409020c0f060f040206040e07050912030d0c02010b061b0703080708130506211005130c0e2709010b0a06080403020d0305010806060d02120601090203 83
    0xa215448d20b05030304800c031048202d0101c4040d04400506510340c0d508106034045c2042e04198035006a0400011510791034910203482003151441c000c200b008111601c681c03038000040c180c2441940d80c1d03000c00c00166103240844060b1020b080195026490725442a0380601918441540c80b8000103100102e007031000003d82a840302c4410f05112081440006900300c855849500ea00030800304101c1c0c139003004004282c40700f01d84034003c07107840555a0f11400d40b25080b181c402c0361008000034020325404160111140909004c40c0e500d4030302404400d032280f07020240c0c68030021802070280054149043c83c1c110310300503d40a440c1c00124200c00810038024100941c894021460340000403c0354100784854101040014440c0b141c0d5080c03221001800d444010100140356498500c000010303110405070310002c03d600e849a10090500c2c0c0742c00390170084214043c501700362400004200c990b0001a803d5000801501c0a10b05009940040f6491802034452210310303219010001910808590056 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 54897368 1250 54896118 54896129
    0x1060e010e06040f060f060302180303030a050402090c031302040b01030b13020406030f05041208060d0f060605010f05030702071a090301090c06031b0f052109010c020c01030b011d0307030b0907 85
    0x1300607038004882220b04984150240220400f50200107010481c000e0340100246804060851216811f13000006c1c03641c0d01c01c54002c5801503c8030240704c00c40c180803080903000f15005811a003035240400c01c0c852070210000303002e41300d652110010032480e40640c0c0b01078050340c030117049000c40c1c1c4c110918030310217580b00744a5000000e103400725209607100c0d01d1042602450303025024050301c0380d600008503007003580600031941c40740710213064600042101c5c0400345201e100302c0011400e00c0ca040c00140c861901010007000b400810420070410300d070f010520300240d600c1040b11040242501721140c1482c006d622605400d90318181107407080c4000e07060900d0407a203059809028601c0403200c8000540c45c02c0c0c41480c0030940150344e80220034058009840c440c4801241c10ba1800b1440f052081003203825100300400c1d940d9030681340612079040c4924a07841c0000e0070b06104814a01c80000c0c00f00e000c079140b080d04130002506084560f40c05000b0707140110340000120250381040741c030700c81e211903061080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 54898618 1250 54897368 54897371
    0x807050a0b10030321060e09070317090f0d03110f0a0507170307150b0d03110d080606040e0a09080a0906120606050d0509070f06020d2a08070501060e010e0604 70
    0x3940d8110b000d1026081e80c1d4195a89107046801c0e203020302c3c18440c2030808641003a15a81c021511507484071420f4030852118004018240c0303136042c449942e0340ca01190759002e210411001c2c0141d10303103910b8070b02107408c240e0381ca880303188041c1012558550403805d6250b0034050110071170040040005c01c5034119004d142a1454196102011003c0e00c3c1409640c041c5a0400e007c00c034082085046000d118480c061804074101c4607000c0020340000c44850101d011461094841e9408503041200d040c40b080907061600c02804c103400021050300461144040112004000802004a41d00f100c48c005a100c3e04061b103840c400440a44110904d018100000d094811064510b01050182000b04c81158075114604401c0b0961400035045c01403000600e031090b2040060704032506202d001c0188665400740420f1910038900038880d41c251203040400c0712a000f15100d10302d1851948040c480c0d031084d01c1950b100e08516045000d84000c1e880965a0200719000060b00981d00c3e0103284900003c650 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54899868 1250 54898618 54898621
    0x1302130302031b0906130905060703060e07080408040b0f0909040f120c0c030308060325080d090503150403120501030605190c0c08030c1c060f0501020604050d030f06030807050a0b 79
    0x81c15000c100741c40c00f942d5807050110021550074105081036003040f005c3c0399008201c14400d500d85510f4005c064a4a00c0000d0342d455040141e00c20400b169a040181840c2140d80c508050325000054010b502400c144090002900d031014001d0740101c841003040601030024901d09818410104181c8403401d0321000125204940214401d01d03070745200310f90080590f419a41175803011103511200408481e05032003050440d030107001104004580c0e201001d00ca69107420b003849021400d00d1280304070501031009200007407051340d0b004188504414070705401c608140d9154101101d801c00c0d10780c480118280307054004010b0150b240c1181c0d22031a070204807a2240618a03154600721144008000c00140a0703520841c002940c14000350b8111030a24003050034a441c90310098141000b510006021a9544004000f400d0707201110000800090019101c0352030203494168651020444280c20980d03152144020f9406503232000e0003647cbc210403601e80f110003600d0000d43e0f48801f0002907a41e100c40c1c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54901118 1250 54899868 54899893
    0x901030606063009080408010203040b07020d0e01020304030809060f07030c0c0b120601120b030114010509060301020f0a0f030912020d120c05040306090206070209070c12020309060a0e130213030203 87
    0x9001d14401d20014103e14071603990025410028081c842089640c1001000001002d8500340044d6001d64040c01085030b0608180344007919010090b5808014080a9064a403680c7c1c1c01109030790840c3d0704002c0d10399442c5045c0b07000034051303c40e10950765540308001c9883c00c20f042d0f00c89080708440c0e103e4003680503e542c841e040c50820f801104d0080401d202c2803000075031154070a00041c154110a02c00110f00d071840310001a0075982240c2420703d41602d200d00400c0245801c1c901c40d03030011002c1c0c0003107107040b0003040800498072a001c00f8105002c83c170f011011980381310383d00c0390f14041d401a6100800c100b4481c0000d464045001d0780500165500c0c0e07a41d11034200034461070b81c8640c200c0d2201d0b4941441e5035680c402901601c00243d91002c02800800701507129116420710860055a07004248080340c5000e80c0e0b142e429451107821503209105807200341d200c0c20f04070b92018100b03081c503c00001d00d850010300200020f18840031101c1c0085003a680c0d00380f10455100a5a20881c02e8504040d881d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54902368 1250 54901118 54901157
    0x4120e0109320418050120072405040c060807111b040219020a03020d020c09040213020c0d05090102010f02180f03070801060b1201080c010801030b0c09090103060606 73
    0x9002e418514581d0501ca842c402448201011505001e880500c101008050001d4102d0b452070000c0001c004e50415074034108002840f400c0e11320001e000c0018514035407a100200c1900402c500280024012080c20100f441d5856940c41502d01402e0244030520f01890400d603000984d00c01c60011480c0c40700070070540c0740681d450320b50380529100204440050b46050011046080f14020b402c16801c03c94460382c18a088911a51800e00343c00406a0b2800f42c0b0300240342005862226086400107080311550341c6e107001015401540454015090303200101c4810003c0c4561000c4500501c0b440000b540e5040d0080080c03c02e040098008024081040c0c801006902c2480840303101d03c80080c802d22140d1601004810504001030704582c21980c03110352881c21101c241e0450000002c0c0401e8141f41503080344545405030101e140900380784001400064203040d01800000c0c0040c03100c40010303900030b40a03000d850460701c000b8540186941e60341410030043c10315000d0b400006d08001c00d601c6c00e06600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54903618 1250 54902368 54902387
    0x605010504180509190f02150304050a06020f0702060c010212060607050604080306060d0c0e010801050411030c030403020a022d040e0a0b060103150e060a08060601020d05090f060d0b091503100914030304120e01 92
    0x304bc00b815000204d40e5a84c07000350f003c90140e0021000501452003da04c4800c054140354000e2000166181400d4102c0b103100d810003456a840380d2420480c041c001007010481135045a44120055202d0f1901c1000640b503000e00c0c00c1e0100380c02d01e0b190100d09030552100e60b480880b10280c0f038000c400e076254024441900c20700306a410440307004002040c3d01d002803030000c650060082c41a00e0a10b000c075800201d011031070000c41007205401544240700c000c0d81da0700c41b0140e418110b400300f090030318070003840b500c032a800c14000d00f81000300c00c00261070703901a4110805440418007441c41d050748a0030348a409940583d01a4003411003514045400f400009406000e81c005070020103059580c854100c42d13982c440c18480c0d41055081000c1c0717005445001c081d12280100400100c0c91118200030300900e1b00004000d80b0341e84011041e0030318142c03800b007524044c0600b0000049488042410045414105540d2840d81c511000040009001c00981e80032061b401f41d9032010f40b80d850071001102e01e200b2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54904868 1250 54903618 54903623
    0x21b0d0c03080408071a071b030801060804020f03030f040311030307030e12030c01062c070f030e010209130e06010e06130f1805100605010504180509190f02150304 72
    0x15180300d4540464002d00c41203900c81d1043c00b8240c90b05515688000198284c4003240e40c4e407190040030300000c5600407259214200758200ca065082c40c007034500600420040c400d0710144013512000c9419900c0e450804a20228054201c80e44d44560700341a0405500510040e651000d100d0542a20b519010007192030080d09a540e944004400b01300700b25450503d1503101c2c44501c810085d0001111080c003585004104c038a010280d256903800c800440101280740c0200340160750420072207440d0700101c003c1d6641581c2d160005031040030f90511402807040d03210060303001d13510150a8031000f4160304013120301c10410007551420790381c4008501c0e21520070b0707801507800045025100440c038001c4e405509a14003900010a100042102040003210440c40664890700540000b002041c031500030000141001c1c40c20318503082c80c00034084160442c010310158030340c2d120000310307218a03010007520821002c0c0c4000f040d110a8246030044001010000407802041007140d00c0301070b046944140ca20954 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54906118 1250 54904868 54904877
    0x9150504150c0f05061e1009020318010911010e010f140f040305061005040b15030c0d06030609050d0f110606060c01090803011211270402031c050c010b0406050a0605130905040501021b0d 82
    0x1030800540300065003000300340080140600300030100881d402d001d43701e01301d801040303000450179013000010a2030319000c0440b8140402e070400850342c0c2c0e5108500c50550060032411315100c2d680c541c420085880f40d580040c02510400c410b08c191501c0c6d1a0800e002c8603030845041209100f110107000608a215000070a0720a0030700000b1200c403240002840303610f6040030005603c64803960f42c0d004542104405072020750140c201c3c1212035030050341015010030380f4201000c3d59440c80b0340320340d40d80070700a1406001b0280401c801400d4002500301609182c0d000c00b00b5038403983c617408980440d24540b4026030311f10800c0035000c1c040b4286201055044480700c88040225503d011500c020290054002c91b018400c4000c0035540f4100c1042a80001342a40d8034140e032000c410344404d00b5584401c588030320440c0344c0081082290344000f10002251700f1400c00307940361a8117800300114540103900ca4400181403900700401c108041d1f00a0101010424918440001280595507a540031042810124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54907368 1250 54906118 54906151
    0x60216030308060a05041103090c03060105030a111305010611010b011803020f0a0f0b070c090c0f14040e0403030e060a1514030106030f03030c09150504150c0f05061e 73
    0x70380300341420369200c41d0240843c803c19a554011804503281c2010801d070885000c8203114040000b030000c0340c0403190817001002c49504003000a40c540002c908028507800b10380c180c2c1042c40c0c4601c60216142c3e201494104101d40c0e50300d002030030400411006c2e44040d407811800e500da40d801040c0b01d80d0b02402c02d040010200381036074244210b0f0035140710b0040e4000c042c24800261091a000200082c0c4400d0f211b080c0c5071062890729044a2055400c0220303418207181c04164181d6110041104001c445c0c5007088400415600300a00d5202e0b940005980c644203074108010715070190810000810b0318021074240d640d40941c60300445034642091200b001c090401000380d40c01d60248003e03c231400800006205980c4d82e036010100e045100b003240801e403a0030302070002d2600203040200605241c2c0e20305108190030300c0001e1192185001d00f21818000d10f807484809841204040c4110f075202000300380c2180582005c1d80d0b6494116441c00e41c021206070506030a9201010f0a80142448480034901c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54908618 1250 54907368 54907373
    0x9030a05030402030102070203010923030913090f05190227010302010e01030b06030f06100f020c010810051c0c050102030403051c032004030611070803060d031103040b09040606021603 81
    0x10781d00107031090340d040d03400303001200150743d0a1090880705807098840b031a0204005080d50303404040b04071401040e40003800300720211345170098522040410706200103005c0603946007820151003031840140c0640300300c0b5001c03803011810840340c5443c18002c65002e18034030034515980c01000281202105c000354944010030065016043c040c0d01c81005050204180c0382c50808200a6003003140d1104190200c20140005030902c40d1023800d030700702d051500720a0356030b43c00700103560f4041c0e5403d040d04010300ca04c0090303100001502400007400c00246519001f22080f1161400001d40034400c0d40c2030f04240e040081c1c03540c0000201d0341260303408800741c9902601400d00c4002840300c2100002456140c2c4542c001c01140d00d46c4106905810060042e200c904605100c030031540800c1540c12004c00400c203c030003241071031041c1c92f40001c0c00c0f90a440a01c24615048070465003207600309841d41720104021603103000c0c6034040c01951b030050b1400c1010399a80d0700308a80c1c0ba0480c0b110b00e1203d80b0001410b001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54909868 1250 54908618 54908627
    0x6041109030a020d170c06180303010b070f1502040e09010c02071a03100f060f02070605070201080a0504020d0b0c0904050c120103030f210203070807030e030a0c0204090209070206011d09030a 84
    0x5490b004a16105c0706140001c110070465000f8101910590010010018008010041b032070504100340011030030366041c000301090b84c0c4030313000700a41611a020070320004c10040624003044800e4044040d5192a41c4003215026100d050720100102c1d403c109006131050320000380d40003101c80702c04a0340c0d095410800019025407000e0403160202e00c4c0090b020540502c552140b40040c4440e0b5036a02490225040c000e040c500b03940c02c510f00f0010100050000b41c0c0c3e0001c1c003160484500ea0001483d07484620015070700703040c0ca10004101801150801072041d403910081c11150005490610840da84d00416a40310703c9881e41001b1001d00110051020074072441130348000344070f82c1c01d084a40401d400045108000e4191b400292584c000080003800e80d4000480c54200c055800c0500c2203988949810340c890181c1e074001d0040089015000c01595500c0d04089541034003d0240b96160500400c003c0d1900c2d02409020000d10f00100a8103542c0c9035440040e100d080300e03801460030800d04460455 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54911118 1250 54909868 54909889
    0x30105040b07031509061203200d05180306010603050108010c0c020303071b1206050711010b0112020a03060b0f0406090e090a06090804051002060105040b010e030c09060a030f080306041109030a02 86
    0x1100c41e001800411000414446c00c1c015090b8a041703524428a140360080090102d44180c00840c4501c1808481821001901c15009e001e241802511003101c1001c040514001c101c5055052003a44000951300e6003582c000c07810b80d6546402402030440380d0100740c43c0d08000c0c0500a40550040001030040745100d032016440c40b03403800f800d00b103030380d541c42c1c00c10216806508156000d540c0c0c0c806022a942d042091042503c103170500900501e5100000642a075402000010045800007481c280b107911039807101c0040c20f90000d4042d1100203001d02c0a0b06a0071078050b190106004480c04600701103c0c100c03091017900d18400516003014103a13140c08c09080c825408940c9040180000700c3c6c65901c0a54605901a07245d004010542c5044100401da80302c00f2641418484401c49000c0d036a100869103011689095070300ea0f024ac0c8030200460f00821260b4000b6000709c0b03410000d0420094108021409035000311002e1041100c0b107061140b1a100e81c034910f55150340311809507001800d1116940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54912368 1250 54911118 54911141
    0x30c020c091003020907020c090f010302090714130902070507050102030405091305011d010c081f031e020604061e0813020d060e0304120203061324020702041503060b030105040b0703 80
    0x78030520f55030f502180c400e400070b0301d81c1405600500c1090b001c50814004440c0c2c002c01603255142c0652458002c51288000504140c0c200004035141400740b180c0e070411926200388800313101002d2587c41c4040e00084d003010001303c40a0043c0f48001519602c00015034003552001456004142c4038403121410000b140203007118295241c0d1400f00c042c0d0720314004501c048400134008900d40d003141c113004040364002840c0960030138800050319003502960f030541c010740c5e074403070800c030207039000b45100243c038181c1c54400075440b450004001c540e0070341c001010b05241e003110f4001042c95451a40072703140b8070f07001c90782903441c0080c0ca501800945000546001454042d00340010001c500042c074500703607400740d082400610030040c0b0640860500b000710503848042d1100559035451150350b51032003400105060394182820010207204840030b80d0480e26140e5006008100e40b04080d40046655a01d500c07040e20542d140a07040c0041d8201030240522413548165104c1d80d81e40d03000d1064000380841c1ca40f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54913618 1250 54912368 54912391
    0x16060603020604031113060e1501030b030307060c0206010f06020a2d061a0301020f030a15090c020c011d010c0201141608040302040e03130302010c08120a150501030c020c09 76
    0x30160321428010f102860058141511140070304c400c0c4103040c83c0800e0611110361800c5000c100300c9002c08906500102e0484056189071051801240503200c41c0d245207515003c0041c40030104000303588500140c41c241e40a442d900d0380c1e1030b403503400a5211481200050f80100c0c10103030000e40c14031210f4201d02421b103284807541c3c1d0301e92400d00020100007021516a035880e1844010611150b0144824020407402546411480e9484031662700024010001c1551108074450701c1545110390f00002d8600740e041005050351859001355514140150240441c041038802c0340f000d00c40c4174a0113205041070b1540c9a08404070381c01113884401030101c50201d03035014808034100c0591034601c0207186004640c6262503505600400c81280d00400c05482c40d60300420044000d091a1262601201e80900380016080164100480e05104150100d00310a00f0f00041000d01701e84c0354850310310395100c035071082c0d01c09031500b0055046940305031650003d40d00c100b120780324600d8444503080e4400442c159 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54914868 1250 54913618 54913631
    0x101a07030318050a020307050303090109090f181109070503160e0a05040c0306030501180210050306030102190c0507060f050906090a0b120f060d0b010b0304060912020f011b02031606 80
    0x1410b1004035404001264140c00000444043d81341c02c01909003c0c02040b00a546080c40500c00130b03181c015103109400a00341c89100c5005604869400000702580520344030061012034908141100c20a445c0c2912800141e4003040c081072003207003581d00c5080350710506124041c0303071a010391340c41c0002d00c50684e01820010b4007243c15107071401001c0301c603103da85012032401c0c15450000d0a60b8906078404a010841c3d00c4503c002d42c1d1030360410a05140b05013040d566176120b44002c01e01921841c6c500082c104d030800422800154080c0131860b44502400c15101c5680d140c0f00101d611922940308070740056800e105140c1076240c424004c296640d00109a1960227940c0c0c00d402d101d94010349040d000c40010107003000442141c90204a6004404654100c10341e2265500c60060b42c8040c01200c113860310100c0050204000760b41b016040c242c02400d03c4280b4011044029501c4108601462065081140310a0f03141e60982d07400c0c0c0c050350103402a5040c10015403003a008010105015076803aa110740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54916118 1250 54914868 54914891
    0x50901030e0f0f030c07080c01090302130902060708071a090d030c05070609050c09011509060503040812010e0a0b0d170708071502070606081b010302030907051512101a070303 77
    0x40d03284103d00b50003442d01d503030032920391606100880d800300705a07412050f501c80e03082c0c6c5c1c4600280d05803541143c42003041149a0a4200104401c401c000d40140c0c0000e401d006010141c0c010740342e003601c038181c88250307240c842c2c41c5582c003e58143c8040c3c03860b51024212509160094021000e400540c2c9400f6003885c0203921036406481c1070020542d41c030780004000e40103d05044d0b4901d030240c4169010b514400594520041003507050788941020444044081030811116404442c0600c82080b0401203a507100c074043c0441850694020140c1450b0200060071800c1414800d0708464101c0b002e07031840011214041c07030342d038001d0008a640740010440700740080d0a8620081c0d8140c44000e0040e00c41c50f2515220b82102c07026004102d0b00d40c00020b001581c0c0700c40340c0490070484000c1c80c001da2039031504e410301d600c2d220480d00700e280d003c1d801c4021408464011000b90801c00e1401c24000500d80b242804d14001c40003030701502d60003000f04400d085210145000420b1202e10a20340000c1018480c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54917368 1250 54916118 54916123
    0x509010e16030506070903080307050a110102120702061005031207030e030703030f09052b170408061905040812071824210906020903012a02070303050901030e0f 71
    0x1406101c40c0c10804100520501000304002507008200d42031800805085450b0003506e400001c15100030404e00240c90100c5910030394094103c14000c100940d1a00120b1042241d4404211030810041c898600043c0c88901641e500300c0031100c0140141c107507943c031000a44a141e220703013820340a0048181c2001d501d903e080000780c0c0294000c0d5a03a10030709000020061035003401d54000c40c070803800c040400d080c2c1811000700c1804402d901000c40c04452a519058120010a18039038030070680200380042c0c161030114045209032184041e5160b440c5501202204a91064401400141c0c0c24807052300200080d8941a801646606056100b42c81c01c0400c5003021010350822012901c8040c00c00c643e00590980401c43c408070350814203482121042d880642c00c11640d1702200c1e0b541c482c000b40040c480b0650459521501c098001e0000ca800369600350311041c2044210302c9400d01c100920f8a2143c03021403841e060341d51550710b4600d06036940004501070a850024040207010782d80f40b104030038104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54918618 1250 54917368 54917383
    0x604061205060109140f0703052502010f1b0804020d14030d060501020f060702190212011103010315020a0828050106020c010306120b0109050702070902130e130c090509010e 76
    0x500c000e00b020741c141a0144241d441425408010008803001e00200a15019480d40d100010b490005106d40e2040d10050b158800e4480e0745000d40718003066440312907819000305044054200050129404480d03200d8142c0001c901c182c000100c8d0a070100d401480c1c401445054103010b8a48505207400e00440d103821644440c3d5801d007039541d105002c01195030107200c5071800c8480200680468030f82000080c0d00c8009a52100c80803621580401c0119a00c0c0007104403103100305002008080d501c0e2584000a610a02050f03400314a04000d107034140340c1600807180040d500c1e81e6040e0381502c4800b83c030b5007407682d030300d00281288480110303480081489100d02d42c000c00180d801442480e0002c4001740032a5115000b908118209003548808181d018000034111990380d0400542e950b100301d4200d0500400340c100c0c01c041d0340006102c0344040346881d00e0030305031a01d60007030b00c1e1540c88001c040f800c40350f004c200090071000418070400c040c00700c50b400580d011400ea800800c0c100c20240856050041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54919868 1250 54918618 54918623
    0x11070c0b041802070c031202010f05010801050f10060e0907030b1306050405060a0321020c10050702010f030b01120b0103060b07060504050c0114030c0309011b031a1905010806040612 80
    0x12808002c44552107584050a03803031044114508079060f00c42082e8031060f1302020304290000348407020180d100754045000f4440c14a010030555840300d003014060801516402061600000840c2e540d10341d64646c42c0171120103848a12880d0445005d00814000050052050550360001d8822f42d856880080c031106070b00d0200018003e0401c41040103c410181c20396019100c600c200703000140d071182c80c4648915600c801d20114442055049141200249804d600f142440c0b0484148540040241c03400754801d880e950f8000a51120442c111040c00d030419000480c403040002c01c071040daa00814036000d040c50302058041d1a510007450a80c032040d411240c0c16a204200300c01c1c40070500034401000c00c00d19000c4c2d83c40020254854560001810101d94040300101140c090b0000b5800355010140d010b08130780748150b090401074024403100c3c0444106240c4400f09265a00e41031810f1051034003040c5c110f40060342000011551074400912082c1c00030303501c072004181d9118818440c1400361 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54921118 1250 54919868 54919889
    0xb06040906082a010912080409020a080a050c0a0801030305030402010909020a110f01020702010c200301050c0304030f230711090405010c09080102031b0309011d0607020d0207081011070c 82
    0x5003e290007040c00c68070000b05208044010500040313aa20550301000c980c0003c0340004034582d0fa051000f85441640c0c00640b0f403503c0000c104015507044420f03e48114007846081100340c1d1256841039452050701550300011f4146001070001900602c040c2d80c1245c010f00d080c613001500c0e50180000c90b4440206140407558a80c07108682c580100316840d5071314018802075007080301c1d07640041d04403c0b1103100113018a000c211003e141c0480303101001151640100240400c2c108040000c0d90355000340da0980016850a08041b0054040c1d0401c040a142c115081500c05025003100405600103640449031300030000004c00c00b968801d20701c81d01803070041e00001000e540945014100046070303030140350745900500070440c0c0d4006065034411015502c00d0880d640b43e96035148113006028920413280f02134407888041d100008001030b45845034460340c080b140d0b41d80d9072078416a40c1d41210b20494150351710294081140404d41d40111702d10040032040c01d42041c0c0309990b0031448130680c0d00300b2130340314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54922368 1250 54921118 54921133
    0x60a020c0a031b0b0c150603031303030504050a0803090904080a0e030a140105011a04091515110f0102040311040c02070515180604030201020c0909031c0902031e060a0b0604090608 79
    0x1074081d80c00c0c03001340600035100c3e150040c1c02044546407007100c1007615583e00180c001420740e48080c012910801c1400d00111043ca4592034050b00316001401614001c4140745808100da4200001b01c404070030740204640d0040c0c1d0307295500605507114200207000c101c0700c11381088003620100020120303248280203120007000100d07210f5084940c140d02440400d414007181d17920b445c403594111415103100c038001092441e015818000c05080c2c0b50b000da03001c1c45003000d01d034008950002903481489440d4003583c0c0303800100712103142030780107030b001c0540080032403c2110031514099201420203511350065511544d030300d000003000c418594500b42c0d0318071400a84c40804480c04020f0b040340913001c40e42d46060a01310f0700000e507070b1400103805500035002c42000c1007030386030104280e8240e50f400e4268840b690200b106608084e05d00c2c6401240207204a040c03c0600c101210032100c54100654001e006650301c0c1503203900541601d06130b00750007140030800421140300b24010500503049050003800c21 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54923618 1250 54922368 54922403
    0xb0d0b160e0409030507060c0845011a0609130e01090203010c02100b030d050703030507090b0c0102070b06090103260706090305040e06220e42060f060a020c0a03 71
    0x68640981c4034100b000307511420480e40d084114240007030124a4150141101d50b000c0c015142d0808250140000645240cac1300c52002d001500000c03419140c032034034810350141c42c50a008450041c112060fa1240e08441000e4156806900560310000c0c02000464010f14640100b4210b510401c203074001130b000100f00700030340c0e2914010003411074803e50081c843d502c12080020f149028880e0020701b019181c0000c02d10f070610403200f002c0605007811401e03030340e00e444c032040c01d00030340c0400801c668021032940081d03070514003c914503049030340201036070130000303503202c2c033303d031008200c00020a4040d00c1800780d0b002049044c40340c200807a10a071541c541d80c50030113420001d010402088944100c06d40c404e14054104032030003520385002008000320328085188016401c10010051907025801800300c035a50811548042501482c01c03543c019100c01c19034091003910440803604160880c0342481030f00202d05004004081c0056248151900e002d400380005102950300c0d4416a94103009030b5050a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54924868 1250 54923618 54923621
    0x1050c01060e09071a210c0d1406031006051003020a140331051203060d02030a050d0f0810060e010c0605041109070c050a060b0f03100f0b0d0b160e040903050706 71
    0x94401402042c61300b0b041e041280780d04002c05651b0020000700c07090000c00c3c90b0300703511401d0b5464074100c0241070121a90045034008502c0303040b06c115100e4810b01c420b6a4922109205032001e0703c1e00901107440303450382400c0c00d6010354041209c0e0010000318a205100c4482c4441c05180a445400c502101c1186e81c101d0f401d000354080c14402ca10811248500000281d00040741010345940701c90107a180d60b02d40f40012084904400b001e505070003500380742000c110000c0342015440c421034842c052502035071001202c4100d81101c0d070740340d40d800d044802c0c060640140561841c00350145850385260340982d8610064607400d031000c40e00c00781c6079001c3e2100da140a51300c4561000491401550318440d94803200d40d00c0b0290403002c0c21460351241c20401503216500d0001401c000a000c81d904682c0c014240c4004010321a001843c0d01d103000d026503240d10b0310503410071f103017a00190020025103410600342d44112440e066102400982d4003510041c1c0c440d40140d00c4c031540252109600d50001c0c0c1030010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54926118 1250 54924868 54924899
    0x100f1509031b0602070501031a0108180a0b09070603051909150903021b010f12020c0f030a08090f150c03100906060e04060e01030503070b0c0c0105010e01050f12060601050c01060e0907 81
    0x42c185400c151001021a2614941069942d024604417040d41c840c00032000144140041d621040d00078a6800000d0000ec124042c1c000c10b0180200e4401a070340d008100e084a03000e0742d4210a104071170011414441c010740107018414001c044011412840c01000d0049590400080780585c0160b42c6d40810401c1107240c420f1401002e01b03180c008085041c200402e00e0b02e080300700f444510740c085000040700004000111550078070b0811266244034001010742031031001c64141203603100354003000d4039421021400800e181030010031151507484d082c0340300e8410b4000501c1c01006031000780c2c1c0000c0c4078105003d00401041c80703407218808901c90300d0900c41601e0007500b108941019000c01000010300000072280d22680001c44420113842d82501d910503441207540c000c4240d0700340710000c1019680c04038458121001141d0703e0124074009410b0080d1054400300789003481d0410710004a0950082008201041d04140002152a1141180d501c4074070140c4001d61540e1050b481030190f15a021400b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54927368 1250 54926118 54926129
    0x2030703020d210915032c01090215040e10060c02010f0e13020315041b0e030312010b030a0c02060403020a06050c07020310060503010b1801061b080a1106100f1509031b060207 77
    0x340701e0840e48143c10756400e61f1040750303810090ba0301d60703001140400030f50010803103950080c03103400700b0510113500640b43d0b0000e0149ea003035040c02c1004141c0c2e41c08400d1050048541c103450301644900d890b00156035154a1094140512540888401080c2d83c5d401000070300403275103a0300507200d050541110f10160304030740b0024000d900d005680003a0101c0003e085a07030b4011454090328045040000c80d065008030442040008040e0001054008150b80903500c24010510200b1880b00a4030040303984070300550300a0301582120f154800420340580001c1e500038100c0d03105a1900c1c00c140e012912740007140700580783c09a51120140545d01d42030060810040d0f04075a20046000461045034158506108220501c40f060b2654040580e43d02109084160000c901c03c1d1140b078240c0f4050900e20220060401d20702848000440d60441c20000c1c130300780c0c2d82001d035064105042c251480100c4440c40340b090140850364070008006100c040309880440041e501c0103c0b030b240340940c003915107040c6e604207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54928618 1250 54927368 54927371
    0x9060702070b030408070602040b07051f141602031e070b070905091618060e03060609090a02010c140f1c030204030803221707021201060302030703020d21091503 71
    0x308007041205068076009504661100c0c6e540350b0b10b00d00710009226650144c6149100070a401c2c060100104154071740c5066008070181855010125004550061040e07268100700310010a08080100e10400300e4960b0382d00460340303020500885091100c000750036040e210400021850200116815041d4010f9070703606103105413605102c001450303218010420385200300712008001e10b2501c130301c0d02072400d107aa269407842c5c01601c40000030700180c0b40f284040d02a00c160400b151050030700e28a06071241c400c00c8003601110445500448104600300c0b130559541d807400c0c032180c048510600002c0c41e0a00c0e40b5000f0200d00c4814400b00d00400f26601496003454410303c410400701d02c10308126070303000f100050a20f00f08030460000c07014110a005002d0f040183c0780e0383c40030100300400c0040481e18000c03208818415000c400d814240e07403643c04001e4041d0400c610030001800d200c1000d040991281040a4420a00c841a4928000c458039800c00040290100304070a8200038200e400c000c071540f40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54929868 1250 54928618 54928633
    0xd0b240f03060403122a030b22021303170c120304020a0e061c03030509010605030a021507080c0a05010203040b1302010801150908030c0a020109081603020d0c030204090b09060702 79
    0x7529504020300103424842d0564005c0103400155009203031000902142c1c5450382c8003500021034906040844101081c0760541d5810139142124248004020084404518030f000072403880c0a5000b02c1c1040400e21700d8200048001100007800010100c5541d0490340c503500b10090052070301c030440d0301c4010003500410503c40075031138810a0809442400110004984a40b008220250b0f810303078100c0c100b07044105c01c15040550503001035000f11080c1c0020301409444504040e1200a0058000d50000005c0d0354080d92040b468081c001850050301400c2c141010b07003004a00b060681c040845250b54000204810841408002900708ca00c80a03440e100651550020304003841c10700607064840601c1c6400b860f60b62180c51900c0203856540162901d5400200000d0b52320001560203d01259143e180422a45000203c00580c07582240500e168945150240f2190080c0c844080e603501c0f4141402002580b65402603140d00ca10850a21886184c101c060908000001e041d1000f19042440c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54931118 1250 54929868 54929899
    0xf060f06080a0b130f0605150f040e0a06120308010305150103120809030903070906030209090d020d03020c01020706020408030304030e0a050f01030b18040c0305010c020c06180d0b24 80
    0x1c403141d1122001c04001042c0c0003c000050740302030311020250320503040080b80340c00441d90f5080103049400c20b40307541c04818284c004c41c0040340140015000141c00074070080106400701c464003600710300c60a40000d0036680f80c0741c0a919411741d085017074011950400c010001c20000700400c0c1c0028805a1803121203505650380e851802441c22010010000c0050101d151b10800b8421a055500c0080407100a00d83e1120083c0140500707100581c410101e82c000a0b02010002c991036141c0c210039405090124820f040a900035005000000a82d6600380200d4002410324401880640101d0004544900c0c083c0b4009001018200110b4042d0050700800c0140e0f80b1120001d80c0260b4090030b02280c489200d4010860b01c42e84800c000450145104c280400e110f018003a101c10740b40640700a2104e8107100030141e0740c44001130b0301c26800c09005c20250950380c1d40c0752005c0b0550840104a810301d038005031074480c05c0443c103a402c0c90420079038041c00714902c3c0c1412110702a081c4203540d14003503120b280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54932368 1250 54931118 54931127
    0x70320060f090f031f0f0b0402090f150906130510031b12090804120209130b01030b090f0f06060a090513080c070e011401122a18090f060f06 62
    0x142034040c0210204488542c0a503130034403100110250f5891108841415039041c0300140079060550a4024900309421405003801c2c0215a0a841c01920380300c2c10300301e034a05200a20b0041d40b244010304505201c10000d507903640c13000303010414049140944441c1810100011250510500d106040c0f80040d4104d1059035444040702d071140c1803c2c100c142802640c81680070b09040c4034001d010b2000014041030703a1600f103c0e011100b0340240e40d10aa180c1d100548104144020782020340301444c3c44004200168003980c41c681d010130103409132031805548440b40707884d2005100c00c282030303a0800300402c0560309048241070014032070f8040511482c2040c042028012018000c05814a600002c0680445808011410007800d03e001000761540c0e481201098840041f030110740091100000110b092030580691440399030303800c101400090510b121050840e040d00d10080030701c2040b0a50041c25440700e00e0140003810300c8400454482034a00a04040f40e5040d003011001c1d00f8841d80a100e400e600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54933618 1250 54932368 54932377
    0x612010b030603030f0c01020406170f1302220902030c010f080c030709030206030a020405011205060102100b040e070303120509060f0c0f071e020316060e041d070320060f 75
    0xc03106519502e4450700082401c41c031071506002d1030700c400000d10f0400e07204154002e01c1100c40c00d81d502c0c070305883c0d4001a141c40c4070302511003e0320404c024010071000700c0d03c008001c0400d4030050280c0d001c1d070b114010290800c085100f4491034159154440c40c250304082c44001c0408009217402c00300c03500c9401000c0d10f501c0d4050712450a43c40c02200080c2980e004900b41000b640d0000d1030940c403884d00c0d0080c08040e50081c005c190005030104040964245103014003400307003078140c01038019203840d05500d000270b0034281c1d0103682c05601c0d644070070301183c0c0a108001c00366000b80d071112600e1412460f4003080e118041e0110720305074012000c001004074459240741d0001011a11070795036500f0300c01011b4075030040f00d00180440b003003d02c0000003414981007070200f591085e41a180d210011201b00348010440b0b118880116060300c03880340046c07509601c07140443c036002414414010480841c2c03481c000c60303034000f220010000c40f050744035a4000c0d00107002c0078004480c032524000c081250b042c02e5004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54934868 1250 54933618 54933629
    0xa0f0f050a08041401021b0d030b0604030210030b04020307090801140114090c130b0a031404020603060607140114071e0203090402070510051f050603010e0117030c1504020a05061201 80
    0x41c60200f401c0005803116000220030080c0290b441c0c40d403900d4640703815174141d280111507108041e1403e0410f4004d020b1000040402030500b42421b10316028003400306a1070901c28105541c030014003c0c240e441e4030107140900c5403503507140000c50400010134215941007400703110008801004211484d180c0300002840c102c00d452100503038461101c00240c4d4041c501d107001d01c204800001041c6584664043c000c03008272541c080c49026026006c1d1400700300b003554040c0d0000300400015140d806c01d40010100f040c401c40349a40e0710100310658078211604e0940783d004243e058401e1200850740b0603001044445a10620703815102c0b0080060f5403803007041109400385030085030784030900a003404a0401d0680c1181706000510301154401c0710303020005e03120f855401c0410000710701c0c7d041500270b0702e041c4c1d03c2c5000440c0701c07070342802d20108814500414032165031001b01b1110440b0700d828844070704001420717806160a4102441002a0304141303420070703030254070180072000080008400700c504491 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54936118 1250 54934868 54934877
    0x10f06140a09020a02030d0614010e0405040507060302090a12290c040608040f0605040c030303050106030e062703070609020306010608040b0403030510150c05010c030b010507030e040902040603080a0f0f050a 91
    0xd604c1482a401d6000301c031000700e0041c1c40e0000005824199032070b450100c044c02d0362091503080c0501c081100701c560540d0080d2081d401144103000f4540658000c2181c1780c802400c3c8011640c1e612400641e185601c902150741c0c07a2030441d01c0d0091204c08480a00000303081c40010001e2038480003204131809030744102c204000e041004682404640d0303940035100368100c00240b0461802d820703d281707203550034070007100081e20f45400010064441e12031991144400405002d01c0d442c2e4526041c280303078524513103604c0d042c0314420400d00d0440410040100902c180404240248140101401c11005030320400c1801080747c100400620300031801c59005915003400291034451114010082c0c1079a0071034a0000c0c070490a1a0304585c03c05c4600550320300c100005d202c00400c03540c0413001d48a103070304a240454814400600024001d1104071034045002c0c0001840a00f50b030001015114150300a4815180000308034400540c072400030000d00d44c40d4201040d002e044410010554880c0c84010810007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54937368 1250 54936118 54936127
    0x20315040201170717060301020301210206120907060e0306010b0f0c0c060c0c0307120308040201080c0f03040804030201030e0d09140307091407110a030801170f0f010f06140a0902 79
    0x5a001e00c07440fa20a00c00c0711040350241c501460080c104500c1c0c40e44c001c600c0d5151a0004810b03140500031203041c0d40602c00221401c0d40040c1012401c40300c808001c0f42c1c080c0c02071001c0800701c4c0b03000440034440e0103c100107241c0700d80703070000c082e0800e0034040181d4000e4005600506c070102c8064111440400b0402084d69909070142b040c6080c0130000c0708a580c490b5001804009280001a401d16401c00807015070b006035540340b109290041c0c1030000100484c1d20040090095030003a02c42580c000e081c650454034004060112005960040f00d0440d04040c010805000b5540e2512556510140110091070004c1e10000c02a01c051200d10924040c2c48200540d8034168406200b040010800d210060100303d400c070710840c038200300803980d5a001800e00101c005402c0d000296589800f901600e501c072a50342170002c100c100079022404076146125110010541c01e030100212410214a04000684c0614403603a4800341c0307006a03c500d4407512030341c0d81d440f15607892050342022149034a90050b40c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54938618 1250 54937368 54937373
    0x1e0702011503030807031104210f1202060703111206100302040e040602030405010b010918020a0e030d0f0905040c050d15030804080706090603020c0604020d0201020304090c03020d051302031504 85
    0x140001031100148040912400810542c200610900170b08090f00d00b48076140b100503003102d4030302551283c41e8420081105401c0710321000c11510408038011541300d04a2207282e103980c242da50783d0f01111401a4456020886a5940340c480c3d0807060007912070540c64141002003040070404d01400c0c007481280303444628007156000303604031001808250000c00c1e4601d1b09080c01d030000c5d04100c03420781d60f035400c2042c000c410358841c00031881611138510382c001c21010001c1b150002504042066010310141c0300e086441035508000140c8110510b03502c4062515104000901216090340242d010790b060504d20960340340c00009680140c0c0c0003000018551916082c0e80c0c455414542c00070f0310341d0a000401180071040030440c0000c0c0c074080e8680c007140c0b590b6440c0c22410bc2c410b1060141c1d264020901003001494001951013410340144100c0e4102920707140100c0840c0d43c4040c3c0803021a40c0042c055a08800a0003980d600c80b008241c220900760698020030b840f040800d010850005021002408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54939868 1250 54938618 54938621
    0x3020a0b09011d010905070906050117090a14030714060c071b0509010f0801050f0f01030b060a0e07180807050105190c0c0902120a090c05010e0402070b090105011a031e070201 77
    0x100880c050f544000c403002d0301c6001900a00c480e400680c1d9501504c0340c0812258040d000d010110342c1d060b903800711024404919525280c2018155074a0b40c0500300d04c2d000402c02c800d12200120742c0905c051a9038240502d0400060030342c0d8029050300d504002c0c200f0080e01907110544101540101942d113a080030300d0000075180752a9000700340d10110600003c41c00780a12040e41007500c291100800403070712802a084040c0108484115505841c44014130001d4406e0040b55005280a4032006801d5241c00c680d4403440011581c45002403c1044844004680c011140e80105401c0c0040c1080509100c0000d00c244a21032000c008054208a8007030b05070b100d0300d84400582d4011046000307494807809007602030350120300c04800c030300801e40c086065410684210343d203841c0d102e541c50009501d400c005441c1c000b0740b07280180c1d00544c00d203c0341c40840e0ba1100a944103500e01400002c65605100481d0311000a502c0d510070604014002c03c03500031640e00300035600c5c800c0d0a10480c1c041d600c10390101d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54941118 1250 54939868 54939881
    0x3090309080105010b040f08030405090a1a030105040809040c0309050c01050901170405101406031e0307080c060601030c0f02030301090b0f0d0311010c020c0604120809030312090c090403020a0b0901 87
    0x925843d0000000e40740c40150041c000740e034854804120718503691110140c2c1c03802240a01c56002036040c003c100540000d900c48202500400c0c0401036080b03103200080d085a9007250281c8920301c000900303000f02c0c0303014440c031489040c807420300300484e14482e202c483d0303603076504904141400b0000862070101c0e8007038529421303000c80c9203100c068546444d244c495241c100c8104280c06070303030030407400ca961150002902c4c0d1003040d01030005c0c9802d1604141400c80030151407485c0390740340070421900303021800301c200030003a41c40154002c006a04252000408440d140342d0f400c1304000840344542e003c6030f4084110381c115900b404000c104245c0600028070390302c1e540060142d1040341c1103000d000301600087c9880e400c03d1040000c000402e038086040c0c1e100d80c03850741080d50040c4200800c1c00101e00d03c03840c5214590080b810641454211000310380fa541c001c0342484038280c10942085113600040000320001d4a055902e00310609045d50065683d10000500401c0580407100188a0080035071000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54942368 1250 54941118 54941129
    0x1c050613050109020904060e0105070807080604090c05040e031b030a1e030b0618010305060604050102070b031008010e0703150204050a0b030a2a02070905011401050307050405030102030c12060306010506030703090309 95
    0x2030010308003440d2078001405045401c5030b0723950034400003c100303030300408403a44281c1d010b0315104a940d2701c0788200801031080c480c04407248121008080346580302d900c103041c5082c004400555071340c0020481404218480f240c03e6289510810004803501e0340031a030900c0780100841040b40d039100850060703010b030600721402c0b900490049280c0014510420100b0180711007a03d00300a02d841310020320507140300714043c05001d03a012000c2080001d580500540c0c1c0204405c0c3c000c541d864031000c03664256001c4001c0c00c4001e512812040c0f0a000c0160070003a108000702c4001c40c0360074980b41c0070528100c44c502ca02006420084005101307a055500440003180038890b11040c002d000001020a2203080440900180708110b404100814140300395416500700003941c81400c40480011143c1e540b0090102c1d0400c14180f00005054a0074000b450040031b01c82002921502100c4d90a80d08180c01030286100c0e901c020010170554071010200c0b6000180c07441d010a40b0916800c081d1742d180c55540c0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54943618 1250 54942368 54942379
    0x302151905030402040507080114060706140c0304031202041503020a120f020408010e0619090804030b01090501090b030a030f180302060403111504061d0a170703021c05061305010902 80
    0x910030694081d0003940b00e036100b19000c2069890300c080440d1002401d00803180d014100f000026100d1800b034003d0015513205010201c0c4048044a05d845050000c0c1d0b06240400c130b021007807204241c1c02c80803500c3c80c05220882141081c0c83c2c0302d807102903141446561800e25500103005440288105e11003131880003418003d001d001e14640f8050025442845002c0303295190101c030881144010070568020340584400d81c1517141c548442a005100000084440040c1048000005030031410b0890090842000c0020150726154124064541d41032040f0b01c690420765a000020b40c011a08090115035442c01348003004221000341e000045030780000e94850008100082048128000c8803822042502c81003040040e12610611038000c50044802203a08074010881e082c031086a820241d0100801c00c90071a039440d0030741c1c0c400e012903460030744071500841030910550030f100402800c41c1181c00c01e40c08422a240e10740d2901d4800c042e1852006489844d10300003030001c01d411507450aa002401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54944868 1250 54943618 54943657
    0x7230f0304050a02100c0b06100c0515010f0e040201020a03210905011e0b090a020d1401030501090210020607120b0303040305030301230f09010306021b01180b090c010504030215 78
    0x2c082d907640016901c12440748040840c03411900d8070902e4204292603120004051507100d074010000c100ca1556000010000803d068101042e01000400e515600c0b61203105515414080a01e003004a150042056010360030180310050b680094000551905880d001e000030340444441240d09034407250814100e82041074440a0150641c40302c1c08102c80f000b40040d40c158001000c200340d4a0350100c0f150700c07c0b071210029424480c5030b00186070f0354180c400300003040d400f451080c030f00d000d200317030016681690b65902107000c504144000c40804001c60004280305e25101100174441680b109020420607101d240600e10f0727440030400ea601441e4400c05907501d070b42c1c45804440710220300403500d046040304000c6030a15070801c8041114024005001102684e00315218807003e07500500f220000300001d03000300d0301401e070280f01d1035201e0014848020548242c6082c10880c035038000d8005001e64105050170042e90380c002003102d0440c1d9056900c21500b983d541d400d000719000e0ba03202203466008100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54946118 1250 54944868 54944873
    0x409050609030c07050a061b0609081204060518030406030b0102030d06061e03020f180d14031b0f190309090f0204030303060b070c061404050301060b030609060907230f0304 76
    0x141109210a904481401740d55500f0026030b603107036104240120b900240001d5469083c1e0200044e0300f8043c40c5c01160015079603030303131280950152008694111011062104201c82c1d0b003e2503400005891442c5440401c01e40c0a0361684075600c42d181c18956900380403078460b4028010703180f4882e901c180801c4000d5503080c024101d103030b5059040d0302c543c0c1410a00c11000d4024800c1e40c0d5443c1406060b903003010080c0d061147c1044e00c040307202da80000031a40c02c10015140b1481083c11780341c240061600e40503481e021040000040d02e440035145c00c81c00c0340002160000840d0440441c540e06440060102406d0a440841040c0c0104008504021605490307a2081c1c00820490f44070b0341d4104271141e41c031400300860b070040340d000404664101c80304000d038511401c03034000e4000300d800d049864644c0e240700281c00c40b540d030352010b0701650000c8100105071600410144c2d001c8801e98082d0041e180004000301901440400107410411800e1207584000b00c1c41c080d00e640070317180400c241c2d890a190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54947368 1250 54946118 54946123
    0x50310020c060606030c0409050712020d0b0a2108090f060301080a05070e010e0f040c0503010204060e1306030807060203090c04061d10060509010e030a06060b0d060b0403080909060409050609 84
    0x1103036002142d201e0340002c5006400c1c0f4604880c0302e0710644141e079083c00d04004041c0c0190001030b0115081040c01c2e040116002420710081140c440c6144000a40780020f409204804e846a804a500075522043d500509004007045812207944000703003a503500130036000248050042c01210350044000f200106254100080c00c01107035002c1c1d021108029640c0142c0540c9800034010049041c0341c040100d1005802d143c2c0c141e41040c0716601c1e4054040d2114040380c2242c009a01c0040004e0500b40301c0c00d61414030700e030380c40303125645010248400c40c00d44d144c84603503110783e010040003117a0000006135450302c00d00880c0401d110051080c801c09941d00c040c044c3c980700c540900355903441402d003ca59a035076450031140464210386c0b41e0504204003030005550810f070350342c00300307401d8000c02d8580d80000d1914400e000281007890032041c1c03140e030151803004c1190044d410104054104001c00d0000c00d80b00001e441001c0382c220b0341c018480d134559012801815001c84010300b1480b98100740050178030003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54948618 1250 54947368 54947377
    0x90b040803090105090a02060a0c030905060f04090b0d0201080105150903070e0403030e0a021c0c030501020a0801030507060c0b06040207080c0d121401290f0412020103142e05031002 80
    0x7882c00070320007501e070505256210928440c000754014000c0101b07808441c0075409096841c0c0c042d0070812892035540001ca03400d039014200300b8600080026040c03000750385030301c00e6115403903003070302c8241d22443c090740041e2500c20706001c2d007442422485402c546005003403088071002d120140940303d80c1950b4404c6183c100c0c00a8808402090406007560320b0502d0024140307800e0394000306070342c100700b00109034032141c0001d058083c0c6891051540c0072022030f1303090006000020082d0340d1140036600d1400e2050a003c0d594004c0c800f04803003800072101003441503000316040700c02200e005035120f50524140303015102e0b01140440c18020031015001958124200301c4c10300800e0309051218204158000d11264402d024803015240c0c000714001c1d601204003a641000c0161220341d524060501c040c100b0180c00c107501c45004d9545075507443c8115680f5001302c404403100501000d54600785030128090145040c0f211072042d120800305a00d4a0b20302c1070040c802048050180d4090044240380000079600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54949868 1250 54948618 54948631
    0x305061c03020a0629010305060d050a0b07080108060405070b09040207060903030605042f0705010212012705070203070f050c04020406050d050f070503040f11060301061206090b13020706090b040803 87
    0x80c145c599441910140d504c8504080910031501c84450301c00019001400b0280009402c421841c09900002c2d41c00c03c12204603901078851519280341005004014000582100c84550004428000080e04c0090305105581424070182d0702c516603140400c1c028000c030100508190300380317000103040c1609948904280d034816607082c400162640140e91040241c0103102e00d8188901d0a80301c2c0a40350100504880c502c1500098504600b0f44101100381c0c800b03030030848002d1070303158074000e1111000401e840d206040c42400d00c1949040c0d517020b9104d00404d80003410806444052504000d02030007001d031a81002001191140e807500b20017405c9030448208000110314090106841440310080144180095600c003880d5030390369a500d550f125070482e030446480d000a0080d92240e0348502c0614040e003003e540307460745140b0318041041510900d41c403100e80f540c80d0100340359598880b402103901c020110b4101603507030300032440c00c00020906c0140161080001c1d1081c0000c00c14081c000310301986 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54951118 1250 54949868 54949871
    0x31e0a080a030b010807030c050a0309060b04020310081504030c02100201060e070207050301060f050a050112140118050f06060d020a09050a0602070e0903040b04031106120406020306030d05040b0a0305061c03020a06 94
    0x9039204007d07000c4445189184001c200c0070b00c001c00b005842070304030120282c842c4802141d8108071001040a9801c1650300303074049815a4070502c09000704001d603070164803001000144130300303003900d0140c1188150072001c2e000e1912540c0000d1000c2c001d4100e0001044020358050302c600c0c124000030748a00d01406243c0c480c5d42400720000b5030420000d00342c002d50350014442ca842c0c0785442e00555100c001441c464000b96294040c0301c0b10b60018003c0d0b240200341026030303162112503500e0900e04840d8020300884403070080d081449096103502050751408104110016a0b6041c1d0000641d14001a6440b041e400241030a010881a5020bd00b0b08210395840c02d4040d40e58440c00e410907200e001c1c42c002c800c1a00d0040c4010404501003032040038401d003002e000c03a858200c001034810190f0300300b15000d5528940000a2098905080100c110310001e10324109092900300000742d02d4500c6244d505100301512480032a403140c2d01e001c00c680d0b254180c055002070240d00c0d4074002e912060384810945609 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54952368 1250 54951118 54951121
    0x3060510050a080304050103020322050c0f180402060d06050a08070f150503060402180301050a0603150603050a02121f090605060901080c041a060f07050714031e0a080a030b0108 78
    0x14203100140b20255142100650708090410004400940005100385404074220209138400e03554860083d81c1035000d880500924010030701403200c0300072007080c1133009000b9816011021412084202e8010f941210320582e200c190040c83c1c8050402334202d80e9125a20003000500c01030002100380482d248041e880107020f92710507145007120540000c09010a4081001075658034050340201501c0704402ca441041d0200340002c02d007101c004a43c1044640d94491003031052002d00e1204000c07400c1040e40903c03401e07040da51006e440303510340b140c001d0040035180c24001e495a824485410860754840d40020342e5040e1500b0403024080084003a14030501e80004100305040802c1e00a050f80c000000810b801e1104c1000d0100502c070078544a1890b40340207010030450b80d1000c0081450140d000406a00e41c2520b0078818104103259000c031120651310000f0040a031000714004dd0510019201c4040b040c02c04c0131160300740400344800030610700002441401d90b42e0140c0c03154600690070398a60f64103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54953618 1250 54952368 54952379
    0x2030910050405030a140703060c030c09080f0d08100b0a0f120612030f090f080703060f05010302150a050d0c05040914040206180d150203040201020607080f0408210103060510 77
    0x6600c2030740141d5415170444005040410007895051000807000c80c100c50089a503a101c2c4402c03550a090000c0019495450031b400e42a44281414041d14408000e0183e40107480000741c0c4c2c40c000340c402d080500842070f000802c12840308403050000c16003810000c0c1c0d0b401109200800300500d0658000101d10309002c010003079681c0307201d80b03030545140c1c03000201060702644040d6542e060700c0c11442c080004e803401c013040a03203204118000a00000009107034843c1145440780c29284000114400d0074900001040035075541010080c09040c0340c0c002e00d42e140c04025048850b48950820703101203508102580c03003161b6014006004aa644e03071420000825010781d1000100400d0310040e602c24018031140c060260403403251102070000805411154845a2320b0403030200740045807601c3d0f13981c080100420355030140829030b8000d0191811554510700003001280b45c802c00b400c081c1c40040c0114114107043ea4a0540642d0002211040c101942e50303440e00303e0103040300710741c0c600a201c0c4d10740d0000745 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54954868 1250 54953618 54953627
    0x415090b0301120312090507030b10140a060513150804060b040902030d03020a02070806090703061113060c060f1b02120a0c111f0504090c050403030c020103110408010c02030910 78
    0x143d41045804440d82056520201ca214444448490b601c9685405000000d0f0f4104200e4004500c581c0c22403003a0300e4003580c43c2209107015031248041060407542c0d41000c3d601c03440e007002a40c0c4c081c2081c50b104c0205030082c0405101d150000c0c1c9100340202c401d0720340d0540048100740b090380305880c00d20550091006100030303183c120400a401d5442104004102406600541500b44c060710480700220740c0e520300c1529046080e03070744081c581c101c042d003803051040d240502c403410f03003079441d0b800c7ca051001100201200420302c5100104040e19000b04100300d0a5000900100400e1105000c500c0c44003d80341c1e509484c0c9030400c0701621840f0480c420300c49403a82520000e005c41c0d01c40c244020350a4032155803d00b0000000c43c0c1c0140642e42c0d240554001005035084500702d90b0701c83d03880b14107201200044030500a4400c040c0b003818081040001c0c3e201d1456503d04d60f0a103030100c0c0ca0304480b038000b800d5005a40140f4519403c0405003941c850b400006004400c1e0100c03000014041501c5040d80d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54956118 1250 54954868 54954871
    0x70b07050709060e06150c030706091506050102060a090510020301140103050901180204050c0f1204140303010f0312091502100b040204300203060f010303020c120d1101020702060415090b03 83
    0x100c0001020005070246012488403100e0402050f031b040c944000d8111440c150740c0700c81b5003290f0701a80c50070b142050251f1000c0042c0d0035440c01104000705810480041c0d41d07108010710100103152608205010004c0a0024542034509100203540380d584a0020380701c1d481d03495901c0c60000c0d160000003902c0311814010800c21144a01400c59110340540030300002d844020034290b003c0b02c04202c401c4d13208964400410b150301104e00b000074142440d240501341c4560074071109034298002d20040c4803891304984003c003125070100d0790b4041d0080c1c5580c07e550030306190303015920070203140f25806422030700480d0300b20f01c103c070f0603204000104003c0d0401040740941e01a81148050b268400c031110060107080c4904520079000c2c58186a00a44c00a407428001310f50700b101c12140c1c000100101a01045142d24440c01220005001c080500c2c086599490603c500020803541200e5034810100a504440040341c01a21b03030f40da240d40300c070100b04a00164035051000121851000a1504110816039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54957368 1250 54956118 54956129
    0x4051e07030902010903050a2108060312070221010e1002070804050f06040b07051b0906010804020f0f0603011725030b0403030209030f010c030c0201020a021c0908070b0705070906 79
    0xa602925500c030100c0050201c510128144851000d000c0301140c1c00304861400c081c80b5405c00740440809980c8113582500380c0c0c1c507003c14091900280306999402047c6490600c401003c070581790310003400000c801900d40d10081c21810124a156202c10606400008031004801c0488566a8200d602003040307224552002c0c04203071040c40140440d2401c0aaa03106c03803c801407000d418691070303482d10b201e10b0703102d44400ca80d180e00c800c58000d02d40e10840030f03980c1041c0044401da10b01e45000400601b40210041000348200d884213a002071565410301c0c8828517500c0504925202d6031640200b4136401e03140c681c4852148200740c0141c01c0c0601c10188240c1048280d51121481d52844d0359540b80150040d004609142d020301440d502600d0400c050802c1100e4000040f4015070010800340840386112801700459004028980003250009002800708059528000819111180440380910703d41c04c14030f828000c01c1c400240c40300d0070304080c102607805078099844480ea02c031136900844801d032194 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54958618 1250 54957368 54957421
    0xb0601020703020639010902090601051c09141e010e0604050706050c010b100309020114031003080702040b06071214070c05060a03091202030a030b030109030503060603040c030203010c05090405 85
    0x4407030030031100c400170601855a500100c4040e10b0315120042044007419606400c0c0e039550080141545050710440703411031000e0a02e00d240c032024070703e6980326680b072240d0b19034000d803509003141c10408002400005091a07800780c84540003500c0441c0c1483c2d4803071340d1051066092412140c810785011a0403170007070350300c1f100070101070b407600c0c0050718075030414821030340b1556982d140c559194889208030310400800343d40014901c1c6040c030000d444510702014180001c0c40502c10040030409115000090b01e41000c2a10b448105910002d03000d07000081c0c800b0b4004402003180e0b02040385401c4201c45100072501c45400e1040c0a84c00400070303004125001d0034460b0040f000300110304000004214030405842c011814200d80d89a540c12064254209001a400059940445e9501d403007500c052440c210020b104036130b003545009245000241490780309110000c0400c0030014817a04020040d94040c009021140f2110005802c6400c4000003501541c1041700040076a003401c14143c43c986620801e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54959868 1250 54958618 54958627
    0x10f08100c0819090804060507050d0305072c0d0b01030c0608060109090c0e0910050f0a050d0206090a080f03030a0e010b031c0201061a030108210301060e060403020409050a0b06010207030206 84
    0x4035816042c154400741000683d84e8040100032030140c01c001c10281c001d0341c5400d0b59814803850581d1405103c020940200740c501010701c9a55580200c44d41d0000f002414083c0c0040000320348c200303144941c0d200250b80f20120285460400240900160482e030044043c024181d685d40d20030341c0d800c60f00b1985203000a0075003c0510050b43c66a0054000030458544544c0d01110718000c00c41d0308909551010744d4201d444010031692401503010b080c9900140c404400051030300010642200211500a105440102d88070040e80c8500c0c040c2e900401140c0b08079504400018242c548aa200f6140c1c14106410503000340d00c41c40050007054a03120300600207040500e4070f40410703c0c100864106280c2155241da5001070001c1d044031030741c8400c400301c0d205156a03516180426180c03000e50b10400d280c520144812059070201201600d04444039418110254090180061031501c034607040290711502d04000030062100010b40c00290a1160410080c01c1d00c500c0700582c2e440c0c0d410300c0000d510600800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54961118 1250 54959868 54959881
    0x30623040605040311030d140612070911090a090f05070311030712020f0a0306080607020a080316090e010305150604151802130b070b07050f0304030309050703050303010f08100c08 79
    0x103108543c0103000e03240034074000030002002c43c1168000c101c02d0f03811949601801440c41c0285501a030040001c681003d80d09081d02c00300d907140c240920070780c1c5103603942c1c2a1019420f1210300440741704041c000c040444090b19010b030900203180c0b0010900d005442d1800040505000b80700e070b064083e0603440f180d400c0d50740d505002c4442c005580c40c40741d521a028011040c9c3d480d101030103007101c11410b480119010741405520342ca020001041c1c0006c41d8840705500d002328410100303d94003c241144440c60035214000c1c203981d451010340c001036000c01004000001c0c4000801e51a07040074800000c0c0b482c9882d4101040240e0f031450040c040c180f00b1011041150071740f101d445180901415602508002400c0304068000c40740c1d030b01407904d480c0e00141420070881c44181c226880001410103906003000c45103811039a0100070001001d1503a920090b405000d420040c80c2c004540c4103084a0b80c1e5a1070301510382c030301800e03441041d440d032040c400707181d440300303003d014000c41c42d42141d845018070355404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54962368 1250 54961118 54961121
    0x90309030f02130f0f0e03090603010509090a020607060b10030b010912031b210f090e09031314040f05011d100f060503150306070c0201080903160c0306230406 70
    0x200e0340a503a034a03a0f010f140010740180104000d4032000040c2c01c6543c100124213498642002001b580c0080015910591b90740c030642c2d042d5803059840d14800d607903202200303140810b1340101a60101002c50150304000312a04101d20352002900d502c100e40c0412030301901511091907000380850001380003030140c40e908041404440e8040c1c076100038510311a40b003841034103050003402c0e01c0442041a24100c110480c1c501e003603410420307191500d06407104c918003e102c8403ca00864420200340d03000b01d880e4141c1002a5003035114070480d00e007041d940e245045512019041401c0d0f004505002c01003d40d1a4030f8403034075040b115040102c00c2241081e9a415000d4400208440c03d084c01030000802d4100e1a004900c0c0540003a48510781d4a050003600102d644d202d01c948944282d04c0704041140719a4840790101c14158203080c0b602994580301409800c1d8050512440008035203100502d09005004503020200c0e405402e041280b104404424281d485502c030030080940c41c26404900014140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54963618 1250 54962368 54962393
    0xb0d030215060118030510060e100e18030325030915050604110307020303060f0907051615140103020a0803030c0315010210050a021b0f1f06030503031006080a09030903 74
    0x503d4018418480003142d10038a1460b13420503243c5600000c692500045603108140141c80001000c00c9d50349400c80a055101c8100d00801580c480e03a0800f260b0b15070054522014601640f00a0f240c40780f44c8002c038440c03440710328101522010002400604824024446e04403016048030240c142400c44070030324005020701601180e04299924581c1e070344000c00e0300207180294540e41c06076a507801e01c80d041001c0c8030300d1708030024410440c0c0780a01110540000449a150b40342003501500116181451507102e559039090360002c42c20007081001c051212104e4606992007100c0501c0070a486840c241c0d80ca002c21201040160b1081020403291021400340305c124910500c12140310180054001d4140d5078191000141d880d00400c0c11066141311820051420074130000524840c4000001c00e41d4610b0440d0300308034000680009103440d00101d070004d07030103980c105040320740c0e074280225500382c03e01092052000289600006c10801032480c00781203e1590035564165019003036490380803100c41c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54964868 1250 54963618 54963631
    0x30c050718051b3c07080406111207020103050406060b04061710080a0f0c03060609050402040c030c02070b0c011d0c01110d09030602030702011e02040807060201050c0304060b030f0105040f060b0d030215 89
    0x240c1d5031036a000139440000c101301ca1241d50820307101ca11f090009070040c040c0d29000803941e080032100301200440c03202030b50b410303d40910b400b185549403424040010105c6801500c52950005004141c03290070000f501401040101404901d42d1029a000c1508642d070040070181c0c0c0108102c14086066944070303480e0a40201501c2018540c0c03030741d880c0111076031a40f0850b00a6103aa00700800d51400d03101c1c00c940340146013004c0c40516003412009440e00b805000d840380c010340215200400d448258007084081c194038921020030744049440542c1c500d034000503a030010352a16803042c03020001142014803000d82c0d1308d41102e280c3c11903440c007020b5080109490219941d64500c076100c1703854850050303d403104240005a41c1d90404500500300340c070036000321055a04000c00d0103200381303c500443e503102d9040350740090032016050000f070034001c45218019041d0308090600007031207004644000045c3c443ca404103c104076480901c0038030b0211b4a409400b5800413992810122850802b1652003407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54966118 1250 54964868 54964957
    0x1f0308040902091201020d0606090501020105071e0c060e0604110607050604020103090f061a01020120030a0c050f0a0306142b020406050a0b03090601090b0d030c050718051b 76
    0x144c0c001512800ca0308210180c45103180c8510040082d2070b0081c400c40c006c0c0200f0320003401503207003009028103e01700c0c2040144841020060031034550b4810f031110200340e90f00490500030702d007449100d1540c840042d54156822554ec9180481900d840d004070f0744440d40c4a00a803190f0340d11600158000d058450041d28003040c42c00990700011914444c0180101c3c0d030700300400d00000c80c0400203003110307448081d02d80c580c00021a5052260710a50682e03a2011481e80003107802d00c0301d0b00f81102c86004101d603600000101244948595416800c030300b05588100f04514215003110703040050b008038035400312a1a8998002d2030103104658424030780150f0010f0400300f9036660704d0000c2001484540d000c1102d500000c028400d95041c01d10407a0f0042c601120140b0620880f6400100c24000b01180201804103800301c600c200b180a02608004084104405003014400d400400103040f00b188e4801d41010304800340d80c901c94604003900d00401c0c621105845101c01485c5900420b0901c0c003d00d040380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54967368 1250 54966118 54966139
    0x2a0207090c031107050307050c040605240c16090c0c030804021309140c0108100b040e07030b04023705220504020309070302030d02070602150c070512031f030804090209 74
    0x4901c0074020890144540011b599445650420340d05280501c2c800510803402e040040100703981e0010f1080d4261251209040c0b40505034040031964481d000016104d03000e0340c01c05202080030f6030028001c07140400002e0100059260341160234954050004000c14a0300b0301040c094100041c01c50a18000700c000001d20840031303128010000c04d003494240881e88040640ca01d6560300c96001034011040d6941c501c880c0d410102802411b020368081e034130080340ea03500001d51292080e0052185004090011951980300140d8100041d40d140b0002801d00100d2030401e842404035140010480b080d643d403242020f002c0e107080000540302031038004d01c000c0b11900106056440c1d100171070190f0304080041c100c0b0303491807040c1401d24407802c40050654010780c1041014613008208e42d2f41c02c511000e02003100d50341d042034103a503034028010064034a00c40d00c214907600302c40407070081d80903004403101c07822100c070900341141000d000c03400020300f0301d00248402c200c0990340d42c01801d01340000400300c5101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54968618 1250 54967368 54967391
    0x11217180312030a0e030403020d020603040213060e101401081603020403050106090902030c24070201090e040b150402090310050a020403140d03050703020a05070308061201090302012a0207090c03 86
    0x284001c5502e4102c408000000b072214845807442021551406640607508051460300080d00308007290380301a0003804000006411036503110084d03031a00d100810100b000a844541041280c14102d80c4034111485c012030100b00040031a999140c130710b60594900c0025079418003101c2c0c010402042040901d03409010110003e5020b000ea280501103d013000541640e0500405103003c140500e85400342400c0455025100071084c01402c050f0481008540e8034916031004880d02c0c00d299000901500b411420b00041041818100303008085100035800380314480000c0104070300ca00c800c110351590200c260b16035951041d4010941c0080c8103d00141400c2c0d407600ca1072060842c42115151a80003103800e181210307054400c55030800064074086045ca10501409403c92003008800f40c240005200000c046a03035a044140250107218000c0c0040b201786c0ca0040d018000b00200b4000c1c962405900d6070600c07400f0b412070681600380d40e004181c000d180ca03241300e0051981d807800004064031003052510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54969868 1250 54968618 54968623
    0x3060806130201110f1606050c061308070804120302010e01060501210216050708060a0501030c05190503031303140c0102070b03071115010518060f10020115031202060112171803 78
    0x705501600d070806d044002d03094003140c9038002c10701f804800d11136840d5203000003450035440b080c801c090071100c81150810303420070b02441c0342c02041d0010005011800510b40a02c2c0000203100303800074402e0205e0024038900741c540c540a0f03035001170078080108032402208111406201207000e00113140c0035444480c800c0000d00036034107503000e51002e08104440740c02007181e19800030000300104499415566030310017404484c41698801c540c071404015555288080320001454001e0450b599098411007440b2440750354401a02e00131130010050068120100d0016400340059020304440d600b803265843d8241c1024061300104002514985858103003008084503d00003443d0001140d80341c9020401c0f90070280c03010704075084a12007440307034603111465002c40c02d80044802d41c1c03040189140407401461004060311013450000c1001052254248209540b906150f0981341c160383c0f16503401521045210300144107150161401c041f0b4003040c800f5040066030f0404910443d201c0100191 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54971118 1250 54969868 54969883
    0x23010512010b0307020d02010501060c02060705100f05060a060516031803050a030302030a0c020d2a150b150304052107020301141f06050d0903031116060c0306080613020111 76
    0x2440381100105102c03d25404006d4003600904500c0240229810450006c0007040114402030043c40045040b004010082c002039005000070501042245564180c00f4080c140540312107000f14050700700406c207944140200c035008078070403000f9a10441d145d40c040742c0f044046055004000c145050201c000391050103070598650180d580981c0380d081030b0500b64211a070a42220055511144644031b80a41102030064070041d541441261212406006072603110120b5008204181044024075800511703400080c038082c0503520b9004880088001c4000c41c48145c5e070260041e404019409508200900c1c81490f900f4030600690621806601003420344251030014456521000104150001e440c0e850504180b410740014200d24640364010340389107d0401c1d410b4006071200040400e242c040d8019606c0501126800c65485030080d9000e014010007210480d43e0724200418242000d110340070703074029100b881c009401a038440c1c00404030000240c21040f81805103070212650281018010031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54972368 1250 54971118 54971129
    0x1b0f080c0705072409150f0305090c0409030c050c0910270c03090218070c030e041b0504150306030b010501110f1009110603040c06050c0705060706020904152301051201 74
    0x840c101309000c0320182040219410028081c5090000b0b04070441d40038900b10003040803428006015164040034608155100403410741040c2840c0d000710406a001d0f900401e00c50140e4142e40070081e406082104020094030f50001172081c20005001ca50526681e0011819080b802545280c0429000b0400c1c0d8404c6100c07400800d649607091019804c2c4a0000b422261200d2248401460850340143c01e0b41264400030b01040784603809400d540c0c60b20360000e040b001c40060f000103070350741c01c55000b02198002d00500040440c0c0400195000c1e000f1700510080d00c0c0e10507090502603090000440d4886007101880d85c9501c2020401c4030300c410140f1000951112150002c80d909005003450000c001940c584140154170030020000407a4000c065002034a0140ca4144da4480c2e64580b1280380801e160807446d8007020004020041204981c000c0c003068070b080e0380501c01c1d444d4003200110106650721071001006a1000b00318152110090842c6440c00141040e50130440402c0c0c0f88040c003007090300007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54973618 1250 54972368 54972419
    0xa0f0308040506070c021f0c020a090203071209030c06240b03070e060c06070809120307020102040e0105060c0706030c050d090507140907140a050705101b0f080c070507 74
    0xc1c002804418007556030300035030724140030310f5184a03030703020406924030001a00304043d10303003203015000340c46040d540700c20503001842081169101d1a11000940c03007540d80b0030100c2e802950340440d540060241d40c03c550b80544810164050356203541c40909018204500c400348642120010316989016440140c4804101c050f11f03442c0ca07920141c03d10604c0c5402c01e1040c4d00138002134401d28000944190b2224a6241060007030b1a606270741468142e0100100c4021440031040001007641580580200c1c1c000710403500041c1d0380d400030703c459841013a2000c000741d0800751082c0329241c02604040e6044030136140107841c21002840c220100c86800e4403c0300c1ca41c001080070010002500c9a14140034402c8600700c04500302908054403180c8030384510503420384046919241e0034094003d46005503040400d4403441d61140381401e000305943e41d4007139196031200081101c2c0310302c14038412243c3c0c1e20544802003152a41c1e8042070f4a600b00c44800c88407840796200108002c560400c429120020107000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54974868 1250 54973618 54973621
    0xe07060305070314061302120406091b1d06030309030a060506100327050c04060305010e06070207080705010c1106041211090c090d0c03050609030a02150c030c0c0a0f0308 75
    0x1008003541c4028201600b00f5007012040b40f102c180c031104140d08404111040000e0b0540c005026007e0f024a916181069a03e14100014014140c0094404a103d070540a952040c0da968000c000e5040740545504080340d40d98560500d0345514441c1e400c0341004003220700342222400080c6c070740388519401b11003040e115400d020003030a100261525a21680c00d050200c0c81040880060400503210ba07103030025002180003090010500c510880d4a002500c24004192a401c0103800f9015090044010b8480d200020700414804900d250654084030041d02c1c0443c43d1800455601039012001d031001a11403c4004282da2900c000b0070040c00c10343c0704054907010314100a8424400180940c0c014241102000b000c882643d0854600e40000c8543c070610030300905120041c00e0968100900512401c403e0040300e8900102401041c8240c2d421540030715014035a4002c03040382980c000b5914102030000c1040c0090581c09001100400c801300c0384480c505071034212106c0610841600031825507030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54976118 1250 54974868 54974879
    0x1e1701120507080307170f0d1109010e040b0609011805030d1112040302011e030e07030b010915050a0501080c0f16030e03061308030903040f080d030c080f040213020d0e07 75
    0x800c1c0c1c0018a480c0014508240b041d8a03200110724020f00c1040503806e0000b01054807400c00c1c0705550101025210400100c090081400c441d07922598426001c03901c1e1041c01c00ca0341c60580580a80082e010301010308114501d030040d16004801d155480c20302070454400b081ea900d040013550403002166030303089640e10340f6100182c240047c4250504078054208010b00260740c00203015680c18080100070f00c20014580c104a00500e90220246880d020700300000050190718241d03103050703440c0003008021122141c030030100c0d08249403007107070f81150880008200f20744c01000c1c0207a0000c1c0281c2c07420b160001c450540d40155120420030100c10b40360381490020300d58030000c0c401002c002980180170307500b402c1400b92083c500c8450b00800c0b8200001c000380d080701d0140203982c0202400c0c50009240c5440b51801e80c0c94107081c20107840041d00d04509000150300c02c9040502513621311043c04899141e9400384102002900304401249800b00200064030704244600d9220b146c28001610280e414031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54977368 1250 54976118 54976123
    0x90a020d02070c0617040c0e07030f0c0e03010b0d0203060a0504030203070c030c0e01121509062301090b150304030f0314070e040c08092d1608010506040204061e17011205 75
    0x110400c106450f1017000304000509022960b800341d400403c1c0c6914a5681c50b1402c6003e400505c3c20140000e007016810420250400000220440c0460085c00711020700303805e104c6000001c0c04003a5042c3c1c0038002043c5142010b500480d000b074043c0c81a2454608a51035201c0a0711890b481200c12041d0781c0c6007049500100d0b401c807405400c0500704c0034203da10a8440360410803190071500d040d1035031f90000801b009420307401182c2e02070300500180315660032940d00d1400741c1000d2058258850400c044940245040c4921014001d03c40e0303e0142191100e032411955210080010340a2582d1041c0c0c05c196510588400351050085075682c3d41040200740500040c0e0340002d54603401d0141c80e005110140c040490f83c243d100c00c0f1004001040c130605400c421010700824010038850241542991600419100281c16107110b0402403005440301e81c10701040b4403541c8034071000504c4000301c903650100346426a00e1030001520308a12102e4240c134840c0e089840a030700200200c2d520308290300070400c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54978618 1250 54977368 54977387
    0xa050a0506010f08090a0606080705150405010203030115030204030602121509010608010513090602030708040c0e060303071104090501051501021b030304050111102412030e090a020d02070c06 84
    0x554005105600704040043d040f41d0074508640309004980c00003a007144000c000074000e6031307085003080c0042540c0b8005507440d60500c1c0103184c02400822010424060000d04403411694107038001e602e0740e8030300b40c0351400c86080030110000b0517808010020110703825002030f148420001701c5045680c00e1400442c000050110750701c5000703c02e090010030255800a420904450043d503d403c0340c08040f0440800801d078103400101903501c048140009551300441c2c0910461081700c0310316240e5290494600d40b800c0450344643d06610401c0848c0004000e00c2c00d910503c20040c0011810410903a140b0f400d50b00b08641020301c8c481c000010072555a410400c070050070150b000c02b1030800560001003512442280600307814400709400f0303640229010041c1440307260b8058000c000c0464402004a881e0400c900c41c6610000401c01c00300d00125401083c80d07965600d0b446044c80360b00581c00340440000028501c081b034940c2801070710300211ba1400100f01007445060600c5006041c032070098024034a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54979868 1250 54978618 54978631
    0x3030201150518041106070f11031e0c0d02010e03060a0c030b0d02010507080c071502030405010f0801050d03111606090e13150f09020d03020604030905060a0507080c0a06060b030a05 80
    0x1403c0350301c254882420500660002c2e088042c00541403241808590280b040c0d50004104c0300c4c3c03080c10042840181841313945528000c5040e41c14800212096406201c81040802260341140c1d460501703c2c68a03884500300d0503c11f0500c0c0400001480000f401e0200c00c130340c8409415114140c4c0c84555626114000c2d48030b00c11122040b10001c0354000900d2402034200041026100150620404d213042001c10000d01c10010710102201614600a4036038000b84101404540607000e103c20090003030455a050340c1e40540030380451140c546080711178680d1001c0c1c0c2c0b880340c040c0c4041c0d0b01082010540305005040c1e103403070360b10040745000d0400b4a6404024040d040c800380c011015000100c2d0540e515060020022012802c0440d0000d06801004108002035100c801003c101c000c041e004500544503600a48030101856510000d000c80c520a0b81240303800610204070644c00a1031140281010340e0070501152030102007a03031581c0403a441c0760441903c240c404400c00c0504090350007050340c00071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54981118 1250 54979868 54979879
    0x41a100b0739030b04020613030c08010f050f0606070c09051005011209020303090d060e01020d0c080a0b1003020703030212090106030c060e060301090905030d0507030c030c0503010e0a05090a050106030302011505 93
    0x80c12460b162803010302a000041070810071602080035551014141d03108c141d42004002d40b125500d1420000d200b4451003081251350038561442d02035441881054441d0441d40150b1642c0d0303a5207001c1090651100c50119003070700160201280c0040b4030711603207202d100f0001500710700c0c5081c00000b40101c5021161900d0b2107003411507400060310044162202d07000c06031400b4103070401521b403204c0600515811300754190b05c0800d080402c04600e4010800e454039944920042d80c0740e01c059241550795800340380b03801c03441080d5030b01e050038800e40c01041d4a601a150060601d001c0200c0018818000d0342d0720070642e91142410300a00120b801520300805942c2442c140c01018035000c56841d000500c00d0826041e80e421100c01480024000ca03482c1100d040c02c208000d00c0c0024025000b000c43c03800c10000a40b80402120031903008000303e134160750050031034546d240c2d1003440e958041e00f40188900c0030380c041c030324440700001d00c240100e00145100341c0011412100c03400100300403d500350721040c45407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54982368 1250 54981118 54981203
    0x105011701050108030414120607020d080f1302060c0c04060e10060203040f06120905061806060a06020312040f0f0b0a14010501050d05070203040513060807060206041a100b07 77
    0x7840005c112002c44605048400b40800d02c036001a2154090030b0b81150540241801c200d919540410000700c040c2c2d1a0b06e071104c081e11068440c070360b0040101c0b00d900441c9c0d28a04030f20f02524044000e000381c039a542e0101c841640b0320b01c0104040e201558080c03004071062405104540e0f0700910074801a202c02e04c010340c141440c0014040007040b00784241c40c00d201c0f045001800116080d0042070940341c100c811103006003804406101d0b0a039246044801e540503110200b162454441c2d0702c6001c880c0190b00071410000c2003c816035850501410840c0c0d24500c0542207000541c40e00c01040000d40650071085007840c2c4501d110059602e1031003840c00000d680401442140e0300003080c0d68084082c40c10009140d9503e0100368694861500407030351004031040c0c00784038400d8540000d42500c511000340c490b507a5807041d09076510f0388140c8000303000304a501c402d419048075002485501040780310800f0080790b03403407001514950104205032100ca10042d5046410046400b0120b203c3da01548002d07040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54983618 1250 54982368 54982379
    0x50310020306100f0c0605010b0a090e071403090309090906100603090f08032e08010b0d0809061804090b06010806011e0f021e0a050712080403030302030a09050d0201050117010501 79
    0xf40601e01100c2c00c1888044082016014424210134600b42c1c1c0c0b12a080082e542c45040c00f117025080000c491300041c8082c0008201055865001401040307162200c1d08900091080350245400082503112280310070b005044036070b0703140c202090003060140003034906400c10f01180025017900d904068141824466160000f82106038000c0721a900550451346a86a00c9180f41c81c4c84d1070320f0007440c9c2d182c2d000c0300302035006190801444115084030000f0885500351800740803021351030507006480d40d542446142c88500b800310090950f02040e10300c64031494a8480081c085441041040d54000104800c021040d600509620b401250900b06650424207280540c2c0700521004d1032041001502440030310528001c1040507500880320110306c20304903030080460b541d040c601b02c06850500c5948000a903d6402c000300c07031074040e00700345003c0c641815500e00758042d41c40981880c121550f00c805d00e0000c52400e001705818a0300c0c6500208440d45884005100082d80310085180d0781d2410740104107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54984868 1250 54983618 54983629
    0x801050906040809040f050708160e090406090201090b03040b1e0f07180b0c210c030a08060604050909010c0908030f07060b0a0503030307021f0605010203030f10090f06050310020306 80
    0x50203540441915030700c1301c143c0042000b60248404c0100080e052200b40120b2a4011019901c10011002203580400b140c0ca8100e89030400040e00319000840080420041411504600032150060504820031503031541c409a080e401202c3c02d0310b08030ba52270144142a0040d421200500c41903403d4124917040103562450b040d90060070020601041d426015600951900c3d40d80060240400590b02d4000c403480950300d44461160005124045d11840c06489116005a40c01c946411000310f061007001c41041d82c20810107010f045d4000010f00c4000b54681e1042c016900c11809280007141c04030654001501035459508400043c0c4c2040c001e41c21a18a01401d9031f03c802c2d000000400d22459000104071200b070320760080341e0940000010032a0711a0006548402c5244081d608006040c1e003948920444030a07000c0c240c01a001000465803004400c000306030480201e01808110359502d00c4071400f2900c0c41c110051280d43c480c0002c00240c90300b480440070410603c04154590300d803d500180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54986118 1250 54984868 54984871
    0x50111040b12040516060206060406050909030a050715050415110306013009080a08060d1a07030608070602010630140f0303070309120f0801060c020d17040501090801050906 76
    0x80c42c1d85148400a41440000c110601100300c1c03103a04a0f41013138885c40001d45038101110018040d81c180030000a850a02c140028132400c418405942000340c0b01108a03915800340b10240c40940c9008402c10750a005071042e10301a03449513185008896a0082000a40d820b400c503406425109104208569030000510f1440c100c210800c028580b4005041c0000710701b803e40001c1400e403a21001c4020414000020204807045444124090f5652070821400c1d1100391070040a0711444880410426000b200c6175411240504000c40e407940c888246601c0e140c404e40c021750040c1c2d1107180c01c0217001d0180004500c4c0c903500c1c1d80704d07a590808103014400840050300d0010000c0000100940d5000710a11401c6c0381a985002070ba42d0381e0804585c0100607100049040e142440502d000700400d034040c44c101600982030307442d40030481e86000d00907503895480400a0760400076000349140007407902e070406500c00c1d803c04901a01c6501b880001000c4050079008007845a1401c010700000c00c3c400110903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54987368 1250 54986118 54986137
    0x6010504090302030c03180306090a020d0b060d0b091006050301050105030d08041703101d0411010f050708041707060903030c02040c030209040f0b0306090307020a0e0402220504050111040b 83
    0x8a10380c5a02e140481c61403080c66040c80540c000810500501511002c4095460104070121011794840907403203626031907172440c02907001d240f122808000a00d5010320350362149000b0b11160405e143e54844426660081b15a0707a155040300c84410404031480c440c038000780000360020010740d07041201103a80e5094180b480d00a00c6520300018042104801c010a0784800005085459043c0103402d090314400074013641da88a43c0da00f032202c40c11480c40118900c15500510385000010044005440c400d8482c41c00c80c0030014200401c4011801c3c0a004000030090b040c034490703601000811300c6007404144c0e0054000c10000007810400b181d1302c103501003052501118009984400b070b0406500a1090111240e0410304006510000034038070f500600d0031a000790240c41541d61a158015100c0c46140303c000d40c45102400240301140d984901e041e4414800fa04a00e032614034011041150005c1a640700d01f616241d104200c1040f0007030140c0c54071080d6001e1083d0a241c20500340c00007501424400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54988618 1250 54987368 54987371
    0x307021302040803040b090108070305071e02010b031b0a0f0506030f1003020a030303050430081803131701060e0c1804020c01061409010b071e02090c1b0c0306010504 73
    0x342440660325030484004024210490350b03602c0d907880c001316031901304010b6280401c1070800042e580c103000b80038480c030500c4259141e1f40342d01e9806884d2580c030b0220040703140442d0760307485041c142500c0420040c40c05c0d06481c0b515001040030030342080040704540d000414030466130141004a40c5a180640360091880c1640c0340e1140d44120500300301005650010398800d031207039000000d040e0140d002c24007882c0100d403070940c042d00c0e0030131a459a0b80b41008a01c00350369001140300d50907118444131a004000711480716104e02c1c0070788bd554030b07682080121801c6180ca10104001442d1807500050b03805070000000e0203076910703142140c0c007000c0380181344141c5181c002941e00314103004055984090500144115191030025000764000c041e1800740510b00c0310035184840e0f0526120707010504a9140640d00c45c0303015a03680d103103d10030b6200d42c54500d22030029000100180da440021a01c140015502c035a118206142c14001c4082015274041b06608807400344401a03c000c150541500c4040d02c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54989868 1250 54988618 54988639
    0x51804140118060c230409020705070306020f0c15071b11030a03020708010c0504050a1a04030c12022803030503060102100e0102030414070f03032a03020604051905030702 75
    0x40e054090441e5424a01d01010050549010410030794425484850700360b560703103801a0750f10202000100220343d00150385c10141310420540500d90000c0c00b010344030300181d5098a941c0c0e0b90b4941a078204800101c0000808148500407581c10070905070131680718200e07100f090a011401800c01200340030b03601143e8003908001428048100204c0a000f4005403c461440310f45080094a403d4079010340001d035428101d400e441c09100300196016610028603840c070b41450705a041103000761003108840f20020600c40040810804440400200740d1a8411041c1104d144108014880707001000d061088100003e0105003d41c10b64420940c2c0d45070904075031360b440d00d030300503458100c0d65407010306103908002100300360380e5041d00039501443c401d200204248a50782c01c1c1d0b584512640c0035840c0c20103c588820404203104030360300c0d20300e601102035003640c81c42400704c0c141c41f80e0300c02035040d809030344800b060204001d000c021044031010b0b440f08a0424407004e9a6280d120310507a1b8000c0c1c40f5072003081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54991118 1250 54989868 54989903
    0x80d0b0d05030a0c4d15120106030513020909010e0109031106060103230c040f03030309150c0203071103030c15010602010516050703030f060801020a0302070507051804 74
    0x4000120250040112500e070103189100030000720070f80f101200c3c034200003400c40001201054a2170402d4150241070540840341800445030b170f800c4070700c3d54800c04203100181c090310b4561180000e034040e80800e0240e580d4580c000480403c44040c0d00100400d07280c00c00300182103015048241c0100d90485084a003515000c003814003410240d890740c1e22652070402e01600305600903d0345000e6036502c0342903410b0755803100010740c00c0702c400c034214800c80302401059840d01d51302212070603800340001156131709054490713420000075901a0800c60220307030744014200510400c140011500400741b2002e101020864a0094582c020b44800501000c484402454155418820b6a03000c06241e81142c4080d981200d05a041c24800e12400c0b000d9441c0c440801d078a4400c41118a0f14444a44c842d136141c0600c5e941c088004000c04582d2005039a41c80c8008075030b03100b081c0014018801c00ea503000da1030ba42da509040e42450390b141d01c054410440c0030740001d0801d92075010b855026401c0049901d2414201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54992368 1250 54991118 54991129
    0x70b0907030602131809020a0e041a0103080c16140d0309080f0627120306060c07080706030b010e0307171203010303020a110d03140c0c1c120903080d0b 67
    0x981005040740e0012610b2000d6040601403c41121081d1325404828217080c0d04480489001050194000c14420380501c842d03403500c0c1d40190068450384c58a00d260324070f040c8080c5450400e80040310002d00002c0c0b803288101e01040b240c124801c03510840c0240515100340002e031000234021032030041105040b90014103006a40c100003d00c448800e80d80114010400300391202401c03501c1d04200c11040710b040041c0300109484131810070320440141200c0075591011100c580006004642c081e20030000c140980f0802c1c0003c0c00240296002050b400303003402000b90542d041180f4807030400002c3e200710711169a00144200031521650400c8840c0100444860300f0442c24040740710b41484000000001c040d40060240741c883d014a88078011082d0700001c00a03400e9041c071010b40001d5419140c60000c0d000300c4020104503444504072060600d210000c035042801c104480d0a08402d658815024410440c01e071020b03851807850700403021411b66507507004a002c0d2038048450581c0e80e0f4800007080d11003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54993618 1250 54992368 54992383
    0x30b0102030f0c060106180e06040b060c030a21140f090106030c0b090a050604081510080a0305030603011103010b030c070203150406020c010b060c031c1401120302070f0605070b09 79
    0x1e02c0c1c641503440362400f000b5a603502c1c00b8403800c800070302d001c0c2c101d07911a80100c1464040c0d89190400003031540705d078820480581307454442103a02400800200340081e0f0308000500d48013505888604014650710105c416501c0c2c0400c250000a080142d011200250b080c800e036407091001c0041400b5454180321180180002d400042c110085c031600410445440005404220350484d001100c1c00d4540060104900543c880c01020b03a103e044007008441c000036542da03118548202e336008442e80d64070743c640340025030b000940c0415000800d100345030900f8061540c40c0d180240c82103145525003801030626120081c09081c1d50382c4d01150314000c554040c040e82d0f000342c8403164107804504260611400030b611600e00c007001507203480c01c05956820100107444039042d0340009581414545522080038600c50100704c400d0680e54040d00e41d20f0624000014045c009041c03111441c880305140107464031009030042d1802d01c01c0d0403020810140c0c44022101d03c541d2100900c03296458070101d00d490080c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54994868 1250 54993618 54993637
    0x100302041e05090a110d030e04060b04170303040c0302010f020f0d0306060e03010b0303040506070602040513020a08070813120314090c01030b040b0a0e070207180b04060b09030d030b010203 83
    0x3070140400080040040200349001019000c10003600e400560750796503007030900002e001e1546025900c03064a40304100c03642e001c1c0241840c102c15000100010102c8800360400004610041800d00c404028aa07001a1003a51400114510308280d00c41c0c0e400c0a803180300081c10000e040c4e07054544184240954031125002c10112460f1202d0440b000d4041c21241c0901c0000500451040341c2c0d91605010f4045002c501070040c500d0b05003090240300ca1a400560159500d5408010020b8030303480d009210494110b0813a07005803548261800105180c81c041c1044040110354000d01a0604280002c0064a41e00101c10066820000020fa0141c013481d00a81c0e062081c0347e00708041c120000c203580c003001000340c1c0c0400c40c4174828401c00c011035005d004415040304800406005c60380032140081d0700810070380101c0d80722030b580b09481440c80b03100c40107404116898501400e401e04044c01960085d140d145050b43c2030295100c0400e5455040c0d203c1c020406865844450062740240304488180380d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54996118 1250 54994868 54994871
    0xc0c0f010c0b040614160e100c0b010807030209010b0f040e060409050610050112020a1e02010b06031f0501050301050105030402041a0604030303060305160f0b0a020c0a0e04030e01020f0307020910030204 89
    0x601410a02c0c001c06104004605c01402540012500c04602c0c3c64050000d80a45a200c11500f071401030214919a00c0310032814081c02c06210000f00d60a45000344c02089a44003c00c00c090031481070200814040c0d0001c81580704c28130003c1c00781040c1c0320a84007a2561520056030320f68540c00020040d00c14640007400078001c00044c003c911032800c420a099483c00e07203548010070994160f00d0101e108004100c00000d40c04070800d5200c0c6255940403400641c81e1002240f168003030800a03040d90700036642c000703561a41c0203102c5090751090700d14800407c4242801402c1d90700d0f140001c2c0c41440b008100038441c41c2d40d00c031001781c1e4055103a0401c04014020b0030f62903d0351b8aa14003c0c00030302d01d501050320148103d5820410710704a50740480e040c1d8007400785032590145440c08a08090708125200c4c0706500400c11201c1e540e450f041c4421004040441c0304403c14203160034003501e03008141c40c4041c1150017000c8400c01d050000811914210390550340380d1101c0c1da920030040f284140740d1700001d5009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54997368 1250 54996118 54996121
    0x30204090809040b06030907050105031902030c040f0519120f0503030c09031902010c02060703050412030f1b08090d0201050c0f0a141908030606070c0e01090b060c0c0f010c0b 77
    0x20050074041d0605941c1a103080049004900420405001c100d0f4108959400180140300551048024642203680700c3d100c8200c0c54040ea0514040e43c0040f07482d03a081c0080841e041016900c10000800245820b48924150070b030f100c864031524404a0180f0170741000d0850040d400c1003d5002d82283c1c0c1604941680d4032810f0049550f40141e00a007901d038424841d040300c1d0b135a80c4051002e201c0031580c0c16103d054080342103030f090141030380001c4015014484140800a903100310b41c050f81c40d02c00d12035030f11158034012054001d42107418540c441c4822142023221200010350020440c0c20b010001c8450760031040c22480107d0700c9229001001506009181001c6213800000070b45840c514811305c0003140b8148004443e075903d0074403410380b807420010308009802085401b0021600000040c0c00280b404084e51a000454070840c3d0003000d07500c0d03200d801001880903e00c104080c1130421101603140200a00300c3d01da4403200c1c0c2003111702c5040d545040c005142e01079401100c41c03c0d40041100384e02d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54998618 1250 54997368 54997373
    0x6160513120f06150518090309040e0a0b041226041b0f0905040c0803120406150302030613110402040b0405040f090209041208070305060102061305120403051e0a0b01030609060603020409 82
    0x150130103481940e000d20113074500c1c90500c0c1e40510710140b0885a00d801541132400d00300810000d081aa4110b070b825000f01e40c07005001c605038020080c4a140a0940b004080010040c01014103200c02a105103200c00d83c0e013184281030451060344d8100d50813020b405240180803a42e91070b07103e981c1c1d21004140c41307030b204000307100d0b185504a64400c6010708004c0070350a6451050684900c15110b444c200c0d41110300005002075246da118055440300d601040d020561030754086440c1850a441c01034290f074030000b510040103401c46660340b42c40010340703080d4102032610b1000c0d5071a0040f130080911640e16403404800d4011180d12505080307030010b094003141c1c101070414100580c1c5040c156030008007007500042040e40213001f4207001c0c5106038000c198903507408001f402c030102c080c1001c40740c034000c080d101001c0c500040d0140c00954049e201508990080003681980011148600c40642c0c024401180100340503010702d504403904500c0100310340803036280ca01d0003441c40340c0000394024a0003460406 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54999868 1250 54998618 54998651
    0x2307090204060914121002030c0715020c07050f03030405040e0102190c060c0306030206040b0a03060302090a1413020d0305030a0b03030a03050a0b0a0503030315010309120206160513120f06 83
    0x1c0b02c004e8900d40468144c3c4400b440000c0362213125068869200c26509090b5141710790040da4000e40d0480e0701424040f9556a403c0120307a082200308950340c0100c3d81c030492001c01e09c4100001d080440712000c1810340040407980340c0c0164422248101d075540c000303999160080d011146201d0f0032046860003080100c40103072001140620542e0550314102070001524024400c070800d5940050040703080c40d00e841c41e142e6052b40120908800c150b129400000140c9a410700d10f4052080d084010842c030900d03030324000d404e0600030880307150048088056000342c0c643c0410400c209825250280c1d482c0d85401c070301e0003c0c3c2a007045080e0035101c009076442540e50302d680180c1c05146141d506201d0041818108201e480280c020140d00d600200b0205a1801c1345c0c01e03410940d020103044c08030720390802c1e4886071850a0030085201c0960041c1f000c101d200302c031b04520b0103610b81990030041d05151a034150004200f0050080e540f040802c904103200740039040c14084200c80d84001d0610241c0d14081e140712 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55001118 1250 54999868 54999887
    0x7060f110d0c03080906070813030e040c211e020a020f0f03040e070c050d050d09020d0503040e012111061c0c09081209040911090a0b130207230709020406 68
    0x43c00602c0403400f06096013070105549000340602c1d80ca0321495115111650b601c1c0c88640d20440c1402400d042d5a81e52713413114001c4941c981c40306e85403c410350f01010380c6200d0212850b12000e40403444c1c8000e16088800f50301c00000d084d0303501d4030016195146184203a01d04946412010b003039200e1108041503801e0000004c100380c5841c02d03c41221078031024000c2d107070004e5650008060342c00104540c0240c0f44584007902e042c41d105100801e030000d03d90042a01d20400345016a01504002814448500107640150040840c040080c143e1001182100b1200501450080c10800d100400401a551b800c040d184200c105400312000840c0096102004202c11440756020401c206800125003202140307640c0d59510115030300e0f2500500b01c0800008201d41d0404032040190301c100ca82d01ca03290181d0711441180c8100000809043c020f00300a240602003000c1103029004100003c00111215002d00d8140700c445050984c0b808140c40213410082940c12100001c3c0c0301180c00070b0345035400400346 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55002368 1250 55001118 55001123
    0x80403110604080604050f16061b03030b04150f05011b120201020d0f050403180b0f0903071d0a060e010506040510030e01020a0905090108030c150403090f031a1807060f110d0c 77
    0xb184118402385420302c0081c41441070b40040f50000b00441c403c00d402c4000b41d040280700b4600000c02c07005010000d0102c400030f00318031165000080e002e0014554000048000e400242001c007841821071070580c540c50b4509900034110f100100d00021801c0c000d40551b408a408484140468080360501c0300040504a80580c00540901004164100354003420010b0f50218024140340110b4810041000d5014036105c0c0c0d01442441c00c000703000d000705210703108902001150500e44d8142401c01d0b0054502540215880c0c0c03e030030f0300401c0030b0ba0b01c0c80d0884040303941c1a9200d29030341c5040702e001d80003000307850300020141d40006513280c0304c594030403004820343d14211065501c590700d03a010660f59014401c090782003a400090342c1c8104508540c102a889440303403030052891034881050480001055100316403844040940c01c4d01c1c20145402a40d01c003e880540700b0994074151402603807803a181c4541414051442c8941d086584601c20f8005400610001c480d410800150300030600d200c0030a0a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55003618 1250 55002368 55002373
    0x6070507150c060b0a0608062404030c0f0f0501050a0f05070b0f070207080f030405040e1c0203090406090c08070e01090909150c08090c060a170702010f0e0703080403110604080604050f 81
    0x40c50036614004191200f07407220f40c3d54581c0107594070402d10600c2744468032001d410f90131103150900c4411030074004202461007680300d00001c3d8680303141c0d801d030402030381c01041088103014070511031640c0c40001e0302c4544980b8585006c00d100c83c80c0050341c0358450b5040c003030100b240362010440c030303096220910790042820342d00b00c40c1c1090791000d04548401710245401403507001040f0130401c61a081d00403100b0b580303035841911101400006480320003404200740c03501507000814144200d14040c418440146528502845070301000400203103036241c02004481480084000e08025900c102e40040103009010310070000e207a22410030b810524010601480200c0c02c0014054090b071003036080c1400342c54404000e010892404040040c1c0750403e85c2040d00b040100041310702d259180131300c001d02a07840d80d00001025809007000340252484a2450f81860340140c00030400500d54008450880e5040401141c091062400080e00da224550208071079100e214140411700401042800407107001008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55004868 1250 55003618 55003631
    0x1207061508010c180b040b0d020f0c0d020703020102070b0306010c06110405040c080a0f0209030712020103150e0f06030d09050423071205060301090f02040902040f0e0a0506090105100506070507150c06 88
    0x2c400c0710511541c081d1b041f9201e4140000000c001050300506044505038078082d003030850031503a452400c0d600484a10050388441e40400540d43c06111032006400889122465440e1041c00602924030070382c0d00a1840380d0700c03c1f2006018070b410040d2809024000c1040c00356000c6800c0090951900340da170116540d2405100844c207580724801ca80d42506c001e000340c03140740c1c80c04881544020a41d0810f030b051545688500021440403103004003d13142d898158540d078189410104000c0e4002014035000303600818107180d4081c4c008840500f120000c41e80440c0101100c030400011a41d68a00c9405907052407050185054100e00141649030152004104640d07482d401c2500b650407560340500510728050940003d4106038214402d11350003d403011501d0b0110051500440d020142c0385981900642c4a203800c219080c8a1943c000140030028002f078102004e10300403c60f118404d1501c200c0000400004120381802000d006203840c2c000003035080361011000c0e00481e461801202d14501c2d181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55006118 1250 55004868 55004879
    0x503120c06090724170a0507020c010e090a090c03050f060712020f070b04140f1014040b012d0801020a1106040b01050103050c0705030304060b040b01021207061508010c18 75
    0x480e00111341d070001500d01c0e41420030700740502031288403a03000c0810030321170240301040c283c049003140100850f800021317180c500000000e04026140490904000ca14000c6c20101e9640701036a540140020301c00140780d408500d443c0300e000300390780c0c0010a01d0240855415170b000b004142d0340d12641c2d8544915000f25141c2914600700d1048a0001d80360003c1403114101241103104805d5116101d954907000500c000203003203241001071100c2071401d5200000107072a113040c0d40500b43e5084140da280031301c541890b40d205a5800b905000f58082c1851451903001903d1509540c0402d10300c95805d0007005585810180d40030b94403d4a500000c1200d410b08400d1010000425a1040780c2000700d409299082c0b00045019290103040c1001c0d2020611045012410500c009c1d0301030341c0b0540e000926480c8150602043d58199035886040d9004107046420302008002240c82d89640031900240030380d002c01d03050381a164290401e8126618200701d9074030342c2d504040c0303011b1203101c058024603903240d981c4e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55007368 1250 55006118 55006123
    0xa0b18100e010803030c03070917070602160503060606030402030102070b01060206060a0f0e06092502030315040c09060503060d060603030c020a15020c130204030515180601030b0402010e0103060503120c0609 91
    0x2807180440f80d510420006031583c0c070b59005140c008550b4503044240f84d581c0d95911044141d4110503c005410004080004580400c6011410f0515044150030585000c00280e1541801000a07004102c00400541195020f5046440030f81e8000303490075807075840e00c0000f942c80b107040790307a140509502d03003021601c03000f0500840c04951080502401d9561080140202000003070001c240415a142603004021001b15036140701d0f10241e8000c544034a0614010101203d130071007814080c0f45001e08812901e60312400640a690b200c0c20095036a4aa00c40454a8203000d010080c00c03e0f450b00c00e001c010581d00941c5500b40c1c0d070088690080560b1103190640404024000083c090703800ba01090005007801140c100264901c11001420540e894a51508190b1103007000048192080204401054006003e00403032038031000404040d0304580d50584488006007020341404110b04410a160b80719800500242101800380e5080c029103590f0503038190010300300605980100d00010b005034900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55008618 1250 55007368 55007371
    0x60e10091802060d0c121a0102010501170604081b06160807030b0102060612151609080a02010f050d0209031b01020d08150d210f0809010902090105090a0b18100e 71
    0x2440103150410082156005001c69282c1006000c510903071b1852180d05d0b441900442c0c4110f44180c4811030794000020300f118016005020380076030400803075148c00720000b0101d500581c00061165103540e031a58058540c08000540b0440e8415041000700c01d0004042c0751580b4540c7c4d440b05540d0791943c0c1000e5042c0c680c1d03001c1c02c4d4010303401040094518034241d4030141003844081c095940358594600300501c202001c03188020203031002e1102c0220941c1c0548124000c00074600648805a82c584c0020510114009a14108070010800000c25000303507044507002c500041c00c603a02c0c201500688001c940c4001c1a090141c00b03444a41d00030140100c160610823028420700c6146800c00c441000480481c44005131100b6148cd2a000100040300d13550002d810782c50b4403100750840d841d1000400b81140144144400d9041681a00040e00c445181c5819500200c50010075a51095041c40003810500c8801d6400000442103a51948020340d229009012580380190000e4a400c00480000300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55009868 1250 55008618 55008623
    0x91305090a0305030a0b0303070f0c05060301180203061503040507030c08010c020618010e070e09010606050a02191e0c0302040b01030209010c110a03080a0f031a030c040906060e100918 81
    0x1c10030007100040c0c0b04500441d840824030742c2c00034280c0d50180100b440e40d0004002100c01004100340c007014004a408808000e00e81111f407189958104a4841c140c54060450f1000168011020074059074580340030041c04a41d0701c0c0620780744d1030300d8141140c3e114801c0c441a00c000c0060480481d2225040c01209010000c40e0014010340c3c503007505141890181400120721550780c0c04180e26071100520120303004008818120000b0b0030155442400c40c0c4c0694450f90030b011082101c45060340d000300302d11440ca030700e4400304441e5050740d040c06010404070201c00102d06800d90012000c01070340310402d00580c0e0007a03c04000c142d01100054040f440303640e0f4403078041011007070510001211848900801c50004d0710280ca50f035a660344002140c4c1004400d417000c191448280544241d1601c134001400c0f00d26031401c0e0000d135882c4046500c1d039401040d11406181c5980c585804d000180d001b5400a100c0020820170700d00c0c2081c80c0440d0400755001d6042003c1c141700b8400c080c019800c030840e21564 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55011118 1250 55009868 55009873
    0x3030f090906040f0204060c0618031709071a04061b0b0408070c050402030a050405100c090b1312030905090708060108010509180609100b010507080d0203131709130509 74
    0xc030080801865a400402003940151590a19501c40c40140054001819181c5401d1030510031441e202c01031f00c01d911b11405508819a500340082a401004880310359001c0075206029140c03034211900f080020b80018070071a4503940700031107900d604802041121400c0d903c21030058040382161a403904400701c0506007910450100303010803500c0c1c0042c4450752062294203200b5607200042416a002201c0e2078008694030003c20080c4101031000401403000044100299118242c024081345070f50701900c40460004031322000359154240c404409086088041a008006460010f000040e00d008290244030003d0214203024007e60400c0d002d06030584a90840e6800c0c0824803680b903500408543c803c0003084003017111200140319803405040903501520f0602c000c0300840c400e403020801c91038104401004100e000c10110001e56052003080e90380035949403a00a03510305d0b40c4000301c10150050f4020b0194100811080c0014159420180c0c0c1001c0d140901c0108881100c900f2911141c03240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55012368 1250 55011118 55011127
    0x103020d1d1002030f0105150714060403030b1816020102040f08100e070b0418140f010312020a020d02041802090a1515020d0e1302070501020310050d0f0303111917010503030f 77
    0x240340c20b070602007186548c403030f049040038819110500000144100c0c04c010b0340141c400d00090540c107020b03d03101c01009440c8500303d40e010203c04641010018210ba54440030303003025042c181c1c0700717404440045c15910038040d000c50300da185a6440b54501d004000340d1502c2c1400d218443c400108161080b954a5400030381030a26120850b8800405030b00c3d949216565195030400c4c43c400d1040f1613018903088140b0182540c103502d800d074600c8070f28010309010740d4000505600140d96841489985642c165000300d1a00c3c0c101600103800c400200c0f00030342c012801c108103c10520541c2c03103400703005c44101c8048c00701540c3d1041d483e5003000f1200c0040c016000403003071044187c040c4450021412f4013401c14500110400320381c404a80100108440b103135000824400210b520720342000c05020126508950500301d5a5201c1c403407444200300509040d16141405038002c104415181c030806545070b105000441000700401091074682c295030010781c8000082102d040020669120354120300c900b603d070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55013618 1250 55012368 55012379
    0x10801030512030603030403080a020c01030606030b15070606080d051312021309030e0616060b04050708011e0b0a05070b09060402030d051b07032108040c140103020d1d1002030f01 79
    0x940d01c01040704d5054801088000001505400181115aa503a014105100c0c24500040a8034016031000080500b0070a0048550b82c40c640540c41d0040c007503030f1059544c0410f00d00f030409001381e54400306050080c42c2c40c1103000c40c0c1000080c071002407400720702e908560f211041561340300610300029401491030f184582c80d196250340304d180b1042c040d051070707603605442100281095000f0b400564104080da0256020070441d0301801e002d8102c1150305110303074034000000070308885c4140701e240240001c16098490144980c190344024112000c0066980d21400c0c10107405903025000441e803480200303001402000c404107160780640d40c02800f4102c000600402200c003a00b0013140c418040c804003003c540d00e6442004a00000d610074440110b01030761034100c4801c1d41401c1280c00b02407210203002c0200242c2204410810381d101c1481c200008200c45004030000e000c0c402203000024130f41300b6a9915441840540102854014100c03050754030282650000da0006455940d5001c4009006121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55014868 1250 55013618 55013653
    0x127020a020a02040603030203040602011401120809060c030708041d240315100305010b01050a0c1e021305010e0601021209210616090609050906100306080a050105060306060108010305 81
    0xa03900c1441c4102d502018164000404440e0f45a0085000d40d20008081000035028001c802444c1244100c680c03180d850604c038844a1010040c0042100308000f890000c203a40c2c040a60710401c100b1400c5984400c0c062900a00c00d6215004222841003030850803044205030200c201d01c1945d40c64065a03440ca40300b64280e207600c0c00034144980c54010000a4039200c6014a030311885002032100c024021843c41c1441170031941e40d82103003810010100840c543c0342e07401c04d031300c0c07250706a1040c0d00e00d02e20440207024610301c442c0400300030360201489071065481042500511b0503680d11400c011450b4980e5001a80e482e000490808031884007445840807900e00300480307100d000f24101840b0540c405443c10581003110446511800d0500c0080c25010b690348802d84001a04040c1055404c26043c41c000a082c060300030300301c0d441002e02454804010f40300c0d4000400130401e080440c0d00548980c90403502a050445d09980640b042000203505c03036102c1c0240c0ca04030798001024000d0319145840541 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55016118 1250 55014868 55014877
    0x18030305160c090e01020d061d040b150607050a0c0608060f091803030c070506060303090109150c02030f0709050606090609100c0b04030804030e010c0507050423010e040209012702 79
    0x60b81c0240e000000500400103000b0704d0240c881074400183d90301c0784030600e001203458540150a00699045440d0258a24404495040754019074202aa40c1e20003021140c051050b440664000001150020400100183d058101c40c0310f02c940090b2036840e030314110383c4034408886080d4000101200c907019424551400c9810414a0610848107241e01811601d168000eaa0010070494001209001d014007406165000141203011307514107155880000e08010160240c0d40c4861040c2d0705100c284c84c0128a40e002d980d9001e0195040070404007003141d01c82d06907115001000741400c002031000d240100455500150080c4158180135003c030900c803241a1442c0c00d00c0602030940107d0b004284a0380c025803040d8401c2d40c1d0301090b45014078005001150502c6d86a0510041083c0400040c8010694030207540c000e940c002121584c420300015910281034251207950400310010520802032a03101b0701c690300956004519980e94146240c2c80d5808030706042100c0510f0505000c1c0c441140c0041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55017368 1250 55016118 55016123
    0x15031903020c210706080609061c051509010c0e06070f0215030c03040201030b060703080103060b24030907080f031c0603060c0207030611040e06091305030f0306011803030516 77
    0x740e8416140b0350104802910301c40380c080b0080100c0b03102442c1c4600c1088074502600c0140381a00c07260130b103080814184d48024082a1180c503806031441003011002503050200d580010860310b103a0740d900c1d11020b0404040d44d65400a50030700b42c810500303a010303440f1041c42240181070fa62a0944580b9a0400e40b10700003c22030380140d80c5080140e9143c0f852005d907001d00c218000d590f540381054800034003118001d01809008200501850002c42d801402c101d0440740c014a021410341c0c806400104e5480100c03206104200200c0c030b420f2a9404004081e600c610300110071182c10075280c40c4d4035135992080d1000407000d07500800c50600c0c40ba10300c40d00d410b040703040b1000c0032414607103a031f03a00802e5030f010990302c40059001800c00c2040c4440f50080c04801d801808180d840c01b03080a4401200b4000200114092008180031462100a8140c05031001d6040410360384c44a0180015a4440e481581c81c103000031210042e001020b90461481b02c1100da064803607510303003490822000c80c50951904107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55018618 1250 55017368 55017373
    0x1020712080d1d0c0414070c06050601050c0d02070302040b09010e01030809030a060204030605150109080d0804140a050a11010201020a050d0b0310020d060f21140313030f0302061503190302 83
    0xc1000c00d000350b5100d0f80c880d0300100540341549011040c00101ca11000e644240340d00460306000f0f666400402d03a400b407941000c8040340c0d07030b907400006942d507225a480c4a01c0c0d5125029044101582c08184107081c0c80c82203034280094002e01040100000c000c0c010b101030950b40c000100001640e100051030000030180540f001c280d05a103900c8100d0308540c0c400d584907502c0c0c0041001041d03009180c0550304100342000c180144c20311100d60f9079460498901000c0c895050003080c01d1169480c3c80f031000b10315a004480001a0500e8401e4558440c40d00484541e0321503a01007c1940c0180282e4104440581c3c4060906030801d03e044050142503c25a401d400351842803007406000780001c0514075410358011518906e0900d22030081c03081030b4042d6454499912000150840060003500c11940204061190400c00c07100c1e50300394416000c140c0311440c5690400010007000c1ca4480c404c2034001e0702929035591781d100e1203800040186d003200354540c00c042c41c400408121078081c240c486010b40f04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55019868 1250 55018618 55018631
    0xe07050a090f090c08060a0b0406050904020f0c030a020d030903080f060112090506150109080a0204020a170403090509060105031e0903070507181b0203030703200a030902010e01020712080d 83
    0x1960070b40708068204040c0c40c0c0d03c0d0511549040c0c4c2200e17200340c014000b522181c8031a0f180031001c00107800366015010400c500040e1003802c5948036010359840c405c1414806035205e4804141c1d640c1c0e5840400c101d00940612000814842e010748686d00c00b807505030302c2c0e074500760b0b85c0e01623045107051000345000c1c10301c0100080d19144a006100300c804c4c2e02e12841c020b0040e41403401001c080e203100061910304000007d00180005003000c501480401c1c0d0644026817102c0d00c1000664a42070360078144003417036280c402003005240d030040d1030ba0f08503403081d258003083d074550303000444e07462104907201c541c0c450001c10002d03040e20b040c15400d41d010301c42ea02030324146000c5030f84a904003070b405d41c01015690100785080c031601c1640e110f00009042d56441905106980110107512800014299414584d681c5044a4103002c03010f00841c0307559006407100c3e9074004084014005040c1c012059001039140100c0e10031310f500001c3c0890030b460700c03c041900030041668445913658005066a42e0190b04c031507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55021118 1250 55019868 55019879
    0x60103110304030c020f0f0607080a090512060a0b0d02030c1002030c0304060825020d05090f090103061d0c01021f06030b01080f0d02010b0f010c03090e13051203010e07050a09 77
    0x1006140039501c2650703420100c04d000d00401124006c00b030344031403040e80c0c16218010316964036030485000c0c95108040c1601e411085005a9030050f85500940c0c00841c4039018071480100402c00301e110b6106981c081100429550601524000410000350568000100c10076189410107c44016819600c1100c2c0342510302f804050030f41d04143c0c40301c0003050f401c0b000d21003400c40c048482c26004075899860001c910364980025941d00c1130240c060203004000580706d039952100300851081420280c40d80c40036580d0b9162410040402d00c034444032908101c01d8100030b620700454075001c1018140e00824208442120b400c52004001c00007015041e41c60400100040c0c41120581c000e21194000c0c0946040e202e41290070700011070030307950459151002c007039030564440700c00d008401740c28038048071400800c0c5815a061b41d15a0414440d602c6440f003080300d0354144104a1001510880960701039044a15000c101400300b800386084820815000601c032912030405800c0d250755a19140640d540d449 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55022368 1250 55021118 55021151
    0xa0e04090219030b15030c0108040c0803040609080d0f0207061b020a06020303010501110313140d060e0102030901060f030c121e0503090405180a02040e031e0405010207080a110603060103 82
    0x145000b580100ca854040042c4503071649040c1e809030b031001c520003007078031000c001139100e6550f82106414849c21802107010b11040a038000c0103000c99508980d0303140c1d240c0364003600e20305c400d10410101344518010110b1081c810704402c1d00c80f01e0180c00410321181402e205441081c9000341c11041d01101e0a40740025a4800d00c2c80002080c0030740155540c0c1d41000001411003411031b50510040d441003024021181c000c850040455001c1004c401c2c0001d02c5c2000180000d141d42800b6001c10709001a5401c2c1541c19070086005240d500001c0103120740c0c0c1c5030782c103505074130a05c805406140111402c00500394500b610f800910b04c80c6207007000c600310b83d07005000740b043c5003502541c803a40702182941103401c1c14441c168128910210248840c0441100740d0764071402640024000e949504522005040400581d820302503c81204500440c00c00c0101c0d5064000e48100e030b005100324200090120404103540000d80d0700070040d00c071103c900c10300340f103415803024020504040da03552203040c107170901c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55023618 1250 55022368 55022389
    0x605030a090804140102120403050a060915020d0501050120030417011e0f050105060415030b0a170f070603110a050901020307020d03030e01140108031c0905030403030c0605070806060a0e040902 85
    0x2c13000b0b074503180003244000900e002c80345106a0052042084144003040b0005441031005900c030a02081da100c1074034180c1040751a0340c00e088192400407a802c00c440c8540d82142d810703101c00380c0c2c8003d03494030b441610360005070060841c0d0400c0d4000300828440d101d030301c22888500e0303510360340007081c0311492070008014580751140b5200d40507582d542120410005029032801840121820b60070f20307080035440d0080d0404030030a8828980d542000140700d403115442c0030024540342c0315044030740c030400001580f03451440036030590900840c64041451030180c85003071340840001540b1803c001ca1030000b40d034a944940d0440f419480305101031001a5200d0500c0080d01d4400d540200300030040c8800380d800c0d5002071081c0c50b13045040000600c0428000816642c0c1700c00c00c0e2240303428054205004100615900e00701400b02c0c00300040c08400e05411031040c24a15108010070842c80d601c2c00c10407101c00809a41c41c5510220420100c04145e101d0f20620380340480081000603240c80e1a400541503242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55024868 1250 55023618 55023629
    0x4020d0b07090920030a0b0a090c1d03150615190c1a0702190609060608030c0601080c01020601060521040302010e07050a03020d0209220308011505070c0605030a090804 74
    0x210700c401032002e0983c0380551808000019110b01e40c0c0d46200c00e00008601008000c401c441c3c0e40c03521015459a5607406503801041441010800303a200c65400401404110384c00302412004068078280508001480d41a00f00c500040742c078058a602c01000040300044040030755065041c400e01c0140d038040100000041c1180e103900501005e2464a03004881610b05400b50400c401c90030030107031030307008a02c801305030b90810100342d4140c0c918074010004140300f039406405c45180c210301003080031000004015025212040f11203c1e80d0f00c0c001256151080401c0305e00580100c00100020350041000d8200c440241d00d4000454a00411100031510115020b0340141e4640255991400f0107000e00809060242e420240c11810f5401154002c02c800310300034060b001050000b03400340e0090103608407030110180c61035641100e038140241604230a019425815400f5640c2201650280d0f044900803035100300c640c1c07003443c601072060b5010f0300010510a96661100c104bc0c000401c464010005040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55026118 1250 55024868 55024877
    0x30f0515090115060f02150603070902070804062c01030218040c18061b1401140f040215090d12030b030708061009051905060a05090a0b01140f0406030504020d0b07 72
    0x43c890310030001a0300c0140e104500380281203c3c038080340395010801000c442c0081d10103120548945001c03900d000002c0c1e00c0211620b101050304410003011030020000c0740c400e07075241d2412500c083c072055043ca1344004030900305d5240560304196075010b5000341400325554040000c0078141507001c101031b101001c1c29400064445107091046181c0325005402400c0c1518120b135002d00d4200d2259400c06080070302428010303550040800c1c1d10404d410040e035490030002891a5824003101642c03001d14196802c0717216400c0c92207403c1c809121402074a221020091881c2c100c414541c88240b94042034000403403c140d2100c50740341c003640381044903a0080518000610607441d000e42100326900036900042502410b003020303c050160074030246209000d0401d8005401c1d161000010140409588516000000c50003042500d641560200f0140b80080e240d0b40c09500100450761224070941c42c0443c204001404140303c0b4a10a40c07101d6400741c40500320441442d059116240c904404841100004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55027368 1250 55026118 55026131
    0xb070305041203060510050706091b0303020c010806090604050a090506160912030806060a051201090204060305100e1302060405030f070503070b1309050703091506050102120405060301030f05150901 87
    0x701d003031241c480100b0304a10342006040d00b070900085401c0c02c031001e9a401c008004c5022014042d4070382c400c0210540c000045071070392a02210f0759101031814030094001d0b014078454102a5401010064452440244909443c0d9a0780081000411010300555045641c0d500c01c280003032420007040b4065400c0c250380c00d01600c505038000b04802c0c01ca400801140341c0101c03da500190300b1074520354024a0444015441e204024400c07243c5008060452005000c54000092a0100e50340100b041e580650f41c144190303518141d20384000d85040c0728038110300100d8000100da1240d00d1001d08407161000b000c06203002c0c0c0e00d00000c0d15114880e0700070052034001781c0c8100100d240c1007020900500381c030004c02d0304002100f280000e000c401e034411365800c60780710800204110701c650b000368811580a0700d2044005e40b01c1218400401c1a0701446001d80f00d1180700e030152858000a4400f01d640013401d051460703086949440c040c460100f4221286e1280d000c16051141041107500d20841c4400700000e00d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55028618 1250 55027368 55027373
    0x30c030612160308091e0306010e0c12040c090c0201020a0f0e180406020301050a06020f030f03281505041e0f020405130b1c08030f0907090e1506060a2a0b07030504 72
    0x380c506c454030303404c1c0c00340303580da2480f070244c0300452060304440310500c0740c20b0b01e03645191410846218031342e00c032280191a0030400c07040142210140c1700382c072a0036008010307590380c400c0160308130311400c08040041080000108076440c03041d250a90078000160201d4665600303149001507503402614111440c07500440140014184480070800a1165100401100702c108008a80f20302c21490900409a400000600c00c1d000c840c1c080080391400e514110300400103141c5182c000d1420b407105140141d012200094145054007492100300c0068590510b004110941c0c10010010803005c201d4164080c4000600ca907506c001040c4004250344003c5844220f00c010445140203c40c040c4140c0d01444c500200801c088400b40c0764010b0b880420426a1789a0300d1509203000e6a66106009480c1440042c4040c950081a60907001075000f15007400d6454901c20000d09004140880c2c0000b180040f50086d9180052040e041c030401011640e459098252100380d0b401d0002c03074044021945076000c0c00704 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55029868 1250 55028618 55028629
    0xc05010b030d050a050306030c06030a14010603110a0503190606090807050103061a07020102010605060a0201020d180b04082803060302090609040c0b1c0c030506090c030c03061216030809 82
    0x901408501601021003a0305003e46a802018841401c019001c40003414a8404209800000c2070062071a5180d00d081c20014020744083e48410280300401c9000141150103400b4880d183e04540c5020350818049032011542c542004216085088040f44514071407056449202d000d81220744d1040c200c903040c480a10f01d042030340d511003070415151400c10003140301e840505140c00300784012240d0b41c1c4e413140d00040340984559045103903c00b03400a295000785030150300500310704803000c5003400b24800b04030030301c40c10901d404000f0300003800e10000140060102c8000341100c0000c42000d00c51510004150032501c5070b51001c0b140800d50702e0005206600c0d00c124034640c04103044500c0c840c1458280d651680001d517510401502c00c4000c01d201a42031b414140e44119130103042c02c00c002281c44250000c01910003610854000c02d40c29021901200c9180f0445c0d00c2517540320346051854544100741b01c076407108420408440d00500404801c1c062002c0b40300070065005100e503580f103c184104014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55031118 1250 55029868 55029881
    0x10b0a170906010b0f0d05190e06010b030c070309030b040302060106080108010c0f140f070507030b06060703090614120708070810030b040b06010c3801050f10140a0c0501 75
    0x300460403102040550800040e2650540320181d003c66160b441c00e1900c20750394001c08500001150811b01001400c403850001405a080c001c201440048800c1d41c85a4560b1400c4c01401048102003002541000d0350800820102e4841c2c40d0000c1c00320358a4940d0740030108240c030104c0068016100411456a00c10300003400740265030000c00072a40748000280240d1820b02c010424440400d02e0090910492030030b13510001140c0800390b0741e0f562140f406a48030641400119600041800411440e0400380161900c503030345902c80140150400b0740503a24207111f85140d507103901e0200010300140103000300c0345000305540d40310340036030703040a0304e020b0034510300240603001c0c00c0c0b80d01700c080001c280e407003030300c1500036802c844560000c2d151080126040160400c016140c1024007184070349402c0020301407540800d040c2020407020011440300710170f1200030302c20306a101c00d00c19103100d1140b40c8480c03440c84852044c103000001050000c0c61008541144541d5030210701c1400c034500a1080a00540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55032368 1250 55031118 55031147
    0xa030f0305010b030610050d0603060b1f090b030402060409091104061a0403060e071203020d090504051314010e01050106030608060c0301080d0c1103070b031e010b040b070317010b0a 80
    0x20301096051020402081c08024172840c42200c90b580c441e10898003440460320002c0d030342e0800f8414281c07172341130078000b81800b6402c6034060442d40303802e6004174a41c0c8440044e22401943c903089024504405503174980c01c064426640315404201c0010400c0c0c40b07125a1403a41d11959240d81c00301501004c100480b0000e600c0140ba00701514298880030038680e080b501501c0d803143c80000c45d10211501c403450891329070040c0182215880c030382c00602d034000407020711001d500d075201100540c943d0b0034441aa10180d408078112404542840c1c00a04031608031464080903800000d41c04004d8074040342503a00a174006008244d40303040602c40720703800b80805580040d503079404c00c2c07031545003681c20f0f0383c0e801c685a102000c02c03005404800401403c1003160701814030050403983c4d0350340c40390b14120300e990064aa58401c10700303000c900c1074084c18115902e4121403c15000c641801d03e0488000c48950107104200c08009603641150070030706284c1d0026000c0e1480d140e00b2034445050040113850340e12042c00302c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55033618 1250 55032368 55032371
    0x110712030c11010e0f04020a020a0c08070e100609120503160b010602100213090506060403050303010b0421050a0b07210203060306060d12230d050405010b04090305180d0c03050a030f03 81
    0x100f4254a4203403d00201c2c0c0c00603100143e2381c80c407d00c4101d041114902000708000b98011000818550001d8803c0568030540c0265202d91140c2c0381c4824160307841e10822000c2a004403040200c04000d200058900b406a0140c0b440c0c0003100c07039440090350344140b044074107440400050007259810000c07940f00c0f90142d002146084091030403984841191301c1259511610350001400503140c80703040e0340c01550310100301e81d01c4c1c0d41c440d042840241c029016000c0400541a420a090f111700c0d46001d07801a0810043d040701400e40e169000304c10310043c4100184025002910150954209030700e0032108440c50060300d0381458400c06013000c6015125511030f40c59450400c02140403010360200500440c01c2c0644843c0041d4400d0014007040580225269004114200c00450b01d40155200d503118100030004840c00000700001c40e0040707c4050000340b03080c0881007424146828144d80248024a141118101540e40320900c20312500308949075003000c1481c1f420960032a20388105c030261800c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55034868 1250 55033618 55033637
    0x507110106060f0813030c0b0702030306150f1218030705010504060f0506060d0c1404060f0f02060910090f02061309050f06010c020105070c0305070609060210050105060307110712030c1101 83
    0x18004d100b0b84020304852810b003501d060080400d8041e09404c00919488003511025241681010f5180e800469030035000b5220f61004a40c000d4540d02201c0d1004410206107042140c000100803004c1802808400304d804030748450828450100080c08180703114000128080c036040c50402d05540802d90b00001803070802050044981d40e5000b5291458001200050101005030007200d40048803050402d8544000030b0200c0e003282d004140e1000c004c0307152520b038141041030070104d1340d07484201d801c0360254001c20700c10340e910b842c15000500c1460091000744181c4505070005011648404142c46a2900c5c3e1981001a0400c5004295004014011441142c03130f0010028042c5514860000e041001c005000000c120b0768184030006140c11000700d903a52505d501c4040e000d0081e6000d09005031050305030300704811142c0d009145c182c0314007421913811078642e0780094070f10000c04c0c2c507c0d03041030203100e9000c54803904010140045601039940c2e0036507000141820361084152001035410440d0014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55035974 1106 55034868 55034897
    0x61b0206060108070503160c060c020102090909070503060606030a090609060b0f03160e06030a061a010e0f010c03200304030506040c0608130201180801050711010606 73
    0x1000c031545601c80e80c0054565080482c1c680d0f00080082000500307000410340f0041c0003a0140c1000042e00d03500742d44900507a0510203442d40181e43c0403862210701d1a100240c5600702c0c1d26103020f408864204004607481e003100070240c6009500c00030114003018042c0d405840c0c0c0c280c01590401c84c40c0020301e0188040c03c0b6485445205c0e840d400399110b854034020404407502c080010f808241302e0700d0028642c074000d50040030258076024544000380412610300941a1786c02034142680c2e00b0440540015021500e01140580260368000d080341c0b55076040040c0c20a01d40d0141080c813407120360b88100481b00310401441c0710282c0030206002040200019155000358071618501c41d0182c0c40707000c22210340e41d0881e001d440ca401c03150741e0300c80594080d80261000821040c100b1920b0b507141c1181d2400c0d150282c482c00d000a503800b42041c48510203228490180100b8034085e5110500d44 = true := by decide +kernel

theorem cover : BRFrame.Cov 54856118 55035974 := by
  have h0 := BRFrame.cov_init 54856118
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54856118 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 54856118 ≤ n) (h2 : n < 55035974) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
