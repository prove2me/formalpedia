-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0988
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:40:36.323726+00:00
-- url     : https://prove2.me/submissions/78942603-4404-4b4b-a03b-4bf83af3525c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 177517985 ≤ n < 177697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 177519235 1250 177517985 177517999
    0x5092503090242130f06020c010815040926040303020f06090a0b1312020c1306050d0b06060f0403030f0801050d0506010b0c01060504020d0b0a050603010305060105010315090504031107060201020405 87
    0x204611070005500f003038080007072854108038100412140b00e04c01c4000340440064841c8043c00e100f0041d09000e51114203e04200c1070400f080508810455403030980c5109650001c0d9400c014204400c02c00c0c5450300c80320b2010203400e200300c00c3d036113144c0c000e00840e4000d07425078011540c0700090a44414044d1017600c015030000d44d0200c04038207412113407500008a09040f0040a400f6629040110440c011080141e000340c902c011060a0a50700107801400440c0100840d40c1010000707a1110300c90040540640d071014001226030f104c48013110380c41c010a84000c3e840759070b00e180003441d100c404049440012200c000018003824201100c0e8011940100601481c2c0c0c03c060101c400350f041500312080664a4000010303054036284002c192780481080701140c159801c1044c80b070f40540b9075219600480c001c02c010800309030003060b1103054030000d02c0c01044004444030071904280e10794101500c0d0034540b000384410140c00104000030b500e04281605c10b01c542d0740006070300302d0090348506c6411000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 177520485 1250 177519235 177519319
    0x60708060f0f090405010f05010602010921180b0703020d0305060d060e070f06090f141c0201140f030610020313060e060c0106120614040309050925030902 68
    0x140c80401c4015a541c0034015164000004002a603c00420b13103040c1c40d00c2c0d54480060303400604500a41c0d004d021207000038031043c1c902d42e1311166031805191469803030081550500743c0140c490071800080b1101c98511100c80d5454054580e0954003224080b40584110018012000d0180c01032324882d880041180288034041d4071140d0240288100c240c181303029402000c50001c4e4251003841c090102c6940303e04040341840000810348000d50000401092442c044120300d55031020010b003080356050004a000704180300685140c1c032182c1a0604008000c903070103a44281c1c00025500c40e0808a503d0200c14103d6030003aa1244202c51104c804030510410610886c1d00a07040d1910314240a042c00d8035144002020701d084440302d80140c41481c0003511503100b801190301030651340c400a80700744c12881c1041d650240040950344641d0f0f00500840000070100c0c8203000f02c4929080d9034504801442f0803040000f00101780c4070700102d115502100a004034252170121a620302003a4600b00d00b1021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 177521735 1250 177520485 177520489
    0xc0721030c11120f0309041d070b1c021603020123150607060501080a0c08010e070501080a020702030a05031b071d0c041208040f06081302010e0607022d010206070806 73
    0x40360460026411210700c20f2080700c45041080f012034560903640241d500d43c0508010882035a1100764a0300400a410300c01103192000420800202c40c441003420b0b56035540c1440a0000c0103101e5030440032144040303420745d0458004501d50f0340c0244664001c004400400e00c1c1070001d03601210001c450b074400314001520740b4000c0c004400d10818000d1603141494075a541e44000d07120240c20031141500b105c000c2e4400c0094800c140300203000d161000b03110701c0074400c015603a1506544035190410050b24040b07842c0d01400c2e81116202600034080d20305084060801640d80e5100400d4014000a908100c81c0d01d5200404c10009484400701070b036100150b481c64052000d80c0160010311491010480083c4006c842d0f14280142881070b0160343e101d602e0a04424115540365024600703220240081101160024441104080c1d09080c42107580715914045603542c054000001d420007442030100c2400b60319a01c000c2e17801c03000c1817144141e0002d50b400480c0ca4030020380711500480d140c20040344d154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 177522985 1250 177521735 177521753
    0x311030604150507050f030a06031109160f2006060114040b09040203072c0f0108060f12211801050901020d11030706021614010b1005070c09020c0721030c 68
    0x111707191080c2089800d49000704280c2c07082e5a08080c141c1c0e1840100208824041400c11000084400207054030b05a1210001c42c4210038000c0308010000c0d56022000f4010304884407075000b44840c40007110321260f401a6104003c0c0da100b400300e80d00c1b14442c1c1e03401c0340311021076003503074201c1170700d036003041c5000050002940010303041206102009010040d9100c000c40340c8402104000e4800c030300f014598062098501c113444040b03040200250400840352a00024841021025200380c4141c1000b01c0e8140c0c2001480212000340c101a00e04c1c00e64001f6883d005860041403013607910300108010801514107120761082640035800401044807194082d02030403600c411100c3c240d17860200b180e23480c1003c99200c021582d80d48003120201a00f0b004100060300c107003000d202c00800040d00c03a03500040f13441001396038640c03c12400241800c208203903400204023b01c0c01540554450502c50700c0c00740c881101d07000d00c001c10764094040c1d2107070400c880360364210749030103499045800c02107031202416 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 177524235 1250 177522985 177522991
    0xb06092101020910080403080a020403020d0201080403020a020402160516081f06030605072105010609150905090711120a0f1d03100b030c090405100b0121050103110306041505 77
    0x1a555090000782c0f03480e1219000c040c0f5095407503076500a64076052130041c00c2020080c1803030069501c103010900c016140d40400c1901613409081030076003a55140703412480c00074018130080d0442d0010a0780e21007540098040d001c0ca902c41c03825200280d0305440c0c4400c0e007000d644241c280c3d50348044400c0d04601607402e4071140807481d02f10f003c10345649a440d88015250f040d142140015410700c0c42214904a4240f040c00d084020802404194500a8020462106805000c1202c0744005144900e24091140b01c00180409400c0c0038180c40c0045000e1320410082c1442c44490003010740701c8981c04890001c07039016140070b48034164004d1410700104c460038104c1c1c0300b604183c1c4a40d55141c04070760382001408120390780050041050350005080c50304001544081d20301a0034801d003440006000421510008000c14900044c03502040c00101c90b81c5244445c40e502d440c2c9001454000070490341c109038142c80c0910030030b013880713000503080c0343e076800c42141c01405070448403021070884034094010381d070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 177525485 1250 177524235 177524299
    0x9050408070b0c030a240303050901030b09010b040e090f070b072d02011101060308030c030606120702010e15011d090f03040b0c01050a0203040812091218040b0609 72
    0x42001640c0c2d031510911681a108800030760404801c124015000340107007243c18640308604040c46140f410700050400740e5000c01018000081030800c43c903446580300f031440c01c40051040d09507580d82c03000146240c1c041d001d203110480340f41002541c0148000f50011070b1010700780082c600d283c6403104220040d0810a011240511091403100501880b108012000b010b1100268100d0b0003500c00034000c4582e949252030389074101034007000031030054070503264024050b03500305690395542c000180c0c0c54403e0300102440c64501d41d0500c107405a0540c04605050168011100d4200d042000c440b080c02c400d10a44102000723940f42090040080c4c0301c0260405102811034415521814405003150070507003100401c0c4202041e02e4014030000d010303050f0400e407030000851850030940c640c05440d1040300c600441c07800c0b201000c24090101000072016413001c00300031a131203590f200f00098103148038000b1980324504140c1c5444803480c04008550144800402c1c24018160301c100391480500d80b086180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 177526735 1250 177525485 177525487
    0x7031214030a050915011d060301150b0301030b010803090f0613080f0c01120515011103160c0509070e1c0203070f090507140901050d0f020d090503090f01081009050408 74
    0x191550040101960065003100c42c041020710b44410214134044003418111007603403101004000d888420750114200540e0701212035141d03942c00380807a01400289948208002a03601c0000341c40301900c0245d8141e910a00c0d18410590f603483c045940ea01800202c254070a020452150b6140345c668010400e090420001c4048aa52550181e0818000382008002900103400b003074510343e800303580340c054014110b104001c982084041c0341c010110300002c103414080c2245c0058000101001958900e0540304c19840a0404915042c070b0034207160f108287c001c02d8003070003081c002ca008051440889401030005410000c1440d80000c141600b200180d800d80191040803901245144062000d031054036808107140c184000c0062828021250760b12000300e003480140500c2ea4080101c4480c0c400825000c1402034000020341d00900c00c02c1000766400340340072400340c10030001001070300c000301041352120090741d10a4011340f0240412503000140990301c2c030090000141e6544000d410500520004d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 177527985 1250 177526735 177526757
    0x306010c0609020301050c03012c160c060606020102040303030e0d081f0306050916120809040f0e06041a060103021c1a100908010506220509010e0102131a0408070312 73
    0x845d003125000d0f1560260080d0000040c8401405906082040c6c40c0d10407201340725000075000d450800c1c9020f080400300080f462031000d401449800c1174100140c024204000c0326a69006c0a4001d502074802100482d08103031040e10031003000f10340703160b200e0a070740c42c0c0801030340c1e6400f44469178101c800702030003410503414404004148117105152140440e8401000041500300e0703400b0303800e640b90b441400102010805800003404807010748803114015200440c44a500d0040030b806401034004121051040740300300320030f001180361400c244e50003000e4803400795103d0200460a0344254180d001030100403800e0f06500c0c525903030141c0040140c48003440c804070344440004603c061000007120028040481c00e20ac203220a104268102d40c08a800404105060b0340e20f141152241c0d20390300302150f903000021000d803401c2d0020440c3c481d81c0300003107558000c4001c80700341220041c041d205500c680303901e08c40750700d61520040340d00359081040144222441c40e59010300d0104001c40001c2001880050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 177529235 1250 177527985 177527989
    0x60a050c0408070b03060a080a02010203121e071e03060f050105070c0306090305030117071a0c0a02100f03060807050616080f03040809042301120f1704060807030209060306010c060902 81
    0x141001400c91391501c584e0328140401044000d81e103541000318150000e0441d000141e800000311501c0b8184502c41d0980c03a0780e00d6000700b0101003410a4460051502c000f080907103540403504c1d288800440c01006180ac001c890201c0856556000700700501487c84000d0020750b008030301803c4000d00c81d00d00f240c9465220f54481e01580c1c0421001c0300403c2c00400180100e05150141d030105000c0074008240552600f0f00611501c0c072241018540c0c9400003071401c05000e802e000f00c01c48160007078144041c83c0400e031002000c0354402c40b01031001900e010000700b00600c0101b00a400c48200800407801c010000315140500801d490088507440030420004409204442c040c61245025031f15060721610300074248400d49280c00501c62211401c0d002ca01030b00141b00980e181510416441403102c0c0c1d0583c90004101015202c5c0038042031400b00d403c43c601c3d4120b10003007099070b81d01e50300c0c81c640351101c1000f502030b40108900194468424030018503554401e0034421441e40c0559030101e000c540b0790300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 177530485 1250 177529235 177529243
    0xe1507060216020a06020a0f0b091c0810060c020a06050c100c030b0a0e060a090c02070b07081803060108070303030c091d09011d03070803040f140105040203100608060a050c0408 78
    0x7038007100703401c000c14150055107420f01c2d290004100078005001f20340c546964000110400090040004000c2004600e100e0420000880480d11013047c0710000042c103c4041c016250854541200c0c07640c025020a14a2080320001035856000d058807044509001c01074480750440c1d042115075215001b201c1288808a0084404090043c0c500041c020001010300000a61541001450020241c244945501e400f10080200c81040c400021a103890f444101d09088031036020030258103002c100d002c00c4c02107042c028000c21800b58044444107068005154899009208402d1203800113041040424002c0c0c003d0341d10103a01d40f40c00034200307860b201c4d0001c940800c003605440340c540720400c0142290091103018241001c40d12660142840044040d50701d00c80c0020040c05400b001c4041400c0051050003100100c1d44500907500e0b210180c00841e0003810120740992081c416030003495003041d1302d4819032050300ca0b954040c0003240c4c0e411054001400019014040e181800c0000007003c0c40144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 177531735 1250 177530485 177530497
    0x9010f0305060121030e0301020c070f05040b0a081b03010b0a1211040b24040512030a0201140c030601030c14031008070b0405030d0c0f0b0411010305070c030e15070602 74
    0x801102560560404074a01201600600fa11000810703807098140c1c03002e10030039011a49460903083c01d541d4403000c2406030041540f400c50611640c8d5010840c8110b81c2240e00940d0300070384080000240722800c003e40d0308001e119154003600f03c0b04106002c0d01e9112807c10480d6800750001c54546130007400310b003484c10700da8400959401c203d00144200710032007112185255007103d081c03080100700c0b000035520f003440f403504440e01e00341440e030844410b045600b41c3c1c0c001c0c00002e081d20840d000f415251a1240d02414203040154038058200d020303c032007a22400e0145000021441c03e40d960b180c01503004048400d4080144560041c207000c80a41c039800551040c1c4208148007201440c040560749400d159401400359140140010702050f1400200003041c001645071800c070351350791410f044401c0b001c1058042c00483c1e400040100f403100070300d43c080402c14282c4c1c042142e9a141203003142d001009800040c0010344070f2203114158640300903000200040c04071800d140c007511341c4d5090105c1e4060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 177532985 1250 177531735 177531749
    0xc0702090f0402011d010905041d01020304050c0913081204020d02030f0115060504030b04110622051e090c0a030e03040905060f0102030717071103010f05060f12030f0d0b0901 77
    0x12100b04011035034407110b0b1804446080c403804220000820001e040740880b40101d42c065541d43d000380c4400b015401c680010208144001c6590b800c043c20260f8450510b02008c0c0d0052103240049041a01c46040c00d100075a00000c1c0700342801201e2514030080d02e800b6205070ba0001304400e9100c0565400e000e54014000700030b00000780082c84036803454452441358000c0041c41030521042000c13034140203046034060781c40181d00c618031003c000020800e01461200080c0c8a1070030601c1d00070001c030400041d0603600c0440b4504000160310f49510782e0704030140ca026411038010b0020900001407000644480026400c020a85c2400d2104413442e5803c6a804000d4113510740c020321455041c440d003c42c00c0010284080c624120803900d4200da035071000c501d60090368100081140c140002070320181e032640f00c0140280b150714403000400c800390000f566454460b8410303204030302c3d80e460310f4aa410800307290035019500f854461440b10105400072103e036050581c46001002c60f41e928888020701074010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 177534235 1250 177532985 177533011
    0x304091505032418100906060305061801061203020a060e07120602040f0b0721181403101b080402040b12030301030302060f07090e1e09010b01030b06040303080705030c070209 77
    0x703400c100f01030000020308854103002102196003640c080102d0800e2103040c02d484085086005440c4c520000c0c19070b580007810600170303031044c011103c04071701c88061000c501d00001c1c840340b070701c41c0a402c510241d00354005015074020409400003c8183d0001c0c0c15191003c07099828550359541410510202a44229540b0303500140601000441d0800d800282080c00c40c40e500b40141031ba600700001c2d03e203400303007820300d222003080b451050700c600046042c10384602400c0103001e0b541d210001400300009403040c0700c2d0003526a140c103460300f10300c21450300140c090100082c020542c00c0545110201403c07d0f070700940c4403100e060035074680e961f90600c041b2a9100440c0d507980f40d810000c1c00d02a0103003003180085003034020710100c036174490381030020b440c02c441e511606c64441059445401d88890b845800800c5030340104881c10307506502a090307142080e202800710301d400104010703851196020040115100c030000c03c001030303c100040c66100b04240c1c5003074603103c210b40009105180441e004540d00312 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 177535485 1250 177534235 177534283
    0x2e0504030512030c270d150c0c020108150d17220506040b0d0209030105070f110105010b12090a0501110703093206041a1207020f030409150503 63
    0x1c081021203035080e6907010550943c03c00c45000401489650220225421041d0000700d02c0e25048040450501008040c62040d04c8140b80c0445c02082d07100d03010400c1440d00b1003103c1c0145c041e0003492400c5a0582d40c40f05240d03200c0e0f00c1a05c0313100682050f2504840481c0d501c0000586800c100e546142000c0961629800c4c1c071494111040303800c0300d062041a084980404c0180c5441c1d05840680f602005195207a80c2503c1c1d060000b03000d428102ca525608120910420682142e090b040d00c00d410394440001c1e50450640728203a54082c4580c1c05c80e0242080200c44c64240002c01641008010040d03070b092041d99103030107007500c2040c0700702040e07031200262017002c01d43c210708a000284620480e185001d0302d110148500111551031040e40c0102e1819583c20a0741c0f030380100d034083c0039500c03155561131014a070b04100b5900907801c030b05c01040d01040494041400007414030b20421500c0c0c003c5190508203010b0401406850920103c115003480e0f000c101a0b03001d12140c42e8206541d4a1802001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 177536735 1250 177535485 177535493
    0x80f0d021212040f080706060312050906070b13080703030501060e0a080a020d0c1e030203010b061e0705010219030b03070608090a02060304020d02040603050a1103120403022e050403 80
    0x208144401905550001125014000e0554156191800e0110300c101041d5107600f000b8030504030300314004210b041c00007144003c000c016032001c010340e0700034040c0704a22640000e081d00d251040908542d801403050100c1c070005102c2860304c3e43d000074103542c03800d0080500e40d13600340c940d044140201c02213074035000140596507118004001c1e0650803140d4500d1185004840754a560004e00064021002c5103608000d009213003510400402001c0401500034070300e2003000c0000c403e0b81c0001ca01c41d5081805948942c9414401d0303071036000d5800302c40d0030f4010b003c07036100000f0f500c03041c82111155020311858004180340c200401b283c511035100804c0c0f03031280c0000c05041140c550051001d0209150a015001e500043d58422403941502c1c200d60302d86480c00050308040c00f001c0c0c02075000d401e10001000300807000c504810b0061007210340158003804501059140c1d1542d418101d25280700344000c20140ca059008030240c100700072030800c42040f00340c03103140c5001c0c15070760030002050002a00708100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 177537985 1250 177536735 177536743
    0x71d01020705010c032d0905090a05090705130e060f070f02011a0d020616081b06040308070507020d06410a0b19031505090a030804082101080f 63
    0x10400d00c05000154240000a8000c065900c4c01804000004c68a840300c0800d00140307180000441c40c000c81c02a80b4650001c04083c1c041c0141790041041c507000c56030750030030f43c05000d002e000f00f08007800310795007480d0910031036441030034a40c2d0782c950b10340c1c074084038071242848400c0c0561005003245145141108010308580c00b0040a0011a8074107080c1000a10001e01140c01c06102125108980052800000d0150141d2040a182e01c44010728140401c08140c0003400e0b02070120305000d03840e903081d450160b21000c2c100c0f070203400702c0d01601c002034186109000a010036480140448100002034440a0032212590310189139004030880c8491641421072080d10200801c86c15107213281942d202101e040c5902504500400d51a00c0300251325980706042c100e40303410750003030300e1744919a00c3c10034180b03030701c203010440b00c0d51807500000c101042d00100e40001c0743c0e038040e2500c444030b84860340da415259101049425442819803440034140b403803030b03130101d000340300800040c00c0000072a0806810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 177539235 1250 177537985 177538037
    0x1a0a05060108190c0e090a0c02010c0207210804080a0c1e050d02060a03110d06150302030105100c142a010306030b040609030e060f0d0b01020303011d09010e01020307 73
    0x18082d080c03040040205041c840e50381d4200c00080d01059001d80303604259120102d070324040e0342c429003100411210101c640d2062900d0380d000d600903c548804801c00b82d8440b44280540900b0032541c1030511100c0d20071401031442030384603c0140389082e5581e4805418000040000c0728056000b1504102400c0c009200c03d0842c800d0060700900300c0c2c40c050010f03444058000c0000d00806000c0b40b620481c9000741d0207500b0008001b100c0680e9081040c80d0300d0014602c038081c0c403080c0140385140f849018403d2080c0c0381a2040940720000d016001300041da032883d0211011503c111191030b119882540c140800b00c2ca01c0000c1c0580052540c4414034070303201e16400c0316254109031410308204003182d000c0010070341094000900107801c004500301100c81c259009159900402c002441040014400d0000c08450348801c0c1d0822a20701d000004903260f01c020b200b00e0284540f030a141070b51103400010b1540e08807900d03100009100003250100c3e0b007642c008580000c00700f200e441641414201c8107002c810707 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177540485 1250 177539235 177539237
    0x60606030203090a060b060706060303020717060c09090a1104080c040b12032a0d0c050f010e0c280f080601150f0503071b080310060c0c0b0310031a0a050601 69
    0x1045107010a9401c4d030b24106550090159a12443c0740000b07500c0300750403a68001d40290090228a440f400e001c0d41d42c040c6445032007002003140100188414000c0342590180001e001060303d46003501c400c00c408044060300c4665072550b2100a0a40000c0d984001c00003004540081c20071045002c017044100c44a000409014510031036580040040104c1120500c1070942a8680034100b00d250650044642490403400c80c0303d004c00e014030258004401c4c9041610600840d0240499264a0390985034880b00340c4c000342d4003121000c1c00300e01c0e1003c030401c02c0140041c0c80081700114540c04d000d21a03c03e500940c4892503441050050000c2409035501415448281a00460318200000c000202c514803c40030040701102145000740f05114410900030a0340307042e450342c4143d0610980c154015103124082c80600382000172624041d040c05210300e03810002c0310003103610704001164207a0004050b140c0541e050800407001a40c3c041c11003a9208055504544516104080c2070032600e02524141c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177541735 1250 177540485 177540487
    0x7020c1201020906040510090b0f0405121501030b06012105010503120307080c090a080616030b12120315030d020a060c05091c031b0f02030c1c0305030c1606090606060302 75
    0x100c1d035030300c407a1300715021118103a40c0c01204e0400d04008684254458009107154100018080407000010015100b612011034812070984000412590b0341c4025102c04400030312004010170204034170740b0006600c004181000d8402c01c000c00c000024100c0031f20800c0321384681e64801030119042c00c000d00c0d900421044981851400c0803280607001c0000201440011140040c00c14140e4880c2030040c8010482c4500311402c43c10400c480380c0d0312888406054002030f01c0c0c80c00400d0740307103003404003130340442040d0000d045c4019040d440310095920045c0003a052880001890045450811407982e5166141c3c1c05402201c1140c0b44c01010798a64100d03a07810800103010040d8990345022900d0740c034407115100440300404500e0203450201800424000020b14015040203016051055440307452084080ea041040074404100b000d0030086124081103400c2c02c40c1000003802940110b800903a1030080f1f504000358010301002800d0202012545180c9800e0a80700b0000140507010203020641825 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177542985 1250 177541735 177541747
    0xf010b0a091203120507031a0405061503040c03050a12090e1611010e0706120b0303160209040c1e0e06030a120c0c0e0c04030b0106020a03050a0e0111010507020c120102 74
    0x385010796500038002e0942401c004901014040c142c0d01c684c044d0300c1c1c28140b00c14644854040c0061031240802020f611203003031071001700c0ca000c0c0306185c4120401802068207034943c0d00d5020a90308020001c031020a12040c1c08004900104245001c040c07052a00030711100c45000001e08810721a070102c0c81d400c1020062207546903205107040142081450600c20308101d0011141c05004814540310260007010400314078543c1c4a9040038043c0c1d2602c5040c408c880c16141410759030303c0f481103c81c0700d100c02c4036840d074014035014001c80e8010b40101001e0300ca050710307001c192080b121081008584e040081400f00b142c4844007850690006045000d040010f145407036500c030882d107012900c0200480d000031401007000c02c140d0503001e4507565404600d145840403580390998800d01007940c11241110000480741c3c400a0800e40c9250305940d018100b841c111819a00d00314615942ca06120701c1c04000480b0500c02d1103020311485040d0b008280260240c02400800072011000407100d074010840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177544235 1250 177542985 177542987
    0x15020301060e060309011d01051605120705070503040e0a05160f0210022a0a06050c070c0506160605040501091b050315090304260c04090b130809030a0501050f010b0a 73
    0x34007054101c1603d8103a505c0d951748074080e00422220840c00707103100035002245e40600c415171020b0710a010220401d401804204415501401011001513204030050001580584170b18080e00e004c03413040f02168103280d242d207540740c0402000c640c0c0400d86562078082241200c0340d4400c1e10152000d600300100d02c10710201d0025141d00000210841040d00019034016911034600040c07242e007007140400d41a0040750220701d4031075011003000d9440f282844042680710b00c90100321442980c2c80140d0303c51480c82c1006220b0242c20411408501031000d00b0542d02043c881d006042c81984104000075503445d56103000e1034520842030f05281e42c0401c084080c0641d0700e001071504811141e41d4882200c40e5111040c00d03140d44580c0d004650f210070b00040c0c4e400000c0504c0481c00211810009403400312506800340030031100802e102030619071402000c10540031003080d0303a40034280604900781c03911000b2800b0901c2d010030000102d0f066035468081100e200d4055580c0313405000803542d51407810b40a00380c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177545485 1250 177544235 177544247
    0xa09140a0504030c1209210506331801170f030a021f060302120d0801092c01110313020102060f04020102150c04050406170c01020d02101e1401031502030106 69
    0x4010002982044111400741c0500100c100406140c0300c0100c7c0e0462a1802c0b110740c803c0490101c0315441124007180160011140b01c6614041c9013803c0b90002c0e0702900380c5c0c0580300558075403580190b00200c0d090980310308061524042e161003500350400d006a0800e440c6003138412058103205400c01c0c4883d002841d4003180c624001d01c800003060040014200405000304866440258481c10588201d150700001040b003002c0454551658000c903a65011100141c0e155412a04144c14220300f015034a0482c0346a000514091030000107030030039852403c50748070340c416030310071105616136184030085607410082b59a02c50f5005064036030300d06140d8000b07542e442070407524007945e0001c0d80c0000c400d02000d0060702c0c000c4c9801030091284540d145212114805002840c079102d0050f01c00d0700109500000d40c00032420601d42c0103004207061401c00000030404c00c0c08102020002c00303000070071050300d070144159000036140b400250b54510316007140000495203411222900600040080b00d80041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177546735 1250 177545485 177545507
    0x405011a07140a05061909030503181504081902010b0604140d06020a08010906060e21010605030102040f05090121060216060510031106040f05040f0b0a09140a050403 73
    0x1503003154803001e0614102c082065040e1200b500c5120303c0501000744140052881c1c010704203c90040980c020280020701038906c0d144025005ca0b60400200301002110206c1003410400c1100355500d03007451207030007a90a4410340342900d40060119140b480c0e00200c8840c011280c02c98002003001e0b0541c400850050300980c890701443c10402c508100e8203403500300305148415402001103544540103500580940d20a004031000140703810400b0401070700a66903000107840c0117086c061141503000c2c00f66803492140318214410754071264009542e0b00c0900182000d003500c6001c90b000d0360f0805040c80059041607010390340981c1c09002c0c40c47c804401c8885106516009500036a8499403640c2c0c1c5040c1034540c48004002c145494100484943c5c12040401503034421400002c0c6281064104080e0340103d0180e8802042400010480c918040c3e1140a04078640d5402054054190001810b070b070a0643c4403400003a01c0b088140e21902c0f140c443c00341d000220500820250030903840040101004c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177547985 1250 177546735 177546779
    0xc0a0b07080c1201090c030b0907080a051b0d050a06050a0b0c010b240903151305011113300309090c030c0c08031305011b080610020a0201050a030608120403050c040501 74
    0x6d07800c2060113482500401d0013104040c004a00e079040007000100300b9042191a01c9a807444c04c000304110440c6440c0440811050104080c1400c2244080300c00074840940340d4010303250f8403003000500d40c0b035542042000b40a521040c035110490301c900035003520070311129640b1070b840d0000c0c003040401d83d034000d500170382d0340c412201d075280c25042002c4ad00e0060351030b82e10004c000c951801c100c40a2082000100042c0c4120b000b0f00c1182d088503001656401141c0d420003640400500c00e104940f000300010403507500a8941450201c0c1c40f03116440300a003c0300c410780000b0240d48040c800350516002c0d103d859407291900700058210203000030300d01c01c0c1d44100100b21010001c00b04103c41c07200e4030244045034000c1c00800164010000c0342100802140140000ca200100080d456103444d64030b11101c000c540e009020403120035030044030382e40d016550070020b0540e1110041a200010070200803142408041c4a60311400d42c10f0840c541145001114459401c1600501110100d2035001110580d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177549235 1250 177547985 177547991
    0xe011d0606060406210213061b15090201020c040c02010209010206010f180216050d02070501091403030703030209060f070609030e06031e090c1c0c0512120f0c0a0b07080c120109 78
    0x1040c6054050040c81c00740005c442c00421002c00c018000ca6648040f0b511985900b03400034040c0c92909094405050060110345450740038003d40e81e140c0c0c000725000c07032052040d038803404100000942200c04a01d9000d0050703501203002c10141d601081030a0140201d003103200c110701e1810010820303d01c143c0341050720303194000c80c00340309841d081c0e000003802562110580f0180490010002e60f5602d0310700c1114001070680c04001100d1010341d500b1400000050702540c5400080e44040e0065806541d0403a0046001c000003044840408040c00e0f00750300c071700400b10b840645800c008082e0300d6070841162244008101707100f000303800015030300c142c4091005d0b02070f502d03620800d003c1e0404800d02102608040e0403011950101c040500d109240e6110380c16607165a61158107203c100200c0c2041a5042c1d0311921040000c7e00224010742030a01d81c070950b03203242c085e10944460030181c60b240b0403510401c8035014001c586400c000c40d203512000501703a050802d412065580c00385e041c18824086100d80e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177550485 1250 177549235 177549257
    0xc060813120c080714070b0c03040306020310030c1e0e07020606010e030f121c0c08130813080d0e0328060f05070216050603070c110d060e011d0606060406 68
    0x4050740031220341c20b0700003e1141e02c0e180241041030202c580c600b9910341c0303400703208000714280600405a801c85e4244900440c10a415562010000e50001d4440c200e49614241d001001542c07011400c00504000382e00030040491035034442601c550386821a4514100d00740403c290300d5030001d5402e0344201c0900c2d00c40d005103103c0c00843e082c4100704903008418061007481e01c442c03985c000000c04803010040704045002c030001c5040001c41c0c0383c03400004009055400410311002803e08501900c0f40902200b0f450400c86c429014648605648280c89a4000341d06000a140d00014841c1c2e00001c1907002d018900b02000840d2080c4100720000c46000994203405000e01020364810310914501a408100c02c0c201420041d54400d44010b80c225003410103d000300d00b508102d801d503070092000b9140d00e003580c001c540d00c103802601e840b04000c0e000761618540c00089591340c06051140070342040006000450040203843c004803060b085280ca038415001e102640d10f80c80100d80c00c0750401d00c0c02642500c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177551735 1250 177550485 177550487
    0xa1107020907031d160509070c080f13141c02061b01021b0606091006080708130510021b030403020f0105030c040f03051024090f1410030c06081312 65
    0x20900c0a40d04118820b50460221805400117502480611441d0b8a8141655a0041284020781281c1403000500c14003103071000920040d01403c8045d0100b02058100a06851100e40959441e4820725034408124100d90207401c0c55504064181014007011600d050982c02107a55449040ca90100b00c0e10345245408040d8002c4d8183d5800c0c1074201d03106600350b03004000403a07440100b516614468403c4c90045404826505040022a10140c60309541951401d0054900580c01032071100d501c8154050880000c4091001000c061880c0705d00507103900d81c00300290151002c060b10f0f035526034402c01080c005a41d44501e005e2041d01c00b441e065550742e4440c00840f40502030307980b040d40da018032a034020080050100b0021440c100c003580c10042c0c0489501010042021101c00a0900040070810f0200380403d80101d01602120b50002c1440040464000c4902c42c08488428000c00d10302d07410b00400c060301c07035900028429850320743e0460030002240040c007090301d1401024801110000e080031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177552985 1250 177551735 177551741
    0x2010b0f120a0218071707090311010e032e020f09090a0204050907020d1701260f0708100b03030a09060318020d06050f06011d091b0a050d050a110702090703 69
    0x400d502404e0f98030720220220844000410945010000c180c0c0ca4824546100d02030142c64401e03130550351070540b16441c645914030b2000300500d0300c40c100000280da121480c1c40811551010642d0480c047c040c0002c15160141c20140a010030080d00f801003200340340c1303aa4424152030880300c0413a1490810740b00c0108200091080b50b02442c3c203d0003110402001c56004500c0c1c030305c80406a200d88080070001c2c001d4941a1038240508040d4030344581400c4a00e108203954210180004022a0a0b0101c0f840400d031074004164424171141c0d00200300154041d50754020f88088060a030000c40c1000300c500005450030182e03016038010160740700c00c544420800000c5900c0303c150060044540380c9000d04004025000445069624840c00c001080c4194031840000c888440e0010802080248807000c0010084010300b4240d12240700843d014041e0300d501c1c0081c00343e20300546440356204000500e4070141c074001071035440510b1601c000d17148140c04690484004d03540c100c500e1200f581d1508401c0d001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177554235 1250 177552985 177553003
    0xb0d060f0308041d06090c030402030a0b0a0e070515220905010b0909090a020604050d0507080601140307080f0303060d021201060609090e0303010513021e0708041502010b0f12 77
    0x590110400c000080c02266002442030b510282100311080d19a80c90001581c001a18220b800040410003c0c8043c40100701031a08944004c00380c2d020b25182c0d440f000c0090710142d600302c1340981d81e19201001000100025001040d0546410032021300c1c41c00700141074051000c41104903040780c180c610540074160510350280c590440c0400c01540c68500085060f0800c044e01d60295201d000402e8030007400060034004184d00801d920715240c2040c051161180c1218022112032140c0d140100d6240000e1180e140130b04540618100c683c40d0460070140342008561003240c442e000082c030300f4102a0044101c0e540224240c41c0d40303520361100e00c0410724000a00071110400d520b80304001c00c01ca540300c00b9401c215200040240b0014503d07010719500c2c0d1000b84105076002051164101c003581590f0060607185400c2d01802d4041400003400304041e03401b900c0c08552100c07002400b8080c1c50a481441d5941c00c17007510082266546c07000220b85c54424010403107210701a400c541c2c0718034100400103110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177555485 1250 177554235 177554249
    0xe030915070f1a011e06050f0c030c0c042406080402060f0c1b0328020a1701020304260d0905070915180203060108010e0a060b030f040204060f0f0b0d06 67
    0x5042126410041e030f680c0940500c0341010742504000007004868015004c491900307095000c0c8409180c01c105a6050b804003031403500d216000c0c00000340846042c030181040503c450301818540d100a4104812186041000710442c4a49600d103428005071515203020f0303422070b080640894490740000f6009014440c0c160840400000c0d43d2000745c3e10100c1e115200002242000303031850200e05c00c142d140d01d200c08010075640c00c0715044040c60005a682a10428000341428401d0b540b65400c00c0c0d000885041849030a030340020a0008200d140d4408003203640c062440c04082c24590f00c964001e0340314840c1410319980e1551041c071306218007801140d0081003055410030031020b0816540f44611620311694031049210203c03460008468022a441010140e407041c841e60700340b03071035003a00110107002c04100d190f41c1c88001c907410a110008500a090000c1d42190a2500d84100000d03103442c1d410015421403803d500b0441600d40c02e60104c00c1d5009a5121038036a07100494010040c501544658 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177556735 1250 177555485 177555503
    0x5031906120b01060206070f05071707080a090f03110f0432091c1404030203120d050601031e0218100903120e0303070f0501090209160e01030e03091507 67
    0x16490388000072418045100c0c00d1079a42c1c60b83e0f28403081ea01e880c8112140300c00b00e90446254090b40384200010b160b564861085d4084a00c580035150400750044401161404000181070203419040f44040e8010081480c24192240c110f50380c86840282d035a0005000d5000424400e040b99200e8112150080c90542c2443d070715290141c8001545002c2604030603003002c0900420308809000c90540c06104200d03014000d509940c040c1200c4180848820022104081c80701200580d400d000c010410001080859124402d150540d02101d4000d0308050515107840e80b140c205080ba20102e80c500b120b500801a116110420910403540e1a41e041d26448840755524400701500100c413001941d0003aa07080741400c100407000c0c1c40c50300e1500b100320390503070003480b42c1c100250130b4101c0100d10303e100318004600603403940d010880d60001070b90a5030105541300201c030405e5610100b500e40d0b4040918003484915502e402040e100c1c403800024600804020b03004a584a0b4850122021558411002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177557985 1250 177556735 177556739
    0xa03050d02120f151206070f210203150f010c02010e0f1c050c010c0f15021209010e061617040201030608030c01090507060c1505100801062405030f010605031906 71
    0x2a00b003c1008a81c0c0d5000350902e00000c220a00f4440c1d4101040e4000e04000c1603540c9030490246d603a800c00d113260750704100250a030b0101744041d400c80200b1072000e8100158890401d28480c0c502100f914090a02420040595400c2aa444001d007480720f502800c0c0706030501508d00108010300c800501058001c054840c1c0c1001d0542d180c042407122074002c10954000c1400c19004550302c401c6058058032030710f0b91082c0d0001044050440e60784617100050014a0031860381105880c226040310b180e251a595030350300c2070611005201d0154065580d046644898181d164041d00031911000b81085800c41000001c045900991000b400341901800f1691540c401040312400ba0814a0040724a4001c1e07000009003107004d04010b80c2801d9119001410b216811082003004120040c00550400d10505000030035000a100d101d01a00306825000b442001c010708040007414400000001c000c07040040000400705180c0c4a415900b003490103594035112074502c910056202140301c1103051400c900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177559235 1250 177557985 177558001
    0x70512031b01020f070308040b0a020304050d0f05130b03040309080c011d030106080a0b1006021b04020304051f06030303110405150a0203070c0e0a05090a110f03030403060903050c100e0a03050d0212 87
    0x224920443c2724007a841c0550b511005280180d0205950090040e48010110204540241c0c9440c1101c2c10b10f2400c581080402c0040010724400c1d544850000980002070006056001c50010064000300e0b0061241c3e25060000801d0360342e002440c900390048030220700d5140e80e800e4001d1001001d0741400c0750003c403640e003400352410f14161001c20b0101e24929001980c107001050f403800034100c400d91582e0400d8200c0501010b5400100115114018a24180800303c265102c20301a03031182d4a001031114114038010702103a01d90840d6445c078900904c0104921780e00d601e82000c003600c0c0218000d40f10f03200b185059146019030030000f007034409204008160f0555091680b48141c88991091000da241c0d20fa102d501c40b454484082d0100c4c03903407012404d03182031440c0038002c1c10601404485c42c05030340e6101d080c00c582030039030102d0004030005900d103c122000c004101146c1080790f81000407020042c1c50541c0d80740c0a0301c004040c40307804a900d1096807529030550342003034003015402c01c00e0315041350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177560485 1250 177559235 177559247
    0x403060e030a17040c050915220e0105060603063d120b131121010f0602070602030a030b0109030602070308060a092f0c070303030b03070512031b01020f0703 69
    0x107850000f501095000b0b1030541200d0705507001c1c070780185c01e00008a0800701402540e500051030800302c100d14009641e29500d0b900141302140000e9002c2c68405c010b13014462080d100101506881681014148401c82c3c0e034040c1160b4103c101221407602c154041421049200501010140400340154000446480031031900400840f180d07a9a0f8005690a40001c00c40368004030882c1c1003035040f95100818200b640c424a9201c0118040c00d0500803060844041142030714080c00118420800401141198018000262159001501505081240080d540d0103420713210010035440e4100e480c0caa90203643c924003e140c201406566806880c180500207001c151003503401408c2e0001c0004008045104154000450310101400e6a10424071a40107014540504402c018100303c400714442c000c0251800441c440d4030007040d49582002090309200c0303190b000700d005030340d500c030701c12400303403012041b209110768848200d44401c1c00c500216009005030b04450960000003d00701c414590840 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177561735 1250 177560485 177560497
    0x60a050313112101050f01120201110c0a03080408070510020d080a060e0916090506131e1d0111071a040507090c180b0403030f1b0609061e050f01050d06020403060e03 73
    0x2002802240c0b24007944d1b01c0021401d22030140e080340e0450261005612030744048629440c1e020848401c448039000240441545900031107d050002400300464001804042d00622088460007030940905001a4481030b82c0f00c010f10800c4804000110700c03400b107030306c000003910358400b03074042a180440089984100030341d018040748100342000a1012400e0044a214040140c00ca10b2041003909242c0083c0c807501086207684004030400c0c110321100381c810600312015044d00e141042c201e4011060844200340c00505883d40c0420520022492500c822048000309002104240d0b8560030550300b4580c0d41d801c00130703555090280300c4044640c0140306880026500000a82c215a18640c1c00840c4c41350344001004248241c0d00196140d01804d4071880c505c2101090000c0582d423a40c8030800c9800b403140c03c0343c90680d40c1510070a810302c1203000c45806030100c0010042d45c20031960b008e00510b0144140ca02c1140f40c440400108041074064400444c0d201005008050085481a8a0f0341010f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177562985 1250 177561735 177561799
    0xe04080d020d020a1719020c01060803031003021e0603040f061803050301080106211103071203020703060b010e0307090f0b03150619060807050906040b1611060a05031311 75
    0x1030740c90702841751a01615030700400702c0e19035144543c40c2946c480400b075041921100d03495581c0d10380001d14100e05000451048840d0140605000d05602c10014103004a01e071248843ca454120400e0f02e448d8001102e81054101c51520394480591812402038080d82c64905650610981d03004105900203003d103045e5841e07000240075039501d03201e05404880001c48444070294101100b400440c459055400441c040a81600c0c0c0c000e49072007190465000910b4124010b80c0031400c00c0040c02160710603808150b4003460704070340700540000042e946658902484000e00d40d0f90104440411060b404101044c038054103489240c44d222500c0f44e448a0b00b241c507140505003280041d403480003141c0844050ba0101e8803945e656031184101210250070030b0580c650085020000031400103200409000b000a0310644074079041e00a00c3e11100c1c0301c003144202401031009101e2610403a4022040e07a40c0052100c4020704900350034180044c45c030b0708048080da005025a021741c44d1078141c454090500e0307411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177564235 1250 177562985 177562997
    0x60c11030a031e0c020d021e030a0c08192102030d2c010e210409020304061a060c0a0312060302040612051b01210608100605030c0a050a0e04080d020d020a 68
    0x109001078408131401031000354010b061011601c01440d180d13403803010040c000451100d048140385c0102c1e24040030004c080e6104d070015041081004000c02c120452918880c003e80010402581c510701d42d0130000034100740180c585803c81c2005131080050b0384102e0446c1c0e02c14004050302085040701030000d41d413022035071030b07203030740307015042901405060822100140101140c88840203203555181d060f8902c551081410400040c540c0d2045c00514000d600030380300011000143c200f00600d1fa800e641549000f18801d0110012000011a000c2c00c2650181007140c621405c0c45c0c2c440e4020070b120b400081d4070078035004011031510990441c1c0c00d1124415404c0341e008081d8186c004540c080304d04000c50008038020101c0380111020130280d80c1d910030007000403c6154654802a09064000810103203842e90b501d4200b2051030204420b8226160940389084014145000304404403010b000307070031850b003110000c18200302c420000c9a4000080300c0c011520b507807800d681080070350702c02e0088d8000118 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177565485 1250 177564235 177564287
    0x90e1204120203100507080105210607091d010303090605130b0c0d08100b04060e0d05070e060f04050408090103090503191d1008190209040e10050708090601060c11030a03 75
    0x2600c80e482c000d06081d1111920303030b0b09e004100070701400c0d442c511103446a151010400444030070003c8030f0051b6840e40320f140682c0e04140060512042400d1205521034000340100003007900f000c170b542c06a80e00d91074115030b1b50301900342000100100703070703c2120403e02c001110148801c01040c8144e03001115540e801d2b0ad6160f80018001003072171405075018083c5c08002c00c00150f40603000c11000e140b4050820142c101090305c3c0c16041401550120a1916102c0f080103c0b07890850728001044400320390412190801e51034a003040c0c0148481141031550b40c003111000c1c40700400984807411014895450003400009004100360714101c01c0d00404980c02c411214985050401c0064000096803181c1059070f681e00b00d000d48200b021050340e4640d608011036849610b1791701800010414850040214508440d00307042220802000c400400c1404030601c5038624011a46904541c0d41d07141841c0d6842603410881345120001c948a645031103031044280403d60004501030681d402429a082c00c8a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177566735 1250 177565485 177565513
    0xf0f0f07081b060a120218010e011115040515070e040c030c05090405060103020d0212090c010905010207030b040201171f06052104080903010518070f0f090e1204120203 74
    0x30000751034041503080b0200b2109040000c0600280c2d4280c0c40c08411042200c42d56008a81c4100d000e080040c1e0624042581540c00454000c0c5088007880c09541c154100201039448201811030804010850740200d01404407c0190074032004450b846010302d818a01005024010080d40240c011820116901415070081c4580b808240c91a01c0d41d91502c03041004000062030001c107150305240e401c0c406c19000d41030b14030181c040c407040d182c0016114100001e01a161004000c001030420190308030030b1180b41d0b07001c90100300700d82c0d0242640c400f5413170300c1c401038a8420814030100000080e210802201710030349200034612241c00f0b102c05294940b280740444540c07240ca82240c00e020036084510b9860300001010b1544140600003a0341003c0c40d0070000f07403c5d604144c60401c80d202c4841e00c000d00c191400d10000d40141204000190958a01400419510203e00c2408021903856800140070b41c4103001e030110304054038000d00d42c0c6584550021030f00c2c00200006034000c7c03040703841800580b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177567985 1250 177566735 177566743
    0x80309070e0f010816051503070309120f020601170a29070903140a030509060a03060e0103080301031b06120203060301020d050924060916020a06020a030203010911090d020f01020f0f0f0708 83
    0xf4910141035807c10200c0f02d04911540e51024200070105659103e00c100424544150300703600040784e07581e4407202c02440800174a00707401a000102a021292a02000c6890008074005490341c42246464514014442009085a8031009600168562040040701540703c0e0380002502c1c031800240310000e10380d00320250f44425071640280410001c001f019681d00d80000509452005880c1c0418860b48800382c90314158800c3e8402c0310701110220041c400c10040c501d1004552103210724081c0e01038506840205042452140c005c42d2590020211b00103880071340442c1c143d00d22803a0103000c02d041c070711000c55603110440d4610341a6140080d107182c80040502c031150040c00000d1001c07000d0b445e00700344100c5202e6008007100545c401c05491400243e12030005d0080c285040e10010303182d45c036008260003a120407605806440d2410000e61009a0b143d9000700003440c0c040d56035015260071000180d1404840d030303581120900c0359001324207100c80006a0000100322640c00e550000c0e64506002d80e032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177569235 1250 177567985 177567989
    0x9060f012403050c04080a0b010501111212181507020607020d0c0b06041b050304020109050109030201050d05100b1602030d11030a030507050d060603020d200403080309070e0f010816 80
    0x7800c8107521690041c0c512a40016801480055602d03141c59524901c1c02c0c50241b51403012191200d980c0c004202d150307000910008a03a005038060181811202d00400c0984565a07180c182031046002155800411090120034a1081c0040300c9480d404e081410802e01300c200e4405005125038000242031a01c00f140080c42c1608a0704c441d008030b43d842d6070f080105c038001050140c00c03581d94400880000c000e083c1082242c00c01d92941662820a80001130000615402083c1800198802000143d90008c01c980700c075060910005915141c840e4654100a010350101c00012000f1038100e55070300c3d005102d10f4145200720121060400d2050f0180d80302031640c00094140e40060002e68070050080d0880b540c400400c0c94000d1400061801d00403c4039210b070454000a039011840e03000e000800e124460501340211001d2845c0c43c1d0101b4007148500c910702000b066401d0110104403003240420089010b0320280b2402c2034107107020103951040800034459040039110f01080d40020300c01d03c3c0d4502003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177570485 1250 177569235 177569279
    0x604050105010b1303020d02181008240604090c050402040803040f05040e070b0d240602062a0c070503060f0f2202040b0f090a05090f0316061e020309060f01 69
    0x1400f80e156800700104400030345016a00020a27440c010182c40c40504054441c6190141c8411310b50704003541c642c6030022619004621400154090410a0741c01049940c007010850700400c2c84039051401c441d245600354070644c0c00c2800483d003c16000404009402502c0c90142c810050b681d40c1d50410058400c401800b48154004400c20b100b0700501c180204040c20444d0004904003000095501d900c0c21616440940d1100040e0240255079041c0314203604404402007510200d003030000204607200607000381c000d07106800501b035507290405000c0305008003c002c00303448482c5400000c842011004540d41205140c028002800385103c2c560340d80130094192001841222243d42070100900010060740e50005155280c40d0a83d55084101c034480c403102c940100d200d00741803106600d01007100070151580e40040c0140000300b0f822821409200350402c0001c03801104200d00c1c1d001c042e4a060344602d800d8000403c0000c5400700149190251020852861242e80e031540d10300070300148110400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177571735 1250 177570485 177570517
    0x1c080306040b15040602010c0f0503090c01080603070b0c010504050d0504030f02090a29040b01020c0f060a1103030907032108060904330b09010e012112020604050105010b 75
    0xd4001d0416600540007044094203103a24088a03101c00400c940041e404280103039181c902152415074880034034142e030900c60030603d00b542089048141c603039640320f125504000ea600c00068081d03070304001e200300600c55928001ea8800a1030186c60182204460a851070300c500244250342e540f04504440c222034000f041038517825595401c0280b036200c081c2810100c19111241c100d20003407900a01080c81020000c0c0c920104021b005000c29140b072030300c0090564101081c00740b0300340c41d454031014807020116121903031441010701c10b07210f415000c0c60b401554031020007085080030000075480140c030b000300b414620742e1001c0030340c6041d041d02030013090000072483d1000c1011b0741004066940c01030304c1409161580b0302c10305403040c41110f03048111103003540f01c50600107803400b840c07181e500142002e8548440a40c10440c0400968006214445003001072008802182e0070f0410501c030f00d03503803010b2100841c0c03000b200025515101590151920f519120000820640c00300c111050747d41da180c01a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177572985 1250 177571735 177571741
    0x6090605090105070b1302040605090721090c0305070806090304141c0510091a041a0405010902130207060f0b03102c010207121107050904030c0c0e01051c0803 70
    0x21105500301c10021814803405000003800100318040191254100c5601030014041c00e004200c1510250703448240555900814446682e90201d100102c0d002d0219448038a82400c040040003415a400c01408480c480c01c000b07c10460041488400ca40d80807048500b01d4460360507113170301c910692050440300c50480e03142c80807500f030200310300d460907200b00d43c03810b42240ca644640d41071078582c1140d0204240e6580200c01040206c04821804425a50000c0d2180c6429518590700d2910311302140d0150184600181c10030109401481c00194080c00d50810901510a20006074000c44d20032180d29003030101994010915110307124940c1001001008040c0c2d407610307510010070f03180808548045051031580300c41c001d850300e00300c86200f852000681d9041d581c00d100140f11080400c078810015055001c40d510310000500d4010348800f1039203890552500d150903248400a40c00c02030640541580000c0ca008000c44894100c80307094070361010081e850180a9040c115107040107004440600c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177574235 1250 177572985 177572987
    0x18051003020d230106090608060103020a090509120d020a08010504090c09020f0c070f030201091505030114120a060b0111120d050703090c0b04051c020d0b091e070312020304060906 79
    0x2009000b42c0c001d2802070200c50b4a000d4940c0030101100c075810440c0c5d1662810440d14001c0d2055100510300c002c09041c0c50350565001801c8078a0510403041010744440101e000c8a0003071004050741d40802c0012903850400050080c081e40002d0a10000320742c107800002401c0c05d090184032000d60307000da0704224050410800400a4200e0404142d40315424440d002c40c90004000b10400351250a101058842c5507200040c411041600000e50848481141083d581e421109803810340d0800015201f0307114040700031840600e1042145941803056010500074480039a10100fa0710000381d035100d121900c0e4102540d526801070035000e8031a00c3c01c00a1102c0d2050580c005900702c030301454045040c00321030315031300111080b64210030700800c0002010440b601e02006004909100b418000319101c000b44c002400d000344192020f006003087c20002001440e003407120b1194070051035030b00c0750045e441d070805035031f2901c1500040300c1d40315030284050300c13081c000815201211b520b80d860380740490a20030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177575485 1250 177574235 177574249
    0x30c030509040c020319030b06071502072012030c0c120c0a031203060816231207060212030c160c0b03070f02061003020f01050a091208041805100302 66
    0x640400805022001003541c49016201201565500540c1c40d0010b0300d4803600450f4489180c40d050520300710400415840301070540d0010354010002407490381e03411042e8000b0f8414260700401607400c1015083c07941190f0040991880310580c0c1141611000704045641da2061102d0b00340c40c5d40c8900b003101d2561902e90900c000455a0303030182c40940d40404046103c040c0c01d90003ca03400c113031181c0800440c50741807040c0030003400c041004180c3c5100c44c1c0d200d500622130901465070000000343d10005a0f1120503c502189480a0b0070315001d0b1900c01c1580352200014010300c801401548000b00310714640000362401122101b9959180100070382d074030855084003400031107030700d886424000b030312100e01d0000d540320305080e40750490a1541c0d010020300f001c1004050504011090380f00f44007507160a9003c01c0010402e0030000e43e20010110160b400100c1584690340c3c10b582c1d020100104280c15001e0700032115020181101ca003004800c41c1c00351a02291106074400100d4020009441c5c092 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177576735 1250 177575485 177575507
    0xb19140405131503060e240402060d02090a0320060421052a0103110c07030303020c07081e1608150a14090105070206090f12090315070305070909140403 67
    0x100c0000e43c2c20354000b41d0b42e42070041075109440c090354401074803070b040c1d40074070000120300c0f400070195200d1109880030b2241ea02002e0070180c029000441c1000d01661254111081c41c5c0c001010329031141d90300d2400914800030700941c00d43c0c08201d60904805420a6001e8400740c0b8890145a1540200714441c21507140491030151803030300c030304200680d8920550058041c00c900300b201150882d84042d0014080d100e00c41803603601035a0030884c420000c403000c203c41003681d074180360160351850798002c400e242200d140c0045d03a8a0145900707645030986c0d00112000c0000405059401d604c50290304401c80f9000741c46410720710b4010711300c0380008404003610107902940700e450000b40c039490a05625021320040b19000c82c0340e076445050281b01501049100d5109402a0040030140c41c1c185130035488100f080745011526402050707400c029a41409418100050020300b02060324103080020094001a1081c0d000302c0e8103c5008180d000050003150600f140c584008506501c0c1d03a81c049542d55400703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177577985 1250 177576735 177576769
    0x11030304051e2b1103160806090f0303160c06060e0a0b031203090c09040c0e090304060305150a030f020411030a09140a020108190608070b19140405 65
    0xc0001086503a1a02c80845000c4a69410440540d4240b41846182c4072101c0c0306101e1a903500d2110b007848024140c00d18922030380020400761501c58480400e00c0c2025819005502c842d56103000300d060b010025105108601c1103040b41c42c00c1081c505000e072a44815a0b49102c2d941c0d001100c107101c24000c075030a02ca110322503680002c00030740c1c42c04401c0f9004030590b050760846464250070710a914080200312151494100000d1860501e055050b07541e111504056004054640c001810f0080c4c81040b40014054071600e0302c282c0c45c08160541e1647e10501601d801319251101040c1d40d15282d0740c9503150f960000d003400e90864103545070510f860306c0c2c9070300807030740079498003400804040c20001540c002c0c040d9600c04514140145014a10714a030362989952039440900b40c800583c0c2e001a44c1a040790b501c80c4c600950424106030305014142c00d80001c031071071040400001e6051502002410764040c02d0030515680c9000340d0085505104031192040302000c2803005102d103141601d594410b0041b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177579235 1250 177577985 177577987
    0x10504060f0e191803111b040902010302040b0307030603120507020a0b0903030d09061506050c03030106110a05030c06070f031a06030a060f03050d0905240f07021915030c020604110303 81
    0xb11095890a031000c0c0c444e802e480d00e002e4040c113000c00d5040030000014900c213901503c003002184060004512100041d03070f1140b61201d59000959010340d04640107000410007107507403417400600243c0640300920013158400400314850b1000c0d03200f4016a40b40543c01000300340c8451805c07c4460041c2c00c00303021258907000c10028800306000760300c92100c29030301c5110f01040018812a0781d25801031942d000c502807100410122056100c04411603041d543c1c00c0c101440c03071640e03c4003075500d80b0101a030014034a210003d09a9401c404c00500c03030303209004961751030204180e00c03042201680d0b1b1541c294580340050440c00c55031440d084000d075a114400400003d81c0c1c50f41c0700e085500c0c0300d9580c0e109482c150000150009520ba0061400300a00419914100603030b000400040c15843c1303070102d4001c184d85c049803541c04480c0441c02c407915035800500e0b501c4461196038003501941864404c058000c0e00030101c2d890094080e020b51124842da40d0058400f583e03603603d03404452121142c2007075040c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177580485 1250 177579235 177579271
    0x210050c030d1505030316060b0102010e03090d080f030f063d05090a0b0c0708210307050702040e01020a080603060714130e0c07031112030103030e040908040b0d05010504060f0e 78
    0x4040007e17000c01805490005803014490421900f154440038000303045904002191115040010032035092000a0b203500d00f052401d404d00c040b55020f90f070281440009c0c008244200707a43c80581c09800390500f25030110f401400104180b2800560700c400c079a6407071005602010030171180305209500ba102d030822a250403040350004840c2c0c400e903005083c41d090042403148005030104400c801914428000300825940040c0042101c8110903003480f04080000001d1070440c484c00603500084d501800900105d0f180c07608060203908441c1c600350025109400081785881c00090203401420951134400c50300e8448103181c60340d40d1050403000083d66880e000000d184400404540c894413881440c581c03100803915000303000e100200204440f031760004040034a0107080004903411244c3c181400c120007001d0002280180c900300d00044c0c413000b0003060000b00018903600070000c954800504000a0b03072100d0402c002ca626a00410f01c2200f1142c00611045540000060700914141491980e0304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177581735 1250 177580485 177580489
    0x50108010323100507020313171c120609021206041103010902070204022203030801080105010807090b22050601090803040b0307050307020f010606020a0b0702010203060d03031d0a0f0210050c030d1505 88
    0x90130541d085001a400060030341c0384000c1c0ca18450b40601031211074640f900d4100b455542c0d40301c3c980300c002d01105000d0740c0d0b55950240120a1a05280380968060002a44da1040035000b90003070b5030101505129600010400d190612903051807001b020049030035a403c1418100c0290001d20040780c226034200648400d0030808852a6032092084c2400d2010314203500c0c00070301541c4181e00c40c140c283c1c100b00040c491003102040032429036032001e100145900a110000d44070700035010f00801e404000480da01585010341d0000d6208810a8840d91200b580e0b07032041070354920940c482d011040500f03101083c54684108011900050300d481110107840440128500719000c0c1d43c4000c000d40c0c0400c82e240c0410211850131a400041ca000840c03d6161940c0072039050003400d03a000701099564600e0009102c00c011540d2102800c1504a6a000d00945400c24500d80d501c0c9003070f03109240e00e550320102144500200d0703816800c2031000d1800c11010024000140481c5006411030310500c0c01c1c04101c1d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177582985 1250 177581735 177581741
    0x903030f070c0306180305120c070615050a150503010b09010e03060705030f0f01081902060c010e030309010f06030c140a09020c0313050102300408010c120605010801032310 76
    0x785000d2000c2040b4640f85280c00801c81d04c0d1074080488940d81011302c40003098110090b210141d020500c0301c0c1090351051030194042c4aa08401421645029495000a01041b603441e003501d00036680b1003ca10b0721505800915208a001400051410401406030340510009080048818103010b114000303540c0019082030412615040082c80100c1040401c254103902d098009681911748690717541842a0140c5541800c901c2028084114450100719211641112003000c0030b50000c020040b80c0303070607003901e90f4016101040d00e507080007845200e500451040da0b0440c1e80c803000d425401450444801c0c21512a1071041e030f440005440300282c940d0081c0010309c442c07440400034503980e100400112100c20002d800190456000c80d12158a80740a007802e0303810226003600c2e4110000703280c00030200c01e20880d0032008555080826100c05641c001010040410780b21605202c81ca40355401100c0540d000d02c0040c00b0a1118800030500e110703644580a030282c1070000382c030715100540a042042d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177584235 1250 177582985 177582997
    0x1103071106070515161404060807020c06131d010803121f0b0702010809150601030905010906060303080124090302012a0b0105130e120a020a0c080106140909070b0903030f 75
    0x3007810342070200009045c24500d4140903100300e0a010340809100c00324000d5a00850089800380041c11000c5450345008000703000c1c40040c0101044d0707450341300c1da51403041c0700158400c4402d0031120210900d11402945d04003416a01072000031414002c00401c04014a04090b003542260041c40110300d2950340c2c6035920030013030011002c0303043d9224001d20004010040c010074464071a0004880b201e0035201803849035030082d40034a80860018070504050b801811602002000245004000000c00d5007010341c0504841070368010302e0031070018048114028004180300400103a01d0581800198002c0d5546902c054a420207151002c150f28071800c1c0014081d00d054840c0802d0340010440761a00800407040c041c951003003405103107000e0449030354070010080f130441ca5010116490809034404c210811100c1c0e0411821801036554800542c000c1249000f1074603892400400e80d00c01381401c00790705004041d104001d01400e46007174903040300c43e084031116070350601041207009900310900c009098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177585485 1250 177584235 177584263
    0x4080307060606090602011a060d14040c050301150608070f090902161704210f0b0c03040606050108010308030f040302030c010c030b09060405060603040618120f0f11030711060705 79
    0x6010b81803c50180002115074041c0c400c6a041c03039455418240070b5111441d00d00000e440e9151101721880d0b000015012201905200c1d0400384208024421941c41d80002c45070150000c001c440c46240c990014123000707000c2c680110f2180300114a040348200944400c0c2040c0d45401e00c12191180020b8085ea030024900b00c24007080328942c032050204203c0e41c1e1b0345051402d102540b0300b500d0103145601c180e002c011060b9101c44401c103001d00f40003410350700041701c980c84024100c1901e00001541090342007980c061702e02600d40700c80400c055014150b803906032600f001003141150ba80c02c040d4914510001d20440c210b0105020440340d509013400798200100c41620b001c142c5241e903009211740b02c54002e154601c11380c00d1205205554441c0000c403508203402201c04a0000c034000703106030003c1143c2d40020b10300c4c0403041c00300c010207610840491132212541e49943c400d202d0b0703681c2140c40e40c0200302120304580007000140300250741da81c801040c00c0c40241070542400890b4481c24103102d4103508800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177586735 1250 177585485 177585491
    0x90103030309120801081b040b091e010504060308180a08070602030703120b06031303050c0d030f18020108071b050604081c0504081204030e041a01030b092a0408030706 74
    0x1804215050b600c0d215072010501e0621308640c5000c81e03103940c9034100f011009522600265401260301d07240c126030116100a00000303c58141000540004500890ba5600158852001156503c0c050040710704480d0460f03909401d100550301001903004010054941c450b100300c00024100400340981d1004107032603000356032501014240900215401441c422426240a004034030650301c000989030401d0070400e440602c034000345402e6640c0d2003002c111001501c01c009200c1842640b5801c22140c5c0b4504a80500164401c81900b16240010a0009020520b4031001400710f40c8200819402040202480d03011341c403240d190703541003a40684007a582c402d00003c000d00101c05144859400c1d00944004200c1032509803624180c50060504200c009502c01020400b8548500790440446900400130015070a030640f0040404c80840450383c0402e040501c082c3d000c0c80d1080402d1f01c1803120a107481c034405032003030341f14110510044170075400e03400900001c10340c400204098141c3c0c030301c610000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177587985 1250 177586735 177586751
    0x6050a180507090c0206250207030506011401110105070804111302181002070614032e0905090a0c0312171602060c030103080703080c09030a030302071205160308040f020901030303 79
    0x850144e50003140d03140103642c8000240038440da040e62001c4107011203111400940451300008034200080ca03400a00700703108940000c070f01414505400343e200e1000745c880714100901ea510341c1d4244c4208a0786140481e01038000500032a03100241d0300706004008000c102025000c8035050200e0704564860703198007405010300c803028184040400c00d0240e89000610000d442c2c194001e04081200d450014445000b0010905064008068200c080c2c000d0014411104200048950344401031140c0c030625803c040c0440d510040100c3c081008980001c5450f070070b0360442d2162140800540050300400903424500c41224549002440c0102062204909440300f4800001e28140c400380c15144040020401040043ca9100c00c8418441d81402e02100c2c80d690070510020500840c40d505426006104040c410154190300400700c90b807054181024543c20300c00c3c200d1ba00d0149030581c906449451244e000802c1c01a02c03200c1d0300038442c0310018561700d61a8040341c01140213034400c50100e0f44800034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177589235 1250 177587985 177587999
    0x18190308030a0e07030804090209040b12060601020106140a060c050304030c0605070b07030506011b1a1f0e162118050c0d020a1211042a02030906030406050a180507 72
    0x80c410100d003c220082c0850f500b5a115a0f1340c9200301d1049800d550b40c0061605001d80380c503003060300740100080104429030340f841e000a0300c1e058100e4245005503e4858082114103c1d80a01055100040c107801c4000d4100307a02503030180c0c1c0210094856200600001002403c140d500c500607150996407a5100c22503442c2840c20600080c202405050420040049990303204000700d00c921211010802e0020703050400c4c2c541c0421043c018095013402000b0042100d10400105c0020300180d020900040c0ea0b5488007111000103440d41d403010f407500d520605059102c0d50b410403071841001700700305070180c146900c2d1080700d05040c4801c4031781480f502208284481804400b41c042815203140194a10030390000c1c0700c13800240980c8194103400c417410740034000d03a941080b0030036a02501c20400780402d002881d104540d60860900c1b440c184c0000031042910100c2684c0c0031003c0640480c3c10742c1c840340d903882d02421004029800c65a502c0005d40700e03420002810400182c0500080d06078a030800300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177590485 1250 177589235 177589241
    0x60305011113060f020a02040b0607120f110a0506040b100b07030f11010b01080406180f0807020307060f02030f0306060f070c08010b0a0f0314010e03030103060b010f1418190308030a 80
    0x20003d4144122900b00c000c0113030700402c201161030740c111400030fa00c400b80d2000030b07030300d0050020103002e00c180000300310240d68201c01da0740c071540b132181ca480740f9400d20fa040d800e43e1480b00c80b10041207034218002060014608032220f0342c102d5a008554110f0700e8464580d007200340c0211000b43c002442800c0c040c0365660300043c084c0560031003e0000d001221000e4000b9201000c003074001003a09945031aa064000580e80b900449268080301c001000d8800d41490b84807904188400e92190040d0080011854018208150803074000c0d006941080c2207120300220b0b80c0c0004241303a401030300c200910907030500c040c8000c16601d44920846130380103003081d04140c00c562003008214000c0800c06000e010340c071144c220300400c07203502140e04112400108000d501412040b54032594070710002c00013108100094024403510442a614064100b0103808122084104000030406c9a04200a905180352924800c3d44507500c01800320440c400604030744070006003c9500540302840044140451110540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177591735 1250 177590485 177590489
    0x20607080a05131403090a0603060512030a02120307020a0206030a050a240513091a0403020d0e011b03092408060f1008150901030303020901030f051b070501060305011113 75
    0x7010082d0f440c040c102698030001e0218043c0c01000580301043c48101c2c10412240c8650001d030011180380da8517640980500007038080c2c00c0c454042401c5000058000005951861420358002c00e19044c01600c00c00c402e601c05072203202103005600b140070168554030011401100720f544005003502e07140c00541c0490f0140c0d458040c515582040c0360110403880b4241000b45c42007114440131a00ca1128254018010950014070b00705696455071080c04400c40da06105c0e50103034080d00d07a041001d2400700c4010345980c8215010031104580d00061103a14115420745621034108181a69115807440b00710b0501c045040d02c900f4040d000920455500c0800241c1044058403600e542c000e0890002c0d801c21300d10000700e0204681d0720700203881001140d454815000000d85103014039616414020046c4d8000030005021a082490650f1580c03194400d042c418440d1800d00700c522003545c2e80c84802544181c40c183c900d0340d295480070001ca0000e100d822035128110320141c0e50b4540d02c1001c407550690356 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177592985 1250 177591735 177591751
    0x40e0f0709051f020f010c030902010906022109010309020301050c130501020303090601090e1c0504050f0603090d1b21090803070302060115031b020114060301021309052502060708 79
    0x207203007041107840303581e010400440c10300301ca0741c0324a0380c0c80c4089182c0400c107103c410240d0700705030702d500d2025095031112401300c0c001e03a52660140c1d00c030f40b0181e03030f1085184045204012100d619042070389102c0007074031a12605140228152050740c000a080d1402074810300c5955000052641c04604240d40700c0700200003e002540c00c62909118198032210144074144803e51504050000b407a07003800f00156411091003095072200840000404a81181c06002c0c0100381c2c07580042080c2c40c042080c1e9104840c1c4100800b03200a83c03480c101d801d40d451000d60602540344441180000e035110108207008880c204100d106018482001800e108290f07000c216684c10030414100841d07404a03400d0f055031003c0580031006200148103c0003070039921502a650150300300400e0402c4c0d070640201141d01364241030f820a0f911200d080500300c1c8100101d9220b484d03035a030010880706580b9008654000f5010480102c0381c44200c00824540c0b001c1c0040c40c006810120800400720b0700403004039000300310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177594235 1250 177592985 177592997
    0x120904112b18140c0d0803090c0103020304050d0c0201120f020304050c10050403060b0a030b04120909060b04030320030c0618012003060a090606030905011107020108071103070503040e0f07 83
    0x40c5041c1103100200a071002e48030380f0f200300d2607a856500c10816401c0f2281d0180140c0c19448490502105a0f00203481c042203e009040701c0c07150a610a0087c0d0740180d80107030280401c0c1c10810402c0d146012104030482c1440590803500c00031100a10505010101c901c10141c0d90b4541441d0003428031045515007403098014560342240e503507029082e1000d44e075200400040c0101c0d0040092a01d040313079440148002c1c0c00400700410819409d42e145030401070740d161500c05a840d0110300e429100036000c1c106180c1000e1000b0801b0038440d4101c0c02095510403c8007a10101c03900700d9900b15071001050680582c0001c0620840c4004820402e140041980003006109070583c3c010101d42c1100c480440d00c1e49020020402075510141600c0050501070010820a681c4100103000b44c0624007050380d05520344006481d9003043d9008a0b0400b5505a4074080c6960700c000d815a060f400c0f04003020464401844090f000034000c01c01440500403042e81c1481510b060040c1a5162070018045410820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177595485 1250 177594235 177594251
    0x30c06060301051510110d05070b06010809030a18051f080717010b030601021e010c17040b01120312020310170319120b0405040c0302040518120904112b 67
    0xe400d450000c66801c013210800e1105000354001c9540c22010320b11b00002d8003c2030245040c650b0850010100584610110000c80d5190001558494411602c1004a800030025841414440c00c98588400841540001c46039111400702d0300d85101885201a24101281d0385580a5000700c43c855021580d4584604c000c0d0710980c00a06e440030610506c0c00e154008008502a40e000388099041c001c40004204032807903c14203128044c140c12280c4c0004540c070094922025905018001e2043e9002508140c00364030701000380109080f449029010440c0303003100f80c46058200e00095014120080400c1e03141420186036000044047e54a0712090307104000e403d150800035815052002c415051008807000d136011020050808d1620250b0300a00d044c007048208180c40c1904010380303000741c80c20402c07a900d0f00400316040917404040c141c04e82c40100004140e4101c6401003075610409440030074252810380b00022190002062500040d260002708059507460190384203130044001000d01c0550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177596735 1250 177595485 177595501
    0x150603100306200c150c0c071202120703050d030f09050606040507120204030602030a0c021617031201060804060c05090d020d0507031719031a010c0606090608030c0606030105 77
    0x10380d15100003815035445000159414000300001e05022400d0214242d0740c52181801c01d031690f100385000b103000030885010400701002c450680300d072860b00000134560b1030300b014a50045002420404c0f64480709202c05034440d114207101303120007148500300620004c50450000340a4840043d40380c011545441c4840c0041800064407a401010a65000600b41c503141e00403076810300200306251f150f40c0005000020810316038000c510404d10f0180402103050510002c98803000e208040b052800c0c5c030031509214000c1da80c1032020554506c101106e2030081d880c2840b441c4010245d0040c40816505800c100903c4110300039010304200d1480c290b480c00c00c001000038001d420b8001c0c00381c000e004240072601000401c00c141030113503401c030500e2240c4100034105c801c11940217090550301e44003015160a8194001c0c007e10400d031407601651030120320340c0801124002020a0260f40c82030b2600000030781c01140f4480d480284c602c00010f10b680b1200204044e1070190043c085600903890581004409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177597985 1250 177596735 177596761
    0x5180907060c020904080a030906020a05180d1a070e0301090605151504060302090616080417010b0105030c030c16050c01030c02031e0a09030606090212090109021f02150f150603 78
    0x205e540040801e407940c1d80f4100450090240c814014809803000400d58080d039040400760045031660901d440700c0c06402418450b4010a030800142021007080660741c0d075080c081000c1c0d6000d01e01d443c2c0824806000d000082c00e4a02c00d410981300555588140000240542d101e0401c4d41c1082e00c24014200071904008a04d00c190303c1840704040e404100c00c0c00d02d075148001c0f1402200b62038000740b801c0c01d00f400c0c8185c040d0310a00c41c1c640c0100000150072841c0b0018061242c040300705031113450850340c504643c2c1c4480d0384002c0c10012600ea0400580c03a400207902e002c030001ea0b000d18001d20b440c1c5c050b8000901210743c041e00724002e662003845010003841c2e00c0c20b030200d011003038442d480c0d885181d00d040c15600d81200b0b40006102c0e5040c00d5000c03c0465050b40580403040c200b545004d02602d50400b001e0880f452440065000400c0300240d911881042e0086c01600d131003071044869000448400d03081198050710300c0004600c000c802e02c841e0071010981d05a0889085800e9451400e06001c4d002403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177599235 1250 177597985 177597991
    0xf090e0c0f04180516080d020a050703260a0332061003021201080f0106060302030705031807080d120605102001020f0f0a09060503060604050f03010605180907060c0209 74
    0x71483e280ea905808a280100958008030750280c11554031801e0b8200c00c0410740325a02400120348250306151120510010b9803201c0c3c250400e000d40340c59800c1d0f40318402000700680a090402401040c15030800e044100142010b01a9a40010701032103010010580480e240140b000f681d10811040230682034280c40700c5400c100c0407607015850600451050b0301030b00409802400c0603003100000649960041070b560b00c0c8499841c0204089500ca850540c1240026140d003400102c0600010b0011b144c600c903007105000000b01111806561540014a004020b107404000102038820340c03090040e036405407a02402003250003445005002c807004140c41140107012601118294002c000c100b429412108811240c445181c2d0381c0309142551402a44248014000140f0343c220004034240b00d8025030307006d54001000c1c40c1c81c0c07a14002c2084100d910046010f6410355860a00207095985d449100301007a5580c0b1060965141c10706179141445250380c40101404401342a020042e5151441554 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177600485 1250 177599235 177599239
    0x230c01030b100c1509140d0810090c02120a021e0c09070503041b03081903140105041a0306100302130b0117070201141008161203080615040f090e0c0f 66
    0x281003110f0341000b0241c0c0424216200c4500d00c0c101c1c290041c450a00a0400200700d5181200c0c12100007135400c8412110865074425000140f040034410300c5401d4101640640d042c0c030484000b06003a007175410050340a01c0d40040942d00030068609102c010040180052017144050845801003001040c0c10742d0cc020240b07020804008000f90030440501e07118035586454007401c1800326240c1c6084030171035008010030406202c0d9070143ca84058800c0c0a00e919560010600007000c1c0d107804140405490b00142058551843c11501c650a40b41044494030500e144a440f442d21031460050051600c5940034230b514403400c02d07c1c92074159804c8010440000b010000010295450050880c010300701c00c0c500003054442c1100740906920424120801d5a101130103459409600030030403404000d01e03200c1c40148144109612001c07900680c0c9440d40b000c1c0c00303481c1c0c20980444c40300b100413035030040d08807403100c00000b0303005d0040030b51030b01c00e080e81d40e080c10f401003825184100000d80440003242c1414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177601735 1250 177600485 177600497
    0x3020307151701060e040506030a030c081b030c060403030605030a030807080a09020402070303050a06060903030806060a02070f090615050a050d090606050d060b040e0c130f0207230c01030b10 84
    0x280e01d0b00c1844642d80541c03036400001c1107035865401c018500b041c1d240b19148a1820440815094940805e1003018140d058403203511a0a0566030240c103034100e5550103121115402c03401901103820700080c038282458601a10003403415181c007904075213a07a08064001d50142030307076100094000e4032041d04148281010000da0ba40c0225040c05400e403a03100a40140c00820442c0815415801ca540921072410741400041c1d03c902c4122640440352201400041a02005c07070300380d0400c90001c015000c0b0603c1680d800707031703154003642d500560329500c10420140d4130801040780040c000100d11030902d003454150b240c4214801c004040c1e000f204181c5402e2a91124440e0400c002a80400d000300740c0642584103025641c10000000d0400665050099013030202030f034091a008030301140c1c102e200070001c0103019501052400200b000c502d80303c102c1c0381c0c00c01020002c070301e21110065000c03541c080c103083d80c811003100b101c1c200801d03481c28134181403c01410000c503544d00d60b0b101c801600140742c03130 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177602985 1250 177601735 177601769
    0x3040b031f030611030708061f0c0c1502160b0f07140106030501050c04030615030503030c0331110306010602124803090f090601020a06060603020a020c0a03020307 72
    0x381c403040d00140e1004080900d0100402c21906441d000b6600c070791240c0e1918040c654a0340309101005119040400ca8607800c00103040e0003900030007201800a0064200021590312459881e000a10b091201400350f4028051500b0746821110100040c000445905081c41249803540c1050b0040650040c540042d0b143e40c3c2400070000d41c1314000454100303000b4485800c1c00d00c450038040c1d00900040e2026400c082d410f002e1441c8218842d41220707809801540340d079a450800b2945900042c090495400d12074004902d07202c18260402d080d0480409445080e400500c0d2081000300c0c1030780514040e40214004105242c1c001c100c210700d11028103500e65407103610503402111194003002c20307607482e006000300d00c107005070841505000c1284804028002140700f45400d0b520b0085041e190381c0710240d03685240c01400c20705c14040c0c001c4010b0048821149076582d0b510b05586040c1c00c1040002e602041d1014626810003509014850540701c030f40c02641540c010a0b19500c1c0c030300800804200074009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177604235 1250 177602985 177603031
    0x209220b06030f070e1005090f01030b130812060405130c031b0e0901140f0f130c0e1609050607030504030b07090f060e0406091a010f020319021e03040b03 68
    0x4a41d50484500b044c4ca0000c0c1c0c503264645060300c4141d1300704204c280166000f00792030800542031070042003048514202d40c1c0c82c6a031000800c03400213103011050a02103040c00e00207000e540180c10403034200000b01c3d00900c1c040003400100e0350002d21050404140342c90902c0401ca400118205982d0400d84140012146261250030080c25038800c1605800b44030400854100641c0542042d8040c1e022403940351b1140d29802038041d00544141540101d2b000101307924080040000c04098420021948000da030307162040104042181c903840211141032110484036440301c0381d50041d0404491503800c10010f504d0040c407600640c000249503590320400b04403542d004060003401405000740007880e03c0d40b100d0300241000010903205009504003030b804a1050ba42c0c0c0154168415000a5041c02c2c1940d04011100c0c103466417050720540c04100703d011582c0d140215010904015a0010310b00d000c20010f966481310313041046c0603155001840103200e460010700807680c00c0007003810080e55031004001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177605485 1250 177604235 177604243
    0x150c03020c07060e031b100c0215040b0705010c1d09060f0a0308070303180201121814030702030609030f070314040f06030519060509011a07060204080304030209220b0603 75
    0x2016150350b2082a0300012003c0e840f960001c1c2125007034041da500303803500d00480441c1c1c0701802c0740d03258488040c41781171030081d1190401c0f01055000522014070010a034400050992180d082401000c900103410340500c07509016040c118901c034138256060702c116900660312000294101489082050013040c0701c0d981d5440040840403008060100c150742d24904501c041d8031202c0100d0100c0d0a14a001d812000070519800105070181c44a007140d10041d04084003d040b80105e06094800d66032500000c9000c80c0b00707290365021904011070b034074101c500405181c4003001b130070440d06030300401c62462a0100c400c00e99584a0741414080c03103c08030018110101d003e0742e0404010b15403052130020f0502d0f495000a03004001d101e140140c0900d00b8041181580c01710301402e40c0060300039004114030f107540c9000350261039007443d00c2401e0039480e54540050b44c1c0701e0b84c420440f0340d101040510552408042d5540c0051554258141003000ca10118080040c08200030b42210f4108d4002000f60f20300380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177606735 1250 177605485 177605497
    0x1501180227010f0806030c2b0503041406041a0913020c06010e060f090415090501021903241401050c0a0c0602060901020f12090f0f01060302090a09150c0302 69
    0x301844000d003542510030607403468851030203000802000f00185500c3c000ca039098094a006405800080840d000340012003410945540c01c00f0380110042c1c07140303980366454240103445070f030141d039449260400b19001c0e10203000841c3d02c80d8008000c04c02c0f006440f00400c0107103003800744040c2c0c2c0b12071258000030025450719502e17094540c000100b95400c0d0342d010407540d040c4c400628103041c064072944280000117004034119500514650042070210341d0009903100700b440408004101d001e407541d42c950998001c0211110390000038290a25500d816000340e9141000380155402c0020107100ca9003d0500c651182e00c0501003048031550051344103030100c1e018100c00c0f50451303880380440e01c0c0010030880a44105001801203501040040406008540701828984003076802c00d03d5804002460100c09808000d0a00c00d00c2d245411207c000c0c0500123080c1060400021043c0ca180144040c040005181c000d1140c0342c00708560008a514041504202280c080065071034a46003007900244101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177607985 1250 177606735 177606757
    0x6030403030504120903080a2d0207080d14070b06030304030215181f14090d05031b070b0a1d21100207030207030f0f0611031815011802 60
    0x40006240d00350b0070107409280300325030201c1c0c0180b00840c104c5011242d800000c0a030755003000342c0580b4034420268007180c00f485a500f400700c07d02c850714287c4104050034221000d600040d00422280340b0038410600750a4090410301c26401640104c40018800c1d01d000500c568040d901149154400b00284c40107942e0191a210016020748a020b54030b03080448103010644040c215450302e82042c980101d034004070b141c83c514000030000820380704040000c040c0544a00148904113065076041c00701902c0c03a00800207141d541d0500101107120302242c4c03103c8912580300c0c020402c1046000011102029020302e400501c59042d150b840807000c140350700645d4040c03055036500d500384055500c40c1c419840810708880c2560890340c1d030700b016800380120150243e00044410404500554102000b59105840600c1c841c0e985940c4d1901300c0d010788a007107a1210000c000c00ca89500c10000d40c94105c85508020040400030080d040d2400750b050103080804c9540d890410000700b5680c05486d40d902e45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177609235 1250 177607985 177607987
    0x10f1b211b09030629130906050a0c020609030c070b0a0201021606241203030903050c0f0c010e090412030b060702130213050607051902010507050f06072705190506 72
    0x401d007801008561507001c10380f00c071890035a03a2150f03607440550951055210074400921002c81d070080208920841d240f00d030140ea100c8002070005542c1d44282489450701c4400091107c90040b402841c28000604c99501a40100100010b01c44009200411078502402856072034200003030483c0a4015080c828605940c0c0000340c1d400c111103a040204106d1035800065050940500441030040303440c443d030250100c843d2400008644a50003100300d00c0c1c004d080080ca48141c01c1162803030145c0d4084800e03000d8229030041055583d104d1040d80741c00b042241d0f11a010305040c1c0740e0581c00703400c001500090503618640307200c90b82c50b69010340f80d103141c0080011141100c0141108041d5200f5050785440445146002c10545003003c180d610882e000f10051062600403191807185401102c02a81449824030940002501c10070042507090300390350180240c2e003800c850183c01c1c00c000080a000b040c441e03804140314564040582011100d0440e480400d0003140d0b050913802d0004d903000103411030b034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177610485 1250 177609235 177609281
    0x80d120504021f0f02011107020a1503240e0109020a0203030a0c090807090f06080304030309140a030c180b03030306010219020d080f040f141507050c06040602010f1b21 74
    0xd00903102c040c1e01351311a0000c1c02a0411010004420300c0340080080d81f00610503000e00c00751500404030080d0072098100012903448050b07604214060300016108201c01240050044451924085004004600c0c0030360400c03460803030203900c0e400020412200c1e19580c1c8840d82c07416125904190080084100f681e00301078551081d00b0180030f00c15503105403541440b00c001649000002280c00316a01561303100c80e040d0400003118900241e1140f01c0b40e00401014010011802c0d40c00c2c8030300103008040411041268030315a8a0584520601462194000340b042005990300442c2e0302214140f40d410780c1101e8042c510005080c10103850300501000300214195040c04803040040040d04c880c003503143d50055071000040303004401881c0680d048070018544440c01424000940071003480398058a000c110304d100465a65007040e07101d40d0060391150f40d800d070082d49521505219403100c03102c0c40210100340360064001740f0a0043d031101800040920900020107034000804c01d1402d50441c40b1003d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177611735 1250 177610485 177610487
    0x7060207032325030503040b09030d02120a05070914100302070c06090f150f0305061305040b0a1a0307050613080a0c09050702030a0c080c0a06180507080d120504021f 73
    0x6003011103d0340c03e0300c0f0100d8588400000c188414407500c2d07415560a1301c1d43d0390319070790344406000c0035142021500c028040d002c0d0710741d07850025107072440144900789503d142c13070780c4014140c3c2d1000d0318a1042c414080e20030b00801c2181d1412a45640083c0c900c2076440903802c0e4200c0c000e124644020300845000c0c603000c1030302e541c040348a40842c2c2855601500703107901c3d0900e04401424440007400071030029010240340501030b4200725400000282450045d00901001c40c4c182e03482220125509100c0800301718040c0118030030840640b88402101c071170b1480aa0219a540c111030090070b100b0740d40456600c1041d001100d070f0f1400b4003441c8060343c010450904d403040301d0b0496806001c0003c0d0078180042e030100d20010039100b012206c2d80e100582c0720580d0319101d806a00000441f030b4907000c1c940051000c40d6040c0a203101e030300b500402c2c0b51408400707424150b08056454000856035000b40717420849503584040e89014054440b00002600d4a803440041d01c065041d19503c1c0070b01031f0011401c0030f01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177612985 1250 177611735 177611737
    0x9050309010201060b1207140c06090f060c07030e060f07080d06080d050712140d1104090b06070f030e040902040501090f060e06180a18050a1104060b070602070323 72
    0xc40001c0c1c0090040c1030301c0721058026405407107650240b085030300c4000703600284100b1141010f0100c4220081c82c1c140030150480c20074000720744000b5981e100c0344051300000c20070481164064a0b61081ca41009103030b640080c020190000300d43c1c8586000308022003c02e06500c12218101d9218101554401009144001074441c500c5951000d00481d0241c110150040d0211000d00794450000700c0d250044440680d58025400c1ca441035448041c07000c0c116998052007541030460001c05025103403032604034040c058036104000340e0700403d001d103c0e000002d10326244880f4070070360600340000e00e400c070403003c41c2c010400703078401035440f030705140c000036200c15140c1c00040e01c3c01d07400105008560715002c248200b100191000d50b0400103a0007150640802091119042902d054002c00d440c030011001d0141c0381d8107007005031403079000604004100701040b0280d0710030060035a402d12900c0d00d022a18007060080e00f001a0041d0340004001c41090f204e40400801e55640840000744007021800031009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177614235 1250 177612985 177612997
    0xa0e01020415030c050405090c0a180602010b0f0406061e02160b0306010e040c050d09030c0c0b031801060803090409050c1305150411030a2a08040b0705070c0512070504090503 77
    0x8a460711541c2e020641c0b04400f00c0e8140c0e031f005403488803940c90b64034800403190701c9030040e40c04120441c51014042451052403000070001079002090204c0d01e00100005803074152442d81c801c2d4909101004101e400c0a0004044010980205200000c0783d6040e8140851010440301c03000404401091005080b8041c0d406110207a0b10740c4a28a00e2200340002c85171100700d0300f00414000d000c1025500d0307445d00200400c074400c1c030301024003d00171f68600b402084035821a082c40314020081003810004034a82c41011488580244450f61030242c109450344191040039001d940c8a000c02c405000c020800042108800350941500d040103160003c000d040035210707100144001440d0034040d00c0c141c001c1d00600500c0000300740c95910703140720703c2c001486080410b01600c00402c001d156442024440d1007451a082e85031030354185068a040e9400c84001080f03035084c041c040c4020008100480d2184090f505c09403800c1d00c00600c00e40c1c04030719200880d801030742e00c01d00704070400f8200140403002d800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177615485 1250 177614235 177614237
    0x100216030c2103081f0306060b04080c0123031003120c11030304030201090b090d080f0703081b0313060f06090b03010b0f01050712140a030c02150108070b030a0e01020415 75
    0x1030b11584030009040700c4014100c0140004800c0300100380f1151601d5100d0f094452054503a42e00f241c1c0e00d60300c0c803090740d055030302c41240749502244c10011400309011100200a0074a4030400355054015021888201400c00050071400440020314200f61044420301840c0c10254100c00b1404d8140000c02c500d07039060080300c001000050307014140c10000301340c2c0e0a40f5416100d6920071428024080c1017508207544d42d03503004442c40e13402808201d80400911410540d10182590740001d0f0502400108020f040c640b0845000300550b030310318162009494100340c142d03450b00c20021060402c0006090410a8290f42501c1e251001400495540c40448402803d5009001c800b0b686410400c40285280c86d00340410b8040040707000040404c40710201860740390800500c1541400121034540e0041c21810700441d544082196041f40c0401c081c45a100c20004146030560410751041d0f116011885500c410170000b1000c5190445503400030703042542907400840d11a9500c0e1200c440d001c60130300d0070344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177616735 1250 177615485 177615509
    0x280203071505090c0405010f0902031e010f0f0803030601050304030e0f1903020a090b1012020c010507050d0e0c01020d030207050f10050709060c02030c060307170907061b0f02100216030c 82
    0x2074042d060500400d812240c0465042401c5071032700b111440603500c000c0552034203140a08101a5000030340d24902d01a02c40141001082404c0c031598074600100c0b45c20002c0aa8802d10130000542c0e80a07040366841076140c070f424013030804200003003840c0385240c01001c2e03800105001128800c0c98495080812280202c40b5565440c0d9150f0f03c038001c5a946041c015045000380017050403040c000d0250052411086500514001500f44800c1c00c481081c1c50383d20004a000684011501701e9000ea9840318808001500c00c2455010021703607207580c45418a0241030300410300b0b00c01e01505009141d80260200d00742d69034600c001215074010b0008803541c00200d0001a001308006100b4100d01e201d85901900a244000b100420442143c2000301442c00300b00c409a00400703244003d201d882e029004d0352000b0211a03051003000750015524082c60300d0420a903d00420200fa49a0403c805a42c3c0558a9002600b15480100c1c02d04501998009400ea01d18100004000c881200c44084a156542d90 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177617985 1250 177616735 177616753
    0x30206031303120e030a2c0105160818040e010e2505041b0314010602030418020d0e0a06060b090108040f020f0303120f010b0a050304030e040e011103010e0c28020307150509 76
    0x205001228003000581f0071100500e88440b1940030308018485040b69400400c0142c0a540c1c918843d80c1c0810003980e00d465404440b0101814103009040381030103440300a01500e0305540c40070307548000050f030403448040d5480c548240729804d0003800014040161040c41285602c940c0d83d00781c0d0701420000030000349040000d004620326924114141d8010313a0146191910b400c000041915940300d4403c5215400c00c1403030081d51052084029200040b00600407240d082d080003800c88580f944061103510701089082c00d140c1e4031040d02a4459484080c0100507040f9001040402950600f841d4040c0300000e568105080c00036003ca00c200d407114104c1089a81714070500100b07000d90507007800801d07814008600000c0c0554005190050003400005141c0e52108180303080d900d024140302e10804002005000154001c1a1981e00051714004e0324688048001c015203000c6031403540d0780300b80880502e00081c0e40d00c240704543e10f043c2c02c440100303828140c00340d031382c80180341c01d6480c908203106440030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177619235 1250 177617985 177618017
    0x708040e0112031d030709060e0613020301080703061802040603030903210c020d0f080406030e07050618060a0201092306060409080d200c0f1204030206031303120e030a 74
    0x400d2030301d15407513622404061001c6049460f144840d01c4959494013482074089140701441c0b003240c00030b10390032050000714100042032000c00102e106800e500c40780100018001c40c000002d00004980d40030360001074540c40381700800005800010020b5029040082c0001030540c42028481501c2c001e0510003200e088010b802036010508444800c0483c24450001026207820400b0b6000300e07001c3c0e5114110b008241e6284212039209070080c00c0402e503241c44840c01c00100b0000d40c00580710948a0034030f04a2400c2c1d02407000105c0900f4203119420010b000420302c0d100f034011038121135200441d100c200c000c15003500741d000f1011108000318841c400c00951a0b00d4540515500c080c0c014282a02d04400040d00c034020305400e1001081c07848600c101c164034164608010105840004060b083d148034200d00b0070300b401c50a0341c4081e9030f02d070300f400203002581c2e072801281c0d040b41c800e1070369000541e02807034241c80801f18515940c5165242242251050402000500404400781d60300d0284d440340ba01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177620485 1250 177619235 177619259
    0x706021b1005070c060b12060901150504050c1603051207092d09150305150f1305070902090a031b05090622020304020612011409060d1a0a020d020708040e01 69
    0x141c510004074a02028000f244455006005ca031b100a4500c041d080c61401e00c43e40740c11030548012611343c2d502c06001c1000b2008142c52009010111004d00c0356090840000420f4007424107450f80041c1e41922480806000e0710032598405602da2744100e0500e403441000d0101c0b5403d00c03650605022109260460f0354031041541441340040a1400c6040e050210b080018020540498603c0d811810b0110206404201d1401194002d02d5091620b103064a5040042d42001c0c00582400c0f48000c50107000580103c0c0d14003c2d035071381100058840c002078002500301c21440d8805405800300549203880c101c4c5e41c100b42000d450094035201883e407580000c0c01803043c02408400001034208280748290b101d00d800658100d80010704d1a410004929807540c0307550b070280c1c0070340354185102100b000f0a0504403c00d0754010300c1180c0b403456020040d120b20070912150822410440310300000125600c88960603124403004480701151a4000d6140c4460140e01038007a2101c14884a40002406840d0315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177621735 1250 177620485 177620491
    0x507060c0e010f11070b1b1c0203030408090307050603070302311a04030c08100e06040209070f1106010b0a08010f29070605040b0a18031e050706021b1005 68
    0xf80d242192801e05500880d45240c40ca902e9030942c1c0546600000d0284149000d0100ca030001104803001401d005602c6140207119960002103c00e0001800f80a0381c02100341c0e68499000100c5660b2900fa840c000303824205e20703400072030744400040140551240e16501900046104c50000b4182110841c05c003041e01040c00c94500051624000a109542c880c0c522028010446c0d002e40c0e050a45030341d00c10501780c20a0300302c0b0f205a0322403d6005c1007400c0a010700018822000040d0070a81460780200380b0481004215000780030425084404042c40350300c140b43d605000d5400d40e03103d540c40e0002c210155200d8040000092040c03c004190002c41d810140101c0d00f002a0b04c02c0b01058428000c43c1090361408404c00c801414000000800c0a40c003e05102e40d102e000740c10094500a0307156003c4032070b6280d07103090440c0344209410010350002800c1300060001c04403101f018190100441d1640704004009104034004104a003074198a074000c101240303989000d0320340c40e0161080b1401210011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177622985 1250 177621735 177621737
    0x7090305072c0702030c060c03040b0c0f09030109060b03010b0a2d030f0b0402270a0513060e06040c0b0f031b0c151f0f14010905030d0507060c0e01 65
    0x42001c00140c802c69107031103482021030300ca0100611481d1552202e1100845201001d078200060500181c0b0b403d00c241940702c101003904d01d04500b040d0b287d80100600052441c680340f000020318040e101b007100117a58a5010044c0244140c0d0010315058010b86050300e213403802582450030f1404a031900501070800d441441c0310656140c1900948080c41100300d480058240088074400f001044408224802c00c5009901c0780c10740d820321b4418050106859001c074141d030203498000141003859100c0c0190403e50407400441c86172a10303645c005020909101c01006c2900c0e101d54440340b604041542e52242d40185840c034401569003552882c2441782e1f0910501d80901000003c114807140c0070804207005241e0422810182c80fa02c1c080c1c42c00b890f48110241c0c407002c0004102c1080d00d03c2c811411351034100c124a4404c540303031421070b1410568078080d4468845101e02e00315182d074400c030101c00c000c00b00107007210040c050400e00908154444030080e24030b039042001c11407900c2e000c3d90001c0180401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177624235 1250 177622985 177622993
    0x60b04092003013e0a0206070801060309020f04050406110705060f0a0b03060a0c12050108011d070623071b0806060102030703200a060c0504050406080c06040501050c01020c060a09020907090305 85
    0x1400a89081c52500e2400e400c0c0f2600c030709501c020120944c40c01401070101c03030390020605030408400182900b10141d000808050030f0030113181c0180c440c0000a1004a0280d4022900313440d03d04d8410040d080340c5110019030b43c030200d500001d006001a20070701410350445200368503212030107501c040e10a0740c8482130700359200901045d440140d0364011844d504192a0044485020f000c11005560707080e841510982c2d1030310301281c0310070a41080c81210585038001003001618055000d014001e07020345401010030f01e41c3e03104082c02400300c116880681e0210b0780340518032902a1130f228160050040c012248603040002d400c035400041203611081d0542c80c1d06400380d820703580104503408083c08280690050322450b0380014028010b0300401c00c01c546800d9100c500f06001d000854020340e0040340b0719401780f90300d4030f0796072100c60851f0300341c44007840e00314cc0d01d103e802c01050281c40359203c07190340c80c400c5204100c1c411320306030700440f400b600c200c40401d8552549e0f20119800f60403400040c02d1500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177625485 1250 177624235 177624281
    0x308101e0f30140d030e0c01080708011a0c070602060108120405090402060a0215010e1f0e060f181626070305070c050703050d11030a1b060b0409200301 67
    0x4902e100d1016240d00c50b40000490104099103241000784054800c00801c1c0c03104100c010a08092202100d0b9080070f2078802d142d4036104400801084062151150746400284041004680351040380e50b4803000908481c1301a55070003000750384d8942441418280d004284c05a2a6003071020101c808540c001841140d2944660b0204151944261003040039482980032283e0002d1801103010b0003040c42828810292508200c0c20090700b110740391800819070500e00a0154110300c1c0c0f04140c12090542c0e581c5401401c40c0c010816060360030500a42950005d020031000031541000c0b0303800c50358150358444e08060a07150b83c0d5400002d5404402c0090344150010b01220701c02c0d0303c00c1758880c140b46002b201600454499500b40003481d04141e8094105e0500300b040c20f03803c403200324014110a4011403410010000041006840c0c0e150f6690004204036407406003c00d070313080b43d08240c80060040240c0320880c0341c040c4805001420300b4012040f41d4200e10b000d45410700c5070031549607040e4504c0d14030315 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177626735 1250 177625485 177625559
    0x703080a0e09010305070501260f0402030c0f09040f0f0b040501050601031a0d020f060d02070c030506090f0a080306010909060602010c11061b090402040f0312030b0406120308101e0f 80
    0x654182c5c0609d0700c03540c3c011044107200d00d5401c81e81d8051010150500d0b100d00341030042c542420b08150000307004000030711292407191215010f059105800a6420030340d21118545846242c15030b450182061042c801030000740201035110f140940400d0300c00b080800406802c1c503881d0812288580c1d4031105003130030000941007901c6ca581c1c1c010030080815103022050b610a0080ba0000783c016507100d03103c1c41d0280200b010802076545c01412400051201c008a010200d40d12003151a005203002408004507881e0b901404246020308695841404a1a02d42100a000307001c44034501c0002084082a82c1c420034010a08600540340d401210000d60140b84c01090a07511802c04a504140c0c20400015500000d481801c05140b15050092900600c400d000303007a10041030300240701e0352610608020040107031003508007a0381c1c5410300e099503660f64000180446aa94820942080d280f085803a141039030b04048425601c1d01071903109000d860340f85c1c2000400f5046d02846100030348480b83c803040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177627985 1250 177626735 177626747
    0x14100809010920010905060408191103011d0c04090b130312050405070e18030a121b02160f0503280f0b06040f0b011403180703080a0e09010305070501 66
    0x20114840c00441c0325112a0f850504001d8503080c0071000c1e80d6030341e0303080d1000d6a01c440c8960080404a4401e0304040c281204180c66200240e120514101014171030810015004844103004000030003c10040403034100030b21030742c0000034041845000e80e402d001843e1070f040c42904003c0350807800c905007554468403025030b800d200490030b8041c0000031400410304042406542d120f6803041c005022081d20b04203030303075201200190004a900081220010041c100007064500e58042c0d0300d4510000d0301501c20f4100140440400ca85400359514600c030f222540014902c04070a0320240c00e40122a607481d02c3c008205428051981d041e005200c0701d00e0460101c480c25040e15405070242e001809181d5215142003914890441d003ea642c00c0400200d4a0b00e0301c60303001c403c10261000d00c103c2d01c040300000c0905250b070700203100d003d0300400807070142c0b40c0c4c0c248007282003500c410880f441c1d16142d0800000540005107042c0025244002044250a00d100b9450489a0103002410001e0800c4019900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177629235 1250 177627985 177627991
    0x90903260402210703060204080f0703080315060d050907030209060d0b0f06011e0f09060e0f1908071e0503210d0f050a0f061a0d1a0d031206141008 65
    0x2001c806401500c3c0c001052000400451003440d0060381d9928041d800c60801042d0b0f80441c0355900182820004929044200da600541065641c806001c2e2070340024400d01540c1c001e201d590740341c04108004404005002401c1c0c80c000c03215840b81e0b58a1008101001301103460007400940c0342e2011a64004408880036000700d414100031070304004002c0188034071074142e1070b000d000411f01071060700e009810029800141085103072403c091820500410540d040070301c0103a01074444450321509a02042000728040c0500800f650503280e943c1a809081300d041000e03001040c8460b1310b0015451400140c0c1d0390102d0076402104500382154a4000d01580002001098580c2c0701d0200491413075803446518820346c18814001481d503000c4420000301e82c03a54103c2c2100342040100ea9507200c5c0a101621200303508244d011460b2000f80c0e90708280f4050003075100d50072103e541c00d03403400c1540080ca80c039905c0b58040810482ca40d42c0b00d00c1c1056208075006815085550042c800303641c41d104000c0554 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177630485 1250 177629235 177629269
    0x100f020c030d1a0619170709050d02010201060801020301080d18240c06061d0f0613020a0e040c030519050118020a0c1407060e060c0c010c05070f090903260402 70
    0x62100f80070301192441c1e110b0b502d0102e010000111034042281c000c01d01e00501444060f20101c1481c110401a26030312850007261b20560340038007101c003160b01c00d4000102a0a040c230083d926565501c1c04507642d1162518400080340200039140b0b0030b118210000011a403100d809003c8020650382d41c210a4143d00004c00204401003449001052060142c0d0700281002e0b444884140164a2009040080500011804420602401800d556150017841c501c01900801682c031030707000d0002d0b1801848074014a4105042440c240d00d503a80607400b81d0f10880380c10f094051800d13220824001142e400340a41022400c40c548030b140c0c0c403185640504103050301400c2c614855250341d00e4805840b017201504211550003803005202c61a88450304003612901550980d00740100301c40102c1d00c41744103141c9681040204a00c2c0300501c40308000182c01045914280d45806450b11b8040c0040c00240034140d01240c031440200e0210b4013048801c500c0c4030072039a046401600c0d1a401c0000103a4008020a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177631735 1250 177630485 177630521
    0x15120a090c0305060c03010509090a02011d01090e010f031e030801030f060207020918100905070519050d03020f0c0105030c07060b03010f020d060e01050306010e010306020d091202100f020c030d 85
    0x840040d904000e02c4e40100c40908200c0c3c0c60358548410864072490080c00f02119400810382200143d030030848005000da0843d4008480d03c10550041710243d40982c400c110804041c0000204420041850801d50b8011010506440001d400d8180c44108070b90006000030100001040450b00c02ca0401c6603040c8990005482c00846800007828000284d810804070200d001695951060401840d2650400b005050119a03080d840d8103480300b019200d0580111440004000c103084c02d900e2010143c10300520400380c102403410001d40e55606a500a01c4901c998000c404441d0300030403d80303228203803c45e034142c60000c140d80c481001d09100c1d05141d4066480d1600c0070310b40e6200c2e001810030700b02c002e0000901e07249000790721551180180e00060094015000501040c1d0042e82030505603a006080965035a61000105000f007800042c047e14852500749090641039000c1503540703142c5100e800a01c0b00ea9421510b5800700d04c103079503860030158801c020347c07012043c1c40d800446a19140071160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177632985 1250 177631735 177631739
    0x120c0302030a0e0d021e0916090605090303041203050a11010b0f0d05100f1a0402120c0c0c031c0314060a290c0a0201120b01050403020d0f0c030305040515120a090c 72
    0x21030201c441b856024481d060362000c04100600f0b05082c80e550210030743d4080c01010003440c03c0034011100d680104c81c20071000042102e80c0340c40400803140240f005000d404040300c4181001002500044105400602d00c0564481004070500440141c02c0000703043c01c80d21040801040121800c1001c103d030f890090300000d0544401c1440351200e0b0309880a400700e003001d4101d540c0e01c644441300c000903200b00d10500485d085c140486404030380c00503000242540e51070b0740c841070a1400d00080380095151203404460b581c407110010600c84411840d072800e01109580080e01c40e05003030304540807a0095500c80d8100f00c80500341031107003070b1f0038555102d20301d8205011071100616070003100508040d41c4115032500c01c6580c8022452641c0d140302d0401c010955400000801c58030461101030311913001301c1d08540074088600303030081803154450482142156240340180c42c0781c10030b1103440e22070350320700940c00e28245000d0110707400003110a030702c0310342540c4600c0807100402c50800281ca07226611040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177634235 1250 177632985 177632989
    0x52101090507080d020d020307150209120d030b0406090504030212030709081608070e040b0c03041509050d08100513020a03060f030303090b01051503061005190804120c0302030a0e0d02 81
    0x500b409054060040d000700112404080d03e406165a00740045500c2004081c000c10103070002000c10080e01c1c040175030354a5035000020034556080c00c6e00310641c01250042c0e445150036504c00c0201305001d5905100750f03681d541042c0d088407030407034014015030071089200800000b41b01c000c69101059061649100d03850f185c000c1e1030186049906218210318440a0102d95802c20032007008200d12424050145815a07907803100600c0034060080e001c00205c0440d0401841c103101140c0a5900c01d820030110100e4248280d480e4065025540800c0c040c2c0040b0b5000c40141c008101550f001524103255000300c0a10031000354410020403041603514031000c1540707820200f091000754001d94000c140c2103071320705240c440d513001a8801c80c40781094448035100c3c50040c4045d01c0d40047c0c04c50703078100e130300340c0c0298140c41c40c1c8200e600380c2c82c6196410844001c80d981191455010303c3c0101e05484404160b00340c1a540040f2100001e00036034401c0c0301c4007090600c10b500308100f90030080e04180410b4680d82c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177635485 1250 177634235 177634243
    0x50606040f0f1a190605040b0a0504030206070803040b0a05130b060a03020a3312020703030b1c0605010b0c0a120215160f030b100e04091709090a05010521010905 71
    0x2400815000289420f0410351074513201c1180d041c01c500301581c3d030715460118094039074411442006454500414550122800303a02a0f81c011a0040c0c03000e40d82e440c0501d844480c50307000b00c0f003c940c0dc0710500041904030045220ba188120652036148060007652f40306c0b000f600000a00c0d080d44480484004001612509000c200908114010301c202d00318000c00d19483e141c0d070328061404400050304d0154900d41c002d04804d0700411007400107035640304608044000c0c042c500c40c055000f810030300659581f01e50300c0940d00310710b90188004220310317600d5241c045118824a56007072401d501c040906404154450001d480070401401141c0001c42101c800e8140c4c9801118a0240900d030308075001d500715042094000c00107028030313080140100b900300182201e070406404004218100c0f40300226030300d4551064544c10303040040c1d8201541415103003038865001007410b5005014101c04100c42c41424003595040c1c0d10001d04030100c0305580c03101c4040e0717556910103040d42c542d02c400780040401d400384 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177636735 1250 177635485 177635501
    0x18050a030806090f040f0305221716050904020f060c0d091724071404080303011d010b070206180603070306060809071d09010b0a0e04020406050409050606040f0f 71
    0x249540c841440d101040000100d0010301514104800104110000c3e00b12110751111a506060454440c04c0c1402ca2612701e440044003802e140114032004a03040c1d405007054541c20070b03503404070b400c051101403a103225071826110302d942090b80c2c900490300514106204c800469005484141820684000079190501c1e00ac0301344007040a04000b4802901034011054901c1d0026004041c00d010600c2d0502c049030b484400e01130300385240004160b403a071103200e6004140c14078203d51034445482d10300c0036840f94000e01c9451030300120300d4400c2c05c150190540d0141212080d0240c1402d14003941c0074050294418111181e00350031205051581c1d03a200070217180101e800d9503002a2a41c1402006000c1c0380c00075010024640c0555810440d6103a1500c0d58410520100e400e68060744600b6030441c050700070305503407540c00003031000c0c0440c2602481c800103108600854061015036a0781c010303c0200d9900c40801384c003942102001440c01d0510b604180105462000300141c0c244a0105807030440d1504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177637985 1250 177636735 177636737
    0x50f0f032104090506010906020d080a0e071e08011e0c090b041203080c09030a06090512030c13050f0f09060f06040f0501030f02090a0302090a200318120d18050a03 72
    0x200b030034040d061580c401c07a82d000c5400c0c01d01405640c20b2150203555014040240030410212070005600400d01e501b048203040c0548045038042500e61071a040f680540e60303e04140900750920001d032003481402446040c2031040c080b840400410000e900261005110321028018490700010b800c5540c400144001c0036001812080e507152450700800702100602222074992042c0b00300c174020350740031610034002d5130f02c0350000504110500d80f160410042624458500364080208100040c0c00c0004190010581c14a6103410b070315881049914132460315026004189100d0b04c2045040c110b0001c3d4004e4402040c0b040380d00d86510006180b940306820032505000404403c0200c0d503014001ca90f038a8001c0c51080d402c046026000c901d5014191001074415641680464128101c41c0d0020041000859154918441801084880d43e0058400500900341500100100740d00882d01e003d10181c03140038240307044072070010718025108a0030614844060a1440c000042c420080d14226a2003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177639235 1250 177637985 177637987
    0xa1b0f0204050a0c0e240a0f1719021b070b04060e0603010b030f04080c030d051501111b01030f0e0d03051605190302070515060a0f050f0f0321 63
    0x500e2050005031100504201d60321801c01003da41495044000031140d00740c1540c0d00072460840c0c1030015200110288002c0402d500019038000340d5a03c0744400c0035100301c0e6111403078104080c50030f20302d5002045a43c0110411000061410030040b60003c000b0180303220420b00c4980c148084041c02d00308254002100384000040401446800000300c8200e01421142d484c2103625000c4500d8040c840106251100710990700001c041045203070658042d10a4081140e40740c45441044c24000e10b01682c0741c1141a561189242e019071251b04100c404850b610050034000c0d20720f151181d22029040c28a605044d11a081141040c041e0701c034071100c085007400202130075200200d010f070443e03001400030511000340d414000043c40e0401d00300c402c0450304465445060816000880090250724402082e40c080e024510b020020b0216034180200c2c8120390315000b09640f1001082c400880b44101500038034030801001c8145004100c000e00c480d0301800340e4920f003e1440e00c070504034a4009450049541c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 177640485 1250 177639235 177639263
    0x20a03140109051905070b070f0b0405010b031203070e011d06070c0f090c090608100b0307030504020f31020f0a08090d030515040504060b040203090d12060e0402060a1b 74
    0x803c01c08441041340c0414400c5054243c80e066100c0032580100c55030110700240c0c2c8070800c40e0703078160741d00a6a00409003041c1400c0c5031800c28040c0c080c1e0360500c1e210b44690196498900c4045040340d005181e0358480d02662140e15006581c42d055424a03035241d041541101c109603101d000080049600c1682e6000f645428070ba000c51400c0f409800802c0200d20f040300422509400403050000e4039164105044203540e68404410040c4658003c1c80d05088003005214086405800840c09903100b01c5a0310241044542400100507006a00002c440500ca8a2003908500c3d85200d00300400650001761411000036010300c1964080b40900f0006400c80c000c0148840b01448821b4401c160381c40d040c8200c0c20304c106d91071552003050502d5482250b40b43d0214080040560000c030710404094015074032880e200750100d45a203a43e408040103d032505251100e124801d02c20714041c2ea044058006490301c85030281f01c415000b440155042c480200f682a1144140c200c1c01d200d600c1c0300b00b040384000300d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 177641735 1250 177640485 177640493
    0x3021306061103070203032203020301090c030218090d03091b0602160b070503120601030b040501060315081f020a020f1b1e030d1209021c060b0a030305030c07020a03140109 76
    0x21002c0007540d5000c0e001806014016a0040121030300e02c200c0d0210703441c2c501103000340324864500e01e5000075455840c00d0180010007030004100c1e8122802100e41a0301035946079500071000000315452145038000140c2003081602980c00900070780c0c0a00e04401640320080404011220b481d041100503900002070395600d02d80040d40000500100c80310f00e0f04109050381c07515581c0c0140850140c00c1c80e08031001400b180d00c246d204540007070004200380714559503000050010100b680340003806540000380450701403c00104ca03600507006483c2240e003030030105c0d5403400a400c101c26090450240012040300c4907820003601001208183c0c01000e500249000c1101300250120035140c80800c0b000e08030030710f58000c919404000a64200f5462003c0380400a0004100c1450001c1d40048040a00016071542481900700184070f10704c2088100039007820000f00300c02c0342c440140020340800001e0202c91002c00035003043e61020b007010444980725070b52580480c80c260f44800c0070f41e544e405010180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 177642985 1250 177641735 177641747
    0x903020a1724070f0c05060a1d03040602030d090618080d0b04050906061020060115030209091f1d25090b0c030405031606090f0e010509040501060302130606 69
    0x70090b01c010666280e0344890002c9024000104620705124440e41840003060091441200c10380c2c0c4078040c2c440c989000c4003a10000c2c501e240e00d5003107403616038400c0022988000119425151319030011810302450340c00040140c000101f089410640f241c41c901c454070f4040b980f240710f0600c038200396500c41c6000144201100d00821a03036200c2c60908042c046c90142c049507041c3c10200564481034040d031000b9068a170078440708c0710000340c6411b6002c6228a040023007001d6050324202d0640342c02c0225468801c81c00c0e4080d8401c1c0590000303003500820514200b0050b282000300d243e46001d00d801e03982d048500040e003503d4000f000780c0d844000c100b162224a46480c01a52a020600000f080127041e400820000103070050100b80c42002401d601655010800e444c0145002800c4600340300720000c0301803075010380e4030038200400c000301c1c000724101d070807580350708240c880c0c400000502c0e03880d1000304100d00070080c00603205c956a810340400541c442565030790340d50304280d01c00720b2410702d012402092 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 177644235 1250 177642985 177643003
    0xc020708061e040212120d06030308010e04230a0b01060c03030509060925050a06090510030c0507062406031a0301140609090f0303010609090b0108090703080a0903020a17 75
    0x7601988070026000c2d5400121041e041501030310191140e0150702400361030075403041100c0b030380a240860544001c1401e900300c1300983e840b99072504041d999410b406d900401e03094078000d00e0004040c40840f640c9094030314409403510014102d58403680180c807900078944007038000000051190ba40c150a1503054001c55800015001c020b061502d0a6083e1507103514091840b05600e081a851141c25400c1710508500642802840c0001242c1c0e0741d04050000005841418001e0050800c50400320340a0300c01d03c400c3c803e5640f62549004950b582d444024956071000c0002e11102c0418900c40201c84901c680c0a080c9a490000700044001c00024401000c040000d2103070381043e61200c00d1a0b201c002150f004102500c190071141c031600907180c01c120340c000071805280b002000005a044d0700241d03440c100c2d0006142009007501c1400119a03c0004032901881648016070800c00101910010402140c00d0b181884d540c0b81c813030780011980d81c056401050340c0981c2020f6494051000d20051070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 177645485 1250 177644235 177644251
    0x170c01050f091903030b2b02100c05070b030402130c091a0405180c04030b0a09020f01030c0203160501020d09140111040f09020706060e0708090607260c0c010c02070806 74
    0x150341d0f4007100c0589000c42070300001401c16031500000c00051b110010001240c035001c51801400180f01c2141a00c0300c084890260301c6001d000f121402000d006040d404501500007000d400c45038103140600c000d651002d041281c10205014400c11210054824560b0b101601e075070751802d0343e00e000c3d404429002c188141060007001000200302a503036118012001c91411028110030341c3d241040d510250080794006404910020100034001100390b00601c0d025100f1a000e80c0c2c003e440100440484d0325281d00c3c00050f0b8000c11555008418500e081901103100e00e00151401d0101d0121030306071070807a8400c484440402074540850003080c0103164002c0380d43c51400d07040500e01000500c18040c1c0f44a02c0c450b1550000703004040c820160070820140c080581c24150906058400070500301c030494081c0e50501620000c1b4450510030a00700c452010342c03850840c4410f18803103c0084904001d400d030205d95008101d8000014801e005050007807000340c0141504034035050900d030910100900c0310b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 177646735 1250 177645485 177645493
    0x81b010c120c11122d0d123b01060e01030311010f110915030f010b07060f0c05030414011406120a021002070e010e01030f0f0201051204060209010e0d0507030f170c01050f09 76
    0x1750040009a211900c044a14010241340300090b0000014208502d00080c842103000c0d101d8403000c41121030382c401401c0f4030306100d021805640f00707a0889445000d40343c0302404038401000843e1141e00d14083c0311548800004002411039848030880b50204003d2240b1200807905c0b0081d45440c0708d0810310560003042640c03175440c00d00c103a8861410140609015003801150755401e1203140e521040d0f480c03c86101c2004250354214025255400c110703400c0350300740f40e5100c0364000d00b44180075242041c0b10420b100c0b440b9445000c1008140405000c0348043c910513101c030107015075a168001c10180100d600a0085a81042c00c404107421050b0003440280003c0e0004000085004500350302551700240900d103030044600c01210382c0c0c441e4000951249031010248800e110031507008100c1c0741002d07203c01c004c44440340103200141c2c4d401c1034050300f1900a50001c00c00b042c40c5d8502034040301c0c41901015241c8481303d5030004541c0081c0c42c0311000d13039900c074100700c14421046500c44e0000303c040020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 177647985 1250 177646735 177646813
    0x30b0a030c05060f0712030f0605030102090a06050306270403020c090c0d0504030e100215060114040b0d020405210d05070f111504081b010c120c1112 66
    0x1c00d5040704648503182c0191000111808074078548816101c40545c4203600401c804c624060040140c40440030074080301c1d2801400007480e103014400c540c09010050410b10f0380602c0e00340c0c01d54458000400894002c203603a440125420140c05486c5410300c03254051103101e04142c10002e180035200042c440c00380d400003060141700354a882c140d8480c8403042001241c0c0e950307180307011107810002e00340745600041c46d81c1556004079004514608121001842c81e2516a05c500044903652345044660f00108401c22062000780c1e02e02e030041400c1c5582d000c0152500340c0c0c500200707040024540c103400400d070102d0070007003001009029101d0150f0641ca0045e06080c07080e2948141419940c100400c00e280d400c4c0e951105445411101c040b076040340022903103840c0d6a030651501c1e540c880e0700c0321603200480c1007180c0c041d6010b00c090910064106c2401511800d5840301501c030240e2003081601c1c1c0311400d0001d03941d20740e661425034000070b254502034410425094451840080b048810185400c668964 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 177649235 1250 177647985 177647993
    0x902070203070b1c18121b03120e0a1a0901021e070c2706050a0609030f060212011205193c06020c060702010b0d06050c0d091101030b0a03 61
    0x10059405500300c956541070240c402100c4c4a401c03050425a417400d00200014000d142041001d1310b601491b0010140101e20108407101e0340010b089445148107034084201082c0b040440c0d860b0340d11007000001c2c0240c1c20b50f580520740500f54500301d0354202121410031022440081c40758201107004025414090038600039101442400078081010001007950b100f8400c6902450004201500007584202001e180c8017801c248691291521542030403000115400c01528130000c031100c2d5651402d2aa00f155030344400684410016982590240212007030f10390044401402040c411142040680c42c62904505080d001424080220184001003000c1215810203c062186010b028480e5a0824100d404110703014200b003800c01e00c03098a0401042201e6004020303014001c0b04031000e070b6440c90300407800d90704800030302c035000782040500c200020000d41080b6009501c144043d410002d20080c064110380b9001c005441c1c1c4650310aa56404d544c141c450b403000d880302a10011121030540e1a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 177650485 1250 177649235 177649243
    0xa08010513050f0c100c1104050f10060903050a0204020a200705120102071713180b0103050105030601061403060f1c2306180f03070c08060c12070f020102040807030510060902070203 80
    0x45911700340011b0700c08040401005080c2011681001042002203040c00c2c001c122408404540307000d9404803010b004030341580a03074046000c40384d010005051058a6600b0311000e5042400703a0710030f00c1880382c444041e40301c101e0385001e4800c5041c4010410f66140c5800c20404e04d070302400c0025240d1040204c1404645031135114012500c3da80c403d1642c070070940c2c01e43c905162003907110b8008829080742201c0b00e500c16400c858045d081c2680d003804140d0301c030380c1050388400080c4280e01c040360003007546618459444000d10b90001c401002e04241085080205004030b425949440d00b10411040703d400b00055044500100800740c00030042c1072800c0a0803a698010180c51402680140e080c41400303240d003040030203004e08540040d207032102954079001c0b440700381c1400707010114043c40000131029000072003035a88008449528000c113445028082c2c42560f0142c0078041155020440854461030402c40c8400441c8a90001d0403080b10204002084450980100144500400c03010016a034001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 177651735 1250 177650485 177650509
    0x3040302070b0306100c080f0409020301081507021b041508010c1103190c26070501050105030613110a030516080f07060503060616170403060506030d020d0e0a08010513050f0c 77
    0x8100300186d690b032814130307c829001c0d2809680702184009808103260308590042c0d41254441012100f20700782078880105402802c403102001a07200ba010701d0241000d48410080c10180604002045000a9078054a002c05030b0812800f50791103040031000c090b80304950f04962440c00016500b8044510412030b10b00c250384d4540c07010010032201e607600303000c99408078600c1c1c000f130001d0032282c81d400300040b00000e8001040030345095190100015a03410040f42061007480d40c00d405000780c11550b65501c201c89501a44190422039001c80840043d07400c000c4604020321011308003401074988482c9a00e00b0650101d10307a01600046010031a1607000002d40ba00030100300c49007a01c1e40e01c04209810700c0c003e802c6026040d0312051014901a00c012402003040c0c901946041c41660340d8132040c15610f400e070724007500040e4807080b034042da5103128600c002e14100c4001e08020045554004a5080d01c03000d0b2100c8055124001c404800c00c00c0400144410300b0345507000c0c180482d0b0040c0081c005d400c0d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 177652985 1250 177651735 177651737
    0x102030318070906030f1407060e04020f0714060912091318050d0503010501140304020a03021212070501240602060720031207121104050d0507050d0803040302070b030610 75
    0x107080c910020740c4090054002402c2141d408200450341c0741044821107202000a90312000002080c0c8401780004ca10305058805980710407154a8119003444000c3d07000c03100031920500c0620107040001c404292070030303210074484001c00792800d100c0141400c04181d42d03920182d9100c100111001d03500d40590301201d15110141c0001e1004882401200b04021031000510034014100041e103d00d42000155040e2003081e40ca1110340111800a02c2d11444140c4003c0d5000350b00440401c0140352a401c1c26402c00f00c0401502e1140c0640d071003000b0701e5002100301302d450384d450b800205000402080c2d55003a44446042c1803070382500d001d00c00b940340c20380a4012010400f09844620210382044c41d042c094001c21002c40303588001c810050038a44006032001c60001d01c0141001240c1040d90082251200030011014a8546040e0402403c2050311030704880ea40a5001c0001c0c50f80d0fa150149900c403400790401a50700d24181c076000382007441c01d4000403000507092080c007903151105684a041c075541 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 177654235 1250 177652985 177653011
    0xf06031a09160b0a0905120a020d02010302130f09050a02030610030b01021207080a03110415051e040e04060f050403090b0a110102031305010e0c150d0b03010216050f010b01020303 79
    0x244121150500c0000c250341d01d51001c0c00800003c2144000c801042c1e025481d41d510402a502c9a040000d08104808003100702e40c8240c06010262034001000003440f403050500628102401c29001010041e99101d880508400881000500424068141e006200000c11850f600d010400580192031030255402010340d02c2110b00c540b80d00030061035859101c0315990360f0b11801c00d480d0410301030344034001d58400242040f8006103035280000645080d651031401c0c240d0b00c51740d901011262a0401c2051a00b510004103e051204507000002e1003d00480d40600c0a02c4c58a030800c2c0c42640d00e0000300c030b50064501801c100210758080320740820380301d041c001d2554440b50318208461600035841c1041441d4400018030080d13002650501400c144140020700c1300548005c3c2040c2c58041d506401600019044185509035a034800100790400d08900000f8040c0d0366007011a00b2070300300300c41d8040564454495501400030400c0407078081d80d4500000e0260148040000f0344074080a0448403140310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 177655485 1250 177654235 177654241
    0x201060e01080c0a080d4a010f09080d050c0102040f0603090c060504051503060607140c010e0402070809040e030708070503071e1101110c0913021219020f040f0504150f06031a 77
    0x1980d0041d2a031580c1290105581082d910003d22400915610fa5a03011409c40e403610300c00c1c5401244602e04075140b1602400c010402d44d681030356145d2103c80c010304555820440881c1419035402c0c050050450785d80e000500c43d1f5507180c400b684140540083c030a000e014081000b0a541d4000e041d5000c03850250882e03144e8403214041461030169400c002e1007400d640300600413080740051000e00c3c1d01002d99a0a15504404060008a1080410180444601b004550700a04003500107000810301c5d001142e1911000b41c035031950640011000b12519000084c07176000780302402c5800314007108817030060302c404a02c0d90360f200034042c64645503070f040c081100202c590f10b15041c040c4250220014041000e580390442c0c41c074020801c00306e000ca10801102495420002c800107414204d8100a00c100d60914081d800704040486a0490194025141c20640303891315042d00034a400346108102082d4600e0308881420141da00ca0200700003002e18041e4104003141c0350700c11744441802580340c1e90700c60351 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 177656735 1250 177655485 177655547
    0x30c020f0d0f12140a0f0b18070c020303030903040e0106030b032a1003061508040b0708040204020706020a030207020f040e030a03090602070506040516050315160201060e01080c0a080d 81
    0x3c1508141d421019150024a0601400c0311004511450300e025040000f20b140c0c1c1b007035804440302a06415088542c070904800c1c00444034100c00d07002400380c10311002d021119800245145d00403580300300e15400c00f01e401c000890038404241e024003d1403c05103c0c00303000102196039480903401c8403203010107000070641016601c1050810021002c0c0000d1307114001c0080240190034540f00d104060317240f1a08070945144110003403030250b544a58150300c0b030344503500c08449801001e00b0507603010fa800c01c1084001441840141074010b169200562100483d0040242ca00ca440481d03074040e0b8244042040b0040c0701000300e846075480c908000808021904114000b03000d66a80104640305880a000130b001c0009050a11071001007080410035441c1c0c0285500c074000d804d48907000c92004004105005c50410142e072040c60207100026015603200b400c00c1700f0010a901c10340d00742d0002500b5983d20b040c400b8001d8050b16400d001054138100ca45c03001081d255107030590000842000041d15403507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 177657985 1250 177656735 177656747
    0x51506090c2d040603060609120b0601140c0604030915080106091a0f040608040209010b070b04020d030318030f09090b06090d020117011d09010b030c091305030c010507030c020f0d0f 80
    0x8048565406880d03035201c40018001308110300500021423414400012003500c07509000600c2e9601200200b00741e102d0307000550f08440c004020360002c103024080492404410001240301c0c078001c2c1d481b403160601e0204410342c0c150342d00c4070306410000114014003045400514440840306403450013a10203403a083d0405941c0140c240000d03148a000400080081d4082030081c0164000c58241485903a01d8291050724495414014645151030740010003501d811700400e508603011f030072302107094054901841d180b00540803040780420350101c00c5241c031580c03044080c4d0180102e2801001107000d4030000541e80d00801541c18414551b80462004591061034241311055022031840c806503128010040d07084a0010003103082c00210340082d181940501808840300009006811401c3c0070303c0c1170019480740144854903007280e00269100103881003005142c80c801d200300028607410301b0b090003025242a03407501c108560202911400c00d940214a0070742d68107113403c2c40704509541940075190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 177659235 1250 177657985 177658057
    0xd0b090709060e100e0925050906010507030f0302090103060302180106030c030b010903020f060f030702030414091303030515030a030e0f03060c04060302130504020703030e010b100c0f021804051506090c 89
    0x202190811000303000c7c844048010f42500d81c21164114295a00001120349008104010b000521900c0500140b64001d6008151480040c5404240399489401181680f0004e5410781102000d0000400c6240d40c18410084452401d1034184140041180002c10a21791360001a10689056555290f981d903201d040303a4005010f050303210346034544850065240e800503c02c2a0031104244a1a0068684504403a1184080e03642e0740307801117a1910120028100204940c0300c40d81e040340c00714041c1c1d5081299400f02d81c1700b642c4400c0d403805080103100219441a2308a4000d83c000720030302c11000180310549083c1c2e1400d2400607103409045501c0b00c0142107642c00036401c5480002d00c0c0b0140742d0306030030a82950034210000c0c4000c00d00c0009019401125407007000005250007640f50000304044e5190001500041c1418050800c140d6009140c2806403004c65842e03003d912a078028a01c0204480c2d4000c0084812020754074104950101c02d06c81c3c0185610000e0700040440c1403540c0110103200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 177660485 1250 177659235 177659263
    0x105150306130e06010305100212010b030411190302040f05060607030c0f020d082106090109020a09030b01091d06061804031e030614030712020405060d0b090709060e100e09 76
    0x1840c0d40b4900c0252906000e00090390f090080d201040800345040c02260140c0c1458110004c26030310303123300500e41c0c9d04042c0003210210803051f050130385a40e402d0040040a180300840c500224510303c10030046030803080384048064200320801900b9941e00d03042d1050036405040040c461a001d1506400a100413040294440448080b4806002512015028000c0c0c1c101c09141150a110304100441d0003c8400300d82c030511100c018002014140c020b040011041c0c00c0400d840ca03102e03510601207000980254030150741d50682040c20110211140c0c00da01c4501c07000e00744505001001c24105442214640d000500550108042520600d8410282e601105500380030301003c80c8000c015124611412011510f00c0c02840310310314012031420b049913000c00d29815503040301c1d803d2002400000300503d034010b02d1100c0910109100ca420103208403120380141c030100d07050904100c1201c940d0f80040c5030155081040002d030354140341481c01500d2044042614070f40d00e82c585c003450600d2800d0154 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 177661735 1250 177660485 177660491
    0xc120c0415091104090b06070209180703080c060402040623041d0d021506031f0c030e030d0b1005180f03011d01050f0112230a06061203080f010515030613 68
    0x11035020003d10140068440e013043c10710585602008100240c080c01801079404040f0340041040030382400e050010303075500141694203040c0d5903101c40b003060f0080280d50146400038404c02c411843c05209020140000d10401d91642d214281c0f10305054560200003400b555603504511550790f070742031265000c0c4070080c088a44080c0201e0340291180401c43c109165585118045120f40c40c0104128841d84035042001c6281140d2010000207004204c1c03601080c07560b00d40c06411640030500041245510001022a14441520034041c66040c10682d20b010060107200c401c1411002e0444000106000c58100d40ca145440e0006401043c645007038082401c1d1071410071410104c1904030030f118000101c0240541d81c0d0f2144d81c0c0d000c0181559000b803882081e025224039000c040d000c2c520411450004403038100c102d590b0340000700c40e6180c200054200540c2601000c00d54030600290307000300401301c244219403406000c40c41c00c6071940d03400021020040001841510342c19015009002500d40034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 177662985 1250 177661735 177661751
    0x70b0a0302070b0123030d0212030406090b101a0306010c0204201614010606020a03050307170705190c050c0607050a0807080a02060903090105031303020f0a060e0c120c041509 77
    0x20f180c11002e41c0018000002c0206041c5c0180d113804a0203080030405034000c0c101d5941404c0900b0000c2d440100210360081d940e98000010500041c0100e1041c1030b143c448841103810088c40448100307030100d00d1110100704000f0000d0b00d036400700c9850012036066030041100f0549403108045850b80ca48014041c900c0401c200c90300c0070026100d08620350003810b154800800d48900d242c241c03540c0e4080e80015a00c4032983e0740c00039109400440d480525031034400d510707482035808409292420b0303504c20002180071802e058000c0b003070101070200607031038100018030342c0e040d42c1c407036071240381004009100e82c0012170740c4401c0c04418040c0e4010998044105c581d1100f4520340f118080d00402003c0c00141f00d4100000e140200020460784881c3e03058549034110742e11421224501d03000c540d0200c00b10701030325030724040c006c4080261001e2103108a42c045122018034907a00d1070031000400c03242c4a28460b40b0349481c0000f010580004c0c41105840105007142c48550210840005038461015907244c0026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 177664235 1250 177662985 177662999
    0x40e010e0c0411040e011215020301030f1e051c18170d0c08090d020609061c0b03070605071707081207170f06012307030c02090703060305070b0a0302070b01 69
    0x76a9a40011a030400881e0031001e0240b40d14040c81c01000841c02c9100014031804800326903800c00e1501c02c40b507810800c5030444a59040c1d800c2a07100f140d020128410348400c10140f000104100210a030b105001d068260311031644e50380c4c44a107442d0b21815140740441c2c100d8420102c038030018030843d41400201d5a1042d90a400d007883c0e10020f09580141d18120161600ca1040ca440198200444508100c4800c0802600300102c100490740034404004107185502d544c0007801d42c005101c541784400480000012045d1100c03080418440e4004081c2845019044429070f00110f4000d0201c958480c5182c00244040c899041c0143c6800e0000c1842103410110300d680c0d602c14503c542e06c0c0b00b410401103061896114040d247c220080b42d603a0006001c5d03501c24a029240415181488420700d1100e030040c60080d84240c400740c00098003c0003690640c101140003641040c02c1d4075081100a2a58071256160030360b5004140c2c0040c0000b4400c60018801c0d01602c85150700704815220315651002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 177665485 1250 177664235 177664243
    0xa030b190b07020301061a0f0a12090809031216060207060b150307030c020102070c091e0e03040602060612150702030403050607030f0b011706060d0e10020915070309050d02040e010e 80
    0x42c1c101c0c03284d0300703044000c900c140f41c9070303101801040702c0e4402d80c0c1407020003201d501e195040011120308009000e5071101c90340707980307008510781c0c00d0241c500540d8524800c1d080c18180701860703c0340700c05d801080001c402c09410300c0c80079000f0960846001a01c6a41e2031130204054008200c069611140610122416410103402103019012031f4a080058484110040c0d00340e00a5083c0940075203a004800c101d10061074100f0b0030060000740c4510ba1202c4414000804c50f09914030030500c03a1310114040c00b006804204d41ca40041045903002401d40001c043d0703580c1c80e04441c0c12030540030102c03001724003554020000d40d001386038414140c1700b0520303010b5030050050400c09114031030030f401c103041c1240d254000e07410451140700c0b0107951513055484100f408541e9201012904d0701d01e907038004800000b002403003c1e10303068590703c101580d28400601040215803144144a490100030441c1200080c3c2140c1c01d00308031f401c280e503824012015400081c00500e09036406000950800031680002d202c085 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 177666735 1250 177665485 177665497
    0xb030d021c09050603061203090a0f0f08010b33031f050d030c03050901050c071202030105010e0910090201121d161d042405040b06060304080a030b190b 67
    0x4501000c111003401c0100c40c4034515110f610b0f0841e074100049006810303d5090301301d0842404003240c1c5090451401304919094590281c4000400b6507414811b2007902c503102c4004000410003403203040035100c0020082481c024041190421450210340b2190301c00d0038000c81e90034021a501c2e16860420500303169000300c4402e0340b03000c0310809008074983c6000540d0395030003901641c0e554075455035668251850b41c0702d103401c6030500605000c500c58a1408012107809091300351108407041701c8034030502d400e65006800141014a850080000f406400148121a0f45003e0008140300c00c842c0011307180100d031103003110170b060b0820021060031005581030381d40c0c8150000484202c0c1401c090088103010f4180208003070840126208100e00383c241246581140c0104808410072426010280c52001419917170701203a9140c0f410001800009200c60b98001c50131f0321140d2640c40c0590f00c000301846090f0300481419507421900301c2c40d48486400701000036494622058498a407894290190400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 177667985 1250 177666735 177666763
    0xb01020a0506040b0a0c0f08060120030705010e0105060405061305060a030b0f0403170601051e04050a0303110609010c05090105160204050c07060f3e0a08070e03060405060106030905010b030d02 85
    0x40140ca110746e41c482c083e28001002d41e07650310b10b1180ca40100440f001c2c0703078440a040c4003c02d94020982c0143c802d00080040c0c0388100000112280406052420754200511035441145488200203071900da034840c6104840c411100004c80d580c2e000b00003003207114190405403201c00e841c020003c2d1b0700700039424507003d28042c4d11400c01e03401d00200001d01c1c0c00d00c120341c00c1d40050000d2104403c5056140494410644941c10740da060a4441000c40c050002540c029000908000d4801c1c00c0064180102500941003c00070b000030f20256001a0080c030030345c0c481e641003000029094850003440034244407210350041041c80541480d41c005482c5070080d54050302c690380742c126049510041449a52180402c460741c124002810035044800c0d000065a402206405600c800e00e0a900303007030080c4495141a00d4510240c200300000034216901c1401950080d0302c00b0782408081800000c205046610520380481c5c0300400b442e001c0e01409590020680501c181c80c8074a613115000b0446042c0341d003007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 177669235 1250 177667985 177667991
    0x60914090109020f0f04180809100f0807050901051b07080d26130b010306090c0501030903140906040803070501060314060115080a0209120c0a060302040503100b01020a0506040b0a 79
    0x604a2035600302e5800c840020b40c03011100d2100d0107907040031320303103040900002400060310200c081001c03107245118000464150701c0000344d504003413030300202c440d00740c500c01e1400100800f228107014000c03000140c000418442c004c0740152090f80310310301301c640c18200c030403182d8a1507400e070103965500c401e54091780c0207038000d8041c03040d00a407245018000c00c9201381c03d1801603198485440005890241046503850b1084003548045000004002d00951180b140001c80c1502400d2860018803150016030402d420485400302081c1e00c012690941d280c3c070100b9580e550750001c005000c80c41143e0044406000200f0210240714040d4020001c40e4014540d54000e040c0c400711440e203c503c240142ca00c40040000980c424520540d80d180c2e02405038880146003001d03c0000410507804826044d4590f4008800c030308a9051a030044002030540707040940c2030074140710005c2c1e01d40f07400c0543d241290356030f9a06001c141e03100b004403c0c03440350000251041c1c0c5c00c090410010707030301003203034000403c41c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 177670485 1250 177669235 177669241
    0x60a0c02030922091e0201020c0103020f07350d0b01030e07121e0b180303060f120a06060608070f0207060504090209031f14060d12050a02030d060914 66
    0x1001000b107608800e802020606410020080c1c0da10316801840820445669a603018001580c3c1c1c900c00300c1004000c84611926500d0361000a19003210700503040c0c1058010301c60f24128801000580d04c0c402d0344600b0044034503010603584069140d02c0061554403030300300c40020000c44406001403014000b03881c800d10480c038509005401b60340d10a6102c46007a40441c6007080454031501d40450304600c036040029001c3d00c202c0d00000c50740ca042005840044000c002d001444c10302c01d0104204030f00c0c13040550300354607007a00010b6050b24000705060042c000e41e0720800403074805100226103030307900c503204002a9442d0b46008000210841d10480842d00f0742d5010081d4a0000990400325081662001d18040c246002075020b03400040344207800d841030a02c16098041c82e00107070603035060a6000020221080c66140f118590040d0103a8002d0080395071542c086005c1e0180c09040285504005a1710302d001c80d012461885070400d10b4000301c2c07070b00d003011039140c04c3c0381c01030001c0000d900c2d00440162 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 177671735 1250 177670485 177670487
    0x9030206181e0910080d05030901060504140601020d0c1e0203010f0207050c03061027090f03051c0204141504080f3304140a0c0e1006050c0a03051b0f060a0c 69
    0x2501c4d80100c00c003540c40185032400301c5106900566005100d0000821000e56400c0802c086c1d40900c2d5245050700381240c01c2100550341080990450a51361414280001550301e801d03a150b0f00b00c041d00400802840500c0056440c2504944046070840385c045603a07151030f0504c1504e03031341040000ca00c64041c46020454401c400a210781c181c50b0800403681c8020503031542084c40364410040079007440e131600b00000c0422441262001e0040c044c0c1c8860366030b1050943c0d101c03000d880b10804010080c1c418801409004001010509584004e0f541514007c2001c003015070140519408038140f445400362509140341c011030000d8481190750781131020030700c0844600010b0650318000807050100400041d000c80c440352440c481c00007418007a80d0f0145610b0f2504035070700c0c050b5041524030803880d80c1400307000e100400c89480100030f50300c1c0482c107090340c41d12003a4450701c0803240901003120100351400500048051305180300c00d100c00300c45406400310f80c481d0300c0d0381d0110303404045246003081c00d000c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 177672985 1250 177671735 177671761
    0xa050a0c08090601050409020f031c020f0307080d020904090f080c010c05210403050409060b03010305100207020a0e0405100204090c020607030c050d05090f0321010f03020109030206181e09 83
    0x201104000b030b20f1140e003000140b2004150114059a21003440c6c015985161401c1c803a013007114900b91440315010452410180c9440c0b1000300035692079100308858404540d03004290384002d8072155000da0358014460004000d0040904090840303105600d10608201404d4010024091440000c0c000d25981000544a80c0510301c414042116000e00350020341d0840010254402e119051241c10320341c44042c408111001c1e60041d58110b0b81c0000107105000040000f8800d10b20032030015403608007180d0100e080680a8400c10000002c90808035040000c140015800b01032600001c43d12580d0310312400b0050039003480f00c1005401004c012405141c070a0061005415494642d01d2501c80181158002003c1c0101540301500400000810400091000f080040c404000c000140314902002e0444050184d0000360160004203041005036000100102100e130100c2d0a55100c015100d1041c540499003800c1d03a60006c0606d82001000e440c421448030b603080160ba5100716a50740e034084c0044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 177674235 1250 177672985 177672991
    0xb0f0406030b04020f04090e10050112030e060309071e0302040f050a0e07050307150c0f2402031015112505041107060e070812070b07030504022d06030a050a0c08 71
    0x100105c20001440005529081107905101103000c0380e11250904900004a0341e00380c0202c103003010b00b0400c48007416030112481e014174400f00c8029146080080840e40d80b1a10303446150418130b9040f8052a001190b4006480110340140080c0002403020280350000e03e000c0300c19490140c034000b4250011a0005140e038181c502c040c1c010700f5141e0500482c100e0000b070800c444020400c1c00c0303407100000703965100e2440d01c0522540b460140c401c0000fa034021280300140091481d64410b0041046103903c1041c0350040369142c2c0000d102000c112041114441c0d480c090300308041c031a155040d144a15032030420120300545249001070151200c0410060300c402c1080300640840610600c0c0100d881d030fa00211a91040d2000c0798102560b5510031410140b00f00b0002503107201c00304480703060260518105a000702e00f03103403c20403494141d000401c82c0341100840780c103c1044010041001d5a009116400c9101c0200410703128500a802c960281c00101c441000850401450b4080c0500030504a40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 177675485 1250 177674235 177674257
    0x609050f24010e0a1208090934052215030b011403180a030e0102060f06011b080405060f041e0303120c02010204030f0b0402040b01140a0e04060b0f0406030b0402 71
    0x126400c411401160190f181014040d400403242400007520110107118072101481070030126140c000303a40c20081c0e208002414644440f4001e10f6004188545001440c0e20903c40d420704030004204100840c3c19018201c00b0b140348880003140030900a158a600030120b42e111104801d110060715403c409036064182c81c180424400344620105240c0e02010b076a021405452400260141952261426445036400d4011230a945d007840c0302540d0611010768082c40034050300701c1c00d0a11100007400754160b080301c4814200d03100000380802800b001141c004100c01459070383c0341d805010300d00326264018860711001c040c1e0371111030042c2c0d102a12800850390075854022040b00d01c0c50015001d41400d40702c20085540c03c000200004400da00160781c16806082c204110b464584180001c03110500307009814400c0101a082c60941c22400710b0b00c1d00a0a45810001d10510f0720200307000d06007582215440032408a1020120000c8001400403954540e400303101181c002c030240802c82c418200024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 177676735 1250 177675485 177675541
    0x204080d030f0b0405040308101509060e0102010905060702071d0c03013015050702150a0e0c0306040b041a040302070902070503090d05010c02070801110a1404090609050f 75
    0x28120340c1c081c0e4801c0301d42c2490100086041041c80780018129201242c040b00850051000c1c4020a2050354400000e4144a018144800118036010704120301d40c0c071440d802c0021201c5488101d034401e40043e000c0b1640310044038070390305140f0000b0b5114850703800b4400070190318030380d041c01c0b00103018001801405542d03d198956400c040300040c80d01c81680002c0e184140f0301031480c203803456522840100c140241c5c0a003803024100b600100699802400c100c0456000e50781984c45040408003c0360808418a000181d07400d00c515200e0034103140c0c000d01d60341401088108001d1095440c0c040d48614482c29101c0d90340c02c016111980506419540a00143c0c4003007820b0010002650040602c0e500442c00c803810b10599500181140140507000ca40507510b41c2c3c14204c078182c0421442c4054900300c4000d11040700025400f10490046000d003c04100c03081c1c0240840c404103d042760042c0001303401c10711195803100e4064000e00000c1c1c417903d070030ba030401d4001a0f8030310700e4841c500b1394103911071011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 177677985 1250 177676735 177676753
    0x70303150e161d06030c0f131a0a0f05130b03160315080304090504111c03110102070215090a05120c0f120a11150c0f1009020a03060207060207020a0314060901020408 73
    0xc480203400003030421000b03800401c55402c420300b080010302300150f0110f205910050030081d441c641d191000482070340c01801801090b02107500401e0302ca00480da1b42c50324079103c42510b07500c0b5000744d101c0d42c0a003040c1a400020f1000c40203101080103400406a2400d10041140344015011f03801c182c403400a5542041c40705100c0b0204540020790020701070105114014007070000100d11003940020303003428210745c9104008250308220402d0465025000031410800c5603004140303225106900d140000700006107008259035a914840c1c00703808054100d000018501800700c2d0b54181d090181442180241400e014a10301201e201c5291540c0d500500101c02180e0f451190365004820f00c00c5d031283d6131007419821180c588000c0c04040320880014000c0c0110030030820308160540e10180f0343c007410141d6080140c1c40c0c548101040f2540030034010f0b41c4081c1818040000d028015000b50310100070781d000014440d4100300c001c1c0040d00a000e581940d268204020701300c4c4120b10840b0310701c0d0031003490 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 177679235 1250 177677985 177677989
    0x1506071205030901020d1103090607020d02071a0408070e0f161b030905060c0312090a020609010c0314040b0304034503080a0305070906090503030d02070303150e161d 73
    0x1c2c68100c1c2d0300c01c0015050a0a0f4024082030350b501c6203440034062808810410700c4101088456045542c031300250001c8008108002e480b0f030494099030001d00f000c0804800e0b000c0800303003250000e00e101c40c00d0704e4400c0d844d440c1c50520504261412101c0607050800704000e03d0200705518100e160b942c4610300d0307601a481d505c60034110380100550a0240345400007079580c0703130718004209005550000d940e58409440030050303445006051340515074050b00101006803195000c0756820300c001d08054044e04000e1400320f0382c1c9070341300c41090340080e0042000101550881d010b1405940300307840c0d41d1001c003400d006400242c1201510710414907010a801c1124002540c06c450b21800e00c0d61506850a4407034070b0721443d5600c200410400039513500c04000e041a0302903003c201034250340c509440b0030351810b00020f070789006552400503480d500080e2902014065400001c8125180d4040302002d6500c010900000c0f1003101c01c1003ca8210440b2843d00038030841d04556900305d9000f82c441e0309459102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 177680485 1250 177679235 177679237
    0x40504050402040e1b011107031101050304050709020d0c080115120b030a0602030f010905011d071404050d11040c0504030b040809030a0c092301030b0f10050a0e1506071205 76
    0x700c180e0b0056524415588030751428411112030ba11a4044000b00e440381c4000101307510807403024007900c0e400100091000840109501035071800910305641c50341c0310ba04066003050304541c8144080391000410703c0f45031005400484400c030044c0c5406c8420303a038408200c058040103402210001b0380000790f680320202c5603130148031460340c007804451180c0d21a9a4071400c0340c1c0262001d9150403075540c010442100c1c84e014041c003400d201c002d076070000308816101019401010342034100384078120030603030740b0300d8010001da80040c4402811070103200a182810b80d04040640081030241c1d0030b15040d424124080c0d01114200c0b580080d4110b1030350350341c3c4c40d4500c15030051aa120741c940a40c81c0407502048804210b140039101c044030019034105101d103640102445060100c602201400041002c03500e540d1019a000000138100901a900c0c90514010400c07180c00072a0301c90040c00012441c05515010580710b41241101a452000c5079410481c8501580e0f800601042c1550b846920461181c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 177681735 1250 177680485 177680491
    0x601020d0509011e030e0a0f0b010510020a0609020f09190605041e20040f0f05031204150c05010c03061e0f1a0705121911070b070206070c090506010f08070504050405 73
    0x41740004068585601160421442c081c0a450050030101c1404c2400044103040340144000c44518504140620010792101c1c0c00810240c0007a95440da02c00079500c5281e014451000002c222650514020703131140c2640f02071f00040ca01241c54801c0114443c20584110507000b40c00d4a100c0e00c1d030b8031300098440c0c050401014500343c4030001c482032a00000c1014041d1014100011409500d94108034004540318160741c4518802d038071150090302c1d400c0d940e604580603160007005c81c4092418070036096030000303100407008040390301c0c4c03450800945a041d880b810565448801d0706409031041141e03403440ca400d03401521030300741482004105032003210160704520b002d441c02150601c400e03909c500c5e090a01c0d08140400c2140c000800311000400b010300c1445801507400c01c01c40744481940700c10380d40c0b007580c003da02400c100003840805651700d85003510f0807030b5403141e101c00700d41e5120600140589025545140480d0900d1489100070340103481280c07260b4039599078203040500c0c10b420003000d04006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 177682985 1250 177681735 177681737
    0x40626030d021305090c0403030905040c0201021204062906042d1e06080f0103080a2007080712051c11032a010605010504050907030b030d02060601020d0509011e 71
    0x100701c6884801068000350000522450b16000500e01e843c050104c040c00007025560b40da0f01c10041840025005003407030b81a540c0c00d40c0c0014071200b842d003040e030080c8a540100d80c1107034031500800c0100540c0341c01c40d0415880352460110300c0f59088030f480e65080d9103040080d920580501061040c0c0c40700481d1100e014008442c00d405803414a042030041140c01e0f0030902505041504550700a10403501c40002021245441d4003d0314041c81c08846082060100414820000814064042c49103044070212055511441007038001e0601d0030341e54100c1b0380b080301100e008152000031124075042425074026001006403e8100c101040920301324201c8010750180040f608072680004810030250210280c102c003801c1403003039014803c00b808009a0003003c4140c0c1400010b1101e641d0140903101102c0c1d042c0c6c4c03451500c1d102c00748213401521580c141d40360140f140f0b00d40600280c1d80011080d0003a80c0c01c0e025100205260001143e003803149540d09404103861420740024907002c2e44007031865400b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 177684235 1250 177682985 177682987
    0x612040b090a080a0306080d0c020d02100e0a0909061b020d0305071e02030309070b09030c060d020c0f1509070303080601052206180e043c03110c04062603 68
    0x150f990744000d04d411404070003001907a90902401103010400036650300e20701c1404c0192a100d4980c0c0051124100b4840080c007541441e0f00c2049607d001d18000b100055000b400300362003a072204150b500030107503554113403041ca040c2403030403204902103a080d00700c4c51203a60190020248641c1c0690142602400220400660b031800c0c42c0005202018078280380f22035405999281841d100107454010746801c0302e44080f00410594949a0700000c03060694481a10700341d484003488100c0500078051091040d80a001e20070504803003d802081261a045981c62000800c0d16100030040c4c0c1c420084c00001c012504000100c0c04541c0124040c00713171225203126180c0b47c6807100750340000120007a800940820300b842c00164100c10540c46c1e82000d07141d90b441802032840d09454403440881030304604880c802e10003032115610200e0100c40c00302d0a20b2507485e081c0c030316000d10f0f0040104a40c443c6401080c094011002c2c17030341c41e1034003441c002c0703c04600301c80109241d041e402982101c00c07850356000e20700c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 177685485 1250 177684235 177684253
    0x2003070e030105040c080c0a060503160216080303040201080703050c0a030b040b0d061b0305150f280603050a0b0f100905090c09010221031b07050a110a050612040b09 73
    0xc1c1c240107841c80b9a1007800660300c1c0d117140c66131031b0345401000b00490388210300c030b007600740f11076540841501d0b0f01c0601c0000300c4014202030360040c2d08102940d040d070081c0309507142d004112503030004020360260f4400e903186846135a40110031400c5410503175403c1115182000f00c42c0100f442500035155aa1000b88001500006140052450703a50038100b1110300351600c107000815440c071450505040602d00f024400c0d4603020441e04c030b4100200034030703a03c034032850f41001c0015190300454081480c030001e180a803100356032041101c40155071103091300080c107010000e0702c986214040c40c02201c0c40a401d003540e03601c1c101304000050f000514940f04002a11000146070365802c0d000c6c1e80503110030007180381d658031203800081c1400480100155106c000e03808484010320000100c2e03501c40e61203040068408031000c150f071400e1085141c00f600601c00c1070b1404e024025000400940c181c01180d60600c010380d500180300c5c0600480c00c01810626036074000034089180f1610307040c4c0c4170441200703640c9460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 177686735 1250 177685485 177685489
    0x10b0a0e010912050a06180b0a150506030f1b0a08070f11100204051003090f0f051e0f070f0f05060913060305032101030b04080d0b0405010b0d050a2003070e 69
    0x3645103c41076075694007607044203091154904c5111401500f100c00088443c5581d214002044401b60100800c13503500c0352003a0800b0a54140c580142100900d1150b0301e00b02415031603c41c1c46c081c1c0740c0c2c03200541c0c00c09166025103030a0303044540c2001582c0f203030265070b0780e070040589603030101901c0d00e0f0a100b0350540042886d58180007420705c5011403400140c44034180014030840d104da94110206041c41c040541b40480e481c1d420031140d031544400c030300c4510002458180d090080e84000b036441048080c3e0f81c841c5036040880d1106410210000301c82c1925916807501007940664402c810312906030007428819070402c000200205400075204d0460719540944560031913200368016260303500046003100089903071040f035005170404418150299411034032140450b03180500000e21404000802d200c0c612440e8002c110782401c000d03c10850f075030356001a40001c1c0e001710071220b60107260a0004940003154030425108004c070019800020403040c1052803950b1010f0003c0040c400d01400c251429 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 177687985 1250 177686735 177686759
    0x210030b03010e100c0305010b040f03140f0307060606081e0705070c03170403020a1202060f0a02160612110c0615030f01050c0d05060f010c02010513080708060103050d08010b0a0e0109 81
    0xa01d82c401310008490a00710002070440b00103800c0345111510400041003440c80900842c2c05417a0045160545520107000d10351500800356030f00e414600002c01e0325000d21900e58028001c40c0c140381c0302c9010603a100c440603400c4100101c903206030700a0f00c401250b0654401d5000c3c0142a118411000605440e80c50300c038240c1149441481030040002000d000318200300210000a20790b0103c0c2012042540e40080d049010750000260b511901040354480c50b13100f0401035841c80e402c0400a090725403544001041780342c4008041e581d136030402c7c000203007048000040340c120310100c50141055460f2101c1d140034210f08500c10a60520442c0c480018841003031080600031000103034281d80e1000c24030040800c0d908000c0c40b1074400c40031844840f0080e60498246d056003942460002e80c0c0304402d180c40348c64100c09800c140c00e144a44c51011030b012000140301ca0580380560101d5490005650301160280424040c00030202d00031700000710807600031680349d01c00403c14113100d05c4140c2c4424408500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 177689235 1250 177687985 177688003
    0x3040b04031d0405090610120302060c0906070602030a1d070501140a0512100602120705100e0708010e01050604050912040b0a020c1005130e0c120c040801020c030703030506030a0210030b03010e 85
    0x4a406c17004c01e001c2503c0c5107000000050000120318410105152006903c40d4402007005144103800550600780b039031040c9c2102e40c5281d010000b1901d03810a071030410000c0080d8007050241c1d0851100c4056610000940b000c01c460059469050345068180e8094040c1c0040d459001030040c20b10010707041c6007c3c01c49091103840200c0342510304a243c5031000b0b10740095045140110041048024045000450b24000c6212818004151041211141031502d42c082d400700d00594605040c00c0100b1030103400183c06490215014421034664910164032038080392242c0c04104000c0204120a080078000741c00381c548640156604403a0b4030b004034003007000420461000400004841c40c0c010701161104010380401c0d02c10369070f180742c0f0301c44010f003c0c4204a50800460110310004107030b05424011070300a0b10000d40250344401003495495030b260804c0030210042070400c80010141d08000a400e005541c00401f003002101d4605d100381c00400b4005123954165491302e019a00c0c0c403004003c1c00b44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 177690485 1250 177689235 177689251
    0x90615061805091b131505090411090d1514010f08011506050d0b0a030c0f050a0e060f0108060414190c0302031b090607150203190203040b04031d0405 66
    0x18001c0e007100e000441010a9080540300311010402c0c0008110301694141c842c0c1c00240c0c010781c3d500c5a40446680c20350441c1e004509075524a11016444d0b5845009418040002e94007400020803020180460b4060419000d401c00041024200401c0c800040c0c854000b802c9040050a600007201010000c14260807040011001c04010400784100340b041c0480001e1003641a581c1500f001070042045c414071f0002c800f441d8480b800c544c1c85541c0d101414004607402103940030150340d82c10326026201d42a00c00d081c0f03d83c1200300c000a41140c1a1022486440010a15903c044a00c00103503030340d050151403190007556071103802c440300c80142c2301c690050b90121443c46a21610802e0403003501c0384400c031802098014402e00441c181481e01e012030076541e840000b40c44d8007842c03002c6200b50050f010003500118001154400184a540c0118013803950404000c10342c95020750361034140e01c01520002c10b60320309140002c011901c9902d685e035400e0200d4220f41d10782d925000000d020303654241c800f00c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 177691735 1250 177690485 177690497
    0xc041203020307030807051602010f110708010f0b18130f1202372306040305070c0e040f02090c0408031b06070807020d050903100c0c030207050a05060403030309061506 74
    0x501803503045800c5c20340c000c070f00d854082d1802e00c0e0b04a10103851000c048000b070610181d52440308045000c2d00200304411045d50071104469514484035003e0018103481040f081d1401c1e1651034036080204a83d00c0002d046044040307580c803881403c0b428180c4000382521500ca01e0034100700052440c0310500219010b582c01000300441900710f03214444c64802040181422002e01d20241740c0c220100314400d00e40003561120800841e0740041030101880c550070506014400c1008109604900170300440c6004414086c0b016480740c905e040c0e0385070140e070040d0000011010040041c580101c0da00d511001075580c480c2131030b40d11010f061441d0861a040c1c02c1030072104450301404074040008582c0000207250048040c2001403003e500d0f00c080000207000c00000103080100c40c0c404025444241d030159008025141c4020001855808100d03400c50040c040e44100203417034900200e00d072058840c02041180f419155681c240e00429800104540403911140d0b00142070720b103501403030002d003656110700c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 177692985 1250 177691735 177691747
    0xb01090b01091401020a0f020a0e0c070b070302120a0207020f1e0418080306210a08040303171501050705010b0d060603120f02060601030e0f06010612060b070210080c0412030203 78
    0x740000a6503040300070448683d80507491540e900040f41c1d800f090304420b0b0000f1140150020600c85c4002d60030511007003d1120500188198041c01491081d015100c80411611550003c90903403054000d000f0500074110041506d41505600030040244020607400c254540c50010501e40790642035801c0ca40448214000094201405907161150300400d03000c0241d00c1940e0744028502016001d24015013500d04612404002c81c07001220216420048451110441c40e083d8140d40c041d02040700014512845180485400026580522742e540400c0008980103401145c036500a950295550b42d2103030503140c901e44402503c0381841d401544042049400e50800303005c810180c1ca4810104080d00b1300752241d00340e02103411500b24809203004119241809545454801203401c54150380c0210000040d00d42d41100b040d02c0c400b10003040034001c0f00d68035440410580503200700079400c024035510306200103106030201c0c3c0c0e21400c01e07161182026110b00c8801007a80900c042180903900020345 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 177694235 1250 177692985 177692987
    0x6180114090d0e0402070b07081b040b0306100f120e03091207060305070903171305090a0f0b0f2b0f060507020c0f0303090d03030f0e060f070c030912030c0b01090b01 73
    0x351552810099505606e8040d06c0d680c0d001c503025005100b1020421401d021601c04c0e51000c11040c4201c40e02801c2c0c0703803900d4a402d4014126030050301d07218412410304024604d083e000b0320402860080b00d84800c0c23000314004681c04007074880d04c1880951800200884a074a64640060420a0080c41c0c0241a010f050030700190172103130090841418012010001c100080c52000f603001c28400f050421911850a00c800c40c1107082d460700701561082c0d20b0000c100c0c05072025440303491000e034012030522401c4230348024841c4048003600800d03004840d0343c0e1a0b0a0180710740300c2e0301842c4074424555043e0080140c0f505584645021003c4401944502c20301c00d04a504022007110004100d0b0440c0b8091030600c0020361701d01c42d004115004141480001c41494001e030301402d1000c1d04164107010f51b080884607243c441408852015080300950040341046119002082e848d44e4161203802c02e413400d10100500025043c201102040000c1490b800002c1030062814020440c0c0c0358041a10488140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177695485 1250 177694235 177694247
    0x921091502010b03061506070b040308040213050c0a08040c0302030a03021b09010501051206150c1f0c08010509040804080703060608010e0f0d0f14040303080702160806180114090d 79
    0x4400c41160f04020071100d07295800306445030004041c80000d001c059400000c241c03076004010001d056034008008100525401160b02485180b08a42103a03101d4500d00c092411038806a40314813030300c1c07024000c6442c41401414101d4003e401107049807040303662a80000d1600440300d40071030040c0c000500b46400441260009a1181d604543c54001e542c140b4000a080c2e001d4040808840404500412000c1d1030740b508003080003140c00c5c9800c5d9542900c0e1000c558680c1c2d1854141d110418010711259003502034130800199400725640c20400f0307403802c02008151280034106580130ba104000004500504000c3c0d400110f01c23030f010100b141c0f0b1401401d942100c140968030002508502402611141c0100c0d03011621052400e100f0403115860f201142c0003034040700260200c080010b800700500d9041180c41d8407a4125508486c01c03461038441c0e07110240300512980c0c0290f07014001240c40c0011911818000a81c07800002568074100202e02c103481a040c3c078550040d0700000c803075060300359201c1c1d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 177696735 1250 177695485 177695519
    0x30c030d0207120c020306060103020d020d0f0e0f01090f02101407050604140a0f15020906130f122103020d02270301060308030a052206060f0e09030904092109 70
    0x105002ca601d180c1c07500402c7e00e40d2002080c0b20704141c0d0008401c0f841d54100e84c1650100c1c803151314100910510a00c4110081c00c1e0350496400b280325001840043e49814011450210b5202858070f00c0c00027554244070100081c00c0c00041400424803038112821140c00142021501440045c4a90304050074140080240100500050f4010905450214040318080780c0815802031802c0109122005414024015002110360260b80043c0c081d081d204013058200980d041c2180c05c1c07041070b50f1445818500300b00243d0040002842b10342e90400b184040f01d2808100c6507034200503140220000102049a004640c0c42d440300c5941044000c007a01f2481001d01540d0081d0300030040681142c469000c180001484032200b03588450010391884407460010b0004040e45450031642440c61502c0d001600542c06050a600280c1d200040d40a001381007081c011041e02c0080c40c98402280c0510001d010b081d02c0c1500d000c210b00548a01070841014021850b880d169039115685080c00076400d03030b8551130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 177697841 1106 177696735 177696737
    0x40b060c061008030901120b0402040504020f0a02071a07140a120f030b0d031b0c0e01120b06040c0905090a0e010513050d230c030c030d020712 63
    0x507074940282c0c8042001c58078075450341c4803d6601d00030030702c0450028414070700390354002186500640c164180030700058907007910b401c00704013030380d1000c0c840b0079004c1c03000030791014150ba0620540b8040d0818444803c0c1960244502c401103000d440c0f0041c00c11111221500c5560000300803041181d80e11680c3c3d0840d6009031200600f03040140000600840e0032301c507140007c2d14240724910720f035640c180c503800101048050105090134018004640e0030f0048140406c190503046040c034020280c2c03041069191071180780c04c02c1100400760030580039905208011640c00d40001050080e50b00c142c0e296501952005d55401c0a070007014800b10a42d4a840203001006a0402542604074056400c0725001190207004542451149100e03543d100c070000c4075441c10700e4070711009003042c402d80402c4a00380b00c4d144244900310b90262142c50241540014460104000065101800152 = true := by decide +kernel

theorem cover : BRFrame.Cov 177517985 177697841 := by
  have h0 := BRFrame.cov_init 177517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 177517985 ≤ n) (h2 : n < 177697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
