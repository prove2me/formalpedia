-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:51.380141+00:00
-- url     : https://prove2.me/submissions/c581a7fa-ef05-4b34-8e74-e2e18134d2bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 574640287 ≤ n < 574820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 574641537 1250 574640287 574640293
    0x206040b070507050a03021c060e12040e0c0322050c100c03090b030603250f06090f1a0f0313060c091412030910030b090112031209050c10030608 64
    0x40e18014400c0104801030103407040d00c14064542c030402031101c110b8480079501c40e2034003d0760460705500c402c028440901c01c240c0003580111380000b0300e050990300c1401840101020508002002d801000540d01044100d8194910318220074010300146e84810314905003420541c1c200704001c2c2c10095100a900000c0289514001c0c0d2305005150b0003003510f04034000f80c1c50101c001115564402541e00030000200035050915048102d0b0a89009040f03546901c100d0003200020b4019034640b12102030001070791043c0c5440e081820190041071107a00614042c0c2052040a02810b9503600365440c0c0b40c42101c45541c0ea88500039088a6142c0c404009403065103000300b1000b083c1d4010062008880d0a425458042039400d01004400a86415490035542040140c0016890444c50710780040c407281c140082d01803000c0c4040b030003440098101c8150000300007103500606802c8402c4101800704840f0900075a015550b805442e68204480c1e103002ea1580125040000e009e0f42012020f00720003422 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 574642787 1250 574641537 574641539
    0xa0e070b0f0c03180f090103120507110909010501030b0c03070c170d110d0e030f0306090705040306151809110114070b100e130c0509060a21200901030b0a09020604 72
    0x4151300c1c08101002c1c09100e100c9940d22142d03179040c9418014100d0ba0004403151601404e510701340c802d944022005c544040b0410f07800400c03603031244103d41c018a040000015a981540350048074440060701c08046034409208004419038000c1d001106c550b070001110000d48000c5d011010300e8010b020801403203d00f8100c01100048986025020700502d81d0310620501c124011055200d1040c80001440c0e030a0800c00200d8908007200b06580019640c5030170f9141c00d41c0c0c1c1c0c44060403559920001c01c9000c040b95800c00404102c48030b415403602d01c000003000610103c2e82c0d400c0e40c6409092003541404004000d91540840071006e0390009508132807089118035000582c124284440e0149007081304520300420324030100c3c1080c14210691228043c004107041c0010011481e000074551680310361a02000300c4d090300401c0040c02e07001d020004c00600503100b8640881e04103100000e481c2d07003080150b142c00741540d82190150440340c00000c41121a1201c15016000e8820745070069001140068 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 574644037 1250 574642787 574642807
    0x90402070609110d030c06110c030c0106090605180a0b06251b12150f0c1805090c120a0e03040e0f0901020f0702120f01150504050a0e070b0f0c03 64
    0x4012581d83c85490b04146002d0140100070390800d6511028001804040c01e980010300c071036100c401106021310055042165400d0030614507030000c50507030841c0c0d454540401295005004400240c0011074a8601c2e030703080101c080c140c084000b03003503c001a4498011a0305134656000b05c6404500881e60140054510400340b809100c6208084804010342c842444000a05203d00815209000501c89040090780c03030300580160300d00e10b10615241c0d00d020080c200b8846101d01400e209030390f1109940000113961100c1c10400c40d170f0145025810440801c0360283c0600125040c81814140406c400d842d0b00e6842402802100304000d0381d40f10002d004100d4483c40d14a8500c112202e011003403071a03882d035984900341e00840d02c924199501c284005401890440032503139544018078219841c3c5618a00a00d081d1002e8210013024a5214001480701d803c0501903254400c00225084c040040918422666003000344140a071041d40415a584c0c00c6000d202103d0310310b000740d0100e075241e44000d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 574645287 1250 574644037 574644041
    0x608030a110f010501050f120c06030a140a09020109170f0a030201020405190f0608060d0b01180b01030b1f05070b0c09100c030806090a09020915040c11210904020706 73
    0x16500a041d8899000802011841400f0b130b07078183c41c00a03007c500d5400c0f502e001d101c01742e2142d422042050280300b01d04040b40d01c0340409144034690081c6d001c41c01c950901d0084504800203817081a07441d06000e0200301507608a1489800c807200082e00361400304560149600300036000d40000c034140103440400084c541d054014105841040b00c26507465041c140340111f1214451242640454440404004060195400b00d80c88500a0244d098444050b034564194400036000040c1d0000f00b200464015201485401e60707015082c00e04100145204000400e07440c21824006c060f00880300c0090a031520170825644a154400c0076074401d820a07040ca08080c0d004000030754002c103030584952261070301c2001d4042c0c0301d54040e20b40c44242d80b9003000f400003401008000d41d11403034840c0a00c000588900d03c206200b0701080e103410020000040030070081d52030204454041200c1144048844413000c140e5416500088503010384503c20441c41700418007402c0100b5074003034404900001482181c0e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 574646537 1250 574645287 574645307
    0x7090e09031633051e101e08030c01050f130b13020609030604051f05041109041416050405061518031509030901140406090302010c05010908032509050d030e040608030a 74
    0x62020795181c8240301c03a541c40b1700b00c003c44550341c01c3c0f44080002c00c0481c141d880c030303201800c50041c50300d0001030312248806d16550140c0c0482d00960b5448003004140c0e0804581c00e600b01d4001c8800301c18002076a11482e0300e0710005000c10003104c030344003c2c2d01c08540ea00401c03141d080c03030040d054845c1490135051035501c4200780321000e01d82003007000d40300544441510501c1d01c216840403030440325141820a00c050030000810488061031002c01e01c1044c0380701013040e140c00c210041e164050b0241414203020680e1409000305024500c100c0c080c0707080903014016103000c51142140d040b50203020b4400280303010b51111754503c86950756014801001c40c040f0003808540c0702070700c0d0000c2d4055400301103902407040b40304140001e80116824401503100d600701700700e03a50140002140c07951994944402c1ca5000b40c2d03c441c01600940b203464800221003a40d6134440303a440c2008094545020003064411602803401010000d411300320a100707960700d602000c040c1810320304490301c400d181040540280c0310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 574647787 1250 574646537 574646551
    0x280f0e0106020d080a1a06130911040f03080a0306031502030a14010509010501140c01051003050d020303011a07050f3c3307090e0903163305 62
    0x454004034041d400011002078083c280d6450700280d5803502d1101d4010010401c50000700c030505201b1a80507560702000c0c018070302401e0390400e40e0f0b91526150740308444410b002c0036401102070204002c4102100e4010045940004499607140c1803001d040b4020720f055040103128587d840560003000342c3c2c81e80594810101c0f124104548071581c030740c264402409110789039111001c0030050140794030900b552410741440100701800c14044126882c25260111801101c0200b0848200140241040095840001400990320310350404400c01015810108070605280c0e00140b100104401040f201c5469204402610303a401c1e09180d22803140c0b00003001c1405a101d10141d0341c1245040b00d46854120700e003410082c00d42d100400e800411626420316018007180d10304c9000c0c030780c42f9007040c1038611401c01c80c5e9030010b80904114071003c2d901d00103010741130315900601a81036081d040c1c0501d4040da5030401c030705003580b4042030300036443c82002c00c42401ea101c2c0f681c030940c1a1011650822401000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 574649037 1250 574647787 574647809
    0x30c03030e010e0f1c0c091b08040503090904113f03030615120f0115110303060111070b0d0506090109020903120a1701080a1202030a0905280f 63
    0x24a0011500f9528018589600108000343c1c0041032411707a039201401281100101c40c000301686503854440c61a91105503665241c60301140c040799a8641090001c000c0e042002c21030078592075190380d03130040103501070040d0341000220782800402c10b003112132000010709200150001c0519282412005181f00900504503440b10301290350881c03d0b034841500b4080154107690f10401001100c0d0515044155110420005807118820340c1f2034144c80b600c10503028a000394034002d0a648145402c41c080c800700304403114200041a0080300312a0000303400d1810007204503200000d6820801c003548180013108000466681e810402c0e0482881307030344212140c0982d03a0341c0324910700582c441c07041441e80c15048110144c6082e180140905049401031400410350700c1c81258400106200303030401c40541c0d02101c1150204403042002440c003510b1072002e9410401940c10141406089006d200e105010190020286003101e800300e265581004d070100d41016a21003a10810640038080c0c502105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 574650287 1250 574649037 574649057
    0xe090c0a0b0c0c0105030a0e0313030b130f0b0603070803131a0a021908090405011805090703023a08040314120702041805060408042c151306030c0303 66
    0x1076094040e189484510702c040c00c034501c440001115141c1c00281100c890035525010740c00112001c0018102d0f00c08480c088090341030950030a841e500340010100150fa000308100740c0009031002c84030302142c0d54829107100080d1500000070b0300b402040d07003010038184030108900c0c201001c083c8038031048074807a210701108041da88902ca40d440c0720302d0b49004050380c005100ca6415104e031030540407900c1e004001c86428080c21b500018291102a802600c615140064502003100b4a1283c1360704407811000034010300f03103598041064914803c1900700d071202c0c1442c0341020f0aa02d9482048509a456910703001b00e42140390640007a041408151031490079600710880040380001c050780251200e41100341011403d908000c0949a060496402c0451300c4080200040040002d140100d20440c00c0301d0b00c850a1880c0d5032030104114201e69080c01003a40c0c182102484030300d10a4029150304120302c1a00403000100d24070803840d103485210180390040020a004504000b0b0007074034030a603035885801c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 574651537 1250 574650287 574650299
    0x9020a03090b0702071815060f110114060a0504051306050c07050703080706050705130b160218150103060e06040b0d0210110601051f0f02070b160501050f1006180e090c0a 75
    0xb00c0401d0189107c41261003c140405030103026650401034142c40c0106103215100c080c50300703503100d10951005200d040c90601c0510f1078000380c0000034010650741084a4a8818a200c0ca44006603202030401642c440114a04000c00c00480d4a401c1c0c000080719985079891a00610691110300152000c42c540300110f90b90798451802c407200d071101c05102d00071041c20322002c20078550210151990b142070305181d040060b00c1d403190000e84030384804240c0c445ca142c07070010312003d42010311440b4105884c08070140300e0b80311094000c2c1d401841c01e8400043e0000000701103501403106c0d400c007961001c50031030b94900c4503522810750024100c0d030304180c8200f640e0311310130312218115425124400c189660100b8900704c1c8219014a810a001d104444400fa6201038071003043d480700a2041c40b0300455000401842000d000f02600480c0313903d098402031400c40d413480f5605510b0b015050800980344200c0003090107010442c0080c1611030b820903224202414150b80d03450b080f18159004082240d800120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 574652787 1250 574651537 574651541
    0x510090302030a140a06050106020102030907080d1215030807050303090f0d170403090906060302070c140619140a0e010807020a0302030f3f011a0409020a03090b07020718 75
    0x200c81d030141c01002c4001c0d450740c808100c802102a525807a100d294030003004a525402498002e1180f5000141d0341d04041c01c80c18180b00e81074021100c81e82c44881103070002540001c0980f03070b2010701d00c800070f111811103102503035903a425880940594000308411042c088040700441c0101015021907802d0b1a201218549503401441c00d10040b580c942012003c01c5512007426600030700c07074500303a0919502d0304040c000700c40c4240c00103000664045044400c020052000c2c0006d0003503440300000b028074007070000c1d08503c00d40458207980006d100500c507106008030302d00c0d000a058507d2050b214800010300502c010800c0c040075001071a0040481c86a80c00440c1d008043ca4241d40503605e01600038001402a80c840344090000314428400595404d000c038503640e40348160704c0c000751640841c0350032040159506820551000c0b50100000c0341d0180c001d4101d8044541110025032240303030a84007900204510440503010231400010000c200782d001c55810180e5005140c4403081141059501e02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 574654037 1250 574652787 574652789
    0x908060603071208072103200307050f04030b0a0524101119060e070b0a090509040f0615032018060d051006060e04090b0412050910020304051009 64
    0x40c01d900070940612003004403c020f8a03140380203880240c0341010a99070030340003071410440c058030207501c0e000d800030050741409071b616100040b84207103194400e1070b42242c00c1403002030701c050140311002450202d508071047c190380c0150b030410070750f813294900212030102404080b44c1200c2c10000c04040080c0081e4525070089500318080c01090344501c886509070f8000c1030301800004140710f141c0e180621032010645142e0090b214580109204490464103403030301c0790580190588100c00c0c8043c00021740e11190403030458200b25941000d07625a4202601301c1c404011000d40350500380555851000e441803201070460340b14452001031481d031035071052110080d100200354800100a56501c40000c01201143c0200d00200038842c02c900f81d940e000e103040c5074100240c55a43d16034a00300312450b003204d040451b1072015a800d100010301d40e9504411403e004000500c041e0b4801c0c48001c640380700780c00f99007036250b02030a02c0007003d20546001c0e681307030081c0c403070503125260706c1e0780c101886031140300100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 574655287 1250 574654037 574654039
    0x1e100c02030702040b06040906170d0e01022a0607080901080702060613090c08030310170d20161d011a09010c03030b0907030e3a1404090c09080606 65
    0x1030074142d2a80c02c0101610820303c8180d4003840501021520503030f20302c80d0b10001d1001c0301322907400329010310050742481c01c0f40c01210140f0841501c2c0325056600030424a9541038210380d400340c028203035000100040c80541074140c0000c1c021403002c042003141c0740100000b50007600e400480c1d60b58048100d80d0740600b04d460b81e8001000c19171000c1c021351503411655031644210610244030f602c0b08000ca20303540046582000503005900c3c10480e44074403c811080e03003000d0354081d00366026242405040e0f0b200403507203100e664000d03900840314100107101514032070900d03102200440b43d442e07521022030b8051407104484455020300001d5030361600d10749801c03003a8000c0d4529003412041170040d581e60b08019419814141c0702d00c2222030b5540c0c0c50040c1c9205030f100da10001248422201c0740b03854044030981c2c0e00a8040ba00006c0c0703194950702001144008078280c01c40440072200001107401c2902401000c101000201d000b15070b01c00030f03030030044517503c159642c0304086a94421030399481100303484403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 574656537 1250 574655287 574655293
    0x1201052232071b030c060c0507150c0e090a1409010621051005060d0b011d0a0504051c02160305030315010c0b0f06040209030d02061807050f0904030903051e100c02 72
    0x550b000f0701c41103071810140d4003e041205000030207031282c506a8070050941d100080000130210100800a4004140005050410440c1610100001d4440048404854031400c0c90310b000602010040d0080707010907030b450813400c0c2c903410281002070207443d1500811811940060300c4000c0f00090b040c1c05900e90343c0010040200203510000700c1c0080c000a0030168011000c1280500402c01b003100143c000d00c40d01d0041d04401545214036040c109001c1c2c8042d40e06030801040c0700c042000092140d02403000038565140b820401c40d0305030728042001800c0801404100e50000c10b000e4040040c500c02c6015203d0b240b000c0391198011584403140c0c000084c040c0b010003010a800d222617804056020030054001490084080006458091421071080041c0d00c00001c120f640c1003503048444985036100e0041a545082500007607110b103d8809440c01005020001003d05104a030004000c40d00041600c0510789420f20030364201400700440b54a0703102d80c005105080d03480e4407410001c6007266000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 574657787 1250 574656537 574656557
    0xe071a0f13150e010206060603060d15240e0114090408090d02151c020c030702010e030c06040303020610060f08010603020307020a17070605060402120105223207 71
    0x240440da40c0001c110784408032200e92022480c410b0803921407a03100c00d680c60304241c18620b10700080ca010700041826001361414070500043e6103503070340900e0b009030b0b00c2005d048524100311500c40c01002401d02903551810748505070004004402c8020050b1440e50150714426a25100b0256054801f181641e402940100001d0003150000000c0c1c040000010310395890a07040e0340008403140c0c0c403000c5141100b8000550807030410210b146540600b910b440c1d0075401d1950940509440c1d01540b1400ba0501801c10800a01984c0601503600a920010f181c20b89854890400a60382c3c0c80c1143c1c0d085080c0390b1420041109402410403420184daa50b4602c03c4684c04e18008801940002e4016415403282652000c002982481900c01040c1428800c9031901d030700303007000000c5c0c42c40a000f0743d000b2441040640d948464005101d0305403001541c9212a1501402403c036480d0468140104803c0c079100c81d6406c02404652628542d0030360380408220020144501c1d5800c1074107807055404240b0030310b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 574659037 1250 574657787 574657807
    0x3309060b0306031203070201060b0f030a0c020c1c0c0f030b040510090c060309030e0a0e1512060a0b120703050c040506090f04120c060f1b0908030306210a060e071a 72
    0x20045a11070464400420340360b544ac09286802c1c2c0241035400d000700001310800c101e00c60184180c0c480700e100fa00c020801a0480e07000300307040042901d2034040b590354a8041b0f106211282ca401c0f0024a00e104460f11400e80c0c90421404c0b0103010b40d4110f442c4e008518404c000360300d66005019a4a810001c02002940b6001c403d80090603600703c01c5040c098401e0a1100746d0f501c0c0070074200180907494900c102850041e5180b00000740c0a04898421880d07a000f40010000004a16620054070440080c602c14a200080c074040488060340286225414002c01040720209800014010907035040c417107904c030701080104c0814200c03690340460803024001404150340144010340d054440c28450000078260303c80e0010388200c614000440e5071a000000e0b01c0e503440d240d1b10074544c0107901e00303400c040e8103000400b5140e21002d004e081c4110341c0d400483c860b008034519001c4460003480101c072181034552400c030b40580b45c440507401c85406520f8001410a402c0848030490b890304904903858104848 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 574660287 1250 574659037 574659073
    0x1060e0c09100c2301051f03080a09050a090b0906010503060609130f020c01061a0a12050a110705012a090b030907050907050c1006060c02043309060b030603 69
    0x4001e8804101d00c810402c40070138940c180c21130ba4550403000c0078100c42403800300c0b0750940d000500400644c540311040d080d03100e0341188051003540e074805615580d841403010103d0381201b00ba045181d0001c14104005003120040e030142c800803105070342404490303440074010340300f07400126142c68102c1001c008419243c1340c0341c111103041c60300c2c170400080d0601d4031007050320890300b100c560744800c4e81d5560710611000400907010790800d06c6640c4064075105060344010444015222f4040b009504d440109500c12040c0e000501201c000460060301c0d40b0260800354040c1090b00f51000349610340310b0300300c46442004102001e54880c5900c50301900342ca01824007485500080c100c1c51980180c2002040698410040c28082d00700c07031b5102ca1300c540682c0505814003400c02d0304013144525008081105c10b8001c2c2101820302d804890000c2c0c00c0c1e01008170141180320038840d4210f00e054280004548041000c03a03481a02c000840412402e5103c92800354a0310041e1070381c5070b05502801b90780032024a06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 574661537 1250 574660287 574660309
    0x50a0c0f06020310050102070e0c0702241c050a0b031b010309051006060807030902010e010c03180f170304050604090b15030a1b081b2d040801060e0c09 67
    0x500c000300000400e070386512080307800940c1c0c81e82c50a80c10b01410859503904020b0303003003e0801c92000307003114144480f000e06144240d44000f801001c0d42800080030006260040c260001401c0d03240e692015441042043d60040e185011209072070100402c03c08901c511a45401c070b0406801459440b000d401e038005680c5600b402281010f40315040308000420920001c86c0488080708080389207420003001501e4400c004205400b007503d028900e20140c0e03440115402c90080a023040c0003201a1400c0448240c07101c040351301042c06210b0300003d03205500044100480b01a40c40701158001c109400c20b40b28803e500c1020360003d4140010700012605501000c02c4002c0100707200705029446640c00c034070340c20449101240c00d5449601114004a10852600c0616145082c0e05640741410005204a81002036641504c4001c1810050002c070500038001039081581e001c12049000062030340710b9403080c00740704019420400e000032954081e101040c001d1180c0e44846052800303440a01140311a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 574662787 1250 574661537 574661543
    0xc011e050c3606120105090c120720060411090a02120a0f06050307030302010204060e0402090303030f151c14010e120c0c040204140910060210150512031305010e01050a0c 75
    0x1e014880b8141e0b941d404014100303800c0030f9245440e00e42c5082c00300b105040005103290348500e0100400030540b0034910300180d0040e42424204c0940c0100702600f10b40010712914260351b8495003081c0824824401410340f4506401c8403002e06641c3d42200c103201341c2c06802140046845a0000309030002ea981c1c000070b100350544c1000058855944000900d1301410f54029400340c0d500003800d000780da0340000014034a8106503825441c3c600381c02e01080e0340c2c0c400144000c4401c03000b0004108940c110300b151102004005216000e000c0d9144042610310b10240c0d03044400710032071100b0f014410010b0003050317641d0726458090b0562150690300e42c4030a600c010700600240c01034503e844060741d1684090005080d0440550300102045000d118000901810300070040a8066040010960014108500c0144c030100400e2604506410341520040781c0c200c643c8c0003a20b1a00c0c241c400e000080a00f89c01c000243e82c4038811135540d401915550b002c1c0c07403e03a0005404120024a840c080d011914950344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 574664037 1250 574662787 574662877
    0x1050c0a1e060615021c17040219090608010506091312090801050109090201020d02070f090209030a080a0315061707050f2208160b04050d0302030c011e050c 69
    0x6a41e42d50000b110000d400011850310320b4444914415070401001002d0703204091030209902e076083c00580701f080407100f0319a81c064940001402c540300c01003091204422070310f1690b001915001d00700050b0a0500680407250701c1c0030001032603417030f0400010303002d215060004010501152038001d00c6444400b010701c00c1c45002c00700040c0580702481018001c15440d1000210068148002030801071904c42201c1158031250701800910030b2054610304a40a01a0041c0c1e600441000f10382040c0d04c20300040d09211002c80d148103160b406421420311002003d182c1f8400640316001968562081905004103406036400652024015002849001c0521019505010800c1011450020021100311380d07078184240400072104108402c00c19000c0341d44001c01c60700c1c18450640241d008a104080c40b4403844031b20300c4145070007841220000041c0d103000703004121042c1910100304c04010b40f0a14003910f0030740000c08131030700d08042d6925020501340902d00c800303040e03401c042d20b02007186586000320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 574665287 1250 574664037 574664093
    0x180b1b0f030a180813030c050603041a0603010f020f07031709060a02070c032003070b04180b0a0b0a1715010f2304060305010e0604090807030503090c04050f06040b01050c0a 76
    0x1070b01c1c4c00c000c0c0c003038509a54400e02c403203821480c010390300075190342c0700a004600500030302c0f0000da030b00003e01d000400107100c56400340da11000040d000d84032102c80c0242e040e10024000c06c8010f903010040c800e06010392210703c00310010311550b90030200304a56503601c0d50852004030300d0f00340c843c0d00180039281c0a001e034031449903180d8a40c840d201e248441c42900b016520344030720103182814002c000091030051000303400c2c246408401c90b4100140c82d6800180382e07881c040742141b40d8850204a01905940380540e458154040740501203144a0040039841d8005900107015003c50150342e012481043e924501103420720941540d000c24040c0384854600440d800680c4c514910320037500061441d65004038407540f4041c84140106405084580117600b0050000040794062045904503681441d14564a030384171b80c1c055052690300900c41d0b5000c1e04040a001c08004190051030080303a04940070403040e8003000055405120700c031250030103034102c0124240898120100e0320071141d01c00703081760165 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 574666537 1250 574665287 574665293
    0xc040e0702010212060402030702070501050c031e0418113705070c080a020108010e070509040615110d080a0f020403120513060e01080c030604180b1b0f030a18 70
    0x1820044600d840141e6000c03407810329609504000941203413068608520350b04050704001d4a5001034001d01c0c0c1071240010314401011802c1049035055080c0400e80103000320035448405095002c0d1240382880400c0c01840380c0a00c40920591600d8203080708000c2c90050b07641e4100c02840308800360f00910440c0d0103542608a00c500590351014005c5aa41d241e071007060b40b0b04500d117030340d580d00515981d174050106480180d800c00314007415602103a965020644e103100b0103ca07548640a41c0303070b811508107040020003410700146181c00b0b241c584c4a0300700300000c01814590b40c0e81e009005000040f41080400e12080140d03101007424660808098030f000d4a80e141c01080b4801c00031118001000000d101a21542e41e8a42c02c015100c1c0e4030f420483c915800300000c2034903901403d01c03107030b524000010a00ba950340b54800109a4440403134001000c01505010b80c1c1032400300d0f02c0c54010b40100590540d0b04290400311010080307484061030454494016000051402c000007a01050300d00e03e0304004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 574667787 1250 574666537 574666559
    0x50f0609012003010e010303030209120f0304061202131401020c030102070804031a0403121d1606080907210501240f050f01020d0e131109210d080c04 66
    0x46a031a40e0000310300300c000780340003076100c0b250b150b200c80b5103107414070040c8070100d03002c2010340c110ba0301031a0140c3c44840a0000440700c0724101c040318128414500d00002d00074010018008480f0a9181c070036080385d0300c4069405a21560720488043c00003410188040b40c000c2605001c881d4062044500c0a01e07544046400c81e400000300351031181c0e01150030001c020305503e202c0c43c940f129094940e40e034103050f078028007440019810f580410b0703114041850500e0107030b451100b0f032000300300c110340c2c04c07a1460118000061441c00f92100244015000a420758030025024080f50048500d440d040201d20b0440da9010103081c408903a155201c800925811712031020b032950124000c21460290303071074000040ea00308059809a8020001c084448215a03000300302c2e00803a08060815088051680000408044040c0034900003a8a02001c9509c4c082c02c02000c0e00c1c40c90401da404940c032110f5010400e41c00f86100c0d0550000398403040c601c616183c8a1b0810a0704040181c1265040c146c544c661686 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 574669037 1250 574667787 574667791
    0xc04270f02131502010e03041205120316080a06080c0904080921100618050403020a080c0d082a1818090c040e030d0e0c04090f02130e0c0d050f06 64
    0x54a2a10b005090000c039a42ca498200003504500080001e200d01c03d910980721301451281801e12070a1024650600005107d070034440744180c124a03540303280c174200040154444440490002d055070300050a118024801c00060762009801040c51001700c2d81040302607030700204101c0d80e040e02442589440d031240200b080c00001640a02181c513140c01c0d030440d140c072005044c40e01c00f00c2d041c6001041028050001c6010784542d820011030246c4c0c1e241800d0346050b20700840206030b0321000a290080c00e00100b0080b10b420003554444440351104580b407035180b0b42d4541030781003c80700c0b400741c01041014807000385001350b803120b14680c605d50141c002078650421150689004680a410809511810f000c1e40c840c04104690800203040d00d052030590707a000c1c090013401e08a40e9200c0010b5202000c03c80050345610080c001c1c80710105520b8038400c07041071840c04074051051019000d0f18550b80d400b1f8401c0c8244610006c0522803a58002c1042c1035000c420142e501740925019001d80350700501040d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 574670287 1250 574669037 574669057
    0x90504080a02150606071707170415031a06030603120309012c1b0a0f080309011704030e042c010b010905060903100207110a1203080c04270f02 63
    0x39121404800c02034240240381d043e12150400003030822115560b8007081d20307a041d40000081c80c40c250558590500d81c810b0b0140a4074000702000080041190103009200b900c49511a69082d0480300000b40c0554000d84443e19203075514802c00030340d9017041c3c009558000b00040444075088807507011a00c1d103038800d0392003a095035151103151007035000015100104815021403000a02e0325002d0003a06d0748211030400301621700709503844886560340b0780c20394041e040460b10f00840c25603400c8100d41d01d9010400300c60104200c81c00300841079991000e018499034040d181c0c89070788841031080200501c1041180c0c0843c404c014030300e080f0392058902c802c686000c44400064850550b05c005844001c00707520041c410320082001e1803450b00c020800b00004d2034007100150300c0d0b00044c90311440080c0020112900102c2c1c524000401041e10322010b01c0490081c1c490b6001600c0b03034001100c0c141309500510000c100c6101c404010803a10403110b076604000c400340010404200200e14050340d1001d2000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 574671537 1250 574670287 574670303
    0x90703080d02070c15020c0d06110a030b040b0d020d1502190e01030506030303190e0102041205031e040e130f0506150316030314030c040504060f0603050a0e060c090307090504 77
    0x4404102d1074400e1680034100201c0c3d03401c444075011071700070740d116508542c99020f0106083c042041005c0b0340c04c101120742c40a10f40703548513140f640b002801409030402d0644924149101e0541606005c480e10b80410b4014091821980c0d203600c1d000042103500203c3d000c510383c00c00a102d9248403001c0301d400d406006640b800360462280c400101519809882c191081e0020010b20180c0454a00804a01020128082044540c01c80118024080c40d0700000882c40f49081d08010044084024905506071602c1c0155480360b118100055020718010f400c0600040303c0899406218284409001885180c107006c2c141c420350381d914144613080d01c03001c0104241440da50120319091018a904d200c00c0d102c0b442d8841e243d514010010000744c0a844004030002012403c5a0050400c65005e0b05000e4003d0000369510f400d1110005603034850380001a10304008a200b03001103009035048400c1c0080140701a40301c019241c2015800421070300e916100340c0100061851840c00b6440c403c038064403038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 574672787 1250 574671537 574671547
    0x172703092d03011b0309020a0503030c0601030c06030515010c02130609020c071a031605040e040308060f06090d110a080a050f0f030a0903080906120a0509120703020c0603090703080d02 81
    0x11207a0382486007585144030f039041c580300440c2509040d100360030581403840c01056188813400882c00300707810758002da605130000103844940641c000420328100c038801e5903410121a92000e00f00c0c12101e054800c00b1840540684000166104503209050540018145501c1e102c500a10780201e0b0503c0d445542055004107204a00d504140000340c001c02c0d4020040ca44c684007030b100081a4840109160710512104003a0490b841c410010780b006014000c074001480d0905050140c40300c03904070380151080841d0381c00b0003641c0c00c000f01075440f04403000c1c0c001e019481d110303030b0b840c090081803042007500010f054400003000141007180c1806640600082e01c034130540000d01600305a00c8034030700c1ca110b9004114075402c0315030140002c4126500641d8190300e803624040040c000340319485d420410b2040e00c0d000c1c00100c00da950710060068410b5400c590014a5000d802d4041d4001e5200103400345c2c200349020004c9041510041d607015a082040d10401512980c442c91290010b40c0d58203081540465 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 574674037 1250 574672787 574672849
    0x415022b11070b190e0a06090209060d21020c030709090b100308040b07020f0a0905180706050406050d1506050703080f15040903030f0509030a17270309 67
    0x10404100020301d0300e0041c980b001c0c80e25600d90905020300901070f050001007440305081c4042d400b00c2d2092200c0020b0355030007000340c1003031000780c03400c0b1406a10900c440c1010554603c3e10540b80d5282e20751004145280140d8900808007845422100c2025401064070341802e50b501804000c010386111100001c10030054140301c2d815020040c011303d0070441c20301003807000c10600350540e811502035950442c2e40d1552807020601c0da8038441d401c0ca401107601ca00100340d01d40280c111074032499840e441c1e152071220950145507248201d2051101041c402c101c10b000c498454001400d003800641d00200e402c2e945110768885040c466402000040c0740810190704060348082419007050255910300c40c14200802c40c542004112035006201c0c80d9540c041d13a0806000b070f08010082c1c203402c2e0080016103041c00b03100d82c50f94440220360000900c110036036048403441d401d24a00603114165072144401f045080410021941414000c1c6448180314103c0350713548448000b1000807010300d0400d91400074071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574675287 1250 574674037 574674041
    0x20a0308160e0d0302161403060a050c0d0e0309060408010c0206090d08073204050f0405042a03050304150e1c020105090a1a03090607020f060415022b 66
    0x94103041c80380250812422046920460b00a00c80204540056181c0d9031880c0603440c2098111070060440181d1340b000940ca05011a040c00305082642541ca040e0348080c14601150b0044480c0c91440c142030214503060303d025031010601d103443c00c0407240b8081c0382c0700000360160015841070655a44850050108c3c0d60305205240c1c00c02a00300003401400712484000e405000010200c030100b0000001d061719405d003c80d2030305600c0c0c8440d049290b10008100070401c950b440f80c001e80b03010318034a158000c030b1800c10b407044900c502d03000180e200c05000c45001994262150100010300c1201025020004c00c0c01807000740024088a28064010151803001a003080301540300b95100364074103661208022541c0203481c4940d542481c0160303a41072004001008a240390300710441620b0101401c02d00c00513110001c50281200c40200c1348507696803641203a0b503400d000d06d0000290001404900020101c2000c43d441d030f50002e90240c181100c084011600c02c0106900042d03c044549a0f03825008540c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 574676537 1250 574675287 574675291
    0x803090105061801060807210911150f0910112b0f021b06041e031e150f0216081218031803030c060103030c06060603021e1b0d020a0308 60
    0x2035080b80015605d48400900128001040b03401489074201040e14800d880030102401d1851600741000411003500f4521000c10100803560b01800a041001d03224100410a441503c1c290008503480c100c4035000380702008404181000910140103c420440c52041c07015041c44880b481d182080b80402d44401c1d0194240040500103103c80c003480b2105940e408075048160b2403403480300184054407a000b11b42c1d10304c100d031311250b00d80b4900d000302035a00c041c020075241207a0007400e0b2501c10300282d840a170150380c00101c0042050400702c03200c000c0d900c03040d0000300c4500c510f42c800500701408001742c8000101c440c8421030b40740c00c0c0042d0080810820079940c0d03400010302400615010000040310742e40344544044500c000070401d101c802c242e9020412507010068102c161607841d40d503031601805247d42a0011208035007400d1012035201d100748241e1b00078142a820310124501c0c4c3d0741e0f6603031181d840f8a0901001f65041c1d508200002d10030000d1040c1c1a10950003002c50590908000b0305400340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 574677787 1250 574676537 574676569
    0x618091e200f0a121a09030a11010c0503041713140102060a1415040204030c08030903100b03061305010b0a2c010803070b090f0706021005090102121b07080309010506 73
    0x82c6465a40560303d400c41c00c1e00c00c0e164460314103440c0010505049a80d840d010080494a2102e0b004220840381c003c00900030000003a25420800c1310b030421000d00780e9095100d480001582880001d01103500302c0300141308940c140744810325003000c05003d062908507a403c40c3c030003081d40603818030207540e04120581d8051640c103010040612140e8095092b0f1034007920740090700880f490b03403d00e00e580c2e0f54101d42c002c540c00002e04034415551000e0300d84a804c540503482c428000c01708465041a541d006403941c44d100140904010754070101240c9145d0440e0100740c0d803c1d0340e91840302900b926000176282c0a8984c4c0d15100f003003150034148000e09103201400c00f402c40c2e045000104010b000000682e0003682c2e000751280300c240c0e01c00400320702d404900c9202c07851512a44c0340000c0e2850300800c03949422400b03a00b0030302030350b501d00c00c00901780d100381c0e890303104d517102184001408622003142044d481070000e0322003883c00d05151200c10154005654000151755580240b040502d070000c0c1646502030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 574679037 1250 574677787 574677799
    0x504051e210c0109051c330506120d0f0503040c090203072a02031209030f19020316080a060e100609051504050f04030f0c080a050a080a0618091e20 65
    0x2203d0000303518202c142c49002003800b03502807080c03000d00354407d18000c1c42c0145003007940d00030505022075070050041a2001030254200060002c44550046903c0c810701040d0349945c492041c00c08011a25130b80000c4c400c2c0c61041120b580414200c0d0350f070000b50b01401540d6a802070252070110142e40c80c1c500d4a866400c48440465080010380300400d20802201400c1042c585620300c1d03102203400c00d0a0800303e10694000c0740c0340c24805880700d007040707400035000390121644080c1c005110031035040b590103159030591000107800c1c00120150024041740c003003e03055540c0342c1e20084040c0140d64403900320a02c000d450740c003000700c1c0240000c1c3c0104070b044129018419418900d50a5462000c040d0028040100562206c5105800f40300d1103600658004036081c1c1c0e4400400c4018019081060446c000411540100d071840d1120b004a2040d910165014041d0f60a03811246004050b107407404c03141c0c00c0214449841101d81c420308148024041c0960100e003100c40030141031400741120807948251 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 574680287 1250 574679037 574679059
    0x504110a02060a1a0609040b0603040b090f03131e0b040609060216060c0807080405090a0504030318050c0d1a0702031309050705030103020909100e0c0109060504051e210c010905 78
    0x400110b10564908130300792031080c0d079141024042006420540c042c2500520004244010041c0508400c0e00c941410006d0303035400c40c1d01800c942d4803441480906146031002d84030511002800b0400c1e42004041854100045a40c5502d0008290400d91044000c540110380411546805000c0c054038026014040b0041e070b4200340010300642c42c231000c0500341400109004041061502c102d07005000020b200c0038a0307107815405031010701030440d02203000a0074150b04a0320100030742c00c15004c05601501402515802900b80300040030200780503241401c4c00c4580004a01a4298490042e4015030144d540e070620040c95000b501c1d416442800300d24a02410060701070340c410b051b41e040d00d50440e8210410f850302000c1c0c034034040026010301c241c01d02d4003107541401070000a11441007942a03d40d8070a00c3d03503c4d5801d0f00e4a0140e171040c06e40014806440404c0e0800c1907105c0b0380b902000810a244121801d0315110042d0300c164000503a59120600904156805c0703a4548002c0001b119498408 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 574681537 1250 574680287 574680311
    0x102030c0d0b12010906090201170702060109150e1f0819231009020a05010f120504031704050a0501050609040f0201080c09131e0c021e070504110a02060a 68
    0xa4458007072010719203030365030a280402e60b48148100240f00c070b20400070311600d00305080c0f140003010071090482c04141030142c0d48100c45031480181d4031030561078024020580c40c0480c00c0020b0100b46000c2c800c0c04d02400c00109a811342901460b000c0c080b230103001403c1e1294545611820140c03a0000314655106210002c60409103004040d80158044a250625107503040a0181c043c0c0b5501c00c0c005900a50072458803807107442d4020309540307000319040d041c1d4640e903400555103900c440c0e60340e800040740541004400009900000d40091103894080e100c0d0b10150f041d950034503016117017103800350000e002c040c09000090085603000712040b03c1c0c80c01c00c2e05060790b0300151140d500e1402818040d1a40001d1603840415055540c000320150085071441e00224481f4010b01040401024a1400b05282da041941d00e1041004801c41e0b45c0081c0003503c251010020000c2402c010a8038501c01d9010108060312140100400011090b10a68450015000c046d040c0b00d4000c00455400785002110600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 574682787 1250 574681537 574681561
    0xd14090d0e030d0507020402040b16051e0d031802030d0f030e0115050409151e0f0c0e090c0c01090605041e0201090918050a08120a14191526010203 65
    0x1203114101305a03907403454404200039026903400080701032808149103a2900c0c0003a01070416601c07079400d4a2101400340341d000d4200030119840540c5500803040e2010b0140240e01c00701e00c0e134004400c5600030340882c0e800030f4546072640c400800007400407104403002c1d0ba01400b401212071540402402082c0c4403a852004e01c640ca0302c41c9900c11b50f22599002e0074001800f03a14281c49003081c00070320801010303503580080e60401e460003107a82c51812103901c80c4e00c3d1151141c541c0301c80c000d6482c100441c03140c03c01c100c5101c80260111400010030860f103125001d0903c40c01804603c10200801c5510301410181d84c50200c0c0365040d01e034080142d40c440c00507a440105041503914039600050044c24400b9003800740c980016000b013041c40740024050501103548050121940c1010741c40e03c00d540d41502c003405a0360f240600507034120180021400321001e1a000e00500d010010300001e000c07881c0b20452000c103210791700c420021900d900701c00c1d0307800402d01602602c805060f0008e61560400744581c1d44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 574684037 1250 574682787 574682803
    0x101d060607080a17040b0601020d0809030d1515031505010c020f061602030307140106050312090907170a0c03061d13030c050d080702010b0d0807060504080d14090d0e03 74
    0x220b2400041e941603c03400784043c00089504030710300c0001842d140c43c01d0605940140d46030ba02620030720002c144040d108041a6104070803060195040450304a4000c015003418020a60501c944400100300141c0d411042c500c80d80042e0750201d040140c40700b071680c0501c029041075041040307046402002d03031a00d0b83c0d40d4141000035100d07a641c03004003151002c00782a000030000d50500000920703600344130344110f08040d6185403400801685550f01c00701962503482e01c03002c2d4140d0001780240621031600c80c1e482a485032503410005421004078001800d904000c5481e0a5110365070b10f010700c07202e64035100d04000303090050151904816480480036401100900000c910902200d52600305031140070400403203a4031078205c2c0d2100141030780140809030308841c00340c0103602c0c04100c001e003894002c0900b08500d4001d0441442c0040300c0e04c4201c09003c0040065880780e10420030080313403040d24414240c2c0d400d2003030b111440d5400e01500c03060510001e48405002c010855031044041da6000c22086 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 574685287 1250 574684037 574684043
    0x51213050f0a1d100b0703110705120a06050c0d0e0109120302041a0315060309070303020124290d060639030c0b0f010e06010305090615040b0306101d060607 69
    0xf940d07440c012581c0d184130883c0c01400084802158202c00c154010f581108010b02240544103034035142c00500c005081e9012010b081030340f00304c514001144441d441796030480201c8030785c10314000041180030291200e1954081050799208a02418001454260000b01005142c01d500d8603291040b420070603180c0c14488004400004040303020020011818800d083c8054046601c034039040c4020764803610148001e401550030900707500100c0300e030280803040303030615040300c680441d05019a0310102c0400c11540001c1854484442d070b42d4203d20b4024101c6501e05440c0841c0460030b1107002807100d00c5260381094034001d1030b80080398462410f0310513402c526002085218205a81c00c040b10794034000c12018022980f18418004c0c441210b0010380c1c182ca04d0803084642c2900c0348030045040790b0301242d482009070060b03800705466a8032003c0032005078100400108520705a0070009080032003e0700c214280c200341c2c10042150400140d04122071043d00031a2081c2858a4400311300c6900c03410b1002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 574686537 1250 574685287 574685339
    0x1080303180309151e070b0403030902010e120f0d0e0612100b040e1605070f11030c0307090506030106080a0507060503040213090605072c0d051213050f0a 68
    0xa005908810010350f201403600034400c3d2403003408a400f480300f41e40302860074a03143c9003075080a03241981c40011240003070f922017041d086964407510f089000301304d004400c0b410400031041034a00c0e40d5070395620600210050000c0c00d11114500400780c0340109a00019007882812140c4a0f403964031f0000b80c49200440d683c1c1144030365521000301028255903040250300c54008103010801c0100e507541d2620840075004000d102e040380034003d6940d8014031800500c2103842c4a600000203410b04a4200e148101034100c03500c41e0264800641041c05a03003003698159582c0c03041212a1a090141100410018000c0c00328010a52a00340c1c036040c00b4001d10b0103001e000004107046444007544900b166089040400a196103860000050131003501e2030070001300d200d030380086031b44007000d000036215039031000b0103046410f400c040c000c0d07050802c01c040c2c6490044000d0b50302900e207003400410a034451640d039500690b00b00000c0101d1741448061300b9006101d56081481513110038400c000d5134030420014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 574687787 1250 574686537 574686571
    0xe061e040f03090e01060302040e010b070b040f1103011d0c01090503030d0203060d080d050a0b041b0309141606081006170603010f06080c0f060c060105100309050d080f090601080303 80
    0x700b0b6500500300d600c094a0404944c00000e0869496409081030311010000c0783e04907661410801c9444c058108058003020b40f1001042c0028880d12650b81305900c22030801c20342d4100c0c00d001030308490034030150f50489500441e040b4107180c0705100e100c408900901b0941415801e201c04266607009880c612600c4950000101c5c05a41d40c1e84c0c21030301000da0088000d1364aa08105800014041c00c0d5440c103400e500301100080c4514141c020503000042540021200240350310044020b0306410b141039070011000502980314100521801d03000700c03004a800d041c1c15103401002031890f030000b82404250840d070007041c807071103a00c542424080e40e41541c584400303485442c0041e00400328258403e00c1c061410100207204100440c001303080d036070212001e484101d0102c080c4040c91050450241041c0c02c8100180494035002c10700c60444143c0340340001e48200155645842c160500c03109501141e41113007040b109140b1101101c0c0d10640240241c14035501d480155036a0307000150404c0422030a44ca5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 574689037 1250 574687787 574687793
    0x10c0302011103040f0605100315020a0302070804091509050f01031416060e0102011802060d02131502030d0c111c05070b010905041208070e010516020d060e061e040f 73
    0x85200c50890102c80150ba0307041c185403100c8104c2c1803140440b44242024000f81806580411315022a0341094649100d103810761801e1000303510410842f810b255003841074201190b00300010f0400703004120000500300000966029a82c0b00329400703040e10340d00b1310f400c00418200382c004441c1105e034004240001e05012074060340c00c145500e1a800701e0600c80b800001000b6031300021a0400030800c3e002080030042c00c0884000e80c0103920400781d0841801c019100d40c400036035005007650000440c44245090b260102e140d00100040d0b0342c00010390000c16150325000c4a845003120510050070000c2c80f00b0058404581c0b035210700725018516600f0040d5070300c0b6850140084500e4542e1106a44010b9078460301504000c007070a0b18280c441800c500c860402c03d074094003c2134040e074029280c545031401c8000c01101c85900045000301d007074248900712401611076550006170702d4450300740420300160400c0070074500140184ad6482242041c0f04000f0240c8518440a41054000300807a110b104282 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 574690287 1250 574689037 574689041
    0x8010b03010f05040f0209090f10120807110105160c0620060f0a020c0316050d03021218010b0a261b0603040501140c030414060114061b06130c050a080c010c030201 72
    0x7161050b0003c20140400c188108100742c9c0030b10130780380c2c4400d48031029203034204826a820325210007402c03844200301180215000d4010144565414900b2500d41440c11049011400a130300d42100d074401e1000d000e1214580000b01c003d44481e0b00144a894041215640c507940c03000903058230300e07511081000c900600c0d96501100d60840b07002041729510f5a21386821a06191041d40a07078903170044513403410070306102e40200c0e0000c41202c0c0091907652906502d00300050b250607051005596506070340540c5444880c800c10041100f4148a00c0740301109030b1112445880c83c0100311280c200c1421000c140fa035042d070840200380b098400b580c036070f41c8901c2d04a004002d60b0110101022a810804c0b0070840b000c4019803085111322500603011030350300745e90b540e1200c0030b000b0160034450382701418581e0b0a00a0140081941101108130440c407078141403404d00405031480025640c58041240078055407042d032000400c001d451001c0103a207031510160320b03200c80520740340c10840c503081d6460600d0310035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 574691537 1250 574690287 574690297
    0x39020a12030c1413080705100e0910030b070504081b030d05160b010b09100305040308010b090120010204090c0206061c052e0b0405060d08030702031201030f020108010b03010f05040f02 81
    0xc0701c2842d84c2c90840d1600f480104183c0c0c0b10303455282c400c0300c81c0407681c1c1c02e1008024a00c4209074641108082d13000c2c0401c491b0401c000d069501440a0351030000120f41c040504d03e0040030345440e03040da9142000740180c245040e080c00000316003030703040c803008460302e0004420440c01682d00d8955100c0c1c1c1081a511419405041c1c054601d03003001001090686010009041c6044c00300c482c220100240d01e416016110100c4018001c16801801002442d034180001c1207000c2d0149002402803024030103103140c07032810745003510b40c503980400c05009132000d8bc4201c0c074810380316000502d41031820341e001403e003140d24030001030f11044801250301000340802280c40a22000c420200218406441c03010480141e0058014904d06100200440381000c1c1b240720300440000d0038804584403240c0300d2206607440900303040c08512080125201c02403004458034041d612800101200f8010b90000411958040e04181c803085810001000038034516401c90003140d43c01daa01143c0f1041444800d0001e000c4e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 574692787 1250 574691537 574691567
    0x5041d0601021e071701050702190b010b09010507020306130311070b0d0f021b01020909060604030506040308060f0a080a140102031614040513091407052239020a12030c 74
    0xb4504084080d017046d04503600c0baa14980c00c5507001c80008244131042c0c001744001402420074a40140440211100103068486042c14203514141c1940cbc0072030b2400720111900d00800849044480805500141c103022a00c411002000c841d8201000c56291f8450203501c0c0962640d2000041d0030440306e0340540d11201301295068024845581800c1d0207503100f010702030720030358883d0000365140c5070a00c191400d40303411200400003a611940c099031071a002a1002c0e40c440c400741c003403401c03c0d03440c200298064400c0030041c0c40045c0b031516210056201000326001285d0041c801c000400324034402480c00e0703414504d00310160034110010355520744190b03080b80e030708030003001500f0f21a00419004082c0081c4903144c4100b412039010f0031517882e14018080e45501c4005151034044c1c40060160b2100d01d1031035030f0310004140c607055000040441c2d10300c43c1c03400d2840000d0011115410f40140c03004c1900000e0016005108036136442408030718400600509140e0b8549108940d207109041c07003100440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 574694037 1250 574692787 574692809
    0x9060a1d03030c10050709030b160905120a0b0604020901020c0d150c21060b040504150b0a0c0309060e01080109020c0c131a0103180609050f03070305041d0601021e07 73
    0x103243c0e20155128060a81940301c2ca50400d00801c110620440f24181207a800144000c1b041d120b000381d07441602001d58000042090038400400c441c0c0c1c0e000c42411200c000c2c41c2c000c00410400385844001980c1c000c042074132442c03040c0f04041c442c1c6d8000c81d01c05003604045030f84241c2d4110911b842c034400c1691122200c0041d10f0903515a0030241c005021544000d1400c82c81c030701018806c021202a20140c0c0100f12401d10280000c1007281456005014288902510801084e8450390b85400079000041000c00286c000c0c9190300915400000c0103029020500d04401c4203440040040c1501c43c061050400380f82d030000d2488a103070310500442c0841800203029030001004103440802800c0340c40c00c03811400d01e403200101019030080c441d214468480404c80d000c505466181d0900610705203405481c0c5000ea03011490140c5010310060412900c281c944d1902e03541001384650503161147c01345036030a000001031001c0d682e0001151812002c07501d82c81400552503041403414020702d640072004c504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 574695287 1250 574694037 574694047
    0x40522090c052d01140421020a0b160f0303020702030a0506010608011e151e030f05100602191b03080c012a03090302030f0c0606040e0309060a1d0303 66
    0x118034241e041c2203a5086450f00122a105000c024402e8107103443c0c000c4090000d02c0482d12940601d40d01078034064000c100e142065620b44003050200f140a000e115410344040664086103400100c1101501c043c48415062800c20b031f00403401c030081d68902511440031091100c08062298044400c1c60f039000d426220301045070b10381955a0070080c000d050100300a8400441d07070980070030492900340703078034076030800c06901d0141a580900705281c1000f0070000c01c0210307100a0801d0004414100e01a541c3c00107451084180a1086480c0030345054181c0700003400c1004150340c00962002c0521680451419510692607d0312051030781072255603800313210803030003c14404803001400b090b192040003804401d0b080c1180001d5001240300c42083c2405508817080ca242c8217601000c0c1d62882401140e203001c04c65500890103801a45d0401202e520030f100304002c50402e0701a4074106850100254180421680080c0443c044c0f80c8a50003000807030441031000c001c0604042d40d0291029060742da8503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 574696537 1250 574695287 574695293
    0x6161b15030b09070e090a020409060b0d06080a1716020909030c013b010f0213140901210c150f0809030304020102070303080903091003060602070501090b04052209 72
    0xa400c51034aa000329160040c01d030541d081143c0d001d481070603150364004560141e0000c00c25102c802034004d4580b2a0709120218008a4500c20240500b040d01209a202c413500c5c016402950b5268009150796040909118000b0300f001000c0c170a841094480300c0d496a062442000080b2030a51010707520070301d20401e200c4806130200050500d140302c04d0003446810030f00480400d134009102085540c032925a49102c040c451141c1d00c04019408410021610481440080d0140d0b000040c01610814444808001802051000582500c801d0740d6910326585007000c0c4402020803100e0102e000b0900901e400c04214030642c03480040c0000c00b0720081c0000703010302e004044001c000300d0100404c12000104500c8003000090304c1c45194168010100c1d03d0075a5011a89010003801d09411448140950104c9a4442e119041d2556040e0380c00550140b03040c40c02450060310b40e100a050040841061041c40b02c030200b1202501c5064601030700104881c59085141c4924809440150345041071003010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 574697787 1250 574696537 574696559
    0x5040218180a0f0207080d02030709030606080607170601080403030b010201090c12050c0307080c0f0406030f050f07120503160305130902040603061a070f051e07050a0605070206161b 80
    0xb02041ca8003007024003040144541240710720344003e060003409110044041c80b468009650102c01c03480d08064a540d642d8900b002c4e1406500652043d03001181042512940314a00752086010b0340c881044a081082c00a003403248043c201504051b12040d10a00690007500500c45c2e0540c4480401602980c1c1e0240030070044107280c04452500505440c114a8500000e51a0a0f65071607405400100c65240800a60000390303c1c0450308a0303100c1c10004045407000d111420114020400380517401000140b1034103024950300880c1514012b00806804508000180c0f0041281e001d114020039101d030405407898001d890094841c0048040702041046403900034104607035180c2c0b42440166240c6150245080c40040f0101d00d2140c244601c2011030210a403204180b4010400d44582900d554035601c03805c1041c011040546c1c1c0f21301c0f0100160705051a80c000203201c0740c0f90207810065540c0c00101a0b1040d9041d01078802c41c82104a42444086020b8501250041c0a03e10b0019038610f02510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 574699037 1250 574697787 574697791
    0x1f0b03060a09140a0b21160602010c2c030601170d14070b060a0b19020708120307110f010c0c03120504080d0f0221060a0803040806010504021818 64
    0x3004110603080001c0c404024041e0b1010f00380408911411540c2d2018104024494181003582c00500c00c201c10f100d032030034042e103550300080d20301c09072110941c40d202e40b000f0625a03074003440840e0704d0842c02e08100c9501140c44200b48426850041500103038200b88004680041041035060044500004501310002c004c80355040c000e00940d60b0102c481c8030140c4004104440c070030060782c01006040c001600e095501a4001c00081441071050340390078412079503811017844141e9a000020840c00025010014600100080c40090501c6664a0110300e40d6001c090700c0c1406105012940c0f01818109100c001080e9074400f0080000000b00c00c0c0081505c02612020b0307010030a4441d00c0380c509410f6000b62407007541c00c1207045290071100e28040c001040c04020780c99120b50309105440b60100001d01e68010a80c9c0104552814108075080111095265010948a0380b0402080110309400b18003181154412100140c9501402d82222044140c04260a9020701d050704d14101c0c641d00c3ca444a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 574700287 1250 574699037 574699039
    0x120c02030609010203090705060703020f120d06081c0e0a0e0a090614040201020d0503190e0709111804050c0c0a0c081216081303020909070e0a050105010c0b1f0b0306 73
    0x58107a88605032014201c4c401600c0c2071038250803025090106091a41c002d1030303950b20030320454041c100e001185509184c4c0810289401c10000a01c03003c002200e0f000701000b0700107a002a28201d00407042c80c000761180300b81084288170900340395410030f60310840b042c40140200c02a8105e07600c0c144100c00011700d2842c2003115500e28110103010b900b210620050312881d41a0018141044c5508090380c4941004081040e510720b42c600c202030f120703d680504215064540010410b0f103082804110a07240020341c042c150721424004c1009051054041100c8407200380c50014031511403451401c04e82c89602403165161103280d02000812014000080803104107206031403070340124034801d10140c410340c809074003902c0c200004800855520002007a03002445440c0607a580d40c0ea40c00700d25001d0044810740201e400500e020440380e10207100140d40495400e004014540c18540083c040a081820140001862072300042e9a8482d40f01d01c0d4001039050702d00718070117a0303440450a41c1a030007181d6007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 574701537 1250 574700287 574700293
    0x11040e06010e0a27150b060d0504062009090705120406090812150109050102030405011d030c0406080d180f03201f090504060311060a1413050f10050d0b010507120c0203 74
    0xc0000701e0080c0b248215003600103100c142340c5500d10103450050710000e0010780b0354984d0788a03135007c900b140c80003012002a2480e444d0b5102d01c00c100c2000b50300c10008014500b403200810a012145030f480b10440d50081d8441c10019030384490742881066030003180c5025a00c074080209100c0450304072040d42804000990750580895100c0740120307101c0c000c512039640402c043c14101040c414020707244072070540010301103640b01d12540e8002801d59081c0d038000111500300f40500816154014520b502404616020540300d5207841000b042c04421fa100c040e201c41d10b119502d0203050200300302203244800003060a01c013480030341003217102e200d60b04c4c62007404103540d90b0300040d10307042030b00811045a80007440c070591140e42205121030b0b83d200c520707084100206205d030304040c110003078080d21101100030401c2103001e00700820f120382941c603100d0c00b9224128148140c28600d9000c000c540610072030010200310741030700c100140c1b0790317000e2258000c006c03242000d00c010b00d03076601c42c2804440710700032011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 574702787 1250 574701537 574701563
    0x6031a101202220e0115050c0a121b0c08150402030a030c17031e06010c02030c0f0604050d110414090c100c0b1311040e06010e0a27 58
    0x4009160a40040c200041407400ca02020740c200181c0c0a4042c04881c04040d0070b0700340d000600181940001d40011000340060001800051145400c4010401e11030400d0780c074141a5030b28440d0b40c5d144144008040a14000906080b140b01c4c0303808212181310744141454101591804030380c011080c1c040c0e04403074031421180c0c84400025010044c020381e0080e01800c2442e100e5102224955040507003900c5920300f03035050303000d00c02c4410000c51080b01030000ba11210016407801d4282554050300e041d041041d2141a2000750341c002c80e40001002d4200c07690011030f070b005130101e02c841c025940031740d40c440301c0d118001c014081640d00d07151281500301d03410403840c040d40d82192200c210950b040d512560019950040d1400e00c600100943e00440c00c11050090040c1d444206000c82106c2e01111040051a00743c1000080c04c5030b086a400b0132202440444107144000742e4420341403150203203203850480414038800090788145044001c030002c0c00740390001d540028102025001d4203d41031252290 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 574704037 1250 574702787 574702789
    0x51c020106050a03110307080d090303030b0f0102030a030c11030f0304061503050d03051e01060c0212030442090315060608012d12150606052502040606031a 69
    0x481d240a4907030090182d0105800c1d5111a41616100880c4030341520815802041918040080e00000c1c0380783d540381e200301411841c0082c1a256010310707d0b8000d0100500d09000c6a0f004000c5d68001859894001640f41c00c61800301c0d55441c0e00803004500380070006020941d040e0010045200303500542d4140856110280c0c180c841c0d0003248005070898000c108000e90144c801c0c1c2019400c400314501408446590310440481c140702079002101180d4945151021030404c0b01307150000c102108061418680f5004441c40c80080c855200c11013003645165240a4003050803144410b07001030b101038101d114a150026203200d140d40815640d5002144041c0c0240e039250107a0415a03500782d4034510540d10340404a24100328141c0e5031900712100320002901c0e8a120740520005081c86102142121003604000755413030161035142d0b494a0a140717041c801709402c88104c0c0c0f01c25410428410f003049444454007440b00d010000254002d05001d00003030036690603042108001510140c545014030680 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 574705287 1250 574704037 574704041
    0x9030c120b153102131d1621020307091707060e21150123030c0d0c0b03070807031a0102100b040b041d061b03010b070606090207051c0201 61
    0x5104603844200d07052016149140c00314060803d807020b5140c51100c128801450b02641c110020b40301c070845034114204024004101b0390311101461480c5c800440c2881c002c031001010640d001c1c60203000200340b01c0001c81c0e00040b074601480080c04c6085480382001d000040c100d072102d22034101d250003801c612244a41011490f43c00b01c0c2d4540e00c400070442406014003000b10b515111042e48000b502400c0c000c4c0040074000d80c41000034a042200740c960601c0120304000d410ba0596560360784010f9a1070343c0c42c1c2c500080c44d00c081d5000301c0f8105050592440e01500142203500207840c16407001c02031008058101d910103010706081d460901c0701c40795840103aa0000d0803141d541d40140e00405c1d140c02001e40303681c00b1403206040a040401d6544c0d0081c0402c0a83d45c840400e034088401c5048001c900031020300215170450042658040440c540d94084001408180124079861100040324020004543c0c0040c000303203410070041d5124006410725940321389a502d5400c90700041c1c0c42e07030115858418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 574706537 1250 574705287 574705321
    0x306110a0503040b07050d230a020c030f07020619031b031b2007030305030618090a200a080f1002040803040b0702030102090333040803060f0109030c120b 68
    0x6541c54600755a02c54580c08a4104007801210512200300f09118504955005111446000261206080610003441d124055000301514117a038414031079000080c8010003100c280d0b04488101507195141800003417002d1042d103c101c20380c0175801c42c0e103040040d059000950010030f03a02e091120100d020714154144c40080d00340311240550407120b181c80501900d40003182c07400e806c0d20300190b221b2661341c151400303209403c10b41c08680080100305240c6010030094402da034000c0c1c02005a4106090b9041d0b448440c428000d001900140044c14a12444000f60701800c4d4001c06035501e840d0754400185d2034118088043e0b1903806481d01200108000d40221412103042d00000c0d07180501e0402440115040340b08200e034103540030044800603541c2004220741090341c3c220b20203425410450621481201100b060f50002141c1d42004080b51891042d02e41c0f2080a5034040100c010240040301d0310556504018940742c0c61b110702155000704e00c0d6404400d180f203031078200031988400010040010035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 574707787 1250 574706537 574706557
    0xb2802030f16050a080d150b0909041205190806010e0102060f16030e030a0f021c0912080c010603050d030c020c090a1d0a080a030501050907090e0705070f0c030611 72
    0x42040b0042001e44421002091180101c0588200c0d0040382d0b6500c8440d8402c1d901c45907100d44405403011824100a9214000d100481040d440c0c01c8400700458004039009201500a1210340480003030b49005e5021102e02c1541204148404a00f060f00a02010000e4070410700240d501c0c20300e0b0038254000500a40120b0383c03031690300c8555850300302c00203000503880c294000305034035842d601c5030055041000c2d203003460f1251105c0c500f003e4810310080c60b0402201076000d81c03100e0064021480d6404c4845042520811002c850045520b803e06204038401d85c81c034803041d0341c0b0b05000001071200100e00c00c8600c40240e5810b029501c0b031600200d82c2e41c21403000650744002900301240312031103141e1200c5000300c151080742408000d1000100d0400c01a8402500c4c0040000752000916505101e00e5014000c200c80040a07410091030050a40c4001e00904202c003a443e8041080f407405503094895940c2d00452007502c98a6500d01035442d42c0142c4401c48185080c010b0301002e24010300250b507401c880c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 574709037 1250 574707787 574707817
    0x1503020c07170109060e0a0b060d0b0105041515020a0312020403021305100815010e0f09030711012c0910060f0e010903080c0105090d03110403060b04060b280203 71
    0x7007003080407000300c0040c03203010340b0079035a81c012500011014014400603d219501401c5c0c0c160060611269078800107102502c1182502e04c40000600d1000c01181503400035503001402e400d0f4401c0c400d900001e203030442e0740461000164030700c150741d0008669000c6403207a80c0c0c0000d469910a07200c002c1e0300842c00000d60100240d5822051010700d54800c1da0702c0b540311908110100d542d02c03e2142840751100740c25414501020050003041400044c01e5040340444980c2d00703180c900000e41c0c1c1d489000d440001091054008507030001603116205600010301c8a01803c421522110085110b58450b41c102030700400c0f4110004029046800c4000d04a6210341c1310103590441d02d40040b07507080c1407000000c1c18000041c7d0080b010400c22009031840c010303c40d0001603d424050760481c0752944001c2c02204141c01c00d00880c0740390743d00c00181c40440c1e0b0f1084c404103161000c600050301800030703504007600710540480c0b07883c01190407941d940c00c82d0700105501c04c3e5900489000300d8980c4140d840d1407003920 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 574710287 1250 574709037 574709039
    0x60406090506090f1203070308070216030803100e011511030705060105010513122406033c0828090e150907090f0608040c0902031b0409061503020c07 66
    0x4200b040c01420100c2004008032001c552440001d0840740c80162843c50961010417a0703400c050704003141d2a084000c5000402284104005511a1080502006003d400c0100100300e1201c070ba1150403024108000034801c156840d5041042d9581c170503d100300c0001c13210b441b070440581000c421517400300c0d04200540084e80c00e200041d9920340c426100294400c1038403800086038480000075850b007520403892101034203a541c00002c41030311034205d41c1c000e052924004100155010707407848410754038050007075181951280c40c40000300a62582c4c1d402c003427001050504011952008000442032880748441c00c05035004428800d14005440401066800740b040c0302d003030401100c007644000c594100401407440000030821800003500d0b140041012007600380004c0044a01e1003002e000280f82944c03072403400c0d13100ca40a070b191171b1141c011050b0b030000100e00c401414500c5206094008a25680d50b40da44400e00d00c01080d03903115120f005180383d5a4684503078824001c50b005800180c0c0104202 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 574711537 1250 574710287 574710289
    0x90e0705010c110d0c0305030d0207030e0f0a090507091e03020a06140313021f1805060a020a0605070c080a0807120902030a020f06091305040c050d03080a05190501030501020a09050604060905 84
    0x2404c803d403061390a0382d03100a0000c0014002c02c0108a008100300026071900340c2d9260181034111046400c1e032140b0800c1d03000b005151580404607044030841c1d03c0101d0b0387d444e851030540c1c6901c8682c00c10038900d9003140c600c070002d02522200c0001ca0788250780e4051581d0341c1d04022030721070401210108504c2c0040012403080040a00400900ca00040c68103038280109240e5128009405400340042800c14109403040364464501c40c00804040d00c40074500481000e000f901c5003643c000090034180d9440110381014031408040900c3c3e81d003c000d60f5590180c0200240120108488140000e0500b0880b02074010703081c09085051640500100140341003642080a82401440e096070400010300856005650f103070800c015481c08041e00052906003820100350310745803a040300d0701074035a101c1c9090001c1e600c03030b03012640000c0070a40000c6503141c903020b11010300c0f8001c0482d12614106030001c0107000741076008081030003c580310380c041c04d5954424000e140c081c5200348004100300240820075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 574712787 1250 574711537 574711549
    0x30b0c0a050f030901150603050c09120a0b0f161d06030403180f080f0703080906030403030e030721020c03030a030f0b04020d060303080a0b0303030109021b010501090e0705010c11 79
    0x26050260030010b081c8804651440e8240d0400c50308900542c3d16184680550711a000342200a8540c501d418030103442c19007904110380c0f00c2d0000190080094207804c6502c2002442902c0c560340d44032800c41040d00f0f00150300480c03940c0c00d9484d170222140305500d032208540500d40240c10490700303552481c0320a0308281040030755000244140c0901880112000b030303400e50300c000310000d0950420071141090414030350615200c48036103c034880750b010384024000b240480d82941d0036072074202d5580b692030b076440c601203001e0920044609401e110100740d1504008a50b520380c14500c024100001e914040c5540890f03a83d00311000094064108000b240d424a210f80c1068045110703c1c80c022800d4608900414101da0140012155465071000e0a000f0141d00c0202560041112542030108608c1f0200081c1c403440180700340680160300003120703e080c0202e0b024141c07117041944001c100e1580d6500428000d0302036036085c0704a501a0900c00b241030b600034907000e044142c0044007074000100d001c05000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 574714037 1250 574712787 574712797
    0x200706030f180c1a031003120212040e0a2307030e0c0a1815030309140418050c030c103c030c09060903050309090402010e0301090812060a030b0c 64
    0x40460b00c5018014402401142e0108140d01c900d4142c4481d41c90402d101c00108843e6048058000d4100240305200c03038140c01d0401a25000603002c500c002500318103a2620352441d501040032000414000344174200346400034030940002c2c0091190112803440f0000d814070301c404090103041d5150100f0001d920940c000101c00c240d4204036200c004140000517007002c0282d201c1d0010100c0305504c0170581000b4000e00f6a458020f650407050181182c0c3c0141280a150044021036031903400e03142030660311070b0007035140400303580e10414458034903042042c1c031503807240b0314240607111340d0186000a06054410650f4482c10b603031088a40801c3e031030600044041212113202c01001e81128240c8212140c24251090000351400100d07200e03000030140078004543d000809212851340200042100442107480c1980c0844005100703903107910058480a403408081034040d031030800c070300003001058002800c010707180c0c0810b0809503652070104a200d0034a0b0100601803100140401c0b030800ba5903001c0c00b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 574715287 1250 574714037 574714061
    0xa060f0b060c160504060609090c050d05041202070b0f07060b0607230705010e010906050a032a03050f040515090307060c0306170105040c05060706020c0a110120070603 74
    0x12441030440000120160030041c003420158004080a001156011540c80d005004c141c0301401013034605140580903c605110b4544a182c03543c6000b22000e210703504a48c0d82c80050b280401c500d09041c144103802615641b05170001d885029408902c14250a007a40c0360f070054070070024944038003070f95100c000d407034810030040c2c10200c144000341c0007a011034000a64080540568429807810000c040d142c000300e6800941444117010032070302c00d82d078865098070580b2a0b6003885036640c00d00c01801c800802704a0a4101e041800c500100740303081e9240321a840082e402d60782848245ca510f450001c150320141d4009160303601c01d81d00c41a1442e0b4600e03c0990002c1c84406507420b100a0f41c69642c01e6500c0421108002a511032080c807071002601032103507100505400130011031410340da444003040001d0244910618002c540c010030401903804441140103424240c0710a210b240c5443e5800c10030076802d00380441e444c0140f01118202e00e0243c0003054086070020020a4940182035005213010781c200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 574716537 1250 574715287 574715291
    0xe0318041401120227070c021908060a1104150e0310020403060203040c090b0d06110405030f0715020d0906030c030603142a010c0803090114010807030c090606020a060f 74
    0x1c00e03065005812950300070141001e00b2105400c8900c10000f0000b050402a07200d90240d90780044036110303c820450748a50740b0b00340320030032041324000a0746440224950080d060b81010020804e400042111800f03004080d0003803000340700c0403039080c80c94001c5026011844034030001c80c0b690b0070711a10803d0001d91014041e1520312411f002020166403082c2c000351a21a0004140030030072841500340c200815840d0070400616003801c00089444441d050003400c059194001c1c43c50100c00401154000d100c0182211100849280f48a80301c0c10a0704c50152000003516441d140c450010440301d042d580565503801003203040c682c0a8004000c1606214101940c4080c0030001500316040b401781803004900804031000c8403102c60703210010406001d40b0b0407034000c07040a0641d80002d85400e00c2544a03490301c1d00c81c1d4403008841d00600c1004500700202c0d1380c107000000c0110000c40c403407003668080d12080214076101c5011a060710765130b2017003000683c015031800012510075403004101e14140c03600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 574717787 1250 574716537 574716551
    0x30d0c06050709080316030e060403060b010e010c20061b0c041515030c0302040f030b04150e0c0402070809100903110102010219230a05180a06021f06080d050408060a0e031804 77
    0x809c01c0b68009800840f092a41c401462801d5078000c42004180380003440c0c4a1150820307036071070314281804014448000c1d80c409407506c3c4070b07079640c40595104240e688e019644d02c10103104803a984000302c3d0701003405640750452444040810482d11000c0d82c541245044510822140c210002c019170400c4404055083c800800c10801d60310b01c5200550091003060441d003403d0421140c40744603241800c00702860300610106440000c50120000c10f800c540050310742006041048852140a82c0a548800010b07d01803800f50401c3c1c0140a07680110703940e460104090005900300d00c01d004090700c01060041203030400f544603503580707001055041ca4064142c0c00c1c001c0b81c014540c014006000220314049a9440303c0ea4640d01310f02e10a1030103c440761840792401c030010352102052401e15035408030712115100003c0c126040031008111510445503e4140001c0040807504240900c2c0d000e07004220110311004403500a00989505e40e5010314070f0032084103140842c0c140344481e00c54109459541d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 574719037 1250 574717787 574717789
    0x7080a111908030f0702070311060924120c03071704080705060f1605131208070b07050a12201b0709060306060605070c05011805030d0c06050709080316030e 69
    0x982010030502c16500a0f46900740221800131070360009104008641c440030b41007012413200040260040002c0d9011682c0c0c6d088440030500b5000b0382500c2c00311441c00e05c07401407040788003407005002c00e8182d80d400381c100e5207503484211000e120a172807540c0012040716600d140320800880064000d0310a45440707207030040c0c0780c4d1041d04100040b0744409100814404110f010485032440c0140001c0324503009181c40f0ba040c041c001500902e000740002c5251080c40041002007403005c8482c1150014040388052814101c001d045600006840340011078600c88074101d00c260307006020411110031007050342c2c1c90300b044141c05580c22800705000c0000fa03100da81c07048054280b040703d014151900c00410301310f06500b840c006980f00ca41c40780c802c0000800461001c41c0700e00c1034210540c0c0c02481c100800e2074090900101825894000030381c140176002446c07012542201401001038450041807115903034100d410749104000c1d11490203e80c204000740e51000c04141d02d0b05c01307843c6c4241400003951020308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574720287 1250 574719037 574719073
    0xa03080936060a0602121209070b0c060a060e090a0201080702012c1509060106120b090106030906060f050a0311060d0603050d021006050f01110c28090207080a11 71
    0x20304080004206000d4075083c01c0c89010050b0000780000c2c000201000d149076290721820a1407002100c503d40480d01090061141c90028480c1c0c81119480c0c0d0700b84401c00d42c4070202514102c045030b1420b1000105512881002841880500090704004100d80c0064441040041c0040115581c8541850404030100f0b41c0c0d5288401244000030301016001c5403528003045e200503100341e2208102000b00784c45d4001003903410b444c42c918000300b00b241d602c02407401400c3d144000982c48481e060000c03402c0b96045d44014a1280035040a002c15030340c0701ea50090707190281c040d00fa0855004170041c0b0210750541044500c0250181c4140d00c0c1c14114425442254010b8004a40350380100460070b10450703040003000e152028240040010034a040c0000e5400c1c05202c0195040c03065100040380034250030310050100c400042c11401d001040800e0f01102c1000e148100803401c046200c021404070607610940303401aa004e0b00d41ea2401059040594080141c80d400302c65510031480200200b003004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574721537 1250 574720287 574720369
    0xc150c020a0b0702040b0301021312031205160806010e090a18060c020703050f0303070903020f040905071424040603021b0d02010506040e0613030302030c0424030b0a030809 76
    0x2082915031203003c40d10411081e11808044540700b0780c0144141c1c21380301c1178045101c040340c00f40b580700d401d80c00e42c1c0d160564895900d003296584c00c038030f820208103404a03403103001e0f42640e5a5986460039a45d880c001580e50114000006401006c1d4a001440300021940004404008041d421906580301d41d01c00054403d41d1540200680001c0400c0007006020008800c1e43c84881c000f40d425450201001816a401c07440060b100e20284c00d50034449444507400070403640d4000c4151002c244e290301540c800c220541102c540103001c10a84200740040240d020007003941081c000310f00d09890854104c5c0a0340100b4940d41294084129030038007044108100010a12660000300e40c0e0704c0c0040c10401251864440380d4140c7d0002d004004807040760381c3e62006c815030315040050f140e803260b501c1d13940107014a070060006032896112101e4820a52415480a85420358050000c002400c0911080c0701c118800100f45240600000007145003084c0d0b407003182946c1c080ba04420350211020400c442d011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574722787 1250 574721537 574721549
    0x30c1718121306021e0a020d06020d050f010f060906090b0f090a1508010b070201080402012a0506040204050106030b1509130c0507021008060d030302030a11120f130c150c020a 77
    0xb8a4200905034060060149a007640c071068400c140700d41d090340f03445895901d0001d110b8075445e0700240401c044c940c1a075410b150fa003407080140b8502650b03a038202c04820300850200e004404c03c001740041c4603d001c1d030151040c43e691070f45071300d15040701844650003030709007580c24000038483c00155446600e00c43d0b0042520b250502e54026040401a0040c1c406811040307251400b0090440540d0304095040d40196080ca0846075842c0c3d0409191145100c0040701c8103a56010301d018018454006041da01440c02101c0c104003e9aa07900f042d4100d8132420005078020300d4031050528800741c40006450342c00d2001d841d980d08060410906011a0340c551003407008900d010071484150b050070307020100c5108107800c20400340e05143e000a010103032070b05d00c01804c00d6000030024124100c950081200560650101901c0358000c49024224800c00c84202d40310901150005e25010128109030b09843c2e04105111030031400d003031800100e1650a580035050001c0e0b00c2580005884021215001f402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574724037 1250 574722787 574722817
    0x504020c0304090605240901030f06090e100b01020d0f05070b070903120807091707090207030f1d0913140a030203130e010e0a05070908010903080106030c171812 71
    0x1c240f400000440b00309401450090002d1414007061310300c1d082404840f0111813080d261a21025001240908140600d009000b030a045001828030296000800f009080300d0540d0405000540242e084800303050344035005070700441d00515014024160000f481c0c181e45859480d001007600c23080c0e24802c00f031310005c000844540c000c10600a9100c400120500a0302e000350081c20207400041c0150a1030291040303148070f01d607400449480801c078a00042c41d00380ca081d51503100c3c6d4200944004103d04100003c1f80f56101942021a0980450008030700e000b0445461603d170400c0484400c0141142101d1300504440d0303105d4a03072404c02000d6003462007940196a20903402901c0044c00807268481850541000014081128622659a4400c00000f0001003030303600c00c0c40c11100801c00f9488140702d0b501e00110300d010f143d4010110fa040e5030301500e06100c200c65801c0700b15005400d04408034040c51103c004035004240c02e80e02c1402c0b0380c2c9044e00f00d0305181e00c0c10464001caa4441040c5000d051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574725287 1250 574724037 574724039
    0x93d090302100203030403080705090a1206140108070803070f080c190201090b09030a0f17030a0605040b0a03080a03151706190903050706180b0c0d0e1207030c08040504020c0304 78
    0x22524082c0014816810702c040c50540c1416503000d4142c0c280545842c051020100702d2103055103501103500010403460401598501c401d0402400501c2000c18a0420f20062000880d24410010744c840407604074400962030030885031120640425074010856004600b040b1000310550304100d00d544000003d5103258045a0b18800948000001e40c03005149440500088159540115074001040e030820280308146145140420b9400600c14280c2c05501012050101c460220350060f0305407541901c08100101c21141000b0030081c19210081c4402070400c03180c1192442900a000c0344007041510f40e4903551640890042c0038403240c120b0456034020400c002a241181c203e503010714040c20010000400c940e1401051440341c07010207000603841e03a448089400d01c444504292039040900c0c480c2130701388000c03031240d80e500c06540d042000e0b0030205060721492021a0038131580303190811441c0303408195035059070044946c600c1920407003820b000003e1035032100d000038005440840e01031541d903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574726537 1250 574725287 574725289
    0x20d0b01021006060f050c0703050d02030307020f19081b071d13050601050d0c26010c020c0f040e01020409020304050304080615130b03010b13020d11093d090302 71
    0xb00107071448010380c950400e502002501c0d0000c2a5840700c42c1035150041c0c2d240050045a4580300c0c05d0307800144180704510b26030903010b50100140d4007420180d0b0a1755821a44100c415903a000b65040d40301a0382c0840c080c190000b11404000c11000e00b118181502c080e407400c072401d0500d035055010707200350120010800e0000c1c440d44100790b4046030949503034814100796210195201d00500a270313400348440600740d509100030030802c2c10051003402015081803a0841c00f030b1400d0783c04a85808502e60824042410719070010401040100c0c02503c12511000200e04000140c0740100620100355401c000114140e403a600055120f0f40c00350008641d10b502d014440351034990028005000b40e000383c29000803030303950100c0c4050202511140411282ca0281c0020b005041200c50194404440d50148103c1c45c02038000e8152306201500c20000240184901c90300340c881d1900003503100304018103c402c0a20444040314148248151500a590320140d050140002d03480001010070703540a400c00071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574727787 1250 574726537 574726543
    0x106030302100b0904150e033001061d190e10030c0e130818120a0b060103020403030207090903090f030b06040c0c03080609151e04050a0b010206010b031504020d0b0102 74
    0x40c006050324210b004d0f15054a95080300a00400701000c25034503411120241c00080003901d02010341443c4110b0f581c0781c15900380c8000001101080101d4031240d000080311401846601031150280c2580103c0d5840c01c1e08010702440039410764401c46100030300100b144070440090500c0f44510301ca410010504500345406001e260f540140315201d024410400108000c64a945440764880c503104d07190101203980d0003007950001102d503080421381d00e180d1a90701001a06101460050711040b00a464500c0114140c0c89280009405031740301c1d100170840d04210303a2203070110500a2034802030540d160b5010000520302a442507848903503010900c85e0500d060b1150060046207400c00e8100304505680150240300014036a03071060680b240028007000c13102110005200e80200303079030349801e5008960b03044118240d1900d4010351510002800c080000e10850070544016001041c0503843c014068940394030040010a0254030040992181c5d212400a00800d035081540800c44803420700009103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574729037 1250 574727787 574727801
    0x20c03010b030f0a0f0f020603070c02040f2f040f060c03080609041a07030f0e010e06010807080a080f0d020f0304021305010e01050f061b0a0203061303020c01051803010603030210 79
    0x480b0390001c09001c1c04480c40001c494903540e50180705c4078101d0390303541012001d000c1070250103900514000100301c0c001340d0009040000364401c5600b0016035960081e04412100709400c00c0d0040d00c400102da00300200251782c0c80000000c500b2000b0b09d4551030300c2100e8002c4403540c1c041c50200d4506074204e000c040d044940c00e076000350140c8809001e0700d000d844510f0900c4088038040156081c07039010405107440fa81000c04d8030395801c1414090940c030034010728003d102013000d412007030243c4000410082030200345a401c45003a0b40080000f100c0da500d0306405640042204003003480c04028080034015a8000fa0642d403e402a841d0346a244c140140954000341e044040c106510b8480140401d041d500350b2181901c40603142c1d503241d0407141010070710a00c01d00358102c2c1002501d6400942c1107500003542c2d0b1015100b42c4c00d6030f0b0301e0340750480000c10408141d20000c02680144404c0403065214102402c040409044010103802031040441c0c2152200e0700b0507070042c1c004800982d10003200f801520 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574730287 1250 574729037 574729039
    0x50c0a0911270406140a09052e0e04150612030c03110109060203040f02010e011d0411120f0708012c060d05030307020f100203040f14070f06020c03010b 67
    0x40030782060070450341c04900ca00c0036110040100c1d03001c036610090440180c06091600604100011915640707514440c2407080c00301440f0b0844085c010980010900840e8041c4c0c14012000903030692800880030414944e150880c40c103081218006041240070141c0c6000780d014411484c2c407503080c2a0f031107003a207809801107028000710360103442c0040c0d40120340403002c5400d880d2440c1e20300300c10901d0318094905d022025140c280080148400c2c0444603800e15030181c07003608c40a10080c0341000548040341080103150303030400c0100741e10701542840e4208030090001c1341030603860301865425503044160140c2c0c02080b1b5082c403008009445801c43d40b103601402c2e5003644a0a280d4034100800658040c2e10003082a07440d04101240d03450302c0703440070b1040302e941c4982a40d44030314180f10029540c91001000c4003c0f44038580500c000f03440b440c400c0301d000d950030802401c01085903880d0507204409030b0a580b89548201c800004021480a0000700940410340c054000503010702c0400d820340c0e5449600c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574731537 1250 574730287 574730291
    0x7080f0d0c020c4c02010605040b0312030c13030b1905100f14130e0a1b1409040213020a0320030108150406090209041109090c01050a0e1c050c0a09 65
    0x1c0300c0c0345891295200f00000d40d0940f1241e0035803a45802e19128080c0340d0303400c0c035581c50078141040c0c4c0c4c2c040d084031003903444c103460420054940d401050794840103c0ba440c400400c00b0000b04541005c5000101190310b202e4080c00402592551140d43d410340440c0c03425840400c404107074403690300602809812030303000118403413094282060162600d07110322500a50803807001d04200706888121a4002240d1042020040c030080790343c0054a5003000c4000321500c0d01000c459108100d000752545e4203654591203400ca4011000d0240504d114010b40705a80c031440b051800c4079010f003180014a20400a41e1b401b1501d400d81c00b40d030390600d501020042d07108480903c01800b20010000340740c2000c0140400c1007650f03481d1400c14000500843c803010f50800304181c200018000d0100d4840030751501a076100d000d5941d0141c411340c50702810051140080c070200901c00740f0a2140501c0c08401c02d00606d00418455201482c0c050707a5000e0b2800c0300c59030401409000c061504000010041c612002d00f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574732787 1250 574731537 574731559
    0x4060b030718090c0e100611010204080304031e0b1005011b1a0705040b03010303180803070f02090c040905010e06040b060304050c01050d0e0f0c041503030801050607080f0d0c020c 79
    0x5812102c03a600803060030703829580c564000038003034060a03940c000e008101804020b0305000c11640e0b02c500ca240202c6006c902800000d02800c64140700722800c85555201450410f0705550f02c1180400070807030707600c1040d10201d126001091049030018015060f14680c00703142440c0c20300240c21034411103001c03011903504e402c41801241c3d160078040401400e141140000ba9602d50301a14140102e402902900c540071001104268022080c0080c0c0e500d40f640428842d540d81c10b94560781c4c86001030041c032020076561101c0040c200380084a801203140c0c116641400d445400c03000489d5800d900c601000044001448802e0500d4443c1d0302071201d0035100300d40381d442c0c90b49034280e03a80500c4194504102d4001000140b4803140e500520310985a0000c0d6115000b00486981c1c0e241d51070640c4510a900e443c01c8003c01c881d00c55590030480341e01da229520240c0c605410040780d03810540e826281e0f8032041020b0b44500c88528014203440700c91010026540e003417100f0080c900010850402d001d0384030809 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574734037 1250 574732787 574732799
    0x105130b0118060b0d09020108010e041a0c0d09051605060415050d02090a0806090f01061401030506041103160e04090c050616140a05060c0909190b0310020304060b0307 74
    0x4154151400c0e165450501c5030054142c800420300c980c0311040869005c581c140c14040180c005410700c0e4000d81c0e0304070040c1d80b51b0030803680c010b07020b80b80100b004441004000d54010032045e02c55009880300692410030175856842801e6130040c04046503142c00c500c6d80811130b00794400341c0c6009480c05440850400d400c110308007980201005086003480008103030480b5080760781c0c04a600c0c1d601e000d8035050100355280b20090340c800f42a1561030203030040211607401d4100522613a001c039600c0c2e49070000258000001075000344000341071240c07c252035031300280c400402080190302882004207201060040300c0030040c40c6c0e080d000c441038445c9040160b0003003c0f418800641040e104100c0703099950b032030f0781d98441184007200c0b500203194403005000351070445404945504410301a006032009070390383d44802040c5105000f40694032010060101e00c840c4d80c212629007020720b011000042a500410021345495900900c00302c200e500042040304001e11809080c00040c0c041d00100441c908142c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574735287 1250 574734037 574734053
    0x50f01051b03280f051308090f270108060c040501120f09020d0b010501020c0117070f02070306111b06062103090a0b090a0e070f03020a030605060c0f010513 69
    0x41c038a040080080080b6046a0140040f14000c04818805842d09141011040054443c642000c0309503031924001564105840703920b509044e07480007480d80ba0002080030001c103106800e03507054000704081d441e014800c49040e00641468644810040250b160010342403030107000401d5150391100520003041aa41c1240001c900664000004a149145002801c0051403c4803001e58403035280c05811040c04150041d2038187c510a90a540300340c8c1212005444020752503100c0145a00c180e0000348603c2d1007002c001d1400105441900c1c4070966030346500301030700c86980409840000000b008a174a060b40090f000303054032048023400c0305223054030000b07035101070b1240c485000d510300c80ad801e80c10340f200748122603403090014020000e481d01c1c0c071080c010340d40081c1a040d026010b4103101080484807002564821400c40d500d85c00451480a000c8002e5040400350f1401d2644608004c10190b5902000d03021400c0f000c401001d5541444030740301c1c20354501821483c7c40308100306a51000c03031124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574736537 1250 574735287 574735321
    0x503040e07030b030316060c0c0f020409022d03060f01060203032a1303330209030304030b01240306050d0f0c1a03160806010c0b0601030b031009050f0105 68
    0x104055803640d03190201900076001d80ca003082e606000c0051042c03100d21914101c0c0d032001e0b000724000c000b1822405001c0d200d844501d80050f028004203001c040043c503050300841c0c8140e01c0500791001c109188403c400f1107d100d203100c890a4048800d0313072036103800c040120507444800003890107899450540040d40303a1101811480401c441c003980b4081c00c0e05d21601c894054050908281d91390440080081800781d9580000c8894010001c40b40090701d54191480c01c420441a844204048a03907400714002e500c00c10006030980070500000011403c02074a09008010010002814011703281c0c1c07c091070a107a000e80c4051501c0c10009100a45495019032043c0703030311078070078a150758140c02c0a1291703407015800401c01c100013222508038221442d02960041d24408615040020100c03815034035954105c9100c3d00141c10100054003083ca003881494000e4010b0400103801c0120b880441d08281c242023a105000742c40c0c904242c1002010005114000080700081140c0d09080f840030814880c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574737787 1250 574736537 574736549
    0x103030e0d02060d02090312090907050a0e04110304060507030507091a0409020a031d061b0d29030706080105090a0504030512090d030b031b1504050910080705030703050304 76
    0x10480c15412621403028090310300360001c00072600c40c0b108400007000b80d40641c0076a4040e018003d03641c0e4004030910191140c00c0d03802803c641141e40e07007460807162a00004085800c101d802000c031002c0303490382d03c10f082c000c104010803140e480c035050038040e050301c00160090301010b00d80702c20890341503440340c244020340741d40040402c0100d03034580c000321090084c1c0c0c001c102c000b4400a01050055090fa10000714811000d109a40700000d440020f61607100450750751507481903500c0c08058500643d0002e080319441c4003000101d0000d5038024035004440440c5070310f03c4120f036180d40d086e585002c000b064024141480c1c160130542c100004a079501310040c10b42c2135610703242e001160415000300300303440010502c10b880744480e03d00820307030a0303540312040f51241c0800c0c85c00101d242e15040120b003c1c4080c540a0002402d004c000c28144407040c608080b800203100000c0c00003054560703032441d0745030289600100b03180219061032152410b0540ca54071861090703015050400024102005880480b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574739037 1250 574737787 574737797
    0x2a01480c1511060402010f120509060601090519090506040609020d0501090b03190209040f0b072606010503041103190b06030f0706020d050922020a02060108011503170d05011212030c0503010303 85
    0x1c00640190f81c0f10003040b00c0c40308d40c64280b904001d0300e001d0014851b071040c0001d81e143c0145680e2001488031966142040000070031060078180a0030000f44c0040740c204c4005480040d040f69160b00000403078000320001e01e815a00d4100411445841d4014602c501504a000d48010580c615406010781030311440203020710440130000702070200741c1070039507105a0444a182a64902040e0091000380310202c0d103550741070b07800050f02a201c003014042d0311442041e1952450350300d9680718521180841000710740e2500c0750300d40040d058500303514268062441201070426a0411000301414020004800c00d1141d01500d800c001c01c50b4000b0b0518032415207420f00300d94409900e00403414403084201031601c200442d405020022601c0e500810307100d0384980c255034203645c994508900369000e05502503101c0c0380c0c561040c00460760380c40d595607032140103c58081c5001030185200c8181c071400d0b406154003806488031601800183c401c690301012032481c0070003403031032603400103485808180030181c2080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574740287 1250 574739037 574739057
    0x30b030d1b0615172802030f030c03040302120c1809012909100e010611070f150815060301090b030f2a01480c151106040201 55
    0x303079842060680207600408140150b000c00d402c0500d0f011440e10600001c1e222074160303000521401700d41c0121028084d103d1307242195455142e0040004414000d071b915014080e815101c44804100a004c2130130018003a42d280c80c07540c01042040002e51141c03102a400a4244143e1603817400c00a1070001e81c84019441c140d1141e0b041d9a005180440002c090f80e14100ca480041541131720960b040340004540c41c502a03903403040d041c0c16241c03440c405e40c00409491001070040034081c034290303c1e041600c401240d104640d2020003085a02c110f51007030350030000080d81040180c2c0d002c841036510580c8800d10032000000302c4042842880b05100310090f0542e2580d9405a99800f405001450b4261800b00c2d20250960019150500342c00e08110100d01018803403020b155018441d0071242c1e014294000c0306102c2e00e000b02c050160740c0007040001149040801803082030003010a6a9201d000c5c0c0000f011140c03e02c24078012202c1d89920100912032200e80c0451042030019410303900c0b650a02e0321180751 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574741537 1250 574740287 574740317
    0x10311040e01030605040c050f0f0105180405040b01060906020d0507110a08030307030e070f0302030c0904170307180608010b0a030c03020915031e190c0207050a0801051501030b030d 80
    0x240201c1d00104500d1184000010a03c059901300d1406103000d0030381c28041c1c643d650304201c3c80d0541c0800164021000076040481580108050305809a070084840212203002d40082c040b00c0d01101c040340c16008074001030000c06e60005107031024003c00d00050400d000980c002820a00499100900400c0720354010b5805032201409080208a2041169201d0505d02c1c03014001c0c285d00c07110303002a449043e20025120f1090306c010f1084039005005803028185140c1444084d0300700400aa546030701d1a41c0005050054400035803040c0081d5481d469030629040c2080e005031b155074800020800064010300c4104d581000f16081440309050014101041040c183c3c0640619621154041c0c2001203031040a000707440110b201b04510001001c40450b01100610410401e480c400740c094440c601c1001080c08070b51200d80c0d60030b560300403251ba070380d69400000c56000b1560070030622a51034101b1700c00307580e110580003640c1b190242400e000a07100740002c00e5490040c10844070410211108143c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574742787 1250 574741537 574741571
    0x1902030c0a0f170f0a2c01080603030903120d0f1407050c10020c07050316030b010b0a0203041a07031b021e150a03061a07020d0b0606280e1801050103 66
    0x2095050fa04030b03921003125054082d02900404011004108000160900f2000344031000000700d0766400d0206c082d00c0c03034a00447e21558018491500352001700711510580c1d40420000800f5018100010b680b24200c0400006954152610501081c01e29180c040391202c0304a02c954007200324038042d0741714129202c000f4a00390348810700110132440040d50001d0a0408584074041d42d0041d01103c2d101409415030b80c03190050b0f444090a4040802e00601010010800800b0b4100075841207908041d01c41042428a030f030340743c583c07440175000010480201078220340303204044504421000810907194000c5520740340d68043c41510040300340030f101d450b0b507204503445920308a400b100307a4031543c0340c21000c5c000301901d008420042c4e00d61f40b0442c2001d8421022500f1460740a01000d42050840e501da01c0700e01d10113440b4650100041c00581c6d240400c3c0504481c0d8044040c41c8890a140c085202a28440100d116240241c8644100f801185080f120a41c1192002c1ca400141d6001303014102c58 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574744037 1250 574742787 574742813
    0x100b180d081e03060a080601121202030c100912031407031805150a0b19030201050310051e01110d1d0319030809060c0c06070c03140703051902030c0a0f 67
    0x180701442d42010701c000182c0c24010318451402903403000c0005071076400055850000344189040c0e40d180010000c000b07a80040c0315202101d40d0300440703050803100010182004441070000c40001d555115100501100ca609240c15000d50704040113120320344929800c50003002042d08007810f84903076041e060705824004c007900058015040d03442100c2d980d1f0702c0d0950f1b1281070b44e101440504261242c811071030090300f031002c2828100702c4000c00300c0c950740c01540c003a003004104901d2103030a000e0014036600c416813081c0180d245182810312028001c030001d4040ba42040c1080900d03403107162001d030049d07001007044152000300c0d04035a1900400f28002854108140562000c8a1380c0078507903400c06030401c1c0b03448d004910f10030a64282e540d900d29014101d01a400301028113600c03031f0010824031405122510134aa0003441c3c4184058844110101740740e00a18003100001e0700010008486050000b0300300304104d461014600d0040034854103941d03000642c501402801080b408030b410800d013000c40203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574745287 1250 574744037 574744057
    0x206030a05091e160611101a0d0f05011505010507060902030316300504061b080a020a0302071a2502030114011d040302030a050708040e010e100b180d08 67
    0x80c4001420302070941e1511340c0341001640000d101c02e4046a10b901402c0401070003060f1400030007840b41c82038a0100a050030b0841e0711800c001a41d58030107036840c0c40c040903640c01d00030100c54460408500d0410b00315250703542d903000710014409041c840b5030703030080c1110062030b08101d01041d103080d1800041e0540c03043c54180c95902e40505049010030401c5848401c8007004140d09038200621a610f04855062040701c20b400581c040109001281c09901c2403c841c1032400e40003800401c1c60766a401c2ca0b54031600790f44000da03114811003401c01d941001240301500343c101034044d141c5522030544039540503004840b100460400c1c1031a85e5174103d51180c2c00c040d90010028030140d0145003d680f04c0c24028011200e0740d032a003074240b940d49d8002d407121501030f640c5035009528100441204840c40c1d040410103c685010810000804814031189135000e84201c2000c1c0180f03003000e045140c3c1440140d0700c1800e00301c03c10300441140d1603c1c10520004040300742c070181c034080319605c0e001c4414400d40ea041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574746537 1250 574745287 574745323
    0x40204030b0610020106120605040311070b0d15080a0f150609052d0a1109060705060a0c0906080c030c04170c030d2c03160825030206030a0509 63
    0x10a000711a00c00a0003010159120303819802c101c0e500300c0c01d0780d40d640100d540503500c4100719000524964402540035019243c6044c9410768041000e00344155580300f00d031850400700b00c2d6080e1000500c240040c040120114401107840e0400c030325140da0781c0e8400034143c1d640c0b00a03c1c8090040c08a500c1c02d440c800b4200400ca80d64680d0654002042c1c162086c50070100122407000509036014a1019110541400c011199440061181c094103080c203200e90480300500200c2480c2d114400505000e9107c0c40c09408185400060441110180d030b0b0b00390100623060208002030ba030065101604141026045a5a03507a891500603240c41240c0c03241c00525250654141d00f12804501042003501c00c134103456000d000c066040340c2000e040003450200f109407080c1044008590712516031851400380950b00312945c880d1024140e01c0b45d9601030350168000088060340e0541c4d10301880140c884100321100c2590441c0c001c11183c0c0001042070708800e6581000c40c004807000c1265503803441c2e80c034002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574747787 1250 574746537 574746539
    0x533040b270901030b15011b050102040e09210a0c080c0607020c120c04051905130302102a090b0c070f0f1a250b062e050c010b040204 59
    0x1241c0301d40d10820010010703595a40252541c1c078040403501e04032a0803508514a5860f50b02d00700da204070703001c0815414031965a2000382100340a54015080b24001c1d0001611149001211141e04000070070452050700306a24903e442800003211400f40c440c00c660203034441d000b8174026039800c1d8100c140036040b1080424450381244001600900c01c01da641d096589145e0b6034024401070740990002e400c41d03a00074208015480c10540d1005500c813046010081c511940d00992340129070782540c031040341507030700e010400c03c0c1034041200d44810700322101c0800050000507070803080484a40b061942c01040002d01042143c4944110702c00350242c00006039440d48410800d607501e103640e101d031010541027014001800551070b9098130442d000421131041448610890f44140c1e0f0000c5d01a01030421071441454503009407003c00b8442a100d5958803d00741004400c000c4200029450f502c1802e6401d500c4074140d10704600c500e45075080a0605589500810035400d0140c500c1442d00e0350050b1021034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574749037 1250 574747787 574747807
    0x5270115120303150303021b15030405010504030f0815010c14150a0b0607020d06021b030f0417010504030e010809010609111b0f07210501090303150533040b 69
    0x791901520301c41c0d00c040101d56600c2031920340e0300960303210240150b040028440400072a040301c1e22260240181040c2d00030402c0c0c0e0000c42030381c005a0b41a500c2d60340d01c204001c105908080c0c201160091400c000d421894030148410050080500c160704014264210501b00035410700c1d10310002d01081c054556030b5401e801400303451801143c2c00c080e12401d18010f417a050422400702d401d0b03a6000303842012981c10680310784000e50300001c542138081d00d8601c07605c2100362050001e8007103e6002d402c0e03e030b40ca5181842c5000c58103250007d51105034540014800065040f441d001040d01003030070611556500c0112041c01440d043d0f100300703492401c2510081c50071f0028030081501c42c80070502c810b80802000089070361034024000354801c55005407002d010314116800b124052071203480b980850080a0303554507081d101169400c8010a4484200d07400190103500090003901040d600b01c01c01d8581031100c1e5860b41c103805016407555101c140c4002c4086a24021070f0054510500059955a040c030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574750287 1250 574749037 574749059
    0x20d05060405010b0f031011040b040b0910031803140c030d0b030616120e0109020d0515162c1c05010501060302040e0a0b0109080d2105270115 63
    0x81d07040790554644010240d82d80390401c20081ca079a80980140302c000c01180d910401001c9520318049110400e11001504d410b4400003000541074588442c0d0b180c0ea0400706200d005030f60613940310305250801002211507180e94500800141d010f1501403240c00c49030681100320710601da000d07415800009101040356189800000c640d20082c1c044402c1e9a03204080c00c580d440c0404a96030000f009030420108801154016154030081e1000028410b80960b0000e4030303915080008503159000030a86005012041c0d100550000c080300e44c1e0083c000f1039030002410480400044103443d8a403680351048082450000004500080c20b042d1441307501d00c4038003a403400c502c081281c4a40c200400801d20a20070300a49048840813410301403251a4040780901030452200858100141642c000a01ca10300f00300204c6400314540320394440c0307c054884c0c003041c844c003281142282c2e070805060041803000100c0c43c0800d9524460600c102c1000942c04a0140c801044030008100303001c940451030503248 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574751537 1250 574750287 574750291
    0x415150602070b070305190e03010c200c09070f090801020c03030f130c0b07080c070b0a0905030307050303010311030f2e1808130e01031a0609010e01140d020d0506 72
    0x2940840790b00301c3d0b07111a4000c0b240f2a80c42e00800141084c010000c2400c0d20074041c42a41a0714180b2110301f142044c04030f401c5032141c103030002c001007075020f403001d001312903507200255a0078510142443c16114808241862009880c0c0c404200086410844141c03007129940c02400c0040025503466a842802d01d950340c0050b02c11800d0800102e001c208070515502c03401407110350001c14408503900d070081442c500e40252800317940d03030307141041015444202480640094030705c2000b09500e9140c041801001e00001d030300280e020741c5c01040041c3c0031850000590341100e5021030b00d5511180140d002c00d04041041191241601c10f420211000c00c07024682c001c0700e020800703498482942c04402c0300c416030744003c0301c1c00d402030302c12310103240031540c4e840080c080c0e40281508130a8503591405440c4107030009900581c0c4e00908c3e8407800c0c2c22412190001034001c40b0442d0b0080680d41442402c590301481803040c02010104485000800d8440d1824140d0854008001000101050a105856140c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574752787 1250 574751537 574751549
    0x210203100501150503040f06231303020c06041d0606071b0e060a0e0604051f030f0204060609060219150504080c0105071e050d060b030106020f0c030606130203041515 73
    0xc0b10459070f8a4801c00660380f04e2500040e9002c0c0d005111f440340d40007007400c4c0c2000401c08508440c00031800401b850311501a9a110303074100c1c000856802d000b41071070b10b8071980d5031040c60200b0003044403610a038405000c4c11920016401c058907040c0c0040c1e164447c0c00c1c401049107200c4c0d60150f0384001040d40c40c070220780e9041c008003003580d9840b0400150001c24001e07401070b4504400401d010741481da0120342c0c00646004018030707200d16111110341d2081e9a900460320502610030420840c10180654402041241011400036042603c00f03500d45003402c4400340b1035000c0c01d43c00010321001401542c0e401c60384c402c0c01c105504080c18131199580c00285c02c4242d82d8203206c0402c0920340714075048414100780c0040c080306500d504808031a242e1000c008500641c3d29504003280c0c0303450200045000b0119a0014500e61081031200ea013096407801ca01c80c82500b00c60100a074584a202c030109051900d07d200603500d41e1030f0f00e002224404801c09a10742503150000c025503204001c4486070585003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574754037 1250 574752787 574752809
    0xa0515040801240306050406141003020315060a0302280f06031b0203040512010b04061d22020d050f2e061d1801020a030209091f210203100501 63
    0x540205000380c0f980721007614007182e11a540d01003000c1010390f408260045c3c82140f021608074201010240d14500503162003135200c000c075404208620f07080003a0803401d00310b075030f0b03408080c13600e4400916810103520003c1d002d4801600320550f21160101151090400d115902c0e050945034103000c147c2e20418050000843e10b00118800032801d010010020700f80135a004601c0c2604050503c000c05040b41c80c0301034103640300c031030803d519606e84c0141c1c1d002e010110310101304229138401d51891400c1c0580000c14445030481002c41140003400601da002c0d4043ea58107400c961586007541c940508000200103500920254007120080750303840852401c1c01600c211903864040c480d09040321751a2084200802110841c0000c640403a280c0302d030312402410b800d100a05002001c0d9082ea40301e85007850020341c1c0050341910310b16241c4002c03600501041c002d052844050520050340358400e0203145000c03000c0410120003009520601c4040650181c03d9030b502c50320040c070044c043e140038080c42048076 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574755287 1250 574754037 574754051
    0x703020630040213021201150c170306150f09102d0801090c0203090415030f0c0e0a0614040e01150605180603041a1504050c12150d03030b0a0515040801 67
    0x900e4002d1b00c0da00950252014401d900c1c0007003080ca40c0f89103403985020300c440034100700007080188081c0118140128000d5a4034a802010090024026000b005c801c1c0710a01c00100703c000c421040d105182c4050b10340c00541000f0110955032045152003407055100b0601035200c56946100340b06480a80319182c20a01c2c2c0d0b2a00403400c20307103006c0c040f03000c0141d0060001d460780c0e1825400c40d401584445403403101c42d0751030382c80d03a4142c406400c200b41c6032a03888500400c8086a03d81680e940007200300000c02c070b9239052a4503401c10f51403440e1290320441d07e5004641c1507520a601100030110303030200324807203d40e9130300010b0001d802451007040c40070f0b07060070f8001d4581010001c4030700c25070303100317000701442d812000c0b9071200c5076005002c50010300080c07030000c5820740311f610800340110031407240503440342c064402e03607880300030300402034910380d84400030794030b400e480e90805142000ea0508011414681c00c0e00840c1045146601480c0d0040f0302040d00310b040c5000320000c1040e02c1403c00288085 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574756537 1250 574755287 574755319
    0x30522031d01050301080a020d0c1509060e0a03080d1a040f14011505040501050c010f06061d03011118040b06030a0b030d050703050d0506011b140d0c0507030206300402 74
    0x11340002d00c1030400320341201c004107005140c84420311503040d100301601d51007251240310000c0881003c3c0c00341030200382900307420b0103043d4001c9609903280c1c038202c800308210341c02c4d0383c2c2e402c42a01480001a500544490030080000381900558500c10405041045402c071091141ca014111200d480b50150f103000001052a03c1d09117031800e8401c515443d11413800f8689001100d980d88011500d040c95540c03084829040d100b140540c0c0b00070300b03103940e5124165030141c14482c43c401010300854030980c90102d09000d818400015600d070300034002040c040301d20383c1c030f4003017005071403403404d4070f64400c800004000030700403030b94814082210290102c51901a0030b941c15661441602c00c054040b0ba414440940103000c507800c041e0344240c0602d0035031152900c0950903155050000c50403035451821030700d4070340c81c0c8008002190054445c3c1c0380245213000346860f116124005400040c1c0140000515000501005100c2c41070401040c8014000e40c1c5d10b40c5c0d910380039280140c40480c40b410000c400d2041c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574757787 1250 574756537 574756547
    0x10f020901120203310512090a0603021903110403051525080c180607030c050606062523030a090509061c050c040c03051f1203030522031d01 62
    0x22407039803500005c031061035075000c08100075605120050721041000c0c415002481c2032000d60048038421822a84540103003080010140b210303004001010710520124070300d006010a042e440394854100020200581416104a441540c00241081c4141050f050751614408245440303106408603c5280000346408403104115032004500010161000302d851110220024039500314100c142c0e4003000040404154030340c00ca02000e501241c61540da983c1400001d20095a101904850043c0b42100d512070f400010445070201d4441d6a00712913a403410400b9201d003040d6140340a00d64070b4800f10328400150b60380d40c0100c48820004550030800076050916680042c0644001040d0007080b0842e41600d501441c40041c083d61130344100c00c1c0400040e107840c480d19858440981d404111450641204a4801400c03200908101e525040800042c81707081c1951110b5a498500451580c441d2001056403000040e03048a104529210700c80030150011030007800c00f80d04d03c1400f8100d5200b8001520 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574759037 1250 574757787 574757791
    0x1508071203080c0c070f08030a170106020712260c01111216030609020a05040807120b2202060d0f0506180109230f010e010b0c030a030902010c05010f020901120203 72
    0x100e00a04003003034030240b004001c2c4ca00c1038820703401ca840c0540e80c3d4510b100740001036400070019400016115540c10f03800140d10003e680701440310384095140a10081d590320b21403040c1c0c6081105c11580104220400b08402c02d641140004626106241901e840c0d10358091700385d1110720b601e0040200d10b841d42c0034080e10002804900c0d0150155184402100c1c00ea90003514207081640d90080404e0031075044c1f0203000d424170305a5400303884e1800c0989142c54403a4981125080c254444405800552003489542c0d014181c800110000c949c0503001c50002d088011000f58044004144881802c00355400b070590b002017200d0a1240d501c81c1020b0005a984149600782842c4403500103000c80b64241c1c00000e0707000d2103001e4003540408403007544403003000c083d9240c60704950114010080d029807100024058035807800f01601e4030152500103540d0784245102d01e030a01d034544440318156030280000c890700c0c1d90014024461104d418100310000d50010a980d4045651904466010015480ae83c1c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574760287 1250 574759037 574759043
    0x20f0615130e160f0f0806041709010c171e0304030e01030203150d1202011b0c030305220303140907030203101d0a0303050615090f010f030e0115080712 67
    0x3000411407280307201910902d0b12205192090808401c0490f2072841c40b000140590084090b04904040e40d0903c82462075000d4582130307100c0010f000104201d003201e5a05210b182c1d2409940d02d040000585035898840805440c000704200901030180701e03800141600d0321a2207032103524001c840d2102d03902d404103940142c0001c2c140e501003c6954000c0e801560011281880180c06130090300c001061007298600c05c880041074242050342e4944c090183c09180038502910000c0846081d0000b0400f69110f4400b508040d01c50001c1103d14141035545c00304024020400c10900303900c0d0401a000e4500d0350f007862400941d90300050440140070031703884140d0f64020041c00c00360110801c0c01e80a4810106550018124600c011a80c03a00801418107264032030344001c101d614000082008400c945a003071260364904101c0c0803015a102d044203141d180342424503246501c0710410071030003085404d000700c1056280070041c0e040e5a000b9142102221344481c03c039482e26803502e01c0301c0301001c0a02070007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574761537 1250 574760287 574760299
    0xf1803050306091015020f07270c031e021e03070203040303030b12030406020703060b01030911010807030b09010f0e06030109081b010e03030f0103020405060306040519020609040606020f0615 84
    0x104000303141540003d03803c000007030035031988152030703564442401c50352650104c0540d20110359010460814050070000309401d050250759a20302c0030f004000c0305a031603403007000d4617034a41d00d00f84454043d500c90a4108058a503130b401640d164203894001b50700200d402020b0445c00070680480c807045504030b07485060030b5406582000d1465400f9405000340601c1c060340f00706000d02c001601d600400150006208690081c06400d00d0750800000310b8440003147e40c1054105142c03500400c0844041100000c000e1808074450741e14404c044008203c0b0454031503008004000004104204075981020f6508100d01000c150b283c8000f09800ca44103000e009209100920484150240c5021110b0003103000000100d410b0025a6210b410f5501c2140c01d40981c445d190010b20540c1003510855520100580041446041ca5220f0641d60740d0300a1019802d11480d0700e40008548415007500c0f103098000d041803110035200c00c00691a0328018600c504e551140303900003203541032030354801c2e01c04860203818 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574762787 1250 574761537 574761541
    0xd081f141e060c01050f0f0601020c1017040605060a0611070312050f0a030f060914010b0f040b070807020f100c080f1c0506130b1c02220f18030503 65
    0xe0140d560aa240030900604441000201c541c940d60000c00421a00000008107850104003014100c50060004022031260004000043c2d0700000d444241120442b140c4002403440303602259503220000444090740300c45801d21040140070b8001c0c0d030160104580400c4400d0f200e490441d000b001002a112040d031000008001058500b1a0b03a1051074092800c140740032681c05840041c1d038005010302000990703a12031a02c0945581c46160094a08503600703100c40c0d13071907050074144980180a82740d44894000f480f22201100b590131a001001d1a072103071500ca9446060210064106400580c0581a410341041462414020b501303c004055200c1ca01034524948548a0035007102c01c2c90084890100030f80c5e01e2410a000420300100780030580400c0038030704202030041c1c1c04e01f00304d01031401c2820b10101c4030007aa2401515820807000706102d24480e566400010310040700514a005043c043c1118020704012a400041a114103d50244040504c042d00016031640d1814043c000a10600c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574764037 1250 574762787 574762789
    0x7080313050d0609050303131a0c0a0f0302090a0f05030c1909020702030a06062d0b0906070f020402040b031b040506030c0a02011d2406060406050a0309050d081f14 72
    0x6902d05401040002007035041070340e809155078400e0750703c2140800441c40b24420060014080e400074030119561995a08040c4d100f40c000d401034036400001e0240070f405000d25a0311036410381d461410028040c854980e41c8101500c0d4036409030213420302030b01600400f03074150305003074040c40303107070205003400ea4481031401809400a40000d4012a41030003a0000200412018000c3c2409000044104c0c03040c40444030400f01c1904e070100d400303012802d0341c40041003ca0100000d542c640c400942c2c10307d0380c81c00c080c035001c0821104154020f500c14400301e000b0a07450800c2025501c640f141c500c1c404ac1c002003030584c846550107903210307040c0d00910820018000340c0c02e40025020040c0c850001052280080600f0768848c00c59010b00b1003981d20900d41310f09003214544090040a10030b075100348007402c1001c085001ca00c20b030700811050080c00100405414820b40c8504060798000c0c0039a21200c0d0344450051051405951b051480e840300b0400d4010010084207807002c540060304442c88a0345020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574765287 1250 574764037 574764049
    0x729160f03020703080f0a110d050301060c0c170d0f0201110405040c0302122d060d2307060804020f0319060b030106031703040201110d12020d1d010b030708031305 72
    0x40022011070207005000400204c0c3c1c1c20203080c21140b001c1101c3d8847d010b400009015041c00d00d600210356020440f401560740c1c10a04407419030ba0075140c01c401003045418110301006682d80a880c000b1700810406804440200300410105829591070b84000e10f0384178103d00f62211084007200740d940c10001008245041d60103000408140d041c09401e04d026245152221942220362031f40e080c440121003840c0400548002c54890b100500c0342d00705003401d401054905003030520081c81e103d900003010101010540b101642c0b80480300071030350369545a80004202c10000c1d03130100e008070040d85148645141c0030032084000340541180b03001ca0760701500c4400280c103114a51542555840b8000300c0480e800e10119030028450003c403540d6030516100040c1740b510203200c1002550000c1c2041451305910101807101403107030020140e11010750304040e00003000200c802403503608501e54044003000041d004980010000c5058440040e981c440b4640c480c89103082e00c80d4043c520110510041c80c1c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574766537 1250 574765287 574765313
    0x6020609060115091e031203150902091203040305010b0102070f0e13030e0607030c2102071202060d0c080702010f02040b0a03020c01020c121207030204150c060e072916 74
    0x7a1038550242075503916500c0d501c094200383ca40c40b46103800006c0c000d0004001d900843c0c40410b1a0400c5007a07817150100101022038029182c811b41c00007041c1a01d03542d4030300f840d40c01000a605981e500e6541346001070082481c00302141c058051401c00181c0c10f00500300038000c0340d0210301c0e0420156549a80d0b110b00d40d00540044081c422107080b60341c581e1f01c070100a03080346486912141d0102c0b1081c1010641c810800111001e803201c25461918850f0f404100c00f4226901d501c95007101c0002d510000d00d0070702603081c406010900c1c0003814000140c0c004010360051001380c000300103400d41c00b03200009902ca640607a11000c00b0800003400218882e0740140110762400c0001402c2414600c0d01c0fa04141200d003800c8080c050200d00b0f5883c10344400500c0c1d8000102c1d043c214a440e140210800c40d0b540c1d0030034003c0a0180075071700c56050240b507400504d840d084100546402d9030b11000e4019245204200102603900703804480c4015155483c101e5641c07132441903810305008106d950300b020901079 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574767787 1250 574766537 574766579
    0x20a0c09201305040516091a0c01020f031806010e01051504030501020c031b0304061706030a050f1b0f06070b0c130303020a02010e01020c0a1a1605060f01060206090601 74
    0x40c268488080c610003001a10707000100e9100c28444a1901c003c01c000e8075006041c80440f46c142c207902452290300044004c0c112401d040c4440c2d00d00000c0349200507640103a1814102c25400000c6440070340203c1301c02036101c0d003400b0070704452103c021f040940c0e44140074020540002c1541e00103005038501035a10002d8041032085480c03801c0d45030707504c041c20790b00803183c240c106070b0000c510420101c03c5031081c08800c00100d0002c608180c9031030780051103c4081070800e004014660081034641c0c90070301c110400c0c9900301045500d1403503807243c65a51009901194040340101c81090005031811940d034007603400c00108807a00700300d40c580792401c41080250a001200e6401c10508911003408001000118000d4010700380c007401500014048a1034a0742c03041c11900110800340c410796460b00310300162003013101c0f82c3c081c02034001401c030482e206580888200f00802c80c01c05d010004009007803485400b0500d1400d000d6661840c0a0760380da0015102d1910b1900800e005104400c981e80d002d94040d89 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574769037 1250 574767787 574767821
    0x16080603012415110601090b01050d050702060106030608012c25052e0c05030f0f18010306050d0803040f080a030c030b120c0d05030906030124020a0c09 67
    0x110442e20300c1070b01c0c500314091102c2040349001004001d40400070941c1005032030070f1007045010583c290700d8031400140038100d0900c1d90341056080c075034030441c00c1d6402424400f17000c01842c1040b00c0046e41d5440c0c240300d8400041c1c01c2201c040b43c01c400c10301031000580c5d00c0c1508518021030482400e8665403000305400d213184500c503518a40301d0320708524101d2100545d240a030f003e03400c0400744489901146514403034014210b03003461190348020412452103d103131421005901c02451b0141c118450740e100008415008a12842c03070b0a010001491003038140500600110780c408010b4041e55440c3c41038551165044407000c010400e004000d65001d4401c843c80307042d10140780e0303c229003034001c0c004000004e40d460004a03003191f0140724840c1e210030101c3c1c0c445251840440603903540ca0343c803070109003da1264040401048001c1058910800300205a55225070f11021804802c01c200b2901500f041410310f215241c8a0000ca00b020a040d0050070345010705040c280300102414114214040c440c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574770287 1250 574769037 574769051
    0x8031309021b0d110c03060f01060c14010606020102181804032109060209041a090c0a0e040615090b0f1e1204152a0305090a080c061009051608060301 66
    0xc0c014403200300c3c00c8555443e0f08034140c61020003685800d00c4c4d42c001c60301aa000c0703001c1c00188884080b0060440d001c501c2e108481c001e103440c080c44114040c2901c90903560a040002c00e1164042d009884091410840b105100e6060410002c014400c884544446001c01000c035000c07a200724051243c00006101030840c0c00c043d03521540c1203d000c850705441159020550000310b107494040c80810304200201c6595001500c000200d4103200038106600c2c02100080705c28a9900890203811384050050040100303603511070504420300b90828030740e00082e2400030301080c82030549040e640c040903042c107180d06004107040d002840000602032480c09039020302c220740044908417030680c4151301c520340d4003c486030510740c00c10039a86100b20b40c01003441d420401c1c4043d83c0042c018042c0054843c6004600c580b42c00341480d04050b0b9281c0c0144c1007490015100c22840300000707019000e0400354024180031990b44003003170100d400540388000380486034a6031901d640c0c4205a05904120300500000b061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574771537 1250 574770287 574770337
    0xf0c05030406030c0801050d0203100b13050903130e0f040303180203031321021309031b12120227030309041a1e09180a0c1e0803130902 60
    0x5800a60100b00041c1c2c0301c240d90029650f001070000e00401050301c00110094190340040e8943d00010401c14116507200110105a81c5011044a80014003602040a420041034107600d85d400541ea03188440c454190000d80c0020816115101d01c071000d0b0b12001a41b0380e598120081c0501030320619500e0a050102c0e409a80d06100818011032003c040000312403a08143c412060040740540340c00c102501040c01c0943ca0710040703c1a800f010300c0000603c2c51152070141c0302d10407044200785510b40c01250b20720401c4004503030480c048916844103549800d0122192040c2c2c8101c06a00d07401483c0c950352450f481712651a00b036440308006042d682046100c40104081300c130046844114605044030105460404170b822003101403500071103404000c0030401007182450082d041601480d0341c05c85804544d40c007400217003025948201c40c4e40c000b40c8e444c82c3c04194400c00c014030102d19600d1210000d40b031a400002c5a031800c20502901c49072500d0280e20034002d401c00e0b400300703000040303516070000c0e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574772787 1250 574771537 574771543
    0x80f0c070803070f030e21070816080a0e091005040f0f020d0c080a0506010c1203061a03040308101511010b030a030918020301050d1202010e0a05011b021c0f0c05 71
    0x1080c402c030303950a50b2007804814010150380d4291980001ca80218508060b22450607c0c1c56030300c03d0b0304483c03140c0d035a4140c1c9445c405500c21441150a201d02014241c41006028002044040314a41e59420608005800c000700f00070191443c4003400801e050800c2181001d800626101c4003114000920782c0101c031040c4160b80c080c208010792141d444d8840001d42c0d40080742c85030000c143c640700b0044c520b0130b2030000c0c0c59013030184006845180b000c1d44102060303201c0d0704481c0140a00c01c0700c2802189202c042040385410541d01100488c122400241400e44403403090001c8680c0003050078482510241b00381c68024011650780425501c0b4011042c40d91020001e44074410b00c269100c0124a1400503101c440c05140300f9000e11913801040100b000d0743c0d50f124000e10140d0051150301e501d50011106270300509503038101c41500d009400c80e2200380081075120486440510381c40070741e2240540c00c00c07a103401d1340028420f9140d40f000345103142d452007a0100143c41540303080c050030440b010740381c5501d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574774037 1250 574772787 574772791
    0x60f13110913020c03090411071218060f08040b0a180b09060601090803180d020d06050f070201020703090e10170d02071208071506120302010207110a0501080f0c070803 74
    0x903024a00040803201d5003060000c0c581c029100b07910450500025010030343d10303885a88040340c46591694820000481c1000807144020b45c058144c01c3c0c401920100a0212008240040c1041040840002c0d00394001d0988500c00b00c0c50f07075103000c42a0b8550341c414040400141031545120355412840d00c907915118001040c03035008040c0741d0050310300302c41030a10f0030340014031841c1000102e2408010744c020001c19030b41c5010405151641031078203c800710341d42d21401d85010790700810141140c03017070000a90203640545261001ca541d0303179a03120000d071709078498410005c000031b0119004206190251144a41000c0e00081443c0840d946114200300107002c88a007105c503401040c4200c8045804104031401000c100303419845120b280e0f15010940c1c02449005402d40c0e10341c0d5a0ba85104030150b0102002c2c02080023131208a2841d0f082c024001d4009075001c9a21980f4940e15018620b89000e0450403100142e440c5140384e80d45100d2098440c0019000c246454400c0c014200024130410240d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574775287 1250 574774037 574774061
    0x190c081603020f0f120a23030a020904060b040b040308030405070801140709050a03030903111f030605090a02070b070c0311030a0309050618031e040905010b03040b0c0c06060f13 78
    0x1c00303c41007481d084c1c20b01100d080d4460803035014076501c0c09812040b02c1078608140d01414096070301c1d41903400688400082880c44c1d5200c0c00f00200300b00c01411a54041c221111007a641086000d03155084110315219500940e228818140002c0001900d0100110b600c00d2040e0152601c103075403011420b00756000c40d5510a03041449008000340c03942d000f00c0d00d03401003c00310341090980e451520040e0450f030381400098212143c5d8a040786803600d4000d100301007240148a4103000c000c0303018000303005048078000c503845030f40c115010030b5081941d80280ca0510303030014404103081d1a0b07013009664601e00500c003101880701c00004c041c400d40c0c05001801e440c400d15200131800461a280583c00c00900800b00d02c20352000d00c6404404c0f00c1d0000540382c28071881410400305c50a0703464003080b280220750042a0044c144000461072044401c00345014501c079031203103d03194480386e80e650b125014081c04080745500103000140a46840c0156044908010b4514181e0180d2281d40c40140e50000c1708031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574776537 1250 574775287 574775293
    0x602040312020c060a030207111503221106030601121b1e0f110a021203040e09070803070b060105040320010e010e0a03020f041104060c17190c08160302 67
    0x10018000207407034000c041180c0344058048801c0110000f402ca016006050003055030220f040310400c50708540f243c4013440f0060180c803080c0c00140d0940c405178003c032401c4070600341002e1400082e410822002c004240d120100300c1041c660f20050000b0f42e00024411410031034118000c0301601d0a52003110301c50741c0030110700b201c401100c00d4090300d20640f21a0140c914043d64074000540c592068a4040503000e40c5000c051481c480100c5a00c0c2041c0a0401b96005115110101c0b2403400000140111000501c180742c803a5a915403443e2100c02c00c0c4034140060300700304002e500240d9240549680548141401401c1c00c0d140d483d014030615185038282000d0303640c412111103568021105030840c04007440c20003401d0780004013181010005100090154500c402643c1c00e5690340c1d048010019401d40309240c07100d940304030003064205032220503901010fa1401041c801d8600c4d4080300c000852014044640c6580f0385000c444110382d461081d2040c1c9403d00100e441c5ca0300b0211040812800380d802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574777787 1250 574776537 574776539
    0xc0f1605040c020c1018080a12050f1c0b1e0a0501020c06030a0b010c0c030602030603070e150402031905040b0f0106051201060804050106051e0405090604020a0e090109020d03170702070e01050409030c0c03060204 93
    0x25880c41c2000c4408442030080a003c0e088035080bc88044685400361110a00100801008101c01601000503544d5020f91003d00e8000350b146011a0000050011220604120f80e02d0006903162922400f000381c01c00c40c10400039020020341e4100b035080d0b007010300d4000e0344070950f51901221100283c10403600e0580000602049207000c10809000d420b1150303042d501c1d8280048480303c80c001100017903020700d80203c00201c1d119410011401d0350308441c0303014000c038909032038070070002032044a038400c107030f965200041003d52290041ea400f80706210301e0904284d090070015600076000500c00c40700c640d200c0700040340a40380c07420811169518805001086070601080000742e82e801000d00503e0b038488000c1002507134580c040241294000f44002134141c1341d1012903805400c540c8006900445100301d62020558040812004407841100d0f070781c4c1c00d44401310126100d103d80c1c0b10308145140c0d00d4005000902d495030014036000e1090400342d0184540c1d80d102c9610350725941c4260364031580810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574779037 1250 574777787 574777793
    0x91505150d0c05030a061a09090717030f391005150a030809030d0201180807032a060e0604020109030b07021e03040501030b1807140c0f1605040c020c1018080a 70
    0x310050321f0000c2250007501a00c0c0072030b4520303581e994034030440c035049101c0122001100c07021300c2103407c44c41e0248151580c44515000001c3e0282c444000311034809025440702c2403a140d4a0081b601205042001d00b20341c1411142e400051b040c041c0000c12041d00400101c1402e81d203a000c0c1d039005510072942036803510081810141440007002c0014156418050080e034858044969200d0751030b44504000d8a841081c20126200700003070709042c26a205200d4682d500344880100c1d07040c501d1007203005000b100a140e4129884800a64000b0301281c2d040c1d0041c00051442c06400d580881c0600c12a1214509191004103640700c140c0e1300101d58200107000d121559250007101d1566400703442e081c60004000d04140e00b0f600d40141508108642409100c5c40707a15044201c403881b07040700046450420500c000140c8500d94030350000e2501031258400129410580946a561201038003d408901500d40502c0710f1070a83c19180030401c480486c06041ea01e10380101c440240109a0080101c0c026620f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574780287 1250 574779037 574779071
    0x607091a0304030311160203062d0714070303050a060b04150f26010305101e0c0507080309010506011101052404060806090303010611070f03060f0b090a091505150d0c05030a06 77
    0x142404d00320340c9000c0b004581100d08040e50302d040000c0362b2000240742d9190306c0b045449122495480c03040700c0380001c00c9400d040d4180c021b0b038020303040c0c0c100030480b4981e46d508010b010b1007075200d82d4401c00d11401048401030301402e00c0050301c3d1201d04004484040c0780701c14180e40c459459108401e4101000140140b0070100f051f44840c8060840c104011515810a1400c244908190841c82e603100d0892100161240c0240c40001c0e80c01a0f5060300c1341440d222442c041c10080381d10600203004010440c8a0a10501485001e640b1110400914602840c0d1000c102c1405140f015009622030ac0009442081006a9407045032000c01850701c81d414040010601c1c6014000130103a83e001c0c0b2002d10003144450300040440c0d600000010740b000020540d000a800c40c44a40d80c1c0c0440700000b00240d9140d60340004a500784280f900a00030070000e0200c90032644256412042491035403100c40280c100050551103a0f402005501e84895884001915100d0201e00c00c4581075116080c0b512035010341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574781537 1250 574780287 574780291
    0x1201020403050106080d05161407091a0a0b160602040e040b010302011b05060f090a0b0a061809080306010806060f040801090209130b04030315120c080607091a030403031116020306 79
    0x80c0c00642040703202c01e4030040040c00760004800010000ca059401000b603c01814043c1215501c103841402e82e4030b044960060100b94041c07444201ca030f0cc1020341030b207444440303003080c0c0d0054003801e824009030700104410610b500404542d0940e0802000c504010303003021075032240f440b0304203a80322503046200060842c4000e400c01d0754243c2103000120002800890265401281c41c814030b100d41e521240181d03e4090150350140c640e8a841c1e041c00720368505a000501940c4540c13400c1e01c1425005c0807908102ea2250901500c0c080c004d00105109600c81c1c0c00c91034001303400511050400f5a85501382035030390f015a006480985d0350f41180d400f10b09083c501c081c0e1004140d0910800f400d40c0351500214004000c000030100361b0707a01c84640c62081081905000b80545a80c1003040740e10901e4030181d108507500035010944a140f0010785182c2c401c80c80d1304241c80f04404c13a802131100b20020340090307410140c011014161074880c00b940444080c4007030102c101c140d1441800301c02050043c10f041040c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574782787 1250 574781537 574781549
    0x11d0705040c0813082a010605030d0221030403030b0a09050f0609040503180102071508090f0606010c030320070305190f020d050904090f08070c0902041518051201020403050106 78
    0x2082c0204402c0c0d0400001039418985c221000954030006038442814000000750215050440381d00c2c001c2d4000c1056002400347c50082c2c1c01c81d901100700c80c005a80d01e4070812030b9144030312220a01503000c1041c85010319001486030030080748603c2d6240018030403c8131500044026aa92000c00c40040180348901c0c1c2c01030000c1c0c03400040e50038071b51a00c0e40c49200d50000364046c0c0c80204964507059200b000140002c0c0040411070b01d001c4140d1000038005902075515001a10500c040c090034440041015402100c05840e141004003080d1f071f05602802e400d0810400091012070344807110620040181021486a0365082d41c0e02c04114101c40c88411180c45001009800c600038100207400044014403040c403814565116a1403074001405084038141c0200850206c03c02d00c410456000003504400d03100d04d0b4291042030b2101e400004074000d40c80344001c5400b00c0c2c0c48040b2900c0c0600040d00401c9856101e440c0f0b6a91903101140070000461201d8455039030028040050000a00c100c002601c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574784037 1250 574782787 574782797
    0x120a050112030c030513050301050112060b0906030a24050a0f150503032704021b1b010c0609140a0c050103060803040b090609130e011512021e0102011d0705040c 71
    0xc0070344004000c3c0c0c032961002010f0100010b03034120741c400207580300300050000030024049980c41c1c01c100b24828913818400c48649003400b444d0b000a00e80030041c184608000f400510f902080c5407034054040a041c0540100c2014035404413140c80440c0c000c05204003211070011030340e081c1f00e0910008540103c8001545460400c00c284120354010040301c481181081019098901070b540d44640010149101c41d440380c03000a040c052a10303005200c040071510030050300ca540d4004000038142c101704c0101c1c40d001800300e00a05001a0b00e0358040f480c03071800f0b100015201030300c80b08410316040f0003a0054a0700380c00040308000030741e410301595009d44440700c040e500741440e14200d40000d02030032410030722507400468200d00a45a4943c60b0009902d5004107000c002c001c60b4105e40242001480040030b2240b0020204480c842164451140340d8040e0951015940c12509082c003445400389490440d5202e407032802c3c809140b00602141c2e510b281d00078101c6940340004010440d00d16207143c0081c88 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574785287 1250 574784037 574784069
    0x5030615040c030b030304030c03170f0405060313021905040f14131115120a0e031c061a0301180b0a09050601020a0b091501050f0f0420120a0501 64
    0x1200354403060044400d45011416421582d000d80c05071800450440d010b10002c680001404620340000040fa40030f0000000ca4168442c03140c041e9118090070580380f00c030300700000c1100b0f003444030042d54000f03500c4182d4122004603030300003003440c02d42074200d4031091040030050082e45018410f5059a0300ca90504006410540d4030200b00c0b008000c2664658801c110f4440c4144a040ba500c00390302840109809206420702d525418a03411032955211090849800591200450712a44048494903c0154208810310004405a1100c01c100944c01c5480d50000540041d40d100e08581205040c1c0086480398148240c5017050310030750ba403649146003814101034a6807682c840d84015284202408a1190b5901005034500b00c7c1c0048024002d42101e0308120b20101c0c080f03942c0010540d003140b50802c1e6642c40c800c000003c8003400e00c407035029582000d001901d180907400146040c50458020a8442d400074800d260ba42068a4181e0000300702010081040010301c0350354050f001d841d003481021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574786537 1250 574785287 574785301
    0x30c020f060907050d0218070c03030b04060b071b05041b1706011407080c03180108070c02150a1101020a0e1519030f02220501020111040311010e0d06140709050306 72
    0x5443d10f02c92240544100034140f01551600803c40c0d021000ca54126000c0c0e05007d0002024044809411350001386051700d082918030b003500541c7d044a45610f1103e042101340d4440841c11341c0c2e0344840f100c2c0040c03158000100c0fa2224002c9031140c070400700b1040500b0300c0b1001c0152808041046031511240c424040180c07030780e00840ca5004d0006601885902c611712460640d2003886800d025581510001c1044919948010800d11100800b80c2e1110701940307403100b059035200300002002750f000c3c0c1000c07101425020301002030007160189103007070581a400e201400d403c992022407010000f906c03840c5d1404903810510110b5810000b44c41c0301e54981812084105c501c1101882480700301070310798075a104610302580680341041c0c04400034440c9000040381080680c1d81d24072865015509041008407036070b07104070a5400b2039421100d082040c10b24a001110b0242d4a11a4030758006c0c2c80348007000100d0407510039040103101000c540390582c14031000290000c01103a2040e8404e910150400843d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574787787 1250 574786537 574786543
    0x181201050a110f0a08060604030516170f120913020d0f0c020f030d02130e1006020c01090b12040c031a0a050f04020d0b0723120106030209060403150615030c020f0609 73
    0x20501c40c5800c10300ca80306ea4002555610a5900c00f8206216007035940b1450100301c0d40340030454603231a041c1d251401c0095210b6445005050000800e82c01c502011894441c1d800f00411040c07000403d038459460304222250200d80000ca020140180d49101040342001c442c85410440d4600d800103007281140c41d2419540c80c81002d400d82d05003900070807400c43c14140c005440c0c0103801060542078051400c10107906c02d41c4070510690005105c0d408180030740b035004602a40503100c0120a003441d000060450b500d011402600450302c18800340400030206060055a007944800c00160038441d0814102e4035060312005440b10518101d508180b10042c0d460480704403d4980c0039a840e0126503c41c8000c0e0707135400342d6030040001d0b003e1004100c240c0650b5607006228120640c2e0514800d6603c6010480880c017600c4102a04003404000600c040344031840229600d00b0400b50101360a0744420440502900300d010040c0400d032150b0820160b40c1d010302c83d0100c0c158129006054030300d0680b8941c0d40e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574789037 1250 574787787 574787797
    0x4170c0601140301020d06060f080f0601050702121002040803130b0310171c050702030f031318110a0f0e01031e0c0216060c050706020d080705181201050a110f 70
    0x1075403641c242c42091507440c04c2d01076540d4458042030410156544000c060980c00240303c000340011049400030f6410396004000c28050300341a0344060800c0b50799402d005000380c8145c4001414420550680d0711a00180000c0001c2c0142a020715100d407410480b22241c80f110303030404550000103008100440b4202c441d88d80840b007146001301002080600c007141007481c210001072002c1c401d84007420345103811070001c18002e0301c2038044929034840080e50b2038a80c0240b0545040e074101404040285440814108415031622003002564100d0044c10307c845a002e60800800728070090b140b152566041300b07021050700400e00301032084402608030800144c0c0441a0144120b030740c3c10321050580e10802c02e8285100c0c24030780a03903420707880e80409009114003210031640c0333108803000440d545201150013000a45240c8070111991103089090b165500309107440242242400c22001c1644d0701c01c3c90050710201010000a51402c2c8030604c2015650781c64082030511804010300d410290444e42181c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574790287 1250 574789037 574789049
    0xc040e0c090d0807020613091d0316060b0a0e09010912080405120a0306090204031103070819060b0607151e1a06071a0109020c1c0e0907050408070b0304170c0601 71
    0x42d40d940c00e910004101e80104447c0102030180703e107000c140e15507a030b0300c9840012000381451145038007624450303540340700310480c080242c1002c8443e0000244903410408204c1c0006003400d015540728518005100c0d4104c80d8844269110f903252000d0050609033741c00903404e1842c10003031901d0070fa2601a6a2001c41d10f400c101c2c034100140c984d85452080d0302c4a0302034800d0f29000d564403552030a00005490150720b03298442d00039840002003030300c0c00007518035034200440301501e0301ea82c070390300c54500070304032071400340d03048007040024400060021001c410f140c800050002075559100004c100d603103804c500c16415081c40c025070f09c25500001040e040000c03500322065651a01d203854032141e02c0340c4050001802c00c60280011a0700da4440d00034100c010340f010100d500c4404500000032101414202620124403810700707000040c1802a1003550020142c14203601e05990b40d110149424900d510044030010013100b40401c00116580c440303d900101c054884c00c2200c1c0c1249513031601c4e0188948 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574791537 1250 574790287 574790303
    0x60a0b0a0804030912060e0d170103120915180807050307031b0305030a0206040b0a0908030c0307031b020a1511030c070f08070c0905091b01030207020402120c040e0c090d 75
    0xb60801d40708020000c05030403610101401c0402c01d191031401380210109040c0d060107a4190740345141d01c9110508030201d005102c7c074801d6481d684941e60140302920010040002c071f982e002c40c002004034072444180400d130340d410003002114641c0440009030354219901681041000300a5540d0000d0103005070381c1c010b5002e1884000d4041e1401d1000d9031540f00400d14040401c40216554000c182544031364000c0300918426a643c14901c070444030b103208018003020b024408901c800c0e0058003d183d02c5031450400060f510200b10000d500303901e02e00031a00040c0d00c855810002c0104c44403070a4400c0320b1030bd074284900c10420120841e5400010000300c814800820294288681050044040c5801000300b940d1890242410102c4010500601d03980380d09210114985c0030000628241001d0410380e100b0310040c01d1401100694407044060b64016020b006100040c40b1214050780142104030015689500c6d084451402d0703500241131010811003444000d189444200d100410035900000c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574792787 1250 574791537 574791541
    0x90604060c061d2a09040b0115020c0112020a180b0a1b080403020906031608010c030b010f021209010c0611090f030703030e24030702070f0503030a0c260c0c09060a0b0a08 75
    0x10b031513041c080d030358206034003085000034001802500002c05050317408171440d1944118000c007043e60307a107811945650004000450001d03050000d136001d040d0303000d01840c20105ca40142d000c0c0d40b11200720f58001c4101e0120024803510307595007190450008110001144101031250303103420340140140e10000e40201400340002d0750030380c0d080c4503240505400000c841100c81d141daa1240c001c1003d450b40d04013292510058400540c0108103019007503407140e004000011207101140900c2d0407000c2c043d03040c02002c4a818000980c14001d140301203581c51462038803503141c0b0041004081c0c03c40040c0307010350468401800070030b6001c02c60044418060b40c1c0440107881450311158040b0051084440492020052101056010460340d04903001809103141c810340764420140c4a10500003580041221701d800e00c0d0020300d5990b0240d41c034011020301c410040803500004000f6074441c400c0e2462640141d2403500ba1403802e1030700c2c903800c04400da5021030094181841103660788a00020a401d000b41000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574794037 1250 574792787 574792843
    0x1506030402130b150403020913080a12020c031b01060f0503070e0702120d0b090106050415030b0f0d05031c060609031e05070602070303080a0509031c02090604060c061d 74
    0x55001c648090f1020240740e50f44d40885420381c1003400100d110b201c030308010800b6a1304200603050502d800032201c80c9411180b03142601c4400070358403c812415000c1c0706100761924140003030401e45202c00c2d02d5620700646003c881303007120070680082c1400700e40340c1c0060100b6280050104217032200e0007e8240292200b070410780c80d09588100156014000194030603066195402c1400c07418420b030750380b08061740c848005903598003e038083c003a5100b02d0401c0c40340b0110304c41d800900a481c8050161112007440b0008a0110047d080c810780e0181d200050610042110301c12851107420ba0752010004182408801001140e040c48090800d050101c0740101c3c1054101d00344505a80c030130110392501c1e07074420000e51110141d22060f00482c0c0d007240001d00010181c003030140f0513504000038502d400162203880102002400740d50301455030a0140700300c5501d549000300301608064441401c1074140386002d10075200c140c41e00846090000400d491310030300004250040358510000c412000f2000c2c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574795287 1250 574794037 574794041
    0x50907060f050a05120c0a0f02010b031015080a080319060e0705071401091101110c031c022406040b061204021e09010b030402100f021515040c02070e150603040213 72
    0x5e5002c403851490038400020f1805009105110303507500c662590011545003031b4200e429036540c00c0d805411440109620391030f940e201c00c00310703120601a400c482c0c0d00e80480390714000d0501c60071150060004140042100101c1c01c00880c40d0303500703c0a102540c24004411000480032b0191010b0040200344002040840c540d0b0500c901041d4008008115082c289003400071001040c4c280490400d0002903213042000c50110210400035000b0500a4047c2840e11608107005030b0340300c00c40c01149591061260910102c1070303041d40c809000c604c0c0b410b100742080300312044140010300c03c0c1410032070300300032261940f55550b00640484600181000c3c41013803490741442d88103000e520130706980011a044074600b002d503010305d000b950030032039580c85000180c800c0e0805966075800f40e4001d403420b900741c461040702c1e03d83c02800305a10003611003071a004039054506e92901d08015030058801480b544007488105a881500d41d050850440d4141e00411150701c0080c2010b4041d9203105030414000c1c9180d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574796537 1250 574795287 574795297
    0xd020c031204030f110a0803042102010e070f031505090c0a09050a060807030b130201091a091503161d0a030b09160506090402031509011503050907060f050a05 70
    0x10140d076a40c1058481c0c07001d041e5002c0390114041000d845414140d14031500b00d018003440c2c40b000402c4510603607158641079400050045401030002c039070742e580e506490180889034a01d07640002c901c1044c014450340c10191a5004980404082c5c4020404504100b01c417092880740e0820000fa0350f1159a62142040620250070b03030802660b1000090403415540070b00c0c412481404200300031500c03203d542d52101d00511000d40014131300c0006c42c00c000c06c3c0c82d0305014402d10504000700482d59410740310660041d442c011168550700031030b40b40300c1424100302c2140244454046070703141d49080c1c1042135442110800300e604002c2030765030100b000e02500408030303100340e001092035003003075640d150124400708101c03002100c40c0070300844091640380301c04101090301c02c028059400d00115005003c000c2d000240380f100804400c8a42070a55124503e8071400380000d003943d8108140c1404004e800d4a030050200015684107030010800c1c0d0b0b5001c02c1c00d8001b001c19191259a405400e0401c540324041c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574797787 1250 574796537 574796557
    0x2030304081e0a020f0613050406030f060b12120a02161e09050c0301050f030a21090503070b0406030905150907090506040c120f02160b06041b0f050d02 67
    0x540031a82840c00900011070351100008010000740c890300d015240c80010714000c5d0404041c070803041170b0380b074900d01821402c281c0e2040020b08590b607000080c20384815500c1030f82c50340501040c940c140300050054001ca40800d554481c1c180c0000728039182c0c0d84200765070f0881d803e00c0104080782840d100340441c10071800462038110a260329055030340e9015407070024154010034030b4a00050700c040f40c0c0c0a07640c800e03a881ca51443c01c680c07911051001a13007000c03c110b9410b0140085590003d040c800a0a410030035402e41d1550340c0d00c1105c000b030450812904034900ca9402003404010a44441c41203405884841ca130204038980b06251030b034038200f1880344808804500c1c80412004100008241d811220002801d01254940c5000c0c0411103001180752030000740040c101051080e0103800c88013049241c60801454418010940c0b001c043ca451403c440800461091060b545400d014014689988480c46030340d4060303040018080720800480c86041c0007003c113a203640490a17a043d9508141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574799037 1250 574797787 574797793
    0x30c031a09060429190b0306060a0302210f010f031104020d0204030c17100209010f03110d0903090504050106050a08130318180501090b060702063007030b0f0a0905040f0203 76
    0x14080280d062121000b0000303d010718015600803201715020981e40d0110b0341c0c2d804149285803100d1041c4140f5600c03c20442c0c007490b408020401c0b40d007441249100c078500b0307940b14545803402c0c1203178003052a45c410b81c0941c0f40e06803080000d1012850984006107100c03001c0324010f030b4610244450340d0290046900140440300405400140c00743c1c64000e05001c1d01040c001e50311404140ca0b038281c1240540c60030980094108044542280d0081c3d01003d000660341c0105820030300e04421080c240c45900c44100d00250160104000340d0503e0700609000d41203600380642443c501e60001009014014081b5507074001030700800c0d0506001d2a00c88014480c2503a0300e06409844a1444480030009428903040c1031401c3c0000079082114490404000c5000302088c3c9400701c56000c00055030000031000d0007103004c4107620484203154450020136101003003403011140c90407200103800c58100d036800501481c0c03c404040d0881e0350b000031400c1600e4050100044c2500e5a0802c0301c40b05619210003074140c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574800287 1250 574799037 574799081
    0xa180902031603050105090a2a03061104080f0615061c0204030b151f0f02010e0a1217100308070302010902191e0810020c0f1b01030c031a090604 64
    0x41102c101c48001e40b80a04000e021760b4980100d001da80701900381010b459800e081c22201014a010b411102d2002d00c00d25048134003e850b0703100c0008458071105c41d0030301c07901d00003410410490140320b21002c01c4500d030040c110301c1c0b50004168850034250308610f40320300d900052050306403401113030646d084511070504545642c1c803881e000c0c4200f40e040c0c6508420b00b4180303071041824034140300d06000046100403000e800d589025001c1d28580420302c0094155500e039200000e19841c20440440b50703900406804100c0c0a25039009048220910700c500c200c2404141040080310140e4001d1045130703440201c2035940c911505040b4010249450003e5010710350100ca072401c0403041d00d503882640e10000b00e1200028120004040e03c40c41441501c05680000303c04a101c411300b68050301820b4049400c0d540348417580c4140d1400d20805000a2600c3c40c0c001e443c00246d560305229030940c00986040401140f03101e0011580b1500c44511914070070056440010745548032508401d0740c009003029409414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574801537 1250 574800287 574800313
    0x902131d122d030f04200f10030225020103060b030c090607080903100912020d021f0b0303030a0212160e0904030e040905011e1e15030b012702090a18090203 69
    0x4e8000d40741074403010200349400c0d074080740040d0011441e2000400d0030340341c14440014008415000e6000b030040c035a017032243d40380c0142a1000480e800b480c40c003072101040041e10001d001c448664100c013030807180a00c20014200074810480c0c4401e203003159440c1c0c0b81c1c40c151900384001d02c100d00c41683c2501a10308440011a083d0308900032407849a03813041091018000e00300c0e030f03407000d184a907001070307000300c42c451805403003401544081c90f6064008161030700004007003882c5610a0340c104041d0b03039000a00600341e00d46161100e070440484284914903840e0090020246071013000003911865800340800c0c20036002d810404614000a4014400d03503800d8140301d402803180c00035286600e00641204100c5807100d101d64018005e47c0868840b4441101050700000c041d8204011102c400300c820101c049240074004034024640506181c0e88080c5640e044c08291449441440d801d03401444095000e40d01c01c40c4100603252041790b407080f501c0030302c10414042d01080401030f40501582d408060301c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574802787 1250 574801537 574801561
    0x20d0c021912050f0115090207170f0a02010501050409030806190f060f12050c0f031302040f0921050d020903190b07170f0103020f01030902131d122d03 67
    0x5690f01900558040e82900c0c1600c6003a6410f50300c5504181e140c02c5c00c01c0c48031100a501a081c000d001c1c4d1540d10030020301114040d5580c0c00000c4419211401043c24214140d09018040c09800d050740c0601ca01c4061fa0380240071090b002c0c01c081e100e1072a1a025014001d03509070b26100500e07002e10340100c101c1d61100050524040703100b4490028041216003c0c10030b00c18010b0301d005100008070076240c0b85002000604903000a0a1701c51124240354001000da0350314014022800d1400100240301169840c0c5862804461042590440301a96013000140c4e0400b0a444542c07801c0e84015a50302d1203c00001c1c01c021040b40c9159115960313441040620000d0981c441c815011911608401c2c0100c20311060300c01e00848442c501d08001c44010300060510981c002030aa1060501043e8020190700003001c568189500f04c0c1000c0d940c00f0f0101c2142c03002c2c0c4031b0407002c1d20024081e100000c101c01e07824950f0310480940c1190845203010070304c1e000e4003c03c4111169480d4255803522810000d0210b81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574804037 1250 574802787 574802819
    0xf03090812040806011e080604031d011b080c0a1a0a0e061902090402120412140c0a0209041103030a020d032904090320071d07020d0c0219 61
    0x28840c880107022500c0c45103088509480071003005046980ca0002464003103a100c045400c9508200200060b1300403007085014021344c407039201c0200c09102070841c0740203100c0c4542114100400c0300100a1006e41d40e2041120710f50f003054015540f6104040124a00520501d0003042c019800424180400a50580c0741c05205c0f10364050250790403100b1011380d1094140e4000f01c904c0e103c4140100c102210350300414640c08003501c00750500c11203070101203580d00b044409a5501900140440d0182d601c048541500c2c41700d2180300d03041241e41c8280703507910169100028040c1c0544000f10303090043c1501001c0300040001c08690783c0c0d09541c200251680b03010700208000c6402e002e032081d46250686400c04490b83e580c559100b882c50007400b004081d0180e081c0c250144443c140b50f0002c082d2a06502d001024105001040307070341d10b4940030100042a504610b220a85040c0600c0b424079804102e40c90350143c5880c01d00744040d41400000d2154604000d000c185034804c020000d400005100c1c122 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574805287 1250 574804037 574804049
    0x60316030f05010c0c033e010e0d021b150712110f070308030f1302060d02130b07111302090a0608040b09060f07180e0709030c120b15010c0f0309 64
    0x12241c0100340c03001742c5210101d031000030045451204150070106021006041c05081b000190303040304240b41c4940940e0001e11500300c12a511000c2840d0056020046285400107500c010301c40c1c060340c3d161004c00000c43e50b418521414182540b10075100c0b03460203542405400140740744201c44030103005007030380c00200b00207040c0303004503010415010004a82c2c0c0c0c0440c2d41040c3c00c02e04d941d07208045a40100c1000b40801030f01c00d0301110100258880b44050083d0380d0000314010707552107815004442c585040d5000740803540c800c0100000003050300c4d00c0a2450b01007900e2180c03d00d580081500c019018007580150070015910000800320350240340240120700641c104115510755860098540c1e200f02ca117a49142400000b04800b584190f850b0061000781820f20700c0a0f03900c458180081d0310042d038922002070f080041c01c1c014018000704c030100401e07880d00203032003036200c640c0c859030b01c2100103216428181e0341010710046640a0302441c00c1c0c0701d5020400381c418064502e0040c3c58110b4a005807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574806537 1250 574805287 574805291
    0x903030d1a030706020312041217180c030109020d03181703120903070201020d141303050d020c030a0b04082506140a020a020a0f050102040314250303050909060316030f0501 76
    0x61013a001200702c85424044254015695403107450b00903540f00d080e91a402045030302e480701003000d5003249456000301f8400050306001c41d44480b18074034000d045100580300380d14003441140145c0e200b2420000c0f1943c1402c1c05110b030800308003158100711082c4c0c04448000700b10030320b180c0902d401100070076a0b0041007c80d031117079807111200a0f5890244060090160b8031400000b05523901400410124040382c2c1179061400040621980020440d40d1048403650300c40607250700309a405010005030100203400070000343c02c85da02c64a020180151018212030000903003003640407081c9402800c0c0400706080c056840c40545040002441c050303840c02c00c034680c584003140c064203060003143c000b4a0b19a00401d0091030503203d0058982200c00c04542c15075003004000005190b00c94405000e002d4840036111100014894450b504031412040c4000e070f049120920020390004244c502080080d102c03c1c842e81c0e00c10000c603103001c5404041100b45082d0b0080002000361610b60207054610610007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574807787 1250 574806537 574806539
    0x1217040606080d0c1119050319141603080c0102190c0b1b090603061c0f1a160c0203010e060c0901140a021504051011031f0b09060903030d1a0307 64
    0x7140c1010042800405d200e420000e004064604a800000d000c0d00050340c0580d40f550302c0c3c0001c0d2411800c00c1c000c0b0000b41200d5084818010b000303c0d111072402c0c1c1240030705402918044111048d100a0100030030000c1d000c5002158050300b5415a00420303a00507164955a036400720140c0700d400104022510144070000040300704100e002c000d140402e00740e0032641440000307010020690002480d0a41040c1c82a140e9a010000401310003011030042c0300078500e040c01400c0400e20344002100d40160340c941c06052150021405440700218580741c600703182c42c00040d2001901503d03140310f000450b0301c124402d02140481c07860081003d040700f41c03112001004c2010740c10401f8098580d5060150f004140380c20f18403500f00601d0f84e03102c0c0c403480941d41403182e800ba42d00d044494034210302e42c04410100c1003101549940788144002e06080e0700d1450b01c2450002c4407100303840345103e82405107501088051443d00c040007599406101501d06111208104250000140c5540d0600740b1030310031004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574809037 1250 574807787 574807813
    0x1a0115020c010905010e180c0c07080f0c09060105070f05071412030915040e04080406030f090b0c0a0504090509030919151b0605070804060507020118121704060608 72
    0x40065000c403040e10741c3c1c082c05140800644001d034003044900c1c1c10a00100d0144031848130550503512450540c0c100c84d846205440c80d091408142d50000c440580c4844039541c0401e9000611100141c0101c403d080c0540e2581d0048400d401076940c02801c05640c191034070100480030408500f519840542002941d20420405c80d021240ba04618460b400070041a410750130284811030010922416403494943d0b00c140c1c001c0060001c0f541996101c501050604c4055490b0192114050a00d0000e01c16810b86444080040c0340107010302c040c01600040103400240901e003542c00814a00348104000c1c50a070b000c00b40c507580060000361140904051401090b0131140080d401d4a201c440f0400584250714000d56440c903a03451b0080d1002030740141400080d48074020a031241c4490703501c007100c5040070305e8144192080900020290b90415140781c4155207503522800e00d4507003100700d4144002028200303544030a448204a41d110034250200b106008194104504991181045960001c1064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574810287 1250 574809037 574809043
    0xf051507050a0308180c060304080309070315062610090201020c0a0e09060606070c0909020d02040e0d180b070813030512030403080a0b09150406051e09010b07110105030709031a011502 81
    0x6d01034550290080c00407a011400d0000a540e0002080f01103c0c01143c6a44940c00240c4052a0300000b0586502e02440320329030030790b4801064410b820b41e0507150040c00e40440d4580c0c1c040140480340954920f518029a8420800d410001c1c0d00640600c00040d10794651801ca06000c0700e80700403030300c1780304082106820440c0c1210022504551401c5050703080501c1781000e020741240599010030103c002c1030140e130b540d204441c10321049000404036546c28003400b42c00b0085c7c1c09229140510030010820500c02c810301122601e81e40710400356aa00342042c0d0f14441d256150300043c0251140c00d02d070410f020318600045001d180240c0715502075943d40c0081c04240c504160b4100e070801a0400401c0303180c5482c40482814220080020644a4550000c100a000b070300f00c090101fa250401504a0383c10100074035800341c00341080c03451401034135454298203003044041e5541005400800900e01c11710541052000c2c5510000d840b44d0082c0b14201155038030000e001d215001900d034640148101c0c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574811537 1250 574810287 574810303
    0x20c0f010b10090510020304090f0c03050619050d06020f0c011e02091c061b020c0a0b070b0c070203030403050303040b07110a0201090306020a020c12031b06010f051507050a030818 79
    0x295030762203021420142880250358080702c0005c15880103010100d6005814042c4035001c1d03100d41400141c0c5070f00c030000181684c10241546000300884020754810903071460600c0d0036500305a442e04480e1042e0724003980284110b00b95070480420101d035040b0f8001041d0804180851024500310680701c030b60303035a10101c0c410740c4012a4002401c4606005102558242441c110f015076070004110001c1042400c010000d0f07461000180c101403d84000e900d0840d6000c400380108042442c02d00d0a01e40d03031008100c00161902aa1010201c1c1c0c090465074104200c8010b19403020680e6103d0a180c81c00340b90203142a500900803c80e003c0d0351a0340c0c44c0000881100f541d8050b542c140c882c520719142c41e8001d6100408403411801843c582125584a0b040c421a50f030301d800006540c0c8003107c00088000d82100c4600c41825000640104003513a06020004150340045600d8043d5220344010090144a800001095401583c00c01da0502d60402c10b014400c131040b0300c0801c3e034603103c11000c2d6141d20230 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574812787 1250 574811537 574811569
    0x501081006030b010c0602131a0a0207170f030708120f04210915020618061b1809010b1c050705180307030503041e0b090604050111010f020c0f010b 65
    0x103032208024452080e00300b250384000c181482c40c2510400c3e1680c40980c1e109190250b249040c0c2c11080001e4540048825401d041f414071541c281040b0366002902d030042403007042d80e9000c040da45007058142c280b1204880700428001c603903950715285000d25054200016140d00e41c01a000040c1800d0091f215080c41258442d418010085030140210172031046114590200545840c0200d08640a03210f41d00425800d900284800c0c076050700c484145030110f00b011600c43e0008014070603402d0204034410307070500004200d03503220140d45040810f564040c50303507260700001c480c00002e1195140310091040005554141000701245000724007a0f420030f0b940380c40010b50400508400306004284030300c9040d80103041e5215a039503a1601482c54005030007000d104180f0025808001c1c07504406440240307070300445a03003818450000038202d405244a02410b0081c0224030f003403901800c0d07009004500c03e805c8215100d50f200c800d4070f42d03114000300500d0b0480d80f034410750074010703e49500000302d4400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574814037 1250 574812787 574812811
    0xc0717060c070c091d01020c0c030c041416030f1a01180e150f0307080c01110f0607030218040c050a14090904020402090d05030d09021c030c061104080f0c0a050108 72
    0x454880d8040091130040d1441e0100303170f10710220114402c0c0a0008201894481e40100200d8080c0000c160514802464030f61295181c00302d000c1c116a41141030aa026108440f544942400100c0942c050000043e200d24034500d083c011460300492004404101c2e81c00f82d0350b182c40d00440c103140c01010b80650040c808480941030024591283c4004010111400500005802504000824900941e43d0800e41c03076070b003000446500f40d582c441c0c122000c1040c090001e0210510700348000340c58070b40151483c002c240e00050181403041030495424625200640304100395441154005c015400c24511b2000240350015810010240202078034201030005042000c181c0320740d030030040290311140034940c00400c4102e68001180043c4054880d0704400400840d01d84038a10421401010030400c01c100f071000c0f060307910f0201f0341c44a0026000350340041c00040c1488074443c111030f240a640d001140350702c00c660036882984808188035110940035109c03483d01c00e882d0001920629012030f140b0003d14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574815287 1250 574814037 574814039
    0x3030a1d0301020705010f02280c0213090b07020601050306010b092b0b0c040f05010504060206041b0b0d290112020a0c08071101020c1f080c0c0717060c070c 69
    0x5841011102003810000c00061600d100fa03a107403425a1010040c1041d5990301090006128a0722a04000d880d440c1c180300010742d80c18204d01520000800c0000b0740540390741c100c00c00785810140e0103a0030085d0000a040e40c00c2c03400c144005d664603400d0007043d009000d82d40000544480e60301c260b40100030002c2692041c5c0f03085c404c4440b041100c8040700c0c0c0648090942c00e40110b450f019800c0e0041003502405c44c0c2c0c0e2030520090040030055644818104030041008026042c0e01051a58111f80d00402c0e0304824141c140ca200028a01c039006003841d82c00c0003c40c1342c01da42c882c1d4440d8041c02d4a0324100c9041400009900040d480280c24590204200300c40420460440d603001705a0282a0304140018600307940324800e0315005020100c800d09017011900442d50780400485160010071a00740c0d81d41403c00c0040c08480152090050034405072101103200c89805205845843e803600080382c04180e0b40e845040440501814114054020f50002c140a0082d00c411240101c0c0c05c140b01c00121 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574816537 1250 574815287 574815317
    0xe0a0501090b030c070c0b0d0c0c02060d0b1906200705030613170d0e010509061b0a030f050f040210020a031403071107030b160305010e0c090325060e03030a 69
    0x5a40f005003065004a0108801c0001079400110840a80b4085010588807914503d140d021a07440d04090001d008070580070b01d0041c0e40d0341040f502c8a11000030041280c000480100707000d030102040017a06c01c110500e002c0f41496020079464448450300d946c4420f1040a4103c4d140c44104900529070150846000540812040c0680c6829284a0000e20007440900c1202c2040781c1c002c03210728240a40c4449a030420703900309029030768202c6074030f00241c211800c1040d00b200664035001181c0481031400700b01007500b00e000394407441c821000501c0503c030a1038481c80700c01c804142164120f100f004550081c503410307407001556400c601da06441d50716844821405141d80750300010b1017801042800c443c950b40e0034900740040c03002944600c03042c40c21401c01001180b28841030f20754200030145000010844030140801981e08070034030008103a620982900428241040d110540300e031081418199458500091302c2c1000719072150b511400419400350030507072688100b42081c000a83c1d945145801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574817787 1250 574816537 574816559
    0x2130504030504081603032007090b0d020913021203070b07083103030e011107020d0507030f0b070e010302030702031b1603061506021516050f0d0207030e0a050109 72
    0x11038002d0034418105a0341d925076510702060280d41000340701d408a0308108250b007044c003201d07254100d0712402c0341c90302d60b550040780e03140d600340310704803030307580c503806122a00c2c1c403076003840511590040d000c0d0a203440c1c0310404204102051404074040c400100b90344540c41004015210482c1d40b01e280341c88542c4403c03a040300d0310680a8448481d1503204115420200e4021901c0c1500f500b03503009580c40c022180c100502103500c42c485800c11a410b0403500c010b00244002140d8010741d040300c84408440c5a414030314a451999000280b00f89801c1c50a030b801c0c0100d041c9554800c0d4816075401d01022401d1004406a00003584d4034070150380309218450070740a803804404540c0703218408441da0220103000803045070308250720544480d42c3d1500020706a40c261001ca00c00351402c0d000401483d448206907212520b8000d00d410054031a0315941c85c04a40315000700d480e07024444500c3d5458052049450009610550003100070a003000302d10362071802e03ea0244e201b00d500c140c54210007240b51042d0485 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574819037 1250 574817787 574817791
    0x15030118200d0b10090f050103020f040e100801060803090d0b090a06020a03021e04030203070b0f0405030a06060e0601140409110c150405252607140f0d021305 70
    0x101c1c0364008801d00714034032200d002924028946190124030300c520b80c400c0c04000c8a5540c414420818800402c2c03000c80c08625400e000c0f10000e107001603440c100030100b001e89014580110409426600c18003802ca03100030700c4a82510600c01c001c000c0191f40e40c0c40e02d0b5480c4100882503400651052840012410140025901100c02015030300305403031300d64800c2c0480e405010a400485d501140001c1031020040c0b031300c1546620100513503c0c040c20342d00001c1d540c131408d02c2001c00007040007039003410000c41c0c141610001c10020f001c854101405140c120050301d802d0290b268101044c0c00040c040790720a0a0300b81c60380380001c800501e41810010700310f003e07040742ca0704030395450801c0007003c0e050a41000341c50003404a0b80b0201c105410585031550800b049640590100155100501c0302b64a07210300c124222514800b503d01c4036110391451880002c80261110301d103000f0100c0005407600360308041882d1020480c1d005019010602c100314140e80d1706000603410100d07440d003409400741b00d644000c2d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 574820143 1106 574819037 574819061
    0x6081006050306060d021f02010218010810050913080d050603010c1103040509180a050105090f16050f0a0812041406030114370515030118 61
    0xb941d16640500f803180f1800e404103030b640131540c0344441b049a101c10004120024008104003030b00039080b03204040c5440c005041001100d602c101010340c420b80710f40d000314400c00e007008244401d0220081141180010f00154407011071031a9000e4a0051411200070031103140010901d0309441814200e0018040980707001211a02c011040c1d40c290307101074860780001d030f951028030300e001007040c203224041c0e01507105904240714064015600c52100a82210785105001510350b13a554891000f4900d0464000701c24403041c03814201c5484201d200814020500752990b203202d0130036100501030000b0a00000c1d04114001411144020b00320049a42d01e00703547c07404121341040c440d10101c13148034200c0c20842000a0145081c044d039000082c01ca407c2c0c4024064100c0068040140240392180d82c88252402c5038405040c1124140c42000414410415149464074090044070242d9 = true := by decide +kernel

theorem cover : BRFrame.Cov 574640287 574820143 := by
  have h0 := BRFrame.cov_init 574640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 574640287 ≤ n) (h2 : n < 574820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
