-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:28:42.433193+00:00
-- url     : https://prove2.me/submissions/fe43e53a-f54a-45dd-97a1-2a2793805f82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 902338129 ≤ n < 902517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 902339379 1250 902338129 902338133
    0x30c0301050906010f021e10060801061d04080720030609160605040f050906060f0c012a08041104060f150810060c12050c1006090b0a0513051b07 64
    0x560801d2107218418684000040c103554030a05400a50300360940041040380c12a14120100204030040101c0921071500e10241d85c035000d015a1004190590000400c282003900c4c0110101c800000c40c1c000320f51130750501001030001021244000c0c0c006109035404081c07402800d1007103010451980d803510400003840040540840c01a00902c4018400c0f16240d82e00d000646d1503000e244035408181a9022041240c0d0900301c524550010300202000e02d0a1406102400d140e0050240d4121683d529154801c0c03905915012400300100d103280c0751075110802000414100e0010401084104546100c1002d070300c2d03541142c030141c035402400310b844236100c0b8000d1004003001c1c008000080c00e1180400d0501d00c2540100d802c1d26070342d0344c0e80c05400120707459480030505170f41100b404001b0108000070aa50090001c903461480340c08010950601c0e0507420380a43d03a20000c2c00e4450300c0c2c1c4030b1041110341e0311541d07000d440d540d900c0d074041042d564543c040e000341c2c045410f05000683d000118102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 902340629 1250 902339379 902339401
    0xa0b06060714071412060a091e0b06151c09170d020903060708011a030c120109150b09100c0204020903030406020303160201050708180c031009031202092206050603 72
    0x5641c540c04440c42200710340c000704130000c030628100302140d03005200407c4e8110305541115082c01d0090707070808641c0a103100034854500802c0c2c07007912004841c8080c48014078029007038101c9498544452405c0c1260703454103031240560b042c1102601560f4080c0c403010041004480c1001081c006986034550000c0c2d50710f03c0c00b941c06078170014401c2c0200c2001810050280078240d041c0c2d0600035441c11081c03080d03180d84c0304c240c0c00a041844840c1d424420400c2c00318135088624041e0403148804030341140c0a00002081060303d4101e60a8a08107024480b01500d0310501155041424030703002e03264004500104000303204000203590580000240403615a80002c001c40c0100010b4100446150300d003901282200c100382d030314000145130300c00481d0032000c18500c0b11400c10204c10548820070300700340000b85842080d612114281e40c89070707914400d050300040350114002d03248005525000080c3d001440b00c2c40c2450403151085008141c000031222294000f801030320f8050301d49a40c904000740f0241e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 902341879 1250 902340629 902340643
    0xb0c1321150e0c131811090a05010e150d02030102031f1410050a02101e110903100905100c090302090a0b0906010509120304170d0503090a0b06060714 66
    0x18400a0340d051100980d044940304007100c03001510098054500c283e410842480d26900c141d0003910f41703035142e5841c54201120413205040c440c10102480c240201c050041040c0018070041d412407400c001000b690b040800056030100b081886c0d0310070400c004002030510056080702070b415610200401c404c00340000340070b500c0c9071104003d60071500c0da90811100281814a501c40d04012560b200c00ca0f01400f030b40141c00a40e203e401642c400080f0b03051f9100803281e11041030314103010b0707000200081c07202c9480381ca8031501900c20403a00c1d08100c1e0000c02e40c0c030910a207440c00701c66610400c0006005042c841d41c10907400c4004180620b8942c00e1000308114924081a481b4509800c041a4540d49500c40e4040b49100a040d48080c1d6407444019910786c0c22840c407107508000303400d40050750958103000420180c10415800009050303102825441c1c076149510b200c09000c0200180000a40001801ca0404c2e42c0107609509669030000402d1903409445002022482da200003052401c001150399 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 902343129 1250 902341879 902341883
    0x210b09190503032e030b0a0906050a050f0a020a020c0906010504081519052701060b040933181401080d0f05031b0723030a031401030b0c1321 62
    0x2c41c02d4404104c880e4221071184048110b4040b5507004000041d003c802283d88229111341c00103100d5440e0b1100c8064a0048452400c4180e1314820450b4081c80360038520341011207030f501142000500d18011f95030b0544c81e04003512079541d005c0007900aa00c19400c03200030302820019550000740034161108c1d1305005590b015020790914104074600802842924810340c0700c1f40c1031850a03041440010051001070000c45059500c2ea48003041c800c4c0380c000100300800c5410300001d0029080100310307007c00c00c07012450b000c80a640c050070110714054241b440a40e1010b030005840180481c540d94024003040c0340d03030942207800400002d450100420030581200203074580400124410404845070700c401c41c1d01c1f0703090f606400d02c0710680c114800c01a040c26031140410608420b00c158070440740b50280040744c1440d6000145034106140d0502504199200c2e408105281d035045560386005030f40e0003800d0559016004c1007040700c180b4103449041c010102003a400002107a580c8a0040080e90364030b007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 902344379 1250 902343129 902343151
    0x1a060906070f03171b0a0507020a32040b010c0209220c0501020f0609030a0f051c0605100f0c080c010902090403050a11030f090123040902040906210b0919050303 71
    0x181a000300603540d443e240c2c901c0c10120b1b142103801442542c058004c00d405070b070814000000810100c00301c0d43c00709520200391070341da4000d040c2e1040b100d40d0303403a00046450240b4149800d0010300e9030072801000e0915411904108940d8545081400040311400d040a810202042080500080050700c0707007950f03420381c01c3e208003204201000b9520300341991980b0041d401004203e80040c4514000007800c042442c00514003120100c41803d91441c8120104215603078030000c001600d04000714109500d214205003011082101c00075000702140d00015000d413200203103001804c1c000790300102030b203a4000d000d05a40d05103410028050740103610080085080b4040d01c2c1151000001581c0e084811400d1641c0707016400030046903031040c076020b0790040042511200424070b24810203000603007111080180c4032481d040b180350981da4194400070b801000045124041409030404003082508500d400d0126126040c14500d01001159034400c64200c251001041001c044015806035008080e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 902345629 1250 902344379 902344381
    0x1404090f0516080103080a091e0503010b120316150c020a110d11040f0b03030c010f1a0105070f022206030c0b120f101703070b07031a060906070f0317 66
    0x141c060602c1c5100c1454a011803a0740300104002013060006208044451501d84d441c079580c0d8100c4031840f02d0b5892408402107013080e0a00c07203410248900400d464080f602042805401c0b000181c491049058010070041424800710500802d034040011b4403410100c100b00b00350070888000d455044015040340c00300340c5036100740624544900d00010040d045840d8242889061701044020815904440216921400340c442160307014400b5021800c00e42c00089090b580c1c0001020071514500c00035100b50701e03903044041540c1d0f481015140c0e00c5500c10404030340344c640c0f030000806e00201384151300400b84000c450a071210180360440d0003264421134022800c152245200711003401010650365450b921000010b09010b80800e803150800100001004030a454550182426250100c5540c02e81d2000417403004010130070800550060082c5001c00540d007188250180b1115020b000c1c0b0b00c9420040b51a144560382c8008071050317aa84181c15a03070550862902070039246c1d901046070468035000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 902346879 1250 902345629 902345641
    0x80a06080601260a0b161106010b070201050c0a0204060902040807050307150807031401060306240e310b2b0f051e060105030d05040b0301151404090f05 67
    0x3610341c16244040900d1400900c622030460441c540e00c41c0d0310000e4841d01c0130320000700e10f12150b8240a6201c109046030070300c1d45242c000c0c01105410082140d164800300041020348002401c0d501950b0b42441d2040d5030350f1002e2040c6290040040e000b039030240c5000780010303803646a1350050048504c803400703990082c5d60780c03410540c41c0c1203584210307000c881124111881040c4200c555550161203414001586c2c82c403410440002e170000d070840c0c004030b9a109020701403c4007030124400252210035004406140c0d000b030040545003400f40b40d9000b41207400c00030b41e5490034800c04045c0995002115400e0041c51079000e0301a0a00e650792500607007150300c0f500c0502202c1d14400d0601001001208035490407662200801c403100d0f0019500c60060174803a6030b004a2406050241c803149000030083c55040104147c141520b170b40000c010301200708401c0120300c81c0079051300d046900301c040d045000402c15900b9589580d44e40f0309101f020200007008031708080980d12017850281408000c0041c1c1d9115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 902348129 1250 902346879 902346883
    0x180702070527010501082a07060b030606030a150e1c090501020a0b0606070305070f060c0f110a060b0406170d02010b0a032415120b060405010308030c030a020f0a080a0608 75
    0x1071a104602c55080740061085501807200075030003031440e0010320031211080324500300f4000203092106000f0030000c1e14401303200c440c1c0244c0d2080c90080f0040e1185052800009907501c08400c00140b11120001c1d032030001c410b2686c0981c0f030f140003071416500c0b0401032160180107141741c00e0b241004201609800b1a10307510010305c541c103c503071051607081141c48807170820120f03030003071007017142000010000240040c003002312070f1038803600c00c160110712040e60100213030041d00035491355803c0241090b8064010040040c00e800080c0d00800300061081101c07001c1000707003403d078102442c00c404002c1004000b0f04000303254400004d09500070043d4107291010003804145a01c00580b021990615401d12010041810703440c010f501d0307000061000030303500c10103240c644580c4403000e0051030b0100e8a05110307404480e151700903006c0754100550360650f541c92a10740800f4101001c08040800040d000c9034080e030495154034100e000d0191a02e807149802086401d003151240300150411030002498180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 902349379 1250 902348129 902348179
    0xe010602030301150507051617060c09061c0605030a0503030114010507150c12060b09040536030f07080904231603020909130b0709060c030e1807020705 67
    0x8043c507085403401c11303000c072455088064241e400303001e260240c1e4030003840348d81001c0040104181890b0203081c10303410319081500c0140700040b0141c042082030b405540304c404490540c04091641e248801c1c0c2600180001c2c902900031603018803650030b0420038420004003a40c100c0d41c1507041c070790019209000441e0726005000d0b0007000c6055800c48000144041e800c81076a60415181403440e0242c4208040103031082d90703001c000503003800030300403d45040c9805555809a200c1e04148440c1c07a802d80c4090203a100059958074100100145a0b1a98030a0003140c0500405292542e2a1039803400c0c20001a0301c410141da200782d1078214038118415150b1034020084a400c54520215900c501d44c1210060307909a4030020550708011403060366076410350302ca0084409112a428584d0107141840c2404805440c9905008046004104130b640c0b00001c000f000360300d440d003142e80b055141d01003803e0184500038a120a00400c3c100040a90b0000790002120b0045862101c0520800c103207a0207008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 902350629 1250 902349379 902349389
    0x5010c030e190827040920031203010905270309210a111c0501050714040e0106030b1c0308100f23030715030204090501091a1005040906030c0e010602030301 69
    0x80240507070403400207840d142c04410303060441e07101d4100302d13070800003400c1b2031103903104035042810004056501c99225800400c0b00d00c06600421014481c0301005482d80014410000e500b03450b2030001d20383c4604603840703444400c04654036030510844554203036140e41240c158513016030801c041c2a006803030300480c168020340d02c0c580a00144d54031a00c0b00601001c1c03a450003034014030500700100c03c25121841c65005c080c095000000c2e5420701403001010706c0300480700510072010070b0105210701000b03800d0450440d0098140040e50202007808152440448070550000319441248502490f0304941501c0c86640e443c4e00902540b52204d200400d441290f000b03030030044070070302162080401041c1d9003003c0020002d040340d0703150341e481c03089041000b00c64498000003030300810104100101030080501520ba165414850449001450305964070401400c2e48100c440314081e19002c0c2c0210102c0b4040d000000381806603549900788075450416612400d44013a6001d000001c01c24404020f49060366 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 902351879 1250 902350629 902350643
    0xe07030906051b09010c060b0607050102130602030304080f03041a0903090a062c0607021002070e091209010e0a050907050c100c020a170c030301230901060e061605010c030e19 77
    0x40c40004444101b044041246c80d10b984604480c2030365a8040502981c5101ea400540c1c5c2e42c1303a07100c3d41c118028581d402403082d94010305c203000005441c1010b44245113042c11107140c803552031b800c00400b04039103002005030300f01512041c05909000800240310251082e504401c000755103c2080750440c0d00151303100f0000b1603c0e020010002c13501600102040030080c207040c2069420f40014248250b442042c0d80542e00c0785000b000710040c4407004a5104088a0280a45140ca90f03003070026846020446410807030480c2e0055015030382e070906e56010340006002400360b4605010041c205030311196004e01c1602c10807e0003418051540201d05502c0c0c5d2903405822942031542e1135040c066035041c04000442000d000b902201501013000e90b0003048884400101070907c070102a03209145640c24602610001d40140506c83d0041009801c181047d41e20a6403140e44000103503041c0d0140400804c55400d00d00d903051483d6058000b41042203112040d505240c0c1084280d040c00301c80714100502e00d0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 902353129 1250 902351879 902351887
    0x4020618010203040503010e0715020f0d08180d050c120405060d02210a05040311030c0705091509090c0a05091509270a14010b090a0b0a0e07030906051b 67
    0x140205101840400d0010700441c3e00f060b0710360f00047e007505c01c419400ca00f503600a100400c4004074101d0b049518590b03030b0003d089045181416680c4900843d24840c0501000c0e00c0030401e0010300030501340d03090302c0510650714420000c10340141540c0c040c408030f030000d125140d485540b0360400011202104c6000305018508006688042d01940002c0031000000749c582c0c054002000922211900c00c0c200385000103014075040c074000d4040000d8403181c0340309500038098405059400074514080e14802c0f200110300380d442038040704008a50219070394029040000f8005090000103410300c40080c201c071000c004a448005014600008540c1c8004200806c40c1d640e2103810000d506980068a80340103000341070049079600b1010210000c03d500c55030100404809009860121a01c030340001c5009120307680401000820740c407400341401030507507a11019550660390700100303100280305281c0ca0324880d103007601c4090010030340c180e402c3c0c41041c01c00c800101c1d0080070f6044c60801348e0400e2065414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 902354379 1250 902353129 902353147
    0x2092701150e221410061d010512060321120c070309030308040c03060e060f0a0c090b0c030d150f080a02090c1c0f0b01270b0c0c0a120614040206 64
    0x1402d50080c2422003c50b0f03103943e103030380549054001c3c0e0b21920892041c100800e00d01440200030100318451000946847c43d42a102c0c0d0f03038001c0c00c54240d000e01c003070803e055407100d80019003484020002035a4005500150603c0c2d00e0412026000c0d0b2054070038820041d903540c42e0041d1b010302c110b003002400920911000d00000c0e02502076a9000f90281c0941c540013926581c0d80c0045550700e034001d0a03183d0289080282090180c1c00190307010f4803444007400350044420780508100490300400803a5440800c4103058a40100190341940c40b2088050048a4402c5520313204480b242c00b07080000c2c42c041c440890240740c00241100f4103940903110301c4a0343c1d94035140b480c4a4200300380c9262103986070074543c09111030b10b00400c02d40c40442c003000039060080900240c01c0e061040d02755140304090011310540d2845500602c82200e0f8060300c91665110380400160805d800f01d1507595000c0e41084010031020340d03100d2007241003482014200603485002c46051100d160859000758024010040760413 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 902355629 1250 902354379 902354419
    0x1e09020913050a171c06150e10111516090602150705070305220f0801050f011a252f1903050105010e060414091002092701150e 56
    0x703540b02c0c0d1003c40a040c40104000038114601c1764541c8030b82e454544009000e480a0346070300401c500003d042c078400d440b074824089000d0303903484083c4a05109214402e802c05100a0029680141804c603c408103850308207200c9d42100c200d00001c01c00074000240c0460070f60f0001482966042000100110583d99018111000da000c01421410404e052000c00c4d612001c0c03403000d210f46496a00c50805040c1031039540c03140d03000303558008109a8101002d00403170324000b580303107411f4829000d10420410035114100d4414412401041d10f092840710031121a20101440725400500c142007d100d08032a0104040c07412121442218050240b0104025103240180c8031581c02d0003038580c030540c2e15540362189400c440c000d0f4401740c40710311070408100552416101d130b05074600881c0040c0c001410304001507540c0b1092400010b0340d040c1d0000e01c405850f542d05034000c81d00f03846200c0350302801500460210071040c0a10a4141002e040f15202e02c0d00c42c0509884070a001e409080040c9810810303c0c152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 902356879 1250 902355629 902355653
    0x206010312110d080a1503020a0e06120610180b011709010e0d0e0a0f030b0109050a1d011b030e100203191b0905030607050711041e09020913050a 64
    0x100500000c008280c56640307040c4061582d6003d40e03152a005480c041c490001603504c1103004040c2e281e4145004d01c0180c0e60010300c0e10680309003105102c0d1540d500c2c008184d50b042da102000640f445040108000000f028030640251045180c00464100704603021500740e030174a04000f40400d810a50079015035030307807103412680002d5034400401c0ca4074060b80341d2801c003d00715007440000340115952090b82e0402410042c000c0441c41d491518a9281d501e4108007910180964401144c89001040301c030103054010000486042500400004015035414020a400c80d142c1c0c080c0340c0d200034442c032800d00902c035410302d00000001500702c07c941d014440c4001d40c402440310001d92a20692007071050114496072200301501824001d08a101e980c029091100319440248a5070200303042010507940002580c48980d842704a402c110f491510000340907225030b1020740580303842600d02d0003410303940e5000001114026140307100291180100f2101d280260400984594402562100002e0151000c2c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 902358129 1250 902356879 902356913
    0x16030618020c15090c210718150627050604050d05190c0e090316021c1a220807080c120a1d1c03030c120e0d0801051002060103 56
    0x9141d012010103400e5400c14025200d162042e48102e444000f282400c018174007031548901601003020542c5400c441d070721003440c00b2310280c52030a0414440071075896005401d90925840750744100780d0f01d80d14000c1008001404261303010700000741c0c07459072134080788065003554000390040d807800307050805110080510200480e220310a58005600040e81c00d00d00e420175501c02d452545240e0b00c0c0551a1050b2480503054031581d400030850b49041c00c2150091468407981a07540305143d541810001000201a03a0054070303180d1401c0d440c106000d40584114420349a06020f464583d503a0f24005c816280280002401d090081040030040741443c009440b2409401044074161095040320081503085601c1c441d0104600c205160212100e104140c080ca5409403a031035101c8a1044c054282890407103405014150b61b908103021f0b2600ca02800503010400c00b10900030b00300b5040c1000d9446690145410018002500114003868020303203021042d070003640240b4450742189ca80401112821141b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 902359379 1250 902358129 902358133
    0x207021e060403050f100b0a080a03121d010504261206060403150e060a09121d030106080703020f01020105190c0504180c0f020d09170f03070b16030618020c 69
    0x1001407010411345004031604c05c0600302030341c214800c0700183c3e9144000d882c03041c084103000b4440244001841201280c01d481d05580079800700c5002301c020300d6440241403e940311011481c0750380005400550043d88103516181c000c000c0c0a501032041c0741503401800803001e08100c2007515032003444200d504000000c0c8650701e050f540703580d114a00c000440400b092241c84061003005500c045c800e9070703130007032140b0760074408688603503540701e01501a1030b03281040c4408211001c035104c545034042184288043c008000e0319844001441d5901680d11080348200c49001c407054082d441070080300e006d9100d480290300503108040b203c2018004a07a8107808100b01407200140014213500d00080810100c0d1000840801e440320041c40f00d1b070494031070700541d8000038203180003a81c0300901804070380d048007a114228403a50801c60034603482c2103045115209c042160818050301001c0b81d8040d2074100c501c0304c4e11007807001080c0c040d60a10310861081e01400510701c0c072420340940080c0b8900081400f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902360629 1250 902359379 902359387
    0xe0612070b090111150907240522080601270c08060d05122b09020303180a05060712080906010617040812010905010f050405041e030203130806070905040207021e06 72
    0x2801c0d00c0c0814101c030030010039441f039002000b211100c00440c04084425071503004241441003000b070079a00c41c05c0001e90005005103240503842e141d0521340c0c00900b41700000c1ea00c0c103503921483d141d50040b4041d0a85c1403005c01c0061a000710100c3d21403800c070404207841d440c4655980d1400c0010800e10a801590280980b0250001d4100980010242400080c0150b1410500780703122121600203441100c05481c606203020016032740000586202c20300c81c03c0741c0b506840b1010302041181200d030340001e03003058020580204200d0700413040162100c041d075400d11640da0f5035940079a203020a00c1030401160950804059101c03030025899409800b5154241c075000288003401e000400992100d00c074265034800620400080004000041800302c2e424001810180c8130748502040c294604400c08140c1000d40381054001c0c01601c450100074084d8160f55a681c0c54500d407548000c4640d1400145034000201e85490188290782c20b268010344504044c0108501d04015464010451688084144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902361879 1250 902360629 902360653
    0x702070306020f0a030e0303040c0e18120919060e0937060b0a0503010915031b031a16030b120a0609110603040803040807080f040e0612070b090111 65
    0x40001c1c0f10a40010320407559400c00d4a90003400c031a50091240303880d40007003080c400410324041201c0d050322514103200846480711a001140c0010078400041c56020f440702203468a90100302070541e10000b80d400030b402e1103900c0d0060038000f8441c00703060041480d40c0e40c00806400c084050641c0315000e9607c59400c000b411000310307140849542e00e00e03402040c01082c41c040e458903000d4880101142130744a802c0c020306010152403030105004010009968200501080701031150307500041d500070000a080223a15840c0d04001245804181c42c00403260f1800100719503109000c03441032654241031034403d0400181240075051152256030f002c0c814035845991007070300f848100c1103107105000001d00320031145001420361150601d110f00c41d0740e013802000080f9000c0d00c1180d5020f54000d036a00d54440042c648a10307640201c2c1105180000e0101d404241e042511082d00c1c0a194219051b000240003000340301e54402c1c036409101007661085c0075994143d40600c50134a064826801501c0301e00c4c3d821 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902363129 1250 902361879 902361881
    0x11d07020a0b0103050c0102160602030912070515040905010608070c0809040908190e040603020a12030203040308211b18030a02040e0c0111030f070809010e0d11011b0b0f0702070306 80
    0x13070b001555180c1048000448940e01081510922078841c00074424443c500304001c2e46a00540f1045801003003004041d8140100c10b000d048003070000180036a0682440c0035180040c0c3e0400d0140040a5142c000003260603401881590700c80c520036034405d030001142c2e82d030302145038020050307158100d40c0b90f521210014540d0b9024241692030254000070384a52440000d0030400c1b8441c0c0a40554a054014005a01c072000501c041d42d003821703001182c82d8442d1504901d1441558800780683c000400c04400506512019801c4401400700406803915021605100402e24001548006100b000b0030766a403201040c1540001e03c0c01001d695180c429500070038156146d10180183c0d0740c201c02d44003422503800001d507040c5622244000c40c100032072150700343c0b440d20030000c0c041c02d0308202161340180c03a0300c40c400d034614000014000f240a40158940f0009040c052222907000c26240092245c01a01c50004c1c111402e8008018002a807206040120b10410103801c002c1103010b01c2e08003001181007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902364379 1250 902363129 902363131
    0x70f17240a0e1603150512030c01020304060c09091a151e07050706050406080f0a110a030b1005130e0703140403110d0c1133180405011d07020a0b 64
    0x25000200b210780f800f14003400401e0481c070312000a241c038080384071155a076030317200140a40b00c00391803040304040c003400c035503140d0b000e8120030908030340c0000100010030001b500446e218941c507448001c220780d10f50b1080307001e0f2405038880c80d40300400a0f89000044c41c2400c0c0054460425402d0f4610302110084400410407084c101d20052400000c1e01c01c0401c182000868010102840c0050402d82010001007041e0300141c001c4000340d0b0900082041002d45a10082020080b00c003da5601e50f071102c405000b0300900c42d061441404009680884036004100f1194958500c0c0c101c010250b00b0917001c055607010140c05242019958241c0b80034000041030064001d5000342c45600e80b41101e24001032801d411259000104030354042480d00150a4000c90180c4140c12200d0303103241030750a8803040d421400140d9003021030091007050700160500314000e10b440503c0aa40c00d6001c0e07004024402601d400780b28010002c2100c03540c6200c0c5ea00a0250b190b0003000c0380c41a0780070203400f41c0f610066604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902365629 1250 902364379 902364389
    0x712050c07090e0601050d150f06240806240309071a12011e03060b0310050c0d0605061216030e100e0609010c08070e0612010e070f17240a 61
    0x2c0d440c8101060f0710400c000090040c4012190440d11600c15507070014040c40c0541040601d5444131102e00c8050301a80000d0090000e044c03a0101418481c0680013415480c0c2002c500407601110203d000790401d9076401120030f007545c1c00703080d00c81a19030048280c1d510080c441102c501460743d002c5603030545142003602c1c030004d62810750b450b00c0c11503001d507210120691111224001c0c0007060300e281040440c036001184d8000c00b000481c210f8a2002c01d00340352402c0c900c1c030300d01840c09040000b1540340401a041c94011004100941034858040c040c1c10312070760001511140d095400960100d1349000c0c5813198035400c1c5000729661b00b412078114034101e003111000c40c10548500300e409101d0000c00c0000d5014216200074400c00060316009419148040e20a00812509018080064a40c0400c480074100700f07481301e007075640e51241b000000f43c2c0155400400103c0b41b40481802910030241141a142101411a2640c88034086401d100c8034950b4000c40a913010401040e10750b89900012000301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902366879 1250 902365629 902365631
    0x319110a0c02030f010b0f1005090910060e09040206120606070501020f0a0305150d030509010509120a11090f0703051305030705210726250501050c09060712050c0709 73
    0x541580b0405061210741000c8410903071400c40c9111083e07441c0e525800060100303840c08030018070f0200c0116030505c20200c0b841d8001381440180071522b030900c000d000c2110380395601d1801d6a05408104910f03e41d0503900654000428000301c8800080d204050b600014003e00301858002c840e0784282c2a078000c0c41c081c0c4410f03d408140342c224a9054058213070300100c035100c0c2040c40e800c40c01c0029070a00082e0805410090049032036210b59009600319041d4010080500c00c00c0d9410f01d02d002d9644500010850b02480d140d00c08450f00d0404030b030814094103c16070b0b0f001e103035903a47c40128001d2a00800c41c02e0f141c3e85030401000404c03800d10080106900407406403282104084001c007100702400c04510000c001004a41c0c04103a4141400741c50104504c1886d1541400d240c0031030050240841d0f502d09601d01c03490540c012006c0d01619103135a071080009210680e108140c0c20114041d045174150001001c0015500240c1ca4124000e001d2055040040c2407001c0100e85516055854100c04021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902368129 1250 902366879 902366897
    0x1060c120c030c140115030c03060c022b120e0c0f0a210c03080301180b0f0906060c0109050303071206080a03020a031b0209040602090f0d03050319110a 67
    0x20000c40400c5006103405400e2480c4240c045540040c841ca140c51000743c52950105641d0101000a40259042004004c690405c158507810801100c0300359120841e0030074500501502c10b6800801d24259200e100e031528110116008401983d81c010010130004208554030071b14400b540a00ca0045860f81260081030820401000d100303142c0907a07010305104440001040014420900150b01e241d8008403100d203650200345421103140b01c094100901c0608040008120703a02661011240d620807120140b10007003036081841b0b4840c500c3c5c0c050680021410000230070901b4880010022002c3c1d11000145066544c1c8405082d60010f4a00200040c04042c40d004503001070300494018282010281c5000c41c00c903603019507a134241c84802800c0c0841d03004c204040400010306048010f4016040485a140914103240290300c1100035038883c0c619a4440d03001800c1180b031589525916440f2a855a00c54040d84d01075080e41c014070f69012600c0c0c01d881c00b40d0240c1e24000e4418080c3c10345442d90300e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902369379 1250 902368129 902368133
    0x10020c04110702030609060108100c0e060703020a0308010b09030604020d030e030601060f0207050603150405040201140403050a03031406010c060218030a081216081303052106040605010c030c02120703020901060c 93
    0xc2045c05404030406520085c0140306001000c41d180c02048401200086c3d080540070b4207540c0003042040d00e41c0c2c0440046240310506801084880040e4400e5031446800d0787c03195900c418502840015503016403100c4005030050518402100945002c0c6c01e000d0400c405420010340b9116090300010700056000d0750b01445d41e90104081c001501c400c5620703074154500034007440300c03558800041e11b100d25101c0700403c05590242804042444034141901d50b92912800c1c00303681d600440800b103000030300c0c100782c001c0e41c622421045406610140c2d5100483e20450321b5040c0a90481600c040c220034110b090101203a8080050070b011038818010203071100c10050304d14066600091500c02016170301c0c5142440e050340403a81e00d501c0b41420810251010081c20b003103c1501030f0318194070704581060420103d402e490003040748109001c48060040319118001118103070740c86c000040125250200d04801498000d8945180844640c11911143d41c1c0380c0001d80c001d8801c0e4091004101c824a030306c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902370629 1250 902369379 902369383
    0x10807030c0507110d05030301082107110d080c030a120c02030a080c07060908180f0f01020c12150f0405151e0703411510020c0411070203 61
    0x252016090808102080007000068020302c00c95400400c110035070140b500759a80d0301c0880d011150b4104080384c0e125a10f4104070303942ea21460050640e4084c40300d1942000d442d03041708407940c441e408003103103d01c0b4050005000007181c003440704817100791050207801c00c101c200304003400c0c25001c00e0703540f01c0d0b031000915400811a402c8079401001c540040080c002041d4200d40c105400c08807410780650758814505040e401040156402825108002240900140101c802c4010540200c0b0704142c9080301c00104900385900810301707800360700000d4a40c51907141010891420740340e074005450703400000c9801d041413407800b12001e40d2500304190500c0180603040250020710200c01042e02181c0c18416a40c28403c507a03291000000756100c400190428841d4000c1f55119a28019217a82660a05000303070000401d01311903035604817800c400b0782c4443c00c501005801104007292140c42400c206007480510b070001c0c1206c409506c11200e441d034036510f80b4400c0916002c1e82d0364401c0d40314861441054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902371879 1250 902370629 902370631
    0x409021005090a09020309060424051018060609061206050603070c1506232107060f0201141812030c070b010b07031403150901030501050115080403020a020913021e0108 74
    0x2013581c501c14010020241c0f40059000d42098015042031540e1080100c038000502e005850041c600b801c000902040030002040c00058034029242111130400014100d8102d0701d1510070400080d8003400704004041c041c501580310b81d00000c1c1d01281c680c0c0c488001c2001540140d4102d030004800c2c0001006012400c07102e03032401d64802c40b041c0541c42c6016a22b01d40340404c0b181000c070301422020150810b5840e800d12040d14410890700180419450203810340718101d500c0703421f011414a000b440e1006106100310300104242c0c41e1019060345139041c001c01c00441625102e0784502c5280001c0260805e00710196205448002c0750395655106803421203880c0c03906034084602e51130140001000690004400071080035003d1000f80c584e614030b200c40c40300c21424420141c004d10404004010b00030190025810b0301e502c0c1c424055201141e0700100e0710720800f00c4001d001a00710320000d400625205009680240302403003001d0304401c240d0002000640304561001d900360070480c41e0310117035810607012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902373129 1250 902371879 902371889
    0xc04031a01091503080414060c010507030c020d030b0a03260301080c100305060f01140d06091a01020a02010f110309090a020a1d0a091107050f06041412040605090409021005090a 78
    0x507030302080c40c603515441c0600503400785447d405143d010b070845645030541907468180c1c070b940c000e1010b41000c0c03c020f00109044035035071006004030500f40c044e440c00b900412041c890f0140a00321428136580fa406c1562104000c0403020107000b0350783c0c101c51400368001d980a000c1e110090000c2031606420820602d002c844d4200525003010104481035655103160241d00c00b0a0904905071903104510061034801c141d0003514286c64040c000c00c4214195018111040c00f85240c0180400340e04010380c4d40d0402140000d0005031207194400100348610100c0d115501c107901200d0418900b500000d41400040300c0004020b1750210742c40c680c10750300c00c0d8103a155402c00f020640080008001140380e40d0503601410401a499594201520180310101d03409250414190745100d6000d100107600d82d101a9015680c3c0c0b003501b81c03900440803000c80d040f01d41c8a46414001d16091a041d410b80315500300f8548140e210361f5030030450002d40c680e000b1810100e42240e440580e5001503604001c900d520702d03002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902374379 1250 902373129 902373161
    0x8040501020c0102280c0b070509123003010b03010b1c140718080706030914010606081b030609044e0e0d03210f02030403030c02010203040b0a050c04031a0109 70
    0x40c00800e1041c0c47c003981045030303450540e075030728040c2000c0b9401d40040001e1603c144a04040a507040e0f507124240710f542c01020311b1aa06520b81e22046200c107004c01e00030003070207181c1000100030341d400d42c3c0010701103020341107220300c4445843c0d44050121481d00205040010394102086206130380203011803849000c0d8403903482014144841181d07581f1050145600745a501d50b00a401c0c4007448050409440e8084000d022058980703c00801154050f50508240705450041c50210002c80055074452400948020520fa85a84850342450b91512000301e501e020880002e80c6400c0864140265407001c80442030010201c1e400d4003401031506090340300304461f1800505442c3da03203120010780143c041c58a02e840f09580d1842440010500c0182481c0a2421070400c150701700d29000b5604c202d000740c03010885000003c0c0e0a9081c1c0c80100c400800c6a100900080c0c01c43c5071a44c4181d0308a01031a91003428952695295034410b41c01070421038110104000420200d056030260400380b103c1051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902375629 1250 902374379 902374397
    0x40f140105040c0312031d0a0c170309041107140d110a080d0905150108281a101206060e100803190212041403280308040501020c010228 60
    0x883c0c0501d480300e03001c000d1460103c800001407842c42508031440c0846c1c24103c20380c107412084581039541c0708040c0c084410143c1400c000030719400d40080442c03007070490310140d45030000c81020840103203a056000480741c04144000004140c071a0310354100300404100170320901035001c001400e28450b4400d00d0709181c2c01031288100084608081d642182950040495941003134580076040c04103103d03000303049481c86c200008400400155054210b6504c0b4542c0181c1520495010441015231030301420f5942e194040c0d0800d0b40820740746990160360325021149190300d0301c0700081840e13100041500c50b00e0b2107120130300c1045181d400003a0420107a00514141e90310302031801da106e0060750424a801207050782040e0f411f41c000d02c41c2d5041505e4940035039641e80d8483c010b02000c000c004c00310900030321130207181484514601e1045400010300c2c0c10344d4200400a560200c90603030004104440b00d5400b032000c0e869084c003d001503c10110701881ea04076161034101d100c1e01c04039030400004200901c1d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902376879 1250 902375629 902375633
    0xc0b0a05060a091e090b041718060901032403050f03040e19060503100515030a0213020703020c150901171509250909060b12010e0402010c0605040f14010504 69
    0xc4094030885035800004078000c4132403041080060854002c9444260070000d681040007210355200d03124511455900c0301c1804441070700e4080e03004180103111020f00c4903a000009244c0300001e003074445414500840c0c003d8034450814001d80b180004441e907803025142c11b0003003203014009441c092076240002c60400d803800c0342080c00e0100247c56209864203503d03005901c452241c04c80006400e0140c100c2d0340b2004004400030003043c080383d8410f0360300030342d03080080c5625000c6500050150000e1410410b0752031220080c00075408110202c040d485020305d940700b01d843e2420703d410200780148100e510303031406200242070030104600c483c28090b02e040402c0044070f04c0400d1016071107000c0c1d5445d00e42d86c5d954030b002c1100b11034610311112407000c051611003007142d2000302c00d41515145041441141e648001e810b416010300344002d01400c43c044014419584010b0307000d03078860300516100d00e140000b030700c035078049660a0398160b41c4480080c0102061068114079200346502400c002c0180b80350607 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902378129 1250 902376879 902376889
    0x10213090b0f2e020c01031407020604031817030909100f0306180602070516050f0901180b1f08070c05100b010e032508011b030905100501060c0b0a0506 67
    0x200401c602c1607441c0054440d22083c0ca10710440140c41503d80d1000d10081d0f21400713990758440035221030000382405204100e0a4965808600482d242e4000304100d465030394064a4841700d0150744d544080e1000310004000c4035001032142090810400b03541c1e0350121800b4808210310081400c44840442d10b41000710351900300d2038400320390300322500044c210f0148024035604411031401610841c00030420406214001c9142203041c468108800000ba036520180520007681080081e84024200010008503100d21031080241c10b900900041445035400080d0320802d441116042d403062092143d60100e400c1101207821280c030341446950281e50341d0b40d2990300c29002d01c556031030380c3d01d076550b036030191340100035000b5072039030040680744951540014900d00c003800401d6140000812940050501e4061044600841003004250041e118034102500504400101100d0ba0710402504903051946482154082c2103181d65100501015040a21141002400071600079140c1400d004503950b038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902379379 1250 902378129 902378149
    0x60a1d0106110309100e0a05030607050f070c12030203070309081c0c020316091a040213030215040f03060f0e011518140406020304031b050c01210608010213090b 71
    0x900c0c0c42c91540d0900c0340c08070700b1400703080101a0007420480d025405583c0050405281103010b6403010304040c1da500c00c041e03480c9400d4031044003140003000155554404400104540c90140928101c09940c550754051010040982540180c001103440e40c00c055000000070300510005009016801001c0c000c0d2064000410a0a0910a604001804540b0180304110f10141c44076134044042d03aa171540c0001802103001c001622031035002d002c414038a49442610200c4041c1a14031683c2800c42d401c0c8280718210b10180c92810307105100004030a521306506d90041c510070304000c2010b0b00c0384189001560805d010310801c3d40d04000004440001c0c078014001112140000d990b0802e41010a0318005e010003c0c4418140c02d14104020500145400442c00b81c3d209a840140ea444907842381c0c070140018080084c4542c0003840365811561240c00b4504e024900120070718100c1c0046481c000c1155415488a0b090340d4010404850149160a0750002008090800c0c0f0941e590600041c0035600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902380629 1250 902379379 902379389
    0x3090209070c060e0f0706030c09030803130f050a062003042004020403061107020108010e0108060a0f1b0201140105010302070305120405010e060c131a072a060503060a1d01 76
    0x4a22a82c002404050781120f5600c00400e01a0b50700e040343c20310b4564507252140a00e0001c40c1c20407035103040251242600a04807030300300341d1341801e42c0c42d1008a41c4840b10300c182d0a881c00e662010251011600a01000e0300580c132446000402000d00094900003208800c61400c0c40c05061041201191000c40041e218010211849103100100b40006000b401b4540016190500d030041d2042282494002062201d000340c84514480e03907200140604a0b00900401680340c000b0004100e40d05019040b580b00c01e00c0401d4045507940b5119503126901d0942c3d617031100140e4551492000300c203504200c0390f024020a00e803d52030003c4c03d403005402071040000c2d02c0040902e59000170240042035100f409140d080e1000c0d40c2080c284002241c00a40000b14400300b03104a810740000d022103064410403c50708810b2741c0034101140342c5c841d6513a0f00300081058504040203242910045400051440038080c0e9841e240e8490400c0d0051080407065900405141c404c4048050840440303c4d84482c1154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902381879 1250 902380629 902380637
    0x3080a050a060b04080a06050612030d02070203010204170c10020d020a1412030c0d0b0d020108150f1f0216051c08210402010219080d240e060a060309020907 69
    0x5116903a070a00180b600f40c2c0f1010100801050204083c2004180080760500450091200b5200c103410482c0c0d541c484140c10610768420040c62004511a030082c00115000500040c1459a61040b000207000c20884448003600075540100b070070f14080340803074114051440201911304070b107030002c0d548800d00180034044d216581040822031104001c00920000019607035900d03070500c0121854290002000301048074101042c9a40303506003025580c07609901607660003810f03282c079900f105800315940c06051300105400100c00d05526020103654480f00080d032172442c42403501500904001081e82c4140360724039444000c014654858128040748101000001030000d81b52400c10a00d2158039206529540c03142022049040900c0c80c05105030300070b80035140302541e101505400e07100e0700f68005002c9035090101007040400c95124910300c691160512080b00b42546924a40c1c1d60f10764020200c3c0d0f00d03401d003006400d0903e0b41540004004a0500703201444499000030080781004217400100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902383129 1250 902381879 902381881
    0x3031e072318190302090708070801060f0309050a0804050a090203010f03020609061c0605010807260c040e01121e0f06110403120e272a03130b070c03080a05 69
    0x40401d4889011004500a01000e10340d8403825410003c800d061005034070404000002891013070085150f42d12841c280d0303a40440d00c3e803d000c4140c9840d00c04544010405503916640c10020b4030800006030310600401159845174034010070448003040a030007954200380140010000003400780701000a81c2ea04032507481e203075484c1a01141090048280c802d400e10701c0b1243c0701c89442d1036544450255803080c2c2c7d400005a440b48001c0d00ca680c20028015403240b514100b00341c3e2695a0308090303400c5801904994034003641c410b5400f00d1500d00781c1084c9220000c02d0312035070802002c03501043c20001400010032005525480d504030030f2a1494001d0002c3e82c031840d501c1c40243c800e40454000c0e540c09026002000d81c0008000d017200c1800c10328602903c4a8409032180d02e0910a590003445a1000a05200c0d81e400f030f0424050700307400006505114580c00340558008420001e50301c01c040210120040c00318074208403049003170242141e000c1c0880c0d001c2a80210b07134010401540040c9151001c141c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902384379 1250 902383129 902383147
    0xe091e01050114090f06091c020a06080f063303150f0102030a12020d050a0e010b030102031012080c0304080307170316110a0503030106020a1505090705010809030c03031e0723 77
    0x315214444800e40e00c0340c25210f028060100784069422316900079200040c030282c4802051b07400034816660304140b002e481000450900e08000c9002141c207030500ca04204003a08403600b00c0b50401140d070b00322500c0012003000300c1c414000841e510210021507840c0821640c040020351248151000e080411003d070070306a40c070038469012919440050801000b01d0b1404040d083e00070300705400ba050665003043c0c008d812514050084e68020454140d80c40700d00c034a8515004180580c42e80101c42802e010720000b648480180050401024404061607a420282c501141812030468200b8100c003000d1041c0700303101808a145961041d29401c4c442460803002404618280c3c420a000346107100000c0041080c1d60f0208981d4a0a44160401242181050f2140d025100c0890b032492682d803010348108215171140c09182c1c0c00441c08002c0d285017450281d452810f41c0e2040b82c3c0010b00340001c401e000c00d1048050307000b13a400441450b001c480740c50010000c407084101250070007118038001ca24265 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902385629 1250 902384379 902384389
    0x423090a06230414070b0a0302090f09060f040207051606031b08010807090c1704081e120408091306030b061e031002180603010f050a0e01140d030e091e01050114090f 73
    0x18159111b41c0a40743c03880100018060341c4086a0702e4000c03201c642c0e0b10703c154101a00800c1c096480144401c01c0c258840703080c00000d402c1200f09883c14416110009021103070388680c4009410166000305408280b0a100604102140714000400c0080c0c8010000e14001081280540c1d504550214513458080c0d000c0310300418160100303000b90303118401d0204126024000b403240512541750782c15a0700c0d54400c8504075001d101500a90240c1c4940014009002c66000707182a5130010300d1030110726110422401124072640045a040d5003690a000d01441c2ca80442c4100d006510301692508a0000204c1c1e03c034040c009202c03103010340104180d01203c00442101070001c0d0041c100700c0c0c81e503a48503d13407108100ba40c401e450003010f00b9100868841200315005c0d05030740d4500a129602060a020710142c1040c604061b0304002d01003005072401d940d00c8086500850b03004840c00608810703072455406500040e030103103050103540000131254034440d00c00e56000700c0c4129010030300c645442d00030030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902386879 1250 902385629 902385643
    0x2104020112050a05090d0e01090b0a1b05240103051b0126040c1a12060301020d0e0c01321c15060212090607020423090a06230414 57
    0xe040c15080600b004900d00c043da0002c0c5c4130312030820440350f1069003c1000d80700b109001c0000f500250138000140045100007004188100503460310b1290345039501f114000f0343c42d206000300c580e500810184408290b044541c1c4460308030b0b5590128440d4916680c56985d00c3c58494004a00c4045241c0841103030f014180407180380a10901100c0009052a80582590001c403405c50707958a983e0004a0010408042c40c05400581461a46005021f103ca0610140000d000741d9040d9001c002060f035a01c5a4024030308802d200d00f0040c90b5640d001800074004040d030155090310841d48001c0344600c0e4100144484a940f171807400c4646c0d803807410424035002248084007011150401d071458000d001040741c0304049403080d5083e5808030580800d092414420070307104507403000d414407403030016240c41e511a80700c60304043c0060030748840500440300e907120121907901254000884950900c012801480c0da0300c55400b42c040d007624010541d110305100d02402c080c08040f0760300000301041004120407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902388129 1250 902386879 902386907
    0x309031107080f0f071a0304050111070812060d0b06040c2006042108220f06020d0c05160f0203070f1e091b030f09020a1d01080321040201 61
    0x2541d51030340c58858050b6142214029075a2034030403684400c1640d40040340000c107484800c0741002c11900b0810030300045400c00342c0142c40301e540e9045003c0d44410100000c0203a0381c8940b0441d0b888066074003503040e161200500c030600a940441d40701c000103030b00710030681d404101190001480207010324110380507100340c5183d19202800d078155403159400020854070485c4078400d09001201e86441c01d2a030f104d40d41700004d011524600120700200d044001c444803001082c3d0006850035620f466a00303100c19842d400781d40956000800c04507021003405a02c01071001030500c64038100e455400080003010440d4007400c00d00d590803028085613420b0290000401c6041d000346d450903201c1511884c440304688202040210241c00024880e0260240210080d40fa40484a0303440b039900d0300b0340207007105411003c5005d0b9036013046401651101c04100c003a1484218120844040324901941064180c0240285500c20b0144022074200c894201b90121045840c903d4030381c440b4801601c02035900c0c501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902389379 1250 902388129 902388133
    0x1202070602071a0c0a02150601170a0501030524181c081009091a0a1e0204230603040f020a0522200d0b0a03020a1203021011090103090311 61
    0x16000902281005404183c440310f518040a52250072012034207214045220380540c110b442c040c4403266420b421103502510605010300004440d90b211903d515040b25040c1e00d4503581c20050050002c200102c007683c9900c0c0800c1800c60080031034031100b00000400440307030741c84600d486000c0410f0910440d0740300072468032804031100480c48050180c500846514203180d035074640c0020205c1050003512022500b20811302d0502d559054010040c020060094502c2a103c01c800840110300316074500030b00000303160041c3c690307080c0103509004920b001c0144280340c40e420b45420b8980c0e1400200e81d002540041000e90400440c800304008040550080c0e51020a18a10b21a100c0c002c1e0798085288964040401861050303220524440d03d00440d48403107414217025042a049081c7d10110030040002e020205490b90799001560b0201a5080009940050308005041507010040c1300c0520203d494240181000c20703680e00c800d4050900c94074105502d600340c40d002d15002d00c015841d03c48020782 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902390629 1250 902389379 902389387
    0x302011401060f2316050d0e1005091201090c060c05070b03060102121308010207030903050f0d02061305010e0f2514040b01030f0e0601051005030f130c080a12140a0804031202070602 80
    0x70090341f42c5074030b13071038250105074100701d0f000103481c019410990140c06621001d0420041405020080e251081324000303542d070711100174000c02c032000040d4000b0442d42d5103190a001040c50000c0c10581c040d0720180d003c5000b40f060020b26a004a40f569a01c81500142500c580700d0144a042c10699a404400e0952000482c2814954000c1c003030021340340650103c0d181401d000100659520115100d0001038000001055050098038400c20125004400205440001d050f900c1d0408081c0551034207140d0050300710043d042c1d0100c00c90000c1641a1248242040c68a14070710300401101303840c2440780d5510100c0c2181c0368000d07441b0300f100e90106082045050f401e01400c03a42c030002801795500c100085002c4600131403142080381e101e01d0444410103016141c82c41c402c001d4202c00c1208940c0921030150225072140c0c00c125480c01c081c081da01010b076800701041c02818821807401c545440540030804914429001841030b074115515280c0380da02d815110b10346c4402030050b40401088140002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902391879 1250 902390629 902390633
    0xd0b0a09020a06052a010b0a230a0e0f1e04060b0109080102040b040311040615181a07110f0414011805010305070b03090c0a030302011401060f2316 65
    0x160180c00031910a0320180401911041c0c1502d003800b943d1000c030f144944649210001480b50310b003054000d24201d0000c83c00095241c0010100310740b5820409504410f1200440c440764001c206500341d01090340c21038000c504100c0d0380c0c0c0f0340e240003c00400802c040e4802107028a0040c0c602c03100c201c00e103d80d4036440342c10b007441c000700a008400701c0b940c009900c251001c201c400042c400c81d02140c0f1402c1180346440d00d144d90f01910606488095648a44e49040005160141441c0b07524503030a0741e07803252620142249802c0102c002a00280b080c01201d141c210303c080708030f20494038155001045100f440c043c0c4000aa407112404181a8000d07082c8900c40121a0f05000340303238140e401610189079000308040e010300c101c460900c07000e88035038440343c0d0030064044d21100864121000405892128100c900130400c3c0801e95402140140c0d99100314100344034030014090302411103460180c049000c4c1620052010b0440d01d002d46640000301041c2c1d0102052204070f45002c8191440031041600034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902393129 1250 902391879 902391881
    0x60603080307080a051314030f040321050708030601120608120c1c02070b1818010801050a0c050405010e0d1202060612070506270d11030f0a021e0d0b0a 67
    0xb80c1d288004540c1010108040480310301072148220240c29020401030f9003603d8003600d1924031540c50080380070400200c0f54001180d8004d20245001d214003200c1144480440300c03091304c200413001b00300301c0e00f40300c0800085c03e84021030b500000240307041b41e4940c40300c40140700108059482501036114490100000c2c0343c1c9200500042d5081c4c07002c0c1d4590700a420094207281c0074404c2443c00507049a40140f190040c104058103030780394000390400c0711038541c1e000b05a0b069080c1d10f800c494040280c0040000d0102409495846000702c202403100d8240c9503c040c0283c0500d005880c14040e04030308000032074503105a00c014940d000038200000c6016404040d4490f50260780050140da03800811901068000401d502210006010a4642032600084040b0303903266031501d05800e02c0b0081c80c000984d031605060b0101c0790080e442c00034400e0701d003001c241c5010321f10882440d25030000e01551026030340e54071b0784101b41c0f00181c4444000881160015460802001c0700030081444841840410325007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902394379 1250 902393129 902393131
    0x5030a03032418150509010b070c0803031906140a09020307030e0a06150f060f030c09080f06070f0c05060c0a0201090c030c080601050603040b0621150a1407050412030c0606030803 79
    0x1030040c08100c00d141c030280c80c200c07602143c045c0700c1d0090000c000406c002054100282100c1d80243d028a5030140c58401c0281580e0055032202c0101010f040034152000840c42104010b12003542d0900700c000c851008a40885034900c1400700241d804400030702001c1c0640c101441001c11201920392000c0c81c0c2c40e01e0780040a072180c40b2071542c01e03044070104c0d2846201d2200002d0312265111001c1e03800c4a9107088011b04141a805020005280c200081001c0204540440040c4100c060282803504000080035080c10042d010104030a59070740d0008200007003655500261a030740515500d001c40301d070a038094500d0b000020004c0310315400000500650b03000800546542c10b040c0c4001d07983e0b90013080b0460005039009032624100d040881d68a01d002c0d401a01440d02c0e507070803802405124121141840d038610083d4001511000030802201d81621804007655030411551040d1300b48044010050300413401180b808034070030709940042c140141c1180100b5940300c0d0040c8003042d16480e0200c40c07504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902395629 1250 902394379 902394419
    0x1b0e1e130212090d080c030703060506030702030a030e12120a0902121b0103090308060f0d02060d1d120306010c0f0204180b07090303022e050f0106020f0705030a030324 74
    0x902d8007044040c0d20110f507409850a40b0b0359283c0309071312400c1d480c107000d40c0f01034810401d05a45200c0010292105009148030700f03015009941c41d1410804050290340714020180c3c1250024940f94031400125019140c402c0150b030500b403c2c682e22504035100416401201a50007610395505000b0200c0000b407816102d18405000c0c940c1c040c0100040d8161402400020041001c0318001600d0382031003c200e5a5003040100500402e0074180c02048440e8403c0c240c030310b00d070f58460302820442c10703540300d00402c15204080101074408101031407001038000501390a0400c402c000400051100c4401020000742c1c00800802520303580c1d0784441011100b06504641002c105000146454041c0307100c2e00449406030090168070303c1c40300c07000001c000c559a0031100355401440745c1c2c5035107616101c0c0314030030318984a80364050350620101914004800c00c030404268441d90f010300c050741b07022948005840d030608021600c40c00c1c0d601070301810310303020448640b02404494005003000c502c04034455040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902396879 1250 902395629 902395657
    0x302010915052a0d0c08040504233108031f0914010608060105180919060e040203070e04030504060302131e030b011d0f060303120c0d1b0e1e1302 64
    0x102c900103007904d410041d032001511b814024031041003c0d08264000d46046e4107c0d500705021401c40e24441140d8250035901d44e401c03104c3e907820006500301112092200b2074281903084000305400c0c1e949180d075100c000c2800d4404661040f103a140e1075031718031841e80030340f8915005000d00340c404c2100d07145040003403045d000003c1400004c6031581d4000c0d8110781c01c5003004070340180180c544505001c00c0000290184440c2c1244c1e42120fa0203d90324400ca1003d0301054a0210007400d05004044c40e107a4550840c0c208050f2140a000020ba00070b0112006ca0f0000d040150320355408802070f4450382c1c04e41c0d100718941c0b0326494690284071031151780842640e2103826490030503601d07503c41203c54614800c480c106800d4179004a42390202c0040c0940d80b14500070110303490100200d50031405d14006441c8801080350100f064182c035605070080801410010010440c04e8843c00c03c001c1c189118540105c0c080e003034504403a05c0541c00d041a180901c40d019051044030310350445103500a521107104000d0395 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902398129 1250 902396879 902396893
    0x5100b0301151119060e06060f0315040c0b04060f08070e0102030d02090f0d150e06061e1f050723150c0c06070e0405100302010915052a 60
    0x408114280c905980481d10300050a00300390000355400e05060860043d03d104450841440c805441d01920202c3d1284e580815020005d01c400b528090010b040d49100b002e900c030b00b01743d02d510002007141d98012031400d008100e032900d06041da900d02c4242c0042c00c20340e400182c0840ca041d00300ba619542c0440303654508000d590386031401c03120714142c030148a0068004200020400300d058002c0c0910080c02400f130200c0364000303000121100030224007200d0680c1050588000d2680510540c4c0700703072020340060001403404100003001c0d00c43c2031900d1000c20300003545500184c0c4500c092110004580002c4001a5001d0742c4041c01c0b0b50800346089903400c0b4105014818941c0e00c00400804145010050043c2e011003040000114001004540611f80600110b148050f0030018280030350301d580c07551800751001c0b400703000c19a00700400a8030040107440c400c20043c0d070301c20321900032600c1e010041c1d1203420100504446610416486035400720300c0e034502010303640700540f81413041003240048440c0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902399379 1250 902398129 902398139
    0x307051c0219090e010b18030f060906011202031504030e0a0306060f050411030c0a05160c0306061410031a0307030506061930150509210d0e07030203030c010510 71
    0x9000305028006505006070010813403002c2c003001414402991014125100001f17001081c41d20007103410000e4103500c140144a45502d05006043c090181c40640040016003500442c2d03071001c400b07880242e00740b03100c0002814141f01c1c0740c0d0b03d0102e1300024521070300c0300e580c0e04003a8094842400740c0130410900803400113a510b002c0c458400d900c01400125410b5a4984480a03000e422103040311080c030a080201200e0240c030107008003082031161680d440b845095040240440361250000e21b00607802c404100c1c1e25a48480103004940503c0c030b000300c8c42c4030f1074516110702c51582c1c11842c1e03014421050007008101b00450142d110780701c15100020103000109850004c60854455504600c2400c058058050341d04800008101b0201c4100143e010003962030f0324248402c1100c45a04640c3c40d010300c140030f24140911850021080f036040e010b0403440d120200c25104040320340ca011543c50040521044041c44481d0046030002c0a0300d4545041244450203000704658008000e0300c1c0000100b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902400629 1250 902399379 902399387
    0x7050f030906040201020105160c020d0804030c03050607020c040e0616180e04050d05030720030f030906040c0b0c03090405060d060222081204090c020c13060504060f12080307051c0219 81
    0x40c000783d80c3e517a138031012b00243c080c84900c0101040c00c2e56410003c01021000c139060604100003140b01d030001f048203250203880203041c812521220b5201d10305251404103004000078180d500400c0541e41c1c1503500d403540c0010740f4000403001d1502860200c1d00c20016601d030f40030780041e20803401501070f15201c26020380110380601c01100c0c880080307035201d2a602c0300c42000d6041c401c0602c1e03420341228600031045a4030341c22a002219140d44980c0302c00100800c2003000034000c00101a4500c0250502a051403100c0d140d0048030790300e5000320380c3d800000f10aa510700200c0f1034a680c10403c119a94800c41da940518444044e40c0e20310040740f44080000e040100054003002d0200c2e40140c20708041c288941c120140245810030310441c0f01e4851100000c0e55034050990880c0d07104079000900d103142c60180426607e10350302025803403469502c10490210890811185a83d110824981d29950042c0544441c050000d000005010b00c0900715903465890707000300034411000952003108251018111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902401879 1250 902400629 902400661
    0x308010b04050a12080d18110a0e06120309040603052508060f040503091008071722050f0102070308060a05041802010315121209080d09030b07050f030906040201020105 74
    0x3030300403c2184040102c030214032849a08a0f20031820b032403a0421a444100035141400342203414418001502810000f906407010512030b029141c0e03410f0240380c54602891510300503c01d602070030503030b000354031540c806104031411820014802c001d041e0b164103259580d1078180060050303201d05000748028140d0703d100000c0403280c1000041c4031a1303071041c415004c081c5010313204036514030007481164000d644400c420848035900d6a03501e5140d18001c5402440369440c062030b203311020752000d0201c00c5880380710020084901c0d00151202c0d00d07203840c282d89080e50701e203155040741d40301190203000c26a210804a000304002c6403070000c095166010001114801c0c1003440040c003241c0755840055000350010180541080300c00c050b401d9480e42c00f03510a0700d10b90002c0383c000802c03401611001e5000a2040043c0c541800102190807603404041c0c6100040c0c00003800f2000d00e000003480c440c0c416012a254a45c495045580385e04164420310764130102690101c1c090350900c00041d040c4070108540c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902403129 1250 902401879 902401889
    0x20d1805030906090a05040e06160903030207050f0a031202060402130614040506040f0204081e010509100e010b10113c10020313060c0e090c0c2104030308010b04 71
    0x28602e0490b65404001e11940028400b94100d82c0c2400f0001d81d40d66140303d10100600304001910340c52914103103a0a900c902c405915040c011064070620100b9400070b4684250360302501d00750754200c8400c1c001011044943e00080c20b1035002d0481e8802ca81c0d000ca00a80076a10944601034104010074000041c0c804901a00c60b500c60816408104c0d8503050f0042600446c000c0d000140144082c144076050741c0c401e8010189a0b13101c1d04000d003a0201000050b00780310904d000170030680c1031001e4842e4030740448002c82081692540d0401008280a40c030003041c14100401010500c50030420140c035280314a0020309032030140030740c7c103503408000340a4141d4075511090207440d0100008071701d2030443d10300c1c00458030920860744500074810b41440294001d004100c0381c80c802e02850320b4114183c80030028140c0410040c20841d81e003940350420f8043e000980320103210f4882a06034909494140f240502891b01d1108100300401d50000100400a9a00903a541c10306aa21505501c0c580d10940c811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902404379 1250 902403129 902403133
    0xc1c11061c0c0c02130903170705040510030b0301140702060a1104050402070c0e0a0b1005120601081e070f18050312032d1806250908010e01020d1805 66
    0x300c0c10010154031980885a80307040404500e0104d802183d6580f181c05503002005680d0080c41c0c06058202c1c04600701d690751603104141e640340c607a1000308039010300d110302c81c0911020350200601a02a8100c80702c00340d406802042041e09007190b03a02a501c040c0c40d0003000d8021800403407030545450046011032407000381101c1c98586000c05000003035100b92829100c40f01c2411011984490416189000e40ca0702d60011a501300503608200301b015030845c0b00c0d01400380810102c042144540925a8000c1090818803000c1c1c2e80c84a03144110707012a4028662a8803480405c558590040600007000e5210380e21003941e804034011002d0b409010b40107070359040d40f0800000da1090302082c02507501c0140300006e0b1074103506c2e5000207002281150040702119000401b08188000d58500540400c801e00000b414142400c1c0c61100c8900d401c4030340210b40000c102a00e00a060244d4050f1005149407402001a0388061104038001d40100b100c95416074144809000741030081c1e100d045000d42c020380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902405629 1250 902404379 902404417
    0xc041802031015050c070807080c03030a080105010c020f06070f05010e010e060109020f0f0418112a0f030d0e070e0c180a090c03050405010501170a03050306030c1c1106 74
    0x2e01c0c01c42d0088000219000c111081117030705041d02003803040d500208041c0c40108805400c0c95455070030b180403140018025071050000300141030b4040440b031704407242801c1850b641525800400d241160400c1400c0d040900014072900f0841c0e00324800089074000c3c00200f008004403611603017a100080c00c21320b00d55204200511400d08941d0040170301403961149180350185103000741e110b5400c039520000304040d085d005180c0c05140c1c1d000b0180a1130b402c040c5140341c0b0030142c106c64070754a681c20100c0c4100c071152880c0c0c0c074801d804000340c4169108080880340c07a4034200e00514090b007060340c4912024000c035000024001c1b00c0803c528051502e884119060498901a410702021210480342d44114a07270000155106c403071081c10300d224542e6401040500d8141440380c2502d03010f0303021032000d9100c02c1c40036a8083c0042055103205504d8541242e594892400080ca41002091035550244421590340c201603140403003086417074801d82038900644c10210030080ca40c0035040c4c00c59205a8214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902406879 1250 902405629 902405639
    0x207030803180a030c260a030213031506090e03070b240d0f060b0f012a0b09010501170105100e07121b03200706050612060c0418020310 60
    0x1075030380035446030841c0c480b520280300300c58a868030001080e00840c14144040091000000380e03102500f007180c01e03103d10300405d10340054451240d40b0040e810103a01082003a01b5508a5241400030360300144c2c01c0c0c0340843c1a4014000801a9215456855241c10483d1240c0103010081d40c000d150004288800b0769540040c002034202031103190811041d01d0728443e5200e545c0c51941010f0103004510000308001300d458a401168102444e080c03140b901c030302000c0b0403070307a01800f0040b601d8864400c01c0389188041444101820f407200d001045154800100000820f0541c040c504031402208120516141941102d088030000c0e921004c0307649540310140701401d1185003858100d01c040c589150340500d01d40000c1c0c01c40e40f240c1001089c0d10030b24803480c4000c907490301548010f6040448054a0100a003d00440038070420700010300d016100ca000030381c1d40d41da02d01011200c3c5113110a8030300324078000011654aa100d4041e500e83c00205101e00b48118401d8401d0300d2241c1d03039542d08030754458208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902408129 1250 902406879 902406893
    0x30109020f0607231506010804150218130e060c040b03240d12031b12051005130605090a0501050607140c060a0201050612010c080c0a05040e0103230d020703 69
    0xd04040d101c512401071a000d040c0d285082d40513842c013950002d04109541c0d51408000b035500a4038040c1000700001c01e101c0030480000110104541e0310310b0050703079800d00b9040d28080702c143c0307104680d0112407030f802d21001c2c1406811540c0600b0b00e11098416955500140d0f03001802540039140303003580f0a000080e01100d07654107007040145900003d20030104005c001807540000c110049508100100310883c445d9054060041851a0031410090f001c600f240010004003084804051454580300410110341d37010b80c0d101d01404018142c40304540401622101034403481c41458010f21000d000902c4e2a011407003864143d60005140514110035510f514004015420402c0c14074098100d10580541d40c0e500101102d41e00b50700041400d19003503013005201304600300701d100c40b079041100001010b81c0c03018189900450b142a0192a00c001c45001c80b21800b560b000b180049007a00008000d02c100c60b03507401407103551403141111000751000c0c134a440381e50000c9a01c000d42d21004041c0001000c1f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902409379 1250 902408129 902408137
    0x30714090310050a140705091315030803010b031e01030f2603162307030c080903060c0c06071e030b010c080d060602100e0618010e0d08060f030109020f06 68
    0x30041c00c80304401440c409100c1203075019600b004c503490351604001002180340e02015070040907403c1c1103061200f500c01007211a0309901c0d440020f15528a00d0984080a4801c0f0380080c45d0001541501c0f985c4644008401c0d80c0700703031001080d8443d45c59080000d00149010305050700c1d48004018941e0280ba5240ba000c1d0201d601700740d001c20300090f4104411400c140255126140b0100e200d0154440020301030071180348c1045501c402d400031076140c0400200d00f41225051030381460312a0190203035040412050040c1c0d40403030b0b81402114203005203180000c0c00f400c4440e1a220640d100c60300c5000058a6400d01424a8004110b00282d400c01c0203001c1c0d4481c071044001070506081c400016030300ca16050b80545504041a42d5484042c029241e0400032603101c8402d001c410848a05116a0300381e0391000107000c210600100d82e12544910801e4100d04010f807516811140d104400c1c8202419003001180d200d07004002c04c0000603413502d014040c45142c1078029044549112502c000c1c480d4640c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902410629 1250 902409379 902409397
    0x503030a141204030306060e01180e0c120a020706180b0a0b0d02030a150c26180a0b0610030c0503010b1608040f060e1002030904050a0609110405120102030714 70
    0x40280107000d044450b11002034402e5109a0300050501d0400340d02074011001140f042d4104011040c070319603031030341101141d020307640700300401c481d00e658410791503200e8441d54000303030020115401405541100c54019101442c442c010911020420001040e11620803003805880d461014000c104504025071207040c51250242c2400c00c96120764000c04d240c00c041c1401191050391041c843c05100b40640f280040d20102ca2034450594105514004442c1d490010319020509403600441c43d410000107a40701c40929190a440c0070603c6410608032800013240c45a00550024081000707040c8a4400c1038201516038442c2810b503400e20366200c14075000302c250301120030a111280300205803140050310061007180d50f442c02d61820214010112007482407814081c0714180d500b669500d40101c26145480710aa034001419554403201d03601902860703100040040c601055002c2c643c44d6200200190b810a075010f0030784900344003459080740710840c0c0f03200000e1003203a44043c00c00b01d0400100316400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902411879 1250 902410629 902410667
    0x10509060711030f070f0312030b010c060b0310050108010c03113408040b030a0b06040e0a05100b18040506120606010f05120f010501020c03010c020c06160c030317100503030a 77
    0x11180d0101d103443c140c82a0048542d0121502d010808c1194211221407196030134641032142050490018040c2442294010440e039103881952246440c1040440c03080800d8200034031465035107401c40c0e4001d0254103100400079042605a004030303194801140c10075803966000310089500b802c02d89128449000004025100c1d607034552010668180203040035002d003080065580c18040001d0b42110340e540541030003240140000c000c0f4141c0200540c1d80414501ea002c507aa9807403180c0c800701400290007030380d0f40700f0780030078500f000c0c280c1038400e24440c0c442034600308101d403519810404410b00b030003249070180d807143c0c0010304654401d4100700c150601c142170031070615607048120452607004940d0845d00b504d03180010443c941c0e040000080301501540208a0150b250318000d4880300065040360055100040701c02684051044015855800580310900c0c40c0d01c901c1c004164041d5100301c2c9204001c160701180c1100c503035060300800c690004006610b021122141900e9140d00b03005002105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902413129 1250 902411879 902411893
    0x40213020f070b0f090601140306040312021e09010f050c100b221b1d0103050709122012150703021b0c12070e0a02090303071505060f01050906071103 66
    0x11411503d1034000c0003004412201807818900040c5003a1059008151070403c84907248984d0700c01040c11034025826140168440541613920b201034400e0103c1c107800303070782c0c12005407082d0003189019103842030090b640c000800847c4101103410340500600004950841074005559503e0740d07100900440015100140c600210025040102035a000c60140540c80e4248060408180801065214024100b00e25100346003102240e50243d1070280034107140e1f03a803002c10a41401082103030b00a00c2d1518030002007100c2454580d00e078140030300d900c080c100f0000031204240d00c0c14648071103094a1010003022a0340d0f0a0b1000c200040c00502190207040d420000c0e2030420502c01c641503810080e0400500701c803200c0c9424070000c81e407041a0720481d500035084c2408004000c0104c0c0b508040080b070003607203581120b00081e080d8880c008005015114800240c994000d81e501310612841c0210b0341c00003103070f280c2e00040d035a40c49048034a03035104204214000c0042d003000300480c08080040c00300c40034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902414379 1250 902413129 902413133
    0x30915150518040308160e040507050c0304240f080406020a030f020f0c0c0a060c031103040b280806150c1006091410051c0602090301290405040213020f07 68
    0x580d6207116044060b42c0300100b000f41500130440c2904214111942c1e01c401e096050010300c4015505000c5200da916a804104090b00c6074081e60010381c01c4005403941c403039131208150f040180300002c01601050b018020100e003401b0b28202500001e440d01c1d100c0003591250b4a45009511030118102450f07914500070a8000403032010b00000300481c805103a03540d400c0e1032078078504100410303c1c0d8440c4d20a42824010240d0089070340420035498200701c5c2844454013541380c1140110307080302200034000f007010794401d080c0f40794806c0741520000d502c001522940f030b001c983c0c00c08210b03242500071200705000c000c8040710710018180ca00901c02a40c0e0752281c200300c140e00b9510b240d03102207a905e4840f203240c0400200038200c150004075035030558528a107884040741c695002920b0070380703083d03441510000038801150103c5103080340c014000c004c0c0071800407140d640c102a00100075008041090080fa5a0030a84105400703580c004003801c0c2c1455500c95011b01941c4038100d4010042014480100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902415629 1250 902414379 902414389
    0x3010e070c050a0f11040e19170304030e091b0a05030403120507050405011b0f0206090d1e1712060f030f0709020d0e0303070e010327050f010c0309151505 68
    0x38181c4c424405951400418107200d00d0503400310703a00501c07540ca44500c410f12000300240900070840c0701000304000300d03a40d003444282808942c02c060b407285000010481099441944507031038040459410915071507041d8009440b805c908007850000c4000c01407200110700a4025640c424480e240200c0b0002c540c0b541e440c00e0724025104c20020031004a0144800c0d0f0b0054245410501a1201401c0c43d2030309031250004040c00d80310290080400240454a5444841c454541103400c808114240c2c500303130303865101c2c440c20807500f6240440c0c0c914a26030b1480d00103003200c92150f03c01100d1542d42c1c44005c104005820386400725a81403042440040005109102c4100209032105005032074041d0381c45a2420f881003020110703265041001000701300e43e00030140c03481d44042032800051945d4940c034003500100d50381c0c1000e108075410a241104000d40018292400d05900d002030000441a0ba01502503c2003580010520344100d100e1070314401e2203a00011100d160100d00a4066680340c010079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902416879 1250 902415629 902415643
    0xd09080d0915060603090302060606070c03020a08060604050c09030c19081b0a050301060e0109020f0d05191a012003090607030903050c0d0809310218030c0603010e070c05 75
    0x5a89003052081202d40c1c910b01d1055038000c1c14982800d00054866035402511403000400c203501c20300c00803032082c0504c08a020f254014517409000e840c8c0c01b1b070712111215542d407000c82c1c0c124459410100000d4515000d00c041d1041035001a00130100c0c10200d20400054000c050b0240920001c0043d00207000f20341045407551140052940210140c001414031444400b6500018041e81c10110304100e000c144041040c110361211100584915400b41c0c40d40302807003081c4640000038100f00030f01c202101e5808404000d003000348030401a82010800d0810140f600c0251180480c252034129103080850190090004591800b92032900001c6800142142c1101c80d0960000d0766051051007044802c02c0381a9081c1c9003102e2111340c8041598901410740324440225000321482644400b40c5075140c1c0e82e511000c2082180c800c8400328601e6a500250410000801403444030400c500560401050080080c480030b001c040c5103a08280e69015040350251001c8100700004400c1c84c00b06800380300c43c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902418129 1250 902416879 902416883
    0x20f042c01050f190b040911130b03060105040b03070801090308010602160806010b0d090f03030227100c02030a0f060501090f021303120207170102030603120a02030d09080d09 77
    0x400c0c50014402a8000804003048098180d0307140505001400340c0111031264000c00712925800d5808500ca0340c5030250000c240c60f5a04181008825130400c607032042d06655007041a01c40c6140c2001c1c42c048001a5102c03249034a0305900400014044c5080a030408020031001804a8071080d64600308682140d200c0d0505500041040b001405401c0d41449112174443c0e401d1440e03007030941000075441c0c946606205117000404001441c10b0080c2064000707000003a042000c02c1c05000039400c02402951061142010036200b02d1210103d03a445803c081e1000c1101602003150521490800e0b14030800111050f645031050f28a14000181603d002d89081480345d44003084551400542000390b450303144002408a00501180b5003090003400d60000f00c0e40c11811011088215140c00c0c0d040c04615001403110302c1d06005401c00c5400150011070203828181d04641d00520450058081c0c5e00842410b000180c00401c0040c8082c031150304407903407650061525601d400604024501103035524001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902419379 1250 902418129 902418161
    0x90403201204050108060306100620160609060f08040f021807050702090f0405030901180b270108130b060102120d0506190b070803090c0a1701050105011b060207020f04 74
    0x14407080d68405039503034001b2019401802c082c1040315861a004149000d11400c02c03100410282c002c582500846110490a40685500c012054035540200c0302601861020903240e010010300d017403180140e4038460165035289905a02d0319030703c0000400480b482070741c3c031030000c2c01c0c4070007600c04c100e80a41c0280c1039131b10f6199403000580f0600440e500300034011458840b01d4410003020520100441d0500402441d203000b40e28156101f80641018a800588603000d010600142c4100600403680144180601404580811800440320000219004008211030b900f01e4000250740003800e42d00030805005517104100b900c01c906405410415401c00003507103a02c248000c134103299195201c4030841022012842d1309141030381c240391241c07007402480481c0000026813114070600c41d141014200034080d1110719501c9001689003a495114400654a80000003070f1642c086c4280400011b00d60702407400601560710341c1c100035040018140d8002104803d038100c0b40c2d407540b007403004240e04041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902420629 1250 902419379 902419387
    0x203030f0a090b0310030807061517010e0319110a1208040605060a0510052104061b030b010c11040207140313050d051b01050c011103010905060409020904032012 71
    0x4401080320945600208010504000b400300e1500c0010031603055a8108211f00d5079400c0500d0900020300b07012144415040d89080040f0781c0c0a05d80510000740b0000700024403e5882180000b43c0300d11944001d6400c2d95000440c920419008908000b48181024123481260103103031600c224172005035000c40e0004484204010801217240b091580100c001d071003d03020503051402203008110540b41d034030240300c004500360422098195010099003d40d019a0102e8206441c042d405400206002d244181241c0c016206280c441e00c90103205160595900c2c401604684400c0c40c0f4501c405c07030309034019800300b040e00c001c540740f00025802000b014000715992252007004130481441034015501c10900d85004001007a40042c4860b04800011032040003404203000503a03103481001d00800044d400d040e60300c003420b64a60007071412120803110602040d5070380801c0108550302d210b402503101100c807011401181c811045810104c208008040030f59180c11045071074103d0342d00c0890981c0000003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902421879 1250 902420629 902420647
    0x7030f151403070914071e0e0603190e060603010c0809120d06350307020d150207050d08010501090e24030304230f0a0f06030915090b0714030c090d0606030203030f 72
    0xa1902404541340301c0328802511002140149000c90000d1414030270040440880c51720a200b08200f0304241002d041000040c200e03210f2a83c41d02000c540a6109500e044082c6001c24080c040141c40b600d90300c406070020b01642c101d99a17698011a007070101040d039482000c184035440c50882d402c3da1060320440c1c00b1b40300d80c40d01d80b280400c00071400b0b603013039402c203001010040c0c80d0a0354040b60254820002d803c1801c040c0411340090140b10b102800500c941481d42c00f5035034002c02d081d4181c44080e40d0fa005200c2d1240d03040300585c1d8041c0e8500b10040c071019103c0c10204450030380c02006420060641c0e2401e41c0d1400c00203074203056032110050b00005c0500c003850360300d07100881d041c00da0f00941c2d00040040c0b1300a0003030762030032061080100303140c1c40d03118580801c4003048142440380900d079400c10400809040800e23544d42d0071500314022640e480100c4110000260580344180300701d01001d07181610090600500e6460201f007211b00d01c0d12080e000c401a90280040c003c004a41c090564842840c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902423129 1250 902421879 902421887
    0x5091515032b0c020301111314011407030c0f0803180f060408040e100302040f0b010809011505042a050309060123102607030f15140307091407 63
    0x81c2203504000c410b4015640300141018000d11005103880c1007000408401d0f0002c030707014044200c5440301d0f8407000105241035150301400c00c025142c0c0c0e8080b003507800c2910303801900c1e41500f03501c4201c0746100034000d441c001703445130020910003413003400070403180031540d0381c3c0c0752a80e00107a82c2003040e6200801d0b04102d18008000e2070100c800c01000030301c210f050075122900239100714025080101103045c00103000c21803100e07404001f103501030800c03c2210500991034000b00004d2210a002480d40c01c00300b40d000c00140034461481c00d180d019481b01c24904410800184250030100748106000c641c1a601300328107003070044229005031913248d40c900e00b410903141401e5058000e00780120240440000780303074504602c080c400005a0711200c3c018009001900d1015003282c40021700e0000740011140c1c00c0f81480c006000e11b07a162400d2110798401004042661218900c40400e8030741d1a604224011500403500c10110700503050b220702d140c03200707403078805c0d9070310004124001c40300602408031040c0c1c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902424379 1250 902423129 902423143
    0x3010f0905010209131a28090917070c0e1b0d06150804080a050310081920030a1502090303120403120c0f030e01021b0106141f030509151503 62
    0x80c00c8020003140c0c4c06d80c03842c40f80200c101c030072560140504144001c100b400e03c1d51491095040b1210308000c040d0b481c403460300034004e0348004542101c110020215a03107890300036502e9080d0300800f008025400c04c2514070400d0801000b50a147c80e082c1c059840202c1c0000c000c0180c1500d0403408240c2509201d81c00381c612440216450402107007004020100b641c101c10b80745d103482c03e40340840d46c80d01c41a0305081e040c2442c1c1c0040c00f0364040c089841030300d00003600d10b00022a22403c100000614a030441c00e030740d480007030202c5030190400d43c00c01c40050402840e0310310300640e404d001420850b8020109203503401c00342d21940c00c0089a414401450341002500400201411090241c495071002c010050070702218820185501c0f25900b40404c0c4080d01a54024500001a80c8003000284000e5003c1d02e00e500c14407080c00040807a5617031508100300c44420048900c01d10031070340102050110020700b8010710040345030040c410b40b903541c0d9807498881805036458846a00c0e18442c1c1c00c00b01130030300c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902425629 1250 902424379 902424409
    0x80d21110d0b03190f0c0b21101401080606040e1e1506070321020c0709110f0901052d07050d11060105190305010f0501030c0b07020d06020903010f0905010209 70
    0x1c090508071302c1920a201e4282c0d80681c0c003282102c00140b0300c0c84c1940c2e00e26a150070110754480042113076400340580c110140c01d06040d03c0b012841c00e0300c8903414882c00d40341d0b074058042c41c40c4a1030044c151710b5016540a503044240540041e20745582e6a80d2002c0d03054050301c06810350f0b03882e0152207041c1940465281d400191340100d0780d540c042d120f40010091312400d500282400031000d007e034007500c0c00c3c2d0000e0b04a0000000706664542c0c8800240da202d100b203010f4011450300e040d150803507850090302580c43c000c894a13851403412141d600103440b1500200d032200080c0c19242c4160680700d0030382c0000070100c4540c1c09071603221480c80c508141030046880384141044003100d0503144035078002031400c1c1111000d958000c06404090140101402e051700050107a608005244449003041d60081c0c1c102c80c000c0c0706d0301c2045034a81021040a128041001c0c0d4810742e00241c14000c10a20381c020032034258020b000040c548081c1c065041074070100ca03400d881503540400c00040e6410111300d483d0300b8130 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902426879 1250 902425629 902425633
    0xc0c06300705091509030a0309050a0e06101b0c0f090506040e060115170108060f16020303190204210c0b090d200916030c09080d21110d0b03 62
    0x45400d210003803290042c4500507200380c1c804d4400c98514540da07021074202440103030544180c1071480c20041d01240030b41c892940200d41107440000c4800b020146207001d884000c003070003264101c0f05411101c0074018195003c240034100120000280481542001804000541400310385480304d51021258010560350040b400c04080c42688540032070f030719040d0745102c40108040000b80c1e000f2900318401c13450b200703c110740300000451010800203d40e44101118041050b40b541c86050070035100f83c0c401920405a4420f00200300300049400041281d004403030300050820303a446a00d0300f800b00384002550321420701d80c4a060180952182100c0103404107019040c50608888085444801d1031203014043c65a01480c10640d030740790704003600c0c460000404000e51410040620500c03944400b080101182c038200b20100002d00602c0d400c030031102d16102504480074040415507000020103818590714101c5180d040c140031081c8285102051a860402c1c1c48031900f091072412240c502031214426 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902428129 1250 902426879 902426881
    0xb120109120c03202103090d0e0303030112021804060f0501061418040b030307030f0f02070312050a030905030f0406110a02091b0405131a090603060601050c0c0630 72
    0x70030780011144c0e07a1300b0380030201c1c2802158111026401e0001c05d080700c500800d00c0c808941c0201007a074000d10b010702c0110381610404802c007502501c0e254a4002100e0b0150070038401000103030b5201800411950028103500c181a99944811501c030004440850744290390310a06001526244121400340c0000e0800341102a142c2d00e0410040c011403000f24120290072038049440e844a400c203138854000a01160b4442030a442c001e01548144e1094800149401c40319482245c4002441d004607900500a4001502c0b030030b00c1250540c0c00140030a0615480705402c10004204200900102401100c15505c1e18142240200f20001506c40383c0c956a1003060403030050795450016580010400202d14403000844442524502556109030740c81102c0459603103076520a030f04484c0c40844440194032101108008001e400c24094900b25016070107030780000c00b194003030f40c01400c0c60306a1030100d03030b9032003002000259990710a4042081c45205035415108450340d904004148104c000d100c0b00321 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902429379 1250 902428129 902428133
    0xe03190e01082401050904020703210504152a020120250320032505062d0c0405010305160507060b0a0902031509010909031709010b120109120c 63
    0x101001c0c40f0b070911810f034400500c000c06a00880c1107501d03c84010b1320a54803905179003009030000450041032400c45a5240c0c010081075840e00ca094441c591007008808002c3c0100003100003401d0030b0405400f404203840c407404071207103407140c40d5004000c1ca900200c2d07a00756088241c4110000d21420444121043c84107201c11000110b182c0a9a2108036141140614500b030448460031941481c5010600742c107850341c4142004001045441d0780d1002c039a4643c40c0d1224480a43c2103d418081c040d508900c000c200e1302401404c52000504554940c02c08664111035030305c03000e1400355841042004001400c216550305802074507405070081080100d070780300c00740c000f030014803408400411541ea104506091a501c10424201074040814210340701c0c03a0495483c101b10b021031140c28850ba112000018100340349010f0406040d6055855080364503080d81c0b04090050b016140358800e540300c5803124041e4440300c0d101c4841c003c0d400000b0a50f40707000d05081c46040d13401840141005903007102540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902430629 1250 902429379 902429401
    0xb0d05100e0a12350f041112070914040210050703020a1e02031005011d15120a0605070c112e0c1505070c12030e03190e0108 55
    0x140c0500e2120108032003496180316420860b00d80c0c80144814941d40034102202e40c8690000700e03020000c1210046104190350240d00c8803006600042c000c00c3c000d00041c1d00c0f29950484c2500a07114142c0844640d443c580050200014502c018031150705ca080c04008200907401260180322000c0442283c038101a004180c00c54054250300781444000200001018800c1080202440d00140b042584211000c0145c0f03000f906171b04c0980c4a403161001c1c03811181e40714408c0380c8c102c0e160302c01c240c4515840815860348a100040c4000200305101003a89282e0710342081880207031f08008094140701e19649044000c0f210081c0801d0108014510b2550000c3e0707908030ba40d03038051000c43c2d80300d14416200c1c98606850b03042002440411900b600e001c06815000100b115030184507107450b103807490a200c14403040b5581211581c00190481341c1c0c21001c110101960311855415150102c0c00300004d0541c240785501110f0201e0002121191010350207500c00540b240703041c02442c0010f164200020541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902431879 1250 902430629 902430643
    0x20d090e01141212031005030c040501061d0316090507080a09031b050a020a081617250b0301060e040f1a040e0c0a03050303010f0e07020312070c1a0a0b0d05 69
    0x380504648218101d401d0f00c20003031048414010100282d407454018031200308003c0c1c5101e0769020b0f1051007078111541c80c003030180c01d042e20659582c15040c140d00d0b02c4461b000e07040b444400c68160142c24003d100110020060102500801d40b021819041c50803008094040090042800c40d15081c00b1000103a80180c14441c0f692a44221102c44040c41c14018104009100300943c4040303201000590702002141d45c000443e030b1302990b900f007190740300003003480c66000d100c0420700c5802c0307914100c1c001603064090a4150b0a9000d807030100c981c94800144499200380c001c1c201045028000740c030246040d014130610700c808004203200a11a580c0c0b19208807441c020801d100d03645440800301000c00400955000c10801041100080d55a04085403039610a0084c1c0060b0108142c010850900c0041c03c03d00402042d40250300d01680683c2c0307107082810180100d0200881c00b83e83d040031075034221200d0f41c1641003a61400e401d040c40403c00e8101d8203020f07910340c0148039802c5c01001140000c11b01d0f0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902433129 1250 902431879 902431919
    0xb030f10050109060f08060a050319050c0a0e01360204050f1f1d0a090905070905010e0a1104051f0e0a060914040605100f0206010515190c050706020d090e01 69
    0x11a2040d247d080016004034525000359805103d140c1500740c48840404000503068090005c2d01c05509030b07841400048209401030910001c20751004104213070070044800c0e42d400440c002111010111811100764408002d03803001e440c4d8001c28148058545898500400002200c190f3302e8a201d860508102a540340c1c207070001d02c60894104030340c03405030000030404a1002449503008940b2628007034001c0c201c0c00c20550301c5100c1e0b104007040e00ca4807489094180c40158000d080d1941d5500b40d075001401044120307001884040c40700140d60b80fa0740068807042c8888038074825011040840040881800100706c0c0e00c101c0602ca4100f1810750044d5256095528084005d00b041c0141743c0481d01400c00350b441a80c01824003a007901805a100e07140320500b07403540c1c4c00d4500d01d0741e0700c03810802c1d240310380f07003d040d0001410801d20501d22090002d40b0703200307901400c000c00000b88a03280d80703060181d1a480140581c11982ca2135004030f070700840d0034010f010f40b0105403250754140740707078216404001022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902434379 1250 902433129 902433137
    0x604090302011103010b04061b0209010317040905010e04050d090605041403250305061510030504230318040221070504030c0815010608040b06040b0a0b030f10050109060f 75
    0x214509041c0300307401a40300399481040e156900d59480704d075882030398858800c3c080001c1c0341c00302d02201c548a9003159070072141c000706440120313401d40e120110f1000d60070121030915130f82000700040418050003458001c2c582e604040030203103018141142088864000102000503640048c411250000c007901e06407008450380d888810681c401107440d100c4422204004441103d034003405030705091040314260b070b10510135140c01e5122030b8201d44090046021159000c1002c0d83c0c0210b0305072085d88800d074828002d030809180840d102c8030362a0008598040d41030a6000002d51104807420030b103010055510580303045141240007091030a02d01c040c42402c544d81903100c0041f84445118009072006903400004500c6801d45d03c0d101640e0b42c0c07880d001520b0803c0f03902000052651300440b002c510854010609981507581c180c104001002d050760034544c85024085c2c04180003581401562290340d00000d074032094102040c840d00d95500f680c0c4050b0400c4080c2038107002d0b003035008a40324610106818 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902435629 1250 902434379 902434391
    0x140d0c060e12011b0905010c03020309010305130b0906040507050a0302030c060d140709051e0d0b06150708090306090a0c030b07030f0f0504060f051b0d020c0303040302060405060c120604 82
    0x51502c0481d18540c048640c00d10014858540c07015804908240c40340c2c46902000d035591006403942ca100b40405005a04284000f1030320354025045994407107200110341c4c1c00f00c0003030354801031414006d031085805a4400010041045820856a0b0150900300d84411456156600090780c40e09031080180c000c0d0004114801c2c1c0c2d507541e41018602523540c030701c40303021850500e100030811011441414410380017142c00090721804219000425403000e440c1110f54010340d291307403016080c05030460340c00459151046404200f02c030007502c16180300355040c0c0e665401130002c06151000c06021807409803c0821000002100c3c141568201d80d8044500a5240d840003802d500610207001135000341400e0500c508001c111a51203a80f059201e040100020501001e10000700c80c4100da403141c10300d003007400c0e020480c02e895028010700400070f840945411512624103003140c01c01c0e1400c0f0302592020042c04100311f01400f08541c000a19144181001201d0503641c5261802030300c00c40c02030381d540b2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902436879 1250 902435629 902435657
    0x30105090d0c260703080f1312090b0a030b03010e0304080a1428300c020f0406140102060c030c0306010c030c020a06020c1e0303041e120606140d0c06 66
    0x82090341e2500c800b8080740e8032043d00c2903000b001035002c00c00880c00129204005001d8941c0110041e01401d1148807400849030070340d4410008151881d80701c003d0050301840007800c0540d00000301070300070b441d690105641e2a04410b050a45200c003c003e10640c000384410f0110150000c0c20f4040190050380b43c401080341d00380050301f88014108081c0e03030241d6021580c0c0d0514429414034512a100c3e6605006506206925904128003a5441c1c0c120a0301c490041000d1340c070400e0400c003220300081c6080b0b401c488440c001003c64103d540050f8101e02d40900e00300700c960b01400300340c0c0e00c050340440c040e24602e002101c8840c0d5202c024100b40c10b2044501d603a42c14507125400006000f58003030300c1a41441d48800010755900610400e2a200e00060940a54030b61017002e41c80300c042c14007400550510341031066440071416042260b03500c1030380e4107000083e40e0924403044500c140c05031400080160600018050840d01000500e0003007840c0148040081e0222000f10201c7d550303442c2418170341c0012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902438129 1250 902436879 902436893
    0x51b07032a1d06011218030f090b0c010b04050f2a04150206040516050105031b1e0a03050106050412060f1e06080c040e072d08010c0e030105090d0c 65
    0x5811402c00812116004890b000604528500401c07090700e400761100480d400020a82d002c0c4560030210980c042c0701c3d00d0000380a0038200401c0c8d0b01c40c1c20140080d544980d100c00b840e070811071f14042c0790780d11110303040034606141c0310707941e0010b81101c1168460f1504611007046010020a200c507050f55245402c40c00041120588002c2c21405000000002c83d482000356034140c2664151101e000d13661542c2d145040c4030128404071041030319150705566603514002c0788062540c03400d0348412010042e05441d2201c1c03840328410a51404101d603142c80680100030100e9005803c60020f1117001c00044c4200b01d0300342c0c0c00d14880740d8071440c003190003400c1c0c2c458a0003400d504400701500c0d205034410320610118681040040e2040d80007201d0444003030030200130540d845145000c3c62600094401e002040180403124580740c14a00701d01c40da0040001325a00e00440d550090080da5541c030a203c10490b409a005203244004400a100c50305001c69825141c0c00130132540f5090041c40100c1b00200501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902439379 1250 902438129 902438213
    0x31f060506120a05060f0f01030f0617030a0801050103060b0f0702042403020405160c021203071217070306140f0f04050403020c090c07260c0d051b0703 67
    0x15044035110400071003202d02200d8250f40c6014441d04041c0080d000b0309025818030361a180c02050055203501c841300640091015443c81001241c442002254010341981c0300440d0f410040003e41c1d8955914800030310819040e00958100b5041c40b40403c41c800c403004c15100a1003008400641e10315991000800400c820402d624606100465003c10340c081401d060007100c0c029170b01480b02d5540d03014196a4010f030010f000380421000740354000075083c942e1030450940410b02c111b03031406d16070f51100c2c410301c15654010300001c0d5031034580c00e810610361132109402c0310407401c080c050107003000781c2896186a00800c460140340464442c00541c0d40729804204100c0010384100024105801d001f903c50a00480c2c41e4020171101002c204140d8200707003100c21441e04881c200c0e50140b90700c66030400c1108480540035500c0350600c2102000c0100380250501310109445240d9241c01044503409840c10303021510303102d074004603000c0004c50403154207030102d207442000c642c6002e4441a005039900790 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902440629 1250 902439379 902439389
    0x506030d1d031e010f2a0903061517030a091e12060516091a03040f0b09160f1d0a0e03040305010218060313060c020c1806090702010b031f06 62
    0x1050307101801404a21404140c1d0380807100b0004e04c0800740e03100415081d41c0c1c00306d60341c00c2160000c124124031903002d45808507032840d4901e00182103907904d0322400c05071072540d86498a0405a90360400c041c0711a40c0104190b02862000341d400c01c00b0440c0050221000381c42400031041c1c100c0d036042880018100004050311104002840e00401ca084c94401800111000044400d00000582a041c020450388040300d440c000c0c00e8001c03a4041480207280d80000c1d00840e0281170b03043c81d14000692207590540704040080c010140480300a02e003000c1129168400c1000040100f4240310521030703000000705070704c1100c0003840140c50f0340c030003071b4020807034007d485019000104010003080f0303045d001800034801c94103100178805c076003508220891100b0707624a01d0107138201d042203000a8240e0442d0640010600641e018031000300045021001d400d0515224a11800200030082c6040013074507820000a20007001070021800c0840c0e0f5884008400540c00301c13002e900e543d60783d03441d5001074001d80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902441879 1250 902440629 902440633
    0x70b0604060b07050105091005061c06060e010308030a060504020c031e1b0d14040f031e050601120b100e1b0d020d0608010e010509070504091a0c090a08010506030d1d03 74
    0xc400f9041c40d0b030080c90150b4240000c0d001e0710116600c6820180a03082c06510300400b21001d59080c00d03100d002510710031400700c0d1300c2d03500c0d5000041d45d44020140c180c02503014003100c0d9500e2a040d0300240803140b003034100b144103620501c24840444d0001060b1000c0003442250031403075003642c00c10202b0900550181300140c904440f0a0300c06002c020070410f4100c05c03d92a14403420810740d003844214002c60092800d007809100341040440c6041442d03c588a064628510006030070791201d6040160981102c286000840185820000e040248651106500101da0340d2103040c081881d845030f40c0a00010080541c10002e5045000501c00700c400c440740d503800441d5034000e10f03003000018007128440c160389946048010400e214041c081c00780b0440c0c4003c003512100e0f05100c1000002e2104201c2075502503001d9500e80c1c041001e031900207004d0a01031042c40c0e158080d40c42003140058643e008019182d04040500445480004d44010a4001410071400c0750301a9543e1600030088518400c0e414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902443129 1250 902441879 902441887
    0x40510050712020d020d0e01050a270608090705011706010818030a090509250f03020c060108060a051f0308160605040c170d0504050f040b151903050903070b0604060b 73
    0x40e50001344001844140f6000c1c1c400b05d400402090354110700840f9400d02040301084407400b040d10844d01c1c01c0c0e401100365404c600769a00840340380d011028a81040003c944038405110301a2002c0101d80f000b05000d10385003542d61411025086080070113080141409088804114031100c842c1800b114080c0e0801102e031504c2d449000141081500c2c494140950b040700040b4012405924101406680c864030041090f214400e04076406003216020303404141d400e21502e4544007060000b680203150040c0200424103104c0700030801c80308003034614200c0d0241400b0440e4400c000b06844401c80e5009403030a51503200000c00a1410310040900825451500c0100704c20882100c40c410f06455007898031013a07030301307041c040c42e5605c01c1d07910910b40114100b840b00304001e180c04e03010038500c184080c00210304405d244001c01c4074203c19505c110503188001c644948201160002d4142d985018903041c4110b041040242c2e440e032052810180c100540d003c00141c00d900d841e00040c004004240711142c1da = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902444379 1250 902443129 902443163
    0x118150515073f17070e12060a06080309010c1e06090b07020f0118020906060c0303131704150309051204090c080a0504231c09080f0105010b0405100507 67
    0x2100e020008226075207083c0c038802002c22881040b003510280b0344544070114000307880c845150000130114003c01200c03900c441550b03100c908000c0c04505030a8018160750421852150a0320075a40207090326038018412007520780e82c040440c030351040e08120171590f48100c0d806020300c04c50860b0400392000c1c1c1010750f900108602c08401500c240b10303c1d425607051005000041342038414480e90801c0f03540805003d40054134006030402e41180005100c2d500c2c01004500c25030a50300115281d14030180e0341003800091009070940a01c42c5114031303414a1800d810b0808814904c0d40c15a018001c01d0341d02d000490810008100751160306484980143d150742da25100349000d0511804c0501c002160007000c1040d9903100e024150203541e0001c201541005000300c6404010480c0d03403503048a106900881da480b02021040540c034201c65540c641d03606003009240c51800e000d0315a404074981c5840010442d1404400a49080e2a41200c08038160f0b1000c0004680d1400351201c05803901c11004844c0361 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902445629 1250 902444379 902444423
    0x60305030a081609030c1406190305100f15050c0f0105010e010603110708120606120f06011409100f050405090a0f06150c0f0f1a011815051507 63
    0x2128651100f80394194140090f021039010b021480000c1c42c95107404402d00c0f10b015503c01401247c00040c280700c3c2451103044008914102207241303030020940c1ca00510041c40c800782c840c20040e1a9001550340414500b00c5041e815031200890031042090114007400403c4c014000401902010303002400156120410241da848084c401d080101b45000c11903490300041c0e0003a240c2e081c1d0008030050a0030a42100c403000720600400c49644810208514540c003d40d000c0f4081c014044050b00b44105e05d4003d002400001c100500350060501c24804140c00380d865920038040d86020303140503105104c2c14042074500e4041c6421a940c094505400c001307608403160701441e00700c00310700c0060140a969402c0c02441d59801e4101d0000941c4992418021940081610607041e21420600762840394644071143d007070800c41214045120b032640108031042010241e12880c44040b0303000c00855400e04501a007080c0c50b803040d54002c040c07200c84c24401c02c0c224003d60701d021b80c00402c1800010b80780c616401e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902446879 1250 902445629 902445631
    0xb040f140c030f0106030f0b040f050601030302061f081e120409050613020901080c03101203050a08060a120b040c09020a020f100b01080109090c150e010221040e0703060305030a08 79
    0x142c001c0c4500d86200c44500301c14000c2004580d040303038202d58045036580741c03c141e40400400541d0004282110040020401c020050086010340d0140c8200d003445410301007101c2c901d4020304051010380c0c03400e010204000c920301594294028503090200c106090041c1001800f11507070070262804a40001c540c13103190006840f44008450541000b20958094400ca000d107091140c001400705002844680d4080d00442c1c1010b650801d21000d155076030b80d001300003441404110002140801c417014080c0e044111300303412038422650b1aa456007418000710030350070038004c0034184215030004582402032140f411005060401d606648c0c1d03e4003184041d41c1c1d40380082d4002d06510030080c0344082400395200b042603110b0305070b445480c0341c0d19290f4400c015182d025000d9552504801c0e001039409040030541006411a8130745032003101c010000a030610601c0441c8501012003230b10004e0242a101003182c00b034480c0b446110345203498400781100208441c0d0802005c41c0300016850903031940000e421 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902448129 1250 902446879 902446903
    0x2040b0a200118110d081912050c07031701051c020d024606030b03010b03010f05010f06141209071205101a0307060e010203070c090b03280b040f14 65
    0x3800c130203150b003000d0144031381c40f4403005080c95005100e00c0c2d500d22184000c410340d03e149450003c24050f49000100101c038002c0e40c0810b10804009488405c05030001a08050320b450606441031940c034000114440d41940c0c60400c110b200c034910341800310740c1c44800036140c940c0c001d000610f404100444c03441c100c0360124130101c803d80300c0c130741c00c134420f1504039031340c40b66000303181808102c0701d8504070003a4041c040c00c0c0301d003c0e41552900400c00315038400748100640e143c3c00442c0410154584a110b1007000305681280c0100070b484000ca4010707102e000111040001d80c2e5008102c0e5507200e8825a0401c0c0362034000703000c103903c4507100609100e00041d038600f40c01c440c40d030104116004085e403091400c0001d54642c4c0c00d900142c0e405c001660050110000c1c4030b40c1801502d1816001e9030b54000e00a02e103070400d01545a07200103812845c20200100c01d40c0342c1d0513040010b00050718000520b032803002c00c07800a00c0000c00f1000103041206440161801d60360040c5c48a00e4a04000750190f00c4120b0300f140c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902449379 1250 902448129 902448143
    0x3030603121603080a0e0d030504060b04060b0414190b070302070e071e0203040f03030210231f0b0f210c0418091403190302040b0a200118 61
    0x203a441406075a400b1030350380b41100c0101c4101500140d4096508410041604843d25621515501e0914042c0241c0a2007030407039400045e1441c1070b103030141c101c82c400c0b04800c2c062407500d00d0034404200244101ca0940c0c48070300003c024202c80800040413035001650480000f2900c03000082d00422040103040a0b52181d000d44241035294280780c0f00c001c50855003480003231000c0c0118143c2a20840101555804500c19280b0b803d450b89006d04162000d43e10403001680032040c0417401c000320b032254260b650780084e020803003005c02c00603001d0311001c007424a80141d08100c81101840400b070100500034560303000e100d0744809090450b000d07260446900800f800000151302042c104c1003031107092281c01c3d4203851908103070414949141c0d0060000441c039000707a51f000382c02d0200f11000300c01207011003842c00642d40c0321024641000340c900d1007810741e0300703040c01407205000c1c200b440003d40c0c0609074140b50604000300307405c80c00410300d089205009015481c25018500012040301d03061707400303800340c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902450629 1250 902449379 902449393
    0x424050906010e0909251703031003080f0c1608010b09060102030f070501090b01030b04050708120a030b0117090c010219020a1205030d1505040513020306270f03030603 74
    0x424000c0c1000122100c5001a0010f1039080c02490450300c0c090300502010708a034121010800c0300d030340780e41308828040d00c1c118411a042100c031107250650007242d0300d200041c0d800c2d42805c081e155054071b10740c000203221640100d1381c0d8000b481c0d16403e0303c00e400720b001e00b280c081155a040c0158440154016281d80354200881d1260b02d08140140500810041c0e00940c80c0040d840300c44a150740260104688654071810310340d011425009495020b140200880e070300604292814a1924040d6071062803603410041c034200901f11724506881c4102e10034140030078060980c0b00120390b200c66003a1f01c4120191050140010498000341102c900e40d8280c0031103038000c110702c0c1c6c611260001c020000354045001a000c1c0a0440041d25a100c014445c0d0708607420f10900b21214800da8403074820595990744840820000c51034240103041d0001c0038000d09038035500164022035182d0000500440f5400340c03240001590201178410a581015240150750880d02e14480ca03e4a175030050b02e0a5100344a104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902451879 1250 902450629 902450639
    0x2160e041a040f11040905100b0a0e01180504081c140109021303140f0f0105090c0105030903120702070513051e0c0a0f021204031a0f010f060e0f0424 66
    0x40d00780c034080d5030481d1203d900c0c440180e6900150008840c44160482c0d02c0f4040000000d104103c1a035509180250115203076000c0801c6c00440c081c25071148029489444c010400b003c10314090180800703003014080342c181d0b51410a04030521070a010b02401d40184801d42c00084080c1d800303c1450703010504101e065990ba102c142050780203680c505c084c02010664200002038010411164000701031040e03802100241c803035182444182c1c03681601b5070b5100ca003002403010042c0b0505402d80c4007420700b00c0c250305243c1030703485c0d0301c2c061450040b80084ca45400324a00500070000e1400800d030081c10b840b00d11507999500303000f4010030b50700c081c1508000c04042c000320000c00e05180c41a50312040c103500b0490000d00440d01060f04400c12070660042504032065a018900100007642c0640311644441e8803d0f01003880846d00181400710030524400180a08807402506c401280da291810542003403041d40054104540d2117462075000381341501209918214490400c0d11311140700c0d400920b144d40d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902453129 1250 902451879 902451923
    0xf03160303050c3d05190e150c040e0a050c16030e221d0c090406180b1801110a110724080901020c060a180606081b010315060e0102160e04 61
    0x68800340c0306d5000201d105040d060059000305840f100350f0702200d000543c003d44044001e84203036030b0603012140024061240d09580c448641e041800800b04000318901190350b1662070150704a020a500030300e06011040c140b05192900e0b41ca8001030191040705458907900c0f2071003102c1101342c003e23103040102704800c00214082107074480c080b01c00600305040c0e03070b0003c005510800400840d020303952081c003c00451106ca4030325001c244505012138050030201060076203041004855445603061a51141e0461900026a251070f07982d41080030054190b62086401c05ca803d0b0041c1c03200c5c0c21450240c0d10218a8001403e0140184e0b880305005074803190038480c03d034420707080c000c4410b521450100c1c00710802940014034852127400b107000c0400d210740d1100300382d400c1a40441929403111040c074041199441c0300500020090030204070003001c00d000b4480500451207800c041c0908194100c020341d00900045603008118500404010784940501c48030200035a003d8800c408040c0d28010f0f41c02c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902454379 1250 902453129 902453131
    0xa0f0c08010f060804150c120b06090a0b03070c02040e0a060e03031308090f040f0f0c050c12070206070803101e0321020f0f010b0f03160303050c3d05 66
    0x1d40c1080c03080b0b030a00c5015070f0100b40191040b81c5120b0740951402011506d44141038070f80ca03203036a400c144924543c010b6825034202030f450798804c00007046003080c582e40e010760034000c90307606994060300c0c1e80e1502000e0710102c45060002c0c0d00f080c24002c0f11408410701003043c510483c803400c0c1c1088500304006141d9600c0c04102d50b034102840e4081c0703000300422030480140a0302c110041ca484901c0900d28040341c162000d400c08290300540703a00b041680040c203030240c0c3c901c103600e03031400c2c0381000c09a52100e540d480480c03038107810584000070210705549070f0b0b1040300c60b081d402800701c96a07030a05000c113a0004d441440340c00c500008010050070b4068100d08032038100c81e00121141c1c240b100300d010102d0b00b4550304c1e03010b4065121f2040912017100082c01502440c02d08440001084803141c2c081c080030907503503124a4407a82251608581d1204010816000e4982510300b107502c0e6250700503054544240c00700684920a030100c50131a03000c102035074141c41c01170080300c031400101d82ca00d1000183c802c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902455629 1250 902454379 902454389
    0xb0607061509111b120a02061902210c310603020f07110f040501060504060e12060c030709180e0c04050907050d020a09020f1308030408150901140a0f0c0801 69
    0x14108102030f11405110304043d2040510304c182c0350317020381c020360070810f43d07100d01503890242c0c010004010b4044820200d03446410b0560034294034203a21821001c40303001c0c40d0072681007003203690804030341070130400c0040d00c0e150614840010b8081303640034980240f40704401b0380145200208031020440c0c522034020760703003000907104904e800d0280d42d03602c00d0440c031980c50034603400c40f40c99030805046a03547d0040074020225911900d030f030b407420940014030780c40c2100401402800342c050344003036610000881c0c5501c405840305154480d00c0d50035003110240b6103070307025800c52074020800c038200426076400041602064003c031141c901c07060040c4802e482c000c0b40d00c032610350030080c810010780c00d100d03a061700c0161004040c0381845864881c440202c0c3c10410791070030708450100e940f4000c23000d0301504502402c440001141058030301038020b540c1c2c840900c46104034019031030118002d45030035009540034295a0091541d20324217807070104010110340d0b43c50088203061480c5000214004e00d18075050321 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902456879 1250 902455629 902455661
    0x1002091318021e0904032c13270803070801090b0a05090612070e0601022a0d02040f0f090c14090115021e0705031006060c02040f0b0607061509 63
    0x903569808012100e02c4207807460055110f0350002803410365071030040c984070742d211b5110380701e142000c400404540c4d20074009440c8441d4808966507400e50340d96422086c1420021b0700410118400340f201803070842503c600e03040101000f01214100103500d405144076662541d0f0b5024a6070362039803010195408100855041008090140000d00340036a94980c8058068240b044850725046076500e0070455903c03d0001c0d4040d4801e000d0300b5a418082e041e0340800740c1c09008000804243c54081c980c901c034860511030414405000119219500608030300346038108204000382002c3e01982c09404030210881e1801c80503200802c0500064000d00712014000d04103140e1a030038100d8400024510410786403d42c49100d00c0420342c0c20514a8042e031500d501030181c1a0103260806240c54078542c1d00c4580403250412405210903a0300c016540801601210b02258500540701d4480c0100500304007036420900000d00c4509018079a000030042441d51524802c0705644c81501342c0844051400a8802c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902458129 1250 902456879 902456921
    0x20415080121020a050a03141b01121a2205330d1202070e130f3003020a0219051203090309040204030b040302301b10020913 55
    0x2050500301d000d40d140c4080c0600070b800d500c860020765608040c1c1d00c101d03a000b00310451000b101d98180302703e00022241060740ca0000424000103404005071510550010307907250302d00c010807024039001ca040c500c0302910129000c000a0034100312a80d500322400300d80c038204800310b464110290498001000281000c00130080404468800c40c0700710300400d0790010400c01e09074003041032000c0049110b181900240401407030142c018046550007421810132407071919a0303202280041e20b600e01c0044d44503207600707440e000c800f030004460495a91807031079500c540440215203903003560061181d00215002c45a0803061118400d201224031074004000307401441111103900414406150001d0210090303906000e44c00300031130100d0f0841c0e071080e40c03403440103001d000c1816014042881942c01992580c4580f140341c40d041410991440c40b52008e0010010340e1042d03044031005048440441b06081e50708658005483c04040d411400b035007442000c004461090b05a134610a91700e10041000d951040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902459379 1250 902458129 902458169
    0xd020304290106081602010209060d14221707150c180305030d090203100903020604020112140c0a02030903010608070e010f0f0b1b06180606010f0203070b0a06080601090204150801 79
    0x101705000050741959000d01c0500080c0d95880064140303580d09032000134461242810a504880015100105510001110540c5540c3e0141440304240e04200c00028442442519413043d105008c8003521002c00c07403000703030070b80080354000003080400ba50300c0385400308440301e03440c4c4100e429100041c0f00b40e0040000600440703403500003403013180c00141911140d040f1120204140c488070481140184c1040003040110341e0480402c02d403800071795004004444a18045800d0110090110181d010000c034204250502c208202c1d0312050015000344441942d42101d2555220140251284800c00b0701c004aa03904030b0b10311542c01c40304400c0e082000c05181402d070880a511150480c0710781060303800d408010a41c04c1103c01d0050b019900c001c046201c0032680c25090180260100d8100101344000442566001050344c030266008046c035107098480707801400040c0100c0d0301c116154020364000113410021035001d0021280580b511250103a003803581216540000d008540114a0341410101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 902460629 1250 902459379 902459401
    0xf15030b0c070c0609180b0102031e09030f0102030103060b060705060f0a09120e0321040e15040617190c1e091b020c06040f050d080d02030429010608 66
    0x1801c07000d00d030780c41c03450701c0d40c0d54545440c030038120b8100802003400240d040088004201c4080c0405840e05400c0009020a5000039124440e110302c51054040480c08824088101c90441d40080b0004044808400205400768042d4100340b10542d401407500c50080a80c3c1400c904a03142654094050f05480d80c684240c0c100c0364030050710b1517442c280d071001140300254030580300010415458680800c690f0306042010b1a05813003446842d00252100b1030b12241188860031380c0d05541c544198013140d60380303280b0100406031104c454682d1141c201030000507894102042c584800c3c81351003d9903402070044482400d10400c1eaa0300038000600f1074020081c5400908401c1418080c00502d04045030342da03002082a03810355150001148a68490b0080e05c2d5010440c0703210005040d1040c5051600d44040401b0300c20030303445128068810004140b04000c0c07144111003038185032090071500c2e4140b0b03080041d07201c0b8903241c03031401102c1c006040501340c00018008504958043e43c501e0802e65031405817603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 902461879 1250 902460629 902460631
    0x41a06070609060906060509160219020402160f021f080406050612070303020610090b13330330030b012f0c120a0809150d0b040f15030b 60
    0x595101e581e02c005400082040c00380020460084401041850400041200100c40608291621025007043e0032505401152070181040000c4d5070310b001c498a400403030f02030b100c0d01038150140103408203403200300080803191310f01d01802070307945001c010340e80e560703034004e006900e50584081110400014001080740d048564032000c007804125a64400c4960309191040c00c2e0411009a00076008120204202441070350080c81c00a0301031003180000d1010800d91200d01800c00045a00c640300c1004030f84640a07829600122451800c20f0203e21002c0061215841d0004845070031041032045189401030900302005a03021b04904011041050240c0041c44c40780b400e9414480e02d0b0410403018151181c500a00801c140f800510950060044604143da460340075803081d5404003000410940000d0980e501541c0b12540039600c179207503000950020641c05c2c001e43e044100140745050000c0035081030315a0315082e5410301c0500c515042e10030546010800c100d0000420040030404144808409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 902463129 1250 902461879 902461883
    0x611030f03061c06390804290903030403030b060703023a020a060f060f15030b0907020a03030b150706050604020903010e0a0b010b030105091906050a08010c0e041a0607 74
    0x480701442c1e0750b54039050350728a40a100145c2009010b9000c0c056604491000d8424000018851003001c0711000c1c008210140c00a01702c10b183c2c04690503003c0101003100345481500326001101e24040c0700056070307a4030807901180003c0c10a0f80781d100504094054a404a515030041c10041c074900802c035180d401c20500c0001c00c9840c007410400300c000c9000165143c03104c20f601900c40c000907401e1840640b60040c14540390300c1d26040d010000d5030410354460b42a01e40000c0d04140714480410110301402000c2e115076481740b0301809010b0881d400003920b01065220b034505000808130142048090809850f0300ca03803454082104500251b050703440607030310150045c00181131120300808030342141c600d414110078587c0040b101c0300138026070620b400e00406112410614560400010a00500d0050004006100701d4002604860081e4019401800018080b00002d55403804e806010707203882e203406400300d1b048030401d1540381070900846205007900101640c00c201200c00f0301070030b94070941007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 902464379 1250 902463129 902463169
    0xf13121509150506150d020702010e0a1a030703060f140108310309030506040b0f0109270f021f03060f03020d020904050a06020f030406050901020909060405070e06040f0611030f0306 80
    0x70801170320304200508a510101800140c4520082c0b00140c0700c02c40c1c2400a522441c4030140401088407580c489020045a030320841da00c903150a2800d801074982900116628101c1074404141c54100010502a10600b640d0343c2c9010b4031000c00f2440c00301e00c1d5440b560f01c40103000701c001d200842c944101c1d00c8518880e16100e5000382c1c1d01d4a4450401303100761411503035001c806050055a60100c4405805400300c0c40302001110200075840f660b08841d140e803c691400e1a0b112082403011500000304050740140580403900800001060034403807a07085040400d203004408254403050b0801c0c901500d502a216026000d510707001c00c5141c283c018404c441ca48103801805000600c0e500203070010001d202101078403818540752070402c9e107070b004040d021941c4c418090192940d0319148900d8105005a0300010325448002003120f070780070240c1140380c00020020780042c00640d600141021111180e6441c1109500000c80d1a01c0784a1003824500251050002c00c200b0725010582060101305502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 902465629 1250 902464379 902464399
    0x219050a0c0503031602070b0a05120a0216031119021c050f0a0c060e062503050903030a12060803090d030e0a17010b03060a0e10020f13121509150506 66
    0x10b146407442c1e10480c1c900c9201e0540204036008550100301c544040c042d034151880c142030380f50703000500c54090a44c80c0401c400120020580e5066030b80d04840340070700c0c080591021a040e508010b0010f01c840510100e00d071040c800604100c0210450a0030b9407940100030740b1207000b10f1042414141c00784a0161407a0003608200e1348241800c102d55020548111042c1d6080b034980000541103421108180303000e803900300500701485014110226505951192000482c90203050441c1e0718050b25807519051b02c4009240380900e44c00c074601365003200e070702007050210548800070b89450340200a5296002607000c6000c40c0001e005003031f8141050310181159550030781d41ca600c54004003c860307401055035910103505456050501140f50711038440c00c000c0c480309803401c0c1e419075680c9078130400030600d075070125443c0c002c02540c2c1c00322003200700d030445507480090b20b4509001900988000454140244145d0b69000200034003c2280c0782c0d40200108400c2d00b880030080f405054011b001503800b48d40f0356 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 902466879 1250 902465629 902465633
    0x209190819020a1509031202060106090b070303320a11090111010b2d0111031914340c0303030e0a151505010905030c040b12120d0b01030219050a0c 65
    0x1c003a02c1940c40c0300345e64809035280b5609141501c0d9043d146901c0842d0031080062200b19003151409003102c0310036000580d03504c3e940c203046004021b0380d00310800507400c1d1081d0044030000c0f0500c00000d5013144820f102c003529228031400c200e0ba48050800110002484008043e60282c845101d481e50040008070301d066012000540040010031f82d03241d95850003002591071401c81d08680f40100c030a00300740c25050780d000c1019649014110f40b0010380d841407250400440e06c150500441c0f44440000d2a440c0c00a4110f18800328101e180e60710301700191301c04d40455176110040030751281904010949226401c0d501c085025149100d100d018500c11070700c0c0303c00000d0707044600010291002034005601707000e0200003011400954801d40c1003156510050020b0359010443e4020300a00312030025110070000302040010440403640445405441c0d002e0001ca00a00000c21900d0a544800c110322040200103400720b000300002814204803240c3d0600b80903001364010040c0d66000d040c5107004003019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 902468129 1250 902466879 902466899
    0x30c1519050109021b0105040b040803091905010e25181b0903030801060c020603011502010e0307080304110616120e0a031b0e041a0a091202010209190819020a 70
    0x380d03c000c00031640028032030100400f49041c20000c48001c4000d1000d800c01e611914180c813405080545608000000f290b040001040f1402c0c55480070045c04038900f40c1c90924500819008201a5050048a02102441c0f018001822035001319403140150780741800d00107103420040c0e040542c04550788501c05900071002c4801402980d01d1030f60390103426030552400500c0c1c004181c4c060820b202003000240c006a83d490280ca0548207408101094258240c804070b01525032101c1034180340c00000ba8103428090b01d80000d62040b8001c00480070071221074000d028903403040d0f074400c0303050002da01400000501c000740b100281e0903251400a43c1100c084000541e402001d901c203c482c4203a03210350b200d0211500680500410f042140c0e58058601a1a510920500940c24880c1c4013001c7c40050491040344d8480c1121030781001d46520403ea5800002c3d0003540100f10f40781c441c4586010f0851610a400704040548001b50068155045003a40041040814240403a880004801e000c40c4100744 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 902469379 1250 902468129 902468131
    0x2a18030602130603020a0c08070204090206130f0e040c030609051005010b040f051e01230a090e1302011409150307050918060d02060306040213090b030c03030c151905 73
    0x440006070344942c5a000a260b240480d030040091500600042c0b08280c1c0124010f108250040703000c4e40d45060510000e4010421300000070340c00790004c10703a44540980d802c512415540d64130b07101e06296880f6202400c220380d040354011703d40500c400b407c2c00060400e41040f0801e41c410b004503004c0c80048252141500c0d0300f6000000c003142c0200e810407141505269000040c1015a0302c020040c11031014a0030002c800c1c81460306020b14145d080d14104801050511420407400311551101e8103040000c242806078807469407045482004100d14640210721201160750584443d4001c1c545460310007250380003881c041d50b008074812404001080400029803141d61a95107a82e607500c0d680c010404400d60081044404000b488108032068503000d40e100c0d00550104d403019201da075a900020003a20a0309416001c4101055000607030104c0c0d07411141412108409075100401a0000c0c590b49000d80742d00141030b60301c15845075801080390356401d174020184c1003240c95800e0840c0b500c6010b59078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 902470629 1250 902469379 902469383
    0x31d09041104180c03060b010507140705120c090a0c03020708070f050d090b091c1406060f15041202010908030307210501030f020405101706192a1803 66
    0x150004401015141a00c100481d0200c1943c1008104540351281340300400c150000800741c941d03c401201c070680c019015582220790004840407054403400307981c1d40340d022901c01d4600401342039196190080002c921056498409424041c0c00da4038192100081d0240b0346004051603402c00120300424094001410740038081e40700c0c218003c00c5850020b00d040c8812040c801088540300041c440642443c08580040100301d510940752180c105401c41502e1782110010041540d2061010b100b02000c100240704640485002005031900c00030710540112001c0381c1207040030104828001c0f092112040c200580c010b140c00e260054480351554034681c03041d694038000c95860702c401102031602c040304420030443c1e024140300c194034564402c1c00f191521000203125503107490014800f207480d016400014a01d0803169103218040084c03036501d80b41c1c10f540c507240001e141b02c3d00295402460090f204030607820301100c8091444208003001c110340000300c0f01c00700548200c600014940524054010398 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 902471879 1250 902470629 902470643
    0x4140d0309140303040302030406112d060c0f160f0c2409150f110d0c0506060316061803052a0f030c01050708070602030c09010206180307031d0904 65
    0xc10181403210703409542c52002c550640c000c02c10440081e5001c801c1e2801c5407024242140800410150903003040d503000c8403801c2480d4030b1001d55000c4000d580e60078110301c46210a5411a0b00c40d10b81010300d0303103d86404465841000c000c031000c0e1078901c00c00381900e03500489400e2121900b90b80c0d40318078240b29510058102045804440029440100140350001d280c2016008107207400c0d02c1c00c0c081028401040b003031046819121400354020b4108006c00d40d9444140c33800a28010406040c50f06000001c0c2d500740302c0c000c002501402d0000e080700754200346034020541c0b18a02102202c0c003444150301c01c10501e6070f80c03400000140d410003080180d000c00c42c0e40001b000c80c16070003511500c43c800309154400c408a018021140c0c5002c258640d046200f881c00e80d0380c40a04c2d003810040c901c01c1c004004c0c4494800810803030f117a80ea60700a029070f038000368240d800c583c481300000d1104038845284444c241c0c10070042000000c0c0120b0203402d400c020403003400040c030010b01c0010b80c0c094040751705440705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 902473129 1250 902471879 902471891
    0x102105010e0705030906070e0d060c1214010f092a021b0103020711010305101d07080903040f060503070e0316240206130303140a020903011514010804140d03 69
    0x9501401e9066840000e40c40d05505501c2c004002580d90340010341800c0034804000070b81c0d8500d458020000d035526800c0403080c0410003440200400d018880968808003d103010744000040102a20050403200d4141c10074150604028001c002801040c0300725000032603070145009121170710510702d80c445060760082d21002c0d042c48049031101d6481d0036901c1c109841000541d00003007041251242208007882c00041c1941e41d80d21056030441190011103030b00980501e0039a01100040d4024800c2d03400760384005860311218003083e540c1c003890282c200e80b03c00000d42070000c04d03c0790029580c09072492602d043c40e02e0440300400c0c1401340074822503d2802540000380101103041c140340ca101a15a02e50010032440d060b4001d4442c580541004442d415240d041c42c1458425048103004058805582c3c00c142807200f9110700035807180000038002c0d404e0400d0522948407c842d603c084030452003045d6103220080004680f01e21008004440741c12514140030310740e890400c07008a128034962800505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 902474379 1250 902473129 902473139
    0x12042105030c0304030f11030f190203070b040b0a06050901091d0303060109050603090f031306030b01031b08130501111312020127081006060e0a0f0510210501 70
    0x14148504110900c0010400e20058607180011a41d005406141000c09807205000c01c071341b14450300004056611011500c140010f02d44801013140b01c0c0c1d50030340c3c400b1603c04070200366128042c146000d80362050f00030014010810000c01194080300810000890700c4d11103000941102c02a000422465a26a4449540c03611403900c2c04c9641c040700c004500b9440c0110000344072111600480d400f43c039002c4045200c2c5c203410021002c1c44114041625120617041070f9070398040f0240c3c402ca1000900306200300c115075010388030380c0402a11800500c2c0119250300390581d00004054649540245120950710104030207108100c550036030b044c0c00300d641e1010b00645081044168120000d002044200080181e80012418418044000c060740314030205004040705ca4000f648504500d00880c4000c010382c814176031244081d900d454039410003032800c0c0e02c180403d035403290003070324040440340d48180558a041c11844909411926201028041c240b08041000b09044180f04145445000501c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 902475629 1250 902474379 902474423
    0x3020702010806090f0117011d06061f0912140f0c0f0609100e0d1e0b010611060a0e030708070f05070e04050c012307030206100f03081c021204 63
    0xa081070f011140c1e60080d040044031205d8181c818400c80002c1c15008240d400d0442c400e400c60341d80040074064140854801c4018181ca50360100c900b00d04c14114003550050590005200c1c500d01070080c3c2d61402c031039040c40007a29445500351030a4a0b41181141c007002d000f1030810408035400340c2600a4a11542d0076401d01c12011614000030b031040b00b040c86011180d403500800f007010300c0440e281c100840351203000410030b420408040a004810469050042041d1aa0b01882040d10030344285900383c0ea078160465400036001c1042c06241c01c58004551201441d4200c42c403060f000b0000d032841c0007040e5440e401e003a070040c8400c40b0000403203d200c5043c40b4081c068203004020f1806d141c17080f890241d480c55150000e402c43c1c581031022801c8120141c0c4448606c17078801811103a64940d660395a03060103542c0d00021220081041c83c03080c404a001340070b46030f088084130b07402060b950602c1a11151440c650420307004042202d07a00b40124200b03404120402e501a50142c070034420411442000300b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 902476879 1250 902475629 902475631
    0x51c06060207141c0309081501031518020f2d03100203070503070c0809060301090b13200c033106021605060309010b13020406080105030706081b19030207020108 71
    0xd0030a6060500d03120742e5071160910480c25081c18054100513014601c3c041d5a143c116800c0154644542401035211001190340f4a040e01d015102d1400310445485841043c1d9121024403524944400900030050510b00c030012104e07800201201d042e034044102c103000342c221401c0c4950141100850742001406d062254002c469075100e001e40ca103203800103000c0c00e04c0c4806468a4204160302c521002070000c05000c0d148003400c01000b036592565100942006030002d1103101d07125408100300840d0300205403050100640003a401c0c4522101d80c0c1100d0320075a00300030006029800204000f80166011410318081444104007103840075015140662444505811503070a641c0981c141400b207c801c268124100c84d4200c542558130740d80c80554501500003184a1342d0000245102200c140c4070a070054400e442c0c481e60381e001503a0b038500805645042510985011903117000c04580c202040e210740e035a190320384a0529140c00103140c01c00c4900000c14001c1400a980400c0c88400c56034003075081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 902478129 1250 902476879 902476889
    0x622110a02150f011d090102041203052802120d060801180515070203030112150c0e04110f030c03070216080313080d141c060308031501210c051c06060207 68
    0x202e00d4079030412005d0300d646034070461201440c41059000a0f606202501160302030700d904100040c0c0d1140710718020b001500186032030040f10408011141141e01a05410907025442d41d00504150510b415003e42031750040c2c245c0d840b881c2c0c80f424040f4040343c090042c107259503140d8504100c5030400703042250038006040078001000392000c051002c901d03800010f903415520380b02ca036403900070a03034903005000500c5011480354140c20444028042900504842d203803c209403402d20115900d80c484403400c1c40ba191403d129003409002040c505001100a0b690002e031a00440300680c0603180b40ca007100d0410740c04014640e200048409117904a9a014001401c024000317000c0c1e0801d0800c09042044503802c1c84002c41408560310494000d100c0c440300041e0300c1142c0030030105850741000c1003154021141038038802d450600690340d035407095507003515141d0300880c0a280d012085540501a0208050843c100813090011219036000000c40081880844200090b400d1510501074240701c8035a01c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 902479379 1250 902478129 902478151
    0x1b0f2e030c09030b1603020c0f06010504061a04090504060b030709091b0602030307032c01020d1b140c070510020f0606010f0225120302060f0f0622110a0215 69
    0x30810004d41124100c54009a0750250640c1c40300e12840114001e0140c1581c074265440741c440d5180e9280000708141d4180c560990f4144015511181191a095481c41007525900400c11040140c0714060380041e40140c0f0131031000c075a2091250000f0b1406000d50404500c3c5590380040c9000c0045d0034901107401140c0f4079030104610303e0484080d46a0000078000000c0c15100c0011904d40621101c0c0745424800c2405002203254098002c0350003374000e0790070b5800310780c43d00c1d040d101d81800c0d00c00c07141c1080d038042e40c51150542041107500415007014040030310710f200d541d001282a590b044000424441c1560013070250302040540c1034038141c001382c0740d40c0c180b103104000d03d0100d40e030204056902011410100c00703891002030621170906050752044039209980c215000030594007080050103076000c400010360035110000024088542690740720303488000020301d240320585081609000000c65200011010500c0c90b207491f07140d100d0034840005130803140c00301c000f0a082c01e144030f0300b105080c0c00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 902480629 1250 902479379 902479397
    0x812091833010f03091a1603061707060c060906050c0304260f0921010e0d02010513060b180132030703140a05070f060e01021b0f2e030c 60
    0x283c03030702c031000300140200b649074610503041c0214a28a940301c4606540348030901d2030201424010032441d00d020800090a0480c009481108810266000f036000c00107000c80602d0520103440c048a40b603c201d0b1480e480d202c0c0040441c0d024455a4440c0a55003070003940c92402e0300e070200c1c95110711001103449545803021129124290f00070380304402402054540e442c045800080d101c01d0031441600723017240c407070248034000e1001900440e200805500480303240840c030b40000e0b400d07101c08803400801c2c8918100b4010104420350090340d8801006000c0c841d240d501c00c441950070707010980149ca8032030042c444402c5d2080545403c10f41032040004942005510f02c000691182442d10005d400300308892140700048078241302402e201c1c0d9100040320f0035546c0d1074a40800050952150700086804101c4d2010325500115815a0141c94440750040d9100c5840070408241340001d104d942100e41d401c82c034550014411046102c04804203010211035803094801019284040f80340c0c1e0411000384 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 902481879 1250 902480629 902480731
    0x80303070f0f080f0907080a0f1a090d08100b070c05091317180d0302010f050622050709081209041a0303040902030c0d0c0c0506090708120918 63
    0x940c3e140e0f008034000c00b00e08255120300703400707a280031002c1d0000071560050f9460003080000c40c40215200380d10030034092521441140d032240305031300d00312030118640e00948501100d0921580b00d1650190700b200354080c850751110441025500548001c0742d20180d460002c0c08a031400c42503480c0d001c0a06981e1700800e0f005d6035500c0c064031024005946201e200403c440c0344480280b413045460302d00c05090428140090f06009002c0d255a0034940d04091801010070f80b1401c155026401d424061400c9452952180605900400f001010017042010324000414502418089444a0042002c0950319140444200022038101150141c1299020a4001c0180e200070007580d044821604005803a03640383c0010fa045c6214803503000d07c0c0c4600e040a50304c0c445404c281017044150140044554a50310f030402580e0714080b50080d1407060340f10003961410550b080004007000000070b4440300c04030700302212920070303c3c0d419644c1200c2001d1500c007048031a49101d59a0701c100e030752107206054000c07410b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 902483129 1250 902481879 902481887
    0x7152f071a0d02070507210614010e0402010804020d021c0302070b03100b1e0f1b010e07090b03070e07021c030c0914210106260c060c1204080303070f0f 67
    0x15a20308521580c000ca001341c14004248007040042c040405a0500603280041340201d0361a41c8000b00c600342d280500490301c0e132542000f00303416030704124200d94081e140e0350019074041d02c1c000c0080b039114920548407001a2580f109140c141040e0091000743c0e00c02038074029040c00e440d5004084191000e204110810244601680c121440da0074002d0361400e55200c0c00720f1901c2d00030f0000794070050001d0650090107a1800610781600070010407010303a40d042c000c0b03a080c1c8003410f1200500b0382c4540e400340b09280d00b55010781200100101101c0358a942d4803a00d24010700d040365a0009030700544c41402c0707000500001168050098a000c0203859810613000d45945924000c940548020b83c0c0d0392002e0b03484000700c07070740d0f644079180507040c4200b03082810902030030081c010b607030b050f854510b88518410707101c100c0b0310311446070a0050300c0c000d1650000d000135a000761100f121a84a08098201c0e603e00c203000520207070050801446c0d032031074002006080324403a0301d8828204100d07003006520b90743d84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 902484379 1250 902483129 902483137
    0x150608060405030a05031801090c0f060f1416050609100c0504030f240e01050103020307210f0f0b011d01050a0e24030d0c0b0a0504030207152f071a 65
    0x1810000d490303032100d440403140d1003c0c10044118239031900b20b018041c0662200c0a00480354440c88210009446003421205240d8082d400c0c800302d01144400700422140d10040c101062201809510403c01619554a1300f6801e46503d051900703c072030b007405c48468901810110011504140b40f50514643d01c16424100403200a88254412404072040c0e4500310316501c4c02000d4810203020b0810080e0655008140a100891003032180c071000042610021300c0c0304144c00c15000600d4042909900d90012051000d81c04a804220341c400c51000075000d1413840d40a02025450051280e884c00c109905403101a0800c500c41c00051b00100000350204034082d52148035100e034040030740440c42011241520b40394443d58580901800800c03142c0e4000811418140515074110150301c61410f010200e41041d240540140c0008406200900c003e40002c3c00001d01e618001d40c0400e52800c1c403140610400780c1c20444070070200018819843e08101d02c8000d008510644001c2c800c68004004a03449 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 902485629 1250 902484379 902484397
    0x3070303092604152105070207030b040b070206010608010501020c0415031a010e070503040f140c041b0305100608130f020301020304030e0f04140118200703090e100e0a020d0915060806040503 84
    0x46c13624005000c0c21701c2401040020365100161100c1c0703007000d03c0c02051105080302c000005110321000021464414502541200c0060b0003815100d9000c4081c4130150160004200610030001c400000050050000c19a618140100852594184004103211040160003901004420f02c10b01c8003050f081001d100f81c031036200d5039502c8541c03030352000c843c10b0181030341006074018540404000c00d541c00c07103e00782101000307507400c00055484000c01c0041c01d00703034021840080e103001e00190100c140020b0f01d0030051300882c0a00c02d004100e03130000742aa0300032503045001a080085504050504003680300344148200c41c1441083d03400440383c240758005100d80e00801800c40c1c0d240a40310415030081010040003045104e0a4078030442c00c8001d90b0006604400003180d80b0000a40b0801c1452a40d00a035a00d0300f02626803840c1009400316024051f0401c089240e00304a070507060b02403445203c0d030b000c1c03003502440003114500040394100c840a070b0003840c0a8000030304001c00103070003000300c4000c3c00e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 902486879 1250 902485629 902485631
    0x209060c0d020f0627010b1003050901060b031608071b0c09180f0b15040203040c03110306040305030a050a0b060d05040b160c021005040f0b09041d030703030926041521 74
    0xc170354416428050154019001e80105602c02400c10071a0305802a910481c0c03007100034000c155231103511020034032007284c0c12002c14808900da4044144144d110503000030440c0b8107200407480c007064030741c0b14804415088503509402282040724100700d020724140b20541d4003860400b150305459840c0109180d0400410404203280001c0f580b40704411120300212002e8030441d220714040c039050030540814001a107075480820820086482e000651030321442e856034550381943c031150704007400303040080c3c00c940c41244c9500302e0b22a16120b043c086c010109880c4c4000c56641020700b800d1900d105d0107800190380c28601258582d11079003105111080590644100090501500040350240181d070025205c100900400140644c8840098641b1030000c440802541c2985800c0700d007082040420558150003d1069501003030190b804001c805000d070384012004280c403214072a00f030b000d041c085030420301c000c1002e2280f00c0e40b03000a4803041c001c905104417400340b124545421740301d038031400a03211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 902488129 1250 902486879 902486941
    0x1031b15180f030b041104052e03060f0b090604020a230c030a0903150203040f0f1406070c110f0306190219110c040624030209060c0d020f06 62
    0x10944140014001005115640c0740c513441c1c641c080c01010f035016503228040e248000c500389010f20540303014010445908199103030b0180901e02151440c1481c030003030305800e24004042004c0340100d4007801910440000c010112001300a0b0002025042e540143c1c4140030f1914400c0d080030b940ca6803000c0507069076129018641c0101e520b8880d554a81049000102e0b2440c02c95030042440c03010b80744039000310404894000003210890108850103040b0890f0b400c03600e8045048401240616030003114800c5459105650f050310b0107200360b940f00c1c0012a03000d060b00520500741d82c0ba0407070010480e03038400c0c0c4903400000269500d0002d48000044010384030440304614172641102e000220312401860141d07450200501100383c4500340070050b015001803656a440d044c40380c8001c4c0c0c0d14100e0b943c80c410381d9040402c01041541003d2605059003000040c0c03290b50f900700541550002d5000412580c03002603002420403032950802070542c0e00007001e00c001c034100d00208121900380c50088140d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 902489379 1250 902488129 902488157
    0x3010516081b040f171b0315061c0b07090501140301063203010306110306091602011418010e0d08010302010e010e0402070f0b10080a060b040b03030c01020301031b15 73
    0x3031090360300042c140503591300000744421003452005d901c80450070991300000c40c0301e48010407540d0050210303540364000b442c0ca0701e00f010b844500c4540085014101001070b80640403100b4140020a0041d500c0300007160402442a60080720400506000c0c6014120040c2d40c4030310729100c0c001805030100384031801c8044600c6000032060158419400801c0b010b0b41001e89070110040d620030300060b5081c03800d10382003640c007445000c1124002e1038050302c40e84055540d01305d8881c0f41c641d002d07100d10855403640000e62180c030060082e21300616180554200c641300d00590136003103038000403809201c0d401c40d14486108542260714541129020308040803400305030001200c01e0751400114541c032038070208100c014028042144a502886007400e2071850b00c0d003521204c0798208034030680b0450340c0503150140028405030070040d61004090300c042488144039000a00f590003108802480b40c3d4044010814404001070981d1511b0f101c00d214a9100c1c00c00001481c4410f04403d80300030700c49020b1031300d11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 902490629 1250 902489379 902489431
    0x8010e120711060f03011403010501091119030b030709050123030a030807050d0e030d0606052a030c070303020f1b0105040501081504020f0a0e270705040914060301051608 75
    0x108134104c3c11340711580c079a100c0c840c002004030740c05a40d070b00940c6400004598020306126020344101c000446906100881400c0e01c0c1d904001032001d4100f5482e451086429201000010042d1519034008916581010306120402c01104a0340322481440024520345880201c0c0e00440c02e6003506c4d0145c00350766101c105070707a20700ca07800b40c04540d98900020368071540303c00300103401c0200408201b0320240743d0701d00e0116440c1c01070000c04600c1c940803841e006403004000b150b40181d1081c110580c1c2c142410120014144141c039882540903030040e175800318ad84a001d0016240041100041c00300200044000a025008600885051260303d00c007141106452204140501800800a541d41c20800e4154444dc0c1c00c000e04000c08504455072065a030310301801d1134600342c14140050309105685041b0200c1f040809400e100034002c00f00800304003a1102c2c05200e90055014aa06000707082c0301d006d05084900060030568400e407080200c10781294040c103c1a004071049a6501c1d000899800410b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 902491879 1250 902490629 902490637
    0xc040e010e15100e18030a080103021305160c050a0209040f0212030f0d05040302101505180c0d022206170f192003100303080105090c0906072a08010e12071106 70
    0x7178a038403011400d04203080d0300024160580340309984181f0382c41c1c100800503081d0344082d613000c2910304200d4460705007940706600304d401c124003940071078403100c078030b40c001c12000202964156407000c0901440c000350300341760001c0b03c00c00000100551a21440a08010581c01650901c044864032800030505151007003240303004d1168160810071003400c0d0521121941d030454031800d07010b50400039031201c104003500c3c00b05102c0d40d10075000515140140d23400300c000b5440075903080758188131080c0484100c0c1e00750740382c038024041c15110b0b2503801b60741c2955840301910080108c42e140c050602000f4107000c00e445580325600d43c0c51004071718252540c45103c11500424807020700e2040120030400303805840764107a0100d9001e40c4480300c0690321002030204a4908a520503000d05040000c641d090504400500a45010306030b202401c80b01d0b148501c82148044805000551100d041404450400e200700d405203090170b0024902c810041649600c10702415501410513101003543e003415480d100126 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 902493129 1250 902491879 902491921
    0x5040e0c0318060f01150306120b09071e0612020712030b04020c030c1b010806030303160504050409140d081b030c0403060504080c0106080706090b0c0c040e010e15100e 74
    0x264403103244c0055501040d00e0300344101648904c031140c0d46d10000c1d000e0b02c40c10003550720000038240790103441c0d1a995882100500f040241d1300c101a40040c0c9005d05031042e041c2e601841c0e8160642a1130800024840012810320890140c81013006c100010701c10781d80340720301a07c181000b20341d524079003002070300034003428203169854040090341d542480804a845444075a004c1b035501c0807034002400440e40920112045e6425a00c200301141c07003c0d0303400300040301509440c944103142a4499010406440f0011802c48408004007402c07040c10800703105040102851317180c105503a1500110883c1c0200c0e070b22484410350700f40000800c045ca07171340390129409503802c01001c2c40141440e10b4209030340c0c2c0c080c00c4e1045403940b81000205403c1000700f5035000302c4407180d46814149080c84010400f0307901004081c022882450b40001e0142c6850207000058410100002580940c0c80a890700f00814442800705d441c2028041010320030140400d14195001d184418802e90f680803010901100d40c0302304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 902494379 1250 902493129 902493133
    0xc0303180f010c0804091e14010b070c1e030317090c010c080403080a1e0914010e01030b3c1f020a0c08060601110105060a1505210105010e0105040e0c0318 68
    0x4003044586c0140c0000e40354422022501020402c0c480301d407822038900b00040d0600c0c1754090010030100221201030b1a2080c0501c009502d52952801c0389082200b038a0400800d011036600204141600700c0c5080d80c50011030890070204c0d05d401000a0b40714100c80c00c08505111000d021602806000002e5a001d56480140580d48070215007003d0083c179024401e43c0c0b441203100180310b18640c0315504010485e0714074140c1d550721001075401510211507105440e0b0416035900907401c800c0e5202102c020343d841c0d1088406900300c00d801c41c5c09903403c00d10110078204203a1001d140c0c0e01a180d0f1030030f94080e4040340340303c1034101028031012820200d0103200174100d007102200218000f003001c28102d00540c1b0907241c1315688800f05060364240c84d000c07030340c0c81c4c4c1c00184044c00b0048495003628030040d201e910b10704a8540071081039000c0c0101280100352030350700318920040c021941c0041d118030001d8001d0070310504140c07800c00290260040240482054480800401e030314080100425a0312149002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 902495629 1250 902494379 902494387
    0x71127220c270e0325030813022b02040b0102010c120f0e120a0e0f06030f060f06220e0405100b03010906020c03180603010b04050111120310080c0303180f010c08 71
    0x31482ea0300d405c180c2d00254070940150b0101400342d2060b40c100200f9034151582c911542d681440e040034102010000c0e47c000420b403100c4664003154445e03044250380014164107200740e2078010b100485010050003410742e890140304800140d0814040e0150004062010a101101661220141520700b0480b0725501c1590290311400c040e00c1c000d850325800690301d01024030321031000c01103843e00c52040f60740c000c0010404980486004000030b507201c480a01007001c8604c5020200302540c0c00300403030b01d60703581d042c840381e01c2141800c049100042c101005044c2460400f40c0b18292500303000c0001e00c1046556500c200c085407000e4100124460b0014811503c41c080c04600c0c07038895002586881c00820311044000140c035200c41568180c4203020306d0036050034103010064498015054000150b44224407400d14425180c10007140700f02448982c6114051800c01000d11b0081150070403442504240000c0d0341c0c0c1c2c000b0304103250314414110744001d6402104070041e1000e164441e00904601d80c005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 902496879 1250 902495629 902495651
    0x3061a040b090f180a0f021314120d11060604050403051228020d051303140c0a08070f021f0e0904021c050f0c01090506071127220c27 59
    0x159802d403045c044101c0500c031a46180d84880120300c00d01200c2c820b14401c603401801058888050004980d01c003404a1000b0a0401c0d41d503880c0001c0c0000301800a05040d4503a01c104e42c0600c03c01e50825401e035420302c0b080c1016540a0001d0041601c51842100300c00002030a100070080c4a01050b60541c00e245113107000c020010019612004c0000c840303608100c0070807000c40804495894030354065550320241c0325210f001111952040a0610301e80c0b040380030000101d1644030040c8100d5120350410301c0e002f00140706001c800300b2090480741401404c10050540260440304003454010221407017001c275031711440012032031200c2541c0600b400c40219094002c0060000f510107054444100300da2a1091071401129210841e00650f60800028030426000070b08a80081072882001071044058005840303003000031032010b507506d074a1032402e42c2c140010806902d2070880c4000b503007510b040c2d047d00c1903101c01261501d00c0c0700f1042d44100d680d01d02c4000c0003194071414101400054203124000040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 902498129 1250 902496879 902496919
    0xb0c03070c080a020a0302060a02030c01020c0c030c15120402011b0f03020c2706030307080f04090c110c0f0112061d0601051c0207030203070b010b0a03061a040b090f 73
    0x1400d4111007240003407901164414000400842c85980101400751036400c4d0350038094660403a4001350150720003400080c14062083c005040c407100b8040c000e00b507808558007094505001003100760300a1601d00902c1070940402c10860f485002e9025005110b52594401210440c0c4035006800702d00d000040080708010007690090f1005000758201d54080b035010042100070521640d6a860308030361515150720380894004450742c0480010141c80c00c0044507214088542d110a101d000c4c0c45400042c18442c08d9aa0f10847c1444201460808000f645c8a150b059490b83d60a107407c3c03190501c070704015090381c420103610700c188140c40130030b0180c9a901c2600c401d04d000006141190309032003034001505540f0070b1040e81c03408000106000c42c0d840b10401200001c2d401400142e04500040180401241c41c00d00301600a2100304441079540d80140b000030102c80c0c994020341070700f84100d01803142d990601020384095464000700540d481c6034540c0091041e041c000c0c1119000510740c801d40030b82d4405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 902499379 1250 902498129 902498137
    0xc02180a0c0e0d0f060914160b03040f110d021302090319020105030708091510090c0201060e070f1106010f0302090a09121b050708010f0e03120109150b0c03 69
    0x451100748810039a060082e40c45203160180e0b543c0028252124101003008100e8002400e0f0180300005407402d003503112511400d0b180c1d1151520b0307910480c1e50b4010b02003400e101000a140400c043e41c00e504040e03680308088000000d0140c945c0607052903040c00d40d41e910340c46042c0c203a0300034402d04403040400d1501010750000b119080c4240101c40503c184454103281c016886981607440c5850741d0b64114003603401c500c025140320171f2803040300081d1801403214544140507001054004545c146400207445c00d40300b0b9950704001310390507d0b03010403190003030708545030304010f40341403070390440382c811104980050390202240d81601c43d8000004203131442203000c0003628000d40b050031096644412400c160f42110b07000503c0c80081c111100c0600c0e01c501c0100000341d65052000d407045038903441d01840d00134281c00c00221a550342c01c0000e08980d980c442c501583d4280310165060014203641340f5201a014424920182e0301c0300302c0a0064110fa40c000c2c4003a2000b204055103513005038500c241d0305d400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 902500629 1250 902499379 902499391
    0x10b0c0f0609100b2e090308070302161508012d031a0c0f09150d0c0e09010f18020306010c050a03030b0a0504050c090f0a08010905030c07151d010c0218 67
    0x8544a0f0803051405d000c3ca41c2080800340300f500381c5003459400c082480c1000340c054410304200c0c945030301000080d640e00085c40c0c0c890003580100051801e40325140340c5008164031581500e6800c0010b0820186c105010604564a95041e09030b5140c0d01c0d402130506850071806d9078100c50b00d521011003002040c0304080000c1c0010300348600c1ca0741d140c003090802403080c01d07143e90211405102648051412055513000021140410390810f00100c40c031000b81c60000d541f0728081082d10040706000d08205032a14010201d02e4400d001d203918020360489600304009400f081d8540000000704180d015030450b2510b41e50040480d0044191402c0050081c00c480201500c110300d4000006094a0140200d5004031000d07150146090b003550100310000f000c01c0e031020342200c2001c01c0000e82240c00e201d0320300010700074006103544070842d200d414100002500040b690720800c1588108165001380499170720400303200078200040e5a500143c072200910400294003903800c0c1482034500300364a0003540248 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 902501879 1250 902500629 902500631
    0x20106031a13140a0f0f020103050606030c0702013c080912040e04022d010305060405090a030c1730010b0d0b06040806041a1e010b0c0f060910 63
    0x4803991480000c0e0720941d281c1030090030714440d0201203000c5820341c15829400c602100e001c1190350340e0307440c0b43d08a0210103a4130219a0701c020829942c01d4026140e018030100d0780e076461340c0303814414043c0310301135071314003030304110b8040d03c1c0f080c56044000314040700502b6120500c3d6040c170b0780d00c40d107010070607510000380006a40c070303010403070000c0005030212840141307400c0c150500d414030092403480320004000703036030106140c0200c0f1001d42c030040032800c0b00b840910307004000780c0807240058107840c805031800340121702e007104000e078600022070791844041d89031600351086101420100010318500b0700030215414009124915482400f51000002c1111200290300450303106e00380092030780901c121525040c0400861495000f541d022000580e001811582010b403901501c1d890180d00700c85c21181c4451505448101140c400303407203503101c03224210741808403243d00c680e9001c0207818880c10b1100e010101d581e801d00350040c0108401c42c001300040f20742134640200100d42e01e000e0602d00700006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 902503129 1250 902501879 902501903
    0x10090911190f141003020a021f051006170705070201140d0c110a0b16090e040605010f2301180302100f14040b1c0b063106021c0201060f0602010603 65
    0x70700540d09480f004500d00034100311070980d01910a4001c2c5d402198100114052040b0b8a41d20b07040310211030840c40c006100c005042c3c5888500c403880c0340e210303821940900c10081354a03411440c070011a10ba20641d14070344140c4034212480146d84c10704540404801103407022610070031202165100c4802d21809907900040b140128400507150201ca80c0d0142c0188520400610f16481d100c6004a07200d503d4502480c038a03982d0000540b103c10150b404442e07098444c001000152700031201400a4810003001001c6440d01201902610454490580c14483d122041881c40940204176200454010708110101c03504284c00a01c3c036002400302c134000c50148483c10b0a14194a4180c400b44c55402140500d0840b0f0281c100c0b001c082d015460381119919100075407170310f4542c4000f41200a0f0f0b207440d00e4000741c00d0055008190a040c0c000c03030044100440c01001059800150942c2544064181c91000820010100e000d0140c079041010502050307080041c42c0e42c0e0560202c1e0072640129054035230 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 902504379 1250 902503129 902503139
    0x306022a0c0a15020d030504080d06030822051c110d03030b012d1b120917031201090f0b060f0c0606030f0c22110702090a0510090911190f 61
    0x14106000c520300045c1d002c840d021315040d010398032890f0014010082c1c1c83c2050040c4040038159111174108403520000030400c04050300c0003264200018001c1c80c115003001742000c002c5503000d03403003840c00c140003008c0780b01000c140302c80e5034500c61b1945000f810b00b0240c444c850a0182c00781c6060100a8002040400c2c80304030012042c440c0d007100c1c0180881691881c80e00c1340105e55a10100e040758142503030480318000028500c0d42c40d414403030925121f4030001c1d841e294480700040c4510724040c10b290002c110038101d0007040b014003415650317800c600107130040200049a00602c56601e460342c10450001c2c403c429450400040e2130134001540c00c80d400b41d910301041c10f41385d0300081c1c9000090b9000d1003207030351145804202c0321441c0403403204030300c2403024504440301a68001c0c09040c100500004000c0150305105141c664861031240d810300203400c01010319801c03451544100203a06030388809440c00c200c042070803c0c541c41c0c402006d8144a080c20901070456025501c81c694404030340040000b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 902505629 1250 902504379 902504399
    0xd0501031a0402090604020f0d0e0f061e061e030f010501090e031306050f0c0615010f0e0306040314040320040b12062a12180c0a0306022a0c0a 63
    0x320a030303805444402139445000034400030390001c00c0c1c241e01426091050054807101072090040d42100c400040114040031f14101d41270407030141c401580e665043c084501e01c5044040e0264000320251107841c1e05800c0b6098020f080389120048541c503002e8204220903e04054014605a410801c400c0016480c3d02100da9a80e101c0c0741d042000c0307c52421000c010081c05040a410300b507100d1032820703207010850715100d401c25004031842c81d190141c80d170380b02e030f41035134040501a40c403006402e010004541701d5000a1381c4003c0140001c04010325140b01200502c41c1100380d40003154000080380060b0b04c803940711100442c2085425001d0be25105044009180c6000b601c403400300c0301c40280000703440750170f1010f02840403004010902141c0c03500760301150141400810603040800e000c1d10450810b80041d41e4070744400b80c05544e0a511507007500e01c15035102080f00c811658001d00046e40c9958104400040e0002c090440d03d24003c3c0d1031005003150004100300002132000c4070030301c04098072402410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 902506879 1250 902505629 902505631
    0x30a02010e16060c0818060301060206010311040204060e09070203211603060f030b061503040308150102070b220806070c0302120a09050d06060305030307020a11102a080d0501031a 79
    0x80300142c2440d04080c042081c480081901d00b0720f414220300f91b41c1c0e404001c64400e900a030f0141c030043c0d009600400c14400349903400e440411080f1001d600c3c0c14a44400200b406100300b488a10544002004c514400e000304100ca2103e00209404040c03070720032081004000000b25048040302c04650100040f00e4406e20415040e603002012080d0501c0c10342d210050304280007030907207400031510120324440c00314203c0076510480c800e5443c5529440c252150303620110b101d5030b03118199800014140030f1810b408054070203d4640c1028619170803417401404c8040d1034240c3c4151054007401060081041c0d01494488600b4025003c8881c2d4907411006c440b070a200f002c0c1004001402c1440030310444c6807820728810f4203805105c0c0428096125107505045a00650700200941d001c03000f0003007080f01c170501e812140c08048808142001e200031000e800003012400b000c0b410503502003001c9481c08280c11040049e07030031100141e1510248151100240800e0006032a004e240f515040f07141800c025621f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 902508129 1250 902506879 902506889
    0x1b0e030109171c062c042402090d0302060f010f0e06120a050d0e1309051c0c050703080d0b061e0c03070b0c0703080601050c0c1c05030a02010e16 64
    0x210025210b00c00780700c01c1c2904024a02d2121144020207a824112540074840c058104881104146405c02c0d0050b440300960390782c501568103244003080045100300c41d42103414124504104100c1c100800036400038070400e9000b42e0300c0080340040c442071560000d4001d00c96400c2001400315641ca6800104000c3c520f803080c98003105041740010580d090040c2040c80c0c21400e9003c650b031000d540d603903407803c081c010a801400201d4401d03200010380750540e075240780c090070008200006501515100c4e160501c400380d5034000d4021419058116215550040d0456040801e6030a102c1e103d1410700c0680d8031400307075510700c00c0c100507a443c4613141c003d0841d02048000c00d034441c02581184c0809589070002c5560310311601051044002144010144a204401c0c1342c2106507a444545000f6081c0301005e03001904101c02848001c42c0c07042c00085c0c400d0724030011601100d000440c50710030301450b09940d4004049002c0400c3d646030954054110303801446490b015a042a0b0365011030b040380788200d02c25 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 902509379 1250 902508129 902508143
    0x140f011d0a230102191206080a020d14060a09030f0f050a141b07031b0b070f06020405040c050c0601050105030c07030503060d0503070f0c0b09090403030e0a061b0e030109 75
    0x201d500081041034a10312520410740070300c0b90580d8a002950898210168291140410821144015601c41140c030006295442c04010f118107007000140d0b182c3c218480240284405400c000038031111503105481d4299042c101d5103d07151801d1aa0081c28000104070301051012080b00d298070702030381e60703086a201182e4849050420080f4103c0d90b0a840c0c0c81c3c035a844840030040020700143d112503681202c180800100710303262551070030354041c40c040a90303003003080b0309a0701c140400c034201c02c00c07541c00c1d580110034078140c00300d40d04080000303100390740c01590310602d4048103c081d1038104001e44001e201c0324080d103003584c0e40d070001581c491004550150410340f0400c4543d000178002e070081d68010202030300280d000070b801c0d6240c41c40d50b805010700341c0f148401c0111800070000e2815040c0050806542d49034101100c80b000f06801c5000904000c0605844241c000310720001080703003941d10364101c4010b2140160035192505155030250b47c2400144003040c0340c2c0b00c02c3c03e050094114072603006034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 902510629 1250 902509379 902509393
    0x50301091101181a0c0f0c101206080717010b1e011209020d05011b0e060a051602090a05090705011106010e040213020304060b101e050f0403140f011d 66
    0x200440d84807000c000842c4001015600101320340c0b142400211a444541e00070329a00c540722645549025441032244090f81c0c01042e8412030798442a00948204c9141e05007000c0040c408004240a080107070000138031441031710340c00034544410101c0c0440c80607a180080000401c40c40500c0300300d80c4060544410002030740ea022072203500c10061441d000b09041c02c001801d011a034000781c0c0d0403c0e00d02040d80e5581d15000300c15094102e110403074070f44a40a04041d074034550300101262050060348d20100a00c0000b14004e45a4100240e840100b03650082401c00c441c50302e00c070700301e00500c1c0a848070000c034415070402082d5940a03009500c66280a900200641d03032821008203c4620000c20880e0028514040725240280500203035000354482c0801040c1000754070203100001080d140d00704100300007842d00ea070b19407410712841d00169486280c05c3c0e03070310500c2c1040ba0074184220340c00202030b2034800c2c1403081420008242c8000406080009204c060340078003d18080000c012750044154010034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 902511879 1250 902510629 902510663
    0xc130c0903080d0204030503270d0309031709121b010e0a050f03030f070605070327060c030608070605071112150712140603150108030d0902031507020a0b0105030109 73
    0x18043d050700c400400000d860301d5200d0b6201c50943c0c003c06820512103e446000d40b101038581a00d501410a00b621108282e0040b51002409020140b00c050843d11001e83c0302140441884121042030308068210340b0034050364584e0b0b0351f4911040790b100c004000b039032000b5030040d0f10551003424040710090041c149203042800300100250402500d40e0306110410001d1003605101c17001d03202c000d001d01000030742440c140d040070302640c4189105427060390418903488440c042c5400c0039511244c203d580010700c00c0c1d10700d40580081080340c2083c901031092041c0002d50300e52080003400c0080c40f4488403140c90300040140305d40346c408200c1002260f0422203000d1002000c900790310f41d122940303141c4120160786850180c0111071140c0c4c4220442d501c408100681802c04000380e41e04400310f407000f45490b40c50300c503151b40c4034041d001810440644481c84001555020400034a02c80d0035148458014282540080c2d1345d8107242d00100c501111907000080c0920b010f1244c20031498204482d1921030343c100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 902513129 1250 902511879 902511893
    0x120c09181509090b0114031c0c022814150714030d0204120501051b041e0b0a080f0106020109020604030b130b01090e16150c0819020c130c0903 63
    0x50001c0265081e555100288403800c601452000d18018100c40d400e035410071001014126001ca03880d40203521155904580003103030700c40d003c40500c5c070b0b00d4107260031112440090489500e800610441842014102e00c4003001600c200045808980b0000c0381d0068074000c0c000345148441c85448024414000000070400240d007003600d0302d0303525007a24540444140b2000c1242c0050304900e101c0c007048201c402c1044424442c2070b40064100c0700a030100c040c2a0050820782c070a40c0a05180910f0015032800020907052440000d05080400c0544172040f440c4000c0030ba1000b20385104001036403c0002a4840c0180300380b100050b0080c101074030301419520f85145015000c0d09030040004000304003404501d060400781e0280040340b402041005007261268644091521420590784c82d18030f00b00210141c42c28441c92601040c1000340003d0740f5418450b580340189031a01301e004403208140070b111a808501301142c1d550450b006107507582d4180c00141119000d40900300890601d400c14000704da45 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 902514379 1250 902513129 902513141
    0x40b0d1a09150109140a2a0306090504050319110a0303020a05040512010f11090306011202010c14010b090115020312100b0f030a1b0c0f020d0210120c0918 68
    0x20000702d400d1086040148962003200f40d111489241d0f030340d1000398100180d214003642080800708103100c81e104240c40c411980400c1d1450380701406080a1040242d030007038201000400c15140c3c10000c51a00d030801e107803250310079001c6c1609480074648003442e02c0c0c000d070141901c0040c4640100b000029603501a0020350184400006202c401c0c040066903a4442065031520302d040b00021450841e46003000064036a03090000e1035003d004c1c410000b090310001a910b0440c0c4401c21089060107241c00142e0300416814005003d90303201d0340b40d14005200541086107040e500751030280183c1e90360740f90929a608400c0c103801c0160410046042038a2031708096640000742c2854040c0840e5031502c00030815480b008003c04050800b004001102109110743d040d800325140c0c100140c00c5c040d0750000c01e0b9100301c880080c0b010100d5442c0005540390b00b18203080013135026010b0080e03201d21410107807219540c002000a100d0514044a4072248100a404101d034000340a80030085090b900f280040c200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 902515629 1250 902514379 902514391
    0x60203030f06030111031303020106090506180a020d060f0314030a0c0642050613030f0f0203150103060b1f12020d1a01120903020a03050f0909090c040b0d1a 69
    0xd03d894117061540742c83c200a40c040c03010b4403500300400702c1c545000781c20344101340d01c000391184c0341008110003a1105d02100311490181e0200a442c0e0782c0700c1445600030300400302d42175001482e004012036030743c03544085141600e004400c1035071800c004d1500b4075500d10540c00c400d0009070072120380d500041c290303401502c0c02902018241c0e618180702610340c400d030840c0707002c109010109081c10302041002c030307810f8001805003910000d25014010980c184d00040340e20008002d0300e4142e110406101d1100da50310400d0f98003c042d1102400d0754001c064107154280400c0e01c1d0240342150004441c0b0f002c0c04081d0111403101c21346940c944140a00f0b88a000322603403080840d903020445207182c07035654801d101140c6a0f00c40300c60000e42c4803030001040342d070207003045600b0035180c800d040d4040380c0c0020381c4140c40c9030705140076550307042030701244901d5000d160901608901030106218840c1c00118201c2c41d4040c043e9130402a070341c84142084080002c1c0170024142c94264000b241e0065140034005a00c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 902516879 1250 902515629 902515631
    0x130b030408190c0f03050315030303010312051b01240b091e062107140a091a0702130522020f120705031b03011a09180c040c0e100801060203030f060301 67
    0x40781c0fa440782d44c2c145045500450000d640002004081c0340401d0b540c4549000c00e038001c501310340c11a51132020001e003815298092000102c0c0140c260100c0c080038200c0f040440000b40a08140e51503444d68100710258900100300310703058042034030240031090700d40f5400300030f29280319114580319a1481041c0d2114940e04020704011803002c280803811414907260040340010020b1178001c000821b009001c00a42d10130427410890300203d254002c0c0c103942682c40300920680e0440313446c04000038a2055010080d0000d20588207207041c5171055018601c43c00f0b08a401c21031070551500040080c60a81c90029031080000a0703011641c01d0200d000443c084921044030742c411b40f80d0000916012801100c24090030100c560113940d4103080c09145512843e041d55040035849800014052001c000c000f0035207040070300000c500a6508004014404401400400c0074046250009199002c902c0c403090140d0400000c22038002e00c5884014106c82c1076501440c2185c07190b081040017040050042d07503041d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 902517985 1106 902516879 902516897
    0x9090e030c120903070303110c0a0306020901033219050c0324010c020f0310051008071203080f09010902150319050108062811130b03040819 62
    0x103203030b048c14003083d10013102070100d04d040c0703400200b103612061004000044c00000d0b07000b050901400e80e81844000c02c94848110048000c800e450070740380c0170780503024140d80c1d1401000d0b0000300600750030300312241c81d46c03060003a240b0540d14040e02c054000b05012600796901100d0b0070f0040ca0100c502c501c1741d030050000c0e08422035080040c2c090b03850b581954a041d0340501030300b1071000c54104100002d09002e121f000194046005501a42c0b045000c08240800190315203004940d0582d545000c50782e901d9035852030a840a0407103038541d92078156141c0144d94145a03c813001d06041d10700354a81c68154240d0ba91408002d0300f14284514010050100c00e0b8003040103507016400c50100b0380420300c040c10301c1c21804002007010200602d031246900003141c034640204420209001906089903c0e00d04200c400c0c03100303460003403907007504002c5180c183c0d1800d001100e00b0303403a6041000340 = true := by decide +kernel

theorem cover : BRFrame.Cov 902338129 902517985 := by
  have h0 := BRFrame.cov_init 902338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 902338129 ≤ n) (h2 : n < 902517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
