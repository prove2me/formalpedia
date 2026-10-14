-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:39:24.322152+00:00
-- url     : https://prove2.me/submissions/fe18bc5c-3935-4058-913f-b7fbd1f87d6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212949640 ≤ n < 213129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212950890 1250 212949640 212949647
    0x912030d15060c030e060c0106060e10030c050d020a031806051b042d170f1b1c020409230c090c03040b1003080f0415170c0a091d16 58
    0x8501c10b14000c108120180400284140d1100d0f00e000717001400d16042c443d60102c02804c45040d41c22403404549403810842c03807461701c21009019005c0ca481e0a0092410b8804010118003c0021100d001d42e004036480c56258081d4001d4a04200c1045060807600d0305030800c4c034060041540c02d0400f0101441424880f96030302e808031020344040e980c410881c42d030740b40500c1004100e403a206800d640700c01c0c803000c1407100c8080d03d000c4503100e152000b40310401c11000b043d802c008009102c00860000501001e8041d11030903c10070422411034414551900b5038000300d009000100b1005240c003003205407410f60820007030b010120140d1807104a45441200006103d14050192a2105021014000600084c55040215500503d88002c8aa60342c0c0d60356112285600282c403600c15410001c202800850503206c10407445903030500e0501d180d039201d00c0300140c1d0850040e10007603004c640055035619041c001e80c0e2032401425081c0300841701c0d00c1d441100391207500090301da4004d020203080900411622 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212952140 1250 212950890 212950931
    0xe1e250311090d02060c120304031701080a02040f0e010606050d0c0e1f02030c010c02073308150307090b191401050315040e070302030618060c0c030912030d 69
    0x403801e00585480c00180401644804142040f68403140800038450b0b2048244a014143c0380c25a110b05d45908003403501514441c808000980e160030510010051030400052900340c41c0d4040c3d50001d2103640751a800d0ac00b4110070382c007060a640c2481e00014071154060000c2c51b000501e10030410400300c200c44110303508400301e00d24030307880b485061a546550441d5010a6003e02c480d0040324a8414540d1203903080d15203004465000d6007004804102e0300074600620140d1602c1803140c090701c0c0030320320800d1550450922056080255100005003580100d0002e031120a80c001c0841740d009a0780d1103000080d20781030080a005000c080c20482941100c02c1690701074541040c48480003105110045645800c01411000d454000640201040d1101e02c00d0503c5c48000b04040d005241c10760052501d00710b401740010440707803030320a644181030501080203074200a0a01d01c4540d148604c0300582d185004004030654050780100a8208860000004020340040030030f051000c40d0303090040111401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212953390 1250 212952140 212952161
    0x7030e0c01020c13061a0405100f0804060b0102160e010915030309060f1808030a1e020709050627071101091109060117090a0201110c03070e1e2503 65
    0xa1210002044900e446400d05500f8580d00030002101652100c24400000079101c00c6c0300b400c3d0001409001c3c9050040403030600e4141030a117801115002c1031f00501901009001412485d030719a920003040c1e201f4440301c09100c81e610303078882c0d10329200c104015000c5801c0c45845c0c0290700e403000000881c00d542c04c03030b00210b90301610382903400c5260000c00c0e103010710038a40400400100802c86541403802c0000000a40312650066484040b480d00c05401d45078450720640c041d240c1403021005540c0c1c0043d581065901c243e0000c15143c6440001c582c0c0f59a0001d2490300e2840016901030324211031b120624468802030b9a081454501c0785291804c803962070f0b00c05480e098401004c0d03101c60034100304080e00040185010640a0100c503095281c0e003c0030355110110b5000a09050150342e0700100303040ea40184140604510342030301d400a544d45d0460f104002c0000485000201c00b9040300318101c9881002c006040401d01d880d00310300441240c01104040101e0241a400c07a180344688107082103070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212954640 1250 212953390 212953393
    0x100807030213020f03070c03030e070b0405040b0d0f0f050d180902030c070210080115030e060403030b030f160f0b070b06130e01020c03091c0b0123030109030807030e0c0102 76
    0x1421a028490312488000c0302d5000769800b080501c00da1040440114070581896590070206031007440c0080598218100c4411180d008420900020795850222000c0355422100041c021101c440031a003207110300c071006031460700340c00000d20500c4980c407003d00616100b071060f59100745070070710255540e10101c040d5001000321000c013805407034144c2e401180c0050080c96a02d0500080d80e0000d91844180d01450000a05020042065014080790a03a60310711604090101c0d540011610742d481c400140f01604050320791804030300c0d503241071244584090309074040d40e104010f040c0d4070445020440c400c28040e924203c1c00003a00035098016034890551060f0036603a43d4880b0410040b81c0075010070009021130713840a0480c40d03203900744000d0a030080300030301454885081c20200302c4040c0317504041c0d02001c4200f4007403500181c04094a80e0654422801c6030300d01096400d06038400e880c9082107540c03d0743c41c04056006141c0c003c1080c5214100b59901030000182c549a27081d1900e01030740003503025 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212955890 1250 212954640 212954653
    0x7150206070804060b0904061a123007060c08060904020d030c050309060406110705010e180408070b09010207050c040b011d150f040602010f05010b0a05030603070306050106030b0301051008 83
    0xc0e900c80c0c2c40e92500180140f601040c54240403002400841b800d8801b00d8036a55200800c1049809a41c8510160401111003400d0600304072007454903068011141d02a440e04036201100b88194609251610310348a03641c1a103410443c07818070002d044030307042c01001c60250380005890b840c000c080c19105a50183c2450820302643d50700b03035072502d038065040342d4a01040c0100b080c01d844802c040c1c00144496940c01030412003030340c1c0c411700b02035550300054104110f00026490325125250010300c120030390785080255039101d041103130150181200003004480900c041c403460440540280c025030b8014016134181464007010001150305008220307021540112507510060303482c140d400c1c80400040d11026030070824480025480d0704c001c4079550100808101030014a909214004c19a04070100c101b01c01e504202c01d40b107441c06035848210411400000060541d1028031413180290f034044010722480d611010003030060880740719143c0c000d40ca85000500702d0258900345a04407184900038068 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212957140 1250 212955890 212955901
    0x90106090e040212030a03090c150807050a0e03010c0c02040515090a0b060c010608010c090e040b010510030b1302031801090c09090302070e041209060201020306150d11030c040807150206 82
    0x180140300800580c4c0c0540d441c2d4414603070721410300040a007010741d640c0000b40d20380306e0b01c1c1807100205c864001395038607600310442c403c500b03400108d881d0700306c0301c0c03030071b2083d1034807035030740b07048075003d24180711140c049d42030503c1e4014058000c1c000d0b07070350540300f1a02400039075252022200040f100d807507410f0b0310213210404140c030b508840d8080b24103a039028001600e400c500c581c802307080d00d0f520760200802e61b41d079400c00c0800700e92246120b0094580030080100908080d01c8103d21120180205480b0748564941040e50a000c0d500c07601400c1d41c081c08001c5100f24a110001c000e400456012000048001d40c0e64003141042c49403800056004003085031a605000ca1036000b030401c1c80084040d44100000441e5003001881102d118a01c5004641941c0100110003480315100390b219a05580c01401030282d95034074610804002650b51844035101d400c07902d401d00162030701c040f511080343c00010500c44501d4402c1c00404c02c0c1d03160f980840e4445940c4840307a0080220108600f401138000d0340220f807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212958390 1250 212957140 212957159
    0x70206040f02090702210c060702060c1e040509040b010501020d030209010207090f061d1501091409060402040f0806040c140102030301140a0306060b0309010c0f0929030408070b0609010609 83
    0x82d0401013501c115412803121903000ca00b2444514100c62070b5250128030300c3d0078200c04102c803552003c040e10141c1700c9400c0c4016494881d01500c64a0700040683c0310034034518101400507135005103001012000c041c1003e0403e40c407100002e0045a00500591800c2c01c05240240200d0700b0b4000e040e0700070040c5520741402040201131b5451540e800e507803107540025621404050581c81c02840f80300350496030500c004441d15000314907135018140510200d042051225900101c11105025241940b440d42d074070001074000e2003079800028990114501c0850450000500706101d284034502e94800140c4903402080c03641c3c003060200e401a402000103200c900c50b048000c450284015000e500019100ea855109645441d000105c2c0f43c48088100802c0390b10074000c52100c844903050041c40558030f40d40080c03031000035016203c8203100886860b40c44007002281c19100642100c107030f90b224109446c3c040c85540c05804203440f01d00c41040454028500b00f11164100e501c241c890a940a1030104c418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212959640 1250 212958390 212958409
    0x40506220f090203030a0207090606030b0607080c01110c010e07090911120705030706050d14040201020d0f021606051902030a021e030d090303060f0803090609010e0d080c0601060305070206040f02 86
    0x403950307036151600c10005071410009410510315a030082c120241c18504280c007120044c3d4016010542049140002916101304490a098001b01c12903034581e4840e001317074054002d2002940380c40000045101d0b0484040d8884071184580109503a007203542c8460000544001c203002a26011250520385028500040101795400d0356006a42c0000d80d2080001e0410060780d00030701c045403000820f0301c1c0c0c5101d60300c601191500780680701d400500300303900000d55444410203601c041c40144081003c88a000300200c07098901d500510184160702c85100402c0c0e41c001001c0300c4ac4041c0d2019810501500200965403184000e50042000d0580c11b28683c0090b5402c0d001598176020410101d80c4034680360050035000c85c0a5140440e0441c40d1441420728400180d1000000b40c10520803c1100e80d40c4030110343c2500f40074640f505100340790f640020061382070808000c25100000903c0c040246c00407800714100d5080d52400c10040d65062000c2c1e07198070741260001c01590010010100601d408140c4c4c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212960890 1250 212959640 212959661
    0x40c0f17191a0c1806070c0302060327030c0f0318010f03060816030201020f070501140903012a03060609180c09080708010912020c061e090d0f0204050622 68
    0x40c080c42d8201e080302401181026101e82c0c0c0c40307a600181d070902c48258100508103100c0151a0140340100e140c0ba1542d035801ca40c000280701d0301000012400e07028203801031001c0706190003800c0103a2100c1a003015640c0c1c1c000c401e0074a60b03000311904900c8007070021098400c0040030f60b0111000d13241d003000444000c4501d9420000b0b05070386000100e2500c40030041c0e10250040400a0b1303c01d24207500000e032400ea00e0001100e042ea1011401b8040c13030341d01212580c40c07a40381c40803094462001c0c0f0006800b5041010516103404149400045000c0a14520030600c16807500e04002581c2c80d004c0840d8004030f24018080d0240b04818000803038549580400d91030301e0b1a181201905840782e8a0a0404410b81d2142240740c3d1204c00c040144900c06903410766416090004094021400c0f011a071540200c845141c83d81c104140002040c600c00b8003142d113481c070014410b01b499441d03480d1800c070100354018141d004030300d444002070b0f0724100103d6441048406520180556035800b0322407015101d40c090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212962140 1250 212960890 212960903
    0x1e0e070f050a0f03060e190605040c0b04060512040f0b131704030206070f0c0f27020c07180204150503150102060108060a0902040608060414060a18080a0e09040c0f1719 74
    0x34561a404061f014038192040c10302240c9400c043c00c00c00020313071107508021245c080c05c0104205158111003210b441420701c0054840c940e4843c2040c0007985070911024220141c45000c00006480da44104603400348154161607140d14280d02c0481c0d103006601000b50440780800581001c101302c0d400ca510140d00c1010321640c45521846503d210b03071107a610400e0710f41c18528601e03415040c0100606054030341e600c0708600f01000060016901d8056100d4040040b00200b401c468102507038045801512040c16001c084925000c0010015401110b0503926002101e403d480250720100d0110304a031039090050000d519200c18032801485280d0041f684107603507290000e103a8505210316485030780940103a0004d0000c03240c0035420f2020080c516079800d843c01004007040c007210205100802d170003654580d203819902e1070079107000301040701143e0f02c40255020401000300e2450400c094419024694040c15501c41e145001506481c00300107583c0c000d0580c6505089101c0c0e00c1d88003103406080d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212963390 1250 212962140 212962153
    0x908070f0501020405040b04020c0d0807020a0b070c150507020a060f14131e0804061d0415090b010201020a120c0e180f180604061e0e070f050a0f03060e 67
    0x60340c94205484000342241d0594011400f04010310380351242690850050b50158a845880c00d40d00b52a8002c3c2c030381d150300340326000d404650658030030002c8250450f0710881744005030810850103020300c04480002c0300c4240e060000015124007500800b40902002c0d001132549000c983e542c0340240480c2d030a038030f800940c1c9280402d040000c450b0100d0240164240e5947d0134052824010300000b50000b078062280590784c1400700140c05e00080320f046507900e140041295403994a801c1c1d02c016040d0826a106090504114050344941a01c4048896003c0200400082e01005900341e0048520042c00300c1c03000c0a2050382080075402600d0300101610300005940101d80c0061003105c42d202d0341c0d01041c0340714410403040b0b2415641440c0c1140340e40070410b48a00c14580080d596400c010130042034107407107008043c00540504506100117440002c140401d400c0e40040e550303204410f00c5500c940a005800000703003030424810040c20b68507103500829440d402c40e2116006040802004040e610414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212964640 1250 212963390 212963393
    0xe01030e0a060501090612020607031d041112150105040b160618060c03051b0c0c060c150105040902150313020402040b04030b09060903030106210510060f0c0510090807 74
    0x107001c0c0c01103007403192500007501c1d41449144021100240c1102d111020341044c400c000d0b99400d03040d24842580b40c94a41202e20202c00c8103806030b000300c0d062075001420100400640381080020b000740024003e2001901da81d6514181d82c0e0101d52100036001c240700300000d2115520b650000c00310200c200d13006002008043d51100115040010351300c58028562550780c08100060164840040ba24901072000f400c01140b21042e06590310b00010071003800142e2500d08290500018a140b40d0040c030700e07034a60120150854844450180c034851170001d00300081102d1502c1d210302030505801800380c050405002075a040e690340302078441d1004849820300c45006aa4500040010304110003100391500d103145840940c0c0340c0d014081c8050340c0c00007820003d100c007000007a2411541c4525014590070382c0c0210710801c810981c42034501080c100b03810007000e0154000404101c0d1040d83c2e8820602001d84c0c41150700fa580780c1c0000b0148d410090107041414142d8001d1b1482c0e500440946141c45900d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212965890 1250 212964640 212964643
    0x60f221505010807090203040803011809051c0905180115120e1e030a0e090c1e1206060c0d230c010e1902090c0c01021908061c030509010e01030e 64
    0xc100800da45986401c0140080c06041c8900c00090021000650440c02c0036512100b0b0b5000c14080c00c00151082c8503100c3c001400e5811980003150400b00303407016248104a0041c002c0c0500710444049241400d002440342848450407280b10381d13500401481d42d080c45104005032925030401010414035030300c401c80e1480c00e0302c01d0000b03241d07400d0001c06a10242903404a143c0322103c815180c0e80d00f090012110107a0802081403032101c040302c0400e02540c0c4e10a000310340f4006d03441a80d20200341e218014121481c6040280800200305110302d40030b95a64003000140d10640c0f44100b5590490409074480c130b40a00700d0801c3e6070311080c105610040d03410303840c01010b4126a88802450703440f092a4641030ba0107001050ba030740410000c22050385000d0b004580040740c00703007901100c0c050020b4070582e2154290705031510400f00310400403213030b881d25078024001c0e503003a921188a04484c4070a203031800c00700340120605c0b41d4141c5403a82031690304401074401c003580c409624181515903208031880c500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212967140 1250 212965890 212965913
    0x20c010e0601060207032f010e010504120c05090f0c12060103060b0a2102030709061107050604030f06050903090a05040b010c0206130e061203120a060f03060f0c02060f22 75
    0x1030f550003045560303d0350410800c069201048010010b10703c84981c40468600040035449010a00b800100c081c034050040740d0364441c503030040405c01c1e032020f0010108580c1000d984100da400300d90320034481c5c072075112001c036100e410b44812210520800c0041401029a001203500c20014100091309950701e44200141e80e010703c00c04c80001e0705582014031107440129076110401c51040e800c504500d4100406041d88005006110603c4600c000c480e50002003001303060042c0c98007030240f50b111556071810164075400b41108a4106050000083c1c52402c000300751848680010300408180d0b04c4c10062000410b800140c65041150480e1042e000d031320b42100608a084070f01000e883c031103103820040c0000c000040d14061044c040900302b0642a02d0010641303409010b01403000c4020b07103855011034020302c02c3e03520600400c090004000306015065004c1c40609221070400e102c031060262040f07032200011911100d07007801c0500450510340705840c100700c15007020940b4407611032307071501c03083e00c401d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212968390 1250 212967140 212967149
    0x602191103031c180302100e03090d03020127030503010302060307021005040308070f020f070e1003120309060f0b0306010e19090c050a0609060503060405040f020619031107020a09020c010e0601 85
    0x102c0c0c005050402d0f450324451410000070681820070140340030743d40292154002d21001c02c01a071502c5100f820b505040c1304454801740c0041c503400a0300c010b0319001c0d0107010409400c00943e412610342518580c0c0c100c6009207655415a559440c5230b0860b402c0205580025120000310301c94203141181210f00c41c41010700413400b948948100b8600120020715140706100d1200854020040c484021540060100141c80308040c0c0d4443c5075407580800c0307807540740b50f80c0701600b0100440d2000017002c0e0513a008018072800341c40d0901a001420441c1400d964040d074100341c00d54003c400400101c0d0280c4c2100c1d8101202c2c0300351009140380c070081901603038441c9000b9651107801c2070b804c10079490302c012100018802820814030182c60704002070514080101041c0c0541c0c3c85000080c00c0101c000c1241e0320855004141680702d0480c51000c402d009000b074085401f00b442d0a95030b20758042c035181a10a40c0794000c1c2001005c0d4107103280a400303900f060041c80c15130349d02d59004001c1041e06000042c043c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212969640 1250 212968390 212968417
    0x8010302030f0c011b1106070c1409130204050727090507030507020a0f0f060e010e010e07050a030201050d02041220060711280803040501021006060219110303 70
    0x55046004240c201444a2041030711a4440c40a0260701e98006201200d018003000c2015000601401e003110079185844d66241d021000042920410172181d01000540d40403a204048529a40c402d01c640b40009540860030881d50f44407000040c5440d801c940e070320010fa031818010f0503905401005240b9031217403c80603080001102800803040e18130600d94049010300d030038040340c184248041d4a9030007202d400351020305202100c0080c41030154000250b5540010100b218071040c40849008015100f1041e1640d400c088005401400015115040d10030040012203034600e10390064a855001c81070f510b140304c1d000c2c440092080410908040814000c007010340d404071000b03040712074620a50400310704c1240e050003840082640c48080841a4400743c9081c10000c00e207586056030f503014018500f8110992882c081400b00c00440034208a8000fa02106c09000944076032009403800c2d40139000060384007104a06059034041d2141c90042c2c02241c0d86c040d000380d5140428115030002400c04404c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212970890 1250 212969640 212969657
    0x80604172a0a0b1b03040f05032b0509070f060e150a020601051314010306020306010c060905070f06021f090201090b03010603090312180b180a0b09070f120210090902030403 76
    0x601880e0710540707a020554918130003601c400041503403524040504003415000034080d004041140810485a22140c00f000f400728559414031149402c8490703107480c00d4560b081c00041011000d0020703050040c1e4000c84240c49085003090401c40d0001c0700d110000340d111611007800780451100000810880c0039541c0540b12560402080c48812103c0c071007450301c1c4516010007070b208091103404460550798000c8003da600d031110001250204901c45c0050300305407400717601e030b0100100003501c001144c10210220000c07980d6074000360303100e11100c150900509c01400010461602950024004034414104800d80c0340d00c442040e09039400980040010950b680c8541c0103060304080355800382c1c50101010300401c0b0348144100039011440300000d0144040001080040a40341d102d04452510801140c05a803110300b4a03460352503003602c030b84e143c9003c0c181e40030528140030034900c03054400a000300030154046a003404881a954102001048003907400403d01c91568002540241d0099a44444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212972140 1250 212970890 212970893
    0x915011d0f0412080c040b030f040c05010302072d120504081209030c010c06110d022104051207290a0605060c0705041a03070b1201080604172a0a 64
    0x15406000780c6810700c0681410100000035010110b10b103000c3c112403414104545841c81c0308403250040b90043c00c00d0f480c1c00720412003040500c2c1c00032440b841c003881d08084107a07980e40041d412840350610242c01c5102d0400054003902c004211a61011803465042802e40241c1d2510303408a002c04844000058000408100307220040104113101c11200c0e00c82442c005103040003994650311429202c1c1401500d545c2a0f00784041c41e4480300c203200444100c50b580710550030305500250f21140d00001c038920346180c01074800254942c0319200c1c0f03074002d00410000c140c1480d03010700c50304840801c5a960740d01a1001529059100c81700c540104c0c800e035412960700300081c006065580e00d811090144000303005003007402200182c600101c40043d20b0000b0b0461140308400740c1c8186c1000000d0f0588510080041c1640e40c00e001007910a218003009451643c8441807180c4a07002903d019005200031079104002d2840c2c60001c06c108401c0750155410460352600292000402005802c0f07550850140d1301c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212973390 1250 212972140 212972189
    0x60a090219030510120b06012d031422110301020a0309030809120f0a021e0307021206150108060d05060708010603110c0a06020708121f080f0d08091501 67
    0x6800100300e0280c12030645c01c1400311015510342000150400f141e400c0456003d034060000c0401c512407600d00c00d050308103140d2900c000d2075800c0342c40b2030009140c030381c0070304104910002c01e41c0501e2920200114035081c0c1702d90040c0d000300c200341c1552041100c074044500382d03501740f0080c2140f200030345012071940b00501700074103412401805009150080e036482d0514001e044122046100c1c442c2d412900d0340c010700b90491170712036880d10340703002c3c0e04a90001141c0d42c4000005809254070841d02d001c0b01960b100382641c1c803042c0c10b0714504030003001605507103044e40c05000040d500c00c3c0c0c040e000303a07403841a41e142c0b50314140c025551b840104d00c0034001404056454050100309440b4207120620b480c40403000079550303644c000c6c00901600d82c041814020000410f007101c852101c003450006031403c100f13000c520a0302d0b810306c8000860f6840200011120b8021039070342e41c1d0304800c101504644080b4201518014802013100c50725010327030520b550345c042c106403006020b440441700d0800400701d1243c881 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212974640 1250 212973390 212973401
    0x4060801050618070203040302030a0b01090e070605030720031201080c06040609051003020c15090106050a15111e0a02030c04110a030e01110a0e0301061a070b060a09021903 76
    0x1805034100000c1001c0b5494807000c0e81c4550016046964180d03a84010803400c601958000a6041c010401c012044c08400041d16051700ca01c00d900300070000000b000140d8503005882400d020510600c00290342d82d024103071943d4115041130200c00c2101040d44000d081d0740c09000050711003000100140704c1c608080000180350340c01aa641403401d81814400b8020341414031555100c3c04401c0c0c1d071000c03400d2080c1c054405103080d2604440024411000a40d1021811283c0701080c1d842e00c0b500142c036151900d2051304a0301c1e481462a42c4d1601034004881e4011744051542c01482100078151a034031a24007490f07101d400301000303401c0c400b44e20310401d800c003091642501d114500348071905003180c044000710340340d81c001c81c1000510601c061140902600d4244001400403c0c04184081e031a500406644010481140200007417926880c08501304c4038003184120301040d05010400000b10461400e41d000900100704540d0903603145c810500b640e010b514081007040c0310b41214046640c050069 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212975890 1250 212974640 212974649
    0x60106030b060405040b030f0313240f0f0c050f01060504110a090506070303060806150414160e0f0411090a14011409010c021f02070603053705040c050406 68
    0x901007410301400140e040d0099010b82481281e88403503001c059903040007106c102c0c4540c035040e04e4a401d8800c0b8034002c110460322036180403c2c0b05100030a03042d159542d05040010454a446445000028085a4284c0d40541400500c0300d00c04400000c01d00030030501c1e03a0895041d00100300541000e00f800241c4850303004480040c3da00307001c0d102040d1f4100c04602d090b00c030103540f0035031200c040342011400f0307044031f51140b0701c035004090a03c852400300c41034580c1c41c03220907141840240e105c0940c05070304e8141102c4c1c2da5851000f540c55102c3c80f034851004402900f1303000f00000440101d03100020100c1d0b45201c2c1e2407410040000d8545183d003010700d07030703440101302860303448a00300c54800000c0e01d8101c9166115651034800210410103a025583d0540c03a80c0c0c0142200c2270845c111580c5024105003011081e01612400000080541c440d006403032040039503c6e40405c0e502581d00ca06002d5880700c3c504100403071001f114410407120300784501d9101e0707400f0f0f02c0150800ca00c1e007410b001c225840b0343c20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212977140 1250 212975890 212975897
    0x501080c0d1511070b010608071106070f1809020408070f17060f06121009050708010c0e060c25030201030f020f030f04020a18050402090903040f0303030b0a0302060a0c05060106 78
    0xc01004a00150741c085100c94040d207000c500d03103c0241a480d010301c51034070f00030207000b8508004039032698003100c0c092281d000e548480085d250350b130660f19607603c0f04a80e5500000c003146a49a02c3c2c501c02e20154410846c0c003c29003500b40d8485a4a9003641c020f900240d0541e8030144040203440303448452a4002c1c584058400042034014400544415004110340001c2c07040002064180e12a16a40d4814103048d5017510400e8994100c01400342280300420b684074400e12602095644040c495805401880d807548030740e800003401404000e03008841040010300804615140b071708036600003148504400c40205038120704501c009000c84114200002d0080d105020340401c400803d001c580d00610000240183c41c0c3c2c451002968040c0c0c0341e003284511101020102550b4243e9800c800e019610032910900c1d641d5a00e0b802c640e890207030f8410f00543c080300340c1003000481d0182e4440c11301102c0140101c00241d80729000b1601c02d51240c4140c1c2c000550031509001400310912000e80907084a1a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212978390 1250 212977140 212977159
    0x160516080601090207170c0d0e101b050703020904080301090f02031605280507110907051902070e040804030b06010c02031002130314030a0807030b0306011401210501080c 75
    0x900e01a50384005004200c5403e90000d44401482860002154140d0900042c0d5548181504603580c69406500c641004550603a18801192601d40308140c401007080c0d40303120140b078a100c20f0803d41da0340040705035410b010740308011001d600c0704040c25102d91b0050ba040c590369407510441d84101d5441100071580c161041c402d00030410300c804101c0d03050b182e40303160141e2034442c003c0c51075511018502c5921500c46643c1060800141c201e8003500000380a0501001d00076208403d01c080000103c403000d000034410814050030046044241000880714030448a0031a103030680b003003401400703840030b58642c1c0d40843c040041019152003c2d5000b074003031070b1010400c071039540400d940fa03110030006a84d007900440c0c02e00c1d10004684001000f1034000700d6124010a4140c0b229840741d001031810400104213800180750340c1d0084c0943d1044401c060010040c0d42e20749426444c80b028a0203a05040000c000d45860100302600c00100e0030385462000012a5407420f00a00c9c1750805100c40e49000f8071030b41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212979640 1250 212978390 212978399
    0x70504051008070912051e0c0f03120d020f04170312090c0a0911130b0d060e0708061306030f05100509070803030c1b0d02030c0d0504080c1e0402160516 67
    0x4560760031545d440c2d00520107140549003c905088040c0e000004840380351a29081c0c1c101d00090b12544103c0644407032810b07081d16000c1c140c031641c9156001a4546007000800300d858120f900404080e11070300101410b09803503800c0044001e8003540100c24907400440d18031925104a910035400031003910080100c1d000401c007040740700e4400d01c9520303500c41c1d90f520710000c0101e21208981d0034104030382032100c1803a19003042400729001b0b02c400e046440d00d051000300d010141406210301684040d1190880c175640c2c0000c0000300005801c90400032034441e000000016080c1c0d110100c0644120b02a00c07055080c5424402100c0c2d0041c5050008d03801800c0030020070304080200c0c0d07001081300030459661007480b064840c5142c03000e040440244201d90800e420300380d0120244c9044421842513840e0168144001c0b9a1401a40586a855000061807510520700008000808150790741d91045669030100040d00305d0300a0705081124500111a000070004103100e6852a0284407500c4158181403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212980890 1250 212979640 212979647
    0x901080412110a14010e0d020601030f0305070602040b030901150506090d06060e04080304060e0703020a0b0a2109060b030604030804021203090a0609170a11190302040507050405100807 81
    0x103000905034204560001032424442c0000c800207020300c00895491214900e84818a03980000c22210694a02032808812203c0440c5800300304020303500074002030b42540c8405c2c1c42d11300311030421400d2110410a200006905001620050590b00221034072440c0101025084d66103484260b000306950880070b1140c0ea403850161111000203592641c0ca51249183c11002065250040e200c5400440c0c02c0004010844008500c6284644414414640104e00c4103a40c2c0926000007035015080741014044084050301406111195280c40132907001c000c40c90914569181c1400c00c0040d440b145007000380320301405000360284040d40208864036003610000c00840f07014100078800c1300c0204000800b45000c0042d40d55001c2d00425400c1941e0369100c1c041e144030094851844109640c0d183d04010fa64081104410240c020000340392400c1c1e008204210b90444008240d000c142d808004030140c0c035240b1446d40704012544a2030303502c0d03080004200c41800e03140a00020011280c0c10054000d61 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212982140 1250 212980890 212980907
    0x70e090f010b0f0d0e061e011409190504030e041116060b121902040c180b1c020d0609050609090a0f020103020903030a031a01050c1b0d020904030509040605060901 72
    0x30700c0a80075241ea4a8609a40f1988130b0119050381d01420001c0b12011603202007002c41c050310388050364880404600d05229201c2d542403040b5501c5400c000081d800c0c0e420319408055000d00074440140001010f8001d400031680203032070543c0040d0304c020300c4014509141c4152101110b41f28003240c00c140240d50000801c508402c0010000340d2200311100d03541c2c44822402c03520940c0ba40503140204c601c41a4001011400c520a921881c00c02c4900c60240b070040c2c4200008404544559031030300e04140f811030107903001c001d005c1c4844100100780880d00381a0301c00380c41a4140050045507079890b0130b036080b05480010b40f800b88203040c00020300110729030025196a4040d840041c00e4a142541e0005a009004001c00c260b098000015840d004503450ba00000c3c0b0311b00014492646000c041c4011909030266010541c4282c2c8414142548036041d10b00700c0506d84801000d0140004aa5010541d2074800356421804640080741c0344c501c1d450319000302d9000c2c01c410b41e12070b07007405c0c01100000c04416 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212983390 1250 212982140 212982149
    0x108100f0b0c03040e07030f0506010c05030a031a0a08060a15060c0b07090e04080703120c0e1207080312090712030c08030714040f08100b0d0210090807060503070e090f01 75
    0x1000288016901c1014404c0d40c00610100c030303665100780760103070001c2c000e0100003088280382c604d00000580750350f0281c40119013a9410100039070400f00d0011b800c0d801098848036820350000c02d05061080750f40c402d8038032005409107001600c100d0a0400c203420540e0000c004065100e6101e600a0111651001c02d0007801a04044083c4150315a1030b001d9983c0719071038208040700d01d40f0400300310900c05220003c0491a109543c0c0130b1131941e1802c12442112420051b038000189032815006c0c2ca0700c2c10107845030041414100b80e80300195515502031171a800041440301e083c0b070003c200703c1003410034091300008091043c08034004407116034004140580a0744020650707440880032908061044166110707003038030901960b64840c0c540551000703800300c0d0701c00d182c002d104250074140c0e900164029440ca90300081e100c0c802d0040c0c40c0e4204207010b003d0900c5a003c00501a40c0080c1e026000c110290003001c040d1a110f0392030900300360041048806148a45c044d072202804e100c2504d000958650444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212984640 1250 212983390 212983409
    0x81c031a2805060a0f0809120f07030302040b03040b0f0c2b020d0908030a1503080405060903030d0207030c0b090d020706030b03030903120a03051e040b0414010c0801050108100f 78
    0x120030700c540e000c07580700542c020a070408000b02d103090b0035940010040040000603102c41690340d40b61480190f540d1070552a04082550038408100d8900c807031400340401070b10130304001d400d058480e40040c0c03482d001150b06a9504009030203201740b18424000d030030341001c18014800d1400302003860700d03901d0f050010340c0b51a00c10807401070354198000303036030584d9850f242c1d100051000d0203007030805001c03941080e5030300003240c1d140c05030000700c40b100140344004903580404801c1c20640350604210964100b02c83d140c0d0940001c010b601050717942440100700d510300c03a499502c070070b5450381000e0300503d01c0105050420351100341c6510301c50f50006035070011584c41303103070215212403e00f003c01d0446c0604101a0f400d0b20a81c182c601e640090329000e461b252046030350400c41907036030500b40c000d00380c1c540410b818174564040c040740c0072070f030440300480d841030091072900005410f5120840c2140c0044802000080030321005000c0c1e586c0c4825001d0708015948800d01078070b403c21102d00b0b40c4e0180c41c410305201c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212985890 1250 212984640 212984689
    0x1c110c15070c120309060c0302210406020f04080303090c010518040510050a08030408010c2604030e090406020304020f010e011d030f3012011806081c031a 68
    0x1d80c4903075005008158040502c140380d8030781c50009405081c81490850310707682000c0e42d10402c948244283d45041c50031303a21b1043c050241030b95420111101a2043c3e801940030006ca01d600031034840100000d14140d0f0013540c1e2860074020781820010010f010904004c420400c00f4034000000f003441003200d43c100c40008031900c4400001040c0511070340001d4204a91450000341241e010006d0f000b140c0103078009004460491800322000540511200548030300702c6440400800c5105815620603c242486140c041c1c0500c0000c1c01404111402c035040e503000010070045051554440d00c01590a0803c82c0c400314070b90001820090203480da4510b001e5501c030451080e80c1e0100009443c3d0703520407082d1882d0403401041402040010500d501c1ea40d40040027240340c1024034000c131103140c08001d07118905a400c0c40d6041448034800c400c1e038510705840d00c4020035030391010b00494061115404640c4003d1200e500040c068a0a0008000c1c40000c030740150300700398407a00c41036044465650201481c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212987140 1250 212985890 212985901
    0xb07080a0c02042c060412270b0304020f0405160c020d02040e01050906010f1505030c19020c1801050904020906030f010509070306060b0a020d050f0d021c110c15 71
    0x41a00c081000a50f000781040c400702c0840301000c101078648420803040030b201d10301107049550399007401e4900400099048015541880c4076000ba4041c0300040391081180525511130820900041d4010701c0348080004288001c41c50501e00c1c001c60302000761001d0241e840c01c0781c02d122240500386902818005100d10f41c100b1035840f9002e42c08210760041c41080b1160941a400d0700a10045603031021622500c0004280b070801410050101c5055001d02c6000c40801c8808403040e42001c1c01c00b00c58000140700c0380401450004d00e6044550655004220014a081c00c00081c40b56000c40100e4104d101c1005000b19219001c074241c0c010b405582610300b80e15250301083c50501141040c3c0015446c000600c07000d440d0101c0c0030402c0fa4007601d0144080e5444d81010354403440b03503203216409680040301c0001880c0c016000380c00c003a011141583c1c10300c0300450800003039038483c48108440742c1c0001801002d48209100c2d01350080d600200313032400d0010394060913a6800c407001e44107031510119000540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212988390 1250 212987140 212987147
    0x902010f080a1103040812011a09042a02010c020d090b0304230604051b090601020604021306090216051507053708070f180501030f14010303020304080f070b07080a 72
    0x1c00c003e0300500ca90342d241a00740009542c01941c03803803400d15014000000d09014481c4100302d28008088450701d41586c070b0040000503c20b80000c4001070103440c0e070505446c036009641310391556079500086402c02005100a0820700c440303805070240060745605120419a00c400c0d240c3c440c0c2d208e40804494081c8464915041c031500d46400854401d03503042004024020030220100800c3e10b100d0407500c010303002005000741c4101d030814016405100001c0c05443d108890210401c0966000101030741c40b02c0c2408241d9110740720320054801c0b0303004120f040020030011000b0382c0304c520b054140c890900c1c0100808034132a260208401c0191180300c4420901402d0041110039040f5034512380c4a501c410015140900459481004c0740c0214140002107000d0280c48607102c0d514014110150f00b00f20056006041c1038400c00021a560303d14032007c00b0344c841d031090103036020381c0085444c1e616212505d4a4956100b0743d810003500400010055198a8019640b01c50360005501303071030700000b00085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212989640 1250 212988390 212988401
    0x10061e050d090c171501120f0f020307080d090905011a0d06080102030709030201030b0406050916180b070c090c020303160e0411030105120102030402100e0d050f030a0306090902010f080a 82
    0x2902d410307a8402c000a5094050000c182e000080700c00303840c2c105021003021795004d6000d07c00c0401c0c030031042c28100d002032210600740d201e80744500c1c01000110542d40100e813800344030317030400c094a40c820014184610340001880c0c00420390103809101640c10088922001038580034440c010b220042503030521a1079035042040640000030085441346000b0a0040010790148400c0e0f001c04e181410098440c00c003402040c0545401410b60203807911a00d03a07045261506484000400c0491024600307440344500d1100028074044da6a2500c48905082010003a50b05900080b1428a08401c0b485903e13004429290b20089050680c042c1024161081c3c4a400030740382c0c1c2c1c503401480c0405a420315084c6c80060340c16503009036401d100704c95080172043e080f8032090324042c1d1700001010041e49018401c0e00f088175510809480000d1002075655101d1900d0314030560950075800c04200c1050f03555051043d0300091040c2001480b009038079400181c54039000700541e1013081a4440043d10a00f580d8002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212990890 1250 212989640 212989643
    0x50a0e062401120c051803032118010f020405040b0a12020f12060702011d030c07030b060a15020303040b060a0612200c0307050c0103050f01090207050c041410061e050d09 75
    0x103001d81c1a0100005251b0f50044803401c3c05107514004d1074103d07045c00002d40348420751000040c00d202501003010264020000c01445076030704807406440740c0780d00c01e0103103080c901d690f0070700540c95a0502081000752070101507040d01601034503c040050314004c412031070712190145c076406505111940852080218070510426520521080c810816415800040600d02e8012084d94408060101c0c0b503e0b4400c0c81040b1480707910040013070010408007100c544c1c0140c0c0080149050680e03917001d140c01c069000800c80003580002c000c000501646601d090741c424011141d5941040c05c098001d81030018008140048541ea08101c00140d86600700080042e450741c40081c0c0c844581188190750380d80700380b50454440c042c02c9071640140d4001d00030305009400e05004200141c0c02c00300c00314029040158282c81900c541491401961140e1080e81750501412020301100d14010141c0f0403200d129600001c104225042000130701501d903031009025010615049981d040411070600182218540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212992140 1250 212990890 212990927
    0xe0409060c020607020705042c010617030a0e030712030e0a1a0a020f010b0907230403030903060c0c050606010507050a12030507140319020706021b01050a0e062401 72
    0x41da00003260b0000f405522038880c42d400c172240203442d0810b0005072180710340140403841e8120129210b8401d500c17801c03444d0303032802c0b00001101c6584500da11700c4003000c0e414a22860b0400141c00090551004071000c003040142c0042905030700d040720341c201e507660000c0081c0400803140c105044c0c5550318030703580005111190314101503240030152009a170388564100300c09445540311412520703030180200c0e526000c2c001d00352079459a40c11425074007107000c451044003418140b5448801c0700d10341c0d000781c0003842c02980d4540c505429440c3c2101107403200b0364840c0510691101101c0010400141032398003c2c020300e801c6489007814607190b454041508001071021b000522412003131a815423049100c0c40c000c0c3d580710181d614000a24060b8441519203078000d4488014114040d000c0390005e25170980304410051404034880d90358101045038098840d000d035103c100b4804003851a0042d43c0d82c44040d000036103648d04002c618000d9144082101c4611208111000b4940d43e005010303002c10790003c0c44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212993390 1250 212992140 212992151
    0x20f040507050d0f02091009150e061207030621020a21050303090a020901150c0609080c0307060b0f031506130e0604050705011404030807030315050d05010516030b0307060e040906 79
    0x40b50131020703400040015003c2c41801c2171014040d48036000d2241200c2d0403041c42c002c407402c001022a102400c40ea402078000d80c04000ea11a00c0d00000c0b000344c400c8890ba0f0340000d041d800c0c0300541c0d01140411840c8240d140840714440056665401228215240c0b0300081061b250808020000d5809600c00901140004001c100d500d40c0003081da0940300307100719081d009030307078072002040481a8445000c400080030156030000180c40c07540203100d943d028a50050a0040c503001c2d05285a0288d131003140c410b600d80e0400c814038104074644080840c421009042d10300e102c940150901c0030007c20f84c43c46401c1e0301103440440340f1654008a25048000207075040d0345401d0524954400c8603124a41c0080c482c0b205a41c800c0c3c0b40704007541d041c1c9512001c194505082a20103c2c046d1414160301088142c145c800003466075208000c044a1601c1100049821715240c0310031800c0c4003400641c0c0b41810b04000543d100d42c1e501007800010303a010350525501e14102d11000c40c00808001c10020002460070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212994640 1250 212993390 212993411
    0x71a1801090c030c0b040f0e19061836020406030813030b0c03041104051e090d020111090102030a0809121201031e0c052701140a12020f040507050d 65
    0x103400d035020383c1d00031100d00b008555118141c2903d48103922070340b45c6803400500e061142c408842d01268012807594900e2400c0b4520700b000030110303901c56024454000440512070414122802958005901c06c200410046030340c6860300c044000701200309182d00603201c480c3c0b08540c0d841d804030000d0b507000070a00c0c0c0c440d03d940c0c603541004040c5003c02c0d2100e80c450f40000314074038040c40c112407245602018000d251004c00e0309000c05004060b04100501003449254a2003030341c0342c18424862500c401c0148045803071100003074212010400c803417103810b600304075916a07a41c000085a001c94031502d40f0304859601d00100c0c41c109001e00003101d210042c00100b91400d80c1407082e5543c16a40100c00806500c1030f251119407480c001c09000918600320144100054079111030002d0074600014000041d01d0303400c403150140f0042c02d07008070000c5c1520b0b850321201814460403150203000d00b01425030000c15075800007100035108020291081da1200700141c0a148030b4010b40b03085400c1c00005101c140c020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212995890 1250 212994640 212994653
    0x2030903040314030301140d023c0f030304030201230d14060607170d18060903080106020303190218061c0b0d02060d0506061903050f060402071a180109 67
    0x10b480305a801115100042c0203515011049904842841030a180a00c001c6001d0200300c00c40704001340d034000d04050b070310524105031080141d002210001c610752820b542c0802d82510440c81c0c04407a004140d203615405650301c0001c101c1c0d050301e409003040038113807044003114201100030609000c5585004101c02e000048141c000201c52171030031005400a075116014009180181c000140c186034050400c461145248401403001c0341003030001003110341c20b110400220103804c8400711039042d61501c4040925a2019009004d0308031440618614100810080039946a030280350000036030000d004404401c0070b01c04413150781d4000d00915118a0004080043c0c4002c15000002c5942803034840001c501e085450300f110f0540c010401c7e405c1142491400f4000c0100510349908403004110b01040003c4403994500544a41d58020400380b0f000c1944d804400d4010740524080c6006104207800202e41444240b4680340341803282c0300c299290400b00b005103014003011080340d4607041950042c0840d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212997140 1250 212995890 212995897
    0x90e1f0e1006030c020604060b0316030b0a050606030105011e021f0518060c040605033103090608060a090510052805031204060810030c060c060e010c0e2202030903 72
    0x1418140510300310380c0e60b803069056030303102001c09005811210001d000036015a01c910020039003d4200c0755052180403940012807602e8005031b504500d181c00300007610211f80a02036000006032803203800c65240c4800a090001c030340d16198021644131303180f42030007842003100103001091001c4005490280c03440355001440d080c0d400404502c08415030060300940000c2e0280296400d5040324030b07041c0b82c07410440701608054075610f00b101d48900100210300040700c4000720b550504c031004010791f00620700541b00064644c0308106100d1003004120f07095440740301840445c2c2c0e4407040071a080e6a081510750540c045500442d03809070800040c2c101502d803900400c061a20303424171071052541c07980109a95103100307010450017000c080105001c03152281462980049400c110400040d8680e6110b00102c14260071040000e804841c49805000941c094100b10303009040080114a00300c0d0402803170340d105000000d010307810b001c0411100d81c24112001c05089d01208045440713007828210302c0e40366030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212998390 1250 212997140 212997151
    0x2090901180e0606060f07030216080706020610030b010b0a0201141017070b041502070305011b0e0607050606010f02030c06040b01030506071d09040f06020a03060504060b070201090e1f0e 82
    0x24503101c03036902911000190395000d008000c0c403c3c0c0c1050490b030711006c000e501c20117044045000e040d880c402d404000c0b03e00900a04000343c040c2c079031142480c80003031a01e0320042c04440c524051800410108490300c6181b8150341c40030a11964620951805074003610490345440503a107150802c0210034203616400b00161032461580b000200c44803044590f03900e0640c060560703041c6080008010021500030411400c107400e005582d681c0380c0d02c0e201c6c107084843d5104840b9609004041c1076038080e40c07026002c030000408540980c08e00c40d2a40b200c0303036250802080d4a051141ca665400c104900801c02d40c0c0b840c071403040c12280c640c50185403c001e2910203201c100c55503c1090082011140901401c0100b4030040c40500d03448000c02d403c0100b1244084e0081d01c0d5140008116004034241c0c1c001081a1003c0780c401282c02450603051208540b603561060f641c540d400d1007020b0050b0381c0300d802ea000b00c90b901c0c0201c2090b5191845440d24400903d0a1910089141100041d0450b1303100c4003644604c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212999640 1250 212998390 212998439
    0x14130209190503060702070302060d0b1c060204030b0a050103051009110a09140703020306030a03080705120a0e0f07120308040813060f0e0103020a09060f021f0614040903020a080c0102090901 84
    0xc5e100d907038003680d41d20b500c0e0000a50040c8280b25132015028554803851850500418580c24156105d0308810b03480d00c000b00c1600c100d07400141c2031080c1b15000b400250411843d480c1040b0303d44c559100c3c2030f03e540c40c1d81105501103449080d0304041c4002c002402c0034000c070080c10402015510700c62000100041c04492526400001c000b480450180c030a89110305006806803180703d110b960b08403000e480c02451242408000c1c42240030103101c00200f01d108001c04040010f101c00e107260f5641c40c010b400500032200780d102603414840c80796403000c84640c459140c00e02c0322060b111460400014011f0340c268a048200780d110024041d54031107040160a401a111222884444e800440c01d131300c180e10054020850281c000c104036031140441170044141031060b0381c0851b00ca0708080c0c168100e0058004a46a100c0409100e810040c5003030a84003207007100c040150111985d00a9200c0200e0728029142c0000400c400021007429011030324070840007085020386603103c20780907000040030440500107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213000890 1250 212999640 212999653
    0x60905060a0818011e06050306090c010210110f0d02040312030e03030105090403120609051f0e0708070908060903180d0201081501050705011406030d020714130209190503 75
    0x503418a40200c4500209990712905195941c2c1034001214000c840c031050b403990703500c0000d071001000c03a82d481d20b9580040d001041d9285448205494050042e0004155401401190400e0703a00055204000c003140e00022404442e0a10340402900070a405002c001000140c0000318000690041069900c90b45280d84102d800050460886061301d0138003100d5407003000140b01518158400340e07400350cc2490a04030700b00d41c19040c2c0096442e03962060701074544540c1070201c40f0192031404000003280d941e041000e40d00d003a0040030601809042c0c84180520b072070110305020f00c40c3c0712030400b4012500488045080c8061351954a9210416082006151512480c007600c1e01d03000c000030b401c0c8c0503500c400042d2038550790101d4006580300c220341030140c10010800091030a0080019044008032000b00d2450008189428124040c1c036480454001c504188050000080180c640c04425106030a4000b20611080028440c0b00000359010540d40540b070010712024030444282c60040c1d083c3c400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213002140 1250 213000890 213000899
    0x7170f0906010b03041106070609060f05041709031009210207140f03060432030705060a060608011716081e071412190803070201180201050417070506030705040609 72
    0x3040d000c2517600400c4403010020424840c9800d401070142c2500846002401c1c0300560380e41400c82d020401503001c11a00d0b682008144800510301e5110840032156651070f0020010000b901c2d030500a842d0510580c7d41d840f9001400724144418100d1803003c107010003161015000030b5610001441107504040da00e4119445500301603003a44040e18010b030080940e5110341d900c10710311245072900c1e440b060804124808400401d018100220142d640165603114a10b081c09810060300030f00c802d4415082510801503d588200d449044072200c40d00d0800c40e640080205060031711030094502e4686101c08085072560021464845810420040451b000c000e0f081258481100d4890b02082d210103a04e07401e0740b81031900348526548000c000340c80131001079060f42030703400000e0a011750b4024000b00c10083c0242c2c0901c00c0c0078905007000c041d107010b088550f00082592045010b400c8484070001c0c03d04035800b1080000c0c0780134000040003207881c0d151201c0010a150000d1042d01d002030550440003c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213003390 1250 213002140 213002159
    0x2041103150f0901090c030e1b0102011406030d050c0a08212a0a020304030204020309071806030804050f0301090f1b0b0301080a02040e120a09140102010b090a0507170f090601 77
    0x60100b000c3c0203e96183c0c41d1060220050240641343e0040c5601c4209403424403500344080b20002a207090746081829110000a0841350000642c045114060b001d21859980009401124070301c0d900d4140c3d80e0b44050070340203052000d00c082c000d1460802184400d0400030381a08801e000400071030307054555481100c0b0f440e0349044d240111051000003090480c814913280010402d40800f03004032440c00b0780c0c80e40401c0c02c80e403040361643ca01c0d030014001400b2110360807250f001600403643c41403202a0854403840303024440e03803084c1d41c8964800038108084c0c0d14213401440ac0030390400c0e0b602d00d14072500c0c01c00b038147c1e0304040103210750050349020200d401a1060142c9060701d0b005001801102c0c83c982c20700009112081c04080903101d003031403081c504222a001000c4209035540c0312401c003403030411032100c102c0c41e40c20031b5419641000f00c00d1565445240303440e60710188a401c00b20303044d11038140580300c0b1020310200c8074810b8221810044c2c649140803000c1e0140c0c1120003215040d80c0d0301c90402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213004640 1250 213003390 213003409
    0xa022802010f1d152a0f070b0405010806010306030f121115011509030b010b0c070504110a0305100f09140907030201080f04150c1205060a1404050408070204110315 72
    0x550740c00d0007440084490500548050b80d46040100f00740c41d084c20503030500045888001110400d440e034102c001c05c030719818420050714074080002407007150300707018580b062405107006042c100301d00440041e025078440d40225004503000701101020705440d007888869480b40803401f034040740c1d2401e002080c176140000c1c07482c02c0c600c002c0b83c00c80b616428510180082c0510301c1805041064000d000700115147c1514907008020b0660075582d03c01d03040a45904000042d4002441a490005403401112149086030f070f0524041c90000340b9990340800750325030707c05250003503d11707910f48500204a083c00ca40c0090640c0b00710f0980c074034056940c2a03840e6034402460200034006802d050219200d104582c1d80140c000d072060700c58643c8244075014140032104699968000264200b10741030740030000c2d2240c2c3e600180246c07411039040d07080c0307140445008200c0170100e0103542d4a0f00010240300c844400c0c0c40a4a600400a00c0280d00440048460750401d071107000c0500e0300300402501525001e5403a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213005890 1250 213004640 213004667
    0x518372f07060912082d010603020a02010f15050f0901050f09090c03150a153204090305031b030103030c0305031f0e150303030c0403080a022802010f 66
    0x400500040e00c641080c1d040880e08860850311144a40e0004101d00d540c14071609407565540705516040360201d51444614101b00f86e0396405841d142102c0c02150406410f54105050140e0b031001d42c44800c90040c80c550086851341e074505500c00c04d030b030303040400304904564003100c0440d803071042102003120161080c0300705644030544130108002d5050000815500014080a40341401240d00101b400e0500414840d0100c0c402001001f403148094804c1040d04410fa00001c1501d43c20071003041b42c1c00c80f2441281120004613000180d6601c0f100242c03480c5a08080d1040c0003007d40e6280c0981103400039100c008404004c007000d658903a00420941c1c0c12660190b071901111850358505a8141d40040d0108810800f544500c0c0d00814400e841100280070160b07038400f0303a107803007449142181a81110035102e40c1080051290070140d510030354040e0307074200300344669607c1500300591404483c00c821800c445100780c1e040343d501c60114202004c09000b030326141c40c5407030351103c1110300300d0036101c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213007140 1250 213005890 213005951
    0x90d021e130b0120060a0506010507050106080102040510030902180c0f040807030c0b0c06040b0a02040806091006060207050a1a190207090b0105032403010f14041b051837 75
    0x540c6c810007940002c0e81003030040c140f207858801c107900c844e800e594540d00103e6403607400241c101714508050040c02102045490104140901d50b03002400100f03c51524000c181070380d40104084130340c000b0464800054001d0f8680c2c0c4c4036a5414215211802d0344410340e1615800790f0005800e002010841d00500c0550000d0000b644c1c503640c0b08040c048002c0c00045070640c1c00e010200c2c401e14100921402012104000c2c0190610303005a00c040c0c0780107410000854000d00e00811450326074445150540780260f500344050702c0b8140c86443c440c003447c412a1a02d2a05403d1820300540224240d005d80d80c40314000e000d070240d50001502c0070f11040d03038000c08982800d005203402d080340000c0444c08080090001c03038001c81c2444200c0c140c81c200c18040c031711480351405120800c5a000c2c4100e4000725a281c0301ca14103854440018040c6566803048a400c01d540e600086a01145401c0803040500c2010302521200082c0c0c00c7e40c03a0000c0c50115005000c1ca0301c810b82c80387d10b001c0c2d40b041c0e81080b022003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213008390 1250 213007140 213007153
    0xa020d020d05040203071e0b1804060e04230706110a020d0b0708070314040204020c15150306060901080d080406150603020705160506090f010509090a0c0f05090d021e130b0120 77
    0x14800c0b0140c0d07209d0066022500d0b01030182034a1961140a068014400c000303241d09503003400e01f04107035040104d0301c0c80d20303015088041c1005010b001084c0d9204560245c101500c15440c80c0c82c2e9541081440750000303521025509560040056500b0300c14000c00317080d83d4024456a880310f054040340c091200b00402032490000040041c51b00e600203109129060081d2540c0b10030195140c0c038041c2c0191403d000744440d14a1a0546060412082e030340000100e81078840d81d4501150729444800018141e0100040500028144181038010b5646110b0041e40c00f40b0703455403210010002d4000d080115070a0040c401480e0103082c52003401070503600010102450b2100c4e034020088000c422910540c14894180310704e4046551b03031116980700704d6601c1404031b10345168100003000304c144082c0b03040600074203101181040c6c03540b141606055606030b8200e0920452103100700c0c4050540f0030748541c0803641001c5043d042c011600115034109081c1ca036108449005100b1100b180010542d40003190b00c0036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213009640 1250 213008390 213008399
    0x15140a05010518060315010f1502070513020304020303040b0a02010507112d0f030301090207053a050c03070302011a030c0d06020a1e0309020a05090c0901080a020d020d05040203071e 80
    0x21481340c2000004088542c0f80303543c001280038110b802d03070020050040c140e000b001030044035000040f210060f4406450024100300010b070414105000c82d008540d80800000c04540b0200300301c3c4d0181103100d00c095114150340f10005d02234101220368a0000d01c010f042055103002c0007800502004141e007200c421081080c600404000035001561031314842c01c984404075140c1800118003900c01d03a680540e482c0050305251380f90240c400c00f40310020354644c0c01030385045506e00307081d41000c03094685001c020300ca10780c08480030b004e4803d58000c5800300091354010140c056000114550300c04040c40e800c1200340f000c05803600030003180c0c03c4c1c000d101c010030140011055070003006000304a090034a1401500d11041e200c0020300061880800d559480e16029860b0a450100003408101c0c4c0340b51080c68040e400d03248a014a80360207051042480c00310354001d08079010b5031040000c00404640300e03078000c0da000010f488c080d00c09034004c0c05160000702d42101c01c107aa0201d07150040d10030310141480d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213010890 1250 213009640 213009679
    0x3072d08040203011b0c0c080d021b010c020418050f07271104030b0103140303060f0d030309140709050108030c0d0f0c0c0603020a02010b040b011d010c15140a050105 73
    0x30710480e855562849544a4445c0880f405040f4000c3c6a0700d0901e82007039803524180000094110107910352010f500700080725400141024184486040791000981220040c2c0300f0902014000b9170143c28040314800408102810611603800b4104552003d02501c6141e902c0300a103004040180b1800c80d01032031004400070398070b24082e030404c100161003041460681c06030f8005400490752100441c00410920940e0a0700e0b4aa0b201400003446ca1800d15000040c2101c1d051034003940140011070400d01030501982c40f030191980c2041c442d1410160320701d52a62a007040b4011100842d2600340042004000001642c402180c1c00000344490f450810082e54185c034500c0790301c810005540780d80c10020700101000c1004100e80d860140e19000e003000007900391007615220a000da85400c2448a03a60307408038103003801c1070001c1c50107058010200c00498810440d000060603800300364103040d0f104680c5500c10700b985400100b15584540311060030314141c48003849940d0740148403032500d0402c81c89 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213012140 1250 213010890 213010907
    0x7021915030e0c040903020c03100507120c050d0f20070803010302090603030d09030513050102030c0706030f090c03200a0305060c030c07020d030207081621020303040b040b03072d 79
    0xb031000440e84400010340001c0d0070380f00f4034a400c4005030490904160300c0e007420030a403580d41104c40d106110742d1804490003000c81c0085640ca4040700e49480707090310003500030340490780d80c80d4101e81c0900107030000d03c003040050604c41ca1070070901c4101000344400e5410003015a4441c0d9440320b4464a90703440c640810841410240810794140010850015180e860b442001e1820b8840d89440d07480394802c0041100003001540101c0c190340040100c600d6240010404400b980c00c039060000d4034403900d00c2140c00600c00840010301c0c81c00303010008410b01c82c030310000110006220b00c00600701600e000c140290948640b0008203542e010300c02142912205001850b0700c045a004620b08100e02500002d42200b211401900580c000c51014041c80100f44119001c0c00380201c0400e213414980a9030040410002071000f2110000b5000d803000c65a0a000f110002c16081c0d25868603251601c480c81c02652044c0d8144012805c0001c2c510240100703103035500d2140b8038005d01120604403210007540c0001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213013390 1250 213012140 213012161
    0x2010b0d020f01050c0d111207050c041d030f070507080102041d0903120f0a0e0c0d060905031204080c060601020c060a051b010608010902040509060f160c0501050109020702191503 79
    0xf03003e2103800d042040070001301c1e804c0030381a80c0340d03014810762042840c08e00381381800440c100c1c04100a910041880018480450300040c0c4001410608041300007030044018101100035000000e014002060750002401d90640a0b0f070594040c9583c4c3e0040e50701300d01c9640f0a18494403070a04403a1007800100b107100b075000800b0b60950f840c0054180448109550403070307140304600011414006807100343e10a84d10762000300e100510002c030b01d0030005800b0228130100200300c85e441f40c12620401c0010300680710f04030205095405141841e2500c401c841d0480c400210f101c0c8103860003d4029840004c4290440300d01030000d03850486400d00032600390340f0500315848204900711441404400034800c01004114140c0001000c81c2c0354410801a507001500d0640036603c00818005d0b880060b2074002e800440300665000d44880030031064905100f40c100c06820740d40707000000140302c94613030010843c0e00d108441180d4601da13851516080200e071170041214800151104141c464002d0340030040031f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213014640 1250 213013390 213013397
    0x51e0103020d110907030e0607090f051002070914061215041e050a06050a11030402030606060304030c0c08061005100818010b09040521070302030d020904020403140d08010602010b0d020f01 83
    0x201024000b095131310b0415541500003c0e03840c2d4000d588642d0510150341c000c602d601d000c84d0241d19054165840342241d01609210390120340241c00218000c00c000c1c00180b10f400d4051041110a0426030300e0300c20112102d50003816488050303014600c005c54942111070015200311b065807a2a12144080b1400c1c22100c00641c0e4030b0826071001c20800c008009106201c0e4501140a1410304540f00554944214081080d1000e005010050382e020484503488031007600c129480744e550b030408a6083d032031848040e10341080410041185540482c1d4944100c044601e46600d80b0f0f42c601c1817110320041c030011600010141700224001040c180031400d50717130302010008038070701400d08001074403082e05607030459003503108003001c280c1c1940e18500340140c0d60310103084c1420710091307071006500d034400c2c007909901341940021003d00950362541924051600301c00c1655103a4480160300d552200100c00500105441400010b446403050240c1840d261000e055110340d0107503a400e201c0c0c49a240e003000c0303050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213015890 1250 213014640 213014663
    0x12a031103120709050d0c05040b190b090102120c0c0d080c0d03140c09030303040f08070c0b09150c1203060406090c09031e030503040209060307030b0a020d051e0103020d 75
    0x1114420006070000c00d00070801d001c2e003401c0c081d101070300780c010b0f541c401c2d030282d003112003502c0c0462800140d8408844080d6404a0b000740200c00196a03a03490ac812421502100040415402820000341c80c6a11f001c1e021519003c9181c6069007540c0210030701070300c0c0380d4401c0705102400d0400156100f0680c3c840d038090350410b04540c240c1d906003030381107407143d000a030b803540328103205c01070000034540000921204615220805002c240c49100042c0007401d0001c418908000700551403040742c913110b420041c010601e50f1954041c102c10380c800344105100f00f1549050701c40503540782c0100c80785030200600a000702003149070b03144140d400007400c9139446544d481c8005408000c80c06144262406681c540003043d0841c44d20390340341801c1c01c464443c0c407c03404032103200180e0807004494100d5011200480c242d41c0784000a45003e00d00c2c2c00080106c00300301e0500080c0031094000d4204084036510600059550740000f420004000341d4681c3c0d4500342000410140c1080b2480f0440107000c1d00c100c206 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213017140 1250 213015890 213015917
    0x90a0902070204200a08130f20030d03020d0b120706030b0402090d050f1011030f0a09020a0305060604061202031507050403050114101403100e010b03011109040506012a03 75
    0x3000d0440d12020b50058030000781d03d1410560003010594003182d2800403200d40151500c2d2404845007230f290007804070002c0652041400703060407200c0b00402d401411252552807068008002e03400c503825150703807503041c002070388481e03e0800c0d440b4a242c92804002c019181c03400d0000c4018180c6000c1994201d41d08028080b00341e1602e1000480030350080c0010103880346100c3c5560720f0412001c40c00c50030700c1e283c16003103d0028040b1080f25001026002c5203003945c1c9600f0304460040017505402580103950041c0001004004146c0c0341c4106000c0700d0130031500e07940c1d8403002c01d140c00d02140258940c024283c0c0c0c050785c0b41d80c59991900036540b4500142031a86a03a03440303003100c4040d50420000e0104e40204164004421208000303450441c5160a0318007440c2c0c0441d9a660404524100c020746980c8262000d40302503100003a03c0200800074040616841c140d10380a6001e04007250180d410040050360550085840f00141608003120801d4107507440d6900e0300b60554800110104200d2845c07080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213018390 1250 213017140 213017171
    0x412030b0f0432040803070c141e0601080f1f150803030412052503031b03020c241b0403060e060708070f0c0f0c05061c05010506090a0902070204 64
    0x2064030410031151842c1c035a4101e000380000c01100c0e000c109041d0f0b43c040000003042c00040d20341200407401e084118000ca89000e0315540b00d48250300c1214800d004c00c03110210340c42c26450302c8444071542501e800741d0301ca1000c40e84980300341065017100c0d03001d400901500c0505d0609883c10bc0302c401c1c8002215029000c6054400313586900c00703062684003005010070f0299242c540044454036042040c82c040000300710140e649802c08111303010b022803800749018035001350440064600d16041c451840007903440083e000350003d05005001e0302c120701c41517441e04408100c1201c645904120b5200c10b07511000111071071011411410020441800000001031140c0074100441605001070519881c000c2c2000f807580d14020040410410a898001034607504400c2d5030284581003120840a40902c1c02d058041c41016806641c22110008a10b51b0840044454003070b4403038260418800d03079076120b00700b04090041c8034059a010103c180200300b4109c2030750003405d04620151012490303100544114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213019640 1250 213018390 213018401
    0x50604030f0c0b12070305150402040801060f08010207030e0d050102070f0602040e0604110301090b1908070302010809011103150f0904060b0406240f0207082406090412030b0f04 78
    0x1103840720411107400c001c011800100801901d00c6109080c108a4892082c3c05204805131420080c10341d260045a40318541c030404c85034102000d0019940c071540c841c04d0500804d694862948160503600d808900850107000b00c1d4030940d0141c0d200c01c01800340e4401c0100c1890701d40001c548640d030810079600080d030180c08a2642a015120050312545000348500031200018083c1d8421441c088602c10522842c809a0b41903403209000000c00e02408000305018990907040704543d0942c07000700140184c030000380c9200b81c9e8401c2e6118542600e0750000107098a2020048522485082c030000d01c06c480c0e20600b0440004001304240044070310740f40800c484900685041c3d07a2a5144c2d03a03104660304040c0509001044280c15400807000c0f403044140023805003e0601c0100446544040040d0f482009050098212107003690111b0b0551507401c2403070780e80340c0e0b2052800c4070118000303601841c006c02194842c81c1c01c01c2d0340008074100b1000440003400705113445030b40810700707101e0355480d9140c1e4400c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213020890 1250 213019640 213019643
    0x403030b0613030b010905130b0c0f0c0618010c050304030e01080a141003020301180c0b07081e0c01232e06021b09071e0504030611030411030607020d0509040605060403 74
    0x1604c1d080d410180000c1c10340b00000d1005444036071940004c0c1c0000c00343e0700b003c0da0001040c0480c41d25082c000c1002e5103248194483c14000c1e2140030180030050740d03001600102c83c00c1840080100300000d81050700c42d03010446018020408030509800306502802103103601caa01308400065407145a02d601d40c42403401c1c1c0d00328444001c000b90510031400d00348141003409a0700007078903e40643e03607a50000403942034021049208004039400b4100310080c01030300c00c980221400c2c11301008030b081e4110510b4110f41c030025595800d00c0312403800f2003510407800d1480c01030b00d540704401d55103100f03c10894851451080060000c8018170aa0180c9405843c40c040e21803603003d4046030f00000b0700c080d0103c039030f10115440b5900c074000f4031140d50b400000d035607140c0c10045081039100000c0303501681d25000c0c0b548040d1445007800d403103203040f5840e88000c0d40b0a0b0f100b82010042d078405c0c0001d0542d10b400440702d000159002c01c50b402e680318001c001801c1c1e0342500038000310b5100e032113001003003007600306510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213022140 1250 213020890 213020903
    0x221101180321210e030d050106080a0b0f0d0807300201060902030f01030219030611030402030609010501050303180f060a050408100e100f022704060503010e060403030b061303 77
    0x404040c00038846040340c640801403400080c0c0300707401c0c12103101c40c10401d60303d1071140d5552507200844c2ca10a0003551100320711040c04110039030303441c0c1c000740c100030048541e800c0d2540b400e40e501d00146006449480e0709039020b4014040c4500a9403100204c0d4440c200035500c0781d0410b00b10380450125840308910007562084080c0e42da240080f000703420b4402903001500d102c0c2c01130080103604040c1411443c1100d0301126062840c2c800401021150713072058001400c0307a403d0103042d07050b91403400c0c01136000d50f02c01d90841e181c1e9900c51413a50300b250402c0c007900c0da0640080000c1c2a26404d82e1607542c0510720300420701003800d0944000611141c0c065416030740070070340106080008520500c04801e0b081e002c000c05015890060001d240c1741d4004400c0e403603030256241001d4604520f541c4c10345a440e160380c0d0264001c42800b00480700000040c603540e6100d2070400c07401146a04040c05122400b6050a0082020340c03201c2c0c0d0705501802d00811500e4024505001d004c03541ca039a45403810080d8001d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213023390 1250 213022140 213022163
    0x1c0f0510090e030301150f051c0b010e0306040203060402090a1e0905190807020d060b1c0606080102070309170a020904140c09010302060d2c0709052211011803 70
    0x80c40310341034a01112100b00300d80c10030700041082500c025100b00d0200d1843c030b40401c1c00e0860300c9003556940910144400c1c0e070340a03da91850f00c83c1ca079a0024140b01c0090702c80c056a130310f428040641c0c42e00d040b580250190071240c0401d0044c105030001a40000c2d80d000003156018003107186988a050051050b04030584514444043c050240103000302c07080465404940268a52036001240c42001c100034000e40c0c0c80005001031001ca075110116581008000c80042062586d009000e50405401a1407407072030301c40c000803094014070880382c1c410f5241d120020080e160090b51214520710003420b04450049075001c000503510b091406208074421118021403074000000b040c17801c08221303100c900940d458001440075039692010f54241513104000800c8503046180c01244003003000c0868403103c821961105800100400d0400c156500314204205940e541c000c214140f13646000e4218601c0050a603080c0490a27140001150120606000308010b9035076000b002c9030729041e4403c1d2407044484 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213024640 1250 213023390 213023399
    0x220c1706010e09010c14070c090e0307060c080709050111070b030f0108010c03061d0a060302030d0c060f09111212070804030210030c020d18030b010f0602061b1c0f0510 74
    0x94000c1d40020001008010400c40180e02400b000781840058546c0440400c0c0348040021503d00080549000c4005000e200840244e044e5680c116080c21699141000001c543c2580300e9098a8890102035544016062529005550707800d004e401e01a5140580040850700240450041d401840520010300c015071500342150308640034403140b54101402c1940820010000100c10500b090441e00c0e01c6c1420303210546400700405959000941500449208100d096008104000018010001072080c424941808401c1b1880c0510062000d40a10400c0660f8208450b4003160070300300d45d04541c150780e0b06480e090855081418201c4002600107024411401c0c00b40c0341e5120b90a8605043c4510b290702080a506d804440d25040d080152540d00080300b2441d1403402c0000f0354202d205581e9650316466510702c080414020700c0094407441c400318003440005042080790072411601c0d070b800e207840619000d0301510207a40300030700c0702e4a4000d0050340300d130540308290146048009254015281 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213025890 1250 213024640 213024659
    0x4060207060e0a031121010524090a051801050921090a03110d020411090a06090e070f0c0206191206030804120813141503220c170601 59
    0x641e00007004100000c03810300d8150f203824400806890340030b181651201400c01c007081040f40c144401d0310070440d541103840c8103c40190b106900502e802001000014840101400080d8495680503023295240703000800c408015403043e504049450025804d1580d101181d50944006480d031250707541100c44041000754401103a80c4458202c842290f0800d42401f000608500726032001520110b95408912443d558004003014040e60050041181d40c40b440f044c4201500101301840c01071a0100012030001d02908000c0121040003094603500c4e035450004903010040150100301f0f11641140d00001030381c4010160000e06804c1d1401c0b402c0703980002c00209024400100003070b4641ca0b1030418004254070b00120341c00d40381c440c07140c0d00c841c0a140c03030b04000c0b074030403006079140038400c0150204000e200400e62a03200b840c103e502c0300030803511920345446880203803a81801d0100030141c0111010050030401e000900450700c844a09039180c2c000c047c1e201500d100684640c00560040c000d1504d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213027140 1250 213025890 213025903
    0x8010503060708060d1209080d0503060405090c030a0f0528030305013809041d010e0d0e040e0a050313050310152303071205010b010804051e100c05040602 68
    0x42ca850410800d092007030201d481c004241c400075000c1034084076803091003405070b08544020242c03041140d0300000d1603400200030380c00c141e03a028403031410701c80461882c8000003003001c030305a4014013800d0b581119940c1c08808940343c0c002224a07000b059000c011205848146003040070800c50810200015498001d00b1030340141c000c40c100c808118441002c0b0325403003400da0000500c0e40f144148041e41e07580030300c00030b004440c55994010300341805084843c0016084100c203990301c3c00280301002c40c680c0b40585440481c148400094000c001c5101c151800360000741c254050541518800c42d401c1d101c5504580c008040d14241c0c42400d0001c00590900700448050314411002c1000f045c1c800d0316458003010800c1c851680e802110240d40d002d03944100781d1840d1315290080441e0002540c8584e10650b1744c007000300668155180110100c025405400060f02c200d6100c4080c000f006517800751017580d034800c206184a680300301140f65006d10350a1003000c07503181c450340710ba03a1258a481002840e040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213028390 1250 213027140 213027151
    0x2030a15060504050111070504110703080a020a08130201030914010203060109120c140a09150e070c2301020705030c0a0209060307081c14070f02090c0a020307150204080d0801050306 80
    0x142803404000180c0d0000641d02628001d00c1c1c0010918142144180f9000790340c0c121503030140c5058640b100072800c64009103616840791701c460f40c13039554983c4150124010340d00300c0404501114005100036002c1110700e03940c940305040001d101d070b800fa01c404141180030b03c40241c40d031303600005000e11981c00030035a000034403461000e01c00d0040259031b6041489002e200c0c07009907201c0c0d04a4000305558149800300903000422080189028424600b045030f02c86104e045010401e1001081080340716241c0480703000e801245a0008a5544401c1440303000c4407645a2004d550a0000ca400540107100806045a120005051203481170042294641c0090b003c1072296105520400140130301050441c00040c1c030840710f1100142050094500d82c3c1818046007c0f078400062450420a0351042d02c0a17041c02966142940c3e40c03103c60580d8a445541c5d5444050b038001d01c0400001200500a2020741041180240c10309585000c42da00d130400701e0040c1310200c0d201200521442c1401c200569101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213029640 1250 213028390 213028421
    0xa120b0a1b021504020418080a140a0203071101030609060905060a08010b030d1407020d14100c05071106091801061206210203120301060c05010b0405041e11030a0602030a 75
    0x1460200007955840c0f0200003201a480208000b500303640c0c403980300104000f400c0c0f100e0940350000e4548540d0503403040c41c040010848040031004079150750f4094914050342d40d002149080404d880d40c007544240641211b04241d15410b002c0b411000c0c5015a000400c00c1d0a004503007428001c01301301c0c0c09901900710054a03898200514029035002806030110510f5060034011511001d4030203640344102800a904405100c0d103000410130040b8140c0b141030281e800303503000c0c510b26104940c26248032560038070000d441072050030b0204442040d0141a2040100303011300d40901803005c1290321043c440c0c0409003040190041041075080f860350940303242c1002c1e04200040c07d000f49005100b2886400181c40c0c01001022000c6440800510384481c00c410941c0b80c596035a150300400d00007107100d007183c095082060018490a090217058051030f80042c9030100c2104001500344030040e840c1040c0c95410072070f441c40c85652410300018011900902c3c0140c0c1e286842d003844000d981c03400c48040403a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213030890 1250 213029640 213029681
    0x801020f090f2707020102040b0a08010501020c030a05070b0904090203070306050f150d030e010203090a0e090d1d0d08120f04030809031309181b1703040e0a02090a120b0a 75
    0x1d82901642401000040f88001c00e5500da109040f4028003c5070090380b080c6400298003c80300b500000158100ca000368215191001d505060545400440c54001c140b5404814148046543c22001d862145405440041c8000c0300390000792814259a00c2070360087d075a4010b001007800291440ba5120080700d075040c0310805003a01240165018490103070030021140d816410503032081c811910444c0000b0082803030b9548500300d40f01c5001044c6c85580c0b05218805500700c10601900c2c18480d4070240030000c004155811060122a101161007120400c4040180210309200054400d00a07030004400c0c200d04c0c078141c0344c00f50111a004e00720710341943c424070150200700700314003a04042d2000210302050079030b5075140b4280c5200940d02c0003050162810000ca0582c200c20703610341cac1212440085885551543c100c0103032284603500400079564890000511070b0821900109410000a0140184190307214100d8446100441c03003110480341d4402408006041c4c0d00800700c030780d038000108050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213032140 1250 213030890 213030919
    0x901140c03100b0a021506310f09020f1c08070507060813020303090d060e01020c1506060c0703030c03120c050315030c0a091802060c0607022a0d06060801020f090f 72
    0x10380380486e0518112200b4218000345150701c2e181803540065803c680d5401014952001890410b000821101521840c18440c0c000320f00080c0116020141c0140420780000850004c1c84a00f2101450313001100d280341d8030304000200303401c0040c0240303405903016102041c10051300401c0e411001d80721100f03a1100200d900090390f0003104030381c5040320444901c08e00404601e4403d0103000c42d40c4160800394400719002c0c074091004a405250002444850f880c5a603501c0f080096600440c6003140341d59021003014000a400340c8080031071240070b401d02018280311000e8034001c4d140c0400040000410210510205442c00d18a068031070b1011400380480700c04c200082046100140b1a0f1119503498580c6c860340e00202a40106c981d98018020965078064510b41f990b0b40e01065400c1d20040c4100c0900140040340100050b419143c5a60f40e01811485c800c20080c80c15a00782c002e842c482e98541000841007024070040c140b4080d2034148070344401b0841e0401c8000e0700c0e1258814020300046d00c2035007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213033390 1250 213032140 213032143
    0x22030903033b03070305010c0203040504051e01030b0a0b100f0e010c08220e0709050a0f0303050405010c060b0d050c1302190f05071a06090c09010c0b0901140c03100b0a02 75
    0xb0385104038865038000b02c1c0034550000e450a0361300d0388060015444d00c101c00340000d40c04030082041e543c05440038452900d502d240e9500036890b08100d036860388128401480044d41c1000843d410040c0716034045244680040021010303080f9088240c00b060101a5000c46950001a1461104024204408295107680344e00c0c0b01407155660021640341801005401c4000c1000720b880900000f4284210768a04500c01400c628686c1c003800b4407402c0c0c05080014401043c0c491035045d0780c0e01d0396401d4203152824005403840031010300b04403202d58030b51b44c15000d2901c4410004d80010b00501c001e00344401900207000072800094454550240100100c00d01d284c042c035480501c80c50b181ca000080450b2190f0b0407180c90182c81d000070100c50b00e42201905005411094a00503001140c180c1071b591030354240c1402d01d10485d034081d400304a20906003404035808002050b80031120381c0000c1900c0441c6018610035070303000c0380e400303a4410002c002e01090252410b10740c03000d0940d4802070341c0381011745034000c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213034640 1250 213033390 213033467
    0xa24060e0f070819050108031806040602030f030a180b04060c170115030207150225020d061505041805010e07080601090f0f02030c0a0305060f01172203090303 70
    0x5000c1c49015804981140780d5030704401250006413000308842e5840e02900d1307449520492390440981c000104000341450b2400448080b41c5482d00150725209148120044a400c020b12092800e40c4e02c0280035001031511980d03110991040342135000601e070a01d401d10803160f184034942d003048a11955100198500c440c40350542d03605480082544030480011000b03403191000040510141003210201c1468070380180003a0f0a142000e40044e0b84940e803a01d222035050100a54001d00300b040b80c0c00800c1c00d59010b006802d0140900c107210540b51400711b0191440340b540702601640b402600b505026083c46070396486080342011300a12440c0000203907032240180035542c40c0326070302c10807c002e40c20941d0160745401500c4006640b6450260f008007d203800488480c0042400e200c00070342e0321301d0300051000c0070803016160b9103055210104201710310500140a00c0c1c03c0c80301c400712403003002c130440d00406510348079640c2e2a0f885421490010403400c0040d03450307481a1005c10900784e0101400d40746 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213035890 1250 213034640 213034651
    0x11508010b040f110f1c0c0f02070602060f010e10030803101a091f11061005100201060503060c0a0302122a040b0706020c16081b01090b0702090403020a24060e0f 71
    0x115074540300400c082c41102c10106c505410524540f1403145551500450310045c05042c0d9002d1750701301961040141c0c5c49160403031384000d1003c04140107100d580703004250702c0e802c684010021604252250390304919035109440d00300f050400300f4810411001c052140504051480145d40e08140e03540020030f10318901c10740c060301030035400a1907a854500c6515044100032601044800ca8145140d03c10080c51f00c0703000c1c4901400107082029100b9005009080442d20054003e14040e038440459043d2a0007104000f0100354081041d82c1079007500b951042d0240404541c0c1c08681d0300f5190b600d030310410789075090000f00c00b0140420001a03100b007040ea40804d03001480543c1c0ca0103441140b9041a029000044884640e54800309000800181e4074228910415000900c00e02440c010360358920188a4050b9040041042c507005040c1100c005400c03034403900442e502441079580364201400c01d0f0485605d14200000204804911405220014007400000a055044c0032141c40d8041400610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213037140 1250 213035890 213035917
    0xb0c160e06220f0f050a0e060408030601020708011406031c02030904021e0a030509010c0c08042d0306091e0f0609110315060301110408030a0809011508010b040f11 72
    0x1400400c8181c84041d5080b5808104000c100e0ba50344030a0007401001ca000e03802422920b400c2c001030a024042c0700d460781840f0400000c2031a170307565540e125143e9000408041c11400380402c0011180004d0064060707042d941c010090907490800140f5141050107402d052019140b6940440386c2900070084a0000f001610701680d951a000366540100740119080c0101c6c901c00913030086010790647c01580184c0c00302000303014404101c0307000c1b90401c030051405048100100003c0145140036000d00d03640c08050000450000042e00001d00c03140425401540c983d92110f6200082040340c4902d4038072012600e101d466001444e445202a82c008000003c080c01d070703150320310707001e201004c0d0f10400007400040c04c031090140010340d02d004004040d5105801307582800c020201d9003180e04c05407016151694011410002460700c11a420840513210070f4030395684000c0180c00c0e5901d80803240183c4800400411552982024041128108100071380040e1801c408494440c0c400012100e14000128 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213038390 1250 213037140 213037159
    0xa170604090f030c0b0f060303040b0904060909050706030501081504030e0a03150b031011091306030803040c0e070f05160602040b040e0402090f04150e0a0c0b0c160e06 74
    0x40414000c10000328060540d98404810b40c042661080c01010481e01c2020303e100592110303000002c15100030b4509a9041d00305000501140441901034a20040b0040c03000c0391082d43d5032040c0c0c0449580c1802a40d45420007001403000580500951340140311001c0113080702080c20451415041000e04010200112035609203410b944840c113860103503401c2211000c1c240880d1400e10f00800e007080300c0900034040d030324402d074410055119007821802c03004001403803c0d42120400009030500302c4c0c0640465501d04010012800d0280074500c2036201e581e41c20079050030f15002c0e01003000000c1038a01042410003007005080da112064400021035007100c0a070800161410001902603500420081100801c00054620307230600041c2c0900e0080c1c0c0d000e00280c42c3e11403403000141048030080c20186c101c11142c524042941e00600c030104c82e103026a007a2105035a10b140d10003a003580b0070000d16002140b20b9280c0601406100c4820380300d00b48102045141081d0610210001461107100d0490074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213039640 1250 213038390 213038401
    0x21e030c1605040c0504080703030c050a200f030c03070e0714031501090b0f091e03030309060702160617060d0c0902031608090a110415080106080d050a17 68
    0x10800d68104042800994210301c40e20032404010103658403401d80700b0f40c00e00901c0301c9624094011a4140c40c240809000d6450458605507140080329000302c81620407507461344003040e4862042070502802c4130240c07810301041c0040041c00800c41b104503100380c010780d46041c00350f5000602c080440e003110300c02c600141e03903122040e01d20b9158802e40003e0024004104900c2d2095454442d1903c03400b621450134483d180c1c8100010b6000b21150a000c8031810000700c201480c007101c0c0c882c6240c11400880c41242c0001021074150b820940d807194003a0300c0081404211a0140000300444801c0d5150503441450100c000703001c05220700c01882140c560002084580d01d49003625a40503811590756410f142e95010b800d0003d600c110750802141340e8188602c540320b441650114081d1052100404000c082034680d0b40038806922400c6510a40e0f4000880340102008030352001000682e000140252800301450b05003840007903510b04200040114007282138101c038641c001c08182c0908a502035803407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213040890 1250 213039640 213039643
    0xe040f051006060c060f060b03010603020f1c020c01060503010e1207020f0904140d05130501030e0c0a0801090b16020601060f050d05040803060f030c0604090903051303030302040321021e 82
    0x705070714140340d00301080441d85941060b031038030321644168410000034000580100403034590b070192055000b82000100103a0b0300c20380181000c3c1b003e0f216020300e00081700304000c3d514807541d040b16800e03640120390203110260a1103100003c15060300203212520b20340214540b544d17000d02c0e00701121308001c141d01d029501c1e03c400035082e02c04044c204500c541020304000c11b4100b60400b00b81854032407144280b811503c00c42c1552040100c410b1007182046c00c1c075006402400c142c2d18242070510035000380351429a9846191401030242000025249445050100300729800904031032840d10000d0694440c0780e400150181124007e14085407040b2030a1001c07a43d900c45e041007550440e04103020302c400e1216160055010388000c8600303070b01c40310b00d80d4145a10b4043c3c1c44425940b20b00c09010400c54541650070004455100e4035095250100058207400281c0c4160003c0c2e0010b540071805204101280b0380c5d00441465409100500030780c2c22100030b40e5040b0680c03018600e600b0b1091049180b020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213042140 1250 213040890 213040903
    0x17070503070b070c120e090105040e030c0607030b0111120301030803071205040c06200607050a02031605060702070501081302040c03020702030d030e250e0c040b0a030507090509010e040f05 83
    0x140000c9220307490400b543d0082c501d410f0420b0983c0c80a03208000106081d0060558031440b00303011b00301c02e0700c80c0e02e400100401030200c46110403081c00200f202c02c526100a00015100b0401c94800144000c0d880e4001811503410701d02100c001e80c400e144d41d80c003200740d0780181c0c0d046030350202c0003590300d54800708102e5110b81510031882000c0d0405003400704000ca40f0380d41406642c404e40d075064420100100c100b82149131f61100c40501d40040c0040341035184124000d06480301240104e91602d00d1071008043c9501e2246425141c5802c841e0600c615694144543c40c02001700f46001c03011424000748040600d40c0c540d800078841c1d40e554400030b1101d80030790166000140c009060703d451104101028028002101c0c040e80d99001e41c1c054400c06140142c00120340f0940f078842041c0440c106240c0200411000c3e0622095070024040098011000801032408558a07070740071456007881c1c00050012800398116903c1a2043e41c0103000704c043e591526684140c020640903000c100e5800d00605205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213043390 1250 213042140 213042143
    0x15210c06121f0302100c050c060705030408100e1f09081801110f19330e0319051b010203070507020f0d050a021302120a06140901031707050307 63
    0x1103020880901d6495440c0d00d0510400701d40c002440c02d00703108030814040036054000250b110f030800d42090402c62080c0c200d800c0d040c2c414411101c0303400030b0100248a90304080340441d6981d0000038244084a000d2000461200880400340004491101030503119240600b5020100c4140703824522058000e801581c0b1158003c0a91980d411404072024a00c1a607107900901146800425003505c000c0001c403000c00107110805080881d0402c07000390510300380d600b0107a039880b4000042036408a61b4140c43c2c00040b81c0000202e020150708500d89040e559000c2e9000b210390030501c603000742d101a003c0380d054000d099160040e652200d0000341c480041081c1310000440d0310100802031000e400400a0004c1c03030080b104014928110010014a40c2607940028220b4004402800040c2060224400340c40a1020301508005800e450607903140021038200200607229442049000180555002415002d40d02c2c0e08041d0304603280c484500e0400308003e8503d0100040220038440140103440655 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213044640 1250 213043390 213043399
    0x21c1a060f1603030605120a03120218030d0203040e0f060d080f13030b09011503230a060509060f09010203071d04090f08040609080304030515061804120815210c 71
    0xb025941801030042440b8001c06004400600c070210030040006242c0d50642ea240e956580b028a803a800303c40650450307484100c40b94100300b241606550705000c03074501401d031a0300a54031035241c4200300e06403140251114580030500c00030700115458039100c6980d9590440442640da5290310103081030b920424030000041400c2020210420054071101401404c21200070300c01d030110f001246a001215200041210b18121800707581d0311840c6881000c610310300701c251454480240c5032041554021034030414541c00c0b8108100440c195000880e420801c0400218110302d041c81024082c0740e80700da40325144240c1001c82e560a07590b07681081251035406954031483d40010f02e0848042d0300a4012100807980000f40410200c0001042c8c800300c07500600144105111401040c51500019104a41042c1441d00b88030210403845c9640f07004511541001412407040d80c0300900f42c080280550740b071201c400300f2100f4540d03128820750303003061718014402c1209580013030030a291042e001c0000303401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213045890 1250 213044640 213044677
    0x110307051006061b02041505060c061e06010f0309050f0307080301081b030703150902060c0c090709080d050309010921030c080402010801210203060109021c1a060f 72
    0x10000007051056510035004024072040b92500010394008241c00183c0402900b0441c0c14405490305421580b600c100c10b11216441545031400300c0c010358006207080305d465221800b0320580314001000c1c1d00283c4040c11562806090900000307249185443c078407020107855400920074000180905180083d202040342d0b0764020504c0c142000740c0007403040900500941401580c2003031090004501d111008020304102402d554403e45030504003200d84002c15911441480140c032940b00030b00c44454064010060340107d2400c00c0030134503000740040b00b004003030002042070f1800001c0960034040300381070042d100e607144040c2900411440e00064052101081e0500b010f01c0c1040d000b4000032525a410b1015503608a4280c48070102690000d00099486004020125110541c1c40b2510000b8010651902654000910381542070b003000403060b0b400245007821608901138410100c051040c1881905c095a0481e9410300c00402c07843d01900000034606058171447c411648601a04820b010a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213047140 1250 213045890 213045893
    0x60e0f04200c0f0609150403080702030d060605190c08160f020a0303080907090606020c0607060e10150f120602090a0f03050705040c0203090f060f160f0c0e071b03110307 75
    0x43e81c00d1046008181c0d4081c0c9000301e01e4400001c240c1d000c00d0580c1c211505402c0c0c5a130f41d8116101d40c00101050304500041c001d1051a00440c000c180007428180c0e07030107842e03150142d000c0854a450b5200e030024420b0401d600740010320b550042e10f49030b460700c02040c120301d0b2050400c0c074024884818000e5010005000200c00c0640024245009000c400700711141035440d0114201260201e004060240c1c0c40501002c001f49000d0f00140741c0944521f0010412502c2c0061203850700c446030843d01c81c407a0b1a03441c4404040070f4114804018500d00b403001100b13519201e59903050710034411020744016000951708103035445903102c12004210b1440000845035032424100d80300c43c8603024061081d42051000f8004034070001c1641c0110000406184840d00403908100322580806001c0c8030740c9009020b0003100c13814000c050301c000781c0500500402814646451405054942c0188000f041c07860140003030359034801c042c02400e1201d48070300c0030904110304040d101300b1032404a10130036100002d003820 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213048390 1250 213047140 213047143
    0x90f2004060906150c080d110c010207050c0102010b010f1d0612010e0615190f120e0c030705030607050f071a010311030c030c010e011d060f040f060e0f04200c 70
    0x400f10b59480c2c000080200000404448540301c0c0440030700500000e002140d01c0348801e032310048035071b405119482d180080c40a0146e0036600301c0581512a6045808030794050f580a004107100740e40c0034a8000c400040381030000e403000f00300402041d030715841500000820784600c4221a124000d242845450b507a40318541000324208807101d0b4010689031455042041c1c00f642030f0b0b404e4002c41e00aa00701d130040c94004480801c0010031000c10400740c131803008050350240c458280e564a20b030010340025981c42052502d003d00e55880103010380d00010401501e82d5100040d60340003000c0c5d04102d5622000ac0c10000034582224148a0840700c1c404c00010402c902454010690341040c1d0a88140300501c0080540f9154000d48080c081000224a40015841610740704050084540682c829141c1e1802181183d0415002032100110020b81840b82900c00810301008145601c0d040061501002c0450040b00c45005541d002c1c6460703180140c0841c80c254016a1140071142540307855040d0040f03130a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213049640 1250 213048390 213048401
    0xa03050a0608030f1e07080306040906150f030201080f01080c1002010b0316090f1a0d080c0d0e03070f18180501050709290304032003040810050a090f20040609 70
    0x5ca910074503005103034107800d9000f0b050780c0340590044149403d503a03a00003400007802c107081d0f044510702e030344103000211140800b40900141c0100d9040c510024114030024100c440090401744600d808030380100030001000903803005c4103109603403000078040b8000080e800342040380300c0c01c0c0c1d0500804100c3c010f40a8038500ca4412601001024030200c240304030b001040300c88900030718507198070030780c0340c2c62060130038055000b2154442e10889282c248074000c85030038032013410f106100190030300031000658603003081880044c0940c1c00540041e945080c0c1c10141f180c240760300c00f0515a888076203211510035030302041c94000747c202c0001d01c8540303000640140301f8007150207050410303840d0f80904901065610490f0030103002d007400e09451601ca5403030542c1d00015818601c083e24044c90b41c44482c082c41072010700003c01c8204014040d000c8206260b100707030707500104107212007403508001001281e19a080703c00310582200714900180b4000c00608486c10081010940150420307100091013203407035000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213050890 1250 213049640 213049657
    0x100c02030d05071b0206160602030103140d0206101503060305010203090c040f0213140402070807031e1d120705030109080c0d09051807120f0207020a08060105060a03050a0608030f 79
    0x4011a41e11070f0b50555100680165906542549001340b40041c14200d00800c02c1e22000410000200c41c60b5540906a0b4003d810448124005c2d02d5841c8ad501002c021081c9010106d001408461134200c1007003005138040e2140000c2e4000b44460780504e107009a001c0710142d0742000003513569251144003603940c2c46003220341e40e01580c6800c40d0041c65038440d100380d90040301d11816000380c0710b140882000399041c20f02c403c1a4400c1d42003161200043c0c01c1d10081c0a814403d40300c0f00c00c2050004906130000c14007000040511086a003040302c00f81c0e8804582102d100211400c2c0d4200c0e01048020740b0380074032074100303542640ca444507101c14070500350042c02c0020348800c1150501a4030728022079092080c2c0c480c81c1d810402803a14540480d05a03045154004c006141c4168003484c030507020000da0b1503103065408800d03030008024042d4203101c10f041015282c8580140240c1d4035040c0410001e1160741200c00c1095550004180c9140e403c0d00800004d0082004885e180d04107c2c880c0d4015030300907407c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213052140 1250 213050890 213050917
    0x2060105030f15061207060810080102040f0509070315080a05121914071203140f06090a0902040b060c0105070f03050c0a14091906020c06030f060d05100c0203 70
    0x21207190000e410314410495201034507085030488018103c494010309180d0740102440c0c181035048008211351802090390350b441103000e041041c100d100a2049800c1081c03244d0040200344043c141c900c031140103c0b07406980c0c40c640340d039070311408070000e088803080c5880f0aa04d08100203039014000030070443c800d00540c10f45000d0042c401c26070000b0b12411a200e0010203600b06152441030244040751010301c41d0403490f034640b05041c0d403150070070000c4421040101c0e6a6003003141854110b1500542e01c40e12014003100c00d4240640014481c002c01820041a1611140300008540f11600001c0b05401c028016540759407044569501070710045401c140021110307103040d0600c3d03220380103540c0502301c1c0300c4d0305601d06180c040c0c044900c281311404000c1c03200c804100001d080d48a030145034071403040d0716503064006d60426100a043c907840c41d410621505060042c4201000c0b10244541c009508a640744103030724a5107402c40c01d0407404400740014034941450813001e260013000800341c2010044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213053390 1250 213052140 213052153
    0xa0c140102070815090f1c0f05090d02060c01020403020a030b0609060319030f0509030f0a29011712030403020307021005271903060209040606030b03060c0313081902 73
    0x18012a610701080c483d540d4694440c46031440e84210480031503811505580075101a01c0342c01035854a0443d04140c03102e0030b14641c0341011a840d51006007002c071002c0d285000b52070302d8004400a0010f0340003d0002e1f2142d0000a030201c0050000d6040b10000c0d68080c1c0300881c1d503540ca04000035052400c9038118050650702c00060140d1401283e280e400e41400c1700031080c5013080b81c50440304000707541006400d209081000a02d981d80401003618100701e144024102804a4a0400c1d440d05d41f0344041440c0c00700000201000c11420740c1c20078191008140c0040c4001402102149404040c001c2c00c00b00700380000901051583c040003e1078514004d503001e05080d4520b0a00706e03102d220b82c0c40c0560b581440e1521711244044c0542102c4c0e4080d100508950042e900c0c61401c0c0c5010900350310403130389a94000782484072810680100d40040a5605003048040f18200100391200d1009020501810703000001038040c83c288880e0324405a0848070060311860070348115031400651128131005446002c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213054640 1250 213053390 213053429
    0x5040b0406060f0507020a030605090c030717030d231305060f060f01120b1504031106090a030b07090902040306052a2208030c010c08011205030f0304140a0c 69
    0x740550012610103603a00300340c402c900207040360350382c2168004903480764041c000040416142e02440f40550b40010140906030300781420589040199070202c860f6410860340c2c40882040881078620135100c0b480d001c520410f0100c181c0084400d5082c01e04034100291b4140400507401540c02c1640703e12034070854820380c4a444904400f410110341d0740781c0c40300c42d00700c0010b40e07075100d000058003400c0003640101c0e0003003003580080d200c205180e246d00341a4801040800c14829524040c016809007540c500f482e000604001c1101c03201d030390001408605060011590181c40340d580741d0001d12034103a0464a480c0c40307241000260005850784900560000d40800c07824000071354041420300c0c01c0905504d450342042000034072521244661200b01c0070900c1c00148854140024a12411280000140302c011601d0103081802d06810490991100e10a80000620f0000485251520581071903407a40e980d8a490b1032201d0005008811a0040c00446810440c0c005d2640b0141c50902e108610212143c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213055890 1250 213054640 213054649
    0x50709330b0313020607020a0608060102070e04170f04181508010203060f041a031005010603050c04123c03080105061303060b010e12151e0a0c050d0e01050105040b 72
    0x5000703001c2080d200300040340443c488a54600303a41880644084d0a15050350001542846160701410116642038100411503030306000741009030a840380078912031f00342034803400342c108a40b424041c030341c0000080c0986507000c910160b600812515101101e021f48010501014112081c2c03a48403921800c81d01044406041c02a00d05c00c071806031881d2408210201080041e0807855402c13504400176408200c003a4406000440010b03524030408a03043d40342110040480720300a080c561f0b03540c03040c4010f00c5160400f40c0200480c0e030700a80c44500f030340c5107500b2a020a8940c18420170702c00c9200624140618449442464254001c0e110000309a0b41c60052106070301ca8a00359007a000340c05c80c0107200088003030b401041110301c10716001f6400194000071540c8103000141d1105681e11000016060a440107031455001155420b03800c810a01088210b284003c041c2054400c1e41e00e44917000c4185108000380e945034481040180003c024608000b0b00170402800340c180030340e0514440303818a003003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213057140 1250 213055890 213055991
    0xa06050a1e1d060411040906030f050f03032e0b04080d0305060306330a18050a020a05071e02060307030e16060203040e10080109120f02011a010c050709 67
    0x2c0441c0d85129500e01c81000001d14080d0916805202d007888082403c02040c81080091403060741c850580c12000e0411382c0c5801d003071490b0b404141e40304004010030b2030301d0312000048040700b010745004000510f55a50913401826005000031a0001c070300042d4103d800900311000981c140c808105e0303902c4410625032500f034125070030100418052404040080394007100c0c80700585206091010203c1c02001606508640e84020b1492980319400c0408085602c40c0340c2d04402d00410451912102401c05480c0d030095642c09006240241c2050030405200101e030b1031803c3d4001c101c1d660320303c1c181c000030780144001c9580c500248268010313003d98490600710f400070750310990021800d061030425800f0146800400440c0b40b0800e080b400500f04200340180e0340018400c40b60441e0030f110314100105031041140403001113a0511100111205d0001100070002500703180c540c60b801e07510704005282050f81c2e0302c840d100620700016105a0340c0c0d1026400c0f001044060900740f1000700100707083d00c451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213058390 1250 213057140 213057179
    0xa060f18051e030d0603030306030b0705030103020f22091202011505060301092a030203010311010e0d1104090b09070509010e01060503010b030703091a0105040f090302070b030a06050a1e 82
    0xd214144442e800704103080002c0c0a034031404100c2e80740c0750503000b0385000c0e202c2d20340c0120003103a107c0100388100205882529807110003803609a0440d07241d41c0024038a101e06034040340c01800c02008942d0452a01d803084545e09803d43e409000d070203402d01d80b020032000f202d02034600552034001594444030b00c003c103020845400a01c41403c507403d00001ca4002c04c2804543c8404003004460410111403000203d82d072440b03030b910010b071250f2660901145034046c1a01e60741c1000910b9011011580c1c5001d030300507200d50000701000c240d50072000410003e000c0b4200107848224070004000c02c4070030004045041c1d0340c05540c800e1040c3d980b001102034105080c00761002242090006005406000d80510340c000200d02e00415000002e8440912000451a07264110355841c0010712050030700b40124442412503075020011f07481e01e910002e448850034003032110841c0c4004041026440b483c0c107d807018110040c0800c0c245a81c802007109070800d5910030030180820602c1c0041d0148804980c0f48506 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213059640 1250 213058390 213058393
    0xe01050a052b0f030c0606060504050120010b1909060501030507020a0b07050418140903040b0703140d0c0504230114030406090b07200706050702090a0207050a060f1805 74
    0x40d2200c451600003200001c1d1410452907185503090101e14500c3c0c800780312078000c1d1a0b01c1a032071a54100841502d81c80d4000d0320900904100421441c0d071310510b2505411015003101e685000101c149a001d081c00e400c0e92588400d110000c1d16031a0004a6070200b2500074020820000b80d4840044d000d64400300d56002c0542c0000d04ce200c0815101380c80c40c0d60001c12031420340c1c60305883d107080c0540401490300b05681ca540c4d812041004a17004481235030070007402402941814948030300161a840340680007400c1000500c0da03942003044020503501e01001000c02449a0586c00c1c40041a54205109408650038000750070b4840014081da5178010542c181c3d41c12904901d242c0302c2d0607030380e44060021280d1656030007203c80400d0a081c4070600600e52a90b901d646d05030702d18100c42d890600c02c070140d103081d0070200d004c0111a8010b01124281581614400300e40c2c0e80c4c03503864070020f0288000140190140704134540c204445503105142c5040042000c129907400f01c81c8401100c07000030402400b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213060890 1250 213059640 213059659
    0x100506040b070f0602070b04060e0f033106030e07060c0b01120f0605010324050f13050a0b09010b040612020307140a05031e0f06070804060b0d080a08010e01050a05 72
    0x1101c030381000801060b0701034a00440821203d0b0365410482e403201006645602001081c00b0030000d003030291000c44917441004000030410b80100d2912885400311100403040022043c2c10f8041e40c8143c03a50a203d000010381ca030a66481070040d001d4410030740344151030700039918080342090040610f00c602c0c1f600100703000403503030034501e1f0031a0314a14110b054075007041c030b00680400103e81d1f005550286204080b030740075603484c4050010f8442c8022702190642410700781000543c1d071760f04079482d61140d0b43c0d4089522210751401c01c0c5052584081014048180c043e04012a00e40150029400d00b5004da40810060b507960049000e4180c113820000d61640000d9020040035409201d1000e0350100204100c3c00241d0301c80000340f070700c081100f2408003140c915403140c01c195401c1c40782c18004180070018081510307000b00000d0413078800a200401242d50f980d4a5255910b94102000002d607028082030354800d030303280c0060720340402441110b514480300f13000810541401c09020301201e0014040c3d006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213062140 1250 213060890 213060899
    0xc07030c060213030f140c030d020c10091d060310020a0c030810090e010b090a09020a270c0e031b01020307060b060d090b150f100f020f01020315030610050604 70
    0x7943c01044842d424210f150f1001c80419900c000031100c040c03156090094424100c4a0305082000e4114030760b200790050b00080c0c1c5115008104403028074000c40e01440c600800410a503202c0c0c1068014030b90740c031002d01e4a00d2045c1d4000810500850b030440032144641d15404000069105030a400da0010360644012070000c1d01508460350005e07040c0d003445030b201d40c5840664003154000102d0311016034443c00d035040ca07401e001c1c4601c0d0300107001ca0011b2020b4405030700440d19204c5d091161040714403d66204050500c03000401c604960b03403102c018090f4a01001c0010a52641401c090780f1a01034100724015009050300807041405060300910304240690301c2d05002030590300c01c15900041c00b0003e1404141c0c4c1441004042849620b5010b1130381400040c030002c0300c0c1030f03980d1171303020741d80c1c1110b000c00c265640c80405141814524050030f0014400000324181105d068189100350300200500520b0b00714127400d00d40e046426011101165140006030b496003c0314441c0c07a400c40d108010502 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213063390 1250 213062140 213062153
    0x3080c030a09080d0c0b060f100306030b1008070501050d090f0c06020606030f100b010c081603080a1406040911091008150c0406180f030309030b0601230306030109050a06050a050c07030c 82
    0x1940701034014a4003501408c1403020451002000c0d601034002035a0385400e10070040c8400c103068100c1111302b659218907080100e107941c1d68140e800f50758140800400c400080c0d108a03003003031200303d91080c500616002540340601070800c0350b000b20005070103082c00007046070800091b1300d198280708600030054202c111981400030701d0b10207011810014071201d880301040032000104466441e550392a48401103d042c010a02e5070054600aa4507041c84c0c4d0a810020001c1d3f80c5a400442c100d0300029080d4051405c9545070944040340d90b00711181104011181d01c0b49041c10341100e10034026200d88410038100f640858004441564040d401401305014091151300c4500128034800d4083c1e5806480d0005440621000e80c8110001220850103104002c0302d030390000d0304180d080c20000f01c11401e039a105440d0610f00c03504661000008000101c06035025040300400c1c0783c01205540c1d4405441c107010014003c03c43e030000c0500e040901241d41c0f600d43c4001c84600e190155940e40380c0032026540c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213064640 1250 213063390 213063413
    0x270c0302040b03030c010e0303060406230f12010504060b1207120b04020a030804150201150501050904050c0405100503180a170309070906260106260703080c030a09080d0c 75
    0x715050b22051049040901e000d00c07580c82c10f1f888843c011034403440e04004100584034903401401040c4107036030030510488074260700705038172040c101da0a8442502c0300022a101c2c0c22104002d280d19803c00c014001070000c15406403003446025075030407a0a02584c030400340e4848cc148210445c01200a100e180418101d08465400c148000d102c018920740c0d9454a100a40058015001844208001d010302c16024816440072000760381c00c14074200d14010020780f135401120903841c0696120000203000044150883cac0240c400141107001e070800312040240243c20803110103d0100b281405414070306400242c1035081503011f4400c84203540300008245040d00080c0210783c8510800740045841c2d0124041e49014200c00c50007a821800c21410480c90f90450045098090340b42483c1404140a4291901d002c059480d242c07101a8144610083ca4030802e94005007501d0001310781841d40c0100440100600c003c1c0f40d45181c4600c3d22841802c1c1c0b5041c0d808469008151040c1414001401e005e03001d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213065890 1250 213064640 213064661
    0x12010f081e1501030c17010507050a0806030f0d09030215040311010c080c062518050d0213020708030f1e0403080a09050d0315060305040f03050319090501270c030204 73
    0x151914420010200070b5040302c01e030000c0341e00e400c84041c01d00c5036540144440e010341780c00300003d01a600348220013500314490410b0030350403ca14200051880c1c4c81c00c0100f01901c0216a08503404252180d030020404152404200d2095510708410340c96071860030244c0d016250459400200400700d000150784520815000305d5981c1818041c3e0044a241031200c94419014a611020801c8205041c202e030241c280c01b40b9000d101d4034510b003d50142d191078040d015604c098805490141c0c00740002205201c0e0003e00350800c500029144040103031102c081c500845402c120300103642c0707442c004135030f208286541c0c0b280003180280020340132902c07820486800901840d00001e440c860b03030700c4007410150411800404685c441c44008120102e0001d103400a000c9880c00b080181400d17510101c101d6803c090103401c000300440410745260f2881490207480b80341d039800b007103901c2c0340d45400ca020309008800c20700710855040c1203254440648490704c40300e560005014241d02e0541c1c3c200802401005013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213067140 1250 213065890 213065893
    0x41e0b0a0b1e0d0f0c0b03041e0506010303180305030d0603060b030f0604112d21030301030b04081215100c241e1a01050a02070b031b0a030212010f081e 67
    0x44c1c103004143d8040070a070161a2224580351707a8986400c0c1000c44030100c450035108080c10411a4000c50f80116034203065a9041c98807040400402681c65260310490300068858000081d1115a00d8250303445001181d03c50030301070010110740c0c42095250311040c440c45403183c000c07100040000d8140d01401c6151400103040e00c0251141c0450b140400d4082900c407060b88607002a480c909140a81c3c582c001102e40680c049400c4150000072070302d038001803000038110002070001c1810404007900343c64220098030708141e0213142100048158051011607640a0b82c0c14400010800384075400c00c131021508903958442841c004090b19155051425903500010342c4c55503105620715000e41c0c1c00c1e00d0304110000101d08837101070003903a48507118046107410b0002c10018041d00301d0b00810150211752000c0b0a07651656100074400c45802941d03400c1201203e00004c1d01d0722140d0301030f4040c00302c1061045120115a0300c806c000c940080c1e8038002c460035030f03200050582e210107610041c0c4121071000700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213068390 1250 213067140 213067163
    0x10e030315060f0f22050607080c0a060509070e0703060f051909111c050609041203090f06020307170405030d0905070905180d0f080f041e0b0a0b1e0d 66
    0x1d400e0001a040781c40e5420f041c00c00020707005e06000c0d001c51512a180c102414200c076517403500000030107902c5859002080315001141c3d50320001d106002d60500140c000c00148000e1500c0c0004980300c0e000c5000b4034002042e254040360300b09100703100300701c19180b03000c8420140c642003800308055204601706005603103025610102c1c81d138080b8020300200001e10a16151034510310b01409960020800d413000c0e84624000c10414190360f092003060300182c00268048425900d004110090300328500c014109403131000903d410481240d006522904060b616900c103c2880603103145010419640030b04140e1051001c1e200880ca141d000c2400c2e50312900c1141d000595640324401512012074525460304243e100d40b414140303052100702c030b46200f03034074100301102c1010001a03d0070201400e061509542c800c0014200400200003880c04640b000e1260001d90543c6411034440c2d00c2142c046848a0810390124080e0034a8100309811444408021300408046000d208103010204025100c080488 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213069640 1250 213068390 213068407
    0xe01030212061b0c1c0207050f0d021e03030c01060b03061e010e041a0a1805010b120c070c031a04170a090b0c07170604051207020904060c03020c01060801150602010e03031506 77
    0x42c2c0d0174101803d466006003600b6031400f07040200102106000c0c5002e440004c108000599409003121601301403542000034034440d44000c40d117180540c0260200544c0b0708a00402c2d4402402d0266210300f9044131949426800c001960300105008a809030110b0b0340d01303055030340500d040c2d0040f50071b0064212024a0741c40c0d900700041c04551a541c481382c01000030752925084280207004560241050700b030a5440c00110794034114018800810b001c28030180410703407501304825006001c004507008001c00c00e000307034030014028001c00c05540c201c0300c600c0c94501e40c42d03600c103481041e100340c3e052580303d00d101249072420303148056020011000321030041e01004655026000c01480e071840d4401e009007000e14052400740e25100c0c8850340f040082c00c0c18081e0030b0069890500c40c0c0e0740103070712000100700034018200c154040d0144800d050306070350a1600200e040401503011003160a03407406181002170341c4110507402c0316001c003655016a001040043c50300c0486581c255602c21000e040645840181d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213070890 1250 213069640 213069673
    0x70201020c150a0c020c030a08130302040c120609050106020a2006070c090c02010203060a0314011d240f010608091204030b0702010b010e01020c01180e010e01030212061b0c 76
    0x18941d4003002c0300410306100c0d11400074440c1c45807540050004105d110401000240e1f03424556030020030a040c0062200d14007074184403a01c00442d0701506c140101c092030400580810f49012191b4681481c0003000201c44101e070040c241228440e030003410b20345490b52074090014000181600512034240e561503816114203005000d000d0242c0b07038041c81542081c081d4800d4600094004045a00510a0081640d212101803045a40c0546040ca41001500549001d03043c1003180601505d40745c1d5442d62522030104002c00700c0c0c0700410003564800301226403512440400c4d1120100c101d210401070000f1401083d601381c106101030122445030b088441c982e0001d07031050700b00300e03440d41840e000d002c82d40f50240a8a1814402401e08010703000c00080001e60381c01c1c1d10b141d03643c1044402c07407900c400e07038900e140f201c80500074043c20045550303140c61100340c507900280310032801110383c8202101d1903080828827602800b21852604450030403000504880c0d00658a07c2d00b05010302c00b81882c00007034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213072140 1250 213070890 213070903
    0x909020d090c1401090801060303090b0a210b0f06070f060c140a0f09060f021b0d060207120e091003020d021f0903110111060a050a1b020c0910030b0609070201020c 72
    0x3d810364040c00f00260359000501d00400c550110f20182c1c1000700a0001030b40020000041e00e1003031400903229035540600b150180e0010702180c00034102c822007100d081a40e40c1228070034290a07a0042d64109003481401510b10230b07542c0c00b90002200d03550120018116030890140a507491800d6400c40508408409480d406445480c01107103500090101d000d821480c0e4200501c91420032200c1d002e005540030752119031070705180c140d05491000c00710482d074038500500381603034014100715154415460040300424101c182000858003034954000945803a0780f019128103c0300380900c3c0690b285500f400740c2b19400080480e4030000c510030b954900c04c0500b4541c0c02030407c503541c20f40d00c2880c50901145041c44032040031704000407444600007800d40003400e10342100c4588000142c6503100c0a602c002041c80c00304100c45500c4211080099580c00241c5440140d0225000802500c8007008028030403440c1c4402000d0f00341d881c0000d80c140c41c0081c1790541c005038500000d843e00301c0840b2542e04114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213073390 1250 213072140 213072149
    0x1c1109010b1206060d0e19153312080318030702010207032004020708181f08040c030503040b040602061e060d030e03060106050408060c030601020a08030408120703020d0f0b010909020d090c 83
    0x7c02ca501076000388286002040842d003500f850810165002c004440404002e80300c04908203a031144041c0403c00800704450020310101c42d805e80301400c946441c00c6030350f00a45002d070340205244c0d500140c09030f01008890815a0580062990500c4c544da8030176188404dc40319001038a01c0c3c0394801040d02c8074001072403424455510035a0f02d48035030079100780e01c108082510740280e03030034a8039125851008030320540c1c41d82d160400213240da4541c0740040700304442d6080284180400b2500041c5410245c01401c02e40f8146c1e000e4032807a41c0e4001c09009402c6c05c130440c030445040e50700302085e410704040070756011250003407401e0040050030b100400d01e0801e0a038800c40c0040c200040c00c0140000a10840e504014800d000c68550308280c00000e40e14080c641c0702801e94100003001c40c042011101c01c80c0d0910316aa240600710f447c150601400941018411910003410664034180c600391911802010600586940c030b4941d080ca08418005e40003504200341103130342c1d5032660001c20032200201d4001c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213074640 1250 213073390 213073423
    0x1050a0810050603100806070903033f051602210c01020c0d09060311030411010305190504031d010816050c1005010b0409230103080304021c1109010b1206060d0e 71
    0x11407402c241145407c100621190810090a03020700000780d028941a540b502101000c0081c9854802c0c8502110041548541c02114805942d8040740a03074000314850448150740d5409034510a030f042c0e88a0107000c0d9030fa8002d4400729001d03442c030071000000e040d184442400040c00c2c1881054417a14040306500d460000c1400201c04000702d030303414003035034a00c4a4010003031811810300d84e5540c80c1c914485034000d0306058480000454003584007514204240e001182404641803e040103003940c0c001c12030320320004170340300e44201700c03540104061409149845489400103020f4003040b10345030818042d681c2c1d20b019000c8006442c3c1076034040c0b54040c1c41d40742c00d05a07817503150140d0401182d03842c543c2c80c10500e125103280e007801580c44203030340c0c11603405c1143e895482d500c1b80300044040d071026080207103000b00d2803484400e0000b04514001c000703100340c3c1c9104403a45c035900e0f405481d01400910103c004008000603805042803000352030313807100c410008544001303581d154030708201072424410141e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213075890 1250 213074640 213074671
    0xc2719060f050117090a0b041a01090b030628022701170f04031b05100f151214030a2115031e08030c070302070905010501050a0810050603 61
    0x440400e2048200422000e40761211141c42c100c006804180f031182c400b408259101c00080040e4014458455907a604c22a104900d10301440c002c0d040d54001106480081c0060001040640e01403088213803600d1300a006100c0d5940340300e001c803d2500311103118084001d01e00d840c07820381e001c40d001800c01c110003940440b40000580040c1e413042c07480c05028604000e8501001490a9412650140c2000d01c03038044201c07607500d80c10156401081511541c100007003c000d5002070000c0801c1074003c220f4081828001c2c1d00c110840c150990f007122951070686440640308010203c0710a0344480c0107442010188601600124030b182150082407001012a660100280802c00d042040c00041000600d00b00911406d01103e4000b10496000051443d07802c5100d2115958418031040d14169012480f150b42e0310b00307aa21199203030070221040b4094464820046441000c60050b0744c181d40042e500c01c2d040c141103860840e4404009400c0540c1c1080c481c3c800b18150312404011445081469002d266 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213077140 1250 213075890 213075931
    0x30c0706110303040f03270b0c010b0a0308040b0705120a020606122b02101113050f090604020a090312050717030f0601051309050406091b080c27 64
    0x5040070381540c0005400030001c110005103044003098840e40c040c0740c060340212003002000c0b0110309601d059966500c2da0340b00020144031240007040e10803100c10080c01000d100307005201c105a420b010003801c1c4035051000f40510442c1102415280b4051012148400224021044160301c15000c090045c0c0088041082505044000d00d84807070320072004100008030000c3c62071031341442d80546004070074079840e600016842040f003010000c950300d904211011071342c900da04040d8040c03060720140341e080325070008680c0790461501c0c0d8030380405004186141d0398a0700300700003940565082400d0080503900030000c2050801480011505902c0d00e0317544807440c1c285074240d030750006608614031504108000ca0060052441500410b0a00b062502c40b003883c601c48090f1032480c1c006000d500c0c50031042000b44140e60300480b00b0350303000ea00502c0c1d101d1448585c0c0c0c049030a003401202d65940c4120900012420913001450881c03944019154409101d1820111903242c01d031903450061066440001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213078390 1250 213077140 213077147
    0x207050705060c0705041104081c030b03010903080406110705030309010c0e060a022e0212010f0501030e03030f090106030b0f160305010f050613090207050d0f02070f0e07030905030c0706 82
    0x40c041c110071a15a8184041540000e94804003805058000e80c0c4600e943c6000b00388a0b800d9801030900c240564401c01c61110200703040307107040918880001d0030085108640d081c1844ad821103542c15540d0f2000a03a11619404080e1241005520010500308000d10114134248050f60060b06401c0011414894460005002265190030710b4031611081040c0c04d50f880d0009200812015011035500701512030b485c1d031820071110050f044056a00014225070750101d10500a4103803100340308801c020719141d100440841d08083d2030098a9030040021640855000031100c2c9d0043da0b8a00110701161a80d94030f441041d01030340c17650501099a8280060a600407034842009546841c0c1002950701d0b096204902d0a41c0d885818022200064808201d202c8001034201070001c2080035543c8600307a2401c1039660103407103601000510185458072200b8404100042100d00000701885420308080885560510103003001c0181136030f1f0388900c00020028005800a00f2940001c2d00c030440ca03011015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213079640 1250 213078390 213078403
    0xf0e0f030a080a2c040e0c1207080f0f0619090c0f0e0f04030f0f0201020712020f06010603020c0706030f0e0706050c0d020a1e03170109020a11030c0a0b06040204090e01020705 77
    0x21341c4400912010b0f42144070000030032502c0c80c00407180801c06100c1440740d28103103c0483d0355150060114a0741e10310b626400220032081f5000c44084801c00d1011240032621800d9072210100302d500004041400018040c101032501c00405600203181020342d42e50300300341c8840768040c20643c5038200c0100001c00c1800074040d0300c0301442c40c44903081d10341940c0c01003030790103480c12600a0009903d4050002c0d8402d5041e035440030b5101031681d9001d8106200a07545400300c90340c24045205070b000126170180b190080e50b140d621807600410380c040c1014403e4001d031010440c07040c0f03615541d1800301d1074882c04004d0180203004507101c0301d40d40d071680c3c00d6031750420541a512605661121800300000307801040103c0142c03000440c80500d0342003a00d02140c22094498440603240e20500021900d10490780c020259652151101c0d0360440074901069101d010740c4240701d0080d00003012a80100b01144815544420b0050006140035221607800c800c03204688070280f031582d8040761240800c1780c204800b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213080890 1250 213079640 213079667
    0xf060f0e011704061503080714191101260a0b0a21020d0804150f090e0708040327030501021305030102091e010201090213050618070f0e0f030a080a 65
    0x145194050920341c00406000608018521940c400072a8409000e11744500301459110080d07581c3e541141c20588948600c03964841401d0040342d4003244840c058000c03c681c5164050011140841d10030015255000c84a20706c01000400c2205820b000750042e542d54800c04215500007602c00c090b0341070000401701c2c2e800c07115400c000d1760f00140c5441034105944041c10f0341120102d121071001d1904807694000d55105130b50740c0044c101d02c0081e054105109503050a00c1d03507100c20500341d440800015003403060368440c01080c0c090012801092140074018910107a00d292594200d100c0701d460003c00400d5801520140d50104106a11190a111840050104034020350520036041d0000d00c00c0c282d8405420001b5410000b2000350764001c0d000416072907001030503080020346111881000c4c21007111100c2c4202010900040c1100600307950900500d8595520745110004110588850803da02d02960243c2e41c0c04200b02036a904000d00c031441d80c4150306858850341c0701b0340080d0002161481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213082140 1250 213080890 213080897
    0x212160311120d0213080a030c1b0b030c13080f0d030f0b06160f08160b0a110d0f0e120a0206070c0203100c05160507050a0501020102090907080601090f060f0e01 71
    0xc80512030740d40015a800000e0800380181d1307400e0104944001205e840d40160b03224002c565068044c0b6420480030b80d40c2c1800b84014001d80080b20220080a07035003401140418881070003c03413060401c039400340c82a10080b007820302903c0d8460344c1c03191800b4000000c1d030080b0342c01340194205042e81402406180c03803c01006125100d01c0b100002c0c010700070300311b4101c41c940c100d190841c14400030004c0c001619030004013165807007460300d81d059452800c00340207031410007070540400e1100c0c4c1c091042d203590650065080c2e00301070703d84c0d0160000d030004005158416445241202c00004103200c1200b40401d80e4000c25500d25002a000c0c0c00c242c0c00030104401e01244600c0000541c402240b554003281d00b8041c0091038514280090300c20380509201103a4400710500b010040010010f641c2c001d440f81181d61a070201d950f50012402e07845801c0703400d0307041482400882c04160154034025005041410020b140715240e0481408200040e4000b6000500051007202c500e07401c0210000c6039203082c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213083390 1250 213082140 213082153
    0x5010f0302090910050903030a0b0d050a14030403080d020909011a09010818100c09050d0f0204020a050f13030219030b041209090f050603060a1b0e010212160311 71
    0x10188440800512000e4058241640003038030300101408201c400001020080207541440c0341150b0381c81d0400c4485003c9580f80403908102d03850058400114070b5449001080e0780102a565209895008030101985100500001c00002e98110251000c2c1100d0440161113211003170421085606c1a0300c61286505c240e5100d00701d5441c68012208101400c2c203020070300351900c28401010050101070840a4041c4040484003088a030304001901982d0361384004070369440300208203000540010043c1115024802d000043c1015009060b41c41031908009061045c0310b5403041840c0e02c0721001c0710071644030450a00440c542802440d841e00c10508038899030a080d0780e2010000540030b031014004042084a050180d13101d12070107006070240c4801488051a4036840c0d401a00c02502c00b40e200c0e01410700040d0111540b40702c0c4030840495410060f9130424889401d5138a024041c0c03010b41140030325021555aa0342450040000782d03040260071021541d1800c008020b4034034680285429004030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213084640 1250 213083390 213083399
    0x5010e010e01061d04050403020c010f08071d0409050303130c0812070b060a03020307090c140a021509150c0a0e010806010e0f010203070506010906060212040b04140402070212010204050f01030501 86
    0x3003003000d066844508101340010341c0710900c0001c1c0da41c000300c0c80d9401810001007000300365000c074440074540320a8a51b603031140c0000d402943c64000c102d0342c0c40c0000da42d080180d1038921261480700b01c0400e0140c0b0000320103a050b128203056900481d0365001e121945195035040144040c21440100190006400c204411001203080d0307202c0c103903000d002c048035880450300e20783d5200c03000002594010100d4441c03da403202e451010b00b2a41c680c107408260606100080e001200d012944c2c4c004055001d004040050381035a4003020024102000e079101d444007145a03c4528070269024440b03071712041d603c239110544002c115001000d041410071540c0c109014659800c06907006900340b00300d0312005444c0c180c00040b4914040c003800078060f44074400000420900729803100d070036111180d0a0b5000413560076000d09071441103128048401404100c1004162003e184110316a60003e001624100070342e0001014845407142d0540c051f540082d042000b40307400c600080503020300b802c00b0b01c03136503261 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213085890 1250 213084640 213084659
    0x1207030f050c010e0a150609052509080f07090b06091503090124080d0c1a15060721110606060a020a05070603090b01050402030f160e040e030d05010e01 67
    0x30450031062100110b0481c88080c401e402c5641c1c441a2075040360125030305410b09141c3ca01905100c0a00c17240380002c007207175889940c09000e1103260341d07441c1c0c04814260394003410411118250104100038000f400400c046c1c00c14004054460042c100070481c031410080c1d484122400310203018800c410400140e001a100c5000a1007105020318196403a640c0d14043c40340500041c41c5048010220075000d4001c1c030f208641d485054509072000c840c8038200c0c00740140d03a403040075040074201078000d040700150120107003032580c1e0150060722003118071b6000401154058010010442d101c01003e000045e181d002d00c00421080f201500d001042c18114071141c1c1d8071403038040c02e00c900540c0000f400c0c0b46100d00030401100682c1d809002c540c0300b0741d46c074030004004000754041100d241c80b20343e00029007480c0500aa0f030140c0d42148800140e40c4400152402c002c48854221042c03110085600a45a5a5208140c0d41070501c102441d604c2003070700d84820803240d058103d6003c200400c030051202c01003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213087140 1250 213085890 213085907
    0x3090302040f061809050c0d030503092404080a0207030b27010605010e060c1504080301060f050f030f060a2d120c0510050403020402160203101b05130b0409020a02120703 75
    0x204528001001071179030402600340441d403007005030461300450382181010303030100040d03100341d41c2c0300141c9201e0345e1680d001c410445c0300c60700c0349480c100702c1074003140c00b003031440e40102601b419900482d422940d40355940348180030704403100c0783c000c03049400c0d246030044919001c007100750f00280200800d0f400c00d00040e15003030359580d0180c0910030104501512100c104054203100301002a009024a410700e0b2140c42c6500902400d8001128508805885801607003500c1c50300c07040c100110b04507901d80f00160060030300100116032140003141c00085928075200003141800011060000d80111500340f5214901d580d031024003841c03407080e403010100710741d0480319054900c122408803030340015041c01c841500450300065445880020218411880d0b03116001d02244258103844254400310b001e00c04880040d401c0b0380c14000700c02c0c2080212071040f0001c01c520444c0c202000c1c4460348a40c000d440a4102d50400b074965540026841140c9804004501448142c00340c20307407074660300b07540c014800351 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213088390 1250 213087140 213087179
    0xf0f050a0e0607020303070c061d0106030212160e090c21010e0c030607080903254b0b010f0302011403010b0f0918090c0a1d0103020f030a02030a03090302040f06 71
    0x4030000450402210360071018217403d0411032b03008502c201e10801e41c004e00691104901c10b41d142d1802c0f901340030021991a50040d031064090b0003061418104074618003008003c01c489004114104c5001e983d0340c0303c040d09000ba240c1d1666685441d80081c1421100040c0300d845850f804490b654405640002e80d081c0d02a550f1b1400c44101c1e1140554507141d802491040d000701c58201700d11f6421004101030441442d4020555000640c1d1a00d55440082070b052600c6152220f01c1517841c003000c0384990300c07051205081c00e4900d1250302aa19205080321b000e0700b01c041f800c9403105003042035690114162420102180302e0300e01e0b40d40751000c180c14503c50381c81c0002e00c000000c00c10b5000366540080030022890018101989443c002094581351031b001c1c40001e11618500b07401240d06107040192a86000c803501600925900399000c1203140140034481303552521403041d9020040c0c905001c101c003c1c920035124000000d007540b0411090312005400400e146240440400059400c0000b00010f030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213089640 1250 213088390 213088397
    0x50f011103160c03023a02031533040f0b090103121e030b0a08010204050a05010302070804050a0b07061103041a191814030304081b010f0f050a0e060702030307 70
    0x507590b5241c0745040c0301c425803000c2d50052040480c00045042483c0916404070b00e010380300b015040c81554068014880c03400a50140e001c1034484201000c2288402d030098050280007250100c0c60343d203c0201c0c0c444110810030b0010030840600d00b403e0a0190a1108080400134800d0801070000305810260502c0003502c0e03410046d070840301060081091841d0000450514800088001400350146c0700c070901c03250288160031000109848180b007903409446000340b039841d2a0313140200445c040d4105c10001d03540d9007800c0000240c035035618001c8034000c00d5986a02d0341c8415090410100316800c2762480c4803071030400c0080200003030111a80c4141f014591550100a0700d4298800058202c0300f5118004186402141a0f450740007002e00f038400c03480b50342d02c2070992004070f04107034403400240c80040920009100464102c0c100320700c5440c0b40e0010200018400e0401800e40d025603001c0c00d1102c96603540d80b020b0001c6086c03180114024210a10001c10a44c00c0842e80295240701c018400e0041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213090890 1250 213089640 213089677
    0x80304080d05070c110d030f0e010e1002010506010207060c0503040317070b01091d01060b0a051c0603060506151215040204030615080f1501090c03091b050f011103 72
    0x40112040c1a2400e44104110412951420750f501a1100c00702c041c0c25900c8041d260000d1036289451155048520780c140d565404402000105460400c1c400c0702c0c55040c4102c20030428003035120303441410142070030390303001055038200b84001900708502c0341c000c0b40c00c00c01ca06003200045600001247c04482e8810141c0d130140d214910030092600032030700001d000c507035540c00000f10f0511a40240c6000c0f0b0800b28420303440510300001600700da00074420b00b44940c405101c2c2000207805407002d800b2101411403000d049100e05122601240d4880c0c0040301c1c1d0540d0b907014492507041501c80451b0560074800d0321031070013246106d48401140b0003000c4085103a185108078030681c8640d01510021540000e0600001320a10a20a00398407180281501c1d40304807040164200d600044a45403030002600a2a6507402d0003007800203000b02d0755410050540b02d40034030001982c6180b0742254010710035510ba0310070b400c11003004882c0d84403031542c5040141884004038209800310844009101801b6060308 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213092140 1250 213090890 213090893
    0x41401030b060d060305070602010209010801050904020303041703132106090804230f09060d08071a0106031d03030c120417040605030406050603120409150b0a05070303180f080304 79
    0x54101618036680004000c240b103c00ca0103560800c605480c815030130340f1a00c13502c0d074000b00d00700d000741c2403203e000580f243d0041090341400200c040d08280040d042d2403809031250001185080e440c1d02d9103c00c0c0d0700000301c1288603520800f05c00003500c010f120401d100c0e00c4000302c4804803a6080f60180c651365840e44980208080311048500922a0b0107040358207401044804c0031400700c0658440c0036101100d0b01e400d061416900712449928010603031a84100e1540380c103103040e08802d10840344421060300032030200d0b1030701c0d07500c41c000d00716a50007055050541003103903203113024401200704562040c0180421141d840341a03601c10198070b6800358655440e802d1410350001b04c0e0407081056000090080340a070761081c01140f089000f0201440b854542509041d59080e0b0704402c050b02d1507060101740246001b03504000d40b100c5411034011003c40d01e58502203c0ca5200c0c04400010401c001400b104150b0140580201d02140c903003007680c80d41e40c6032900c11060445407030060008000000040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213093390 1250 213092140 213092147
    0x31501030e0115090f05040c030b090328020d08090d050a0903021512090a0c150c020301320c0a0507080409051518070c023607091a041401 61
    0x1860518600038003010443c0c041142d00c4030b401c2e00480e1442800c200c00d1108000090140b2030180340d0180c50358800c146181c50303600d1904005048032403180030410000b00340c40b14000240880070181c990b10310200341416000707403400d203d507108030040c803651a0400c00403803408620440c260419023080d558680c100c081c216404031a0f034100944c407003141c89090a6040c0075402510000903c1d601080c66912403440c0e00d5a41c410450000701188034080003880200044d900580e0781030304030700f0003000d498007035030000c0c2c03d41d6811741a40d0130418242500c112325005100c040d840e00154550040c900d81400d41c41484e940c468042c0140503c0030000c1c0507070400ca80c5808440003423640003010403043c01d01101e10031141c1070303c0120706d00c680c080d2031081c04400c1c0c0c08403000b40220760689807105400400d50a01500001c82401140303916040c0103880020310704106c0da110703041c0c1e060140d0303403980c60004030103071840a0300c1d04a1001000902c0c5801c4c809a40c6101301c07416900d40950001407042c0000048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213094640 1250 213093390 213093401
    0x20c151201030b060405101208071104022706042301090312020106080c0103110d05062407140a0506010b0c0c210c0102034b0307080f0c03150103 64
    0x9540c00c034840001051002d8104020f0140000319401d00483c0c95400007070400007880e000e002d02004d403400d41240014a4800280070061055a401494040d21000181260401d40d1a4685003841d40c1d4803920100021580c0e103080b40027251101d06141c186401801c40309040814040900b080386000000c81c1e001c4d05800000b9680110f0a00caa07040460f8028003803c03544c4281001b911443d003840c20301c2d41c001d01680c41c04400305a462030400d540d43d40b030748000e01009030009403c80d0a40b4034030881801c4161250345280035419520f5078818181c50710342072514420b0a1400e140d005074070140000790002c1111070468441d51a0b480d02d07940003120b078904101504905a078080380d241c100344140500c01407004500d0b20081c05841e0254440001039071648180e140051698424600e41c840052802003400300314103070f000b0145184a1106900b528945002c0c5141046d81c0300130080040050f401003609602000303000300301030581003119041000780805800d44117842940b181c544100c0e44a540003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213095890 1250 213094640 213094657
    0x7020d020307030f0b0604021801180504050702010204030c05030102130501080901060e1503010f0506060313150504030c0b01060e0603040303020a110d0807020106050f03121309060b0a08010510020c15 88
    0x2c1d02c00060f03a0f8034240e0401c3d5030340c2604980134449000090000e291600c2034565040720701500c010740300501401100d940030325107489080d105254a000c915074843c2c1c89082e21585e0302d81c000507070310380c11400d004200c1c5e120346c2c0c441446a8010000c400b02c900402094204982081c03d1280b02c5807200e1a046014042d2500070202002d6035104010b0505011585095802d800707074000c000515100d0f81a5090701e404540329074004404001091011380e842184180c03082c050040a4040d0103402102d006071602540e00782d000995014205003800000366178140188680e091000d9641e12400106019000050015081c1503004c113011a540d40075001c801c0341c40d1401e40c1a0350700100c101030060a003000c141d54580c0150b21340319000c580e9040c960302c500c1d142c16005000340502c507181203042d8555407010100000540c03422500040543c51801814040c00c9100300c100c7d211080603800034545036059000503c20b0008188003911b858000c907044008400036500300ca804100e160203907105110700f004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213097140 1250 213095890 213095893
    0x21009090c0504051c0b0c09010c051603060c0503040b01091104050d05150a0b09270d030b01030506060a120504111009080d02060702060c0a032007020301060603020f0d0207020d0203 80
    0xc025401ca038054024410707100c0813600c0c000034030000791080c01101d5607220000c0003000c150002c943c10003500c1e0050088448149444a402000e6035105070406c28464021025101c80c901d003807080005070300400b5900341c0341e40352090031032400b900c5010401c40d061080001207903440c46410701c450314060444002e42000ba12500d00151030745840c503900c3c005100207031982c104035408603013000d466014a00c80720900428804140d141d4102c80d0301c81d400404800e141501217001440950541030010101119103624006042c441d03101c00541518401404184900e60030001c01501c1c0f44c201080007541c055668001a040e80c0707619080300f92000c903243c0a50f1121070003810304403072680100c8020a8450b02c0c029a00c8084c3c0b102404d90b9030320320681d60500942c0042000075100e0b05a00d02412075402240ba0114450581c07542026400454541043e8500d500003414419810240680d100400007494210b01c0d2000c4c15001c081c5500815511000081c0c000a00b10b041d55611507503244040c3d0001c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213098390 1250 213097140 213097151
    0x3180b070b01080c0d06050a0605040e071e0f260304090e01140c09010f091d01060e01110304051e040e15070507080702010804080d05010303020f190c0302100909 71
    0x504604180e0848803007200c0c061402000400e103003401140f0803026a2010302104951403180e80c884024110080001d454503039600030000300750707545004484240d042c034805085d10600744010088402030b480e081c40401014103000700840003152000d20304645201681c520040d10415046015035012041d0f0700b00d40c40045000f080515007540408400c2c00410001c2000905035442c00310060004c0f5955541844280032001d920350107070b8040000d4440c0d500d40300342c1094961500d000c01d04020080800c060011800620000e50803807810314400c3c0090a2070003a6080380f50780b0555a02c20390081d030340034044000c600d40d15040c1e4503101400032100240140400d40c590003110b41e41d003003207041c12200c207801c0c50080340b2014001d508884040d40c00c2602c1d2441e1010540040d21039110180046400403020400210402850301c20540a140300b42d000c0c01200d0f1004101525045032074001103550342d07004a6180002c0ca04003052811694155454144049000019a1402d8507a4401c4000ca41042c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213099640 1250 213098390 213098399
    0x71806020606100206060d060e0a061b09080f0c040c030b091f0b0403080301030210051c0504050105010f0e0114040b0a06030e1605030a0b09160e09060906220318 71
    0x825140d21a100c1620304444100c84094104e903170b80d84c180d5419130054141a0b107140410799941000c44058918422103855041c43d580742c1c01240e8102c0da103030522861512030084515884003070100240103010003800740482e65160345460380180c0440c2c43c40386503119080450280290007405103000002d1640305e07207251441c400c504100d01142c1c4c3c00e0038042c5541e008100412000140c4040c2e0341c010b02c8a6046038216802d224400d00c0c0307043c1d68003c0c03101c1400701b20845868659455024043c241021a940c2460b25001d070a42c0d0060300f001d1009400316409000c0c0100b2000320b541121604d100c005485e25001c00072130000d00032215040c0e000600c1c0340021581942540260f45005800c2c3d04135114680101945c5021440e18004c6a40c140c204002c0d41c0b002c1200340c503d00f0380000382d030800da565500c141d0150b10041c1041e540075040b24481c0c4410460491418070070683c1c4045102c029195914001c00c030501c03424550440c8489903808200c110301414070540917070001d440846640d48a05454 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 213100890 1250 213099640 213099643
    0xf12030f0b01020d21150f060504471804060506070f020a0f060c05191707061d0c031504080702012703061a01090602120d020c01050106080601020f0606010f0807180602 74
    0x780c007036084d4002547c0e800107111445001140e0403036800904061030700141914101d407510741c40c0d40300d0866420300e040d07400c620400c42c1c0740c810019804902090740c81039958820038040c00390151240c403e80c5025402c1003591101800c07262115401000800448664400070344000d105070030466403503151080c00305006070465140c030101c40c0a54202c2c1c101840040341d5001038640f00500401c00301520009040301c1d1420780c06012004d205842c04690407030300e81500442a00c51045c8103000f039010302005406401c051100320b8045d0140360340d100d1549440c1d00c1e02c200c0c80c030031514024100001080d0000304251440c1c0d00400d428074080c1c480e01100d68038104103001d065681e81411070b502020099023180e40c05220844200c90064002d000c0300009071000e440a44c01441c0c01440c00c03a002c00012080b882d0a218041c0a003003c0e44070b00d01e40f410710200080c5007074401c4514080c80ea0042c024040c0c26a040280050001c2c40c80c90030000c0ca0f070f1450b408880002082591000380e030f09280011514540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 213102140 1250 213100890 213100931
    0x131203030b1e010c03110f06040c170705060405090405030f19140c0a03200a0f06050609100504021c0c110d0302120a0b0109030f12030f0b01020d21 65
    0x2101d8081855403402d03524128050340d0700d1a6801304005008590005e030091420305940244102555078400c02041134030b04280c82110100c80d54142024140586201c2c0541e01401402c90802406020305140104069204a0244030300c100314a030002800c000013001111200c2c005c4200542d100d10502c80d80c10b2503034003001e96403008210154400c0602401e0306041e03070801581000203060340c00c825242580d080c04210310500c0c4c0e071000c5803510442100108817640003a4840c4c04084248521818010700316500501031070b1045406038184640e6410004150003034a03012180141c0d0742e50007080d900f40c1641110140d980c03141c14104900340c1d451704080000398030301c400c0d0240e484d0001d400718214100d200c0c41c43c200c8006402d14022829102590340400c441d4041810441c2c610341d242c1d201d03159020324a51040316072560b80c07039183c030807182d060081510f00307090381e84203001c0340010f2030000c0d407608494842d01040080c3c01c2d40786805102c42290640740c2c0b071403102040003005d1803100410302059 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 213103390 1250 213102140 213102161
    0x409022404031203020703050901120b0612040c05010306060f050c010209121f0e030403110307080105090601090f09080304061802190602010b030304080703030c03020307080310080c0f03070b13120303 88
    0x44803c500c5018070781c0280210340086034155501d41c9015113510054400078940120821903603541d20b980101d07916000700a044d0f1003420b40c181c00c2030303240034580032048000f02c2c3c020504050529804018098211410304e42030720a9040540e119004601c40f14024084e0600d2039510024510390801d40c10f0b400f01e0700031b582e00382518104c0d1356214411410740a4039003003642d440d171a52040204001054850701140d03130201d0000d060b100c41d2035452240c50b0035140b05485030034103600014010000c5145a20801c80d070030f055001c05200e0b55031641c030782e00c4442c0001071010304142c0d201e8010800321554500300341c10041d40100040050400c10b03088942081150051401642c40c0603000d8119107000806d81e421030310301400405100c0d0071a54204d0b8251030700c401c04c030258401441804002040e01018603c9a1991804103c019151070781c2e00340741c640903207103071030280c3d8182148258589011039000255201f4078202c0d82c0e1007101720355040c420009648850741300a407246c0310408156150300b0404104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 213104640 1250 213103390 213103403
    0x6090204030605061509040f1e0506120a020901090b13091202160e070c03111911010c0302070e06010e150a08010e1509060a03020306040f1b0602060105040902240403 73
    0x44e07462000b8007040202411114134105014401e21143c0d14281d00b1104404560b000c0104680000c2000d0400d000011501a18129211005c0010509080d1440c54034944443c0c01081d20086a4010403030009042c0905c03c1c00c00e072558040101c584520300304070081141000100408001030500c201440d104442c4600140580302ca014001c1c4103a8806400b40da00d482020307103568071001010780310301a03244012400d201540c076903a01c00400a00c40940e121600c4103000346140b88502e49230740150365038480c0c581071010100901c2c0100c0d500003410002e442d5180b41d2134000c9e44515005035090294507000c40d40c8912884c0d002d02003e00e610340075068440c0c907074031003500a90301c0340440302001c5c10848084411854101648520b49010740d8402d401030000340900100589a4000ca420001c046901340c94a410b1101d040c0c041109046014460400c1600400007850801d0743c001d445840600c1814820368540380c000e401d5640c0c3c440301c04601c550780a04a4407680d0901c0388064250411321042d10070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 213105890 1250 213104640 213104651
    0x2e082406030d09170a0b090d090b0f18030c04020d0209040606030608100f020f0406050306010806120a2301021927030813080d050c0f010c02030f03040302030c01060902040306 77
    0x55040002c0c40503039840d100d44414202ca0700342841c2082500403c0a0340c1d00910030700c4000780200e0f00e1500361600904018000e09030b03042e541a8040d241d4526607210406c0300f003003002a031a60648103802d6078175480c0328035001c002c6030301200300081c60f10340c1c3c1041030b6078031520024511280300025401031080b0582900c043c05403950700c150550450f01c003849481115080880e00b1400c40b1404c0e80040d0706611014801420184809840c5045400603048200898400024005c407513070020101d035071207a030846044600c81d03002000c0941310700b04810001c0c00c440140a02d421403421b05130441c11403107160802152141042800d42074140d041c144440046002030700310540c0c01c001e15020002540c00c1c0011860030520f9551661080e601250440c14401891003020035000403c0c04110040032a40d40e03125100c0b010459018281103441d80d030003166a240c540c0b42c1050907004020b650710b1403e441d201903220f9a440c10180d0542c866980c892142d5403074002c01041c000140e48c0035206503405079108009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 213107140 1250 213105890 213105901
    0x2130b01140306060708160812060414061f0c0b0f070f02010c081b07020901030507141906050a020a06060b0333130b06120f06092e0824 60
    0x4291109560064201c80c01704522030204039003130018058100c0813010280c29a507552503800d0079401111100c0510189a824085140340600442d00b0a506034000502503040c1080010b10399030140c40d10b0246549103a94185006003d44100b441c00d0742c102c5030b213100724a030480303c07940c44e11000c64840c00441d0064455214840c41403044500328032040e01c4900d0380e0381318551808a403540c80e04049151241c200309900c0181c035001800d0f8000c611440c01001c120b41880c40115503c425004964081d0070040a111700160616103414111140c60403d10340e2500c090204134102645400c0c054102402c21a00050300d000100042d071140351150311004051065000d040001c154001d41c401c0282112074488041d803600c0b035811001603e91501c0010415020404100b80d42c00c0409086130301d0703014204208554401e101e41c9503010800719804201807410032031250392080c078400c86c8820008441d241046001c0c0001000000d080480c088950392880410f803050590400445d1080e00d5952002082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 213108390 1250 213107140 213107177
    0x41407050306191512110c0601030605040c030f0b0403082409070201020d0e0c0a0501090509040b130b0103080702030c01080601020d140417031e0412150902130b01 72
    0x6014541a0340c03010315548520040056035400b40900c030044492070700c00000e10201c10441200c0612803030b114002511600c80c3c45608076079000fa60044000c2d0200702280c00090081146819a6401940008c2540b0380341007880302034105400c02030214140304034550501200212040c03003903129545604032581c031001c000c403002c1800509150f4022459618202c2440e1a4036880c4e4000361510005041000d1010b640c0306882c12445664242e401010000c030f424100041a00042c01007802c041000314078040104150110050000e800080da000100d102d8400280c40c034008990424802400c550711b80c1444803699001c800300300e00c644aa07400015413940946400e034441c12058011f4515299541002c0c4c0b1001100fa100300c001050801c0301140302d10307502d0079115200030100000d50300e43e00261705007406d81010a03035007040400305110400c1140090058210600c4c1d0000c4800e00c00408100900060a0000700080d8060304401c1c8940320300309039510400803130b0800da0318128858402034100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 213109640 1250 213108390 213108431
    0x9060621030305270f0c0f0a03080702030c04020a09080c04051b211009051609090e0a0c0b0a090603180f0302010e1002030603011409060a0b011701030302010501030311030a120c030b04020c030904 86
    0x590700510323092010800314160344054008580098142c85800a039040000d0480e440494150042035a442040c0403d000400c12015054410b807001c018a0404400b1104000c0701c21100c40c4440f00d00007009080d0411100d583c8960b0143c1c01290900d504140701007402c0196039002e618000e030714140c00109090720082d0441080d518070b8565600417401d0a1984000d44060785101c1034030701c914540340c2c001480035000c0b00000c14805803215103440c89100024902e11707841c2c0c40f4104140c00d240d1080380c0c6000c018168801160701c50041d06010700c6e117250a034054080720842400304d00800c0840d02c0726400380d400561050340110003c00c5100d103465104108400141c03010011688a800002c1d07100586500c6200810014100944030100d58011034407078005c00d03001140140d44031401081016040300c1040701c1b0f4502403000d5410070340c035108010205003011184148042d11010000b0030715000c1c1e800b100e100c0c3e00c040e0003075503130702c2d4042c410690b00e60184034903038001c42c039000d0210800000350030344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 213110890 1250 213109640 213109669
    0x306040509010911010f09051c02011b03020c09063f01090309050618030a05031c05040807031809062c06090414010f020d09060621030305270f0c 64
    0x403a050b030131244011280d040302c400510041c000003000202e1603a03280070030301009120311461211803c010b80300050044600e19401051040c60354000030001b50003107404418004192307006641d85c3e880380b00062071200141030014070b48851800001c9189103421002c8458402805c0d903032040305540560368229030300c03a80c001d40011000c5006100914002005040c45e400c100002e0164a880d28001707401c194840c14100c03007a0b40006101461644500125485d40e034040c41e0400c500e00e0141c44410007880360403401800c0104503910080090041c8151038068003030500100191916000060140042581c103c2d10a0340a8110344020185a1070003e100d040040e15100c410703120b50380c4a40c488127558000e500d0b40e54071900300764110125440901f01190500d407001c01c012855060003021101d0603001044070040520704c0d05584444a440d01c42031550510300041c80703a03140e0240e811141840c515040004901c0508400c01200024000c2c0510703045070151861000288100b01140c1e203100702 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 213112140 1250 213110890 213110903
    0x12230406090605070602090301060b040e011505030a241401120c0906050c03070209070c120309021e0a03050604030c030207121a04020f040501030602030a060923090f030304050303060405090109 85
    0x1428070810780f00b40090840b2902c144009410107103c08002425505503400460150502140422981e0f2111468600520b000081c152000341081d000408521000b00300312841a00c070004240a912400c010068060000904c0140103880da800552440740c00d04000e070016001131a02c8051525600c1038410406294484905940c980001a40d20360403050707804c0d245000c180003a0000d03864080c1128401c5869580e6580d08180b6894549040d0390510810f0080510b850304100050301d41c0001959403010140074402d54080100c0056840021a000140341d070107007005110401d50842d1220200f14401e0302035440d080e45415889098110303042c03010700300340c08a089081107500e0448181c3d4016001410f8421000442e0b004076041e2202a030040f03c44540c00020410403122500c9082d004c0c201440c400d011700d4600c009407600403115070300d801701c54112034004034040120030031400085401c2e943c01d60b42c5a103800c0c108141c40350000c40382c0034000c81c1000b002031880d800600ca10b0441030350101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 213113390 1250 213112140 213112157
    0xc0d030e0a1b0b0a050702131a12030d020414010323040f030302040e070f0206090c01080c03220b06150306010c1104060906091a0d05062212230406 65
    0x1c81c0c1088924001070b00b4104500b11800c0840c07404580802046402e4650712020b558440364410b01221005449482d003145243c0a511041c847c011042e928816004954807090007a0640740d05041d03219030744101c00d00d0341c0b00003400211500740c0c01d0701c02c1d0b550000362410098079440d450034102d1441c840c078803500102003401c00900080c0030b250681ca0424042c0c900181021740301c519655811006a5500d0081601700000c40142e070340c1000402d50001c07010001c0d2042c031000c0c0001030b0843c0c80107080c0720382d01d5401100180c1e403921200c807011100003100f60302c60921341031b03401c002c10502c01c181c4170240110410044880650300310002c0380e01824060b590311184150381d44443c888480c807046c42c1c55001c3e444034400103c45010380601000392400da1400544004034403104480075490408840c001c141814901000c250003042311503000c911183d0702d0002c0510050990b009801004004140240355049024916400782024009411038640d800c8603280e841d80c290480c2c000c80c41190000b41e07010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 213114640 1250 213113390 213113393
    0x60e090d0c03030207020a06052a0c0f0f04241215020a0903050303090f01152105010f18050f0622080903060f1b090105030a0923030c0d030e0a 63
    0x2032076001c0e4094040e207401410240700303500145c210180c0c2c0d480b8074001503020401102d030034142071945060714001c4122428081c102e80c1240d40312005010128441e102c10010b070161510341c07015007001c441e002041049142d400e910b503600c101a032a0540c01101400c00300c00700e054804040c43c82202c03070f08034601540020344041102e0181d44075401080803c400680000001502013000c1c6004c0d86c0c284c000340c0f40c00300e12944bd031421103c0101c1e0100d8072400d1604100034201900072030154003240c5046000d040d0240e030800c00c0c003500d07101c8424048686400c07e00000000382106607c0018820810380d0300010350040400c2d81c445081d90f040414021030104960300c3c500599091141501c80c03003255080c003e0300300000f4200700085502040d01060307001001114017002c20107129101513805210300344044240000c002e408000c01006040795510350361014050242011180080e07881c10002d126480c07840c0e115140e400c0216034102610400321703880105c50003030107408182e500e02c4000b0484840039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 213115890 1250 213114640 213114647
    0x1911030a08010b030a0f05010329040b0a050c040f080c090c12060405060f031b01030c0206010602060415020d0c09050112060506120a090b010602010e0705040e030d0504060b03011806060e090d 84
    0x340807174400075038514121074110381d64041c507030003507004509481d10390705c80b9800b0a16080d180c951207040d005900c1e0401c800960003001c0146c11140f20307080001c09640d0b040e4049414482c13600301d401d242100510021748001c000480048240342500c802040391034640fa030020a0180001d00203400c07440c1c0c0d0008110781801e900584c1c0c400801401201f114081070701103410030015000c0208030241000b50288103507014082c49a01c1001c80c03006019a603d0814020b4562130082c100400a140000c0404400c0d566501601c80c0208004010005080000d0000d02001400e105150208030303452900e11800350144100740c01c503070025100e9490181640d01081003140c000b0306088200f55102e214070040342c144600c0c81d01030881074000180d40600c41402078034024290348502d00c224202548640582c3e00801901e1030b100ca80350700411203403120f150181c06000086d404540542c40c20221001d0000b02031242c001080c002c02041110340e8440e0a801145101164285c05a074032240c5e59080783d030320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 213117140 1250 213115890 213115897
    0xf03210f0610030b0402040902040f0b0421060b060a0f030b0316090e071e08060109020306011b020a0b03270c09040f060b0603040b06030d020a120c0201090b1911030a08010b 76
    0x2d0700d00d00000c40c0500c1400050803030b0011b4000c84100c0350302160911840c8035008124018010504006080c031b0300d00741d284840420018451501e6903d4100504100801e54100700d0404200525040c2c44020000d4018030007001001400c0c0080d0915078000d46030701b004184070845a0203d40c01502d094100903010020349800f0750a803a41e4800c00c02d00140201007050001c2040002001d014007991030411010f00e04401a0000d010951041060240c10381e00300c0d15003411020481100c05140c0110700000b07020044583c007c840300031000041040c604000c2c0b40ba0b11020031024a494032620952500750f075141e01407140300d508000000c01160214034029040d4240d94480d000c08220708000c2404107000c0c5c0c0041d50304880d65510b81041c040549030921640c2000c400390b10007045241e009864480c5d10590b600328420034058036582c02415a4030400100b40541480a4041e68a480c03d4405400200b2031184030f8000070408010301400f040044116a110b0030f199540c81041e0342026440d0000f0f60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 213118390 1250 213117140 213117169
    0x906061d090c1b16060c0c0f051e120a060e150108030a210c020a1101081003020f0f0603090a020a1712130312020703060501120201050304150e0f03210f06 68
    0x101d02c4c1041c21190011044110180905542e11494080246054815031200e600450813030780b202d420a2060343c0310600d410003001d072441065044e507a00d21011071003a19a070400e680050244014120a020160304a4000700b12000b013107610381480340c880300100030020b02421403030380c000b00303e49074001c3d2044107031404005400c4016842c50045284040840701c00c0d917401c401580000041070140400502850302c001c100382482103013454590841c080d054400e010080c414002c0040c15a415110602c5402c450350015004680da801c0006810f599a441080105c0c40348075010710110301e00f918240a4819812400c00801d800007120114a41c5500545800d03000031011240000104520141f0180504035a40107409110709500b024025101d05801004029200703015900050340d010044960041e013003a440c00700788040c0e64903000a40302409440c180c5100d200c411810348540880249102c03800320208072411107000c10541e604079822220241c0c402e44030700010700c0da4109001a1410403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 213119640 1250 213118390 213118393
    0x20f0d06060e0106080f0c0a020a03121508010b0f04090c0611031e1305030f0a32070905060108010f060507020a0905151201090f0312060906061d090c1b 67
    0x280c0c03150b00e0300d400c000d0b09078414400610220144210700f00c40b0f00115401980804c01d840c0b50100101000c0d6841c46c3d402002001c128100c80300a107000d241d540b01c2201201c09108481409544100c160701800c601d4221502c600806803001c190b078a001e22400c14802d90007106910301520300003090310a142c03650158aa680010448200118645c00140701d900904031500ba894900c0384030ce0081504d81c542101e03001e0b0340040140c01d1006000600518200d900c0141812900701d0161001c59154955492100c001c0d10514445002600030031110151100020b0820282d03403602c0c01150000d200f80309034800c0560104040c400b103031082000f03214603800a0610821b40e0707030b1600035904841c42214400003111056114010070318001a00805a220f1003000b4040c442e03041d01e5141034502c1c5554000c00b03024440c0d103005401c0700701c0c2d004400180908e003400c01030140d440b03801808a00754113281c40c0100c0032040700703e41c030b07454035111503801150003041003420070350507100c0c52484c01007505000480303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 213120890 1250 213119640 213119651
    0x120114011b03171006030510030305030a1a0406080609060c03010308030601120b03061513201308030301151101020310062712020a230d1e0b04020307050607020f0d06 73
    0xf4240c540000d24001c0740080100a86a443e010008040310000781414081c0404c2d00400c20202c0d80c08015203811111070707c80080c00c900024030401d03034401c1e4024160380250401c01d0016207104085001c61081e00d0741d0302560400d940d5140030340603511007400000c2020354140042840755100f05d40350710082866010000302580741030b0000e032408ca8120f41004d81c0500c12640411107050010340c2c0310244000d1f880a100c04400000c4a10074a4900b002e000440d8401041c1c1c09e1459880d0707080762000300b2158042e2992542c50703515040c02050b921003881c003c03548811580540c2030051003100e01c1007010314041030906082800488807901c0e035081b41c40c450000a100d0056603800c1c250040000d00c084070f80f0701d903403011a2062003010107550f0b02805101480000c0901b285a0b280c8000090010407100c0707034a5940689045034000040c1c4441604040c02035400408200c142202c05001e103000720120389040da0780398204020b0b44505c8800a4000c4081c10b5022518103124600d900014402d070b00201c1c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 213122140 1250 213120890 213120917
    0x10e160c062013030201110a021309020d0206040305030c0106051815010315080705040e030a09030308040521030403030f06050a0e040f050a05100605010207030206040e0403020f070605120114011b03 87
    0x10750b08001103c0030b109140b00001c00456800100c61005d0f00184409402034041d80d0f0005509060031150515881d501c40c10200119511100038000143e0300804c01030300d0300d0712801d090759240c2118039103510369881d03c080491a40341c8810341d03a0150f0318924041c00ea40c2d9500c6820203003806144211814151607944004002da01816010301400185001704501441c010800c000c1c1c076404140300d909600100130903880340fa800706e03952085d0703a01800c0014858031503180c42c82c54800d80344181c1080958a0141c9840306440b0001540524000d503828040079652440140c1112510710455038007031200e031030401012210900c40c5912900507480c0d41102c0c034540d00c60604090a8039411580d03500030f4040c031006d50009225030f1b800740000b03200900005007141c2c04540248a07601400080f01c1c003190004040602c200401c0400104036000d0b40c120302d60340c86015200c0c1d0031002c001451080302e04008240004400d2121501000594802c0d4084010600341c6100b0300c408070068082000c0c8000642 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 213123390 1250 213122140 213122201
    0xe0c070305091323060909150903090402130608090d122309010b0a1202090f04150c090501020f0105150d02190b030a0c0203030906150a0f090203010e160c06 69
    0xe8145114041048914180c400b004208400030841c905c0b95041500340014503000092a1000103408e1000c0b5015842c3c550240707145000340b00903103610030f00001c0c1c0031071314001c40842001140c021740c54034202c030344a24521035100c20340da4201e4000a020300c1c2031070086800c1d54025040c2103400c0c05034415000e160701d1185202003001c49850f451a9100e00546025080050501000305162200407190340002da0020306000300c098400c0064a0040d00401c0a00544402100190134070410410000c0b00c03000004c0d011052500c12180540075011428150a0041c0a40740c072842d0740c1071058240180305020440410701e0303017605980100690b080c5e44032402c0201260009041d02c02c01e229100d141400e0f00109690f015000e6600710f4105006012114600141040d081040700048984ac0180d90011805019082d030117540e8100000030001034881a036401107060750701d01440801d49949000d900100580e44003110800075186811000100380700d5403042502d03400000c1400c170030040194550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 213124640 1250 213123390 213123401
    0x2071a0c0403171201080a0302060a09030e0d2003030c070302130e032b020c060601082214060702010b0916050405040e03480307050d08100e0c0703050913 68
    0x242e003c050002407190402d0341c00307803d29004020400c01000c0c20031682d68020b40b901405040da0703201a40b540161010235024044c1811a0381d000f502c541c55100e61810002200c1071042c21820445400c140315100c107050120855120706004401401d149107140c0c01c0c440712459644841c480691b403172803207400340c00040c402461325412444002600c0410340400c4c05e4542c5c20041e0b81a0100d10412001541c010f0114580c2c1d40441c0c00d08082003182c0d2070b00700311910040d9102d41c03500030418a100042c1007140305241d003110ba441850440303840e943c80c508203a0072a240060300550000301d42c0005520369052071049210084545070140c142036850700441c003900d4042d040d0103c29040410b90480a0448540412418028800e600420912b491480c408000c000d42c5031112403c0c01c1c0350fa0758006400300200c3e01c01a6014046400c800d0a06000415000d0143d07407514151403803c000051007040e4040c2c4602520a01a00c0da00e000095079041e90301e54401807503d41c1102298282d181d9105c014402d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 213125890 1250 213124640 213124673
    0xd02070605040f030e06040f09020c071802070c08070e010e040606261b060a03150329070302041d07031d030a030b04021e07020d0606091b0302071a0c0403 68
    0x3088220f02a41c40e001c2c200700b40751040d190040d0f0f8203200400001d91048140b0302101d00c44440185d6400192070500e00b8213585412035005401802c1094036201015070081001c54010325040702c1082c0c88046060702d40300580303d0400d40485503030040c8010000c40302c84a8010344106070005416980c0d1002c111500c0c00c010070b4285152002001480400c428440000320061b401140c0a03d2403030f0b100058558001d001c0202d080550b100380c40c50807600741e585c27000040d5400c5030003002c0c0801160360040c070302c5c0403800c00e00ca03103500803002040c0d92900074000d0b5403d45180e8034980d1b218080c4407018440d0f02c600103154104158540140c148101d60401781c000b0004c044101a640c0c40d00000c4001d000d0311b0b41c0910b5140194410051442100c01d94400000340034003500c03070740c3d94650140c00040c09443d4a420040c1503540b9001000512000607801114490345103040000819000740060f4224055080050180841620780019620500041550211211249a05080d200d03159203072160a080d49 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 213127140 1250 213125890 213125903
    0x304060b1f0e090c03040b041b030503030a060303090806090727021801090501090e0a020a02120309030403020406050d0819020102190e0a050a06140f07120e040f0216080d0207060504 80
    0x902c0e42504040307002ca58080c29900102d491801c0c1982c490703070081c20041c8050882c40c04503000103070401c0f500b8201d10043d600081204d48900f052464400245240e100450226500c6840003c00000c08145a0b02c82e81c11240135150144c6041a0616858011180f0100d4800340035500c0380e46c2d9999102030070002e0701c1d00c0c41c42c00050041a0003d40b544046030081410302042100811640c02c800f000b03a40d00041011025881d683c4075030040c4d1070000360301401644104048208040c540001000c0e20450707008507010710007d035841061161b007038000710b03001d00812070801c04400340714103d070a42c11203280184001450101d00c80e104450318010b41004000207460390346144201e2078a48080c1000d850121072130400c051424601419001d078003650410341050104071542c85540d135409442340960842800ea0048500e100b0080030301808003a103034441c620b0880221241c4d200c501c25a142001c680131503d0f00c0e1031250300c0301001d5802c913081440310690200319a00000790a07000b003500540c461007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 213128390 1250 213127140 213127157
    0xa0f020f0408010c030b060315060d0603060608030309100c050703050705070f090603020a08070b160303061d04050f06010b0a12060504140708070e060a080603030702090c0a230304060b1f 82
    0x840042c186c0c3d1081702260700c19502031040c0401d80d100100144001c0303600321100c0707a40c0c0042c09502009448103070300c081c0030346150500c0052182c50100003184101510020b48203140e2920b54460200d40542c44140006034040c000c80000138022802800f03041e0048003150000b030350b0303240f4000341c09081e500104a0151218820011403c1040c2e17180050b01c0080040c02400d4200340d042d02d20b50148d0b51440300308030700c800340001c01e0500960100001e0b01140b881900701d250718001200518105035001c498511413081110302a40022880e00d0580389004034503403404c10042030481da00801ca9812024855980038000340d80ea42d00d110702c2c1580b6412004840061804500c0500780f060300404800620406c98200d080c02d686440071103000d0b00407420038500548400020074a980650240250015007060a004141c0f21207005801008165a5650700f4946265160190000d504e4600d100c070110074008640002c007182c00900d259038020705801d6142110251200c0603420101d0f100011903206c1c0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 213129496 1106 213128390 213128411
    0x411180405010c0e0409050703031101020f130819080d0c050d0c020c031903120509010905100e0601090506060324060403140f0609060a0f020f040801 66
    0x8100114040c6414901980246080fa4564001c110b054850031071601c0c140c0111441d29502078060031000e442d650b03050360010050103901c3c4455400784140b00c02250902c01a0210204403000310b1700d414a4030500c80e0034091824900c80b445c0b15000b24030804182050100c1c1c00a003a840c400142d03a0390902c10032126802000b003141f1582d810b02400c454896800a640110624100c05a51040640d5400003072803144040740103012803120011148040141c2e0b00c940d0b840000c207000405c900c01681d80d01402c3c000c5800074141500c1d6030b65003540040004100113409440c070501c040195060040001760540001032800031001e04022880b503100744607100070b01d01203d014002a48440c0c0342c0c6062102a03400c03030a0000075115010104484000005a01c0c4c042d03a41003021b401c00392a03a5a146006e40341c14101e04503030507000c010b0310650301480d400800c01040400300004440407034 = true := by decide +kernel

theorem cover : BRFrame.Cov 212949640 213129496 := by
  have h0 := BRFrame.cov_init 212949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212949640 ≤ n) (h2 : n < 213129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
