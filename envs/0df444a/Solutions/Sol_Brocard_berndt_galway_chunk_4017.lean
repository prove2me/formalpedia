-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:01.172671+00:00
-- url     : https://prove2.me/submissions/2ff239ed-7a31-4dae-be12-9b5a6eb44ac2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 722302158 ≤ n < 722482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 722303408 1250 722302158 722302169
    0x10905120a0b060907081504060e040305090a06050f1e0904092004111b010b0306102108070f05030904050a090614040506060d0201050d0c11070906030503031303180303020106 77
    0x10b11940c0c2c0d030b9020016202c800700e43d039078003160f4003800044045c020402d03e055101402880040e040780c540113804407038081280c00303c01040700000c140085140148105c0b001b440c0601d0410b01d840100b405c100107a01908823140703c900c52400714201d41820b00c50940c0d1150801a1041001c400710f41083d45070004900181004140000c520001ca41014000c04105c43d56a800d550720307007050070009900a00442c402c00c81c803556140303400320701590b040c00404d00641d1107403101541c440c1080e000c100005500d000d00140e040034180044001140d40c4151420f51340c1044c20b10004403914280340d415442128021135202d031a0038100144042150310848850f0701a441c108142504075407001800c140540d000340c111f07403084c8001079480c5480340d03201c0211441803405600388030b00040104c0c00c0d5056071004102040419a144208500c100039500c010642c254051207443d00e542c80c2d8035200d11028143d4690301c000040004141030017808000d4100000c1e4030040e00c5107a99080c024001c1440d070298 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 722304658 1250 722303408 722303423
    0x30c0d080415060b07030516060e03270306070c080d0528090308060402130918051c050d050a09080d0b040f29210616091d0402010905120a 61
    0x120001c1d548901c40ca0f01594900312125190048070b0301d0558242d044404c02c114003c00821b043d42c00250785004440801b84040f0040d5110604039004009018110b400d00316100711002c0c0c884055a800140d1540018440c06d04c0340d040d0409041900304c511440144403d00c070304040500c003032708101c584141034417141400c9656108c1c01413800501503400b00ea60140008001d04082081441c0c00d900902c00d601030740441c201c0385a41d404000c070581c0e036001180d00c030080b0305e03680b06002d00030180a511442610450684945025204058a14091904800745159a400c0011801042907100305034040e08a100f80c1e0b120840c00c0c010801600420000c54003a504040c41d00c1c24814142c0214990410b1180760100003000310200c41496800403440103902030011040d1400c05078075840e14410102c4404c0c00b820482c0780c01e0900f40c0c3caa03c803890364441040010041080084c070030b500e40142241100c240f203240e50f107842c00100c0308020b098100b507a100404094403801c41c10002041c1003054812000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 722305908 1250 722304658 722304683
    0x9031a0402040f050c09010327061a030c010203190207032a050f10050309010b0d0f11010513050103050405150115110c01301401060305091617030c0d0804 68
    0x243d505485080c0c920805692041c420040ca56001c1d40102d82910803030019442d68501000c24030100009000c0300303503211942d82c46121201c178603444821000807815401000079403900e00c0001d59074865030382100000b6a503861354401062003845514011a0013041c407111824508034268000d8403480c0c0854518405600d00065a003040f0174034180240c0000c001c030322010400b68060700c0f594002004411a5540c500031521207a035000700b0b00040b5030145451842240003490250320348601d209200d41441401d00c0320b40c20021810143c0b030300387c49080c039012585441f649840e51400c00c0d4820503000301c18149002141d00c0048a105034103044065450280c0d01c018005102e0701c520010002ca400036110300c07a56480050140030045c0b80c0255080030034000a0483d601c8011209501c2d8504104030b280001000280c2d454000d40d0342240220000e80482c006003d07101c2043e9005105010342040d0203480a90044802e005030f80c0d1000d4410240c41e0395284460340240100401c45003101c1e030150286 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 722307158 1250 722305908 722305931
    0x20408060c0c16081e01180609020114090d06022503050306040c0e030d0818030408060411120d08070216090c090b040b03061509060a02010f1b02070e0709031a040204 73
    0x41c490104c0e00c12002400703440c081646103541040034820a0a607940d00c8450340b44103660303c200e003089010700445001880c1312045c8001090045040c50035886003509001e00b80d4076503a114109004150b1000c001650f030003090381a240794130b0800c15817040804c240c00134075040c95081801140b14501c112000c000c140140035040c0c070365941000a841d0541d01522a82d50300c1c0d4060316806402c00c594a108490318403c40d4525407845d4842e0f000782403950002400d00042264550325091059801c0f2000328104070145040c039a0b590700140da40f0704022244000c5102907000340b00d0418009040344481241300d4840c11040080c1043c00c4c44c0030000b0300500b200040008041060350182c5100740c14491554840030200130605510801d12100c000d400c000b9003035240e84280c01808560b0700c07a00042801c540c2d01c600c0b603044404150007114100c2c0d96252000d5100d9011500c20260b030030142440d0841d07119040110fa031114a42c0001b0103400d00c0712a00070140c0c00d040450b91040344202c405126503820380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 722308408 1250 722307158 722307193
    0xe3c01140613020f1902070f03050109060b09070c11010e0d0602030f070206040203061302150c0c010e0609060d240e0405060709030c0509181e0709020301080606090a020408060c0c 79
    0x1e504035680e42c3e07024003030700042911680005001702010300c1120141500c501e506100807007103500440303542c2c0d035035082c1904200d420f01030180e41d2102118000b40a01e02624080c10b11a48100010103038440480d40c0c100c540e0240d0b0b258480300d9809405c90203168810324185009520940b9070361404100340000030300d8140300085c441c0c0726542c09809000c8540340c800e4500207814003400203d03407003240b441c0f00000410014026000c500c0c40c210040032442e0214001510101041c100e041c0500e40402840c80141c4540045850001d20007000081080700c2d500300088441c041d0121403101941050002000d6582400a5021358014410750381d0715111031005540707203d414480103185640c012400c200600e00748101d41e40c025002e032040d81500305a415010705120f19034520001c070300c0304014040b12400042111501070303c036005046155504288183e5941c0c600104568803440050307002034007856140d01a2402466401704030349003400e0a2146590a801c4044007440701d1007106501c0303c2c241c142 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 722309658 1250 722308408 722308417
    0xc04060206062b06091703011e0b0a0e1c08040302100302130b07050f0601030c14040203041a04030908070e01051302190e01020c0d0b0702010e3c0114061302 69
    0x5510200c2680c3c86680c1005003c4504103410b8401da03641e481c4603000708080c240001881c14050f01826925030400e003100b018045d4154034000c00d01100081880f5004543c81140e440e4501814004404c0031118002500145122514044200c81c02980d400b04540c0c1005401500d10840fa81d6074610a5078400700c080b4080c5010983d480d800580e01080003460301801420314500407001d58283c8504801e5079854410300303074000c844a01a03100d04004806402e040b12600210031501503256040c580c88503040586032030609a080c400c5900801d04050040d8074020003499200e0a035000304d030391000324406440c001d00c14580941041c1441034000c0b01944226500711a140c512071000e010035103800c5481c460440c0c4000d05610801c1c0802009681e40d14015075841e2042050a000f03281c000c0c0001c1c25140e03104c80d40c44060b0301188186180240c0e05d08024071b400300302e40c0c1d0403a006900401061020520210f580d03200d501c0c010b500d04510b030103103401a210300c00030b5920400d40544800000101c0c800d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 722310908 1250 722309658 722309689
    0x1a07050309060d020912070e01090b0609100c050706021b12032209140402030f031306050703020a1a06030f0d05120a0207060e06040605220201180e0c0406020606 71
    0x2044008410b240c9200a4986032801c1e0350018100314404002c1032580158907422052540031002c00c11103400f0312082e41d40945441001030025000c1c07080460382c28050f500c440761050200e5028003090342e10581007000016001400c0343d4880395103080107922500545241c003000c40030040c91400c582860008031703440360300d00c01c0118a030141004803c0c3c0354044c40c40c440030040c4805000041d0030080d42c0501c1a0f0404580081e40031810188101440c204801b003545040350010b10050681c0d04001d540d800446209080166841c000c5280407424006000e50013072424242c44c4c0d112201109038158075102c1e110a071304446000a040b0740c17159941120002c2c560000341c080080b01a00f50742c4c11a16078214600b040054180381c1c155a6507030a86a40c6400c4684d941d2050b010441072004601a86802040800484c211852880c1c40d02504a8034050041d043c0030f441c1c036a400403180062500310091080b0f4064410604014200b014950302a108020052041c58007103402880c201d50f0440c0c9201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 722312158 1250 722310908 722310913
    0x642050a051302180904031805060a0f03050a0e010c1107090b0913060f02070c1403010603051c0903050703060b090f10050d08090d030906020f0c09010603150807030f140d080f1308040308041a0705 86
    0x130040341240a408000d00700d00c44951105c0d41520030443800d01420880001603110940300016040e20f15240c50095448508164109010311005448820f501600311b2844480300011201c0341c24a07101030310040440051142c8001503510620072070340d0320482600c06030441000c2110341c08082500340c81c21130000ac1c2c01c540141511619444485c0350001541d0294201010420366a0321502c1c140000f0303034002d0b84d480c0c0e2a54440001881c00240c09580514140c801c01c0040c05d02c0c001502000ca124002d040c0540d00048254007408542c8054600021004105d42414040c40c81c0c000c2c402c010354070a403005031141290361209000c010450941207040940950426032825104030f010700045951008441c00b0f100c008501041c1c2441f01c4000b560050424640c8441c503841e061280f9541d07910040181c0d0402883c0d41007072540650710b1500401607100640060700c4510f010007410448480050850400160000070014404c1c003800446400c0307901240c23400004061507801d8480c94400801c00e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 722313408 1250 722312158 722312177
    0x30e16091a13050906060a0b030a0b0103020c0d11010b01030e150402040603050d181d041412040303030509190f0642050a051302180904031805060a 65
    0x12140c07a8400c60011030301c240c81c10000d0803560041070744030403820080c01c030345030700e407400c02c54005010044290841c0054604545241c501040ca91050002408903500e01e603c40d0044550fa82c440e405450111040030191031820110700b1001d0180d414101d0189440e500707281d503a80a0390300078410030203003c00d03c2d0b01810541c0505c20a54035844002401242d0103540c448020001c00c00030804075030103800e0354032056080c03100d82510280c200c849602c050480100c24035086036500c00c2005103078110740d100d100b208080015546d0f450070702e00d80300c411138540300000c07800106040d81608141c0c05640b40505545050045d0780010740308216203c07014025a03040c002890006a0980c40114841d401c0c180810211a202d001e44c049040201c0f80710f0042241c4000102d0a42007015110b0000c20045600180c060b10308000700e081d00e805038030110788069021407840c840f511400b0000d1303860301008040c02980d29081c98050515010382c5941c550b031119202c404175080c00c01404550004a00e40c90302c03501e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 722314658 1250 722313408 722313419
    0x10e0d0201050d09081209100501031707060f05070201061e0b09090703060801110705100606021b01110a0c080f01020c0309090405011b050c1501050622030b0c0a030e16 74
    0x1540c4001000c044007a40d1310307202c10114104c0000b4040b40020340c22480b1980c104540b0710b91030b20000780ea84880b010710b0203004100041e4074801748130348a4a04511241c0364406400c140c001010490301001e400d90400040002d401d5065100b0402d451445035000c9403e102041410710200050290160105040002903843d00c0e002e20343d150702034191320380440c245840e03034041c90a644122055200703c4402040a204104040c41100c03071000c1c140303404100a51030158001c1d5509980d0b9000449000030110f840d4059100390000c03080e04050100325010b082d82d0b45030903100f15010348921041e600458420b030910030018000c031900d201c603540043d41004420350070084a62401b038030494081d0746c0c1c0c000380d01c0800920b210383c1003640055201c1320384640c1c421708694108404440c136000783c5081178005024030740d02d000903500702600108138009080d500e20850740c4d4100240d00080d00556000c0c041007034410b0090b006103140300065905000380004094203907565503d138100410760740043d4030305114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 722315908 1250 722314658 722314667
    0x603021603082205010b010f111b04091e11030d091404020403120c03120618090809030f0d03110702010509130219080a0507050f03010308131809020906010e0d0201 72
    0xc100140b580c3c3c42a60034205020070b03a44080b100400c403401e944a6001550039030300305d5140140d0f03031010704250092400b02034071103450b00540810503610503010303940ea14180e110395201c0c0320015031188204c46010748031085440c5085d1300c0bd00403030719401e841d1020f07030540c140818188090350044c0ca4091200e41040703408400104070b103a0680d003090f401d00000010803079209407044025020b448403c8000341500f00180100640c2000c48519800c091040040f55550418240200301c000c100194118292030309040600c910907400d64940b050074243e00d082080407840301c0100b10140c4040041c00010890383d0030300d000b4640040d011820030710510360a802e03c052080080030340040014507114040401c0710301302404034120400500040c081140e01c4c006881025001100e07401d159041040b00c40510381c140c48140001440a840841c441416404054401c005025410240c0c0c0e400c2c811151060010300d00c10f04182d205244510119140d03501505036085001c1000d410f10a18901c2ca400545 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 722317158 1250 722315908 722315911
    0xb0f040201020a06111e0c07030212030d060605030906100e04020d0212120c060c04030b040f1103031c141909020609090109140a0203100306050c0c070b0a0306060302160308 76
    0xe0542c001d00440d100013407154890207516465507890340e038403200d9448148400071451044001c0f66401003140f10326a900000c0c00380d0403a43d0444104070304143c590342c40c03801d40c082c0207290400c050a110000c0354030b81c0c104c4081c51003030b4000c004942650b51040c140c40709555051140500b20300010020070054102482c10b07040c0f10380060700e00d420410321070303001a00e44141d40680f00c0c050400801c440d01e101c1c4050024541101000403000e003060700f96101c00854000c080c000030319601c4100e84170405c1061041d680020044000e0035261220944003c010010301e07000c03a00d1501602e041e2002548262000215000b018640400c003460101912558002c05030300c1c50981e1300ca8010305c114400750740c0d01000701d4040c0c032500101140b411003040346d101d03d82d0030140840c2d40042c0180200601c4030400700d01c040440e42c00041c0030609840e01c81d810a002d1291b880e14040d0790040982c0800c0c01035160000700b0760240c6558080207a1680d9000807400c81c01003c0c495102081c40c3e003455000f080c440c0300e805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 722318408 1250 722317158 722317163
    0xb1c0605150a2001020414030604110609030703050a0f0b012715180e0f0a030516060b040c020d14070312050615070b01030303060611060f150301020a1d0604030b0f04 73
    0x4100c075000108900514038103d003940406607400290511083d05220504032803120154020416070600350b0f0340e100c07000250840c5500941c0c0100d10132029079401c1082c0c4000307503000400c1d540b001810341440c01c01038800403c1600c6030604040001200000b143c1004060700c0d4100d00d00486200e90103400000e403a420401400c008452900490310760b00c44442d82801407030103c0c00045a10382c0e2800c0509040c9510070203001501f01d003103802d0110382c0210407601580c80817202049044254036111005121542ca0300b40c0140c82d22404111541e000a0040e003c04525190610038070141c4004500c40e01c01c00000038009281848211512401908103d170000d4000706450b0311050741500161003a00300101c1601d0344100f0310f004100741505480307030801904c03a500e480340b07032100ba81507a81e80c2e885001c0c00080518152200251a0442d180f4071041d40c0c0c3c10003002503680c1c1c5500c2000900040102044c83c0b40031713030141400a458034280c000c440450742d008055903081c2d950796101e02c014503c018404d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 722319658 1250 722318408 722318417
    0xb1f0e09041415040b0702010501060f05070302070e01170f071203050c0f1204210305071101120204090606110a03080609040503070b0403080906061503240405010b1c0605150a 77
    0x25400154001c1c40124501803180c150820f00b850300e8240128208800340c84041564940b000600c803890b030090450405100a080c001d554250601c4d0032490042194003481882e00507600205201e80aa610618030034170741c0d41242c40400035a48019112181481001166003070300300e21100080c005e5014000030024030040d0360000110600c00380c100340e10b0701d5140d100d2000019040c41300000e10369005081d10b11035003100110304003070380d0042d0641c40740001c0602107186185400c0c40b1a8070590340107260700d01c86d180554603269a03210303071000b420300b90123900301150522103d0b8105207000120b0b08201d0340c041d039911440740c03031340300038001e00210141003502c50340000c10251003c510307030707039801d03800f542c0300703a0310640d0030b01d0b00f5100d4a05080f0050000c41c4500035030760315151040d07000410317a500044d0808058121801613425603c11510000549811500304000041c034090041e0180030f9400c4100d424408420380d10b020780f41110070a0040c1540816a00d02e54003102d84440040c201014003401c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 722320908 1250 722319658 722319683
    0xb090112050a0606140901060c0210110c03011506030c050f0d02091201020a091409060307031b180203070f0c0b0a0f021630080a150e0108010b1f0e0904 67
    0x20f82c0002d8882581208544107042960180303507003070540b05180109150300d4041400ba19650000d1813404144c81040200429818030003c3c0943c24003008140400050081042101d40303403491018607014820340010928000e214851207004008652140810005003407512002002c6c1c400250011414190003040d07844600b486290300344010041d644031515020741d800d1500301c150050b16a09025107002d05109000e11100752030001d9010b0580c0e500c2003001c032180340700b000a05007661040e841004004444e00040f10740300302d00d60095000e0700f400d41e03425065903020441a10070305005000146640201d10020300c0288282e44120f41002400d90054076107546400c1c43d55020800400556100d03965415206400a0381c0c92100302ca41442d066a04d1070034040c4d14080d1080c40e0050110240c203445001d80c01003c52010b1408018205c4050300340070551b100d54025000300030a00e001d6000d031044030322104a40303040100104800d492590342c218200b000006002c0e1001d405801140c80b1800942e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 722322158 1250 722320908 722320913
    0x308070f0804030c23060a0f031e0914061e060102030d020408012a050403061d0a081c060b09060d0e011e050c070230030307210b090112050a 62
    0xc0208000c6002d04002140302d420124205040c1d11041d00c211001c1e42610744c105e0b2103031120810b0b04e1626015052110328104800c03410340203000d40c0c0c0c1c0d52460000660513404da203040c43d50f0114001a00030000303000f00009034100340b50703600400e65180e03064250002200100b190b08040450740f03e03006205a034100440320403041d040c1d8000fa080b0000d00d035100c2d1860005007004404004803410340504012681403003200182c910b01c41e9020103000a038580546040302e41d00380b43c00c44901c89411040f2000a01c20b0300b00035a250f04a00d0034507180c2c043d1201050054643c41c01443c041e14001c003c1140707000c17000070400017694414101c9100240c0c488284000820086c440c0380c0c00305c0d001f07020f05801000320062400c101c1d4002828040c66001c184840000b6842d40204030b05455280040009294840b14401c3c00b644548141e1460034800001045000d07503200c118503201e00a00d034041181c0044d02e20b021710584175011a02900300c6061001004400740709030300e541e40d40d4010405d60301c0030f4000c0e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 722323408 1250 722322158 722322173
    0x405070806010914060117010519030b040804031407050612180a030806010e061305040e0f0f0c09060409150b040f060906061707050307080c12040f050d05040b040308070f 75
    0x9038800c1e00040c0d035592046513115440118141d01c070000346400d44154070303c038034001d03202501070007581e00030030300584150966040034101e84041c5070428600c003e24649403a1103a8581d010340021034501c80103110101d0b4804002403a0029a08000c0001e414140303070b071650788004000141284091521068407031a00c050030721541c04014042e42d40c0c60b4030380c81c20034000f6104200300320304103000f242c0402800c8017011140202405136101202e001c687c50241054052514030b61040c003109500520a1503140100001010300b039401d01501d210300f013644c5d49810402121040700e4007421114003166031003041103041d40200c0207040000c0000a40582c640786000031150190846040075503140000d00003a6080b8054545240c400088280b00d8500107130b00409a0101a2401041c0300990000c104a20064400e480300440280d0880a041c07a0604041d0003541d082003040c0e5881c06a0000f03007201070701c036108a6044d0b5004008051806195503251070043d8040c82e03064604c80c401040980018014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 722324658 1250 722323408 722323411
    0x20a030e0d02180f07090605070510020a0e09090a0c09020c0d030903020304080a050601170d0f03090c0306020d140f1012080d0e060106090b040e010e06030106050918011407050301030b0405070806 86
    0x1020214040d9242028014200e550640c1200c41484420b101d00c10020700000bc0c020020300ca03a16002d81c5920071a041a1040150340200c903520080f414100207441a0018503000c4039806421414005c650b0b0711040c01c01c80c4680ca601128a030000e1499554850181d04102c140922a20499282c1540c1d0040c10f03082c0b0300312035011140c9070040c000420244081104c102d51340040c90001d05503080c82020041c0c40f024105500c05c1c00d060301c03007a0680901507500d180c58001c41e00328000759601d00455504400905d60381c840790b0301c0c0c862004003041140c1c42d201740c030f1803044480201c400381c444c0c14004142c1122407486021103a0841c20000e45500d2190742c000c1d0061250701d4002400294100380028020b094240c002c41c01c242000e1008000890010303951a045823069000580f90b40c4999001c6030140c500d980025401c02264010302c0480520710f81c1c0550b0301c0e020800204000c1c070b42022074840b0550240d035640d0000d00d051006001150441e44010340044c440d008a40c070b12a80d6000e06400c1030300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 722325908 1250 722324658 722324671
    0x60307150c050c0f09010608101802071b050f0f03031312150c1202250b0a0b0f03100b0310060308030717130809010c021519020a030e0d0218 62
    0x101000000200942006480e014643c12160101c1c0b001c10b030341c0480e03024007052142c0c400700134440300031032062030010f191080a0f00d40440c51003a040d4020013408040c1d0310006044448a40030b40285c0e0107400c0c0b175841d103029103070001c01100440d4819805c2084980410007800c2e07150104001504640b9260365400000300041a500d00c3c1510560800359042d024084034681458101029240055031080401030303500f10300c900040e102c1c0c01060007002103617140d41c40705401e411411540401c0c00154006107214283d500c0080c070440b0030403028401d00b420a6034100b60164404000b00d118200681c0011621400c094221742e903c0d22002c0880d01618925803069415010010520000561104810300d00c0c0c0c00e40d40c10200740e810050421000c035800d07040007415456001c110283d0980c802c0700d40001e020340041609402c88007202a2022961000d404590320f8004140c224600900101d080d0304466010f80f1111030820000301403000c0740052003022680510301880781e120b03048458503698019030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 722327158 1250 722325908 722325917
    0x1b03040c0504050609220f0b070210050711060103061a100e040c052110080d18050108040b04080904090204020a051b070b1b010b03030c1c0513030b06030715 69
    0x10710742401c1c403003100c0010340361a014a40b01402c10030101e04078219041003486109a040e51003115090107419040092802003190754118140304d200b540c005942180084410401c011a450b58102601e0b0b40e14480d0200c156900010010408200c50b94450520f20300394190007020048990700052204810488070030100c3c3d407100300428103040a120f404900754050500500d0410074400c816249174400c04c201c48a4402301d030000384080040348440008280d00000c81e205c0c04812a00980301c29002c05050716803031300c001c0c1c000449610420400d80205c0c1c0040020078607448948808a0701e500034038106400540768021140142c403140300814902400da0384044c1c03210850b400380016118903050344501c603448002c0c10b02c0800148400c95010300600303c9290020601e0007080c9015040d03130200194140008180c10311240d0011a0869140c4660345555104214130391080d146800f80269045440142040610000e200d061040e80c1004d401011035400c159031702c0d44410512008008900091f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 722328408 1250 722327158 722327183
    0x1060e010c1e1a09010f060308030103080a20010c11011b0c0f0c060905090901090809211c2304090f02070209010902270f010813120503100803130501081b0304 70
    0xc2130a11600c00321451000303082c003900d0718580303032030016020602020b480c041001504c0c0201901911030120110980400c242810a2100c0c03940d008240039041c2c9400319a44400300d844001042c81013242c00d2481e50805407001503410b60403110403c0c17400c002c440302204041d80e800402c526151100081407e40d991010309424040ae10000304c80107451100c0136814010402c000526940a41d0a4800b041d140322038201d0441851340e000e540030060440b1207005d4002c1c1d82d0101c10041c040c0b003070228101c1d1120441500c0d924022500d844465694494a01c1c00b0311084c081018240c201d4003240034810800341c2028010b0b00016034081003070b80008180da9000076140e040101d469800580c0029600c41001e441003000d000c40c04102000640c03a040000c400000341d210700c0248641c4004a030070040b075000602c8207400203003542c1d109449040001003203190000301544000101c4200d5410075481c0e0701c0b518640001580c20f40740260036401d036003010041074000c10f003007000030314804c80c061444094107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 722329658 1250 722328408 722328421
    0x3070501020315011805040b010e0d0b0403030e06010e04023d2003090603092b1d0105070209090316061b05090904080c0a08030a02090901060e010c1e1a 67
    0x4070100b00704080d06120760745c540c81019101c216988011100c0940f00461004015001203462103c0c0160355640004000c4004003845090b000c80c91080e8404e450400100926120680d0b43d0030003442803d010307646000010703005042006215800c0402e050002d14019090307003800000240408501c041403080b9180360600c940d00c0420980840c01003003c1c480c880381450002c03070312072240b4401a80122304c004041034040c0380030000c541700a0b14001060300107194903240c003041030442e044000d002030301c40300707600750075000c810f4800b140000305071243d034a00b090903824040035150040c000c0b0740c1030009010045820f00c0d0008105400c030700c01c41000440300300071104001d901e04030010341401c003c0280130490b00c43d04c1d0484100d401640180300d0903100d4103036100880c0361250184005010301c00200c1070100112a41e000740c022500c08036001b000b942e813100d408507003e4903130800482c0060761f02c4c0e070403c0214881100350b0801040c1401d0f4250614080d0712400f47c6d0800807291003150f910344e40c040190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 722330908 1250 722329658 722329681
    0x403080402090c1c0509070b0406050d050c0f070609050109120905031005060102061f05040c08040203010c0f0e01050703180308120c070c031101031508010c11150f090f030705010203 80
    0x1840b044000d040c9007028813488600e01c1c210080d480d94006241d56601141c0c5005c81002818004c1810346440ca0361291140c10041c084c1c1c2180441038039841c00d05c408070f09207030400400e5030051071044038032504101507500c40c1405080b242d4001e07a1903550301d0b206400403030b42911a00d0070b5004192034003190036181070181442c01c0b4401030503010f0304d031804043c080755070307404508541c03c98944070886890884020300c2e9522200301d0350003141d2203882c00d19103515a81c1c010708a14810340c000c40003081480c0782450156961060b500c0640700061280106280a40c0a5006410180e00a141000440c5141415000142a03580043c4d40c20100842c644401c154800c20b065401001c00c2400c90412070350383d50366410001d481c04010000c1d00e1003004507105234030079401901090a502c445c070108035980c100150003094000d89d0640041e03414554541d580100051324005030700c0c8445880c040365600c42400c80060400b502c000014020108442820744e4200050000d26001e41d000580d28104840120f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 722332158 1250 722330908 722330911
    0xf0e060c07030b160c020907200318011b1511070209040501050901230105150904051f120f0206030709031704060e0a03030804061a0402040f08060c030609011203050f03040308040209 80
    0x130801004100000060b02d621440030f810101c6414084d6021411165080b03103100c3e082901602480080f038a02e0301f10401c915a1695a01d007030b265110321501c6a6460444946005030140140c40c9424204002c400541d00c040501c4020180050505080790b0001c0d0601c1803d039402e641c070703039120b90500440034001e11845041e50004446540b20303d0007403c0d50b6001c070105203c0c4912174001031f0303165101c2100d028101e64920a000340100224900700c404c9410203e070300c410110821242c0100811b1101c422a0180101500032280f04a04100d035070800069030300c01052030381009106400040081c01500d0001140c04c005d0000320b46031820a08000c0090503c034540ca40304a045920410109800c81d0713405801070380200002c101204c0c2080c1050161004040040d0014400500001c0700d00228460500b5101c2d80d1080d02c859440b0089241d065010a80d03840d07610802d45001001041151801070300054070a0400c7c6003010103800310081f1603081244d041e4003048240342000114030744401c00c1c0b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 722333408 1250 722332158 722332201
    0x30a060504060e0102090901060e0307150809070e1506090613170606030a0f080904060f06050a0e0a030507050118091103091015060e0609090408040f0b0a0f0e060c07030b 75
    0x5c40c2007114540014003412018403c00052092001328009292814418072002d80356103944d1358039003600d056009288110840703210406009402021070041412140342e405280c0f10800c1c0d1000c40344da002001100d03480890355540c042405c002050a59000d40070510041c0983e01c215500200301008550800000034010b61090b0041c501c8440040c02d01415911500d0b049820f00f0745070b94240001c10000d000c80e4112000c20b1722114800107005078003c00a00e0704070140d0780c42c458100342050038411000c60a0000401c6030b0484001800154440c107940402ccc1c41b011100007405980d90f03100902141e1a00074480c4880d40004204a0003001c20000b042224201c01e1080060841c002a1000b0f105030724000e00c2c0410041522558444d650181034440b0070900401003030040c2010b181012240c0d00c188100920680030b00d0300080c6001c810340540e41c0515241c0c444100b000c448550403524260f12019007139002e0b005000307070b60012204100c444043c5100d0fa0761045d040c200340130041048900205034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 722334658 1250 722333408 722333411
    0x31f0204240215091902030a02090a02090f09040206030609090709060f030201142b02040b03100302100203031006140412060c020105100b070b2206060f0e090c0d020f030a060504060e01 81
    0x140045468005a081d805d07450f40340200c04040c0c00362002a003480209000a94402840340900151007010350080480c8138007120006c1030001c1000a000b0886021100654411020700000e907090034100f450992003054181502c42c0700e40c54011040403580190421403001c041040305004550300000900e800600c14211242407804103038801c2508460725900d500309a44e035040c145480582074042e036005e0031440010680360315041d19280003260b0300b0320040c1e11901c01104081891400441103030700603002c103210a01e249040c4007081c9c854007070100a1100442e8100800a405c440301c10391080d0300d5204030702c04a440b90341c000b07000313095070301c00381081d8802002070342c08001802544007140d01e4250b105240884a50b1040c0484001d1011a41c00c44522004240f04104201881d444007054840404600040e01d494203841441a182150b45035000e60190071071040524001c1000601c043c4010702c0400b00101d20008a410011200b004881c207a0b2100144401c00080780103403442c101a0400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 722335908 1250 722334658 722334661
    0x6050d150c0318060c020f15160e03030a110a120f080702030f270a030b090d0305040c0509091006080309130c020d120f020301230f031f0204240215 65
    0x20466180d848010f0010400c0340c1ea0304e80911300900a0021540308280303102a2400130560f8440164803640440c0c2d001c032021071307100000400b036006800300c0307004110243c011820842440030540d00340740b1051441ea4288160001680040c6041d03020448950050755400c0d080c0c0fa04c03c03009000c00714007400c0d074407d40d00140001040e03101024191105188007014002d200c1d42e0b41141c010050026010b103641001791500c021050108448201d8080c524200464000d00e050001c100e0803140d055400074418482c141c0104001c2c5044000c0a030411035540a48080400305d1049000700c581551105000ba040419290310520300260814040108003c0a00c601d008890000b511080b81c5040801402401c0c4401d031008440ca512411303142c402030400b1581e0356141c5869202c00044d0300c000f0814900f040780b03d006241804070f01e040d070031071014000b4040000528800e1a21031100110407160725420300c0005410242c40ca85400380612950844410300000c440090612804412078498400540c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 722337158 1250 722335908 722335931
    0xa050919060813060f111210120b0703020903010f060906120b0406020307020a0c0605070611120c181309020f120c01050f120708010e0612030304060f06050d150c03 72
    0x9012a42c801101400c3c080064110314224006083d003002989005103044000703800c40f0b058400a0180040185042003c2e83d070710f0041d8506886079020300005019044891000100103c00258000d5032500b005414101c85d54082401c4403154000040d002d030701c1d400104152500c520514011b0a4a401c7c03880d544021600c0d281041040940000c100690010014102500c240080308810350302100803200c60303580e60380040060300800303416a041ea00e40040f45c03460202200807201c880030748a46c0301803240d5644101003019049070b01c200c4007501c4e01001e60b410596695102c202e4a03030483e03200180c06a1030740180420511104c00e00c60180d8106050450b50040020700340c0401242403820030f41e2000ca075101c400350703400b40c4038031120300b00e0300350091008580d00004258160368041015074201d56405082100459400c0340242064000b08003013000300b541c0e0313040303203031341094030340004c14a076a1341c80103d40441649441554103008a0f403050483c40441d01132010200c1d0385103020702014a558 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 722338408 1250 722337158 722337167
    0x606080c010c020616080a080f010b0301060f08090309181005040b06041502100911010f21050a0e1c03180b130203070b1306030e030301060203070f0c08030a05091906 73
    0xd40b40070b44619800724101485040c680908101d090744551260340f50350030b1000180000030300b039843d00c4418080c4800440d07010014401d40c0c1c1242c0c81d583d60307840030b030011a400b619120b1018020031510300003084049500d03140d030004d25002031034614003581e0a1404c00c0881d80c4500c01038106c00e109504001d0307040d140e1341ea4030b8240d078140d4045004190803210010800e900d0000a2007110311158142407071201809010302c019802001d007a02c5030005c100c10240b0480b1600e8045c600900307211030f11162000810010b911059100000d51030000d081030318185894540f0f03007061110464001703014010100c0c0741d0b250050016000070184018048030061f84d0b001140c03c3c0050003003a0300300901d100041076680c00c001d090003d10381d40a540c1e507115141c1c80000351a01c03050060718082810320740001081d4600004490403102c03140c0c040d5061101942e600d0318840346902d401e40c0c100507444004124084140001d0601001c1e98072115504c0c01c0d403005109500d05503141c026028104503c0c10000c0344e421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 722339658 1250 722338408 722338427
    0xe011416272115020702190302010906030f020705100209130b03070302130f1a010e010206040c0e0c12090718090b0c0a0203070b100e0907120809130f090606080c01 72
    0xc11105070380100040b001c0b40d04010b00c01c00041c0c00002003440c200745084440e801007407001d000755801612400c000706e040c00c40c2c2c4c2c80f40c4402030009001800811180d172195201500b2405607003001f5240403943e0f00e60500d007070311001c0d004240560000d2041e07951f02e4140400c661031000341c3c00c18824400d034080021345500c003c3c8006402076240480102d10a00f06600480600e01c8000c01008003602a484500d406119a144680401c200003691f001c00c0d800012014815540300f101005280d040444021014802608140c2c0d580004e0014034040700c040a41144180030006c011704126140c0b0710160b01400305038112140b0280381040060210b403031955616804940209125070791035008004901e107201e203141c044c0803a0040028086940c1024440030100d0345490b40c0c01c4110380380c19140d680c0700c0c456440356450302041c0e04026000110101d0107086050700007030040f4001202d040b84001036800744c07218602da1a6a4140c09010411548180005000c04a0003854075451074400030300300602 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 722340908 1250 722339658 722339669
    0x61d0a060f0617070e04021902070b070c05040905190624030b15060d0c02030c1c08041202070f1502010c0305090706180b0c06100801090f03030e01141627 68
    0x2c400c005a4224040d22030303c0b46840f0041e06c01c5580c1d243c48041c81c1814800701c0f100d81c005010b86100020405001e20640f0300c00364000092464051400040000501d031504040b40d45010310b01d00705600c0c144080106c1c82641c05100c01040b5100420704080308c414441c45030012048031004240003080203040016402865000e01602c070525a20000342c41d0700070b0710122008a07040800c1840303903903408805010700d0650002114071200441600104008068400000051040b000a070110761256020048401240103481c0740648034401c1001c09101350304402409103545a51303100059091262191005081ca020807944c182074405546a104a1251200b040f800030701480419065008034001409002c01e020303a0360709010707040c40d00c450303044515107105d41c18404000b48205041c0030301030585074860705d0911a21101e580541c001c00305440030402c030750350340d000112615030035150f640d0050f9110160610b44580004004080185003100743e408800c02c4800114102c035481d500300190341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 722342158 1250 722340908 722340947
    0x31005030d2a021504090f050402150a0e031c021e0c10030617060f090708060103020105070503070b010323070b0406030e0a05150109050f06031506010201061d0a060f06 74
    0x26480b000503521031401c50080e602c10130580c41d5020075002c0d88014400c80343c002d20300b4804140d46500d29030403140d046601030f40004003130840c14070554032280100301402250808000c02e0042001086c9005144488491003c00c0380060943e0207404105c0300030142c0c0412501030901200d002c0d1a51501120b00030b13540251800e92a25220b94000e40014000d007800e1001155404041580d541d5122400d81da41591b818815002c96420b110208200080c1c80c5481c00500f116461070307004554540c85000b098805000901080c40000c2813529414000c5010b0f03c0241c0c0d05039400c140e40307801d06400380c01401e007940c0000402c002d02070300101a9011641e4900300090380ca103c00c1c50040c1000f090700001461070080c110000c0c54035030200e03c0c10707041e900014403c0001d80d42d00035070150384841c01e444082c1e0551000788015000c081211080f49d00550610001c1000c0c4e545070086802023107250302c4000425010020858040f115108600003800c03182e0b5019080c074944a005482042c1c0f03d100400c211 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 722343408 1250 722342158 722342207
    0x924150822030e0307170c0109060903030503040201080406020c0a05010f0f140f0a020f0d0615030209090f0a0e07060c02030d0e0d080f09150903011401060516060f11031005030d 78
    0x95a050040500600100c0c6c4c4488501c02d08220305070700c4000c541035035400708044a50101780b6034401c41e94401500c0c0c0c1a03d40c1d514585540c5c005550ae80c41c010400c40b8181e07020040c82e01200c01c01d01480180780c6c464800810b02c078000614a07000c0d2940c00724400030051a00c01418140040b41d083c4c04d4001034094160071080e103800400d8800780c8a844046000035400040108a2103c0346d440380080324604038000d2042c004054045041c3d10a480c0101d5010580300301040743c110960400716000484008002080341c010719150f814840c2d20f501c03820214548400030340035401c0c1440031185e5501140707002c58840c07040d0800201458440d075405058143c0220300b01c50040500c01c01c07600b0301c6100403c40b10100290344640072890380001c21440c025400d0003100713140c443c42600c12506035403250316100e041101d00d02da213402e4030803154030594650780c0342d0840c031000c1d030301034030403041c0800d610040e190f076034500702d080300084101035805130780640c0c0801036002d5603992001c070084441c1040c4860302c1c0507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 722344658 1250 722343408 722343437
    0x82a0c06072d140c0a03080403080603070303051b0c09070302090906030a020a170120031e060a06030b0a0b13050a0e0106050d0b27090c1207092415082203 68
    0x3a00400002d941340d8480d66402005142c0c0084031684145e00c60390350010555101e1080c551101d04c94400140410814062014041010107041100e80b8100003124601c0307404600281815400ba0307200d2011903030006007842e05003462501142c0c8800203400504100c1603030390100c0c06420ba28030a42d803e13440164083c0600301c0003034000b04e100c03c0c40d07240c2c200d407000c0200744491010750040ea6189040c0d038604800c1c500c80d040144001d80f0940c001000032024503d0003500360007419444003401e0703100c140b02001180848020000e881070f081c1d051001c2c2da0030350130401405400320b9103800a00500003a2030040102d55400422540a1888207a020951903429004102010100c0311181c2d18208514914400002483d0741a407081da00c140440e14200071810501600e00e401c92401c05040d0050328003400900d0064000e03504e000600340782590044021402d210758250b40f600088071268400000c00005940b00341c02c3d6400c11041c5c100c0d07171250002030032441014000600020b00340180100ca0480c0e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 722345908 1250 722344658 722344697
    0x90b0a05010914281d060f1e06040b0c0a1b080d0c02060705010c030c0f0e010806191206090c0f0e1906091a04110a082a0c06072d 57
    0x4031240b408484e41c5a01d40f2049803070121940c80c1c5503500b01e8021600011201d180c191001d858140010741600e101d2030305440a40c14a226030801e0380e0300318004200008804034280010b0944800c1030300548140c0d041881c00e2400d00910760704c41d42d10103070640b505001141011400b20000358a42c10080340890103840071580f5130280c01400340540d441d0400c0a9480c0380c05800c08240d600080e80d0f80e240768449a40c0c25206442d25412050000c2e0511000071614180308031140c0c4404000703104a203000b80c0d11a40803010780010b01c0c0c1141c00341d44980b0722004105d200c040030400f41c40b1002000e00503d0901446c85030f0b0307200080500010141c20011611020001d40c468800f45c0061003040c003510802d01c0c064118880d0740500c2034002c51411a10381141804001034440104d0035a49a4103143c03194030b40310300000154082034031420509030b403200b1008840c4004000300e82e1542c01410780b40c540070354050008111010309520701c203200000c4e0304a16119081d03010301c1e54101e0600103480024900d0016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 722347158 1250 722345908 722345959
    0x408030a030906151d010b13050919091a1006050a050a0c150905070f08061816090c0809060c1b12040e06030f0d0c11130501090b0a05010914 62
    0x403241c03120000e000c03030118100f100c056176103000c0018051090f6640c0fa0111254415505500341c3c1e426180070074065464521031064101d801c0349600020030784c1420101c001c4400c0c554086441c0d004a141100c1446501000140d01c4240c465040c00036514001000d0801d101c2c0b41c080c0c0c801c1000000d5429121809202c0c581d0515070440d81018002040080d40f00041140ba00c05503500e200300140028200c41c07400310502569151400b500468640290b001c000401c0701c80200c070540501d11035a009082c010701c0300c900a00380d100012403400d02c490030183c5840c170050075030b85460700710b102085000904201250b1742669110703040114020501c8a040c281602e100304850404000a40090411a0720040301c0c0101e40440c16204490400080c0a5413202102c1044011440c440d00b8980800d03400021420074040180c82d903000d10005021050845000b40c000c0c0c00305980d52071034401c103420902103a0300942400c0c2402288282400c60440600000810461007911200d52640310081e40c0306410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 722348408 1250 722347158 722347181
    0x40308060d0b0a20160602070804080102030a29030a0803100918020103060806040b041e08120403020606190b2b020a081b0a0c1407080601140301020408030a030906 72
    0x8541d24288030f074601c0007030040f00d0700845840900003424038500000100300c960400d081010000e42011036510440a5084024161845da01c140400106841c013030006500ca0001c644000038240309030002c0b0a492000c81c1080031880c1c0809900d0445510001820856030380c00484142c1c03240d42d050400c20140305c2c2034000075403107030a000e0448000483c0d03c44440100e80f00340c03018804135403034101aa54800c0e007114090100d1010310003040200b460241651130080c074160001d070000509413070b1081d8541c050a0300500d4020684200414980e05200d01a04190304480c15800380d0180e0202040f41485401010084040014802c442d14401100220030280440881d0a510301d8a07405e10001e401829214011401400005860b0a11350245182e54040003550604290109604a1f800d60030707018200c03400c3c0d480135600049007004216002c000c1016600500c401d60400744245501c4125031001402a8014002072100d600044260f031000b0445182c00a0000c4d094104030f0084d04001106 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 722349658 1250 722348408 722348423
    0x310110412150c02030f04170a02092a040b07140a0b0f0a0f0603201513080f0a0201021c020a120306231c031817060a02090306040308060d 61
    0x4400c10008240d0200e8000101000704280030a034a03091345c40e44514805403010300b42c2000140070a2a0030740307040c1c0c2200c01203000c0319080001d56000c80c500080955580b05560320382051420780b910100e503000340030302ca1280c0d030a0805141072603100b0309010300314008010039014000942642d0f02044500e42007600014569401e041004081c0b02117142039038480d40c080d00b40051070034018014040e07501100e9000014110003072071008054001c3e166445010340c0003004960a03000c2100c0500039140c07941449031600380b0649031a881c18540361110b45640103e810001861000d03070380125030340001c10b400840c840c1c002000071030308a00307040355140c1c020809400c1c5200c511150341d060b4402400c4c2d440c00f82600a01400301c000b030442c0e403103040c0c07002c942c02641103c5a0038000d288a00f40e14900344642008a92203000301094003420115411401880d080e1845114000c001088040d0300000c2c40311045161030413603000b00c5e85440c8010000350501c1400300200e000c03911100079121045410584 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 722350908 1250 722349658 722349689
    0xa0308090f3607020601050102030a0323010915140904060e0a12030606080105181602010b0406240c110603040215070b16050406020c0f040b0616020112050603101104 73
    0x740101c104030b401e510140c80c4040c440090305a40c0002000c906070307801600210700f02020741c0003c40151452511110221400c0ca0070b8501e4504171030840c0d8084d1030340d90004107040720303545c8804001d01c85690184201a803490b06404198031225086a0419004040405c05c0b08220320110700e4030100c00d10061111100c0c4070502d142c207526038021010755070240d54000940c0d0b81c80003005840b6081c040551601c40e42c120100e443c0120ba0380300346500d04014000440e514484c2e200280442c0c86d168429020517590040100b04003d002e103078000c11110031f06003180828959100c0380c08818014100c00c2c002c1d6400400702d400d564401490000d20b28405000d40d07a109040e00d007440c22140305684801011003245940701025002d41c0c02e0381c05503141c590040c00c1507142d030720401c801c4001e4003411036000743e030b290380020b100e80302e0000411035103461410b0401d0100380f500c00140840ba864044001d900d25141c1400207664000c10900308204508102141e00a51040038004c0340c031480d444102c88454010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 722352158 1250 722350908 722350969
    0x25121103030a0c0c05010e01050d0f0e0a030c1e0309030b130204090614071e030b0a08060c0316020318130f0203100611061303051606020a05180a0308090f 68
    0x2100c0f035118420348039889080d0342e450054490040c4040c2d46c0e408541c060100340c03000507607030344000c40f4075004075800300d0180c001824550038806d4240b0280c0000d8014001c1000744090510720380c0b405014150525810000d90314003c101c2030700c6000c01000b0403d4a0040340e24180e000da600d040154004008001c41c01a0745406c030000d06c03030480002c0022940e1000106170502420344200005500030b80d40107040580c1408030000d103004031210364445031032103010420300303000c0158a00c41c0a004c5840d0341d4908060041d6400e500144080c40c08641c000c200c8200b450640c6400f922080c0d206450030302c00e0344007084c01c55015140c80340003480043e2020040000303903d060f81d010b60450f24642c03586140c02402c2618551502c2c41241c1c1c61000314080e141c0f2000081c41400182081c1000034a41081200148c4d1800c081e40d00c01800301000460102d50f21585180301030355400190030441d801072003e480c40d42d03001c0e91800381c1c1c2c03421031268032220300040407030712107540e8003525545810506e40c00c1c50300c00c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 722353408 1250 722352158 722352167
    0xc1b060a0207060e1b040b120d02030306150408100f0219020313060c0f0807020d0615050901060c0525091803030608060f01140105040302040c0206060325121103030a 73
    0x10070050303d440c0e0038007400984c8607901141041c40d2940e884207000c0d0f521440014000075200c880c5400f03808c030b02c0250b800840c07484240701500c186000d541c0a5035403424140f04002890116030f40d101107041c400c20003040207080c0001d4a01c00001c02c1c0740003103101c1e43c460364001c000380140f514512590020800b0414625800f00040580d40c1864464500e4280c503003d0440e641c6108060040ca402e001c0f50000c03002c01e1415000e081d522f40b008120741c00e141d00c00d80d900c0782642c0550146550303c0c840380005200c5898505080340c054052880c0803031f01c0311842e489039030350341048071421288491500f060203260350007a140c0300040c0c40122000d005600300382e89200042c4000c0c020aa0000e0704e011404148103c000c1021409045d82c144c00450320b074200700c140340f030405000411034144070f4200000001612136008070072011031560081c7c01546064820705040103070340c440515a010400110080544c41000b030740003500d150340a84464980e0900e8180803c024156015074540310100e541c001540d8070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 722354658 1250 722353408 722353417
    0x26030132030a051f09080403200a0e0103020102060f0609070305060a17030306040507020102121f090c05031e011d100305010e071e0e01060e03011e0f050f010e0c1b060a02 75
    0x2112064480c1381a803a18040131569813080c0140742d40e00400c001c0002c91403003079502c0d1030f40f20028030080301d0140200c0040c07500b0b052035101c9022174a1102c010001d660301800bc0503030044217a145143c1514011000803080000101805c003816620710201e13009072102c8540d000681400701c04881c5447d048068190f9a400445031144298108000102030368418002d4546c3c0100503130310b0b04102c0c5c6a00c41205560041c487c114900c1a1507e1030003e110907a600501860100d251035050741d90a181c500030304102c424403040b25030b115500c001084000103010748414980e030704192030181e544a4011040b00488580d1010302207601f09402510928404519902150540303510003402d910b40302802540085a44111800412407030010050179002c4d2006540c030001c000c0002685503441c88480180300280178035040c0a560f0f40740c54501d0741e0802d1140b15000000c6020b025203070b40c036046034599040c0b0000c5c070640400d4004035904625042c07034212900b00850302c1090b06d42c1c51500c120050003e402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 722355908 1250 722354658 722354683
    0x1005190302030f0a0b04080a120f0f0507180902070f140609150f0106032f090a050613050f031e0a1a0702060105040c050d050426030132030a05 63
    0x340921070703043d0810001e0b00300405988590b10300c51554468031258841c4e002000c0f05000e0007082d01c04452400001c3c4100394180f0f2040d00700103991034940380448101d440040581c0d0900280300c815403500303900c45441c0011580c107000090703600c0b030141c50244072030380310054000c2211440450f204603111003c1050307071203801920100d800c1003c10440b00d00e201c44060341e000d070100c10300c0c01c0180201803007504480d410740c03156070011200030a040c541c20b0400e640d500c80c1601155011032105810f10f0b25a80c010014002211047d04240c00b4240381182d044441c42440c4c442c0c0d05603031020035103460034403440710180c802c2640324410710f824145142d2a910403074800c41301d003040103000c2d44010060720703221801a0341036401481039030300300018800104845d200010030f001061141580c0c6028900071903100d644564a0f607c0c1011424454030345032800504404075018081c00103105056010b0004090000b001072120703259844280c1e081910351400b07a54603054000c00c59200c0a000001807504003590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 722357158 1250 722355908 722355913
    0x405070602121201150c0807120e03030f09061b0703060e0d0302030103240e0313080d0302040b03070c0807060603050303101a0901030f060f15020f0102071505100519030203 76
    0x30811682c1406601c00c0006030300b81d4030007a10042c070150720b8440c4911180c0103181402d400c0001d103500da50000c1d4001a4044900300d094691035000039502c900c100103e08401d90040d030800c494041c00010034000c0c000c01e140110004203001c180c0c40c84990400091240c9403040c1c0781025100c1c100503000e48110f517041c0000e4401e150900c203000c4d12a200f140e040301d400c111380924147d9404403810700094050140a92141c40b0305050030200c3c0188020100e454810410b003c004e46070121803400c10807040c94000034148107020420118032094200c80c0c0c468818941400452502c1c0f40c00002402030103005429146442804001c00800000441c020f222070461182d2140c0e4901400100f45004480741e80341003c01d003c2d90480354000e4200907a00a0030b41804950b1a8540e00084d5a40d06594802c05498141e6845a950759805001141005440ea002541340c141140c44a9008403815007408014555510019105580c014412400ba2070700401d1030807445843d85030102d003c0c55900080c1e02c0390 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 722358408 1250 722357158 722357173
    0x4060b0d0b0a0b0d020c250302010206010503010e0c011107030b10031401050c0f0c0c090708041403040602030406050903030c0a0c0f2304150e07180b03090709020d060302090405070602 81
    0x918000b9034040485510302000da1038107401d4400c25001c0d400c8070490700b810b4802c02e5024050301021203d0105481101400752070f206140d80002490070703c1c10b90000303020343d24041e0100340f0389501296055100d007003800c0c103980500410000350320380740031680040c00350024582032100d044160810300b03040724041e0007241c9400002c004a04d080f29429101c2c1c003038070300041210098040e44200174107102c080250948041c541e0384c1010503801c00040700d09000080440c0200302c100008005202e0741e00191078001e600307242c109200656a0710540c024902880400b1602e055140e904204490364510b00905441c420b08061410700c0710034003580200e411449804034040744410701c0c810483d1000c00c0d00c4001001084406080c440141898107001098000180c1f000c11030810040280b4001c50f815510a00c0e0400741528100481d4003c1d0000e00d030000041060080c0440c0000c0e06c80203581440e000140c0c0c40c41d0701d0301400000e000da41c0c0020341018841d01007100b4488040f490030100c50140d02503d988 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 722359658 1250 722358408 722358431
    0x10b030708151f05090904050a030807080f070e060f0a0f09051206011e051c02030105071b06051909110f0105031003060f1e0b0a080c030a080f070204060b0d 69
    0x205810070075440e401c00342ca006840004540480000f605903454103042d0710300003002d07003c01c0d69040b04803010344156100303248100030154000d000359031003130300b61810089909000384603281c480d0b0003401000c03c1103074030803503010982d8410044450144c02e207400c0d0755481603070030805000c4240c00d072104804954800030008460a1a801340c42041c4224000b4049580c200804020805070083c00e489860f42c15030350101c2c140d219022601405e004034441d482c4003031401d104145c2529401441070003000802d003020070341c840106a440c20340550000c00815255900c0c00150301e100b40085440e080c00707060160050a012a14501a0303e00300c060340c00c107020b403080400540d0203200c15215840c100c0241030042020a01e650321070640f034103e601003c81c006121010a00c0441407105c0d150309210744c0c420360340b4202c1c40d08101100050034040060312082e44001d001903120004440041c022450001d007001688805a003160000c990080080200648660848079290025184501c40354a0b00c80003986 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722360908 1250 722359658 722359681
    0xa030f0e1f0e100509070807030b011a040303350c120108030f270402040306060513090206030c0d200304030f02031c0b13140a2412020315010b030708 66
    0xb40b040c0c0c00000e1006400101101c402000000c1401499004481000c50441c0042c0200002503025103241101941807c03403800003042444010310031014100001c000082e04201e184090b0407900403150702c1ca80070f00700c54604152038659070740070800311401001860b1800c0b0300680201e0300e0001061450340c0c2c82c0d152496482c41600c09a0f40880400e100d1103400100400041d6007441305402d21502680c021404102030740c0068100321003094071500c00b4046420210191059108100000d100c071342d800e40c011410b9440041c246544590000411880d03641858018990160300c0b080d110030f050140b03517031180c080d030003e84040340040d441d00c0d04840c03c47d100200b5035200c0041000801005001188402e0042a02c00541c07600000c1169042c10805018880e04507101c0c0840910442440c10b05240400c540b8034030030310065030104550881e18800413150380b0007501c020780900c4510358654000280b80190401811010804d02c500201c0c14444c008061402600b1a84807020581c446c0905400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722362158 1250 722360908 722360921
    0x5030c1e0c16030f0f1703010b2502010906030e07030f051510060e0607140a0309060311120414010204050d0501090c0b0a05030f18030c06060906150a050a030f0e1f 72
    0x100800070301141000071800c03142d601c04065110f100d8015444035244040301c6c036500240d10100702c0d000080b0b5005845404e40c1c1461688414101e001155200380358000b0b03140c120180905e2040542e210054605428104502d1000d1500011a1000f41d0320700c2c0740c015655108584080e0896544ca0302003160601d04c2e01001003a10059112501c20301c03015407c0c4011030700a8002274401d40d00941d400d4109107401c0c05443c490034041ea40d0515828104100601550118a07803c0d4040d8001c02c079090009800159840c2c02550040455654441424000c0e019005e07582040d5446141c20702d024003082415030102002a2142e14031180095542880760481d009031401c2c5000b140c810000182d40c9404081016485281da2021030944291220150310355041030803010f500d80d003d070090000524103000b0f140d42c030080855100e030201d030322021415035900851a0b00803d104022980f07085280c003982010451100c601010040c3e1030119404035a1f45608412020b4000c070604051200d49545014a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722363408 1250 722362158 722362163
    0xb01051b0102090f040902010c030f0e0909030a02120301080307020d060b061b0c1c12181503050f0610050a0309080304060b13141501020f01050a061806050d0305030c1e0c1603 77
    0x9c55444446480aa8408410400003401c202070039001c84043c3d5074082403540100611001991109145440a0f01d0302400040d00c1020010901c0100300024000084400c5280d06031210411a2058a0400043d0400d115055032100000c00c0044524540030803207064112002e00721900c034400201030180c40303501c24800f0440320071350240e03100c0410590b050118011035a841c00203030030f891041610601100c9034102d20303114030110909075030070f0790b15001d4560072a0740b40906240074208900040c10080b00c203200d900512001090910340300340298000014140c012134500d0b50303854145480700003802c460300d0252282002d828003025205440c0300300000b044007003030a255aa00e401040990602d20400a6411445a030b800c02070545402c1c05042e000f10310351907001c0b811500b404080d01c01c001c0e84801d010b09103407500e40208200ea5501e0304004845405080259503a181c44000107140c0c4103004440002040081c101c030a0002e9070802820b00784150002d46800c0d40441d40e00300c0b6510003504c4003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722364658 1250 722363408 722363417
    0x150d0c0e160918110702040504032609190317010605120f27011112070e3c040c090609060903080f030702150f0906010603140a0b01051b0102090f04090201 68
    0x3100c102c0340980d4000c08102c09808030942c05d01083ea800102a20002c803400c84c00942c4080e2250039812160b154090440b0b4907601005c1b5501d030031080e880c0c0d2485444511160041c0700c501034014540503d0f5100203a003079000400c4969a161040504a58031440103ca2103140c40c0300060a100c40c1d0a603051300800d40e1000802c000381591070700000306007c03c0e24201495682d0481801004a43c200030580154495055520380c80c0103d0f0140c0b084d20192440c3d80a00304004050000f03400f11044480900108854003c80d455004c46801c8a0803d03409a10307045458101001c1ca00b80c2c00200760b408540555807100c81d031980316082204c9903060343c48000d0043c0020f0149558142c207910146a00800a1040ba2a6456003030701031801c0500034ac0f4000c4042a480d01400f079507030310600080780588054101070002521451001c04045c00040c0a00d070a02c0d5908142d009036807040040710190300d0300603007044080e081e184000b8003d60244401c10322580c0c501d0300e20769076030900d40903010713440e0b40503141c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722365908 1250 722364658 722364689
    0xf14060a020c1c030213030b09120c0a03050c01140103050303150f060901031e020403080c0106091103060409151505030c0a0b0724090305030702010e070509150d0c0e1609 75
    0x82ea4901d0410700b440f00b05243c0c003402454001100c1403040720007140201c4a80304581408a50541800508a03a0815a07801080036164070000043e180c07070043d6251410640d9020176401280c010011088a07001c2c00141000010505c540000550702031000c00e04084044060368080189030121054903035080f40062207805003a602a038400703031028004120192000c5400420700c4104ea01c550030844980c80042103040f83ca00c000d21800001e0403d0f102c0400542c4503aa000e0b00da1400001d0180744a142c40b2030302c940400000560112103254080d80600c44509241180382c3c03810018040d0034068440c08401e80120f19103201d05034106c0d191403d9003481d10707610782c0b034012140d452073f8081c01022031103114000d00c40060b031140c2680240640d07035054032030404440080c00d5800142d600101603200c400b040c400e903520300c1c1021b904044821161543c21122078081580780c01d44820281031152403a070001455060110380900c6036081c4082802d2a86502d002643e81e844a03000c0c1003032110785003a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722367158 1250 722365908 722365933
    0x309030f120e06271912030b131b05030103020a060f091e031707121d0405241f0305070302040b0a12060515250f14060a020c 55
    0x1081c0a400344580a40410034511256090f071030b060080d200c04560040640500e40d003401c2810203010790001c040c002e850004407220131480301d60403018000d0300b03030040383d0f50040145009502000c10101c018291040051810000d0340081151504031907003040c0c243c0040201ca0310800c210380c143c80d402401c0019090801c1803c540040910542805100990502144207805214021070b11145818110740320790442c94110010800885420303072952080c00071400164503c0201c0410501e145403401000840f030240005d941c8140e01042c6c0c0051410041c401c903c10800001ca0303151002c84001c2d0300c01e43c000414071983d040c0c5011040d003280c004034600e01645100b60001500a0b070741d40340c007509042c0c17120b040381d506074046429200480e60015180406082c0c03800303060300801044aa2100e00441c40d510080c6e14070488080c030b11000b4000c2c2c0c0118004120590760003116400040da18100580780c0b5010541c80981030700701d0003620407540000c80f10780c401d0003169208000d550107005203a4112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722368408 1250 722367158 722367167
    0x30405130b03070308040306050709320102010b0a03061b0f020a0b06010509041b030e0c0307120c0e010b070605100515071a1302040e031e030a09061415010309030f 72
    0x500203515003d01c02c03000010500600103000514040c910008440c1484a006080e5460581c000000c0c44c100c15401814040024400310a1907982e0410000a0851a0040b0b00400c0c0c4154007035404400300e1408014804e07260700c60b001a082c242041c030415034000e1401d4405c192424041c0b0016444540072000042030360030040d8015106042140c101a9108001419696890744000a0780d4029042441030b55250085607040040b00020b031981c440ca5002090725031560780034141c180219401d11604000f8003444e030f5030090042004d0130507156102c411400c100d5020303050503103c0900307101c0401c2201c210b0302c0d5410200c0f0001404221400c1c40350300880c1041e0080101594010b070140f1a070440c0d0359018040390310801030f00c0103003041d0210720b01c10803080b84c15581103865164428881c01660105184004c00345405540b8455260b0380c910740b00c240500070080f402003030641045c040000080030942000c1c09801070200c1e00e40c1c01d00006004500702e8440607006800100200226140c0038042d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722369658 1250 722368408 722368421
    0x5270619120f0807030503071e140f09150717032205010e06070906090b030c09090c0f04060c060b0301050f06040c18031112070e1902091c02030f03040513 68
    0x840c031800c400c1c002c50310b80700c98641000d4070640104000008008030f003075210709400c101c044072a003407102450350450b0080c149001b076036451041200006046105000c2c100c242c500d80c180c02004404907150841080d0045c0d049000e04440d00c0c008030079540c80030042c103021703240300c3c485155003e0a140d110b50311002c62007110800c02d5440d95a82c4c0049048108103011003031041c21283c8500d030304240f92410003040215542d001d5400c444052003840302950943d4111401c4080443d81103030380d40c0b03448000b08071034403a0b81e0300c005c4450000a0001180c6030031040916006000d80c030100518400d10050500740c840c115187da41d4451103000040c2c0368a4903510100e2014071502d0800c4142c4400a210701001c41c0540040c2ea042c0c070001004003261900300c410180301107054000e840c0140c503081a80e50040380140c5200350041a086000004503980c0e8182c3d440031000070a40308a0111210f000c428801c44800b00340e0013806080d41c4a00710400000403141203410151500400310394106490000b0f244 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722370908 1250 722369658 722369663
    0xf0c150c0c06020c0703120509030c0409050c130b131802040911040c0c050d031b08042420030c1e0403050d050c0606040b0109060305100527061912 65
    0x351050500701142240c8040d200e008800002003001c2070031070074400700450840224104001d010094540b040d10046005807a00c54190303004101500c4a10b412800d00e81c04504140d0003004c8694190038041043d00401042c00c0c09450741c3d860981580484019200030054811020150031400d8005003804e902828083c0c4c000c8824642a04015000406848081c03150ba40015a100592414890103118018420340107050030021582c0440402e54011510403440d024094040c00160074400f0082c0c8034040d100c1c2c0f256481e0720041d40800c281d07004280c8c0c0d09141005401052150100764032240c1264040c00790041c1035814800706401201002d0140d112210801c1d100340400800185c00f0426001e240c011500c1302d54655050300642c40c0b03854001050076109909008140b0401e0360004003c009507402d9250100e050358640c0064101c1110b80d50080740c000c1c0d000107a04000000c8009500303555030390b2402181c440d485900030404a000110b0a54070f0b48035101204000ba01c44002d030f00b0000c1031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722372158 1250 722370908 722370917
    0x1a18030415051c0c02010b0f0402210a150e160311030c0708040306050a0203040213061a0702010c0c1404060f05091614040b090a05030609250302150a0f0c150c 70
    0x88800f03561043d54484841800540e444000c0c0a00e81d00e01440b030500d001405840442c209040c0425808446049880c0c40040545500102d2a040340940120244150307000b01881c4160703a03880328014211044800c02c01158140080b0702001d4800d0103401c58030f540e9020402d0558466400f07103891684050011941d440c020080000081c0d03a900980344164606403005840c0d20703150050100000106002c01c91281c41c01d40700744101c580b0540700300782005100e00141d4440400c0d1005a486076642d00c4080c01d22002241c0008074160340784180c1007000000c3d501400b050341c1e1049078042c44000c038043d05a001c114240000c243d030300c0204200107000003d150000351143c00000c04003156020350480c40b00100c000408124506010001030000c01d0305400400c0140340c801402e54465450204004032000b241c0f507402c00820304000311002641c1c0042100301440c0a020790144280d102042c0b80c00840e6420022941041c0180100848241c2160401100038842c6000c0d1004150900c0c40c1e0040c003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722373408 1250 722372158 722372197
    0xf15020709181a0601030608120d090f0b04110310091e0204060e1f05180402041e0204061106150a0b0d0f11120901021c0908071a1803041505 62
    0x1d0414403a088900c0078843d950081420680001829130f2419041803801d80d000f002841d0b03840c40203004407410803801140000f0140c81521b07218490401d800d1000d400248540300340000c0c40f6142e00c0d0032401450403011550710404044404081d1031040c04007820300510840c01030f004410030140c010318540300030f2000880ca9194410a242444190380c100c91190540345000c6041c1800303010b000240c00301722103426011030b0740134078000d403410000d100230700a68447c15081b520f43c8040800c1104040a5103040d901c90f13882d041c0c000d0202e103008008016034071800000c188040c411031454842508044c251901403410280000050341c040b000010715169101d4030f01c1c6054080d80b282041c4001c503003219030b0780c60300400014914440c010388903d40d5a4410060340261b80701c9c0f48008004400b4150000c03a454000d0300b041c1840c2d02a098000c0c1c400741039081c030140c03420305a82c0c01a01c0384441468040364015a0f0101039a2801140280146a140c201145041a00960240441c10410b002c0300c03121 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722374658 1250 722373408 722373413
    0x16110a020405040812011e0b1905130812070303140402010c20150703030f110a1407082d030c092b03030606030b120705090910150f1502070918 63
    0x3d01c04240d21403480d0301f01001c2901110140e10f12107400800b41e103400542072103602422003003030851819103003007402800500c0455041030704150314010090304003a01e060b0726a8500348003281d8001d900440000b460001616004041048043e00581e01030b5104040351000d981e44081d03615031003d07080191440480300340c401e580c864510081e420804441c1c207032141c0c9603141c00307001d03510003122101ca40b40c1405510032040900c241a0307030250f80c8502e046009501000700c1010340303100d500e0014240e14030005152606141c0c040541c054442e80c0c001140c2c600407403c0054085000690383e02d205501c00300609506490010282e401002d41020058002c07a640e1250440c401c44062080300400d40320002040030580501c10a00881811780f10b01c0070016070b0003c0e05d510b078200d43c000c0a00c60038012022070300e148002c00240524000c15141008110280c900d52507812080d40b01d010302d01c02d00e445012851204850302c030003160311281c00130000ba17400c008001014124030316003070080d42440b68142c0301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722375908 1250 722374658 722374687
    0x123072706020705040f05090a02010e13060b07020a06052106120604051c09240216060203071104020711041e11090916080f0601030b060a02030316110a0204050408 72
    0x1094542c005040161401090200355482c1c01100c401c1d2924100820005640c007180c1c15005903824608049580080780000b107450180800703a02015103000d50210707a56010000620885000301c0300d0658159441c541110380380300f49a00021106400b0003070342220502907208a40241006210b250000e4840b44440e10707080c8105d0701618960300c03d01700703d41c4010554515005552031450321080c402c0c1080480360f100f1083c242008100118884151000c0c2d00c01c0c0551480b0180041c0351911555407400004e680e9084100140c0d08003403000c00c111500d2400707108441e116640103202c8000102075004100081c114400c02c0d4544464100400481c0030980c42041c400d8941e11081c0e503190b5015405000e04128000c04c000e0011900c001c031140c48503007004002d90322011888050b004c0c0e980b41d2004030301a00094554275080440480d000d0102c90300480070358881c1c1c0078140008031008854070116264490079200d0451900100207040c003604190b04401d500074010041c203854600789810266 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722377158 1250 722375908 722375987
    0xc140909100b1c060b01090f08190c120c030302060c0310090c090b041d09030301080a0f210903030e090402130c020c09010e04020a0902030c16050f0d0f02012307 71
    0xe644d0b80e40c0f05142000703580c0048095000d03020081c1101031032414502c01395038414411041802c4c8003000f466032020032071508600301c040e0040442a0f02d40c0d0a403850030300303480c22603800110b0260084e24001044184c400060f24400c2042c400500d03040c614090a4100929602d48a8010000c034020040740c1c12120f81c0042000348031000103900e11488480402c441e04502610000d901e0700104010030120000081c0049000c0d00180e0302204070303482e071030040540e00e40d08040d00025500198008000e030b800c142003608490082d26900072001201082040f00c00003224001d5000c02c03a9130002c0090b0760780d5880707030710f2442150044a0174420a040010100c1109a02c000030a40c001400c1108504203460030a0040a90510035400c40c1042c030010f01c0b0170300a0030400c010580000b642d1005006003000b20043c0c49070038600f52504c0e0024000004c0004000c1015031001d5130270030200031201044045800c44c40d410043c0c4c02151a15190340032288640550001d00c5800b00c40613038800c1c41c814110184 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722378408 1250 722377158 722377163
    0x1104090501050c0c07120206032e0e04020f09070807080915010321090b0919030f06090b0702071a0a020a02130509010b010c0f0312020f070c140909100b1c 68
    0x161344460083e051a403070b1400a0704200307201324010078420f00688070310054a17003040a190700000b9081042d603800420301403552504d00104c0c540b000001d8403090124a0754003a034020313240100b05000340c000780581074130300b560b104001481c1c000000300310500c0b078070f50a82c01464500984040032907500c3e146995800030707041910103060800c3c2c400d01d0b0840d510303041c081d1320049082800791140b0303140300c0a5a0780111406540580d2800c402040e0048000d10310320701540c0d01180c2e9403140195420101c0040007500e008940001900c13010481240c0006049000c039502e82014481040588022804640000b2485425071085031075803c01079480e20304009140312410700000b214513007000c4440c00e481c108450035060004400d0004081520304010a20310f039054140308410018890448000f40305500231541c0c0e1290100d1204108008203003224104c2ea024036000319400c4c0980108824040b040d01d031030041c0c5d4081d11305540ea030741441e0800081d96030003d141606060007000c44040f88040394008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722379658 1250 722378408 722378431
    0xc05130b0408011b090902130521010b01031a061e03130314041404020918180c03060c041211030601060503010519050105040614091801050117090703110409050105 72
    0x61005000074802c00491500031013401110040104d00a004007005000f15101d00d81c0000390949a8500d840d00d0344014a005800e10312902c0140c000720000c00c2401c68590300a5007031106807040c66120740213154209041c1c05c09101804900d80030030005038080c12860300640880b1a05070b60050300e51002e14442c0b41c88135000081001c0b146001840c20003220030300d820b080c80c24082072141c655030181511000743e06440040c0c3d6401c3d8100020b0540c0c030b1503406901a01c10306d404102040d1071501a0754000b01c48c090032180c07104003800406848081c211180802c0350b02c1884208081004d40340d405407020700560418504045950220781042d0003600040f020400c000010031060800c2c03810b0f45208005a14180c0001c2d00f0300340020304500c101d1140e002049460320b000092140d0320400c17100c0d800740c020402c048444440c1304008450509101d83d6010510210461407030a0002c407600340315002a402078600582556100f6820700d500c000c02ca03400030307502c0c0d14200c0054007d2051038081e4011450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722380908 1250 722379658 722379667
    0x1b030703061d07121e080903070305031809010509040b060109080a0b0106110316120210060f0303021636091406090a170304060e100b04110a05030a0c05130b 69
    0xb09249081080c2d07105410304c0d040c3c2c0001d5800301d240302c95070f46802041c0b000c0b0038035400000d00349135010703000f00303203a0300da060040700d4000081100000003810501d40241c8041040134200d000c201401e1300034032405030020882c000040000c0d0f42d809005c0c1d442081410110515500c40d9034051410202c044200d40118804d0010301000b5040000a0304420007000114039003241c0909a605810840300e0003490318900318410f0710070320300030b0280c82441c2903021010081c195407a00c01c100030002511054001d0701525500001345d10741d4544540c26a080006100d600d00c0f1030308104805809244003580c0385201031004120510814000c5050041c080d0802881c0c11144104041c101075000c0c081c25400c5d0b002c1441d050014a041c0000b2002d0030b04851429104d035154200f12000d04101800101c640c018411520700c07200b00c91744003071100ca034213580c108814220b0541d107050510580311202c011800a00000e1600c9010340c05c03171502c0304024034206040c05d03c3c900800c6c4030044a50405801100e000c03a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722382158 1250 722380908 722380961
    0x1503010612081206240316020f070b090607080412050c040203070905011413060504060305060d020f04050406090b160e0f0d031b170408011a031b03070306 68
    0x40304040c008824001d0032240007907039601c0d280e2007038030700c07812850001d400095240d55690f025030b82840d000c000b0301e40151700445000c4c549a8011102042000c084a619a69003840000d10b40107001c1248000d0004a04044480681d81c011011140d4000410821440003424a00241c0010324034402c00220584140c6005403c059060040d070b400313107105200b08a00e090b402030440e1304486003820030800300404440c4804062003000b00d030765000206604001a0f10b43d00500401c1200c3c0169010003940d01d400e002c104400c2407000020b03510034001880405a840c096002d2500309208e0f000004080f521581e03110804001200d22146030326440c0400e0a003103400a66856406001b00c504481c00b040c80b03000612004060350001d0200412042c01003804410052034a040700e40096406074407185a88002a5603446400b81e041a54200a8214480c0300b40000d4160046001006040d02243d2140f101800d0754580289540c140324082d800008076146d0f1085d218100d20075104c1c0d0403850802d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722383408 1250 722382158 722382161
    0xc0316080c10110306040b0102120a08071404061416050f2125053d09030210050903040b0301030f020f090c030f0a2403151107020d0614150301 63
    0x6280182e0a80d04018507030350a107403100210f9034490320440340050b41d4100310004070b2800d04103107100c070440e803800074504803100d800010051060a650760749a800c92103115051010f400b03280328403000716018400b4200142c2c2da4001801e810aa50210b10b91842c00c19140d1a01e4103040c8513811089822005202540c00207403048440611900754149180c20171170038840d100202d0f0f800301c078050390b103a50700448101305060201c58580850310561001e000385040350070f44898408501c018411700101d1180740e6004041c06501c103d03a4150b0041c0c12224040030b98030340a07203001025909140070400c0040345501d6480080c601948c056424164003912510512005420840b00703548030340d081d4410000100f12150481c2c0c1c0c8000d81e000c0e42c201546030003c034140605035482541c1cbd446501c0c4036140c0180e00b503141001044a0003032200043d288548000c0d01d080b2003101800c124400400c002101c054103203100342600702d80c454007000171090807190103441ca1800a823030441102d044501030620310701c3c09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722384658 1250 722383408 722383423
    0x807060f0b180901060527060402070209040c090b180a0b031006060201060f05040b06190e0a142d060f0c0d0503041502130603050402030c0604090f0501170c060c0316080c 75
    0x58031031f8803500b0b05590800818250f401c01c0030f00740340c04400028079681c80e103406840041d540a010541d02c1c0c00c21345044091080640a20781005203862820750702e6103440041e00070700e0300c0001d010110603114850101c0260a41103132031fa07014400c81c039040902c45c82d20720421004003a03075400081d4a9051011400f00444943c1c00148184c0c00c00581c8041540c6000032200c00391301d1002c05900003503c44800f80c800c814214490343d40f10004034000503883c07066800480c99010101d48091902d290b50101a8000301c507007081c0712050300080a051100c0c10800001c04001c034202003a0b07030800140d80c00075441c0c0ba4039030400381c0c00288088280820400c00c01c0381d000d0b002800141c15810104c800c0140c44001b2460303ca004105a100c034041011342d01c050060404000c4044d00e550794694855080b04060101c1001304070920f45440000140d205070440c00d007030001c1c03101c40901205a1050100905500121402840d500040140c06246c1e902220068411441071034803540720340071420040d040110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722385908 1250 722384658 722384669
    0x202719030b1005030615041d03250204020d050910111c0e030c0f0d050408031206060d0504120e0604050a1511010e0d1706030a021302160f0c050d0807060f0b18090106 73
    0xa10703040601c2041e022050380e0311314904441642b5411109041d003880f82c0302541020303402510020301190200c0042d0042445210304d00d0440720510b480c0f0610314212541402e004019182c180000ea006900c2c2902d00343c02c034120034401251a0105081d420300355408400341078000e500120350190000d070305000c0d031903010006050280c24503207040810380c4c50f40f04900c03440181020160006065513185400d6074500d5004040812645ca880d2030f01d002e140403808000008688c540308085080c3c038040301100c040c0e441c0680500300481c44c115941c42050001080f6505022084401203d002c409200b4502c003602c940000b08031140140d08050040d02026100c0c1203440782020400c0559200010710300240c42e8140c90940003c240003816000a0141c12001040780302034130605400d000c500110350050071b008201481c2065a10820041049400c240c020525a0305000b51004100076a201d140c42a40030080460101821030024130455555065011181c2c110b80c140083c42c0400d01c6100702504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722387158 1250 722385908 722385941
    0xc220b18010f0503060403080402040b0d0501050702070603180309120204110d02030601123b0f06061009030f060509070b0d0e0d0e060d202719030b100503061504 71
    0x820341c0b402008c0c10340c020700281c095926070503924819220700d1072203000d13160400001c001301d08021000135200c141074818480020304080039281400040344a903450160725889103602140380c0800284824900304090341d020740c2d0b850100e45454994401400801000000145d0ba40b900c0000500184601034190710751a2401e801030407040a80d112040101c1c08903901441c40b88441c0500b004128003078030308143c40b805644d180d6092074500250751400340104680d8424810799801084400041c0b80c4800f0306110b06095100020035810350145801103481c03001d40e002c40c0d84811340d4022981c0901b2511b0311190752025801c10820703082c8944071180030545001100c40880c080010341600810340d0070400c0994038008108011000d0103080100d088207448a500c07030810041d00b24481810b20400c900900d5641710718401407800c001c07458201100181e1000c0d100c0e082d074445050905004107100e503c0084040082076603501003052600c80c400c8240c025000f408c1010901043d01d40d01c406006251 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722388408 1250 722387158 722387161
    0xf0b0a0615050705100c0306080601080a0b2a161e12120f09080702330a020a0516050a06171807030c030308040c06020c220b18010f050306 61
    0x840c280148041c0714500b490b0140c2c4500325820b2550521021080400d62549804003a06006070140c004108455003502070301c41c280c0c2d0300d900541e2685070081c4000c00300d42e1901c0019105c80088411100494181c0b4107401c00b240039085c40500d2176011002c070740b08412040164508010074240914a9a90300c4840301d0030b4854903944041741e062414800106001c5404026810141168040c00c2c0d9541103440502c000c8520b0304040c4203983c0207000583c001c000300e12071407202d5150380c401d813008000444210341c00702480b000b103024140c00c0261110110700941d407107000801c1c400c0120030070601004258a04061070b0404210080e0f006038881e1051204000710543e00258814505610401c96102245000c43d4000282d0601c052504000d1034010349a90100506901660a41c8241d00ca84007044403070340c5911041c0d903600c0d15201810ba0200614442c0c0e1031100d100200410442d410b0000451450154800680c01051000d641c0c00300101d2107004001d28011407000b00001c020a9000e841036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722389658 1250 722388408 722388419
    0x2030a030807140d2c0606100e060304060e06060117010e07050c0d030606120c09031104060e040503130e010b031b040807170d0c0c150e0d08091206090a0303150506070f0b0a06 77
    0x111ba40051880b8820541d08840d00361185c043c0b0a07042c0103035001494907540b4070f031924020000b4900d1050800b03c82c0300312800a03409501816402c4c0c0c1718407810742241d9140c7e286c0044103030703525030080001003000000e1104514400080040341e0401c1c072941c502181540c01c210b40200310f000c0014408541d103080641515103d0f4204840c901902d4202841d0407001040030081006041c45920a902851441040100303000020015000313901d0321007100710f52181c2e1602d001c222200e082c003c03520581405c00214020000710b91024580050380c01406017800e94072001207050025582c04184061400301d401d020b4400b061082d4440b000c000c2c100242144410b4880da41d00e45401d000e036802c0034054200610f0481d010300c440f0104600000c1c002d80d80c00d0348502e0301c6a2660001c4030294011030040030206003020010468900c03501c0c2d044001c00d808841c030340741100945441401d4100003581c0306004902d544401000b8035103c0e00400c554a216001803611440a001c01444188603c1c030b403030800c1c0179 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722390908 1250 722389658 722389663
    0x906030103061a06031012050f0312010e2503020d0b120703060f06210302070807170f070b091c020a080d08090313120602160506090c04020702030a030807140d2c 71
    0x540d00703900000c5046240c10701c0e05515144810000307849c544008101407850710070500406068681850311500181c903503544a59101c1d0369070880f5580d12404171485420303c0d01c294060100301469420204400705c0c00300100302c503204032052010240e0400041842404407a00920000d220006400c206143c0b41140e1400400d20103451185002d6840f1101c0c000c0c94801c0012401130098601075a000741d0f0381e0550641030074004070301251107001c2d8001c0d1501010002c18070504903160700702820b00c2c0035101400c004010003d080b0752012880d4110600740561550740c0d031703140940b0034800148050f00351020007a14045005140d1340303641e8002c01103001182d1070400a0fa04484c0c03005550a0900c0301841e0020290003480d4820034809a1109c0120620070002569401141068203031004c041a103000e200c10b81c4201103000e90558051a03000001030f03c51904698000d0562800c110030484202d00000c1c82e50040e080d0f040340603151202c1050140c1e2003001600740509460200150228441e0f1681c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722392158 1250 722390908 722390941
    0x301030b1f0914040606050904050a020118090203010b03091c02101d010f060501030f0212010b030411090711010506011704063201030b010506070213110906030103061a0603 76
    0x105601100350001c15200314070615200503080e100300511a40581d10034258580400716030541e103407414008001103078144802c01600450f006009000c4c40600c0340c00540385420800d01005901000100000e4018021302c061406020b9001116070f0784e04180400c18079004e00324180d4445178600c001c019200750380014080d030642d03144100c08104000030040501c0c94041b495031010f025400c105c003840c11020903901c0300301500e03400d0301e007040240202c854040c128000c0c206000c411085000040c01007003840c101039175100b40300b414074114511041c2d006c241d40c1d005c1a540040801e00c0085100c03491002802100e80c000000c1c0b800015861904e00d40448520001e030001d040c05a0311540044035413540c0394070003600b42c100c8455500c030807800c00c0d031001100824882034807804034600003c109403400b00115000c0580090080c1d80c01d5808030403c0c0003c1401c00300c7c1009840041020f083c0769103032140958000d60042c940052890340e00800160342440024009104070070400400c09000805817828 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722393408 1250 722392158 722392171
    0x151501020304031407090e030703120c1b15090b1e06010806010c0c0f08030a111209060309071a1b060402031c140d06150e03030d0908130b0405040b060301030b 70
    0x40c01004138078600c2800e206058000104190401243c158203442c008028114203200ba524100c4030140c45609a040f40c015130542000a0600f1011042005450b00a01c80702405149a40d0b80041004600c0c000c544202e10125181e0a0542c104250382411148400e01102904000c40b56840e0010008040510042076039040c000c40702d00d890140032030410300708050000c0c1268501019181c0384056032302d420140403400003900d0842c00e232a02c21808200511800348000c3d00a050203040c004105d00c3e500020400340300381c49080350000c3c800c0c1000c210304814881929502e40d4826190030fa081402000071601800c60b800304080c4401a00d001402d44183c080420814800c40d076100b0045a803180d000752005000340020500c080d0044040d40070310100c0d080800d902d80604050102641c1001101c1c0e20554590010322910b40050034030b401081c4180d104695540c500b212204200d9207410981d0020117802c9008035040c4102d043c41c2c801c1d88605101101d8190440d891503944140310007008129 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722394658 1250 722393408 722393423
    0x21c030801051e030a0b0a0b010c050307030c08190f08010824060105090904080301050348030a0501051906030c05150c06010303020a0323270402070515150102030403 73
    0xd40c44a00c108010441e40032005041c1c17101100b0f10b050030514100256848500340d89070032500c54072903002e102d2201e903081d8840069800c00250761010346081d403851000741c4100c01c00b040000802d10082c06080420308041d02c5031100d411803068000c00e4231070143c00001041e030229400c00c0306001280300c08216600d25004256590f513881f001282c4a014210181c1d421901007020700c000c10102001540c1070707e60582c11104500a030081c540703024400701005c2444400e2240b00b401d5041d80352140b1000c00140010303031180500078035022a207007190940050303030700d0303550b403403e10101413000b01144e00e00000036542030007030f60300b0341e16400d407040c210740303c0c2c688a0310414100e440d800c12280c044d150390749480d00580781e0941c0c1d40c0c140a501c0c0e010641e012000159011147c5055145550b4028011415180200c0c140020411150b1800c0c84181079400b940b403440500da0f025644a00003044007c2c4200301520b0300f4040d8a9540e11341d0035007e4044500803558114814090360b0020607901140d400400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722395908 1250 722394658 722394679
    0x4060f05071e030209030703150c02120f090301090213090303060b0c030405060c24040b06040c120902120f0c030c0303090f0105130b0313141c0f0201140a0603021c03080105 76
    0x241d00a20601001c5da806005400c400428001413000f0000c2c0403c032800c0902c04001010422602c58070705005d6111105c4040c0103450389062203201a10840b200034000080d01081742c0c000400051a100d070038181280c03500313188001c2603450300490008000144c07255040440c40310b11561240030360f0140c075000707800203d054034207228100850102e214040b20324001035520b09d0711421180c20121000d80700c04c0c0c1c40f1408076002c0c0c1020300c512480c2ca04d182c0e6610121409851602c0040c0c200c2c840d00742d074490500407540004480034413050394408254401807005a021030141030920f030640e56030a110360014440c084450322600c0603001d04e0102442e10310741d200000880d140702d02c0915003200c1a0000040104000242041c988940321030094160350101c941000c10305585040240010002603008014900360902400440c40d50b07000c0780c0004203c00310880c2980980321411100440389907111942017003075060a400000701d07020541c010981141d0651809003c2d9203041c85600d00515043c00e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722397158 1250 722395908 722395967
    0x10911101d0628020a0512071505190c0207050f0a0b0301091e0c05041d1003021c0204420e190e0a020109050d0b040215090907020604060f0507 63
    0xf011003c0c0820710484403100c107480721000350b6820010000700c4452080804c2003a00c1130100c0c054581031a40410b02000030426825038001822001d0002c1d000204069a01c3e0701c0c401e42c034010101c0d409020780c018101e6914104c20003c00c1c014850040d401154051000e0081c20118011203064400041c0003142000340c00104801013070844c020a03110070700e002c040f00c01aa038040c0041003142c0c00d00c2c000c4003181c09850000c03140c0300c8041d42c46408040c40287d00308018142448414070384011401c06d00d0388019142c0119050f55010400031b0000d50300f1035042000800410f00080d031003d00c4118440e044443e4000f2484031312060300549205001000002e50007410348010100c600744222000e00107550303a030161954401c20000c04a000c141841d0010986080c1a101c4c1003c0707a8008036242100e86844d020b02c8400560120400c100860400c01c1c02140d4569146450042d581540101883e103014204141200d5032402c82603025410b00080c40351159200c211a240044512842c1113040b0890 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722398408 1250 722397158 722397187
    0xe0115120602280305070e0f0303070311011811041404030207360506040605100909021602040501080a06051006082e09090c05060403030827010911101d06 68
    0x3074a0f180120800b070400607507240d045540a00119115502d00e420300c40108041e41d032610f400c954141d8001d10110b800300307100c2c1001400703020000000007170000034251100c945202e000303425a01501190070058403418544103050300c0e40b082a03c1140303103060070355000352244a54400c0c0c0001145c3c0c20b442610441c81e0060720700d0b0507415911080002401c406a4a020b803008580c010700c6145405000100c03401c003841d03c0c1e005100b00f86e80e030106140c288135139000203400c0301a280344680b5072003c01400503100c6214050280000c0350003807402003150720b404019114020410707001a00c0b90001000004d41005110390451515560f07100e105001500241110b00d00030030b80f800f80031599a0002c2d805a040d0300050380a401600348c90841a10740c01801018822071100600041c140c81c00182080070b10440206020000454604002d4507400d80311700f511000c01066034008c001d00c0408826181c4a94502c4c2614203074281500350110140c82844205e551680107130041400244842202104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722399658 1250 722398408 722398447
    0x51308031b030f070f090807150201091403030f1014040c030209090a05191a011107030503130e0a0b0a050108071101090804090c090e0c070809060a030e0115120602 72
    0x30400e040d44a26041c04060340f05a41039a1440101e140304c01078a000904c40c001c2d14040d030300048014299185098042084545880740d400300b15581c8084082c0029070301c40d0440002c100041c0210b80f2400c0440b5088183c840182c038004d1030380da4907001007140745060811403d03091000c03200001e50000c0c0820540c0a0303c40c0e0200140d002e900102004100142030344000c4c090368041c400c1900600c2540300100442e1143c0c210200d220003040c00d1b0900079840781c0c908051001c031220030b90781c16581e259110703072940d00b01c8444142e486011480600c0400e071001d9501c1da20840840d800e02c1440001e03404a0000a0ba60090343d042080302400680501e004500b1036800729080c02c020052880300342044072080d0001d02035042c6160074103807404070107440b8890300c000f2785685148800c150b0b100c07054410001e9210820848124070300748080704a66490b040540800c400300d8801007050311b298900f00e42150300740c19000c507007159a0301040c48501d44c0d06940000e1184d003d440140d61b074100388126080141c0707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722400908 1250 722399658 722399701
    0x13151d2115070c030c0f020d14060a0e011125120e04050a060e19020408070b190c05070b0304020112060e1e0702070303030b030114041406070201050609040224041203080a05130803 79
    0x44022101c140c49c4001500714070645543c8000c008840183c09a1400c1e1031480f683d142d405003050018020981d98080d900c012075409102200d00450903681f400b401301c00c40e884a20200300e230855048500d05003405402e900884081c0c0400c4081d041048402001c41d010306420045106000720025440c00365044601400c9924101d8102c6540c1d41c41d00c0807580d00c80450b000e64a24503034251f080160240c038500c85d2207a4444080c01c2c07554204208041103400040081e410000030890603107102c010741c8030380c2010788030207210203405c0c0c903010707003d10303241c1c0d501c10406442c55422034208595141d0210f41c203000e0b254149408a841000580000c1c050048150500115140842404104100400003948080d54603003918440d6032443e8040c3e00320303082180c1071070b042071009000400514001d0b2280c4061800c0007040b800d1403e103191501c000303800c00d030050400004019000000e140d0804001070b442048203070280900d103011113405283c084258402000d0f4540030010442d803550f0f202c403e07802c800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722402158 1250 722400908 722400923
    0x11a0a1803020a120507050a0e0c0a02032502030c010c0302070605090f09100e090102070f140f01051807080619020c1903030213151d2115070c030c0f020d 68
    0x3d441e00d401c064013240c0074101700c49511940c00700107091b0034080c002d1002c0340c98139891103a1f180c1e0b41340d80c242c0407580000700903401c40c081000402d690300200790355a0008072200103c3d41004000c0e00c14136140210103102c46050042c8441d803075001036800142d10090340d42d60310f031182d226032450b40464500143c4610790b0f0340c40a95201001a04824405500125a42c481480456880b41d01a2074200c0c460340c00007a22031200c2d040d898001c1041300c3d03d0290b101c064402281c03200107403804044d08444042d41c0c06401c8004440328608a504104981000703000307048060055803c0400066412200f01c10028800903008540c0382e010810500507052004030015420b10120130500c1c000380254082120a0740044c182500801c1c900001c0c1300d80f0804502c141ca8160f0800c40700f0000c6850450014021036000b984101c04003030000b00002c0500300c0c1c500c1c500080c008554000e074501043c84004244004000d140c907a01c0021030b03032000c05d0300c83c440e401c00c0d0200c3d00d114490010803000c8103981e601030002d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722403408 1250 722402158 722402179
    0x1b120f12050f06010206010b1809040206040503010212091638040803091302040803070f0227060f0103180f03051207020f0105010e2a090405070207060206011a0a180302 74
    0x300802d0390080c03040300260f080d5101607803200d0312918140112003004005195142e034014042c02c003003199a0b005400104580d00b0641e03640c00080c01e980c031021039a4017900d508800e00014030402c0189200303034901103030800080350a224110800e0750101a030103a0b064a0201124040c030308036080030321140550150169141c1d20b8200881c8d585d03200c61541b500982007055200100c0d0b08910949081d11028400385141215680f24504295803411040e0b9001c02003042913111800419008070340c8507643c1c0e03680343d4646440c1c0100b280c1c00e009100c1040c14503082400e9084424210160075000326030010413a4580c00072070404480c107004a200b85996a5043c03018440c450b0340000f28a07180890400003440640c1c0c84540b00c0c3e07841c1c41d00f52100c0f00312502e03501b03005a400110810004c0c40c0c031a29070489007014810720018042d2035064070550b0250f0050801801420345c10301c41c20b40540050302d8809602144c0000c0c4508a10801107a0002c0001c0351941c3e00c40c04010102c440002d54004210141c41d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722404658 1250 722403408 722403421
    0x31906150906080f062e0309060b060304020a0b16061a1e0109150210060303030207050d1407030c022709070f051008040f080f0a1b120f1205 62
    0x4100d20301281404958901d400140d0644141e42d800d104214668113001c060b00d0710824400007004511080340c1800844540c90101e480305104007000500300c3c0e602182944560500e00c085485803000103008080c1001000003503200c0804800445200b011141ea907179401d491460020080d80c280200100d08100b07417904102030b08915107040c08021101d04079041000006940000111844580402c0c801d55007003100c02c5158854004a10650050340d0183c3d90907034401e000c540f610340044011a50218641042c844104510010000103087c513019103904082555034500540d10010704203c1e44248802c11500c5551040a114484400f507100c07003040c000c50005107070401c0b00c2d005018440c090001503442090714441c804c90b54041d151100c403800c003044c2210308040003001038418007890940c0c540041c0c2000300400c41d8142c200354054540142c0d11005000c2000412002100b010001d001300c041080b0700200b491145d080e050130030000c14292025110f07014034841e001c04075494541000781 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722405908 1250 722404658 722404679
    0xc080c031206010c11130e070f03060b03030a0206190902120a20060f0f04120f060f0c0e09070201060503240105091603050702010207081605210d02031906 68
    0xc00700035624440a81d641c207801100c4280010030041c000c030100d015a0045418035001d510100d1660143c0800c180c2d1070120014a050900d500640500c01601020004d21075244188420501e0032800fa41c03030211003100003940c841f00500b1400300311032a204030785417081d1503510010f240703030b806401a40820540405903071221034905080d2004000d4003510905581c1d03140c1d03401c200c150000c4c079250801a0303d4440d030b64150840808140703101400c12000c120740401c401c0d80d0308501d10513032809916041603e440e10603100d080551405043c10f002c50000103e400801341d0010804c10354594416698902c1c049000d460702c1d40c8800c0d054010061005c0300c074207240c011020b00c0d2142c40d1042c005a43c0e07403001d0102a51040300c811700500d11818048401c5442a04500d07004612071001608090042d03ca0041660202520620340d0720140310000410030240b01e10341c440d0341b0231381a0800c05811203c2034005407044070400300e10543e000000a0f90103100540001c1040140c01e010082d86845a172040d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722407158 1250 722405908 722405917
    0x20d030e0108090102030105030a1514011206060905390307030603020a0e011505130806010f0918081602130f0903081b070204090f0209091b01021c08070c080c03 71
    0x7400200712100042076100140200e80c104c82025005040c031040588458004100640f1071f034041d207482e41c1c07100a000b440034003598080e0100420306a00c0a0081c40c128084585960041880e14100810031035810300c060040840705482115989034000502c2184280c401c0048141580c20004000d0000d903a0f80b550088040e04c4c401d07103144207078070303140d440d0384100744024810041928440210884150321600240410450054840032000c0d201d880050030904c00760400d888107800c210041141d0144c5020710200400320800000c1c10b9481901d984145104081c1ea1b00d000300740041030001103440e40340d11408000070b81c500030000074410000c2c01000d068142402d900240001c40030943c0f204e40b40181540c40100c1080440c43c15003242c3c24030010301050201554800c82c080f0711600540c442110192080c129031025100c00041214000c411106071410981154070210201c2e03014070323250259803140c94840c18000640e641c1c440701240c0101460030014200000420010340300c200010142 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722408408 1250 722407158 722407187
    0x40f2c161101230105041503080714030c0709141f1a28020606030d0c02042a17010f030203071406070c031b120b0a0f0e1911060a120e0307020d03 64
    0x60041c42c60301f20140f000f25190b0b000c05003200004000082c001800082054101c0407410203603824045801501402d000f00d5034030040031161a80408450b001a42410741e07071001c0f050f40391038032074a020340c0c06451910300c9000b5000e00001c40f86c00403080d003c00c0001e40e01d80d402c030401c0990f00d00d494a09408aa4021205c0c85000740c030600b8003282c030070718002c82c002e1462855641c81c0001c0d2a0356800b000302518994041074a002411141c0140e0b00c0c15800d4801c1c0e400000e61501c41c005819203841407a1244141e03c400303840b0490f8101880140c0d008500c0340c044800b0003034000e00714860040014a00d1160341001402c80d203080000104200e0969002005025010f450f00c07999940d49404080c40b920300c00c002412440c104002600750b041580c8000282414a40009441d482e8101c42a01d008084010b26000b50101140781040200508400d514480155480340c2024a80b0704064141000c00d80c0307525410b0740754200b00100c800c04000b640e400c01d800622003280007109060150108141c00400e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722409658 1250 722408408 722408411
    0x60408060f0a0e21221a0a02030d090c180203041209150302032707030302100b0604092003150406090e0a02012607050301211115040f2c16110123010504 67
    0x701c0006e54172005640032450990099460245c00e084240000d083d070b84400c6480302d101703c01c003103560a0482c0f41140c903110588001a0b0707a05150901e224404255007101e800c110f40d02c0700500222503041d6045104c5409403d002d41c598031030540385120280300d42c1c004c048111342c00b000703503d00c0030300007621204a034040d40036580703110004011141502d8515840319000001000f00300018030451f40311100e80c27048400c0340350200c00c40322414001d0b94803d80b012841699803010098403498244140c00060100250800440140b5480300303440740d1031030001034144400030036440d50748815002d1011140012440481c0c451419450142545c0c000f03018a800c444a1111b019014a01004a14800f5a007200140c0c044002d540100040d44014000414250109010001c1c120b660001d02601038405610001009881501121415822166100e003400007120520048a0300d0414038034680c2840d19002010540c0100e040e03003d07082e00c000011184500f00000c00c05400000c00040c1a20000c070350 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722410908 1250 722409658 722409689
    0x6090c090510030213020904060602011b05040317160807210203070b0123130f0b3c0d030e030d050f19020a02060408060f0a0e2122 58
    0x3080088070030031034084140020200c414009841c040f0b1500f900f0742240c240143c54404100c001c1003c0c4c801ca90700000150b0346400d07003c03110000d40c8403141d010800a01e000c60030586503480e42c06d03000040c03400d00700f021800001c010710800161480010500d4101c030b00d10346e036608180303040680700040000309060340041002c51b90b4014404021100040d40012484203036908020b80c2c0c00c030b140c1810098140910041305114080c3d12100b0001c40007541c044030000d005070043ca108006da44c40d00311614401c1403a111104d0715602005104c0321088a8461081400721620016603a02c00c40c0e00e190f02e501c4280013580b1030403d0341c05080030840c2c00050341680d480000c0d01700140c540c2e0150002070741c102c150901c240406842192070121003030703d003071040380c081da60160040b48481d84203800035007040d00440e00308205c8a84000c1c05940004155a04224010204840d10b071074206200241c0706225101c01a40841900c21007520b422100304504c03c403403100f010442c0031440300b0900c40c04895481620 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722412158 1250 722410908 722410919
    0x801060e13020f010e1801090f090309060f0e150d0c03050c0405040b0a1a0c06060102070e0c1305090a0c03050606070c2106050a2304122a06090c 64
    0x84000d0081e0706040444400e00401e41c00c104070862008075041c10000048000c3c0416500c141c5107101d5003120b84440101c550500440b00c084d0f0352a060701326542810484200d00107a4011070703200448684d0b00e0504bc401d400c104084a070301d0388655210364482403800b000e045802c041401802d04020221040010b0755186105405031003040346c0c40400000144005c20950070146c120628900c0c0c000c01400c8002c0e02d070b4800400420a00520a242004c0450380c15000002085103d0300311300240000c1c000e00e0314056164203020001004a1440f080c089820008001080c20701d20140500501c50146032901103190401005c205208a0011f810540482c0c400d041680c02c5450964200c030010b0281c504060b0900d881d40e4590720060002400c2c0540c04c4081001842014040c1e003070800c01103184440d1b1045114074600b4241e4032104019410305000001c0c0320b42840040044082c200110014113182d8400b5a2305500a44103441040c825006001c00069078030094040788600030228400340c8a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722413408 1250 722412158 722412179
    0xe1210050c21010b090f010302070803090703140309060d0f09060e1b0909070b0309250510020d08011e0b071505180c04020d02070f0f030201060b090607060905070b0301060801080106 80
    0x81c07061451301442040703504903900b02404140c01030181810098544030282d81d0700e03011a84102d07050007aa400801e000d00400803201045600000e007500114104000341001404510420801222080c1c3d20b550440120905805c1040c446421020130032a410000b11a580c0f00c03c0c1070b0402c102400030034490b010241c030b01283e0903070007091020024004141056400c407240d51020b8420041c9110345e10880001c680100710b5103c100d03900481071044a4030f00424407010080d0f124030081076402c8101000c88483c0d0290113607045602e410b80b41403054020701c3c07a1004001e03054100b618108000960402030183e10700c0e14001640448400f0415070b82e40000c1445000c80c00c444030050350b003040c0051100380c0b13450f40207441c80e0302c5080c2c0c00500d4142039941d403441c401101034080b10b00310141044081030507021b01c6031100901054040304d00d000c1e240c0f40011010300c94184024140e030355400112041c03000800148024140c00103815559585600700502581d00174071440c9842d6007880000318982c06623 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722414658 1250 722413408 722413411
    0x20010c0506090a0b01090c200102040b03010b0d0b0103050c0702040518030c150a060302010c0f021804030c02030d050c151b0313050d021606110c2205100302010e1210050c21 76
    0x40c0c1e40c401848c0103510403942c00103100041400c0b420b640034031010800032102070086000340154881c05685000d10031040003510352401c04241854580020040201c450508403090303298119000030301c540c0c8811032134104c10700188540c1054400172420780d40c00b05000a008848034005440404103544403c2600e0540b54903010090000e150070190754001010310002e445818401010300004101000301540d222070f086505038001107924000c4819400d09000405540d5554500945004ac1c41115a81d54000c0a170808102c0d5951000141140340c06140860b00030160300d800a030f0320700f05440c40145d5411200402d44041c025054111800b500010b840002020b466500001140c540a4240c03009a0221b0000c0c03c40d019000741050541d40f4031410b0502c400710302d03001055400b5044004007c841c0002c02481107c0380b90141800541e81107411101c004400f01c88201e90040891040c40c00d10f49946001c05d42c9600700000e014030160514003030041800c10304000c01000400c1c007a001c130241c50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722415908 1250 722414658 722414681
    0x60114060406050a030f1a041410061103160c0305060c12010b070615030b07090b03010b030f06031c09060f05030f0103080c01113420010c0506090a0b0109 68
    0x2401c0208100707940c0a48041c20001c103d03401d00191180064943c01c06442680b2014031603690301091600042c90148260700e2503c000c0301d40061103103084d1881820600d006d00402050100b100300001000c1e40c10001c0703402c01032603d030341044508254600b110060300d81c0e00044809018240005499040350b0b0305030b80840115401c00c0d84183d1901e510059154801c0605031144c5444031966070722030141c6180c080045109170b4995076580742c1103000425040315038020300803100c07040004000e646110340035250014100880c445194031418002440c0811195040c1c0c25039070307609201c0c3c0b6511b8001c591981261450b841d0680400f03040d00d4201c0e01440200c45a00c0201091801440414060400381540c951b0280000a410450035450b0707050703800c6210002d00c0004880c0c07058112003030b80080c4000c0e1158441c0711205a5080d5541e000c0325810314040c204404054080c0003950b80c0c4180352918074a03401c2000d842d0203080580282d911080420b8083c1d500e100300c0700000420902c00d220386100c201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722417158 1250 722415908 722415919
    0x2070e0f04032312160507031e093606032001030e030c01050105031b03120304150c030c020f07050307123909050f0604020705010609110408060114 65
    0x1e0355640c060302d82100569510000714100c640c03100403090002c00030485070340241403001183c44c160001c84074000c01200f503030341000414065100081d81142507403640807800d940061803281d0141d8121006c5545e68014407002700c20020515036105114065500ba401b00d060459480d52120380c000b00359951071100622801e0002c482544200c040c8503803000c58541490041464a050184117245402c42503105005954507801000035183c108141c00001041d071340c60300e9800c40c107080081c0e21070031402000c06994000000003010030000d240c5400b00040c003004100030201d45540020024030ac40c40c0c0402c00b5119505034085000070000303041d01100d030020010203d103403c08101480c440150360044a407101c500c040742c02c40844080b01119000410b5071601b28a20310108480010b409035444440300307c0c9018140051092510011a0b10100540b00540d07991315034504540101410340c401461186010341ca0700c582c00095004004903101001100d41c1070341c07500c0b584102004035650203035101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722418408 1250 722417158 722417161
    0x801061412010512010912020d08011706070c060632040501080718020c01090b090d140f09010c0c090518011a0d0c0b0a03050a29041e06140102070e0f 66
    0x1803070724580c4c0b104400c08003000070403030022641d00c80c6428139215415101580103846440b41e1141e008140900410b075507003181c2e2207120300c202115200c00c07020344448104000300200b40140700725a040b0a008110089540701a00c3c43c8a0041c80ca140c0b4030304000094541c1c4618058080c603260107124165803001026000d15071400c800c0304005080000c0d9222815003d108000046a0078440c1c0d40303403a406801540603031f10700091001d0428880c51694030600c0b00254106411682c28001d8442c1030074000d1055a95004c0d4400585540340a4100202418200803000c03488441070b400c040e0244550000c01d0070181c0d006840942039980d2201070882201070050301400342d192403032015040c140100c019401c003d4890030500200c1d40107000c1e0b0800300343c80f2401d00c00144160b204103d18118600461035906280170388041c40c0354125030354144034a4503210628a944440e4000c2c110607d078841007007100f150382e1110403074100d512a4849003d405882d400080e030720301465407103126402250b0105c505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722419658 1250 722418408 722418419
    0x7030b010206270709091403190804240e011104180504080906180f0904030e011103090a080106050a0501080103230a0b0f0610090807060809030712080106141201 71
    0x20828400300341c4141d00340c060b03882c054000f0502c104000b43c0003108000c208065241001984d50098903140c1c0060f0703000b0446080201411440001484541c0c98485044d440c0c2d41047c1c2e61007501c10700d544040c0792180c041d81d0100d46080d404250744604080003400750340d500c0b084030410b500462156000303042031000c0401e0a0400e59002c1988207218208140c140f440c507101080d01c540044800032460b20180f1450443e502d0505a49184102c00b07c1d0346034028941507900910700c0f40005041c0d418007030703e041000b94096060080e0f445810010340a4040b865a0380c074410302074205846001e0040c0c0103998042503551245020505994120741c08004211019105014518080f420703141c1e1800b42180c05000665680f1001d8019604070a54001d60b080100410803481c18030b400820034800d000d4010070078181c0100d9030300111030700c81c10400d2040d61401c0ba00340c00c1d0310800d40014010b00c41031456030070090304650841c3c1078503542c0c0da4500c011003004146000a2040f5400c5c10141c2c654100100403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722420908 1250 722419658 722419681
    0x6091203101206020c07030b0406110a050702060d0b3102131a040b0301060504080c010f3e0f07140a0b0c031c0204061115040611040b180907030b010206 67
    0x1e0091103203c006151030302c004a00350034502580c10481e55046034005020501c6001d014114000e01c001044030710b8290002d0b4041c0c418420864002d000d5140404c01c000c0c5695168010f141000303001c1c0c0348124080504d944404c8110030b4140f500707084d1040000000b500c0300c00d0702c20380b51003242e40b200a01a140c2002c2030035004424140b03081c15518810040851801100c801640c003c0056490b074a841c0e40c04c0021041c2401707508031034031341001450001d0405890340450081062450740e854180c0301c00030b11859080300040701c0344102074540c011034425401000001c4411030415103400341c5698545801280f02e56400380d04040ea804108bc40060095e1071140c0014400b0411040413240341000d9030007036105007a0040d0301d060070558041420002c1641144030510140c40100190141c1d50041c00d9051807210043e1001d005c2c0750380d4462490200d007850044401400b40070b44100c0c1c6800205035446a800f52000070350b4000e151080c01325010f980640120120424140c0182c07a0b81d503a94510100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722422158 1250 722420908 722420939
    0x22050a05090115080c0f0a1502030901030b0102031206011202250c050a0f0605030a0e0105070207050f041401030f0c080f0105100b03010803030f10090e01020c0d081e0a14090609120310 81
    0x61f480450380100080108407070548000c0050a6005140c0f6104880001740403140841e01503410b64000300141c0340040114115160b000d034090800082820783c51940b48024000d604041001c03802601c021600100c0b1120000301d01c80c07089481028450b119400e10130904020300c100300328400001800e01086004a001e140e0040021000003161074a159095094950540e43c00000d604004024429400c15001c050b01c220b00039201405506a45c0c14009812001480301501d0002e682101e42c0401011240d40310050860104840c0007103008040d55008180542e1300c4040d00c0c0300c1300c4002511070381c184240e904071001c00010b5411607454008403401c1c900001d044403001c0a007000c0203e500701540c444c02c180308a519000503141c042201a907460540d441d514201030001c03107010010303188501045010080b01c2450100d903141c48881c003560107080c21490f044001c42200c020844041030004503284111241000c5645030014071210107124403050751300c801c0b0301507514000d01c410f412004016 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722423408 1250 722422158 722422189
    0xc0512220801360f11010f08070903080c150408130e04080f090a05060309030d1401121707060f0507081510031503080406020d020f160522050a05090115080c 69
    0x80c80000f115602d82400c44030030301d012103504a828441c0401564804140005880e0314141074070350303081c228005412201c00340302c02864404d0008810f81111018001945150210603a10f10340d424181751082c000e4001d1030120701510b21004001500c01c40c2c404400340101e400100b06442c0288258284d400365005441311600301c0d003c1c2c24005501e0316110005c5203d014075801030750300c81d9991340c0e0110960301c07142e41040104450f1001484080943d2001c0b00702c882d4000240040c10845108501c214044e102015006501e05040c5040001c01e90304020700c03490069407481241da40d0344900d036610000031441c554110202c2402c7d000c8103400fa030f000c141d200c015241a2000c0650fa5514007401d6441500681c0060b00711007014140f640d0100186022003055202401401900c104070111116852040d5841561641101c03010100020164000c0501c03285040c0014a41041048060f03c0280c0d40c03980550703e4815080d29034444410a2801d0300c8000b005400e0b0720b4403900403c2a20341c11042072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722424658 1250 722423408 722423501
    0x90d02040902030a03030f0b010c05060a020c1006120c06021504080c0a06050412080c072103110c0a0c0909020f040b0105190309020a0608090d0c0512220801 69
    0x3800c0250f6420050160310707a200c4d54010034400381c903122050a460712246188e0511404000501c0054004141150f008070742800050301c2d00c6001c1c189078a40010f14086415aa04d80a40415203108001d0280c0105c2d00a02083c0f018a68401049030b60f1400c6244280d038900c001e8020800080c9108010300020480c2030485040c2403c0e500e07260b085070070a89045580001d290514000540c100c4121a4010805440d4505101c0a17403514071103540c0107001c0d1404007516203580d4000340c1c046e80c4001c4810a03100300840e201e0b4000c0303802c03942e40c880e035640c2500d514018200006611415000b0800c5869010700300c0740807150004103000103405000209030600006124000c80c4400d203485103615225541d401144d40712a9005101c01e480064010382c0030010384804000d0300ca02e00040040040e0068034048401010038148181499101607800c0103500740090324151a0b0030200d078045040449c050440340060b5200c101c0c608880d12120b10140481400c0740711050a03010390642c0140c00c400400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722425908 1250 722424658 722424671
    0x615060c01151401020706020a060e120406020105070305180a0303360b070806011b0f12050405130c021c03060305060a2703021905010e06090a15050606090d0204 71
    0xe9036080d520712542e1000c00d1032262004000141e00c00c100f418003140207001903d44a401d2490003512403543c4e01d40940500c0d02c6107492013404800300070315403010180c80092500c9640704c3c0d10080c041c00b401d580780000241000046960205540070120304040d079040105184019980d054000d0b101d0780303895101481c100071065104039030f03030181c9041441c1c00c0c41a005680c00b46203013051210502910400400241c0c1d0304220069030000d207054031140c60075481c0b150b0840980f03031219a031022040c005202803288107284600300d07081400380081e00d60803290304079408000091201100c001511100050344000b081200d2846501310000c00d00b070303643c600803400700c1d1281c07074280c0703003580a88251030129510010101110480c0700c1961801c626444000c0c0307103100c5034074002c1d40c61200ca03011600e4040c01c8002070040010950103003284c40c1540d0251003261a0100d1041d0325000e032400c1c10360b01e001809001d4034080c0101d00c01ca034441c8500509590a002400d024403410076441441249c01c260f8544 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722427158 1250 722425908 722425927
    0x309110312041d06061e09120705120606060a080c070f0b06151908151905091003150515090a05152b06021306180f0602061506 56
    0x3003001000300604803580e441c503101a084102d04a60010560300b0150014001301e030343e4503003c854041c940c0d0a4520840c1c0c41c44a01524036200d072480040e44000c1100c240110004049801801c40d0002c44299480000c031501c03a9485400841d01079078405410040c0c10b600ca07009108090300490b100e00c020342402c020340d5130902802c0440505440300c0031043c003044210314262006000844590996a080400c107038201c44950310013403841024000d10100103899000c000354007045440c8020a1000035044454401c0740415480c05640c0c01403004200082d0b0f510002201d45003100e42c00864a5049802030700d41ca001024042c061750511a4002518003840d69901000d40c051080194002031038104060490b004201c8414203902461540080350a01c06403030724000039104103031020a6a01d5000d1806000034851521102c50904c9d0012000c04c000d680312070360140c181503c02c9214403030f588404070500c01462038416100141d2100c000100300e010828440001082d01a000c1c50801c11141d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722428408 1250 722427158 722427163
    0xd0e031c1403041703040b040506060d05340f0306140f13081204050d1e020c010c020607020306090d03050718150c051009030917331801050601021b0103091103 70
    0x6e40d820f54180c4e079441c0a11050203801c7c06102c0c0c03c0344040326083d0820309166100e5031510041c60302d03c601e54001d5070162400c501e0b0300c445180c5946035a4080d000b607988400729030308bc4408501040d228940f4066103207981581c641c560301d01510f4040c09990195403000c20040441c403402404840802c1305100c00810300e502e0000d030ba4010303407084010308100506d481008011035440c126120706818602d034881c80d11038010807800d5402c00203281801103100b05002040c0f640c482da28000f501482070b101000b000030801302c4c0c12030540751a80d5082c419923784280c01c0b5000c0500703510440c1d0031421441e080000b0203a10f102d9400400341030401e9501c10300c90741c880f00e00305407117040300c200c03016114503104080551010f100300192140a003d400208030305041140d4841c0109510a41c00d0401412040141074005003d2810024601030408510b0210f00c0700380311004000210a0b55030074080860002d45c004030300342070031902020034898890401d80046001d003410180544000001c1c040758078564606 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722429658 1250 722428408 722428411
    0x90913050a0c080c0901180b06090a0603230c0a03020c011401080c12011505010f09090f0209010e0d050606040f060906031b1703040b0a030e0d0e031c1403041703 71
    0x3040d10b580d03001c0c50443c21900b00b509612900b4491150040140a03021440e4030280089400704000140004402c000c1034040c4102030210390320030401000015010340c160083c1c04030308803681030582c00403c00695100201ca0994510f042144103001c44000035103e580a0144215010004680418489901d0500060a03003141703009812178203110f001424103c2c2c4044c86409520700070001c0e0614144442903050241c014541004900c00c00c0c0c400407441a500c980c00b8100300d450070028852890803800095200300042400b01c0d141150b800b20070300d803000c562895035402c00058000faa503860100001001d0015400001c680c3d5541d0200e13031030a07a4410200950300c41ca8005a5010100040013200d20260703114a482140c2d150140c0458103002c415101285d6441644a0322124a03800a130050940700e00200c025200300802d012401d03900c400e02480031807080d03040d5500c1081c401604c0c01d03020200d01c3c2420105001c2c030000e07400c035000d10780255030250023aa00e41c01d0182100402c0c0e6a582d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722430908 1250 722429658 722429663
    0x30703120603020910060807020309030c04050601020c0a061e030c08191b02010e1504020a03030507080d020f070c0e061503060f06070308070e0102060403090e19020d02040807120206090913050a 85
    0x11304103040c403006d0f8010000d550006110b0000b1410b0548480c00669280c04480c02980266165404540380364000c01910700301c420020a40c60106440700b00080440514a440d805a4614104150725980c064400c0080000b000c0d651040725036075000c20810806484045038a10507a940c001a1044052103d0a11070de0315940c00480c030003c41507843d5203011841c0000070401a08079040c400140d50303101e8001c040340d0b81400c0041d240e5241b42004d01c881e0140450b105612800000c50100c0782400c80010700c0041e11810007400d240ea11075050501510302200c104c1c1d04150a0300c8035a000c0020100a0b59015100512565009000f20042100c40e085540100e000c2030f25131050011854001002c01c140c01420310082c0090b24103a20020034180c1584a40320b1400050310100c0e43c94a0191607071030b00307070003101030035555001c100406038000d500910500b20b481c001d08002040d60320f10404c230300d0650f0b5002040c66050551070000c0000108c0302a11900c1c9101c43d500420b070005205000c001101030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722432158 1250 722430908 722430931
    0x30a020406140a0b03161110060905040302060a0e0601090b19030305090109081f020304030c050708300901030c050d090b061f0f11070b04080307031b050307031206030209 75
    0xc81d14070070302c04103d101da000340030121000d03c100000780d0340004655051006c60f14000d03809124038462242840800d0001c207408070b0034514042014146a040325002e940f00c1d0b402c903011591069400b40444068203054081508a50010080060981c202c28034160000b0005406210502c903a807688400990003200807810105120481d5030f0000c040384010043c0304003801504c040140d102443c00ea04029011945601001050501d4800e104460329168403008030b036034141e202c5103140c5ea1886d600940341c0900007241102605001400d030a600c0c03c4900d0402c140c241050b800043d000740508603c031f40104442070090300028607181c00b420112900038041e0040c01e0a2841c288009104824243c282c441c3c0726030036014031070703900034000c180c4841306107060004404a40c018608050381c550012001d5034003c10085085074010008021b441d00c60341b1039014052825001c842c8400300507101404030f410030310a02000c01d00440d0190500900004001617481c4c032580084c10103082941c5000324130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722433408 1250 722432158 722432189
    0x10e0708220b091014090105130f03031a1206060f030312010b0c150f01180603020d110613080c09060a0806040b0702101a01090609052d04020703080a11070308010e06030a020406 78
    0x114030038416035402020400514041d09c1c0c0f5512003a40b08105c0440c000d0401d40c0d9018030103178044002c001c601c1892002807003201904100045c569492005a030220700c43c05447c4402c115610700002110380b51400c0b1000c1900c682c0c41c0440c0008150410713264084075006440503070701520b80301041144202c02e070306052170072541801107200e08030108a04985481d80b81c0701e01400940d0f2041e80c546101075110300207031441030001d008521b440c0140d141c0d8007a1854207510120b50b5041c04214a0031040d019110410f450791a1010444000b08a00c14187d044d040880460041500e005440f0b41c85050b500403100c81c0261180c0304011210036010082005220384201d41c41382da880305032840201558501100da003401c2200280b01581d4000c2042c040384680b604072244c100e41883c0d4411010b000900454a03801a0709010b80a8801154504001881c0c5210003158000200c140d550503601070f6a8095103030b00348280c004042e0b1001d000c1503414840d0400100044c0e0751402020301401d01b0120358200c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722434658 1250 722433408 722433421
    0xa0b090a0c050d0c0e0405010b100e0f06070c060804080c070f0806070e01020318010c0b07230708090111210c010b0a0812031b03010e0708220b091014 66
    0x141c15081d00100d2180202d83c0c80310000c80c0d041e82880b4251614421042c00310780340d51420500400c82c52901542003008045403407001508030704040a02e90094400d100c2080d52903003000402e10550000400014221009010303c2d80708a0605920503c100c1e00d01c0d14088410204d6440c1070b07030a07030110f00082e240303950501000d003087c002c10303801c00100d040a881c501107400000c1e48031302424010840e00721040c2d01c200000d80c031034001d02003910340010b6000301500b485500205120310031300408101030010134466100802c840304503804150484241e40c2008410001182c40e52560320702041148560000e000c00034802c070380398031940005414080d0b56028800e10890965541c0441700d0b125403000309003005900000f0555903103003c400180c3e03545d281d0751004204030702034251180451280780800042403200071800018001c40180d110950260f49103002d01c1207100310161021a1a0071904540700092004117000b07810940e1386d0b0a03640b06007640f07a1507104a45040c409031078074104010078440d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722435908 1250 722434658 722434673
    0x809210303161e0e01051215030f03040e0f06041e0e1614090406061211011407080d150506180f0102060103051506060904020705031201050604260a0b090a 68
    0x50b90714904180d42c02a900300c49080298000f01c841905005400724903911682c03050044038142c1d5440355011400e810b26810007116180f000406a02070302c00c82c03907858001c400000a4030212485091043d0030742d5903c1c01e4402d045840a81040e80040c0c4950381c603a604400c204d0710072680d41c40c400d00000d0b44160f91000f10b10b42000d4000070740344200961018803221100741588d112218041e10510140d407101c1c5030100080846500500680740040c2601c3c01f08038205902d0703c0114405da880e0050615000c1a0000070b02c13503c10010310080302006059181e1020303801454102c025484086d0f1010f1ba00c02c049005980f1800820002e0030003040240d1030340c50070440c0c1940800080c80102410360640e13490581c2e403243c4100c13105d148901e80300000e0b80d40c0c2d02c4400711180314901034400c1d911250280b41076603507a000301c100120028188800400c1d83d06080c030580341203a803a40c2c4c080050285425001e20200000c100c0351203d80101c108a00c04210700604503402080002d00800600742c480c1001007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722437158 1250 722435908 722435941
    0x3d0504061a1c0f050d080901241e0f0b04090e03070b040813081501090f0c0905010c0804091a011b05060414150c041e03020d0809210303 60
    0x1000d0a000c5199295164260b01182003805a40190281c951500300141201c2560710020001e200c3c0300c0544114951007100a4080c4480c803000303001c1c400d44003440643e22500503405150781c0101031000c02c4045016141c101d50703c1285d40d0f09900064654240740d00030b0030140c11a51010b0030019040101c0903081c41070104400302c00001e54202082a552102c01e49000340002e004441c0200c0c4482102200f4a81040202107040440303d2101e00301940d4543daa000340b24080b07209140803005441d41a290141c0d02c1040810342d80c13003001d41e040200541d8000351080060b1444a0148408030f469017141c80b8600d00090238112a0349a02c0d4214001002004480840c020a004a8810380c000610025415800c07070392145000351005404507907075103070007520781070300c1040c0302c0d01002e200c039040208004109603030031441621a44c00308084a244059942e10009402520f00ea0802c0e01103020346001c0d04111400030403084280b506500f074a010003422050b07400b9542c20000c140008041403c1905 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722438408 1250 722437158 722437181
    0x9070f21020a09081501050402090a0806011509061707081506070c05030607140f030604020c0115080607020c0109170f030408010c0206070e0f0409060f09060608060105123d050406 79
    0x40058a17aa03803c0c8407140003041c45414060354020412891550301c50990b0405002e40b90108ca101d5a520384900d141844101100c1c2d000c45c001803008a20a4407a94250128181280b80c4019a840c0c2c42012141540010550060201241654210b80e51000c00602070f090054185034002403c090426042c0076000d011203043c803d15850741172a034480102a00c1180e0004044240c4030790743c641c0860041c0c031401000100359442c100d02403031100c640598403030941d55040121000c540d2541402c3e03a54103d4a5105400720314170041c100541c0c20702c03004201c15503c0c21002e650b0005000919246981c0041d000034100385d441e1206104900c4d4104200c56010041e441c0c884013029042c1c0120b14107040c0c640340c0750b01a82c0c0b9420440c09000d02c5400449464005041c2004a05a142018002000f9600880c01d990084000001e001e1610807070404908031031002912482c000070940310b6025074100b0f240c1c001c03550070205006000c0c03130b90410719007003609184010600e0306c0c02d45010340450f14a48100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722439658 1250 722438408 722438413
    0x25050f0c010207060e06040b041d151e180f0a14010b180a0308160b0105090c0919030c06110c12060105010309140604210302070209070f21020a0908 65
    0x101449aa0b002515004a403000c0c00c200e820311400c1000b040591003250480b0031031340c00c001400124402c40321410084260010a0286541c0340c8c000012200c86000312059841344007800c0480d05c200d00540c1d0161200310003851410311204140000381408412281880741d180c0c241d081118030912401001d2840380c0d9001100080c1d8145041a0040d00030b00e400c0b24600780901c4035400c3c4070f0300d8111440006c2c40e040400c1e240c64940b8241c00382c2c0c1d8800f0320700e000c0303c0c9415907900018090516012650040d03041280242c14a10400c040c800113409000540921204d0b812000002c01c0d243c4140401500c402e564442241001215023841d100c1c100d0500b0b0b00464076003c40585d5031401050b1a8195002440d0100e81000c440c1070003072603182c02d100a0001801000f09100800610900c0d10010880c003c040d01400c1081d46070075000c0f070203400406500b110301e0302d00244080344a03521100030319a003410880c1c102d095910003040d0316851b2160703a510700ea50019002c1d42d076a81201070a801003001500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722440908 1250 722439658 722439673
    0x5090a170706080a0f2412261606060e0105100f03110c010f06080105070c0503040b1b010509150c0a051b01061802030103030e2e030225050f 62
    0x22010341c1c0e10300c50300c12641048200000b0850707250301c5800110b02c04140c040d041c8900c6502c052000013010117103034455032058a40900050a4082c2038102c01d483d0307040f41e4650380003440326040d19400c100702d00d100760068404001ca800312031030146141814034003884000a809040866a20740e0311418bc01a41c410304078500100641c9078072980d490070000842c034000c11240c0c20440045898010440003000330750a001008400074900d5024404540c103010091020b83c40d04c0d0001d444407940090013900c2900100802d111030700014008207042c00045070503e401648255503107084a80980e0440e00b1038001300285001229408507080d00a04804003003882d1226118018016105400642018859142018491100a52184000f480410796a08160303010341e1800d0020340c024001107021601c2200c1580060403d000114140c45080140030720b4181982d420600c0c6801d18101c41d0105a000c00c143e980724000140e14400c07144543c204003040341d60f08d00d0f010f401d2424030b00218000d0f0f4003110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722442158 1250 722440908 722440949
    0x301090b040b100f090b040308071101030c050a0c020a180e0f030c030a26040c060f03020f030c090406180e011416050705031215010201140603030a0509030c030d05090a 74
    0xb480c01c02d00d440343d07044c001c4410850f540103850405160b807024001c18030102e00001070081d940c0c000d018040c4190b51591440d00d80500540851326000300400009030140590300c1039501421a02001303038002072030b40e014107548001c0024004040d45c0b000c001c41d82c46101c0f1554100c020003510f07496141c58406981803814894a913035690240202d48000c014141000c0300c08030505a0700e0100f10710320026281540e141c03608103d40419094401d410001c2c030070310ba10300d100c3c621900c02d0ba0358442105420358a103444044481c00039401140c40d290740700f50395842c0012504040e8031441803004510402069170461480b505007114001c40201582d0122801002034110040841c0c41e0103141c1420050b0f00c4401b681442e52440c0941902004c0b00d0080d48148801403541d91300e0740b1400325090740240011a41c503c0011580e290960340301e9055441404800300d458058009000800f1016085451007940302c070009140524110703100c00461f01c00203004e0490b00781f8030b000b107014141d88120420202c03900e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722443408 1250 722442158 722442169
    0x601030b01051801200c01080f040b2e03030801290405090c0f0301140a082e0f02030a020304031e0c08160b1906090e0303010510020f030a050301090b040b 68
    0x903650f5441103442100c00440584c000c10346448810840d0b440780109441c19040702d03642ea0004440203000c5082c100000b0b4014010500700e80c0b141d81d2061012505840f4051020310564024000021000c0403048a507049840200c1081c0210701940d121840b6514064001c0c1c0c900e4081d8421482c0c480403c041c00c02059202002c030b074100c03203007540d84141ca9135903400104180d001e0130f01c280103000c00000001030b10b0b030074400340100351002c00c076100005540e98400882da1610800301c11400c141d07580b03511502c01c8021107002c0e50740001c0301c20085032601ca0b80146504036030003180c07050900e607400700030b00040c140c2c4803000002031462031481c0526070102e040054940c15402c2001011660001010b82d1041c0d2141d00ba144680d034441e09819050418039100449480d072000140703034170351030180d000500044601030410440d98a102451969003004144440c0c000200072070802c2d48035070f074030f041c0e0000b2040009201d11052130366026200e505000b41c91058840071048984038604010b11081c00b42d80b003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722444658 1250 722443408 722443417
    0x120d12090f0c24091401030b060d0b1507121107120305040e0c04030b0f0c130303030507030b0301201b161401050a0e061303050607020c030f0601060e060c030904091a0601030b0105 79
    0x40d920017041054031100124080c05503a0845130b0410741c0031641002d0107255801900c1c0850044544002c2c11030700081e10304c01406401d10162202451380c45e004c440a0140c2043d680303c696410039202580d84910124131a80c481401c101c002401c0024204201c03103d074141d064200c1c501507007052506140d600c815000d60400b40160244a003640d003c6640e00240300c00b2159640c110580c00402c2d80d9803414041d004200844045020a050000d442c91034a018400e03505094216040c500d40a000024200072503005114a11030b80d00400026000980c0b041081400c114610701c0d5544129040c040d98051001450604605000061205421490300050b15183c18141aa407050300ca10740c0195902c00307921254005801c1d400350742e00340301d03c1c07550200d034800b089002941140c8406c5040d9050303d03030ba43e909100388000985c48100002551030018000c0c11410148001c5900302803082000030215150203404594504c0400c2c3c075060f024480c80b400303603400302003420100801c07110200041c0480c0b06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722445908 1250 722444658 722444669
    0x1c0212030c04050d08180a08030f0a0201020d020c1f061a07150e030d15030b070c02012607030614030a142a030c120d12090f0c2409 58
    0x400041c104000da00103a40c002c0200030502d01c0b0010b090b040c8182c02d44d21070342d505520b50741c00d11302c1c107441824202040c1044400f0200250f10345400031a4a2515400010083c4110754080154589440c1c885c00a040306070b08110160901e00383c7e15400300e40360965100c02012040c20002d080050340c4072949100700038084144000e85e0780c10b42e450040c14040303c0c200c02c0041c051400101c50b02e000f900002400701c46021413400c002d40100041025a80d14052200801c6107403401d00003412548a210340c001010302c10b0510400c81e0b030302c2c1500c0040c92446001c140844030741d04820070001d240e050103408010700c440000307205000c038040c01098603150041c001a1216144040030306188404000b500001f10354444010302c040e808404100080341d03a20203070b40c40f900c24460417100d107260a8100440c00c01034100180402d10812105071a00c072036400340d005007280da400c180c0d804100a20b80a0780d00621a0750910240760800c2c4020354a001e40c1d001c06149101d00e2100c4010341a00040484144c54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722447158 1250 722445908 722445943
    0xa0305060324060a03060e06062706130608030c0a11010f081b0f1201030204060f06051c02091314010e01050d030804140d02031c1802271303021c02 65
    0xc3c1c0f1000480c2043d411035100030049441c04c60300104103140829500d0040300b0807916500e10040e9101c3d0114004101c0d4061501c071991440030070690304c0d144200400c024041e200100302646c2d562410350840d040700c0398140c61508404160410000780d0606010001c000f402c0066042042c03041c002d09824004040100850080003890184120081542c0403900c1c80e040350341c3e540802c500744403200d11003848203d00850408801081d082c04000d640d00a60b5200c1d40c0c0c103824070071a645502443d01a490080c50b05990030020711299440f882c2076032801c0056040c0201d0b220b5091801c020200c003059103c001c0c2103028030010302c040ea460404001a1503010b2501035040e40b00d80c1410100740780d0000107240d851103a0804000c41e00d4010014041c3c0e0f108001c3c10880f0351144604800c26510340340b1114180c0250340200c003005141c0341400303082007500070740c0f04410041c0d00c0c40400030102d400d68802080301050505a01010360421413080880c2046c1144114003000d11006135440c08502180d50550303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722448408 1250 722447158 722447161
    0xf09020d0b06160c090c0f0f050910080601110616050a0216060f080f070207120602160602032208120402010c0c03120f03020703360b0a0305060324 65
    0x414650001c0040e490020300d072940c1c60a8000c2540c1c9540400a421122030045400002c0c2c0d181c598071926031120100d0f118612180440502240c0425011944c4020300405000403502506c13031074030385d007922640b5803035030307030389810458000b4009441540d4030442507400340e010010280044070195608101d00e040494458020400580c1401c0004000ca5419031506d14002043c0b94052050040d41c440758a56076071584403042c003000c00b940120f410348096072000004020030b01c030340320980c002503000340001408e090a409010561200052040d0358594002c024410a14180807404c0728950100120a078180e00316610f01829000b0f907441500e1209031100010309690103000440c60703899025401000281d22440c101e03045d000c11150300d4001030f60b500002080300d0301038800c0703405083d0191150514082c81a100308010302c10101c81c2d1041c0c03050291290280c0c1000c4150034080c0a08604c216140d07412000e0040440c0d000078200b034841e034840420004130707000e100b01800d16181d802d540360310380c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722449658 1250 722448408 722448427
    0xc070c0b032706160c0c06050313050f06010609080712060b0301060803040e19050106210b061308060a1104090b01050f0304030807020c0609031e19051f0203010f0902 73
    0x1101c510b11903000c418000c1c40b10084000c88080380d19442012082c110400e42d02d444913040f510b1761300c44a030041c105403101c6c03404d220250141c0041c44e40450b500e4400c0d050740009a03142410086030880d640c150382d014074010b0000503040f03c0031070701403c1c030b000040145610f481141c1841c000040d0700540840d41e50f48180d0019282900080043e010350000c0382d946682d1000300c88224002100e20f0740074507841443c03c4403034402c1c0307024a5048a40c00d5440a4031003040c00b101401c01c50002c85000c0c001541d541101c1ca02d9260b004c003426602040b00441c0b030718507141c251054204500248400030781231400c40401d011444070000e90381a10302d0885c0014401900340016101c41c442d030301d1a00740d42e41d0003008100416610058952044510b0380c01c2da134091920030140109c03401080103090340b5400c45600441d00b1070f0624603a0000c0c04a0004490101841c09082d070132011504109481e42d410043c0303440d107420380841820203422510b5104515641c5010019208605140074800d1001c0e00042ca9000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722450908 1250 722449658 722449681
    0xf09160b2d07110f01050a1d0a06120608030903030304120c0807060203180c0f04020c0c090703230613090201180b0901030606030e070e04150c0e04050c070c0b03 71
    0x41006411a5501c00001d2501150040d070400442283e410068031221501410200801c00101c24103848690030003440500036180034500e1161004490703417880d030951180d40d82c0c84d80380008003000d031998502070801c88a81c00c15624030ba048402550300801001d000c54400004a030f6005401c00e4051510010400046a010f00c0410019081c14004210b540622850742d00450169a01401076550712424400075074441c50b80e00f02c100c1d448692074030503200c1e0303040c6074000b041100403050680312a10034034000520400e000ba00c84000103542d40b608006106600604030b0410405d16919012602d02800000d5002e2040407458241c2e58543c0f007001c0459000ea074401418081805404030029212901c002c15900304124050000c1d041c001700003a0700d03000744207481400c10070074064640141841c07004807480310044d02c11514045031459283d5a80c49500c100810030720140e0b40c540c880c41c508070410060314000340003080e1078502008032070005210820048115111699183c0c0c480c0d85144d41d406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722452158 1250 722450908 722450947
    0x420030f1b0a090b01020a080d0e0307060f0506090415020f1207180603060b16080f030405010903020c1f0e2d03070f1a091909050f09160b 61
    0x1000c5108001c0595a8410100c6408003541c00c2078030780810065440c218141a180300f0020b25015800c00c400c940080307400803004082d0700307504031808103108041140840c59980180310503566983c0d58044098100000c1c0500790700b12170210b480605504058481c607003007445410001183d05e0340092010031140501083d41c6610b52145507031610b915002e00c1c0035000075908142d0402a500044012072424043e100d104207440d0209042c5040141c140080b0030201c9500034140c0d100c8805018120402c00341400440c41188241300120f441c034030b245006454004940c0c245403207596001008150f02e12115650403050000b0301c2c21000c03051903100403840700c0495155650b954050340c10002e010f04403c01401460000c113408035201d181c0d844814100180c801d0107103000c2c01540c541c1c0d4080710703204680504080c01009107181c0005140300034900c4120102e90011b01c0039504c8404100b20140d102c401c45501c40141005401c0d401e4500899030b00d10100c0d4081c04001c2c05c004140d086c92589184004c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722453408 1250 722452158 722452183
    0x60c0a021507111e0304030206070c03060c050403141513170c07030b0f01051507050111040e01050414090325050708010203010f090b130b0117100914042003 69
    0x12810b08203000014218541002440e0161103442d030003800200e04070074400c1d48000100081c2d8105801d540c20852190304c080015912138101410200205e16980b080341c0c0070700110385900b50b55500d140381184044422100500241e040b0400c3c10080c1c0c4501511158003000007017061f0179901903450700501c00c0c202e400b01f95400b0b01c4041011065508000f42060540c3d000d0703084c3d01d00ca5580c0d92400b1440034824015650004100c5e060708a041c899030001d440c0540c482d900104e0303000101c80807014582c1280d400440e60840360401045103042c98031895a09184102a41400b8070705121038565034440da0002801c100000248850303402100c14400014503031190690360308030f070380302801c9000c1c0d0002c2c040c00c0e03200004144001400081c0384529aa1424060038807001214101280720080884090b01814400392000100c1c2d1030381501e802c2481020700070078055046040005c1101151503250403056814210028000401c001160792901441820300d6601400817010200c2d0070081511082c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722454658 1250 722453408 722453443
    0x140d03020a300f2d14090a171606020715092301061a0316090305062a0d05010312090806041e050d09080d05071203110c072705010305060c0a02 63
    0x481001c034070380c0c482c2d10151440d40c3c04c082c024480e50441c00c0782e030400140d4804405503c51100c1e0780000f1940c03020103244540010125083c00a042c07600e1104010190040b503085500180701c908215520714030150303242040e01d003002105859a2100b11140c541c000b56800b6038001091704101103402d40001c00074191841d000c0c00344200c0010500b1740c6402c140c455541d0458011240e2110621440c54803088a4000d030050003142c5990a00440c0c84000010041200110300050920006040003c0c0b8000d50000d030000340039851400d24400101002001d2010002c419804201038440043d4081e0026041160140768442101d19000d6010303014200130301034081c40c4200a42030f40c10040307500c126001c01c07081d150000401c004c02c13641d9114480d8014143c811998214400b24401c0e4441c0c4009050b007080d05107445000101c50f442c000c0258400c00140503032009a0300954401a18604000e40ca03003010700695046684454071144014484d480400000c181c442c1d0161007000528500004002c0c1d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722455908 1250 722454658 722454701
    0x1d0a090c1203030e010e0a05031602040902060f1902071503020c010204050910060e060f0d150302130209120106210c0b0a09030b060d02010806010507140d03020a300f 73
    0x2e000d0090000e43d00640f10552034004140005180820a030904a521101a601d41003d090305200380b020a104180e1300160381d01e054070010b13229100100840500004066200c003504645141c0300c0c4103010405046402c040c404000f82c0030126841d2020403628100981c440b10f10000c45030080c051a03102c192b0094918050080140c900b280c1c2d0002d440d0f00c1d40c3c843e400c42c5002402c2c0b00f003500c240a600d40c09034100300724600b125480342d80701071440000513070aa000151750b500045e0024105048a00582d44c0c0041d00094a00c1c2c4040980d80d8000e0050007408254680b000e0025001c8034080e91042162000c02542c04001084040c8000f800c0c5083c901c03900c5003c10751004144085a000858000d0092000f1810515000d941004d40903416910b41400b0341d5400b004483c030303400c0f802040b508038044244c04c40004100f4099120408880e9800580b500c03000e800080c0f0480700f0140e128441c070102d400310005040703020504000000c1010012800c9108201c2c80350007414280d41001c5040c45408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722457158 1250 722455908 722455913
    0x3022103090d03050a090816030b0702010912030b0301240308130914150402120130051506060a08060108060a08160608010807120f020307080f070303091d0a090c12 72
    0x42d2138010b001d50784100c06241c032500c40c7e6960b042450305083c001e0300d85000400001e258208541c0c1e124445100108071a5090b6588100b901c8103d41d880d00400e4680301081070905007441610240500060311203108038400350714040420311800094140c0400060390b8844c0c0003281501c000030400d002041240e22180c1140d000c41c5030702522604106428541d4502d00d600d090f000b500c24140d81160403004a0b440c040e014240e41c4140c1c000c05038a1501c90b01140f960000d16041c144070140a00090202200302c032401c410790321401071680740701c0c1c2828413081a469620010329039100c0e1007801d04402d19141c0000182c500401e6038009072240c800c0f000c0382c000f00c500700000c02d8111082c1d131b210958180d0325117011315103401090285002c5256035184080c0171400d0f0b2003010840b540058165003c3e1034640000a00304003114140c480d01d0361120100b00109540f00407488021320714001103440003071460964803a222005807003040469155103610052184841c0381d10014101001c0b00c410500452 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722458408 1250 722457158 722457167
    0x1804030c05030417010b0609100c05071d09010b0312030a0c090513020c01110a021203041a01080601150f0c03180e100303120902030d050304080c030a03141003022103090d03 76
    0xd06907a040d500b000c0e001c6c00d503401c0076816141301090007012881c0e58104204101c070901aa520141c03a01d11505200081c3c20300b4540607404603460019a101003403801a4110f420b40f001a156640240e00640d0521400e0103e030040c1d80d0400b040d40004108510145421201c401c01038100d02e0f440a482c4141d41e2481095a00810182c0b4640000b4040d17800c402d91008a1800741c6a00140907030040b1b030b40342c42148500c9000f1540180f00d03034662900349088a5480c80003c2c000d800840490f800b030b0005000705081400c1000044c0c501380f0b80391040381d03c00000180901d500e10001814040042c000c0e4070488084a4880041c003e00030f024105850540c1e00700b00c1c0100701e44803d402041000d2492148007501c3e005005200760081c004003903194800b90200d07619072004000303940e00c030401e026040c510342c1c05100519094015540c0454903480c0090b071700e408105c1c0500964082074020364104010384803108400d842941e000c84280444881200d1542140310318030313405a11424038084e075400c15801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722459658 1250 722458408 722458439
    0x607051632190b01090e031c05061c021005030703021605010b0f03032809082d0a0f02060c01060e190c020303010b0403020d030e041404060c0e1804030c050304 70
    0x8100455000c0340c4007100100756203a0ba1200a00004111401845032080e0342d08201007a1922408603440d040104402681c4c0c40d01d081420280b054481060101c5442c21016200880000c1c400c1980b0305040c03a030000c0d80f00c015401d03601e070a000d00800059146802581034070202d1801c20700d2440d6000c11403034514000c042071600184101541e000c599440d0500006503200030042d00000020140103003802001906d103007039030a00b000581040403031550402c3c0000c41d075804111034041c021810070743d5801c031402c201445e82c0005912000e89600400c9035510401c0107180c054a015549200810140b40500000d0708464441c1c42403905001344001200b40c0c2001d02c0303440c02410400408250030407a2284400e215a5500714018003040c03000d45130540781c40401e81c0c428180001e41345080c0000c5400c0c0c5201c00392826440481d031007000244402c3c1d0248180400c02490070241404024000844c44030301ca42c4c10010308420b0500180406000300d43c1c000d4102d03000011203444583e1070307001c03000b0001c1c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 722460908 1250 722459658 722459753
    0x2040b0a0e1807120f0b040807081201080601210b190903111605180a02072a0e07050a030e0a080309030705070e07050307030f140c130806070516 64
    0x140c03c1c0003d074468000c1c0c600030070298003040300500a0741c1611b442070000c0015005580014041002d6000110303210010a803000d12240c1ea000150b00d81480c441c2800c3c0140d0011200d09194a0a0350084121008040511358000040d080302d0f16040e8407540d02c580c0c401c0d09041083e103044c4124081c5074000544015580001045801038264611703030407a050494400c41c0e400c4400c0001607030f583c40c0025a8240d2001038000014100481c5484000b0070f0650101001e60702441420503402d184403d055860241ca0056001540c9090010000b0003900c100c05941041541c2c6150881690000b4000b6000d981e070403c5d121512800d045007059202d500c03031001210944101c1c60009400384604401520941d41ca4407082c0c21030b07803080020380181200315078980020365912068004c503211070450710300400140412545420040d45000509900b40c2c2103198254000010051416030003012074400c1030901d00503940744c0a0302e00d0703d980c10001210035a0302c094502d6090400784003002140607080c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 722462158 1250 722460908 722460913
    0x408010f06051f0f0203090604030f0b06040c05160609080d230912030702031308060106110303060f01180b0301060c1110141605030336070302040b0a0e18 68
    0x299140100552150583c00710000c200d94010240e040c103008116004160b081401076074a40a40304c000204564086d800c2180c0c80700da058140c2c07051119016601d82e00900c1500c04115075065400c0180071801610540c400322007040540e4800c005064020004442d400756400707442d10f0070a403454029080d280084a10350841103600101d0b03141d00000c460140c2091400b0304030180002c1400c003c84c1d40001d00722000d6100400c030080c0c021070218104002802e0b4171000d4158ad504141c0300519075040392a841009500c02d10038000c0b1580c0b8400d500c0c050060908190a101000d000a4008031550f41c0c04030410000110000035102e4004d00c0080c2c9d0503108681544000c07013080300700103e000d01c6048101c0003078101c1c3c0541c203101c2810340040c4041c00c0e0192134102196401d9841e94910b900849487c8540307601c00c607551072280e40c1e8500240000f0600c620390101c100c0c0345606150380702118400030307220b1038445440090b507403100030100c00a01100003001425207002d402c10180c3c2d8001c03c00e410300d02d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 722463408 1250 722462158 722462171
    0x5090705032a100806010c030314070c1502120f09120a020606011b0b0a050402040b0303040618050f030d2a0f0c05010e0a0e3601150b0f030a110408010f 67
    0x5140407160380c03d003c00c840e2142181911001c00455503291342200480a0665a442e140d4a043c82544a44e00c19541c95a4540000d00d061801c94050110041c0001105005009080108150356003055000c0e540c28506403d80e52072010b02c514281d000c940710045200005610041280c0c0840e01511410080c7c9816001c0e40158001440048032214041d04400380350307010802c008000c3e040240c00c98002040400c4034000c040c0000d04541c0310342c2c405c4000c0340c098020250404801000c0304010901118403040043ca58400310391980c20103940d00c41006502e20b01040219a0207010020403d0034807030920305c0300d1440c80c001c0b800000c16102583c0399200350b14005400d61043ca180d80e0448400b8040c441f055103030100c03462043c1c1d030140285074006450444400c0e100c2c0c2c0000c1c10312928501c4d521101823003007181c45150031141c2c130340440151554031020900a000114003210700d510081841503a595079400c0144000b0420700d10004200d050005d000124603005400c1051306080c40c2d00c007000710 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 722464658 1250 722463408 722463493
    0x30702060f01150e121204080c040b04020315060703020102040305070e060103050a0615050702120303040809120f0a08070201171906171c051e03010303090b090d060509070503 77
    0x104a040f002d0710000342d2903149a010768208210900d03e10380e980d4003180da80038030001c14030401c1c0e003107500000c0040e4428981d846407840c0902132861032450036181140b56003050329005c0c008200401d03601b8010000050020100b5200354101e4004540090549669584603030881c0403405d001e4448600007414003010032600b003e10300c1a0740c00c82d1241035107041308844408007580c0c2c40e00100010fa81c400d0910205101c0c0600510055100e5441030814995070ba4010007003101155a100041100f580408400300c1681c1c400a01070420720341004000d6110145440100c41103070401da100544506100305001060005415803545009400d400b409890744400c5240c034202d001d004098070581c0455007060754003c0d500e000b03c00080443ca03103146015030302c0255071865564000010481c2d0400401001031562080300d100162440030100f41c5015050030001e200b450700c045010b03007103a41c0c0f04046000e4010070803500c0c00815020382900c001040300c40c92000c071070203084411044240000c121009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 722465908 1250 722464658 722464679
    0x1401020105070c02010f110f0102091c170f0d0c0c06050a110304080309010e030708120601090e060f0f100c051204060203030c0c10020c03030412140429030702060f01 73
    0x100750015614a26001c0f56500111440c00801c1201814024464100100d0391010300566004c5d104100000d40e80e80321100c14030152102c5c5e080c02c004ca0600850900d0001401300805209940040e84041d849000140d0b0041d00c03413040081818159107403068042d01150080d110b45d5a26008403030030411036480c465641c060752049802c2d8141d1311001c000107000100144042c58204104100010f051405100c050b855940300c001c0680350640302142d5414182c0040c49410360180717007807a241000600d01a0000342190014110078403c105581741184551621200c18144000080c0120b00c24018404080c20001c40c92505442d83d00650a01c0070b170a07410030f0221411a08240c2c0210b241da50f50b966040d080350020312540100b03003d5101700540c0c2e61800e0014100c4002248043c6980b428645001d020300010300c11440180100010300b0803000100c4425503048408801c2d6844803c0f4083d6206c4000c40081c0c0d00e0805211000300c1130003c00390f8009881440b1f50000190068140d0f2654803243d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 722467158 1250 722465908 722465911
    0x1202040b10051b0f0a1a01080102040e04150e0105070903060b04020909220206030f070e091b0f0412060204030b0705030f22020306093901030b0d0b07091401020105 72
    0x400b14204000800740100c1c1080062181d8604400b910f088040308414507040c50504035040da1030302c8500304e0412566018006040c0100b01d4000214a41407918882d00384005006001a11400c1c031500300550a42d0580c01007104100700d82c000b04210700d0002c001800c20b1116000a0781c0b22440d2035404801ea0400c1d100310f400018000b4010011642c4d07440352105580f1401c04205208000070701034200586401001c0c60082400a00720304542c60f200b07800908040c0801140b91042c01e03180144a020314031a40700c801c40420300d0100c10780d115130402c83c032083c0348030b20340c80382e0868007402440c0b80911005901070030969100e60021070036a203400b803007161240801d4a82d4125414008007286560030003c2c2150303400341c0c10400000500026400007030074844221402412074011402c0340d131a408106071748100e081e200301034900301e951720130550712a48440700d2f08850501da5268107103116035032142040c0340815848402800a86010080200903035181d00c41e403102d041000010310303099801801190b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 722468408 1250 722467158 722467189
    0xc03061e051e130203070309141606050f091c052104090c1710090c0c050303040809040b030a08070308010f081f0e010207050c0f0102010e0303070809070509011202040b 74
    0xc40080c82c1c03103405a48982d1105160541c04980080191003002e9540051132150480b078400085d00c01081c2030405015441201d80304480d00158103070040714010006060a030307680c5203403490321076041c14200101c0e482140c0303c4550007240e1460301440d100b070200403044207500c80c105558000e180c440203444045e5104211100581c2c0503c0140041f03021070f403102d00301e051540b4102158940c00d040c441010041550f8020785000c000c5814006081c0c01d0143e00128803443c6010b83c9903440c141c442544034000980024080800003404051564403078001c91101c4030000c0980f8049441494034003c11391048508901281c80040005502e13110105040c1c00c4904c0d0902419000003d401079240030081803000521880d690390002802c08824800b034210144200005c10018502004100c05c00140b5180607045a0400320103440381034000c01500d03009581c0d0f0501c88050b071100102a82080d12640016401060b4400002041c1c40040884464540259030421101000c4405e0146604461444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 722469658 1250 722468408 722468419
    0xb1801052407060f02160b0603010b0102060112080705070e090d02121e0c0a060e0c120d0e010f090503011406010e0a08060c0702060705010606020601061101050121020607060c03061e05 81
    0x20501159098004005889131007200600d8040d910351080c0344043c507400b06407065001c207020450241030900c00e00c44040e90034002422150315140c1c01015540c0d80101c01007009001107803003c2041005c019070300260515034400301d01072600a020030741c1d42c01a180d61a00612a0280c04081750380e4910441e2400180240ca1190034918800d0020180e8001d22076240c0314400e0f202d9030030200e040780c400c100b11042400701030b01030172840000700b0100380300300d44580f4002d8020100400300f1a4021042010f001d400307007004030380103080d880140d502c020503a00268165003403526030b81d100c40c01c0100451082c0c0c001d0b00c4208800c1c07404414414000e0080c001e01b2041c1d0f004d1008244075080035409070030224030080055103456965a83c081c2500c5248e845200964002c02c01800604c0e00001011224464600200807562400c5003140b0390010210521030518403914845080d5280e54003141d11440d0071100a0041d00311601e80100141007074030030f441d90b225103485003a6511803604140001c48400078407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 722470908 1250 722469658 722469667
    0x60314010b220602030d0b010509130507210606030621230f06090606010513181b080f0615030c0c0a0b010308041d010b1605010b18010524 61
    0x501007807640c0321480c0c10800e20160748207025400d04141010019104950203180c0f00c0007211134940690b210905441d040c0001405075030110f4548420440d400f0501a102060b1038807488015a020302c915144c6280038540209000a121b04c507030004c000702c03105540d041080599840d0084e14440d2280f1010540001c0c030600b15004ca03105081850011441c03036402810005800c1249103810083c80040d80150004020001100d1040c0030865011800782000b42c50301100701500081c00d0707074600403000704101003d06145400da0a6020240b60070002c1c03180081d1841041004d800f203141101c5107881c0d00170003000144a82000102003102c1d03003107280c40a00315145d5030840c0b21103030005204050148910302203280841c6454140900031401401a1680c541c20060b031503040541002a0b00c0840903030a00400105044404445030540200d10185103400c842c0392480c098146035030080c0c0d00080f0400c4240780350000192081c1214012071342d12040c6510000d03000c0c010500e0b501100c1c2d40c04000e01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 722472158 1250 722470908 722470919
    0xa02040e040b2508040b0a0606120c051204050303060a150e010e060c06040b0f1311060307030b0604091410050901050105070f1211010b010206010308031f050306040501051006031401 80
    0x10390454018440201c07040071a01007101100700070000f0f04911000540b08030900c003e004d20406116007280e03054000303200680c00e240d4090036100710b8042040ca4507a070381e054100741502c00d01c19103412040e812100032603418242051556500259480351085618032000500c48160403403190159860307031540152480f41000550f004c4840b0390225401c40410403040d0558001445120310031480f410500c1c1e06800e14030004141e0741d03c01000130740f41d8807a0400410104464a4021020900464459999650b091001c0703000d0720f012190590009404a00490b0701c201c0360b000600c07032a03201500e05205070346404000c0079441851241070b23001051600180842c1d4429801401103a004508401c1041a20743e40d43d84210003060280d0300007480303400751705d0aa04082c007903800d000b0340910040050f941103407100481c5201c05019010101c08010925544e4810700300c10304010031006040d07414501c0e144c00c20a018060031a0b00003000185000082081f9010b44170f41700c0d0540d50342002448aa0a20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 722473408 1250 722472158 722472173
    0x1101051501090909020120070303080106022e09050a06050702101e021b0d0c020a060c0302060a0f09080c0322030c0905060103180c080d030204060e040908090a0b03010503060a02040e04 81
    0x13060607810061600d940246688484a5020045580800a020340b034614100200003110680020045406c94080f913484a4180b03454000c07021188010303050f8007501d0a180500078a1411402001c034090103c40030180540341d0700c0a8481c981540035103400c0c030a42030000c405c448800001006d40030f1080c10312414508a175001e00942440d00020801c0507034040d1855281031a0b4001d0f120004542001040840c00c0112045004010500300240f41c0040c0eaa000703511141c4c02462004a1907860b4a03035501400319030010000b0035008818132740d9400a00c1e408949039400713482d519416050080c5003800900f203102c05541142d402a0201000b64200890034014090180200741016103d0742c1e440e6664003009810b0207594803034800c001900e4601142a414100303070194a030107140c0706000c200709580d0004107402c1c041c1c10468000450b00b01a1808030028040c107840b46412440e104004120204158002c5042c0c071001c808544c0241e8030014090300382d1065004a0140d248160b000c5000100344c2c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 722474658 1250 722473408 722473421
    0x90c080d120b1c0803040c05040507050d0504051606050c061b0703050a051e0d050609070c02060c03040e07020304081005010311010e040b030d17010e100623040611010515010909 78
    0x1003042c03c0c0f501c4030341c54100039403401d01002c0d1039056002041c4010840d51400700700c000c0a081d00e05000a2810074809021801882050021503446400240801105002d004982154581c0e0404010740303c038001001c64000703c00b922507a100721004100240c4105284400881c19050308900d064903541d0216080c0c0c00191018040c00320034011700300060b27003500c0c03040e2640003c050019191070300050300600340d40c40500b00b5802921000d00b80680c0340e070b000782031800c001d07010b50348699031b18507842c052486c62289520000309002d00005001d51590b01000400c00c0700c0c0c003d8200c031150325401c60017000302d0b0f50070721008060507884151162a9402029040c03281c80005100141050001d00440d05015000c2034007400640e60565105076400d849151901401a101698403d881d0000c2559a035002c01d014440c140403160500382c0480f018154101c80e040300348030b81507850340c0d5100e0015140b440c40380702c900b8043d4280b80020f01407410400788100d82c164142e68080503545401c9030140280305 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 722475908 1250 722474658 722474681
    0x21e030105090a0b16120c111005040203030406031119030507021011030601141b06011707030c05211b041416030209040209030102040b37051b0a06090c080d12 70
    0xe03022031075244440c030b47c42086d0000c0260303100e01d107070180800551818040752580110039140b0700030521002da1000810b445c06d68549080001c0c41012441c2c0d0103044c1d01030401103100c4458128036503000c55600d500103501440d02d80d0200c0702e04458900324681520365614804450300000e00c001100c1e03612a45180403880c02d141c1030280342c0841c20f007600140b600a030440c1c107a1540102e004100382c040b01846581100b0070003010740300b07040c21903582541004042c03090303030301c00e01704048042800c212509031162501720140481ba118980e01c91424091445048446e00ca18903001840c44210700c20030f601841400d80d111094041350a000065000f9042403141541050342441210b1441c0c500748000d0010b0104900240d460f0b0fa007901c040803595103c2c002442201e914107011030401034102c000c0c2c00c0704003078505120f51122124420f1140fa0304440e0140303a03191050020401c1400626800000070a0094080e00649600e80c0300d032a80e41c00209078204009461007001100e54005a80710020904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 722477158 1250 722475908 722475917
    0x61905070903061d100606020304031235060f21010e250803070203030417101a0f011809051e0106090603063f021e030105090a0b16 58
    0x36200d0302d482007200ca0480040000300441203014000f140304000b09910145d00d00d000740005e40c24640000c1d201c0c011840001c001a102032140b044180c003c034140041d410054500071000101c3d01941c20494414030405c80000d1018404a101c5060500b000b142c0c002024041a01840c0180e5180c0c510024503060f100580d582c0c3d01018008107024002c1010f10a640c1c540c0d034960090540b0320200f0240c2650180001da44200a500700507140801624206d50420324449907003c3c40c0c0101a0401003040140e0440ca442d110800032000285c0e0881e4103000010349d046401079080c0d20040da181003a81c1034407074000a1300d58007004946219000039a01c0400352082c145208400c44513900e10f40030a0304101c0104500900a0040c2c1c0c0d410b00c14200207010300d1010001038440b03040341d0f061951088600b0840a40102241304000d03100ba16204a4107601406421014104100c0207401090f6000420f11035400d21002c50340410b0f000821a14194004441c0012504c1d1001101030901c82401c1500a00c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 722478408 1250 722477158 722477177
    0xd0b04030309050d030b0108010b031e0a0e0d031e2706061d09060703020415050f130b03060a0902041a130305030c0a0b070f0f03181707120206190507 66
    0x74004d100000014071030391030101c1c0d00144180007400d140c3c0141c03c5000c00704018810801e50000000305602c2040707903494501d00603212544407801504080d500c1042c14400c49070851482d591650000c280c08098280b034441210211506009540154580d120b0b44040c0c03080c0343c107604d070015003e00da0f801c0c030a05000501302d54418800101d2813602c0c4d191460380c0903040c1004815442484a2940580710b440e0440c58a810711805405030406100400e0030403001207000e0b07a80540c1c40007243d000513400c115902c1c1e516500d444200c81580100e80c420b01070340d0180e90018500e017240c02560160f544202c0310200c41c0090701803200d415084401041d0030a1580d01001010a074180010060f40c030408010f0318506c440c03414008041d03e0060b11410800c1b0003d07030b8641d1000e620007804032142c1003614000c43d555185003031114801342c003414080d0100300c40e071002c1d0841030100c00041c810541b0400440302e20b0140e1450a0703841b881c0c101c810010101c1b45184240001c2c00c0b0b50712442e0300507007500f0603440c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 722479658 1250 722478408 722478413
    0x8030414060703140d200409110c1b0607060e101b0912060212010803030402010912020d061d070602160f051c0204020708070302010905060c04080318030c060a050a030c0c020d0b04030309 82
    0x18a0280c0c62030382010600007014000304019002d8404010000100c0d50705cae101d0642256503980c04209410340840b05c00d0080746078aa942c500803250b501c0d0f0172150070300240e00c020004c20345500240c0c1c0d000c4407482c0b1b08119070440d1003401c540740a0102607900c800b03420903d0285000e00114403c0f204544156003007008180f40e42074010301e107000e0480c103c02951a0300e00383c400500344405075000416204050300d0f507903006940310501141d20130380c07003a0040f0350390171014812486042ea1904070155406008004903103290700180d41c2248212001102816650300c075584440f0ba240c9000b550340001d540392801042c0e20400f030591700028405840103140c29016212080740e60054001240180d4540b02054140300c2c00308034154112042c1d20100b440c0900c2d18a00950368403e4a0742440c405810390b40c400c5407960248800c0344845405801d141e5191800c00c00181140c1c840244200401d1030408002c1209114402071601c4c154080c21900031401140c0b951507a03948010011402c06841c0c4001400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 722480908 1250 722479658 722479691
    0xc091e05130609090507090b0a14010e011707050c1621050f15180d021b1c0b1609081209060d060e0a061d0105150c060108030414060703140d 62
    0x141135014101804d5581d041042e00780550b0401d51640d4404d82601005002080548110070340c4241d0900f004018401c0c00c10040c0c03041c102c03a05101d40118a45c4040107a807a0700300b401401c100c403c080981c0d0011034229100301c1c504825004000007404940c86101010f80c0c0c5541c0c0590130780c081c00486030010540c00b042d500d84103481c1c80f0002890090414452156419091400ca1501801c0600400008602d000b9510001c280d168000009107404564058803070014076164890107031840402d642c031500303001000410a640b90341c03054160403035100c003507407003040b888044c4c41604000c0d106a032140e24800c152a0001080960300c0801040741000c200c0991260780e00810702280d001c0c00a20341812280308980481e40300c03421180c01c0072440310010004922003410b44c6c004581d0303200c8811501040d07584501456203080d0705840b0340400800ea0b10000000b0304103e541c42000d41e208003001c001031007402d02505500502280c0c00020145240080c0c0c0040d00443e059242c000400c0b0341e00701100c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 722482014 1106 722480908 722480921
    0x906060310030b0f06011b05060103081b06131403210a020702060703110c010509060a03050c0903030726040e070309050c0901090c091e05130609 64
    0x101d5814191031608007450f0071000021480c42c0801c40341c1c3c000d0364245e5840c3c1c0450780720303070510b42d00103064400b02d440941c0c410090403840c2d00c1c42d6101000c6420902400301034038aa00d51400390700000f0080e803889a401190074901c1d45001d030070481d44445585ea0701600c6038208021900b603a42e240e4000d2064101462030610266640b00540002030150003002548004009000002c1c16801500c0d40480050841170b0341c4c3c03010121005456610402001c1d681000d0709100000c102d42c0607621141d03100e009800d920f0b14204580300024250341c40480102c9450300c20740b03012100b00000c1e400c3d14104100300481e03a80b41500f0200e082c05c04450042c00c8008040d103d0401030f003049420702c440e0984110250900c0700c203507186c00921002d1311610001000240924000107000c40900d980c1d020000780001590005034101000d03c1a00f03c95400403600b01c41c1c5031100000c00781c40d50311812 = true := by decide +kernel

theorem cover : BRFrame.Cov 722302158 722482014 := by
  have h0 := BRFrame.cov_init 722302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 722302158 ≤ n) (h2 : n < 722482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
