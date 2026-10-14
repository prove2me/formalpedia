-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3649
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:52.941455+00:00
-- url     : https://prove2.me/submissions/54cc78a7-b70c-4762-8851-c80e90cc46d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 656115107 ≤ n < 656294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 656116357 1250 656115107 656115157
    0x3010e0f24190f0b03060a09060605030601080a090f08190c0f23070f05120303090d110c120d0215010305102c1b0a2103090308120714 59
    0x145180c80040070540c0300302100c0d9150b004075003507820354101413038210001c400c4c8500c5041c086029006010711980c144800c6040c0340005246000c010403d504100c00340c408a20140ca899100c58286c2e030308480008210512401d00031040d601c14840c1d0242c42503541011040c1d14411030104105590010126144071a5502c4800c500942d0f5000100d50b80c0400509001b203030000c0055200405450318035a08103443c002c2045030380107441290401503002001003144c066004501c55030034025600300360b220601d448003d1817034172000002c10340e0485803c0240502d5008002114030096540d0340c00c860328070340c0018162088450a100c0105503502140d400025043c19070020301d1024209030808080580140200f81100780c0908064010b403c450303d8211000844a18004641c1c0d0669060300d800d850b141188c201c0c402140c0c8900070150b6802007410416220720101801550444111074032031850014100b80d2000c10f0f108030000c155205011a07000d0144429a4503583c410550140100040341c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 656117607 1250 656116357 656116369
    0x506130b0a0e03100c0e040207030e010c1506030305040320012c0d030e011409010905040f090206071505071d12150a020421050c150f03010e0f24 64
    0x5001d050003070801c01c0241c1610304000e050034044044d840840c0c2082182409040d50010781ea4590003a40100700d1880403036003050900d00f04104c2072030300361446000f505107100e892000c1c3e0310074000d10b4106a800024140c0c8207024106490140131718140d81001403100c0e03001a000c030000c0ae4045141061440003903449460381c1000040002c4c80c005480a00d0000100c60f00c855480071408501d078400500d80659101c0c902c00341c0551841c0201d40f03000b64a0002a2824801b885402c0c0304540f1080c040355040e615402901ea190350188c00341e521081c0618054a07103240005c2402c0d095803900c80000d030414450001d2290120301c298030082030018000138070001c8000b500070450071380300e00e0220700701b01c014105040f44107074146900113031503d0900301445401c04011b40810f00740101c410200c80858400f00d00c440e4803050868051902d190701c5142c0440c40c0c0110500c0e140c0d0002e006c0000a002003003201e0180c4240c2d5136413400c1b001540d400301d44041099041c1e603041072030a54807901d005141000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 656118857 1250 656117607 656117617
    0xf07060e0d0c09060b19171303021203010b0a140405010503010311030313231203030117100e0705100302030f04020910030b04301d210105010305070506130b 69
    0x1c095240d02070f42c4800c10842900c402d0345c8009131841e000520900e10144640d00701654054914101c010b00d0340c0400000c4c15840042c0420300b00b89240d40d0060201402041944400300d12207021a440f5a5105416000b039000b60300500007041c9000d121010107412030301110152441611038905607400c584600c00043c2d03400c1d0019816100405c04404203451013454030008200b841c00d400019100305500f0030010030001d003014060844c1281d81c140c29034000c4196415240f44220f2715140100154079140ba060000c41c0f409103240c5450b0b01c8810103040492a9015034500392444c50360781800b030600f10100e03c41242e10891004101002c40d006150100038150018000042c1601683c0c50b500c80d0070440c8415102101c4840b0060500d501903a80388201010030000c40c001e585644400d6000603056000e018444008070b1510342211060341d9424800000042020f10001109008100018001c020a0200703030381d00e01c00c1d400001142c0c505801140c130a40311009a1000d082e160030030080b007076040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 656120107 1250 656118857 656118863
    0x1f0807110607122702040b0604080309090a091e02010818031602040e070e09120301030206070b070c08040801020a14090a2306030c0711010323190e0c01020f07060e0d 73
    0x100c180b44e5480c500070070381d040a440e00140c80c04916001c988104012076003450003550003500113000400041002205981c4180c2080d12128801d80e228003240c0002c0203e41d41c0240495140d41403210b1603403c0381c01d5002014403c0e01c54031113a403200100c05a9190140d0715040c2e4940c0100042010190483d032001401480a032000c18040c904104580c00c201d900d801000300925228200150a1010004405d4a90b48031010f94915415600882e5007071081c41805080c510044020440080c45000968212600180d8290b10345403138030720a0703010350b0162400310001001000800c5001d90060216485800020251820303d860892158000703202080041e21075829040070005680f54100194480d071200d0700b132181e8401082c540515060f0012400504051421312250307a20000040228503012810b61149020b80d81d40034150500c03130003000c03049251400c0c04285c00402a0014605501d01c07026000e40c0c13824100c00c640165078210310b00c55000001c8030620040d80341e041c60080300c075007140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 656121357 1250 656120107 656120111
    0x37020103090804090c140705070605070510021908090115090c03110d0929040204090f050a06051012020a1a0c03040806010f0533091f080711060712 65
    0x7a1074440410359042603109014080c2c4030004404510b90001d000580000845c020174141822030300c0e182d030f4408050083c007043c46000940340c424403a080103510400e2000c85415981c44076500c6842040303c04900040c1c0218400d0070205520320700600030303642e100b0340410f0050a000c8c0350031b02c0040601040b0f103010007490b42e1030350000f40801030b290080070511755078240800c088c0483d05c3e00e2110ba030501c94180405501610078000b2a6030340e4050075070040c2d0100d501244071415402d0004804076808401450380c461406a94108185504414403031522840c820003a00e5860703285854000882074002c0d40895142000d0000345904101c1c1104003c0501d580350a001f44203011034a5903000f034210201540c04103004001c02c1c0d86804426000d0901655000500900350200076500040042d0020032119030045140c00c101188095614162004050300c0d03d0b898803840031441d00035036040c42c1000640600c00910340c60300900d107a212404016006240e2541c0b031a00484040d403d100c3c440d20043d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 656122607 1250 656121357 656121371
    0x302101512080a090e0108211210030c051206040210030b060304051501090e100b01030b0a0f0f060e01050313080403060905150a060b09040504110d05030c37020103 72
    0x120500290001481105920340c3e40041c0500a0303e030410079441028804441e00c0113102003000030404441c000d80c1420640c5080e030749000c080009005003008051003404032420001031a01c3d000100084901030142450340341e856100b4006206e50036031092803254045004503005042149159410074010701d400602942d5840028581f91310543d415501e076480070400b4039200b20980802c0380109000c1904104c7d82c5851034170a500c440c0b0800780007242540c0e42c00d000e1039a034029082401c542c00c008010b08800c41c2c8074644080c25121a005440c03075621350740008a6001d00400c0c0010807050140c6400d42969034140c6d00704480c1500d0303e000c442840e411302000000400d00e010300b03030140d44514084d00a400f0720343c4d654002014010322080240341003140070080200b1041c1103800700d00b010380303000c0780c07554960400908411034042042d402c9040d6102d0603060140100203009401d403220161080d03c1c450382904000d40101c007800025880300c00300d2801c50760885c4030329410140d10604020401b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 656123857 1250 656122607 656122619
    0x90807030b0c0408150a0f05011203050c010b04050a0609050c07030c0210030905010c05040617060105180301110d060f061d0f030a1a0615040b09191502031e0703021015 74
    0x112840c04500e0417450407030003d0001542107806807400f5849a1407003008251f24005036421700211405001e81440300003d100c900e00b0000390010707650309002401c1448541402032940008160034410b1101040c64900070030400d407180012214015050780c1c41290440e115000c00c2040a00b03031b0010000d0517910100100021402c2c001d03030880300c0050b11059255850080080c003800c02c40c1b900000701c002079604101c826a0030205462003c608081c2606100110740003090041101c2107002004030004139a0111000740c03600882d0a48019842080d2007546c1c0355800d0303a005180d100b0b14500300c2280001044a4101241e00000e403040050441c1d50000c10b58440740d108d003400d122035841c1007034480c0800c0031908010070035050310444480c44c80d04e0715190170081107ea0042041080c800e058040555a038408820005005071a1594400004481c4000069a07a6101d00000d800d01c807401507038207484042e0b0780309580501e901900a0102d102c41900328030001c081000c080f0020b44100e102c080382d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 656125107 1250 656123857 656123863
    0x6220f0f0306050609070807081e04050106030c0515040603050a020f21090316060b121f1b08310b01170a23240610090807030b0c0408 59
    0x4010602003405240d0441c201981520001081c950051185800780407200b607005c40015070021a0349800c90301602c070403840001100c1c4641c90391f500c00032010241f00034084194082021a0b01c100ea02800b620b50394000e0080d0b0008255038940011010b200c1008858001e030440d5600c1442203000526103295a00d00c182190030a41c0100408c0408950042d019150000040d800ca241d2000460802c8102c5900e46440c120003a001007115444080005003a01d90b020005001c4000e0001d480d4603900004420041001d4100c610a699041c004125a440c0c02261030659100481c1d450251703d80e030f212100d00300c1b8001900d250844070360546414001084040d04021045d10618642c501549005012300480c4d07450440c1100a070003401000740010303400c182c45504000981000c019130a1050380b4030b13040c030104c410001c01c0b2490410740c11400480201325944180401c55540304c050008140840f44050303507004041f000c0e44102d0090011a505144840c1d02606155149162507255100c02d41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 656126357 1250 656125107 656125109
    0x8070b0c100c26010f0b07020f030a03050c12120f10031e0204050c040b03040b041e1a0a0908030a02090f100302120f070905090c09090405061b03010506220f 69
    0xc0c0440301d04203484a81030f0010000003070003948010507504100320420703600150304ca0785900c0c1100280240443d1100e050310034924030005c0c1510060703011420060302a51001b00301c01d20a0007801d0240c000703001d02e002540d00b11010740116102680d0340d8003070300c03417400d00191010050465540c800000143c091078000190f0501d000080e0180e0982e106210540d00c0151810080b94010f02c014000c0325402c40650703500607040140c002e041e4486003044030f28070285201500c10002c0303540800042c006401880a545640010301c201155034100101085039400d0320000e00480d410404074010500d960080c0c022100014410111040031070002020440d2040000300840e80104805042d81d0001c08019070000210710310304e5a51400c480002c02414a60140c51b124442003400700306104400801d5615980c0080c111150b90b00b0702d42400c3ea42d4a030121190010041441a6919006022419039040f01c40281442c0e08000b02000f0400b040302c030040510980c4020380200190691010690340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 656127607 1250 656126357 656126381
    0x507090606090b030129070b101502010b0a0501031e091511040608010306110d0e060f07020c013f05010807170c0103050406060515090a0602060108070b0c10 69
    0x2102803030507401401e01e40440e80201d065810078001044541c2072041080d00c10800681e00c1040601c80800954440c0180754001d01600308402c200900205218005400d07103080c0300709441501c001c0034040b030a84c0c40341e00221340c0142c11002c041005502035044502e010f510000a001003e00c09031148003200c0780d84c002034822a881d2682810203641c544505429501c0b128070080c9002e0400802604044042c2b000403e038940e20910804250040300a6510203070368035006000102d402003042d981c03564147d4082e40003003001004201414000200203801c94810b86548035800d80c560860b030313900105000b02034060354000390544421a10620f1b0f1a0303840c101070400199650400c0300c0031b40303040e080f90403100101c0011141103604000004141417440c00910300824244d64a1a0040151150ba88002d401a03402c4034560f80c1c1c8420003003d844204420f595049000d0380ea0740d0f04a82d40c80d2300388503010325a000500d0912828402d0001000182c00600032101a03005004810b41108d13040a401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 656128857 1250 656127607 656127611
    0x6051204020105093012030c0c010207080a23041805060f0604122906040b0d08160b09030304080714030c1506042a030b0102011e0e060901050708070309050109050709 73
    0x841008105d0724261400f001c620003d00c80c14210341b50079482d0344005000c2505400b80420850302ea031509404842003164050746094032514880c9018000080d002e054400c2600380b085265540c0c1490020354044441b9030350398006810b83c0c41c014030000c0c00050211074000701d03403000f82130035500d440d4000d20041400368280340e4100300d14284070940c0100c101c80d103880700c2103401d8210b6200c1e0a00d0603440c1c000c0400c07500010301701c2120b400103144988008004007010030105500c10346005014400080a009078a03002075076603140b2803191203100860700200015814001d481c0481c100c0e9101107041c0c0c19481c00caa01e4010805482071401d03d6461031710120401410400c40300c1c0c2807500411212003010315034403c042e5503401c407200c00c0d1007601802c00100344e80c40701c80c40400d030b01c01d4214103d0300d2030507159420444c049103561409040c481000c0300c800c1c810b4201090046005108544c0315111360340d9803100f65159880708074041c0a814905451641d00d0703a04e6400464000e0124000400c158200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 656130107 1250 656128857 656128909
    0xc09040c05031e0714010c0f050f3007020a0915060e01031b050a0207031e0204150e040602071403180a080109020f0409080c0f1005010b03010605120402010509 70
    0x1018a8160500c0340f6101443d40142400000200050b03200c09541d168035003aa4281d14140040b15001360300100035103030840b640525030a00501103105a1030321002c106580c4002d8030803d124203041c4e1010000903030000081104190a080c01002e0301005200420031008999901c01c0413003a04d407072018900f040031701900304100c02a00064181c01ca00b4017802c00740304244441410824040184401500344040014881d1100b4420301c1144003450303009414030551449040405008404220101e0081d0301d840d407558003d0002103041011500104a41459a42c41e9526000650006d1408440f0a5132144036802e0094040c07000e0320320019001041994001808200002494268009001c1d645062500c50140c0c9610b0816030300c038003083e203000c580307043c4516000c0c68900c0b0f50f0112241c0c0380282844000300b2040840e5640072443d0042c01440140d89400008016100c03e01c0303108042582041040d00f86080e0b2404194000d00504115050a0301c00303001c103a2182c0c01c0090101d401c4e040c026 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 656131357 1250 656130107 656130109
    0x1140f1206060307140d020d1e0b040b0604111b1903050a03050f010503030421060939271107150905060c1308070b0d0b09091c020c09040c05 62
    0x200c46802050900103003c600300c2082e001c2103043c02400740181c059408e0900c01c0c41030007400514607480500c0d0b08036060000100d41270002000e002914211076071450780f40031900c3c925190140343e1840410701c002511784108003030f4041038070b040c00c05502d01c14080e441d0083c0c4011941c3c004c01c0c40540c081c2c4c82d81ca41d02c8010500040440301d00502403151206842c00600030b94a0010943d800c1d11111642d00c0200d0714403140c003101003913403004000c1c00c56080120000030420645046c1040c2c411130303c00c4206407140581554070f400e46074020801000c0700035200f003143c0251a161009800302c4511200720a00d406604501521900180c080300308070002004401c202d110780030b8004c8060b0a407800c00c400c00450703036000d48444010b0b140d03030314111022801564018621007410000d0900074112060540c0d03074140100380e0f13000f000001e10000d1801d40d1404560812452143c1b04908800141800d0400460f411400c0f020002d562011849048200e1070b03980c60340e109040c05a8007980606d11180d02d0302c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 656132607 1250 656131357 656131363
    0x70e0118050a090b07140f0a050703020f071508040228060e0603100e060604080d0c0209071803031404080304032303040605120402120105040b01151701140f12060603 73
    0x3502e144211450300c606a404620303129407154000b100c0d41390158a0801d03280700100740307010301c1100311106000062813180154028005041491080d020380c2c40c2d1080342550680c0340c0d112842040b101030340641a54800300d115681240c1e115100a014540140e4403101032544100b50071580c421000c0c5001c020b10440e50000c8024540000864109246141c14910708109008034400c00b2510101c0c4008280c0654600d41590050440d0340c0c1142c0007141c0000b4000d28407007000805900448a213000320759110301c05c462900b103005144030014201e614590b01103410b05001c03108040011070501000c10b80d008148010b0004501445041e50303016100940d1a1040d00c40c0007044000b68402c0001308561500030303065800400b19201c0141c0e81d540c4a0011800e009041c000c130118a5180c102000108034100741900d0580382600c2c840b2150660101042e02d18028030800c0001845145004000f9007503641344039980030714050840403081030034001140450300d02d650b040280390406001c00229050070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 656133857 1250 656132607 656132611
    0x4140a050912070c0e040302010905030c0c090112110f010306090e030d110405090109020901140703111e15040507050303070f03020d020309060a1b0215070c0e0f0711070e011805 78
    0xb22003820320b84140e607a141d069203491849603100092182d000241418000e511160100340c00c0015260340e0000040d0603900d41e004d250742c041c42402c42c0c000220341c000c4c0c0c80b011501865071100425a0541b1030404000350b5100c880121410951150030224485445000d148001240312004544400a8284440030b81e4040c41e074a5140381010310007000306540b812030980c11543c07007410060b900d40030302c001203c0009001150080d00b030740000301d004c10160306c4124024840c0000301942c0c5c1c180c0440c2c4112000d4011914000c90030fa200e4100540341945070f0200940081c421021280401d6035400071a0443d000300e40261190340300038501c50141a014040040e6010b440d2024501d4020001c0003d8501c2c01603105402c10090660040100c890828100241c0240c0045c070500000c0c440c4e48903d115580904021180012280300001e0241485000d00e030203250324035010241d0380d841c84000c4a589034a1510035480744070f40d450014200f203404900b180038103805581040003c449140c0601070f40c0740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 656135107 1250 656133857 656133883
    0x108060a081b0915031507050d050f04030e0f280305070905090d030507022e060b0a020c0105030c160203150702031e070201120f020d0f0b01080f0f040b0604140a0509 73
    0x9160b200a010340e9020446c038044020806950406464100b4102c805000300404605140d1801041c8041c43c86051800c43c8076621994803140003450210074080780340c0074000350790f82184a0025074808590020075240700c00b142c3c02003600a2961b66214280b074802c1941c06009400c0c1c0d40c2c0188a81f95078144010100e032002400d00388200c0c100034500a40d0303020070390341c0c08942d44608141d405030080c40d4003a40981c00d03d03682040c020203485040035540751b801091540098031030841c10f14503550151058a10803180d01c11118104070f141000d41006070301103031080b0380c5400b841e4181d010040d0b03441d068038015162a4000c40d21030034100c0540701500c041110703520300f91b8003d00c0101c0051381e01c900701d10130f2400e889001159903040100c00001134060012554102410b15081c656401010361000520402c2641c41c0c0440391a4441c00c0180c0a6041d107001c035200644000090111700708109503500708030301034400255080710068145100c20140c0b60507081d26152018026046400c1154024080c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 656136357 1250 656135107 656135131
    0x30a09150b0a1217210f010e07090f030f0f080f09040506090c071104111c050601390b04050d0207080d020309010c1403120a0f060b090108060a081b09 66
    0x2039240c0818560708111248490400007413817401d9080e001d5103030500044501108103840c01c11800444000d9824012241e80b20015000280e05501c10903400088941c40d0504080d00d40c15502c3c0c2c01d0404400d200191195007041480c1e1001a0070600205440520a041d8a8648003a1001c0001b500c80141480b84580a05428042480340c40d108440f06641e00803068032440c0d5016012801410030b070034008501c6000801c0146644181c8942159842100b001c02c01459407404015601c4d9118844140031182130307040c41801c903650780d940c00d00c545c0030200300e50000107001da0380d00a0100c60803a42100d480d04800d506511058041002002801104003d03000c8441030b800e000351ba17801041551810411100050070074040f103403004d002c0040d0b02d03000356941d0b80b03080101da151910050343d003407008074500301301510901505e2180c2c1e01030b02d8100248038035200089004452944016014070b41c031447e03040c4000740c05903081050741d440035441003c0140758404641080800180100000c403919 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 656137607 1250 656136357 656136389
    0x11e05041118040902030d0507060f0612080c010615030c0f0e010509130609052e0806040b0a150f1a03060603130f050714090106020f12030a09150b0a 66
    0x421100c142c40c4445094401110440307400400140034200f00e4401a4250140d44c4011001c107900000400041b4020003040c40383c0500c0c00d81a00442d04c1c41d22031484a030705420100702c000b5880000078480d034070303403a00046595500ca210b42403290602c3c03221400800d81e00c1000907409500045940c6503030409080c50b0f14400802c0b000078042d485140c64192050030200355110a000c826440b040c050a00e45d40104220301d01851845000174503c035602c003582c2d03045440c00b081200d801c0701c018141c52045000d040607440391790b00d001c010346000c7d140b80c41c0076444d0b100041616841c200d144d001000c42c20303042100240381115a054001030071241e084940300c20001c11003030391640000c598100080400307140c01762000e803c205101880742c40000b0124022280009400d41140e140115802811101f0803113a980c0d0b8401a0f0b5605c5000150300c5072504254048400c540d41400910b5101c2103600000c50303a40e0306651183c0d54060844035420a0a03601e203a0810113041410262001d001150711051601d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 656138857 1250 656137607 656137631
    0x9060f21020a020106080114010503070807150806010c0b070f27030b0402030a0c0b04091107030806121009050105090606030d090e100902040e0703050907050d030806041103011e0504 80
    0x50544503201051141c000840201c2c69100754400c4d001405190000c02440b030011a01d103000c0704007171142d54440e200d40540030a0810010511008944078451005021075821500b591150002040320341401140c2c884600824181c4101910819055035000c4d08041c0c1c0103009045c0720710400c4000703030100181000392201484644040b05882e001031142c0d9480d9110301c0001d1400c042d22100424900340001d0018900311030801a00c16100c10f2282402030382040c000340b07901d9000b10800940062487c10100d07140342071001c480b20740d07000032005490050205c81c1101080d64030384038003150300d40e540b4000c01000031001d00c0030540140c8201e0150850300f41d0340b88000c02c0c0c60424020b01a084505034041791071035510800c508020a042030096444555580b40c0410750300701110040046030034000054180308000c40c0b058141c4000415032200c2c00c85940b03046900c0d1400034030964002e07039240b140b002c850a2810155000b0100d107800908854410809030b180840c1590040740a581040049201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 656140107 1250 656138857 656138897
    0xf0d020307021201020d090c090f05100545130807030f0e0d0f0302060f06060307050901020316062a02060a0b3c0906030309060c160609060f 62
    0x46030b4044800c05501a09102c00301e00a105641d08512250b1520b040f050030000c05039107075001c50710703084802c1108480d1401e0a07410760b00c086501c0112859201402d00151822404c10b00c050781a44088195424500074000030087c007190900e0341040c1000c981482c0c2000c1009803a17440503041210700c2505010355a0201385001d550001801c0c40140480e042006100c2d05070212900c50040100d2610790850400c150440c1d8808e000b5401406250000b0b510990b2501c0e1340d40c0280030192009246545410f4201c819801454059045000c1000815030b490012010314001900900380000c0c451041c040042c88219601914003155035803075602c0d601c4030b4002c075072594041d84041e40400d47c50b011400013007050440e107140c00d402c20b113061002083c4000d110308900101859115103550b030745008042000b000021540f2a5259104100f00c282a05000e00034000e40c401c000c044880c440301c11181148100c100703820140020729094410041d5592160700d00c90707400c009003091003203124000f0b20425 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 656141357 1250 656140107 656140117
    0xf2102120708090312070f030f020105101806050d060b030d140306010e060d0e060601030c0203070c2306040e0402040b0108090c0d031112040f05010f021e0109020409080c0f0d0203 79
    0x40d500104030b1043d99202841204885030380300f20036544c1d40d6040d141003000c441c0d96100a40000325400401105540144180b60107480510f01803001c061400c1c2e010060a071055021940850311800c0001c2c0381d0312134101e2101150310071080480c20000d001c0c289464181c00c1986801042500ba0b4075a00f044422800c41e03402441c01e02c1d02c00e8000c0443d5011400600c00d036002212800d01c1d000e419440042d011a5050050302d00366014041c1690304070b0308a94034040c2c060b001c3c00e030054400b030421125081030b0b2060b10308242104184101701440d00001c249820640c48120600c05901c10801186840d2060039803050b82420501d01a003043c2c501c0994403001a004540903101e0148000c00b4180a0005c008a505582007150b55084000c2030301c3d0010742041c803500484118074800401c10358014012642100c07070980c0140356071009400080a00101e10710042c040b550f03070303030495000760b1100e00a0300040b41c042c808495854480c050741600d8090715035040552a00240c9800c844664003000302c070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 656142607 1250 656141357 656141363
    0x1c031e0e03120703020c1b03030d1e1401060305060d11040c1e020c030c100e06030403030207020d0804031e030504060513051804120215010504020c03070f21021207 72
    0x9503080d28030854a14601c107403940442d40001901c03c101c5020760540007008840070840580d000401030b52100e118911110381f00c01d5040e00284546031901110ba032080d00e940304c0610078503641d0701401b0780b01030440380c0030340003068034004070340c01400140e40501403260410010741c0c40c07800600c1c4a07203035940d410080840417440380da01d450032641c145c0d02c2000031309034090b00303070b509031900ca1515100a581e40c590104000d0207401085541c1c51030349071a80c002043c034401511000c01921b50102000116803008000b2000d140d4284081d10141c0c90b41003000702418425542c1030340d02d908504050031007030059001507140c3e04400c0b40303440000e6444400d0f1405c55a290601079101c00a9100e1002c4c180021340065400519425a100827200a41c0c000b60103030b8014208982c08101402d803c0342c88030b5000c5100340c21040c9540041000e03060a50080c1002c0c001201a00e080980c29640c000034580a40401c0d54502280e064030001a050340c9040d03611200c0300d000502080d030421031445000e0154400c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 656143857 1250 656142607 656142611
    0x7030c090e0a0204151406090607030e120f060117030a021f0608010e01050703141509250309050106140d0204090507080706020a05010606170a0f02090d051c031e 71
    0x45681c18000b0404099440e40c010310a20007441030a0b600da034508554807032607101000140500d009410701d801116483c04000d0403079171a004080e20249c0791754142e6801d09030400021040400c1c41541448002c00035025100076203c10351400b6041a15004800c507040950b40040201c040e10700c1c1c0014040c10200c80c00b90100c004042106840340c001c5c14907500c90b80300d40d42400c42900e03da841c11f610552060b01241c0342004443ca41c0c41800320324a00c201c4952208002d50102c102c11460100d0f2156445240e100c0d01c446280150603910880a401c0500100800e485440100c04c0007000e00031100601031141074000b0020841002440381d004901010713001e6941c07034a9040c10f0003030510a01001d48000c200b107802166841d1402999555540d405a0380c5511300744010401c0d500c54040245202c480603040c0c1c2241c4c030341118201c01003940700301180180da4208000000390300e8001c407918030350340100060b141142e0104031a070540b0000311070a800305440e144d020540d4009010703011021079808100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 656145107 1250 656143857 656143871
    0x1f06050706051b0703020a0219081506040f0e0109140d170405030f0301060c15060f0501050a020109020a14130507020a1401060504180218090c0d1e030801031407030c09 74
    0x1903a107540152000088140f0030000314442807580004800b00c09a10980c1c410754005c445030030400c030400c203a000c0c03541c081e005248600307114030511041d19001230005100007030061a0050b8a0200c2d590310100300c49a9444e99441020300801050803401c25403010701400c2c69800d085c3c0000c00a1075001b0091c034441c008040460140a41041550028039103011199600e5071254805480c5000081086032000782103600c028003c0b085018840c210385c001d01b0179414080c14040199000e40240030030f081107660b51241080980e5428a4000060840058030400170050b00c050150b0070302c61520300324000d1b007010300b44200c0383d500003541d06042d90894503500c0c4290f41030103098090084d650041d03900c80d09060119402c0c03a00c043c08602c40324400c5590003100342c59100581c1a0f520221140215500129805030081c2816000a46c00a210310601c0000e0303042d00403540300403a00540260001207a0138014002c000d104a003038110a03000d0740c003c2040d03d15540d00c11030011800d0080040c00c64803400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 656146357 1250 656145107 656145121
    0x2061807092003041a010b090607030f0e090103030806100219020d0213321005060d020708030f0609010f0f090c0509041a01080615120c09181f0605070605 68
    0xb00064004656110030341d580c2c106418004c0400d903107070f0109222500428000142451840211950414003420301e90a1500d05e0700c007070707400c0320044050100340000c0d602c5200c0e56550b034070304103806503101c7c2c0c41e40368440c00c00d00d01707012000441c2c0c0c2c40c140955001051072182d00411042c0c2541a43c0d040300c408400451510103d6111080c040328800e1603414101018a8480066200c8031207190040207501030502d0002040501d041c2500d07003000c0c0305841d12090146044c00c0740200b0f10707086d1006002d842c29100d503940b0a40d99200720384d64890103070306a06004031490001c20041c018100b03095011140c0d402d1001c112101c1c42c09118181680d1313a20b5290109442c091000d991015400034001c100d401d201e0407955800004001c4001d0000d0403150000c0c10303030300d4281d017407945110b040c010890030010007000701e46082c1c6028284840c40c0c00d080c04000034958030801044280003540403100420304001041540070406007043c541c114001001c10320045500c0300644003104c1c4c00100108032521129 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 656147607 1250 656146357 656146391
    0x10e130b060c0d0804120804081b01150e190615050c0c0d05060a0501090c02030405010c0203010e0610030b0a05040b0f07030e120406200703020d050705040504060c0206180709 77
    0x1110b00d0024001d15201e001c0c0307240c00c01e81c51803066000d03640985581d803031554200c509280c00c9400400200040c4025100f1564040341c608150703894000005803124503009400d40298160702c240d903500031804c10007810a070392000c05541890909814440b260031b041028140c90990034100c4100400495403900012042000c44c50b038140c0030f000902d00400e0390500304d403586400c0300d4a003034050408000245c24040c82c82118144042d07540950b080504000c01125107488841040c0da042d920f41446040020341404001c0c041c03440c41118411079861442c0580328804000c2585000034508010800450707240208151301041081991146550740c0c501a001804418a0741280d48241110b804942c60600000c00030745101d40c90f40c01480081100c0f60450701c40d5515000013580100300c0801c01400e040203100d140300c6c807034010f41c1d18580d05d82001c0340031074404550035903801e502c1d09140000c1a405105441c0c0020301600e5607070382c1440c1c1a49081d074514061041d0000540d450000406005003c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 656148857 1250 656147607 656147617
    0x8030717070b07050d0e16120615080102070203070603020c070611103305030a1b1203021501092c0106050d05010b10111f060810050403020606010e130b06 68
    0x200120442c5418014002040781e04a41081c0b11810f00c0e000b002c00540d40005940f00d05e0806d2944615821810410600968200d40100321241521010f41590294001005402600d10400010784031500b81c0101403070043d03240e00c10001e2610410490424410214141b8141c2d926402e00003444001003082c140b0340f054011201c1c078510b181902d10407040c000a0340030042a54401c104506414001c4040c00c00140e2511a19915510a55020000455100031403441d00d01425911030b030941c0e100300310300395040b480c0b4084006802c0200b581c4035100f89004c109000d0302c01c1f0401003040c0d030007140b6003001d080f060019060106151038151340208000b500300f0009001301a002500070034030b520b4114081c11550f50424428000101d2170150076115002c01422440e02c4001130220303210702c0003540849a25189035040d0130b6144d0784041500e100c10060781c0c007511459940082c1d54900340c1002401d103007001d050342d0f0400061012a45095552035021842491050340010700d9a044e08001743c81c0344a2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 656150107 1250 656148857 656148863
    0x507080c0313061e0c17090a0807050307090b030a0201110102040b1201080d0203091c0317040f05010605030c0d02010503060d0605010b0a0e06130e040c1e0f08070803071707 76
    0x81c80300300b00c1c0c8110340b003801150042c2c0c8504154290801801d00c01d500c06024580c000780b00d034503041022610012405650701151910a850508241c3c081420305c180754102d03076155444410100601d043c100030500c010007500e881042011031703240000e600c508000170040d04100d424000c55888070002e40c1260000e202104000f6601c0214040303980c80b200c802d100c0c0a11902951040004283c0003004803501103d000305821020400c01030502e0032285030100c1175040050312014061003008030040305006900644142001104616090f803d43d00c03a80c2025000341c0188031120200d031500c40038014110b90900700300d1f03226629800400c0340b01c801e0f680064001f07803e110001554500d024020000202c6580d604a41501e030501401443c1c0308585107010f0042c40e04804111250269080640191162000c000f40940c2c8201200059072a06070990308100b01c444200303d8090441c0200006040c490013a00c4401d282c810216124041c511014100e07a03440c0c412101101c1d500c070100c2ea078841d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 656151357 1250 656150107 656150113
    0x71a0c010e030a1206080c1813080f0903242d07050c0f0d1b06090218010f0f03020d061805010219140705060a0c0c060e1510080d0507080c 61
    0x8080f50020142000000e2000c02c0707910340f4601107a500c10100300b9070300120015241d421008114100207001b2040107044068690241120b100000c4200c0001d1511041e1000c50760380b04c0412074201030601820090031810744540086194070500345401050b0300030f00d540c03c0c0941e2490000c00c014035001d40204a242c8071a50300307003086202074205002c0c11071702d0010b000b00c441000c036410300c0d03541c0d5581c90740c051f00c042486c4141c61400707400c12003031015895100750001f15004038642d0100d4810407441407002c100402140040c04141802c581d460020500811703101c0b507852454012500d1110201000703001b55850310500c182c0401c0d400071003031005520800840d0f0b1481000113264006412141d60400640759000c001e031000185000d0714404c035027200141860b82c0740c14543c0002015442c2c8454144801c9482a1000c14014425602c92082c104060949030488034401c1c2d03178000b00180200511203402d072007408002c0002075200d94518840c10407275610000c6c0e042075042402085a501910300c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 656152607 1250 656151357 656151367
    0x30c0405031903140c25091505041503080d0504021906030203150409080a11160806061309120806060f03090c100509010c03030207022e02060702071a0c010e03 70
    0x15400b2007000d20454040d43d1034a511800200c0a22480d103c0c9122a28142d44010740400c081c00b50109001ca4241d0783c9800002403665480c1d9000913900042000300c0c428a001004001c0f9003003034050101c1803d1310302070700c00d8010b0644c1d84882d082d00420000d02003031940c0301c00046c1191503070106040e8020031441c12442582d500c0b03800038080d50007291500c4440c80c0f40070715002c04d41018081d00c0d64583c0c0c00110300d13080c4420783c40201c1d0126a00704860f0020f00ca6030011662006c42300d503202000e072405202410040c5000c0c414044000001c0c692011954600340d803070345c00f00d0841c1c18003a0520709245046c9015855080014000c1d000301d400c5540d04160000c14450980d600007169109900240c9441c401e603000c2d00702c1584c0c00e00502120701d02090520540e200000d220341d009049191004004034044402c000401c035414074481c01034070543c0300c1d56803e0310059404110443e0701504c07074402081843e003843e00006070641b092080b902c0801e00410360480c801000e401504000c0520012070342c0711 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 656153857 1250 656152607 656152633
    0x160609061b180b0702040207110a0801090b01080d090b0c0715030504050105061807030f02041d3403090213090606150c0b13031803050601030b0f0402090c030c040503 73
    0xa11601107000300420755060241d04411211030742a421140d81c4641c250801503603400307000180d44006d03000c580814000c180390f01e060340c450082d407010380490000000c5900f03031840c3c0030311141c0381a00100c2c11640140c1000651a0f0300989245c165101008820344440c11402c1e807e180070090341100c5c07903034a6040032842e90340782d1540c44503114030b0044000340425250402070000c84c4506038104041001400700181915000b0382001c1140d07a20740600514242d620a144070310101c2c0a2030642c41600880140a1540c5100d800104107103004808008002101c020b00c900c20340344101c3c0341d4240350300c8201c144150760b90f0300030080c2498422801401002903034500007000704414060711b07407585401e504121f00d451043c44104885c60380b01407000001d803203000c0c071310720035442c20b080450400c1001c0d0307035a01101d00e040c000c80000318450001031101d0f5065103040031202a00030405016070302484d04200c0580d4615082c6070300801d41c510740e560b480e2204164402c60307108603004960544070310280ca00f00c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 656155107 1250 656153857 656153891
    0x80c091905130e0712050f030d0b0a0e040f020108092103100503030f04090b0103090f0501060501030c030209090604180c0e150103020901080f04021201090b18030901021b2106070f1416060906 84
    0x480022150b034010242c96000e01074030315508de94042d18024404544600550103800c4450b000300f498021a050000210003810340b21400340c459a070803d40210034000b1040e4980c401d500900811400703181030114603804056580180d108041c0480d45492120744282d000c2e0340045003036900a04a80d0201005081c00c5000e440540306841c00245460091171601e4841d01c02c1d00d035001e400400e14100c4d5180da0307003044094000e8814980321005c1d1240d100000442e907c00403401010108400242441c00344440b0b44078140350490281410b00401c01c0002580e807100b0382582c01003480021070b003983c48030300100350102510203d042c1c4541c80c7c201000188240c5c400c0603440740d0744050724040c204459103e850784901030a00307101d001d64414030440c451110b2899200c8072082001d021203e0180f00d040c2d0701d1500c110148010442c81c5c00c69030510000c9070b03000d4034810f83c401103806c0c0356003040040418100144900d036800c802c041c0c8a800b2020070071145411104071107400900500107034152103041c01d0303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 656156357 1250 656155107 656155121
    0x1e0a0f0501151d0d11130c23120412090f06030b150c0309090a0b042912031b030d0903022d0706080c091905130e0712050f030d 56
    0x85900049072088010745043d401d20002405031001040800b03da440a10b141c1c003034050340346d0141c8041c1d4148452411031049590700c0a890303884052004101c140c04e04030f14050110010210f5042144aa01825007441550800d6002001516955429008035200b8040350000383c095520032000052007585034201303040c200400c03640c07028003041c1d850980c1070703038031904c0740c8a00940c20034409459546000004140c1c00a0b020340007003140c288960000f02111084040c10003800020b03207103600d4540c0c62180302c42c4500401e071201901038452402c616584e0103440140b404c6c80c04403519903c4101030601c103070707124600b0104080c8400182c07807a010f07480d9003a00d400c1040080302c600e5240e018040300881c01e0403a40786100600401d03414100e0440707142000400f1028400c1040044040c00e071a110000310084810380140f20f240b505040c100140b0140040400e002d00c3d081440c042ea1106001c20303070000300c40c00d5902c003800800709031400a08105900407103164a02000c548000b0302c401307603003000d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 656157607 1250 656156357 656156399
    0x90c0120070e090c0105282001020307080606071a070903020415080c180c0310080d030e0d022d0f06253209030a050307050c091e0a0f0501 61
    0x200000c0c000c41c011100d500400c02c1107462242c1fa10070b00c030410500560720040d0403441e0301d130080c81012584001103400081c40c040403c107039800003c0090031640644171306d40000d0700700d804904c1c3c1225515058169001000007180507407480022540440c01585280c0056901401c18052002c1e0041c406001e84420322400752140621107000c2ca841c03400c0050016840d0342d200303d41c8800c0e100c03c050701c0815000201060a6200c5022001c103c1c1c1c042004a50a00101580c6c049880018002042d040900c012414800e5601c10701101c0c42d107003510300580c99036102c45005428101040900300749031a82c100002100c5005030014040c040807006048448810102d0500401494000c01121614240c038400700e002c20100d101440502010202425949007400100d4101910040003074108080200100c40c541e10001c0c1520401505118198001c102120030303003418502921032100007121207a01c0301c070b1140100c0c0000c0501040e50300000172103502c81820810741da142c0c451150207001000c554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 656158857 1250 656157607 656157613
    0x20d0b0a0612110f06030103080d0f020702060f0a0201060e1b0d0f140906010b0a050315010903080406051314060a0f09210b092b09030b0f01031703090c0120070e09 72
    0x3144c01d00749801102c3c12030303034040d0b400c515080c038565981e0014000140d001620540801059015961b04005000300710703804030002d640d5004c04603003e400c4070711603800545020310203000c008243c00d404d5050201040318041442e40c0d0440c00740e4a03401000d40c890407140c5a8905240300510314500c41001f44505044011229245d0700e94131011264001c1700c0303000d000120708000068101d00e22040d80140d02c54181011058140ca0341e44003c005d401ca074000c080015008940d048403c00c180e00540700030600682d0160703c00c0c0800011413604d2180041142c00e000c10108440c0216100f05103101c000d010040d400800041441c10502907600c0d00c0c1400d948440c4200c0114105010100b0300eaa6100500e554580e91000c25182403443c1e07002441034803041c0700302804008007060703860f200688940301480400001e581103181081c092192940c1c0c1e01d410340c105008009003224005070340c050750720303003401c0c0741003101015206034180c0c1000f560100902d01540000003500e40707020b800a07029a00340415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 656160107 1250 656158857 656158879
    0x1509010f050705210c060103030302180409020a050910081903030b010f0815280819110402031b07060f0e1f151509061704020d0b0a061211 61
    0xc121014024140050220380203c6062003400005501ca83d90740744042229504040d15181c0107424280242e00540101c0d40014000801103000c40c0c0c046c00704003088504000d41c01380c503000308240c3d80290041c5409410554042081105040c51040c01810030b5412100105803403036642d01142d114000c114082820403d01c4140ca40c002c20b0320b41c1645455580326042959142c000b41561661041003a800c40a001c01580403889550700301500507a55030001440740b480e107000c0626040740c4c0720120403600e4600c01b8490015a2a101c1010302075022940581c0307a8a8006000840c42c00708410340804540016580c4100411a0401400d140304228200002e03000c1128161701c4000e032002c1c5009040000f201485806119844071160718091a90380000d04d8036600a0b090703d041a54101021a913001e50800500740e22402a4440d130348030b456030084034185540072441030702d400c01004100d00b15160010304110190b52048000f090321980350104105141040806413088022260181c41480340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 656161357 1250 656160107 656160137
    0x1e03091e041112160509120f071a0d0504170309010c09090b0607060906020c06010303021f021e0c1c03090212030702030a0803040303060e0a1a031b0d0303020405150901 74
    0x2e6800c0b00c841c66a954085a0700c80014040e500d01130100c2400303102c401d010305038070381d180c40c204214081004070040041d4400314012a01c0c005243d48980020044940544c0c0d441c42c0e1101074420001c000400070920745c9542c0351002c040c51503603000340b086540101c10481d81c5007054110419100c0301e40c50f6545070795126400d000c190741307181d207205070002020062600007a0707090307000a08003800f803030b801401d05a02108403410400280c0c000d4005921025a00074620072141e011081d000104038210f2030203900001680b41605502000c4100c0c1c0c41c00301ea02d500c0043d007070000c6610030150300c5041150710600034000e030081000402c143e0140290044102440c0800012a04203e800030b00130070f140d40c00ca685846d0701e0360004001b1800c00d07031100c1300010b07140ba4404029000c1c4041e241c1c0405e220030080842110a510401194820703481200302c024100360920350540070f1401511980a56906411b00340c1c044d20442e07120380d40107004401d20010007041580a07120340e182c266110302039500810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 656162607 1250 656161357 656161391
    0x3050a08090d020705100504030b01120b0c0903061b130603060f08340b0a020105150907090504021b120406090b04030309090903030603020405040b0a1d1e03091e04 72
    0x1a107002d01581c00b001c000d01c014a40404000800038a500e00649010384956a10111040c2030b0302a01010351301034007010400841500c0c0382c0c2c0c088140700d10141000648000a540e4260162070030f540e0168290b0984030864000080f5901034072400700003800507030b0304c4000400812181c4165000340d1a8141c001c203165601280ca0820b140e909003810042000b2102e9880c00f4a422510000d0351010529002a9403500071000d001c40c00416000007a0a241ca0781070407500201d825461840b8400755400c001d0030700e400003024010b5400c01d03240162566015914180460030501c0000f445110380038031080f601c10007100410540340250f4804250507911a00858503014034000140030134100030050002020541c00000c0050003072030045109583c980114085440c182c3d0240c440d0f03a840d86c104a82481c103401035074484500801800f00d40641041c009840700545001036448030810781880c086054100240c4d58014001410007400c22154058500c00c03215040d41030f801281404c441e420208010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 656163857 1250 656162607 656162623
    0xa0b1c05100e150903090d030e1c3c0f06230a090f02041802030d050316110f060903070b0c04031101080925060801090207020303070212120703050a0809 67
    0x182c0c005281c4240c2d10740880c00f030018020720b101458032040c0040785030340d034405000805260198a42040d5280f200c401c7c01241444950700c194800c860611000c000b0b44105004903140d80d40d00d00b051547c1c841c494005145a41d10242c1130415070311400c45405201c948070f02120520701c18201001842e0403510845405a0180501c268500818000400680880d0450f84030740344240c1701c13030140741c54590006d01110802190140e4514541c4010030450134204444104112641801c50a518011944002440c20915074000708031603484140480901040100f026146100942c2d0f00c5117841d124103960ba41005c40f0603290221035034042050000024200c6042e2600301d03281e501c41d1034560005407801e03c03002d40598154441c42d10083c850441008aa80e140e0503011240e80300103261100040000e1010303080301c400d03984100108401a03070000200c50703485605030380e001c00c544054404181019070301d100d800b244520005813003042551103001001c441e5025250170700c6544450b0410f9a0314511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 656165107 1250 656163857 656163881
    0x30a080f0601020a02060304050111030c0a032313050102070c240801030c03030f0203090907031d0106051f0c050f100c0809150a0605060d0c09050612010308030a0b1c0510 75
    0xb21013414405820000000d50f8480d02030703c0041003040343c030450410765038402c4881c00701540c0086109065a6414000d00d49441e800c104a45c206100510034851400e0003d840c40f031a0705c2ca1100c0c51020000c00790181d840d0681c102e1460b942035079455010030070807007890040101144001e42c0d5034068a02940b68141030700e0300b1540106209095640558040002070002015840240851030382c0c1d544043c01c0a00c5103065540115020a00c0c2c1e0203c111386e803500701e040d902a410114184040d45903014040000f0000303001660900080350780075105180b82076805006409203030a429414040010045040c8071400f404004d128031001d000c44003040c058940c00c0b07540d04031010400c641c034040e100c990380094940700c002038850341c2c3e40002000780c0e1200c0d5524081e00c1e110b003c2d030100550442075800040905a402c0303454101720705042485040e0500000b04078040200108009080907800b60700c9084015015404030211402081130b07108403884e0032925032140451050f582310302800780c2c0556083c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 656166357 1250 656165107 656165113
    0x108061206010e10150f110f250e0103030e0f01030509100b040b0d060510090b030706051c0212040b0105061c09081306050c0c0625030c050708030a080f060102 70
    0x42003041036008654054401c440c1c4003404d0b030b40030441c460305070300200e1902c01350b840d91003007480750603009020503041c0c20346094a030304000140c010890000c240b00750314101512141c1e80c445401e0f0801c800030b440c26008007a030b00540000100c01c0540112411075080700888070718012004000046040c0c8404440c684510741003512a2b9021446613042010651001000416880100c2010640d010081503043e00c0e03103a10b8109011200b02e00701c1442010b40742450051154490050200b0b5854005100c1c00080290020380c200c2e025280303c0d641d140a000050055640b0200e40a031031103201c03015541031342d00024072000011240741000445107544501a042c0c4219201001150000c05407000c0640d44202c0404c40890b802039a01ea1610161580e40c58a603220501401900d142035074070220103000d848104181090030703404203012000c10034100c40c0000c401e2100e02d021180e0b8000202e00074070314422848045810b94005c00606280c0019640f130307003526135444c00303151100d203030554803e80503030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 656167607 1250 656166357 656166359
    0xe0715270e06151c0b030601031205130504060611010b190b090d050a030203030f22080a031d0d1206030b01030b1f1d060907120f06030818010806120601 67
    0x14041040c00e42d445400100112180941c4070a80c807000d40c85151100000c03041010800d00d01d80741441080c8410341e094004014643c1180d450488070f0716090003100511030085011040000e103006010080d20700074006110346a5281005003110300640c005a104d0f500300311412a450422501c24100c0008100044074214a0081000104d600032000076800c1103d6203544404108100542c0001e2442603006550b01d03d4140140443c480d4081c281a24984444418011000c283c400c0c400745a60090300c5647c0c0e40707803c51400d40007418000d0000411032400c5c1c2c00341c42010404600d90366185d80d5a1500d1000c50805040e560484190b400001c000032614401800800c1c4d2050116034484a000d0380e21b460114003909000f444004e42d40021b01d0b040807060031201203031b11400361641180e01500c6940795030070121000b40024007840d032441c20050340d41030001d00c4000035802c403000440d0029a050b9840468041000113411008051400708403010007084460808110303100b010b1030b0f001c0151a0907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 656168857 1250 656167607 656167619
    0x60b030601080a1a0901120c150206040210110a061b0201020403020a0b0f07081c1b050d05150d1b080304031709040917091504060c080d0e071527 64
    0x20022040134002d007107401c2080c403c03642c561040c100c0c003034818a100d40300d07074840c03900d04058050525009440c0200c0c03000546040e0b40c0d00012941d401540c11249909840e400020448100c00c030400b1520452007054400c0c400d1188581c009a600d42c10b080040b481c0c00b42c803030001d909030302c6a484020740000e2140020071030012000040d09400308001c0c400361504e2440c0c0c0382c441440d0807010140d5442c400d1f64a08021110745c0d0711034000c2641410010000c05152031101405c2d0340600c2d031620b41102c0d01c500c001148021540f040c00301c4141c0080420101c0802401c04a1689031580c00c4180e41030300501e4040f400c0130000090b141100e134443d200c004424498004012660000100b080e08161034250100000303100107454000b0440522110761501e1180c001c110203140e0079081b00b015100c0420041c420594002e4142c081c6a420060188c1d5a800c03c031100320040c01d14188001d014000d0081c080703048030300601110140d9100303550305010320705c0c5040c04400003002c0004038956016010010080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 656170107 1250 656168857 656168861
    0x11104060c060626071e090b130e0c241b100f02031f0b041202190321080c03070c0f0203010c02210c0a0206030408041512060b030601080a 61
    0x181d18840c980c0810344030381d00c420552501500e06064a014440b141d062080c0441c00c000c048000c100800c0c0c207070000c034070351400348200342128010011040e8640e0203074022900c425038941c07070503801400704200012030001200e844112224040b44126840038001569400b9024000100c11551300006d03d444102c078400242940e9030107041030784e805400003880700c40ca41d911601700d90181c80c1c1c038003580d01d01d8084505130809071001c04c0d1032082020b03203170207100c81da59030400e031f40a813202e15101c0403868284d8000940a05508041d00d89594091000402001428008012010b0b848081c0d2b4000090110b016655000f04540d014140d010910010754414850001c03850410b00442d0aa02450010340220b403d4507800106400075904c150788108810942c1001c030b40c02c902d0755400d0a41001205901c5d240c4819003490301070710a982c080301040520205004840041410040c600329140340101e016011008908100700040d26200e000214000300000300d900c600016926041d9039601c112241c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 656171357 1250 656170107 656170127
    0x1712091c0215030108100b01020d14090a03021c0302011b1704140607180807060c060f0b0d0606090506090105010c02091015030603020307080d021e0c090103060c020c0301110406 78
    0x19010000d18801000402d2000c001c502910280c009040113a421029072426142500710081c115441600301c10b00c0c4070742c00130554001d54070345001259900c07141c0002880f5102243c1010b54840d88800f00c070300c49180e07500e4200c10414800e8000740503e00c40c4056a0000c44010a402c1c0e01081c00700300e001c81050300c00c84149071301c14862040e00080341d443c2c103a0181703084011030b9060040f800049028040410702801400101103040090503002d09001001304243d04003c0c0060400e0b44074806601c480c120f80c0c000342001c80c0c000c0c01010041c43c2a0800b240901803c1c03207034030300442c0390202043c09401c0461426050f00c006844100d0b1100580e400d01c100f0b4000149254415001c0042c045141e0941040100800b00341c1d179030101d002819401050304213511079110603410307408501191981038001c18400d00d404140000754100710f01e00d94190b030034142480c026551010211001000b0801c403640306000c500450f5080f150300040303410a140c2210543d0100301603940307080c03004003c05803040228003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 656172607 1250 656171357 656171359
    0x4051303170406111801090806100b0315060c06070e090c070209060301090b011d16081314100203150a030302030417100504030f02160e1617011712091c02 68
    0x2448880c130030603280298104804c003001c0c0300444040e42e003441d0717848080940642003a0014004608081c3c20001000e81d141c458180d2062020000a410340e44150349030590400203012282e83d042070011554070b518040301c03c2c40100e8400c040800103030600da500c2c00c1c82024206403071480c1c13030711580030080c1441e00106801d07419074030369001000103010a09241c0c000d28501c0c08003010100c4c521505103500400400e03c492400044201401e555400100c00e90801c205440035850143d903420408640c0c80d03100c280d0b1181d445207004c11050800c85a008510900c4181702e0032403120611010050f10030218803002d00164000d0005000302803200c140d074003503c22610121036603a03410070427640c01d590382101c00754085010318581025258041c811450700340c2e0000c040350b100c84d003040d00b1078440600103813058080103401c988400100e030042241140308855007500a10303075a90303100080d00246624003404018050080014000c004100035699908070041078055440031407440409041ca00c0702080e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 656173857 1250 656172607 656172611
    0x3050a200a11220f0e0606030a0f0507031a01091a13020a03200318070e1f08060a0b1005090a0311040207080f12070e0d03110c0307060302070204051303170406 70
    0xc000040e09044100d0080e202595002c142072441d602e00700f0840d03e110a2040c411b8100340100081b9035800701e03048003000c0d4030100303403100380c01d140c20f0191030000640c01c0101000d00e6843c00402d400048200d5904032070071000184175040011448200e440541404146c100751940340c0c40c81c0c11050354001e006070301d98901d40000e455904c0c2080582944413610081c400a01c00403e210034201d03541c684045401918005107825450304200110300c2e4802840e06070040c4800364000c89400f000d0b21031500500490045802d2400e014064070014021144813920400400551038400b900941c183c5203543d00041c2031849480c91074032411072510200101f01e42c056802c01c01c00c00003412142c0903041940c000762400c6e494240c0c0b9001c0c0c1d281c03544054202c405101c0c100c0240c00c01030707a0b404015118550302d80f40514904202401071031500585400300ca50500a14001040440d819409000118004c45041c0100d071030788503001d00403c0d601540030300090504043e6529a590303003880150054491880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 656175107 1250 656173857 656173879
    0x15150d2a030e060a0b06120604110721110712020f0307032f0d080901030f0c0e090f090703140a05030d02030a0e01060506030a0c140703050a200a11 65
    0x10184044408038204003099503500030b80d00902040003480d03440ba581c80003c011003103400340050741c0f50107421034040d000d00c0c0340390000b10f254442c0d41007034000705040c85c10640c07103a045107001400008e00304d82c280c2c2c00d101d980040c40b842ca0701c01e001d8492440f40000240190500b0034241e40307078000e103640e826138110882080c01c6a59440400179103000310300034a50b01d0309111203c021824607080d0666134411019190301041e002e950b60744038944030594000401c42d50740000c00011f0740503101204c90b503041d5500d4034507090049500180c0d42c03441c222049412045650300d403d0310b80e254040c245e80100d9147d001d140140300140605100c044c19401c0841241c822000c90790340c1d1851039210b82d01800215030044188410880d16000780040c03507217070f00000e000090811010421501004018810f01502c1341040b1988900410310341c059130540006032651803800e401c01401d40e52181c00400001403890200030320300e61341c075800301000d00c80400c060b100040c5c403074944d200402140e0500360741c40103085103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 656176357 1250 656175107 656175161
    0x50f030708030309011e0c12050403030f0608011b05030f18100c0c120309030e0603060f2707020a0f0818030316060507020c010c02040c090b030f15150d 67
    0x203107203e104028000320b01d0b00700c5100d01042c601b00014403115590308105681d240c20380c110b40a090f242c203101d00001070710360721800c0890150400f101a03101c9185003110225408030306400400411a80c1605072200003840308003190326100882d6000c0404101a02141c4050100b0306540c100c40d2646040720054810b80f40c1e038000710b800000305180403940c000e41c110200503200c01256040d0074941400c00111805403405401d400c0428121442043c0000000b8043c1c0c2d29002d00842c00c01c0c014166000164501c081c500c43e0f4403006005d14141203450f40080d41c1c0b144002042c0003d01d40c890a840c00040d400d6490081a03040070703038040d9100384400200406a20f04202034008441c41c2d10300c0c412081b03428181001141c0c0040e008000319040814030b03000c5a6048072980b110700d0340c140e6002440008051040704c03160080e401c40f03010301f01e000041c8040c00002101c6580a00441c4900084480310b1804000c0b101007106104510303010300f4011b480c0d40031301661280c122076910444000040348424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 656177607 1250 656176357 656176363
    0x1b060c040b0d0b0d080c01050106020d0c0b06010c0302070906081b060724060e070e010f050901091a0409060f080708071202120c09090304030c0b04060203090d1a01030b0603060916050f030708 84
    0x20501d46c079269911401040f03280c2c1e04000d40031402c0680d0401441454a40d107a58a440e8001010141440a101c00e003608061080202c10000d00302c80100700000c90b102d03690306d0389039420914512440c8881d045210600c1c60b10208945840740d00040078400c1e030032003101c2c1c181c9403070f402d240c044100c590742c0300d00150340040c00743c00a1085d0381c26505d5981c1181c600c8005400441d40c002c844040020502c41800c00341d03000610081650343c9950b202007425602a03002c001441036400070407043d410f00300001226411142032074142c0e04c01800740c551141e02c50741d145a40754011310504650b40441c848080c0903017042c0400746012030460042d502c2c615005404150088002e640401d01d5a01c0064100184440c540710100a02524900d4900d40b620f0312400965900491559a00c18a0354100710780400005000400b40d0420307c5100703001942e0b490a1007031140c081240d406019008000004500c1040407510304483c0c01140f80c002001801d10090003414580c1140300c80d0940700d03108000c54900342c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 656178857 1250 656177607 656177617
    0x40f060c050322050c1504080715020d0f0906080606090901240e03030a0807050c011a1309031d03030912011505011e031802061b060c040b0d0b0d08 65
    0x69250340d5500d050440704101c4141c0c2c490f41c02001500354120003c000348020640d100441c07001c80d99060610343e09a407002080c0301d640c0c01200729110b0306100040c1188a9604c2d1515040030303409030358244a001a0070707160341e0415a4440d0025095080512005018820190b04941c000d00014100304542d404503005050a8005513601315400361054100b041104c000700c03031040a4500709450000b040042035503401206180000e00c0641e20004400030710807000d441d00c00284000a01c040c2c02251928103060401d4940c0d64005d0b001d81c00303506403007135160040c0e071003ca5140c1e540040a286e4110cc2c0088003c078508982d925000c1000080103c2e03860744910f055481240c4000a012901b460055002c4400365009038184403030450509125142d2500364201c0360101c1c1000b203001c1c015806d88080318004408001e42c01040403920001a40002c00103071016440c03c1d0841e0404c2e12902c03942c0710036001314840d44034185401c10042806c2040340d000b0039114100580029140441c544e0307144442c0e000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656180107 1250 656178857 656178881
    0x1c21090f061e0e0a05070b07050c0307031110050a05091311120613060b0f0a03090c060833060c01091e030905060906030a200c070923010509040f06 65
    0x1569200600b00d146900c41c0211060300c0340c0081103440c42642c0c40545032400c6104442081c5004944502400b43c180000d4900420041c151111140c030303468481d445001c41d00207076029603504290324110300c0c080d50407144481c440e519a0342c1040707581c10400c500d00c08130201250441d42c0b0f4440100074030541d40080c01c1d00c4a03e00503465007900d40359040c40034924018940000382ca00341201001490b080328211908a80c00200407070380d41d03d0315501540640b0300c1500040061b540c00e507000940c194001102400b03482130720300c0348413240c024074018814040d04061a982c8000c0424040e5202c1c6003180050420703101101c00418407074a56101d1050030700090b42c050b4126420707006060f0816078071800301000303480d0440301d60341007040010204800b40002445001c500d9510740f14912000d42041048a01b100d030500c0f92640c0d031401c0c40005480d0a01d91143c0446141846130400c1c07404450740325440b00503c41c0c54402420b81c80e00d07040010441028000343c441e40118580307000802c07850300500e055004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656181357 1250 656180107 656180141
    0x1050c09040b0301090c030311210a0e010201060f12140607050406020d1d090a091401020405040e150f0705040305070905011404090210050c0f030301081c21090f06 72
    0x311181803005854120850a120381d16165008000828000328401602c1d054545070041c9c108000c4541c2c0703459407900100c1d0b01c02421040c0701d00385d2200c1100800c182c50483d901c101150111a005a09840700c900844140d80654101840f00c0880a61a4113080b801861140480d0030b400d29101c3c24518151444400078000190a201d02074042003242aa4016841c106800340304442021604180c0003000520501220005c00c0c0850401d4018a0040b80c01603c514a00504119810f0007907019204142c0107500342909010714030000301d03004058540c5201401c82d5a940c00341180da181d50010201d40610000344400f00c040f803420400f103405400340c2c280004a55050407046903000310a001c3c0b9038407841c00d0000501c010f032180903e003415407000703040058a03984128102410085085044c0c0000e11006c800040c07001c0c00082c8200b4020740ca9082004e14200140b004c0768140680c480042d400381d81c943d03540100c6855680890152805050b0444068160740e42c2d0a0a9039a09000750036841 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656182607 1250 656181357 656181367
    0x60b030702070b0a02100f02040b1209060106030204031a0405070f032901080a03180519150e1f09150f110c01020a0b1807030b1f240c0501050c 63
    0x10780412000d405404000c01c42400c02c01a104001d65940300c0c042840e180319202d035030210380d400554040ea0301030b1213840d4505440d03021025172115102c20885401c5550b101d0039000240c3c0902038400c403400d032078021098541180c0060301c24030a040001e40102c50500c0344400010380320400c90030080c081d52080007048024803e03807908200d0190300200c070321602c05d07181c4010000030324000307081c0c3c0426034107050101c0d207201d800e0b0b0705521501c110741c40203401002c4860401c0c5c400c00c09105030300070380e0f0301b1200e03401048000203000c032118245100159040311004441e0221841c845018004c1401d0514054521540326a02d4910591401c85c405000c1041c441d9111940e603044029420100c810f94001d0900ca4400d00000303540d6a000400a0a8800000007080300615000300e040b4004050f1b03411180140d587e1303d0700d554a078004603a650b0b841c251030304441a800c0d00d80d103158000c80309105691b460383c0f128012000c00b441c00140582d024072003104a40c1000a00c00e00030248903a240c5a00c0f25161 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656183857 1250 656182607 656182621
    0x30106061206060e06121504020d0b120102030c0714100c0c03112a04020702060705071e050312030a09060504140d05040e0a0b0604080303040c24080c0d0f060b03 71
    0x15440d1034202a043c8801021003491381e4803580306540003000b05c034084003802d456250007001100280051660041c2c000503800340700c1c0c54260483c400421069600401018035500f0303240c02c0b40010b072051012054100202000300d4000c03001084c003400b075401501c0d410f40100c02004100c2c2d03d4904030601040308c0f81540b4042c1a04440701d8174441801d6006072580b0183c110011000c40b07940100c10810410007000c080c4107403225819034141945c00f5000716a40c07403960501c181e403024240b2452142a10030000b041614080e1044402191005002440011003200b507040b540d800007000340c003425564502a101091017800f9441c0514001c6a401032070702405603029081010b9845031006104040004200d14001e021603a507011104550001d116400781d000604140b00b01c0c0d102c49928030020061000b440340c460b40080c03c44100ca000480b02c180d908000f0510041c2081c01400407510303402c00034945070703240700081407503100401000070720a869000c00011a030b0380380c100c0020031802008000013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656185107 1250 656183857 656183861
    0x120910091d10080607080c0c160306090b06100c020f13020d0f050a0c08131b0906050103050a0603150921030b091012120c0b0a050403120e030a14090301060612 70
    0x103084400044e2090340303003010001d00b220380302811528986100040314101e188050000d044c4c00c0d10088003036600241d6a0620340c0c0074244614040e1504010384e8046809480c0c05446030060300f40649030307000000c1061702004020404410707a0f54000e0000540140c0d882d01c0c074801060903403d10000012400121900a0111440101070f0010103183c8441883c6d9250041e10342584504481d10f90340340b0807140d18040c2c100c001d501600c3e131b0316012403880c08680130308103801c01002e803242031340c0400c12a0b0320714400b0419141d481c40007820300b05000e030840c02481c280d80c01c070322042c80c0155010001c903d144101402c5040017a103558001a60702c031002240303450704040d019040f0945c1003c5182c42c40c107041d0302e03401788000004020110705504455401e014040c10074126020380090074420305103003950300c03100505411201100081d460300306000000e1401d219180c564041c2c0d4004500b0425181416180d10340c1e00c0245000240c8140108211076034240580f17000f5082a56410607414a45d600c00d900b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656186357 1250 656185107 656185109
    0x1c032a08070302030118090c030503031305120909192c12070210050d090803040c06081f150504050d0609020a1212031e2c120910091d10 60
    0x70405004000400811010140010300c0c02016080010380c407900e8500b0410700d1915900041c003a020100c10001c038800c3c1c04924041c924080d20540d195030321800c000032001c0c4a03e80400707a0006a04021425044522840c1d81d0740b0741e80701c000010320003801080e61440403010807007100c22021140c0703c0c0c01c500200340030f0200481500000300f814050303190f00141300c6580c0019000200b100100d0248089a45600098102a004003d2503500c2c2894244001d011f1598000d00010408803004560348100300395a90011030400104035101074148081c2c0280b00080c80c00010401c0f10600c80480c0559403901080708480c4108400540020390784180000c1000e154480e914408100b400e000104160b102a0440c00d501c1e07260000f01c84c1101e0a113030302448440083c0350805480c02d462103890304100503066000c2d0780715118806c41418401602591003c2d21024042c44580c240700c031791080c2c00c090310003101815180c10a00c0100791200fa45800e08120031106030352580001091000400704605000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656187607 1250 656186357 656186371
    0x516020604080d09030c060204230d0308010509071404090b0127140114191b03140f12160909050c1218010908120603060106021c032a08 60
    0x41428507054940607214050030003285122616800c18600305803051030344000c8560310a900315103d64507004280806052480792584105000c038407014185050301841e60001c0d0305680e4142c0d0f680c00c110901c508801d01400110a2251452448109950140103003010b80f05141d400104100c0c480001010b4811034035040401881544683ca15407940c0d25074201954203c0044280c85250900100c13030745002e0030360002c04140c0208211106e1801e00c03800000c0009165122a0700103160070301700d420740d28128030090114285100f0518007503000340c06010981c0441d40100d0416480160140d410740c400c96400804081028246440a4009042c00040c10042900300200c2c81d041c102265180700b1510300f000f1103240c91000501880d540e242120120900d0030090041251602c2c0280c40c0e81c101000c00f05d10100c403800041c90034280082c038581203550641c02030801d00740021440c8440e00c89816408205521800340004110307c008440110340c84001c1300402080030040c0041c001f400181c102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656188857 1250 656187607 656187613
    0x1a03131b0801110c061501020a030e0f0d0303050a0b06090f0d060209030d20030708030106030203040203070503120a03050109090b0f07021011070b07020111040605220608040c080c130c0201140901051602 89
    0x141140c0d9000412031080c9d94182030030f42d04000c40302c000035003407845450041d070f1005040c429041015803641100c0e02520f01841d041c0401a4020b0401201d80a203036841034201400c4c4070614441d1030000890401c1ca402002c4c0145040c00800119080443c025000f4011454901c07030300a00c0000e4030707500e6a014006001441c102091561282900d10040c80341c02304140d0007202060941d58188860401400b006046032031140f00d800c4840e1881c7c005001c0b000209182030300000c0e105059020b4200081d0f0300c09140c102507034034501c01540811019140c04110b225003148406501c1c898410082080500241c068a40c045c41c03030f1203804200010507480459041010769182d072003a000580c1c0030703603da43c207019454000c5075655041d040b00342c8000301010489907100181e01c03600607024601030f0740903120090a040d180d000707840d03903004007141045c3c200340303084d40c0e030003101546034400e01d02d0701d60602c0081401079001081d80322081042d110318080b655a40240030181d0340d104030034142e45040b4006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656190107 1250 656188857 656188891
    0x6070b061807080a0b0315011e240c0305040b280e0a140301091b05010e0a1809060605040504051b0414012c0901061a03131b0801110c06 60
    0x1000302800f4021340242d503803a444003c003034040c4d6414054001d0a1000113032101603981e4506140511440365030750780c082045c0300d90021038181c4c3c0400744140901c40049040482c01d000b410704807150141c6c10415810440280008940341c01c12400030304009110746c5002458000c826030000800a81403130350300501c141c00000d180e6030385507204c2c2c00044a0030b403909000741800c0720001c640900002d50f4003d241d05000014614540c0c620150701040e20000eaa80c48000d0000c04144000910b00340580c10283c5c100d00c0443c8001b002e83d411001c1c85c80c1c4182804643c0551b1400420306868055800f00d130b0b1a08000c1c0c03411440010b8548a0b0110001110103011800e1540b0310241c0d40401806000307080c0400e55680b82081c0c010070708400180c503d014071714400f440c22042c0a070080242c1c0c06001d82c00014030074074030300700c03022003003664000c2d001e071040c442a480440d81e40d6030400050348401c03001c0a0741d07c4400140780c0401e00c01c1ca601c81080740c603880d40e40e40311445060b0034080d00420a072009401580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656191357 1250 656190107 656190121
    0x5010b0f130c050d060608101a030109151d1905071205180a0b01060f080106092112170f01240e0a090905010b03070302030d0c0305040506070b0618 65
    0x1140448158428001850b42079058100c82520540e8501c0c91400d080c0200042e141e03600c10740c1760303105103003030f0048080540d101d5200c1c0300403d1411042040084040c4010301220403503900280ac0344c6103500f450381905590f0b003203c1c0c50380c0d03510042c00c0c40e0150b9568200803030020140e903446c8520141120800c15443c040202902c007081841000405a642d02d000800072740d24000c2500307014802e14225208150949410f00c0700301000d00405000034201c150842145015010090580d03c4e140c8840030002c1c14034494600400031181100d280042800d01e08003c250070207030f01203006180b45d0f10010b8500395188640a0908094420800169104d00400003d0703d0912014101b8229840f8141d2020000d04104da82c00021040d43e5030100c024000080c001c80c29500c05030700303244150000d000c01040e2404254681980c1d11000e90103403c01080038852502c190380034840743d442424520708040c1ca610110781d01c1d0b041146c04607400d065403000d1090710314160704040c00c620112000d81d509450014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656192607 1250 656191357 656191369
    0x612150106030c050f0d020901110712080a21050105030d0c0203061803071509110414010608071808030d0b06030112020918010504060606110706021203092805010b0f 73
    0x111500301055912001404914807400c102c40c08105101085d50700c50b0281d400c020020f40c4040c6d041030104404070444000b0002c04100702040324480407481000204c00e89404441390301441046082122511440c0d5440610034440c1c500041c007048d00162541c10f2a0a2500c0c05019450120901413010304460040ea40094219481400c6000d00340403450031540d19071441c011800000c10f482200c1800c21044407203070b0300c0015010300402046003079404003818802110403030710401e4150400040107000c01c0b801240240d801020a10700b00203242d11901c203da0001e102070300056816000040d02c402c00d030f4034a0091400310b07072040314010700d903516241ca01001c50703650150080c014111000005c83d5442c3e020204000f4400c00c000a20142c6028074082000b07086c1400b540000c900c80c21204c2d500309000190a2040d10038540051550015465200d100ca400042c030303141041c4a603200d03109921030708080400c1c0303280e244440360f4a02d03030701d80c5050f42c2500c14524030140100084003910315269070300c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656193857 1250 656192607 656192609
    0x11072103021e0d0608030c06101203021c050d110d0c0315060c050a0b0106030e010e0606060a0804021c03051206030c060d05060307050a08030c0c040c0804290a0506121501 75
    0x515509a501c0014895080180441707500606a9000108103040f115402040c03961081400311000c0d4039050300c581c6445a50180c8a2000d40141c0c000702456070914508800032425501d04c1c00e00d0b85c10464519032840c16100201401150042d0101d4510380300d41c403900450a4403680c1303003418040c0502428441480207007500ca0201000034a10b0326000380710091100045c401c5d00008403641c290b0311030740007401034901d4004081c0341d5841c2043d01d1900c4070b8040b80550007100c0090030f2074940907441c0011141010080c0040c0c0e80004000000308400b040b00082007281d5100fa00d481c0e4507000d80040280340960300401c2203001b500704102e01c00455884204980208045a10024940e01c0f0240032074500051900450303040084180042915807000021301491080c4501300e070040d0140c00180400d0710040703184080418a80c501003400294445c030a444031002c00c035000d041d07207290303540401001102034031151000c50b40c0d1b5061010501b0040181c00582d14894024550712145600c00d0700c00c0001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656195107 1250 656193857 656193907
    0x21071805070c0813090c0f0f0c020f01030222080f0d020f1504080c10240e01210503031005011106041a06012c2103040b0d1107210302 59
    0x70000701400341c80f00e1444484040c00e81d54004000030741b041c80014040c1c0e030000c04180e01007441c205407841040d04c40d8644092042c1d0103031984041000740e10054000e9082011000e000101070310b0101c00807003000d07000100803c2148000c24401d05407007001e50814a02d091035208540101055034500031000030058040000f01c3c01c030726180c0d981c5c0c0c00c15224074000d580400755140100040703646221007640000b241d0803c072152200d00600007a15900396020039100ea0700000c035021004014192007001c81014644801e0903410100700d150f0345890459108440320640380c0d03070014091000356807051000b421204044002d08050405032150080c4807200c070040800c182d0003400049241c2d1040c407003900383d024101d04030720181c0d5084540c12554030041040e42d000c0c8a5401da005841811406070000c2c440070580610720b41400c12580018540c001031035464955103401741424000e10341002840d4060055024400f40340202040941040c034440c440c0023014014000546d690400c83e20040c4c00a030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656196357 1250 656195107 656195123
    0x6080702150901060e0f0c04150c320f0c060706060b040b0c0607050c0c1011100e0114190209031905010c03290d05100e070819030e01050921071805070c 67
    0x25540904855403168ac00d4003c10100e074014100540030b0303d4204400e40c030f080740301d401c0300341c03078001110140e03141034581e07000d81c00d0740c0242c0c60342800d400d10310300a240582c042c907004250780380c440c3c103d00841d60190348003a01d42c0e040028006100c1e072090015540080d51417504900e000ca0402c4680e80e5111941c920a2041644020541d049170107000651544a0010240c4107032030001c0d410207000b0160051081143d5082071006500c2d1580100c2c030360300c1000010320a074040328840c5250070081d0806095a50941300b003080780a4200d903250300422481d4420380000c80d516001c08070050a031104051f6036902d020b038a2401000720030400f40100d40400e41510f5040755042c3c43e0030202c1c80c1002078481c005a10b0700c4c1001c0410003420102c8c5500c292111001110094006400503003038084e4491805400100340d0010072009611070300c01000350f00c100030202c4411502080000d00407846469100d8090382c8104000c01440011508190038280d900c0020000e9280200380038115402c400b1000b040c6075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656197607 1250 656196357 656196389
    0x13090f0e010f020703020c03010e0d0c060216081801030c1b0f020d06091a060904060b031617010b060c0a02040903050d0f060311091006080702150901060e0f0c04 71
    0x101259000c1010000650000c0c0040254400064001d50007044298014003c0847d044a541014020801010400f800602e81d01c40b0221040311017010742101120b20030303000c0060304c00c00790715a09220301440c05140169914600d03608005085030754072003403a050505003c050800d480d000603008050040705c0c51100c50006941c50984001d228014000b90b1010b4583d0b1110140b110f260312103020548624801d614041580c800586202003c07100e5a502c08100030000b400207515400606200001404841070102c0d0801c2d100c6003000c81da008403550001100c02a244440d003405681c4ca0b08000341c0c1e9103840e102d4006800ca8070780e00c004801038040d54446016900700351060040364070082504004001a4424480d41800340401748401e483d1780d14407a0b0540604c2c50304028940c02100b040e2a0280010303c0c2c08410354503984001c4c1041d065008601e4144140100c034841503200d444d40f0000010114141a01090030300409000420704d009290708018007030980000326001d40c1c0400510038021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656198857 1250 656197607 656197631
    0x1017060106030c03050f1f030b150301050603070b07080d1b021501171002030c041220090c0304030c030203090d0606050306010b0403120507020406090c021509061303120e010507051b031309 83
    0x214280e88c0c0010710180c0e0070010001c0401d0700e8180c1c56a002c5c1c04074000d00c215140c1000301a03a4100354001d40c8085001040307080000703445031000302482e040740d02001c0385002d424005058941180c400301409070b00a00360310303074180107910f0701c480c054403d180c0d20f10b851029081d611030380e500c041c14844080c0ca078004042041d2000705d0080c0c0b402440040144103000ea19072400035101c0b07102e9004862a130100001000882c0750410145114100b00b0740c40350b00395519924111451041a1001c1c1c007980000c12144c440740c0c9448900e012414003805010440914060a01d4505034050b440345150340d4082c031080c000103070481a101c44003062441e0550315031900f800040d00508550303014a164602e0100c603183e0311a00800d0b001d249808000702d50840340d89000145807100000c1702c8c040d59181c03051005d41e001074011105400101800c400018a40206954981c21aa010b0390807002040c0c0c00f140c0e6030008500d21070710203994403008c006142071010b01081e81c084110076009400001d0348410581480c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656200107 1250 656198857 656198911
    0xc060f0114150f0a050d0606030c0516030c150614060a090e0702070b0406030b092401030903050904020a0915020318040f2009010e030105010b0f031017060106030c03050f 75
    0x100601070b151403544c0f00c0c1c0c40354010f406580320b2164000301c40d0810b10009503a81c0a4401d0070300b840c8180e140d91745020011490b44030010340c000800c50601841221000201e01b071440c002d01c402da0001800100c440c1042510241114a000e81e50301c12356080205c200410383c840302d55403c1700c40041c0c1c000b002c1e03121218180d003414140d800c035040400000ca00080c9207607240e048035001400564812060361120040c21002e4285140c884e8000a24064292580c0d44298440014a1301a26049081050410004050740c0c0a45d42840000d00c2e881000d116000c00d41100c03603001ea90900003103280c07040010312030305e1106440c4039080c810b81e80c0724000070079141c1c03641081030803030800301c01142160790380f050002c0f690308182802800250600302412650505103c0c040c1610000000c8034103003407230b18200540d294402032110000e440001000a0600759211055240a074040040e24140d8100400113045079200d138462000c0600304414005042142c03040c0640041c10b074542194100b00035040080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656201357 1250 656200107 656200117
    0x609110f1b060906190203060d1704120b090c030a0b07032307120506040207030525080c0303010e070302031312140d0e010c02070503060f100b0a02030c060f011415 72
    0xc5070307018402c10041400004224144240c40812000c0e0141c010076140703000301d000444145402900e6070540b80c000c141207205078080320f10000c2d03c0c545420745030b0090900e501c5940504584041c03100003400b401d00c070140304980c50044140c0052403010015200c2801d1400d01138000800e140c2d80d00340c4003006000300f42c050340c02d40c00d203d10195424105103400400712000501080105440c20000c11243e14040c000c40b6841501541c41608040c0407281c011540e030b41300c1401501112071140039500051440d405040c3d01c0003003801441d01c0758074200c00b015000c44014024410544100b0400042c9206101d011035800d17007004912072071070080f403002d45203058142d00400109902107040440d02ea280d0b0801d43d844d4a40300e0003440f41c94083c10061b655503056016076541a0006400100c051080c45a600d92010568408410342542d0340c503041021b500100c60000140c000089411058008024907600048280a10318581d850490110041c0000040c0346221341d120911f103d00d0b620180094038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656202607 1250 656201357 656201407
    0x1303060c230c010605100903080c03090d0c14150f09030c040f060303020f0d0807110709090b010303080f090304061407020a0e0402100807021f091b08010609110f 71
    0x381141d101ca81d81c5000c69002040124110341c02c0c00030102d19402d007806942e0b0021a01c0d100c2062a81c1555100805a048011405413600c400e005002d19a0b554007140b040f158061a07080040d6400d100300604902d003c001c4080c026218a011091102114021600480c1b01803940c0e541325141c40c00000e0812803a181d00f01d501508000455080700e00e140d0141c01201c0c4203408890918203402c00c480d0f01c038944042d002010401180014503400d024022030841c080700706003034a40150f29001040c080351031140080d00d19022050060040540020769550018103424549290f03240c5110116680c2c81507014080030040d00e0000c1510144c2e00c03c0541d2034013a4024100f8036440e40390880c071503503d502144c0c142d02c03d8002c407a014000c28060f10f5440c1c0a003600340d0203414080e1913102c004001c144480507800f0059503ca8409012030024503100080c5440321408600252078881c555084d1485900504030031840d0600912541ca095030894080c181c220b540c9a841d400c1100600b102500810b13030903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656203857 1250 656202607 656202647
    0xf031a092103090706080c0d0b01050d0e0c040b01020c0901090209040e0307050a03031107030f0e0111010f06050102011a0618220f1401060804030809010f0c0c050c061303060c 77
    0x1e1090380d03041d006148683c04020444041554400d021101d801c820b88401000ca0010030080040c0d42130790b00209084101030600a10386075850070050b00f1180260103102c0980c010201c205036600c1d1900905c42c6d01c13002440284018114070001861414041c072444600950014124013191101d4202c06059800c140999072203008034100580c07251504c8204a002a00e44000041030840e20000d449c20030741c140d0346000c4900c040150994034103da0341e400d941400b1051645d040550401d000ba0701514008a0707000c58803c0c40d0000190070f440350f02c1d010b0a5031007581c803040111a03c4503400d8890000310303114070091044505002c95200c140d480900b10307201c4a000661218034603180c100d1210941070b800c0401c03040019180c0c62070806000c0c082c21000440803008900807070310030f440c035a40100c28400001140d00c0e900300c0d00001ca40d11002240081046010303c4803d100050111040d00c00003541c1c80c7e442e2012043c451407020040d804001c095075964100791700c0541c807a910200d0b411500f0041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656205107 1250 656203857 656203903
    0x6190f12061d0c042106151e171b1311030114060f0a030507030e0607020a0203070f0803090d080903100506100201110306060a020a2a0f031a09 63
    0x142c10305400041500d41d4880303801241200000008560894004a100c41840560007150030300d48500054192050307a00e40c062a06103075041c6c03124800030240343e0204100560130b401000004105c9074040f03101895040003040140d4400b051108901000e8201c40f0246801d140001d40a443c50080903218107280004bc07001d03500f40c4800179410f03141314000c80314903040c0c80010880340b40302d02d0402d100e80000501c07e681d40e4038000c3c4c00c00d5800230510700b4089044c0d004542400e1a15404075000c00050f881039110509604062200c00c0190540a030400060b50501c80000e42d84e11401140d036000d400740400ea07000b8130489a06032882c840c4001c05441d040c2c80940c82c92405030006817030180c410a8945140e07001140148142080b159203924203d05565131582008000d0300310a88100c21360003900004400600264101201104203491159108401e02c94944103002035802c503400582d0409400c5c004907203c3d0f10140b101155410f8111910b0351f9501406042944010410a48004d040c003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656206357 1250 656205107 656205119
    0x2100203072706090303050721050d141302060a120507080a1a010e01050d0b180a05070207060503010e0a1d1e01090b011701090510150506190f1206 65
    0x41d190100845070b07141c80309044084055140c94243c1c401e020200d0041141000003d0141b03001d804034500a1341000c3c003410001402d10842c403404000342c8002360001076940a503403010300c1464032880040700d45503010314089103581042d58403510003a1168101007400041240304030b4281c00d0364032141e0014081c60801c4000a4008502905c40700c10b0329051000c0030047c0c0a4a072045440300005940301c1e000f02a407800199001c5d170058502c2d00e0b0b0284c85103108201c90712030810b01708603956201600d400501c0c4c902000001c85202610200c11500070f0202000291341c00820b503410749a91642e40d18085c2c41c0d00440070004c1401d540c5003c3c11103285c2d200710b1240003000c550b01011154501d07003171800c07900394200e060890307000d600003d10008180e001030101c002c4072001180c5101d05d01000145c1045180c6a80c2d00c0d0252002d00c2920f10780c0c540703000d000212682e038000401090191070341c3c2d0412440c40d0980340c0080004402e034040102081402400354070841c00c030030760110f102c201008099203c04c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656207607 1250 656206357 656206367
    0x70b0f0c031b12120609060f03010212040c0f050a140a0509070f0311030702030a030b0d050303040b010f091e0b150a090806011401172a0307110604050c0f010210020307 74
    0x41580c00e11401000650800e1442c510b0403580c404c918004c01000c00d07500e10342000601440a0071365a0040ea43c888216800e40f0244001c00d61030400ba09501c1c850700e41072929200c040a00c1e085807120b48441d0364104000c2d00c07000b460030182c0d02d41c0c401003c0c0510f40200492a05030b02a40000d034420003a0303042c41715294000d02c00700780c0401d00c2d50b0103000c03644000003940d2542c4000c0d01d40b480140e0082015591040c4254825009a100142940000d400740e45546155400035601558400700401c010001c1004018409008041c001070911001d0300d501c10703401496200c0c0c600481443d0725044120095501d80b401c0200c00440c040c0115103581411100918841e01409004000e06c200c10010441030500054080345581c16914020382d141d070b0760f0100e44100000340c1f1110380c5480d40c0c1241e807680c0500c20b04050502c07980941e05500d9241611000340084446564120a034001d0800d1001241d004684070701540c201784c80d00181c04941c3c00040340b070304001d0200c03c0080c44c404428054280d03442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656208857 1250 656207607 656207647
    0xc030a0306031a06030712020310020d1e0501061b0615060e010e09040b0426040602030702010f0807140c2112160c11010e27010b040305070b0f0c03 65
    0x31810302c4281c4210500940e07070814213595295040d408550104050325a1110358501144090140c5038401c8440d422602030341c00003082c0018003605c400780002900e41c400b0782c011070b400e45c840041c0300b154176014000d4801c11507200034119010480c403441c014060306801400d4443e09241d0310708415643c0b100000d0055007140d8519000400084080040b407a0201903140981e800c6002031055072203e0761103044c0e000440072000916815680d58101044004000d03100508294000c0d65460000d440010518000024854240914082401226035000400003141e208100300c50ba503840c80b2204003440c10032005642640e400303031510b500700c0126141e0050030010000101c000d84a807034455054003c1d10350300f4100c10004648020460104040c42141c96003640181000500c08800c42c012440f841010902101031040f241010b0754000f40b59850b550040c55115041420030b4110b54500c0e488050500c0f50202d41003010034030380d032a110340008807604116042c04884c0d80d80c080ca030801c5018881 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656210107 1250 656208857 656208863
    0xf0806180f010608130b010902070614010605040306230402040f0f0204140405010b120403050a21020a1107052d18070e0609010504091503061113170c150c030a030603 73
    0x240e03002091039944845c0c500300d082e03940300407605910703800c2040640c001d409c000302c142d034400c0e2251140f500c0f444289032424007030181c0365982030b500e50840c00c2070401d40b000740100a05480902c10100d40746480d1481d0103070810390483d0301081074000c24190102030140c00c040014004e200060004150080008000c400e01041c0e505100503a40ca503030003409402800d40d031607450809070b800500080c2c854801040340c0c000da030404420b05007840910000000c81014601c51041d80091464607e64020f4000c0c544443c03d6001481c1c0c01c2d08050201c0e00ca50040c1110005090b0008944074010381e400c03d00e40c044240c0a406200c5280c400880100c1412003902c082000c0340251004810a04110084070000300040c0c40352854a454514030000818500052211098449201000041d054000ca60302c03250425030460321100c00c515115541442c0d5808042c03c011107103075201c0c0182000c01c1d0300e1242c40007140ca030004002c40404c2550f141c0b1501251010030702000518104042d0154040740139a40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656211357 1250 656210107 656210117
    0x1f020d060e0906010605070812192d15050301090303090c0f0b040b090d0b0921120c0307140d05070905040e071a07020303131401020a030f0806180f0106 67
    0x6500c4a100281c0740302a11401515000940140b203101d0061740207009403841000142d18203178a9020000301c4840a0345d20462180050341090310500c25402443d200c030b020400c0072060f03160558103900c0c011008003e441d00171500c905001807003814000721000140701c041d00a0010002e80d150040080500311030803641009810404104032035504501015204100e000f5890941414060b508541000040f1a40030203080100c500007614045018081d1205d43e000302103d50065441c1980c5074401c0081408100c41404628021640c81e0a4a0f4016103a01c0b0f0156494a41e208101c81c11038894056a41c2141e000400040b908a40d07485544502082c4c0d80c0d01c000c40c2c0d119010442982c03900303030244110f50f0114106000032042c0c101c0d07000051441c540407500d00700065002c01d0130354215041481e09014586020002d8401b000e41d48000d89000b40b01501011025507000741506206085540c200208000041c40648811250044140b4840c00058032807421541252001000740104000a6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656212607 1250 656211357 656211359
    0x1b030b01051e19140a0302070c08032b0e060406090302070803040803040f060c08180a05220608030307081b090406080c030c01020d050d1505091305010c0206041a04051f020d06 77
    0x16101c1c48200c031400c138114101c20300c0c003228003900310081d40000328140c400798000c1800103a100c6081000306203007540401d102102003050f80c481e4558600c0b99240410080c100f070030300c0c144160f020404a5000b580004001121131880c00d0481c9400e006802190b1288400200800c04000000141007210118a0f042d0051622400101d501c41c0010b0b0008241c500f092010240000d40001e119034060809400102c449a0312000031310b60343c480418083c0c0c6020078401d804505215801180080c02c02c850007940f550511060050120740000d181103140b0145184640c254180c06045501250300140207200c00303600e88681c9a2207010001d60203209209201081d00c1c1c42d4008204580101c1c07150b01e90908010469138400d0240803440f10040d5400e0892102043c1c5a90300c0070024003540001c00440c075a14500c0ca8414216421882c40c442558880070400c00090124140100c1c0e108140c0e20051541d100e6141040c030740140295108c8002e1a03d150309210040564041e03c500000040207000035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656213857 1250 656212607 656212657
    0x717030f090c19030201031e11071b06090e0406020c01090b0f060a0b030c2506091203020418110705010501091e09150b03100501140a05041b030b01051e 67
    0x110400710b880c400c442c03d61008101542c080c0e400340c0030240344410100c0c6e81c00c48508002080b9250300268250109002ca070484c24400c84503941d45490002e038011031600e03400d01c2400741c40e0b40642e1040a1200a20704009410040242c05407a04c04860000900140300c1c1882c0c132104105044407400c150b4444000024a00c4c0b61090381101283c0700d42c0b82075403440d100c0c071215901d26806020182501c18200078100c221042070301e06a0026400f41c01c000580701d10910345944034004d031810f0341d0304041c01400103003d40500041104100b09410100040c546224a60304140340100c410180c0b071546407030000500111550042002ca80d200798010680c18803a0103640100e40c011000642403100f110124034120b11150301400c01c182004085501d80d03140d04080c10180d8a007600704003c0c2720034a0f640c60303140381480220300014210403641803080307690700201720303540f8074180001c01c08058881c50103a03210b034050021101a0100d54404014180080c000e044103584843c880c0301e045c2c1c041c1403e11040d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656215107 1250 656213857 656213869
    0x315061309050103240507120e120d020a1e1b03030f0524030f03041a0c0307080409060603020903150c09060721230a05190804060b03010b0d080717030f090c 69
    0x7c12003072030321854281d8440c0c001800080c9840342d01c00e095071041d6440c04030b8164128004c1c002480401d40c004d40e4941c04404001c000080240d01004d00004032103494400982240c0840b41c002c21710010380e5001b00c4ca50404030b000c1d01400750450b640501d00401c0c0320300da540c0345994541001b21800401c03800007078001415a10300703460352100d0303150b082030100384900b00d0b0300c4a1700b103d81814819070f98108804001003e0469111603401c0320404800107041145103500c0c01010000c3c5200c2c10114280600c00e008240c8a0004400491500804200181c00701e40502c6c20b5420100020381170340d455410921b094084440a0455030b12108503441d64072410900c902c1d0241c07510b0400d44a00b402d424500691200c1942140071118280321040c00b074920400150900340040440c1340d602c0c454142018142942225080d00c00b580c0240d041031581c0300942c540490301c207000e1f42d002815554401903410503408078075141400410601c0008140100107000718241801080140103130381401e942042000301d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656216357 1250 656215107 656215111
    0xe0102031602060f07080a020304030302061e0412020a0c0605070203192301113702031b1c020d121a0d080706051f06020303150613090501032405 64
    0x9804841d000160040c241040a001c0d0001d00a00e501d042410315034402155800000c1090016400440d04006041d810404603410800c002c40c1d82002661705125038104460090014021141c114184c149540c420003100c64525084120607600e10b854105c0100140c3c0810020780c803c5c8035100d0800840f410074151700750030903433000180307420041071020120750200c1c1c0c60403c0c40555841c89050b0400c6112402460701c6070041011400c206484590114850090000c562089082030800c00320280c001040fa14211002540500070324039019046141c1084031040200d0601c2080c0d9400d19640c00141c400c49160154a6a05042d085905500d00319489603011030303110703034942c48203203c01e0600a103841c903440e000c5c1d01802e2400312a03850300e01c1074400903101c2004004000c4d8403400000000c00e5500c1c003038502840a5482c5040c10002300200c84c02d146007292207032400180500920710342c85210340007000101c0c020b000960b581d090082d00300902c1c17000c4441c50070054494616084a0f4400c0034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656217607 1250 656216357 656216377
    0x121606140c0a02040e2803080106051305092a0307030c051201061214090601030b060a050a1802040807080c0f0109180e0f01180615050102031605011e0c0e010203 71
    0x40515007003502008081c05c021210b020960003007507952041d41d4100f070151004440514100440b80d10301e841e009100e404141d04c02c4003000402d10480b004400f031140d800d4101c9a003180c21044a481d40714a00b0407000310b80c50f076084960019000c007c0701c014043d01035031042c24240c81c100641000120251094440d8084c1043c82c4180c0c4e80040c025035008804a0054040600d00022248580c00c0134189810003560040b03420f920034401041003103510b007502036001c48165000c00144d40342c240414011049800307094401c41654203040415001a419a0000d01040d000c5520196440c1c035074507241d95030515494051a102086140e844d40144412011a8402083c0c9a8540030311704181e4020303c100c03410501c0d180241700440424031030034090890610503c00203413a100e0740c14a0171b10101e4110703a031a0208140c4c1c104040015070b80210035502010380d2102e42540c58450f07850400d006190a0517203030000d12400c040e034076207080075500c501003406051b00c5101b807155090b0b00583c1d5034017030b0110070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656218857 1250 656217607 656217613
    0x608070f0302013603050609121c052d1608010e0712090503041d060f0916110a0f200a1701020c01061d010b1204060b121606140c 57
    0x81c109481d550b01c498503c21000019803100c8100f019113104946100e5031040d80c03281d202d038050114400c010700020890100b0208141d180039041c0745a66040b40300c1c803a1702e0004a54440018000110110100034a0300d02d1828000e00720480c0c039182110400155600f158000181466416450003180a01d051794514003072200c0c56641c12074112900c1c1030390000000920703203900030300f03000802c00c01c0548003806079400884803150301070300300e01103c080081065108290904600005880c0d449000b6000100c41c6030140c5200c18020341503441111811228441d44101c8000f0014401c00b4070344000f4951264a4407003ca81801c9000301c8820007002c44d0301c0d0f002c2c200300c1c01080303d42c502d0259910648010800541004560540c0d982113072055484420141d40300001d512a03070180c00e4500f80500864030390706090000116140e5080c86009000826050b59000c031820243d9421010004e4074520004507a104404904a03410090462180c080440d01c0b140b404c4500d54451b1055403a0a40e1003801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656220107 1250 656218857 656218877
    0x31b071508091b03150103030201050a0e01060e0429070521040302072c01091a0a080a030e0a0e0a0c02190308060d030908070b070201020d08010e1609080f010608070f030201 76
    0x84800c84208000465138184107260174058820303504240580214081e400025091400799031100a554031201c0701c00082c2d2401d801407040019181c00141c1140d0440c0540030300309040a0010b5040c441080b40700c1f030302e002180811800b142c1c0200109a0a0700948064079080f890310101c5229610070341e40240541c1040c102400f10202d280c9125280b442d000700c2103181401c0718104000c141e03600382c0004e4403032038849205000110080d000440020010703940c080400d85450302d81c60b121542600003d00300600304101040680e43d0a90350400340803e160701d000c0d6800d005500740004c0200605c0d81c0094050110031030520b49811071190003158254a4645a580c1c901e000c1024901c0103c0d012424011310002c0890b1900c1c04100c04001b5240d220106542d071a05170002a241807041010b5904000044006118400300d0138901600b280c00e0440141c010041c3c01c41c2514101030039041190749200c1d10000d81c4420300150044400c4600110580d032401f903c41c94400e060090301e000c00780c04594481e071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656221357 1250 656220107 656220133
    0x50402091f051b010e07050102061b030702030409020a03090228031103010f1d0f19020f01140310050a0f0e0f040609120503040506060a0f050f03031b07150809 70
    0x141d004100603514010745407110040f00b8034401458040c3ca240703141e54485144030803800821405028213801d000038140c0e454a43c0c1f00c200c011401000080801c100400410b948500800981c4c000d020b42d440b080d521a00100c000400a044034201648518449551022045c2418805102c1b10141d02004083c26045460b403419100c0c031510000c1d055903941108144032000703440340100300c1195018414605004091103480c040328030010000729082014800f0000362815050b10449034161085510b104048005070b035181c0e42004040c84081000040050600351014044141c440885080d0041501c441c24415540001c1c00741c00304810554008c135030442c02e5096003651142c4129004603032082940ea03a135460841450041c001710310084188020040d05015065100c00151252102d00340743c542c0d03082e00d2914070b10030721f0b02504020034000c525071014011145c0d80208560300150701103425115640e81c0b03141e846124142e10035a0075030004903108040d100e01031604540107010203000b1003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656222607 1250 656221357 656221399
    0x624030a020a0c020406060905030f010e070510052118060903071b08030705030304031205090c010f020c04050c0c0607020a0803010509150306150a1a0409051f03060c02010605040209 80
    0x490b408042c424103800b15401651180140350140c01079581d0f02c0380707c1e0b00d050241482c080c90581b001c0850390410b803150781e5090780054540202c5404507600c50b40740c003022209503154803030303450b42c1181c40d51030385008000b083c040d60207580503106e41d007940b01d403000085200c291034460544a84545400412980d400b00f03444103100010318400b9801041115510340d050351444e44446000c803010380002c020401070540102a111303109010320010b0100f460404111510b0718049100c15042c030690710318603403415108218400c40b203400944100001d007050010403200d50401000a21580320721000a12414070201d00f4510b12940001e00f181980d007080700304100214000c1c81c552031071141e07030b02c401a1030b5010840c16026030b00180030503450b201c4030010b1102e400d1164204054410301b00011951603403420302210221094100c0019054441600640e16504405408081c2818a0801205000e501e034001c12a4a070b068008015141c0d5507420712080e030080402e42c6038816486da41c40c00e081000c01e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656223857 1250 656222607 656222617
    0xf0c090130051503012f09090f0f0c070503071401020921010e030a0f030b010c0606030303150812120417031801060905010b07030c020f04050a0606090905040203061303021c080624030a02 82
    0x1c40038481c01c0048207c0400d1410400f201c014040084040501c5039400f10043c10640102904504a04d800c02c1601e034581d5901c80c0d07440041681c88824061006130780298140d9111030802841d90b0791913500140c8865076480713200b1000c0c1c3c595180a00341e4805a80c00022168203c01507281e07018010300148007a0010704103144401c1c148100c104844001070880e00c40c040145109489c0007580c101881d2900303504008540007150990310603030703907840d0b51001c0c101a20300b15020800c01a0280d41ca920b0149004035121400e0710708054040305005076200071782280d01c0c81c000b40500070400c0c4e60b920000c0f541610703001c0c800c0e000000010014400032a100e42d411003603c0740050721202c1c8542c0d101c4080380450780e046405031681039441e041407245c55400111000100422102807109007855000280c80e002c02500c5c0441c94109601424105802030000c205010070700005902c1100c0c000c1d001a00c220304c1218030070311810b240d006070042401909044103424581c103003894110354034111104000e40c0a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656225107 1250 656223857 656223941
    0x1202130608030406050403051b210f0f0109021201152c01090c030b012a051e030310120b0106031d01020d020d050f0c09013005150301 59
    0x9695010800c1d12040004000510f800d65072107640340d2460900754100112442981d1040e0b48210f940740440c2c1c0d0f145050691140040c0111450841d0100070600d40461800e980f0341e6405226100d21000d20103600c030080260096400d0b4a4250302c4420840c2201c115070798ac0d00104a1080d81444450155849a5075600740350901000040901c903080d456003000740d0080243c10b4803064558201c90b4140039400c0400800e083c03000080700f90250b28602c1c903c4105034400000031442140b03081c858200b0418855080005a101501e50b010218503100d52007107400380c01d1040da4030800514800740d00410a4101e40001c0ba074a0981d081010440160000481d01c1040031290910002c800000b0b100600800740380718001a07486200030b4401c005e484004205482108610b420480f500503103008490600000b464203404040e0640003042e440304d00c0c04c4502c0541400c40301c40c0c1403032840c1c5911140c010207001d80c0b1042b02d10080c4c400c140c240c500c040c03c4136207102e409464070314146032105000c41c48592 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656226357 1250 656225107 656225111
    0x5090f010e07180e251701031713120c0e0f060d110a060c050607030905150606130801140f0907090b0a0306051e0703060509070c11090901140f01120213 67
    0x540e6844d100b2281505480d0899455044052040c801150300c003901d0041c0c2641c01c1c03c00201c601401c052412a20501c00905804080441500780c41441411203040d03d808804001d051520b0b951030701c0700020800d81c02c50340d00c003408001180c244229084144503014450038809903544d0f003001c0c4009025541d108039060070240e40b42003550b40d2070100100c064881c50340d40d03844c1038800d1300700940341c85000341c0300c40b0a05140134401004618081003454003040d554800301101d0311184c0209070350344118640d240c5118218000401c0200c019000308145601d0b4407048056515803011913144000c003a1000c9040343e0010608000019864209a4078503170000d000380c041a44c0e81e10750000340d40040310702615080d8028244580707186820001500310b600340c6020801703c1d050902140b06004003500501c14030814000502c10000590302d15682440c0250910885084c40c08099002e0f0840c8411090840e010344000b540d00c0006080044c12501401100d980c1d20105400b03111242409600518001d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656227607 1250 656226357 656226359
    0x905060a09021323040b0d03050304020d0507080106150305060102070b090f0d080a030204150e030a081c1b17060604030b0702030f12010e07081005040b060706060f05090f010e0718 79
    0x1000c3e040f10300c50003c0c1104c3d801c24514815008003c120b4001c41e40a5126494580d280004281e00c41c050700ea1003030b03041d20b03600e29003011410014079200072030740021a40d600705840803961100c00c440c0c010300c178516074030240b000313840b8035006a80b9440580103c80d41ca02e010300c0480c0c042e15014111046e2000080c0c5895401e503c240c40c1c1c2c0042c2e43c00140213074007180e0001001c2060000e00005000e0150072450200c40c1d44e803840001940300c42800802810b81040400c803000c009400c5040c0760716000320a82c003042040b0900000312940500b8440c00300c0401c00203030003101c080007245d242c94415000108943d190038150b80e10406003000250919046100521110711624441d0000b00034040307441490b002698074000d0f2004511000504807001c1040075003d020561890080070b5081cae41c0216070100d41d5483c150301003503440c025004064959428040000b4910001c105054281d54058030b40395095a594143c45215040a01c9802d840d4084030380022440b03486055406540c0b6a2261088002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656228857 1250 656227607 656227619
    0x70f1502250306050a020403050d081e070e09130b0c0a020a15020f12010302040624140f0a03020c07080a050307080d0209040c0305060f10091403100c11070905060a090213 75
    0x7581e0844040280640c0040c1c08d02c10b0100402c50301c4013200c524a889005490510341e912807101c451488060680c0000e008909440d000c0c1400041c8994054400d8202d0b150011030f004a1080202d0700fa151256110007084503101840219100307070005400904080c400ca95404c0b001060b40c8001c904115404d000d01c0a00c1c030080030041585145c030301100c1c140703035040d4010041103030a1503218500e50041180e01d2580700100e00c210035802c40d494204981e072503480c9515050315128418952114903400a214a2201d805501911142040d01c00f120300094490f0320565848030301c035201602c980c6c800d020085c00980301e50010509001706110260030200b2610118064481040c17501001c0303529501000300d54100030302c0180380d458044558403a15240528082c02000b10380c0106481d1000f0210340c00306ca41c60400001c41000c03140c000405c411361a003000202104101060300505000310440090105514007415009105c005d081a00c030302e1500012a00030b510800c9120b50900d18400c00080c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656230107 1250 656228857 656228861
    0xc200105121b03010f0801270f0201212708040b0f070c0906050112060b04090c0c0f0b04050f1b04020304020d0b01090203061302040b0a052109070f1502250306 70
    0xc04411003011700a5081100303031425100f15051840c0c1110039120301800a603030325210340c42c1903600b010400c5004000c500040300d0786001040b8680d0a07021203600e149000803258001100340c076034441200342c19241030078a80d07007034070100c500a008140300f80020710890703440000038200140c11a003800e10300301c6199510420b03a0300d6035101d40c12a030b0350b0742010411560845e80d6031202444000003001000d0034504590558000e60090130051503030b9950141c200350142500080c1c09810070301204081c8000c1c0b078007024a4074120b034202d80b94011302c1c540c0d224106d400520269003e000b0070b83d09405001840911000b5080140b00360303072203001c110645004c01c22207900d50340640210040541c1d40d00d40f01d02800b080076802100314040300d1040108000088150703060712800d03105450300c55a00c0e043c3c000c500c040050b411040703000f141b88410502c80c0303400c80001c03071600f290302080c2d18058150340d40d41810a60280100b80501680000001d4003000c0074011186a6800078480d85030020b544a0311b034542 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656231357 1250 656230107 656230109
    0x806032107030912031e03020904020d020301140306070e010c11040e01050a1a03060c0d060b0a0e09060109051e0301022124010215040203100504030c200105121b0301 73
    0x21440340001400418964800109000350050980744400c0c184280e50052182e4440e4511501c0415a80904045203100760121340c00e0010041c0309546580616402c08000c1d4403c1c8540082031803040d6a200c00340c01c010031038602c100401e03180c0b98801c20003100191001c121f006c2d81180e00034550641500284d031248222600d440800d000028503107000d107100c50894440c3c2006501c40c88600c14a0003d90f03800080550703001706050030f0707661500410b800440190009400510202401180742c010070303030340090301c1c10b10181c00300ca52821640360540151a81c644500034141c00040c40c0340c0c00f81541d203502401c489102c1000e4001843c00218030741048600005e000f210201000842c2802000d903032100002040c0b05040115048000048002070350f40c504240399080354440c100300003070540d9410303c4507030031041c4005414403281c500742c90010032180900d0701c22100322548441121003410b92810820300f14a06031134503840c0a03214650307072040660003041c01e98420300c0c3c4401c0c42500074911000c1c1d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656232607 1250 656231357 656231413
    0x912060b0414160e0303041701020903031b06011a0708071704141201050f13060920040513050d12020904140118021801030e191118010312080603 64
    0x41d1050030071060322412000200d0f92002042240080071502e0b5401104450440e9840511451020091032070756001e409082c3c0c42d5607040c040401d110008409201442421040d06005e44009a0300c0d04a17001744141e10403442c0030507241c00d20400000510a9000f0700b51a40500c22030018940142c100c2107031644141c000c180b80d00c0c19000034000d00c0c01c3c000142d10600f421a4001e0009107061003800a40c608000c0a07810715101006460083c0700c0c05a0254243d550809101e000c0b005065081c0b421105101608a028500e00317000102104410780071000060b034028054403a031211502c0c1140e00c441000840c0c94200e0f400c00400315190348511800302e9140d10301c40030b1401c642c9032810b9882070f110004500b8004070b004000c8404100c440e2581e4494464003428001440d0a903824002d10741500308000728110f00442c0c601c6e03008c0c001a0003811041d14411607c44070b480228000f2181c00c1003081c44001d1468444031060b0f40030318003407524194030107000b504480440080f00001414898100aa4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656233857 1250 656232607 656232641
    0x50c031608130504140a09020a0f03471009020304050f0f0304140904030504030b0a0f0b03070f181803080718030b060111010e0f0304050418030912060b04 68
    0x450a403007074240b82400182011203080000721085001140444801450f800e40207548031034400443d43c41e41c0200e40a1700e4212450501c007a100e01e0182e103002d81c82d01403107402d0060301c0c840358003400d11f00b540c54140a82c1400bc0000000401701000c4e011440502100c02c4c80070700ca00d010603509540d1001e10300c1603025a00501004107004052410b0036001c0110710f0507904200428808001d01301c041c110080780543e0b90304180d59842c2801c442e18090340d0001003842d42c0003400c0c0401d1403c6500456000150f070601000103e00c0c0318100760391401a0b106001000d8210503003000144240709100010041c0703064040303211826900308001c2885518801c50100d507650003803182c0b0b1075002400070003500c05a5070340415113095490b42244a00c0080c451810403641c0100c000c003024003074020b8101c1c211400100d0f0b100050b00807620351281c10900849005620341022038040008a510040c0b8040e007585482c840c4504203120800c0c3d102c3c1c800000c0d039003d512000b40ba1626191380c450a50503030350308080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656235107 1250 656233857 656233867
    0x1090303051e09060c1c0c030b03120a14030a060807061205010504051b032502030c15060a05011404031a090c01090602300d0c080108010c020d050c031608 68
    0x15110001c4104840000c2c400c81d440d0420609007400a036298101500c641100c0d10381941c2030300f4408401e2030250002203a4204030942040c1500f43e080340c00c8024084065030b04416805405040a0082c0e0030810005401011300500404aa00095801c51085c01000c941e40d40c4840005203400038075170040e000207041c0301011241210314402d26001d04402c607030a01c510b042c810281da0000448440c41c0e000d0b040c0010219002c050018148040b90300c60301203548411034900c00c0603449400059120500d40620b000c40100d84184500d124484c01004200c050303040c3c1441e00440c3c04117016010700c01c06090070000030001c640c550321084100403152105d00d0303603403030f01802480c1440d0b65000d0442c1402107842051012603004982c1c02d894100c0f881d04143c201600650300c000300c441e9108044241600094422007525480e007040c0211600d640301c0c04196640d174a8454202c4a016100c040160032450202c454144101e008001c800c25100c00c0b6400c0036410399a0b0302401c44d010504890980703000076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656236357 1250 656235107 656235121
    0x16200a050336100318060608061e090a030e0607080d0218031518010b06030c0d0c08090a080f22080f0a080d0f02041a041a030603030d05180109030305 66
    0x103462018501203000c80c0c15400c0300501042041e81140000c1007450340b079180012961804981c0c002d006604007001f48003007540c4107003080c0c85000c15030350110b40308211505018154802a42240a03144050090043c501c850702d04a40707860350750010580c4110101f0003180480c03440701c080d0025448011006a86549488031099a001441c80d010300a4200c00101b0751208130414040b5405500300e00700300880311030442c40500400c1880d8105502210100900c546042c40e0b40240c07008403500c6804005443c0180000d68880c001181c1d864030580c0020000c0000a03025030141c02d445000900503130808000703040181c000802d84040e400c00a4054008111103107080004c1c0a9020078803001c0d05503a0300982b10080075208190000f00b1042e150784a80100922b540d045130020120251030403443c2842c529405003562061103900c40070700c004004002194022011240500001001503103045845040f10f4040e0000a2241e9200c40c5c4400140b4219107082c0200c48040303120342d400090a26103c0e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656237607 1250 656236357 656236417
    0xa0606170702060a050705040519031106120711240906010e10170a0203120c120301141e060406050d06090e071206090812010302010816200a0503 64
    0xc65000ea44004400a1100745900811001d80124078684040351940d20304009550702e00c0345a200fa80c001200385070741c410040c0c0c3e000c21201a071b882024440b84c10007800080010900600c20140400b4078501c0119a1050042001000b5145840d098071000810442240105095004810301c01d0500d08100721240070103101c079502512000300404e4083c02c16a8002400303030424002e1003002c1c036640c481001012010854041841d40c02002c40360050310303c141400160308003180c0b242585c071034008020045e80140f8107880c1600c0c002c1c9500e02010301d2440c204080d22401c0510f4052041181e00d203c10036880303160003000a030440e034071032940d02d160200c00001150700303e0780044212880c222440c080d416011510038111440080c0458030400f0340c3c14005d008000c2e03280d00074024600090b01800c0c0303004050030340341207034001d0321498129078071418418070348400405100e001445224015500000c92195480900038080031200c503000729940b601e10355030084443c6003d515000907070f24000c41c804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656238857 1250 656237607 656237627
    0x5061003050702070b07080408010606020c0312090f060f090406030b0601020c03010902100c0c21020a0b07030c080307090509090304031e05060408180d0f060f0b0603150d05060a0606 80
    0x40d2404000500d40444002d494076458000c8070502d100004200e400d004104040c1d50145c1031582c000c001541d03903141301a43d16020b1518441c001d0040d03600c004200c1d0a02401d40711540d50143c08038105141e03000c1001700e654040602884440018002c049281d2542c9c890340d0091489890b10050038200400060300e0002c008216900c240c0c148200040142c8400c0b100403460b9066060100501e480c6250003012144590400c82105021494041041c01c40f1180714800134001e84102990640720741c0010104e1180c008040d01203007004890303c0c00505120000c0d54031041d5481c066076141d480b1400501942006c0e113200030958008a000d009200384c090301c1212002d24020030188800d001c0e074406803100c000400c054455400411450048204c2c0030b440000c0760001000d10751006040e141c0440e50381001142a5101490020082810b150b41e00c901c4109001c0106450304580e00c03c2c41c03140945005030182604400c2c662583c10010b0301c01c21107140518001c00700807a200d810004010518500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656240107 1250 656238857 656238889
    0x20c011e0e0703030203120a0b09090a02040501060906020c010f0e0415090c08130b0901110307030903020606150d180b0c1207080717040203160f0f1a0307080703060503100506 77
    0x510b10030030010b900042100c00d500362440820500d960342c032400000a1080d94141504400c0400c1002428400440c009a1312407080b501000700f0b90700c0d141c084850307140c0c44c016038002d40e0201301c00c4146980111955158a40716103420281c11403000c0114042d00c045258120490101c100188909421400f55651840845c500990345107422081c00c0c24880340888050700b4100d40c04049900b1860070b4119541304074480740c0c40d42d5282000c1c0c3e001401400520400d80040c09000d020038039030b251001c5901014000c2500071b9003040017451800b0010801300080711803501e426011540090307e020021485003446010554544551030010920482c00601e500c0411004030204182d20f500520105164081c101880380503680700d2000c00d2800340c061917411902c42e44090005100924920502c0503205c0c0c203440e00890341c0e82c0d00c401e039512070009640c04140503410300001e1001445954040d078080020f06d0302007001e0340d42d04042804c0c8139100144d0340245882e801007101c9410015107004074025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656241357 1250 656240107 656240113
    0x170109050f0d0206011a0c010c050307020c150a20010908070c0f12171218161233090201030c0c0510230f06150f04090f020c011e0e 58
    0x1030b640c400030346404050042d003011001c00094100c950141d0010340306425002c1008008a02c8c9140303025040760805c5071003078010310544410000303a0506034401103101c0709412006040c021003040030785040300303140c0202d1680f20543d00d8134880d4030301c24008d0600450040221560b50252401c1c511a410316540207080c480008a0302007140000d00581101c01c19089400e0307200300907150b421100c02c0d20901051402c2c146070081442440d400e40d0161021049810084130203804103541c0d00390751922584207448941c40e2040700f91002c60500c050340740b600c40015800100b01081ca03a1304248c201d030501f40181a0981d079042c103070110b5030188680134084805003010000c48407160f17281c5548050b050b0304508220307220890014012508405c070304424405c2018011f040c940560015924032080300d0f068450040080c3c400d2000346840c7c2120119034404100c4c524160405920401500d81d2540ca40b040503800c025040000000784a0050051107240c40440c030310043c540c509080d24882c010b0161560 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656242607 1250 656241357 656241373
    0xa0b100e07020c1e03030a120e1b21030301180506010503160c030e040608030304021305070801330f020c1e0f120d050403120309030e0613170109050f 66
    0xd400107500d80c480602151301940084258402603011050400e11a4040c03001240d40e403039694000c001402c0011510400b00200d0040200040d5030360307402841c0380b689002c2040c400405042001c600d520300c4640805503202ca08168801a2031984240d000d1000c90074082032a4120480d180507882e04480b0929180b4298240700c0508843c10315008005014010081410300806025010700350310040010010000145d503642101e4580e44112001c07441031104940c03285615145104190040819694242c2140c0c28040d0300348000641e4110003034007882201c901c10503403420110b1075440c01800da440c042011040c5101a203032111603448140705801c40d45a000409200700d10050050a0071180c0300d288035407100100c5c1c00400254589840c03400b41424814001e42c1000007401140d111321a410388098002000701c0449400c0a4000c00080c82901401d0981ca8400050800c04106000b45182190b4503114156600560719140000b070351250141d00500c101480b030441d1000f241c0c0300ae00440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656243857 1250 656242607 656242621
    0x42d0b060403050d26011e08070b09030111210903090d0f1407060203030a0f1b0c1205040308030112140f07080d1e0810090504260a090303051b0a0b100e 67
    0x1705005014203a20100e01c0400c8446494003104000300400c0d03c1e40c25206001c0d101e106000c9190300000d4150700a40c2030500c0507a03031151480c200c0d041407592090341400e200c40d00300c00d9015480701601c0e0b144244003e121410841d9246041c19030310300d1258008201e04205072600d0f01070a02d9030b018200b1240c101060804c6803507000f000300c960050300302c40f00142c00f01d220b000c480c0060451414040d0800e0101c14060700c890b8002400b0a41c4601543c1d4201004000f6101110740d8419030000030000d880500040104080e4054000d908600c030700c00c80004040404406440d02180500c803503081e9000100402410f9401c1c404900011600e1070003120314017201e9821106003680030340020806c80e41c83d002a0380c200f2506c030703001c000e4014000c0038421803c0c6401e00e0714003c0541400c103041c42c5054011a05540005422a0802600e40d12008c00e034074030f580c40039a4543c102c0c00352a8510a025000c1061541081c00343d410311380d1298407174082c10b0a00545080711140a90010f0800f02920340c00d002c82 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656245107 1250 656243857 656243927
    0x9020904081e04030602031f06052b020d06060815010504122f0901050f030a030c080c120d0509010212162c03010b042d0b060403050d 59
    0x805500041c20381c2e981c02c85400035980000300010303a624051400700740401004420340045000b0340b8904001c400c00c1c3d1400c030385190410120701c1a0400300b0402c020b03040c0109940e8603440f6007540d2a05150790b00010495240040c0d0703215820042e5402e684440600c100d42c7c1043c10540c104544501c40c0300e403000d002001034045d02c15400b51007111403205498900300060942d2000302d0002d81c0300c0c541d980d00f5088460070b00c80580c1441461040000c040040f030941082c600310f01003810006c000f0300f031041064a041d0b41d646900b10080e02e0040c806c1103106800304040040691181c2a040881e80e5903400c2c8403da03007120000752a03054103900400c214504000302c0c0c00081e0b000011780c0c00580345e034000903c0545030109540042500b03250301035004078041c0312080c42d11110361070503402488512013100800c42264202401c0c2ca034003484020400c0524201d00f0b00714080005d0340c9000040011840c00000c0d041d4000d0703030044440b98031640300d010480f54060602c003040d095200c1e1000141e200c109035000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656246357 1250 656245107 656245111
    0x18090106082703090d030807020105011212030c0c0503040b0d05061c020127170d210209010c080c0303100803030f070305040305130e073002090111010c0c060b0301090209 75
    0x420300258940a54850403e104480032090011718011018000d441d016060080856654016502e88000054011100240000d030542c1c00200c070104032080c054190003d040f040c0c588030400650030004000150100300410245c81100d0b0602d4a4200640c03c0b8010707218005c0145002d128860722210b4402031080c0e00342a250750900305620302e102102168032540000e004514101a55420b001402100602c851245c0404c00c41c1691a105081c1b1400c0c0e410f0b107200041030340c60001c10318000f42082030580c05007006007014941050751006e1900d940b0078a40207a0780c100ca181c0c00000c00d0082c0301c00b00303000603001081007201641c2107143c18180400d51000050440e000d01da26000003604140c40b86046500460080000c20301070340c0c0b075441d4054540c2c005c480e10808505820614058501e114400c020244441c914103004039410980c8040030f5008032a00380e042c031070316404c03071031340b0755401e0296141418186c0c1e10114083d801c2d040800589407507443c81c501030b9150000c001c001d82c55003203c040d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656247607 1250 656246357 656246401
    0x261605041206180c090b010e060c060106110c03030408030a09061b02090601090504020c010c2714031f050405070504020301080303040b0c0d0e0303040203060a11031306020405061809010608 83
    0x740161030201e004540d0390700010000c0103001844c1c404503068070300764441c0190110aa88448201c0011001c8c07010b2403055608051980e405480104100741c0b14601105c2661004010740d05042d4200020034a903811036040400c0360380011800c03c0c1e080e544030700280002c0c486898500311404414220014030b483c42c1c440a4002c55800b0000b0707a0b00d0340038151400003440060002c541e9030095124103402807400d6031111b00021262101c8040418007001091020000c45650100c080e01d00606542c0031007001344059014010100c5030804078696a000607954444154046400d1925140c00f44c103181e410381000c3d01c9140b042c4010702669500006980d0b000780c1c400701100c12a2685121004180280c0079030340503150414405c0300341e240e0080065809184203804175012600c0e1031042c8415604124810018038105000140290328140e0b07064012034050140185403175120008103900761b02600f00c102601d03ea907141a0a942400c00c0d6460060000d4901041c0c1170600100100b00c81c00103014030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656248857 1250 656247607 656247611
    0xf0a03050304031416080702130e070608041b0602070f12030807050a020a0c09240b1606060e070801030b0708011404200d0e2103040210261605041206 66
    0x1c000b14030703020f404440d071490200e1021028122981b924480c560302c0203c089000342c51450040c10190010f0050880c0d00365504090007100f070500b101207854200c0244155498a9448008070403007402d141210301800e401d0f030260103442d04150059084c001d01e640001c064070b051641c80d0340440e074840210303a0007405903d045a5580303921359040b03191845400713010380704d9150103c0000d0f0f6454180c0c000011410a100e602c40003c42050b00d011040410f403192041540c41000b00035850f0800d6400503014078800c4500007010341d11a0965801d0351400c4899101003820000140140003890000650044807860018000d43c10214543c030466035094010303015949486448008102000c01c5031420390b802e1780d165440d070381400b03c44c00190505501c4d0300f1a03405400303220641150300c1c80c46410250f90072041a495510760fa802d004500c40d40c80041001c100312410020b02c0c005071038040624816046004107940d08280304a1401c0c3e18040c1078076414440100302c1000703010a03504201c2d000e19004240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656250107 1250 656248857 656248877
    0xd11070c060c05070e07020a020316170f060a020a050c030406030506041817030601030e3c071e05030604060509190c051005160f05061b07060504060b130504050f0a0305030403 77
    0x4140e18141448c40700951502803e030340c0f500b0a41c11103490341d0440e000c0032514801e18401c5c0c0d040549404100c050940c06070015130001c0c0d80084541c008022143d483c0c900701d4034000301c21054030b095802c203400803800243c60310280301c02c81c80c10380610541e880348159502c80e890801ea40c0c0000d28400c02c800c1d0303021980003100082d0030f40c0c00b80c1d01c61a4003c100005480000c0307400300f0b00000e0640c112a85201c1084c5002c004620089151099146c620039400144281d07030030100340c00c00403211402c04c000110b929400115031504d0500c0114004c62185a0100e16070625540050a000041400318003081c0e0724074240010075200c084c802e04444003030f205580c03034850542088500d40f01d49a0400764000d01c03038180000308006c1c5941e803000346002d641618003c1d01c1d00c00440790501c0804141d8002c0c410b0502040c5c001c50a56480b0780d0b0000e00c0740340c0029408507044c0100e00030140741c0c8000328082e80c0e21710800040c840180242c06001158030040c10f5242e00a5601503c10301015002408004400303031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656251357 1250 656250107 656250121
    0xa151e052115040f140108061e040c12030305040201030e010219030e0f060405071e14061309051317030702061303030b150a0e0102011b03110d11070c060c05070e 71
    0x120001c00c0036030207841800050b400141440c068000900d5040d4178a21301400001c249a02064440c01a5601e0f10101d80c4035406602d0b1001001c0094020740c0c4e40f246041c000a040d14240030309405142c803903100821a484c060001508070344040503241b01c0c40e4010000d4005205409605d9010307403008bc2800641c60710518041407400d1521882c01c1c40320705c01c16007800140800020580c0031619440051241c4220008003228a41c015201c1c07540d403090194421580c1d8070b46840a4079881c02d03012040260035603140d841c0e0050300c0c401c4e1005000a039503100c20009200041c803890108104c10a403503440c0d4200302d9002503071888001c160445503140502004101740c420f800420702400024840261010550201c03200e0b50311442210010841c00e0f44550601c0d40180244211404000c0d034104001c80c9050058001e040c40a140e20f242003010084a0b031944605c3c400d1200c22810119480c0e145c007698540120540003a0f000141030189051100e40060340020310a82940e03a40c801d00031154456031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656252607 1250 656251357 656251381
    0xb0321090d0f020d03080402150703020a0b07170a020903010c03020c030d02090d060c1701050f280b210f0c09061b010c11010b10090b03060a151e0521 66
    0x20b8002c1d07010043c0705a1006041e0310042e1140194001c40c0d032064200e202ea43c104025210f542c9005015070840d54660000c1000054215402200c83c14131002e4410814401701c0003a00496a96400c9a0302181c4003441d07040910508000c820907050031450010400903041c1d50380910740c0390714200c5400052039055610340714840c5087c503510502c180050020508080c01d1251401c1e9902142240040000b482c2d28100306580d00804c0090510811035400d41c13040c4010150348059100150026100025100c0350705c1c00803ca02035501c1402003130041c41d03142030300110401501c90342e0418400018090804050022180c0c2c405c4100e6045580c0c0d044c6404029444034151110002c551074250440c90043d045182043c1c80e00707180001f009000100c008001e119115006400700180c1680001d001384012031000b960801d800403d050245a503904003058240505043c0030005025031800e010440b04d201001d02c8110401d0030040d0501d4031210f0315004451501821403503c4088a01103a110390b422 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656253857 1250 656252607 656252633
    0x603050303180f060403030207031211070f060b0d030504031505090318030a020a030b06030f0d020c0f0d050604030507060e0d35090d090b03090d080c09040603060b0321090d 76
    0x3c1801d42c1c58902d49400c01030002c0d042110168042250406403100c068602d01c00e89089849035080e10707040104079110741c0d240100d100d03003c4912a9a03090102c095a41c0c00d41c030003140798800d035106960b9908603c0c10306e0000b5103031740000c801a81001e040c00034024000c415611141e8502e001301c01c0c04140900001c0c41c0801c2e143c07002e03401c054002c0000c0240005401c05074419903059003280d000030114854540c5d5a0100700311500142c000700c01e9065203217004081046185001001101c40c6000c507100d060070440140ea0031801310703800242e407004115050091044151a402c05011400800070000c2c00710043d40e095590301042c07000c1c448416200c0c03410840140c40940440000320b142003600079650303001418448010030288600060070f02c1030401140c2c0300d148280003034107601c40c10030300507245c64001400100b0851020701c011469500c80d0311508008600800f408103400001030203040c146a03a010804070310034038500140d036440305910101c84107040c0c2681d6044044445080810b030f88065 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656255107 1250 656253857 656253883
    0x703020108100b13170c01020c011220071a09070504020a0315030302030a031514041107050d1706060c2e180b0106051303061a060307020718060305030318 68
    0x4086200c01060f103d13143d030601a41d1894841c80d0250305591403003562840c500c0305450042c0c3c081140b122265100310402c19140c9240500403034a00b9484408590100e481e41c20f0801d25500070400700188000409041042c2c4400d880341502d42c105180d109840382804c0c09039500803a00000c0a5000d07078800c1e40300101c0300c000c641040c80741c1500c0e0f16000b51260320826030307000040e0030815051071144110840308120780c551070291401d2654002071001402c0f1454030f03080151001d00591000c284240f00035240038000f0381c0c030010b9411102201d030044450181805000781414000120007810000300c0351a400342445510b070a589900d542013441c5030f480c0001201d82420f040070001503004010b440300c80c440c852000b260241c0e0703c403141100c0303070f00800544a04c0c0350140041080880d402d680050b601400750546c5003600c8880c6004a4007580c001e9904a005038004d080400c11100804c0308001014030506050020904e19100c01c2d0380d074000948004000102c801d09804030f072070200300280000107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656256357 1250 656255107 656255129
    0xc030309030e0d052505090a0b01020a290f1e090c0d0309150302071709131409060106021209041805011506180303140d0e030f0d1d070302010810 64
    0x141e03074a030680c2c480c020000c0640703652405d81d4003040c0060062104c44184c0701e0191000f1081d035240224000501010f4030414154020b08000c00c7c0802c0307944201d14651b403400d4000d110075000f0400160090400240300e1030a0349804811b02c482c0c0c0c00728140016031580500c055060b581c403103400c0541044c4407603034010b0303200c0300401d005810141c00c168103200700d40f0a4900300300c81c8900c4802c15816441800001000d155500c04e121041190304005440c0050b0050700b400700858842c03420400f12200e800c06140140f040030200031501000b00142409440a332000d40701e140c8081401c1c4905004015083c2c0c4955180e4000700304070103050090141054000009001d90071691454100c403030164020705000a20013a4000a10f5050f041c0071011280d0581e1044c0032101490080541600a40c030078484094440003c08594041080a000d004c640510066659094006032a0481d178146000c00348040d80741c144103103150400704292003240d40a00304004103a46030181200e24051076006240801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656257607 1250 656256357 656256379
    0x10f0504202b0e0f0f0d0804080d0203040c030b090c090c0a020102070b1302090705040b12060418140d0e06090103090f060606030603171305300115050904030c030309030e 75
    0xc4142c0000d0314002051090b20803504d0800e0700745480744030307080c4040011351000d0f000c46111b910a4035074680c494040c80d641d5051655565410003039074030a480503200c10b814183e0500502800c040742ca0b070041c444600424103106500049042c0c0ac0c801065038186600103d841ca10a0307000390110b400c03043d03200c051402e00b483c1400184c000b0700c0b40c07d0401d034003642505d80042c46081c080c204440c00e8944040c1c4040c1481188121480e07500f00c0200019080358032107803109903180c50419601c0b1054031441c5400010003d0085080c41c050f02402420308011000b081400b0307a444200440703078810002e2801240025082c184100c207800d0140c4001e111918200c000900c15516901c004d061b21b10440010481400009a40d0081d001b80e034084071074102e044600300300c58500b00c0e00000d031042411003070040e810740080c2e041e120135040729040101651074105c01e4044800360401c940280108a644d00001e05258030024242c1180c2d80c03005051641d00d0344010249030044290180c0100000c1070340d0009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656258857 1250 656257607 656257687
    0x6010501180b0706093f09080609070905070306050a0b031012140105071d1014120603010b030d090b0f0f180f1c0f080d020c0303010f050420 62
    0x7001052415105403203010041b00e905025009040c0b440700100c4501080b03107501c50002c800341c1c9580daa890b024400036042c0042c1c452800e2005a100304a008050545d81c0e00c0e0056644c00d44034002c080c0340c00c141c80d140f41400b0301e550b440240c5056130004810143ca039658182001068080341e003000721682c2c0426000c00403c042c3c450201d0510b26410001c0c4255198a07078142e42d130110801801c001301c0414000c1d4940c90800541e0301d048003015240c00206144070440c201c030300354005182d03440e410b101541001090b003000d0145428888050703008142149a040c2c0052402c8910701555000c16400181c2a690a48003025206160450110182d9401e000391106001d205100c0200c0d004407045c03060002c0c20b180081c01c04c400009034150718500e59145a03114008035414180884584500303004052441d482032014101410565006503520350500b180c2c80080c0c600c0e03510080c0700d41c0c20a17100c0e4205804800343d000001c1a01d43e01c0795211020002c0401d8030020306110355010340383c942520055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656260107 1250 656258857 656258861
    0xa260108030a0201060509062b0b070201020903070b130e07091d04060b1f211409120c0312130609060203071803050307170705011404021002010b0306010501180b0706 73
    0x190f0300200070170340c1d0352803d21401c0242294220303445050203109904040882010032034501403a0040d641c1c684540c2d581e241440f07000d480b13900c0141e40c04038800540707081c01c00154002d0021032503141c0c1071620446400d20702d03040f5400389031325004840e030204008030b00618050020f01a11601d81c2c507998000300140e039405000b124107840913414251040501e042103226846030f01e006424040c4282e40000042d101032002011b101e1203140c10321414012080c00c0c0c0b00e0f02d0080c65030fa1507001c1e4103007401d000c26440e01050007902d00710700408002001000c540042210420320300c03018040c00c96503031104010652146140040c0086041c6200a001c20070311340d00941c03150002d6241e100f5010720320601c2c8966003001e804000d10581c410415100858414075828010150085215240240546c0c03524292805003080b01840c07546141400218039190741d20f094a210f4502c020000144070400182c4d50303c0e0180b040b20f0601c6803100d040011100b03403c0e45100038041405129a80b04040e16003600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656261357 1250 656260107 656260117
    0xb03090102031012030e0f0f04050a0507022803030b010504030f0506060111010b03100b0f030307080a02120a17180d08060f01051603050313120819110a26010803 71
    0x20b03d00540090204040c8080403e001c1e0f078a80542c0c801c640d034803250007480402da0300d01030400c1c4d120000c20724001d280e54950141c207200308841100401c05007031543c0c0c045d2900419041424140c40700380c024500e8004040c01a0924a805140c0840c6840300e2a006a869100c1c0f90000f501c3e0005040400701849000217140d40039000c2030340e603038030080301c0d00c03034424201d0300455055581074218220000b080305480d084a140a02c00030040083d8000e2000040d207940e02c4040111200300e0f001c2211000c00b031701070100014000e2092902d07454548986030040160b00c400e2005c60706442c82030003240d200200500380c56000c41d16482160600300040718090418001103960320711540d1024085403082d4460340c00e695030180c1e5030103010b071005225038040e0307481e810040928900000c102480c0011640c0028582d901e0443ca440b001d14500b40a44254031000740c102e400d4019504118002d40c503074620004454a185103403070b000b1613081002c03005400c9900c104800c100401244070000c550000c0100c0145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656262607 1250 656261357 656261371
    0x70503040b0709081b0a1e18050f0103060e0a08030106090806090715081b0711041a0603130606090504030503070207170601050112091a102103050c070b0309010203 72
    0x629030b91590119484600340c01041c1d201e8000030b003024070459070191a85620f101c01805041e245444d120900061041d829a613140c040d00d00030308101003c071b5502c010444214440040c0b10a192402c00351802d98810301c80204400d40e524000050082c040c055481d80a500440117503681d6903801d802031080d02c0c0c0d070050380d00307034003416010804040d0002442011030380780b91501c11000b100200c0a5800000003800703100e00290114001ca84007140d403009180c1d140c4902c0301510410104c0d01440100c0396810100300019400500054203651100d00b40c1e0b43c00f281c01c801c1c01c00300101d07a140500141c03841e079104c1b0140b182004144000c058100c009540b044800f50b0172034034090340d00c1420b212205d455202c60130003504510f0062040754031451203c1d41021507403202107020b00341c03030b905ca264410300e0150b10280a0b40000c14811044488081140100b8801c1c215815080b80980114107032001028001c00744000010506505102441070b071000f440b40f207061903228a461802d01d800303588211004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656263857 1250 656262607 656262623
    0xa080f070b01030b071119030e060f0703020312060f01121e090c0602060915011505190306140312030a051f14010e01030c050d0f0b060a020309090a020a05190c06020307050304 77
    0x1402d807840c0000c0940e107c50142e540c3c02000304a03900e003078481c0f0006440280e0000b03010004040c403c01c414004002c0d00e4485e500559a6480e44c05501200000141c40248601c42d00300c11003116a0380061a060040e030b4070140041c0000c1c002c0c0c101e14812080c0808012541e0900c01407406120400c4019000c486054003a1140b642e00c45003e17584414200010308000e0300364800500403c02c0b601c04400315030446040040c60b000d004c17551b080e44000c09200e004006078a811003800340f00c04242004001d01015001041000c7e1080b50400303035400014a0011007541d5030000400d104211301c000c1c0000e400b50084070040940750105c0203c003040c0c0141290103c0c0028460000ca54402d110f0661307a000700d59070345c0f0301f405480c0b2120005460b030b1904166280d03441e40f5410100c0d030395000041c0104511a001940d9580c0c01e801070000541d00141810403091040c0111104141c01100b1201100079403030304203208545903a0203650046601e14080c190620104c20440301c00d402800842c0914042d40c4a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656265107 1250 656263857 656263877
    0x40e2818150506090f07020a020604091b0801150c080f2d04050a0303030b03100c050a030608010204080d05160510091506150309031e1808010e0a080f070b01030b07 72
    0x10080950b50140d40f016040101113000a25820b05159503d07040300682c03050f40d544254a030001925a08a80c00510b2407035501c0c080d01c40008454100000ca08259041c403c415604d071003040211140f84010401c140316200740f02d103003007101e400101e0b00c941e15001c185513226403101890003400f1680c120340612030124154588407050f041c00503602251802030031215500e0650b0303011409000600c0b11035805114500e4001c001041c10f010b4005580c5440d170310f0640701e10300040020107403251a0f000c14017592041209101c42000802e003000c0c40600d03400d0071a51480f6000308610780d641c15070009071140c050001800c0c842040d5801c800d11141c040d00308060b01809400446080702c006100310503505666006c480c1001d030007038201c60050b500034101545034181c4070b48410303c2600c2e0a40f6001c00035014204ac0e109a010140c0c00c440501117550003040500c0d50100259900c00398035101910743c3c50701142c8e103941c130004030044800607903104881c05209e503580e00c0d28034490396003502e91078041420401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656266357 1250 656265107 656265143
    0x606110f07080601141c060b0f09040b0112020126060f060a020c1e1f092c1b0714120a0503042d0804090c05040e2818 52
    0x201071050320040c0c1d000d008113910300002d8400041c083c611040c0c200311208003a03448228548866a580c0d03002d0400868040068010030080c1c01c265440c05101d2900802400082485c8000c9581901d00c42d0780f07204080d499900040c2c5019131400c8400300c200d40c200d82c1e010f0060f614046054052501a01d03ea4140210001044200e000383c0c20050b0050741b10041600c1e1038900300b031600301800010103918030b03007150f80c9002c1070fa8a4264175241c910000c010700c02031080f81c2c0c003006400080050101c2d035521700062005951a4070710035249005204250004203002c071160601d4030391000005244251307620864904840314400b2680580c4480c040c14465010138191402146c5182c010740d6038462869446d990342801c0391030b01d400080c030300944031040000403044880b4070580e011b024000081d10f5519010075442540c2ca080403544c1000000d120400941c040500741c0303034100c0500c1e481c15000c2c580400c441041d007281a502007407002c1c01c008806809210b40c4410a42c5203010303143e40750f60081029 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656267607 1250 656266357 656266363
    0x9090506010e07051903060b18090c07051b0102011b0c0311070f0b0d0207170d29010509150d020d05010f0303020d110703060501030c081009050c0d020307090606110f 73
    0x110f00c2004030b00d0400048610200050500040340c0e2a820300098464640d002481c1681012110b05204a100c071503016640c601809095404480100407518103101956040d440b012803070810180614005401c40b05603000b074001642c510001044201149031100c402002e003c868541600881d03803002082512034000310b0a00c040c1c6004600440205240c94503460b49640f059020141c0303194248800c000003414006070604411440e2081a1282c0d20b2001c0d0b04225540c0c503420320400d03280000c1d48114801d401c2e01100e0801c1d007d0070410b031105100710200d4003043d4910640507505c1400a00d03500c00a15940c0544241c1d030a03504200103903a2940e00c5002e480b0b82500015015030701505800001600c510b441400c41a142c3c0203032a1030070341e00e5503006d003503030820b800c01c5420084121051064035001c1180305440c3c03406000c107001c5140c89495658561b0071016031359000d49204d803d000255101000300300300405203c0c0c000c11450340d442d0801001421030032048043c50040d1411130954030000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656268857 1250 656267607 656267611
    0x51b06040b061c05010608070f090c0e04050603010e06010816050d0b060d03021204150e0102191202011103090606010908061b090a0504020c010b13023402030709090506010e 76
    0x700031084066110642001040d26041058101140303024400c41e0003d0030030700508006018902c000c001885c20045a07907422895600314910051130901d0181c0302640c404800c1600e02c0050300c5c00205500c031180440d0140150000400c07007803140c10000a002c420018402c00c400e02404502001140c581c0d082014112544030003030660035032500481e445103089209141e00328424011a00340703203020391101151b504a548801403601410510031103168002040c0298203600b4400392443c01d1001d44440070b0016400c0000e400c0c00c600340c00003078a03a4000d505c481844c0b02801030442e102d1400c81030056880e0011100e01380014843c85000a21040000d10940207468944c3c000d100200140c40070310032038004880841d4800307502c1d580051540c032248014001d08402000100c0c0c0084103005000c840f440030309007025524410441000c080f4003561800003852444101408400d850950900141c2a0240041c0d85400760040020b01080b1039800346140c98481da0585075540e030707100c150000e03110782 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656270107 1250 656268857 656268863
    0x30219030203060a020f070b0403021525200a0b060f011103160201031d0a0c060918090c030804081e0109020f0f1306060302130801111210080d051b0604 67
    0x40b06010800407000c1e60040c2c4085405503002d87e0a08410b07032a038400310f840948040e03015801019080280203042c2600551020030800340c4030050140030041091130a0010900301041700c1c104da07510101a4403412640215000c00c02c4403050304540c14906070000c4241c4456110f0a0451119a071550260510004c00315800005e54185030038406444034020021008a041558454840c8030307502442d03460b8010348800100801e88a140e0380b503c0000f110b10380d0032401c24405e01c04004c1100024100324019070803078a83c408035090102e440c140541c5500d5030802041c80c50082400310b4840070014001150030044080008051180700c01c031403c903150387c680650810082a140382c120b0a01e00f818401c0705030050120710100104143c031008445c0650403010000ea00020840e0314400c0104041000c0c012080080041071a010344804451180d0b107052800c1100c100006000000140b13400c0700202038810566900d0304074030b0350042c1541d000c200481e88848440109614859001070003038810380c0c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656271357 1250 656270107 656270113
    0x70b0a020c0f120d0c0602040f03120305130b010b180a0303030b01020706030203221104050c040501030606091503050c07120806010833040f1401061407050c01050a0c0219030219030203 81
    0x400c1c01d41105d120080b10801d80760a5020000000d494000f1a038a000441c05152041030a0107003143c002d0a45001401c3c194484244484150120311a500c0641c1128a040400b5540f141e01200201c0314019501d45d503a030181d0b401000000b4190140c02c0150441d030241d083c4c03581503480d500c007502240801d841003c280005240f0107500382d04104e40c20b88065026103120022018880700240079650100c800a092041c00b00b000c00c902c0d600350240d4400313089182059040341781003016040050903400c901c0300400d61214081075006071100f00300d6807416004040000403a04880006e818441d0958006002418150000d0501410400340c0cc100702500038103150402030401d80d40791042c00103290f1039807043e682c0703451040c0348229210f020f0008840d180340d18800d614000d40a40307081c4200d42100003002c010040c3d400003540c04107905004034000d00340305480350b104480072284040400c1c0029000b41409804401200c040c02c10350341103900c00c0781e02640d072903200200c66516060307078032000350075078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656272607 1250 656271357 656271373
    0x3142d0601030f080c06150a120308190b19060206130f0b06190e010509010801090336080f1c2a0503070305040e06030a1101080603070b0a020c0f12 65
    0xa1a030322443d20308540030303080d650304080c4282520350900c4000d8656113400083c100464195060203000440140641030012003103c400e502c001e030015200400140840c0c41894220004490340da1102150300f00142804001c0e4141190015500c80c645c040c681c050300c07803100050504410300007074448040d400580c00400c0300040e0707030f800c0ca10070002c0e100d203501c402109281c035260034510310450010406601c155140b54901000e0007106101078010740c03840c4c2d05101010700460b820400807166032060148150f0040c07a00407030070b40e04104160f011190042070b25030000e284140020800c1e141c107044003d84900804142c041c401038801c0503d51000326207030b4941c0201501e182840d544c00b07404100392501120700c030755032581c2c11070380310280c00c8020542c08602407041845c00d20a840c0e2209069004050700440707a02c5000100000300c0d51581007028000001e06070391020300c0b0000062170041411a2540030362000603455407044041c06002d04140d100200d40c0d4a01a0300d07907207201c011800075110310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656273857 1250 656272607 656272613
    0x506180a0c15020c041109150a0503010e0a0204090f020901081f150516120f0908030f070203010b040905011b03140106030203041707050705011106060f011803142d060103 75
    0x752460b403000100b5401900003240007500c5034003a020002c00d141054581c1c50b0825002c20054134034101444802507000d00401d40d40a810904490640f08078010500840c3c3d2805000c0e80a44503640040401a090502daa903071b60f69227030042c0840e2002600c920f82c40d540c81d410b080000076518949240074031024201000b4015244010400c80906450002d01e8907464000340d01a6245680b4100d40e0200e00c0c01c0070801c80c55201c5880c80e40d0f00c980b484c100b001645060041a80d901444031030301c400e082c1c0041d40342c003155002d500040b81d040700070b041400009170a0804030300800c1c00c1c500e200700c034030ba500c2c05c0c1032070f258401d1045000f00d04404419001503400c104045001b500003c00407641041c10f0818401c81d0052217010b8100d051040008064450505000500c201c0c1c1072465194241e01020500c2159580d031800814405403e00c1d08082c6071000340e10202803003205a2020f40002007030303c015004c813400070030710b145484035080311680e00d4858207085030344400c4c0d81101c032081c03a0000030042c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656275107 1250 656273857 656273879
    0x40b0a050d0b011d040e070e1602070503061306020a030b0d0f060b0118210b0103110f040903170408040b040801020c160518060d0611031008010605010c0303091502070506180a0c 78
    0x107102c146d04440c80c954035004400459907040d41c0c14100101c00c00c81011610b0f41c10064140a4081540035100b9814240505400c44c0068030004007401e4002c01c60308075491180e0320070580080000d00e244040031081c01d0295055022003001d40c0c080b41090342081032540200d500e400286840002d0304909490420394802c10b104100c080d440381903c00381848046012005e00354040d60180050042900d420301c20400d8020410f558a07002ea400c000c01a000b003a003129604200b103400c4180c0040a0381c417464141c5151149070441e0945003004240482e400805501030076072541d500701101c41588120b2035608051095104030740d031003e0030b0142c2600940c40142840d800c2200641944421750030b507918802a50207090000141942c007004004d071503411070302c2082c028040a002041414249400204080e0010030041d007456100d2401004002c03000c004850303d8206000215118825403a03c25121503060f195206000d030845d410214411007c104110881d034400443c1c0c003400e00c0e01c02c80c106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656276357 1250 656275107 656275121
    0x60a0506031012082205060f0306131104031a0606030c0f0904020703080411090405031b15090303180c01090312261f0e040f0503040b0a050d0b011d04 66
    0x40140140c00094403a02407405040b0a403090700007a88510040602002e0340c80048020554000360b80c60800c101d881c3d01040703403030072121084103627582d9a640020901c0b0507090500d45100034540160000f204039890064800d5904c520a502d03900903040c1403c070030f54034041d40c10903130285040000c5010720585030300510f0303016140b600325424020101c001038100d801c1110140d0210300528200300c01c2040e54421519404400c0b6603030410350915889081e56070081c0803069400515030301c5103040502080005c165650b4828403c202c6c50301c1c3c15081705032030384c00954030b44003001038400c05400580c4011590b0402100180d4401c8012132458a8403a081143c218004043c0315640c03171503c145a0104e80700c0440481040500355042c205003018a50940c8410081c10300844100d10501c44400302005403900190000c2814072082d0b5141441810740c4500c1d0300c0040789000c00a505807102c1d80040c05044803985105c0c0030000045498010b40e1000881040c400c060a02d50032580400e02d01544444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656277607 1250 656276357 656276371
    0xd030c0215060f090601090b07050d030f1b1d091509060a032406030b090c0909030403020f15040b0c010501060210060b070f0c0f030f0605010f0b1b010b04051f060305060a050603 78
    0x4605d644c2c5c3c400d42d548c240d40c050041510650400700f028084180c15006040350b4200c9618200103c01d802d2620020740441e100c5c0ca20100180390051078483d010310680359218a40040880b445400c1c64501d0042100d1000c1100e4025151000001c480c0e01d0560f0f075030006c50350403400ba100003103c1d02e00e04410542040c0c07101c8203100d680d664040b01007520000807603c10714404000741107075004942084061039000345000451b910070001880183c940480585c41c4406c00c0d140c070f440d5040cd40d00306c404203001e247c1061980420214040400c4401504401e04990640e02078a429915520081c400e0314803a02402c509442c00b006158002103024075000481d6014066042140703072120300c00510b09109500694140350a080718005010240c03255900500f80c1c070048088580c0b405105c3c07901c600070a00015054601140390321000d003421b40040825071300060040089191078085415020703102021030307a090180e410082800c600900c1407a001c2c403002000106d50314500780c00c020071640014409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656278857 1250 656277607 656277617
    0x601090e01090f060906060b04120213090506091c17010e0601020f07080114150916020304050d21030e121c0609090203120702090a0b03010b030d030c0215060f090601 73
    0x380c0b0202d205001000c850520401022034900c0c1c260420106a40b0320707401c02415130008010400c47ca1010060402c0b0fa00c4c2c1c10707111283d80d02010f901e00c000425400b0000f40445c0507450400c15010401b00700a1056202d00c402007030444c2008600f160340d05021010501414240f03001400503c003259011b42d0f10490500c111003840c1c100410550802e900361384a002035039160942a074810740f4003411540c1c4414807289007002055240005603800101801902028181d040d218030401e10a20856000d048041e103d03d06090662500b100415490718864050025035a08003080c28404d00511002c0080d10004041c0a20010031183c003941c440f118403540c03180200d070b00050107220750203110014a4001070000c2d0aa51a006150038004400340c09807208404011900050f6030b02c01405070020071680e40000d0185001000c02d0040040c000d002d03625203c0c0e030504085099164014181c03e05881d8250b41070205154040c0b00c8005090300d42c0c690110340180200e190341840490254041814940 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656280107 1250 656278857 656278871
    0x6031406040e03090307080c01030c110c1c0b0f060f0904030e15130801090c0b0a1403100b03040b090c0102070b090402131a040e0606030f1315021315080105030601090e01 75
    0x1b0700e0f1a42642c01410190019554580e90b9a014410703190078507440c1c2401245003401c0210030b074813035103902425403007181d0b80030b2590000c2107003d000203181a400070307403132826040040189107126000c4421a100300304d110550401428030603449800f0b164035498800c0028400e000f00603210214520130070b0815024441220840e044e0400000103000300c80c00003500c50000c3c108003180e0507082d008102e880c50200100b01c0b6083d8000801854244404212038582d247ca50a01c20820001e503ca4105203c0c04018081803050880100340905919001c036004803020720016030302c6100b14401c00d030041d0400e004080c42c0e4201a0000d209400303401001084140d11004503404410000c26950751109000c541804055529050140c020004950480c158500241007021851004094080f4917191302041010010300d1025080c640c8640c3c1000c1d925841400b9083c804207442e4411202c181c0a800c100d4045a40200600c5040e174002030064032990f824820724a010b400d00c90903400e0b06668403c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 656281357 1250 656280107 656280109
    0x2030c0607110310150e0402040b04110d1b05040911040f080303010e0702010b09390c0c0a03050606010f0c05060c07031205070e13140901051006031406040e0309 71
    0x500718240300d65480080b40c030303903201810f00c0c4c011201010403107076103050024216200d00860748802c4034888407031040d299660b440800e000e032100d0340700984c0203400c011b006218075095101401070219014810000010520f2600980c640c040d8090400304200f04018010b4031080e421002081d104030b43c44900c1d20f543c035010300044050070b40c03145074240c001000500c4407100101001d500b041a601c002e200340302c00380c800900440400b03071824120760701aa86084042d5412500e5200c0f1001c0f6008903880c00308000c0ca0442c440d032055440b181d03180180400c28110f4a840c1144d1415640c00100a0510340d44020040d00c2c4822810020410b01c201002004d0010341d00b040f104e849010390402a545070802c0380303000340429082c0f6103a101142d061000f00007941d58003406007039420004482600c5034044510300b003001400703201c20b030807041032404040100d02c060540265001d0807000c424481119a9920102c2c22644010750b41c0f69010131100c04a41c0340e242c55000303d05c9444c001d00507a4500b2039504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 656282607 1250 656281357 656281369
    0x1180b0307020607080f341e030e06040204020309031e0702010801061115150a12050f0d0c1106090d030e0a080a15050a0209060d150b07050c040902030c 67
    0x1511604110800000304500c0e181c2c107100e4103030803180b01d003032402803420081c0c405400e84800a00b07950403031150128000342076120881040481808035140361251707042c088000c0200c061242c4d40740003145c810418a080d544603108544035a4811320181c045902d03280d080101030340c00584000484c0c4410701800c1d100724007a80101142d81361a1648943c0c510b007900c005458402c0c140d00c030a084c03110401c81f5501c20440441d44081d0300462100803641c95503030b1104e05082e25000500c1d10b030400d16805001ca03004c41144288a031f16801041183d000030720b22645d5655901000354031600140748007403880006840c50b032440301c43c05070007007007207080c22039407004103030301005d150b10a800140362008144010308100c0a44005005078030050144860035880d100404100c1007500650700d036492000484815180d8140c5800c4000200950b5032003061258a80242c40c1d5000c2420301c0e9013105000083c8450241d088910480d800005851f00391070f52800c106c000c100c80501070342c0600554600c0c00b603d81d110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 656283857 1250 656282607 656282609
    0x27090320010209040f060605181f0207090e010516230304060f050601050c030f030a1b0801060306081609050405070b031003031d061605070914160e010801060507020118 74
    0x30000140c0380e041a80401c01034508100720010160f203081011b02c64140d0042c02c5410340f00360b4600354103100801c4c0b400b041028605610b172404d00041091812000c942c00b05101040f503005a40a000e9200301e801c40340d080310421b58180d4502d00240300f981c0081401144214541544401410707090415040320354010b600441c1c0032070b4042e546924142c0540b0b4541314680e00a5800e107001c90800b501c043d209130303032846803030b15a04058030040002105142035400803a06444042c60f55240200c1e110805000c0030000e005820100e810b2202c0402d01140009040004141d0502ca88408502e803400001c0106400340c4140d5840c01041c00c08612414600000c0d4064003055801080c1c0303914600340105101001c9020f8103d2503245541002a80e540e0020303580902e14840c041704daa90964136202c4e151160580c44900f0450401c83c46420380d8082c0c0d1140b074807580c803000d4004e9040340c11100440303004070341c51070560100d040000140020382c0314001030b081307452044c1494011660a10303884000c24050b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 656285107 1250 656283857 656283917
    0x30c1804032c031501050108011a070203070b1201090c0c080c010b100f030b03030304080301090b060705010504060c08071b0b090118060204091d0c13110c0601050109270903 76
    0x10380120780c0d05042200060039000b0940c0800e417941410b0009041400c188168021645c00e5001c200c80d01c010901108c80c1240c1c0201110035040c1e84202c2c81c0903c0d00005881d440505071080000f400009500404152035076945e1251803142480d9604c9240790409400c040856607108540e04883e00c60f03507551900f02c0410748480c160b01840ca44007c007036440301c00030313076001c0d81040c030501000407400c20589042d070303038080804200013044c000810054003d0380382c0500b06608210902043c803071994040c203410341c030340d5039800b034141c2d140f001c16514448600442448544030341440c3c80810101090ba03500701c184140049803005c02200d00c4e1005500aa100740e84907580003400300040b00103403141c1c1c400504000c00812080304501c0c892038460b40c4452440703000707050190303070501000c0003075101c05200d03100200a0394a4150307403882c1a1340c6560074020380b40401c0f100c18001c101d40040c591144142d50400301052010020005034030080c094415044040c080005084e8030840342c1d0320030008007184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 656286357 1250 656285107 656285177
    0xe09191505090109180818090a1a09060102060f04020102070b0c0601081b0d0f1e0516080105091b060f03160305010902070b06210102040906080606030c180403 70
    0x4100010403002c120107a0210030380a2030000301c240750a00c90100e2090050700059070035114500d01441d800303400c54908406a106c01d4403010080d80c002e2940c8080582410b00c0140c0c00d00b288840706016000c1001e803401405a4032902c00a810540f0303040c142c42d401441071040e5038459660301c80c000f083d0382004480070710640100f8014480d501040000c0c610090f190300303010f1241d800c8040415000420000c000e410440c00d0112142400450351f544c022007000d94084180001080c1411602d6604d84a2140b0001250110000d5001c805004140c00343c03070910081c00c801c2c2500c4c251030850100081c0556005201440741e262040300c082c020310b101711005481809011000000202100d030140c018039901031040c0314260100d100c0c03940c0c40da4050015500c16401c400c03240720b0025000c0071040300098642c0006070114044016412071004c95907082d0895110380c80c3c81c402c06840b00318054100c0e40122042090025140103000c615800500900348022203029050b07498051000c08009104482 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 656287607 1250 656286357 656286359
    0xa020c1305010f0506250c0e130206090d030c0503031f0e07050406050a03200c0c1e042310180c080109050c04080102040f140607030e091915 62
    0x30508821a03911194508020001981020740d0b00825019138082c45004003000328010003081d03500140d203101000020b01038244a01e491038044a51031080c0a001c8200f5000008206542d09003419003850380d1f0300418060500d801d41c000d1094103110240d041d4104101b03403181e040801c0c1c0c217100540c042d115840e00e07681c1050034580300150050700c6610003481d0100c60f03c20014034540c401c01384c0302500c02030314010b0750b01d13200c07034204030080c003410f0009804802d5681e881003002c05540f0003c061001c2c01d2010313100c0c03020b480d104001000464448121280c882c42c15408610710703290b40000c910600030261008442514146034084804c12190725104040c003480600100b0540003d00600c1c2400c04028440f41c3c002e0b6200405005041c4a950402e54407040424a0102c1d140c1c15a0050302d6008021034803290b03640504483c028031032103290171003684611410701600740f8000b210042501900c0d0044d19141036000d20001d02d138001c00f034550030341101000c1c518003006030181240711501400006485 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 656288857 1250 656287607 656287609
    0xf0306051c0c15020a300c050f030a20030f180f0402090d0b04031b03020105270303010330030e0c041b0c050109140a05010f0c0c0206090d080a020c 65
    0x348250304088020001d040141d401694005083c409a030340c0004850030043c00704003481461242c400c240700c62190a10180392001c1e91147c40d04c0b5131580a0f0045072010043c901040c1c3d168440d10b40300400090110400300d084c80840401907001c10601c804480c5000d80e44400500d80d904140750b00314454540c41c4038400e60745820145086903039404c0f41c085107001502c1002800074000302000406039030400d030010b030606018955405409a40c00230380e40181480745070007030081c00204c40035502e80341c038002560b00d101251841424016142c3c80110724690031034441101c84c079028184a04c044d034100104540b2176580511080758200f5075100031400501001c038581c02c200503018403500551800040340302c0c40300380c0401d013850703000d4031700700b400c0c035101d0342d08220340904400e4802a066001c090003d1060000000e4040c02c2d85c1d014a000b0800d007600205880c0988004448120008103080c1c940b0000d4a0000014903030010000c050b00c09020250b80d4854030b54120998040240e0407441d903518032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 656290107 1250 656288857 656288873
    0xc090607240203012303101b110f120f190302071101081021050f061605030c1905070b0109023001090513051b01111605010f0306051c 59
    0x2803070240035001c0d030a40d810181c014008104003401c902003e1095000c3c0c140548051000d5449610b00c00003e010380d2000e03401c011a408004920240010f074410025101200c0105146204602840107413076120390011855a094220080420300d107203041006456000a100c4a60702c0524180c40c0540c4a5015007084a40301a4102000741488006010440d20b601407501c240d05030f41000221300c907402e1441540003040c03a4100d0b4001d081c0d100b0062499249180018102d210300300e201b611a25080e800c0c0342c101c440b0b0005443c5040c6461003401240e0480c4c8800000c1a00c8151901d40141480600d442d2850a03a8080e0b010061003a030000316810180c05d4548040d0305c00b08100c2940e40c080e2445a00e1a2644105100c0c0000e02a59000803404c035085041041141c290401d0480da402140385880403d4aa183d00b080e501003019079024881954000c01c046040f960350b80170f42c4c0c1010785410010b60b2100100680c0204041c0d47e118049416500c40c02c68110503004c1c0d01d0301c05109070781464001c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 656291357 1250 656290107 656290163
    0x150b1f080406290405090111040816080d050304061109030303040b01050307060302160209060f130e1006030201020d0f030f061e0e010e192307020c09160302030c090607 74
    0x10490f6a600e2011441400d6100c050410302c1003075a002601e51348103017119004001e102c03007070604103600103000259054005407c49019070501d200e100e03c9130f51410415562070180c82d650010072030a2002501041141c0c0c481030300341d1442092149407900c030000190855004503400c64400720354030010302450400b0041507000d0a42410f08504c0c25110b841203c00003d11004028440c200200004000d51100d00a5803001e50014248101303007240140d40b54080c0144400d0380d4000d200d65000f22079060f05038000c2500b20382c0c0603006008031030428081100c1c1c00d10600c101e8820305031201d1a940e110035880c40381d03034014018012051250f0701c0d40c02100720810382c19030181080480300001800a81e00041d212508150f00c00c651000450340700d05c034600940700004204101c9003001041000c4921581a190b02c251800e03030a40302029400c0307003000910b87e02030340c0071041035030306000d01000355020ba4010350304000080105800d1900207000036100d0b51064074103e9030301d00310869102d001b40200c44078003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 656292607 1250 656291357 656291381
    0x304030b070c17091e030307080a050301090b010926120d14010806040b01062001060b07031707120f0222081c0203070f1a0f01080f0109150b1f080406 66
    0x84c0b52070321510025024040207010451481c004003420911a50204102e400079a80030804c1501da00c2d4400001d03207139030002d1040720016400c108141340d10b984118500000c2d146860901000c0c028210411502c8148017203003da03581c41100c6602d00f048481c1c60103001c442e000071102003110700022030804140756042c0d010041e0342c2e21403420301001410381582c2905507045480c00c0840101c858011f0b42c0041501030f4003980a510301100030541603059801814814020b03100c0701d0320710540303040d03a01c0e1200301240c0300e9000440c640c0003c200b1488941020303191b0f00041030054188881c850307004c0c2e0384a5492041d051100e95205d81080710340400d10060b07210700d074265100b1041644005000c0d440b4842d41800900383d05040c000c1404100b500a10401c220032001066044c510b4400c4620300425028011403009101d400c1450320303822014021a44510b5100004001e04444200c1c2d2402801202c810594070841c140a004010172510000300c102010982d56600c4504040c104030040b00c044036041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 656293857 1250 656292607 656292653
    0x7050906060301050409051204030308160f02120f040b12010504051008060712020c01050a0507093606080a060c260403120605270a0c0c0f050304030b070c 68
    0x2080c25600d21050703a044540c00d440205d03165549150041c20000e200801300400140460040180b56001406034400e203041c068580e940110304400b40c450a0880c020000103174051040c5180c17500c141e40207410740010400c0c0711400e01c5d880c0d100388061600004000c1040752040401003100307103046e0007440d8100400d100b50184007400c04208580362b03034004001500b404a2414440301952030796040750b040d048400000c02c541d040c00a0220098039040d907c84c4006580c1070b40c0802c0d90342c4010459400f041e011400042c1d64941030300583c103810400720507400c50b15551180000c5080d0144007651990b8810580000e404226907409428140c403d202c4400c06d404c2003284211005010360f030241c009405040104101c01500304203809420280c201c44d030040c21b01743c1d28080c0b400b440680c2c43c4146000703491810095803081a180c080f07590300741c0c0d450001504406c01c0b50100d6022209000c0d01030040096901c1d064684d2105800070006565040000e030f80040d0f010144030594a019004a0740c1e0301c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 656294964 1107 656293857 656293861
    0x60a1a090603070c050f0123061513030b0a09030c03030e0708070b090a0b030624040906180c030b151b0a0303020a0206130302030d11070b0a020c070509 67
    0x4111742e00d21940041000808040c02040b84007841c04014901c0302d502c0d0035107031000210241440381c1100b0408100600c1c0211203008001005035030700951081482c600d02000c00040041c910b004480c07038103010304002940186500740040d00b5190101d01041c0b4001080e00b00002d030707441030880303100703910000409a0240002d80113101084451b4100c8a0740c50102c03080741e1100f1035103107034800c440f40f4520300f00d824082924406811059040c90a00c0d03200c1c40c3c0e101c21141c8136001408040313090740341d80410b0303440ca01500305640c08524061116400620114054502d4442c44410309100032640858244603944441d481880e12400c480c0b07103842d242000782c0203610401e80100180103070000540f0311044100b000d164140c2c550300031803420004616000c003d10001d41044040d400030000c4501082d840e090240c0205100720b00160380c0c20100312218980415984021300414003030303003 = true := by decide +kernel

theorem cover : BRFrame.Cov 656115107 656294964 := by
  have h0 := BRFrame.cov_init 656115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 656115107 ≤ n) (h2 : n < 656294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
