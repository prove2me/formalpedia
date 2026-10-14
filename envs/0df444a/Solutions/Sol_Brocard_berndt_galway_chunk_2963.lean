-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2963
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:36.358988+00:00
-- url     : https://prove2.me/submissions/0b14b035-02ca-43ab-bb69-2a2ddf557148

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532733812 ≤ n < 532913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532735062 1250 532733812 532733827
    0x314070b0a05030735010801111b01020717070303290d11030102041d0f010503100906090c09060807080105270a140c09060d03020a06050907050a0308032a 68
    0x220b840d84014807810411546880b05032030020f1950310302280070154a0b408045490f511241004120107038840d404036031400480e00807124005c0151543c1c081c10007a110446480c048425000e4407900800403c40c81c10000346101000c19403001d0300c41c2a01980d01004084106c1403900c1e00c580c84092502c03240d01c10ba107485101031030b002007000f220b1407056842c00780841d800f8011a099070056003210101c4121001c5d031240000c51050010f912003050490620039500d4039001c2904c581c640c00c109241c2c2c076100d00c0076a0a2041d0b0360000407121b07600402d00442c071950751024070300404442c0141e1200d80101d403000108000140078203170250400c2d0b1601c0e03801c0a0744031080900d411030080c1c200080d0083c042c0d00c0f00441d905002500101a0f0f420103480c2010900e0308100551500501542c0303e01d822030350a0010903400100340103800d0344981c0015007078590348100c44c5801c076145d008035400038000c00302000300f0420101440c014814559504e080d00e0545407900c0d51000d84080d40303805094103201c1039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532736312 1250 532735062 532735067
    0x1c0303140a02030f011401090e090a0311060408040b1602061803060907031a07020c1903060606050a120b010e030d030f1503051c031b020f060601050309030418110703090314070b0a 79
    0x44940c1b0005040041109941c1c001c281201101112030b01e480d500a03504c54000e03d900410419110500c04019140030302d015030300e0140600817030080100850000c00d40c14040d1305807800c1c102200e0b400a24668660000048800d81302c100701000a029011b50404039030780751000030701381054a601c083c0c034001603886180c642201500042680d070441c429454900282e45030455480c64100f03001034248502400e40c2001000e03580542c0c094420841d04000780c42e1070540c810502904095070b2840403032803e460b00e00490b6008101c2000f40e0b81800380d548484900b80d015404103018601400047c413455407682503c10014100744006030464001b048040d00200e4000b4140c18004010309000914200210789492004002000c0c4009640800d5120000700401c11009c0c1d0f0128003480c1031465481c1c184440c9459009500c50100e040e0890b82d4030030f46125051f0403e050000321407503c103449001a08004014034400d00c0b00343ca4401a41d111604902c0c00820034005072060b05503043d2400c0c0e9401c204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532737562 1250 532736312 532736339
    0x50901080c04030606080304080d05040f05060d0603020406060908010b030c030c28030606180606050405040b06120901150b03070207030201110f0f030c0106080f12091c0303140a02030f01 82
    0x2160080c400030440400041c0c4e151003a11302500800740115213507810941043e1400001106d000280704090108011401c5450690010759400f5102c040e100c0501c019144040c0605820080d0700034201103010602d1070b0710400740e400302c81018000307000311090007052540300c454098149030140c12490321140d0a0a20000380780c02c06124840960081c03814002c400300290700d42c0c0040340d0a070389940003004881c8100341012120012410100041031030140b003c1c160381b1a91159078091380e101d07003031048242d03520810745481e0840300d00303104500d103890200705008002a084040940380c141001080031139505041d6446181e09030010310401d41142c00543e40803902c4000d2585c0361144215000c0f0b4011305201d0a107124801a008603102c0d00102ca8280c00d41e50700d41c20803003890b80000411002c1160000b410a0800b1040b2080d40e0303102c40240105020003030543c0e0f107160a0700308013014400c26a02d03921584000f60501851100d03074680003502e009070b1005030740d51004200410018030a1040c0880d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532738812 1250 532737562 532737571
    0x61503120f03130c2d08160608100513060807120807020904060e010f06030c0602030903150a110c0607090f0518090313030f1502040e0a02030a060513090c0e0705090108 74
    0x130344081003a034070b84d0010f80e01c01410030440701603600480382c85d00310394880900202400e00708014214402d8030414a0103844c1c40d51080f01c040203000f1000ca1481c0341c5070004c0c08050500074000c01c248405d010074230713005040c07107114285451048080005030580107070018441c8a42c080701040c909980758003003101844000e4000c0c1c83c0d040e0307100420600700ca001d1041e00103024003400003103500c61860401182d4072209602240030754000b04a128460303940480c15001075000f81d443c4200580302e255150008000c1d150140c9001c0b04001f6032881044400102c0301d22412a0f40d49040c4401e4841070301a4080da028071881d03402c8154080048101e00721400c50035480003502c0c0880f8200400000d40c5488210160303c00c1da1225250090710040c4400187d940600f10041e030b40940c5480d10b0400f0f64019000020700454205a01101007020713012241c000500a002c01081d043d50711100d0007441d8003c1c202001c4c1111000440400010740702c614640b214070841194a80d982030015a00055444440080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532740062 1250 532738812 532738823
    0x31602040f0c0806030c0103061a0304170a0810050103090c063f050901050609061002070f0f051c120c0201050d0f05070809010605090610050c061503120f0313 70
    0x31540e52003041c1071240d18041c40e0203546408075030608906050405c038161007078038105420040c09010b030b5508101e502044429070a00e003580d964460400c0c10b60010019420402e0640014884070616806482c050080840000754a42c10f0340c0d0b5030040d012190280da004248040c014401c01200f8044c07180032107203030350112610880c0001e11480500c12000d42120038001d80c6882c031038601603100ba1041581c04410303e0020403483c1006400500103000003002c003841203040903aa0355800c1d109004210040482c05540064161980066400701c035140c0501c40c0a01c5070840c8005800880c1c00b10101c8490300710408080c04000844210f9000034a0b010680c18041c0403c0726a40380605440340b24004880c482d0002294101080c00a08907440603025035038a0381006403e00041ea00d0034199074200348201c5800c2c5c1414840e14090300c813070003110104405402540700304072240610b85011144060110207688800000c4032101c02c0a000e440200c8590a100b400060130f8458002d01c403454050103203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532741312 1250 532740062 532740071
    0x170705030903010906060f0f0b0702040b0d1a04020f1009092d050708130b0106030c141b0c04060b191e0201061a191416081207080903160204 62
    0x40080b9003500c1c1c4070308080380c000c1c1d51201c04006142150203c02d0180c1901080725003854544100b52100e4054840701a11031695031036881c020b03543d141c86071060345600c21a56000c2080c040da44d0340501d00d0440e01603015110541c0b002c5554a0300700305805560240c0d48600da151424050a58000d12440042d080481c0000054803802c1007200024001d2206549003c40d440c42c002d03031300904988000c1c04004408642c0060100040c0304040407505403a0315190000d07009030015001c8501007980720001c648a100001d03650070500e020703a01c1209a464490840d900380d0303620424842100c1300c42c0b0030002000024800130043c1e104c1c510404041007030610b0000d120b03901841514250288036420380e0b000d40c0d529001000f0b410380040000c455000400c00c0340f8100145803c0d41c01d0035481270b2890f8420461b00f10f281070500c0d07031200c040d244000c3c100358100501218914100549520140180102c40c1c1d8a00018518a1088072a5441503045101450510351110416900d4060960040b640151603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532742562 1250 532741312 532741327
    0xb06030f0a0f05070602060115083301090b03070f1d030d120509010902060415090b0a0c0201121b0c0510021306030b181b0d0905010b0112060317070503 67
    0x401c8034604071401042c0c1060a40014506945040385942c01a010340d0031540040007590402c80044a07810010700707101c000e5541d04c1540300a40041c07038205030b45101d1b018800d01c1e044c42c50080b090304041400e0300c0740640319840d8010f80310036002c1142d03504001240240c0441c9410302c00c9400b00502075075910f42c01d2a08000c5c2d40021f003452050003500002801c02c808015172a1011700505805c400c41c0c40c002c100040190300418054416405900300141c180c28102c10154400c2d02c04c5401050f100e17265075254920a10003c1c141107420200381d0000e4001c000d042c1c0c0c0101c0510a800700304d244d0142c410140d00030068195107500f6011400d9609000e0048409160720582c0010408818040380c4032030442e06181d0050100d640092845004420100c40c1015401214500315080301c0c08016800c160755403211040d1603031182c41000c0c8030642c02c0408600401205410410316400e00341c9072001006042c10408040721414400a040ca0490789088201c80c8038441c01082c8590160040d0f900d0f0010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532743812 1250 532742562 532742593
    0x30b0a0b370e0108030a1b02030a061a0f060301030f1407330e0105031911070c0812180604031a0a0c0e030c0616050d050c070f030b040b0603 62
    0x1c44800c0045003156203000900881d601c00192800307009400c81035022541800700355556406800084400c2c0030000300c480302c4049420810501481d4000e00b291400c2e07100e0318000c0049d04007001c01d900e4030101400d9051072890010408214584054903803800d5030719680303600090464281c4142c400107a4840c0441520750705000c071402a00e2140845158542d05420089000b4401d02891018034120304800c0c000d5540000003a130b00040c2464019101e866021154216a0b0441e5007800f40d24a0720040d003025440c250040c059650140c08502d0700c00344c0e501d142c00d0b11102e440c40d0720b0110107010001600d010040c4940c82d00f0096000d80001c0c00c1c9034490392204e102c02d0b4281c04410484207100c0800c600d03d050380c0982c104061191070403151034240400400d40d191081511a446504080744080f800681074084500160300f180840c0c1e03145e040c00c000030380311384d01210102ca090f00541c0008651003080d80c031a8411641e2000703070700d52a5691901c4104840c000500002c3c0e150241003180c03065400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532745062 1250 532743812 532743859
    0x61833010807031106210615070c080c03030703141305090a021b0c0d02061c050705030a0b060403020a061209140f100506010507080304030e0415050306070306030b0a0b 74
    0x1000c00c0042003a2415818000c030382c0c2c561307840b045110f41401c2001d0220307040c49940007410242d11005568150300d0f04030000f5103504a07040b1090302100c0c00724000c41403102034142001114291400d44150107441c9003815264030840c403014000c64041d180c0050100662801403421500036503091030400c0c0c0301c1c40050640902070f01c0d011060303500800c0c1030140c0e14808101d00358001d000001809200a050049008090f4000d0040c4c810390b000300340d214042542280c0341c88444800f0300c082140d403500b2040a020350700141c035203551306032408100e03032042e00389001101c096a0300242500112807501b40d00322003440f000310030110420b454203807000c00150303441c03218683e01581a01030a044104604500e1804030110404110300e03081400f88401640c0010803151481c2d0403c54441e03485e0303540d06042c0d840f5103002c1e16054000f481d000d03600c006010140148002c0d114110142c0c0d841d5190640d080f01910342a001c040c0083d4000d17001f0812203200b41d485224641005003032012985240d91070040d610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532746312 1250 532745062 532745069
    0xe2d070803040b16121214061c030c02040513120c08040504050a1515030e03030c04030f080c160302040c0e010206070e18010b0c0d0f020a0f060605030303041406183301 74
    0x224007103428a03034151b150094000c900c031804200b84013441e1a60004402d04400c50600580060140098061500c80c200c1c41c07506030740150080c842e506203401800145921007030141c5000d1080d1014014061240340d420000d61340000840f41854241420030004120103008104140d40d00e9020362109c450341d080c50001880703104021041c2c51415280602a108000790209042d00304208004803041a50180c5081c1c9403c81c05003004107920f89050b000512074101294220710032600e0110034807214502c0081524400c0c0c905004c5500345203001c0d40d400c14400c1440303015821800003e204184951256050703070038020459000030500f4030260310044000e03000044060b00016160b4001501080084c03102403040c9084200641802802901c078901032030001d22102d00f00083c18103020450700040050003000381981d542e130500745466240e104401c25450000d0088000240b0b011101c12500282600100d0207000c0b2411804071a500e00c0c1040316980c40842c21004800ca0501514020213010f07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532747562 1250 532746312 532746317
    0x3080c07020d1a060a0503060c0d0204080a050d02011404200a09060608091902152a0f010b0102010b03030a180801050c0a0201060506040b0712030e2d070803040b1612 73
    0x3e202004603505440381004203e240203132030b801000c0016403800201203034020261030150740c540410100490103440b6942c441401842007089030024040003041c3c038145c010b0660000c0000340d0f024603401d9a005000c46028024500b514040c154500b40351047c1c00810034001d0448140350788450505041701c007140c00050006044400b040000701d02000b008204032801c03608011490340d0390f4001080404030703145580040f0303030118410f0100700b580589070000d52001240c4c24041d10310741030465a504040c8481903c076600340a6032140550040c459a041d0302d001030040c45c80c000c0540000e42d1641c83c1e0307114240c1c0c5203141400028a040702032180f0703409590556a02c1d561100180c1c0000c1c00e50700b094008511803003040000f000300c04150000c41e41c1e0280d02c0041c50000c0200b440081d001062500d0481070035004a124034280007861070006100340000850081e00021a4507a0980d00c203140d00948105038001c200610481156801510511886404258041203241d85681c8116030200c40e0101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532748812 1250 532747562 532747583
    0x3010b040e01150803030f010506070f0506070309020118050907030c0e1008060a090606020703031110050f090d020a17030405070b0d0c0905010c030c11040204030602030f040c080607020a03080c07020d 88
    0x240f9040c2401c00100030300030007036045080c910032100541006118a038403928001a15a04020744403e0745940c16410809580d01880e02d498090042c0500c41d0040380010700ea14480e44901c4a0780c2000415224003503c1c4048070398910704150020b100110300f080900c020116080640e0742d6480b441c01900d2403594880d902c5003000800e010302276605400906215007817000c28050309500150075412a501490011000204c0c4501541440820000124420300700307000c000b07012500b00d5001e0f00a84079001220343c0032995242c1203807921081c0d20001d246141001c107610b401c0540001a541081c020b90590381700742e80e1101c840c0200c0d80003907030428485480f58410307011a90010300c804003d10080c01c00850414080e034006000d011101c00c000c26068022034005110f0b1102da040e20055640900d0455581c02c0c50b04200c00151412941201e900c5a071010100f20128082401e80c05808203400038030510003242d4040e1251040188030a4203844180b005001590b610110241014001d144642 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532750062 1250 532748812 532748831
    0x31b041a1e0405070207060c020105071a0f090c04060305060103020d02040e031c0b040b0303070605040507090204080a050d2c03150f0a0509060c040603020c0a0819030507090b0403080903010b040e01 87
    0x140e5000034404e40c203640050a04000b81ca8100c20070149030741c0d0901c0d18603a01c11035032800c8815024070007403440011801c1010081e68008030346a05000340016003c44100701d1072101000242d46203408000c001d904448010401418200726000f40e43e44020b00104647c81c244145500e51b809c50034404001001d6542540f9181045214074a410301c011784003408070500074004280d81c3d1041ca00010700665881001a050040510200700502008202503503541c0c2e46d10312141d034843c410442a20140164449020800e010301c0c0d694600c040140d5409100b801000d4042c0000340c4620180c9805000d00d502034505007000306121485001c00d5822507800d410048011800c840b001450100640d01050610221078a994159011101c051038017603503a08940100b1400c000c0f02744d1000b0b002600c041103041c2c4209540300310b01502c540503035040002c1e648000046440201c01c2c071404000f018108001d00100e203580005140c241c001500101d00c1f03000c0500814210341800042001a035500e54684 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532751312 1250 532750062 532750069
    0x92708040e0108010c090302060a09080601060e03010609061419030501140f07020a030e2701080d080906060f0d020d021302090f0306221703070518031b041a1e 70
    0x154094940d0f00002c000503110fa5202400c24605404064416500810500300f46807107a285c42c1c001c0c1a07510192000c81d6522100038044400350201c0510950038207001048003003151143d0301c106c90000d92040c0c00c00b5410401d2181c00f070204540c03148010344074140400411024052408010120406201140343c03403002d00c44076800103002401150040099900030a500034000b00d444042151150002039118021410074150f008204000c500c0c0d5100000f4000c0001c1000314a490a0340c4510b211655110101c0351140c808403502d43d8419003404e07800515082454144080d944080c044c040b05a01c1900041d909281e031f800701c501041e40000391041c00e03003400d510000700d2071410750050400c1e0800281034180116525071a04104206554007000e2040220040344240b1581c85030581d681452040200603504c810b00c48000481403c0301075441d42400694042d02d8904a90251859881e420410000d00020004000c84404500d101030b0b10f680c5162004202c4020014101044d08a01052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532752562 1250 532751312 532751339
    0x3030f02010507020d03050a0b1c03030516020703080a1b050c010207051801090506030a0f030302040e0601050304050604031805031608060f0609070c0203030f070b0712020a0909270804 81
    0x816085906090503c000c1a030005000201344a4508011403241d81d03a1500c2c0d001030642030b03c0f03198003118082c0708038405441f44545c1c0c00d9860090350300384110350314800f0710207810151801240041e48040000c1000c503011101900034845145030041e588124495020b16010781824166510380100344188041e40e01006118000c040030f4444040964444d200f6031201300051142c1408a82c590000603001d42c0c09014440500e5404040c4070510f40f614100103000350428002ca903484038900f00852902c0d03010f0000c1d684559032190091a8595540e0307012503681016450805050310340b00c401203056502032005004070010160002d000c14500006030b0316043e0040d10410701d001e90a0b0501000c1d40724007283c907600c44e41505107c55103448a102003031a51141c0c8420710407000e000f040600411040d840c41e14019100303a51844020b8500b900f1540492289540740c0020030310884c010000300141e03406c1200e003040300090041145004280400c0c1504000300c084880180009083c45500c0b010840c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532753812 1250 532752562 532752587
    0x1d0109061a090a050a1d100b07120c12020a1b03050316032309130b2107080109060606080a0c05071e0c06030c021b0307050904051203100303 62
    0x1814451540360107500d441c0c40381e0440703101d1028500094526003d8603a05402e800030070000d015040039903982d00c12894507044040501c0100742103040030444a1424a00b0002559000000f04d0303d4005c4a03078540c0c448007030840c0007c00b0702070802601c802066121540703861080e0660040d08160300540741848150f51303040100c402c90800541c0c20f002050000054425400c5000e40c400301200e014241a030b2031000c802006111101c280d1388100038203020401030a640345060718020138044580c800305c03080d5115240491307048241849410810310309070240c942c00414900907104440d4541900d14203645400c0e2095403d1611020100083e540c4800b0456102d109a4070410403034490303403c001c0091040c000f02501d14000c49809128451404a5181c51301d680052010100703541d400d0041c01804802d07000e80054060f901503004001c0c4001d841420b502d0000303000d0016541440208030300c02401400c01d032a0781c4940b01d41140308000701c1c0b000b14000c405504001000c1e901e5450010110040402c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532755062 1250 532753812 532753829
    0x130c0803030a29010f02030f03100302090105010c17030a0212040b040203070f0b07032a060501180e030301210b0103060e070501140d050711120417010209060f0703181d01 75
    0x10204220100c403078940b01120a024644005c4961904030101c0c514080c181440340d13440000024040c00e50000702d43c4d5400c40b8400d50380f0300c00680c1d0b01c00042d101c0d10903866025100303035144040c00d400c4441d500011644552001d00050808072206545004103c013110215007040668040c8400d43c030741000b80000400790400807080560600041c00c00c81c1c01a924000d00b8410f00c40880408071102100580014046034080b0b000c00d40c0500b04071002e07007402e02c100340303203440c62092200c0b10b500303507005980266003100000c40c0f45900c0d080b40340c10200f5203c98034010a103a81803611000503050303e2840d0086000c1c020203c0d04c2001140414103042080d4045410b1004c85c09c1e101422080b600141c960089090500051a0ba40c0300d0701540d60100500308180c00d405415400c40b10509072001400aa0b0103901d880307a40440030a43c02800c03072062a0185601c140c00b4049520b02c814540d00070900203110345805c140184000300030300400c072020303080b0014030b00c1c040058a4454904803036131801004d041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532756312 1250 532755062 532755101
    0x11e03060e06040b1003020c15041505090f0a0206130f08030409060e0f1315060b0a022112130515220b0627010f1a070507050108130c0803030a 63
    0x1400055442c0c8175640d01201403640108481c29010000c0c041140c81240303552800c0703864a800c2c42d10745880951034400802c01b43c03502d80407030400180010700d07144c1441c1480041c0600b4015400300041500103213002c030b5a0158107400400d80030448503003000200044001152141d04241d0f0403000d40e4a140c0007668000d521104004c000941c98440c0303034110180400c2110003180504000ba0048105000c000c159420844001020803480004040a92080e425500c181d20101c018070b03155690110b04058413801400054400303d8920b2440390030480f46440900c05aa42e65100b50600080807004100b04640d80100003001d058503925030b50084204085040083d030641e245460740398041d0a550040c48001c407841c140702c0309050881c04400c6880440700603980d40d0001c41700c42c490640039000c0c1c6103100015890350b465141c02034131900d90740500580b080908081c011940400c00900854003056070001041c0459411203501000d004050042d559925050004100365144188503400c81c400b007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532757562 1250 532756312 532756331
    0x1e0c02010b01090e151219050d030605030312040305031305072403050402130b030f030c01061d04081e1b010f1a03031209010209120c010f0e0618011e03060e0604 71
    0x5e40c102118992812920f004821204840240c900040040080e04020400703c1e10070a1040000e005080341c400d60f0340c203000d079a8550f000d140d01d900480040399144c044c510003190000780290b0140d0380c0903540e41034001c2c002c0c040d911458501000380d800740660301e00c00660030503042c1c1e034012a9000c80300c46003804e10440c14164042a160940301e001f25840f65a24400401c05960611451000f51403650031691901e0400d881e04e402800e841c407805095071440098100415880a6140d1045405c280d0907810701c01a07940400002c4c1002003011412401040b042c00e0758903440540c440f045082c0b07400018140c5041c000c00c0d04541380440c102d001c4140002c1a411250350020407103a0100b4040c00300c50680e2242545075019000d40841561b101d0070100361703103440b82c5000078807080b091800d0340c4004c02c10302d030800142d40c420320550040b604031000300301c240240351001850a00d045818034000b044405411740f40424444003124040009498120800c41c5114071500250032810881d000c010071440c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532758812 1250 532757562 532757581
    0x30c09050a0c1d03010204121b0603140f091006030803090c04060503070b0d020c0d0507060f14010e0403110f100f050601092105030304060509210d1e0c02010b01090e 73
    0x3c0b20400e0154a900700d0f4600d041d2820b405a80c001d010600140344110298907007145980c9400c90401c0100c4c00315000054241e100e4015040b00000300d100032080340d25036101c25400003070010006042845150003602c1108140c0c0320b004003d40c05200203507280d00b414080c55080825020f00307d4410b50502c0c0060180740d902080e443c1c01c5070f88009050740e4032801c05042e64082e0148a080d283c89000d14041c0e94001a00030008140492003003804109503059803e82030102e9420b0950301140700d02c104010b00910010944c0140c025000381411505070b41707592480c40c40c0c05044040c481080e0000001e45000004c0350080300c204480d0f120301800180382810008013488000e00c01d200e03110510100e12032210800003840c0c00031541060903a40d5a2601c0d04040001d00000d0307031021010b10824a0640250068000c40d40fa07a51120300410b03d02042d50345030f0806820103210b055200b00342c04400d070004802600c25400035402640000c600f00f098000050011741c80e6038000700e070030180c2104100d0b2002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532760062 1250 532758812 532758827
    0x403140703091715011818060b181b071a0a060617221502070804050108010b070f030e04140103050c040522030c03090504090c081e03070803071107030c09050a0c 71
    0x103080c00c055842001e8070f808110051f003094440040380740ea24104060074440942c00c030f107421000507505448140302c0070055107400c180854441840300142c14409245050740360041018a02070b0307940c000c004050b01d4139034030044015520380340000d0b56202c0810619801c041440102000349007401d0303035450141c680b400300c2d11401c3c9418280210307202c0000d003005400d05540d184100e00d0b100440d1100f02e903181000d499441070003010b0103c1d40400000035819070b0f9000301c860fa6580603410442000c02550103489050700740e00c01560042e15200261040004040e40c01c3c003e5001300e00800010b943c0070244811907102a14803416001c41c4c80c2c4880ca4586240071038a030255040c03512190a60fa681001c4581420940209138818204845182403010100318030b815070394a81c060710b40440400c1c0440b0000084d003a1100025081401004042925200955485640b07030038202d4100d40084404d42c18180260411103000d10740350410b0040881030b124540e4041140c0108000e01540040054a02c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532761312 1250 532760062 532760069
    0x50a141803031b04030b0901050603010605040b0105091012020a0e090a1815060906180c08150409020a0305120307020c1801170708030a030b092d040314070309171501 73
    0x2800407140f80c4081901040320000d5400210740c01880c103200f2041c501a013004d0300c0c4c181c400c2d0b0030800045090325042c4111492007405031260f030328185000d003e101d8400c01e02040001070005520b0700c243d030070000d40002c00000c0a40e07a900c0d01010074a40400082c0391000d405050498a4030f520224900725101640407130903001428481584920151071001c1d0401d900718485841c100750b4000f40103018004030002d0001c2150041c00b200b40c080d901241c0c1322404642294244041e0080d862490400c7d07844520000c2c0050320304060f058072034641a1a01511800c00c12185600200b000341c0c86034140b00e0500e2030001103402110a030000c2e40542d01c0c3c030406014103920003d000c101005e000b001007080000415450050300d48074014808068000c0c90309401d0103001d00408070014030800d4860110210894000c91000d210b111b004134203021510700104101c0038003403164104a01084481c0141600901ca65190030320981403a400e409444410b1040c6402540502c41c4800c00c42c18030300ea980d055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532762562 1250 532761312 532761331
    0x60815031c2a0f170d150e060415050402090402040e04050304030c21030f020f0d082d04030c0804030c03080d0c1e0305091624020f0a08160204050a14180303 69
    0x1c030610306505045505c100d1001c04086884c011840110058035030340e00080b0744a4080c2e10110f960351405210175143c003024131300000844428288840d16155002e001c031300002502c0142072680750080d4402108c4151001d403010b6001040400805c030070402164040c0600c81840d41da540b400c12441410200b0410004050000c90540003e03014420030140442e040700504544655204c20400341c1a444250ba6005510400c554042000030540704407140041c10140c2c1c1e4100c580d40d948085621f00c00720b08080f240c0200c208000000f0130281a490405036005036011640e5081c7c3c0d1030400d04403030380c102c1c040003803140b0044070b017411206850017503490009605000c50682c1c2e410b0403540c00c1c141c15031035086046010800108840b04540307007408411f1140e4070280f0810503000c40c203a0b942e407410007510b0740e81d5200c1101d103400500864050305141042a105468100c0030398000b5050300c0085600f030102c583d4800201c0e140d580c4a070302464002401c03150f44c082e035816007082103407213100040c5034081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532763812 1250 532762562 532762583
    0x40501080f0c09130501020a090503120a090b160c0801050a1a0f0d050709021206100e060403030f030b090c0705070f060c1106090303160507050307060815031c2a0f 72
    0x46550009642c44c030000c1e4048002c6503500e0341e070071029054440e1806224040d1050015800c0103c0e80c5108a40c046803d5031600407150f840c00842e102c90740c0c04100d01e40304841e0090721410000742e00605880c003610b0711500103d05854072241c00350031200d18540d138800304605045011540d0300c90001000303a0150950f040c103441c0b0100e04006140614903032240c2e42e01c910000b541c80000403410101d80c040c50301124900f61142e081c50088031620411000160b12901c10402000000c0c05040d240d0707824401c5040c0415a91381c0500094480b000880386c000907180001040c4c810010188403410140180c242c2c8548000c2c10941c1c010130b41c400005006240c0501c030100b0f5602d5070f42c0c4405540c4a00c4005080703a1b42d4034640300c0c51103403442c40308038201d07800e2181c014013240c3ea140200b10141a13850035034646140b030ba904085204405050209260180114813481b1281c00c411502040c4c0552a80c071500407580c582c0700c0004036443c0028540090066004001d00014044001402c00c01d400c509072700d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532765062 1250 532763812 532763821
    0x2030415050a090e070e0f0303030103020f09070c050106030b0414160504090c0806070e10080702100c030b030a0605070e0f1f050f160b01080607200a051605040501080f0c09 76
    0xf0750449041d00202d040400e42c3c01045141c5500018120342c0003020303036003ca00406405e060643c3d0740000c2c04000d521403001d00340403915041220000f540b103002464842d0194032580c5030142101d0a9401c240d806285000802003481f001103440301907244044c004000c103400551260089a03400d008851040d9150f0b00d41c0010307c0500990324003e8041d5405586260622100241c08500c0c0003a0710780c050a017220b2842c4c4c1c0c03e401909203d20500340e6801811035100d45003040c2c4010714030b000d449024540c4d40d10380041140c4080020000c101e01c5010006660b040086000e000744480f40c007094820700e20034051081f544c8405068400407010300070300354010340c00060240d80a0280c4515418044008205140c0e103010b480d424910702406440280e4069032580d207103070b0311480107e40e1f0b07201140828544075800380d565501d6208003010f07401610244062a99005c0c208035803524800d44260540343e06200c0da160500c0307010f0040c00802d005000040c4001c0301e00707840d41c0680d081103114041404c0000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532766312 1250 532765062 532765067
    0x203310506090d170a1814010e120a030e01030f0e0307020d1707030e0f0109051f0306090c09050a06170708060312070311010f151403030904050f1602030415050a 71
    0x80185030348110080c46180c92480c40e040ca5405c07615042c000a07141214107001c0b2042e41100c18142c038101e203a10354410804000644060741d880307074290740040e846090030f0441002880780e11602c9220b07943d40d0200001580004003620700c00740404040c2c600c1c10741145014000041212041e9038107413451845d82ca01e50a00900f504400300a01d6100080010f00104050707000664141c400d004031108080441c00d080119505403003070080c0d40d00800054021f10f450500d0483c08107070302c4c00b03519000c0741080c0c640401d1003c0c0c410804009000c01c668030010300507490315201c413a0141c5210f250144d8082c4a14125020b400c402411102c140712044000c80c0460301d0610503070200400f0019203135640e440903d80100360a0740c00c020440294601200880b42c000940201000c8200050310840a0b50500712504094600c0c01c6a40340d1501c001c00070b011607a101d1b8000d4a01c41c4841e400325000c0b501e844880c2c2518001044240030464204020a201e01d0460000c4010001234901e401e0352112100d1109 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532767562 1250 532766312 532766329
    0x11030a02120a0b0109060b090d02040b0301020d0e010b06360303071a0711070b0c160308091c020a14130501030b1008071a0a1806020331050609 63
    0x29400000c0501480503800001842c0030002e8803031503540d00c181c0e980300e1582c02111500d01804d46159401c10558509282420b0b803001c42600007400040e2440c8080002400c981c012005484010f466100c0b24880032021301c62291808801e40350035141044075501564901c400e0200603200c2d031400e00078003c06401c0c40142082890020301180c0c0c1c3d500c4503080481d04144204e14200062104d0400100750354860b42107548400303403110003048124100f410b08806a00280b04102d510722401511014440c642054000114041d03000745944200380020301401c82c0c84903030182240e005102c00500141c0340d00708000215031510514221000c075003000280481c1544100c444418204030002c4103128070081c802d80220340302ca40251401c0e640701d6005841d44880d03c02c80701400400b44440311050313011402000003280600e8070b0300c040a00200d00b000c042d01150010401030f8004200030400c08070010340c50340c000705003007200300f11980140701e4101095850b002d49070250801144d20071135521641c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532768812 1250 532767562 532767583
    0x18020c12040b19170105091509130203070f06090b030a090f060506041802060d0e01020f040303050703080105182a04270c1209020310060603021201140105071103 71
    0x1103440e0350301d076600d1403140c003600001c28548085819a40b000c9485020b41310084490280f425840c0c9568601410401500c00080c407114001c004540703003650035074030612010300c651100c82c1c607940c0c6460680140b500e04003082d00103409841c01490305101d82c40d0002d00107002c442c2460040741e41e135541c0c100c2800107130005d050010550f0001d14040c2041116680040d446800c0540b820012154440b8a1016558007038002940080b0204511210078000303421040c0141c1c0740354000361030845410302d074030040c1d03019030b2050b00007071408900c07482015448000c0745c0c018482140d061050107a5008140b9861501801000c4001c1030101ca66200f09089010b43c80b00c500ca00c501551100e9550b014044407841c524551071081c003100740f0b1300e82000384c00c3c410035403040301175518204001c82d0905514002d14400700c050740c1c03511500180324443d807040c2c015440980500c0c0d40268444144241c2d01c080c42e041030300081441c0321600010080781e40d201003030350703110340d0081600b011f095142030100e03050803004c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532770062 1250 532768812 532768843
    0x21623030a2c100507110402030613151d1e0c0901031a041b020f0105040b040209090a02090114010201150e0c0d180606080d0201180212010f0e010608010b0a18020c 72
    0xf1001030901c1d80010141a41c0b901408491071507080c80000c11040344001c40d95203074480543c4009040c44062540005800c1e544444420031058403150000d502000005510b60740c04240800c2069020003050411015910f1240c440c2071800d21500007141d034002c0e00c2c0d90604042da1040208046540341e075a030001500050403c1000d040c2c44044620b000b02e00c614204050321070410071800b0b1081c14442c2c0340c03080780c111000c410580c94507420041c024074054151906440b44200324070140e5a18154940201620a8020000d100500c00a82503039620002070044a201e09820000011840422940410000380c020750710304c0c42d40f580e000200107003050461261080242c20341000307100e6000d80107440c0c841c8119400044000030490030f861609050842c41080101c0b510010705101c0325000b5000203c1c0c00206003d0112100d20085664940e0030a410340e45078107040100c181d0070303c031b903184040c2c05842d4401a9810715646112502d00d21480052040d400520440300040500440040d289541c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532771312 1250 532770062 532770079
    0x301062619140c2a060f0709060203030415020901140c030a32090d0b0403020109031101020738070503010e010f03050c01080406021623030a2c 63
    0x4181007880c4091120300951185040c188a4401c81c094800703901c21510060710340d240c40d0620044101c2200f0303481da2100c4ca00600c0800803240c89040c40603520695110048410300d1801060040103c40300ea8001c1301990400c0090002140820901c0130300d100841e4009a514000706c0300485103a14041d4003002d0640c0086045c083e10301010000b800706006555483c00640500700240b140c83c010b00b4081c400c64464801c3e10f0140740d14080c064580a01b0040a940181c9440e403a0406414800c07581180140d659402c000b00301500000707030900c2420104001c40c1001800d6a500e0324500501c48c450402e07021405085031500725803454205d21107085484030031682020200500550400e004000c0078803500b500200d403040e07480c0d070070404417a0090b0007003503880d00d03400040d1007186004d007058401503000c00901454100c3c04200c0702c04c16116424500f0b940c140d4203074041500800318444d84054008001d001c01b5154440d0600503540781d950300c40366143c03091601d00e50b41681c10500790364100311403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532772562 1250 532771312 532771321
    0x9080d02010f0c050a02030403240504111305090d3507030b030307030e06070309170c01020c060304110108071e09030201021005160e030a06090506240603010626 71
    0x40d040b100c20240d141005001011501c8000d40d8035000d860495401a81305000800c0401d2050401403c00c1c801d00c02c0d4011034034120101e8109880e000c440907120207020000c0240c4508012110044201008404000f5401c000d10720545501456000d502001400850801c05260103c9c1c25202c42101031098100b9008220004541c05012100100440c0c54420000801c1c1404821a2243c9a1580ea29031b060f007036903820003c140d0890402a0100441c00402042c90200b05030580c452040000080c90b0f40200315000900d4000700090b440d010301014000e0000180841c20072400005090070008150790f1407030002c0740c000b03016244101070700c0038694120844c0c0b50040040d10580e4000ea003960241c0c07004a081c002911000c1d100b03600c280100140820b6100d2050404100c4010001c003600e1194207142c82d080140c1d00344201c20368842c1c0050090005101c441c4c042d0709007403c60000c8603000040020300141d0745000510903e020300c80c40c0b00b0340090102c868074800b2415030030710390300074460b082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532773812 1250 532772562 532772567
    0xd020a030b0d0c08070b0304150e0a06060801020306030c180402011b0804060305010f0503030a0f05091908031b060c0403080d091a0a0e0c0609060901030905100e160509130309080d 79
    0xf20303c0303407046038040c02070041014000207040b40d210b03036004520744111130840380860300140007002403810240546041900018040d0003424001c018403000942c0728109001010300f0000c540c907440c0e10034010712071560440c3d2510182a6809030b02420128007904082c401514008140342c401032000c400000c0120391240c040d400241038a40f0305d042071131596215000e05940b0700c035500482c00807805d80184118454891001000c00720009030a00c01c43c200707119140e45c0c401145070004411a0008140085060b804005525140702c2001c01000c0c28140300a8907a0184510702010b03056801c0022000140000e503080303510003941c00320804009080d04000200412026607508116a0402000070806500018070200b1110700400c0c242c90003104400b0007146620681c0711905240e01c038503107000855003e00c0020b07046522075034081180907070303608007506042d40c0c0c450001c1c180c07003402c0d000d00c8940c81c0c5610059108100c54601d03412005e49040a950b00e0301c15a100040d1441890380310001d150f07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532775062 1250 532773812 532773833
    0x8120109060b0f03060d05030c010e0f0d090b040e0408070f030c0215091e0d170c1204210606051201090c1202010804030804030e10050405010e0f060d020a030b0d 71
    0x11888681044159258001d0700b44074418482c064003102e1090001c0388241c0f9002c4143e080c0c4071b1180c03085a143c0180c91a9050030349111943c4101d1302c0d00084c001c0700c0d004005001c56020a11a464210f030500e0415405203058015400340f03102044201c0d0000b4104a24442111221900509612000881883e00500c4000d00341c504038002d04d10200940c400c0b100c000d081d00c000707400c0107101c0841219203003d8002141c10301208030303a1281c20811404041401110341b0001d070229500c0b207555803901c0030f240303614014400150107661841040f04001006040050240c1c404900002a690b444c007401e000380641100d802080e4005d250155a035089041544940308081c461247c4124180c0e44140c507880390068880d0113804500400000350000f8440c01031580e010340b00303040000d001c00c1a076010840204d41d81c0084004250001780c2800b40d5030300305405102100e02102c64281c2c407001c5101044c00780c040c0300e0719405126004280104410300075040f88a00703510261001a6001c03080c1003441244 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532776312 1250 532775062 532775069
    0x307060209100801180f020708030f040203190302070909020d21140c0c010f0215070f12150b1b0111130b0c1f0b09090a1502160b0c07081201 62
    0x1900e22480e02c9600c18080c91216041350071340d40000c10000c40041d081005000040d4007090155420403000e40025841400b035401039a0300094440d10b440c281c1305041c40c081100700700c02440c0034801c1d00703200003c0c0e0005554065034140718000c9004052032003c1000c810407594000e00c2084d480360003c006800c102612482031921380d031f403c4d03803044601e901460544101c3d65000c0f42900000c4a2440c2d55004080b00700411245104541050081c0c01c0c2e0040c0c800020f84884d4002413414006110b1154003046c0442c5110000400304440d0700031030508100b00180d0301c00d110395803c02103060350080c071030784141100b46552100240548644941d210300107500c13800100e0803c20b40d800002c02c0d40a0700105031a07c04c00281e004201c503000d01c00e240340507100c203000d081e41c01c03d442d0348070601140c680c00d403041d00882007040244418030051404401f000702402c4004040b5205104107460440400d10760390705560080d040d10700c582c0b100b400c2251070f8800c5080151200d00d00050b00d1159914203184035048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532777562 1250 532776312 532776319
    0x2010c1a070912080d05041e06020403062327120702310b0411160303050f07020d0c080c01150305010b0d17090406180b010e0a0f180e0307060209 64
    0x100c54030f5904403a020720300c46202410721803091240c80a64807a0b0b44c0059085406415241c0c1420400ca000c04d0400c0300d440350850f15140c002c00d0810812401e406a0206204c80a6100c1440341c1a00708803e58188020096500c00106120080c0783e43c1100d514480f404c543c903815200c07001d64044044c1d210340d000c010128017908117624010f00e480f42c01036007040018006148894a8500f030910000901810700c00254016a66061600c01086000080c8440f00043c080f5036248116814080c0c01c80d02d0090020587c0d001d80c404100b0160380c04070b012520320400303080412b031045460030701c1c00d020302803e9406900c5603e4050f4080c024502c0044c0c50303003280d104000900c000c401c20f100f84107001901d18401001489007040d1480102c2005019040750a0302510024039076070b070703408804882c1c000142d0f8519025501c079242000d651307100034400034505082c0c850009071403a100c021440923845104e0b154000c0c035409034120983c4041d400c050307006480002200d49440150500c00020361140004510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532778812 1250 532777562 532777577
    0xf050102060604090302150a0b1f030b090708010501050703030204082517070501030e030904051f06020334120207090e210307050417060105010f020a0507090902010c1a07 75
    0x42c0e900d098041d04900302d50541c0035000310002c03140c2034180700d030020308480e80301c40d1505820b260703d4413107040c035504800712504a9141208494005002c031245009964069013a1404225070769400a074134904484003803070202c1d614400d6040480c002d0040b904410320a00817102c0603045901036071601c1452920f2202c80d40c0405945107110190070a0806000b8910b4000f04010005580241d1110000500c500c042d2413600c680100001c0444134205c1d05200404602c07084105040040c0c81541c0107880d06000541c076040ba2030098104012110711400420404c0c1003c2602c2c1640402c1d240e0f5540e0761004046414a154800181d1528003501407034011516000c03034001f03540400034032409030a40ca03064604403020385011702c1950303601c020700250500008100000e10f1560344510b56102809480c0548200e50500d0001032061408548200455000c0b060728030120350082003140880d4003400740069074807514401a60307030000311100544031030103103c0003d6070b410f82e1445080c400d0605076180b03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532780062 1250 532778812 532778821
    0x80601020f060f071103190216050a0306020c0a17090f18070c050c0a0b09030f060103020a180b04050a0e010e0d0c080f220305210d0f150f05010206 65
    0x280e46104000d041182030b8400d1021400350b40401c0d440c0780d08602e40b4540b131000b50222104442c80e580c42030303004078000128a5400c00e00300b541400740c42075040c2ca50402100b054504400205c481e5800c2c0405411203600061003440041d04000c2c405400794482c04203010306d401ca011300c00c00d68002445050182e2541122058980f80070410089400302a1030980d19984602c6021500540350a0007200c2a1107a2141c0c01c2c1c2581c0c0e8005460000c12000c520580e440f06600306050414032207904a40c1680d000300014030050742c4401840c401d0707071400805002084bc500102ca005000344211a5400c54074003c18001c0c0252203400c400b2850354105c1c0244841c41c2d012141ea40d448520244110019200d1506480003508105c02442c0760014000041d007081924501c0400f041d16048584281d5071020500700108071003800051304081c1200b61030428440c2c1c658042c0070a1040340410050180d59101c13404000a059124140c800b2040400724030054680b03032096034130503940c000c00340507110f40030000c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532781312 1250 532780062 532780067
    0x19060806061303110a030b0129040b07030f030204050a090e1c0f0309060e120406080903030601050f070302031b01050105180c0d0506131401061b0506073c080601 71
    0x4800d9911039050029040e491030302c070b51300d022207200ca000f50f1050302d40700300001050010654902034620003003448400c0c81c015041310148070140b045103408500600041002118450039034581e641c2509100e0158080e002d0b0440013032143d9001107900110700740c00801c50403a280d01070990a4940700072030300111017040580c152404c068084a00181c2030300c0340d060000b80700b0303044030300210310641700802c14555440030541044413020007000d00f46e0001c0b6041241543c801c64540c0c000c55190095880d60604400081803440303806003100304040009400010144200200e408200081c5a185106031200740e00c540070307201c2845240d20410040100d0f01e1030090300e070000ca01038030355041410f260501c8060b00101a00700181500d03480003603444001540c04550196000c08151650061082d60401c00f0160000320321101c0e0100c001c41805040300058000198103400000350704100072180030040340b03840030180900034048100c910241028012881c86151042c010083d01c0b90b802965400004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532782562 1250 532781312 532781317
    0x19020a0209010501030e19052d0a020103022b1401080102040608011403030909090604030f0c020121110c0f0c0607020306040305030604022a0606150a0503060607021906080606 77
    0xe58400da030500104482d6001c0d41c08611a07080c034000b40c50401800b4404280342482c0380c40142d0b1207400c44030304a007501c08100c2008883e00700001000c6d42204101d03c10741c1d92214110740c000e0505a000541a0000001140e03c0001c54948249569480311804000002d007804424031480220988000f15540c43c042c02600e090382d1660740c030408182e00e00000413842e100e0b003c000503014041080032000544620071464400d00c809801001141490b107001800a0503d4640343c080081c840007260042c1c1c1d02041034030502c401a40850711141a0381401303001003800c1c104006250200054214040001240595048104006641000003010140b0525109251001b90306030480000100041e00a4000d150002030150006082c01004003120400c1038801c280008035028042c814503056400704029584030130151061282c04050116031413407405159080701c02c1c020040b000510030f0312544140c41c01c07183c00030b09420f0045425014400000624000c1c040000c8402e00002c043e41001c004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532783812 1250 532782562 532782583
    0x50a0216020402090d020409030507260d0b030708060702012301030c0510170a0f0c1404290f040614040f15030b180a0f060302030c0d140f031902 64
    0x800a90945007942008002d600c8458800d0f44800b04464100144c0c03a5442202c11444c860745440c0d50754106d03404d00017160540402100c84000350030082d960302c00c5040d01911301d4101010004240401010002810140142c02440c2e0300d12a92007007000350341d81500b050100758030110120103014544c0103400140142400041c1603a00441410025410002c0c419034000d0380d94641800325540306c8d4407005180f40706448880307000c1d40300e1513400c1c101c9105110729445120a0304101d1180185001004000d001e5441016180750014031580c600c68680600c0700517011b0740c110400e50303d140e0340320f100b80700742c115010f9640080c800d00780c015403500c00d4604907002d465108042c65503c6242105100a0002180e503150425840d00b265207025103130b26608002060240ca089100c9140030548441117848915803480d196041450070170241c0c5012070880742808090320064486643c6003090035400b940c20000801602c1921040510560f011000e000c038a18028070903140e0901c0c50b03074102d90f07d03c1d880d03c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532785062 1250 532783812 532783837
    0x30406140415240e180303040302010b090a050f0103060509010e010f0e0c0604060507080901110114010302030d09050a050402091521014e0302070f2c071e02030d050a02 74
    0x10414030a203128501515400900766005580c0c2c529030317480450071030b0016541140980e45415152115151035000e03554400140402080300385000c0c0c004040c80141032001034581d5503680d01007a00d00e2001e4200906800001000740300b014048a8008010b00c41040c20342d406003e0344a01c54106e03c0c186045404403440d40d038541c4d007040d0441d02c134410706911900c20745d030520000d91041c0034a44400c1c0201154140c9407120080598914018141060560740381d15003008040d6905100903558103803044141c232400e95005841d50a144003040c6243c450b401a080d9810010603441d0a040180107202511085444590042c1e607a0302075038007101c04200360702c0711aa6104581d201d2004003410441c5041c410900100c4061134030500c0405080d02d144030261700507004900e00340301807440b49828030001d0581d50081c052110034606180300c00c81a5041e40c01070b4103224008140d0141c495400c0d68500c00c1521940c0b03102c91003483c0017940d25409540440b04440c140000603607594507901c203540480060f013 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532786312 1250 532785062 532785131
    0xa050304021323151005130e07050a03050a33051c0f1703100e0c04030506040201050a090806180d08010303021902062208072405030406140415 63
    0xa4030f000a820300041c0031001c45024021401e00d241d84e68210a4071100090302c4540c1e440900c8180451100d41c01c0c0c0080d207840b500c46084c00f43e01c580c017204491807040c480c580024036886c0c0600700e50140c0f4003403500d03a181c44188008034100d0131703d640c0c0018546a041d83e6141410b0754030002c4c04414a0107810b0b0702e200c1000203080401082445480603540d9102d02d102c40ba00c100140e900030100c1c1c100380d0f10b00d411a01c078030409100c1e000b400c80303129400808221100341800d24550f1182d5503140e0061009040003c046a203020481c010070034900506401010742e416032900407402c0d0941d00380000300707018512400d17501440c814060804203051705d170568003600c054004e00708420b00c100800d440498100204218030006506a105080d071311411504540d545189070091040c0b42030590f8120f00e200004940d00c1e43e441c100400880c541d40d08450a02d07503229a600e0130264010103c5015903094a200301003000104840080c1080b609445000c0401001c0404010600100c400243c00501c00e141e2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532787562 1250 532786312 532786361
    0x3053c0702030a0516080c0306010b032e0305100f090f080306010c29010611070e0406021b06010513090b130203070f0e060102100b010c030f020f030a0503040213 71
    0x104004006050014080302c41c07189960b0b4840c4c5c9043c4e403840d1078150060325a4801c0c4070b544400d001c03284c01070408600070210355040034aa50298400544a0b4103000180c0c0b4000e80c0c01c92500d6800000d50701d202c0e404104250b44c900b001078036420383e450092001464008a4059070a2503c241180190411035003418460103070b407183e14039403014024605002c00b148141001403804030818090420078968040c4540b02e07468440c1491606810020a01c242c8240310a8407801c00a10b410480c5c0c91030500c15440c0d2a94104071000344500300f0061421101411400c01d9800c0003d04581200c1040d60048a00c040070401082201c92000009050201c0200400e2901040b681c800e0f920a00003800c1d940c01e6682c42190550100e02c40c0d005640082c290000c000440d0b07018490307524130100f00c0100340f000c1e06c40390300000c001c8001041e0003404d200045541e40c078a54400c201d00080316038841d0880780e80d9407020230050080d400803542240b0500a11003030034078048242c010300c01c1d441869900201380081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532788812 1250 532787562 532787677
    0x1d0103032d08070912050a0b07020c0112051b03012303120a08061201090b01090c05071707031202040b0417030702030a0f0f060911010206090d0e1509030a0305 70
    0x10b01809100c20026040004210b41001c10f01608000748204000d2065610302c0c0b8141c5401940240028150b40100d4203154080c1d82140a9030310841c040c20001072241d407103d20015150010ba9408900124048004100240507000203242c4421080781c1100c501500010540d40d207070030020401c140e01092141120403030241c420705421030360082512032080a07444055003100c41300c603001d2711522a00c01c010400b4044a00c596201c460751854020700c1c008082e200e1135500d4111100c00740d025040004c0002c24036205140d14442c40080100565645a4811364098075403c5805081044140200351581a210001c01c5031341c1c150340500035100b690159203907079000005002023600d05031206520785000940c2e921400d110a40305202d40c8840c17143c100d00091800f1001844041a0351268084510094000410041e032010407240c0c26a44865000822814040c40c05506c1d014443c1c000e101d0304042c1c1280240003075070681e07800f598400c3e0304420a6161030140714481c2e52903444c0301c109040e8500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532790062 1250 532788812 532788827
    0x40b0703090914280b030d02030a090909080324030f0f0c0103090507090905160602100b18220215041a030f040f06140f0109060503010b180601091d0103032d 69
    0x1c50604d0000da210380e001d011a003040d0389406900010380000a0f502d00c6c0076040084107020b01992031041000d1410307662090814030019110000c041061401050003030603950118560340c0010707007511901d1000c03100a590710849410010000d000d02480700341254424812040c0c92a00702c0d00030400e662803c040600105140304090741c08d80280c07004502d000c900c5080c194010006903004000846d0240c450000311001004010310540b6400410b8030300100f010305c0700e50013458031031541c485400a0807a134411000d03403400007500100386d80a05040d400e4484045d2045072400e400c0300140d00d020415095143c071044502c143c0b500030310f03c0480d0106158415580c185481000e000942c004545c80d40441c0701d00c122210513a00340404010b01c1300f55114018800204410303402401020428400aa5010220074a041131705480c0000148607a2045503440c0060150b80c014600354259504240c0d1022003d00042d80884c03c411a445100b44112034040982440c80c00445c03440000e0840450b11003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532791312 1250 532790062 532790131
    0xf0d0b010531090c020604061d0a24020306010903110a030c140f0a0602150604020706050708150109060c03050a12021b060105060906030417040b0703090914 69
    0x20405212298030041403003000000d1101d169240d58104200180003102c00e106500008811410b00655902d429000108182c01c150300100c0400d41509205881d4040d00007071a0b103c400b480b481c0307a84004c0c0004c407040c1000400070025400c031404682d401e104280d2005541090000b18041810000b241d1001003000c041c0d41c0090800e06444d940703454a020a407500d801001210130042d21041d424030b40b8070f4001002d584296080c1880d00d1030705001039100e0701c01c00c10000311145071100044007983e807039040350100c1c0d0703000c4010003940c00d0101c0020045142116840b2a081c2e0002c0340388100d43c09990160110f4084d6039546802c056207580456994114610b1001840983c460400e180321550020700501c0108051080804226480b1a0314004060f40014042e200820103800355480740d4040b6603000e604885503580000d08610440c2c1d191040340d01c03c1c5e140c550041204020198070001c03c1003203c490280a04c04807160018070740045d402039440800c4940041d4001c848030801c260340042c01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532792562 1250 532791312 532791317
    0xe10050306060d0302010b032a03061b070507080111040501140405090c0705011416031103100302060c070803040b0301090b0913120e031501170304030c060309020607080d0f050603030f0d0b01 84
    0x2d407e20100800d00d01048015600409100e03021450710300504070840d9500750500704c0003403c107424219982c01c032881e0400070491021400048907024840100441c000400104c80200075040101ea42c000080d00700d4024140041d122484a11040201009803800d8580c02001d100750340e19040b40c48000d03070b888240d00312105d540b2010882c0c50154070010b4075105040040c4101d54054108100078212210740020046d2000140180a0356000824070740c4c007900e41c180c90031076503840e80d0035200b4a0b29a03254080340c484c0c032000a000c20389881000183d0b040360710b82c810520480c80c4100c00c000321003004440c81841d00b080902a500480c2d60080c007038a20401c5030800e1074917014041c0219013807030000680c96031b010203810010400000740c0c82d1008452145103024605060550351050b000c40b0251052070201503c2d88002e509550301e000480f480c05a100290b2076880c003000070504084c1200c011a01c0c0f000d850540014003500f400310446907001102d0740c016240c44040c80115005002418001d0304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532793812 1250 532792562 532792571
    0x30513050610090c0513030b1807060302130f0b0d1a041406030c0a06140307050f180f010f0c06150302180f06030d0503070f020c15040e10050306060d030201 69
    0x20034018007a00d80100031024954154074108a5140705681400c1e010104202c802c0200110328000040c034041607070b91081d500d007456143c1c045024550680385030408694050440c0000e000da03090b41c0200180308420060103040c0759908448440c840640c8241920918204001c8000380030940c490b0a82c203043c0b560800c0d400ca402c1c0e022400b01d80c3c0041340d40c16003600d8241800b055150411000c10048011a4150032050401e880200009400c00ca41c407182c1c1000f00c0464a03180c0510140e590790542d040810342c90b1890f0482d1240b5004013012031501560f486801840c0070352040b80c0c075010ba0310f10750f203900d42000c01c1a6150002070181086100d9800a0039001100598592100c02110300c07001d0020341d21414180d0b01c80340b0551000d81080d21940c46401d403007000c02e82103804d0341e5202d149410610005480c2c1e0009a0900c000c0e6000c2c981c0c00039800001075400007071480508190f070009840b02800d55603003820f0000c220480c0c001d90354142c2c8802d000694a140201c040b9810520030701c00440d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532795062 1250 532793812 532793851
    0x103021e040603020403035712030c0207080304060c140d03090b31020f09090609070909080d2003040807021206061e010e151201050604030b01060305 66
    0x30381c1050300031200103070f00080d00300f0034181c0c07180e034400c540104140504a6034090700500c105100940304881c501104074000064200e441ca000e818000c040d03c04104448043c514103c000910482c2d2410f001c685400d5200c40010700c006460001d50300f941008514041c2000c009480300c2c6d84c0745804456a00c0052150a0340010901640c0c800c0007150701c0108606403a440c1c941c400600c001c001c0c0b40310140c00f9030004403240e8070944407140c0482d0500d0702010280d0310300120b00038003604080141c201c5a04000e000140800061480c0b00e0ba9045094a0540d0380f107072002c0050303031381c20301005c3e22480b010312041da406103441d44144900c3e214506800c141588110390499540c00845060398960408141c11055050004042080d15465805403a0905c1c0032400035203800c0482c07500207008a4444824081e5034001d00581400c10701c010b00c0c00c80c1c2814003941e00743d07183d0312041e0002c408038030940002078141445026901070f03a41c0042c00c11503680c00c00d80200c006140051204220a1114800c803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532796312 1250 532795062 532795117
    0x20a080105220f150509040b0a1806180201020f070f030212190501020a0f0e210102040b070b012108031b07081603030b1207090b031005070801030c150905010302 71
    0x181501c15060f0000c207242c2080c40c0004200e220320b5010a000702d2520080100042200c10f0b00d652049610714002a0084220300561211042290042c0303081d1605400c400080034400d280b903041803003642152404c0040c00d440c1a1a007140d446801c0d1400b624800610041c5881018100120780d0b41080383c9150303200a49004651000d0441501c9907540010100c56050f48801741801d0040f06040400186825001240c900c80c14111010351103600102c103810150070070740440f0001c14000c2c00080c1c03510100c0c00d190301c03540c07000e00c41c000c1e0b0307440450004c910941007001c81454907a00032210b40d0a40e0390b281000400552880441c40c4100c10401001000440d250301600901480030000c1909244519000d401c85244d501e005200300c1d0148090002802c0004008003951044c50300850109800302c0440d00d00030340360008110040c105410812200d0307000c100e55040380d0141c0a482001e2b943d42000352072901c40701002400061140c0d000740203a50194009284015404403011400072008040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532797562 1250 532796312 532796321
    0x250f1715070504030b07090b0a0513091d100932070e04060e0a081819030b0603120708030109050910141617042306090109021003020a08010522 63
    0x1d00080b8401060520601400081d01c45d803221050401c942c82d20b0420094202c41d0045a95890406c180040c43c407101420035034150b40104100d5030f003880014445031a6044401501c030007020144101030385205a40c450b4021a10b80c0781d00f00c0c3e1030520401c190316203524560503600c2d4040032031101c92001740700c5041c200807490040c82c0c00440e000c0d00d41003a1038144181d0300c89142d1180180d0040742501c01054090007114041c902d0000810300b11107002000c60401d0070f007050300000241c0e1010002082c45480d000c424440d59040b0103444407007220325100c01441c081c011002d80a10010300061080c403190790f02085e0003801e450211411012085070041c180c81048812107060602035080c04440001c3c1007803c608000745041031000341310f20405013644a500140050049822001090b05040074107034585040c000c072a00b034421030714060101c58060b10074900104c1c00386080748141c0802900c81d100b0744002c00629542c07105240d02c2d2408028101c5010004181d030b0302e6a80503081c041d00e000c0d214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532798812 1250 532797562 532797571
    0x20115030638040c170610030e070b0c061003080d0902210a0209010b040e150a1a0c060f010503030304060e010b040c030b0a061707050a02160602250f1715 68
    0x60b500c40e01c50311803c2c0802d03110005101d40601c0040742c1c10451410b040451035a020708160742508440141900c120042c3c61440d02243e00d5004c0c5407000b06501400c44024042c014102048440304c3d150b0090341030401c0c0c010300c030181406200740083c03030a49540d60000468680010300800c220140d00403d001c3c9000e06040d4643d0b10303031040118900b18180218442c0c01000c18154140c1400c0c6000b503101d0000341c0052441c4114001c00015010340d0b07546aa0031005860300011030941c020101c0705541c110307840100c01020611500c8005408034a0803c0c140e4103a1b10060069411512079544803800342c0b080340b2482902d5500d0f180110003d440d80d208a082c00341240d600070400905079014004d0303041e060740117002046803148054002c034140c164403a030050400d00e0030301d58508041004034101049000340c142501c0e224000060b00c15800142510070318403407813001240107000b40416521420601c200b200001c8201c034104990f000d0140b46101f8600303400290f8116004000824010300c40885 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532800062 1250 532798812 532798901
    0xc0605010e04110901230a0b0a0f09050d11010804020d02151804020306101b0c060905030c121b0609060406030615020102070b0f13050d050a020d0201150306 69
    0x8208014030010380f01400f00c00341c098844401a50403c07110300107411040019140f4000d010040100d0b40c1c507188000802420130340103482c1c6400c04c0340300042c14045114028030010703126560200d82c0740b406055030216186d1020110800e10004401034903c45c03001442a640004405401c1c400358856854501034528503000090381d400310340c4003e00030038031140d00703181c0035510510400002d034681034000c00040f1541e0411409181c246400592004500364000340180d1242800160043d0031810f50030035258220b09840d2021182014450781121006503e0b0f1607a120f8404a01d80c1102d40058180e80100601041e29001d12032011541c680d006902c5100002d542d03520070000b500b40c03024880c00301e6560740300079483c0c0202e07901c50004159019001e0710045000502003182d036080c4860103909194841c0940346007000880b4003801035000b084000c0b0140c01025040c84007284103100d5407a0440030041c0840e940b5046448003401800c80d940c030b2000e0038004203c0d407100000780d800a41c01560590 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532801312 1250 532800062 532800089
    0x7261605033304030f12151703070f030302090f060310030605060604081606200606012010140903071a0a0e030c0a200319031b08030103200d11010c060501 68
    0xf0000a044004541c03098140c580b92003100c500031f08502c0300040072150640e07034540302a0415891181580700d903c000420044c1980e001408154068001d052044401c440003007140d0069001e2003842d03c41121441c64030703108901c1c01c1c0300044c0d00d030340600d421a0f000b600031401e054480300001d1511b11184031583d600030302d0080820075139621860b101404040703a960080c41c0c100c3c00e03540ca0343d40c05003e0100c07410702906c0740652210032031048401b143c918445e011103a9502414074140010043c2215a9900f01c0d0194009011072000008075420282d00807990380b80c15044488001000324043c0503d00250f84079010b40250200810180204014580c050030044401c2c0c0381011000141601c51510081d804000000d50355010808041061140d840c040c0b400c072080c98100c0d040ca000d00b843d5003145400c1a802c4081c880000c0140d41664072880b0080e2121480c0c0d0200d52501900001d981d6000303003124610000134506800f014600e241c181403080c628807581ea0b0341010381d80241c0205100e40da10f03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532802562 1250 532801312 532801337
    0x1c030515010207060507030509040f232d180123010f050901090902011103041203030b032121070503040302010b120712050726160503330403 62
    0x40c0d000c055035031400740010980030740ba100000c0d100b40140303400501403000100750016030340c6641e0841c6089500074007040101515000004c0f0030441860300c5004200c040000180b00940091894103501d0b00c8e4109100140303645007114000001c004001050001419101411522013401100d0619031029a801352000c01c811070b522508505a200c02c0c2c10681c4107000b0002c2e80c036042d00031415a231803548049149240d500068800034100d0000316801d1100050018100c21843d101d1008540700303035000c0c000401c0541c100340e80c0704142c001c80d210020340e107008221310602c2c010040480030401180311403140480380d40100081012141c01d000704000000b0401010b50a01c0395003c540011509500058103424010b650b4200e58007035a80207880f0f100c40b900c20b00004000c1503009110542441a20100500c40c0c0c1301001483c07242c007000d600c2407801803106a50000201c400782d60300a03005290010004003004100c01e8000e0f0504050408141ca880c0881a0360742002d1040b400394403002060b940c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532803812 1250 532802562 532802581
    0x409030c02031c1706012c0310061a09100c1506060f0908011a130b13060306050903070f0b13050d0207170c01050708090f090a0605030d051c0c021c0305 67
    0x100241d04e068192596003005400da810040c454400164031144052002c0d18000344108065a10042645407050708601000d024850701b080c01682c048180c0691000481c6000d00618080d80d940642e0000c001e05214451a101e441c842e003116005054042d5920100589a0100e0703501e5084500081c0d0080d011111043d00015204014191440204030700150b898140c0402c084500d40c90307200746600c0281b4013030b40c800c54105442403c0c0041c8030340c130300c035101038a032030002c100c6031100301c0342c644c10400007a6046002005607060704d81c100c0c40440007042c059a03410014038004101800d000e4410302408082181006004401c20f046d8000b80300c0b09045c440d000c005984100c002c50b80e103600480700d60000e640d120050382c40c641d50011100303450b05080b200041081c2c3e02c2d0511590010312502c200401144150410011a00240c0942e075900140101c100c4e403920510109618118802c4005403000c07681d036121500040b0288195031100061300f8100c14034020b080700c03000010b901ca8062115140307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532805062 1250 532803812 532803827
    0x30105090c0f07171c0b190303051e04090507020f12041202060c0a050f0717030f09010e0406030203061f0e1005060a120c0504170a08090409030c02031c 67
    0x2000d800024140781001808425600c55040010032000c4c0e40320064092801e08010b0b07072090fa0400d4448526100e0350107030380c0e004000c52028140303e0490442d5141c1c04500558644041d80c1c0c040c3c0e01d50380351040780c1403003c0d810350300c00752128100441004009001c034030920845000b02d0481c1e0160000315101200540761085041c0501ca86120401040024030100c0b600700110540c15034015444601d08003102d820301c04000c4014041e07008842450b911741d0000708480094072060310070182200342000b40c0c1e030354074004c4c0341000002041c10841d43c5a03075030042c21140c2403424002c0003c2001c589940c00700c0d04010080c0c6908020418040410004030711074043c3e0700181c04240400111450300c81d200300f65078079452160038050000020307841d490324031030412008400350b0020188100c0c944c2400c010015403151003980402c801d629440c1d202d400010503419500c070f40022005003400d0082c801c01008080002084080c400401074200050714244102103401c00d0012508041c03009403a005000752 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532806312 1250 532805062 532805071
    0x50a030c080d080903180607020904110108010b040819050c0a080c5d0303010f080115030201030c020c031e0618060a270605071101060320061e03010509 67
    0x8503c52040141c074010000540d082d4801c2c000c1d030042d42d0040d0101045a40c484c619002c0e401046d440100320512841c0d4ad0380058100c020b81e907115050f030380d07082c0d840024081c0d4003807032880d50845119600c02860256041310264003800654140c220140c0004942030080e9200c8055600440200011442d021600c1092103004034405d40900a00d000c14006911200703290814802801010b0707108200071034a011412400428504464000e5071203560780d0740c2003449070102c140240c010100b2020418003840f001150000c1d00f1400c00b41c00c550040d4054031150707078035604601c1340f1038187d08684c0d410044e4440f142c10102c06808940741502505003004401030078042c88050b190144110010001892507020800d1040080d000280803052181455003000d5082d2100c1c02030f403c2028804a54429030055a960700ca14154144a0108500703a503090310014048142c641e8103a65100c26460a111000034010034a40c685041586504c1071043d502c01c189014650200040c800c81c108079842e642c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532807562 1250 532806312 532806317
    0x10603060f0303081605040e01060503062e0e04020c03161202030a05070f060207080316030501240804050705030f03131415210a0c090e0f0c0310050a030c080d 70
    0x242c2183c80290110350301402444c2a62002c04120152600c103e00360340c080d010100f1190802d5030750309002080c2da0030585109101d101c80308100c0a03a808103450405544007100da5010050011400503180e10700301001c5603400c00c6d003c02c0500203080e8240000c010007680410740e00c441008d641800103000304604038420a550080003041c1042d0740040c203543c0620342c03126074424a2002d42c50002c000c1e005060006020b18404000c1c09030b1460302c21805078070158156400c2000740c1e62101410043c21100003074104c1c40381c144000c00d001720700c9104519800340c0564111181c4564034001310b07141c1344160220144542000c60812144907400c1e5819000340030103002600403c0c40107000030700001c0001d5070003204550000340884622800300041d03400d4161358104000b5858191052b41c0588002112480080c42d07441000c10045032a0106d43d0044c3c480002c1c59143e40c0d01c65048201c81e0740050300c580500c12888400103060f550f90128140510b214070320a034140780c50052031516100d80940343e0341c207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532808812 1250 532807562 532807589
    0x20c06040e1306060906030b0f1302090726070503040c0e06132706020408070f1a091c15050c0a1706010909020403140d020a0c050d0311100501060306 66
    0x34010703607041000d0300103403402a448814140352030080010819548150012801c00360000b090001e500b00c0180b00301003107143d40140755a4040c8269041c3c9407242c000794000c00076004150010b10070740c82659040c410400a2151201070110040c10107821213101c000a07200000300010032841c0d03040c000040010005030a082e00700400016400080307a070342080f205968441c00b9405100d0019032041401418820148940d43c600f07041d0003a511902903d482841007100015001c3d8007824001c081720340348141c418080f40c1c3d1444040c282e600404a03564400d042401d42d691884c483d07078003000b0083c81009000e00d100e000301c58a0b0240c0e80c0c014071001d6a0340301031001e006500e801101400c0003100d50740c1401c803913684200069881c26610b4006205207403000c9408410080c402c611250b00314482c804550b0310846080303080382c2c1c07081c2d003a8005041540010f001c1089041030004c603440c1c2c900c40d05020300504a0b0305050b5181c0000d503040c0703001054881c801004034641601c074120151075003014070003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532810062 1250 532808812 532808819
    0x108010f0e2404020d080313120c030203030f09010b03030a050702031902130f060f091d0a15020f0d0c120509160308030a060305030c100b010309110f010e03100606020c0604 76
    0x40c002100d079a0020940a01d150003d8115a16031410602e02540a80c900fa240e04002011100465010b18120b803109170f4034280030912401109045d4080790305500651450b69482c0c1d00070101c0310f014002c61044d40d01d606a8030351580e010704c00380c03141d81e40a96541da258003407401010300d040e00701c0384104c541e20045140034000d616484d1048030b1848211b040414202c024504040041443e60b0180b656061251804070740c41626411440e1500e101c09400940c2c0a00309150765110b40f061040213081140c41c00100c0074101d903230380250511107803d550003814804080b0042003070301c140120060014984400855148480e4440e940d0480c1b82040140141030744035071300c0d682c910385a00005c0e081403004030014005032402e4009001840e03204c000e43e03850b88501d58101c4d6540c2d240400a501c02400c15000c91200d5100f4864011140e4021a820541d401c8200c14088001142c4800b24104084140c0340c02881d14108895048082c0e03c1c600001c0381762400030000d061102003950580705410030413041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532811312 1250 532810062 532810093
    0x2031905031c090308061009150504061715190e0c070210030e0c010c02120703080324010509120313080f070b072a03050a03020615010e09010303031e02030108010f0e 73
    0x1719400f403006d0f07807410990707444102e09540305801a48003014001004800124041d400805001101e00d5a114002d48044469402d01245000c6410b005000c41c1c2c0c510b0606185448200c400707188500c0031210030085c0e210942d01e40e00f440112003030303500e82ca4005039203400c60074420301c01440c202c0146420001c00c882e07080456115041a48081d04000680c0c891340155511115000007038a891001c840342e042e601d20b80322010b41c104442c194103902079029112418102032096aa00d038034142d452ba450030051404008180f0380804160101c0d201c1400320f050001c0d4415040320180c00d46c40001d001c61801da124039443c220a0381c01a0342e04880c14400c240000300d00d2150b48085892201c1e80c0344c284500c400e02a4042c00ca55070019246110301da46410130b1603000f051190050070004058034601855100656020088640303480d00021003400410109109138410542d00e4071501d5418002c00f03045503210166002a0490140c59548100025140b040352007800501e0415034043e102c2c0a404041a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532812562 1250 532811312 532811327
    0x12090f1d071115090604060e060702071206060e091507030c08010504050a09120903020316180c05040506070b0f0105040b13020c0c040606031b02060108031602031905031c0903 77
    0x100c00d201c4140790b03400e1100014001440340c0d01c0d01d01071401162030400d01c82a5034070702c15282500d11a150012a02e0a0b18010407064410303025130b002031004515050311000030340ca9040040d43e02030f40c2d5020204603142e0070748cc00c034050380050300284440810030f0442c00d80014090034001c2854a04154dd0114682140c0b080f81181d0741110000307a56501c440808000d40304168009201140c200c010705039058000e0f035020140c0f402a01250a1039143d416079003c41115801007401580d0580f015204003256078212424201e6140b80c45410140d82d9008030b4200d420401c0d085a00c0e0100030200005440c100810500600c01164240a40108140400c901e04515501050101d40008035907005820800070546405000b0b0f03c100469aa1b812000300209428002141c4015100850149041c40051824162036106c0043d5103002d070a11610f0403441c4040c0422a014002c410002c0c200264003021108114010406103941c0c1c14a2420b00c08800c0e004907612541c14a804e0f08000400d034025403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532813812 1250 532812562 532812571
    0x180c0a1205030c062a12161404090603030806030606060a080a0b0a0b040806061504140102100204060225080709050705090901081011040302090705031312090f1d 71
    0x1a061000d1041c1041402c511030048001060b100305010300020103004880f240030a6a5440902c19a18120889005a1003102c8070b40070802002c42c08144c003a142008042a900c0b001e082696500301c1c903100400f0150040c0d40851012075030f0340002c01c14150050581a0302440840180c070307030b91a01ca17000070614015011205c1c2005501800900c60240a0f4014071154000070000d08503203170740340010360040e405070144940030f0040401107041c07410418800400034510740c90f00e0341000e08150300015082c120040700341c114402d08101e184200071920041000e022140c0c00380a4414800c1610500382c3c548241e074405041c1007010400403884040354540c169840803102203081c2d284c8410848160090100540d07000c180348000143c41100003845004800741c180060040751500400d07092140114840690041a280e000901940c800c00c000e5910202c1e1020f01c1c030804c00e01c1c2d198498588207a84042d000320702062002d000c0d28100d4001e401c018001c940c5114041e000ca880c004158210213031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532815062 1250 532813812 532813829
    0x11032205121b030d020703030e03070b060603060406030b0f0a060b1e030a1b0e0319020f04020c0313030c1806030809130605063103030512040501020702100503180c0a 73
    0x510410400c01c0624000c0c00282d0001c2129128640800108020740c01404120702083c40c05005074050680070050300c40c01904004083c195a5510003030080a40c8010130403688603940710400b00015584070205070003203a41c005d0034007651401f441d105003110f07071581064107206c0c0300b400f00c40140f180d43c05a0301c1c00300340009102030716900c03584007550181c100c1107958114100740710111194503a03c40c05581003501300324101c038124125030300202454040d41401079001003050301000e81038200754004058010820048038074041c60710b590403005081580044909103521001005401047c41405514144000080101605d151348880c080c0c4103203d1a98010071440041c0c085084055018400030a400390501e6030b100406410700404100b1007503843c1c12103000319400c1495880a9007100d0540780d042d113583d45880007540001030070f40710040089440d03640070000000140c43e00180a900f9100c0d90305d5282c2c0f81d04010924064100481d044210b582d030048001e8961961441d000d0421650801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532816312 1250 532815062 532815067
    0x70c09060e131511070605090601150c08090628030f1e050402031c110f03040e0106141c06060806030a020a060c020105040801020a02030309101b120b041103220512 72
    0x4404038805042e04e802c100100b24000709028007880a40e8000510030060a802e03034503142c0e250301404a0702e07d90801440e0000701161000000203120310000c00603d4070050501c0e00b840302c860907500306200d6103280c0c1030702100355043c8415000d4141c040c4001e01c0ca1945414007c5802050f81507000d8001508161002038861001c5015520107104d08014014440d03040110000e100c280902101d0100048188502c215450a90825408015602550590040310304980d00e00711044400c045c200f6500c004010040000802100c541e006140c000080710102213252481e1060160070340034001d21080c001d0304611175900050740c450102006882003410100c01032002c07400129954002c035080401c1b82d40c80010401c40441d000070107144180e54079012070b2807688200e03400c8029074130400c1c105105000d0308266000182d004840d40c420003030341c3d220000751101d0444000707401d07220501ca421250f8240002800403052030544190303d0240c40c1503400d4410f01c1c03d90b4a49903280000d071001032414901 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532817562 1250 532816312 532816343
    0x5130e0d0c0c080c0f0f1f0f1106090307030e1c03020c0108070314010e131505060918031207050c06070905090901020f1b0319090806160210091106070c09060e13 71
    0x1f10540c0710515201035010720014218242e0207400c01e2860150302010500c9581c0c0c452038a8000643e9074402d0400001075424400703036030350035a4140b10f011200b55000088070000418803c3e408854100c4c14041d600070010701120500240c20800d0141955040500f064020316059009440303040c112440015039120540e616a00e0034129910510001e01d445401d4400700030200d000e40045010b050120f0f04120103403620342d46030072079401d102841311540d0010300851859401404103503903c0000e600300a40b822001d0300308541484001c41e035520200704001d01c18442e5060242c0c0055000c10b12000031841c040240100e81260300416503811035920040c026003281050078004da80350b07004407151418544100010240c159840d90148404520407840012103420400032140c0682629401070a055881f0356141c03000342072941c0e4180e544640c1081150800d07100e92000b4007200f405003603010082401d0250060544405511190100c04030030180050b60948802100c0d6499002c184010110030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532818812 1250 532817562 532817569
    0x90111030405060c011e02090306010608090705090406050907290904090215030414030a0e01081b1309060e01030302030a1b050a0b1911030105130e0d0c0c080c0f0f 72
    0x50390300101d0b0400f6012460310248601500311002c0301081c0a551941d02c14900c05843c05c078081e02c2c80050f45075000900401c5014010350865810690400170b650729aa01c81010850019041d10110342850381c803804c01100100034403501004d0010b11482210050203858044070480f140009191040400190b00085550302d90184d9003955003d4181c0c030b0b074402052010341094100319020740340c00301c0c180941c21880d103001c070440790700c0c2c041600e841c95030103104001140c90420091900d030400105800040020707803407001409864044c4010300040c0b9082250390820f03140580e00c0040301e03185850052000a8000c4151204400b107490800c0120303d1919a05216014442d4058000e0260301c4000003805444418148604c8410501c2034800c51307400100001c0390034801c20086244414401480186403000120480d46000b10780811800c0b4149551400c22124000100200b508040da0208001c1c1810401000f80316503006008007140210118a4840d800c00400f446203242c150000301a54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532820062 1250 532818812 532818817
    0x30709020a020f1e121e030916030c061106041a0702100908030f0609070215190510050316140f040f09030c021318120c0f0f0c0e06030309011103 64
    0x303c001c1c12110034503804140c805221014900c4207016000b10308000c04030b1203050b0110b6070241c0350421840380d0b4001c120301001c40c603000a04410428000d0306080c03040c2c0241c06d582c800180d03008200d02d01042d071400d203000d0011a05045d0348201500214100000314810300c01001d02a0050000240d165803070041c128204108102403032201d51030a0008428440004061072292000d8a9400c07031036115881000608042280c0714001680004217000350101c8400c070742c0342c00c900c80030321807500801700d0800031041d14800c44104540070900b5034208600c0c6420001c07103070641c1c0c1850300c1008040c2031a991402c00106583c44500900302c0303505400f00c54895501c4800000385824003000500950701d001842d0304038a40c01a880b840303400308403019942261283da10001d0a612400010554999486d1204852442d0103400d11040198a601081e9290368040d0201d205036001d01814011740b44c1020b9000c0c15810000750100b1880c03c0000580300041220080314090810030310113021100e0035407451 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 532821312 1250 532820062 532820083
    0x90a0302062d1006030b0d050a11130c0525231606030903020c120304140d020a03030804030f021204090203040c090609020d0b0f0d14070510050c010b0f030709020a02 73
    0x842d508011100030711900b00d00682d0403075074050204a414004021050742152005405174001802c00d000180030001c1022000d0400b41920080f0910150103000721440849040e000c00e4000844054201d100780c0026000031640d04015400e840b1350320741c0d14480c45480807003611160440f041541042040142515590300c0000321f44216403209001006041344084c00c801522a10718005c0e0700303144c040022400f62104070010742c01e140c80d100e00084070402200c0e1842e046507030311004001680b00c0140d14806075000791030390182d034101460020401274954a1180440d000680c2c100c009a101c0000c9600320383c40180301503100c2d01c850614401c207808551001029a2800310009003e00c0e61340c0181030b02061034813040003001c00241c244903d0a46000300158843d945546003c0000c5845142c0380d0b001d04040200c80311540c8400c082202c1c0c141001446001c51008500850074400c2402813400001060b208400315050b9540480c0c4e0350740090041c0825282c021540c107680c00d20030442c2200c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 532822562 1250 532821312 532821391
    0x3050c0d060902030724080115030903090f030317090712081b1e1b0603041e0f03180902090906130b0d0c060207050a08030702061812070e090a030206 66
    0x8507903500b81c10400e201e0b8446c0c8528914a60100443c0040c018826681202d6035003c6a4a124141c603030300310001d003074400c41107003404034550b00491341010012090016500c40d85900301008200782208444040007000d00085510045041c03000f00400140e40c03441d0b5a20003501ca841366090b4044d0b00c0c0c0c40c1500845158035208480300c454909401540c111000282403041c0c48103a011412100c1885002c68061900802d0400203e40000d40d21140001c0910440c40180c0c9000ca4070b070398907501c0089920b0190001001c05c01d048804102c150400350042c000039404600d001d8100700820b4404070001c1040d84242d1444104201048440d000500d070803000505c511407402c441c0c0f600074891b401500440700140700310b02011503241005070701082130b030700f603d80210f00340710f41c075420410f0329400310342c101801c805540708401464039a10040d50802800c900500303c2d040c02c00d101007103542001000004994041d140c0440880c1d000308426811103400c031209000801c2406621964001100c45d030b02c0e2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 532823812 1250 532822562 532822573
    0x50f150a0905010305070516080a02150a06031712040f170f210106051b0c04061502010c03020a05070807060b1002060406061203050d0b0102100f150f03050c0d06090203 74
    0x400e00c0c0c0c04503580082d038400342c03400c11050300c1e0304600f19403d001c0c0c00c1445840c81d03110012140851281d101038600a0424030403104041d0992550318141c0301d007030350000c0301e00e0b40f00c0d1418000c1008032418288004040070303c8905040e01e0302d5071a40304040261016004040c0840300500340301c802c5c1c81e828100d101d2409017035a07503204000d04c108254010036540e080101194800c8880c01a520005030494955036a070750700f402d1002d80c1c2c880b140d01688a00c00c03400c0c81460055662903e031801080000c01c0948480d030664001c0c0756001e03007512a684210404c01d4070401c5280b1109030010306a480190b0000c2d85983c4541c0caa00d0501c006003005c4424640c0180c820103c80b2450307070300140c05445603101c6c0d18107020702688c641c03000d00b0301c0d1851400140410030600c00003017105100d50100300500c005204440007240303c246003d044400500030140b0003503e5008006e0384412045128004104c2c0300704203098a40755403a410303215100750002a00c1a0703030304181e500602005820910407590020306491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 532825062 1250 532823812 532823827
    0x91b091801180e01060503071e090c0804050114010609120302030c030f04030c210312090f061b0504050d080304030c0b10060e062109030708030414120703020304050f15 74
    0x19402c01804016600300741c00c0070b1007840c0000041c016081200d6019008129135810080324012100d604c444014810b00f2161002440501030b00440b5580211911804650700b0541801d90a481d20324500702c0c502404207004000546e404180c20046130400d08440e07545140c00c0c0307000c9040d03104107840c00e0201d11011840c118000704480050080380d11130f4850001e40d1f40e464503110032101040b850b11121004600ea480c02003401848031100800d005a00003484980a5540004d407032510304003030706c070b03180d0354040c0c404100c4100000c40210115401c0603800d040c502800500c141e9040403009280d000c0c0071011a04150058081151066101401040d1840c0080036900c1d00040d03403103220b0015800c0492806a410203c0031a0050300ca410401c01e4448010003a00030054801740c8450558407041205001182034000550b0056105081040000d1807050a83d46821a0b09555080180e410006030001035000000c4138115079050300c80482042080e000104000141c49013480800000500700303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 532826312 1250 532825062 532825079
    0xb0409020310050a03030806090408090904050a05060106110a120509030304140103060905010605222304060e01050306150105040f060e0315160804050102190801080606091b091801 79
    0x95100360400c2910b800c055a81d442006070320402480301401195908011404a017082c10a0307a0b88640540a501d00d031550313840108422003404c680948041c0c00140094081240a01c11130307005000529000008803103460034030341c60b00d104a100810104080d42c071000c002d4090401e8504640780103080e030f40c507170b9136448003402c0020002c440e550003e441d014000c1540103041c800d25050b00c640b0f96569007468060000c2e0341c04400311300f00015184540c0040000c4011200d5202c506249082d100440034032030703140c28030041e10300542124280009050042c41180c4002414541c4909584e22026000f00040c00580e00e80c03040360007465240c0d403241e0000c6001c036001030503581250000c0d000c855104800012045034040b05580b4004501000800b0310b9080d4442c450041d04180180d000515005480b000d8200c02a03800c05400041041c3d0401005004810b2100c1d66100d10152420700161508a02207050787c40c00403c2c031101100b0200303d244407601d891800b070300c80071030031b198811440d41c440380c68 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 532827562 1250 532826312 532826317
    0x1a010e0a050a110d0902010e0a0609091103040f120e0306181b0a090c03060918210f08070c0b091b0103091101031107060615030b0607020a0303080606040b040902 71
    0x1290000e003024082950b07002c4522820310380507100f07003206040540580000000c1e190000c42681040b01c0c04078601000e9958142017002402d69481d00b05819242034025400d036a0030040305440403030140108400b040003400ba00250b0750740b203112041c030b0000854041d500c07903250f114502c0d0140700708000c2209030340d11010544080e0310b003001107640b00396030a124610040e80da541030a030015a154010003052085800c01a1503103558140403460035158403140c02115510003040b104100c1c000c118106100701c620903100f6410200524442e1040da45c60054150820010b5040c1044156030000c0c41d83d078402c0c8c03201c4010543c05000401503003000c80321241d0f03034407000c0a25051030045c820801d00c60341c003d228000e245035100101a40c1513503210011b4000703080441054082e11020000c940010300184503100c040c092440c010200064540b2004044640381d800c140d00a03903082040902680e00c0c00c400000701c950600d030219607580c1d40c401048883c0101e5204944242c0081004204901c0d40e401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 532828812 1250 532827562 532827571
    0x2220305060a0e0c030c092205250b030c090402090603090f0d050a17070c1a04030210020c0a020f121902030d030507080109020906090a061d1e04091a010e 68
    0x60100c02c0f10601c0e5a034450909007145941a0320828815280b820f001c28800c1e40052204600e003100c010140044d00c082640c4401152076412811905040144071084198000c508941c1848e44905040010700c00313100c05484610501d41c0400c440700c9960f1541c048504042014082d140c81e401d11001d030369030703030b90300c4c5492032215008400c803c001c07003031048090301c184880030f40d034500101083d05001c030040c0c0d81c041d000108110088000300003051131b40b4107032030070030780070b803c030740d15140b45c10309000f03080510741c10f01c101d8164010045031203c0c0074002080500190115456a5500d6184c0005103140b024806500d10314040e910030f46408000160040309024000e8090b11030340103400e0b030201c00f2a101103c0c1c400101302d0607001800b0b110343c194082d24600901418036031400e501c40b400100c1325034041d0301950008240e103104414110350020340c500703641c00075203500b1541c44546514884007455941101d00450b42c0340c81445c280010400303c102d400c1d03801c0c1c0060600d075854003039601540b9401c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 532830062 1250 532828812 532828831
    0x1506032708190e01020d030b180408030403080901181407170304030c0e0603031b0c0301021b0d03110a0e0a030b0103230609060f0a020d0e030915040503070501030222030506 76
    0x150070b606118020543c82a120324168040c1c0015080040150014a02c20305440d0300300c030704120100544141480030900072405200c00741d40b24a001d180003000c0a800408a540c164100280c1780015040071000c40941380d403000708030034410b084080091901240e0360010000e003480031580c0c030020001000620503607014040358281e041d01c40c100b94040002c16104580c00da8002c10581010b8403407404540300f05286007060f142d2020408000909980045840b9004516910f4900e19035010810000c4124100e60070180201e0104611003601409105a2030041c001c4020071340d040d50b620301a000c400346038014000215940c481c10400031007609178183c486006c078140090079101d0b000148180c402c00203003000704081e54442d994411440c0018100409468007403061880411890080d05803041d00c040040d41c84010030010030003444400c84040c41090001c020903c00d5480208000b01960700a0030013598a00c01440c201a56080a43c10f1a0b404080c00300d000c000c01070003150b07450140a07240b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 532831312 1250 532830062 532830097
    0x3090325080a0c0b210c0406092c0a060f0801020405010f1e0507020d0506040b0712020711040213030c0306140105060a0c2411040302090a1506032708 66
    0x541030079540d904000c5000e442e0300107a41d03040142c0c0600300002d040e001100c542080111030010820350036030a0a440600f04201c0214007444a5a80614204010035100580740607074440f800f002040700c28001621b060303080c562000a03400c105c0d1070b0001d0004040c01c1401c200e1465441c4102d6000b50081c1c02010b000501002041000c00e106449034041005083d16031009508148000c0c0c2e0141e02a07601281c0000c028007001000c18802c0c00785510660040c8580d41142c94800340081142c0e014070100c3d4000d9106102c00c2c00821a802c400e52020502070380c2c016a5100030b040380856440c210703480203103072004400700030040242d9508022954600504080d49603600d620400c030301d601030040381b140050118074201020541c204410005802c540c000190303041210202ca6003500c281d41101801010002000c004505080f1407041c0d00001d60340c01003240000c1e039444494064147d110309020142c82c3e4501d26809200d4280c080d290748024507a8003d42c100c94900803076190007403001c1d5080380815 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 532832562 1250 532831312 532831319
    0x2406050d0606080702071206150312020d050c0316050c030a1506050105040e0408071515031e031e05041509080f0c030712050f031b100b030304150203090325 69
    0xf80b602c10b0b000e510f0b25000362040078240310805440f880030500c1a40c080b602c0d01340004400084180c100041c5001e0030100081c03002a0502170b141ca82c9801c7d082c020044100002c094403140803094414100d920024016095418241382c0d1401d0003c540b40da500d0b0044a0001c020000c10b1440d244030000c500d0002c2c40b000340d85400645960095214030100d21044a0008001841100003041071500c9002069001e020700d4214100700c4044480302c1070b5020134101d06105008100c0165440e442122039038030b8401440b594010f000018140d82c1c92401e192410b100213100b400b07002601d0141260710146100b90b26040d9000f45548080c1c42030300d02901551243e039815950110301c80c05040000f81c0202462071030090504a030b000d00c458165094045d880c1b458180c00d02c184014000d00c00056640c40340101c00844850607d101400f20090691800480c001c4a0718040280d604491720002900c4c074003401e4140c180d04512440b540d07543e050041c2100141084d018115409005510340d8010285545 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 532833812 1250 532832562 532832567
    0x6071e1a0105060f0f1c0605150906040306020f0c01240806151c0204050a0b180907060507060902190801060f0b0f2107030504021914042406050d0606 66
    0x80c021640c00000130003529190007004001054421100003405240c542a00d41d400080040c0c80700c2000b40c1c2d80c85101c100801e10f4946040c06050078500c0d0a180303007201c03e40c0003039014400ca00c0020051900443c65001d032700f03032070019101d0346040180280141d20f400c0481042c00030f5051600c018102c04580e000ca401c0d00c000540380c1c40f85c00ca101540c0d5111350400b04000003014a00c0e2400c1c420503020f16168010380f511700500d40038030900500424001c18010030003090341c0c01500d5840400040004100c000400010b101c42103680b103040c02a91240c1c00d05041018000c09400650410b00c12028490384032141c00f140b900f152007082c02003040c151110400c030300b6641c491044910f5500d003801aa6404900c0b20001d00e5030b6044070000070300300d00c03241c12f955421141c219a1440400ea45038200400e608200b1401c0c1e00c01261248005503040c00c2c0020040800000c1900b2070242c0e41da0305410000100b00c003210303104282d0320340800c0d48840d91100d004125038002e00640e03a400307080c048001407460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 532835062 1250 532833812 532833863
    0xc030a0f080c16110a170f0d020a0807060f060e1f080c090a14070206220b01061b0b090102090f0307061403041704030606080609121806071e 62
    0x900e66500b03928100440d0800000c2d90811002650116140706145002d940c946603060028001c10686040040d0212106400e00040c1d0785041d04581080507000015a40880ca04440340da008c2c00442e103540950070308500900748644412211468800086000d10001e900d251054500142ca102c3c45981c1000c01c4008035028410104a5800340c40020038614045842c0c40d0301c413520740380004018074115010490148240c07950f80160b0012000d001d40c0c1400117001c2c40444803c6600c60545500c15a00d0510040d01441088200710110302030740941c0d00e440001c0e0f02d483d0f400020b2a540c0341014260036000b50302005511388941454442c40d13041782400300b00a41140e500ba214550560034400c1c06c8a0320ba88000e0040b00e5039081d0007201141d8284080141001d540140b500040003420051075070b03d0060301038203605942c2c1c001e08180546000900840d00c00f500c00c1c0c1302002c1c08002c41340200d261070048060040c136070181e031048400b0b0410410542804503000b000e109002c540248800c84800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 532836312 1250 532835062 532835071
    0x1103091e0c1c0614091005040804092a0206070e090105030309151e030a0606051c0b01020a0602030a05040b0105010f1b02120604150501080c030a1104020f0c030a0f08 73
    0x903000000007102926064401d0318074440c09032004200d001031030791680b040790f840c020000040e200040601014010404c03156440f28034140f010421800c3c180c48142e9103009074031a0031b21290b03c480403d61404103401410181080120131201c006240c89806074907600201e80300d20000342d120a403040c00f03240c10746003141240c40240155180000580500414105c40a6000d603120700411007081d20202e4800b01d2051800c109203440d89904140c000e54060b1880c6038001020440184441c054070341c141281d01820034120400040c08030110001030b42800c01d044000f40c81d861020007048504807641e00880d21039885030191044903070b00c0b000107462030484400400c0000d1141c44d0310b45265100000c2500c0c409000906007291000c054061501d00001220708030750340400f4041c2112105058010203003d48610030180a607030401300d0102e81d54140c8510702030941c050b19010001d00e03403203030341c100e41c2011503c1c0c100598410304405581d40ea544480d550100050301c4040710081507200d80d40c5e8a004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 532837562 1250 532836312 532836373
    0x9010c020a3206010e0a05070c02010f230a0306150507050a03050904020d050108240705090424030309031502070b0a0b120105181219050a09050301110309 68
    0x4103042e102c03a194106680007161004101954061184100400c20701d4000c0030b1580121080e813030800048800c2e41c1020303100302d061000000c40040181c0c1c00c51030f021041941d40c509a4900c07200e0701c800030030070510144540d072610800903803100d4440c3c0c590030220684160000240c0c03165070f40320048540d40300d0400040d106030000c504440c0028070440060000c81e0300180058107104100050204030b031401e911000ca55440613002580c11f0071051001482c030211444060402e1038030443c00362061140701ca00c18840c0380e03100009625a503041140300701e01c1240b00800c1d0200b5499240c040c001c81c505d408150750480d0003401020743c08400e80220b80269600481c004803c1e00c450f82d0303d802a01581c0a802c2d0300c41c81c403804580e9045000d11502e882484c41c03000c0b10f802e050040741218142110300705482404a800c11100c0d210803d19111510b40400c2c604d0103941e58203d01c07a0032a503a5131b03241c11144e03265003020203100030318401c50702440c019896501642c20380b0850300c2100e00140d19001080d841e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 532838812 1250 532837562 532837583
    0x3030108060c0703020102090303040f141801060c0c0f171c050406050903010b100e101d06030907080a081206220b0103090b04060507030506032803141209010c020a 72
    0x1c2c1c09081c0c0c0007801000d0b109000140c240b014150002c1c1c2140c01542160307085002900301040820541c1801c212602400c0c0e5410310040700040d4882c0703141005002c1c0400703108030345201e1410800e41f8a10a001044c001c8001c02d810b54859000380d13036031700606c40c00140740e205194640d81120b449034a07507038400400d03458140c9007611f00541074807103400c84841c90341d0556a40340701010035228800c42d41c100c5550391391801c0c1205880d10400c45c4004440310003604001480064811542d0608003443c20b2000032560755032640e82e440c0c0d0f190310703000164022907024001c60b4858800c0140140240c1007000342c500c60200142c0d906014000004092204420620301000c0f5160344141d1a9116102d81241131502240c403400030b440d0304400003010340b01102c900f07940d5070800c03a010750b0602c1400d8001c0b40c210054040c481c075402101c00400382e0000d21100b03044040c0342c41010907000d10591400301021014503925101d80360586518010200c031000003550801510142861000c07420254090b8001140c51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 532840062 1250 532838812 532838821
    0x81b180402060306151b280f02040f18021512010513022106010e09040b0a2417010615050f0a05090924030705060703031e060f03030f17041118070f110303010806 71
    0x9222241c03508c01a6002907a601e410028041c603800b401c1203441c01602048600e02031b61040c0034103814803440207a4156000d00074500464441c80d81181143c004944260440303042e41d441200911038944224514580b404d03d10140c00b00b8900303014444c960176240d18003900c2c0004140155a002101d0017004403412800064100b15181d01c8002c10700301d2101901b0000301c51580711202001c3c0c80e0041c5a261200012054034a60240aa10013610980d1801400030001d50000b420310300400801d21f029241c0440c2c0309510b1032048041c0c44052000070085105070405003501c0141b07003440c9912100c04000880004613034100000d08504545002d4980391070151309440c102c0041040c040c4400149440318021501400c16025070340142c000f030908001102e00d98940500f1010804560031f090002084403c05600626001145d000c0d030006030f207414040c1d8010000e0b4108024480c458680411001404181584041e20f45094502074a0300e03110358400c03201c0356030b50b80024402c10003191300100014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 532841312 1250 532840062 532840073
    0x106090f0506030f2e08071e1a071a160906020c042327160303050306013c1404052206081b180402060306151b28 50
    0x340e4400c030120000d1700c00b0024030100070b4450149403a29072015000c40d5041c401d6000900103100204010304000781000c2e4102c00610505c0101e102d032050520a0160380d03070858403010201c4140039030200c10305400742d900d0030710a120040e05460384d0311003894102c4090a400d00401c03000083d101c96800900e4413920140c208005002407108210504122300781e10300c51100c0a003d01ca01981450a000b0100307020500125440200030850550541c441c1200301c69029480310040252905072504550700d0b595140182c44644a5482e2402d0324407a0880100c1044199071181c20302101010000c5104c440c88a0102d0f0030304641c1c3c1141201420402c402c000510340305d0080c40b000701d042d04101380c0c45015407010708100c035841e900c45845604115001c1d1441031840c594119412421143c1d44175510010b80070710f152002c0180000e000d034200001040702035840d0f03007600c0c031300e183c21300c400513601e1201200c520302501006042241501c5200c40f4190044101d000400f200d114140107440d84c9283d07134551 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 532842562 1250 532841312 532841341
    0x8010207030e040f0207140a1e08040302190510090e1e011e03050607020a03170408030a05150d0c1d0112031d0d050606030c031b0d05010b0a0e0106090f050603 70
    0xb000580717036080180c81d00080c49004070440c1d14003220007a00c09050036007031115031100590b065500d55100d110394007002480c02c03419142960380644105075035031180100d00c0d00c00e0900b1307004690f02c50030064140c007070240c0c440c1030306c1c090724500c541007102e54407001c2071100300d4420305514100030802c86005100410002104244000340c00808101c070b1562a21154109242a520240183c01190445042c1a001210b01d100e04181e0200740e0258030b4103441d1403000d40401f0b0549628240c5400105038014190401041c2012000741142c0000d41c2902d001c004039221446075454141b0900954100c64220003170a504a40c07140360107207419095a9012159880c80044100d88206a555004555112044485e0301c030340c8241d00400791820076408051034034030000d4000d4403a50140203d03500f140140f92038039501d1641507507114a404001e02d0300b54050014408269007014040a000586042910036103040310303266101d0246460b02c80540c01c0c04140320340501500880100046030f544c1090f03840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 532843812 1250 532842562 532842581
    0x105031e010b0a06081b03040210080702120d02280504120c030b131a160311120906180a050606010e060903060c04091802091506070b090601090608010207030e04 71
    0x42d080107040c0000382e405a00390030407000514400100703c0030018114040d101c0065419680e41546000da00103041c040e54207109100f000040f001159110380200074810412080c1d01a250316900318609050007500522010306001d2042c0320390018142c1c00305184034040025958017841c003400c0404039801d901c5aa50226040c008000001002c214203031601d070f0003030080e13254185010b40281031607101a1241840e035101038000c2c20502c030744040e14172080d542040b4182000320b42c1c0004040c2d1100780e8000c03103070510481040d200421030340ca00e001c01e006100320800501ea04581c180d840f03405076681c010380d5009100341c0c00140480e840d50f000e8008502c10520040c002450203805801081c10001d0030b6944054510010400b405100c14a010f507401540102500b054021040e800040c80007102920440302c030049a44c1081c05c6032205011600e41640140c2c5803025810a441c02507500c600900c01c0d13406d2075140c2500450380030010700858040b1600b5940d8040603006400411000f455802c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 532845062 1250 532843812 532843873
    0x25051002100908040e09010213090c03090602070c030203120a050706150801180308060f090103110d0f0507060f03020408030a082a0304150903020604060e01021b060603010c0305010503 81
    0x103880000c80440e0059245003031060f6500c41c0c07510700d0715001c4140200058115441640140f00c803220065440e0f40000803036414220103d20801000302c1500144410000900b4084c00004d502c428044685139407800c40c0c0c801d030110b03a191808110403400c00c5c0582180070000030002c005800115146411850600c0820f4620507082981c0b44021402c503103481070385649104c144000801415009501c541d80610709694642c035865510002400da200c05000c000e02e102214502c0140382c6d2030b122a40d000046c4d00031075455128416081c07495551000f4810354002458004800d030b5024031034001da50485105000071401e004460005460000004000c10303042e044403c4810114860030000c103480701180f07a08aa5607041c82c1c200541129108103001842508110740c5500180e0700240c183d9000c3e030040c0b00051180c5811515a01a1240c8002c20000c0820070085c6854620040798581c000da504034000c12000c0880c100640a03640244200c1354181c0001000007400c50751113003252000342950 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 532846312 1250 532845062 532845073
    0x1e09010b0a050a0e01031b020109030f0f02030a03090f02120a0501050601030b06032a0409020405130612081608040e180604120c1a0f0103021003050c1e0912060925051002 75
    0x40c03511f214849070301c00340c1d480113030346804502c400e01d9000040c001400290340f400e03016107903078083e0107903492068001d10307000c0540d6044680144a0381c140e20818055000702a1148426121250346c4d42c0d020400058035694640004182c1075030180c400c0c4c0307030205405000c1c1030940d0788500e00c600c00703031008032640704d000500d4184482e00d040d440d40081011340300c90380d001070700c95041c10103101110700d50200c0200c02a14285080c050f442030290104181c59001c8000c560b140e110314000c948100c44058014440c0d480801d021511606d01d0354014458142c0d2140340c8849050700913115a942c0e4140c1d00a0b200400b151342030503200d403150340c10109880c0260074a85140c8411000d4416601d400c56021102c107507042c006100710f19140100030600266031606100e10304100f071041905109940d91100300340b4404441c800001c406400740c0e50b103000020420401107002d032131819240c820032224104540200c48040e183c0120340e500f00d40d140b40e43d02c0c6a00c544181408180022080801c00e418194840c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 532847562 1250 532846312 532846331
    0x30604020903060c0c010c080f01091104090603030302090103050c130501110111041401020601061701090203041113060306060f08060a09060605030a082a030313020f1e09010b0a050a0e0103 83
    0x3c000340c50151091384003183e5a030340840d91442c00c54028200884c2081100300a00c0000820543d600d41555040b00001032004880c03041d03041544120340c03210009505100c0e00105054069000d080410400e8a040c4143e0392403e400c01103d1285690740b400780d612858041c04039510a50003418520621400001c801c03a4101d5240b0241d00b00d90700c19201c2401d0080d00140550341030001d1070040132075090415203070001c0c080b01000d0040500035003082c15070110005052112400c2100c1401300c000c0e150030062542c000d01034000d80124002a24514140a80011084501c8241104550515000d051240c4443c4803000c003501c4d05c11016590542c590300049460340e01071041c3c051442c0316a000d143e85220302a54100d070190403d117040d001140c0e8410744041d841c1d01008aa501a04581407a010b00c01d151000403401d43c059170a2540000c6100c81240c8901c840d44001054000202c8800e100c80ea65100301031144e101e514107010010f00180300d02d0f15107602801c030515142105050105001c0038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 532848812 1250 532847562 532847569
    0x5090d0e040b0414040501110702010206040618020406290405010c150603140f0c04021215010903050f0a02130501030305070201050d020d0c0818070b0912010213090b130c090b0306040209 82
    0x96003111403041300e203050140410060240301d03424181c01c04550701804c2003900e40001c1d4840070000d2002d02840d803640030403003d0310700d1941c042101c01c0d030041c0100219519030000041c1c84c44600c84403c4400100d8149060740f051080a035001c84105030744030605600c00f079070303548902d0801418416140b170315201c1c00f100084104500210084c400002840d88002898110b0710300300613000030f9802030384104001600e1591f80302c05a684100c1c03d81c8a41c030840c4030a00100d072640c07603d0380f01404c9401401c0844154180204421120074000c07605508154044010344c070840341c081c0300c000d0220710100010001540264050440c1d00c211050060600b00d4102c0d00106a038040d102a400040b03000b020040e81183c080b8412608031032040040440900384181142103102c2d0200c018840c0c00280340c41090001c0940441d4500712142d10000c0703032150389480c40c0010305107070003003180b00e5021a016510924030602c203004110743c507656040350081c50604980700580c0094251900140c01300441940c684 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 532850062 1250 532848812 532848821
    0x9060c1b070f09020a08010618030611071209180e030912031c0204090e0a0b0604181b060809121e040e04030e0f01050f1917040f06060905090d0e040b04 67
    0x3c40c0d950160390303003100701c02c02880c1d29016040442400780c404614581002504041c6041d261322480015041d07442012100c0b86000b110740017002007207030f1208810f40d9680902000d00304e07400303000b0400c6050142c201c101d040d200c0540360308805038414004248030b072070642040c020001c035482c2aa464101201c02000d030a40c4000c0780840360513000101080317001001e104044800c803054018110700c841503a00c80c103081d100a4072907880b440d11480c0c8152480301103038003400300c15488810824280b54540c0b410300844032030b01c03440300468080c1c3c000034068031012a0f9002c0e10103030020034070f14042c00b1910825580340000601704400d242400007184095200b202207000314041e8541102c07500b5400f04001c0c05084c40026035041110900040b80800301d101c0580361f1344410a5025000e446403010100c1e0700c030703840a42c2c03210421048801d01060112228044170f0043c09118184409502c82d00e140050321030980d507802c0e00c0e03846087c0d03000e803162182040c6040c0803001000410310101c40700005090b42c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 532851312 1250 532850062 532850069
    0x109030215072601080c040b030d1d04090308040b0a02030906040305071a07020c130b03070b1b031c0516080604020304110301061710060506040e040807050a03080f09060c1b070f 78
    0x21101c03d00103100211040010700c0d10064116028002c0c865031002080e19905000f0f1180148000410108503902d24621803810302ca0000e1f000b040304e02154140200144015241994034824038004100707012014001c0700d11404124004010b02d886594046419920515069600b400260700f1984807540208803540901e456078010304005c050320741001840b9a0008105415070300d0500803c4050b20045400302c101c07845030300c901d601e80c091110400b050612080c080c06c00380c003002442007500d16403454607036034011041c45d041240c0d9851203040d00c1003101020030b4a020403006400900f4520b011340041d0350281c80341c2c0503038075030112540c0070a096031840d8002d00d202c09501c0101c43c00c9400c0400030411741c040a90f80034407405160201190141c811801005c642c1d1000e0b00c000f4003880421411a01c240d40d1000072204d500300d5505008001c803409451001c44c0e00d208401144c0901c82c0001c090780203d948550691420940c0c80c18a0885d50740c4420804640c014100c0000300111300803c2072004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 532852562 1250 532851312 532851377
    0x2010f14011d190c0302090909030a09140d11010c050a030e03010f11040b07140a0c142e0e12070e09030a0927090c0303030e010903021507 61
    0xc03541444600074408031401521240103075848100300c101c5410009902c0d0342603101d4000102095820300480281c4a40484d45400030f40754024010761010010080c81c850010707681d062010707609c922402032489403000440fa03201040309404000b0a174071a09002468105051400c1e00e4199559a41d0800001c40030540219040701102502e03400c00380141107081a01201c01c00030301201e090a140c05003e540200449a840810382e0000c2010ac02100107880103030808032208291321340b401c5a20b21031a4080e21805071064681041d8038103060034200740c501c2080d8080302d00c3c48406541c0030142c00d19429050104210324080050685030f1407042c001041141c8040c0c24110308200c0d82c090403a01c06020366440d50300400c0380404041c0c1c4807220b04269054018000410a1006000700014410303000c1d4200c4985044500c40801400060280c1243c0c42514148000c45440c000c2c142242d003071290180c090313040410a089005e85403c8401c0d804540c509003022060b20100045034039075410540003c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 532853812 1250 532852562 532852601
    0xe0c09041404110402040e0408030a060305060108010b010f050f030a200d020d060f03020907230d020a091e12061d03040e010b04060c120306082e020304050a0f0302010f 74
    0x901102d82d0319400c034060142c906602d0a0328010904400007c002d00160109101102050003180c40b80c220030021034010003210075650316105414020400064454081090100080c0c121030003007042d107086030007011030141180d0f5070301b1400025040d42c140500c1c100c405074107500203070381800029182080080c040140c0b0349582500c05002c540d41c5070403105d50700303ca40e0003c00c01a41c650b00203d41c4403942d480c003620840c00b44030b500243e4940028104401c080081034496542016074003400b0403018a41d1250302c0159a00010f4514007114041ca070040005e556041c062000d040c0c10301070f4000e00c503800000d090b11081585118824000f441e00d00181c10004041000360308241c42c040c050034083c02d880d49007034600b0303501420b60703400100e000b00355504031000c00c54030358005e0380401c009001e4038090b5003034070448a018504c0c100030042d1406020362654080000c490061090700c2c801e9501500030b1000400391340f42d0340e07031301107603480e0403030441d901c0754114251701442d409001c4024490290002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 532855062 1250 532853812 532853821
    0x40f060b04120c050d0c06120e010c0c0b0708060a09110d02160b0a0b01020318030c1f030e010207122708011b05090117060a05030a0809040b0a0f0e0c090414 69
    0xb0000d046944c8014468001c4564800c0400c00890040080711101e04001a00381c0c040d048040141098198003040e035445c2062161055400c01c52020206100f165201020b45d01d01105550b0076800b5551303240c20402d480401d2104941d1540040b08034540300c0b0016007803c08020040007680d00c05082a00c0f0341000c80c00ba0800c124480250702c1e080380201d8400d00181e0380c090b000035070302d0140541c0303007802078801c0e00313000c0709034800784240a03001070040c100201c004d1800480302c3c200c0d41403000320307800a494082e00c540020010701c2980d8009a00111039108080c200504840001c24003a1107072202000102c01a840f40a000d21980204001c070008556031090007035011a240d0f8104124092080400c2400c140ea0303403004c011980711001c00c1c2042400d449000120312000e400d9009280c01d40b14044414090181c040d001d011421400c8900740306020703400307042c004a5021b905c1200883e0031014014001c0c00900201581d0000c2c010340c80c5400c1c003c3c0c2800280a4581900c1003c0f2144411000e11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 532856312 1250 532855062 532855073
    0x70305070f1401050309060604021c0f090b100602070911040e0420060306210f0f0304090b03070f0b0a020102131d06010302130b090303070506070f1106040b06040f060b0412 76
    0xb20301c802024204030781076142c070301c403015200c0c500203140521403a80094600c40c900d91b1152861915045140d0400c2a45d41a031400c8005240031a02600d203100303c8400507a0104902d0302d800c0940b40c80d03a010300a07540c81d141c0c010001d000c8400201c0c032089000c5c8400f1031b000e000400000e00c01c60252041c50b4076465014a00c41250215101507805070341c0800c00c00a040d00ca81c90161130403903496603800c14055941c450141010501400480079020ba042000c00d5030300c00001500507111038203401c11040f4044bd003056500c2c0000c0c03282c40c008a10381c100400002494501138130422540380000f614002d00c00451220101c401c1d040700a034410450808031000700c0038404030754003c40a0030110b181522000003250502c2c0700c1d11601c0804a00003ea511464600384281d8100941c00402c542c041d0a10000260101d6009400000002c0e10040310003000785c40090b01601840d0420324500182d200c0c0c10500000d0b002201c0582001d0340c030784c03d0015141c1c0d0280c008200400c2c8010400718940f0051819 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 532857562 1250 532856312 532856339
    0x2030a0e2e02030f0c0a2f1506010806091506030406060311040501081207050c18011811070b090309121c0203070c1e0305010e0d1103120414070305070f 67
    0x100340300a1050040190002c5800403885c0c00111458440d619042100d00441e882d0608203110506611030040b050240000c0b04524030418058400b92440d680034215110040c40d0100c3e00f41d8000b81a46010444900303020f19860b82000c0c803030701800120449a004640950300950b41200d03240d698000030414040120408015240115030070b2226515210042d5990404200d054164010015441013008010464072054113000f0300b14000d07031a05401d0307182882e5000d01c50703072089101c1d012452440342a40d2043da908513200c1d0018900b0003106d070f1a03241d07161200600503041e51004102c00d541d544c1d00c0c000d1200303402d090a4000c0003500a214160455020391200c00c0b419540140a10000034000b5454001901e001c4400c505002d10b0f40b0100e20100c00c0140c1c4082c00c00d52a200840c03106020200d6540d2a25402d6229400858910003029680344510000b021031600c0003004140001d24400c60060001d064071304403450580c0343e460705401e2a4040e40524020950a007080080a1040c5403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 532858812 1250 532857562 532857643
    0x21914090a14010b0319060b0403051c051207050c19330203060a030f1b0614030424020409140a05070504060c1a0408031f1802030a0e 59
    0x5040c0200501c2c12000c0002c05818011081113040100010781075502ca03401c40d0f03d010540c20000c0c030819958030382c0030f103065026000035141c80c02162001c91404401c2241c46050840c0350381e41a02c3c004000310041c0d8480e02c06011881001010004001540300400074104c58a49800c00341d160a102c0d40b800b0a580c0c18040000d41000700f10300102489802c0c0308009510076900351001507502d41d2900c00050358070607186c00040511850b0200c01042c054142c0704050710074101031000da0301c1c42d00e80c10151202c5c400c0d042150400325003000010005100c1c01129103007101c00d0b00e0304240301440e44101c0000c3c0d80194108240c115a64000038141c40790070b0703100e55004900c02400700040d0514030320003406481a80030384402e010421240b00c0c200030500f0800c002c014006481d0b00140d04092031700c1d03516039105580e01010310362800180303201d100312042d141040307401c9502c03105c1c0d070031200040043c041d400040220807625170320404910381c59020b000780e0f6108041e144800c000700e14000c0428062844d00c55 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 532860062 1250 532858812 532858831
    0x90a0510021005060a08032101080109170c0109080409020a090b0316081f0605030115020706080a09020607050708010b12030702010c0201051c0f02090a060809060a050402191409 78
    0x14180315004a081c0081c80c0c010500403556958200119004584035032225003940f100041c01109607012003164545052841001c840a0742d03144145402d0703461002001c0d140b0f05003505032050300c180200003414559411400401d01203250b440b041d040381c001e84e000d4008039800041d150042d40e07000040402401d1140a1141181401c00c584202c2074000c601e004148407001c1c0c003041c00c44102c4407541d030b917243d0528011440c05454800040140e0405e2040d4042c800e00c1c0c800240c41c150000c5081001c0d50015958905141c1d80d0300e040d01c0141040080c103a070809000c02511000c03550611625019244585c00404c03404070040c00d0040380743c401c007042e02d825081440301000603a030203020032580b503809107401c50b00c52102c1c00d0075401090300c0d40441007103103180041d502d00c068103a8000e85504103044030881d000310380e903c5050302c62100860711b2203030682010000030b201b22280d0b4002d070781050018000307148498401c15130410901081e00700e980720001c9014450190f184c00411541d1200c2800c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 532861312 1250 532860062 532860079
    0x101a100804150510320909061b0d060b1306090810021b0f0c10051201051201060503030c0106090b0d0f02040b040b03120306120c1003200a05090a05 65
    0x549520086107032105a40c2d040588807008698960b00050f00800584441000702c0120780c6805100c1c580c0320f8001d20741c1d400c848808480704203546412031140c1c0c0309010803800350031241c0e02d0484050501c80001c030b0f07030410844207100d10f50201d1402d2149101400c004800745030341d1010034040c2e070081292540140c04106480c501801041800300b10f120760904410340250b00e41092003210810414004c2a0300d200340f06200c0c0613607240800080c2d05800303500075510440c400803a00303001c0f1224410903c9148031884490010001c5041418014844134215000000e00c20749400000307080d9449010340590f07580d1914400d1200c444103101d040000c280c100c0790802e03002d4566844094140c07080304060b00c1603596245020349502c2d5074000e1041c004c4014292441070b04003117042042c58006465003801445040154152114005010301d003d0800401d140000ca000010032000303008021504103c0001842c501e9285005c1c0d0b034080c1c24907031f0a5803252612420b07050700340f207003040d41903110300d200c4d0302030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 532862562 1250 532861312 532861321
    0x201060b0c101d070e06010504051507031218020f0d06090305030108060603030a1d040f0f0c1b21052203060f0b011b11090c131d0f09101a1008 63
    0x1c50300c086880101417070740396540d4400180e800b401030380d0020f40c020100c80011044410039034018020903200703846500c1c2244640200000f141c160440400c040085c00b0010ba025180102e017100c80410024040707010360406984480c02d58200c41c0c0224045000030005102158051101c503a000e8000c2d0700071424558451801091016103035000541c1c00c901e9071343c024458486800503000c441410105000e40396a009a5030014a141d00c01140001c40300100c007100c42c002d000d041800260050016024a60101c040051307122092003c1c50500100704118003a8190b10b007400c600580c240312040c65001c2c55400c0400c29615410904083e103841e0240d009481e0b80c122060b500b54601c60a01c90880303a00364940560402001000d23141c0c0003000d0001c0001c045424001040c01c5402041e124884955034104a111040e000b541801003400e03000c00901c0c020012034000d070344141924100c1c1d0b0b0b103021406060342180c80c00c0150049210b407040c90100e85052590b52038510940900d80f07003035135242 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 532863812 1250 532862562 532862621
    0xc01020607110a08030a0b1021050f071413030303060518041709030307020d0b01050411040807120c050d050a1428030e0604090b13090209040b04030201060b0c10 71
    0x205503c0040001030040f005c121164625070000710081e80140c8000360f5001e5245001e0084510b06400401e6190000f00500000000340a45806401085800015900c81d88810303079003000145c564501421040c08031b0408034502e44600e5008600940b0009070035418402800807140e0640d4501320811949010700c80011250000e060041d02035002a58681d500d180020b811032007101e10181d804600300307403007400b482600c1d015141221001c40d001c0210011003101000c44d406140300365592900800d000f0020800100f510341d12440c07142200c0a01e50751960001201540c8600301911140c0c44074000d48204040350b021480c0b0144203400401022804101644104003d01019904030404581e8002014002c1804191703c0800a050302e407299103501e20940188020590035109000100700c4806000c124880c07003001940181881c003155440c0e8a4100c1041c00240c17080701103650b40c07a00012050259000b8000020203480a0810800100070500c20380d01441d90034044030700d0035030744d0301c00065 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 532865062 1250 532863812 532863823
    0x20123070f0e130b030706020703080f0d0204030b07021c050301212d0501060b040605090405041109130c0e070801120c0803033306031b0c030703020c0102060711 71
    0x3140c80c40c015000003507511084800b02980040c40340c12000002e50400c202640d030708046200101601221512640c0c0c200803682c07a80d007840090184141001441900c41d158401410f88980140c0054a010340c3c0c1c0d520302d200780008488c042c0050300200351040401031a5200742511502c517103411400c0d541000c645140000c401c05000c20b00817481c030312440070040c40082c0032040700c914544200c0d414403e08450840038002e55401c50321540b0f817080224440081d0300c16641507490559485003880d01e442c1c184401094094002d5440c1619201c9050707450b600c2c1d601d124440c24448640d080985418541080c0c641c6c4660841d41c035200410b000c010305140e102001504440941a55989405041c1044400241690003841090000204011001e80f81c01000203040c001c00c90741d41500f0100d40e0a0b118000c440412540e0311100810105804049426011910b42c40320340c0c6c0d592500044003140b901d180e100030000ca000d40c01c10240b2015640c2c050000b10b078000114104905c0121041c4401620362 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 532866312 1250 532865062 532865071
    0x910050105090613090501020406030c0908031812150114010e150702090c0d0e03031b090a09020f1201090506030d020a0b19060b0a02010504050d03060302011706010e130c020123 78
    0x90b100392840940100c901d17001020ba0300d80201c02159540c1d210000200940500d880b520040b4001d01d0f0002000322000040395040b42012141000c5040d100040000b09600751640324903601c1100c4032101d030101c4c01d4924500910003211402d4000748040005007122445449e118407800742002007240100c1008105c070328880e41180c051f1500d41e1a4510313240c0714000c076018884010315100c00301001200000086015244440c0820040f003806c0e512202a481203887d034541244c00304404100b1502940c02411040c4180c84500d4144030940c1982408044241d0050b408907813200180126828148900d0440106c2d07407000e010040c016861358448100007420f0700b100f0481c642140c0902d54056400710002e400c0f45212143d440f07050031002030203000c4c02d884c1503440d40078444074108102c2c020300c25a400c40e581a191004002140003122141c0075000703203554140840994040e241e0341d6010858402c008002400050b48140000000c0c00c58a103010441c2c1d00c0741c1000300e5440e58200b07800415510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 532867562 1250 532866312 532866319
    0x1e052a030102040501080613090b070807020c0402190f0203270f0f01050a0e030c1c140c0102070612200d0c050f0403060905150a0603030815221b050309100501050906 73
    0x9984070640e888e001403c003d04003030804002a0f05100c4107651104241c0e01500d03146e82101c0f42c501f080c40401089100e0141040b4108039180307049641c1e40e008588440b040100e80c0196400d080259206211200c4400040010919410102140c81c5070982d540381d86614181c45101103d810440060603d115030b0a050b0284221462103110642e82040350000c001409400d101034121060a0130085950941c0110360020001c004544299000120b00719082d00590061030100d140480c1a2102c680810741c0303507410ba45510700400c01601110a00d80441c400110540d510600340001d081250007201f000c004125003004900714044c08842910b0aa0f50460310004520003103250203842c000a0b00e020140c404032a10401c0302e00c00c01e5611410840e4060703125403141e40d455076800c440d4071860400e031581c041c0203089400110b2040e40c0b22921503013081c0e44006a01ca02c001001c110f1811000f000c0340014000104201c40c21000780400c624003d040e40090085504060000d040464010080d900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 532868812 1250 532867562 532867579
    0x1060c1b03051f1107060b01080a050402060405060a23030702120301060c08090d1205030a0e030c030322081216050309120a030204030b010807150c0507031e052a0301020405010806 79
    0x3041d98140d800000007003a0441c155a803900e003031501d030703001e0709102c5031300c7d408140c0b40400203440c071500d809142e10030303130740241400d00e420705100070804290001403286040000100c002808030706c40d0036110998042800c40c3e66101e24041e00000c0c03401c210b0415940b032808092004202d425009051454142c1c0e010018580315180342d00030940c003491800d0090060ac010180c40d800c41c0390041300075030050120840500440c1050101e040d540d00c981d02000005030320400000d44086541d91411074441221819008100320136180d1002d950044c035041210b100d80d800504c507030040700801c40c81000c5054200380342549032082900380c584c5403490000107060000168a0038103403090381100c0255a02c009418002c1d41c480f4482c3c0c2d170b102ea060140001440d0350900000c00341f40104030001009a0060090140c0e40c00c6541c0c0410840b40740b1082c00340851901c4565000803404e0004071070903440302c1d14840021400004800088002400580c0a644100024003060340d0055405500c480240d41408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 532870062 1250 532868812 532868863
    0x40305070212061515210411060f0a0306150e190f0f08010507051201120c09050a05040c14030325080a11070504290f0901060c1b0305 59
    0x40c0c40b0b05080d010400c0c40d02803581041020070081e071010f01080b038144c4c0c400c0c18448815036080090302c2403100705260300c00d01c01c6a01d10980030142c1040d5002c0e1007505582110002c54010a0603504000f46400400d0000708840e401d0b0f543c14490b00c0c1c028001000c0701d0564184074000644600d443e500403e002c1e1440c40050715000e00000c081000a04428150300300a5940320391141ca80c20682c010306596508050114400d24442da0540f1307622420300c542c0c0c1d442c503440c201507003000c0f030715451b0b0880b14001d011800252031202c3e44992889240403d0000c1681d140c0385ca8110080400303a04180070360070075805183d410744c0b0000255401504050420000b4200780c41840c21010003403200100741d15000502c46842d42d81c0907000c091010348220031950b40c1900c0341d08110a079007101000c00d800107039400c1a80200208202c0b01180c07102c02800c40c42101c4601d0020800500e003d0b005000031611003a500301c200a00a5035403800c43c051042414106030071a96400e880b0034405242c048400390f6400b10300d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 532871312 1250 532870062 532870069
    0x603030f260c0406110303070912060b090711060f0f060f04090c08010e0601060e010203180d0b280e0d03271a06011e050a050405060304050a0b10030b0403050702 71
    0x19480406014081c0c5102d1601110a8005600601994002424109421164031000000c1d40c0c090000c5444620290341454800c0c40c5102d1a0301003070307480030380f54940d4241a840390a040d6004000c556141c4919a4003083d083d440c081000e0b01c004020300170b0b1010401001041c4080c0d64210320201c0d1101c00c02808900060051725461001400d10101003000080012055000e800c0700d060300001e0301c1c1c140c3e81c1c94409442c54103802e041903000d604108011041c03e5150001a0a80c00300207007006030010701380e102c9545480003100c214200343c80d103284407005141d4412040c2a44401c10206102414920000300d03121060200c1c10000d250b251100c0000ca88588841c42c501b02060f80840c858090b03c1e41041c90b4855009440610001c3d07041010450b9540320703014203487c16002403e04001094010000c8a442d4400c40305401040b01c1803001240543d1486e00440c01503000b10002e0102c80a07030b091264a44201400c1c0010102d20a1401c10014140e068481d50242e01400d000d0b072140c500c1d0020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 532872562 1250 532871312 532871357
    0x50403110f100e01140c070501051602030703050307030e06070e03071a090f01020f1002090117040b28020f0c190c0e15060c060f01270e1204030f1103010603030f 71
    0x80c2d00c0300305e011070200400105000041c1c00030703600410080c060343c1c03201010311941000f00c660f4200142c00c10400d500209008500440c0c01280b41c1c640002c88014044c005824507a081c2c074040700050382d0b510f8412b02132804008000c0503160311900320300c082c115104460702ea0311886e000940285c1b94601c86400f680c3c001d104811840d100079050f00c09226203941c1c00c000a5100c01481d502080b03104000007100078100700110b105035030091180b100c40e01c0e40f5000e41c40c1c3d8511100300104548400c4101401202540045c1800021241e4640d44034243c0301d00f164282901e01060800702100000300601007100d012998003100d08807010106592540090103d0903040d69240d540c00c05400034162400002c006401d80c031582556150801690303c0e52050307801e1a03a50342460740500c0d51400e03c0c000c610380c0350b440410340d0620702003201e400f03142c40c030300740040b07a0029031043e1350300741c0d006080c8028443c920184107200e800850080050a04603038024011161414607441000015019034140c00c41c003001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 532873812 1250 532872562 532872581
    0xc080c060c07060c0804030e040f0e12040315090c051e0a1203021c051902070909080301081204060807050f16080d11180108060d080a03050403110f100e01 68
    0x292261841c201407058050b0307010050403290300d8501201110610301c01c03880360b401544e01d940d9419580c1c1d075a10420010b42060751100d081145c3d9103401d0009548200000a5401118030b80d00340c40c2c03461810840316014280420b1012503050110303202c006058000e02d0401e544040314004c0c0820740000c088100e03042e0300440c0540000e0141408901805d01c84440d220302031081d421101041484d10305d00d444002d0306000d6802154052010303103c401508011020a20120f1040314a003079510100501928075901040d1141e090000052020540910617607800510400c00941f03401e1030410002c00000f0f0041289040142c00b0a000c007074208014100e609189882c841041c00d60445d090541c0c0d00d600c80e000d00d851007460038007903002c211411000e551205001a41d40c0201c120040015141c0c000300134101a80325141c881c0800003d8a644094421900715990000f401e10f000d01c3c002c0c0211091180802282e03018a6100d4601400000e4165007000b07a50008540868107200ba5030241c40c0e03060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 532875062 1250 532873812 532873837
    0x30904020f0f040803090f0f010801090c0e03100504211706060c150601030b0a0e0a090516080a030f08220303020c10050411090705300103111e01020d0c08 68
    0xf00000c84840010140c1442c1904445804442810201b00324100041000c4940450010801001184056032002c0540f80c1182041c2e1646641c80c0006404d040303060b100d07060039540c2c0d041400140401500d51a900040000c142801c40c2d022000c080d1904c8503202d202c503084c403103010024045072030305400d444240f600c00c0100c90301813a146440e500101c2c000c684c1075002a2901220030034600d000c401120449448034044841a29500580005014a804262640e2084102c01020110328900c2c0000903c00700c4003a105828243c46d004181001c0d00e0100e41c01c2206880074030102c0070125000c00003214820b1031902e0340b2540703890700b031700a4040c103a480c20b00741c000c4400032030005d403407604100c0c4114420038100503140f00c018108a4000390582d184d800040050081c001e0b82c640e081030745184045000c0c1a035800c0c5000414210041200340c0007118642c0d500844081e103418254034a0a43c0217503103c038038201e0440c3c400001d540303c0d00c2c104440204083e200000003030001b071804881100c5941f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 532876312 1250 532875062 532875067
    0x31214030f071b030305090c0f01050a03091a04210c11100c140705150c070e0a06030c03030e04140f130f200a0f05030303012c0103030f18030203030904020f0f 70
    0x908000c2c5c000e00080703c03040b01c24000d481c001c5240703281800034614140380503184c1508259100390114006c1c0b03030124040351642c00132200d2a00411864003440d00c40d500c2107032110901013840c0c145501503404142c00348103101c810000300b0006030702d0107400b0076100801d03101c0c1e2002d021031a10440b641c407101d40000e03200180c101c0c02d81d082c03c8004124203050301d2056038858502425100490018881d140011006402120080c0400d01c1083c0c1c3e800c1e00080c05480120758181c80f80c403000e0440d005644101c020901050300314406040501480c586c410580ac46039944e0720300360034216514040101501d685042d20031100341000914190b1108054000400c4000b122032100049039106501c0e52451050540e00c4001030405d2409030180140c40000c3d02460a40c0d01c1c1180f021590340c0f40340c42d840301e80e4403c0c0c001043c00c000d100069074002c1d4002d9845880c08000da02001d4410401d000250001c1380c1c0b102c41c1440541c400008503030301006e0548005a9501c800c1104990501a4150901d0802d000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 532877562 1250 532876312 532876367
    0x207032106050103060b0910050307200604020a2c06010311070b100503070605041206020705030d050a050108030a1403060f0d03020a1b060f11190804031214030f07 72
    0x25510001c251a001e80b4200000d40d120032aa01301405080380e5154407101102115120070300c00d80c040c40e04007416040484ac0c5031082c6281c20b10b40d03102c41301d991301c6543c800c10801081d440c01c1002d0300014244140e05c1502803410000aa100900801800c03007102c0151000c902940d100368080782d68140301c1c040080c2c48403141e16140340c01c4e42081e504240704110501e00800c1d01d20703000c1030003000c8440d60b840b01c03454585410107880001400c2e0500b9110554288030780000700302c0500091243e46a40000011903240c1265490200d8106800c190010f6200b03100d40068940c10038031244a80240c002540d0300c036a11030340095504c880000046400c9120013042c0001c040e00001d07070829152007045c0c40030b0200ca03e49400140ca10080c41600d0000d03000c1052001c00c40d0090b8501c010065096003981c42c1505000d64032499005041c800302c80d10180000c0030010b0101440300300f0001852442c00c80c0d9215411401000e080c08007914241032003001d03030007092246001c0c17104842e0000799a00d4141d0b58011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 532878812 1250 532877562 532877627
    0xd06081507030516030e0307141606020f0d12020717030f0c0313030f20160f030209010b030c070c091d0c1c05120c01061a0901080604020703 62
    0x408002034102122040400d800c1c1d40203000341ca00c01c002082084c3c01c0340220301d80440182441c40c03070056960004001e030b04045400c002148001c10006002000b10102900b66003124103c1c40e030000f0219004403450b4400e403000030a5004040e51035191031700c0540354a0889074000d11440b44000c0098140000d60480070032002c01461062440c00d074420001c0c0d451402c0360150384800c58010a1320b4018410340d0002030b000d075458001c0e80700c80e45040c042807400d080b09000c415a002c0220011a8803041c090300c0390800b03105d0008041e1280000c101d41c03082c699400700303030180018003803c4d084001c00300016100840403000e5548075500302c3c098800c0941d480758494000c149130004040d20701850701d40c2c0e1841040019160044001c0940405205101c041344036841f10780070f003021200350140b500d040740130b081104083c2044148907400041c0035071804440d411041d004000c01c0605860601100c1c009a07006500d02e5070010060f10003503681d03011803404aa50790b4101078000c80144414801c0704a451 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 532880062 1250 532878812 532878823
    0x60c01060e0109140414030c06010f05120114060f030307060908131e06050306010c0501050f09010c17130f0503030708150d0b040204020901110a05100605040b13050c0d0608 76
    0x11100c101d20611640c0700d041c12000c0da00c0252104042030f088601181c00512188181103440c01000240c0b030804080c2c04005061203000c0e0701560300c00f112000240304901e802c10010f4410031010000f00990500041c0801d902d80d0010007682c840d0448480d007445030780f000d2003181c0b951039000c00c08020b030245074601030b0b805410123200c203041c00f03440110205210300003103800703820000704400c0c0908103442c203170048034243c0c0000c01c61410010301340480c500291090107028080c0204d512440003a250911010f070850392071400f41020801203c0d0415801c19100c45900d4101d400c50285040310301440c102042a8814510010498400007081184082d800400a070041803092030045864800c0810800002940170000c2d01c202196400703e001450140c1c020320300c03100107040140d10541410025820f0615080003912290410035002e6482000c500c5800d000e400115020001003801c6c0c4086440c00e501d000c515091695a0320208104100c09015a00b120410480c1440300b247c4800b0450703205d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 532881312 1250 532880062 532880069
    0xc0910080105130206090405070905060703120c0f09060e0a15020c0307060810050603150a0e07020c030a030e04050a0e07171c27120f050d02060c0a0302090a05060c0106 74
    0x9501e4a0045048000199103d048035500184081d0034403a41d5010040109000b408800034030040040000740e60300c0703140182440b54065200c0852190400401d201551020100790f020400f05240c0c05e15020f4210710100c00f82e0f00c25150407601c0c821900c1c003240300980a0742100e10382d20708162240e80c1c00e640c00180c140d6008803e4094540c0e40e643c404080d52412010b03281c400380c0100401c414030a50410070040c65000c441003000700707443c1f4030300001b2500046c840d801c41080103007008100004a501008441224407080e0000c00070010326880c000c1c1051140d40c0c005114586178004100c016545400c0000c04249810582e480142c2c3c81c4621002520001600c0300d10780a2909424440c100c25041c0d41c61040c2140c540e00c480003204000051100843d490244103440000d002192191107690003288203889010103c01603101810050f28115468543c03004550011003040b9200040360b041e581e0405050030090385400e0311400181a02240d5001190414004030741102c05820540254088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 532882562 1250 532881312 532881329
    0x18100603110312030601120906050405030702180106080c0a0c060e1f0203010e01050105212d1510110f01051e010b0901050a0c020603040507060210021303140c0910 72
    0x380d5641410b164039240751045a00320b1400a000040e099402041b07050780b001000800003d40c0c407440c0c0e991008546003a90140c2e856400412164210308021100184d03100d01d2072010f07101d5600d440c500601c4101c00a28800c2c2810000c9001442c003401014002076850b40b0407400e10080f150b8810065603165052505644070070a100c0455104000e442200d0589525522030304103a0b09050040d40d0503400601d100b160342d8003240c07a244805000189050045034510b51080140300c01020103900310380c06915000300c00103844240f010002c0500585a07810009847c1d150790b03007094000644d0000348110350741150b070181c2d018003000641e042d40070f10310948442014241e0544400280030244c40309001303da00103c0200038504141d8040c2c3c1c00782c4411101403500700852005580480c050b80c100381c50031034860340181d800703011207034050201c510000c01e05981103013458001342e00c003042741c00c10b44800341642e080075091643d0000240728003051114080c01743c5855007805021081e220780180700f400c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 532883812 1250 532882562 532882583
    0x302130905040f031404050d11031e07060e0f010c1511070b0907170303040f1704090f11180f032424060301030308060f100c15050f0f18100603 63
    0xd1172410f00c801c1c5e80c01d440c0d026141e964440310561700c0128003c418190158140700e6503810a100358440c00e41012510b02010150040c3c0703181041c054820302200250302c1c0b10754140d40364150103036413043d401401142c1040381c4058014111100c54010100041c20346214940014254144403010303050a000d042c08104503001d8564500320400b01c6650200703940c80380e4000b0008200825241401400440c5c060b07000d840000e0b50b080881e1440d6801035004910b55a00d0340a441d2101c00107200780340c0c240180c0c003040740c81d20000d4111158101c1c00640514070406001703410710781e80e803000c114280381d003000c0e0b00080745000c600561024032480c1c200e0700c0909110a040c001d59010f110303d12404600c61003d060541542d09541d01600c00403001170030301c0c1c2c01451118541119503114031802c468003034242c460455400706030400b40070645100458204240c00d04041c043e41c594010420b66000c03100603240d013a50b0f00e98101c0c1c0e421000040c103101800e80320748140a049181c04d03502c0030044030310610070202d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 532885062 1250 532883812 532883837
    0x513090203012c010e01170f48041d0304120203060709031a060f09070306360c021207080912010c0e190506120603210702010302130905040f03 63
    0x400f50a02401894040f00160004000181c1150400f4001e100c1103400d0300d500095405c01107141c10030400c0c4142448400c0d41e4413100040b10300c030185000e1003400c81202c1101031860000506406500e014a01403903890040c4210301e15411010b441c104280019281c1c0c07590345a0a02c031f0800c03684081644a40981d07030205008074061041142102d600901c407000d010360703c2d041000042001403100d5002240d40550368502d6a80c1e030006445000b844c0c80c0000c01074140200030b5554084031612000d100001d01d000742d20b00b0010400244e03000079840010801340341c82d0328100e04100c00010801c4800002195040c108400d05020340b80e4504240d50b0074103081c00c401481401e851251085001140c0120101d4a55040c94805061070000040e005d0b286550340f040451841d501c500d09207000c4040c07503028410145828094000e4041102080140703464170b40403c110b031481910700003818154001250355950003810901c60041001f40d000704aa8501801c00c02012007140008900142c10002c40c0d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 532886312 1250 532885062 532885139
    0xe01020c0f1906020304020a030f03080403110c0307050411160302070608150607060504021c0602030a050c030402012715020607081f0501030b04021213050c0405010e0601051309020301 81
    0x291402c2e00d0848901e00000780c3d00d0307410003980040c00c1a80c002d542c4003004800f183c001c0e012840c54038803a6966898500e82800d0041c0003e1400b6912131241e0072040c058002a600000c4010944004035000611a407a101580e40503204003124040d501d2040340344103003815004103291003200c8c1291265403156071418040c0a00c0c4c00400d003050303440b00c0c05114540c00f06a00d540529842480645402c0303420b421405040589941c02e80d0480d102c0b500001004504a001c0c095150416800644d15085042560001c0c0248041d0440700a09081c0d51110300e101014840c142c07001400400c444961055200318000c0d210305c030403550400400c8455002c2445c0c17034000400b0030141103200c40c8101400d41001c00450141c41032500180e03221741c0030b005d50b203400c5070301000c1c030ba01845150441c20300baa1844c2c0b070450b0902d0b1420718298812440c001c0100001c40351407900039441102440e119031b54200e03250a1704280d4890340c011f40b481c1880440007203020383ea401450007642e031418003801274206415408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 532887562 1250 532886312 532886323
    0x3050901020310030f2a05040b120613110a09020d150302010e04021e040b03090609010b0d02010318051002031909050309040c09030f080a080a14010e0601120e01020c0f 74
    0x2400500b031603801003080803880f25181401e24512494009890106e0441075009150100d50b14500d0004580e20410043c60140f040400c11001901c1c41c40b21030034103d103190303103da4004140f00f407000442460324040161000ca144c0e1000f4000741080f05d013507100c81c2280001d4008600c040c003883c2ca40f101c0c680c0445940218041201e9050f5504602c249100301484065080f010500100c00c00c1d4a0310768400381e21040141028040e40c040c0340b0380328036001d0708142c0342003030141140241ea454144541ca20303403110b46900754555020b00b40860202c140702820108000711010203040c50040b00038400e6a6405a0021070186205900d11101c50581c940c1400131541c2d024002402a4800c12105580b0309141d0001085003000f800c10448890b42d03a1079490312a9410300f07040f5070081000519404454001c000560002c0041504010411540c1c1e10310071001e00c10b00034070120f5200280001e1180c0e100300001d01c1544040707203060110051206880b400303034101000034800760007141c004200000b80080d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 532888812 1250 532887562 532887571
    0x80729070c0c03080a03060e040501090b060603070503010b160206070339110d0206041403010c0e0d0f14010c030902030d05070302070b1c0204062001050112110a0302041407030509010203 82
    0x880b0030703080b032550f55011425402a4400300038543c603040d00003940c10010404a01c544e0250001060f602070314030780200303542e0004040500c2031405209105689378040243c9040d140440b024941e620440741030103203c038404941c000d500c4480000c0c82c10815502074404c0da000c070701c2541c40c28028141d07009540e08100043c24040c3c900c80413408800045032990048082c82d82000c1e02d10052440a07801140c459030040e0403c5800401441034103009040911829440484c64600000405810000681c0c1d078005248007420512004000c0810700c0341e500e00c1ca13032183d08440020050105052000b9000c1c05104130107034803a0040c07124859025004a048070072103507044c0d01030f105241c00c004220b0f11a810401c0040750204c1d000340301c0c06c41060988028009440d50352205400d40d002001c0c1c1e8401500c520503001d80603410000100800c4141024a01c43c5551140c03ca42402e038020001c0f03100603413181c1c40654030a09100f12000e000c00c0b80b00e5950b00a50565400340090390351540c0c46030a0303100685 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 532890062 1250 532888812 532888823
    0xc0c0d0e0f0303030711070501020102030c07061a0402040807140603070e01081e1e06010c02061804020c030409020714070608060f03012a0f1119080729070c 69
    0x1a50411494032a4840c0c0c0d08011004010701180c4015102191a60700304449810214090000140d0810f204003d504007c0c072092009600c2c600c0d0a41084400340521a00103018a44400c1023048002c80e00e1001b00d00303464080d10071511141c2d590182d6503103884921485042454801505c070341400c01c007086a01c1240103480310045400180c004581c0b8010040500c5221184512603081c0100742c1d10865014842e014a65120041880d82100c10600082c100714140300586440760010b0302c07076200740e840c074224801c2c090040c60540004500607105408955442e070100003800300b5040816406000e0213809400000103c86903403000c242d6601182c080c0e00302145c1f11400194441c40c08075452050500054004a03c5c0c0c0c94031008090350f030b800c0401542880318101c100a8505034880d103550000d8000e460081c450341d0002e410207465510041c2425610314543d480881070045c01d104642c22560b0204a14500799007400d80c03040d140c0116070f00c0d080902614404502d00300e2044c164600c0458204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 532891312 1250 532890062 532890073
    0x1090b041a0a020708030705060601080619092c0106060f110a06050a1803200714040209061c06261b0f0409030c0b0c041203030e0a0b010b09090c0c 65
    0x70032003410982040c100542148075615000c41c0d24142800503019441c46500200b14030305003000007401c0b418004190902a420b00c03220031200710030040c800c0701240c502a2000a0030800c0c401c0704105d002010012102e5948402071048400d43d0541c024030072140c49507544048901c42d10400c40b015071406200c5d041d03c2e40101d0324140070804c6a0701081d0403044190000500b04804c02c14103100d041c0302c15050b00864815a50542d044c425160548602c44be80300103045134604003400c1405c00d94450a006004a50118200c142900c4520844281600c00500a18900caa0680c420080c050074041e060b60320780b400e06983d005540f80d10741ca000703e030715030ba001d0a01071044118609101d100c210b83c455205a402403400115100c9100e02e02c032041c000e0380c40f900340d503115041654030b10030040c00e620142c0c10204000c02041041200040c52140d0600c2c02081c5a800405010301e004000800a0881000440001000321001c2d005040c01941a01c4000d001ea4800d4664500381c043c00410302e0054118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 532892562 1250 532891312 532891349
    0xb09030418181502030711120a03091a04080a1d010903030c023c060c0a151112160c0201020304121401020c010c020601080c0d06020703050d091101090b04 68
    0x76421080480c2001440d11070800ea4075110741550b0b802601c12203451581c0002841070325503024041c074444a2240c4024075258042c1c00d0080b001d03210702228002090b40e10302000c801c004044010f240d1040e25101240c8581c00c1a04200310184d00080907400825080e403043c0002450072a8024072011050b100c9040940c1740d0384017520050303e000000c0380d01001e08404840c201801290b141c02c0070fa0710b4020080201807a07040c25110009644101d84200010310094414950010318007a0740ba80c4030320041840700300e880e214405407401900702110600c020070440840e25031481014481c40c4540340140f40d80348140b000303840e1299150f901134010b07003041005204c071880002604e80304030310542c1d00b42e000030b82c010402800c98200018455031651603103424000036504000703050142800501929407181d002000072050080c514001300701c140c001c55201c05141c06541668510469807d0a1000100b20310384031300b012040d82e029a022651042003c900444800b0079901a62890450354404c02803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 532893812 1250 532892562 532892609
    0xe03150604021c02220618181b02010c030c030204080c061608030a1e1a041a1503061207083310030203060703020406020a080c030c0a06021801210e0f070e040b090304 73
    0x12300d031b407030000740c1d685810840c40c40a0034806200c2015031254000901c078034074150000c060b1259007a020041600602040c08100310104112110b83d004482c8640d44200712003899203c140315203000390407210b0110030055000308581105502ca40312080049401c200d01030100c08549420161062225001c10b1041103401c15612102c2902d0302c00182410b1400440300151031140348520041c00032801006000080c10200025408441904003401c0050f003040c580380d5890030720403091009545040c40d01860361101a100602e81c0c940c5000303d07401403402110980c40c80c0780310320003203019102d042c0000780d40c1c41c424401d8800f981c0c050390142001c500b5a44840c0400c5e0040f011454090004004400008a04100385880580b0411000d61106410001940c1e04003e102202e41032005502e0082c0d6900c18000d42e42c02c0301030362003d0004043e42d8140009107001c4c41d4826141c3d0910036120045407281c481c41c400740c03180d03100d0315a00a0556a41e0005501d070700881c4920b00380001d04105036071030800d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 532895062 1250 532893812 532893839
    0x40b0306093114032205040209010f0309030c060e0105160318020f060c1e010b10091e0e0703020d151202100201020d020a030c0e03150604021c02220618 67
    0x41c010f00303400c07003004500611541150b110400d8040c0700c07070920500480184070040e405008240071181181400c5070b410000e0f25810751845040201070b61a03a1510426009084048403150030400800a1904241d0703102c3c0204803c2d108964034221021510715440c1c400e020305110750482d0b4800c440d1005d296420300140c0d04060071a658031081c01d20955040d031a04001e030860f0000d840e42e280400710040d424045c2156070420030389020780c00098100c0b0303200760441486c1044914200c1300c20710540d04603858980301c03509900000304c6050448280a181c9505401428903030810110410203520001b115442c004018860b5180c080212082076000d8545555030600d05085800090303c5c1c10f07000d003280d10890b80404207040c04281c4c0c5046c1c1041141c0e12000700503c54030190014110f04a202c2815129001c00604c1a8031403034000600c42103a241c1d06905034001801c02d40155140d202a0318000c003101d185001900100f0002d410009910744580715820703151409000242d00642040750070311820 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 532896312 1250 532895062 532895161
    0x10e0f042609120717060126011b090515030103050a02010e0d050715091401020604080a18030606090b01020607081302010c1e060b060f180102070b040b030609 70
    0x2501400081c280e43c4481004180f0400c0c0031000d0842c560829011075042c0028040d000300c580e1151005100071112040514401c0700e00500003c480340400780c4040c0074203443c481d6103485041c180314410362241c0110407081515001c8954221030b550368181c2110a0000340b1004d00164440c01c401d0001d540140a01c81c018070001e4801c111540c00d580b6200d1808a603680031001261036401c80c6161a46e0240c2144090304c0c6403010013a01c0703202500000d5450001410161042c1c1000403042d245074040c0c0740d10b40c0c0b111244542907403840d55030f0400707000400b800d1040d0103485080a4041000790302c0800c0c124486c0c515511240b107592156902100e41d61842c400881c140312411600c0001b113080100708242c1c0c40ac0651410000f80598038041c0296070444d2195030090341300b031203540040d0182074107031014100b8001d000749004055100403454003400358859040c20b40300250114989100d24020341c42548140c07003500300c0d901c038800c884075806810081d0b0f9980f1440f24501528000314045076a201e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 532897562 1250 532896312 532896383
    0xa0312030b100c0614060f01110102040f0602060115030501150813060216051e071e0f0609080d05280201060308130311030a05031b030d09060203010e0f04 68
    0x421451a000c900980c81010000b000700d192603040300c08002803800f400f42e50a07110502c180107070601002048540d0602001507040c003048040e802d09000c0d0943c1510000d00380501c10000031642c98501039106c86003800340802c0307009482901ea2001c3d02901403181220703d101c444a8840403500700441f5401340150200d140c0c0304114001d280424001c1c0040e080400c041c920f4003000c9009854490310b44000103100340e134410f90740b04603401d2860001c40c118003110400d00c1551700404012003600c0c1000d107145c1184001c0c1c8039843e80801e405038000354001c02d84d041c600803500081c125a50654090007056520f13003003000d401a40100002410703400c00b140400600000c9051501c070b50360340b5196001400b240c01c12800d007450410521010b041800751064064024003080241c0303071985a100d2281000c0c10580a000104141c0344000800c2111812046440100004043c078640000070354020700c48e02a80c103401201262a444000c82014082c90344034000001d00c0700070101800309034281c80b148200c0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 532898812 1250 532897562 532897571
    0x1703040c0509041a0103030e04290d020d02040608030309060c1305150910050903190f03030e1c03020319051014041508030409060b131a1b0610140a031203 68
    0x4409410741174041e51003500d40407112200c19080c0401c8807011009040381c0842010002091009046c100342481c0d019242c12841c42c00d90f001068440c0c80c0d0800c001e40040c545100000c0c024008030146000d03c8168082d5417072134555100b2411240544090480d0640503c0d0341000b0904d0401c013200100c0c066010010b08000107a000038058224002d0a040800d00000700b601051401b4000d5032180c004d503002c9000c0c01e41c4591070783c0f10409041c610080501d03684030121811264100481e0902030b1202180080708040301c08018069041500c010490b00414240030000300154010b4911900c0e0507070042400610388000005c5690b2900300e4160040d594030704400c2c41820300c2000602414034180115621880d0203040c0044910300d5010300d40a104c18450329a001d54081036800880341407801c0a00c1204450801111f0307889031b503540c0c119070701070f00d00c0300c40300350001064662107032401011204145983c0d044218003c411940c0841c2c2c020179402e41480014821603c807503c14104c0c1c0743c0080e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532900062 1250 532898812 532898843
    0xb0603160c031103032a0703091a04170a03030b01030635250605040e0c0903010f0c03090201030c09120303021e040324110906071a010f031703040c050904 68
    0x1400c61744162010007455020b0441203051071a44101503511010035503981c0c0c5402c80d551030017403840303040c0c0c040c1c1f020102ca4400c9085503582c860050b80c01403c502c08010481c284e18411a50b80d410740381c45c040700402d060843c07005141d8000d200305004c070707000285048000040d100450706070294541101d8400943c45d1900035010780100500049030140c1170005041c0e1695402d0900c140f1081d40c8003404020040009202c10f40601c10b01a410210b100c1d41140c0320b540940009003d0250400c1c4803410030301d8080300c441025071540014031014000e07207080120380900d0000f19001c2440d40039801058503c10400000607119900901150b130500460040090522020303403a01d6000340d00681d0801013030313481d0400159080038860781210408a040140f80042c100c0c4041c2e034001d03000030b81c0c810303600814958103112103910070281c0040961509003e942e1541c1d6004207002850006a2304040310007a000c0050b00a24101d0b0302454201c404d090205103008104452020014001c5809500c0e608602 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532901312 1250 532900062 532900097
    0x1515010210110a1e2001020706050a0b09070c39080102040807060c110f010e0405190f0b033003010303081605070b010e0c040302030f060103060b0603160c03 69
    0x26035140e602e07041440e911150368000a112540c041025000b60b0702e0344518021041d04455101521028507040c860050f0256031094020b014140c0060000e40c00c001c1080030524059010122000c011241c8034495110844100c80c05184008020110b904002c100079042c0f54410703c000e40300f40c04441e031250028480f45001e8403040294400c480607034001c142400401014464a0050070300740c5807500c200301c15601c0c0c9a51100c103203420203004424039002500140d100c0e8500020f00c000c090701c14000c9040101c0c071341d03040c64560070201002901c0c0450076144c29801d409a03407614040180108407504492206400000e0750540709011a0142480e0144000c0450040c5001314002e4a9881140c5013515910000b0101d0112480c03c000c004c01241d000154844640c606403003030300d6480c6415903504134501400d0b22541d00042e5140c401e445906c9813010001510701d040c3c3c0e01c1044203210b2150b00005200751070100b529009001e020003851001110b02c1803040c030510304c1c0039107008440c00350204c040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532902562 1250 532901312 532901321
    0x103140a15022805040b03180a050a0203121206092509140609010f0819020414030c01050c030313030c0c120b0601021605011b0b010b0d05091515010210 67
    0x203101245801090407500882e150100500c16440f5841c0c12503c0414044010701e2840340740a04402240080089148007c0c0301c0507445400006c00115141030b419030604607519280441c00b2031003803058040c1102e65080e180d06a840480b28070000800c0b030f445400c02c2201c1481b0042c28002c003405041107011289020b6100001032903403a0b2643c0480b2350030702940c05220022142c1c0c840c001d020802c1201c0d107036603202003260702103070083c9802441d42c1c64400101c200441d12403041007080d40081000b165041000c00100180d4104a08642414082800546d890300540301c0c1100c25400c01d00005613001001040018a24400e141034860b11149a0303502c071703100005801c60001070212820007403c200620344903e401078024002481c3c04180d6007898000201e403405114100100d400d42c101c004c080c0b40b16245c81941d8000d000c084990303100d902c0181240c101012a4400c20b0070440803c1000c500801c1d10030183d12000404680d0f41e45600c40005a07034007800080c0d0462144150340d81241e070a500c40c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532903812 1250 532902562 532902593
    0x30412091a071e0c0801050601030c051804110427061a0703020709151401210c0c020411220509060f01120e070501020d08160e12060708041e0b0103140a 67
    0x1391040c4604184500d0b08450b4000c22840c1418608400b442401d030b0044143c1e15007242006404403030101c0000800c1c00b41c84440141c4116000114020176105103007400e100890704820491405406d00061401c103482151044110f00380075004d0650160030b841c40106000c034000d004540486580385e0404084403603904840171000f130108010702c280310038144000c40602003481d20810b03140060711180c9400002c962070740d42c0b0555034015407040c0d1340202101d03040319400034020050b0042000c0e080f1186c1d80b01445100e10381c1580c0c80158180790005041c0307401d0303581c017a107003010301d41e03400381880800b4190a4942d030601c03241128030f12450030a405240b12074180070003d0407015252070000780c6040305a000c401c0034082100708009041c81c81100601d10791400d4502a840e01e850708010409044903026400882d0044d4420400e0468000041c076000781d01c070390f603949205100e0070001406008a03603801400c15800800410101e850450b2901c0b42e03007121b400f0707204a078985036130300017054200fa81d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532905062 1250 532903812 532903823
    0x5070e0703020702040b181819050102071103070602030421050f0708060c0903031213081b060f160e030c030706030519180f0f0b070203030412091a071e 67
    0x10321002181403a01500f5054a01070380e8000142103424141e0001c060008e08503036050640d406511f0001da0100701090b440828034a21a0400415080060107940845425a2284182c04075100c2c0d6080001d50700080300d078558059400c140c00c0096410284018220040c003901900f101600400c00600c24040701c0841c6000801d00c8a10f40300180c5d0620100524044100c582444040b000d52008401c8407414020314001c0e0a20b6035030302540c52000d065201002e840010040f503203007040c010750046000c81240c1d03030b000c5a00582c1e540034112402e85007103580004003100303c0c48040d25203001302c000c1010f1800c01811b07240c080d1206004a8078103801039001d500047d4440042c002407d00711601c5003c4200d8848050204443c0d5031000c0200e02c410741d40c010012042190343c45c0034030220681c000c0c011036110000c10854100306500170740c2c83e001900d00740c40c000030b00890b02810901458207401140c003a44408a4400c80010960b926500b020200340d40d034804c01c10380048010f0180882844061051 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532906312 1250 532905062 532905067
    0xc030429090708160b0f1303140f01020901090e060a181a0a0f03150f05011202090f01150f0302072111190803090c030111031501170c0705070e070302 66
    0x4203000c0c544502e40d4401c840503001440e014145003030f20903ca4080e41c040d00044c9030740740501068030100d03205406260b00316848240c80803041003030300d40c0f008030403052940c03c07200d05000c00002c4c03500701e100e880c10f5103002c41c651803020803a140c2e4209607a0750003c001041c0c00c40050352140e00c158501c0080300080300c0c0c03d54404400b5442c68903c0c0c19441d016400b83c4490381c0703050070450300b882a1602800003504006004510103105917203a08a02e1160a915400740502e5070b4805040c0303600749401c401244180300c25000950303401c80d49203140b070407112080c600c10407000410206403418602d40412a040680820048001c2545101c21407034281c000308035051032001e500c800500012000390f02c0485a046030220713007c108209022814810f4101e0f88166403a101c4a4540d46415a0603284603059400c01c00c04041c010360306409140f160300c0c03e1f03c2c5140c3c1500184011101c04c0d00f60318417500f07146021008140001014400307000c41d148244110f071b045580f1038140c152403402c110391460000347c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532907562 1250 532906312 532906321
    0x5030405030d0215010e100f0e010501090902031b03180604110f06030c030109020901051c06062015040c120503040305010f0b280b0d02040905070509090c030429 71
    0x10414601c0c103031281e03c098004400c1c284000b88001c2c6041c86003001e40314002d4082045032611141c29001449040342405400b9030350032001d00300d00e2003442514041076038068006144400c900840e403242d00343c103201c0f102524010720080f000d904090300000084202030301080d1600381c1008258015802039101e020b80c0c0410100700f103140c800b10080349008150600c00e0114601038101a0307410341d0407032803026071555402c00040f035071030080c210101380e8005119003000e04900681d00850030f41d0b100d5641c40c0803100204094050714208218407002e9a070090307400d9951030f100c0b4602543c115102e600154200d59550750303842621001c0030380665041d000040d042042000034428241040c40301c0400740002020070700051044290440c801c442507244050042c1d00c0310018501c00041d20910103459121b9658005190003500a03000381c4507214900008214100d015109461750030300d0007003c04800350740b8044c0414060f007000c2c004907209400c5040c20b001d02c41d00820104035516040110104910b0b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532908812 1250 532907562 532907569
    0x30804230705031c0f110a02090103030e0108150a030b0c1308030c0d090302100e01030e01051503010b0406080303061c0611210c04052701081e0d0e0904031b05030405 73
    0x9004c01e014103086840b031402150150040e00540c0c1c000100e080580d1911a10108941401f0109030003c1d4081c4003880084105600b01d0003084542c4ca0030383c0e40040d107503507840f07403030350b1099501d519154481841c6104100003105c010341d01d940884004090303410600140c070100c4422400d60842c10454001158034410710b41d04200104404a039841c042a0191964000c505a80781c0000c54108201e100c0c070621202c0d9020b03070402c0c030103840e1043c0200311510b841040044da884801c0f03102c1c0c2c0309500701749521040745440d0040710190f81086001e1481c5480d106c0c10040030007844521b00c10910401d10101d004600c0d45c0c41801b62881d61100c040c0e44e2002e14000d2a0054900e600002c0304540640007881080c2c4401d006450940c0c10694001200502d20002c50b81103100100070040040300b8200003060a1102040c000712035180018105e540000707202940343c43d241010014070000f80b1810184085103081c08085810501034108100401c2420303800c000c03507011740306080d00d042d03200190401c01e505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532910062 1250 532908812 532908823
    0x19090b031603033606032c010e0f03030903090103090f05010c09240e012604290f0a09030e0303310b090609030c0d06051509011203080423070503 64
    0x8920a204400008070603540820070049130113140d08143d03590305900a118210090f41e01c030030b007c0e04040306062600c0040e840c00f07089201c04015241c021020743c4040020000182e034052050400a941440310100c0110b0007031000490a6500d024020452000b182080c4181c00c3c246103d5501c001e00103041000d01e50312041210007030403818541aa50000c115449001000181002d00c1d02c0b100f10041143d4024106072801c80354100310324510148010042c42c0d0425540c0c850300042c1c03407800003c251f8034065117280700300d41c1840382180c050000f94000c512076119001052090030711540c03810102c0e020a00d15081390701c110034070b8120383c1501d0b0710051000f4808022602609600c900c1c586c2020510a4103020707410314240185c1f0040b45401c1559014001414003440c068119440800c1d02d08060010b000300f0b0302c16960100001c203040146040100015060b1442d02130350359081070203503a04460682c402480ac6e01c1060b2241003035100c240160440b9100c2035402c1000300702e117a0510040600b0310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532911312 1250 532910062 532910117
    0xf03060b01081008210405031203060310050f1b0417060714090f091306090f060c08160c1502041203020f01090201080f0907030203060a050a0b19090b03160303 70
    0x10300e0464400c000484000a0383c01d011030446014039140101c1000d1704c0300c1402141c00095050213a00d450f86100710040000c1c62181c4011001c60b1a9003140c54440c404807041605c00d40c801c046280000b0b400c0160080c040c850590050711030324901540c42d0200c9030740030a03420740a001a08064288550540c0c0b140031400303d1043c140703850303250020210000368003401c07664145002e214440300291a044041e11060781c2c01cfe0b0801d41c00c0c84607040a10380800a03001c4003004480c840d1074080340d420b1444c81142c24522806401e0300c28a211401c50030b00f0782e1089840c0b20101c2e521b6034403141a001d940c1c0c039400580010903050071030181d602c4451601900b000800200404168034140c1c030341c405030fa4000c03030003500482141454a100e4907420f03959824143d4980001e50103101d541e0900030940f41590045108078141c001c00c01a083c200b904100d404004072111392044030150b4000c0c01f4030000ca502c0001d04440080881f0b1000c0c610b800e2901c0d04e0782c40303070b4000d030082007110400090351089121101140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532912562 1250 532911312 532911331
    0xb01060e011107120c031205031f080607080a090c03050c10030b1f0909110712031829130506060108070504090209011b1101030c020c0109050d0201090f03060b0108 72
    0x2c403814610341e646a07004d01c81c5000c81c401c9210078000b13102c1c03040d0b4038501943d0450003480301c14200c050042d02c2940300340c3d02013000842c40c106210070000000d100c901550b8806002d4480f68803000c2c0300311030b4000094110422540c6d2001003400280110b00c0f10401588a14003908001200a08200350700d1414040d8a003454113040d0b000728150f8401c400c16150307103140c01d00c3c00c01068030160125a150301540058011070b107041c41e4241c030712a50b9406414014404d5034a8203800000140c00c82c00d4620f2207620f007e0800740c01107608005440e000c05203903030440c01a030385e0803003030114000803104038019154900f000c09c2e03060004061000a0000035400704080c200700758141000d01c0024018403c2c1d02c191840c1c7c1d40c2c04140e2160701c2c0c1c441c00c07143c00d512107100355031985840141464500b44501e120400c1c04245843c0c81442214008070700d0340280b4070140c49d90581e0307500d05014064984031054040781081401e100c04528426158800300180d400b0700b1000941c0740780755001405008003d000e2351007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532913669 1107 532912562 532912577
    0x901021c06300303050c09180f181905010b0604141906140309151602070605070c0b0d0e030c0a0204051003021f0e0d0b01060e01 57
    0xb996141204004480c90b1106121400300389200b0402d911030801c42e07036001080c02030748132030750294605072158903005a070800903c0312810001d02003400500c0d10144100450750391030308c6a01103444050b9008002c085400e441c0d4455100c0300c0e0400000303180f54103104100080d080010350410140803640c4841d01d5031364684201c10350141d4180035111504032050000d04402906c0b0441d8000e44030b001d070600c01c40d03d00f420a036000400c0c0d1149441003003000c1d1820140d440c01c070341c80b074011580340101407050740034007e0600c1c3d1154008030402002344011004a1103034100c000c102c48544150983c0c1b1402c140d2140301514802d0b0040c003540c040410901c0145101050b05804541300301e41c00c1003e95100707d0385880070302240c080a900603100b0000100940c120409400603c0c03890b0608030102071780f82000034041800c0c2e03407044411868080040041c0c64110405000b501000d080210 = true := by decide +kernel

theorem cover : BRFrame.Cov 532733812 532913669 := by
  have h0 := BRFrame.cov_init 532733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532733812 ≤ n) (h2 : n < 532913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
