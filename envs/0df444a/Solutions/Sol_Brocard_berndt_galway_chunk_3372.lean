-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:24.251674+00:00
-- url     : https://prove2.me/submissions/097f1c9c-748d-4641-ad17-e6216cb30c83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 606294964 ≤ n < 606474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 606296214 1250 606294964 606294989
    0x81509011406030717090a0c06050702090105010819050405030c0613030221092d010504030b0a0e03040b0307030e01140601021c0e04020a090504050c03090709090206091c020a 77
    0x1210344180841e4900122007a24101d44a40350000290303590f200000b050914144680104266000000354001c0214083c0c250203000c1c90303c0320811142407103180f10194104802200400c4554420413600d540701341440c4c002d000d50300042d4280d0b0b09032081a50140c4407a40007144504801c8018481c240d040b01d8041040c1c8000b14107550041d446039482d001c0d480c520302810100300c100d0038961084410501000f4400c00d104130b01141e01c186171303816144056071070511410702e030050b65000ea400c0303034240e81d004001528035076030700348407500030b00440d08104071540424840002c18460000166000c1c203d42c2d10045a014070300f090050071103201a400b004000b440c0014040c19903008285214401010744c00d03100c0c800602e500645034440c3d102c0c8030380d8002d4400107030742ea01036600662031000d45004541c180069210801003802a01040d00d0410440c1c0083d0ba04000c1c0c891903038011810140302401003070400c0038101c0002d51072140000030f00b040d402202c00c000c0071407900402100c0034208410116 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 606297464 1250 606296214 606296219
    0x1b16030c060b1c080306010903060608030c0f0c01021f0b04060b1206031b010f02070e0916120507051009030b0406050a05130503090d05070504060b040e090a0506240405040308150901 80
    0x32400d081c80f007070b8003400104000004c1920750744241f140c60003460f084281403140315511903e076507482d8042c02c0035004501511525501c0a00003041c40308848405038018140900018103041c0310103108252200100c2d41c5001c00b62082e1200e000d104020100e0300c50040d26009030030314103505400c0c000c1c041c81c840e400075a50241c0c218a140d10404100400b0701e8a043e2000c0d20a0041c4d00c1c101c2c00d500451030807813980d42003008004000412030880154003e9041041d580d49120038034003000b0390703c0140740390050748092110b400e091400307510303254840c40c00580c0a6500d0311003040d1460140c030180c4903181c5482c2000842c81d41c071302900ea0004c403205901400c40003103880c0c2503140c1c014040c0e140e00c5001c02a49038000d2140c01c004280142c43e00910801040d661004003000700e43c42441045189071020300000e90a0401160180300180c20901802060340c3d840202e180e01d0102c10744208050b4401c804402d001c1d00d80b440b40c03a2040f4429240d1449a0504c040d26800c0c161106c0702c03151007282c220005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 606298714 1250 606297464 606297499
    0x206061e061209010e1b130e15070215090a1416090c0908030f0c060105060708040b2a07030507170709050408070b04050106030c1a031b16030c060b 65
    0x11110703501c0359080c000b21035407291070820380549030010111400748910380403180d00310015500c0608400040701e00c0c1010840755810a01a10b40b401030501c1690006007e50001e04c0000c002c485c0e00407080d1046d50114412420140700d507080c10b6030300e08102d91011440d48100440311090003041000100200040e58454105943c07201050042e941003a484150f088206409152050301420400050703c1d00c40000301c182c1c3c403054001c08040c8445200d00c1c2c000180038100542100d43c52030300710440702d181c18100071040580b80d0051074800034420412428151641300031170710204a6240c400604005861070030040c1c9000c13643d030090a5410442d0101e241c01007000140c1e081107030110100400d0603903a904003a5414001c800d0090f048a40f040c0811041050640c0001e003030742e111b4841c0d440c50300d840740140c0303d9011001cac0300c0241d07001c4100080b40b003003490b20f4018800300b000071b0f40c0f8914140035220001c4002200b035104030045002004020100061409404150002078078002e001001c200071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 606299964 1250 606298714 606298717
    0x501080a0f020a0f030803040c050a1a030601180b0a02010c02030c100e21040801050a020306060d1e0608010213120230011b0318051c031b0206061e06 66
    0x20040000d00910658000c648075400c03c54010f055903115400d076550740342480309082d40b044a04650a02c81c580e00031805188c05207400041d0b076212545145104000c8440242c90381c000740510781400003040060700c613800d02c4040c41000d01800f03200c940d16101d6440010b800d444101e4a503200b990000e00070403400c070030001403a15643c42540004144064a019018140307404611444400b0382954042a407506a401c020310454100c600200180c2e40c604c4c246200303d010a40703590b913001204014800442c402600a06860b07001c1034070700080030680c0003420040303800643c0200440d9401107404201d04541184800080030f62607800020741915034005101314081302e1451a03140301444005282050008034003910b002200700070081d080146442c8a40f00d2804e40900f0002810556503248070307580543c0c0e00c8401c90744034000300203d00034941d1650510040648440c02c2541c3c0d244109848820a80c0000100c205600500a9410b10b141070000440b0411152080464406054a041d880c0c060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 606301214 1250 606299964 606299983
    0x2060d020a0219122a0606150c2018070201051f05030703030809030f070302010f2f030712060f0e07080f06131b0914120604060203070306050306040503031603050108 73
    0x19103030803540102c0380c116410b17060744940070b00c03041811100b6900b041083c0e40000180d0b41031141e40144008510400c03542c098101a000302510300b45c50b040703040242841441745140c02c004003000c00314030311107020600821003121032030700603034480090100c007031034070588120640144144014040e05040100e503844031584401010006242c000801c841028410385030301d0004541e04135650265070034001e010b0440c24428462007803030034800300c90384141580c2c5080440d104402e414080351081608042e1900010854414808030105008590f203c038030824000d003034924031500669080c0060740031802d000500000600c00c00c54207020812000d100d103554807083c101d50307d450401008508201800004400011a00c01a40040c24454001e0902d805130b03420301c40c0020501c14100100101d00100d00716200c0d09802480111300810f01e607070000c41e409807482c01d0101d60700d690b40020030324045048505030751a070000700c284141140f4031100740b00e183d1030900c0c0500c0745504000031503440301c8040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 606302464 1250 606301214 606301217
    0x70302030c1e0306180606091905040516030501020c100e1509120c1c02160603051f121a0124021507030b01030b060412080c0a02060d020a021912 64
    0x5041c40c2c0c8114110a542159802500340c450500744114440480c1030513040040041c00703428005012814030410301845288100d8564002c0c5002d02c2488000f080090029201c3c0c0c001e1151171310450301c0160144c40154451000180d642005562460625100d400c01c030b02e06c00e06041c64a20038040000c3d102c481b42142c842004559100c00c0b1320780e403608008060800b541040811000c0412202246905c002103031921820500a41000220307190807507000070700f0f800d0289007070510525210350700c26903000e0048240001001e0203e03403187c0c0200380350360203030a8114808107500700b04480303402c160f01c0e90f5101100c185655414043c0210404065110a40d106141500045a881d100300440288003240c1c1d05002521f0420715001000741a2501180e804281041c264020600709042110200d0704032200d409440801595281025031016401000390701c43c2c4442c80000d40c1e81e5000428911003d00401a80e8020014000e0304107001032032115034007aa075106000209018020410501405e07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 606303714 1250 606302464 606302479
    0x20405010b160b0a0209151213050706120b060712021509070b0a0e09101419060f02030d050f06150304150f270204050c0316050703030621060509070302030c 69
    0x703682400d0000e01032441b80b194800100310811640d4401c1d00000c11094000c901c2d140941d03031b14075205186c61440d814008101d0b42c040c1d9020841e00340704100004410414910100f100c1c0350840020368030f5006842c0a613070810500003218011501046140b1003008a038580101a1928000d440d40740c4025100c0e952481e07400003588880c1e588200700c40c45940c50000e0200b08107050560f688888100903001b0140c407080d0031016408285000c00b555282d440352003011003521810102c007251040049400541507120034410714a1190031801414415041c003400c001c0540340c0b0008003c94038800c0e2080382e030507040800602011a15070a1444085040c4c0c0c0e0300410000b4000c44600010032861600d1180f0000380d401e440f0807060768042e07402c41d49008842c00e101039158200104100e21059a8080306200c9604402c40302c81e0240004d080254002c6c10001106543ca4504240c2032400c0000c580b0300700782d5804400100b10b114480c280c1c001c003890004141aa083d0b84c0465582c41c03a003040e5a10508031b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 606304964 1250 606303714 606303721
    0xf0207031703151c021c020a03110a05210d0504120b07091502071707050120070902030903072f040b03010905030a020d09051009060f140406020703020405010b160b 72
    0x281854062490006040807031250513010a11a41d16100207080307102e950304800f0b00460390518402486003a4000b0109102c90746184e5032241038540364500d0a401480c10917000070703a6070740e440310940803204d001c044181004d2500904d90030300302d441c020841405414002031061960003540300c1e540542c0302c0c11451060b02c5005040c1c03401c480c56070141180d07819034550b2038401c2c0e50111380c2e80200c0c0c3d4040c202c5007100e41641c44081d1151594002c03980000ca00003188400481c4410100d0b140900c280d00f90f50815803242c0d0520140e92080725401c680e90700006030031041081225074854000300140c0701800b000c00000c0424000503403032200301d1203140c440d002004280c0c1d080d0301c000541c0e60b06c00c08680e0f50b00f031846006500c4090503038415022139544a00041e4508000b0030700b610208c40d0b55150803002c4c0c2030000039a064022054241c080012044c02c2c086509c5a00c0c1c001c0c40075100fa60002e02d003441c034600c100015a0701c141c11440c0c2c0341c001031010b1b800f00a244065001010781c80081802a0756 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 606306214 1250 606304964 606304981
    0x40c0b0a030608190318050d1e050a03030903020609060103110f040213030f17031b03130f0c050a08030906030a0b030a05060109090c27200301150f0207031703 70
    0x700c9410850070f900403164105000d1140d0702000310124800c0d2140e4490242c03035400000d07001840d00c14a0f8200c4480340d44640003d50006a080003129420440c504800361515101c1c54013072005000c9002c030343d032545090181a01000700b640d00c120494007c040660440e0751ba81e01c0154600c094a0045680002c2105990b8468055400030880c100004030784c10303035900701000601d080d50415240f002d040001c0e5060740020700100d910541c03184a0f014024039200200180f1584003d1418000361546c507001d0000615100c6021a468012982c50100c0c90600f07080040030701030782c0c0c403540311541b08000c600300d9500c401d810340341d00c16409070303001852403c01800b007400d20000c1d01008245029a2001141c0181036601c000d52141c0140e66005281c3e88401c400c41101e4007170510103c0490038508041c81d01c20880d0040308010321541140d0a030340e64070104040f0b0541080c0c010415000790713003803042c903050340c440c0c0c1217045d803200c5100074500309113035403144594440801d01242100c0000000103d504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 606307464 1250 606306214 606306221
    0x60e0a05010906021e040f0e04020a030f0302151f05060d201e2104080c07060806040e010c09060302030a2a0206070f0509041505150d0c08040c0b0a03 66
    0x680c010009100c500304602d0084000c0d0f1205851800b0290003811100355800100142c40549207500c4041c40803506142d02d80d45000c0d001032040740d121081050100004291140f0f55107210f03c01d80040041004040c048401d101c8024625800c86000c0c00e4044180354442e4101803c1340c0b0240c924a5444103481460005803070003c1d1242e4403100c20580c1401d12009950003003c100c40c600810504208013020038040c4e900c1101c010300b4501c02111004101107490000d241d070494800d00d41a841d1a0400e03a081d810700010ba8020400700700c8041c10010542410301840046031100d00080040c0c1c010030302c000e400000c0758080c04040580c04000201902d08682c0103a061114500b01c191010718106802c02600041e90079880c010f0103080085000030f130090480701000000c0b601c6007410715005030144401443d8441402c11205e070070b000c0003e203907150950440000b043c0720300300981e40d40301a030341030b419603010103104400c222100701000701046e04607442409442202140942e03580512808a010307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 606308714 1250 606307464 606307483
    0x90d0e0303091c0302060f190c120c090905060603060105030c0a09030501090b0414370611040815150402031e07091e080709050c0708070b2e03060e 65
    0x40403c60b408020a003550900d84640da1081c0e0032071b41143c0d04d40c40c0713a0304141d80655034403400e0740800c0c40510f07101800d80c00181090240349019201c0d1001101440c0548840200f040003151911000703200500b1039010f0103500500c143d034000d00d18113101000070098403004288481803000440d84208142c8202c5200e40115040301c001d000392005414454803000b0159000c5440b0300410b41d045240b07880100d0388000681410010101c160007011010b41510101559142c08928204420b00000ea0f28483d1055410701c0700c903056260f42c10540360f589070140e98004104289004420055140c0340007d556813108415500580c981e01c411041c0b6194840c85107400c2c811007850740030030110561142d0140100c0e60807513001044408034410b82e02c6030640300c0c05039400541000800348040d601da0703013000b81c200a4001d201031400c2c0060b1542c0c101c076001074100320741c00c800000502460320162006c1c49412440090a0404003100380c1c0c1107108110b035440000c000a868641c12400b40d0303818001104c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 606309964 1250 606308714 606308719
    0x170a170714101a0904020109031203090b10090b010504030b070c32060615030f040503040f15031506051207020c060c06010f080a030503041403040f14100503090d0e030309 75
    0xd1542042c40240301510070038655482e840c400c840881d4003442c02c184054055901a15200c0d42c1d1401c549600024100b4030ba26042416262401a80001c07400c81c3e0487c4106001080400702c0790400b0140c20a03070342c9600400341040f20502041c004a00c070032401b83c3d04a45581030071800c0d000b480ca0840c86043c604083c819400c185201e41100700340710b51858030301074607044094039483e41e100d00030805240070141c1c0341d010a44041c80003078107013440955582d80050045007101c0c200303544d804100d03a440c02142c0040b07260780394009a14400c00e8041c01014030350141500c442443c10f091201c001c0243c0114540c0442440310031011039056802800b12201344640030300610b544031402c0e002e481e5a0030080c4034121685403000e00010b80c0389070115000380c41d01e07899035605245440d10307201d07040080720b43c00c04030455010800000901016100c41980104040c2d040780078410003200801078244401d80708034040c00010410481013050100d4142c04a0583c1d050003008030300203101003032070340c0030340603800b034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 606311214 1250 606309964 606309973
    0x311030319051c06090902090a05070c020613050a270c080412031104060e13110304121115040b060a050102030f0d200717070b01090c02030d15170a170714 68
    0x55411817079008001c55038002c1d200003411344c503400d00403001c45130100c03902400036449082040043c81d01c2001005000e80318214400c40980b07400010389003074950342c014601d0903a228200700e03904032000c0240b4007280450508004203500e140000c0c0c1000c20080000b40a10800d0001c5a21a4000c3d80000c071007080d00ca084a03120760f1548409003103048007000c40c1384103250b608102090410540038101c80d240208000751b0450301c1d0307550303040c00070301d0310100410034000c6841b08500703441c60030802076401050314100307080c031400d10f424003401c6141302800440c002c0b402d145083c40f8590b000822070b0304840080d2021560b5011b014031703040091440d609441c0c20281d40c0d4104501c0400c0ca80c1c042d1407110302989154002400c41e0785030301400e1058a000400c00c1c03400b05c004021502d0b1a41c030000700042140140ca00c1d055100c04000119518102c01c3e08081494800500a8050250010744243c9404004154140d1603840c1c280c40b00c800c10211130750356100000e03104100030b5010030000f80c2000a00484 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 606312464 1250 606311214 606311219
    0x40314070507060f020106080f071e08032808101503110318071203120209060d150806090a030c12022d0c09150d0203011509060311030319051c06 64
    0x5000d0442c555008005601f440804515880003159400c65540d84c24001c1c1042c40c90b140e4009400c40220b01c1d01e80301c3e8294a080000c040364280b0080078981c0603106603417075204002908000f204143d9078080300300070b01c28041280700c5000c119408207a5494904030900b40d0381114044000d0f05249404600380369020040c002c000e0400c8941c01c1c901c8449030b05030350a031038440680240b01c001c26070010700000c0d0f990804ca03602e0b504550040c8a52000504958034241200c0d01a1b010f640446180009640d004030042100e60310a10056400c114590041c2038a13441030303103006103503010a40028001c000b40c03161070491540200410012850200d003600ea1085803800300300302c03c8120302800c5119019a0b203141c0c44d6807405564072403181d0f0410242145248240042c4964141400400c076003565a50f031058511060008411004029901010840398107600c0c09510b03007005c1918440c0031f58414400d403207070210040c01440950703d0524042d07403240c82e0343c49100c8042580c6070010402603c0c2c401702 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 606313714 1250 606312464 606312467
    0x4091b030b1006080c07080a03150b03041506052101140c030a05010602061612140907050a17060615040302271503120f04050307060c0b071704031407050706 69
    0x40e8482d10034006258000760f900c800030b031942d040880380030f0080602001410001038400300a000c0f032400a1800150506103071040004039001608042d20040e004020031080010078a00c8043c041d90482081c8800d91a00c80401d000441e42c0c3c09819615060641901034804254800c003084261151415500d0800c048516003590042d185031150b141440004a1014000030340d981c05901c10190b0300003000c1c01c0c80400c0301e0111500303048402c3c950f12000e1110170007075500d54bc2d44c022401c01002d081120304d400100304030480150720048004800710106090b03210040b5040d0b512a01c113403071002000c82c60300594030051156406c000d5002e645100140007000384100c0700541c512010900b400540c540c0b00340101c003015071540703166156000a01803011018031038045c00750a210035004500b0192208002400d0510076040070002413020b800803800d2102c000011500100305041035100070303100e041640c4414900400c06014002e80301c3c1201a601800747c1112030668006081ea601a9110f900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 606314964 1250 606313714 606313733
    0xc0219120506011a030403080a14071107060c1109040f060203041104241a070609080a09060513060e010e0306180609030f180a03080a09061409010e04091b03 69
    0x80a480502ca0080003081d120a006403a030384140c08144c005041d0b03a80e070354040703c0c100e03801001c201020b910b40c0004840c0401c02c410382405503045844480c503800541056926000c80e543c4008104824031040002140b0355040444614206890410485d5203608110400e21200003008000900c004100020302030344914003110580100d03014040c101078030100307440e2031706980b000060081079040b00700022030284211088000490310f0315800c0c10b503103459040880d004c2c02400e8903402c00004042c00e00303952140301b0308007400070b13824401d0504000c10000d4555005d94042c1e0740030b00c00001d0704100e00b07030f00a0481070704a2800a007100c5061521040b02c10a4540140f5806903900c12503010030359008010060f0b503940d150344030180d030800030840b0485042e0b46806075040c0d0803500100e4044081074800f030003809990391039110307680002d160650041c2242c282848080310f075607052001c011244e80c4510b246000046c11a00440e0180c06030410551030394048416000e612810440001085074102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 606316214 1250 606314964 606314999
    0x300603082b050c090108060f1903060b09130f05210a17090a021e03011d06010b070b070807030608100b13090c0303050c030c1209120109050601060c0219 67
    0x602250024031240320001039030b000351001c081c0000c040c0002d6215500c10501c080c3d20090003454002c106038039602140520403810522046012400c1c0c00b4810b1103210300460311105010340f6502503529161044070f140011441c0020500c600c04e1600d4420310400300000c038003404040b0000b21322450f90030340c40ca165502858070302011130682140810a030701d03420030544c80b44a0000c0602802d0300e581c1e080008003210840020040c500301d000e150300b6a2000d1040041c582c5040380c04864119001d0810b52404c54140c3c441132005400704800340015500001c0d141d04044941825940d58603494015009000706400c40180ca1041c0ca0141c18543d619410800100e6000d40d8a80c1799070281e00d4801c02a00d00740701c0302400c003001803141040080e115000a01043c4150002e503030904040c01c00841c00c0c0001c0c0c0c40003050307030140811039912900d80000c03415080740c450701c001c000902c0d00e5039490351034080512032001032269440001040d9187d10f000f0391121a0040307a140101c41d12012800b5a020120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 606317464 1250 606316214 606316267
    0x150604060504080d03060e010b0f040b0c07080f1906050601050d090507091103012115180c0504051e150603040c1406040f05040504030c05010c11010c30060308 70
    0x980c05a004c240c06842200e056920301071a00300a0ba0810b02d15840c140d12000000003000340400c000211070918070080c042010241c005000014505400c940c40c28100c60007003016500240704401c0c88051140e08412510f40c008404207190755100016103903800740c0301d03d0b8059107041c44101d60800402040c0b201c00d0303442020040109989904100c001c5000900410400c03d140f29805403d80003440342c1858075134440d82c0111100441400c4040c242c0340d00c0920b94203444020981d0008200c0100900000342c00203075010000e514001c100802003001c60502c2c0c294000079000403400101c0d121110034080c20b0090b100664a052610781071076a04c1c00c41c46503001009045108036440e11301130307084600300c488120b203e1008900746400c0100a210107030045003802040d01352200091020b0080001c2850703d038441c0500760700c0d4002c440e4292403402213a642001a10800c0010120385403480311040020301000311442810140750000420840c0c1016049120200d500c650441c0c02c12a40d440d415401c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 606318714 1250 606317464 606317473
    0xa05010507020f0a080706061d01060e011e0305072c0a09060302010807030507170f16050a1409060c010509070602010c020606011713080c010212150d0b15060406050408 74
    0x115078080741c840200001c085070030342110544201050018028240090003039a00246480c0e0b01c084845613120380060345010070301c00c2c0004109064021201c850b1103602800c207088800751000202080c2e0880a1440702419511400708200522882c581c410f03040c1d03541c0c0741c40540c1c540d01040c2d11400f014541300c00d11584546001281d9454580282c1040703a07030607140e4a035142c5400c0426000307844000c007003404015032180a00c09181801000b10301458014a6038501424003114003034040020605034070034424100000e0707a103160b000e548600300894103034005460358410000100e42e40b14501201041c0e40c00c050500168000c04103040c03044503034035002006074035541282640c40f2441102c1c4203001c1202e000d10203815218a200e040d520038070001512603941900c0d42e40b0301c5642c102001d03100140c0c0d404115419240d14081480c0e800421144185c41034104400c0080c68850b40444010714410b11403010505600811305024006031006100548454450034028901d070070500c10b44460303114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 606319964 1250 606318714 606318721
    0xf171303050111090603180a1a0f0703141801020c0a0c15020d0e21070308040f17100902062701120c08041403040918052406040c0e120a050105 63
    0x2108003280c9680070045c00880c25980d410403c0821855203140c0e5840a01828207114000b070540303c920548462604001d044c0341c106243d60b00c0c813090008108070709245c075002034a1450480309004650103500094040000c0e807400301800d0281c0203400091925111705a2407808100701c030038844050710314280708840c010428101c100d07070345c1c403a903010180440c040c0b117200203090900032005246281c02a4050600440c80300301140751132210780c810ba03441030002c0b4091108013002c00000f0018618401c00c82030f0690803089040d2150f0340e0600d0380102c3d66440e9501d000b151a00320035500ca0020712041440d118903415100c2c84180d4000e4201800142c134442b454445e40301a10488088504039618085030b07580c2d030341e600a4041040c4002d01c00d9844140800514034030f5170f01800c01102c855402c1c0c0341c3d0078640740c41c02514184040c0060341804c071409105803401d88042c008550300c030000301d6000c290726040c210159840c0d8030780055507030400502051844444400508001d281748240002c01a40d41d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 606321214 1250 606319964 606319991
    0xa0512030624072d0f081603030507030c0201060b0f0d090c03050307060b0402031303080a1e0b0415060c0f15020406030212062b05031909060306050f0a030f1713030501 74
    0xe0a0703c01103013881c1540c41e4041c0410740130302410060303c0c4038501483c50b104100030310815561003024100c000940390010002000c1d410b005508041001c1d0000703200c04e50070013041c0e8116000b41b42604e025490042000c1481555a030448a1415008090005d250f0380b40c0c14426126071184200342c1e4000d080480100721f40c2401c1c82124464003c14195242015090b54100d50301c0801030325052411361200d110201140d4500c102c0035800c80c4112000902030758180c140010713543d0072a5031040c02004608104600340d0407180c42e04c00c0c10f07405240b018010009141011002440701c003c181d0713091002c2000700ea1941c055005101c51242a03a0007a0159a10010440c2081c2d18a00400c8118a500e501c1d03204241d4400d0522000c9200300c0c2628180b05142404040032500300c1ca400c000510080740400415805100e131001820b000e681d408141c2e44138102103100101709100040155041c010000144041c00c0c9181c10303840555003c07599540f03484042031a00d024280025540c0e0b520344900440c064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 606322464 1250 606321214 606321263
    0x91e070f06050f181206090a0516150c06090602030c09092401030b04060e130c090b0a0302010e0d0204090b0a0b06090d030c0f0f0813080a051203062407 67
    0x1040c620f20b2030850410203c52500c49a410b025800000050003001c4404080c4030786807103424200300401c5042c159090152809684104401c1080700020092044c6644481c03840410440c07410003005858191602d00e004010307030740015000900c04810b201c0d100ea41140149400700b0120340e80d03603242c4c60301d142d100e8003110001c204440311144a60b6482807035000341c001e0745015000420005500c0c0e641c0c0c00142c40214101c50401100c0e4010b58601c040054200192000d40303186e41c020400410040c01203018407000e800b01074180311101c42030348503031382e0b603140d12100c1d5035405081804036558a01c0c05400501d029a10424a03034180409800d030760500d90b041e12069000240703003000e4094640c03000d5030826071041d4203a40b00400841a2000f14000d049804182441a0700c916500c0021484807a13090501b40c00c41420303a0410100c040100704002102804400000b40455494450200051040701d01c02c0703042554400d040303400401e13000100f0142a64034001c0342600ba2041e04601d04000c0c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 606323714 1250 606322464 606322477
    0xf030a120b0f0f0f06040b0403120f23090411130315020a05160804210b060405250210060602070302030c0907120207020d02040203090d020f24091e070f0605 69
    0x1041c191903030583c6250203018040303034100180c0b01900d0310380c07a03051a01c000c1e0300c103801c10741d003000c8104226000c0c00d87c440d40b0003c1c5c84071286403111203602d46000c100c0642941c02900720701e842002c181a2403e03541c85d0b005914140151078810b503900240c52030b8065100c0c01c0e1105650301d1000d0480c5500800d09402194040c0d0314969602d494200210740ca800d448550395800d51b45040240070108120708a00d0300c1d110080e0380d40b039503404240514503220306015002403580b40541c0c24101400725658070107007104a08031018203103c4c0e0010040340200d103440702c00a1009001d81c1400301c005116900414444280d90003074059400d0044100240040004183c6076580022000105031a0110312507000d0103103d4801016202e00402540018040ea0400e44a610141e0401c50882c0302050301000120007102c8204060640c121501c4840407502c00790020141056000e040024034a0000f03000b840303c6000c4908104034240a04614581d403103c3c1d41c000c40282c034441c500040741040c01102a2400e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 606324964 1250 606323714 606323719
    0x30f0f1a03120a270302100c060b100e0f010327050f03040509070c0302121b010c230a020109080301080619021c0c0c14061005090408090409050f030a120b0f 69
    0xc05658140e66040114510400004c9000003404001030341c0e852548625142c1c141e5904250581604251040713442444840b0b2007004190010012a500a8220401400102d4020a11020480c01a0090000d00f4030103041c80c035171640f1492031a0071880305000a640240103c41c200283c1c03485140e52031255004040e48440f03604001801c0d64840c040d0710300d015100380b06982e42102440c030400a642c11020140410481f0400c004103542424030680c02070300c1c801d18149200118030000190740c2c2411001c1f81e081074000092000c1c1c0300c0d0003504040001544078109603076a41e03441c1542500c0c0c540c01e5a204034002e04030340d402144000c8500030785d01c8500303814a640f8403001200d41c01c0c000170700a8010381d90902100d03c2011010407440008042502c00300341c00340c002441e260304802458003807500424481c1c40007105100106100c00243e5420b0324044c0c038005149015070400502c1c020050340072107418400010011032050744113100d010708082440b000d0082c0e28616040150038040c40c001c0a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 606326214 1250 606324964 606324977
    0x1404051e06100e0403140d02090111060f0c030c0714011b090f050409170c010f0c0c080d02030705040e0a0e06060d081c0605060d14010906080a03030f0f1a03120a 71
    0x7010f00f9410490b16002446400c2c40c014000f030000c1d00c1803080e001040300442c43da5010514805550308031031400c203603810030340280280b0b04d07165130704501101018010500300ca0380800002c03140e031111000c4401144d0405d003402d0240b20b05000440c041d010960024900c03502c042c1da102d02e4540180300702c01c242c4141494442c04a070425051000030100448195000c1145950542d21300043c603005005031214580041400556040a1425903142545003003c00c56441005c01c00300304e610301a10460486201d0159882c1c403401c03022a0b10f401690000480320001d40b090007102d6526500006010500c1d80a4071740c10b50390142000001292842c000d00020410864561010701000440305080e00e0b0980000b1301e107460320b001c0760f080d030040d0019045a550b108010340c0d1040e2801d501500410740040240010303030034009250780780d000e0700c00c005060540b150705035015040d00b6008140320300c000960401202e0440e210101e0100c2c0000c030850300a0058001500710402c14404486941c00755480f02d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 606327464 1250 606326214 606326219
    0xa0b030d091202010309021806010f0905061b0a0b190f0b3f010c0e0409051f09061a01030f0509030405010c0201021926070308010506030a1404051e0610 67
    0x4034000503400c0d0b8201d04040e0baa4100c0001660340031000f01807030011107003c0006152a00024103e9030070000b2802c14442c1000080040fa0384003001c0381c020581e0f05041d21001502c4440903032400441c600000c050907080c90801458040d00914841d5440741c15205001c201d40600c03000d0121440d01d0704042d04040410710725180c5096414407204008900f004980401c11300450742543c103158100c82902a94440c42c008820940c004410344e80020f0482d0100140c00040d0b503007640c1d441c4070581c1e450000042c41d851440608107079003e040c00503041901031281c18030b16800f19030341c41e003010b92490100307140010101005e07182d44079840c45104000c00035480c1c24140b50040d184000024400ca04600c1001d40c550f020071600c0001c0d28403a0710900550704940030505249a048080921407c0524400c1c000c0a010079070040d2003d0458000b07507403080c0e0b00d03100c603821a00500101244072000c0c2219a05200c10040d00092010381c4025040c401424603401c1c1595584503201a506821001c1c10300b00e05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 606328714 1250 606327464 606327479
    0x30e12040501091406120106030e1e030a11161d13020a09020d0209030102070f0201090509070f0f0c050a14011d060a0f090b011203260a092402030a0b030d09 69
    0x41130311000000389054205404c01103c6081041c09030441e00019446450341544d240781041620600050210048011008918000d689000700d00c2c03601c1c104107890315131100310387c010b0081c507140e040b001c058418083d458131801310507101411700b403141005803180000e5984d40454196040e017507004100d80e140d41d1405890780060340100d201843c0302c0b41d0820180400741d80074801440c2082c42a540f0b106041c03c180000361803a16540e0209001d4000c0800700240307181e0009190299290328103081034880f8030b00004aa840e800410b00802c0ca00c1094102800d102d000ca2188007005646070007880740d500c003d8070304090800c290f4140d02c040d901c00c1c804541e03400c0254200d90311003108410000388080d22070b00c80c00405582a40038540b00003601d03207128245648800211042d1450803180303422901161459900750320000c0802148954403c0030408200c940c0da120f40c500030900c003981400e14840c0f84c4500083d8400e40c0d1046110380340c4400e4030301e1800e0105a000e808801a11082c2043d44ac0100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 606329964 1250 606328714 606328739
    0xb041203120f0f0605041a011e030b060c01090c05060f0403030503090a02092502030313110f040c0e01080a09020f010f090f0603020c0d0c0507060c021f030e1204050109 74
    0x1903001c045a103581c41d07120200454800c030b800340e0046400100d45540750400b488200d444035140178062500080000e0382990300b01000030134584c45410302d640403484448045004003d0721000e03503031003040001c404170200d105410001e4001d01074110046c6d490b550707800300000d502c04c15403080c05540b420320041001c280100c000d1544040d079002628100070403030340011000003040745e400e0b03800c0520b641483e01d4182e08002c21401e81d4140d000079490f500388810030071010800003d004002208445084190f130319161044000444068400d0042e2105220040d00c60381c0c10003c29030014403130380c0002d0f14004403405821603c5030003030400c42e0760803109001140c0006842c03d0503014004807200010300302040198100040009070385c0182c0b14846070801c1400e0580d4000480200300340d072032064010130400300c0c210080320114180201d14110342e101080c8405895030f00c8106000c1950615048650590441c01d4400c82e88810340710410f0810b00d90100d6030055004407030016500020a2011034105c98 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 606331214 1250 606329964 606329987
    0xe120313090c172a0d050108160b0304020901090902180a0501080c030606102318010306090510170c0a0e25080c0a0509040903031a06040b09040c090509010e040c0b041203 75
    0x1c154944000c071045070b401e48100784c0c0080a5a03020358038040319000c8507617127440940242021a071450810b078002900013035041c060180c2095440c8150070840d1b4a400e444801c40307100002410091900080d00b6008110900c110901c50040c1904ca040a24002c1481c5200d200028849405c0500a00081301c0070230056000a42c0c003400c0c0e888400c0000c400e507001d0910b50b031030315a541004030b5241000406840169002d140303ca4105002e20602e01d4180c0b400001b5108686400c440d44505501003a2520711000300054000301c21080219000c02400da10034450100844030852240c1001e0741c04040300f0240c00c6a800003610b070b07000701341c008452400800300c180140c680700c6e00380008a8006011501ca5000032030100e959501d28508403407400044088a0100722000d504240c500800c01c4c000d403203401c148501c202d82d02c100310214240a410130b00e02904000d0861800d640e101c41102511400a80d0b00b6640c040c0b00d01c800186c2d1406002c00c503000c3d1140408510740701c24255405651074440b16 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 606332464 1250 606331214 606331291
    0x5040501060b070b0a060e0106021b0105090a0306020c010c11070e19021803010f0213050d0c030602040f06031103040c15111204240e120313090c17 65
    0x101d600103902841c01d000340c41001c0c001d80c400c00c101c0c03d1000c810021543c5c0ca50080f110941c103030300104880c98010030240d580d4805254003500d0400003000485143c481e0001e5664070503202c00b00482170004590141416000030b80081140d0701101000307170f60030003501c808903003036038031011041c00603201c21042d45401003500903041d80344084900e8020241e0b0042e0450460030b0345050070f6401d252400f40240310701e001168008601e0841000d0201d110415507024603401045184460410840701c1002c5100a40c1c01c041c0031501c40d5140c4400c441e414070035100d101c0020b400c000c420702c0003604140c2200e000c0d07548005881402c074580b0b00680d14003844c491030007040c06000d00d11041c0c49601404000c1003442d4210610380c0e50f90500d445e5150f4600c002a4505503210030540c140c000325003040d0891180507003107030110031110400340c01520310b108550300c1480c64054601c00096100e0250004998103c1c507486500c4039201d9260a1031981000f00c401d810494a00b0f12000008072101d602524001d01c0b2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 606333714 1250 606332464 606332471
    0x6050604032d030305160e30030c030406170f0711010e0106170f060405030f03090a0f030f0e03030c0c1e040509030c060106050f0406031104120605040219061205040501 74
    0x48600c0240d600c503204000d0700842e13121010801010024062480b2003250f90504421980d042070100750700218030040d0503945040d001041104880042c0c501800392840030840350388104cad44601030b031203420911400300418414844928005495041140303d0005028001c11684e20910201ca00307046907c105102c0b55603908040300c0c0d089082c00350401410001840000306280c3c001c0e2180f4200c80e181070f112103038101c001407000055000c000c499654511110190310382d218182c0d541d043c0200305200405800b03c0c46601803c240d0018035110904100c3e484108009404000703140c0c0382d104420350711580d070700404280c0e0420700d007070440b0003201075030000300a2082812102107000c481c029106c2c1112684041080050b41c10300300b01090140145252440c02c08900080d4203030540218013400c0e007403640b038001c200c00075080601074400406011844020003445800c2500042c0b1040d10240c0c0113461502c2c0f03218800000039240c9040b00c80d00d40e990b0306401c451f030304440001e050241c4121459500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 606334964 1250 606333714 606333773
    0x20c10030b09040c050a050d0201081308040b0301080601150f0807141b010501152307020103090605180d030b10030902210d2706051b060c0702010e040605060403 71
    0x103418078942e00ca01c0c41204d48180c46801c080c100711a22003181e00c00c178840d4412244050060340d0002116030401c100e4103d080340302c0c050340f0740310030180640e421000040c0b601100018620000181c514100c0f03a003100303a148201c0310081c0071075102da500d50040c0042820840411402c07881000700b00e020360090a11203007044030704000c4210701c554958880aa80e9120001070000d1440e80c10740800d0a26542400d092114000940040650500101c03452415012a030341c0c0540e4000e4000d185050b500030000c11903032521000d00884449404c00700c001c01c1c0f0400340300c03043d07180c0284612a04204006c00ca4221114122421406000941001c03038001000019a1400044502c0c840740c401d14198080c5c01080d01d00800145412240005d521020440c40c80d8031068080300309142054030b043d450402c0d0365440d107018684c9944c001c42c2c41ca079040c0c0302d400c08100034030702240d0285c070049200b44c1e548010541134a08000c15110180500c2d603110008010400004186608040d8049204004ca140281 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 606336214 1250 606334964 606334969
    0x1e10230f0403080a09090213050a230616020603040309031101080c16060908070c051306030206070b06010e150a0201060807080c0f120102040603050402330a090503070b0721020c10030b 81
    0x2c21841c0c00c421001410b0710305120500c0c10f0ac0c12000a40341900e004140343c1486060720840d141d440d1480d5001d0140050f8400f40210803044501401c1d030003810131562402c141c0b47c02071060400d4401920000c071860100c0482d0342c4a400741030b014104011641e41800c0546c1100000d0454400d01224030581d07417440e034000038a01c0c40140c00803074020301d42541203030718040600034512020792002c82c8185c0381000620050f583d28050741c0d51150402c11184981e42e6000058480c40c001384101c540c48422007000020a45070b04000f040b41c07000f154002d2200558900300c1039a40c408500403c400e0303400c1034a0f80b41440c01d02c1410b480c84007500401074030b8401160034616089a0003a04080002500d0390308100035030a0040ca07a0b40b510380c000d906a00e12440c3c0180d6401200c0701c55500300e24008001892074085480b5025110161000034241d418840d51801a640c180d8020325040b00e0303800705413030002603400410b83d4901881034260050007100216804004421546241000078103940c0c0701501e1064 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 606337464 1250 606336214 606336217
    0x10e030d0e1011070b040608091204120c23030c1e0d170c01271e050309060f09040e0105092e06031208060901050f1e10230f0403080a090902 62
    0x5101c61035021b0399503420b1500060400f10010000a4958040d07920070701d040301c040040b1421100d500406201861161074200540341d20350707001064110480c03140c070009038400034800203150000c600300c0d0000403444e02803003042d03800d0305002c030f0903400b0841c244c8000b400c010328081d85d41c0e8070803d543c40035810703c1c01030300090350410b4985085036036603100f0034200e1900c10b9840d151010780c00c1c0d070100380a02890759003c1490010003070b1100810124004101080402c10540d056110300501d81034448042034508003150f004140300510030742c100715000707181c41030601c00e15000d4400d00c400381c0024490b141f2071210110620b500c03c01130f0300301969400d0840130b551040c8030140d4401e80f030100b018074915070000c2940e48060702c102e11500c0403100400699549031040d092040e010360302d5514647c4150201e01d0305525510036a40c00071a00031680398800d40c425015a41601c010314000080d0408081010b002d00400042c56107001c0b00704020300100d815000540403200c440d180030440c01c1d454540c66400d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 606338714 1250 606337464 606337469
    0xc0103091a0405250e0a0e0705030303130b060a05011407030e0a060804031d0a090b0303070503030a0b09010b03130803040f0219061d060a11150f06010e030d0e101107 73
    0x64019035107801190340d4460141d0003204d146160040d01504100b140d075101c107800360922541581d901c02042c0c1c222000c0c404007000704002025262a031800072060300e10541c0d0f0140c01c41e8240d041000240b80e510b00fa070004400e541d01a507441140c4d101030b400442a60344000c0d010360501006080218039a540d421003080580284e543c0e5103914189440c001e01038044000d11208071803000c00461190762119010402111100c2601140310010031021070f00710711407030030302600354080041004044040398200d0700e080001a00c07007949580e44d03140044854081540c012099030a041400c0010440c5c1d403000e1a01310780500414052144c031039000070001202ca046443d5546c2c16888200a89600004980b400490f41c0624141504000002407103511814401d4030501116081c0070b10070300001c0200c0401a848512180c88074208030320b0036443c40c0402c8924900188402441e000e5608004c10407060920498581303450f000821400c00c220f0410400300001080f0121400078440201001003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 606339964 1250 606338714 606338723
    0x312020705150a210906050906070e090f0103020906120f010e0d030e07050904030207080703150c030908121504020d0207020a0803040503061f0b04140301060905090c0103091a04 78
    0x3600e203400300b44000d6001c9191140a140e030140402e4904540108809280a50000480c4841a01074003500001d100a8502404044c50581048211100007401900480345600c40c41c11500746401008020307035084410001c1d0155035001000141022004150400350040000440004482806140c6010421070281a07034556507080811a014000c0f800c2c00c000038901401580040c240269440c00c00780300b414007810700328001906061092040308042c10b00c0400781d8074129075904112030303100700107c1c2c40d2705e406d49000781a4140e01d020b8800c0342c0c0d81d80c0d03005081c9402c000b248a0303500800c1034010400104404aa00580460713078480c4020b0840c41c801ca10010380b40e080178018010358a40a41050203168800c00017442503030740005005510104042c547e000c035440b0b2540340c1d006e401d0540d20442d0404070101380403501014402c2000c1c2d0700e140940082040e16620034403241500d0042e03a0707419040d0031480c800812544260000c0d81090f0242440c560005624003245850400846050b02e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 606341214 1250 606339964 606339973
    0x20c120105100806060d0201120f11043206070314210c0301060c0b070212030a051801090804140609130c020f16090e0a06060b03010513180b060a031202 67
    0xc0c074004034802582c0940b80900c000d109030310b01040803801d05010150003a0603c0100703100c0060000803a0414031030078542b01c0d8284078440c0843c0d06aa0150854083c0c061f92141450404400a500c85c40003401b0182071841c0503548480c15051042590019800f6810402c5002070762040001000c002d00c480900c0c503006001180301c10205840c0002c02401d8440a0003080004000b91944040c071903d82ca038022141302d1135501c1c3c18806a10b4030782980d10b00041d04802104100365052207234007040c85501da030002c010a201030b4001807800c0354070325100103105010501c401d0005205000d0041c10f41d44001e0b03c0d982c600030341390000844d100d86203803501c020542c4070b4854101c91581482110940204c0d0f5008280f05d500030074080b102c80350a80120320b07074280d0741c880040c2c0b124020011046040e070130140030084151100c604070002c3d4400d001c2c040c0904100b03c40c0704180e00446c8102a015203044001c07044152881da12110004000317450740c2da01001d202e0002c40441ca1443c45140d41301000e030001c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 606342464 1250 606341214 606341221
    0xc0c050a06110d05161e0c0b18030f0303070528080a0506030105040f2307081c08040309032603090a20011d04021c050a05070c0203060402010309140d020a05060a110d0903020c120105 80
    0x510301482704080c05009421400e0320036814680001500d410001e0360900342e89440c02c142d641407036004a0344640700c2e0001c94031341684145030445949802613001c08000e01c010381d01d95040c5403d9800c2540d0041c5540c1d0507a0302203000c140b85070300404800141e66108159148200161403600e001508201d180e03400040d4460940c40d00c40c0c3c0701c0700b1911a80d00b0300ca49140b07890b0328060003d41d000c0c4005000361841c0b9101c041c2c03980008008203c03141c802040c4036124104440c2c015942c0061034011909035603080f01030624225681c2c81000401016540c0d01102104007080c00106003a420010b80c0244e000d100811011040301103404030101511b20005091811420010036a44003416a0341441036400050015840c0401c540f9481902130030042003001c40c030300e028151803c801201e03412900801c0100d0f00d1542d804151414454000e0046903510744640309244112201c001109181190800042c40c072806d42e500440ca0642c002d0065420130041080170a515801070495100181d5480040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 606343714 1250 606342464 606342487
    0x203101103180c0607080708090627040b03250f0e041e0812100902040b1806090a050d031803230d0806010c0c050a06110d05161e0c0b 59
    0x10108140a0350010003c000044010802c548510100a0600a80001d000081c04a4941118140c00e0094a4559210034204107200c01c042041ca04203070000c903502000310140350500601854100c014090f001c00c0603600d10140f4603502601c00d807885040403a01c00101d1302400039081c401422010500401e80c85e00780f4001d40c5101e07052030980b1000007103a02c14808a22b40b2130554182c400d0300320744207116881d0203107e6060309003140c3c400503455000080208240d1203040140101e0504100c800d4241345080301006040e01503c1e50064001d462940c040105250076440085483d01904240310101c3c2010b40601d4884000e420584030b041420220f60b4610305459045600c0820f070801030050940c29150041c51814080c14550400402d803d4103418080c2c1c800c800001440d00600e84409180d03106d00241050201000b00f170700300d000d80016005218080c1084401b51168200c5c04440100a551001100fa0340103860320025410b0761404000118180c001e04060009229842d4855007028403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 606344964 1250 606343714 606343741
    0xc07020a0f0e010b0a0e091911090f042003270d0f180906030b01031e110402030403030f09050a0203070f0e0f04062d050606040303020a06090203101103 67
    0x18055650a240100220340b03400c0601c40c19101d21248440d91034140b10402c40700442071b040d0310b41e0304c29265070038842c0c42c43c1e107a6880e031041c55400209010050b0a007481e450b0314003034004071540007a0100e4404400f4a02507000456030103d2070130303142d50080c68190741c80003074004643c049621304401403514043c91402ca88203941d92078040c001d0400042502d4020180b0b1444410303582402100101100000e000611a40160820550404c0600d40e00c1c101400d07021004e1000340c03282d413440d115007881422482c2c1070000c42500480d20300400c0169206200095100130300c26410580d8801c0381d691000142c0c001c0c0c040300f600900050200103814010581000c0e0f11758004601078051303800402c200c019840781160b000c0d2040d0126001640c4a0410f013020300042c030a40512828601040c45060890f03250101c605180420100710664840b01800903920403800060003591024110100140c0140c0016000c948060180c1c0d94024010f400f1200703603115a21410b03400d410100811030354103040c1c0d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 606346214 1250 606344964 606344969
    0x60a0c2301181104051017060103150204030210050304060b0a1509050f030a030804290a18020603041509150e01050c0412030c03050f0d09061d060a0906060b030c07020a 74
    0xd95a041e020080d03039070343c0c9450103081d64560069494500181c039110b00b03003211600420121071a40c80c501804491542c4905007400200d61a1402c54a00000b1485078400d17a07064942c0a800c204243c44100404e5905400042007181c0d029281c0c040a0070070b0b00c41900d07080040c41212003010043c00681000fa00705a41a04001d000d200d0b00d0401006c81d607000501a500745806041c5260640c80b00d05210b0326403e000b203289001d804031075a0301d02000300120104da104403d01401088510400001301081b81950500a0740c400342c18800304c1c020841036292211004916840085c46180540d0b408c541c0342852841c1000c1e0f207555159403031301d116003030040580c000c04503002981b40c00d083c0075691039840480813019082048500b012020140680111021001100842a240c007010706c1181e000d481080c2d011508241425004442408a00800c0b58904400d070041c240580d151060340004101d070700d005030b90140c1c4408001541c12503000c0254021020400c44c60355600c0580180511140540d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 606347464 1250 606346214 606346241
    0x90f0b0f030d080c07080c01090b0906070c05030301060e030a12080604061205030f0901051201141002210d0609050906040215030106050306040b0d29071d060a0c2301 73
    0x20040c0e090b42c0d1200415500141c5040c190361180b52905103202c11b8007036610014604d61a02031003409004400341320512a03000002283c44950700e0301c40480d4650700c0418000e00310352042c4014882c1a0040ba25407502c1c800c040d08450b040791060302d50701543c0c031180f1501d00c0800d6102003440740314107240c09000007510114007030341e080b40d8040e0f4510342e991107540c3d034400a40c000410506900d038410700c103c0301070000c900703031403201940c41f1112a99019010b56a45208602d0341120300c1070f0500120b414050619900d0019001c01702e02d45c0d5a01c66540001c190390901c035a02c0b180420081d505200e1940140c60752130013040d0380e1074180f050100fa540c080110b011210305c140010440d856001e030480f0707840300c415035010071b281c0d0418010982042071810014410001c120506a0543e080b8100d400030700c01c0f24243c4031568aa480054840903488085e14801001c508403103042c605124000740075400507440d00210600d401c0d00c0d022204400302080040d500c0c60b031002154080001d00481c481001300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 606348714 1250 606347464 606347473
    0x9040f050706110a2006040f3b0912071b06140316090f03060f110301050a051908010e072408010e0613180c2913090f0b0f03 55
    0x10040941d0741c0d050002d00040290028030003884600440e01d8041c0b01c0142c029200681f12034403a080e02c0d24103102801400c80480d0312080aa41e840f50b800c9102559000c2d501c044960b4910074480400502401000020f092050001c02003581e440da0000340a03050052116006544a8070040c0d40c011205a0042040000141c900300301030740d1040c12a034000d5840f001005000007111810707500c00c285540440142c01104900201380480c60700701c10454110030714100000340b0129901d040d180000c0c040d07140c0001c4180b400b4000340c10303e060380782d541403151a001b45040b82d0b03c9030181c0c00d5801210b8944019041840100051001f2000032070312504501c156500d442d03440807000300071020511070500c4c84072a1901003010f549070281c40c44200310205034144049104191004c40b07204900400701d440c290550030025650000d541c01a40000d00c001c0174001075443c0240700082c1e44c00c041c0c0d425072110b1401c000003c11104a00c9200c0340342421a001090b144503060800144004410440703019811 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 606349964 1250 606348714 606348737
    0x1005060c0d110d05121003062a031e110c0627070b0a03020d15062703080f0a02100e060103020909061302060a0309060f14090a050c011d09040f050706 66
    0x100001910540800015600c625581b11000030241c01150b91002d410145040c005401003031984140e040f050101582c8840000640c2804800301c907801005403032412403150391004c2c1d8410340e4224001e4000740c00b40c21404d107092000741078208030b41580e28142200d071803841c0820141c9010351503040c0f00f1f035140103001e005151100c03400f49442040c00e250101580094070100120f100d81c402814545840751610201e0313181e04014150150f00e009011a9244507805091120001c2262905517a03000c42c0744d40c02d010052084040e150000b0070702d482540214245010390f84040e1141840000c0307440018030321945103005000b95000084c040c4082c50b0440310402242109820781c0106144d03064030440c2e17072000c03a800d049001740000d41c0028021130a080c00c0e501000d04c1900981c00c41c10305ca060300c4003141ca50b807102c6a40c9044441005045420043d0070340f03900c0d8010200c003071181030715048601c0c03182c1034040043c0403c0c004840480741c0c00c501001031000c1c41410800d4101070441030600208800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 606351214 1250 606349964 606349967
    0xc061602040513060e19172b06081204122409060b010c021819020c0c040e0f0a031103040b1b0d032025140105070e13051005060c0d110d 60
    0x58005401421f401c6851425000341241001200c0020403c201d520080d405444103503408540d0f0b034002d80681a09283e008203110b600400c7c561019140c0030031061500c0e181091f00780c050000c0343c209540560780c0082c030040c3c1070082c0441888840034000002400c00aa04e408011030703003130401160400041500303500041e124401644030421b094589034800359148101c5040d150f1000f041c15643ca800842d035030358850780c0042c480e1400325040307030305201c134905005d09255107031101004051154001c081a002090051003110603030280031080e24501340d1950103030703041c07030f030003601207084010300c1c5220710559180030700940c11302c00402d00e0207000380e000c0c1e8885400d40d200704007001c05058100140c0c41c48003034110b81001100c1d200801003560410302500b06042891040c200192441d424070b00000e0526200f202040c0e01150010f145061040e0000e03015802420000c004901e0f82030705060100d1142d8400000c0c0903a1144980148000300b04280000c00680c40c02207403207982e81c00120b2a05586 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 606352464 1250 606351214 606351253
    0x5010507031a0108250201060f05030616081003051911040509030406030b010201060509041b0b09151b010908041e0b0d09020a18060e0603030702030c061602040513060e 74
    0xb62001d00e0700c0d0455844600408080c48100c80c00154511124140d600c012034040d08001c080307810039100c0d220615a144180741e111366085a50203c05009c0c25240741141c3d00441c40d4540001c0090451600b41c0e890340c0d1010301e460020100d000c00380840c90b50040c00c002a25000c4c04144c030307041c0e800740040d0805c4d64070326640b07020703500401c000d0540b00c9c400720345140d1003580048000c04000b050f071141c0382070a007803011341e21468151190444d10201c0f00840c11600e02d00403940d03408006061420f04410181c2c445071942c1081c125a013508038691100c1d900c20400740034070020309004803c2656950320b0001d81551003001b00e40240d600d9842010300704044820071040d01c904c024074200c00b08406949100140c0d0003c581c0d04a140200303903084104044032083c0e400746040e248008032030b0165840d40780c00c16540340120340d0f00030740c150301a00c0105400e050034406000c04c008031244070b01c0310284560004050b514116842e2011096200c8254203010705030090003501e00f207100203011560101c4a004400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 606353714 1250 606352464 606352511
    0x80601030f0f050c030105040c0f0e01080a110d0b100207081b0409050601140103140108060a0e030f2d120f0c300114010906031e020a020a0501050703 66
    0x141951151408440881d94100c140305801c032034030401883c641030580041941081c040c06000318900781e09080d0a50245d10300034881001501d03070400044030b120046401c524001e00c2a000f40740c94440c40f1040c01030040140100044015000c5150800035090000c004418101c10045502403141000340324000f24001800480c10201000d0850305003012801405011303600501c81e1003104000502600505070480c1a00426a4140104c010070084201c002e003081c01a13840580141c0013041a5501d40d5100404001d948000e5a0801c0c0c41581103a441d0380164030216000c43d800603001c194960340205c0d0406003082840c00d05c0c2080301c84166038852600080a1030402200e5a0120382c2c006648415240d907601e02c081c48440c0401e800c41e0b0f4006041e038109411034203051440012550311041c0c401d4040181041c3d40d80800c140c6007000460140c10b91131207a540c00520b0801441c1c420b802d034002000c1740310841d0018141100689070207421030b84010612020545031102c0340ea4001031050a404070f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 606354964 1250 606353714 606353717
    0x1903023904020f1e0d110306012703120504080f060106050702060a0e1c0203010507020a11010507020a150f080112030903060b0112050414070e0402060304230303010305030909070e01080601 83
    0x2150102d0100d40040b030301c502803068184d000901c00960720a0700400081c0464100300304d0a02048180e060b20403941c0c0016100140483c2080c005041c0d0a02050f40b5070340901029030b8100c1600b5580e403104410240d880341c0000011b000003a0501040f0b101300301d480e075010303400c0b401009250f241c120018181d01424000030b10581c00080d0600701581b240100309000b01c401818901e00c80500c40c100c52000c015540200d009509010000c1c05c00390020560350b004a0300b0412031300d100212200111010b40c88080100d80c05030381c048000c00d10044e40c05141c2150b002c1d42d1551134041540c0040a400365405a0154009552024140b80003d0380007513010102c03035100c0c07808150300303171000d00607100382d00078030350030107150f8501010002803064a54080c9815031600017540c0400740c4448400c0780c01d10084034040e401c22020004a0b00054002c0c5102003021903124800c0600f81c01920f01909591080c0d206481552010884050706e1800c00e403040d40010703103070804e806218103844c0040d0200c880200801d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 606356214 1250 606354964 606354967
    0x15010c0804030b0702010615030209011d130e010b0108240405071b050a0201080108010c090b0304021215090105010512210412030c0b0705030621190302390402 70
    0x400308449401600c000c1e540c0035400495602c2d01d000001d00030311140c822444005041c40c60f100d1840d0180c401c80e0708008041e55004151300082d40141102ea079109010358200c4900d401480110714584911000705000400120350710480a000401d401e0340502100000c642014180741e41a00e00200c0e602000020349010900b5030750900d082d165214101091041418160f402178100600442c801603007902c00d80302e03441140d03280c50000e4200d501c403d0082006c1141d81c5001e000c940306403005554410302c010000b142c40e00d0040c2005062109120144980f00120310a208046600303004103405898143e0750307400300c51922074803583d662002100b8142c00c100e00448480c0c051220b0001c80d1b026010402c0807001180083c500100074421a04066071001c0d070f450007080f07006105a0480740140310040c008244180480c000c0368011041300240c030035501c40c45107040d0503884002055010903009401405401803809001c071008000c000c3c0c40030210030504c050000007501070341c032010505030580d00103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 606357464 1250 606356214 606356237
    0xf1008010312021c210501350312090708060c180301060e0c0a020c040e03040b2203060e0c04050606220509040c05030d030605060304060902190e0a141501 68
    0x2681401c44581c0e00c1c42c0c4080511004040564201e079035151420301e607003094412610701907800d50803a0310a02405002c841d048410441d0102311040d03200c0c460216140444203444100036242c0746501c400c0d032030400c0748003850400c481c484003800110000c0c04018040d2406103003080d0710382403900c9102181203499107d405c000006850950250f009081031040403102030030000c480450f1904812001d50040c030940140d401242061300030f41d000240c20400546c01c00b810010b441015401c5002408211100030803001901c2d291070044200a60007500d00141800d000701c0842d0403c1120002c1602a03420301092029548802c41201c030b452043c0000e074000c421a110910517010701c2d5510103944141c0c05803d000921609440010458000310216482c00c40f0140050b4141c3e03865205c0d03507034080340920005020071320766048105641d100500c0d03180c4c1002802e00d0101d6501558001d0416003a01e00e08120791800d00b44078580c403004003501a60a81d00d44620345c600c514580ca80c0359410025110b101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 606358714 1250 606357464 606357467
    0x10c02060d0b03060a020c16030c0b310302010809012f070204140a0501051c03030c0c020d03030b10030227060f0a020a11040908030a0c020f1009020f1008010312 71
    0x2c0c102c86009003030b80c402d42046060382000c1d403c0307240c2c030318900c0c0100b45c038040315035842c40d00c03800c116540401682c2e80c0d18030340141c041494010301d03800340d003503c031b664510006500146400304019250143e84c080307c0d419070000600d20740000300204100d0f890000c001c0189000320700c8148002501c0744860f0b1404292000480c024010844001e42107410042c0c0c0b91600c803a80000c152040381e0fa607000700324903030f0303100d0400c0380303101e1040c0d1100c01000040e00c01c040032900c01d4100c1c130004121400c0150358501d0b680d0208642000504042d00060303a2440c8045980c42e04000600b80c903489840c0560801c220041190155003410030402c04885d4800000c602949074841a2441041d003c0000d644030840000040c0d102d0240d640c0c00c0300d40b07a9125100301c0e007a24051043d022860b4004a000c0d05681c0c90102030350040c00314011000551250013502c0f03225442c01c0007002c00100601e940810043c00a1062184074521009450b00c240300e140c5402e08d800c0c0c0d000d4640742c111b83e0000c901c641c0d8581d00880 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606359964 1250 606358714 606358721
    0x305130605040501052a1f0f020316050d1d0a030f030204060207050d0f02061309180f060b0102070503010539070b07050c19020306060405040506060d020a0801061710050402010c02060d 81
    0x40300d21900a40501b50300350401c7d14000060010b48440a004404003614504203c2c40107c1f9419000d42d042c1a42d5070b00f1521410152030005a079240004410014401450143d000d13804511000d40c8105c403032800b0142d104040504c140d05504080d400c183c02c1040c06925007455008490085100100d482c082c004000e1420016a80142055070750707091101f59040000818042c1c40d015608144403029001100307107140300c580ea04008407012440042c0d440300041d24601e9640c0f8114802e00001040070b507800c2c8680f90046545000c43c0c10f650714084000c030001044c3d4158182060542c0c080a9881002c110440700480da000306d04106030760780e9100580341d038041c03107000000c18400c0c500b0a0500611007040302c1c01440c001c500300d8105640e0709040005589084600400d21303081031003c90352a00f003400301130260303506c0248007074640c607203841206007152001e900c0000d44400d000c1948800004c103101810a007441c01005010902d40354001900c07182d19400001d00404002603842d00c50340d00e9a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606361214 1250 606359964 606360037
    0x3c15010c051e101503031d0108130317070e0315101e08070806010f1e0608090a1a150d0503030c0703050403060203040510150303080105040908040e0103030513060504050105 76
    0x1204100c100b00440d5481000c13840e5000c02c6020850026600b00702c070103c40105034903480160b54000140d500c140400f11681c207401c2c011424020a829414120381400d81501e104040079030300e421099081c401098508140006c80d20124241441031182d0102400c04c80c80131b950300d900300601c0448403081003509044540c0e00210b00f50042e030001145015000c26054120382e0b41c21408030b24651108134032007030100c103245000351049884804006c0c3c940501c041640c00a40001a0b030100c0406894449101d8841c00c551750020221034200004508842411080480c05680c0c2d030b0743e0f0a060b66241956440083e080c4d03400122301186031004c06208008032006954400b01c04c0d92241410301e00f00350303a83c881443c0501c0035400c20614100010320101410122505a59003450991800c400d00004003143c500685d0464010080407645108901c5258002c61107513680c10f80ea03019140740381fa104c003400c0e00404100700e0108130400180c1e85c4003080d12490401502c0254140b4428510b8004030030404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606362464 1250 606361214 606361243
    0x3060c1608030a0e2a091021200d060b0312180901050418061802030319030506010c030905120f011107060b04050f3c15010c051e 57
    0x300f000781e040301079001030b14554a080c08441d00e03051440b01c140c18214520030340c10080f02e41c800c000c0540385440403105421441c400c80c0d03900029104d038041701c0c240009400d028410072000c0740840030404080003654a010072035860074014202e840000322006001d560103009542c458080f012a0b40c0c06010300d162441c1680040e0b50344d02182c4440d8071340d00340081d41e1940326000c440d0001070303d42028050b0a011541c07030bd4411051000c10b80e02c80d801070840c018501c54000e8241a0a401a00d04000030490310a462030b0042c0d40d05030041c0002c0030b9500007000356041181c40501c01c40025008044041507131f0041398100500d600702504240b9211444448260941c24820b99103c00d81c031040040000f5401090b00303002c805009410300095400503904d46080c207a00500041018071a4603100c00311f4180203c002150a0b0600a4404503100c4181c2000c00f54451380140700700e0710b8508103600302c0c1d04028201652310034015140e0355240c0117003040c4800c0c250b00b0350303c282e01e0114060041d604180700303d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606363714 1250 606362464 606362467
    0x150717071101030c09081c030603020a090b09010909121202130618050405010e1303050705010c030f061d0c0d15030c091d030d0c090b030f060907050903060c1608 71
    0x1c0c00c002100400d0180418042031403c1892010284139140e41e0302561207a1000b8489514400142c1c8603000003151380d10308141e42c581c00840182c0e0303241c0d0400010580c00101251010150040190210042e07004110b5640b61060a800003520070034071080807841e0303051070500401c0c0010399801a1140780030003282c00000480c00b003a41c03604801800050400844503660b41501e03142480100d4500380038540716075181400103248aaa4546140b0101c2d1280c0340c0182081020f65445007580c002d590100003107a145e208814006000c1c4c8149c43c01040f02c101701001003210f881140c0c034202800b0741159114080060200c04a00ca0303500612000315064030382102e255504e05010109025a0060a504074201a00460101e406001c906017010071320010307525001e120140e0000505803081c0b61400e2200d042d60004044000030003844c840c41d894041181c0c0340c03415400f084420b140082082c01409010300000c031060f00e0019005a000c5041c204035543e807502c0968030020321801d6800109002d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606364964 1250 606363714 606363727
    0x309060b1309050106050316030b06010c050a0305042306090f01210b0301051302182815080303091506030a06061503060e0f04080a110607030902150306150717 70
    0x10765840007890600510003040b4454440c020036480e502020580104924111014404201c04a0060340c2111050405550041c1182e1701c0c14289043c0c0c807000e074007140001c5020004004071002c04031041d4000b6402c4510052030364000703106401189000784c00348a04509005859005004440380d145000d8240590748101449501c0606156007900b030080d405c20b0b0206075000885ca440384403459005041e50001c4021107480e003242d4038020604030720220001000041c64030ba2050100c4403501003500450780c0030905401c61003032402a84580749030340c800c104000c407801000c1210f00c4680001e90061440340c031502d0000b440d041e0328000240c40c0502e44440024000400000c4101440e07043e1001d210081c0d99135106020482c088440c04034011881c0001000500da80e80149400c0c221070400c00300304400e0f4404140390550455202c00800c1d41c4805003000c1d0700d008103a614086001e0090300d45189401070100701030303d25501c400038001401050304410080315403504403480e0200340382540c440c80e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606366214 1250 606364964 606364999
    0x11b12050916090e12030f04140111040906060824060c12040609030b01080307240e0703050303010611210a020f030703080f0f040f02010f0908060c071208070f0309060b 74
    0x4a81c160081c4984900344030b140200ca4020300b568801c1d00000c07801a0710342d84603110240001e508030210f90f565584c0d0880e0901c0d12f030205014001401100400241890405001400a410207070031402c0c80c10b9400140508408035410b4602c01034811380f40a5264018400d006103005c1541042d507a8000002c180400c1195020360000c0860740600030040319070343d913034070201d4484c8903016000c4d040c2545100a4190084409940e00a40728841e000080050f1003074529806c01101d600f00300e606030800001040f40c1c7d03030b1007100110103d506201910403540d11004903071100722402c0c10342132410701c04908004032034020300003804090b2700e2000b541d0791000030f80b13002403440800310b9001e0720410b03500c00400c072607000d5188000d1040c0ea20071240320303401c030349030300103448014016144804004a140780480c610500b03105244c090b441000c502910b0f05040e103014200e13041c00092141c10020500c04000c000340c0e101081c003000c1805c504001030180c40f20300309800907280940080e504200e1078002900c580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606367464 1250 606366214 606366221
    0x12130c151b050c0102070b0c10151d090607020c01171b130906090203130f02041d03250203030a1d061b010509030f07080d0207020301050405070602011b1205091609 72
    0x2900c05da00707441086444400c001c0d003901615003051010341c05461081c08003e010f0384408042e00c0185200d9208a44d00c050120f04c2158000807111458003403020311580340d0003081050b42000c05400a02414030708540002c1041112880c60030f000c414440114262381440c600744520240700c2025650340f1080001d040228101c14400d0308560f0345400c000050528003803003900e005520307a810805418003503495601da075051400d000d903841b03503840108081c0501e0166216080e00b035914051500e4842800380b500a001d1070048070300180d1100c0e000400140d80105c1140c9003a416403c01c81280c0104141a50100406010054008c10300140d51031040c1d03001a1100f008040001c0240900d955040000d5181d00507117035605490b400030701c10040026101006050202c4000600600b040701540000b030035184c0170b950544494100b800f0902c01da0b942030150004450006241454080c48020001d12402122902c080b03840d680c0d41c0030071800d00090000400c0300700c404206040031600c804948005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606368714 1250 606367464 606367483
    0x31206190f1a0a0509040b031507020d080c090906100302070501050c04170c010e0409150501030308061305010b0d091110210e0a020108061504080312130c151b05 71
    0x162128488010701070b4035003201c501104940d1500c1c104500102800043c009000d1580c0e814022082d00f2040003010b04038403403066425034018195011610b8010340130100c090040102c86400b00901451030301e030341a0440e00a507040e100c0701c2038080851801c4000380034252009140d5402c01c801c3c0050150020003a000b50340d140400c00790f41850080b0595a5002b940e455580865800d03288500f81c0d00c2c199120014041c007548106110301105980c85040766026001240414280c800b402500e08102e541c0540c0070712440d008000550402645d40444e01400c0ca5014a0f10f848241c554200405407003507012103800a0242c000c0c410910001814502d003154a0740609100d0000a020f803800a004000c0903003680130181c12001c90a0300111a610343c01400107400456803001340c900c19515070b000744010071140c4003440e200c2c00c00b400b20441c48040981048003802d0200307a508003041222048904550b00c604e41eaa4018211102c1134a001107a403145103035008290390100107000700070030711000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606369964 1250 606368714 606368729
    0x40e06060f1b0d1d01020a030e0d0b0a0905192619030c0f03090f02040905431404090302010f0c050705060907060c060c0509060703180b0c031206190f 66
    0x4000c20018000b105449004104c600592215040700d0110780030b604000300034017010f0405054840c0036111340c01489030a980b07a1442c00d0741c0f16141018440180440f143e0582c0402181078600303100d4944c85814403801900345564050aa020b603080c00c41c41080750100c6101803c2051162650113024004201140701000803403000020811542e10038030801c1c0d0000d46c001e1801e2840b0310740e0703000c1c4001007452010441d560302c00c003580704000c0001010701d1260325500d42d401c10303a6404071040d80d440b42c0c941402501c4180f0b645110610244400c003280020081c010745001402d84000d0408a024140e102d005001c00c61814550306c0006512500800d0510f005504036142034803480015560342c4203920032a00000c0e142c1d0240d00008210380c100003841c61041c505903041100c0100060f03540d170301c883e9048012030410702100c00081c078800d0b0600300038080e50303c0e40ca040a2141c2071142d100d200c1c074401e8903810040100010031035a2a80000c0500c1c0310b004001d401555181c02d144e014124440c01a20b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606371214 1250 606369964 606369977
    0xd080f220f0c08160e040f0212030c120a080105220216060518030a050d0605090c121b04090207020a030b0907060816051912050705090f0105040e06060f1b0d 69
    0x2844440001c40c8055540c48001300420203150480400000300050004c40701030444546210260f80c5050b164003a080b0808043d55a032102a80440d15003440141000c1d61141c09121421003241c1200300c0720704448007030f541e040d03818000d2005620000c1d1031004a20190f0703c040b80041010509198040c1024803580040107191100c614001010050412103082c0da40300b002021495071003500540001500c086001c90040d80f5803001844803801103400d24210000802c1c5c3c00e241d40c1000058542280c1da480000210641101924415200d64060007102d40d4000480c3c00454a402060b88000c507003000c0892041d041000450b62101e0741d5124000c002044070011070540c040441181d00100c1c459101d1501c0c080010482d6650846a0020002400b054040c000c9401d095401441d228500955500d503494244000700032044585040150401c00d0620062220403641241550407950032030f01c0b01c0e1100d45107032884225215526103840303180381102c4c05041c64403001803900d60060b516103401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606372464 1250 606371214 606371219
    0x311090703241401020601030c03060b03030c0609060411010c0209040219091a030d090b09130f020d2703020303040b1f0b070c060507150921021507020d080f220f0c 72
    0x4a031b44031028000508100141002000020040e42c401500054040d083d00d080c00541c0342d0040c24100200c0d001c0391113804c0314082104002c040c03501a00100e03400d0800f0b1002c2016500070501420004000900424003000c10b14000e03503c01c1d5403240100105401404444160f80181d0400880c10b000140640f0074003c2c0420114080c1d4424400d44241c0b642c05414441c0c2e40e030400504007848410a8071070b5030303035058401810403580001c0811304080b140120341c100c1440008484069640302186c42152640c10600c000f81d0301104598203c0d804c604408400c1d1184190140503482001240114240840740003075840905005002c119018100200c46d8907510b01c0103413902d100f80507008090b042c010407000c10141031607201d001d615000361107110350880c894440004256a200307004026034020b16000503031907000c1c0c1015501184d14400b614081d2044e080291543d00c02928113081c0d03421840c0003d450400795030801d40740981c15190400c00040d21b09021120106801042d2160a500ca030701 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606373714 1250 606372464 606372467
    0x20a0501050709080319031b030b0f0301020c1f0e060103050604030306050301021c0f0b06180439020c090a020d0507020a05070510050733060311090703241401 70
    0x45401c0794851006140361000c00040c524411b4a544542c81c24150b954502e0742952070014250030f02d43c11140c800240c4200c4000800c200d44101c1c0420740d01c26801080840700d52000428005421203180c13040b8801c541d007003511200581442c100700340840c031407500000284440000c0141c0074034081e403000c000307150325202814281d108007c18200c61400c55a541e801d074a8250748018481d1540c004009a0b114618002840e079620002050340d15200c0884a49014034140c814030040702201a9514040d4810032620140340c44c412104103200007207800aa96128001d1280a02c1407100030001c041514029216074000c0d042030b1580102e151410b00010280760000a891030301c95003050003030400070320784002c0000c102450103081e0f081140c10f01500001030b1510020400c41549079103020310b502ca0200e50721244031080c0c803560000324107007101040450025039240580d41e000351264081907492081c01d4019000100001030001c03448036030340d020900204c003c64182c42520b10741008180c8403000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606374964 1250 606373714 606373727
    0x200f0607090f050609100e1f020c0d0c260a0302010207060606230c0f010213030302010510031e02010e032d0106030305190c051002070b13050303040308040c090903020a05010507 78
    0x583c0d60410700070001c401032440c292122006000d0307646401000506405c0105413014004d0900700a140010950740c2401c54061003040181c04050b100d00e00104d41c5921035007140310f01c0f0310071128500d089015040080908900c0b407a209454082140c074200d049190080c001d600c4404240c031054606000818400c1c130a415804460b02c0a90b0102e01c107100c81c000c4050a40e103c0340382e054083c880d003280307600a91002c1c00600704030a0014041d040c01441d41c103010742034440c0280072000d031008c0c0c01020303c0001c0c07210310000c2540303c1068207032001c030620f4401a00d1030358041c0c40391a45840303078a400f0380601000c0c1c0f900b626a842660503206c42c80c01805c01c06400d80f4443d0000402052082c00700314058081502d103002a00c07a14605070850703040a41b1480c3c1086012030404c0d40c95900002c1c8038090105400c905504030075001036071580b450071070b143d403038072400050001400c2280c04c5001c00c0c288402c0410400180000407820024066285806903a030400c40804980c29428000040d08281c010382 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606376214 1250 606374964 606374969
    0x108060105060f033103050301090605041b031e1416050f090111030f040605041505040b04051c05100b0f0414060105030c1306080405100b10200f0607090f 68
    0x201c0a90a58541d91103c040e03c0042c030032082c8a000365407104031704040c48811a062490f02a4490355034a5062510002c241c0381540c10050245003000d00201d9100800d03103d2541d4170314036180010746000c12403655882d8118403090000300d0390504584c129a101c03030264250042d410074401a035001c84540781500d20b80120745c1c3c0f84030011804d115800b0750354050609443c0480722141582d103001170345c804041c4140c0158004100140000c5000d2240040c04400f128040843e8100141810b15107039946d0902d00ca42d000d558094214410349030303620390140c0c00c00031551f41d112094501410b580b11000c002055840c0c2d0303040c03190401800d18a500d080c40e114401d100b81e0072001701c4a85a80c1c1d640150303520350000d0000d64150b6420403600180b0200829101d0180c5a940d961008505050412614000d00c81d860040624504004c034003583d070355401c04c0c226500c29410008502c0d000820041c98031300b00071054401d41e000e01c0804041e0040d010070080c0c8684010303240c420038591039a424078102e00090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606377464 1250 606376214 606376237
    0x30301091a19180e060f010e07050708030703020f09031b0f0a0b0f030705130933060f11150a06080607020304140f030d02060a27121107060503010806010506 69
    0xa4180600001051101500380d126a400f00d01a183e0540c0c45145c10000c40340ca191030001c040042c095485442001a08140c0c00e10b8424140405074580d00051301c170182c0030405041c0d0000c4c2e201c8564213400b0980c7c080640c002c0075610900b4400c5a0409502c0f4400d020910841440c108001d03d407419503614015101c00345280e07424141010300017102030344041c010005100c3c00303100b5103c001c00d00ca42400050302c1303201c0e17010800b101c0d403030b40981c0d5009041c1064080700e040a1101d14810110711000300803560f1610303050b6403500e0301000540f240300100014100d64050803500c4000c050106002602490b08030208101e400ea03100078081d150301c0e00b0380c4c040e030050300100401c01a440a802d0403d03440c0300b00400c41c404050312000000c0c60100300d8030003680580c02074000c000690781c40784110301d0354401303402a90310010040b0303c00a075039010000c40105003516045100c0781c028400c24502400c20005012960016150309000c0c200d50001d1061290905c00d0b00e00115480c201302d000c0c0c03030f814140d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606378714 1250 606377464 606377509
    0xa0609050d26070c0c03140d0302090108070c020f120c09010b130b07150501030f1b0501170c0c032802010c2a15090c080d090312030e030301091a 64
    0x80c0410b22a9603102900c61000c100201c60701c88040341082d40c0351001144150110180c5181d0f0b4002c00307040c1810402400c09051041c0400071182e60042e414a60100d81c40c0340107c04001c20b880050481c90803a40b075980c2002c194084546000d200140541d5038407000c4540000b01da81c0c85041400a2140c807100440b4058402d4040000b258800c1c007800b0454814061046e0130215455100110b5000364000c2c0c0d034061180340ba10b014458014110710058480a1105008a0419002800400d0a100c040303480194520020744d00c0c81c0a8025105440c80c2042a00e07594043c01034003441501c1000041000150700451000b04103005120b5892640910b440d01003800404070b4480e2511113681c1192070030560340f0005000019525803001c1040c4006000020b038013403550501d08240c0c81c0a800c00c3c01d082d400030f5000e030380c9103801211030300c00c5a6002c0044002070b401143c0440107840b1204c0240030a100120012800303600f25084401c0c840d00185414180c014007001700402402040c901c96080c068 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606379964 1250 606378714 606378767
    0x33010f0b0d0b03030a051c0504210c050115080609011a0409050a05070b03180c030a06050c120403050424140a0c05122208030901030c0905030a0609050d 67
    0x18090201c41034000080091080d0082815644031018440010b0800171380001ca011000d280440c11400300e200420180c0361075594014002c1c0050512906071703c4046450a00a2064100f511000d5000e4001c0c00001c0b07841c1d01c0c4003031808981c00b030000385020324800640c400c0e6052203921485102d0580d60950314201c4001c2c08010403400f0070544541c000c105020010600420003200109010b00d046540e91901c4540b401513243e4482429006410840404030b8682c0c0c0000d41c0c09820b50400400582d6445d00c0c241d158481c8202c4a141d4101c004e440c08010500d41c110024200700c42d88840328150035050600c02e47d4100e900c42002c0c90105108522500c0585500000b0700784080701420b011924510507164149001000d0498000040b800594507005103680d5a081401c1119001c5542c07070740342005c000035180d011700c1c00064105035880d2000707140548201102e10003004040c0c181c9501c1e0400c1e04140d0b015042c8201d09039060f11400b609005024400c1607a803118041b581d4406600c802d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606381214 1250 606379964 606379979
    0x20424030204110408031207032003151c08070605070306080613050102040f0b210c0a05090604030c030609030305150d030c172107020c06070f02011133010f 69
    0x3085060f01c900c61041404049108101040140f4006072004004900f034503000000a003070300c01000680c107100051101084c100c584040550340c1105080002c0203980b0741d5500072070403c80c070610700504101d507003048a80c140029003009050b154044e9200340010b41c0d07400c00940980309544181c60703569204e0400180c45003800100180143e100303400252515645041401191215030005001c41c54002411040e011010040c145e0070521a12060514a00031000203220301501405500340180090840e54030395861048401031035114044014007500d03409c0c60780017085d0303020742200400c3c90a00401c0750080d041191035aa0701d0000d14220b00c144403654204c42c3e94224a00c104d80c1031081d100c404a00f4404600600440e0401e5a01d50f02070910b000990f61082a01a026a05541100d224140180c45070b200310b400c1e43d41c11080d031a841c50802d2004071052440040140458025410820070003070101ea40d04a1014064825240301c007030045c038503058501c0a100340070407810344003420404c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606382464 1250 606381214 606381221
    0xc0302070911070f1103250f151206121211060f07050904091416090c0801050d08090a091a04020f03070c260d1109030d110304051507020424030204 65
    0x240f041141100200d1040041b91500071b584840200d51202a945031103107a01166480e07008003200102842c0744c0c0c0c0f400c3c0896096009500049080000310f00d804880d00c002500030000500440528507501ca0882c1418601c91414102010005107034031694030580000140c1c031409500240799001030342d1905401503c159018014058001d40c545407410045810301c0c98290408004801600c88a10a140e419020f040d55030000d07400e5130302c0e0000c8000405c2e880084141540c60a03542c4070034205842c20140c40900031101c14a510584c540c0300410b92070700c543c1103c0490040e040d400f0011034552400c11044e4018000720140c182014800105641d10440408040030302666105151003c1201f5181c48002c0c44020000b030550002070500111a883c45441c0039a0005a2914100704542002907194210300c418542007004510084901e8081070045900400b4000c00e038001008640c648084260041c800a03840b4901c0c0c0b0000f4010030170610300502c030700e540440015103001d0455003000000e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606383714 1250 606382464 606382493
    0x220f1a01090537140c07020f030303010e0f070c230c0a060806091008030f03040c1a0d1e060603060812040b030a0e0106050405040308100602120a030b12010204060c030207091107 78
    0x203562201007260584030f0740d040d83c60141d086450300c582d5540c50750050040742c00c504580c049c042c0d031003000100000c04e1801e5001e500140341d103203688041d49803800204c0350404682806440304141e078044050a5246403c0e200c800c0180c00180d64081c00c070f8004009424a180c0300d4100491781410020b0018500341040d20341c0603541c2c4d21561030560b100c503c4180345400a080c40e18a14900005220600144401c808010070644014030403101c00c00030301c000240100c000201c60581c40f00c1d15410300c0b0030300c80442c03d00298012420001180e441ea00100605014070802c481d42c05462080da8800f9068401c4406440340c214600b45140ca4114102c001410781f100088095561120042540d40c4c40b402100e005601035600e00e5a5801c0c00380c0e02e000c0403c9a54000d20541d4030006c403001e00d40c2806000d40308000c1031401e0019031302082c0004200103000301e40015166500c0001d001c03a2051708103407083c2050b8025403c940101d51125220030071100840d0300911410070074420300740002c2210121026 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606384964 1250 606383714 606383821
    0x30f0903030d02030412090902030c09120c04180b0f10150c0209040f050c01032702030c03030705010204030507061b0f05031b060603010b0603220f1a010905 69
    0x180c0705000d140342d070480e08207507401c80d5080d0142202c804659800000381001c1d20145d84118a9810303d02401511032140034503c03070040c414203071013121038542840f0b0501c400d04094010f000c0d403140505080744048804100b03c07004400305001c100007045a440682c81981583c0321041902e0510b0518900d8031081c1c0704150070440d8403e4498016107a0900b45400f031489030600c0c0c17100f02c844e480c01600301401e2201d0681058581050010b0700c44500c6d070a6105052345070000350041e0b40c1d500110f4200400f211080380c15110001d04e01041010550081c030840e40544140c640c441e48441d8201c41a8204094a0034861304200e90180440d2417007058000f103900c12000c480c9400680000b030b900c140c0015640244580001041000600b400e0003000c0c483c8074112081031452510880f038884510a00801e50100d101080a640421400024891b600c90300164a081048000450b607062183d0034091100304605020228000f9203505d21038803440403811901180815001d801007020900d01c103c3d212 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606386214 1250 606384964 606384967
    0xd0306150e0a080f01020304110415030602030c090306250c080901080c0c0a11033901020a020d050c0a0b030702250b0a09030c050d170d0207020a080a11090702030f090303 75
    0x20f403080040100b00d486012040c009a207901c1c00e810308078000c40d00c0b18140c038003560509500c81d0300026000c0c800c0742641e5020348016125156503004501500401810540601c105014400c00c15206080301d8005552243d445004445502d0110b030141c00c90340c0c1c000d0a13080180000001503000f1910075a02c402e203855007505010003082094030713142201074140d502d1020514524030a04041c00032031035142807040c1340d210b4440345c42074070030f04580403c140f08100024460041450ba01c24840c20001c960010600b20840c0078900702a0303124078680d14414410390740302800080c031034a1042030b00e02c500600e03000f07808403440101141c0200143c00091780c03602d29108601007180424800982a00034599403008445030030752411501400307494001a04c030310915007803080052001e0401c640c940011000b80c6443e9100c4aa800c0c000c0d0203a081d000b544005000c101180214000a0540c01c0302d00407103031100b582640c441400520074094800c04010b80040200310740303940714000200b15000c4054100c0c1e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606387464 1250 606386214 606386219
    0x6040807062a02010507050a020a080f040905010b040e01060f140a0e220b041a0d051207060f1b08070309020109120605010e07020c030304061d090f07020d0306150e0a 73
    0x402014038011481e40640c02d9032950324801a60920032250b11142d1030a29a180607100032010b9511290507030000c140340800207000b00c001c0703803c07001d4500130180c2c00c40c10b01c280d586032001203900b50040e00549218614a80c0002a00d03031064155040c00e50310758031801100d2988400c0c0f01c04a902103244d410a00400d071200582907100c03c4004104126130795401c110b000d52a4201d50f084e00c8450200510960800071401400c800a103984d1240c10400c8800b40c400e101c00340341403400c2581c0e070740d9140c00e19840030030711105100349900009581421050b0420040160200590100e80343e0300e41d040011701000c000071107841c042d0b07112114071801410151201c560f101d850419215050b4800ca80458440004000004140720b001f40c01c6500f42c00030b00000314000020983e03d001c2d5100c1c0c82d0130403401030b54000705402400f48082d807184010744180319038a005544142c5031141603c5400052044c404146040f40c0b09225000c00c0d561800c1d44900340301c00042089900310a040240c0364005c1820300300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606388714 1250 606387464 606387491
    0x1b0e06150c0a03020f0c040605030d03021e04090b1c0b15030309130c02070806090a031b02030115180b030304140301140907080706140a030f060b04030b010306060503030a020604080706 81
    0x200502d03201ea401015590303081c400040c140805404030301c1c011428030740188069a8089103d02055035540340060700d5441040d2440e40540d80d04d002030900481c0064045000031795504240d40d540815648104031202612001503060550a00509800e030040b01082400307007013100e6004500c3d4020f04481c20030440c4000180c0301d0424407242d003040c41d40c4150203001d2a8040c8441c03001850f028000c1c02c3d4a1402d45481c645402c1000070007800c120701c5001c05c2c00602c00300c0b802c18104a0f0050020000c95100c0040085080810b00807407040c4a4180402005080d10340104640130390007502a60405140c0089003c21a1900385041d51554850300400c00c1015010411403158102000a0048c0c1d440d0820080c2040f00f50f4200e04100040402c0e000c4807142c0c1201124510055480d0001d40595071116000040200390000801c50314009400001c3c04880c000640c1070f2805528100722080d9620100b541d00c0c03113903070000d402603002100004c02080c02080079051050013120042601c4004011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606389964 1250 606388714 606388723
    0x42702090a090213080a020d060e1e1b0906031b0409060e070e060904030c2003060a060501021902100c17030a0f050a140c070f060c0207031b0e06150c 66
    0x4002c109a5000c1403494002081e42c000c20010204400904084c132000c2e00800c40c181c0c03120074082c002c1d549480c90800c240c5810812009091016128031517002c02d20100d5a8075500f890001c0c2c0350112103100a01494a042e020b083c0c0690030050050803000c24076a55036500c4141600b50560007075031484142d0104a29003d000d62910600018200c0035003000d21301a036101d00036000c14015a007c104000003e60000c42c0d424015401114200101c2c40c40e500300a00c241405040c0e6805024140500100316210313000390060729001d809554600e4800341c1484410f502200e07010398050001c49100c10218012070042070568044c0030080e00700c504200790303c0c07210752096400c01c00040c3d681c48056849203003071091741c0d00000d032044c0511051100c91010010304102520340c0c6225040010b804040041d802c6911a64030b034041000d00042003502400307919245103110a44000300121060b1008001401d810380c00e0303c103401d00112158031030400348245403840d00001342c01c40000b0003110360001030400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606391214 1250 606389964 606389969
    0x2003040506070c0807080606010c0b220c061b020310020a0504081f0c0507111e0d0609140303070f0302070809030a12110120030403090e04030c0b0c042702090a 70
    0x301c1d00f40712030b2800b860701d45421501c2d400081242c004005010182e0790104e03600c04225000103d010568443c8408480920020001501d1f02440800300e18200695151a181150499182c24138250281c0302c80c012426001e40001754036401c0001c4c41c1503400d129601030301c0c1400c400d1421505003620340207900e1400c0407004513403c0300041d18204080c4001e10b0301031803d5014661425a06117006690303250001402800d241d48941f02111078105901006c3d0080d2401003001481070080c000142008002032203d20800d650b00f5490140d1082c40f01400011603005e00d00720b607181035002c24045402c4000790030a050032141c004040052110741d650070800040c40e280517066002c29003410b42005000f003041c3c08c03682c05a99040410303c0741c0001840d255040d044005c0b1500360755a6a90b49000c40c0d40b404a90801508032100c8818081030551103110b004055220324074242d0b0946407207a03075407c207008911500034140d401c0c10080d180c81c800c0b1452140049004c10f005030034038600798006901d0541e0741c2c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606392464 1250 606391214 606391223
    0x120e03030a1e1d01082a03010306050708190b0f060d0f0c0f020d1d1c03021002131403070306110d0b0a03051203040f0501020708120a0507200304050607 67
    0x54180714040c0c040c0a4800301d001c03041c1051043d80419102c1d407010000c40d140f102e4184403012000a148035500ca84e1000c0c40d02c03000c2c010410580000100740240c1d08207000a40d24645068002011036018400d41c0d80540280028000c0401c0c0a000c124080c000d258842a0020b2140d06106841e4031080c0c0a03000f01c2d10505004a8409003440c3d00c04101c0d0510140380302006498030601510a4011940320010400c501d0442500200340708144c0302c0b50b018605458116a0002c88c0d410441c006010000301c55100740d01f40c030a0882c040080500380d010350134084000c0780c1c5801040003000c0d08070000c054001805402c0d00d14041c0e4a0b110a01140c0c0d941c030902d43d410030001101c60711400346114008040b42c040320b418040900f1529100d540c0c2c42801c4155060401c00008a01400210180c0f0354250341d000009568507040e91a0201075a041414004180840140800d0003d4083d000c1c03144156010350b0741c01c04c0785521054207481e9842d100b00001c458001000081103903107954000f010541e004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606393714 1250 606392464 606392477
    0x41208070308093f041e12081c0e06010305010507170415090201020f071409010504090314160f14071703090f13020d0b0306090309010c120e03030a 65
    0x4904001d0440d12005000103504d030020300501ca240800c031880e10006008080040e03191102d0b0501c101c43c83c08101e090b2581c0d030440490300003150358108200e018071303e52007880316803003503035401e80615036007507040000701000000d1240903200c1103014a1203090710a41c440124100c5042086030b82003040c01c1c1c0059171703d030f5140c4d010040215042104000e800c1c010052a0110b4681a21408034820809201155003a00d490801d010b46e8400c020b080d80400b242d405031008155584018580e45885c805400c0c003c0c1c0392742000152515041c480d000c90705400d030f1100d03100c905219421180d17550141c01e00d50302008804407010003240480c0448100580724040101e10011000c29452600340d05512003028442a80403074403540b20080141c4100d008180c1d408988a0945000950903000c06805c0094641c40402c44181440d801d801000c0400401d50036540c05448440c6416101c0c8140151030740460030144118000074000e0700701c070568602c02d24292402d03120440009095500030554000025071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606394964 1250 606393714 606393727
    0x5040302041d07080f0303160e130531060c1215080f01050403020a080a091a09010e01050a0906080a1518060f1406070507150201020c060109050c04030b0c041208 71
    0x40800603c40a848000001c0ca04007080380c0e1990380e02e00c00103224902e48410240388008a078000c0e0040074005400a098071070306c4181303000e468000c1400300da10802d96070000b0040d02c5210414170326111280d4114241040c6491a619040042c004c02001001000321081e81d029905180784140d440c44924600789002151821501506c2d1041307044446a180e49000288030001b0340014422040641c41107449480f441c034040c0a841d80c500036404003e80510645242d110320000c4c400034900901d091700c90341b5074422494011105401982410400725504140a0190a02524880b903000707410395400302d2a20840070203120071520320b030310100d0442105050111184102c0c0110401750071a507909503030f0549881c49024000100c201c0340d41c001e400c002041000c1c400140200e502505208407007022010101400074000c1d80080d036400e5050090074004214041580143c034021003240103001e0900d41161101c0511440c0076114030280e1104000024100c01041118080b0383c1c001d039881d9441c0c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606396214 1250 606394964 606395021
    0x3010f090b0c0918071419020f0708030d09060f141b160809030f01060e06040e070e040204020c0f12040f0626180313081501081203070504030204 64
    0x2030001d031107204040403e0016440644801000f41800c203ca503001d66031300d841d1041c0035541030f0491000c809180320300081054a03000c2140c14042c141c0000d9080b070702409601c04506403148841d005440d10f507001000b080c21001c605030031543d0440c1c0a84800610050882c00c0c2100b210b1002a401001c1e11540c000c00054004241030b00d604118202d840c035150454400c00002040da207083700402c42c1da40840c80c8005a20100000148424000000c20900d501c0d0300c0d09181d81a011550707144034504004100140e600080b40c1c4ca400c5448600f42070000b62105e50030403010b03400100300801036103c0c51a4240820703204000300342c204007000e40340c41c0d82c845c10701e5001480c0c0400382d003005050001145251040645903180300e000381c11000c4590a542e117400407000810b0000380b407020014480401c03903207000c2c40004214002c80303c09030115030000e0b94061540140c900c0034070407201d0b07581180719840014095100210744c4120546440c07450262070340d00042c00c443d950072511148460a2104000c81d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606397464 1250 606396214 606396233
    0x50108010b0c0d0309080c06070305010305060c04050306010b030a0207080301060903020307061707030e120c01020c070603110406080a1e021905040b0405040e07030b181510031101090503010f09 85
    0x14020380030528940180c2e61001d9541d40355100d440001c04d5610702111083c4011001526030000700042520040d0a20040040182c40203000950341c1c0d000c0c05010075400001081203e048441c0503001c2c280d81d03840c2c00950b4407140c000820112129808005c0640040d04402c029070103031507641c403200d034031b10700b94010316162003655004542403010141c109aa051a94040e10742d01490b00d181c08105200081c10b0b480c1448a60420f00500318004504014000d00c1034028249860002d0b048800240e600c0b07404405a5580c41c8030000901e40030402882554070440d800769000303c0e207003404103c070f880140c0e989589050b040316510a20342d002c18000b40c0c40d049284401d4402c1400d241c001d040030b04000c00c60810b80b04500c10360b481a0355a0b03410b1000081c1c180052002183c1040210701c0601d080e0618144a440c0c100f03451160b0300881103003484030426800710302d000d0384410000c40d00617810b60750b1b040c00303940030b80001e18184403190070300140729642400707500550707901e181d00400d00101614010101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606398714 1250 606397464 606397469
    0x6090a0b130c14121f050f01060801060c0302030403050a0c05121507031e090f05060f070f030e0c090403050406021207020f010c2a0e1302100f180e0105010801 70
    0x6444804070000c04650035034881000d03074509580b002c40d040c403071100260050044031501c44280c02000d010346586080c9004250903565001c2c02880556030700010905051b03024064100400c10b0038006107e035910030040c2085041c0f10340110b91402d078498664924100c00c200d0100c3da803940e01003040c00039081c00720040641180c844000d04181c00d698685042d4035800401030b03c10159511203a8030941041c40200d000c025aa5508000c400414204520040d0500405032070511031240420075011456409604c42d2405580d040014000d14504902400d1507400300801c901c12040000c48030303620303445043d0045e0b100f9103030aaa45d80c94180b02904142903caa1500081750030b01c0b0b41c5015885503840301074500030920340740c1200000c41ca8602d00a02d0102c610010141001c54241d00f544231080c0c500b03003902c51350b480d180601d03a10240c00c1c2c0000400c51f43c000350130070741040740081c0040c0101d8503410f14400904011069281090306c80c40c00120030f078002c03401140144010459542c022621501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606399964 1250 606398714 606398731
    0x60501030e0f06281410050603010608040609080f0a111009020312031017030a080c0306011e11190212060106020a11012001090b06090907090f020c06090a0b 69
    0x301c1e11202440603228000100101d079030f20b031440c080c036242c690316516150300844c811800304800040400041d040403000c45414411110300c9402140b14a0280280c1c3e040303070095a540325059803203540d00703406050544400c9513064020f2040400a800302c40142804000c15603c0d40c0082002142a0380340c43c283e101010021407070302160b2005601d000c40c0d404206c8104d039012310342e2900c0d0107648180d24800f07a4081031106a0000c0010700e203020101c0100326a1050356100507403611040000501480190707005808500c502454591140031a0100201c0340c405081c0500c402580302071003420310030307030441076810703901c0c50310044085251204030b04d159141804000d0400390305000e4003a640384420400a000c98032442c2281d15942c2c4102008589a021002e1640421003545403080c00b8007500b00c001c0f00c0705200040080c0e02408c1c032480440c42010085d000b04100d034900848580144a01c2009009807078080204c03000007142000f03400e0003030400000500c61031440f41051201e03030002502100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606401214 1250 606399964 606399973
    0x180a1107020603090c240d0203060f0a1203080901050f0403033305030105090604081b120d0501090b1905040b0d060518150606120702030d0c18170a0b1b0c01060501030e 74
    0x6c80130710606058810f80c103040c0000580e40d40390000040d2424401d020440c1d8031140c1d113540450000d01d44003c80c14207038443d845030406519100311007400e80c2d104480b105240e90380b0a000501117031207038101d4481130790740b4110f0b001c40c042d0300c4440e2801c03950f00202c81203800d020b0a0b07003001182001d114055105076250b0141c8003a0a260f80c50064502c12501158520b0116500c000c07060b032002e00c29100d12082d5110540c1d17541206030740c164060b080c2485017000c01c0340380c020040561b052141c002c0c81c050346440c00c0f800340326040104210040509107540c0760400c403240001d00c0051854451580102010381c08900c07031007801d2000c1440d00040a44280c2500100c40500017540c984105503402c04c2d1040743e030419156942c5204030300c0c6020300000030004509080c4510350050b00025910b5515010081003a21503031a60521400340005620407882540480e82c00008201288903d036007001d40e543d4504440440e020071040c154000c40d0383e54007541d40d1407004001359a0144521405c8801d42e40180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606402464 1250 606401214 606401269
    0x4080d020a080307030519090b04030306050d1101030c050408010603050a0605090d0c08250303050103020f10050304080c0a05030a0302090406050a08030d1d0304091505180a1107020603090c 83
    0x302418000504104c0502d6250004030740140141c045581c01c095083c501007206000381c2c01d00c0450880113030f609401103031400d280072406081c104030511000e43c0040000346e0394204400110010400c918140c020000140004150044280070719001180114020301c240c51103030421404550000c0c00c02800ea40c4420074800035030744c121000c13008880d008800981c0f074112980c240703684000350801d400508030281100000f0181c243e40503070305a90003071b102d12000302c5000080c84010b509030310b40e4802040c800d100080002d00b003000141524a08042502c1c80c09549548161840e00054099000300e43c01282240f10384c10030f44070395002400b040303825404992804015640780d128042000d03010351740701d41e03180d142c868240c1004013510100a0071070399510741e1100f0300402888510403400c50035040500c001014682040314544004000c900410f00b9201e843c45c5000070013040711140d00048040c0401d10240e03940300d011314850b0300d011005e02640c4080c2010044030300900c03d04c01041c5000101342 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606403714 1250 606402464 606402473
    0x61a0904050a02040f1a160318141c02030703020315070f03020315060a0324090605030a020108160e04050f07030e011109010e04060918020907030902010815010302071704080d020a 79
    0x402045035403001d4441c3e04012503154261b094480c0d28564141100508510000c05500044000300d100204507c0310402d52155560901d803120507002c85c2e803052805048001c0340c40d022074048281880113003241c640c2943c83d40800d09041d08180c9187c2980c4540040090094004c0861241000c1a203011451450411a110b03100b030349035034106005102c0481e1780d01540d03009038020211400000f50b05440708070b440e2240d0780c4881c580c1c0590100035041003000282c9040c001000003030140d058617010450b03a04c103030300030740090340440f030340c200f04120102c031403003a600d43d489024001c145030712104400740740c0240080e05513860b0015041213a89020b450a4001b02c0040540b40c402109192040f030f45007034080018042e02d100d0704001c48403460001071050024250307041e200024401d0311140c00503900d5150030340803180c021501a0104100100007040490440c48045900e6414100141006000d44a0080310f0340a0080c1d01c802100014050140c402e04114040c07c0500e280f0040607104801d944 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606404964 1250 606403714 606403739
    0x2409150e0c190f0234090c031503171e07050c040e0a0c090b0d02180a051b030109051308070606030b0c04030c15110d020a020109170a021201061a0904050a0204 70
    0x440c03a0003100800d601510a6045858005c0304040d6030340d03200025a1200010f80041c60032a8030b000c0403901d445e15622110300450302c0e10701203030b400c94100002d40c42c007219844030369800104100e488402c0780042d00340301c003000e001620906014200034142c042c140800e103c02c9404040e000c01044d44001061000a40046603c2007664400400401c070483c25030301080b02d100001e0802588005004034141c1040d80310011244680c44c5c0100a00c095103640e50001c8544851007000c1e11810340070001440350345295000560070007415070720562251801d0312a880c543d003001030304540594441804005004d628001e903034002c94601580c1e4501403035030760f940020441a100e0908030047c9104520a80ca0260a60030009405402607030300560780d00b1802512006000f070101e01098042c1d4020441d840315400720000016110020640305502e50208030444280e120b0031307441c0b50340b6100042407585c10041c2e0003000030b4180c05e2864840b203250007040f094030310040601c060144140b2003001068038050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606406214 1250 606404964 606404983
    0x60b0a050f10090f06020303090d2a1703040b061203090a090504050c0402032a090616020f030304060c11060a141612122409150e0c190f02 61
    0x480c11480c071169514165504a030f00d50048007008510600040c110b600800290b1140c882c0ca0b041d07550003652418150740410481c0c40140c00c6503c1c0440c1c4a0440082d6070140c0c02c9a800b500384442403000340160064140e00856045031107082e00000e0144d2802c00d00e100441907140c01000c0d60818850601050622500b0f124183d0200c2c3c8501c041014080d082c80840400038000e001550f480c030b0500c1d01c1c0124403072800c00a001c6040040c25508500007040150340507c03170b004148501c1d10f00c2100403180b45102005042e82e02076441c101c003d00340d503402c0006000800e000d86075102d40000f6800c0c0300000d40404525180101b8041041c01407090740060b1444041d1417030042c450302d5001a1a0015012142502c014036210600c0b60348101d00750000140d15280b075503408280030250390000001d82400040f0b4000908124090080c843d00700c050304400800701141e010312804a43da04035040d5601c1050b2003e603040350000a0b003207284c158026015400d407a290510742802c06a181c2e00940e00c25405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606407464 1250 606406214 606406219
    0xc030c06030a0c050d2f040302030d1d0a03110103060603050c0403030c1703010602060609011d0c0901111501090605090c030c031e15011d210a0b13060b0a050f 70
    0x111420b0f41950300810a550540000729030400c407400c22485003072000140070403014488550204441380d115500c0080b02c05495001e405400030500c40704040d00c01001321107122041001180051a0b5900d400e1304110080d401030b0289054040801c0001d0304944164100c2c508040c1001c0070081a510010202c81c00c5a9040c40c020070b603225a030601d140003c207200e030244007484000000080e02030380040c4d80b501981c2d084071031045c6030f640c440d40405180701d4410b241d50780414440016070321407129805040d0044042c10013400b606200070085007461a061224006000c0810051004403c0c1d0b20801e005010b0580d0100710300d05005102e155035020041a060342c1d51400000504002a00301a241094844101941450414000f50170061803140401400a8115501d103428040b035020307030101d691005450900103010156502c13008445d66030003400b15116105503c1d00150341400c48603c90451034048400300c41c40351501c1010766203500c1ca04e9104016101080c443d580d900c0350781c094400ca04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606408714 1250 606407464 606407471
    0x3180607050c0a030b0603010c0e010f0e010203090a06081b040b0f0702010c0f030507050607050324032803021b0a0504090c03082704110319060b03070504080c030c06030a 75
    0xe4500180381050386600d90303400070758005000081106042c402805101d00b14024050074542190498682101c0c0c0d10f41800101000a014640c0d8051801d542c58901d041c81038038a0a01048049038100455601000006210004104154058080085107404003080c190324007494100300d20f065001c6d2058001104100113808000c582c01008520b820b141c1c04080e6040030351082c00d019000d40c101e00002d075a240550000141d074140b0490403240305582c1e000681c88001142465603c0342c50010904541500c521080803140b41d84204484071804909840052040d0140c80c0003402d0a5810b040d03042c18100e140c44a0007990b9800c2c07070480a0703400566000903500c4450400c0c109a203a02d0344050b10b00d10b00098103050b8881a40c00c071340b08003030341e03150001c050910007024402214400861224181400d0001c980b0032000e0700c44400f880410400c01003440c0d61208082c01c007503480bc0c1c5428010642c000340800008009114919070072030220058603142c0e030590041580b51000400303903d00c0781d50707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606409964 1250 606408714 606408727
    0x1302090c0d09020a0b12060f100309050a0b012c09070510030f11041e030209160203070506090307120201020325051309050103230a0f031413060908031806 68
    0x74141d01807510160010300e1210030765561042103c0c65484900c212400c50391201c001a45401d15803494100d07030034041c02d0603911803206c200407001440c0c0100101e51038003d104000c004219000303400350107040046c507441d010310140112001c0c903d84c0b51905180042841c810000007420200301c080490701c0a0780d0100030105641411401845400c5540c2e03204d515001c0b00c1d0004840400181c0240d9481c42c0507118150307614507004c084503403c1c3c030000303500c2000400000d61002e00c00e001c0f00240c4429004980c2800502d0740d030141400000c490301d01d0aa840800c100060013001902d86a824100380002c40c50341c04c02038204c5642c0b1180541000c00e400401e080b071500f40d807007041101c6891400000d10503034603499405210103444207100c25201815201403106040348014455201501c40000800c50301c01140e4495a0f03200419900f9401e0150228a1810035000035009144110f4846a2041c0d031074245800600445220f80155544d64814800d0303069505a421080d02681c0e400c550b0161110b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606411214 1250 606409964 606409987
    0x11205100b010504030515010e0901060b0d1802060304031d09130210180801020d0f0c08150a0513020306010f020607020a0803040c05040e0a060e0a02011e020f0d05121302090c 77
    0x80b899000404034410070701e221802907c076000d0541690030b020400101a00d42c840c50310700303a0354640650600540d04000541003d2010341c01513411240860b2840c0103226107800140c3e035034008580540100f00b545900d40e00752642c081401542c04002c403450384070383c24661000e00e80c000c41d0206c005c1c0a40702021600c50002d02a125045080444036038500e40746468040ccc5034081e400c0800c2d500445414202618850103150041040e034503400da4585645a036051345015800c0c005942c0680c00c041c0f0441c000c140c40e2540d00f45421050124003026941e03090050005084070802415141150000c1050045085d80032400c0121290013901c233035200c0c0c9803810b22000d41d0050381d010680c06403915000d12601040420a000202d001308010443c602c580201c040e00d92700b0816001b030000364036800303101448200e00032404250785a48102c8051381c941d001c1d00b41c90140c17a030002e00042a00130030002c9001036104501da07407002000c00d07500c0c017070842503010a001c0c20018005001001000c6101001d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606412464 1250 606411214 606411217
    0x1e0f030906150302120d022119090e0609091903020309030703050708070b03100b0a030b150d18050307080304030c0c0e0414030c0a0219121a011205100b0105 69
    0x8542110781007010010200050340c030b0060920040f03000302045c180c082c0b9046804a026108849940c000d00001141807891509240c0383c5500342c04031401c00d000e111202d42c080f80a1680446480e210401101d0a0029003003405000034034041c460781060b0108210b903071011030f42c1d42c1c10500080d003045441d482803400340c0c1507024101c884e070340620641100205100000523017030708031080242510441c0e82c855600040e64802141d90250302403407007000b040f02141d070500400383c80c000c45ca4002405c401403000603031550740c4150714048178000810500081c11322072059201e8a00980c2c83c9410709007169488079100c2c042c0320000340514201100140515002d1803120307032903e90084107103045a850301d140b0f0b00e041c9403d44050f103c0ba0034414480b115480000b086650f03c003680c800070005004540e003004001c5070540ca04c0c105011040c180001d6081c1b030071904008092103545030703074201100c105c07005101d21340590048000d0b0b0082c00e0f501c4042040410320001464140e50b020802d0360000740140c0d4035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606413714 1250 606412464 606412481
    0xe1f2d200a0e061b160e06060a020c1c080d0c030b0618060c010b032a0d0206090d150e15090a02061b010902060c010b040e0d090b250b04060c1e0f03 65
    0x46002c0c21541508200b0812014810346d120501c0e0482c1c1525910184400780c0286400400983e202d007181824078600818601607060103c804e803003003507202d80d6400340a03420032000500019120050710360403940500984215200c1a03d4060801010071390f15000c144015907024040c50000440d0000ad4030203400c250010140541211512408503000122600a1000c1403a030301d084204a030000c1c2c5410b682104c00e46070014050341c07c000c1d18208108070900c2810003118030410b00c0d00103990041c2c00e8028000ba141081015000d00b890038003280c18401d100a141100035000f8250880050313459000340c0300d45084028020050001c1442c1d418018000004003a500060100708903034081d00c15040083c412200740c070180214941100741640d6811084003c1c07002c104100c0c41440351590b00300241811190002020000d00c090203055080203090700001e4a020031544204002d00020340105505c41043d458200700e400c40c50700b100350a83d6404002c0b48200a240c407808003000b840798000001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606414964 1250 606413714 606413767
    0x1107030c15090909020915010314010824060306010315060803070f1e02060a050a1b0602120c0403020a1202220f0e1f2d200a0e06 57
    0x2032035807280007408994002900800000da048a008620844036008040400364080d114003102d881d604001c0d0751301405981c48604150f520b401e07688028076082640c40c02030140c44040d00081e440300c1c1c3c00143c406001c00300841240d00310020701440b500d0016100c1e044a42020001081041a110841c003620036584140e00b28403022503048140808a501510741c01d100703450070304d000010310246000e8807070a108060743c03100d020f01c5981c000f5030043c001080103009510b8418448440c3c507000f102e012a00160688030b2550100d09110003850106106801a2039000c40c41c1c28507280d07500082070720507240100000418410400000c540f6409483c0708410040304810901c00c00f082400030040101d5a0070410240c101034000b0500200850348003072241030004a00d0001c440191540c000d0111b070003074080d40c60010b00f0011146075030a440040c4040c1c040341d012401441c500d42011100f01e2007081200080000c01481c00016000540c8205800040d5002c984500b0310000d8034044480e212250350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606416214 1250 606414964 606414983
    0x1a090d05030d050a0b090405100b0a03150f150f0b0a11030c0a0605101a1b150f060f090a051b0a02030306030709180f02220e0f1c110703 60
    0x80c4140802c1e0085807003140713a150100700c25141c0d08200300c210700041d1000380440c6c000c1455103c081c409a00302186410001c2c0c03200e40d8407941d95480d0f40989042c0c040c855034841d42d0b00711002c00f5101601a035a201e00c22410408566814041ca0301d034645044c1c03103140d240d903a00140d0380d8a542d004240f2401d0700c49848041d00d0f00d50307180303003091a12484072100840d4500d18000008104410959a05050740e151402050ac5402c02500030902940712521590446000041000d1901c5040100c81f0400c0680055541e40c2c1c101440c1012003418007900a0b4480d1030815281e1449845d240c40550344209200d00120341c0e91035a0904507001c0c4858811441c0565001440030822034001001394001c1c48143c04503420542e8503006d52007110f07103000040c822a0061510130020a04071071115801e58001820742202c2c4200441c00e04034002469903c403c076640780d6500b02c1d02820148090b50308025041c0181108060041180e91a884441070b10424802c0b0820042c0145804011060140d0ba201d0940c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606417464 1250 606416214 606416227
    0x120201170f0601110303151201090c030f1101050313030507020d02130c1206030201021915060f090c0f08130c0e0702031207021f0209041407031a01020105011a090d0503 74
    0x3401d886a0840c2d100e408a6250615444507400003c1181c0c4a2192004003400c050901404c121010321142c00400540d0340b1840d41c1d50100e803140c2044402180b04010a9116198a1a0204c101c070262940641802028801c004400340346000401c000341e407500e07126a0300e004900c002025000141e0700a90006020006140d4000c2a580401001c1d41152602403044040c0900700301510b2040c00001e0040c0c0000d01140000c802c43d901c2401418807550b906e600c06907011140604842d000e5101500e21076940c1410070a00c1407522401640114628015010b14050716000d868000060001c08444500d00d0756a82441403040000000d0700c103210101c0010300701203800035525080302d500c0a25007241000070400e960b000045034071814031104019a500716244240300029044050240d800684030f4503da440d42d00c1c00c5032980e214140d03545002640c043c651b0310780d5500c01c144c540d0300d9040d685404014800e40600402d50405084e1a05216995900315004110003a0801200410901c80412031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606418714 1250 606417464 606417481
    0x52b060e0c0910030201081b0d1d0307020a0509060102010617030403030f020a05060109020a030b1002100c05070b0f0403020c21060a09030e01080402120706021f05060303030112020117 81
    0x40e44859515044031032100480c1d0400800e01c41c02c2e00e500200e900f042c0030410043d4010380d0103552002110400c0400a01341b5041c1c00301c56440400344134041035131200300c1c0b2441084c0011811100e04110000c50074500c281e404034194201ca4080c442c854000c400016005a00c01d402c5039000c1c1100a582419440700a100301c0c0d03030798010740400c40200b00d0000c220045948001568281d8035040390040c4081e0b441d008560000f5844100c000c03041580310100d0f480075450b40045403c06030007540c02400c000c14407640080c1100c031902a180c00f0445d04009290203c3c425010041e007100c02d900308040940c4851401b03030b140c40c011a282c950000070140c0310102c0702d03001c407500141d01d01400b0151022980c42003c6e0604607100c2500041c045560030180f880c595224080481e401440588140440c250301910f241c0340070160752245005070b1002e449030420002200c00410050b00c0c84006104a05002000076101d0005018a200c1407a40460301000e6a1007600407081401080d08042580d0815409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606419964 1250 606418714 606418721
    0x33403031505040203160e010905060309060a0507050903100f150f06020c01020d120509071e09060f1a0703031427151f0f0b0301081005010f052b06 65
    0x441c0501c025542400182400c181c021603101d00350203201e80301e0b00c801c00e03142903818070151076920b81080342c00200030410383c171000001c41c040c0320800b00804952a00c00c40301403d94600410380c1c01004002d2054810503100001c030a00c160300800000724016048000050040020941082501c4504c490003c0c910301a000d11f4010345546a00390b4190a59113401a41d0302d491007400100003030510034540c2e03003151640d0311507a00280000142c6448036541c0480000100c0c00000300807041d40e030f0481c01c1061801c0c0c1d20035600200030100440f50b00c107141c04d04030020306682c1c100310344051000090300006c140c461350004e21002040400311035103041c01148170f18a10604254903205581a111081c00d61000280500b03040c0103643c81141c056503160b00c445200b540c244100d604400c15003401168054401300c1407000b4244482d072031038596140c2030902d442e120400c4103568031649004018480c0c0303501801d1071001c2d20002c1d10358844102014690f001440c1762000e4400801d48003000c01c42c1004035580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606421214 1250 606419964 606419981
    0x61e03030d021c0b0906040902180f01080c030c150a140403050a0b01060503090d050c1501090902090705040b0406181508040303050a1802040b0a120b0412050c03340303 74
    0xc000e940e880a010b0f02140c00c4480c1540c00c594403d035408005030341850960088200c01e807000d05038401050700b02181c0381e01100251445411541c141d03005100c06a0b0400c42c05011940032001084800080b50116841c803515055007464031000254009540f40100204207544400f4059a13984940e81d040580d10742c2d101050440380101c10f50b00004810707200340d0a89009680b8240034210342424440269046d6021007070202044c003600030f00d8101c0e0090800d90900900e080180840c01c003525204000540b58002d01032028480140428003800005070140d0382690b1560910028207611903800034810640c0794441e00b410010b2100950100d984140c409014030310a4409008c292905800c0c54185c0d42442c0040c803d60341c02c04c030050090716040d0040d104001c00070702034040642d12024100010210380b0f405a5043c3c48076000e1100b0400a42a000c20030114ad16200b824080704805290b1248521030a21408880c4c80f101c1d10169840400301200800d15000b000c82141c00c0c034900540900b03402e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606422464 1250 606421214 606421237
    0x20f1917031312050d030903020c0a030807110303070302030406030b0d0c06030c080106050406140d091a0403020d031505061309020d23040302070509090109050102030103031223061e03030d02 84
    0x5800000ea03000d550340000103484e030300c000139101c1c611807040c045005295460701941140720340011b910498a84460341000395020b003010030750301d6400b42400c0d01400540280b040c0039600400204000c81e03408000c2d5419517089240100300311413400000b1310301c40304140d80a010700d41c24a800044d8560103520144601c00c098940100fa030307a80300d000340c40c58081e80c4154004a600f00e207a034030b03650010b000140305446c3c3e64000003c1d90000394640261106000f107001010700c1c0c03c203092000b403580400400401a6151034280b0180e1603121001340f49034003e1065600030800440c104562241d41501030b009000400b5085488111616010b00501080301d01c2c08a007110714a906603207441d070340310428410303034040d001403219a10300302c180300d40c050000341000c0c4a075680b4070008001403803e000543c02940a5514108800d13030001e511411142541c00c040f0140c0c0384554500100781e05031040c554041c00031945070318103880343d1003a214000c009040c05c80e45404001f5610188440d03540c0a0440321085 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606423714 1250 606422464 606422497
    0xc041109040c0e1e01020f071401023d1b0206011a120c03060a03050105160e040203040203070e060105040509010f06020717070902300609090307020f191703 69
    0x4800b000daa0844850700b969420034904d1300e420400a08490000540c92418411a40c46820704100c060514010750000e00104540c8a0348980b9580d04003d502164210f9007001e2000040c6104001440000849030150030315020000e26608484c540c4485141103480e50380d0041441e01d600b0094640809010340080c06c61040d00e120810703040d0b482500c00c0c0107030304001d48a003030f25650f100e20090340000740941e9025583c918003000182c1c0a0161743e00490945042e85460804020050507956008050500039031050041001685c0c00144403821a541071400140ca0307110f040c0100d504d8456600401e8004682e2030000a00c8400308442108540c601c0c0d091ba08007a03290404c0e4a00c404007060f1022140d484032006000000b0240c2c010001c41c0c0701200c044804080c26a0010f0820116040403800810710704204013440c2000e840c0c90b03501482c3c5501440c0782c8041607001850a94051514500035002991907511011a0310303400c030090103000c0704120381c210450200c55529841540742151030b005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606424964 1250 606423714 606423731
    0x30501060e030a200d030206061309080919080118020f010203040321120c02060601230f0f1b0303070e03070303080610030b04050c0a030608070e01030b090c04110904 73
    0x800d450040781c441c0c0081c0680166641901c131036501181c0b419141c0120750b810443c0b0592a0340d15511104501d100c1e40107088149011810001203040c5074852102c40c81c11303c01c440c000120502c08607a0b0b100401c490000242c106201d10009910780390300100c2c0190710702030b084a03004051005401c1480e10032110340b0541980100126202e0259200080020b00011003113000d10b0b01300504c88180e40c1c2d051401403403079006698801c0a4030508004140540c1200050142075644594031420750500c0e0b440c0d040d4034004103080e220303152140c146104003011000c201e031b4070081e007507101b1101401d1080e0b500a40320f4209400e020380320b500c00d90300c40c00420047c2c48150740750b0901081031801c0747e8164440020340c4d52180188404403814001d01020155141c0a2040950700c61007258002d1800350386450300c1e82d60001cac000c1e040315000d40140c10140c0c07002204000800f0702840042c15203074000e10b60b12540d16180ac11078907204068120075071240c1480410203245060401501464508580500101d503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606426214 1250 606424964 606424967
    0x70e190e1e0612031303030e0f0925021005070215130206030c0906070c061101060b04050303030402150d110909010608161b0c0e09012d1109040e010c03050106 70
    0x8902808041e041e440c0c1000040151404400f1805440c00d03003c10f40c0d01c4c1ca4030038684030500783c02d0783c2c0040b004540c0c0b10303e4030403180c2001500109084025a0091103d0803e0201d00d0500d0303080d00c1840c00e42c07140000030f944a05100740320340480c0c0c01c03034124144110300300341c800692a080803240200821080c2c100180c02d80740343e40d00c12940326402502c402d186031521440d074100e40d4401202250440820070507900002d074400c50380c2004210303503600c1c040700c1c03250314048600f52142d03a1f002c014020000e0009001c25036000c400c0340c0e0000d90413900488c803a2200b09208120340030744884508200d2030070b0f0b02c05500c491148024244084200d032900e14a81c1c90b640144c03204081654041e020b004600341040350300e40100b864000b00651203808810380360391540c54280860070351f041a107176407010a0a10400072002d00501d07400c52034802000c8112a01140410940c0390820b060341c01c1c4c940c4440094444aa0000c02c13070b54214400b50051003085a40300c1400d01074035035400ca000000e4a01b80c00040d046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606427464 1250 606426214 606426241
    0xc1c081237091e11010219021806031507030b030706080c03041419061e0c0206070c03120f0209010f140702060f0405180703050f040218070e190e 64
    0x410781000404041c4a190300410040903020001c0f6400c02c042007100510040707400100050038440e048406080c809500020700b0803107a8a155080708800903a0400140d51322107190f80c051a1000c00c24906680d1031f40068a415005810000165000814810b003254140c11044512a0540450703005540d03441044a281d00700300c800c0c41c6021414000708000911905070744400030b03603542c11111780911100030b400d5081884902100c80d2a0750705055450149500469032558280c801c0800015034407040207519480001d10308410000980046030401d801030403590021504101c080084840302045100203510a548003030209107000302d26401d8038824050760804034400e071011400c1c00255800d0000503003102528003804041848049111b4452403004100000998081c1d1840e086c0480060112070001d0400d1402101000c00c00003d6102c07061807201056414090100582c0c3c0d69804688061441c0d01095000001c98941400e403034078904e01e003040d21000c0225050765110300014407a0f4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606428714 1250 606427464 606427531
    0x2191805010c03050306062d040915030201052a0a0b1e1b07020f060a0504031b030506070c060e07032f030a0605041a0a02030f0109020c0c1c0812 64
    0xc0c030400002e42c45043c410301400d0170030541d200c5a108c0c02900700100103920a4a41c22001d842e01c040307000c0001152a0148150340c0d0340800704803503101d0858000908070b06c5100200300f183c0b00059500e0300d1008241c820000e15808110595407030100501d41501d8699048c7d5196040b107050a080c1000425070aa4990141f02031a08540c8168020701c4002c080742c00c601401e990000d040f28040c0c10648801009224500c40d59551a50312815841d04448013180501c5500c0d110030081d0007400040c4000a140c1d8101d038450070300c0d202c405014541180503100041d07458246000d200e90010030821510003080d135020703490102055152690302c0340c0443c1c15a0b01031095140c1d1140400c0d4010171a03a81c085d54202d40141c28803141e50f500102d0b000c01016040d00c1380c8406a500008001008404074850ba014000c01c840551805041d0544560344500d0445c500303205000910503112006800c00d40100703080c1e40008090b450707900701441c070785605038100c40780c40e11035041001e184c02030500c40549122 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606429964 1250 606428714 606428717
    0x30f050601050a0801060e0103110f0301050a0b04030b01060e060412060f0b010f1209140601080307110105030f19020405100306081b030d08060a0306110a02100e0312040602191805010c03 82
    0x41c00e03807a001c0205e49058001f81c000b418035969401e803500040700003004146108090100c5c41e500c1d4505800e102c0d210605034001d03111002e003070000340002801600c80c6811102c851034402c0c0648030300e000013100c03841140d10650700d130012800c05100300b12083c0c00807404003c060804000d841944030040d541c40e030004581300d00141c1c00b040410361141c0749900031103885020f940c0d503c035450200381c900c510304003082e040702001e94400300b8140c00300000b082c0541503403107007840c005003942460341c155200c204000e480c0409241c24540844145240c66041d80c00401c8024460700220b82080703005401807a040c060307000940100c40d010240c0501e255201c0b6606080500200030800306503a0856904c60080c0500d0340c820001d0f0b5000010481600540900003828107200b80e880c0c40a01c4081d1070040c1c00f403500d0400d1400c114059440c180044207071020f02030684050401583c0d01c0c50420003d00c03960741203004442d00c260100c0301c80c0398411911010b00301501ea0b2084485d88800045d0744030390b44600b0040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606431214 1250 606429964 606429977
    0xb040f0204050d14010b090f0f0108030a080a1d010f0605030f01051303200706090e250c08070804030b06010909020705030a1b0b0c09102102030c0408070303030f050601050a 76
    0x60141c1444c03055021800300000e4a10304002c001256142d00380d8100882c400020244101094501412401400460015403070058580c40142c5501d10061a4404540e07072170300440c03148190081c000d031004a43c18002c01415021000310b50080009001d00c0d030184c8110b00d40f2590070501441501d01403191031403c0c805140050f50212240c0350701c05400c950020100c2200861031700100134039800b510040d150f101159080030b40d848460302c0f0041018000100d003031a441c3c901440c0b14842242c4055500e0010340c0e48015083c26582c9218030f1300010f180610005000090002c04c41c02d8a001c0e00090780e5001000d03943c0c40c0494142d0042c440090140d410800c0f0b402c1095005a541241c10380c02d110080d0802c00684d00c03051607000c0101c44400120100044e25000e910303110031200041030007070800010414141c40c042d01d5141d54213240030100c0b0b60000c041039224082409550003041050106c1d0070058581c94000d000c0c2c0304e00c0034040360742c41c28580441c01540c05441601c0f100110b5541d40c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606432464 1250 606431214 606431239
    0xc10151a0d0e0f0d0e041a010909020a050f0c0f0f15010b0d06090507020f070611030304061814100606110c0103091e1406060402070b0a24090b040f020405 68
    0x1d0001c007001110b1110340d11031103821840720031040c4281e410328551074443d1042c0200d03039424131064544410300b100c14440d2002c059002c5a030000007000948080910040e241c0d19621025a15031085480340a41164081003100c4003550001c1e1000309020000142c8481040c1240180e980c0c00c0d0070342080c10a4021a401404241400700c09400c080d040004040b8815542d08000c43c00c40c0d909440e00c0c4016009401c402c80710030000c01c2110020503180c82d04900c0220b9405080d612030102401c014045074a400d0030500f6480407411021015411400c1e5030031507040c2d021000d6940850440c000010b42c10701c000029618041c191f807109020000010f003842042c0240110018103143d401156a203a8002079050080306011f0b240d40c440744122407901000c2c9580388150f16110004003420f100d207004000340000113010350ba40d99040894400c2c003040401a040c500882d902c8090941810080214000601000943c02c61146184291010401c0c00c00511036002a8070860040d41e40100c042c9280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606433714 1250 606432464 606432487
    0x3030302090406090207080c0d020f190203010b120a0c0f0b221a04080c030604080901211a0103051b03070c1a1608100e040b06060c10151a 61
    0x144a0500700030400201c0c10303192040e08040f60400312055514510206540349004820401000e00308100d00060840400c062041da40e82d40f1100381c00003821450b031036403c0840d1000d42041041300c0000b07051000b0b02100c4e01d50780355940c42003002918200680300c40083c055481e000c54a044d0f85a00c24010305d40305608500c3c0c48140c840c65180300741803101d80c0000400ea078441040b803200c003c1103102c81d0765903890070703510700c1c508100642c02c0c40c805c3c0c009009100005e0400811a002d0010a007030140f004413a02c031070402960001c070001651141042c04088445680072988146808262004c01c150307180c9880c861000000c0f0501c0b0380c0c0c0504200040350704640103080c1000f155100d01d40c1113842c4c41d04031180b0301440d00240c0d0500140401000f1000070180c03c404c8859205051541004440b481c010400080100180004e405080950045500d5854200132606440b030800c0c201ea444031203a959510080154030105050311031000700c082040103e80c040c0e18944410088074030b0034401444031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606434964 1250 606433714 606433717
    0xe030f0703260429041203060506030c03041403120a0204030605090f1f0908070f02030106060c051002070f142d151305060103050606130203160e040f09080c10050105030703030302 79
    0x4200055440c0040040015001382c1e100620840c4901d500d0030b031101c140c00b0041c06a40980d0099441f07950284100144440d1010590f54455006001c1c0f142028516003001e0561169001480e1020f09500411a20325040c0c1c009008503071044204104540d0703441445a01c555824001d0030540c4c00424003042e00300140003032200140740e103190005034894180c0d00d418250b8015a002c072404100c1081d4607003945400e00c03481c0c00a014a003080c030b110f0751096654940b1003129020400c0320300c0c0d010034080c0a2020746c0b00c0b68078103a98032803403001e24041c20507849641c072680c0c5424074000c102050100d0420700740c03100c2c02d04d80341805d50005200c1e080750425034401c5000020035054610301d5501640c00401d10822030140210700540c083c3c119400d0600130300220000025003a202907004100340a8410740d008010680e1440034500b0000142180c800074015001640da07403108071b41404900d01c1072000400081c100411480221481107055403c0f85c02521000d1040c00d501d504215001c0000c24081d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606436214 1250 606434964 606434993
    0x60a0f1503061a030d0f0f02010b06040b0c210412020d06110d150302150d09050d020d03050a051312030f02040b1b0601180f0e030f07032604 62
    0x510119242004818445940301507510540e10242c46040079403030012241030740da0440c0400d0380505950711002e4006005c40c0101e00b448400c000800304056104c038400c0d0700c043c1807004000d140a07582c60390388904d204a6000440b03000f00d40d004e0080c1d840681c514802080c80f400042e0072285007040d00d0f003074044103c20302d12842070f608a106540c81400051310383c4a1000b02014042c0381c0d903281d07401c40c080c0c0c004072400700c01d03103440c1488005018805aa10003000e11090b000306134a20f5650034240c0003240282c11b01e010300030040d10801c4039400b0390580204d2000041c05856604211a035100703450042501c3d0292186108031451160f45008900311400d6001b11144900303000c2083d80e048648c040c00c0f83e20580c41525100c1c400306401d0000c24032411941001c7c054040202019410082080b003541062030151016503940d4000160880c159081154090411015030b0344903070420801320080da204c008100c00040018890b00000307402c08002240120140d009000103542c0e5170703200d0050301c0582 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606437464 1250 606436214 606436241
    0x150f01050c190c120206040e07020129040c05030114040e030c0d0305180a03080703020307020703020d1227030201052505100f02310302060a030e0d0c0302060a 70
    0x41004003007001082011603205449050031031494070721824a04000382c81a000f011403410042500c0b8003595490b006d40301070b0307011005aa140d075190300c0402ea004221402c459020100d4140300181401000122084440304c00c0c1c4041c0801001e01108940c3e40c070090190704800d032070f070807500041410160b01c501c1031000e040c41201d00e008503c2c401246098035408140c0c000070b44410411602c01408610105d041c2154001003945000035070780506982d0340240000e041543c040b001030707181c80c82001610001c5401070030202d041002c40c20b0080c5da6042c05803400c80400c000c18141d20003294545044d00b0b45544041c000043c0303d08503401100d50350701c5081c00310074001841401e0030740205181040f0000d1403090000780802c85001e24094240c2d02c2c040d41702c0101510500415004000c0711005080810a21840c0c6454411900c518206042c00b1b40004e074001002140540001d0f070107512022041000b8800c0b560381c002211021101301e400c2441c0200180c000c60080303070300d403107294200c8030100401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606438714 1250 606437464 606437467
    0x715020115030c05151204030c0312060b131e06030908071403030a320a0f05070c1106040f060503090a02131e0e060c07080c06070906080a05150f0105 66
    0x25104900e440201504282d4221085200410040c0b80ca02c4034410b0750b0000e1041e440c242445915405d0b01c21b000103001405100c01154040d04061080080840510364032900f0040309468003003203411a0000c01031070342c0107002400c01007050154054560700c0c1c1856848031001542c20a80708601408502c03400f202c034502c040c480c042c0050301801c1b041000740030100056450f40350161401d01651200d02100e108615240310160308111020381d88400644d207003c1003c03240e10351041400080c2045c005e204401440c042c2030040c102d0707200108824480c000c0c5811111046500c00704042c903c903600c40c2c0c84189110f040304112160207003011715440064541030307481f00600c84d000f2508000c90154144801c559840c0c680c0050aa29030300d143e0031815079881040004030300d42920b0364a0401510040301004041406000c1014480c100ca010a400d03100760750850030302c0000544a141d00e40202d0010a06402c0004c800b0040d40c41110310030000840d14401c100e01e901c0511035200140440d86040010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606439964 1250 606438714 606438731
    0xa060c0c03031406030303191e0920060d0b030f01020c010501080d110c010809010207120e0a0b0c06131511041703090f12010f1d190317060109152309010207150201 72
    0x40c1e64074501c9d450a80701c58007040c40c107110b00e07189554880b641c0d0700d944030300ca5941a500c4582c030344409840f051400c448001500c481c11030002883c20341d60300140c1c88a0740c0002100c0c0050b03501904858100c0743e1a0080310303840d00050500b0b9070420780600f03c6582e6640120b031a4401584280351180d0071150403000103190900b1511100145103207001000d020850b10341a4500f58103003900d80d2001000d02082c0380c0d040800e40c3ea41651030702e0000d4040f450340314154001400b40030405921484610810341e00300f007038a40d41003510f041a00248555544c0d1f201c1c410071f03092884004001c88594000c0104500b00e5802804100440c01203400116021903607116914016500c4a11500c2d4040a07062601d6180031900320352079181051000711102c0700741d001d4010700d000031b0f00444e03d20110244640d401c1510fa4500c80100d810271215030141d0702c41540000384a071001e802182c0881203184100340d05c0f000003521b0364004410300c596542c041c010381c05200100301041c50305012502e001c0c40c40c0b00200308041d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606441214 1250 606439964 606439991
    0x8070507140d0206060409050606130209100905130b0f01080a0f0e0a05010b03030a091406160b0402030114070c2429011b06050402030a060c0c0303140603030319 71
    0x116052400e01d54022046400d9003501040166444401240c0601404000d81d90b031a44810303002e00014011002d40c80da081c6281c1c0315405540e0140c101600001c02404010310061800043c2d100b49400f40a60900701206444940166024030340043d08401715105030300011601c3c094014449907a0561300c940b08103015486005040c460700c9200028261089141061070841c0d461260061007136008004103000690400300b06070480700d80141010311f0b4070005010a0a42c80740e603075411118802c1820120804c52280d1941d4000e41c000e4000300001d4034040700510064106660b002e020410199108000415006007070040d81d06a03001c038510ba809a901d84801c0d210b0710000c1c0743d4078414030b0750440032131010721038001200d2109186c81c03541c00103200c124a000c0040b114002c1d00443d1180700141c15520f04120250740d07030364081070401c103a0385124802007011001c0d21041700064100401102d01000711b031051801880024040c61035900e40100d040c4054079140a00882c030382e1101040c1c00483c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606442464 1250 606441214 606441233
    0x51e03331c0309090614010f0207120807030e030a081902070e010e041208060604140d1a10080c0618180c18010201021306030b0102030d0504050304090b03120a08070507 74
    0x507a0405100034540040c540504200c3c440e80000c00d903985011401c000120700c490201000060030300b800c8000c1a40070004905003040c0f40c0018070001e44004100341041b1080c402010002d000360f1b6031080700e000c500e00b01600c1d0b40c41a0b4001e80205814006041d494190f0040005039403450300403286c0c4580c2c4c4101034125148240d12244084e044d540c100401e0103600309542d0b038507115a02e00700d1014a008000100d09001b1030049040c4108100c1d087e12007038540345600d015080d000030f82d051000030000b060000c0248100c0d01103240003490300001591502c0011241600b190091410341000001d62050303041003002c00d40103601c8414903600c50001ca141381d00c02d40c0204030003020195a0009002c00721401100d111fa5141160b03c100000c003c45606243c2d038200365020f0f80382c003007074a84000d80100d00e10f000c2c86040c02031b524034100c00e0004010b80000104105e5503568010b00c20010711004154a1755081088200c82c5a42004400f000d00e11a0b00450340c001028103040341030140c02d0f240d0b113881 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606443714 1250 606442464 606442489
    0x503100306090c140603090a0b1026010e0d0c170f1216081909170f0c15040215071703071101110408030f0d060510051e0333 55
    0x14640203020f001130b4041410f0b0703000c07010090341c2061460800c01c1c60301e95290080100640361a1505011a0080030071a801c0c40007002c0300103403802060400c001c2c01000309441491021035628200644801140200301c40f1840651500d41111114441d1100c0d8104880703050410141d03a1304100b404200414100608050310500c54522110710b000c24a03051300103443c140c0c0d035051111440400c000004120702382a6142d400180c04104059680b42c841c3c1180303078889031043c0112012501d4004207440310090184c4040f20821507458500c0640301c042c0e42c80c42560003a4112401c40c00115070710b0108001000ad542c0304e6044c912b181290b007514100ea5420642d10704001902404550080030401d004404182c9000d02d05c503458245420351060352441800c08407482d4070780110b03102c05041060740c485401442e02518445020490010041040c1e1103403178030754102c4505260380c0011690003004d80344900010000b1001155180e20700309401461880d11250520803182c80000340d846c0e40000d8406e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606444964 1250 606443714 606443723
    0x1a1905090309060304060e070605040e0603120307030b01030603120c0b0a05070504061b02040204062f0c19080307140f0d0903150b1906091d01051005070819030605030d0807050310030609 82
    0x882d2414404070cc00a510041c1c006403180e8088428132505902c00300480b42c010003903090000c0d9007499403005802600482d88080c02500d505150b40340842e402c03160145039a4070500d1490b0b110b541d401ea2071000c403601600c80200140007448103001050003404006125084002c009142179000d60029083e40e00503001000012000c510000341e10251102c1c40f07007182030303880382003219001c40d040540d40c07900380390b524078800d051407190380007003881c040a1074021b401c11006683d503a81c402d04040754888042a18404a0710440e40800c450388804100d0304244101a914207000700d16585410140070064210101c1541c1c3c3d9105015581c2da0303024510600c06005154204c1039854104058014400b55000079245038501004031005141040882e054a10840c2c80ca40010789a42c0215078601450000810480001030500d10716282c07400e038900403031207699050064a4480f414991a0003001c0040004100c0306808281001d000b01d020b55842842c01c41d500413072550300d8549030f050b9144500c003038a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606446214 1250 606444964 606444967
    0x3090a03090b0c060609100503070b0a021c09061202190c020108060103060e06041a090c09040c0e0102030703030b01021c0804120315211a1905090309060304060e070605 74
    0x4101604004070030020007a1014141c03c1019084103035440e00340040444d4482c411101c0081d12240020400703c02502020b8102d40003e070b160f8581412580c0014070345030242c894038a0800c140648a2044841181c81e80d0f2100c4000b482c102043e603041003c490900e051903004d0007281d900e05030401c2d00309200020350b81c03000701000b20b500000d003c003030001d4005410181002402d0000c81000310017160000e90039100010203114909441142d035503151031a03913000c642442800b0810a00030081c00c42240f085038204045802c5a006440d0b5141032128180960030520045c000301e802644561b045520600554020b9007000d1070f00040c0600d4410b040f400324036900e0600c03052145490f1042a0481281010401c2d00d000090501401c5900d10030015010303103614014081043e000000300c07074554018402510101000011540130100302d404a20300642d12091902200140c091180619418800395203040d40210a001b41c5510041094950584550f10801c400808000240040c10141d03102e5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606447464 1250 606446214 606446233
    0x150c0804150f180803181224090c0d0209040512030c0417071a031e100e15010e01030b120d051207030e0304060507021311031801060e01060c1401020309 67
    0x501403414a11404400740300c54001480308074000400c40d088586d00e0000344000740300300400181200e154008541c21030181941d010021084200f80002007900f040c031005859480510140e514842c0400d016403003180c0108450141c140003001c650098060015160540b10310a901e40f0503910589040040e1100006c04100c0060207028021040f040000642849450207021a0b4014131f4036410119010000010031205d08082e148448448d14907140d84c802c0340b42664100c00c4028551141d41205c00140c000180949403801001d0100b050585424049010107001100100661144a5088048420410310210f0100110603a103142c1d603540310b586020550403824502c030050044401d05007000c48400050300048195001d4468a00d030840e1a8501c0b130000481040d1858205c00107030385010300584d2107040d00c90045110b14010440a940078011000c01401c80307910707100301e07003010302d07060010701000c0c1c440e002c245102805055200141044d2000341030880c2c0c03003625048010342c05180704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606448714 1250 606447464 606447467
    0x3150c09120604080901050307021510030c060201051e1302060c100b030a0b0109150506210721020f0903030d0504170a080f040512070804050a0e01150c0804150f 71
    0x1000c075062144405000c85007802c3e912101980a8569440c0c1481001701c00526228400c00c1002c9000180800081c1141048889010320030002d01040c2d4040c01c5115010038a54014016580108252642c1c1e02e12002000e01d00f47d8510800703421541051420038050025130b40350009084a21517003800341c01c000c0f2000c2d681504544ac84501d95000e03400c0344544070301142c1d00d030050070304681001c140484c3c10340c241c00e5241c2d884c011580040360712800108001d2001e00302c1411541c445403d0111000003a21034001c2600c844800150b214018910f907070064404000c1900502401c03007641e002d59043c0041c000c00a402d50704210316680360340e59a1410041803241024a0f80b858a082d5404c41c0e150030720074800184100d40080c5007028003031240020a0410004010b410750140307800280e030b902c03181d803854148069401440350500c80c0046a80104e804801645410704840c5aa401c40b00c50365581141032352031140c200c0c404d85207241c062000046032603522030000e0060030350341d42c0c00400d683c0d42c40c070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606449964 1250 606448714 606448729
    0xc010c031814191d07020a1505040308070207050d060f1503050d14210403022a0f0a062705061317010b030c01050f0c0304081f0e03071103150c09 64
    0x280810303e14164003c0104090020903840392414042107082c590382ca240040e407500c2554040100f26071150340d60b0380310900d0180d01460059120341d5420034103407980070003240ea0301d49134002c4945c0802c150858100082e1141c0c0240c4001162080104508401084070680f800803507000307407484c0d00426440c0e0060b46d03104006041c041c4081d640141001c240380070010185403424458592041100d001c90300b45802002001107540b03554080302405241c4200720706509842840d024010004080405c2040c41e0a440303c1e001c2d2801c0b84e0f541c05548901d210418008508940c83c09800211000d0101e10740c0c981000a1400400301c074985082076141604e00c05c0003119072161300c1e28a07490046980300341e5a0114400e030380070b042440d11646540441a640c8168415580500324038440001c0c001011403002c50040010031880c801c00006000030340c02002500c41d040c0c4840010b0704100880b100141e0084440ca0b42d807200a002c07211120f8904090911001082d1041c01c601900840c82d0804d80c0350002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606451214 1250 606449964 606449989
    0x6020709021312060b040f020c011503150213120b010302151305061c0207050607080612150c0403050d030506270103020d062003010e0a0c020c010c031814 68
    0xe001c61400042a18840501c28180103481240c0b2100300b881082c05a140c0020001400c0107200700300440c1036102d41ca00942c080c04504100e0b508010440d40c8a0603200c00320f40c1141c1e08400e003a00c113a81d0b524000d000030743c001c0781c410140b10507552010600e4010505c040b90585d1050325810500c0d410750040050f0079030344a29115001030b040201c208680111800c00302202c00c187d60854a4171000c400c8075030a460032090003407410380701040360380c18084005000790003042c07a40c48a9034191282403c0c000e8010200d80b4506250380303d030081c615211011000654803002c1d400b07050741801d440c2e5482a051030000001500020380340c200b40216803074130001020414107111402070b401c906064482c9041075051102074401e00d200c008090506c031030303504a081c6102550800306040c42d0000c14108440c0c00a0282e003191000c44030004202484074801e0508030078494004100388402c0200458100250043c200e00700140880344038600301e042442a0050555001020303202175540c410300940c3d510b600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606452464 1250 606451214 606451229
    0xb0c010b0405060f0108060a050d05150c07020d140a080703050c070b0a120f0207020303070b0403020f0c01170601112e050c040303081f0b0a0206070807200c060c0106060207 76
    0x12050040c01e0307403031100413101c0503000e08120103a5900d0700b000a240fa007450f48002c1e002400300c01507500f0004003064400491340200340340040e41c0c42c0c0c01c001d11058000d0b103000a400078152a01d05011070718076403418890b640c0380d01c110303010268565510300f00ba40108400f100820700c081001601003a0510100015223401081241081800c0e54010138100c80d8200d80c0c06456507803890740d01c000780c81e60111250150044c0407a03a6403080752400400c200c0c0219070940c0113000d119000e030066000810100583c80050752404a83d507983e141a02d115480a4409818088c00d81c414081151003400000d0250100c0004110b009034001d542c100040fa00d102d583d0010383c90035040021111000056070207403600f41c5028103140d580c5210900c03841140e000c024941510740c01001030301c1d410b400f000303019071a100d40c25104c0680302d1001c252031018041c1c0c1c00402040e1502c002801648048038001c01195440007150081450403008c1080f6500150800f0340c0703651507010070300140e901040030000070f00c0342 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606453714 1250 606452464 606452471
    0x806060f01050a050d1107080a140f3a0b0a0801060305070e04030c1a07030605090f07030f020706150501090806012304111305100c0302120d14010b0c010b04 69
    0x480020602d21030f58004106010021600c2c40300f480d00c80d446046800a40621a1303074484440c00e16030f00d150800c001d0003000075240c03040c600103081c41c107054829036130303582c0c507030302d0800b0520303482c803a03044450a10800d44154070b680c144489030a207201d080140e00700000005011078801040c400c5480c9030303070050035660703040c040b040000900009440c0c04680c98100003078880e0316a031508641c0980c0003400034001c9400032100e24881d44040702142e00402c041d84003085042e540d2002c0c4103604a040340c0301d1202020400015400c1c90180d0000d40c0304080c40c1d980180703401400e82e0340300e00720360b0754010301407500300348550500a0b540c0280401000c0c25249000300708540c90b00c42c5c418840720710100f10318500814101c0003240c0707860341d812082c002242b008144d501c68120140c100170101d940d2203682d219078803840c520482e880c05080303012525074166010740030490000c00004400e078030680c29070071001e03694580c15030512080c03031009020700902c0000c0e5590f001070301c3d10a401d44d004460001c3c848c40c507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606454964 1250 606453714 606453739
    0x30801080a0f0f03140f09091302061c0f1d0c0904171614030a02010c03061a07080f04080a06061d2d28060b0f03040c08011401080606 59
    0x224646102e056980325000c0c03104019240380450380000b032040a600341c4040070038010480003c2e4030141c011008159003500c01c65a0b4a50803051610078080041d40021003001107003011101561640c00700c588440c0013017541003610515108030340b081d4540c103461102d10156842c0343c034002e01c9000001101103400c00c2c0c16090030780f075400005520f1010009045000944104000841540151031503080701c004421181402d130510384903800903c491005510705124540010b004e0700ca40c1c1d054070480e824135032003400c205400d054130b603100802c1552032001c14844034400305005e0008001502d2200040c00c4404c0c4580341c29000e85450390040fa4a1140012504448940c0140210780c406485012480480410601740f1100b05803014200f20707650a41042044082d8041d42080c13541c85105002c0b901d00d0107501d9804101c408902030360030b8440381040180c1842039010090b40c4c000e4000c3c28000415036582c4d01950031280801020301140c0b40c0b12004201608080c000035074081001d5682c0b024128 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606456214 1250 606454964 606454973
    0x100b0f12060105120c0603071115040506011206020403060507020a0c09020405030a060c030b0d030207180b030601090b01050f03011d070c0506041e1a010f1710020d0b0d0f030801080a 80
    0x7101405400e02034107280100c208070040400c05682195000780001d5500d0a02d820002c01c5015141d0000d0301c1445070510000440d114821090301c2241c100024004607401c19803014a00c1440304c2080e20919002d120200200d10030388140b0740500c126400405c03c80750300d49040c040d44015030b8408101039206002c01c1202e0f0301c3c04103542c1007081e40007500007201d191a5000f64010110700542d0740e0003100607640401059000100d000641d6584100c05020030001c820020640302d40d154204d426030440ca0041040c0206904003030b0ba0321905050060030180300ca0030149141d00242d000317131900060b19070b8400e00b2003000e00d995500484280782c6207180d10415180d40f680e540340500000e259040c8030390088641449a55040b9102d58402d5084814000010b0302c40440745081c002c000c0074030b00c1c41c07500080340c155148902800e040a90041c001c0c110080650b80020341090907221500e0781c80700d020045507a25519078401d01c920600706942600d8060800070111501600004242d0b07001d14000000314 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606457464 1250 606456214 606456223
    0xd0e031321020120010515150c0a0209250509010909090b0403121512060b0a380406052805040b0315040903110c09070f03021308100b0f12 61
    0x368084c204003090480420400710007602100d880d1900754030782418401c2403200d8864118041400b111031546130140320017030107079a02c10b16800350100e50140c801750005050030a500356000f805100c15500003d06222404102402c203a89080001c0001665492079070308000d401002d00221002000084140d41c0c0c5c05c011488042e0016040c40814441000d40e800190400908410700c14040b0081699030b050404410010110464035542003403040c4a80b41407c00c7d0980c12980c0407041d240d00e00410380a10840031541040c0c0700d1b03090760707403c25004074440c180707004000404c005d17544c003942c03100030031120315401460708011120507035030745046202d496100b010341c0d080e41d020f07010302c40d502d407283c006808500c5104035a181c1c000b07040580c114280758000c00b949580666003000c1c0c4070100c428004021030007900700c41340c1001ca402508496517451203603000c0c1000c01c540070b150110190b16410b0280c602907a42c0760041c01140c450080401505041e40715400c8003c0580342c0000e01040c4480803030700c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606458714 1250 606457464 606457529
    0x10e0c040603020d27030e060304020d0b150312090112110901050a05070f06051801020a14090f03150a11040b09011b080f03010e01050111070e09030d0e0313 69
    0xc0580101c1c20114051850b8803a0404080303161041070f0081c00c031480403075014117420096020859088100b001c50404c603007100e00c101d40c000c081440210726a60340052142024040f4600301044541180b0151410031420802004100510351104e400c680018400b1101c10682480f03d418856070814043c610800c0e030720414400d08100e9151032501d641240c203030050100190201060048020a00c03440780d0102e4007401100701250345044843e003100d0b00740d1045118203400207486556140b82c0100002c00341c107400000400b916000c01205000a1900e829412460f02600d8400203129151845d40702e210030b000f41003458103003401c1c0b40001c100c0d10340c0240b0b606603043c030030902c24208062841022680301c1c00d5001820985503a210810207241303420900440284201c8100041010340c0039800c0c1000c44040400141401c078200b16586495003401751501d00d25200500c1449043c0c08a8087e075040040101c0086442c2c41450a450060382500d0307000740d00c80c010091007880e103400c500e60a5102c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606459964 1250 606458714 606458717
    0x31314030915030c070605010b04140a060806011206030203010e1b0a080c10091205100b1e10020304181b090f0905092404030207140612040f0501020301061106010e0c0406 75
    0x46a6484c020319000e14441e448004100a103808004603128180388042c1040d940d4000854a20b60820b8040c0310602520307018010110f8a40340c001030310740d0301c1051081c20046210601140842e80e036030110b8250382c1c4001201d42c4e550814005417512844480061149100c221021400c01380ba00840c1c80d1600d910a00f0f95000f050403c252400b0640030b0406c00000705038142400710450720a09000d522480d4400d06402d1450400203c1000d81ca0107185c12180384265042d1800060032500410100d03860f45504001503000c03c0c0310025050780e0320720400200324a01c40010620b0703913810706158142d81aa29a80050201180c4c05100f686517035030850040d61104000061141c0350140d4040c0380c9081c01d2400f05039031110b007585004a103500c210060080741300e602210a82600c0e125080900e50502583c150064018030500e080e9040044920350814091441c0c3d007200c0d1032036202c0c6c40c2a130b8000d800c80000b050301c4481e40c9459043c00c0210303a0041000b07252102e8542801c080111072031189104410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 606461214 1250 606459964 606459967
    0x30a111213060f1b030e01060e090609060702011118030106030602030a060801051b0a1b0c03060c080f0c22050607060b10020309031005061c0303060602100b060a0c0804030602031314030915 83
    0x6c40d8982580204003500c4c0214400400c1d1030800c035540e1341c0c0c45046406c1c008601a41000c10841030050003030440440340d400f02c40e03040681644403080340f0004505501c1d070540d212070303001001c0b40462000b13502034058040b01084080c14540664251100500068103a2505448103800b80d6a0a0181c4403529014904103280b00940300c04049840719008002e403d0b04c041c0c420001c2040703045d52200340300402688175400d90355141c880490190104941c0a0b003151070400c03100e180320740260191024254054070000701107884801155040e041000115059981c07260a4403062038a001501e444040610045190a46580c0801c1c1c0714400c0d64116264640c407040482d4203503a0780300100c5610307103a0603600360b03007090f00307080040145c1005d00c5200007600420010010b081c2c07150040c841006009000345d454071960f038500302e940e441211000d984180b0140000b10024035070b40020b50003609201401140d039181424600380300240440b551115030f00400c0000d11b01e84484e201001c0724004607000a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 606462464 1250 606461214 606461231
    0x4060b070b0f0c0705010c120e010e0c0909100204080313152109022d190e060424060905090112062417060c04030503030a111213060f1b03 61
    0x20089014140009005508003400300042550001640c04048c11214082c4503c20514061364200c03a071640c407050184c1c1000004507a0390524a84040e00951014216521403069020000498210740c00040f0680c01c00240c403e00c80701c02071448800790002c050700c032440c0380740e11002801000130010a40c0504038641902d00405009610282d003444d00a0405402140c004107280c0340b03c4003001e500101d544078017880c03441302d08141d0401c0040c0e52755102c40403034803410700040d022114001001250b00c01d07181c9910810500640003040c500321030038003240d02d03d942840d44c0606607004a801042c0a0303803003200100070726204083d00d488015000100010202203840758001004d150140d41408007001f544000b5502e91700d079080412074a010016a90261a002808205d5104610018210394003d0021403182d0000d944840308080300005c0b07a526101c0480c8c096200f0410895840c202081ca44183c1c60501026004220b40444840c0d4100402008481e18031004407580d6404070070160380345400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 606463714 1250 606462464 606462481
    0x9120c1e0b0319060b0a080402090c030c07060b0409050f0a121b060b0a261014040201110f010f0204140406151805060f04030219150c02011808070504060b070b0f 71
    0x2110151085c00c40ca1591070402090141010100362030490040501c1e40019100c1d0001c041030320302684940c90a24540081a2a01e0001c0d10b0238055540e8401d42d01d404140015108000b04454984108098a0342c10014248500c492040c421500103000ba04c032504100c54140c01030804400f0751090300054074440890104140f1680364202e101510100f120340b9600c07101e01910b03811404094800c440e00e0a1503000580213440100866006500030b61002c50300544c09800d48062031103500085640403019a45840c2c00c0d59a2aa9454003144d40010107006056030b25403014103405080d00c083c41b147d4074080f140401211200c04440401842c0216541400924021000244130081846031520080d4016084960041c80100d100d0303206000b10203180d800c10040001100d582e40e68080015100712000d6800302c5020008904210319500101c00340346001e49140040c101010081c0f405074148400d00045410f90380101d000c81c1024800751000941301c4070b80950020791000e00b03045a4544000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 606464964 1250 606463714 606463721
    0x1e070e041104050a0b0a0504181e060f0204030210020a0308040b0601050405030a141510060f051b0601080f0708120a020f10090b1b03060f0109120c1e0b0319 69
    0x10070395215007881c0c24440300b41c801d5000312050040484600100e02d41c0d420401c02101d0640d80704284074003c0745400790124000c091054100b6000d139040c0c804241c3c4a580c0e04046801c8052a030301160b5010600f0300079424407414440440d11180018103a441c550b490261289000403c024001103550000920b60f911500c26107008110103800c032204660340f441c054541140d0404c002c08544103104000880c0804000e5680c055600321a00381c002504103401115038100802c200024094104100d000c41003050071243d09a854403802380189504001d902d500b091000740d183c000603030022405101076107000c2141211081c0300f41100d6a47c0e004410f0a9041c0303030200401101500405c00c140442966503004071020300c3c800c04400d000c9688a0f0b080101208854801d40c60f0070b50b040c00005d14600b412400f012510b80c0504212200d80d54820907000718002d0582c0840d210504101d0400c02007040c1813403203241c813a80c101080c1d0303074904000d480c041c83d003c010324003401c0000044076034165079403652 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 606466214 1250 606464964 606464993
    0x9100b030712060f0e0a021509180f0702072c0613050907060f44010801020702091302010806360105120105010b030a02071b03060b01021e070e04 64
    0xa01c91035280046090900040100035034504d41103052510038800e541010800c21040c80c1c1c0100300204051000140c8041a049082e10580011b89017920004c841c410040d5140310301c03020400c690651401a030002e081100c154032180401407400185114486002102d10340ca84902084030f0080c5d03614030000f080f0f00d4056081b50401854502400410040841c1050a46a40b40c0f9864040c203807115040301c40843e079008038500a03100c00785101c40c0000c100640001c410b0086402c481e10034209446444126080c2c2c80032034980c2d0300040850460810342c4d011039000780c034010034041000e03690b000070704406402001e00e8400d46011005280840c40c0d83c0f041912154907070720303c1800e816101d204030904c070428041c00f4422600d03031844400411050080d141070f680d4001181e41103440d210710600c06034202075000c459030591440c40740440e0000302102401180600404103901124000280c103042c180544809806d10081c2404840e000000310042100e0b858640040c89503545c0c14824030105526 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 606467464 1250 606466214 606466229
    0xd2f0901090b0703110d0801030c090518010c0801060f090806070e2704330e07050303030a0c080105032e0b030d020a0203060a1806090f0206030705130b0309100b0307 73
    0xb0030444281544880050420817203542102c1440044080943c1d5070b40d024031000b0725034408001c0900500c03005800c102c0e0807280f0483c041c00700d0b944413501d01e42559540400c0c00001070b17168004101e9161721540f600c00f00e00c03041c104000c40d00d08000c2c1f140c0d2101d60081005003482098140c0f00c18030f03100c001080c031a8822002076040e0540c0500d080c5404070006841c15103110145030003051608521031202582c480900e403422524900d02c828002c00f40403440b1161203907014045001232140c6044c00214412445440f00040320f030b078220400742249906800036030090b48a168800a4040c65500e281404845a91241851440503540b54054016940a26054007903001e4402a00d81c0010f00300005910880680c0c00c40c1d900c0d05c1e80c100458002103880b40354501c2400794200803c0700c550017444018064880e0588078502c98020882c20741c000d8840b180081c43c000b035068101c080c2568440041c0c01c404c00e0091840c10080713401071f45e8412200f1110140783c0d940c030960209075010000c44000b030000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 606468714 1250 606467464 606467467
    0x120f080a0513080f1011120405101d0d1e03020313231c090b070f1205030109110f030a02090a0e09030903070f05030d050c070b030a020d2f0901090b 65
    0x4800b10f840c3c03941d8040440450f680b1404174184010740032405201d0010030810800c606041c1c0008449810340d20160003a102070058031a81d46440216008041103d5094140310446050040e40c03d4074114800c0303041c204008440c0c03504a1108400421801001071398139015880b0f80362172103e03040300e00d42698010321060101007001c1034103c0c1c008031000c06527a400140d51107a4070000741940c0106804900800003510864284007010940019014282c000c1c540d140c060f8074241d17150380d01a80c15400480120740040b004000c20811030250043c5900078014081c18800850440c2c3d0180c0005891880744a40125288540340c442459580c005d040f4081c50900386e0500d001035948a611644c100780c000e018860000c140120300c048410100c550140c003c1540c018802411140c030b030429001e030300c03060054000000707407104501d025600940d064540141c1c3c5100840000c022640c1c405a40c5403c2103103658214503044800030305082104503186016680d02580004a0314000b258111802d807610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 606469964 1250 606468714 606468719
    0x1203090118030e09100506161106040e090d02010c0509010804060b0405011401120203010b0405010c080d0603111e030a1e0c18051e0411010905060d0e07120f080a0513 73
    0x740981072511041d01070380c10603600d480310401724103060284d00506410180c10064820901002040401c0701070061083d411113071103a1000030f1040e4800e601490000d90803000f4000520001c4c411b0082c10481800204401c20400b40040c0481c0a02c040f61411312000b84005014404079030005440c41c24001d008000641c0c40346003401282c0e03041d400c41c0c0e002a28441501450500d2403084030706131181c040625042c070f8a4a4011a101e02100c03c080b60804000c2c0990b200c4110300780140b4010798401c03a4103041d480d2001050000025074032002007050400c00d090640d842c0c4000c9040d0782c0158004490000d041c02003640918043d15603040101622102203000900400054450207400f0080009018076103625042c0c2028445070522100100c00460205000610040410700c0c50341042c181041107599400c0010001d411126a9250f900d40312407401202d80400e00890000c0c1224442540c0220002d0f210300c0a2804001c030300070040c5100140c07141011307009005840c8111062004c4203100c94 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 606471214 1250 606469964 606469967
    0xd0f0f15060609210309080d261611160b04170105281812030b0103050702030a03150503030f041e05130b180c2208120309011803 57
    0x2490242403029280307000c40c0840c0861041ca2041e089070440801c1d0302e03000c11560442411461014412018880c0241000030031140920a4030708401c07031501c0e56142416005018403100b000d80100b48188100c0b00c04015500c08820101c9407a40b10034030b0000031245555401038600102e41502d444490120440042e540c480d2800400030f48940c003054443c101100d240e82400d031042503c403195102c0150000052005c044502d40f180c42400040204904590460700c010001c90044152410408015042800c5130103000307640030780c9805c0c07070b0410032850500350094032402017203010400c05480c0e5480c15014582040844041d2500409480d82e900e020320040c8100d43c040e01c2655042507140d51004c4003140b084074030000f19074003c0c084100384580c02c1050001485a180d103190702010000c54107a0071801c0303a900d60702c140d0040752103d40d03d043c0d00d5401000700a85880724480303070300d0a03042800301e080702140405517800c40c80c8a04e5165103841524a01404035107180700600c0e00001d0040041c035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 606472464 1250 606471214 606471233
    0x902040216020315071707180e0604051f0b0706090606080601240807050a110d030e0f1207110d08030a060306050105100c1202070b0c0d03060815060d0f0f 68
    0x980300303c007107998012011420968081d01118000e000c01d500c480e480403034003660700405510681a181900c10314180300c00c41e0380e1094030f64105900051803181003210a0920b03100b030507000303160030414141001003410401550507a0f0b001d4600268404242c1c042000695009004000d80c0000140561925691000e5070b0f81c2007481520380105119520a45904070020700302006085071b940e1010729a205030059945901c0800000c040201001c0090b050103000d100b0304146940c3e41d40c01040d004202c0c05070b24600889c14070030003010340050095002140c0103004480c441a8080e40c4040c0c45e500c0d0f4800a14042003000c405401c46000204010322900150300c00400d41c4d2280f0070801050f40c0362401d200c0c0d103150b407404000100300d00f2040c1d18049103ca02001c0402820751040701c01c6503845580080390394202c0c00340084103500030400751165940501804014100540c000c0286409209401c820350303102401580c0500c440c0e009032020320060f00012410a90031a06042c400e10303007450f10b1243c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 606473714 1250 606472464 606472507
    0x20d03030b0607080d0b011b0f0201140c030a02070503070b040e0a09240506180903030708310501050606071a15040c08070e0109150813020414041707080301150309020402 75
    0x8e201d281c24011040c00305c0d0345a000740340c1012441c18080c21a078019a411511070140300c4081c0000e00200350ad2003010001080440001d40c0645111481d11041c94500b154503000b62031400c105102c140031a02a45001c5940030408640c082803007441c07400c00c4001803010294003010708444124001181405030070460040070250354241d180f01030000c070303202d0390042659200c056420030000b0501d268807600699812411041c3d15055403d110000705110000344660382d2100d03040c4202d1a02441428400c07141d02210965505240200c140e8070902004141020203883c042014081010f50241c1685074140d000007070310400000d06e030204094080c210407074581c4000340403811044001e5109582c2041290f450b642070810f00c4844039015140c0c01002003124040e4403a0b8251a009603039107010b52018001d007041c1b010420300f000c1c24031340014074024800c8042c00c1d00030030005000800400c1103c0c11a0b50b000b00301418203c03988401c278007402d03003003102940c00350011650300c0c5d0035542c02604210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 606474820 1106 606473714 606473717
    0xe0c1e130f060c06110c0307080f091507020f040b060f0d200712050304030e060307020102090a09270b011208130602060f0105030a020d03030b0607080d0b01 69
    0x668224590220000032144001001407043e41c0c0301d40c204178078052040030701c0c0c0a042c0e08178a507a84146140100301560015100c0030300070b550825100714000c000e00503440d4260410403181550003044080c0d1003800341c10700c4800903160a00c20301c4644440502441d044c44c0f0340d190301781c029070426260030190035260401c5130803800d5015035045554051100d915140c600a04084402007200584030381031007005c00034080803940010307103c0f00504049238940d940755a42c5a049019028a461450b04030350841070200303119860f40c0100c555485801085100000309440780c010396020395401800c110b035120300600520750703444840c8101c107000354082d62822504950f4020845c00642c00600140c20031003e2045d0510721101b02c50040004a0007400cbe05550303600060703002c02c51241c008080c0350740c0d806411704546840007030391025500400c9041d00c0b107056070319a60140c42250309450 = true := by decide +kernel

theorem cover : BRFrame.Cov 606294964 606474820 := by
  have h0 := BRFrame.cov_init 606294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 606294964 ≤ n) (h2 : n < 606474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
