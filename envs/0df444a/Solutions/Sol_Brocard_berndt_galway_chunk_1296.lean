-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:14:02.922996+00:00
-- url     : https://prove2.me/submissions/44573423-c6b5-4f95-8d71-a07b3e664b0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232913669 ≤ n < 233093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232914919 1250 232913669 232913701
    0xc040b0304020409031b050f07332304051203030709031e0b04080306030c06070506060f040207060e1e07030b0f0705041502031e0901120e0f070305011e05 68
    0x183c0a03d40714613000081602c201c580f01c040ca084000c408480041e545001741c0c0794036082508103410701c5600000b003050f410650b4540790300d030710015100303040d4840b10754198004680812010700b0301a8080c65a51140c601d464488038050302250003e5541d03003800200403081100003064a900e510510821104a0300280c90300190394000a09101544203103c0c81f00040d0034941c40180fa0f12a002c050004100340c00300a5402000e040b001e440c8155412418088507008000001d4003d43c0000089001401c01d01100000c2981c054030152500c2c2068a800c4250381050071032144c1a440b2030800000c2251200b007001a150f280800f40069524645030643c200e070000d00001d540f6941040440c060a01400c100e07001842c0c0740c007029042c603961520294407034110b0424505541c1d01442c4030360300c0390b00b05012103404141c140c588166010443c11800300411291302601c1e590f00c1380718050000c5100420a440c020751050002007801d401d005d84900c03050451040c0141d10f41d003404103110005843c0c220708 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232916169 1250 232914919 232914923
    0x1060b07030806040e100e3003280207031106010603020301051e3007090504150b12120414060304030c0215090d0309030b0f0106140703050c03030a0b090c040b0304 72
    0xb04103a61715400e0141011089000301240c1031400a032121b4803800800c0f02051014a1558048030841c946a00e50071070800564070001e0a404000203010300c4c103481c1e0007120311144100103956645c1122214412603220301010340c003103492410a05e20030541040201d003d481a0701e010f5013154901f501007100d0700a20401d410010301c04010f124416121400f2101c01c0792040910104030340303400d100301d0001c0c4207081810003490203108000b1501c04c1c9180205070259500c90f0a0743c106c64491003012008010200d8110340c86000201041e503520820061000b03030000988446684a10b02582102e41f280561821801144244104004642c22070040440f851f016900400c107034201d1701c2d200801d4420b00781150351026546410764241903011181c1010b80384610317000001038460030291207828101b4825400011050020031102040300c4e400b420a1604c04c0c104603080c02940d007006401c40d001241d04801044c0c1d100f0414840385040c02c03c96810048070184a880c0505005440d440c0788402000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232917419 1250 232916169 232916171
    0x4060302270a0911091306063b0f0306010603150609030803060405060a0b0c0a02040b0103200d0905010e1b010903050c011b0b040b06090a0e0c040f021201150201060b0703080604 78
    0x1d001314804c01c9000302d6210400060440140000800d810802072003240070f8500003400c5204500c045e20282ca0b06c18400740c1040c031030018514060888956088401c4c4041d68001c441a02c92004a840400c2110b01801450b01e02040b070503c0d40c40c8080c001a503d510440401109440c10004500700d501203a80024003960040f4141d65118013080030092990b100d120402c2c000188030111031404551900e425200301c80504c1500c441500450580d400100c41c0c01c44180c8019081320b491103680020300034402c1004c0302241c140c04a4452034211400700c04252070941182e01510f00310504880804031b5000f0034281011600c1c29521f0f11079a0b0214400c80e0360521200c0c020b00c0c0c007900103821629100a81c002c52941c0d0300e180a140100c2c030000b05891650040310000040748130172501340103141d10032002d0030040c096a4080c01c01c02c00030301220700400c44c400c0c0c0d00300425103030b00c2e0b4a1407005001c2d0054206c00d5040300d034400802800c40c5c40960264018190500c80040080d60102d1515000391040702c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232918669 1250 232917419 232917431
    0x424050102060903270616060203190209130504051006030c0302190b0301090506061603020102180a0b12060607020a0308120c090d14100c0c05060f0403200a0804060302270a09 77
    0x810903e00c10117030400380d201f00720b059103810081d0325001544640c450312110a6448000c842201c01e81c041e201c001a440803000c28000c1c581c041b03a51100d503001d03000702c0c1202d800e0151403640a040f12404d40003902e43c1c580c01c0381c081c020b508001484001d04560a10302c20170300307441d01440c11720030b010600440b81c80036124404141c45a40360020303650083d41102855100c9401440c0183c000e510007015203445e21031200d48000c01d4a45040380c80c0172500120b04071450800e4500540c41030100050485603c02000d020b0354015332543c4c2e40c41030282d0301c5240f86a81e5000503694803020310303c0c000d0201030056400c2054281c035032280b04090a400d031b0300545021201280c10300890170081c0d01080501c8041c9002000c06c0d581d513012148401c0e10b4003c2c0255144c82d203a0002c506940d06080302d014011480100d81c503440341542003100e1039900c030f0360400d0b6070400300c3c1c40e42d8558195000b0b60200c00043e0f004500c003030103140c044242149200c980305100545110482c0850252000c51085103500b550b00c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232919919 1250 232918669 232918747
    0xb01110d021e150c120a09020a1202060d0e0f1603050a0206030a0e0d020304140a0e0f04080708031504050901140a0c02210a020c0d1707020424050102060903 69
    0x1165a020340d843c0808000c2c24078255485000580080c108440c6401d5001c000c60700103a168820312402c2600900301098090070040c49007048205020201c0c0c11000c20090340d14412503911031035100b03500c0040036111020003589401c2c6002c18400480c1c0c0c44418840040000581c00540414890340c103131202a2a5070700c2c010054000c000c000165681b5000c0c2001802100b580071000780259101710910f100c6802280081c0708841c24180142c015074501500403540040b104242e0a620500c00d0044034079180055a54800702c0d08180d4581d01010b0f800350012881d490a4001c20341d114080e140204141d082854014460184c06810304402654505440300b03024030901802403a0700c0c24841c00112146c3e440d00e8400300d40d01507081400180a00402c01c081d9181007109c0700c082c80d802c0180c4a030244841e0030840c01c1a84018000c986c8039a890001c200d1541d60000081c40345005000154401d624200c00a81085002459060960810403401404948001002a03401514019080508a01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232921169 1250 232919919 232919923
    0x3050402010c021c0506130b15041107110a12030507030c26030613060609091503060903030504021002061b071b08061509070e01120603150b01110d021e 67
    0x4080040d4002001003500e1030505013009070441c056100d00c08803260b43d9a8400c0c0c01c00480b4448400500411020340450400340040a100d600e00c040104000b0344107c80d80d4942c01a68002030048800001d80500300640345880e1801c8002840c59440c4154400c800f0350b00240a442040c000400713000412550b0002e0021850320b1060034602c10b06188000070042d07a2407038043e0800c94606214000070f0400710718898050040e8002c40740a81c8a002e005410009000060310746d801009051a13021840000491000e008218070107020b6100010705040034018084e40c4100303101d441d819035202c8000e020036400c403076588bc000c0803aa03018180d19000c1c1d0f441d01c404840c0003800c4440c048484101c001c220020042201360140c40c212400c03400a131010002e00030030035022a0080082102403c0c003880950107603201c9072101d00e4226000502d04d880e942c5a040e08070050703a0046d880b99444810106d80d50f005000036900c0030b00140245911005a10700035a5410101210220308240b505609403034102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232922419 1250 232921169 232921187
    0x106021b040213051302041e03030207170109200f040b06030c070c050a06081906060507021e0a080d1202040308090f030312090a0303050106050a120c0c08071a0f160305040201 77
    0x4c0140340040517110000010301a41190103100c8004c00300101006c01d01d800c0d140400c044a525401901c1903c2c502040c16030f00c41400030410840b07540715001580002c83ea8130ae800e40d60a24403050303442c1004508280950888820074080c000c505d82080d007001039403240180d96010864503095903031040c1d01e1a020032031440c5079100b641c01c14640480030030030980061690307110b040d0300745000031003040c06007a04c07080e13031201d101d00e20208108204560260900c00d1800c18580c0c4103500411442042c0300c0415556242c40c0d00c100d010741c1201d0f0601d0000c0358002c030715200c04642d110082d400c06013143c032a030149100302c12020744103c0d03d901104600d0f46044c029940c0400401c402d001035407400b07100c4a500c0312000c1c503080380001d00d408008038019009605403102040107665840e842c41e001c100c818018030751181018144200d825403c070004000c040100803141c800c481d64442c194042c1240c00340c2500c080c021406a50314030080010f0b5040c441d2803450b550301c2030320300490b654940b03000694440d06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232923669 1250 232922419 232922429
    0x9030312010305030406034a150708070906090504150302030604030c11042a02070b0a05220b0a1404050a090c020708120a0c17041502060106021b040213 67
    0x2403108000018044003002601c21100662428001842c2d10031414884040c0c012400141d00485d00c682a495031602c0c060300c0e620340d00d0200b94042006000420382c0b801c1c06401c0c0b0420504448400c002401d60b200400d135070005254200004c0250800364090001d44243c00f4a901545c0d1390000e00e071100507001070007c000c0d9009016a689400d0034280209110105070303080d40c1043d41c080e0f01d850b00f8207140c400c2407140603007004900400c11228510f11034200300d8001203001c51051210115885134050000c140320307030311074880580e070b15090580308a01600703071118106030000015007004454002402c42c1c07115801440e1040e075603035454041c0e4449004a811103a007000800101241e4401c00d80d0011008400e103400f100c0c0c5d0307280c0d81c041482e0303146001000f00714800713030510590070341c1070248006040e6148190003018400c986480c1e01080d50300319038002407644d80320590030038050303805010150240495201800c0324008228002c0d11100c0c0032070001e80580d0780090340c1d0b4408100d2134280000f82c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232924919 1250 232923669 232923697
    0x150c0102040f12050d090b0a0509040603060501180f0603020315070210050103030f08101a0c07030f0b0f0c0a02031c0207020d03030f0b0103020c10181b03151e02090303 74
    0x10f44444088200c903c0d665000c0700d80d03200d0300248104180c01a1a468110340c413030780703a02d07103407a5009a040b112600518000d503040b540360300c0e0100020700940145d034080c040a00038036104c02c41c000002c00070b441c03a19469000c1c4030310344941440541c0340824074540c1c411b140d05d04011343c0d0700c40c0c0b40200c1c9050f84210301d450890f49010000300415070701461240f08070003070f540c07100d10a03105d00d03801d1a002c8449210f1358080090600b80818442c4804016042c07120b1104c0641d01140c3e40da031150350744c0c20b40b010802c8680c664090700b0001e20b5100110303e1600043c0c2e40520a085c40c4030340f88013940c0ca00c40e807007800898200c440810301000c02c0750703011101d120b03901400d010148951860090f010b441c001040301f203a20306180f20000309501c170f4401e50b116602c5010083c4540e256003500c100050042000b0084a01040010710b004141035010508025821020102d042441e5050650364544486402e084031404c0c50443e01a0307000582c201252029282c0d001a610980100064690302c121100019a4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232926169 1250 232924919 232924949
    0x1201090203060a081f0f051017030c120702090c0307080f0a0902121b03010b18070507081804061a070b15030d080114030a0f0b06040603080f07060c030605150c010204 73
    0x6100d0a140382c0c4141710020b006120306071140d00f80d03405490040f21003411703103004a50100a4541c815080d02040b80c400300a0f2443c050402040d142802c0c960414142018000030b5068210704060f070100354030800c104026421800c201c18018100c46018218040c071041c400042031154180d035001c6488194020100c0c0d00c5940d080c06881d4441348000c650a9501c607080307034448140d04040c022008602c0004180807a0b00d81d00201141e0703d0703440980200d0070010188141c200040c2501c0060512803602410380c55103a1124003000b00380d030081e4119511600c0d07001c00740180d500081c0241c4088e2540409070068564a0b003156031070030741c6040142c582c0351086002d000c0300035810041c12410313a07014032103c1e91406400c0b024544e82d003030342e04401031041d8100d401c0350000c115040c00c0c00d5000712004002150150b966110300459400113510380e46a003000143d480100195442120300488150505225461404000030020107c0b0b1098024240f0001048020110b0a50440d40642541d0b2042210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232927419 1250 232926169 232926193
    0xf0109050c0f120f10150507080c070b040906080309091518070f0e0307060915030219030c03051e0c25050a1211070b070303090c0810060b1201090203060a08 69
    0x34400c4d07030700711020032404010440502d896a0404142c41c560882c1e2038035504240000c88041c0e1040c401a103482e6014821503604000c10701c0014014140d410300030351510f0400b682e000071105680d1100c1042d5204010020003a21554840c581c0109001e501701b00d5a6a200040b0b1214009150352035842101030042082d0950840c2003141c1083d080e40d500e407103510403d028590b40c2e4103140151804500034840400942c1100110403089582c14074016041c194003401540c08080c00d40c81103404640c071201c900c80b40541c140728841d071100d0141c0040d4131980c02000700f04c0a10f50003030310a60458900007030019980b44900010211f6401200b400e40c40951541007050b168a42c0c2d100440c0c1d5030105c07200364016288a220010045001e840241c4042d0345883c01d114402d0b4401c1030f04405140d10750030f000d00850021006e0000901d0381c4005405a1030a001025044411036000320f84428421700a40c1d01c40ba00c08900c19040d10030992006a0b25200c400005d05902c001d075001004d2441a1001950 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232928669 1250 232927419 232927447
    0x906050a0213080a051222060915020a031d030a020a0f0812030702030306010c031209060609060801111804090f06020903060604090308060d0201050d0212010f0e0f0109050c0f 77
    0x31a079041e20312030b003025903290259103858038803480c0050000d0340904440c2d05548500d00040c141c4810502d40d131000c00c403d01094460510707150317000a020036a0300c1e4040049a00403408540d00d10744a102404c8442070643e00076110b403180240c1070a282c2302480360030446860811541c0901d80d002450b02000c04da48884448640340507000c0c101460040c01c00d8050b000c4041000e036070007141640c0103142503540300d01c01100c0045450100740c0030403046004070f1401115900c50001c40c1800380c6404035105041130003c0b801d60700a548040c2c8168900b10b8040c00c0700c0924016504800809074400b2050285c41780010060088024080c0c00d80c0b111001c40010094550700505000400f80c3c00d407601da40d81e600c1040100c1e150100c01030082510030001070b60516113807030409805403050401900740306102c226181242c110f22213000405501c1c0005000550014a000b8000c10040f2001602c0780b6001505400760721044c840c0d403040075243e10201c2c011400300f1040e0750769481d2043c551034880c2c0f3b89000a803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232929919 1250 232928669 232928677
    0x7050c070306091a0c220306050c07050c03061e090c03070b03040339050a12020c0a0801110901051305130b190b160c030210050301060f0908060612010906050a02 71
    0x80d12901c1d0304074182404c06207003060b40c0c80b481d0b40082c06828034a0340700a240040c0c44c0080f04002c1d08483d54400300000d400c030700c40c040c000c40350201000e40710209803500c940780000c0902030604c079a104a04000c203003c59640c52000041c000311000b0701c15110411160701c1c0c900724045560341401020301c085220464a406144500d00a03a2604041c08464816070303c0500e4070800d501c14a069000c054050540c0c01601d0081d9074815001c0f680142c6603622982c84010380760f600140180c1000304480258508016201d010300390690017001401c110007a103000301d21484003002d0502c200400d80440c1072205000a20040102800392404a440d00511000402c2e002c070040c0c0c0f08690003100707200032005682002d0203030b401c0200e4103440c00c20740040b403a06a007020b620172200100c0d00c0d14040011313200d80721405071450145d192151654145000584101c5214100d0401c201184404200d906000500386030080415030320404010b818490321800342c040684068049030506040c0012404154014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232931169 1250 232929919 232929923
    0x13061203050c1b030d050304050c09100f0e06030a12021e03040509090a0b0103062409052e030f140f061801020f0d0203060d0f12080109050f0403030507050c07030609 73
    0x240b00f4107980311000b40c03084510515040c2e05a440f9488006050303020308000c64001707000300f0840e4040040b140000705103540465090044840d03404040000c12101c1032000c018108003401104145040004681c0d1000d031200b01603c1282031455030208a4024848500301a01c1a00742180000030184595a298414450a0300400c494800640780300800b04440a1740347e44811082e210f40d20750380703880d4081c04086a90440803022040c907d03098522406180000345290390000c14641f4204c1105403041910b40703001c841c03013506038412402c44803d4601007425254000741c03038103180d42603007040c500004008284c0d40c4288180c210f0030240510009206100c5c0c814214440210080700c52254281c0c001c1041d424a0100c040c86010000710140d0040c40e44141d020301031242c5030b10952550448008030315810b07152030341c200105410345540070b6002c9024040d036030340610160410f046500310301c440040c0050b08055849001ca0b550512a0040b01c010240c004111200d10b6200c1c1440d40040003001c0c3e007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232932419 1250 232931169 232931173
    0xd1401050915090318040209060c0105151f0f12021b0d090f0e150306070513120c0306021303120905030609070f0b0d0906020406050c0105060306010e0613061203050c 73
    0x1002c02040300c485140c502c140341c0b1401441c1021100101da808414200d008190b20079000e01800d0501d4035100d001d003864010311320004c280e07030401481e84451011f04622041c00303044150381c03201440c81081c0c0282c40f00e4282d841c04a9003d5000d8208031510541c0400d4584828000281489004251080003640c010800141d503002d034030000d03080c2da040005120340c1000c405030345402c100351014031000e951301c143c07130315844c20400100c0300000c0e007803000c1151100041103000c52001485121084800080c01c110155881c3c105040e4940703441c01c0106210060032181c000482c0300ca00c0c017140f41075800450740000c4080c030507070703000001030090311031801031900a1003036000146580400141c2e04048443c1811030150755404d108010364554060303018032203001e4642c0d41c8000000c40307030300c010310040611782e0342c10b92101c4001070024290740c07016100a21a600000060010003103400d40039420030030844081140c0a208a9103202070080e40c0d00281801492603588024160030400411900d007404e02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232933669 1250 232932419 232932433
    0x7020325120f030305072c180403031508030708090d060e0a06020406020d020601030c05090702030f0a0903020406080c0f0418060204090207060b15030103080a03061e03060e0307080906090d14010509 87
    0x80215a090b801c42d40c0020350501f100c4260b00c0c00f92084c0e090950f088009040c01545401fa0044039088080650301280020340e50b803e04e200300003d8002c1d0001800d025406146071401a4407204140c3c080ca04011303100d1a0b44036414010414541e008480100a0308180c0d4840da02608000000790011700c14500513004a80d445a4020310100340607041e02d070b0284070005c1d03a41c02d00c0d0a00030119401802c503c20b611081103025181c1d000080070700984403680d900c100403e811441408161034041c0d012a00603440a500050665100d980d445203010055a0000e85818101c12115102a0014001d03102c588000740120b002140c0b50020000c00c1c1c00380b00c0501a0009500a0261203455100c0c00252800248014000281c515000701841200d40c0b8000c50403940b5406592094101088110710780403200b44204208011801074113090f4040700d01a50903d5119200c04c44107105e00d004032031148000241004460366400b41030190581c0105008003201040c42d10103008040c25a2042c5c15441225 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232934919 1250 232933669 232933681
    0x140402040b0a030512070212030d06050f0405070219060f060609030b0108030a020d031a090112120311090d060615050d1406060919080613110607020325120f030305 72
    0x100306000f101c0d44407005001990890640b04004d0b008028203e80c84010b544207005400d8081000c9c1003003d481034000038000b80741c50700300403044280d80300380303070080341040304000a0030380200d040440ca070b200c0e000d03100340102c3d10714010300140034001c20544040c0c0f41c40c4002c00c3c6654441c032180d050324440c0a695449980380d1803a079030349010340030281c001030784050381102c0314178401d802080d541030040070306541d05080b4000150040100341c001e440504010042d02003800529441d0074803581d00350400f000082411406410030780b080c0180b0701d020301903600e12442040b0182e4825001000c50141400340c0b408840c00040181c0d00c440841020f0724102107205a03d425051801e600070700c0000c01d010710381412942401070001c0007101404004c0d860a00010710408144101072060340c00c41d071002c0074660145400b041c880150b080160080c04244400c60045e1000201009080348010a40101c44a030070000c60f40701100b500f180300350450313025240c3c04200210300c806101e03506c01e4a007482190303188 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232936169 1250 232934919 232934929
    0xc0212010e010c02193903030c200a1e03060f020301030201120608031206030312090c100201090f020402130f030501150603090c0b090f06030408030126030a08060f0301140402040b 79
    0x508400352120817601c1c0384c0c004006d240c00d001001d171079040981c00c040f000d00010855640c0700301e910941c04100380c3c1006504000d600081c0811240000301d00080c24901c680101c0e001940c58041c0080c07401d401700700c070740105903542480c02c001d61f4024002e00140e441d698485001e900207100807404180410310b1801084e841d401031000f50748d00f8070019030038030701080101c021006c0080d00c416098041044030000b07a0598000ca90b01c14070310700004090440c00c840034084410701e8503100c40c046925181410000070186100d090119030101c03009030300d410341444030424880c89070b4480041262001800000c11030190840000b40031007040d44418107070303282380c243c0a80d8002c0781e0003400d40c41601c0040c0031b81c03003d80b0f000c2c02c02690060b01a900714040100490103d51040d1030a80c3c081101000400560450384074100d40540c0d60601c1c80e12040034078500341d81c2e038040c0c40c45010501c400c481c0081c8098407441c42d0065034007801402401014804d514000800c80e041c2c134140d000318200700c6100c04a09007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232937419 1250 232936169 232936213
    0x60203101a071208071b051609060806010b03070302040f1409011401020604300801051203190f030b06031f051e0f060706090b070806030a120c0212010e010c02 70
    0x8043d00c201d003240e00c030a04a81c5082c000b0040414404002c5481e886184038200b44010039204000600551001c51220498171314554401c0030b800382401d80c2031000d1400030503030a0440f1001046103403070707407202502640603015680040ca02c241000700d00017201e0700310100c0c000e09a10280c03a080301603622106510080510040c9503030142e801940428000f4091108040e10801d03101d00c100844034044400c4e10342d0b0001c1112703001c0021110310041c8401d240070003014280c1780006c401140340000050101c59100c05a544000c1440342c0d1201c07448003a4003a8005241941004040c07590381d10301030800c0d0f01001208042c0c8011300310360081c017046a08045440c412a00407000403034004da07004400704890701d84d010034607940243d000c3c001200020107502401c525140f06440e12809460702e51402080791300010510346c82540440703500400b01c0c18565052045403203625111480301c0b40703030002c0740c03080050709848001c5610f04494100c03100c0c03044d071180c3c2206805030b00340c2c2c50301c0b81d0307840d020415055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232938669 1250 232937419 232937423
    0x70318030c020918010e0c03070902030403021207080f03010e04030f0908060109020a031407020f1603030e12010e060f0114010207030210031d0d020313090203040b1b07060203101a07 80
    0x100c1c40200402601d42500c66691202503807a1003403200c20300201413802c1d03d80102611946510502c01c2c4001c45c40d0510914001d400d000a0444c21480c094400941e2403616040c440345551000038000b061040b090200c800c101c4540f0031007035407540c2d10091071000d681d04650950001c0d003950030240300707288211110000c0b03481d07080003415980d0030604210020760082e24906c06140e40c84107a90f10442007480b9080c4290752035009002c000e840040310310306000075001c034407c01540000c0244002038004540004141042d9448103171076052a00c2e040c010303c11440303c0c40c0180304d00410005510f0190000c20305850803003070203a0110000d45e005a035209a070303000c000d600c00711528090030030a11070343c0803403140107a003021700b08a1000e00301d040c0d0601030707600324400050b04006044004500d41d019280000e11128100710728500e0a43ca45c2000d5410107016545002d80090451959500380c50550b49002c1c6c020344215032f00c2c10030001010791081948504001c03440440c000007811008081580d00c030503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232939919 1250 232938669 232938677
    0x5010c0206011404020a141c180c0b0309070312050d141b12060402090a0512060f16021b0301020d0f0e06090604020d0b07090f0305010506041d0d120b061207031803 72
    0x201f020b001d006d0250025008050100b0051055502c90b61030b07401b809085609400081c455680c0304d042c10200c0421940103012400803c005000c034051001030780e00222034221440400310031701020700321103612402021101d000d007000307002c440c18031003504003c0c000d0030f648100c000c110307034800f00d91030440c0200380c68410031801243c0014103e00f400d8004000200e401070511101903150000940c000c00f09440c0c002850348440108042410042d000982110309880c890081c03001c80403009546004401c802044000041c4088100340c80940540d81001c0c841c0c50b003440701e0b40c3e4a5003044010b08964a02c280c00d407181c40d0100d081200080f07081401247c000c3e03c201d0380c410700c90701d41415145000d440e050030088a5280007549a1031015410007551007040081002d007864070030082611503000c044088841110842c04401ca000103000c05a583c850804840004112144100400d00c0f03e5040fa00b041000500300c0b07804248099582c07041c00c80c1c3c0c604211400d082d00c0045da0307015410710010041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232941169 1250 232939919 232939937
    0x6050a05010804050c0909060a0e07031104020a02010f0204292a0703080d0e0d0e0a062001090f17040f03080d150e1506280c05010c0206011404020a 65
    0x1e51003000d805a000340540121102c24107941c0100d44480001c9403401038981009040c4421541c3c1409600410182d40008200003411905d070b0002d40542182200e00c10b0340d000507881c110354000c1d041150716041004013103403102e5490994a111024041300c031031111204001103038000032030300b0a90ba0710803104590094485002d00180ca612403045488801501c2140800000075919800a116280c0000c0d00803401240d400c0206140c80d070140d410b44107014100740a000c56840b29100070741103815034a44038441d901c00903a2225119510f848101d01c6508084110b03061041314a0303400d00244c03180701c2d81005500c1d400070f400071034012805540c1072090149000c2020036038050280290011280380051070340d00d00d90440306144000d6003e880d621030b603070303007040200c425100a41b06002000d035142490005154484404546600700f60b0740c1d11003180c10300703800c0940310703505201a442d813150007008500246a00a560740009124a0089460710008455030b41403500a55050b007400b0349600b030300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232942419 1250 232941169 232941179
    0x161a0301050d0201020703151401080109020f0118030f140705030a1502030601090902070506040302101517030c060c0408010f060510080a020d090605010314060106020a080d02190315050406050a 85
    0x450b480205a04500c00c11401001203072068441045a03040c4410000d000c440109010780701e60016802000035914200101000d40c4031200746100700c000901c1e03c698001c20a558900d000c82030f40d04060305070003000c245a82048002250030381c044000000712299503680d00d0070150385e00050903008201c0009902c405216448a0300a15041201410b0106480e5101c5a0702001c03a004454183c1300382e4003003002c0c8402d054043c030000801d03000b03141c03062001c6001c003c504907143d001481395400006140070b0141244c0018020b40b01452490002d45102e8108100490340b55041401685425403070709121100d54070f414460341003154405410440c01801ca61002ea618240043c0703001c0c0307040d400304201d520060061181030402807042c803000407a03504505105035111005203d070140c5d58030100060000c980c000070449408c075407141c00c256441030040407541c041d0265844d004100c0d45514590040b041d019008925100007034051b006003140d0f26802c01082d507202d84112a001900382d0400e200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232943669 1250 232942419 232942429
    0xc0f05030703060e010f09030215100f0b09030102070203030c030a0201180c0b03070c050d0c051002070807082101030303061e03080405040c020304080d0305060a090903170402190305161a030105 85
    0x15113500391400000d417840c0054030000c25152940d07012001a0050000010000320315881560401c2460038115070040c20140110380e42c030754500421051071783c00308480200c1e65094044900141e8090242ea8480c1400600b0039940e421003003802c409942040c1e40e040701c049501000300441c681120044c02100e20303003898001e15510141c80c9808220303c02c2e1130b400c0416000c20160b112541980d940200491030b9050040c101f4620600903900380d8010400d00e0702041000c016a840c0380d41100010340e43d104812103000450302004400a8501c10b180000014180c05521140032072741e10700f0005084064051340cd003c841510b00004050701424001400903040aa010483c1c00985004a0f0b19180d141c02c040c508d40a40c940e440800243c450080211030305100c042d240003030102c1302d0b00b0300c07451101d9600a00700382c2d01d04c150a02c0348891040000c06542c0ea4180d51a5000c2840050000141c1c07a41042502c451183d0b5004501c4030400d00c00003511000303851a07091880c8001a011b080d40d007000100b003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232944919 1250 232943669 232943681
    0x20307030e0d0c06022413120225051203190e010e030615010e060f0d0f02090d0f1403090906120a12030b0a0506090618130f090c0f0503070306 63
    0x1c0c1d08444441e0701100000c90305a8040050b141940040c429105845201d81540c25000b00c89280381c3c00c0401800000f5084c01094000d072a030040e100440540d101034120b1030054090640b17002c2030036002c0381c5410201125509010341340e09aa0b00d03112000d4a824517035503441024032800105883e001402200d912420310042070140514100c0910b00039040000e141c40011b5560400002040d0601601c43d80c02c0400202682c109903070240c146142c001c1c280c1042e008202c05007020b95140c1104200b40e1803551704490310440d000b08042c040c180c2758140320f4030000402a040b100c207400500f02180c196800015911000300041115030560344000910004401c1082c4c1007102d8400d5103602d40c0080c8443c1e0b1107603409481d0b0746d00016015807120400000c9062540300c4c600841d420011451161184800c07201d0091150000d1004d5020200204110301d4544110010f22860160440303041081c42e0030118025001e02507005460391a0103500078003005d00c1c030034207515601c0301d0420400654660002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232946169 1250 232944919 232944947
    0xb060306130605033307080a02030a090206041d0c030105060a120f0c1806050703092d1401110102181302090904030807020d02070b1c150f030b09010b0102030703 71
    0x89525540c540109103451400c010004d17218100c01030895121340203030000802641c4155540115003400e43c00580304c801e000d4800d9082c80d8000000602c110b81d160030050300280d000d005542d0701c569403519003c08200d040c0000c1098502d080200e418010b00c40e09882c180c60008101a1500d0003001d4203444a000c07ca00c01c0042075141c41e240d09418001c0c2c46400701c3d107101798840101c91030000004450906144c0c200780240101440b480f00442e52190625056540030b459440c203241410103500c5200205100900550100078000315142c4900d06035450038000c04e0301c9011040c20b90b202102d0a038082d40c003010848194000e101d6030700d841c1000c0c4001d8400d0b10b162005180c22980300104001250803036003900400d007100c1c02c0c080c0306039041190501201d402c0c405070034030b181800c102080034400c1c8000f00d41d060510b4104210103a50591003500818010310703010407016519100e0003459480c40c8010354085200d10009080320006006041000c041680654a00070b05a0303000c0e40c0f501410024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232947419 1250 232946169 232946171
    0x2061804150f060807020d02070303080c0706060b0912031c1e020a090302180f0601051b0115150804110103050a020f0a021c0903030e090c0c1905070501030b06030613 73
    0xd1000802070000c842800303048190740a410840c03d041010b00841e201400020855101c44130f070400d400c1c0e022410005407503152402006d1030f00d811040c80224050030401409076464084001500021603004040740101618443d00724001e048400d1b4503401503026410801c42072001203286c200c2c06074003155204082550700700b090101c49103510126009500e811011640d03020080c401d5141481007055a005410340002ca5803400c0144030600010148c40181440300100e118014260600302e83d500c444803078030003004800701c54407040200000501c1111009980210140320103407090f13101c40e00c1503410034151801220018011001014001d140c450807650910090048061a500601c03040301030b41d00500d40d41404039595400f02c0c03078503000b10081c00b003041c00400020340c0040070039617540c400302d94040d850380d12030030281010300c1800000800e90180c2a00c1d82d407107001210460104900031811071340c407291514015400c80b2901182d1660215003440000d01524010000140030000d810b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232948669 1250 232947419 232947431
    0x8030f09031e070c1202030d0e0f03010c021c05040e070f0e04020d09031413031401020c0a05030c0f070e2205030d1a09060105070b0403090305060c0301140d02061804 73
    0x2c801c41d05007800003240800600d00080031800d000800708501d016000034001412140c480303a00003a541d2070103003c04000e2040d2907803040203d0381c0300940e00d282110f01a009000d485083c1380c0003902c0d00b81046440b401c0302e6071501101d103828400d00aa805469000035520456114034405541c9a103010400f40d0030000440010592600c0303c1c000703407464106070107020a61003820700e030182c50396102039280a08500c1c140b003e000145443ca01c0d907000c03070790410052241c421b09010303c1806482010341141c2e061281241c40c0d001c1010010080100900701c00c1966800080b123816140c03100d41c0c034420f40e61840d8525001c80c0301c020301494180030200d9000c2407554542034a60301c0034295045a48d02c0384081340d81d0702e4050361040c0c2d142d0600201020840b114451440c111001820900410602902c17400c02c4500140806004015880240d42c01038122501031030028070f0000250320074001e51081c84210007081c1828201952098145640240000c0c2005031403150705491020801400b91301ca601c503d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232949919 1250 232948669 232948687
    0x9130501020f030106080a2007140102030124080106080403300f0c09030203060f09280c05030f0a080d02040e01080c01032f0d1b02070302040b0a0308030f0903 70
    0x110050003480380d036284183e100c0d85040f001a0045200600c69030f40b803800c0002110840099a1100700b003940b80030002901c4000504050300c10009405500405620000012a5540e0810021006000d80c0c040300c0340201028901141c80038020302c90000490020300c00301e800039005a12441007510417100c1140c2d688244040b040110340111204000d50f6550081d44081150a020302c0b51642030340e00340040028036642c00b09654a8004085014030510440854803544050007001c00d0315524140c2ca592a42c1117040360038500000040803960b640c800b000010700d42c100414201c040c2c0384130134003402e0038100a4480f1034041e440310418490259007000042180300038030400034040e09200000304031041c40342c4005030403a402001c8040742424405444858480d00c43c08050000c465030041c2919159140207110103458080c0200c0610068086031010903940010b0ba40101c9008031000d0101d030700c5035400d00003042160b000c0640a5a070800001e5008031b030900207141c00070550011649400400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232951169 1250 232949919 232949921
    0xc030a020f0a0c0309050105040602150709050a06020c3a020f041401030b010806160c0303020904020a0806180c07060504021903050a03080703020906120a0b130b03010e0a020105070209130501 84
    0x504a01c01c04a101600c3c400c0a05070300c03c100702c01828003800c02c0c919142c20210083e6940b10303000b00418110030036900156900b446880d07a600100350181500c60034503280c400194031402d103c002140642000e0988411242080c918000710882c94601c04002c101540d40d40c0b010804140d001345e811600c0f1180c1f400c91900c0d10301c1200039064008156001d03039415860440050001a44060416884401885a00d40468960a0f884680c03801d011516001c146816400380c00381d59007440c0d004d803003c20854186a040b00d05280304210890360303040c040f511441902103a400c1620071150404060104074006809070f800590400d00040c400841150411814102c20f81940c10072511600490460420140c00c00748180d00301e80b1a0406500301030700540440c03e03a002d852406d940110752240441c502c00b40c1136002455007600500b248841d5003003045107101801190300070902035803034002c2c02c001410f00890014206a416510103140023025006c002c10400094000e02c11184185081000502d013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232952419 1250 232951169 232951177
    0x150f0e100e03070f1707051011160f090c0206010e06011206090c030c0f08090606010f200c010e06030f0105040203190e070515090a09021b030714010501050111060c030a020f 76
    0x500f06131500355030500100841044068080d00400d41c44000240960744c0e6080041e032400000b89030048840f15507a40041c41d181c0d06000c400c07280205200040b41c0210f0100c00d01c4240c80703001d50188061404104101c0e60f80c5003d01c41d00307912003030100115000d98032a410329050b000c0030340e50101e00b594540183c0340440390001d64203030200385e484078481c403182d0700701c0d05945a645981c142483c1070302d08510150b1b00c1d060001d00c868100115441c00381c80d92401681803240c0c0440548622100d03251100784a50744108030002940840c03040135000b1501d00c1c110080324820590300307003110b02c2c40c0d107428140300c080d410203441905d55061024880c580c0c2403461103104a422421740003400002d1804041c000303803d076070200d40c2410a000b0820b50480c0e868201d100d1301200c1001f000140e560b41c0c040007402000d91045012103850100186030320900003581000940155000020080780e6a85d50054a03030b242004450b40d500d41000b80080d4500b0710210286500c00d210b104054a810304400e000700d040d0b80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232953669 1250 232952419 232952429
    0x14070b0a0b0103050610020c011b05060702060f0a0c0507200603070507150209100e0103061706090d0206070c11040b120109030908010e0a1106120c04150f0e100e0307 73
    0x15481c01c011400c2e6a0501405401402c242c0e0713444600e5140c4040252110000d0000a0502030b40c01403001b110301c0380402c0340d484680c1280603502903040400000b9203030f490035621700800c0000309020658a07031607403203078518248807030302c070745103401a82e5569000d02c56039083c400280e04107041607140303940c80702c20041d4030411107513590315900c10407460304114200701080c444003900d03c184100e49158a0381c90071000751402e64108402104c0c10000100d01509144d00150f007030610b440b1140710000b1300004c801e40a0416881960542445240105d076511800c4403010005000b410004000c075854039450603441c4405070001c110404d03500085199104041c0f420341c1e150395500641e4042c0744d804541d400250101100a000009460070381d2039039411201d0003e0580c0e41004c07038608aa03510300003190300c0041148130020310b03464402411304aa8200e8820f010341002613610325540b880c4601c0720014118402e4a4050310717a98910144002406121182c00a002c6c002d03000780110b54040200308002c1c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232954919 1250 232953669 232953671
    0x30311070f0828030503010501120f0f0b0a12020a030f150c09030605090d082d04080901090b2d0d090506090709050f010504240f031101020a030f14070b0a 68
    0xf2400c00003855040b030090040b000e480c0030080d002d00002c0c2d0300904613411207000746454030742d001c040c0e0f40c650001c09407502e0008440f403410f03854294418941e0006581c226040b1a114500c035510070740524900d480160080d4401c09501c0240700107071f002c40320301c1d4131180524040440007004030360b503c003100c06200300c0302d0214041d00001c100700142030040c41d0388411040040c04040b10030200c080c10040010740741c0719840603c844614000040c80d840b403c1e2100344082609018105410b20300035a40c0807078030300b60005940c4500411035200500482e40129030440302aa0380c0480f2150445010184404000e0400010058404245024001c0101a50259000e00070b2420015003591401240340c1c4000c0c6500c1c00d140402540340b9018982c14111035003542c010444c8004002c2100100b900c080b02004405102c841c04151201060b100d8803e0340d2203030541c0c80120000304016680c405195000400013881100071088440c40740089210003010320034081d04011841da0384460042c41215110041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232956169 1250 232954919 232954933
    0x912070305130305030717090a05040c050906030f0108070f0806040f020103110c1609060602030f0c070308031003200915060c0307060506030105010b070c0e0403050f0316020606030115030311070f08 87
    0x1c4447c883c48080ca4419a01c6103501c1c0814400100340e21540a100300c40c440c89d5540c01c1802840d0044084540c2c110005100903a0b80c64020b4601110440a0003110981d03c10300c54045000c0712450050320a4407800002407806070355998895004000d1000c0c01c03810036880d07a100041d4140030a0182c10702d001c03014061301e1241d104070560400e108480c0d1201c20720505114003001055000b0003203032030355144400b03a20303603550b2400341c410301d000f0003039000170010100002040080d410215254050f01c1c4142e23840b860032407040ca4400310000510201a40c406400008545c068110000c0284c581e640503011a003482010782d4041c1c11500080341c00c0c0c480c2ca403100104056031a0a00c68140507000307403100b141c1445060745540414600300d00031500c5070612000800c0034103000310265400f4445480c0b400355607103040110b6182c050f20034900380300540f1981000c1a441e107018000e84144410001c9810141c2c0d02e0364508582c1c0ca0742900040c11a80900140441c05103c0c441506001d002c1c00c2d8004d042c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232957419 1250 232956169 232956173
    0x905100b061c050a0b011e0302030a06050a0315060801090b011403070305120421030f0f02190c05040507031a06090f040507032a0203041403100f1e020309120703051303050307 77
    0x5d035421407112071304010710801c040841d030410f9600550205424a00184c0300c0d900e1074000402082107030000359000c2030f10f0381c0000420406010650006060400602c81ca43d6110342a80c00e89119000c020300b41c3c01804018000121401204003000703600508440c0015038a40314242009281c0c10304410f03854000805020115080c850000801c100703c9104959100e5900c008298894900d984000c200400524010141c400c0052a0803070580d140c0c007040060f8640745c012032020302340c881c050040f420040041e41482c0039100c0c1c0c880c0c1d40b02150131588500c40d840b00b000780035400740042a80c81000801e0340c5030161281d1080e54811101c0e074800242858400541c51619220b6103400e171543ca5050740380030200340d408001d440032102603144100905042500003400c20500d0710bc0e02c0c50440c603003200c900300503520b07800c440e03c50201d80819600468a82680c4030691100311030281455100c12154850b038a5908010a8814041e00c0c1031820407003204d0490b40c14445551060b5a644c1c404600281 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232958669 1250 232957419 232957421
    0x106090821070602090118080109120f120e030f0d060e1b0a26090d03060b090108010302100302070203060112031701030f020108040203030d020c0319030905100b061c050a 75
    0x2a00410091007030840501c102201c240d1144007801008640c0200300c8250503402040422102000301003420415911007000b10b0080110a505035079181d02e40080c0300006010340720b0b03900710070500e580350b049100842c8038000c0540004945007113148010028000388101b110060643c03c007480c440480c5442c5041501701c070800002e85000c00c0103424002e0716000d402c0342403c40b100443c0d6070801e8440a501c1916011990a400c081c4040900c40710040021001001c10b100c0e51800d89501d00f0080780781c5821745011075000d20000355011940010040c00946031140303421007406a6883c0241c0391001aa0209061610a0344070070340d80111100200101500542e5500c1c10300c040c10b282c482d1035807440d01c0e41005100c0c0c0d00f8010381407180781400f0a041d500c09004440032148103480130355540c805610815565132150307003a810700a200303c4081490768484d0107a090800e420030000c051075001050600020305401c0710140e806201008208243c00102070714071080c24080034001071070725220002d50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232959919 1250 232958669 232958683
    0x302011a010206010617100302040203040f020a1401050d0e01060308040e161d0f0d140717031315020f0106060305041e050303240301150501111603030309021801060908 74
    0x7415900700000501c0b00d82d500080074003414841a852000584030700310b140148900d1508060b410038000800c01c401e1003510118103814620907242d8183c440e544030740c00402030080485050000d07204100342c44030030305582c00003818540803100000b01c071580c9a5841d03034141e20981c06014545c110b0401c0090702001c4072011000701415040c100c4083c00b03500d06003c07034982003107131f841c0c0b190100d0794402c2031031744a00c1441941958841200500303105101c0b06140d403a4a50321500c0d42c0980d8031203000e4903007807001c000d8840140106915035061410218407605500d061440e1a0852007441c004001c0710344240110b80c01480b4948001a09051034180420704500349003081032449112000c200006500100316680030310381d001c58581d252484408100c489840000f51075066003052448241403401801042c11150300f601c07a8203860b042d00084948851102c50b001034105400042000443d0103a00017038103a81c03001300401c034442c7c03083c2c508104610302030300203400044030004107125802c1d0811010b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232961169 1250 232959919 232959971
    0x30906080903160204020319050109021c0e0606010309150c0503070e0612070f03060801060305060915090c01081905070309060c050c0c061e0706050a15081e0f0a030201 74
    0x14524041003200301e069030501c40c0c1c0e002030242d640040001c600c4600c1030070310000c1030b03407401027804035580d01d0103c4006500300d4001100060400304a05d20f07224501d01c194100800c0038006448241e0f00c610054005092880b0b06403991b44071007249100d01c1716503100300308003880a525826100d0800801c000d00c0da54550903036a01030b0f0340c108981c0e654402c00b44500f69010300301c1c0c0341c070402760449041d04401421043c1d0211649608024005c01042008601c50744241c0c00300b01200c101101604468a807802d0940b0b04402c680c102401c105180d500c1201e2540c0d1041401854443d00084490400c0440d0811510b020000359595014420000140203d2500a43c0c82c50311605000400c1e06541d150703d9042c1216225a60010301d07003400c2c195008004d10503081c54404d00d61200118140100641030031102c036180d01d843d0420303402c000c8a102c050f03001a55070000040440460a0850088400d030449000165100d10084040020380800600c4e01c0f451096001195030302d00340c03440f40c0e8105404880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232962419 1250 232961169 232961173
    0x10e19030303150e040b100f03080d0b1f050901030902090a0b0111030a0f030504050705150307080606040605090607060f050c040f0803030609042d110f04050106050f0a02190309060809 81
    0x104106940030310100c0c035082600b14440340d07043e0310b80c0900c1c2d0049002c1f540c0b00d00d0303002110701c1000050101280240041c034130203c60900015540104011841c000e540b1504642044160071802c4980300d4406004041018140018001c0480c0c0006409510841b2091441c5841d10280403a9592056020503100003030401107003010100700c4003800e440c18141220042540d6840080c0034000c040101c01c0003040301400500043c0700d00500d100080e402140d0080200c0c01c5207010510504011044a040351915a2200d050181032410020036511002d002c0c0c5055444000045208159200d96805a44050b80340d80e40c8500e42803880c0038004c055031080809400903c10841c0c15100c01d121541e019500440701c60a9600301c544c1c2c107481110b020402c581c418040b0074050100040320601c2c0c06403913801c50304014052460410001507400902460000071b0041c06018521156000603244464042c01500c0c00c021406180350401a1040801c0d8006946032004000d455003081c403064103e40c0c2540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232963669 1250 232962419 232962461
    0x4061d030303130302100c0818030909060d030e03010e0304090b09010806011502070924120f03030209150c06040606050a030c0303051e0a030c020f0a110906010e19030303 75
    0xd80341e01004001c503101940c00c100039001c1510a20884e4452046e80e84204084072194034000c0032101c0464290a000c0407001030144000741c008145d50078442c000b81901030680c1c6030024080108440315084040c0303c7c10a0100b04141d07002e0059114070781228000355151403a0003d000d082e950b855a1043c00740814130014840752001040303103419908003a0f614460301d203c4500403487c118041d40005000d61904c840d50920003511100450300600c0c501109050307a458003c6d82d07040800c000c4004082d107804244000c0041e0081d00a000b007190002d1000d010110410b0902c000341c0c0c40390000c5076203070f0401f40400040007424411140501401d5802420303640c15661034441d08041400b02038180400403c88070209000d0b040e02c496400350307030b046403600d4008942010b07024214000c1060094095103004440740480026800e1200760084400900c4804600c1440300c240f4002d02030b00e04100a0112007021603d410a030700d5460741e501490980f03190700e1810010104c804490604940e0005a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232964919 1250 232963669 232963727
    0x40f11040b27060a050f0405070c12080106020c060a02030306090403050409090803011e030309090b0402071a071e140c0102070c06050c0d170612010b130e10060506040b0a020a02150406 81
    0x42c021b2501c40400365000110b80d190054241c0b0390320003041c801000788030192903800e0700d15030000c1990304851860b021200d9540f107010030809640903c00071500103078801d0000a0092502030f00007034100b4003904245141a466814007425191014400e8901d41c00c001300401c1814048282e100035a03409150705d00369981142d170002c01c1750080d0312035100c4580d00c032100c208260303075640e045071040c552000714003c0d082c401d0080030202c582c04951480204115501c441c3d5a0196081200c0c0100c090355074a140c180d0803000d000ca80341c0c0007083c00102175035080c0103200011359205070101c06031901e52038060b00c0703100b001c1c015850f02d10024048420003100ea200d079130b68407040318501c94000300100c600c5406602415202c134010f040030040c26600200c501544210500280d22440300c41050302c0544110000444030003081e118070380700391504100c08010030800e09400c03101a0140700c240e88182e92a0284980000701a413200e50500b64000d50700042c10049541c000f42c0d00c44c1c4c82103003406082c2175090700d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232966169 1250 232964919 232964929
    0x91a2e080c0114040504050403030c0201050601030603021c1502030a0207120e06030f13020306191a06030103060e0f06010f0501030c0c0c1a0408030c0105040201020c0306040f11040b27060a05 84
    0xa01c0c000c5050007009040c12a104000106a8000d0800503004011a1909040040c050800344614001651034240402c07555413003402000c0c140da0300584a40014510302a41c00c0a8086202082d511000744850032000d40100340002e501450074120003580b541d8044c03c1418040380003600d580d003406030b4030f07501490719190b03001175a900c503007052001c0d8816650200405d000b1480e0074802036050044004000c7c0040003c500d01c8480744020a00300b19465043d4001d81341240b414030b109510031300a100400005201c3c1e0480c0340d0003000c4100f541c24440c034a0101030700c0d1040a8000b154a03103c030950600465a142c850315050421501c4c01075001c1c0500d88600044003584e008404060f440e580d01c2010a2024000301d40042168000703c940d2546e69195040c001c1100f40c60890060051006440851a0015007503010350342021041d0500c42240c0c0ea502a5034000603460fa400075200c00d1451070503520b020344184001100e004c02002071660b41525051010001c00407882010032103005e004035120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232967419 1250 232966169 232966183
    0x4050405060f064507021b0d020409050127050712031b0b07030c030501050904110a1206091103010915020a14040803070b010603050c0f070c030605041a0a051504091a2e08 75
    0x42042c0d0000d036151a1f0089092400191006900705040010b40002c000f0154040c181c0c0c0c5100d80f0381c070a00340c0010b00c9510000d084c14a000780160b40401d80034040302d12601c0703c81000e03e1090403c012505120b8800381135a101c036210550700c1c14288403c02200d640c15014000142c962464100315560608001174100840508050160040d041310300f40305803180c0f400203014141300b4001c880d03040c01a117080b4000e41300c0d00500301d0f140710448001c4c0780c0a0905000d130714019035010211100d64010008018000d420030303403200c2d0421800300300c0e0140e0411003400800c0070740801c0c5e000e10340e1000c0e603003440c20704110181d1000c01054134003000c01c145030103c80152a001c0c408040d2095640216080c450321250954002611851902c0b040c8010001c1e03a070000a100244040d105455590720402d8404407101203078029828055580c00711aa0710f029031148060a12039201203009181302244400005000c4032404c07010444105500300c59440103c094604140411002c031a0764141102641c984207 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232968669 1250 232967419 232967443
    0x111c0509040f020c1b0a0b04030b0a0209180403200606060a05041701020a0206090a0c03060e1e010b1e10030b2206060e04050405060f06450702 63
    0x4404035030100d595803203810000403804008419915074410040c069141d0280040c101003a14109400e8030f45410515800c01c2101c0d2032054080c1094a140c45080c4011001445140941d0742004402706a0f44d43c140c42c803526002100c06900c0c0c42c07400d0320f009804403822542d51300600068464160980c0d200288080e401102611401e4070b422003201c0a1341d560181d600042c07085000c1c02d211900546055000e01007081a03582103540c2c940341c3d80c185588070760391604050040c01b420b4000340081949a000080c80c0d4080c001242c030b50358403181074070341c80790b140d0200c8001694442d02c0c0e94142d45024032031400b04001100d800e00c1b04110317080006204602e8020080c050546a07000307020301c0d40e0740580348100300141c0c0301502c90940c500d9120200818240c0506804a404902100788505261250600c2194080c5c0101010f45809081841c0e0f00401043c00354070819072501500c51412403009000f41c1b0022000441e01984243d00f20b640f0003101420940a02030708c8402c01c1045a400180001404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232969919 1250 232968669 232968677
    0x609100510020a1e0506010e0c041208040e040f0b010503070513092a1503051603090c0506070c0f140d030309020d20041b050a03052a0a111c 62
    0xa841d07050590074481201c102500c82d1501c0780e00e8058041c02c503014802164803880a0b0381880c0e03240c40c07204440381e200b030b50419501c00d01404240030310244d56021a4141b0b000d00310444c28141e03100360b000725400c1e00b190101c40042080e65114104444d8200391400b400341200909100350400c00428180e07140d4548400280b40c9950398002403098500003031031013585492050200100010304000050f88a10409503ca011011909821842841018090803420f68070b0f41d01e8141d0303400d00310040c18240c002521450300c0b003240003e00b0b036140303801003400a100d2001c40c01c0d283c0c42c250000d410001c4582c440080c0700d5400c1801050351f5074181000e038050354181000185181c01e400030400060204500800d00501c003048a10b001d50002600210f042c02210180482900c07400303281841980c0501c440f000c0b5105000300080ea9000c0c0d00902e03404a821034004600d0850754501d0103807410380000e9402c0d044000240a50b405a001c89881101510140149010a980e40a15001d0424000220100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232971169 1250 232969919 232969939
    0x70210020d02120c300f150901081510060903080c07050303030c0304121701091a060a0302250b0601050304082110050102011407030b03150103110906091005 69
    0x700c03600d074140c540702048441682c00e2407408032908692544154a070007410010491903505510002c26400703465005500180d580307846001011203094030140c6640e143e0386140510b13000603158140c807103009002c1000107007041856007500301807030381c4060324424000f04a81014404281c10070b0b81441229840b54440c0c1d611a0103e11250a0100b03507009285d0500000042c806a00c248101130f501035400b883c00d14010f020070b06000e8800d0140040300c9a040c8140000400c4800c445601c0008a6015000d40d036984030040742c0010201d600000315040840c0d0302241101d060440382400d000480340501204c03a07502d0030358845c140c91280083c8418100400040010100a081c809036940015190040703444040c540120096400d001c0302d010140c1c4000007000200f41d03205003e180c2846e100540d6808468586503070440c081d110100520760940300390840605d4411035091024021030050b036068032085420020000142000742883e80708456000604c100800c0000403041141c40443c1c5000b21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232972419 1250 232971169 232971187
    0xc0b042109350106060314070215070e010c050303040c08010513080706051024030e2d0a020d0510051003020303090108100906030b0108010f150e090717010c0906020607021002 77
    0x2186180460007015500301213000444a800d80c100c512003002c0c0c5c402040b096918104100c0c2c0d00d08400c0c41c40c030544039044001c42c01d41802180c501050300410b140c01e1034440b0241d128545168401d0354100c81a40f95403a04010180f009c2c030441d50001d00c945038500410f00c17031381c580801602a1003400740c10a599000492141d0080201a0780105212030b10241d103140d846000c03da10103105807280001c80c0c02c1100e040c411040201c1c64000b03104044901d49103903422909092040700d0071485514551244207100e00169440565088145200390003c108409035010034005881001d050341318000c42800c01800141e80200070350303100035401e1030100b004e90345070200c003400043c140d4001c0030b00760724000000c428000f142507654162210003000780001c14038114401c08607621082c20342c221a03003007441070050541e0f02c2c801c10307007149050044600c0c0c50b40b10640103100080d0030780f580a07240c1d540c1e80c050480e140c009000c1d1004185e540058034461412150103034a481d401032046c070415a0008620003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232973669 1250 232972419 232972499
    0x120603070f060c03110c090405010c14040f030f0f212604031209080a020c01080f060306040201080711030a210e10020f19210c021902010c0b042109 65
    0x6601b40020140c038110304003410414003c01c406640380c40081c0e40326185d2118044030804039411610301b0260514014610303203d10244805481c030440e01c03c80e40d4249070012a03640c585d0151903c0c10710103c0300c480755100b0b1003d083d040540a510301101c030800760b1000400e2540f680140e1094050505040300c40701d145200006004001004101000106111122a130300140f0900e1500c020707210080c007a140c500d00741d041c0b20030898080d0340c07590060340020019441201c6c49a040306e1b0500300803a008441c1016035043d0b40080c8021400030b0444500e00000741c6c080050070080b0a900f8104101d5005101e80f019140c2d01440c43d440781c0c158000944081c41080c880884030003910003081014800d01ea004010314403131032030001c56400340300d962401e460742c142441441d40c5502c0c00e800414002d4200800810072801030001641800314040394070000c60700304100d0302d1003184181d00c00d025945500561040c3c040c142180101044050001400752080214600600e88403c0c410740c0465192058980 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232974919 1250 232973669 232973683
    0x2060a0b21031309051006050a05120a290a030605070908071404060f21020a180504051623060c0d051930020c0102120603070f060c0311 60
    0x100c105184028507040d02032002c4050100040101071408015a84007000c41c103450068440d03481e148400309082020301e0040c0000c1418200d14103040c0c4c1008450703422400201d1049860200254451984981c4031074039076884a0b01c800080da12207200c0d2101d030041030081c00c65000007440e456842c03001ca542c3c180101d40c02d0001b05404022144220784441e5810401c058042403140180c0c01c0c140003003500f04615040d1000d131552030800c41590826201d441e8246699100305a070483d4480c1004244104c059201d03c2a030810080702141e04e003082d00d030851904140d825a0240401d074840107110408001d10200c0382c9510094041c840401c0010006070f0078810014003140303038401c0d03d07050104c3c0f58101011b01384d001002c07440c803204944003800564445124800d28000000c1d04880f03001040314500322039012880700d00006040c081480384d10790132a840b000100914001c04000c105c060f18081018401801881011250103460301d00d004c1c4c22240d490000405010040e0711200b80400308202030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232976169 1250 232974919 232974949
    0xc0c0f02040b151305060a050f0913020409090302070f18050405010b030102030906010303022103180a140304031e2316060503011d01140d0519060e0d090602060a0b 72
    0x341c00030200b109643c451079004504440b000e14128500084900d0709100f034440302d0500e615180c2c5407810100b46800c16500400d9202d038017404103c15000580c0d90f510251000d000c08080c00120b00c2c081d0b040203480c0c80c15030340c0501208142508140b1a0081d4551050101002c0d000007140c180c40300d00d030441c0904092071142d41c15620101c00c0100400e400a01c15040368040c0d020f44401c0074508920741c003030008180701a21741c01010404900c1c40c4c1104030b40d425520104070b0684981400d0380c0d8810a0303005800c51007584650001c1002d01c00d0080c0a4080d100e007007100c03040d01c00f0704541035444e098202899080f0800c070115a80c03160394400c9090000210302d030b501c20802c150030354860002504070342082c010300310310310405a10540417501c1c805540d07040e42d2a08044643c2c2c0340c1503104002d09800c105404469a010304041032040c4000c40000304040d501c1101c0108000e50008040e600d04506001c1300b03410045154410098180c011030115040741580501080310350001010840e4a403d41c810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232977419 1250 232976169 232976179
    0x30405040c020124061d0f010c0311070803030109150302030d051c0203090303040b0a050403021c26070f0804080a08180303040303090506011401120203100f0f05030606040c0c0f02040b 81
    0x22031070070139001e121030162005c503124000041040400252258006105c0c0c940281d0340c0841091650300031000409032911a14107500040d1031040007505080302c40d07001e045560310100c01441680200d024401d04d07518030b02c4074842070710300d0358000030340e0303040440540d400b4004009001401001050784a400d24000100c007075503030341800c205040e500c3d4000c407020755101c45868085002c030032540c042c40f801503401da0300400b800c0e100c842090303902c6c20f0441c40d45400d101d010380e04884c0100b82c041449091a0050200f0009490114000303000d40c40c2594500c0c040203103c50030000019559030540d030f0a500c5030300d041c16a6513243c0c82a200d00c040c017400f925450307100110030041015455001450100c1c40380701600c800d030740e030303008521035581040c401280803442c0320309680080c00c000c1d4040c5074400e56402c42c444049981c1c003242d01891246801891050070900340610071801c0412805070845801d840810441d411040018012110000014481c000c5108400103550321600120040140240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232978669 1250 232977419 232977461
    0x304120c03030f1403061302160c24090b0309030f0d05040204150b04090203040f0c06020d022404080c0708032101210803040606080a0c031401090302030405040c0201 73
    0x41040121486110490000b490403440300182d0b80305001c604c90b0303283c604041070704580700c1104104015400c84000317100c8035802d0042d5030070845060715000c00c04c3c1c040d50741010b440381060b5402c05442c100700c09441030880700420044e5569071107a81d460841e0500c080c001e4494540101c1726085d441110302040005901280070341c403000d4075034040f43c00b079842140e0800c403442039002480086d50281c404c2040400041c80104211540b0f90000c5034054400d19048005100c035a948003078548094000c4001a840103100c0b4072040d80400c04d04141e081e4141031070403441407500420411050080000700306000c04180254111410003803030000c1c0003904281c070385031161a11100408034800145c840008240300c000111450b09138040c1c0400200c1c601703034000d0060280c60703010191784007130401c81e060703540d949002030384640500003080d400d0b01c101e60214240d4510309107411504080321446c006a45020315030760010390004121400c40360103031400f00314031405140c145d005200400100b0b0300010010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232979919 1250 232978669 232978673
    0x10e09070b03040c050f01110706120b031903020d0305090705100210060b0910080f0a240602030a0806031914100f090b01121509020d021f030b0607050a080c030412 72
    0x14070b050140e803015941b07010031010420045950154031803160305079070410392040c03005034454031682d12203400008000c90008541c202003803078440500f188040203a28000d12004041d070520800103110010b150500550030702040302501c0390b44902c2070b5407151146404000d841c45c024400d403022464207040410a1503a42e083c001000e1703000c803115512070540103002c80c68840c01040d40340d0186013103540c84020303942c415140500500001d0202c61b500c5c00441d4280100090640b082800703004141e0156850788422300c00a466004003810003446500603500440071200c84021034001a5042003480944510001083e801d103011019943c8030242040381a03296041260004000240b0031160322440d43e98800600700482c0c00d02100400c01d2902c115002d0a03244980c2016404a000030031480e054142940007442c10a02d105000301c035440707200c4482900b0354151099014480d8296003240c64881d9035502c0a07100c2d031035070000410b210004200000b03800f0042040c0c5015002183c083c4141d01c60034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232981169 1250 232979919 232979933
    0x70e0907020f0c040213290307090608060f1f051b1608010507020304060509010215190c08012d0b0a0207291b0a02040f021206100503010e09070b0304 66
    0x520211102c511070b203440003010b03080620803580d00d41c100120002d221801c002080c02c807200444401c0702031240012801c2000038107880154040c0b242c40c1c4442001c1451720b40c0c05450a08024002031080c00c140e0382c80400c80d282d03c584034242100c4e01c00c060451280d620820b40303090144404000d01c4101ca40c140c0070907210006030704103980b1a02c01e08550180e0303440a1041c00e841040b21541c006070000e0004111050007100078010b620014010f071810140f200480039100320084038640001c80720042a003104407034521401e0394955403032611400e958181041c0307000d001ca601000c03045d0418004903819008050032440d102503c0a030180c1c80e070390414003100a50702c102500070900400350582c2070400303005155855611071488284280d09003402d500c0c000d402c14140700c030001261f018045181c00180c1c1c85100d02101b00c40040001071710758169250f0008000d10041915029000a161b103042c0983c1201c180c030b0450b00000e5a2869075503402c6c1e42c0c0fa0500f200c42c0d01c0031407850400700a1000300140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232982419 1250 232981169 232981183
    0x102040302090a06050307031421031501141803030d06030501240303080109020304060b03010501091a01030b060d0b03030705120a080702030a09170c03030409051b030c030a05070e090702 82
    0x84071002055141c5811860480310344e0b2045076450341c40740d1001c000150580070061224519001076484180030390f030100d00f602180d611000c40c001800400c001e42c1d99111541002d4503082840c1400340014003020113485842880300c552500c845c0c5050580d802d039004c000b00e0b45c2174190341200340403031982c80c03402c02d0180c281c503c414007440c00c1040b000b00f202080c0000300d1013140d8241d540c68130943d20302400d50000354005001a101c840e160500351415880902882e0700030301303074100002028104001425004079000041c03e04040c00c041101000b5510001594544c1801c031000040c444400b000103407540c4540c1030010902d00901c45104500c20f00300014061800d1180c484080b180d88142c812a02da105618152000c0781d0355440034000500d0301d901f415500034501c0111079004501d940024616001544030b41102a2201d08202681c00360b9a4031107135400199050a066043c00d090207000740c0401000100d20a540c3d90014418500c01c8042028450014120110350700740003034000d480c1c085e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232983669 1250 232982419 232982423
    0x5010e031207050d200d18030b070905090a110306060904020403020a030615060e1c020a080307083408030403020a020918010b0303091e0604080304180c0203070b0a0504030c0b0901020403 82
    0x401c0c03500501d4195031028007881118035602500c000c6901900c140c502d40c1c09000e5607641f9112014001c0001040e5804040c0214010344481c1941490708042000c5040c0003404009140e041c0705810750035101c0300c400d49401c20001c85d0b4040e203903000c4401140090080b80e102a620038444000001403081c2ca903c0307401d0b20f04185512914032601d40e0741c2a9004040c090f25160044500200100300001c52032000044504c014400901b0742e17590b144079840e68101500c190350701c800c00640c6a450340c22111a80e01042c0748504507110a02c010055007401644059000e4010100000054205807003480902111503004009188900302412040c00d00c04101c0f13940315030f40d0b29005141d000303840d002043d40d042401c018a0194604035408050740c90b5980d140180c0d40240e810322010840120910207000030305288004050045010b01d5624296415440c03200c066420400805012130061546c1c00e51050a4802c04641500d540c0742c03c0300c3e66044a00c02400f010800d4051000b20b94042d001802228 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232984919 1250 232983669 232983677
    0x304060b0109030b041b0b0a030b01030f110306060a12020703170601030b0f0f0f130b0918070306020a0203130f0815010503030307140c0d092d05010e031207050d 71
    0x40e042030040d034000c801400082c09078084100002c0009040020300c0e84503400f8860414142c0d6038031503040640390454603100011945544201d00300356458421400d09903604031040c0800c0da406400d000300c40c4406020240038082c00503c1d0000240940c0052404409080d011942d503541030030000c0c09120b1007035002e080e4100210104006600c03d004040c070f00c03480200728003500c028050070066900e0142d148160480640d881c40b000543e118942c00740030b89854040030810f071441e80c0c1004000b00004020300c008114a02d21004501d00c0001d041c816264490001aa500003030303041645103002d00840250380043c0340c0c20100b083c1960807588000c4550140445445021500140381c2d031b08000d010b0b00d605584140002070302644641c05160350742460750341e03461030001c6480210b0f08006480d01104c01240111404000e510003011044200c02c00c00e41d650320280c40c0d200345400012410323100f4541003180080018034160350a02c00c2008080c000103a142c1c1c2d8102c44d04d0160744072150545c0781000300e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232986169 1250 232984919 232984931
    0x4020a0603020c0a0c03050d0915090501110703062a020d0516021c050715030204230a0b0d090b0714070f03021c0215070c0b0a020a0302040513020c060901021305120a0611030406 78
    0x6003581078800307a2b07500c01d00d440c2d0640042c20100111000729011111600c1440750020000118649102d00c3c00210100b2070390b01d070000010301002841d459007007129070440d8802e541c0440c0702c0740d10400759a442d001030781d500c1850038030318000602c40441042818623403d0504820000b0040c00203000c80407a40340344202ca0f803101e144501a0101d015038460800e10402046090091400e0000700c440001c000402c400502d0343c440070310941070341002d0401c100c050758481d400c0f801c0c44103426107540e0160040ca007151ba1360310035180ca0000c44c000c1c00390052004615010450415000380408444114080c2c86e81d540326048900082d920a00d002900d110840c0d10400702e85d1041c46031280820350f6410250b00c0341d081d252030200d6002907120502d900d04142d4280004641d03982c8000243d079915440040158444465120060070400064440c1d10641c2c0f040007101801010180c6410071503904035402c5000450040441e41803070714800c5c0003482e591034404620304129081c0e015500840c040c940412103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232987419 1250 232986169 232986179
    0x60b0432070e060d0e01020d1e150f030b09150703060905160c0308090c0301060306020a020c041a0f040e07030507030b0c0c0c060706020d0903020d120504020a0603020c0a0c03050d09 80
    0x480d1000c40d1419401041c1000794900c0c000141c0c05c01c41c0a072102100046c0b0300004000381c1c204650310b02c506120341b150000401d014500240c042c2c00b004008a40c003000c0c0c03042c0f91112804541c4c07260b1200800c0342011600107212080c00303214588540c2000c4014150310300e0080c1d0018018840341c024030869602d0701e00485c413002c0042060380c59049454450b40c40c20b050b6500c0642e4540c1004206c0710741889107844160254400303000b0140210320480b00940c450211800c06401d040424500c513020f00c0c64a07a6451801ca01c02601060034541610403c210300c1824000c14040c0803402c0405030240318a4400000700440000c440b01203d00640000d2402d8a4040c6d05805c60310641001d0000381c0d1100641e05030070320f13110000f0315084d4441c96005107400c608403100d0056550701002036000d03800c207a42019046421040c04e40421488002c10466850305a0026800704501e00a140170558042030364480307080c0c100410500c90307422001400c0061360382d24040b995948039407500c1001444103072000034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232988669 1250 232987419 232987427
    0xa0b030912040b03060108060a030c030f061d07030213020d0e060103120503070e040c050d05191a030a0b06010306050a08210301081b0102071701150b07030903060b043207 75
    0x403d44484180282c0b031612110011100000081c0400354064143e880000010304041103181c02148142c1c1d00e04030106c82c82c00c2c828211035101c2e8002240030451214065a041c000c10640705613a41100d00000d00c0310b6a0414200a024851403414203031326051098450f1013000983c00c2c12607100354142e1030502d0003c3c0085505020a82c0e4140114070751511004940c0340c213820a01c6021842c1c03800600b80038409032010f040d24015035000c4500158801008441d40711401081c852146008094581e40004000300743e0b11604100c2c0940b1409209010a42c0c0c0d82c843c5d0450030003000024000310f100c5031204601d603100da03002441500c0040302d07034580e50002113142043c0d904840d00c0c00c01801c8485041c010184500d00b01030109411401189004102c0300c400301d40743c100c001c40304000061107901303144442002d801241c10403110150b080c0004400250b000e540242545e80c8194040364140d89a80801c0103461000c2404440001c0d128200114225581c41c0b2504001ca417891035116071242a000c0d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232989919 1250 232988669 232988677
    0x140c19060e030a140c030d021611150f1b1f1802060702012f010b0a170616020109202e030903020f0105070513060306050303031902090a0b030912 64
    0x300c04282c0c084804a094080300c4040c00851140f182507e00d49048200c00380102e901450707400000300c109096107414400c081c0d20700c0ca12008180ea030116403010b01c480d1450b90f07019001d110023240e0350004031070382c001461034502a000c11405040340c160171210742c0c0b00503a102d207400024034070900d44001103e01005030301e80c19110980151109103400015001101d0210f0017409540307070083d00a4000c04802c0110802c00320700ba011100028005907000704000c00b01025500402441035200c1481948050102d625a0820f031059070344400c44c05450426400340c50301c0344014015510751802110f482e40880340c3c00d003a028007220300120819004820302440404034014102281612642d001810300035886104124060f004503001c00e1405c80c0e41609480c001c5880b0000070b0b4000c50300c0840c60344220b2401d405441c140c1402d101d011b091401180d07480c08000c03c500d680316505120509071188590455100003c06070140c0101c6841d01d40601c003ea00075030719112580300d070082000305030418030296 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232991169 1250 232989919 232989937
    0x50708101d06010201180b160e0604090c090803030c0901030518121b060907060e03032106010c0b070903021009030201020c04050c21090d11060601140c19060e03 71
    0x1029070784044101c0705256110050110307041d5983d070403c4000c2c081c1507a0b0354010040c400c800c501050f292031000d4850541083e072181007807040c1d9004000a540d991070a540c180c3d44007000c0040c001010342001c0700c00039080d0344001200c1c00000140003240070102c004002110302a01c0a100c0d5071554021506030904162190100c0d0300401807288a84a8541c000d00c16191040c9541c003044410391421414400240c0d02c805240d800440c0800a4540240000c8030b000c1e0304a01850800c20100c40c0544134500c211803203440418842e001804c0eaa0090000801094011b001814a03141c503107000380c100c075103a00007a03224102626003e542c05105150070f03015240d040e40500a185082018017002d0030018001020707454041c06626540400365400c0017030a401101500581e04024403201e00388404414008100030000540c07000e61040025020307003001b420303c0c0c41041c60500d002d10034000d01078110024402d00503014030411203168030820589160080d00204100b10b9032071b0312290f50b03106003900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232992419 1250 232991169 232991189
    0x41508011409041a070e0a061211070203060106110a060c080411031209040209060f0316030e0601050603180c100504030204060920070c0b040b180108040b13030e1305070810 76
    0x203810142c4d04071010f80d0382c0198a03820110150042d0100040120407544c20250004100d00c1410124046501859212030103521a80d89000c03030a801191710b0329014061a004d2028045e96003d0b007030410081e003084d154001d00100903034000400000c16a08041da420b031070074a0380207d901503614001c5400c0070031860381c0040358900b02c5c01d001803101039000703c1d100c5503000c841406001120800303000114895407001d08420f141010700c8030702404a0344001c3c004d040a034032010040c00741d519120112034001090450412003030000c81a00351901e80d8070700c201500582000d40360691550090301500640748211001d011036a141d07114402141c94480c40c42031312a11030500c0074941c0032580010403c1c1d078041d0100e00351064440383c00c142c050748039078040081e03c3c0303001441343c00d00000000c800c0f1482c1c0302407800c2142d42c1081d403224208071001410000e23400325100070000815010307030745607402c800c2c000c3c1c204120003182600711001440c0440b101c1010500e182d0004480741c54800d0640107445241c22 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232993669 1250 232992419 232992443
    0x5040506070f0e0d1703040302071a04030c0e0a0209120714090f011a070b090a14010513060e100e0109120f1e050d0504060614031203160504150801140904 68
    0x8208152030a04900c181c4000010f0a552a280c045c094000c5204a019800810341e1515001080510420000c0c100c6030351071040c0018000120082d80600c201d6850051203009038407902200c40091080c1295076501c0803000e040c440260002080d82001c071440340d191890700c101141d00b449001c40044403040118100706006000c811081900c034100100244001800c1a10582d5044260300701585ca07480f01e030f406403a0b41c604000a040c800b40d40070106000a00a5040c4450ba0702e0842305002d03001030030b0303a44410038501a014104400101c9c1d585200081c00400104207101e8000c1080f501d00b500c8000c001101981110f0080756451403103409640d91106003c1e0040f4140a42e00301d4060400030080b0810100c2c2c00c01c051801000c0c065070141c840014454a01200010a4040400c40c90300a80114554141411046059030707400300e461051540c01304c0c180c807011501403003240c000e0f45594420082000106610000c214145c0b84100011403103040c8400130051f402404440003006085180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232994919 1250 232993669 232993697
    0x6160f0c1a04091a0a09050121050316031b081305090c0d0c09051017090105060d0813030804030c0e01091a0f18070f020105100b040b0717070605040506070f 69
    0x19020300c00e2025407081050f03100e011400018208840c0d03900498510b5115001480041c007800c21070b00761401040032780c191b03074151a40c80948900482c4000d86000301101030003010305024401c900c0510f62400ba5040384020240b4218402e6040020b1078a200d08404074007003014100a04602d000b4442e512813182802802d100c2000078040c1f840c5401c08000300c0c0c6000142640300c4e40c205441d00c08a80e2140c1342140c04101341000c0700d400051415007560b0400d400c0c13005a45501c5955980c0507080168291355206c0c00329a4042c3c400146d00041004100140000501c0003030102503098078140050070110740d0380c80c2002c4043c5c40380002c08006181440d024642e03140b408110401c0451800350030003250600382c00700125021800c0364800301003041401940c1542d54284581c5030b00c580d110028030811030800268200a003c0c60203007040740380c800201d00090095680b41000c1c001c0303000c1d88484c1c0e2200c6c2860081c02809041d5801c54040c40703424041050701d40640000e07500c550165460b02102c0d0641e03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232996169 1250 232994919 232994921
    0xb0a1e08010e2a030712060b0310091e2a030b010803030907080d02030f0c010f0c020d030b0108040803060607031106010609030303140403141b01021209070e1b0906160f0c1a0409 78
    0x805021030341195950704116442d2010301c4107400c0700ae541d000c00100d0810b94148030741a8440e10581400c1050800c0b400c0b40000c40d55025401000d402000043e0b8440784004200c46030a0780d5007010780f100c1d020100008060a0020046204007a034006503a41c259031181c8503585c580703510803500c0c0035030010b00c00010018014409070074044d803c03d002041500c0010480d03022505009007a500680207003540d1201c60f50140a4101c13051401c3c6041001d500d40b684442038030380005081c4901c112400501c200501d07109026800d035040d1030078290b91143d652120080c2280308035200803404603081203001484030314000c04003403085406494841c0203064402841449510a00500b01e2200c08600c103140c844d4004d2000e004410210410030510f030500f00c0c0c0540c64a0003c0e40003910f5103c09204002e07074418840040c0d039002d0161404203848252000001d1000c0c0030700b281c18044c08000b0049101408840b0b191441d44d50300981540d401300b03440d0340c994a8502590302c034660a1a10400c000c008800e16 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232997419 1250 232996169 232996199
    0x20f030f04060c290601030e0309010903120c0506010f0609090b0607032019140f10090309031703040605060102030c1b060702040608060405100b0a1e08010e2a0307 72
    0x4103001129110030000105021302c20842609003890700c40c88200a4a03580512601c800d05060400450800d4051400202540480c0c0001400c8001d001021903801c1c1c040c18620744d05d507511000342d0341150f071030710044a503d254500c20721001800304140000d82c171045101e500c940d8540540210703d4060f00740c40940b100300c110b00403091420506201034aa01d07000b8000c02103c0015450400345816003070900000b9200c8003c03136000c641c0c011100082400000041102c0c4c0d41c8042400030940f80c0e410304007a02d00e102164000b131b00031169035580e40414254440110b20582c8288010040383d00c880700120380d2405074414813075482e03101080400c10740c0c2ea6660401214200105803030314050702c5501040a0703030f5840e03008118a50000043c0010400280602d51340403c1c01e0100300502c1603181c00040d0001118444d40c003120240c000a4425401c005d80c425018102c610300030305c401101c82c98115941e40d44000a9013101030031880383e91500350702843c0c04400d108018010103030303a8103002e0808038a0724 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232998669 1250 232997419 232997423
    0x230a1212090b043302031c020702060418141005040e0709021306090803180607050a020306070e0f150315031e01051006080609011a0d020d090201020f030f04060c 71
    0x2a0341c40005404840c0a00410103400c11034111203030403c4440d400208041c0403813070382d52501480d00080d81c4c266400000e8a07900800003407030340100072910114900138400c0c1c107070107500803400143c00701c4c284407102011131400e90a9002041a901622414500c0b01c000b6079146407100104c000411941ca81600541a070020420940d402d580e56407620000301d0f4000d070310322031591a0101d03003003040304d412241c01d0000f81300c0e500c0513510308001c0d40b200d0085162034528040c42400c01040c220180001000452012035018003119031034200804041c203c000344441c00341c802c0d40c01c074038013001a081c0500c10140d546e0101078014159120140000110412240ea407901446000e5100062044900c01c0000d0b10b20441d000143c035003840c3c50403c9040e99541c00c00d0741400001c1060025903101c452031181150f141c03110008918034804c100000910990044404090021403885041c10300c07a803003200304070b100360201d46000c3c612045a07030f01da0050f0380404610341c03018401044000c0c0592404c511040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232999919 1250 232998669 232998677
    0x6030d08070509131a1807020a24050f01030209060a05010c020909160b0c0111070519030e0406080309030114061c020627030706020708030d090807050106230a1212 72
    0x7991622800c8115031710389580044440c0c404203040c0107820a8980f2031203000726140c2d04446072411202c0651b42c1c540d100b1004280075000789600c02c120344010003410803404007160510140c1405074480081810a00003a403061410202150191030011080001c40310186c450242c0c80c0c5032074003000480c903802001d140c8103000341c3c0c0c035030b0117060845810800078010001d4140c0d11450300c00481401c5840c1e0301074038941040304009400101d0700c00111200c880640703c6a16075551100e15046030f84020812159403c18107001c008600040003201a152011003980208442c02065180080000c416101c00350030400402407101590086d59501300490300240491385402061000c407544075402140e805240d600122040303485190030300900e40100080c1c402030040c50b0a100f80c1503264480d1001d02c6010307503034401001c4100140030055a41c4190010001c10180717a0f20f401c04098141020508103a182c1405011381c2e840c6880c6052100b5201d03001c803c100602a1980e84c0d010500340708074418280 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233001169 1250 232999919 232999939
    0xa02090a061a0307030b0915060c0c100309060b0306010e04021c15020c0c0a06080117070803040914070912030f0e03010e0c190e06060717040603021206030d08070509 73
    0x82081500c0141860b010500030a80d03a10303004a0041c100c600003a6014030510b000e00038040050000d1080f9095600101c0b8030a940340c2c6013031116482e000039800d81c40e030131240c0c02c11008041e80d01540300c20034070b40c090384082c1314403c1c1d004101602c50a090003000500031281c004507000d82010100000d101c1111001d00d102200c1c0358413102040d00c0085038104130380340c0000700244113000510012103802c1082d03c03030659260422101030f1503100140a0848105460100c022414a04008170f41c000c01006007940d681d40d40303600e950070207400081e40600c5502d14140204059500c030b041114221403902400104031780300740c0e42c2200c9108030180402c040203c805606a41641c085c829482d2048034080106110b19048090000c0000130b0344e0000800842a24100042000703e801c9950250044464a42c2c81c003081c600190052000407002c0b02d20030000c540411296015401440308044800b2201c910350360326802c06940f030b0500e00401c0300141d25403011070200381c007503009001c820313800400c2d001384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233002419 1250 233001169 233001179
    0x130b071a040b010306140717090703080705010c140c03160204020d24050126071115010e010b072a05031b040b030d0f0c0503070b0f150405090a02090a06 67
    0x426030980d400e0300d007200303108010002c10015201b03000b10402055000340391854100b8002d004801415540c81e19203101100207007801e1428030549002e1a80110b081d51070b5403d6040890081461182903000b00d55040c00d2241c191121405564031400007400942c42c0402c641c0f841c0c404210380c55412030300325800380001c01c401011070040060040e850202451505480f40c041c01c40305460703500007814054134180c100c000d0107900c190012a006403010544a82d1140142100d61403058100e00000d030081c40847ca6080c0b00d4644c1c401c0c12a841c4280b80e50144c5d884001407000c40c0b098080c005c1403c10079281a21034202c481102007103070180c074070031009110354500c0400e0814074234480350025500c5140011505250511902d0110301c001e900408820100c440003030683c9a4044010081c00142c4100340d040000c10000c894855a01405404940c1418201d1000001055500002484540301e11010324105481106d1240007100000c044014035a000d2003200407000c0c18449620741c8407000072403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233003669 1250 233002419 233002463
    0x10e1306140c0d240504020903030c0604080a0207060f0c060c09030804060e03070b040e0f090307061b021009030912140a0f0b0903040b0304080a0e100504080f03130b07 74
    0x4400e9082150940e43c4402d038074414001c5406060440c800c0344c14a03070a2141c8801d085005205448095800680c0ca03100203000901d58007480e05140003a11400f010801041200f6001d000107402c40c1d001c407044603480b04401d0341c0c141400185100000d600c0d070b00369408507502c0d800c901c12202e001c0c10000702a07501c4e0340350f0074900d50042d045500440c01e51040b0820b42d0404100305001841041c199600340750601c45598905580603103100c1e182802000441c1d440c50042c8120f4034a507a0007a010841e80c5a8003061500b0350340d50300d2021016015101c0c140d085280c0c140a100358442e45a80e480a11350305024400a10140c98036040e56106000708d006a13081e0340c2040780c0c3c62894003d00c100101c000d020314019003882401050400103400510040060b00c5071752095a801c10b03405510140c4071034503103904660b1680794a000350b51281003a0180401d19401500400a90312080d06543d0f240303442d52041592841162158074490085030b81c00c01c015044200602105446901d04080f00444480000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233004919 1250 233003669 233003671
    0x100b030d1d032b0e031023040b0a0f02032a210f060d1a0a020c06040c0801150e060f0103021306110c0904030c0b04020f0a03031e08010e130614 63
    0x1060b00415140d1803094289089464000c6043c5150085422000101007900e596031968503034500740e1200d0100202c0441c4c0d0b640b00c04070700034003000204207141c54100045666001e440300e0500d00d10300812404084200d008807449000c044030700960354851200c10300c0d05c584010025040b19038080c03000d030040c3d07410050403a401c0a120a00300040d030402820314040c41501500d054461600586400c00040e140d22004107209981554a242c030f40d00d000c040c0003c0c0c8580f0020b04614010f8104120400101100050a0fa00600000c00004803005050150700030a80620b40e03404c101c40c0c00180c010718100d010360743e000340306160160070b10f41d05003280305180013341c00050200c0c140e03505241d000c00342004481909201110b8260346414107440c0501030309005140509035960500009066440702e03407151300582400ba29000507240e50741801460368181a4090491082c400040d80b5400e2050420b141078030000140c0c403e031a1120340841d41c42c0341e50358404413485601c03140c900c0200a900c941003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233006169 1250 233004919 233004943
    0x310050108070f06021203070306030f050d090614090405060301090609120f02070b1c061a13080304140913020301050f06040f110406030c1403010b040305100b030d1d03 74
    0x424154104031540d030408009400c1100c0c0300850190400034658000781610401080140305a92900c41220031400781001740c0000c1c1c401200c841c0c00e00c080050009010740140c5a564992a200c0d45450042b038045044008200d401c15062000d07000d5860117501507904080c00400000722080156102000e89498000c1621010528030a040380580c1001908602c84658400fa040f4203081c8561090103014000c58095142d0618042000c030b102d040d4014000741c0303141d00030f030050ba101c60b8412482c00d503c610112150b02988400015981e000001500c069420311711610784510210410b0107a0a01d0040c650501940d000d501d45000d40c80a1044a0203114852110001441c00d941404151082403081c001000d02c2c058500c254140010140d40c02c1e105140707004034198000d41030403640480908402200124000000a2a0048100208220f0741b1400036981e5021601c910002280d0421010503015003000844502540c070803480502040f2004044620b1621400c0200f441c0502421314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233007419 1250 233006169 233006171
    0x902251115090a030b040822080c0a03020d111512010e070f1d0102030d020c0109020f19090902040e012d1802060304060605150d051605120408090310 66
    0x31240ca400d00440440c000780300c0d00e140768602210764011030300001c01c61202615410712a00850704021442c401c5075245401410b46460100c821543d450031804148038440c503901c104040490303103040c441c0030340d0200da8008041652103001522072a9940c030411070284d50155151104003508130080000c0d281c00e001c0d111210240b076051a1041001c4200503105d542401307415106180320a501101d903920f0001e40a030408001c01c000b0340141d00c0c6000d00e5800080d841e00206031007007103074015030100c9102ca0085500d40c004401940a010390031100303d00300d5000740b2031706400348072aa205400c80350185201610000390000e9161216084950200344881c0041c3e09203440c40b400c6a59180520390030111003820400c810b040800a100c1d150134540090085c200440000c041c03283c85d910490080001610310103550b045400004055072005104a4120345000e02003001484808442d4600e040c0c03d803200d5250146442c88120340600c020805c4400c0501000000c0c401d0303c00703101018034204003003c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233008669 1250 233007419 233007443
    0xa0308070b07110d0f1418100f050d11090d0b0a050615070f0507090507050c06070e0a09021c0f020d0f02190507050c06070b0910060f090225 62
    0x28181d080d20300080d100c0c60400156600c1c48410000115041d00c910040742010880401e0b58501a80d18480301401004055400700c0d0803051103036281c031506070a11081ba07451a1072400d4190644008601e010481d001981c14041e01480c0c07000b40d402050b242580904443c2051480707400a244800c00d44001ca4008520307800380040024136002c0e190f003014080302d100c4c1c5032015040c442d000b140034441c00502035075040a441d40502c48140100400703040c2104087c0032901e00550060030076400340e00042da60707101d8100043c60041c030404030318844d000c000300400c2c0c1c000c2c505446900a500a0384d03100e22451161640150b08402a1242c000140c40e00040940c403803600d0f01c20710040701c01c1041c0407000d01e8010000701501c0005076001030012004c9080c400e490b09801d00305a8904040d9240142c0c010b5800902d540c00d0224006080c0c2c403a640140494090b00001c003414020340b84188545225160590710a02040e0515005003290160f040840780311100341c0101d020051030b2084041e00e03440e8946e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233009919 1250 233008669 233008673
    0x303030c08090a0b061e0a060309050d0309020102070e041b1e060e030d031806060e0f01060c0510020a02032217031219020408160f0501020f03030f0903090a030807 72
    0x8180e40c1c0c0c0300c00460040d080016413a00d80300012003005241c2c40c402c2c0310100c405a0240300503e0a000a800c3c040c02071a495602e62001500500300140250350901c1500107080a046c40ba0082040350360b4180d0140504034a0130103002c1d0142c2014100b160748000c00c085d0009440151381c00b1a00038030801c18030311030480740703050b5200102805030400320410140441c615107d480c00201ea03c0400c42e41c3c078001440039150400001d60781c903580c46c02008241001d00002d00a40d200a100e4001e000480c811449660780d030308d040d030fa404104000203180360004004400f10040e00d50252003440b40780d0040d00e03c0c0442c4211441d1620340074040010704040851800d1100709441f04011041030040c8008500d03003401101081200b0300000d141c8402c4500032102141c05403160307011350b0000c100400860300c2d0b1500c44000345074100c4040c0200b04c259490039400088a62000640411860020014511750384401900000c008802030001c0d060303110403c450009a180d2271115001540611400c070b031551018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233011169 1250 233009919 233009927
    0xd020715050a0219050703020a03110103050f0601080f1009060f0305061b03042a0902120f16200a0311010c0302090a0e100306150512030c06010501110a0b010303030c 73
    0x150024007003040a0140240c110340000702c8040728441d0110f504002c15191500c286082c07041d401c001d4201c0c0d2801c400004120f22100d0002200400740c0b000d110030b6a400e1842881030100b00d50f89400140c0c0704011443e49034a004804e40c0080c40082e560420a44a8100c0381c01e940c090b50001c80240142001001403100600100f5000b00b0f528a0b522440d1102d9031180ea1180400303400940b800323503001100c0b100d0b4442000d01640450451000c041440d0f40e8602501c000d40103c030341c0200d00d043c000c0006824261004901d48120101d210400c03c031018003c0c1100e50700c100540c05a02c20100c241c400454000c10060000814030079604c806031110310613891429a411000002c05046c0107226441007a581c4080c02001c2e02c09030305c100700c80b0b40d0311f80351424024251940040c0040d07250101c00c06288135400152020f948064488201d858035461003180d81f0721410641c040c0f95000600144825072181a2400110002c0b00440e40201c40645038400040001c4c0e0040300170a0303888820f90811504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233012419 1250 233011169 233011199
    0x509070503060a1503022701061d01030b030d0509030109080c0f0f0a050c0103051906140102010e030322170a0201050103020411031009020306033f043002030d0207 72
    0xb440c01384900c0360780131250001c407411400028400d681c0345134404900c0c42c503d10458003640340d12442c1511965510710250201c2c00411207a40d10002903442d07040994083c0c01810303181031020307001301410601c00c0421981074201610490b41075403220305150211311007502030701c070728000d580144c24801204658140b030070003904000001030f0003007201000030983c0407400203402002800d011070b03680d42d0708000900c880181403420807081c0c0703401e070041040203826001d001c42c090282c0003001584942400c4542d0307404120741541c20040350800d001d2410003180c83d82001c951055044045991400042a44a800518414005079550b10040003549020b0042c0340e03d02411070007031481c508080c01411b000c04801d02410410b00d0300040401c20a4600304103005030410300c000c800d0b428114882c03040381440100368211041d10340541003220341c001070314200d408403910000e1a90190b03c941122020050100c05641600c0040a0040002d624140116480350005501904e07403181001550402041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233013669 1250 233012419 233012431
    0x90b01030606211a041e150f0b0306190207050a0308041205070b0a0c0905030f030309060603030301122a151d01020a020f0a090c021605010c0309030f060f050907050306 74
    0x70400c03001c40118500c140003140840340d1102d044c81a07565404d040e6074160119804e40805d026030a010401e01070040d030103159480348801c0c2480000c0081204001b500e0840480c01d501d41c102902113034014405281030000c0c000b0182016040c8101a290182000a98035007980880d00790300c104410804850188040c0f0310240c1032903810009551101e006121005001021941d82c4620f01a910740c05080c80600900d401000c4803105912441902d459070002d44050b0b07002d1240b81c022440610780842502c3c10b0310301d0b040e0841501d400b251154008400d00c2c102400c07410102d11031002021300f02d403110340007918003402c070301da4103101c001d40041807003181c0c4c46107900b40c0801440045040e07a01148020403240c040716404c102c08c42010004441101d0355010810381c520342415041d0641d0041031000141c0380e20500b130016142ea0b4401074038420a200c20003800101a22414800104004d0742da600060240788005480e02da91a6100212181541c14205c540c1c0400713000c01083c50b0030440c16901c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233014919 1250 233013669 233013719
    0x403020c0a0605161b15020c0901060f05070305040e0103031e0e060301090b040b09070206010f06020c060f0f0d09051b1e040b060c01060909020f09070e040f090b01030606 75
    0x1d80390500080c164081c90031850038502c94041e0280c107209030740f2044211520a0400400b260755103950f541c061411240103840540140082001c1900c0d05c015014100c07030458a4010300c9443c6080c0498590380010b82c110140726040c0030200d9046d08080000d4080e500c00c0d11082144420941d80380340c0a1803081030318041044003401441c031a01d540c419641110f06a0300040b81c1c0c80380c0c00d00020701a000810342c2c540c0100c902c8040028050b80040c24604840100c01c1002d4000c0c0c4882080362590000315906400450402c0714281c0f941c0600000d01c1d080c2d801c04409410046030108c030005403004210281c0c1d450b80803902d0910b03202c1003400e003900f01000844d100100315801043c0901c2d00316010b004c0e1032280c1d550f40c07507a0145442c0d00c1c0468034141e0300c201c001c012098030b41e190b80380204020b40003680550481071207401720382090310000c1d00498243c0c80d94044022018204009003418207450000c09841d08110000107801069450285200b01c001007485401e108018034a1441c2c000d001d0741c21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233016169 1250 233014919 233014939
    0x140a1109030d180902070c03120504030803061003060312110f2802150d150b0c030313051c0509090601020c0a0b0315062d3408040605030403020c 64
    0x1664002440c1c0d002d070700250600c0d6200410403004429038a0b0f082d8480c0301d00030b00002c3d456042124004080b01924410410000c458070310b0301c812501c0b0b0042c0e00000b040250104041880c0d840c0c0308404842c0380744546030104616460744e0b2001140304e65804039a020423a0400c0c51411400144140c00d00aa013244c020844910002d01c07601012203100958001145c10428001c21354070380f03d140b0510054011100ea42e10b50810601100422402005480c840c00001000c070754035528408a4502010460040d030840e11a07140030b06001d940c41d481140c443c82860f10b40d42858101418072684132500740c68098071183e09906011807030000801042c119041441d00034055a15900c6000c2076032007101080d070f01c0b0381e541d400070748a1a452907007840e40000d020034002208020190070740707441c94500726000000042441d0300c40442c05040b0503aa0116408400003c1741600800c41294040964084080c00c0c0800e44035450710364015004100000c40010401050680401c920340440100b51101204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233017419 1250 233016169 233016187
    0x506010f02031b0c060c0d0807091214010e1902011b42020d14010e0a020a02030904090b01050901061d01080606210121020d08090a09140a11 62
    0x3284251031542400000c3c6503501100e00304108000c01c40d00ba0082c02460b07444850041040d510300030000d80310001120307000000c0720f140c81111003008072150342d441c0f20383d41412a9200b04404103150f0080446660729541118800020468059030702424110424000d00e2400010041540d44000440e859450021b110005180387d000580c125619038106c00c9501c084050300c0400d144120290020303e840120014620340740e40c1c01042c10003e01d900800084110b03c0020030a04e40911852000c0807000000648441150300104000d8090388160ba140c002d401c0002004c555045100b6124141e81100502041c140305849a002d01a50b041c800f41d0303222010501101c000e2081081c0f4100300700c0d80c000c54030360344400302510034090b030881140071202404410071080400c240709156615044406840c40d05148040700300328103401420481a91149444143d1320703910599240f030700800315142c001070030310640c0700e45491020062503001041c2043e8006c54240c601a5590074840134003000300c950 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233018669 1250 233017419 233017423
    0x120307020f01110f0703060204171b01050a09050d120f1403011e080f06090c0d02030705060304020d0209070203090108060f09060f1302040906180603170906090a08100506010f02 78
    0x11803802481c0880070344108800e29418084884c4a5240510400e1004010043c1540181060f01c07c2d092000c20802101c100d5960307290304807107100c01c00c1c03050743d11070f0389031944544018030141c001400c1255480799104003260903062004010b0b038085004107202010395500044040c5020250720f4450b60722503880302d9002e054031040c07286c001144080c080c01c40d47c1a1801c0b19580080418400780c542c0c40413251015034aa00c01140e00080303e00801000c4900ba24002081d4051190060010f2110310b080c5000d00c2b400341c0c00a0820385c6e20032000d0300c0310700040c1d40e0428160310800c0c1c03d60155072611b07400780001d025441c002d88950710500454404a4050701d48125103940310504a60703000c00080b062020a80382003030084080c0340d803400020041070900700d40e00014102c445000c0e0807103036403844900030701c01c503800b0340001000306030924400c101c51074404010302204000100075034a400c0c8030a001420000c006d90116845400c03007a02e4a198079098462a9407160f800c0c00d0252207a0b180d02c030009c1d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233019919 1250 233018669 233018689
    0x30f100606021f090f020619030608030a0c030e04060812071b0b090402031f06091a0c030415020304080d03050f090c150a0201020408121b0d02030d0903050d050708010512030702 78
    0x288049135a0300500040c4100c07030f000c0409082d0082c0407151f4031b44942d40d5201d000d400800d40389000c241403600000b0b03415000401c5035078800c0700e5501c600c02c84015603011940b03050004660ba91240e2640c1b40460071180030300442d1040441c504070551340750345a1810011074010034070540d280c128240410840c1c00241d00444400000c200c40042e62541e0304107001c000700d004462104800c80c2884000f080c40ca82016011007039580e410a8130400720020307003e201213841110f81c81510358100b0300c820001449152440c80c0c5080715401a281050744909410340380114401408001030349032400d012100d200c109443d50880d6401024250214000c00400e44551407072028140b0541c00280c03100070140300f98161000b81000c1700c00d68180421540406003c1d070880d503909085d003a400ca000c244110380024004001920380e8010754244503484918500821780c0c0d100503420302c0710420003010000c0c403a1203001d201c0c40b1b180c1c4410200d941007200303101088a11454180031940100074010159032000411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233021169 1250 233019919 233019973
    0x2105040b03070513082d070501030914012d0b010c11010c080301140103050601260703110a1215030822210b0a06060e010c11030f10060602 61
    0xc035030366180c407042140c50780306003072032a0550b0080f018013003a10800850700011000c086000303181e41100c1d00010b031030700c41ba240d0b008504943c00a641042694044d40021442c1070042203001c40045c0d40c22801400d58890300e2310f8908910184441100b20b1b454a124000c03c81c0c074a88041088030103840c0060090140410040c1811094102c0c2401682c42545000c0c1d038164000342039503c1e56540c0c1c601c0e89000350015100c5010230f04210019151f948141c001c5c07a580640b9000400c100c03240b406480c10800c4d400b406400030140c031201d080210300902c0d0003c00e4042111351380d507a1412241c642c80021100303156002c44031000009820400b0941080584141c001044c1e441c03082c26805a214500351941e1754410080115440c0007045400c2c4041c00d5403403d0781c0a000c60309010395800541008841d164020704010910510010816510130282c80d1000c82c032a682c090700007640b110001e464072402c40b0002c0701e03c2d800912612040040c9000d101b0081005000a02d800800411141c400107110524 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233022419 1250 233021169 233021189
    0x403050a030b04110c0a0b1f1404020d050f0601022a1e030f0d0e0405010e0406090311060112140118021c0b1302040513030807030c0c120507210504 65
    0x340300300541e0b859101190842103c00016a02c5c0b03415140b03261a92900703042035a511041e00c0000704080c04100c9401c400540f103001c1c0180c121304041103030024601b40502c560f04168240b1600030120081d00c9000c1c025851710070030204a141403000203180031143c071665034002d925001d1403015041c90348020038031300100b05c4940c04256104182105203038134030008a6850f11601461600705400400d03001c51800312551038100400741d10050106590081c4980540c00b0004c000280106160740d114141141c403a02e0076034130458003880c030140b40003820b800c5201803010703c8103014104a19050620700a0203510001d00440700d0301000030090b410a06001f0303026000c041c0c0b103124104040c2c01240f9485a000341c9101c446d00b024064030b048000040002c0380200c1c90900455140008519640c5003145d0541e5050903980c0c03a10002c4001e02042e5090380207101076400c5000005d00056800b014401c025601c1d940c95005a00f4254054010fa2076600100c0c00300032240a61a64014219003d852100c11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233023669 1250 233022419 233022431
    0x501030c081c1209051f0507180f0501031e060f080d0c0b18030d110a110102070f02061312060905011407170411060703030e010b040c08150f06030a0501050a0b030403050a03 76
    0x80131401c1942000d81c41c80710741882c01c0525006c004c254810360003080f19560352401918400c00c1424510441e0286461350032030900d04201c5036201e600090030f00129103011300d4240070b18010f44d1040d03965603000081c581504040600034060b0410000c40056110b1503c12100716103038503403280103d030240c484400310906070a92000c401007001201e50011081004100102d0702141840040c2c00040c180300005140e00031520041205000b5100c01036007125140059030080d81c200182c0d40d105000c81c10112624040001c1d05441342c1c0d003203110300c601030400070560a0301d502c2c0c51070858565041c400300b0b0b205620107000e115a4810410091039200134901c401c261100c2c03c02300c0b404a0b510860544c0010001619820141c0c140c00c070780140a41c0c0002400505130700c00422064031498104072000074002d5000071111003d41829040c40350015002c2c09200c44413401107402d551045610140003521800100114101840325100501001c81e00300d040d42403a6030020030310300c18008041c04064443d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233024919 1250 233023669 233023673
    0xf060405151306080402010e0405010b1602030111130302040609091a0402010509102105011202012015090d0309020f21060a0903030e0a03021c0309060501030c081c1209 74
    0x49609000d00b01426004071941d54000030b020318002c80f0224005075811510701001d003071078045d8505907541c44800c503040003040f98108001e901112002c1ea450f640720a401000126010008c2099000c20015080003d0071801444207403401a4013180c00c1d1454202e450001c5004100104c14064124001c152140ca482c00100c0303440c014800b00a40c003030011400c81c5842d40d000403c504072041040c070002e660300b02030000001100c609200d079003000345031244503000540c8140b803200048000c11240b010a07400100c0441c4c50900e030b4400500104104009002e12602d081102000300000c520b414001210380f5030104500c580d103520181d01502e80e413540070720315070355807030412402c1e119120850b059481c1c801d14007405428020400d030003007031030080014010200868448040c1c1d4041d0024225004054a80400c00c82001703008010981ea401a660010b44c060042e1402507005104011817a801d2560f01030030421010644caa84038540c61120080c1600045107141032100e4040c00201da031380b28 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233026169 1250 233024919 233024959
    0x50703031e020403021c0c06120e06010b0c120301060903080304060209030d020c01120527100207050d08060315040209070e0405040503190503040305220312031a0f060405 75
    0x3540303540c160460072040501c4860340c241d0240045900881d580c0c002c4400c240c40c4844c0800300604080c0c031101c85c0d044144a2180288200214141c0082001820048001005040c4017080e0400c0f121101c0000f204807180c90108980316400420020052640d490044080d08844880c800240b04030700c080001400c0c0442c0d603041d10610240641503514030f20004100035116900a040503000c107108110b034000d502c00500c585407152203d50300d44c0030802542c22204070000c01a07080c414070307841050281ca015a41c03e0000d032403031910510080ca00030035100760184c0000c200400a85c0203a00c4030301d80300d0300d03400c1001d4690340183d01075070303106050703122100700716030f0315441d04000c0d60068241000c0c0300412400200801c0c00e0840c46140074002c0401072400c50300c1e88416280034001480910103c048016004404c10410400c0a84801c629aa9036a011b852a0700000c0c00070200c2c0c0d54140001481c07a150860680fa001e04a40480790341041d5030005032540281d000d61401391043c040b2108580e80341c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233027419 1250 233026169 233026181
    0x192103110604030e0406090605150f04030c0e01090f02030708070e122418100b0f12030a020606040e120d1508070f060203030f13021503390301050105070303 69
    0x200c206850840c5018240a4152094481124099882c1c21000a00c01445124610543d40000c226200c080c800c00c0001c8410707040106d2420300c4c1031003000004001183e080c5584024902e648a02c035141d85040c125500300c55403c44840d039000d00400400540c1036100103515030103107060600941400540021130700c56810b052100841d44100d11074403480e5803102400f0644013880e110340802da079491403c001c0001e11160810303820313580222b42d0419a41001e410034040f692011340303040446003801c800112081866041e00002d5080024202a02c617410301c24158003c800341ea0503c08400781c0301c0c10381d54802c0c64401c030683e828004180c902c660b00481d0040032141e40c4500324204201e441d60742c4c1e42d45814603482060b815400c00400000c8403800881928800d01c088080304074181d031103a68040c2001d104104c12684a44e0f902c4405501c1090784001c0d42c040c1d0b0605030001607040300b82034844140845400440219035910382c2c0071075a2064201107905546083c80d1294a50701ca91030258003401c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233028669 1250 233027419 233027447
    0x51b03090a06020f070c0b0a0f050c0f0601090506091f23040207060b100305100e04061d07060314060306160c0c0e04020a140d0204180506040b06192103 67
    0x100018420f055560410050001700d4084d00741e00d0f180343c2c6c1e0742000e100300e840f4111603500440c0a08030b031011031501410281a00820440c155900031032030381c441b82e04010f001d0700301d40040d9940b18144505402c00c00700c95540842840c0b4184084648803140080126a80c41800030b80f0703034200c0c106452003004d07011070103403c24007510035500c07a200340c60110082d01032040e000340508151030350105030074801d0144502510410200b40081410700d050742c0120360004005a421756150340d2145103107001d16a0200c0302070903c9002d0900141071100c014255a401980060b0552440050044071b60740070580320382010700013020340400c03180440c0540d9003a15005000d820804500400070703100080c040c81c01e1040d48201c1e0303c090b004c0e072100c0a01c4c07040703102440d0381600f0092010381c840050400b54400d14450a0303004030301c40380280e641c2d00da6181880c02c035412946900e00200b44803e42c02c01a075495500f6100303403204209a0b040110252a21464000c070380c41e1402c280c600c000a141c012a50109010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233029919 1250 233028669 233028671
    0xa121505031b031219050d23041e0312020306031c050a020c0904030e0405060420070b0c0a120507090506040915050301150915051008150301051b03090a06 68
    0x12001c20340d10707116078182d42141d402801408401d03445490600e00b1201000b041d1121320300011290070044402e50880c0c9110010309035111070880e00c902d404100030b0321600000c0ca10400700d29092034a211210300300030000b003c0c508206d24800010f034001000b002c640051010060301c99441800280c40c051070007070001c15100c2146001ca643d1544240146600040794085940c102140e000344503407020110303406400200c141040314010f01d4507402164000000030000b281c0e9200e610150340da02001d1015201000320006801410050003600080e0312141d020302140c28460011405003800c1c00e201c0840524545c0d0341c002490841c002d05501001d8040908a60b0315507458058a070020611002c07405d100708185840001c06160501070142000c40590a421030b0620f0b200d281000b07015044441c0341c6002c96005c01040c65281c00d1200000384c61a507070740c00c640e0b09061600702d0307104182c02c07283c80c0241d0502d0f00b04840b008926a08000400d8058507440d5039540b1885018188550700100600007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233031169 1250 233029919 233029933
    0xa120b042c0d080601090608091002040b090108013f0b040602030105090906010b2a030a030903080c0c0307030806060702040903030519051605031003050f0a0b06060a12150503 77
    0xd1014241205100036059007264025042e02c1000d0740c41d14421210540040c41c045010b0201510403481141c10008110465200d0b0704500600c0d821b907082074010124030040411482515a4407828142c0105500c0380e0305071a006600d2080340c4c000002100c2602c0e01d20407000c0d1100510310606082a05d55080422802c0d542002d18240002c5d620a220345441801d642001c18040a00419064102c4032003180c010300e8030842c914101440b5404c0311200c07054044805074032180c110300703100808083d1616500050790751000c0c54003500c2c1c1c40c00070300b05650241c0300703001d803041c00348000040f681c80035090304210a06030f40311740c0003a00700c0c410444025001810500d01608250700758024501400001114034566404801c504084a908540790803004800100b41c4400c140502c0086030420103206440c094a034598480394500041000a844180d008054640501800b80b800940002084404a240000f5408004c0611601200480f09180d442c00b04d1810412142180c90040001034169400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233032419 1250 233031169 233031221
    0x70909060b0f0105090121060f030507081c0e040f02040b071424010905070c1b08010b010e03030304060b21010509010f020301080d0807090e0f04050f030a120b04 71
    0x1e085008841d500903000c110711211158010390581e0390042040c0d41d80914802c046003410b080c40180304800a003a40d0b60307600410918411240d00d4055400391005191007468a00a940b030500d014020304000c951001088803c00c3c0c0c01001c0307464040d01124003040162100142100a100f07c3c3e20140d030804000621408004100d45403455107407501c2d056505822402e40c413891210030740c40f4540c03035a1a01070010b1141845c29800303070350410114078014681500590710111001080c50511029000100c000c1112031800d00a03024907880070310f08810348810900110f60340e80800781000700490b843d018a1002c0d9201c0940f110a1040b0500f500440b541810031070b1402010255210910340d400c00c81c9200a008050086904030f84440b4024000e10b0303c0d1050032102540007421b0041007280001000810b25140e94195010325840b0360071014038203113450035a10b8510321703a215017516041446904d085036000000c41090f80c00f402e502256440c0540005801000f24070030240e0003c804804d2111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233033669 1250 233032419 233032421
    0x50c0d060915020406091e03020603190b060703080f0702010f0609090b010b0f0708030403031b030b1c051c110f0109020a080c09071419120c051e07020307090906 71
    0x601c5500851800025810050715003042e4407582c0134641c041000030030304000e0101c1800301440710b14690140e400d01c441c0c495001a00c0c0360b1003a1825012480220002a0300c1e1105200f511010f40e0100c4000707207041140e0354094504000180f08801300708502000a114030700039002180d0340c4180880405c80d203515030001f0001001881c000382d802401034000031174883c1d40c00085410f01c0705040115400e20320349030b540001030361000b40100c0130940c9404c607030810760011890400e268025510042102807214062040488139111241c10b010380808003207010034004903001c10500a00d01c4030079052040d407002500d0150305122040254440c4515100c0c9013181035100c02412842220b540c4683e030fa86100c001e40e1010007a006643c80000341c00410310050090078005844010403e03c9410b16060820750008901d1010b000740100c1c03021400c0010103c401e01c181c00421120341005410952002c1c185034004c003007040390740b000d52400909981555000c000740c000401410400384002900c03031500348 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233034919 1250 233033669 233033681
    0x6010e1611161e090908070602070807080c012007030e0114090307080c040c020f0303070e21070504050702070f05060a09081e07090b03030a030b06090d140f01180807050c0d06 77
    0x81140f0307503a00b40882c61880310700917041050b40100b642400c00d00c3d203864003402036111840481e4914403c11408001900e5038006d824010600400000c00e60344003061480c1d5408491075100950200f00f10a80002c1d801030710281074900d007231920b00e1011800c0400150240305480242c1c4e42f500c2080710006000c4c1c0002000c2040000c00d403810700400300358500a0381e440d442004582c825400502c00038420500ca80d50303003000940001c040000d50400000007032580d0500c40c0e0900060b0f040044140326a0a05004450f04218548024405145000705070705518100d4014035104603000603030340f0000e0f488dca41103405021408103880c011224402603650320000304c0490f0f021800b44004c000b403c0b000a01c40c5410441c0050051132130022142130440003010365081c1c150b4450ba0500c030381d00f056180c10200002d040c0c0b040e0010004601461840b034a8034041810f1100a41c1c18400c503411038002e05404ca5165039401405213840f942186455420305010241480c0c110b000c8501d58028804160448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233036169 1250 233034919 233034959
    0x30f0f0b030f060408040b09011803030201050f0c0c0a080c1005131403120a05061f0216051002070e10031205071a011a0a03230906010e161116 63
    0x11216040c0c0c2c1c448064551200703d801400d00642880100032900ba900024141548145015103600420b100b2840032020f0310342040d00181e41d1001005201217410368119084038982c1e07095400d0000500c40d055071000c5040c001405242c0c040f5801c0480c05080100c40001c8006403002d018a240942010148034050380041d600d02c0c0e0b90724101d9003074410100c101ca807600740140358031a1981e02c02e030750a40500b1000d05181c0e001054604045007454007071000754450441d99010b0300000c2c7e910030030001c1d81d42980e00410322803d0402c1880d1615900001e1750300840d200c2101e0b0f02100c1e59030400d10a1105010f60003d000c0c0500768041202659120b0001c2c003041c0d115040460805000c04400710710700c1024022602191482002c081c10399484001400080384907141c082003080c0c180c03640682420300b0b0965000c0d107032001401c1c0401a0000d01100d80500b0384848641c2240c50444501001d80501c3c103505010b000c90301035486080642070000320903000c15580c025a42d2a502d220a07a2814515459 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233037419 1250 233036169 233036173
    0x2031f09080d2306062a071e14030a0f0c0e010e0403080916030308090102071a01080106080d0e010806060f190e010c0308180c0a0b0c010f02090d12030f0f0b03 70
    0x350003105002443c0c0e241c000e22016040c00c1c14124807480c4000300751902e442500040b0f0506a00040204041003075101810107029261101e00c020411240c1a045c0e42d00705802a0240c2191b450a60300c00040320032002da00440050f00c0040d450801c604004c0c00e5030440344004440400104411300300d02d8046028510aa403109000d559607815661500e460810401e100112401c04002003072040890341d4100b01190001440c08a1665401501030060350f450784821594100411240c4000c0c45070701e00a01007000a002c011171400001003201e00c1c10b07400d0505011400000c19070b82d4840d401900c20894200c1c012550b1211241d10702c10090b4038400c00c2c10009910448030a21551285102d114041d03490b448401250b201c0d5001e103524201d01d4001e20340c03a4825904159100e030f80e400030751801485c6a0030308507602c000c102d00850940380a00c0e1401d1015004002000706900da50081510007a000904404010b1002000720040d008151010546a04164900205541c06c0e4807a1801c8042202 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233038669 1250 233037419 233037461
    0xc0f110901091a130f020a0201200304051504030e060c06040204110f0d020c010221090d020c0915010c020405190b0f1f090b0d0c020f070302031f09080d 67
    0x42c481c1500c075081112101d4542a41200c1280d041c8610135008000740c010010408900034966542260464143c810042c0c0d161101030160f1404144010000400480034a141d860652561a0707991b0104088070b1000c5000390029051603c51070b0b8481902744000c100c0c569920f4001c7c000d550300e64003510f003a03100d1407400c0020900c0d01c0340c1d03200b251207501d0141d060303505209000013410001d4002ca541c02c1000d54081182414a136a0110840015500700508495504003913103107034608030143c29003005651060a0882c219910101030381e030b0000001d4144e4113980e0414004a6050042d4480290000d040100780401003070000b114070b00048040030100000084101000702481e000b00320990455440650500c4241d000c006100810707072a420107054450740c8200d1103265034002e00e08034025a13a9514400c07000c6a05001d001191801c00300202134280c00c1d0b400007529001d0101413804c030290004950102e80340650419049140c1110102d40c5540c603221050f0043e148042d420510303950300c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233039919 1250 233038669 233038679
    0xb0a02010e0a0c061206031407080d0215162601080c04140a09020a030b040506070807360801020408030a0f09180504020406080a14010507111209010c0f110901 70
    0x1200019103030031a1280410790301d8404c05441c202c54110314481a43c1d2120000300126207402c2980d0755100f103400042c032403a4940003e10303052041a030080e10464012800900701940510107076904084051803000c2c1d83c0c60400e405442015220710030b403c05a8000800b0310725030440e0b06406040b0307080902a0382d41d2402040400c0100c495000b8100f030301000180105003412030a030303c00c850f507074400303002552030f25141c0d100c100c502402100c0031521a40240c0401504540c4922015040711060504c00d8000610084228010a1940070008d0040c401c645e60741d1440c069100d20001480718400855949840e00141a00c950006000c2e101090807603560b00642031041415200319243c00c0e1544152040504010303000c1d01c0081c00c166480742e150000402d48490500002010314402d2030b41510b05481010401d00b5544000c02e0003082c000d00915020130080081200e0800c091205110b5541e02c0b0f6150068403403406540c006030a40302c4c0701007150200440c074001110b5240c0e0844200720681c1c0d0361 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233041169 1250 233039919 233039923
    0x6091f0908030f1b070b030c0d0b09010825051507060c0806061e0405220e011803080a060f03080c010f020f07031214190b03060709030b091203010b0a02010e 69
    0x15040150083d442040101c581005204100030404140e10940e5886642c2d00100d0f0440e03003003500d42c0380304244000f5040d8400f0100d44203583e03006a0a80b04100b007076140010445d11003050000110b060b00c040d006d9452900400401c64002e44002850060904010701c14a0400c4e0803400b4100c50142ca0001160035180c000d600d801c1c8546c80007408180f920004c54000820389071480180b60740c40c3d80500000c5440d690b90480740c0c2c206030b4880c00352215503580f150b004090310307016080c2c440d090b407424444145030000c4804d10105190141001f24540d100d6080600c001e00700c41d44104502c6481203008010001e542e401080346219540090006071881c4040d0300032482000706040c00075000700403c00010b40210241d48145844440c0016505c5803040c1215500004a950800000015051021040c0580700716440200150020103c0e86000c0d140a080c00050f804050902c500ca07d00064118a080103c01180320010390225100d503550310724030040b5000800c4010265003040b4004201e030b080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233042419 1250 233041169 233041177
    0x2103130801050a0b0d0f03031b030c0201180803150a0504050112050f0706020616051e190503060f061c02191409131a0406081c050403050303070e06091f090803 70
    0x14200f0b800303013000c2e5860310301c506c4241c1030842c00e1540341c038034103000c0303d1070381c240301203180780503140480c5210090704001d0854602e011075075a400740181f030300c9010030a2041940c0c1c0c000030415589946107075400c000f4000703c11030342c001130b4001e00b4800080350325608444030000d1907100340c0850307000000728400a07446a00b030303029050040e809100040d0082025500c2d80d4492035003400d015207131444250542034100e50f45080f00089040c0003c0c0d85603003d038001002c3e2907002a600c2c0103411418202c000920300182140020b102c0e0700302190346290040340001c1c0382c1c12b0520503a821583d6465124882c8103640401000c500441c99001e941401040c82030102c60008200804407403068150028100c01084078819580410b100170301c489101e5103c91051002138901040240403070700609448131490b0004401c40c80c1000414001040002c10003c20340341c00c0102ca080c80400701101340c000c201140100740c51103900841440b0512440901180c190b04c0d441181d5403080748030b03074645005558a1207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233043669 1250 233042419 233042441
    0x3040303031b120209040e0114040c2709030302190801050a0504020301030305070f03020c030d1e0306050d08160b0103060212010812041a0d1401140f0904022103130801050a 76
    0x81001040700b0003c200e640245220903004100140100c074820f6071508440c0207070011103a10111006010070b04c0040000000209940000d5282210841d5107416040c42100c40c15030080ea1103404860402d03009070113a0f4089440740d40000d40f00d41488a00a0400c1c900b84202c3d0300850b0345940104050a090080b03078180d90301a02d40c9403900c10580e442001c40f0301c00c2c520a070218060102140780c2c5035014050b888041001d59a4080d03081d20352a10b2000c11601c00a03000181480c140c4100001d0701d4000c80c0f100e0300d45d00301c1c01654a0301088203805e201f08540000c0101140781d9440044200895a8060261080300520b04805030303032560140e40c0d5850b070030300a0491503d402c3c80100300c2003040ca40d018008080100e6140d0400c2c4c00c580741007040d82d040c00030b038481035002e440c01403203e070020304a00300403c1800c803240030074904541c010803a03440020308080c0c0912564040c4804800e00d1482c000c02ca0500c11088a40e110840481d03038040e60741707034068070640d0750800c1c0118844068500035441c0e100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233044919 1250 233043669 233043677
    0x14031303030906082e0f09020d050a050105010c022b060f150e060f1503040c0e07052703031605071a1806030402030a050a030f080f100b09010203090301050903040303031b 75
    0x1080900100b80307096050a05043d6940e4005d8010400c10111420b010041c5103403000540c9410384a5038602c01d444004000503441d07481d000040000360392042c00104c03001d40541ea92174100c041ca880005100c802a822480b0030f0300b01c1c1035180100311042d40a4014810481da003041a0300c0e42c480c250301d410b0754034410902401590404078035280303031007140720b403591300f0050454940c00104094413995420883d0290742d619039071441040b841860300402a8009402d252452030720300044000401c48038908001c581c0e80c641c044c0018640d03181041281e441102c00d0045052100091500d2035a85107503024085010048015881462003010f0a668a0042e04880c0b2505000700300103104550700010420383e418401d14107240e01044043c04009c140302c1c029900d5006865100c100078224800203400d00210136030340410403022204810b80c0d541541c03080f6038030070b58801141004034a58003030164031031707415440d000611401140003c010012603210340c50902204030b0308030190b11000741c030060901c081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233046169 1250 233044919 233044951
    0xc03111e03100209010c0213020304060b0a0b1c1d0105070912030c080304170d050702210702041508010c021b2b1509050a1401021908041403130303090608 68
    0x42403d030040d08940d81c041c9407814a00c8070580010742248403c0c2c4001050aa0003c14030040c130074a4083c000032440c05071405070001c0d00d0010805c60394440c0c04505d0103021004c1c01c001d48140f10940049a43d280c00541001065003106111802010203543c1c08001c00c014510014494036407046803184660503440e960700725101c645480e0b60541c0014400c0740c080028404044500c5500400b030617104000480002e403d1401540291820f40b004002d03005c1d0341d5603112034144000c1008200c804403a410750300030840c204650030341e8011450355003224400354204600142c805a000070f85403c403070ba028030700c045d8550454003800b540601c220320300207805901e0182078003403000191441840c039220305031010b41c3c0702e552010b101c11078400034001c5030325400c100c050b1400c0c401a2000f10602100c4003000314600900000740401c1300c0d07034400c014028031881d040081d003071000d42c120903580411003900343d071b80c0d80c013100344000d40c40c0600307000460204101c80c2005c6542032042c54120700c20f4143c454880b143d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233047419 1250 233046169 233046193
    0x5401230050c0a0b1f090e15101a1b0712260d240e041209080102070c03060b12030d0b030c10031d010e030315040f0603030206101409010302010305070c0c03111e03 72
    0x40040700420000d003c44a8030000a1181d210500342401c40300104080380d03c3d5500f03900d5405252f40350442e06403645e480124248650441050b0401130264008000c203106407458114803010031060035507204220000c2207094240f049600a103080c042216021035001d818007130703c1c07072600c20980984a503000403c0000750000d1090601c0074a22001828a08482a0b5400d81d050990740513000c01c0b01c071080607820400400c5503078000c1c3d024003034040b59101038100300c1ca401241c1d00d0140da110481c00c80e40740e5041d81140c0c2c601344070440948a0242040c1e40000344480041c3c007910400c0c180e40f900219030f9030891058a0180f041c0508105020055403a43d25020710503054506100c0c200c0303903c543d440807081c0aa9007540715401c01584280c018004500d046801030144030816800700c54083c032106056102540c40c0b1003e581075941c24280015646c50382c0e001144d55101d074480040c05c042141c0303004403d0040f03061505084a800301c48455913248100498910041c90030084d5406030710401c0784c508 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233048669 1250 233047419 233047453
    0x1061406030402030717011a0103020a02120a031409030712052d0c010213080c0109030b0a0507030204080f0f010c05401230050c0a0b1f090e 62
    0x50424001002c5826840d1541164030b001b0180006401d1544c0d541c1e428040d0000381e4004a034500703e401d00b411400c25040070300c0651103212030b00c51025030100c0080e5842e0714074060750102d076907550f003007013a11114a0941d1a595503544903220955891700f90203103124180b403103072086038440080a400d51143c0c1d0580395104850040e018423290b2964814440f646258a0034405030003000b0007010940549840e0402c1c03c0d0900c690b110074141040115102840811110030300a90085a409000503c1d6566680101c00a0159800c0b0b0307107260255000c0d00342001d800140300e110399a42103008000456400d078098070144078a50714203241c40103003681c60340c2080301002c0700381c8980561416a10703017889070100454209076075000102c14241e200380e01c1040c01141480c0100c49110551042c8080d007440103460301002c4051000c1003000320005000c4c096000a03c51669110740c80048802542400c040c0c40c03070903441c03140031291102a200400102d412240c040d0204110442c00030304400160442c0e148 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233049919 1250 233048669 233048671
    0x10902070305120c07210807091514040305070e090c06180d060f061d010b0705031b0f01020f030403120501060504121e08070c08010204140607060f0510080f0106140603 74
    0x84002c6020b02c00c07a0049030a40c405940c480303507117243c1c14400c030b561b800d0040c0503148003030b125208109180105010408840522200203105414900390501d00b4155002c06441a500010090b008180d00015642c2591501c0d0780501c51203c08e41d09000c0c0403206000d1180104070402c10407058110780d4086500f80308a6803003a16004500c0070510040064804080e205198003a208054822243c10b02840040495030301401c420414980f1b0801d180c0c6500d540e900908680151940c030641e0f05211940c0c00300000c00002203154020354980702c451501d80365035081281e060340031030b036003000c5409503900500c01c02e030580b022510f5a50400341826035004044500c52800c6400e000003401c00f500351044110901480c61048021a13135400c0780380b40900114486030b004101e9030380113210034401c840c8407500c41d88401d1002c0e00c2c503079100c1d01c4904004028260b442008000e2528103414407140c0c030020442041605d0722941107072890034140380301d2401c03140207225010b03115003084007800d51440c01900079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233051169 1250 233049919 233049931
    0x50709050d03121103150904111908070303080a06120209010e150406080a050c0901060f050a03020f0c0106140303070c09230705070203010f05010e06090a021e07060501090207030512 80
    0x9500900f0140c1100c808441e9074407070035407590710080200080d40050782c41415441e181030301d503000f080c02c1a94030782c0110240059100e105501c1120b0721280000d03c0c01021004211000c01c40301140d59a04018090300b01c280c80d840002c50600f000481d500d10000860503c0941c042c00f200760326842c000e01d01c0c1442501911409003d98181c2700050395503951300428002d44070b803130301030904c2940910f040c1d403421403906401c0d070092052900402c80321340c100c809040e1580e6a4140350f9540d0b0700c0305c1d03402c400920907071030b00c02107151010540d0030180303034158000800c2da01c50001c00c54043c0741580416941c0c0c0680e00c0c000f800c0c2c0050101c24803450255401a0700751410310b41c100c0c24107907800e80320040d2403c0100d80c02000640049010402c4d4a402d0280101603441c03000c0420055042540807840f0743e100030700003801744240b0b2010403540041d0764100e03100580c0a48188100402001c03c0f020140c2c045882039403001d04000010402d03640302d108030348070716a0680300c580c6000c0201c840c83d01000001019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233052419 1250 233051169 233051177
    0x6150403120f110102070c140411070303020a02010b04090b0417040b04051908010c02060a051005010806010c021f090611013c0218130c0f03021b1903080a050709050d03 74
    0x71603c01c1c0c1c03070240050700607144944c040c80801c504003980d038401281038043ea24443e0b070502c5845610171030460112075034140c040c80c003d40da8002e07468090b0302410008444d00c0d0814a0314007041d0902503109a068040da20840302c1600065500d0011a103501840c0220981180100000c00007031070310a200c00c54501038541040c0d1341d540c0d110041da0850324072056400260700218100480f5014600c80c550744000c2c4107100ca0026410140000e182440007080319040c0900c0c540e4450075580d8403c450b6400d011200c4c41100e241c1e808160060036040248200d401003200005d10345c90110042c05006401c0303001c01ca207903100c1680800d2640c2d4404900c640c0c0c80021805158600d00c0e044a07000902c1541c03070703d012415020300c240c0f06011039210181020007450389408214414070380d02950007a83c503401443c0c051389030000318509200d20010303d40031104c58890198071a8a1006210803002450300030788901c54241d0341c4612250a0718402c40300e80001401494003030195141201204002d02d000f0301e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233053669 1250 233052419 233052437
    0x4050c040501030b0f0a0303020304061e0e09130c06020c0f0f030604110d0803010b032424090306041b0812030402010804060b06030916060e0603060607110d03030506150403120f 78
    0x4600c0b4141b05400960041c0c100103014004150020072601409100e071480507460700e204a8020b1280342040a1580704a886134003041002048549c180803460300030785c812005039900c002c060f41e00d1400c00c504c1402050110769040091070003400164013000c01030094100d581e45c40d07071210f10702e61320301b903180380d0020500d0b003143d01158030350000c1d6018251388107180d0b980781000300205017480300544400040c3c001030440c01d4076945400c040b0040d44c1a01c090031107260000c2e903111403510301640c03900541621800c002c1100f403150240a000c0f41a004071151004140c813051070a840756810200c00d40002c004102180055202e007002540c01809a00c0001d803504102c4001196a07206890700c581503404141c80040e420700b5210114001c0c213241c00c00003803548010011230041d0000500781882040c005c5211001d00c41c2640006070000ca004010400980c01442d025004006c00d8509501404400d800c05804d030412170125020741e40c000d0101c0c0540341080034101c0e40381c80040701003c10062504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233054919 1250 233053669 233053699
    0x1110913090611031006021203041a07110a03050706060e09070303110705040509030903010c050a0c030e150f13080109030e04020c0109080c1b0301060f0b0703051c0c080604050c040501030b 83
    0xf038055400360002c0e201a44d1818035010000380b5054412800e140c50311010401e000000303203032280b241c1c507a0140d9104a10309a0300e00005170384084100300e0592207402070482d260205940640200046403140b041000059180c8154102c400d034101c0b480a10f40e4040941440030038042e14140c20000c07450011100382a803150003140c2a240140d8075407a20350710205464100e0310b028002e03403501a60320301d0000e0030070000200041811051070030113000d0245000c190701070350311001070005c110080c0382c01680d0b03200703c8a0340031f54899001926a1052524078400800c1100060056076800341e01a035403046158400d20800000b50b00c0703000d8548003990f030f07141908001042d00340074003c1c0c1c00030080903190707107028165010403069503200c03150b1183c1d140c540b040c02107402d2601000300b51654101040c1d2103560a10b8207861390701c00e1003007100c0c42c00e00b05030b0f840744614401d401610080c00700d5a6032600a848130403e00c0291001507a0303010035144140000d1006500c6503000d8040160020102e01e01e50f801c80d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233056169 1250 233054919 233054951
    0xa0216080f040807181a0f01050c030c0d11070e0405030a0318050f03030601030c0e0d060c11160303030f020a0e090901061a13050303070b040b060109030204020c07050102011109130906 81
    0xb5900032181c14411117280294108a40700d41d460000d049904100103884040014000076000c00e10541406000304050092050410980350500007490446100c402c00b1140681520415050300b889403145174408981c1d9006400d56501413903001008500780010701c601035028001640421044200503030b40790000c40c4041002d6207100e40d00d1005541d49051107000101a05c1744a00c0c1d1000380046001030760700c3c03a181c0c0100e86000e540c100100043e08020010304450504d003041100e504c5200305200c01d800c441142ca114021244a900e08201c0c4100d4034070301e04143d018251b114000320f010714001704070505000c03c4403540000540000280f040c4c44080c86d00e403607a080c2d22541d0540d100030801004221464912001400e0210021400e040d00d0f0351340d4009544000308002d08040c103110114136643d01500f40b420143d5402407044d03441d201c84001c02950f50156103e42c0c1d0040d0b0906212021024203d421513110050181c040f110303011400c07038400c01030035405904071052035071100b2154a40040b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233057419 1250 233056169 233056183
    0x140607061a0111120702090405010b090103050c010306170a02010f050c12120105010305010e0a18021305271209061e03010e0f07080610140a11060a0216080f0408 71
    0x1d442202050000e40340700040c03102490700111209907108120340302c1ca81d01e0400607034050a90480d0184115510362800030301410f244c0d01100e811030084000841080404649441e01003401c1e0b80804c04195200c0000c0c00c0c02c10b4000c08880f690f0008135016000d5449644144440000c0741009171424032600c102915040c1800280045400007084c9808003c0519103410b005200918080c801541004940c061400002e440700048581c0c030341c400819421011a88032001d6002030565001005031011440548401c440b14803603545041c0000c1d4400c00306d0300070994055140c40c018860000d4a5201182551103010480e51148062084010140944000b45207107519000301a440354074102341000c01940140085044016903000c00c0800c603840401e040c0d01c1101211482510043d10300155011300c0040c081e000400400200c03100c04a1f0014218520501d80300111002039072440702e420200e014020700d840e4034881400c10354000c100300f41c001e020380d040000c0c1e90b94034140d95804402e140c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233058669 1250 233057419 233057441
    0x10605092e020c0603010807061214010603050906160915050c0303180609030703050706020f0c01050c04140102160b03180703030c1e02090a02030a0213120b01061103030114060706 79
    0x1c001109000600d80c14040c0c10040700d015180340d402c42d4104410152184c10390300515081011031149940c4007055500178011100080001c9802542c580500401600c8110b0703623115144610713804030340420445006580300b8032480e41c550344501c4c100544028a8107025030b09101300300d0b0901ca074200c40b402c1440103501425070b151369154002d20f5982801d0518500810700788840e04140101d801082d0003401b00ca410355031013003006a0703500d040d40f030072500c6000d03104020b81550700e460100035274200c03140b00a1080d03807440074007444c801003100d0049a5034a20b440f030701086000f29031010000380c0f86c3c3c0030103550071000007403418800f400b440305658030b4034113a540107600103114241302a00340041284c3c144c80d12881d184080d00390130f90f0b503008512091000717401c0100b40e55000000504c800b00d242d050321001e0f11074040c500da40da5602c00740038001c110340220940d103110800000042c00360040200031150380d00040603605503840c01d1003034400c0c11503403040c158021030100030405c0020a1845182640c1e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233059919 1250 233058669 233058739
    0x8012306030c090a20300a020a121d0f0102040605190c050604080d06140d030c17180a090203190903090b0c0f011d070306090c0305012306010c020901060509 69
    0x7942032486089503170581038000340380c81c611b94071000702c6e00001c0c0c01c16400407001d01c0240e901c01412104461000450840200f01031501d81031140c861b0304041164034450b000c40880c0c00ea048848a01c0f0f0803032081780b10341030225000b01301c54140202154030701418500d00c2d062100c601021a01c1c3d0a06051045508807910713040000c41c01c5601445c9c0c45048094481ca1281d000e0b0410024042000d000c200c242c003909008c8000a04820460383c02044a140d91000f02c1098482075088030003441d8100281c0702c14031031000d002001c80d09801920a817448ac6181403540c10318002e100c1c8190b0000d00c0c2d03101041d020450190004900e1303038581d10003000303840d540f40000c1c2946201d0b051518210f80726056818540c01c0604200d4110303400000c0d01d01e040e26042040041e1104151910443d403545551004000394241000d45650b4091542210300f0022650366030740f541e03030340c01d0300440e22440f1062000754800321002c01404428803c03400b50180c0800030741144503166010022040c3c81041da40029992 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233061169 1250 233059919 233059927
    0x100218090604090c152c0910050307080307050f0c0616060609110a111203070e01021c02060402010207120803010b0703020f070906080d0305100e0606040308030108012306030c090a20 80
    0x40c2d4000c2000b400001b001142c26050601c100543c0482d15810200c13620605015000c81e02c88004001060000c040003011244035507600c1185507280d4000c00015034039409034090704000341310080b0340d00209002c000d000c0c1e840c10340d0f100b605500c6010780d92010769007644e40795004500b10311b00f8450003c000c902014030a842c3e801001c002000450410915105030704004580701034501c510342900d070014101e00f4030700c0e0100e1000380100e28140c0f01c400c044c0904ca084114295100d500804c2030342c0194000c1c0e0a40e11802d460301100c0204c030140170b900424013201000104032001001014003102c80c031a1055624a074040d0010901c0c1c0181c0750001c000040c2c0d2001d04005003c010001d0114240c5681000d01035880d090301ea045100501c4d10900e10302500060015100b507035840100c1c0c000d564042c01c10381e10395840d80000c50003411003103040340140740c00c003020052100848800920a400003070003080506204404d0001c1c03000d016009640558465015a080e80351102500d49410340f000c41064039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233062419 1250 233061169 233061209
    0x110708030304210e0306040209072d0801210b06010905060309010608390303070b04030e030105060604050d1b0527060a031a040203210a02100218090604090c 69
    0x10b16083d081c1d0107001d10141d050120f059460208083c0c1d03200d50102c6041d1a00d903201e2206850104100440405c0c82c07900301058035111408500c0700ca4000da80e43c2e6000303410f07030300c0750004803255010814881d99007034140e212000107488089074540c00041171511151300c82d07640d400305010790000c1d45d0500051f5120380b828040408204014200c41c1c194241060700002c03d9203403501c8415146120071039501c20854100d119403401c0040341c0c0519400060810b07540b5040c00c00400c44400c4225141c032a5003007501082d0303103103003080a480a0b60302c014454501d544e00340c2c0e100c00e00d11011b001a942042102180011103582d883c0301e02d5040c03000e125049400c802c000d0200804c5200c0148418402c401564040c0085050202a1407455500c025601c11946650000a10f13000c014501c0c0c83c0e440007220710581141c181c9202a010100207078085501454000003160260b00038640b44a03101014140540c480d4503007130341500e4210002601c00104101c1079110051003500c1ca800860407000c08484005c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233063669 1250 233062419 233062463
    0x60206180114090309031011090909010b060705061b04180b120304060c050114010b090d0609020d0c05010f08040510020f040503060a050105090a0b0901060309051006080d020f1606110708030304 85
    0x651a041070010065814208d902032414000c0000c920b000702841c10010700385c88401d43c000c1030244001410207449a030185002c0b83e84d240c048416420392480791242c101144107420039501a50304041070307402c0c0301c00840300140c020b201c0206016449400c820b00b01e405188144001c1001c0c00c0c031985c58400e106642d05100d401d580e500e030044a200c110210041125810380c400790742c50b500781129450707048a41030a00902030f04c0f171818040d6200c01005101000c000c10000d010048030700c2070300d1f01c80078450030410549114104640280940d00090204200392846900501c1114032125640e4141512400030910744041213a000c2042170303a0782c005004a161550300e140c2d1210329070f031041c17040c034503482c0102e0000c4c001881440149030721201810200001440014501d1044042c01c0152580e0390240c01e84e11b5001103008800350142c5924001c410001150041c00f40c0703183c20703244800ea45000b030110366203969441c000b50071303000d04407006c10140000d000031402240107105030303107000b418001154 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233064919 1250 233063669 233063683
    0xf0801060e0408070803060310060801050103030305010501020109050a06050702071e1a0a021f0b090406091205090d02060a050403080c1b0904121d0307030b090d0906020618011409030903 82
    0x750005030210420000408800440d0f15807a440700c8030a803283c450601180c9040d0300c3c0401c2d85801030426501080803101544054103d81c06a601400b099076141c004ae400c89140e20005000b64010a411070081039458100070380094191045840141c0c0d154003007030869428083d442c07010500410208492108c0307809132043c503510b007181a45846a000e4000c0c0da070f86240020010301045120189003c84200c1c0d0040040301c801801c003511302d1410780383c0b41e801440c41c0d0740126400380c5c007440d19001c1c0364860001e461918001610041d1800300940130031140d500920024000c110b8200404400105504007510703c040a55004005078032008503400719a0141413440d60240c84132030704100208036103500014040d0700c20708048004120360a040107201d5011340391950540700342c2030000b0401500d0181036204082030001c1c0da0000300000c0c0200c0705022544110380c0117901103004250f20000b0342d0b5603032a401c10070b14000180105080740b050751890003100c414166406c0441e1000290605004070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233066169 1250 233064919 233064929
    0x8040f11060d0e06012408070201020f07050f0709110f0f2505071a03010b340b06030303061011010605031b100806130905010209040f0203060a060206090c01270f080106 74
    0x1e40d104030700c01004c400581b42c002040c40d0400c00e0000100322a10300079412181c0e040d508100b1036070707030b41c0060802950b0745c00411103038027a40c840c11304000b492007a01d00c0b40400c01000091014501851618070007040c0c0c0006d403184016400c10091014045041d5110f15002402e00c44001048c014a09006040060a5114200d0280c80f800c0f00100001d5441c1141c0c1910103400301651160441c900710201c0c40311034050000034074042d01c44a4900c4190200f5103030418480d08511029a603040149031700c90000b40c44058100c40800702110b299030080080714000f40b9481e00000721207541760002454140c651705032158400d420900315a50b0301340711801c020145a1030170003ea032802c1600228400180001a40000a41d01c00e22101085001c0d0121600d0050040080c0400401c11407600000d44c07041c1d4005104164840c4000352880c0089170307462240e2482c0300035102100d4090f0040d541d84455030780d124500c20241e0001043c82c09801d5544025060388012000781c182081c0302d042c02c644882d007003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233067419 1250 233066169 233066189
    0x130b03060705090916120608060a0609090515071101060b09130209010c120309080d050901150b0409090f02030318030f1b0402070302010227040b040c08040f11060d0e0601 75
    0x180d60700c1511103245003034210a081c2c50517840342d0b200740401c4840324006050b100a56080500004051000040060180751030356001c01030380da41c2d910342c20704452030007600802d142c110a15802c4510620241160b2080c1107040030700a09007001100350865074a43c219204000010901401d94242519240c2200410b02d05c110f1504d44081d002030710914212034010042c49421101c848a6407080d04569842a44110166211070302046500e003c2d050486800c0107a42c6003003510b61131018a02c00d0201140c12824820303107001d080c07043c1c074000740c4011102500d00051031113400c40161010402450040c411680d0600014952000c2504100f105505001550300842210301e900c0054907601c4c0361131104a9006030358040918040c0c1c00b90080c1c01c000600c4201c000a10610444002c01d6550b00740c4040300c08110400008082000b15580500307480001088140003900080a03034020141060180212034403d40300c00700001d420740c0c01801c2c02c1d05c6c40354860f9440c464085041202074094488014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233068669 1250 233067419 233067427
    0xa0c0806030c1521010e0a06150c050304050d031817030f03181606022103150a0f060302040305010e0c030c010f03090c12050c011e0309030905130b03060705 69
    0x80002c0d562603110030b00c00d100c0c14000c0c0307440b0b03403010300101100c0c0100c90360510f00800200c40342001352044805d10078a40a04071101c0002d6066160b40f10f4081560090303201c400400588280880e111309020f075084415120030000803555a84a220040e0713030364800ea0742c1154000e4181040c0f80002520f522584200841c418186020107004c002c4d603c5021050381d259440b940d42c0044040f407140074040c0308010b4012442010011100d00b0504410f80d850f039000c4504281c805134104042d40b254245200b5440b6050011469103040c01c281852094030051005481940700c5818040c01c600726803020340400d5000408004001003070003490000d15015029208400d100c50101c0d49070b904007100e00d8104189018031062082c0240c4c09070700743c943c01c068040700b0071352221079030303101c440c20340c0c0081e28203114034030003281c03e50b100b078a644020b80c43c0001030000c40e02c1c0c01c6c1001d03000341240d070001314240010f02c0400b2503561520f0810014082c51181c0219200005400349400c0c680e010302000d08100c0100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233069919 1250 233068669 233068681
    0x103210f050d021303230d080609150420181509010507020a15180e13030807030b12010c0f0c081c060816080c01110709021b070803030a0c08 62
    0x901915400b4004400159845000001c0030264091680000340341c1001403032242c0c19101c40d01880d07841034801808039007030680d0942040c1d4035440110b940c60743c0901510001580c2920708582c109003c5005071000c188000c03443c00303034580101c40344c1c0218500f442c003041621684070984d918400c241d0083d80c019040d0910351012900612541000b07905200c0001502011901d500386000000e201448004480c1c1e416030310000c0c44c041152080400071342008002140f03030324640503004e00404004004008030005507806568800006003c2c01c04d06a40b0400600d054941d2007000c07581e05010b50000035000700e00113018003c1c2c880303074540c0000c000004000c000002c074254125203204242409100030a0982c03003503003028016a0304190360502401c05001c483c40e003100c811f00c0a4400c09400d4480400d000ca0046a17030001c1240d1081c1158880d2404100444895008120500304a48680032760190005c4451400f41242d01c0110154030010400c240020035100300308820b451458680228140300c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233071169 1250 233069919 233069927
    0x40606080f06030c220b0405090c0d0305041d0604110f071419030302030a05060906062205120307050c03010b0a052205090d0801080307080a1d0402030103210f 70
    0xa0014045141d2440800e0301c80c3e404228007401c11400400010070102e005144080128036103070a050040d050a6040001c0d10b018020740380300d14070b001c0003000444018000c00444050707041e41a002d0103003c10001c03e82a401d01509006d002817074004042c1030619809020454140040840c050081800141c05c201c4800c400c13a000150401e44866150711480300450031301a0f0707901c0c0b901074801d000b00c0002c2010381503000b55100385441141002580c0da0341040c098207210489803550300c03c40402c1112140c131040d03007103108140300220301c0e072a400d51a080440c5060500c5003e81017294000300b500740402c00100245000c11505070001d0084460000110304030309190301619101d02c000c212a040c0c44c8070441c610010f45040007506201504014a1140e110b5045054000c00641e0440c004194090000f0072180899486030505103451405142101c10340c0d02070b80400031400451201c3c001950390350014602950040e00e1455a0349009200c24603404008041c0700b00b8400307914540c004032508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233072419 1250 233071169 233071171
    0xf0702150403091d04050d020c01200114010303020c330d0209040f0c0f050f030a0914100b0f100c030305060d080c030301050913052125050c04060608 66
    0x12100000115865518080e1444102c0f80c12651540c038018036031001060f14040e605010754014000d554800000759008c90f10740c0b9504544a0101d241825280c40c1c001c8208484e240300c2d41d0640c0001006100388543d08068034080e482a40181e003d58030010307081c03411281c21001c0308030f6101c65501501e43c904100c0c00c01c030748001e0140d0305c0790b002041c00414a200c0303804030750302000010020810b9170590380d41840202101c4280400090b150881040400e005600701c95103140e051002d00d065950b00e1400c1c4014103083d4108640a081003045085402d50401460700500c1c601040402c00c220100207000724605400002c0b40719103412850352130300b0340d040f61400c0505905440d01065642c0d8103000300346008101007004140c003500003030400750010b000c4040c41c103860081f80c41c05815199401d00142088031136170058065084250f40c003011000718071090058544171240c050802000481ca0503450002c28100d00321041c00725a2502048024484003030340c4041150104030710b80c02d0160040c041c0034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233073669 1250 233072419 233072443
    0x3061302010e010309050f0703120201060e04080903030702031002071208040f230a230601030c12030c080403080a020709290a0503071502210d020706060302090a020408060f0702 78
    0x440c86984940307039200e601702d103004076004011214241d502080580d611803440c403003a644041c0d0340c41021201c51040c0648401c03602602d0030351449840f240c54125096005520242d4103100801000005803001d100e5401c0c4040040340050300c85031306042400d84100c03080c0814040040c08802c100000b45201c008000c05500440d4050140c1c044800e1111100b01d5500d0035016440307500b205408110744960b9080201070380000701b418850380c400340d041e5900300a000050000c4010f06040c0074004030540300400c80340c002d2505048500c0c16440b10580f940c01074105449000c00000c2044a150301004888001c00d454403040060760100c0040c44c0c0401d8940f00c6040d684e058185203c001540d84428840c05804006d040d2402c0075071b10b500703618840f100104500058081c0d0080d1048030400e01c80032481000c1e0180103180352101003045030000350301c440403c550f030300e0361010088050b0b1591700ea00d5100e03223003502d0010b07a07039030505c080c40d03242c0f9030700800302c0080300b0f045801c100a207540400e4043e0b04107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233074919 1250 233073669 233073677
    0x10050619110a0c1403190f1b090f091a01060801120201030f02130f1d0f06130908030907120206040302040b0126060109060c120f03090c080307110306130201 69
    0x100014140c40c1045001c0c42e019000c10400c240208810901c25008040504124100e8004840f4000041c0c0c04500200c0c02a00d5011400e0b1860007043c032140000c0407010045c1c055290154649210608982c1c00c0100000d89980d91101030040101e4000c03030404803544560742c0d01c1c103585000300081c80b49005020701036030102c1ca28107080459000381c01c050010f008007a02551903140e04402614110340d1071080c0c00d640706901c08000b90f02c00c0c00c040020310754065900d0840c1c00d03594502014100e54405044550040c00020010203020914461a20000d00c00d400d03140d034038101001c04618002c85900b040c45c1601c0040e1003180169124400c5508880d41a10003084a00da80d8005a44000002d001c804000310303003002121400ca02c4419051048400362100d1402549400341190714000194005005100004000d05000d00a00c1002c01d0000580fa0101d9110050b907600600c20740030394040d1920741d0000c42c030f11b0200004000c00d15902d00c0c4c154014001440c01020301180d00003101c5000e8140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233076169 1250 233074919 233074937
    0x603120a0507050601030605160903050a26030702150c0c1509030f0415030f11070201030b030705040906060806060103090c0614041205030306010f081003023610050619 74
    0xc0d0050702516961504a02030f2000b40d030b964101807015100c01c85044889502003240803421a000303400c910181d0b50004000e2642020b95990341565070b085800d404000d0072000d60340e45000c000440154403070145a8013508080c280f542020070400405445600608004d20048142401c0010225000e0f41c924215584644605000500b54480d0102d991003014000802280032030803000009a04041541d0811090854501d0a0b0444100d0036542211103000c004590141d84203070004120341d40000c06603620550342c1c40c0003900715250754004846050f100d841c04c001807036003402540c0d0322950a003000c1c450811603035115002d40c50207018030001e000c3c144041d00d81005c441002e80d07003d080200301c440c00f03000c0da03424103036600e800480d03038140003900806090306003030300c01c00c07405019060541d5020b0788a030641e400c1241d00000c00310141642144c050101110041d604008a1000040c0c1c00030b841505060480d00040003d50300715500802040185520b00142011040f407505440e02c1c080d050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233077419 1250 233076169 233076187
    0xd020309010518090403091503060b03041103010f020d24050a0303120219050333010309051014090601082103150909010c1206080d050a1107080606090a0203060312 72
    0x85541d4010200360800001e000300001c051f0000c91750b81c01e4170350090341c20f000c3d480c4801003281a1103050054038101a418004100001c05804420502c2c650040021400021410f42c240407a08411070f9281465260050702003640054006116001d640364004441c02d03040c440841e01403401c3e0311004080100c00f0b10509000d01d1607905542c030300d40c1301e00e43c90306d4641040032000307019800680d118104d0200d000c0324007607444e600c00500c0c10958810b44014150990400040d0b00500380004d0071703143e038003d2842e0319294017840d00c10140600d4041a240d240c03800d090b0425460720805070025900f5901007020703801071003001009840041c030558609581c903901c130844810341c00c00c0d4400007500144c00100748504020103400c0040c00c041036540e0442c031004c41100c4207094230f40510640f5901e030002680c3c070903c58407490003000451001d051902030342660101a1b031911074a0341c03084400b0780022040c001c1900c1e11140d4150070100b070800031340c00d60a107040062349424603020000402c50000400e108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233078669 1250 233077419 233077447
    0x405090403080402152101051c0201030c02030f0c0115080a05210d1d010f061206020d0e12091c0506060d0c090e0609010e070308041a0403020907020d110d0203090105 73
    0x20311620103003405074485991b80d00c0303043c1c142d68148554444900c2d0301d0002c551414110031550203080c3e04405e058102c15507800640c001c2003206080800c42c0000c0051a8091548200622030f84001e40000226024410810000b1303815680100301c1c1c0d60404400403000c25000a03030710348820110394038214104d1051444100903c248483c03d1034a90404a078921803080702c4040304400d0a60a0091095003880b8200300700301e0340940601c46030982800c10440c040782542c0d001e002504016940002d8100a4541892501204120101441c080000e1115140c00c0648003034500e141d401d41c01c0801404907680da5901d440c0001e08090250f9908640e15041c40300da80b040500820b10270900f004400400d00c00320b600c42c8002c8628440640c200100102120000282079044036080b000003030030181000b201c510010258080f00c10401c505100100140e42c1d1802124000d80c0c803a00200200c0300a9880603000010910210026401036250071040c00d03004011188035030401d00c1e000b66141183c1b03e03031072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233079919 1250 233078669 233078689
    0x901020a0b0403080a060501050a0f0e0d0501090f1208010510030c14030a09051204081e0f070f0501170106090b0d0608010c050307120c0c02060a0e040c05031503030405090403080402 80
    0x504410900c01c00c0c0020f043c1c0154910b070080800c80c00501134151a0b1005460701c0c0709000300305001504890511101e00d00c2116400000340c4c000742240c008290b00d4890b1800e440c0d00c40020380c3c1d24003102940d50100304c2854640b1040c00c00074100b001a0b98034000c00a261800190b56000901d6190400b00c441140310303629840c4c551040c9282c1035200c0c10032407450030040c81c3c0800308803190310078401a4440c030381008050b28200c8041c00000d00d004002c40040340c1041101041004441c0308400c0c0168000e0390a01c503050140c103800030314084c01d524003000100810b01240303248000501b81d00041c40000c0d400350040c000e642c0508d14460341c03856000103203001042c1a5211482d65460100850301c0b8a40c890015405004c1d141c0d03861000d424008000e60443c1d40c2d204002c000309210701c0500c070060820f03030058407420046040c1500c41c0c02c2c4110109081e030301c01e08962400a003000003000032088a82c003d076100340d4000d40046082034200f0b000b04000c9070010304040c06201407000010110b540b0b5804035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233081169 1250 233079919 233079923
    0x402040b0415060e0108040b060409050307050706170601110a290a050f06030d0e0d0309170a0501060b04080604020f03010608030a0201020d0b0d11010809010608160e070203120c0901020a 82
    0xc001000c40c200b407244054245008100001d400405250020f40c850100c2c4c84c09a41c00c8200e200007900c8480411009100d00202111036001c24130110f00410b43c1441450002c0c0b18a8990003c2403007460880360000708000c00c20b906003c0004c0da2040c2c682c0d80000e0401c440350b8041c0b02400b9424161070009131034842080396400850001d001c21400010a810542c01109244005c43c9103854600c1010b07100c05180341e0040006000c882d250015140c081c042c10907180c084d05200b1030f900c1e15036000c4030f240f03401c40b03444000c0c1d64041459107041010920811000301100c140d032a0529040034071242d20f526000c0c001a101390140720800a0b55502940600003d002e0380003265902c001c03200c8042d01139040000c0c421903c903d803607140000780c00e10a210f44002d81c2c0c443e07010140c0c8e0b071290740103445a100181c0807c1141d9a50000407884482c208a100c41580030085000400361400761200103c5100071700c41c00864109001c00c1401d1050140352580010204a11039210a90940100c0c0b41118032600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233082419 1250 233081169 233081171
    0xf030e0709091406060411031b0702060a0e0102060a020a0203220f03050618011a0103180506190524010c06020909010314100509190204090804240201060f0302090402040b04 76
    0x41c5010001c03040c3c06480038a41e588113880070790392400200021124040e02c420069501040001d4000d4040400303c5c200d113085504070b50034031180d0b80204140340c02803111000420b441c1d42c3e4525803981c04103c44c550041c0a04400c0d8984542488002d40301d024510b0481051448200a481c46a800181a2000c1c06420706104c0340c299072420919521482680e01880e91500c15603070b0080000107015210500780050040141641c4581c0114014802c180d000c4011103004106400003640a01c9040d00522885403440101020100120112400a0409403000400713405820034804010b00e403d55100c1d090a01109802c494184103011b84540c464941d84842c2c044004000c00c41e0303003110400750107201b03030884580181030311101d401c13290160303614034055005407081d400d00c610010104550b10301c0a070001c201c0c1c144a030356510690b04148c200c01d0b10f80382900c0c80510b07140400240d80c03448804030b10090144c1c13868205023144d440c2d903600010b03029904e040b000070295192038004000b0480041c0c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233083669 1250 233082419 233082431
    0xc0306040206191b032c030d0c02010c1a0a0c0809060f0606040902030f010914070903260c030d0b01230a210c0809030a140304020307080d03021e04060f030e0709 71
    0x50b004040c03a0508481c6c0d842c02d4001d461007917802140701c1e00740d1316210026008010801504405440f030f0071968100328100710000750350000180c4820051070512045440c140e580b420000b0000090311080c0394400708100d03020b401c10140c801c0024200c2d400c803042c10007240031900c0d400042000b074840c50304194201400003060040100e0759180c26412034401050802c0740586d00010260303410f50a031000000160700900038404900445202c40521040c940e110160030304094015000c0d81108145100540004c10340035000b4095014410b500102440c000e0342c0e0000070a80c0180c104903000090102c2d031000300e54940114007940c1001c030118141000c0038000003014500001905061102d400000c0c081d81c0403d40008000007551140300d119107802180581110700d0b207003950401041030740c4c144a0a0000a101501404a0164045203560160b81da40313420445a0075650240100411302c1010801044090340c13025014603c01742614020907007680004c6054602400c6030480c84c0310502d0f01c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233084919 1250 233083669 233083673
    0xf050d02060f0132041b1d040e060c030901151202031204120201050f0904020319060b040315150f06030609050603010b01020d0c030311070c0303020c0306040206191b 73
    0xd809481104403030000300c1c840c1e80341c40e0444200c00f2031001344101000c80120b14420034914025a884c01c034005000014a48902c04400281c4901e50082001003014803401c052a0000d81c0c4006c1d440d41c4080d80c042c801581e43d007100c030b0350b11000240b440003205008404206088807e40001c10146400085014040d85520500c1094041e20750100e212b8420040c0008100300d50a043c5c0b421a20941c0340c0d10103403021500150f4165101d8030081c0084002006689181e0f84c85101075030180462070a01c0c852100b031507651100b00e40c01da802a60020700103120403c0091200c120103c06855100004103205500b41e03a28217030741c07000d41c1151000800581000c101c940c8d04da404182264540b500510207510b4030000c1c1800c030340308000d5050050b0440130401c080036000341c45103420148285800140343d8440c2540c0da1075500820411500780704071803010000c1c1581080b0410f40c981c022806813415042aa00180c81da204000c011000329010103803603071055001c2c401c10428040f49910a6035200128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233086169 1250 233084919 233084923
    0xc0a300b01051003050f060d020102030d14010302010f02070509070c0503120a05060a0603061805091e070609081906050a0204120503070b130305040303030f0b1002100f02070f0f0f050d02 82
    0x9016090007045451100f26066100340101406a00446118085622600c050206841c0d10a00690651004000d0603542c1410307071285103a90246901401095415440010000c1c200c080484d821944440800c0c446a92903400b800d80204035810010800950f5240890a41c0202d00300742030703241680d20820000458913000350340700310381c103d81c5035403201d898450503000c86e80107000311525103c42280c2c0b41c10078483c0e680050f8001801ca03045a0441010b500c9900b1786840404bc11381058100500c108007030382e0428035002c060144a409460080544d5508041c007203890407000e04241c0c0c9032008504c96000e15412203024243e00c0d0064400055242001696544081f4040780e03880552030021f45108192038101001942c90303642c082c945131a5480c110b020b440a4002c4080540c0d44054940d2a036a44a2080344442c0c46078003e05412402e0301fa294003194003032200d01ca0f0300c50041011000240c2c0d144000b00346154080340074041d0f40302906103500c030112280402042c510428500f0300d070303444d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233087419 1250 233086169 233086171
    0x5090915090f070e060408120702120d05070302010510051e0406050d0308150d03020d050a0201140a0504060b0f03070603020c150907230a173301080c0a300b 69
    0x81919800d0440781301200340b00355440b03140705a400e5038200e251004c00f4089081c0003480007a000404624a0300d807107a02c0c050a0441d00c41000002c08c100007401e034105502070103029070058003107038902c450740e26080c0420000e070011082d41c203840071350100d0b00c2200d544960106010786400340c00c1406000e0300346000b80c10324030706680022105800c00028249031500f00102850f4607410742c090450240d0852045d513082c0c000d0000e89003595214105081c0700c010601e035031031161007400004109800e1900303000040303174003480310306001b50f20f582001031180d00c0c0003d011040700c059140060760341e06c0250701e640c1000c007a0610095880514014805111000070301d280690301c400c00e118418581c42505070304444c1888107d40d41054607081c0c2004048440c02c2040c0d24440010f0541d80c0c860300c101610308540350040080c83c01d181019025840c525040c413001400740c40394100510000290500054070000d00340301c0c0ca01049020624a10100c00c60080408201c85800428104145ca89050141568 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233088669 1250 233087419 233087431
    0x813080f010c1107060c0206130b0d0209010806030607050328050408040819020a090e1504030801060e0102030c06040b060109032f0d020f31150e0705090915090f 71
    0x1c025a0000f0200030108000086601c16101d04104229036800e21086070003c480401c0d0320b00c040d0800045000390781000b84001400d1a00050340c0c3d4441d203001400302c002c060482c034081d074042070403c0174054100b41165042021103202440702061114111007541004480032151402c00302480104101d14000d0415141410240c91032000001401d0542505900d0043d601000031042080034900075801000091598030955483d0502c0320800112080c00f07440c220f000074045401002615401f6044d428140f50074805903180048010585681d10000390000c6c0080d0304500100d29035a0240095600950b48500ba24200142c081552068004c00e0424105171038072092040d0340c103203401d002210300540c2c000d1404145046100174080d0034401346d180c56607480c4401e00b603003400442c0841104659019000d02080e00900640344404a04140e8488201c1c03500d10400c3c03090035030700082556440c0d01c2c1610001c010740d803088000f05516102100c0c09820401000502030f00204515400303200318 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233089919 1250 233088669 233088677
    0x15090411030a0e031306030c3b03030a0e040c110d0804051e0a031218141b0102070e22030e01110c031f0b0901060c0b0703180813080f010c 61
    0x203104141c0f40381c0340d10a0941e03964009030181030034011940a0b512081d4640320524002c00c0c46d0320204040c10341002c0411040c02080300c02411114554070f40d65075034101c0c00c0160f0245090418245001c1e10464130f02c8001e030720a64581c440321040e00c2c440d28412503d95104022184511607114024003100001d40e42034071140101004041030400c04540c1485900c0000002d0400c0262038401715000c101d4148d01007507480d158024200200400485224918003d41c960406d041e40441014039050310304051581005403d0032240817030381c010400ca0110b0745500c914043c80d907034280444842300c40c00301090701380d009507004104c14142d1154004907028020780354090142d440c1742503141d0391003001000c540d040e404980000d0990168040c0c11b88010300132007000c101415a100054030714602608007100150110207c0000c0c420f24009c0d45800c039045040400103110f14038190404421000806800e8040001d00101c40003490a010401850002c00b518480602c0f290454041e03c8803600440c001313 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233091169 1250 233089919 233089931
    0xa05030f0112080318010b0301020a020c011803020a0e0c0405060a0509030105070212030a020c0a0c090b0306011205030706020a0e130c1116060309081308070f0b160215090411030a 79
    0xd802c04000c002ea540101c255421565108810040d0008400e1042c509540310341150855890034005404240e899401814070b08003a1400106000e08803010000300d20000a42000961184107040301a204441d841e2041541d418012600c14407681e40060f4101d20009447d1591b581c1c80741c0540b240744421002449580c840800807030340d4001009032034503014400c0011921410107a03008042404c4441d0545100003150b40301e5080125103503102400356a141c5000100a1a0602603d40580b4403e0341d240344840391034071415664051a80e000341030503400982c0e070b2030141c021100c1800d01d000080136079001e0010450707030401814080c030240d0045038418810304824400030030341d8440240d9040303074035802603e800408c8010300b10801090f04c15007410048040101881c5620304041d18500c801400c03100d19110307896204003507650019416610902c45245290203000010080680440b8ac0c3c100c60369460b0b0126005201701c4001561140c908080f541120550300b0180d481122412406c00c06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233092419 1250 233091169 233091179
    0x5030f07031229091e040606090507020706050f0310030b04050a050f0a030206040b04030c0206040806010f0506070206030720010207050601090f0b010c08070302121219110414150a05030f01 83
    0x110305420003d000390b500d002908152a070804410075580720100200480303150b051032100301c0e13844005450a58405468250034820035009001d01d907044502e41c030060000c41d15144009101c0e0140311540100801d002021442c01120000303500051600140200c815007094030304196114003081040700e4901812406e1010100e0110700702d80140c0e0160003a04041d5900d50710000038003070080007103090042440c503910151700c0b110007a0001d80341200040400d541801c0c44164140e1a0ba8401d0748129002c00000c80183c84100c00d4a410104508140c42854140d140c0c40301c8d1401c01c1604010b60758404240803081c000c1c00140325049600400082180f5581c640f4032000f5200300d100128003181c051240c02c000140924014600d00380a4419160005c406040f40d645541c40441c84811100c02903041c40304800d1070300868000c0c103440c0300c820402013440110b0004c0902640c410700ca4002e81004045140e602d55103040c1105807884956107958003130061000d020b44e002902e1a04592540c1c00000c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233093525 1106 233092419 233092451
    0x61515210c03070905030706051c09292401110c03010c0305070e030607020d110a020a2d0302150c03070611040810051302040905030f070312 62
    0x42d4034246268000c0007034809810040c0b083c0c00203003040141c50f4100044031740016201c85050302103050908018018001e2030009000500100c0c2b02c0340c03040003140f1205802407441c840b0540e0a0302c0f990b00c0c0d052400303401d080b0207184404c0c010282c0300c03a600406409036102000800c0b644603841e60b0f00400d003543e041280035400b094413501440341c1307142c002c4800944841c0a0f8003c10300c0e443c04640003507640d0400e80c1c0310b00c01e108030100184d404140c180040c840c2241c0181c0b50000300e90781c801001c4103504071100d00c1d000d40803040c13841aa2001180010b07808480d0020030380d0341001c4140143d4806640400009200c5200c10031001c80080d091780540c03c200503412404503201e030b00d8008500e04141d4441000300e0380301c0c500070400108424000c0c1c0405880e0301035600140c0c0c403c8514020f890741c411010171000c2740001052100415500c91161242403a006400340444c401162142c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 232913669 233093525 := by
  have h0 := BRFrame.cov_init 232913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232913669 ≤ n) (h2 : n < 233093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
