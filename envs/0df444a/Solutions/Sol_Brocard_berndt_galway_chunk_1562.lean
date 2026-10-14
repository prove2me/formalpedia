-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1562
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:35:17.924193+00:00
-- url     : https://prove2.me/submissions/482049a1-6ceb-4ef7-9e84-bbe8c17bb550

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280755395 ≤ n < 280935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280756645 1250 280755395 280755427
    0x60821030a0f050f0414031201031104091401020c0111070b150f0315150105040b0a11120711150a090603050606070506040516080d0c0813051509030105010f0317 71
    0xe4a0030116050006101e03034600c41c013101d079002e2440380b81c9001414a02c81d03900c43d128060300500b0051082c85c90010800302c0c801480605031a81c008200181d07204041e60b42040c0f5401009080c0600e0b075000c500f010020009100ea00003540d4849401400c0c001c0b1642e4020342c80d900100351801c1c13410f40b03154000d1203032200d0304100c00c0007000506403103403d18200b0b1002d01100c41104e01d03480c03005074030030510707019406401280e007503900d00e040007071604030b2812007510321400c5162401e01074491140c000380341000f00000340c81c450707100d00382c041c0b421110b44080100103042c2c0c0f45081440c060401103401c00c00c1e081180ca50865003c0d0401058907a6a940000c00314001c0120142240c02031704100820003401280c024075102002800b00b184a403900202070f41c5d6888020460080b404c0024008046142880506170442615400107202c40c1c654010031400c211041c0700c04030002d40440da81c91300b4078080c0503150151080440040540d03256440e0482c8481c0540f0000d0b203401000140021403c0d003040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280757895 1250 280756645 280756661
    0x1030e01060918050106050f0d020d050c030a0602040e0741070305090306071806140c2509050405030a050903160b030412020a030c0210020f1f060821030a 68
    0x5420450030383c0b00d40c96541120f4121100b02e81d154a0a031000ca042c3c9000048851480000341c0410384186156003413101c004c1039003506848902c54600c940b1010781e400c01c0a0801e442c0b041001586071460000e1512052002804a03018055034890000300903802c3c1e000d2102490540c400c00740b0103610440e45032410090143d001969400005004061540002c010a03810b40c0540c00c50b010780d1fa40010403100d090f000707150400d406e08000c9040051921440301c101c021136076a0300407841c0c001440c200700e1070a6907075400040ca40c02e1140c0b510045041d41c000c95402400544401e0109140551f0303042d46030f00c0b401003e6400e00c00086900460341e18200f088050b280d454101050f6019100c2030b094440e604101c80484402c07075151000072580e0301c045090a001076040c1c0302c4500038001c550800c41d8001c040f050060441c03003a402d001c451081c08021000340401c4c4041c0c4601400300d4400b030031064030202d400c40d401c50b5010bc40011046151654082a40c510b40907041da12611031581c45030260a0311 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280759145 1250 280757895 280757909
    0x6030d050f0f04080c0a0e1003061d0303070807090801200a1701060203130f06080a0f0e07120611040506040918060606080907090b060d020306191e060504050f01030e0106 75
    0x1c0f80116408600050f00114120111001484e00c2e80d00d103002c17003c0800480354108041000d40041000429a4005041c080900700d62403123040c0c882d10764a0f01e10f40040b01e4000000e02084180b04a980d00000083c01400c045402032220840880044444940c50120f01e0324003000003031560001c80c4604a07130030149012a6031040d2a5a481e6402541c9030801d40005aa540920ba00040c12501404070322040796600d803a040d90a03690402c140c0028015400000301e038940301c168048030b098090100001030480c000e5855140c1032241490011a202c4c5582080c90100800051285582c9d000075102101c0e0684070104a11410424a03440c0000082d0001c11682c100040458019000560280314501440880348a140d4a03156801998401588aa00080108440da03044070164005542c041c0000c3c2c6010741000054540c0501070a41e13900c600e14500c982c40c0811195500c1481d4540200b5540c03400034206400c25000480106003048503e061650b0f420b01c0300c0201c1801c2d0000c1008101c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280760395 1250 280759145 280759147
    0xd11030304080607020f0a0210030c0c0503030705041403010501050901051306180230060105070c030f030804030f0c0c0e150d050102130902070c05040b010908010c050406080f06030d050f0f 83
    0x5a90400c5540f40c50650b050030240c0184002810178400c0021184101500140b026a00007200881a00203024119003d030030000b10329a803401040c000c01c001c2d4040c2d010707951110340c3d5600c1c0048000710210008906031099052100401c0550b840001c0345054403021110701c65407034050048000140440d80c000d091707918040f50320b140d11003c00e902601c0240b5148442d80c03045009280000d10701c181072880312180102d42004600d05c0d501ca40301030004244a41d1051142c1a00d039141c4418629840e102200000c00f414100410035038441070071941010380c2e0401203a100b003565552603240c5684d00510f9001c201c0310001450030440311120786145c200c0504821a250b0b190706010b4043c6d4050b021045921072540c80000300c49075a0302c21a941d2a0f0800d249070b03203c85c100003c00024003042c15049041042d40600412000428891144061403641301c80e69118a042006031140400130010840c00c0c0307020041041944010901c1d44031200a840e0169450a091010700e40c14040c6821392103022030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280761645 1250 280760395 280760399
    0x1805062b0608070e0108150a1517060109110c06040609030302070605190c021b120a02060d0e0705060c032a1609050a02090d0605060604030b19290d11030304 69
    0x20b00882c4140076182061a2131100fa070300c8480d100e81d01c1e043d44a92a80c0d03841408002000c941c156400003080d2580c400300d4810056580f05040d4002d41aa000000c90b03401400040000300d8580c0308d5803038440080b40890341007005c0e11071110307110b10000340040e1819850318070610030580b10368104c40540380d20400401a41c202840145244a0b800300d03111429031916000320b000078000101c14014198800d03050000303890344030602010010340250340925128500e4060300503036030a405429600c5104200103541504101c4152a205140c0d008a000700420421148042404021240c09012400700c110001883c0d501450801888120b560307418054071000394011006640c0690486039011014007072601c80e1500c8004a00c64800d005502590500910300015070540106070f010030000c0580782003968a88502c410200300326100d403d032103003840300b40004205a100715003500c1800c00d00c04444545180c0f89078011a0035001c21442143c445260204000106c2180640200064140c03611a9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280762895 1250 280761645 280761659
    0xa0311030a0b090703150513020d1e060f0b040608040c090203010801140108010606021906140a020a0f080c030a15050d08040807080303040206030f09010f09030f1805062b06 76
    0x40d446812500c501c81e5a40070840f620310074080c0c0708440710b03150110300f0b80d14500742c100080f0703230105040b10700d1450b02444589901d8140784505080154804d880181100303159211004175441904400c0c2004002c00080c00007007800382c04d43d8150342c0306061003500c0b502c45013040751a07681582d00217a442400000013040080b0190040005030103e43c40466560343c030b0b107508030300ba500350f8000e50005a0214009a0010441d8407502d000a8002d41f800103c18042244003407100d0341c00c0b26104200c50300050311a03100c0c1d03804494014804050701d0b111416051202805960744005001c13040741503200c004254100041303d00d600c00501c00184400b00300e55444c030300215580c11901c1800742078050110002040c1c0b1000c0b0440384119802881507145943da0401c43d5a428000390002c10990b40e00e500e0805a14018890499118003d482d4000b0380c00c00c5c21001424032012480c0c039450104040001c00c001c2d1210310984030421055078500c05c8814500344a10003004044d05090040c07410003100154078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280764145 1250 280762895 280762901
    0x9030a1407030512150a0f083c0c010906050c070512030c01090c030c0e1e07031107050609010506100903062301031a0601080403080411030304052205010911030103080a0311030a 78
    0x4054180c403d00840d980d5110302810f9900b8520031075940b6005400082c800301c0420a26100c04440c0c07402c44005000841030f280d00c009c09000c403200440c4d08c0109000d081c0e60700051400000c15280c80c0261800c400407500584600311403003220300a030000b00141d544250b050081e01c099445580081240074024104600380c55441e220940700000001f001184002c0c0140003203108003080e03860400d4404404403d4190280011300d120109035442c400100320645c0b0b20001d08001d409000201098104030154a08550019000d14411855004070030036868100c0d031840116900071400080c45403600360701183c05408060343c0d5240769000310000c0204003c00b00e5041c6054600091013502d655041d0040d18910b8050702e001d40401d80e41400907001031407000b040d9409501c060262420281d031600840c010100c00c070741013000003480d40b580446200da207110300342c014102c0e0780b824490445e12a80310b102d58441800050082900011a140380034020707003000c060b12859116069076843c10804440007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280765395 1250 280764145 280764181
    0x623192f0a06060e060d080304022704060c031a01030908040504060b040608010501051305090603070b030a02120603030316050a0c1e02030606010306080615040b0913030809030a1407030512 83
    0x10b803c0c940080480c4136101e1100840c8070b684054848880034015031961840b40d000204100d90141e00d5042c1c90b07884820345104403d01d51121302c088011400c0c1883c101003510704841c848010036250000d94181c0c41010252440d01400c2802c0004511005080c0720100c2d04c103e4008903045070a00130300190510030f020060040390250755030781c1003d98a8000440d00c900c9600182c00810501382400c2c001071034005000d0b604101c00400b10f400655482c0c41d04986500115038001c00305601161040240e4100800d1036807040c400c5003e54503524201d911028082c5080002e202000350101c7c1d002415805000c80000141e040400010062440f02d507001850400701012030180c0913080120756954064040c60003690f220070f0140041d42d0760003248102c810310981d1103e5200b0b8640003181301640301c8024250040301b041b402900071402a003006000c511000d0404481d9500400054040550066143c05801400c10800b40e9411003030a04883c9400b50f4800e12542c0003901c0d0910184a030b00d92180d01e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280766645 1250 280765395 280765403
    0x30309060c121602030c01050f06030c120d030c1b050604060f09020a0306050a060308030406051602030711190902031f060201020a050d0f0212010623192f0a 69
    0xc00c1d80c0740c12005100d030148504007440d0a5244011400c80440034840f50040c803038601c101d07801d10949484c917600350f500075120300e54501c003200180012410280503000080e6001c1d00c1c60490f1200c0708100c0d90b80c400b0300040e828101590740d40705c4e00741948645070f26191011030300c80d801743d51126818a20b0301c800f005c1d90203da055107000846008150780b030207044680740d0010034200400c0d103075031101c0000e4100200003260743e42d5100b0001c07001803d034070301550065004a400150914168240410600c90080790381c0641d4805d000b6840042c4888200400803c8155100210000d0011041c1250b01c0b0b650011845c0c58008410488140c110010811200c01500c034001803050340c2304d03002e07400c034440e1542c0840090307810070604100010b15082031300250116800186400e8552164400194017078010320001130008110059040c1d0f0880301240c030b015060b16151408440c25000c07081405a00011428020300585513407201c01b640990300d4580b40b903450f035500780c1018880041c0e101c0340240c1040b6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280767895 1250 280766645 280766653
    0x6130f051f0b0103090b0403140f0f040e0903030606160c050d12020c0f0a21021503150a0518090f0304090903080108010608030406050715090b011805040309141908030309 75
    0x40d002c0d0302c01e008101d040d0f0303003000d02403441fa25aa20120f8100e042d42e25862480002003010300b542041550090007030310b20b031003203d5847d1401d09000707140004010700b0507051644280305000145d6200d0007128039405406800400002c103d10b003400c0311000c180e1006030700201c0d0380e00e12018452440c00c49400c0c40400d600380c1342010306d0745042003c0c001680d0300160300010541000d02c01c1101c0c0b18a03003500442400302602c400c4880d6400940310503210307000d11b00b07860004014000600d00501140d025400200c2c0c80751103590500001c6000c154500140c0091510090082088044140150f8440144039010b0f42c0c2d4941e1600740b02d00c05000290001c400081010000081c0d0090610420069800c0100610701d054074001040380c0c50703040080f0550b170200f1340640d85d40720003286106aa00f4180304e0003807401d241d0301d1f200c2518001c210102120420398240fa0130003000a500c500400103441c2c0c10301c45045c5940c11540403402c10078607035502401d480850000401c800c0390001c00780d44076207e034804071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280769145 1250 280767895 280767911
    0x18010b0915010c030311130e01060807020c100315080610050306040203030711011701081509010902090f10030206030f1f03050712020127090c02010b010206130f051f 73
    0x1000314100200c80c0411408100205160701d584100c480c0c403007060007407901084801018804078510750060340400b0088002c0641003001c126042c200c00e0040c0344034109401d0078540444040c2d00d13400003482d6980708461038015030601900175440307451b202c80307608442c081580e00c41e591142d95000556044003422070390f0030009418038000981c01c2c03150f6409000b441c14030440d80c0d58140c130143e200c0b100c4c505202d1202525807070310031003844450003000c0210027400403142080c4641c03030346840075080c2840c0c2e9060292640240e1680075102d0f41111510303a805c1c05c103070380e00070440c2c0c030360601900001d511680c00428000300c1c03034200c510b15000303500c0c844100090b4900100301010590180c44010503d40201d082080300001507144421001d0040c1001d65407003c0c5e0f0010082d991103000d03444501400319410a1002c1042c6200d440e0440369030b80000c001d032240000003c0e6940e80300405250010040041d00020842d1016010490070b910504031002c0b42d05034241c50f40d01c4c1005030300401d0030714a48080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280770395 1250 280769145 280769149
    0x170a0b0c040303050d050901091a0a0c1b140111070503271c0609121e05030903270a0303050d0e0c0f1207081207060501090501081c0c080318010b 64
    0x4079002c40f541920f86520b4465041050300203481c000304031340ea85541c0e82a200001c158001043d0980340c100b9240b0907407501e0114042001ca589001c030f4641006040c0605139114421500074034101501700245003010b01c0300c894bc06014242d202602d080700130001ca180c0c010400d00201504480508440702061a01e0900e170741c0c00c10700c410580c440d0b481002c11111003082d25020f002c10800c140903007000709902e1000e4441000c02c52000150200140760304194142203141d08001c40c0d203a19191030101c2c91800d0042103141d07640034400004144400c40c2030002c0c0c0586841075018281d10f809401d10014075640d0a0107001c1d41c0020031050001400c124641030f10040214280c100d600008014004590100f428405032000d40002c19000340300da100d02060641041000c00341210780c043c2b5840da102c05a01d42402940c0f41039100b4401e160615006009412000c01e29103c800c84940c07005804800a03081103441c80c2e00c141024041c0c42000040c0028450210407032154142c488000b400703501c5c80401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280771645 1250 280770395 280770397
    0x6090c0507081e2701170601030c180b0a08010f060c060207110a0803180a081b01021606050307031109010f05130506181216030f0c170a0b0c 62
    0x940000151040180c03400041040b00039014110a00c490540c03c4401d00030303002001e901c061040110740441c400782504203284000c000018203000c3c648400652002050014582006048541456214580403411610600b20110345560111481d04075507968007841b01a60301c05a50540000c0040002055103142c1ca0045411222166124801c0c0941901ea2600a400c40e540c2103501041943c4501e086641c2c039101500602480310207182c0c0d90001d10428800740b04441c50b42d60142c0c0d041807080004645c00710398031043c5107029400100008140004178103250040d80203641034080ba02c40498883d0340300c0041d52090301c040c1c81c101310b242021462003116019049a4034002007040c4000e00ba001c1c4501d019208508004035102d120326220b000140482d00320040280c4070414802070b0f20520702e0911070480d10029501d02a02290509900d10844101c96010203084144154100c404201400e4614002440b80ca201b00c22080d04104040751a020104000c0d95988403a40100381d09500c100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280772895 1250 280771645 280771661
    0x150405042d0314030a0e0115090605040618020f07050307030f080c3603030c060f060a0602062202090106050342030705090f01030507060c0215030907080304080d02010609 75
    0x3c0c442c030041c149081d64014680d030005004a52040e00c40c820010b840109000786043c1e03100310072103ca0381c2c5040c41101821100a640954030860030b000c1c00300020450b810511406004c040000360b919002c486614101d44200e9400601905c000541102856440b14100403401d41ea903503241000c5e10f44005418a41c01850140c00b46060000e0841c5002c000640c5041c806040001c458140503030405c0c0080c0c1590040341019003140c0120301001403014072421001e034030610484071129001d0808100a40e1204003d01c60407402201030310306c001d60b070030105403590b04076402041a29a581c5a00c8001e01540080d0346282003500002c41801802e282401c3c440008900c401660052059400703030008000030580619030540141103012903180c69284019200b2900ca102c0320000354550b2802a1400e08942d22401c10071641c1411580141d0307651480c00003603600c220b40c041d2652601c40b140c4d400d002c406d62103803005200010300003940c2c003008200700b030751800541c00803c05955500002c8003541c2c102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280774145 1250 280772895 280772897
    0xc2103060108040c030b0a140a09030504120c26010f0b030606300303060a0f0501050301050105030a0b0a0303033306031508061f080a020f09150405042d03 68
    0x14800110385520492115600c207004e00c072000e800a07075a0722441718681c402e0b41d1940d5081c0d01c0340d45600c001d15000041e103400a0800b98100b0000090f078034000c1882c060b45c0200340c107411881c44158180b040901400d4003400c0a00c0d4020b484181148595481c000c6002c5903030311550030403002c92030740780d050300c694042c403074029001d41007039600d141c10002900d0040a2024408002c00c000031004105450503e80c9800408011175590600c0c0d000c00410002c1640125000c10341c0c003d05000c1c40c0d83c8641501d044850a00340562640c480d032000c44081d0140c418200d411416100c400024550315030040000d40154004042043d512005805600c0640e800921102d81c106a0204a1980300c2d6100400003605031142143c2142c482482a080c54016100344444400480e981c801c0b03403c24180d8440180000001483d6002c01503000ca60001038a201d2103200c0c6a9040002d1142c6013083c81c07842d40044000c02c104654036103440c201055840351011110038100e92044e0340601299202c82200c0c103501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280775395 1250 280774145 280774147
    0x1005061302031608090312010f0f05150a05090607020303180111030702010e0d060b030613150509190c0909030809120406021f0b270c0418050c04030f080c21 69
    0x200c00913602c124020f440d03d46070340300c1008440250100344030000d018080700c243c0b130030035940341609614a12188e5000b05102e4101e285000008440c0881110700480441c01d01c60b071a04503490004425004012010390180000220502c1030b100032000c502c0b000318240c1707039000c00032180b0303424981d43d0080f264002d0208005484400244c0340040350342000510511021070a003403c400424107103501035602002c15001d0b0880342c07040114507140c03100141080c110030070113490010890740e13641c00642c0116400c2100569075501b07001900791a20050001902c051003142e10030f14000300400d604480c074843c0d0b402a1840c401402441c0801c482c11624140d004003a9503280044031195401500703075400e80c1c580c1d11841e003641034903504040440790f6001c1c001200400c582880900c90300784001e110b6a0100010803003030101d028a51144c2e4071522098800040382e6954030300c41c41013440386400103007501c41e55841403020803804400034021611740c1ca0580d011045042440c008178000c1540c40700750894 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280776645 1250 280775395 280775431
    0x9070e0109141f0c1a0f040206030601110708102a1107050a030807110f060d02071403070503210103020f0f01031410080705030a05030316020708100506130203 70
    0x41908886490100c1c02050440f488000d1000103081e01804540b02d004100b58084100c1400810b1a1041c10f52080fa000348405141001034400403e04c000c100031f10032080800031a205034402d00e20b60380c0c024802400c641b04903440c1c642032665966020320940b680750510000403e084201d03082420f40000d0116034a60402400c1001d540850680e0144500c610590341c000a841d610300b10408011401141d0301541e42106c1c0c14201060340700820460b000b04284070420b4a191903032021562600c466690051319040e03a071922411902d280505804107110104480085c04404001800c0c0a400e280302c40314000ca0000d1454441c00003480065800310340c150b10300e034080c20040f0310f00e1003c10052400144403001540320f807a9111040d0342c0b000703480c00c0d101014040600d0401104003d00f2080340200000b007220355a02c4d68034071009000400729102c0c0c608014aa42c000c00c5500090140c48094803d003480c01c0c80038400500e400c030f480c6841401c1d40301110b951000d0724401c4070301036031440c010020000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280777895 1250 280776645 280776659
    0xe0a051801050904140d1d060a080103030e0102151e0702070f03060f0902100903050c0109081b0102010e030a020102030708131a0705131205060a0507230f040303020c09070e0109 78
    0x151008109480170031131040803da48510074810b00131030f40c0c1282c40d601c03038911a07825203e44101490030325500801341003280c0c900540e00040b03224110f0707a261404448502080004134100702c0d5400394241810000c5050200750f140501f2141e01d003010170603910683d07540301c10701240d0b1044580b00d1464040003154050010840c0c0b40c1000842400520000c16000c0c0d665011403c1c03804030861140c0040c2400c40e0510070841c0034032800020450901c0c1c01030f0500d05001441ea244c010644a031041800d10a0303441d04141d0007074000744d0b00554401d003640c0e02d585031400080d01070351048a40800283c260030000d40c1d04000290403050b2985c01c404000f0100c181d44515051561010b000401445014080d8200401441c2d01140c09080303820700d10722a041161030900c0ca40003010b001c4030711003424401040b4400f540000100c40306629000b08220440e42100812224441d10a108045110004011040c1500012100d07105501034074040b80c00d40e68403800f200c02c402140e00c598000342c28800c04200710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280779145 1250 280777895 280777909
    0x301030b01060804020d170901030f06080712050111030115030b032b031d1f02071a0c04030503030c0c1e07150504080a060c090f0510050c1005070e0a05180105 70
    0x45031000e4181c0c80b11b030800751502c2c00c00c925818a2901203c400003580211545d1500138242d9001501c4024070015084c409a69116000342c0928040b03003102051030b00c07e204013504501e80312080d1103038440d5030356121380c80303080c00c407194140704004a402c0c18205183c2d42030004c0c07180d80c42c0840c01d1040e20500300300642c00b161a10404030700420581c860b000c00801e90310b010070030142c10129900400d41d680d01030f5000014111850200410144103014500101d12508241c02c0c2c407042d1a506000581e03101e150041280c041c46e040a0a503110201c1085403400c061401003c504403010b049400c1203d03040d411100f0940c6583c1601c2e07280c5c00191080081608903141c410600c401820031500302a114164103103801c0b0010130a40300b450b1203070404543c064000319110007a200944039060982d0070540450074001044480c00100000000c402c40c0300780d401d024811034086c1894050005080610009100298100446204141d480b8002a03a0310307004038011140c8072119528107540c0c0c82d0804120f04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280780395 1250 280779145 280779151
    0x28020f01030f020717040f061106040305090a09020a230c1515130207060605060301150c1518050601050f030a06090507180f1107021309080d0c050c0f030301030b010608 74
    0x35000c1c0003220003d017071400c2d01c916035042d14200316142e51078402c03010014000c0d94415028454a00e2000440385004150240d1080d018204142d0300c0d5500e2000c280c401c1180c0c2e0044003c01d1003c42c80409030390b4414503182582c0651388905882a0030350004800c01c3c0f05100300303552740da803142024140c101c40312007106521244400a0720065038036580810061001c5006900c121540000d1450810865100c0c0c60007412081e00c00e0790541d810816810709498640003150203100c00001c0c01400c1104400c034000c0642d800000520a000c0b22070304c200a20f24040d0030803549030054400104403814480404590910300074001c0c40705074a02e48499005020040003502d20340174203040490800c0c5200c2c01034a01030301e061800a03c2590b402e0b107031821110b401640d14450402048070b980543c0e0b8851410b410108034050000e004002c614084841d4820708035440d11090404402c00201030b0014080d0210070302e000181c4074135207000c2c08016100d2000f404010030309842d10f001801628440d4106070740c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280781645 1250 280780395 280780421
    0x61d010e060c0102070602070c0807060c0803040c1503020d0f0216060e10051003051903080a020c0a060e0309011b05120307031514030f0105040302030a051c02030928020f0103 77
    0x101d4000b07411411400da134001c18060700d44580010341201080643d01c0706c04001c00021018010050800e000200b000a10020203001918003001140910000c5810340c3c0c000c0200e07145c9111080c6040d100600030790000301104110b107203440510305074045240200e03000391490703407111110b440095641600a10503040c40303450358441c6a28007039952105104490040f40700d01d51190180d49185041171410440d10b0020035610b441c621048006a080039059401c010713104070160312031458840e05450404880e901800807405e0240b04100100044010440078000383c0c1c80448003a11811b559a0010b9240c0d00100740d0381c02140c203501c4102c1101b020f940c000d1110300e404205911444000c002e900070360f810205d10030150305044419840d040181c04001c41004c0c0080c015441c064902a403a8001c040712001403003c0018803c4000e0080019481d0101a0f0700c0110f440341010206582d0b102c4503518502c0714452a411101c600008106145121560040450341280300303140044000c3c004840c1041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280782895 1250 280781645 280781647
    0xa020c04020406030207050f010903050703030b180f16030203010f030f0c0b0d1b020d020d0815031c09120807060903030b04092118141801090c0207061d010e06 70
    0x2004965480c00100b00034181c81e0740144c0c584d48141001070800c1201070381401544e160020a20000340c02c001a01c1c80d241c1c050800055a0341d005002c1a02c000394010916064003c0f4030801001401901c1100d00075824540b02000718200400d09500301d10003801004c01341c01c4854030400c001002128010b0351a8407440350704104c5552402104540c3d00017020f01d0603529114401c24078810030703151001200c2c11162000f0100144100707000f070f481e88045011201044100000905018220b5031188a80c02000d1b00b241d902211484072411000691502c3d80000340500000103801c200f41c00131103c106411904007441c0500903a101d0340103020f195412414107403121140d6041d43d6851003a000340741d000d100742c100c022014241f03048000c040d10f10f450060203200d02950418054010460b001d560080011403441d84180c3c000941102642401074201140d0700008140c1c035003140c100c04520340d441c0d02100c2405480b00400d0342ca492b0a124000009841d40128080310b40c07058400e8208800050b0110b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280784145 1250 280782895 280782913
    0x513020f040b04140906090a092a051005030405071401140c060a050a0e0c0607140a05072c0703150308030106170606030403082e030f0b0a1109060a02 66
    0x100c03941c02907480b81580c502d002c9420801848000c40c80310440e031089605500300d14012001984503036015000008040c0c2d103491100400040b0707100032210044442c42004241d100c10280c41c2c0ca03201a0103400c2c0910544828481c3c460b010300203032805181d100024094079814215680d804000c948459030400400c03011203400300025200a002180880000e400300f8603042401d24280e070405090100c2292510300c64888402d40400c0c004440c05084609075540c080303030b040509003038581d0000c0484c80c3c040c01c50314504003e40000e903c01214106240000405070000d5075440fa05007400c80032400440085c0010717149440b03944000300340360804100c24500d0b0b490f51907803070194100340c22000104058859000d0031026107940141e01010440791285140b506680040c4207860241522403151441e6154282004124900000c0800545411081240c2e03d0800100304049c0203015101e403414407002c101012441d000310061168000c40c001d1a0800050501c8601d030b2000164a0443c0651416 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280785395 1250 280784145 280784167
    0x30201050f0a021507090e060108190905030f030a02090315060d110123040501030b03070b070321050a020912030306011421010f06020d0f0f0e04110313140a030504051302 75
    0x55034007541c00c41e61580c10706c4c2d003815503118400001030072103414441c00a0070420f2000300d01c5c60000c5060360010010403010382c6031804d507182d402005042e0880c0d64012003004404040c2d41c6c05003501c040c04804603400c9030b0485000d013080440c01e41e41d80b07400000038540c100205018810644810a06140081001c00c0500c030781ca4a140f44440340c02041200040d00708440e690600a00b0315200b011005089014a0510b42c104948074610b801030a00c42c543d04a40c1c0c41d4110303101e00c840310150009091149160004112000358480c032040313807080b074003000f800085510000c141c038828401a11050318142c40200c510705140c000a45140d00444c200b22070108196803820b20324020030900e0b98110009081c6400a810044400d01403410441400e040c040e19030342c440000700303158205051a100180071500400d000d814a0b14030368075141c0d000001e22910348221000e2181c118000c0041021012082601a403124281c0c040640040d50900050003a45040b0a5081c660130b00d0b4440107103001d4100175 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280786645 1250 280785395 280785433
    0x80c06040b07080106090605030103141e03030a1104080606090402130c11060f2203120216260f0d02040f060c060509161829120304030201050f0a02 65
    0x80c04032181c4003010207016000c0e8004421901404050401440e520304265004110717000505c00548007500d080814510003034240980204400112001c410140c03004640d03658942c41500c00003a95450050401841002d84c0141c5041c1e0300b07800040c1256032140380c1000050070007c4c0c4180d82c010106c41700c6003c03010841c170074822190001c4d121414542d41e0022407904204e40148a00c42c00c2d0903000411403803c204400f40c01c618404e91111001385400d90408a83c0d407508841900345d19440000e000e004e502541d0352241450b8070500e0b0060980b50503014510001c1000c404035040108240603150020801d0009031000f00d11036080181070950311001d402d0740946983c07103034000c98100318600007401558041d0960100c05d400c01000d03091508006118105683c0c400e0300d0604048400200c0750b0895a01324820394500011240418074000ba03500000040715120030b84100100191118442c1010040c0c0e01269016141c0e03500f805824010b11a803944540100411800b070000170143e09000e402c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280787895 1250 280786645 280786651
    0x30601032909150f150c1f0b0a081b060706021201081c020c010c030c0b0a0b040c020106082d0a06020a0306080a0c0605132d121707080c06 61
    0x14504074140721614050108482025001d400c81052045500302651a00300d11aa0813a80990760404008100780e00300e041c5014195610f1510f0280000c0034200d90307400c00d5100d5000c0e01d40041044014030403010029042010f10600c61143c0080d844003440c0403e05500c89020280a04000d00e4841c40e60307605130480e0700c00900c0f0309004c105840148010f11003000749046511880482c08a2102a09006135607201402401410441c224840000301071003198007001003948104080e005050160700b400c06061440c420703d010b42e29051b10303030701007502c14020300007281c21100146c040d6850003500b11000403441800803c24803191021300348440d8080148402c2c0d030740209070058072030000c01801001e4844982c40018640d100b10024800304802c2d0320a0402c0310320303e080840ea03c0300710241d142c2c0340d45d51680c013003030f0329a844400140d51546500c451500c12803400069081e40764540314a5a941e002c07521001e4140c6003030514554448005e00c0040c4211806200e659050001e20780c4440e240840803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280789145 1250 280787895 280787951
    0x90504030801050904150903030f0903020705090c25020f0a030b101202061206121501051002060c1806091011010506060412080d090f0b07020d0207060e0603060103 72
    0x540100000d1551014403140075020884261800741442d07112a04505021812a20307195605d000c0f00301014000e500200403020741d00024002c1c9611810041d4988049210f128020005900010909810741003180d800031141108582465440100b80c44510700c0700d54204e8003c00e410302d03007e41c103544030641c2000542c4a0b4803150708520f0002c016210384900d580c051404121649540e0300180d55410545502c9036200e60403502c0c651300c3c1000105132520303200f540d6000f8051100c0707258510158503100d42c141d81094030403e02c4800303545030403031752140221020510102c050240404040c0f020742c9400788110010189802c00a074280041c08a00d860480d000210f080a41300740041c02d0700f07014066101c1d0044801d64200362800340443d412540c2d922005000460000b1003002414071760b4070030072000350440c18143c5400c4252600210090042d9611400361145403000d20806200007581000e40e211650f94860300920281403002035003000d041c071814151034445030446810110b29080c20031002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280790395 1250 280789145 280789151
    0x3040e131403040f0605070201080a02181c06180209060d1401050703020c15151302040b03150315010f0501121d030a090905010e010b0f070f0c15050c070603050a1509 73
    0xa0030f022a13a00003e20703072140e400c2c00b41c2030107804c0260307030009480e6910420100c005a43c80524900c2c1c1502c0320818602c40e54402c041e80c3c0c10707007000003011084400d118800c3c0c0041041c00c04100182c0c0c0841c01d19070b8020351103c1c42c0e50006038a414507201c5901b1452041c45101d19807040c030341a550030360300c0c2222203000103035010481c801c4c80d15081010781071046009a00f034015040c02c00070620000d03105580240500c004224002c0d80703000da071303040742d0041010405480d16424021041d20400c0c4402102c00d05c0703441511003034240320240c0786d0411b04840b0165107803110a81f50a0043d621210007131100400c20b0350f83c860b118444003120145002c1c25400d0005907a4506140d02d001c1c0c41c4d07041980080710040d03e418010b0100c1c403501c1d0000d905481c0d401050300d44840074032000452902c1404002445455032211100070803002603407402c00c0d2031038824a032202c4c8060071022201402025031082c4194040300f0f0420000d4003035400740d5048858150081100030882c100b00650890070340c40850350304d075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280791645 1250 280790395 280790399
    0xf050a060504051c170c0313080f03270c09040201051204030e030d0f0503040809060c0a0309091116110a0f03050303041a041703070c060e0a03021005070203040e13140304 75
    0x200c041c18854045420400d4100f05c5021031807148140040a50004c0040000070980031040e5107421300385950300c031000942d142642858030155800c1641c60500300000d0910f4114034003c0c1480900903040024002d1055600d01010400c00e1400500140c0c1440304c00c001250180c009411203500c664000d8450102151924003410314040c10b04082030108803802c007500c1034003a402021240c01a0300600f8060300ca09603580085d10034800d91441d00e20306cac81401c0448040581000040b0229030301d1610800c00410703034548154851280c0000c000000b001100b116001070a100a0f034004032101030984402e242d1900902e0b04085000e030801e441590010080000301703c01e80c40e2106203e2035450440c44d19040076540e0907068040054460f04c20f80000c000038200f140b03d101e062a06079084402400012940080703540c45504241c000e50040c0107660316413030540218040e0a0044102e5802140703064501b003159000c2c00005050524a61211264500031545507100e400c074204069024503980c1e8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280792895 1250 280791645 280791673
    0x301060206070816020d050c0304092903010902060a030e0f061302041b0801060c060b0a180b0f06041202011407030509280303031802030f0106091401030f0f050a06050405 75
    0x180009114501130421450403200c41a4003080c088030521a9003000342d00c480c88044e01508602944d0448407a0310714021003071000504907180040c0b00105041d6046449230034074141400e0700c071450006904581c007004403000c5030703100380e2041d400d42220300191910340f01030345040b5042c51025940c914910450580c1d560a6252030302c1159a03c0c98a4101c0b4020090ba1250207040c1c180b05103d494140f20a941c0c50344103104681c2c006030103142c00240380e621169159011103003c2c0c0c190198420b02145054041c5401e400c00d041d03100981000140554281407900c444c10b040e80e4404a0101e042007003803801c0081c0c0030301900140c0200340c402d03160541c95903100801d10840001e0440744031200300e600780b288011030f81c040018801307581d01894081011000d0400e6807503080090701c002501441038081080d6108010f50103a8143d515004043c004464140c00916060000b07001c0688102008032060002650480c030680348244910155464210340b0340700d07001203480858040d61140c1110031082521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280794145 1250 280792895 280792907
    0x2060c0706030c0e0d02090109050702100e03030708090613242903070b0307120e1c08010906060203160f020d0501060503010f02120414100c0e0916080703020d02040b030106020607 79
    0x6404c0a13a040503682440b500080c007618010310034404000d5861000c01e101c64800c0c0400c200344003050009022498259204a5036640122140b000280f50307440030800348000862075501495101c0500c5020b0840c544410415020061050000c401045001c2c101d00304d8a00070110060041b064465094210b01d0503020400c7c02c3d0300b100c511076000100c0a000520071241170300d8001b09149407403084582010446d90080008020340c0031103100b102ca00b0025451880018001c10410369194000340c1d03a0b4012400988e905070003900c0c0960402e00c10301c10301214a921078828140a02d11030f11600e55035070045a48400800ca064a00d81d4407040240035a0400f402200309802280104519009001107109070005002d00014816880c060114002110400a02c0b030754040c145410825007003004d070050592065000d40034041c4441000040e41110308425144000c852912190f000c5d58038604100c00944c80508035085240d404c0c04086a02e15031003001e903010341003640082c242418104805050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280795395 1250 280794145 280794167
    0x603013501060b0d0b030d02120f070c03080310050111150c04120528021e12010c05090906060a0f050f040306020f041e0f1401030e0a06090c090204030503120402060c0706030c 77
    0x7e0340140c9004821950008441b44403041c030180c141e8680c50751244204c901d215030782c005410386419010110900000000560094028222100c0116a518015030f0140300000074a002a002049aa1145034001c2249603106980001140c582600d802260001e0b03000c900e02175486034030142c601022040a40310565200568080381d50f42500030b5400150703d1001007050001d260841d00e185015038903100311300568401c4070f800a005c07499801500601d04c5c1c01c00082948560020b00102c4c480c1d0a148040307450025096840a440407402d0f141a40e0f258003280e62000da0800c10031001000c83e07054070250410f00752288403186d0715403420707900c583d1a0086088080101d0f0201c00304202c4418012503160803260000c10100d0100c0780c01c0016030003440035890000c861b024120b0b22a041160790f034030143c0752500ca0341c41c0303155054490b13400c24201d0003140001400c03a40108001250207402c003080382d901038401441d541c90600e01e8140d00c0d050520315071100e400310313444801c0091090740001d0201c1e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280796645 1250 280795395 280795399
    0xd0207050a0602010e120c010b030607031a01081509090a0c0306140610021c02030f0304140f0312040201200f070f09020702010912020604030507030309140603013501060b0d0b 77
    0x1103c00710100d15866040c0348941c46c07070010001822a0380070b0401c1d0001d4055040040c01d6030441c1c903044174050003420007011940c0480c94504000c3c204c80d070080600c14054400700341913031441e58404040c0680c7d104042c0c44c40d990b5108415a281c0043c017240ca01c1005903218040224071161f16040308240054040c003200d1180c20640c0043c506186d00144004210355820480c40395404c6900d801c0e42503205d07480381c3c400908800400c001c00d1203da00300920440106000701d407500c1269810f09a128000c000c56417204540080c04180590f2280480d07080c01c00c5241c820308404c440091866142050000801d0040c3c1c0010070308101d20000303640120010240400294a00460390b030000340007481c1d5004031103c600e000103500e025034460318291006584d012044401c1d1f17640700c0c10098076034803146c42005444540150320300000d040c01d43c00d03681220302c4150120200c04801c031040c110b815000358406c004010200043d00102030900450008005505d007441c0e079030405034246000d540e88000854 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280797895 1250 280796645 280796651
    0xc0a0501030603050a020d210309120c08120403021203092419151a0d150e0105100c060606180503060f0601211b1106240102010605030d0207050a060201 67
    0xc040307100400c170100c40690407504d0321103400007864169048000300711401c03100b10709081c000c0390f45a00359008004080c0110780402c8540e41d00d0320200d504a6030b81d06e000305202d02c184520100d4040041c006500107200340141c81030042144102907640e001101c01104590010b000d40b5000359000710500c1509507035002c18911807030007401c03258140038000d0504509a41c1c420941e80c249441d522050058071200d0303045101d155401d4505513044c0c001c00302003a9070341e1030064042e41080482c3d01c04801caa903d560304131000da107400100400c0c0d0b10312901a009002c25010324000080b0544618405040d56803200300c0b8600c0350160090f484501074004600a92103e0700b0b00403d0b07400065a598010070902c0c0075950074081e001040c80801c006070a041d806818812a60f81100306032451818180183d40c0320140307824100049a46c403038098580d084d041c1141e203403c0381c3c500d4017540c071590038001c10b000201b800da507900040307807500c00c1071083c0d0801030300016010300451910800110040c403032071000b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280799145 1250 280797895 280797899
    0x607030c050a1a07110d0c030c020a060c03110607090b09040209120d020d11100b061b0309011d012c060301080f010b010c051510090e06071404260703050304080c0a05010306 76
    0x2031b0b90310341500c074030001031280308890034003007501c50303048006070660140501c03800d03950b1141c3c0613090101450302103020420000050350200e50000303400d0300c6804959620b441c082d1600c56040f105500800b8000c0e08070b40c080040590644511480e00c172408512001400307450300701c200090400c404080d900d002c10042c086a002581c600043e0101140001d001c00580d42442c500004d0041c41080000d403814007080c02e030402a0140407001d803481c24401c2c2c071828000d24014804541e01400e45091601003000342e0111002c40048103076048000d0421000500d0072900c450014070f49404c00d07403000d1404e6100100c1d0702c5030f08400b8001c400045c4000e00b2f00950400e015998070381c07103c01c41034440510510040000e0040441c00c80202c0041881460801c800005a10456160f100c00c4584c007000c50480044044804070300c0d03088404881c1c65400203c41d981e03d85034070503030900301104d600043d84079082011020a1080c0001c1c80242035031401014010151400d004601d07807039038045030500d4502401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280800395 1250 280799145 280799177
    0x10b150316030b100f09050609130e0106050a030b0a0c05030903030703020a0c02130e1203010f18271b05011b03030f0e07050a090510050607030c050a1a07 68
    0x26640c1001c162100141e03210500c1604030014508510199841003080c402071400b80d40181030031600d503005596141d401901c440070321205101d04664541c0010b160084032411480e40d134003041d40c18001c07600100f0850b0303a0710005003203010302e9081601d07191032a5007403003101c400f80c1c40382d081c03c41c00a0078a203003540341000ca00c80c0c4a0000030481e07001d0540010744811041c0c818825020301c19801800700e40041c0186600000a000d00a000189441075185900c0c0790781c06a005e40e4129280c1034901c50191741003424500e003401100d0640e518460311101034030309054251091086200307161801010200a505009072004694034500320311038071070380c402d0186980c8981c01099000744010484442c068503c0c0c110000e00c244203494520740d1504031900c0c50000b0115200040360011a582c0300d10341d48994604084030b8064a52140440e0b21100400050601102820304603010342484003080b07519403102410000c81ea001201d1544d180002141d04084d03510035290486181d00e400c0c0366000c0c000790 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280801645 1250 280800395 280800397
    0x1f0605010507030c03020a0606030f0b130c1511030301151b020306060103020a0c060c020c10030b09041202100e0601060f0c0f080f0403023d120519020c0a05010b15 72
    0x20040e007000b40c80c4201380c052500030080512034540c4104200401541e9043c8018104914202101c0c0d200c807440c00f04410001d40110040d99035000fa4900d020711b85031054900320013121042d00024042091300c20500b0010030b201540c003c08280700c801400e550300020040140c5481d8261a0256010280300350150300d00107101644075600b804c0059442012003000d44080c0f4803260024401410800004201c0c0d5010880030707070082090b926500c0c1c130701c0820025400e482e9403005160300440c3c0c440010b0b0108040c0c07072813240010100d00680d4550f000303042c400015101ca400600e41c0070760000340100a4903600181003040380c20145440c07441e40885a80b145600b800001e40a0040032000c034980c8800140d85045a009517802440e00f080840b101000141e008141c00106030400c1c0e41054405920691100c881c1038581c1c00d544882c143c000c014002001000054500d40342d841c250000c140c142d40f1a4801048038000503801840c0190251400509407043c4c10411070184007003e04440641140c50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280802895 1250 280801645 280801657
    0x1060305210720040c0207030209010911090f0607050d0201060e07030e030a030906023115170c0d060815280b15030106050705102306040e030c1f06050105 68
    0x26030300a030040d243c2c41004a14016100c0002d52040c50030b02d1810b00e8a80000311b15084034801d0b580d00810f0782e0303200712a03000c40c0c03d219000390507054100000b0390070b85001030380080e003800014001410a00c00f40c03152880e00d080709a5030320140c0c1d0350700b0f400d0001001c514403099010351b41d403038140482601c51030310302d45a000f40600c40c0305041d00c0d0540703901081416010b99583c1c0580800801c42d2861925514544e42c03507540002510507c41200420300c040b0f034518000421180781c82d016104030304054407594160009000d0300302c1590920002c070300c0d103041e40100d90050044000600347d60703441d07580828000c1d81c00350507443c4001200240d060a0420740d0312407501003800d030400007074583c7c044021850f44c040300205030845600000000c03d8107600b1402a040c40c90040c422140e0000010b0343c04011244e10030710310981c00d100029141c4000321450030b100e510080180c0003041160000100720f01d10b42041480000a80185080310640950400c07403c030411500314040c0031b842c1c600320010740980300704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280804145 1250 280802895 280802903
    0x10303030e12121003050d09090605030f070302091b070809040f1b0f0201060b0301080d0906050304050601050d0f0f03030509010b010c0c0902130e0a0213080c0a23060309010603052107 81
    0x3d100007002d0301c01c02003403140215088030540340704039050400102a810740b4080e2400440c6400740108031405c000480131002d0400100925240b821a020010a898010300550f00b203c160a02d105980c18814003602540d8070403400503440e00c0f1031030100016109002000e907100d03860085480ba03011034055058501d40d4181c10111854042e5000c200d01400700e94002c0004500f0000c00011031040020321195810956070320301e80c1e01c070303143c0c0000c640074407080d5400752166001900601c07491601d086441c01c51480390b0055404221207645040e40040b5403c400d6003c241d5420420102e82c42c00c0c0918060303d6024030b0881141e803810381c0c5005807403516001c0d0790071055011030842c54900180c00060040c240c0f6035140400c62804c0203111019500580b012501030801d500c0008104e100000c403445901c5004000c07110042c10700140004107000301200c0c642c0110840305199450300c41d400113600407407004002050040c00c2d82421842c140803083c41e4400701c48441d48580b17441c0c0324001034895080e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280805395 1250 280804145 280804177
    0x1150e0f040b010504020d0e1b0108180304050907120f050a0b0315040602030601030207140708011506021c0212070c030210050f12060a051c0312060506090d02030102070602030f010303030e12 84
    0x19087c030701c0c80248403035060701e981441001c80300801900c0c06880c2c4001c08400360b89541c080d039184441d44406800f0246448115441440709000758508440c11701d81c803004d01d00e80b188108106000b0b038801d40710103200c00c1102c95543d00510820700007a0103001481841a8024920801000c01c407514041c00204050071003a40417000c507110b603102c2d0b012140040d030042c0c89440c00224114070140c8654092084240711340c07800c0c0100b80d603030a02d42020012078810b500030b4400c940818440388074498210b26258114090b00e14591a4943c200303010307004843c0124000d8521500f50710500104000b809000f40601005010078240000d0314021111003a4010f100103840f80ca070400825050840303a0491a07003d45038203a800c1c003450341a0a0308052070f02030765801b03984401410310003003115a64050107802c2030f0100309035441800c01d0418100e1041c4090700040c0703840aa0389034841203030402e8540d980c1030340e03525004106056050090b410070420840103860365040340c1c4204401c41c40780d40302da03144110b9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280806645 1250 280805395 280805407
    0xf0a06050c09040603050d03050a05010303090e060a0f0f0305120421050a1703040203060615090420030a061502030f1c0e0d02012304201201150e0f040b01050402 71
    0x902a402d0b10300548000c1c01c2480015164503015484006902c101c100180c6004005190210f0030f006003412203030503840c2d41032150704001e03c0e0201d01d0720080c40660050000100011010b41000d0040000c102076218440302e603043d031514605259041c6d00c0340f1060582800306001d0401202d802e00841c101c91103000300091501d28000c5c0c2460350b40307140600300c00b1105981e03040740038441000358840d910840c01c1e59156500c406c20041c0c00141044110904c000038403414030ba03030800d940611002c45400e0807c5400b014040c0c03140c0115031080f103030381600584400040000d800d012810843c00385150018609000034030811404501aa40700307004c03c070790482c03000e85c103540f0f441e03111540723a41c05c01064807171b000024a00039020f040c6050610381494060010713038400c1c0080c0c00c07149018560000c105101c11032588103829600c0542117120f40d000d04000f140b6144000f0900c94803001003071081c101d54211346824050461204007d1503820118124000c0200040101e1041c50545104550060300d5030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280807895 1250 280806645 280806661
    0x31b0702010c080a090f0509070206040b0604020408160312090b18060c03071a060307120f020a0f0306230403022104090207110913020d06110d060312020f0f0a0605 72
    0x18042d194003030011200050807280f0b8561003014102583c04880c0304490160ba00d40500c11050070480e00800160441d001060004180c1d8550b5500128000c2c80942813584400007941807500e10044001101c5810104004002750820141020902814034407a030600d07101485440c0d100d4000000110701c07100b804c0c00c19664585003aa120000b80764201c036110390040c507010141d41461000d107000c50030003a0000304030385400118601642c2c030400d0702c030000b200c4a07170381c0200f85400b100b000c990051050340d0214000d01114070b2500110f0046a001c181010442d22580c130503600c01c2d4100c840c100d218010131020a07000111014081c0315014a0840442802659965070041d90049201140001550750900910a0300101c074564111104d8200b5111804444001c0f48003030002134011100f84061004100203901140d11005441d0000380f40c060788000c41c0e022a191600308665400d4125a41224240c2c1008000302807000c0c803006120640380d070b10345141d444011840c0140b10640750b1000035000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280809145 1250 280807895 280807907
    0x14120a03050c030d140a1a0f060319020304120305091c0f1404061d030601030c030b0a020f03070306090c080705030a0c0306050418170304080a030b190f0614031b070201 74
    0xf040e820081005c02250344d10014080420f96400d1034450802c840c414a00301d64590090069000503e20410003010009002e202c1c2c00092298221207640c0120181524440c0015841244036000d040b82224039040060b04680300034100d099558081a4480e00000880a004144002034101460801754000c0101c928003002c0300310350b01080c0701040c00103186801c0340c41e505954000800d981100a4010103040d86c9420901c809418020408000c0000c903071081001500180f06040161400c004120844410342c81a540d01e00001d031b4480003048801543c0c82207510103902442c02e4081c6051210303006107540406003404994503520200a0a80c7c0d020303a00100060002910601c90092640220780311034100070740c20386030f40c0314040c1d8070000c07200c008044912507a0f22000b07030781c144480344504900070441600701130b0300940a0740c00c0340900005840440001c16640c03032880d07122070414030000e03c9042000d0012078806001c3c0180300e0321070801a0405011251458120389548040c0012505 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280810395 1250 280809145 280809157
    0xc0a030305071e050601170f0601090207150c0e0901050d1109280c0f050a021009020607020904060902010210090503090f061e030105090612061f0b120114120a03050c03 74
    0x54a1520320315604020020030524100d40c41042c0e80f2003d82c11f01c00340f031500c510321040482d2a542106005101208841e405045a1401400700c9508030200e03402d2007007105d8100700e0180102d4000e8070a0496440c00725851f9002d028141d5503400e030841d5580d00e291000e43d81c0c000407445000004005180800640742018180d8480d4244028012a11303058000a1141c4e440160018901030b00c0c8000380c0740100c044501000c22a8001c0c40f02a209843d03800040210843c12a4010400c001c0e00001d40d51700264140030364010100001c0d00c4c42c0c9480003a20301011003042d01401e60600c244240850300100a80741c1082066602d200303414100c9000030103a114450031490030039aa03941004c84110380c1c102850695800351001c4201d41c4400d010000c86699803001d102e00c40e80310b000002d102c01403c00002000d1a450203003501311030b40350701112080c0c0d04012600c031001d094110041052070040c0c2a4600100070607251681200b0418494581304c02d60302c07e001e020710000040348410404c0030822150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280811645 1250 280810395 280810433
    0x3050405030d09110406080609030f0c031b03130608010513050406020c01050429040804060e01020705130b0414090319050c0312071205071b08070b040f0c080c0a03030507 75
    0xc01810189408200b04d80c4a02c07090f17005502d0004041091480040c0e136902440a180007103041c200e26400c1550158003190b0303001214081405010f90b01c855005034240c400c0f4084018580b1080d650fa028076424400e540705400300421300004002c90b807114146000301800406000ca02941c96090800180c4900d1121500940c40c02c07040105106030121640c038514582d4480700d03000e03101070b40d407590301c464207480c05888000d08100030032030240501c2e60030945040c180156038030130380c0c0c1e00d0014160031401480b81511903207911101c90245401c1c07041d14440901248080c16500b0840c0c031143c0d60b030280020480481107000b460540c4c031343c0941d00f51085042032608171b0f03a0740d4a004c0600d03a44104152028408100c80c107244100f81c00030342c02802d118104968407055840c030501d420000511200ca0140c0d1140020802a40402c0070300c00300c148214041d0300c100815003c0340c03801c10200d29150340000f000e030b0002d4510700071782e40d500d20055040700c2d0140f900d191119800e052030f04072003068100d045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280812895 1250 280811645 280811651
    0x110301030f0209010f0e0708180609070927030302030603070321030c0309020f010813060e01020c0c0102190204051009020307031a010f020c060703031407050405030709021903050405030d 82
    0x20003031401c640c9500544240d030220401d99a44181c640c0b1140d00b40555400d8042c10400204054410f2514560103d2002440303146140c00034902414a0700540c0d2030091303604141c8051081d031040f400f40314402c103d01c1d048041000c403003c46c00714070706840030001420135800002150303441d03408025443c080d60300080010340c14200c022021880201c810320b20f0002c64184040080e0702c5002e03110f4a000c56401502041034020000700449007184024080c800301c0c00344010080c0420042c3c895124500141c2c000184d54124684400303150025100c207031030466204002240b02500fa00d107814503481c0d0b0554000c2002d4503888100061041a60401c0c18011301c08000c03c111b0380ea241d04407050501100302c052002c061520700444070081d0f0143c010b40941c1c00007050880905200000340382240c0207260000d521860b81200c0c00e5603078015640000040e501203800c1c0641d140078055400140302807081103180c4402089158010707802e00d25090700b8107035a000003806012003441190301080b4001810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280814145 1250 280812895 280812899
    0x1a0408100e120301030f060b0303270a0f08070e060d0210170105040216140f010c08040b070c0b061c051c110309030c13140c0909150906060a03110301 66
    0x140051948680c01d00441c802c803209841c00e002108102d9040c0c03030b0009600010305449496403405441e492410580510040042c07040040c500310b00c0f6210050459050640058180c040112070100da030000d80610311031000c10001a003001425104172101810442e03000d6882100049800d414030030003035000f94203c009070b407034207500a9824031002c513123850800701641c81b801440220300880040c0d140f003121844068000c030344070358051200148240d044421503141c00e42c841c2e00b50f13410b442400001c601c083c0203000400c181400855400792803403800384000c981c1c0c3d8895003805000601542c4c001c00d508108418042241403254400940107011580e242049a4031103c081d00321681c540e0004203484442c0b420840080100d0b601540020300802034015004108007082900c1806901c1a035a5407600f50009802d1700041c1d849180c0780b0503095185c0d400b14050000b1b6540c000c0100c4111026540f0b03c0c6103d5841d840c3c0300ea0003100a845458403800203142c1070b0000c01c88045c2c0d54604038008000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280815395 1250 280814145 280814173
    0x90f04050a050d0f020607081504090c03020a1412010207153308010b180103121b03080703050a0504050d18030b090c040c0f02070b090d021e2106011a0408 68
    0x7404c01050301035401c440255403104000c440e41c100556215840c0e02c0d050480851a1815401c6a041c0a0080d55900f6003941d03646c1c000742c0f080c070640d8803441c900404450072404130b140c00e00e001c0300c480600c40005d5281065503554070800001240ea001c000ca6900ca541e8844241c801c0b556415101109040c0b01c00c0410118680581c610244100e040c04d42c00c1c41c422054070b003007a0001e6606880c44c100c03144001d909580da150094142c0d80d540c0420080c100c26629131054148608000a60080c0c50700d07810f60802680080070303204010641101281000103000010b0380000d23a40355030f10890b10f450b44c4002100c402c107030400c0705107030300c080c0c41c00c071090341800100700020464858180b01218200920740900354103441b5074200700c45000242e04020f00030403505400d0002440440c41c01400841c003c0200e0307002483c0c0d8040e81c104001d159a02420032811404c021480c8421b010600000d10011540310f5141a81c1c0c0405004039241c0d2041182d03003001181040040d07402510b4003406640b0801c0c84510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280816645 1250 280815395 280815407
    0x3191112160203040302061b0115030605010501120605060a1101020f070303050f0609010807060309020f040c08191a06071103150702010510050607240203070e03120306090f04050a050d 81
    0x201d041212501801c52800d07103000000b100d04695029110f282801c6003034058030710420216038065900e54a4504045040480ba04584040c2d80300300c40c00191941481c000520750708899100f5501c03113207000001e0100d581c0f1001601e920681901c0d00e40d08414851296501900a0410300606e0140c080784000c10150941c100303d11800c0c000348182d08135a03410081001d5040203201c1d0f90041c1c0c01081d810f1240b00d200f500b03c5c07980640080c141d40301e128030060105084844100d2880f0005915105005140136144a849080303000c0050601031141640202601805510040e80c8101c00010b000410003008144100300090020180e4507400d254940d2107181e03407002c8860f41c005510f401c000550030944283c0720003d440019007418103120f0719030f83d200b4100e030100218a4400425120002c0c007524070b40000c511807600c80e9aa9a0426440403d041c500207035042a8040141c080c800c00c500c5071540340c191544220300c0c20400c001900c643c06c106091841d01c070f1001c1c0c00d5000d48145610a560452 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280817895 1250 280816645 280816651
    0x118150b1201140c1908090c0307030303020a020c010e01090627030302030403140a05060105060d1d0f0106120f110a0b0c060f0a05070c03050a09051e01030b0603010b03191112 77
    0x501d400c0720b1075030703107021092161285410b51070361740b079142804441840c4250306d400d074016116003c407a01c0c4031290700028903010083d44124006034000480d240d085905100d81c40c0f0701c08007800d01c4c0001801503c00030707108861034012a000c00a01800a00700d08025618071080042c092001414490702c0303060094503135000d0b010669562903003120751000d0700f50015940030741c3d98004005e8038035642448204140c0381d11207417480c1c2400d07807181c0c03170f081d510104000d149998190f41c0004140640e0990802404c0d160241e1000550803144204031020500741418581d00e82da0000c401e0000104d100000745441c40d968100300c00d507000c042807510202c0400141c2a0080700b0240d40e0030540c0d03681d4181402034440498245001030841070034500040d02034009007449003007034101064210745507004200480b000101c000705640303103030180a0665805100b0310f0320070329055802a24542c141000700c10b6074880076103804405034818540d020222415403083c031001c01b10001d55680d601c07405040300c14400c3c0507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280819145 1250 280817895 280817921
    0x4090603141204180c0507060e060402090a020f03130201030e030403060212010b1602010c0206041508041709060406110c130f0506030c18100f060c0507080118150b1201 74
    0x700b00702003010110902070700c00302c03803502d0a0041010151124440504101d410f04010320406008020000d031482c0918605000300c0001081503107054010040010005452038800610403c10038030b0a1030710004a95106030032503005044080e1502c0124010104103072482214000401c0c044204034203a0002d100c400041480002e290742c98403130003102407080b03031805540014400100700055004542810485000400c80f60400d580e0f01c480066039601e601d44180045d040404107c100300f1990300c01d40d501b54402415508100c2d136480814028030950003100c0030b000c01d54002c464202020081003010f10b0703001d440c51041c0328072050104050f15248620000f65818440024111300f000902d11011850040200c81210001c002502d815003020740030200da00183d0802060000c030b42e100d440c00401c1190703101d80110340f0b1418200e0800c100c94122101a0f410301058002d00603810584151090700310200f6001030440f03e04120040845110050704240c0444024000d45010b6210301c149a2078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 280820395 1250 280819145 280819153
    0x190b0d020d05100c030b0a0915150906030513030806090901020c0712050c0906060405012d080f010f050603040210110a0804090c0c021807020a050a1b0506032404020409060314 77
    0x10b44d8801e800b034807488640590004030b8424104032910309604008404260504200c0745c0c80d40341d40c0c1140e0019442c0c0c403645d0114581203010003620740e145c815541e0107204d405100032880c50703540e001840c1201c0544000e10607100c00000c191492000e40c126800c1e85413510407902202d54422203030851024104003900c041c0244010b13865a4100213120910a000083c07001e8509428000151003182d0300d541e24034a20301c3c0300b068441003070401e40310303c00c030003e01506e0f1000c0c40d2400c0c81c03c2d28a40c0310140c010b07481e070000c240420030003030700e0b0310069980141d4121000303001640e0b525000c440c8128080c84000140c81001c20100c01c1c464010010030036101514001d104c00214528261026071100030000c0d00b084d040c949071081038a00d0303401d898001d00580b0603074000d40314a450f207500c9c2c01585141500d42d01015021500c1c101103041060004120640d451400d500c0e118400c080c54420405210301d601050302d8a0301c1d000d54681d4100c80c00351003c1241000b94a032031b07050142281c40503038406141d03072003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 280821645 1250 280820395 280820411
    0x42f010e060a1707050f04180605100504120f0f140105070516140c091801180222150605071103033604020403050a060f05190b0d020d0510 61
    0x806608507260a8003a80342c0c122045200f400360002040018180700801006200c801c03030400e0300c0401080146071844d20110403a05144803442102e200394445440384500003507050003143c002c030599045460b5280c0c0710425a61501f46090000300c942d80003048140e40c040b90004020381d260a4000c072510b004000c000d15914103000b55410b100346140280c448190703240d5040003c030703000c508601c0956528107035040c02040707002260b40407106035400f002d092483c605401c001c103424400d4441c00d042d00038408201d040c0f240c0105601c6100090b141c55102d0010b03028101d10019908001003028015640320300c015640d00c40104550419102160b1440800385014010f140c000244c640030300c481c2c441d03c0403500310016400200309415500382c11070040160ba5031400d69603440500015401075028100e0000d09181410480d03001c03420300c880325841c141c288080784940600d040c0030400c2c05000050301c00c0e00000010340d8490300c080001e610284140124082110102e014040c0160403801404111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 280822895 1250 280821645 280821649
    0x9060e0c03120f0c06090a030e03030a05040509150a06020c01110f03030601080411090412120c200307021c12050f190c050109060b030705060f04090203042f010e 71
    0x85084114941c50760007a802078203041c11441c002d00001c062285030500e0400ca0380842801c2802c11100b607012608402101824150414a50b015000c000c5016616101102c1c0e4050407901441c040c49004200c16000540c4800b9002d4401071f0020b401040118641c0d40e0300d074002c1d5140b00d4840a0b50000e001d0b43c0080008200001e821009441d00d10b001e03504540e40c0d90011184080c00500555075000440c104418985558880c24000c42c01a20300204d420140d4001a103045102d51a50410515002400b41c3c0c02e80d104990140300011984e02101a403007480b00285580600e039000f03544406e10025445030507a504400000b500e1141200786400340d039075502a581c85c02406400000d0060400c2071200c00c0400041c8a10140560705007000850615103c107421030746545070884000e42d0301d40c600c2c21140380800040004000c101d6800745050a28001e252280c0110b115002959401001090400c84020b860214801140c6405840f4230030043c41c2145d82c03001d101410380450b404242803040d40c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 280824145 1250 280822895 280822903
    0xc0f0e0f01030f03170106050901170603281b09060b0a02030315121501030b010f08070b07061e050a1103070c0f0c0504090c08160f060507030c020d0609060e 69
    0x100381145058080360701e50703150103950681202048003005510305415655118010300c2902030f129a0380c5482e100c10450001520707280e088000d43c0030001c0c1e04002c0001d2aa40041e907c008106046c401624110440c010b501013540c1a4100034058000d14a81120800c0359a007110700301d80990398184001170352640c035406a403043d903008000680080000a0310a550003907100b60390200508a0280072244041c00c1d0704040800000d614214a01c400400c2400000c0407c0f0f4058203046050349203140c544640c003650b500c0640718070600e600000c604001030018035880700c91045204a844400001c9101c244001840d045501d40b58051a14600242440c058010350b4030800d01c075240c48070a00b10036214846c0c8500402821110302003000c8001c6500e8855008000c9450301c1003c1c15001d42c0c0c10204040d05040d410784180e04910303038012007081403901601d1190110742d42c5042050380c41096060440c0c0188101d0f1020350003110b041c0700d2030104a215030150300d2042c012901000f500280520389521 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 280825395 1250 280824145 280824151
    0x60e0603030a030e070b03011511010510061101020405190303020607020a02091311130204090b120d05031005030a150c080910020a0e090106031d0307030f03270c0f0e 73
    0xd40d109008403a24035020b980300449401e00e140490715020740d591101b401030350098021004140084c6050071310140c110554040907100301009005a107400380c00503512880600c18141001350a05920100000a604503800341030050400d550600111141110040c09448101e00521809000131b00c074910100d00070041c150300820703401341902e42c2c4003014107107500d04406507401503a01c1c14050450340d40190000e08030800c58005038881f803074071039160211a00b00c11458040c2503080c1140f01c0d880c3e40412000e081d5801d0b424459240d4a410b05684069101500441d80610440b05030000741300312684501400b800d9610700384a0020001c10403030f84400252140c5100768882541400b440c2400e0300070b020882180e1034603140b0304a4003030020f0031640c020f0384007038082039a0700740c260141d0000006082e6088481c1005600e09161550000c0c00079900418800c105503449000034914980301222808100c611540b0360a46501804e0906003c10a80316a0040f645200b070001411104a42c0c2e40384 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 280826645 1250 280825395 280825399
    0xc030301121407180f090206070f23010204091107050c010503070c0f1a012c060d02060304060515041404020622240306031e02041e050a060e06 63
    0x42140d10708500707100d03240711401045410b2030450300425600081005080c0040c4150a22081c48a04203403034a01142c101580c50341d900c1e41450b2400340584c9440c011500903952000800d008212039040c801d8007070303c840440c0c80100042282100007048150090000d40e21840b01c204503155030302c8a00c00c400e1040f2400208650020783c03004c80690701a4000c1c0d64007440d20f007400040504987c0d0358403005400e1660450780d9072a844107560082d40d036102942d014100c403c03080b0100c00b00071075451029100c04960550354205910000b9241e8441c1a81e00030782540c0680341c47c0c0c0300d0506240080c050882128030f08508082c1c100041b41510f098040c40300c14248080c0c03184015100c54090100301e42c001030710b648100f101c401c0d4001030030484000000081040407101d41122403070110444402c0401c1d1506400c1604002050001c102e400307103114802c0000480c1c4801000c540e102280280c0f04000b041c0d038525100c0401c140401503250401440b4590100d02001455220048128054000d44480b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 280827895 1250 280826645 280826647
    0x9040b0a060c23240c030c07060e100c020309030d02031c020d090c0f0e070309020f2812030917070b0a020a020604270b01121a0a060f02120c03 63
    0x40202d00040400f840110261411030b01007400d014030300c0e1030302c1a074450500c1340c0344818410f85040819280401d8005003060b40c0030b40f0f182041c1c0d90b03070308880c040d081c000b816580d40c03403816072202c0d00b040045001c0c50810441c1442150a4038601039103d41105141a01a000d00faa100c000c0c144040201e80790740e441c074501000e900003c8480c1b03a0080d0082d244011510759205110b07000300d10110302010080040d020034411450401407141d4100724050181010b150500c201d00340160789a134200f1903100800d80d400700d1603100780070040c2d002c0000c5902c90044072001403004500b011180c611641c9040c000d8844554841c0d41c0d001964259003e0041040c40390400b18080c00071413a00c4000f4856230f0304034130468084c10100d8000840a0380030f07038401d40f40008050f814040e403030340c0740811656008012000b0010961002f00180c9800d00031211140f01613552003080e44e4040c4c1c045418207191501602c00001d1946404000c0c00c01031501120802502c10085141041e03031460045609125012000d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 280829145 1250 280827895 280827917
    0x605090a090201030e030f03190513030309050312010920030c030f0603030403141c110d12020403050106120b0f100605090120100612030804020d02060714010209040b0a06 75
    0x1080101640314007241090b44417403074448400700401c09415581d8115041640d01d0604100036100c1d400018000e2241906240c100000000503460030100c9903010705001c100d040062415a00f184907074804038904c0f4604600206440825901010080344061807606841d00c40c1c413150840b5010490b40c0d0302402d00204005004020b00c1d440701d503000a07000d0102d03820903803a0f40d5103151500b4030340000b4060f64000060301d0780c1d0030440b00040a0303a600314184070140e000c084000c5911030041564550a008032a20f01c080c482d2030317940c100d4008603084402044100d0322203600c1c0714203015036407080e074031420710344085020701031031501450188940740d4030072407007900d000c50640710740c0c0101c81c050b41403004200d0351072402c3c2c2d41d5684203440f4108480c00360008900c042010411200a42c02145c00c02c01c2c02c482c850006500188982e8010742c04071070a00d8110704170301c00143d06200c0e112004017041480320281049000540183c14140c0003100d06001040705101440301a1030a4420000080d00007000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 280830395 1250 280829145 280829161
    0x60306061d0103111c08030a061d0f0612010e0303040507050423131e05070902040602031b0705120307031716030c030902091612020a020d11030c060c0408060604060509 74
    0x4011204c04040d0109203410010b02c080c545100c03010000341c0d4401000420807500803594030419000e401070828035010340c5c41c13680c940120408010940d40c3e803003080402085265960051100c482d2111400038400035805540e4180c4035042070f28203d803188204030001c03e0a14090150b110b1050948030001140903600c00a907100c1000a01101c0100c541d507802c89010075240e0381d0309007003150030407218413551903185060351506034507501c10340344244144018005286d02004441b07a11011a014140001500e0742d060300f44842c590140e6840f8504028403000010084040c03d8024041d48400c1031f502007411100b49075200445140300003170b500c2220100381030f0180d8402061851146000100d0720015400300d0600d80065400401e0703c00250104103200740d10484202a41d48052025420050a036801039a42d207820b1070405c050002d0360340c0000a001003001902c00e0018600c08803039550074034076400100c0b03601502071901c0300d0040800040840c10705001d100115800a040d034405541c40040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 280831645 1250 280830395 280830413
    0x4090b1e091308070807020102060906040c140f0406080105010608070309030e040c0e181b16080309160e0a0e011b03020f1b0c090601020a081909050d0303060306061d0103 75
    0x2c0500751101040e03003000400c0019004e0680c031031103940100d0792803111b80006454050010b0042c41c10744e1010341040300241c40b07a00d0003821900342d58540e20040e42d11000080d00009000702c1580c00500d0b0400004490302d0541103141240c00c1900c428030f540e101d529084003960b04d650b5025010608800e4031100710300b420741c010400c1020070b241c82c0300c909034400002070500c59403030212400d881d802024820400180560001e0700c24810340700a2600c90746d6601d00f4941c503d051405414402c004c1b0015100170800d0204001a46544c583e0702d501c80d031601d905c11085c64003030307607400c0d1f0062800c4515501c00e0414410b030314130344071054000d03420840c094500f10007030752015010f0f01100d00c043c00705812524a403107010b01517201c1000509108403c480500548680041c2068115800410f5610210315040120b42c1c1c000c000c604482c603410700e15413080d00c0f5450594401604012080712130b070b050561540c41623080d80d10840e003e00c2807554602e40c40c1d0b484100d008502446010600042000030b403050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 280832895 1250 280831645 280831651
    0xa080a120603080c100506061305120c030a050601030c09091511090d1a060405010e04030f090e010602100c0f09060e0f0a0b031503060c180a050907020304090b1e09 72
    0xc01144440d12a5900340107508024050043c0d6805100d0b09441d00443d4052564440d405848070350420b407140c601c914400c00148900c0c1d006040071f18a0b807042c020b051000c24017541010b8121000352130180342080d03864400344010384421103140c0303020411140a00031059102c0e04249010480686206c1040c004e2400044500c94440c0400484e06c0f1900c8400c203481815000d00f0b10609040b580ca003c141c10800c0090945228074900001884101e0032034a00d00d4200c3d82601d0000c0c0c0c41654031030240d402d41200d802c5840d000305400c000069096002035003c1c00f00750484000c2c00603d202c04802c1d1482c0445003041000f01388141c00502c0f582d44202c0303000110640c0102100342101100d40401c0c0c04400581110846100010400511000f07110315049260004e400a20403458110201090707800f42170b62912072610040d24040c1c944da504042140a0000140307120001d0400000282d0f480d4014850a10390b40d0920301c441c0c1051800c12038550069032101402c00032001b0740d00802029101c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 280834145 1250 280832895 280832927
    0x1009020105040e180f030c01060b16080a050d060905070f02070e181608030717040b0711040b090106050901030c1110020708040e131104090f110409021905010e01020a080a 75
    0xa420103144130395040001d001c404045601a41d5605034260b40349003502d405410000000808000e074044141e400c00070742c00130540114159844400c240e60444042c80750501c000c0b400c17070800d200440c46046541c4802d010311307400e0711400380c40344103140b00b070380c075142c1038030482c191050910300160703802d060307100380d81d0f000c400d110103480c0c0c005240d000d006007048241c0c010301181d07400401c0311410046030843c00c0010180b000b12a0781070928007114039a140c443c0d568020301007458030020300d00795102c40d0814880d403440100503014643c2c5410340104941c008907800760000c0d061810a071601401130302220702e001804006807650760801c945860203540020412103c0e00400c00c000035110991a190701d0054221002c01c0341400514204030140e0602d580c4028800c0303240c030031044001192201c514001e281c0c00840c4098501c8100c00041c0200038942004e074101f0103000c2400d400c07060745041c1100b0b0f520b003600c0384a8001d803168012656120700b49402400c80204102801195000d030541d85001c1d410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 280835395 1250 280834145 280834171
    0x1c051e010209061803070501110613020609100e040612021509010203190c020103063819050403050609031e070c0b0703050c060a0b0a0501030b04090f0f051009020105040e 75
    0x140001040f0554080c0c0784d8400d041c1500c2c01c00c040c462909002641c0100400d10b0305104241c4a0b17283c240d10f034400944070044c0e11081800312400c645600e02651808240100380310320121804034050840900d114805120b01c2c0340160200c2c0301106e001c00d00000383d4001d051a8189042403459500071391280c00717180e0540c80184608503400400d440c207500e243c440b60b038490782400074070310015051b2800d640050348640c0048076014000381d11080c0b040749080035132030189040703018494a08071500c03c0c820080340a84400d038030500d01d6904000100201d17442401190220f5840f00308454680c0201c840070300f11212450308a01c480011040980011030142450200341c0e541d800f60500d0a505c180d0003100492000b04000c0c03816042841415030012103070b6024025100000c000400800007801034134141542c0310442c600d55100e0742e00c00301e043d075400300c8680c032015450304250a20300224002101d0910803034a05420001d041d01850042c9136040e111982024101503450410b200018040090052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 280836645 1250 280835395 280835407
    0xb031b0d061d1507020c0d120c06020a020a11030303090c01140405040c08071d09010501030e010e07060302070219060c0609020d122312070e011107060801051c051e0102 74
    0x91140a007030350804007070b005000002103202160090400144000d06640050390204c240d500d4100120105942c01080003040c2403008905903a00184208080c001600c0881c40010058002908082581c040e01c610740d00c104804040503524842140ca41040ba08003404c0307401e803540100c25041c50740003a40e01c0c490030a51135030007150481c0c840c424580002030100003030040161300020038000030344c00184c1044211030000c2c080b4280703001c103124071410540e603a5009040340c0829400b40000a42c840f00f039807501641ca44d0024069013007200103a104202c2c03602182c45da4043c0009040c103e580a8807400e071024225112100100030b0700600360780200c1001901400070700711120410349090319495592500780c1c3c4011f22a401541c101c820b548090003017041e0313104040d155414ae90301c80d205141000080d510341004031084904100541e580c0e04c01c489010603850f401040c018142c0d08140c030342410707132000100050705600782c0d0310000c0d007075800c520341280c4001115205e040c920802c0c2000545000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 280837895 1250 280836645 280836671
    0xc0d0243171c14040c0e04030806011803050105090c030d110703030f05090301050703060e07020106030215030403020a02090405100f110d0b1912020a060201110307081b07050c03010b031b0d06 84
    0x621400040e03d95442c800c1c081204000d100c1c1c01041c00391645004000f00e61070948e5001e003400d403001e0803541c14400b45414003034904030005d0010000d150310400a02160404110b0b480d42d40140445041c0b20340158660700f00c50911444082d100d0160040003409010301c2c5460540c0d403a01400f0750241007140c02c00803441203841c2401020701a103180d5130b0001d1540c0c82d0251142510302d014000c18116410203104001695600b01c9010380900b00c5200c0350741e40c1d119403400364545109440025045140321007003009002d4007007010f074640c031500da00c00d000070128030303480380200c600c1400d03400703480c0070240b18190325075007140d103e100d01c80d001401d4100790020541581d12a2a4242c0c0403024004159100e0401c506080b8402001820580000c2c0401444040301800a0100038840020400900b0005030846905400c04124582c8460407a075581528103001da100c100c0828168001d40c05c0c21000c040b182000200c071046c400004410b0703161203850408000e1010140081602d1080d140c0c8400b031004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 280839145 1250 280837895 280837901
    0x606180406020f120403090602010513030e211510060917120d0b030c03010216170f0a0503040317010608070e011214010305100902090c0d0243171c 65
    0x511044c0310b40d00b10f00d1406140c002d0051000d07400c450f046904140500071009900004004025494140100b4040c4d019003c40d150100490b210a5240182aa291400c20000c14a120030f040300d01014081d55850300c010100d10320f540e00c80d96001543c0c80d03a080283c04a081c0c8180e10041201003521108850200101e0f52500300310880318110390380b402c00f0815803404000c400400c040a030020341c10201203483e41000072035141006003107008a400b000e207091410300c0c02c41c3c58002c80d122409413a02d4803004014165003080301c04901090912981c07490220701d4860b950304988065643c4030080e9030b00441200e111540f8221135051000344220300240c0601c6d0300505000d001d0312039150340c0030740c590b00f02207107080406400d445089240c074460f040582c071010070695101e19059030312580e0b01c000c1c08040000384200d141507d02d0407a400c0b52402d007904d1140913892001c2004a68041c0701441c10003000412181c0200201034801c2200b580e201110200b01500002d0700c0c0508030a18488080410026 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 280840395 1250 280839145 280839157
    0xf020f070e090d030605100f1116360b030a080409230c04050907090b070c06080a1406040b0325241b0206040b0c01050a0b030606180406020f 62
    0x1c07000048100052400d08204440b10a41e5a240900c1500c0c60b000c08100c1c0040502000380c20002d01c0030000303486c18012155601105000d1040360064050710058820440c01e40c001c40b40b4030840c0944611070b105010b148446004503102000e001d4540303142106004001d0807503550f0f0503026040034800840c6204c40604020f103c1c42c080828420381400c0050119100031f840c01710071074191400d02413401c0134401520709442c2c0c1540c0e072290329115002e090700c0b070400c01e03407001000c204001410350070401d4190029086900310b1f1910102c0351140b8100000303403a1514203410041006c240042c2c0146425000303000160f4010f0700303072184003050040b80c1c09030b91000920b040c044441d012007000741045c2051000740516501c2c0d0800d00f8201516001440c0404000d805005c40008011400540d0340d60b00c100e400800110019650390401e03200c049000e86001c81c0d40503e00c5184c28448545800c002c900e480c8101d600401b46900700d0301d04803045a90150190064500d03990a000f180790307000380c034002008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 280841645 1250 280840395 280840409
    0x18130603060b03070f030302070306200301140f010819090c05030303090303010807060503061e032505090f130201050a030902090106080f090a0503092403041b0b090f010f020f07 78
    0x5010880361081c189011215840700785c00e201092400c1011039400f03d0660140d0358015800300e894020094222250725103405503054590000000042d86050522050f0019800341e802c0d090400c80381006448600e41107031078454426440b1703003c10f10aa095480120032034869510094040d89410200e41385400843d00014150b00c008018403d0074000c1104900404030340c40c0080ca58a4600040f84494000c1070036200c3c0e0248001c11189241c1d010b001d22440c00c00e0440300812101c10201d0b814100203c0d07031040714040c00d6a44085420620300000c06441640f550903070034a04003d5500450300c3d40e0152280030201075580045200603580c4004e640d0007402c0340e5035280c1181c24440200b24600b10060044c45540d400311030032174001580032003074074035500084844080751324005071041204042e1302142148601d000040008002e91041480541001d01528086007910f03040024001d1148240303442d44600f100181403015849400c07042d01e114102d1060302d055151410306245894404c2c0c100038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 280842895 1250 280841645 280841651
    0xf13030515060a08010e0a030e012313050f1804030909060e041a070c030e01050c0114010806010803040609090b04022703010c020703110f120f060601020c0103090302031813060306 79
    0x803809140140f0208054640040200024a6040d031000e80c0c880841d907004080c0005254a0b40d8268099402c15080110401001000c01401d0021506641c00031480e10504a103002010600342004d8400404074a0090021032120076041d24848020500800803070411a84510205140565004140003071655900891890515181410029110020070401034100c00c041105448d84180d8075180242c041c180714075038042003401202d06100e1048000f9285d0300b05110002d410180d292401d040341d00160580d40aa40c0702d1880719140c1c41588544800101d5000050054040310340c07001204007802000145402464084040c11144a0442103228505049101c015040a000308030000d42c80744050a40d041c2903507618511b6516440600c0d025a014540610181c1c644c00e000480724800c0908a9a080200390f0700103a0719402110a5401401041070aa00550083c042c07155290380c160051400d00e06511402199051011441d41d8481c8a000c04207081102078440c580c040c40c080d06d408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 280844145 1250 280842895 280842901
    0x2030a200703140702011e030b2d03030a050715060914060a0905061309050a230c0d230109140c1905030c010c06020904060b040302100206010b0f13030515 68
    0x250400319648803110509900300000360061fa400140b85038620a400c8004000e0400030204800512202c4c0d04c1d250400322400101d402c680703171035001c0d036180c044541020389401843e0042c1500c034041c00404c01c010401c28481640015483c2c0800840052409030000e40d41d507450b2100360036650f00c1c00b0f910a86510601c1400b1041c200105000d014009120040c807032414000c000c5014520210038503a0034aa444251100300407042c0801881c0740c1d0802030100e2440380d071103006694001c0c0201c41400b1807082c0040d1000d03038145107000c40c0c0e10b107403c0040301040c550b0341d2841040804040529141030355992402800046180c041c15144001c117a00504800c41d4002c28010482c94050540c600c407515501e0802c03d603a40090442e20243d000c0c038102d9284142c5180c814060300403c0c407500d5001e801e24201144458404010f001201d008441c0d2000c0f4020040059895503400e000e04040348400b044413401c000f00340300080c010b0f017501040064032240e0300c0d1a4141420410781c12885e251012800b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 280845395 1250 280844145 280844147
    0x3030305060109210503040e0a0621020607060e0f060106020102031005040e030f09180703092901060e06120109051602070f14040b21010c030e1002030a200703 70
    0x40c49600c50000c2c209041580e0400031118031510400c1c0c114600c0360200d9955500300841481580d0007800d200c0036018090810945e550041d20850180c00346201d0701d851210304803c000030380c2d903c1048e00074080b01e20305455a21003d002d0442d100d0800000e01c204203002d607030100204030440c002c128a030300050706d90600001d101c81180d1a1390100c0d1149041450480610b0004002c0b5460781010001b125510741072200402c81142031001079005c9413403003100700083c40760990480808284654075882003024001e000f61550000882c0f0340040d014584014030802d0301901509014030802800503042824500c0c208006601c240c1250207100e440b2410b00c80510320301d0b5003215400c40d040c0040c004c42c80c10840c88035440c0c1014804d0286a03a8060312440c5a80c8175a401f5034015403006d8002d1244004c01e810f03000c40d04c0c410160480c8c2070340c078045807104811710a1180042d00b04880b0044e200c0d816400800001940019103020200c41d90f0320101894212513581d1154043e02040c59562641d07442c2c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 280846645 1250 280845395 280845401
    0x3061509010602030901091518030501090b0a110307030b010203091c02090604020c030a141e07020117150904021201390e0d05121314040c05071425030303 68
    0x7202c2d005660007402104a1070303821810010960304008000a01030005103412280038403650302201e032112101c100031007170110641250301058040e041c0010152074400d41002219080484031903061005c1c404284180d119800405469a051040f81d0500308076200084500e007a091141c0c0d1480e204c24001011030901d20206580a13400326000c41c00c1418445070141c1302d2154031000002c000c28101140101d851100c15245030403a151045c280440411514400e1a404810103901060300055a3340d40340104140d043d10818901e40307503060b002c0a442c103005000c0e4000c1c004030380c0b000401c43d040d500c2110900c030b0b1020740114800c900340d554801402620015200401e2940c007850a400d25082041c1c00035198244402d058400c0b812043c0c10341400d50910201444004042c00009005500c00529400c02810b6032482d410001c85603901c1400c000482e8004421031000c00e40500200002c5164494003d00c000b60f11019108042c0c1031040700062102d030ba044150001003032031014420305501d44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 280847895 1250 280846645 280846649
    0xe0a11030111091c05030714011505030304060c0309080111030105130507170c1b1e060f04060e0f0106120c050405040302070e070e1f03050c040b0403021e0306150901 73
    0x60000c000d95501044045414403580c3c0140e4062296090300c250703100d204000005145410809030b0b40c441c1c04e40c6c40d007029040c070601000000c82d07090060868480400203500720403980000c000710300d098942141a2176060030160258240b00410307000041102c002e00840c66050150440346681c1c1d8100410002a0b03d240a00420f1b500e29107010070040b95040003146003c10f40302e610080c0c0966940c40800301ca80304202460851440b03a141f00c80c0f1743c04000841284034440c0b581c92950f51140307590403550341c1200310342001010721113402041c08202942c0c4584401d0509009031410903562460702400d580310361344030700304a580e00c00c10380c402c0c4950044500b000e080d08076028099420662002543c1d081c06000d010800c00f11000461419401100c1c14048550041c005407400701550400d910801d9101c04032102081c24080041c80c415107220454040d2612082e0150900b81190240014540421140c80c440f0191642562040e98104001745c1300d07010903a5076800614108051000398041070b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 280849145 1250 280847895 280847899
    0x50607081e0304080f091210051617060402090a0b070503040e16020a1b080d02070503071a04033c05010c0e0102031b010b0d080a03200a08040303060302040e0a11 71
    0x600501000130120011942c8a190601e101911a80c1d000001841004a810040660301c14080000c451064a800c00d0b8030509000c14100e1002c500e5141c01d445803890984e081414005070000a0114074281d8043e0070250409482417105a4440f2500191680807a1040d111540041000c00000880703a0320350b0341c410010814502000203000001c1e5646090f40c1b801440d9400340c903016100000d103005880c005085035030440d1628060300c8400f07501c07000c00b0f006042c06406124404120000042c1300721384117000181d48146018035640b9004658a0b00d0142c3c04a100c143c140303004040b4074035103e42500641c0031003203950102d80b01d10700503084907401d140c144244818403a2401c403582c0c01105407801141281e1204030000008190b06006003a6200004d07881141410b070030b424011060040c4c0001da1054504024000030001d01c4080314148181c40603900e0820440610042d01c10703448650004c1c030a007400b04241e52294000340584a2174210441180c0c4604004d0046c000a650200450841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 280850395 1250 280849145 280849147
    0x501060c0210030507121b0305060406050109061107080d2a02010e01030b030708030d0219080402030a140c0d05030918130b1b030c09040e0309090a0e0304050607081e 73
    0x180c1c1e000c6050400560102c10901d640c07040000d0045005002c07114011007854410083c0c1c15081100c42c0d09160f030701d0b00c10000241380000040701401e0910801003a104146c4510111a01c0c0c91022201c42e0b100c0b00c100042c82c04bc00b42e002031004010011002c000e1841c0e102d401035102d510b5a0302440c02d43c003075080e000f1207211522240c0540d8000070004545002868080dc0e50345490b00441d28009d201d0348070510500c40040e00f090b010000f0340c044c0c170f0b004070090300c1c41e10940791280c41120074500950380a98140c0100190000241c0324450420b001c200d02ca094841c80041400060400682c2980940d22500002900300030351501000f00300c81100e2190544502c2e05103c480407420f6080c2060040c01c140501000c0f43c1002020a034642e00400d0340d0802d150340f4038102c50f2151040d000005100e00a03810324503416625000441a1050f0b2180a0480c0249a80d00c000d194050202601e15200f28081000b0110300303911154014442036000e90203041d0742d00b03030200d40030a030640046c01c01c02c08404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 280851645 1250 280850395 280850417
    0x30a051b071709010201090503030f0f011d0a02070c080d0207090f1512050322080601050f1c03091e030b0603030702010f26010e04060b03010203090d180522050106 72
    0x9000310702e102000d400d40e00d00300d0f1243d5614005070300412450f0000b8002d0b10000c0f0810990a640e6030755103109244080c004409030740c5c1c44000c4000396122450703e00d078070b60700040005c03e009001d6014024aa0003640140c0601c1d650762042414961031608200061b00903110a1128014a0084440f104484103040288403000b0b11610040203540c000c0382c40a240302d40c1c400f02448000c2003a41c46104482e030f03960349070345c1d030099140e82402440d02c107a20702d5008460000030a80341c2055036440112000e48402100300000600d240d000492280880c01d010581c0c0006c24003004410415051034401074655880b90f0a604140c0744442008003484d2190b8800c205c8400180d80c4400b00b440d00700401d040018031040c03c07071600726002210004480884120000014103001d030300702031030f00440c0200b404210001c826810f0509034403040b140182c2d0707a0701128078043c2481c1309840180440c00c4000207180459200c0001170b0340d107140f081c69043d51a410511640f180600c034499180140410f0414155001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 280852895 1250 280851645 280851653
    0x509060426302110050603100308090d120c060f0c0c08031b0a0306051306030201081605040e0c0720010c0b090a14161730030a051b07 59
    0x452540802c00181d4201041c8150030b031101e0054841c84400007a0241a42c074400d04041c0010000b120310418403480301100003694101041180e008010507107450048038203580300e28041c1d0b40184070458011040101d542c0c0418001c0403c45003e969030307501c3d84000e100034240036053300c40100e04040302d18034004107507a000d50851000496941d004400315125580c0001184441c0720074a030041500c000000c13000940b6616601034400c0e200304545840090400070401c10869945000c000e000c40e8514010a2062008015407d41030b0590b00d001490140c48188080ca054000d80d61507220400110b4203104100c105031710981e44a00e03032110100c06400c104c000800e140d820fa03001904c1500e0f507038085490b079017043c00648000c40d080410303032162900911200f84d0324070106648019903040312030041050391040e000300c0e0302c401c1c080000348480102c2d51051603030060080560340f144400f580d00f45103907880ca500554451000d41c8400903151400d0030301c00d400e0705006902000e5452040104500003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 280854145 1250 280852895 280852933
    0x13150306080f030d0c050403120e10030513080d090f080c070e1e040606030219080106090e100b1810090605300f03040f05040e19080304030509060426 66
    0x1403490384e03e0110b0951040300059030716202d1a00003403d04c0c0d03101c01d02100c2d10754000f903005181900907500420701d11a010030490488005840c01451060b0610001d00800c8245000d0002140c036041b001501c025a6034070862100500d1404456034680410468000320061003000000e00044000d00154608a0403841c4420100b1503c00d81001f00c840101e0240681e82d44480041c690180500c40f01c0c0000c0b2030344202c42c1e4081d00c1822031644c00e102c004100e84100e40101c1141000480003880403901141140d8050101d21144a802c851002001d00c81a00c41a10b407a010b0034448260000aa090800d000217880b100d8100e0390003040c16240c2c840c42264494035a0031240c07a80b403007404042c82585036031400c1a080d007103d4101840b02140100f100c58941e07106c82d0485808a604106c1641808450741d01c60b488003a4404041d14104401e901041c3c0441c015580039100345486403401d2030724400503209400603040340b20002440b100881507110401c61300202e080042c0002c182c0c1403c807017412251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 280855395 1250 280854145 280854157
    0x50105060313051e010b03060709050d023d0215041515091d070509060307260106030c051c0506130312050a1b2c0613150306080f03 58
    0x14620306620101c082c01001c0c82020008074400d060507903501340c94028503001c0d24030707100240d01c80d015280120301e109000d049500100c2c3e00180c104e5806500d41d40801c900780c0885281000c1d90511607000b5003c00c0000d00304002c0f02c50b0727885009440b0900b0184003e203401c02d82c88481b0094040e00b000d00001c0740c032280e180c008144841d94049a00c541c4030300361421201c6198480a40b80382800840b48100b240c04404d90160707072034a8100c2d2116580d64003000000c2a040d43d000c5d0301a0000c050500038140031001000d00302407402c135080c1c4490b24040c140e83c00c45540d503005441c0300900c000103000318a0000201040e0103294000011640c046403646503d684015002c00c1004040010f1001018043e441440380702c540c1213810052450042c807580c002c1c0000c04d020f8141248006d80c421002c9000c0c0c540c950700740841000f9510740051040d984d001c80044644420360140c02408000c80701041d400725500641a507140803220302c6070f030400140c10786110f50440c4009410080591404460000c10340d42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 280856645 1250 280855395 280855411
    0xa03080c06070f0c080913090305030a0f090f020424080615040203150103020c0a020414040b1b160809040504060b0a080309030c1c12030203090d1e0819020c07180501050603 76
    0xe503071b22103400068419005e80b810200c0da142454034100c14190080041c510564820b88140186052a00200125000b0348401054400810000c0015040542c00110300c00e96006242054840c011036a819042040c1d001204590142c2d007040704552010621009403207082c0c3d011340c15414000e03241c0c26103440c60003100f8101035021a0f2940508410000c20944640151040042e540110451803041c102100d060340d060581d4008900728101210015074030382d08110302c0c1420095985143c80b062554404151010302d014000c200c42c0782c1d9540300d0030740a244601710005400b8030610600440405540c049101500240310640340d54070080740c014003009040701c1003d0200c00c40b0341c0000601407000350283c4143c03180c6002e80740e415050350065000708045012910503204180c42200c2e2503a0300341c00e0083ea11078903011a01c11501402465401c41100032560b0b1000f0859600c0000701c1e0403540b20740e04540c1c0840c104104001c81c0000401c1c4100403400107004960415001c101c0394072001d000f1103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 280857895 1250 280856645 280856647
    0x609070f020709060801200f12092a1018061101150b0a030b04060b040b07170c010c08011a0a12060f09060509090a051207020105090a03080c06070f0c08 67
    0x480e298424010340001c0e103c3c05004000c41502d940c03400d070003000e070300c0c04e2515528600c9500d4224045840256500d0048441140b407400301562215802d001024140c0f01b0640304006281c0b42c10320902150a83c42d8010302a170b00300e0781074444200000001809400300034020203021400c841d04601040c142a01d40500f0009500c62034021100e00608c480c08180e000d81042c03107804030300c1c600048018201d20307806660a1105140c805c080000312081445094010b80040004000e03200380240a009080d020703440341700c011319003054980001c3c0d10540108400e039660310b0900b0340c45a04804a5805410007102c0f0043c05125400e81d045540302c0d441e403541c18046200c248219070400b44d00208003404042e5440a03496984003040300c0a41158003c40d0311403410440000d0055000040440b50b0f43d03000b100910340f4524041041e2004d506c000e1050b410000100202043c1d40c50391039040d40294410144181c0d100840e050643c1406c01c00b401c540304102e10500c0d244810340c0d02082c01e040b0150007400311 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 280859145 1250 280857895 280857917
    0x40201021b0a0b0f040305100501050303070b0c0702130606090b0f092209110a0503030a080109050601050c1507030c02030c0d1b0506150a06030905030d1508070b030a060e060907 78
    0xb800001154840c0c21864000952610701c0c021400180c0f003164400c4003200d00080d0301402e80402c0d01c8090042c140c0661051082c0c1010504503003820390000541c02d51145020006d40120b801c0b01c640103d41d410450300d5000401000340d01c14003000081a0202d002401c0c028026480b003d43d20030001498802d840c98034214030500318007518048290b484c18cd0400181000f481d02d07681220b0b40000241c4111446900040c41b420b02200700d0304000415520610a6030800f50004014040030303080270704000c1c05010381c0420450401c81d2064502c0c0311341041c190391601c2e030b2009040e581404401383c219042845500c00300c000c0010070601c841034034108000041d07900c01c0000c440154440d400f07041882008184600514081082d0f2803426090303500d05401616031034143e09640403184018410380c02045500c41c284060340c0010000c8810700c0e40c580fa9240e9442669103031817001d41010740d508074004240304481440380328020043c840001c01803070500e44200091380302d80c0700504000910140e2140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 280860395 1250 280859145 280859149
    0xb060706020f0f070f03030b0604080a03140d06121119091a1c050f160b37030f0b011407230c0a0f0509041e0804030605150108040201021b 61
    0x80d941c00140c004000f68a41c8143d0805110b141c0c075030207003500440c1c45c1000380340b03080c2424801c840c180e8494500600b60b240055a08440380b40d6080705c4884005010302c400707034203e88a80210001042d200c61400b210b8800d41c1400c0100d01c8403d00543d200c2c20010303508038020040d103c012030407200078071000a0000720b1419400426103648070382e603910103242c030703040307000103940009100c41c0034010021103059400c0d50b200799540d07005003a10880d50340354403170040012007000c0300100424514448200840b58130010101041c06111491030543c070009607641c2d51aa40c903105121000c07207005401e110071001c0900103031803858030760381e0604a41c0c400110700081c0300291110050310b490425000b11005030f0800039686885900b200c0b1032085200b18800240e0314002081d00c0290340340141142e61039281ea64540e0080502c08155040f090125a45000499408070103440294003c2501180e41c0c61f020b011302c04a8005019150305000080b0300b03100242c2d900181d0600a0380d422086520b0b0b91200c0d00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 280861645 1250 280860395 280860397
    0x613080c0c0402030a020706140403230d060602010c1b080306010807032406020c0a080c0906030a060e0304090e0d0c0b0c04051c02040c020a0b0f07050d050a060302030705040b060706020f 82
    0x4080e50050f000009001c4501003aa00804c0320700c0c0140c400b00910744080388022084a41603801400140f02440c440c41800e5100790420152209580020303d8000c4000310403054603c0c40c2c4c4141c016035504c240721100b07580c200c80d03001c076925130b0444484100f031260307a204156400081d120a0400030f0641c00501c41c0c074003940c8070000310b00c0848961442405440d0910498440b14000e18006002c0c805199005042a00e102c9082c0c0d5884405018612140d20a00c03080c0880145404c1c1d040c40b40f42c0c03010000c110f1520842c01c003229800061a5164180501031090380d003820b5824105a0048078040c034100e601c020740405175a403190b04406640c80d0303109200c4003402a90001548808500c440403c421845654500580d10aa80a02001900c001e00341e0f140c0008500180908601c03c00284062190003201a0b00c8110703400d080e0704010960342c1000c00c4800031900711020b03540c2ca190601c150326080004a0050a040301e00f40602100400803601034024100300070002d030b40215080e2039000d00b4074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 280862895 1250 280861645 280861663
    0x80a0507080705060402011d03061603110a020a02030631080c010c0909050a020702031b0d060e0610290d06030204050f1608010e060120030a05040311030613080c 71
    0x360030a4481903581003e6845030801c5d1000c030701055610150701a0341580755400d03c02524024090a25503480c003a1171054000e810001c0c40425a65940d40d41d0001c1850b0050b00d030290f82c950003440b80c440a0700c145440e00c0005048030040494001030340000c40d801660051103120448440344c040c1d4000c2c6440c0940f400303690364940c511b509103800908040d0384a121003044501e2007500740080e450740280c0c00c0481c4101140a901a00302ca00301d035400c160380c9045454641c00c0a00074000c4a2190780b43c2804690500710041042d8208005000c140c41c460310002c809044001c06440c0703100c0c0318000504c4c0d00b4102100c0860400d10104040700701005680c4030328011078001d402480603281051603c03170b0f50f560894401c800d5049100b15145007601c03900805040c0c5038500d084d500e4903240d80c070041d40c00841030f5814000c00c0d8031414000788503c1052001c2c011021040d1922901c8a042d40742002883c0402e9101500a0307200104110607410041242d160103074000c0170720ba55800b080790440b0300f004064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 280864145 1250 280862895 280862903
    0x1021611012102131e0608040804090f0902100206010f141201050c0a18030c170307050d0e010909090f0f1b0605040614090117190f0911030d0507080a0507 68
    0x10707100c018000c2505070010648004a03244c180c466640300d505039221030f12043c1c0b122240d80e4a1078010321080c1e000b20744854016000d1080c0c030741059511083c0343c060761000b00c1190141d49e11141c60301d0840c103240c0d4880741000c031030b0700103820306e5030421803260010110392140040d41403505a00c03008585070b84480e40c440e812000000c4c01103140c5032080380d03a107500041181d40040d1800e030100107103074501d803065400e4a52041c1590b40242c070b0f1000c8004c070b20710859029403181c0020803500c00050390400504a1107003498540215a071001c0e00090420380035030340250340003401c0081c500001116110070b02200c1b94403034401e00b90b12110303090492402059103010202416044004075500750031038098004c441c140c1d640c2e0351081900480c00c4941d40030301c6e0b0482d40030920300801d100701c9500f0b2040d8554001039149401e4906000410700c1c4080d1054000d078520000e5aa00310b403014001078040407840e40c00d0070780040c4840c1c04443c03002003003882420005041320202140c1c4148152280302115506504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 280865395 1250 280864145 280864187
    0x11202070506271b01090503030f0901080408040506070507030b06060403020303040302040e1608160603060501020d0309111008090c01021908090a0302270708060102072903010e010602010e0102161101 88
    0x140b100160032013110062160110b04d00020000d02e624001007296a0b815604500c0c6040c00c0c1c0c258015920014040c00440d5905c1080c800840d8030740311030001c0c05426018000074405d062440c2010202507002822450160380200014030158600100303d40440f607054800040c00707803580522500305071082041c81403583c1082d0700059018000980c0e5001c030003e071b40555101d03680d506c07404d904032020351280030302607000302e00710340103490080d80700d0811140641480c000a141c450b0000720043e01c10220b840111700e500040c40b5003105c04100500046000f8002801c00e144001c10404694040040003010b230100000c0121103034861042c10401036a0145c10f944050b125540c14501c8500c00180910351051118009144584114092401883c0603000380840c18101043c2c600071910b411060b0f00700d81c020f4911032400102c00b070011802060074403800c01c600d504100c0002c0c00d41f520030303807038004603070040c400c00407045110b0041c00f81c6a9030101d2007a14650411006079032550b030480c800c180101c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 280866645 1250 280865395 280865413
    0xd110405100312030b0f0f1f0201020c1e0a0803090a05060406141b1606061203170108030906030c0c010b040e011d070e040803060604170c01120207050627 68
    0x507202039401035911500141d103505140d0341c011000c0f13404403440c0c0ba074400c034460001c0706541024243d03622615005040c0307016102003418034290548440d030925006030750001d40d418045000f0700100000c912503412048480317200103501a5250a1054050072100c40080841c462250400c1170f00340099010003a901c46103060305094006014003140344600d041c1701000107103891050000c4070020070365040c185040c01458070424408000e01041120855519400461101c844002c01104a44a941c0d4804c400b0608420b00034825010790140c0061380c014000a0803c1d42d420040e80c0d070004c002d180b4551111040d50015015010b10710b607058209150400c181740742d24040d0000300c80383c841811002c41c2c0e84154460390755110704601c15182c04108610105000a0743c036402583c105800508450030720b6120b07a05891401440c014900f6540d04c896030030380b50380d60000382144008200340400c60901c0c90a880c2e058172050000c020032110400c890000903050b04000c20100b41400c0e000841e44904 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 280867895 1250 280866645 280866661
    0x2409190609020a0504180b0712050f161b03030b010314070e120f0a02040506010c0206192d030c09120b0103020301060503370b0420120307020d110405 66
    0x102104000b640500b8a407400860103013071500030701201c0c119034400e6001200d01034941201184001d0b250204016500c0c00c040c00d035007072901031940190000023003080242400803514a601000d15080300501c240c01c80642a0079054240b080002e540508002c0f80405d00b90004900501004004003031903241c440610420713591149106410100030f891204050924111141e61440c08080c80f40311948902c0b62100103007042d8018541103032042c140020f0020f11980007a05c07980100d45101c10203000004414950350b400401d0f044280d80c0d0030301c0e00041c91000519181e07441c03201d403103040c141900c0b5100609914483c00d84ca800401000224501d01d52140c54142c001c1c2200b071200364865805d02c400421245408191004a410416540340c0391150301d46034003140300480311000007541e10001031400890902e2005611907489a60808010043c003400709582c1101107074414020074a1a80e039401c0030704000102c450071a012100c3c560a840d040c90141d14030200a0500382d08941030006202902c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 280869145 1250 280867895 280867901
    0x9120d02040312050d110c030d020d0902100507031701030201270902180a0e13142107260406140c010f05060102060f0402060f03060f0d210224091906 66
    0x10882100348124181110741201c07a001f80c450f100031301e07001002558095440e41d402002c140191240c04117080c84140c00098103420380c10448004500005a50020180c0c0003010702c000041d040d42801a650554000038801c0c640e15031248800103424090000d0508050040001098a1581075540e419030000c141b05403200242e1003405408200e038041940644201200c0c410300c80381514542200c40d0f0384440d02d42410300c80901c410343c0109080d402c015984c0071040303007003030455045069484000e4a03180e2880c4040403041498080303008174600c0e038040c200048030200c48203440d0001a072841120580b4451003000c110190329031802000080307105983e0040791140d4026002d0322000e9450420800020500b2200294089010459281500d0250707003d55007200700507017012101828000421a500b612110507501000c020443c4c8120f40c0a550340541c8400300b03440038240380c0023000400030b407425540c0c0c1c401c050f180c0c1410024003004420008050107940c958141d90060882c0d040c60402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 280870395 1250 280869145 280869157
    0x70c0f17030c03030a02070c030606032004020a0e0603091501240816051309150509060d020901030b04052e20090d060e0a08091809120d0204031205 65
    0x1a404038041000c0c40008816070321080c0b0030802a40c070395600d2a50a4000b540668822110081030080200c0400d41901c541005184680410b215884141c0e505030003100040c4201446a4010010181c0d801d82c0f00100341200e6031300b554404e4a07501d510141d6400d00400c8004180904038803400000c0161075810070010310302c0748201c0080d024102d04401c43d00300c04111106141100c0803121801114030445c0203003410207000c26825030281c1c1364075043d800d8401400d10640076031201101070201e0320f040006660012011103601e11004030980c0070403a41e0005100c0a402c24102e400006d0030f111090110710216400003848200a0824400126030408240c40c040c1815160216042103403c5584100481140203900241008440001c214644400e49002c9483c140c55010003c11410200f215428261050301c4041e01c80207080c0c1403086015003012a0b480d00d46143e01400740792000407070343e00c40d049080740d803883c2d40d000d0900900000c0c1c4a6640010305140c028400015030070340c02009009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 280871645 1250 280870395 280870409
    0x207060906150503060103140106170c0406060305070e0603151504080d0c020a0e1906060e01080c0301030c1a1201060309050609070312050a020c1504060809030f0301051005070c0f 79
    0x1210300101e40c1104001c11850042c3c41d0107500c544018004a20a0b50400744403800c0c110000c103400b07444030020720031a540911050016441100c1d941c4203446c117400342c2e00140841c1d141c1088107103440d4100804407100703600d103a07004010000c003044c8082c1540708510388080f0082c0114004c3c0e1280b21b5545207aa0080c85803600310300074000c10301445071040c1034544070f198000700030030700903410015020568900a041d1030360f0540e442050341800002801034200800450701d441e0000b032017000000d0b0071303e00700510b101461301d01040140001b9407882840c0d0300307642c00d80700804011031035400c0c4e1080c40c0c400e1181680d80011a840000796403a415085242070500c03c0c01a10705688a070340800d561110366020040614808012020740580700e6400750010540340c0c03049544584010000c03c07200b90001c0ca0030b000b00d010005061080d03031781000095810001d01e000840c0342a10000d9040460700041c02aa4407413050010241c514034401d0342a1108141c000c4441c500e02c550f11510f03002107913818440c0c05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 280872895 1250 280871645 280871651
    0x30a0f020f01180c090507120c0c0209010f09181a1e090c0a081b040c0903021e010807090303080106030b0a1806060e030a021807030915020d290d060e010207060906 72
    0x4510303450035005050047c145622914611184a14840d001d07103e543c020604000e00711721042d0160356001c0c8400d000748070343c0001301030a60614216406a03185a00c41c0300544040d428943d000520322020703002d0581c1d4058246010707444000c14440c184404a040b00180c0c00c8407030611414030804900400820400c8600c00e16155440c1e2040741c8521407041241e0200f00c075000b50040c1c41c10241c200c3c0061055901d0030107401c0b5101c1e4004dc41c0440d140800c2000b0042c1d02c7d0300e001c015600030111540006841c117101845515665000704802c005000386003c01d5140c21965041d512121980ba02802a00b80f00c40310703007114600848000c1001e8031072480080d2900c00f201a45060209045111a801034902d001290842c22030381c00d5000050000c0c01056a5144841d000c5003101c505042c400d08250301c0541c1d60035500d4410340a580e01414400319003085201921910001c440c0a4403004400b510107a080c041c1d60b0401d400101400300d0816841e50000131180104031442e80b020308089d210705010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 280874145 1250 280872895 280872899
    0xf070503091c0b0a05040201020304050d060209030d0c0804061409120c01020d090f030201080613021b070801060b1c09050313050a0f050109180603020a0e27030a0f020f01180c 77
    0x900025a0109000c1c00c2141c82c071020075100940b6400c0307146d200340107004480c6000d0355035001c6450349112040640c1d00300d6000ca0922910310b818400c001c101020762400e4100c61241d6181d0104d070b40b1a910500c1c050156181080d000a440d04040d0755901100800221000030000c81058587c01104112401402303815000c03030103580240c5818050b5080840342201d294119801903490060150030694130113002540784125580600080448000600e082c6000c0f4040c00180e41c945044ac1e0054040c80e41840d8091008114040980304100401441c0003908041c98130880c0c0100b044c8500a803031400700155001002c0c55030000c6100305c80099924241140e80c03506a040b442e855805a81e000400d9900c041110395425a5803920780c0b04007110000b150382d6250700049041000758002850f1403142820407803040c00c801440c0e16005002c42c1d054044810850090b0386905c1409528024001c8001180314036904c00c00c036200750008000c000b0440040421b07065203030030365400811103108100b0200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 280875395 1250 280874145 280874179
    0xa0906080a0603110f011b050705090703020903060a0b0d050604031d06090a030f02010909090b010302040f02090a0b2a1c02031c0b040e2e060e0f0a020f07050309 71
    0x1440c2d0890f43c00140c8900850303c040300b04014444010800e030b04002c8030b810404040b40c26540d0100324079100e00b0040094038a407909120803810000c2840301410703c10300024907503480108840c1c0c2d21203203401c8000b80e401c10440004444094046003d0b01c244951803c100c10990070000348034420300c50000f4260091044c1c000c100c41c62142603940c9822074210314003000050800c0a002c10701a00c1410303c10520b50711a1a40f00031142000b0083e00c1d041c107082c00410a50410380b00305d03c1d400ca0f043c801903180ca03019101060b0381c1401e51046a100c00c1d4002492010803205241c40340b04442c110079203000801c19040e21079540c288c040341c2260058001b03044c2c1d81e03156000000311090003081d0a0441814211201d00b48018003400d020260015240e000913908004140172601e10540300c1040c1c00c1941200584074000c026054041e020b0aa14102d03062140d00c2e58424200e9114240f40c40d00d1034269903820300c400c040e02944540880000012450348104207011019040d002d000b990141d11036005106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 280876645 1250 280875395 280875401
    0xc030c0602211e100303021506030c060a03050f07050702061207261801140f04051504420203060301020702041503030f020616030b01090b0f070c090c081f0b0a0906080a 74
    0x8170080c0541d02100c000e1541001d40e000c019440701006081ea81140c4201c004910b442d40002183e40000f42e039141001300b40014811000c0d00700d41c051508505141d81e6a02280313643c45415003040300b0701d905400056406201d01d0306066041b83c0c3c0e03046031450b02c2c0dc110f10045641d4040c0c0b60161284003400450201110520651545070a040001c1c5056180e403a0100c042e404080c0094445004183c4407070400f0100c2c0c0142806280301d6170003080c11169444266442074100c903485203071031507080495103104a0700c8446d4189140c140100581d00d89840e00041c2c0280304440001f50024107000e14441c0702070003100000c003160f0094483ca480d418445004030303240c400c101c8401040b401d0300301420075070034400e90003522124010306088100c1601c45001078816008810541e5100d000001c0100400c40e001d02d41c1001000c1d00c020602005951120103041c2a20080140b000080c01c9200068a8542c82c240400108059107080d9076a101d8400014121507443c09680c0205000f5800b056003101070748 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 280877895 1250 280876645 280876649
    0x15090c080618011a07020619020f07080d1d0d030c12050702010912061e0c090b070b0403081b04150f02060910020307050d05010b0702040c0c030c0602211e10 69
    0x9021030382c0341c0e0070041d00da2800000348903030500c404000d001000c01070300c8900c01000059030603003071f0f80c964408090000f07103066030022418000d0f070041b490400c40e508001815011690b60b078103005801c14400c00781ea040c8004004240c1760b001d1940003c14042c59089940368119500a003541c150940c1071034030a4907a4415180001d0001e02c443c481080100c0380c00f411021210f2041201050b402030404840b05000120300b0411070150340c4040c5010003a41028041d0020302c000350425040110907212000e000c50000c2000e001c1c4148503001a150782e0141401c1020111039141803030712551503c00d00000c1c1c420030704400c0082a0255454030303001d400080c1e1a889214400004c1041c4041e0820140183d003001e455481404800c0c01400284038941c014030b0b01820a40003a10b4903280707240100002ea546103106c020a00c08010322000101340e2100100756801e81201015a031030107100b00320003518046030300010b81c00300d880090090440c1c0f44410a05030009046c2e610a00f602c5c1c288540d0006040c0c0c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 280879145 1250 280877895 280877929
    0x60306060c0b040b0a090503030a06050a0503241302060301060e0114090d060906021b0a05251a04030b0a0e061005030a020d0c050d1406090a1208060415090c0806 71
    0x240d0002400a1325505030107502107a001c40100d00580da40c0d070b5a034915007080d10581000380d111030092003542080412500102002c0b0000c0081110b02260400c484e1504c06034421b070103450320f00180905182001300242c256000c8d111695a6940d0000140011246190a80000c265540040008451a06035a00e0020089c010040710300f00355039000080100003c21108070b502401100840310340c00c070210b0b1003180528042d12424031070740384c04c0d414440030791040340c0e104440442000000307400c506060107441651015000d21070340c00c002020580a0340e40010f140722038420070010b407484c40342c11041316000c2032400c80c0d03401e4403110050f4854210354040d140d010780c0003e03d400f02524091541110304d50040401c000043c0d1a603022600e003841d400b030192400d0b040c08428840f6201c0400001d5480004031005e000508040d07a0b44100c0413501d42c251108009400e8041030544e600c80d80140200c00c000150b03428190350b0394000e04091b15450240c1030210794a04002a910f0420716585480f00f020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 280880395 1250 280879145 280879163
    0xe0703021e091504090b0301181a04060f02030c2232030105040b0915060604051219031211090f040507230403020a14090a0e010b030102040b0301060306060c 69
    0x80e001c0941c0903074000b100c5456102d0018a040030b41030700b03e0001040503240f90b400109200d5194410305080d1340010500c1000401302d481203002281f012a444004e40381035000031100c40d2100d04000000d844800c82e404070080c17001003408204d400c460018142a4510a5440500c60014094405134041841990b00c1c0c0b1100303002030400615200415a504890a06c4040c2103007072480100703003110b00031102100c49100090900c43c0c140420400039008e42800b83d81a4090702d8401d0206190340103030302c241030054529600031061010203106102c01c10303401901040245c00301d0300300141300207440c1e401412407503c1c0044110026211608032100107c01402c0311100032031107410b04c4010030b070040001040281d10030781e400042192020031a040c0c0303041804251228114010000a20700790b82c040c01c04206c10410900c6940c86d00d01d48035a206401c0000000c0d003586049001c2e0240290013070441e415480020007180d0b81d0030140c051b505960300382d54200301480c1c40f103405484114948401900e0401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 280881645 1250 280880395 280880437
    0x6010509060310050109150503120904090f12020a0312020a02120a020309030a080909180c0904210801031506030201021b15030103060516140403110d0803010305070e070302 76
    0x824100494001c00094201c031039141e040110301d400c0b15000c0c0c2000c0401034a8000240403150201d910901400d8110003800c1c4040111724030080901c10035004a0140e03448001c01000e0140c0442e40e0b0201c50740141640901d4a07070300f03a00944039a20640210701060340201c1c0d00c5000c081034170a8031203020b255002800140301142440c40540c10008101003140700412800c84070303860502102c42c0880c030030310200d515603001404024140700000d01800404002c441c00025120b0000307141e04242d0820384039200c01e0745850421003505d180b548c92410020301129510b076469507000c902103040320300a18480c8088120308113040c007a00ca452002a0040c2e111500f0003039034079a400e520140c294401841544100d015040844494100340e0003030b00c2840d0b82d50f080004200d8500102c01c0d0403800c61030310000811075a25400c281d4020b80c0000b0b0702d0800726031100d0380151a05154001c8554120015544940c1c6d20300e8100e581e2421030240700700864103940410351b01d500a00a072107052042c0e141d1008010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 280882895 1250 280881645 280881649
    0x1407120f020d0c0b0705070b1602010c0c050913060e0c090613060e010906091b120e0a02030604050105091b03030409020901180e0a140112060209060f0a031d03030702060105 76
    0x58a25941a0b07400846a00d5180000e0a41c12180b0010152a07911039111200317403d11500384031250303000340520081040241892130390410700700b4030b10394242030007240d0203220f0809a01900c1180c00180d00001901d0074007400010030881e583d00c003440396400b4880f2450361280c5a89561001131016041920100480c800d0f1412a08107000501c0700000003030060f40e2002041c0d100403084c0d1108010598580052181c40880c0c0501c0310f2903e44051040711880c07038008000e003541c0111881d50342d01543c1d01009410310b20107010f074564140e0020202c600c0350030a03081a500038481514100f40900c140704402c0007131614000040101c04004000e5402c213450110098080c0d480030041034100007407112500201d8828140c040083d01001c0684d0b2017038908000300400b1600820450502a015800108203402c502d1113840005540050301586800c0400003080c0940030340c140d01d116042002c20381d03400309545136000e00810a8503000d401c00089440700c425442c0d110903140080141c0040c00140312074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 280884145 1250 280882895 280882913
    0x39070e1303020f060c130b19030c030207170301090606080c07030c030e030a032c06070807020103060f0e190b0609040903020c0a1410020d021b0f040216140712 70
    0x11500900503114400c0ba0070001604080c030841741030354140e401080501e40111803600d46409840e600c1180d52030301680d880d02c000c22a1485c001c050030941c40342c0150385018400d4041e01c0d0025402400e075481040e002e10f411701550001d0249243d458a003050000e40c4502c140da529010b4440340ca40c0514201c0c660300c044030030448180003a0144204116207140c20b031401c2016505c00e038003a58441c0711032580e5207030b852105000010f00320000d00300e240140002d503442004480c81c43c0d80c0300d086107540782c20b04e2005a014001d554040c00019060701000580c003484480d0003440b03400f80b00402040011203403d03c03c21698030000d107a07001401441036420b00c0c181a8000e01c0302500a0044842200090001034040012078200c40d058040f200d016034260b00703110000c81c40003030136170004d030040c00c401100084d510846800804c0c20a0003286400f900342c0c4880c94560b0010402400035596420102108031018683c0641241c004800080100b050503000c650001540e10303104480303000746142d0720b9071005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 280885395 1250 280884145 280884181
    0x30010b04030b0618090a0308011502070e0406110403030207031103030313020603040c03060c0e010207080a0302121c320f06010e1f020106051c21030239070e 69
    0x3000d00122440c0d07500d4890114172032440b0b000104482061840c0052031841e069210b006821900350520000d1900811080e0a890300b20209208503a11800c1940213000c03c41074804103101c000a0101c185540803651005890060042d12500481385091640e2031000301d600320003000072000c4103801403402800446e002805800304045403500d17501c400c801c41d034428501d8000f09008070072458140d60140300003001080d17240d0180c40c0c0202c041d20043d4944040c084203e11041000448500035002c50f24000d480306800352040280800f040350b041c07004c100842e040d17000c0c02030006950321160404040c0d40e00c180292814807500b40c0703402c00107407010018208655444103229026161141c0700303c071180c00814081d03001240041c580024882810040ba0a1310b0785203a80085500c041a261007203122426400250850940300c1ca0008500a0180707180084550009400c031586441388010580340b01e44410700414000483e076540b072075803544148107450780740c0c12101c00075074038400c45001201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 280886645 1250 280885395 280885399
    0x9030c05160537230108060603070c03110d0801060801080d1d04020714010515060f04051c02030f100e2a04150906081203040b04020d06020c0330010b04030b06 70
    0xb603906842d40c0d4940c41007984d04140d03403940012009008003d2903a18481052000782804606814054085601448014801c10074003644003224401c2500c1a15402ca03000b01001c1521221803144400030400802032280030f000845800020404580c00b08152410030599280c607600c210040344140c14501078031101c154059030038444d40c008030320400c0d00c40f03003b0213800000282c9860700c1e81309415480150307100180558814000c070841d461050301160b013951011200d0b4120000405c501115500380d11400039014014500030400d040320000310b4503640c010a8a05012041940644aa0300e00070025a09914840015409000c401e844000d44804401410100d50980300d403940d804010069404540300d141e6503041005030910600c4000400032600304894a9414580c5405a01c0700000d000a0300c600303410b10b1250100010307541200c40100c02501541c0d112402502c0d040d1718a10111100004518840414401c0302540d52103117040e59418092035041504544460001141c0188016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 280887895 1250 280886645 280886719
    0x5060a2607081015080601120813090c050702040b01051306081308190212031b3603070807030c1a0d11041809050303070c0f0609030c051605 62
    0x21035070b140d0074020742020305040803010a00401521007012100566030020504c0e40100005004007482060350011064004015035190340b4010103c680000a581c40952850325199010100c0d0ba0040040d145450003100c003001204404070054546100ea000366450300031040700c05120303e50148048a8100740c0c038080c540700e40c10789595142d1241d44690044408907101c610440b080d280d04002c03030029401d0f64120107085040c601c2084003000d207035039900310400a01150f105080d80e952016028000020010b02c0705058800002d40640c2ca0000c0c0003034068002e81c4000309000c0400103208085947c00450b4448140c40c000c0c003640390300400c2c142a094003070104443c00204019009041e0764040c14400141d5030340c6001001250400b8410001c40f00d10b0500740840003090000c42980d601032203508180110781400c4c5405001c1095000c001040c0c585403607125024142e01440d011600342c802e0007240c1c0103d006405c03070319140d040c0e849003562040d04500e00001541d8201000304022018240070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 280889145 1250 280887895 280887899
    0xb1602070509011706010603090c0506030603010b2e020615010f1209030807030f18020f010c06090f05061f060e01090e070221040506270d030201090605060a2607 71
    0x2981c800420790003100030210500a004501078140074141c0100008d0804103c0d0500307540d508020607101d440b40354410000400000d1040d1000e400c1000c3c445001071040209041d040d80d000d0990140002c1c118440e180c1c1d8001050080c00040c8641c018141103400c5034060740c100b80116000040c0211440c1006801e240145038034405015043c410351090300c0308105481e04000003000c0b542c0303010040903640c1c1003600c00050078208024060109405480603060009038400581d030440309100b00401140c507100b41c0c0d20901c0f0001303485810040c410030a0303544a403102404401c41001400c1040054144541d040101034041c482d030b0000104d043c1455094940e40c3e1400c0d01003000100c402002603086807400c0400180407640042c0600113840482d810b003401c050115885000710110a8100b040f8507001811111070900302d1a41c40c1c500500c200c4420190349030080c041c0840b80400c907520b9092030b0202e4100d10305050080250f0300b604101c284071005100100303d900e001c2800080c0e6038081d060700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 280890395 1250 280889145 280889149
    0x30905030a0f170712140f04030b1b0c030a050c24070e040203010f14040603080c15010803120705030a0b100f0207090209032109030a0c0509130b16020705 68
    0x1c4101080c042d0081c52050034503401c180482041540800e40100010800f0000081c24078803012070300801881d054440c8403065042014a01c9140768441d035481010500104005040d108184106001c00d0203c05800c80c0c0d0031403e07060b000d18010100c444c0c00600812103000e109034050919030315150201c0d07805210030b449111f003040040711101080143c5108000d812504900007201100d81a01c04610b10340c5404c680d200300c400c00f40100c0c000c10020107942c88150795243c000364050b41d0401b28490b901d51210ba0a550f440030170700d110100104c0c0550000800000c0401511000c40e6100c40042c019a18018201d58561009101003032040d5102c06115a40d00c412982c00e69414054039410100904c000010785001030030380c00b20800500421001386a42c80205544190b0100e040007000e41d1381203030702162268060503041d150584201d50480f0241b00092080c4021070740180c1e10f503219a15441c215503c1c9488541002d0312141d070b00b102141c03070740c1401950108811498810352b240b054407400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 280891645 1250 280890395 280890403
    0x9040f0618060c0c200102120301080c03061006020a06022a010f0b0406030f02010e0102120310091d06041113021803060610020c04110408011d0f0c0f090403090503 72
    0x25149401480c0d60300e420104059485912001c20103400c1140813008581d6a41d09040032070580440f40c0410032007020440d9000b00b118040c4145005a1300d174032503031140b81c03095951608956151182c801c0001148402104a0026040e5110340e030140c4152038207a11410041c1d0703c4902c040d00c0c44000101507003009140108911a03500502c030020401081c6080e00e5800d4501e81928603100b01d242290030000151590403e6026070350a0911501c0342c0460030040c2e0610711300d0610301c50030400020811030701000a0204500380c0c2c43c455801c201e81c803190601e44605130305204503000140d11040114000c42e031007030104031034444000c089003103000c4200c0b180c000341e800034440510408440e500320700c0f603846c0501035a41e2146040c3c40b0503600e182e8075240203540c1d8240b000d032075010390364a001d1a0807402103141180d018000d00c0000744800d443c0c4019208108811070301420490080c1007054070402804200b1860071b4a000780030400303440c64403042000001000e0b00c00c90a00440200018150318148 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 280892895 1250 280891645 280891661
    0x11010c0210090e0714030406050705070c030b01060f0f0215151003150b0a0c031b02041805101a060c0109050a0f1a0408030c072d0611040506040509040f06 68
    0x7680350806a883c1c884000c8043c2406410b04061200c0488484038035811541a2580301c3e0f04241c022680351034964043d5a144111034001e03000a08000010043c042a4a11141200c4071a80c614071654180207080300e02400114002005030094110446100e804e42d41054101805450b2205030300d92400014801d080c585025101003510b5816100104040d810540000c00c0101e41042c5009c000c000001c10348030302d1840046c18002e4ec0501c104100d00d882101e00c0c4207950190080014006084141d440320501c1041200c00d40724400021814102c54010311039446c500841c825100b40390201000a160460340032619650f6941307103c807000c148100202e00e04240600f03254610383c0780d5800d20407002154004241c2c41030410b401070100050340041200d07803150800703070466102ca826240900280105501e10a071544248615881030800f6802e0841030a219110030003444401a12407070b01030140c0e11545038081c105000170085401c046c4441a8080e204550040404040390b4840c0200da51036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 280894145 1250 280892895 280892897
    0x120105160e0a030b01051309020d030c1b0303140706021e250804051e030d030218010c0203060703110d0f060608060613030204021303080f090306060604080a11010c0210 74
    0x30100e40321040d800c006403480741d032000da40c00c6071910304544488050641c10721031340380602881511548000310950041c41121340c01444602c0003c042c1c14024400c1000f080c0c1540da61181d8122400a219107000b420b044039416140d2295111000c3ca4982964100d1807058418a408015250481e084038505a001590700d00102c1e8480c000702440090460406030780c00039040200704d400c00880e0120055600f2030308203c8001c00500c501000032500310b02155412a0144a5070f40e031655819015005800041296411420f0104855004440c0c040780c0702da0194141c2c11042c080340a071032081c1c0140c60032862280f002d5203000d0301000d0000031120031105000205a40e15024451150f0210031150050300371201d550404a24400e460034146040c40001c0c4160b40c0000c12840040425000d600195006618103171604880d81054600394080c8403110302c20300480000415902d46403060314140c0d24050f009110b40d400c0c6070f5403903a582c00c045011a061041306503000c00140d65045c0c0d040c1e40050350b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 280895395 1250 280894145 280894171
    0x8070c1703091005270a0b060d080702121b030c130e0a0f080301030201080f06010206160e060f03061c150906110a020d0f030c0c1511030c0c0d0c0f060b120105 70
    0x2102c017100340c2d099840560030f01c40d0080396400e4081001002620741010040341ea0041e003210078a0310300581d02c01d05200a4000d50412000300040c4008140c0b801000500280032074a41d1499081540b103068480e0b030958460040180d007001d092041c2d001020640000d800c4450752107050b03c0741c803041d07a40c0c85000c541c0b041000006000315680300c1d14803074124070300398562501401d010300040d448481c01403081c684e1885100001141d0340c8a252018648103000c0e29a5540b00c0302020300c101690b10032980d081c00307041101c020642102d008841c10480a0700100050354029640150901400c0340c0f00c81681c0303171030300ca0208804001d1944014900a9102d400804000340c401802030200caa88041301e1040c1442c001e00340c1c00f1190403031414408141d2000e80402021010008400200550000320809600200c10000300301203510042c20348414490844d144190140001c07030b0038a04a100040a0512503d100c0c80000c1031600303e4917103d1001060111580454005e481c02c6032801c6074800e060f504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 280896645 1250 280895395 280895431
    0x20a15030e03040e0106051327060503240c0c011409060708090309060c0f10060807120c0b0906121611030301120b06010903170301050108070c1703091005 68
    0x34051040145001c00c000280d4102131800c81545056032052180900b0f202c800210024060404410b600250443d5007904030008510302c1c000500050790f100d4181c509181c040d000c1054a0001050b0102000d0514840c491904496a00c2e12003100a401d980c1961014840023040003001c1c01255541e94000c15141c000c0d00d00000d400e40703000c0014041c1803e1090720014803100034804000c403000e1900541da015580d000d044422440c1c030000810b20b51117030013101c0c0e803103003030140303a8010303030211a9101c0031a61030940390780104c0c10b50444c0400c010140881c0c160100320444088004c1c02042200905583c01d00f5a00c015026100c00e04031864100c003940b21402c20505500310f824540a4028800214115030410b0031410700400ca41c4400703040c0e145404001401680301d26079202c06160710801d40d040a01034101c0800f25508280106404a2040400690790a210f400041400c41d0044480125810141c03002c6c00b990388050006295070044611142c500d034681d02805020b0006e00e405016000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 280897895 1250 280896645 280896647
    0x3060b01170609010302040c050c07080c0a0b0307020303071805060a0c020306090309030c04050417070f0c06030e0307021002010b19031e0c090c050d110c01051503030d0f09020a15 79
    0x5101c0440c1904400790081440010346401c01d219064a40c10745d8005000d0580750f01c2a98513000f20303900c54074948070f50701c000b082610005c5903a5031100000d444002d2000d441c0c17080250b45000031109480140e0043c40000c1c60745210700070003100b420360303407030304614064948000c15840e600c001b0f0b500010130601c00310b90b011800d0412011b0340c04110140a035041883c0342002940319260782d003106114030385520110301030246000d50000e40d4120000b0241da1580c2e10b140c81c8140c031180305020754a240d41b501c00001c1c1b5602034018090021003036005140b40c10070a6080101148140c0102000c6650790084170255803981c07000700340c03042c0c446580588414698600303240f030349810440d50000060b4084191000812030307242e02040d600522004286043d10b848211514020000c0c1c2407181410074a8000c041070302a0018125220400d000348004d41d80c0e200c00701c000c2c000c01e001480e01a0300402c407684040c9002da000300c1c1280001b0301c02141c04602038000507240c0d505500a00500c0904004d628001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 280899145 1250 280897895 280897907
    0x17060402133510020906090925021501030321020f070b0c070f021203160b01051e0a060e0109090603051c0801050f0f130e010e1e0c0d1b03060b01 64
    0x24048001c00c1e00c1c0000c00545180d03e507591025140e21164000c50901c10607a15407042c2c0b403030650050705000c0c840c980102c810b0a02050781086038a5440c4940304030411b54404038602c00804100034415032144d10315074045425074002040000c003003404c2d0f45201d0807441c0c3c500003021110707031240c402d54907840c103070901103880c4101070b00760700b08480101f08082c0092305200c00c00b41803a40443c1c00032041024140f0107400c1d0b100f01100f00180c1502029807604001c0308021241c140d480a486a50b80e003030045c00c4850100070311700e1100d42d110764081020810184140301c90143e1200604d09480303415994500001665055003045a5035007003142880d403200b14030250f15103c043c00d440c2a03e101c1d49080c0104500c41c0001c0c0d02540681d120005460890320340d2249071400d48003942041100e0505085540c1c000c09190205003c6030081c6180b40020ba2036071740140321000c0d941c2004e4014603089904214076201c940000b107645402c03040c2440018601d107200e40e0011800380341c000c603052621030001002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280900395 1250 280899145 280899209
    0x30f0a0f090c0515130b090a030618120f081801060308030109090605071805010e06090d1101020c040c0e04050702120a0801082a101e0903140d1706040213 68
    0x109041480060f5503501d2800c081011106d0b8418166030b20b00440010038842c94050304050a0281420011402d00725003020111030b8a0050040f044400702c085c4045605c1030521541800081c0c40c200400d801401008200c0e060300e040200005049a507543c4421454000b40d01511203a96114048404d0040d14051f0b19845901890005038100301081c40600180450281c981042134100000855468810855254940003460780107007100c14581a54101045d0404500601851601048905180c080c000b500c4015407103914100c144042444018400209000c0841c0f1442109000e00a2103c0080c4400343c00f80d41c0340d011030360500303a000d4902144807410203000110b1180d03102d811040e07685900e9040030110b44541b24103a0456003103a0301c0d144001500c3c04544880c0c140030300307070340c0080c40b10048a20030981c890089250350005600c03840117100c420041a5568012046505280b41c0c0ca64080c600800050404a60307481c00b520442258106100c82c01c0074205030000075611361000c03c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280901645 1250 280900395 280900429
    0x60308091201050606070f1b0909030306050328020d02060c0307120c0803010902030702070b0a0e03060604020f030612030c1006050906300114070201240b030f0a0f090c05 75
    0x1007542000130109000b8410b07020042d00c540d403003c00d0700c4200219a00d04502c0905050300f40a070907034603110700340010181c0c10401c9000c00d10303151000485003404603440340c0e030b00c150030704420361240d1602a41010405041040b64440c40700c6059100590b0380901401341880c68500468641405103060401c0b9039203101c102e001d0140c05071651002920240489040d510312800168981d2625001a17103050019003158105410110740002000d601c6295111036410441c102c0e49107448a00500080b4071075480041031070101000000c0f61410400000c038120300510040340d280a4541040c1030070013141c100001c0580d81c41c0d82e0304000525158501c1900800304450680b99002003800004101c41800d140c0c0f80c448801400f020080ca034213501c4101414001d4940c52501c1c9403460000b802003090300300310b9908003201104a050010058004d2007a25481c1c2ca006166854000c8103d10305600140310b00d07407803901c0d001c2e80d41009001c0e005401010f84940100c0d100b40b030800b0100082c2c4080196601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280902895 1250 280901645 280901651
    0xa030e0a09110a0c03200102130f1401052a0309151207081504020309060106090b07080304020105031909060614010c110603090f060f060307060f0e090613060308091201 74
    0x25200900950840301e40310700300d00313007060903001c18981030350070001320010000d1140303601520016244042d0020520318003210b442e01c400a45405020741c08198501565100141581c0080029401003000f00300c0348114036510028051a41d50081d98803500340c2c40140c0503080440c0d04016030a0455899050380d8900c2800340c1040c20180c10107010520090182c3e04200a080200e090550842803403044040d01803c15952454859159070780c0c0c031000c2c41020001107903001d00144400c50780d0207450b050395000784603e207940c071140c00440b019040a0100350302e20401c1000302c80bd1107224070070318411510401021035664030306010707141000c15420031981400703030903e14000002e03682d011200c5070200480d03e19441c5d40b00e64000619040340d4420140c0b01d8031500040c071070840320701ea42041c8941c0c8101c0031a8000c17602c0700001c44003680c44145000c04510031500d1070f0400e00e4142c50b50340c0d10140140215070f5200342075000c94180d8141e0b41c070954490100180b4440d00e030426010021188084100034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280904145 1250 280902895 280902911
    0x51302010e1005091203070b010608090601090b01020304151d0a050307090e1c020714010f080711011103070c060e010204080a08030901061d0717060906060c010e0a030e0a09 76
    0x81c100c0510314103164800c4050000741404075005909881c1c914601034040c0c1c0000642054090703aa90000c0c2c400e42c2c00c2160302c00001515485031510070712416100019150716440c02d00c000001d000e10007005c0d81940420302c808204000000004001c0348919a241000e100764540d144909201c8203614500540d040384c002d1043e03840000d9943e0032103410320300c001580c068455016040958410810300b5150703d64910302d800d1680010f151068900901100780403621800044d00d041c64000181c0780800c09010004040d2400b408070032034040301d918000308000d800c0d80380a1840c2e07401119503602007410344000d08117100c44d9105025550f191400210f160900340300c1d105a460002e43c000a0201a0000020303000c1c41c0b0a401c204010550b08410b102d06039480358810051103411900c00d00002d011103924440c481960301454000c0c00c0182c0101d84945401051000661010b40c40710810b64a9405400c10340c8820480c1840c01d502170f90b0707403040161a800401c1600841c65024043c09410b144603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280905395 1250 280904145 280904147
    0xc0c0201020d0f020309041b14070203070509071b1211010b03030415120c0c03030b04140601080903040b120405010b01020f06270f010506100c080d1d10090605130201 73
    0x8440002e180c1818100038040c1807410481c03840c071640f5801c9403c07605002415106004040f402c3c1c0e003000403501c03454050b06101c02c0100450150500103907160707020300000c010608058058541150481c0b1b0064407113120086800c2d00e90101139070803545984c484812100a0741c0c0302c2806184c17180010000e0001c00c84140001e9541d00642c000c41e09148081b890301d110440c014680a09035221140c0240b000c59034024000c2c0c4407103506103082d0003183c14002600180e25003841a4402c04004002404403a11844011950070070700418006051100b08004101d1105050140071140e201c0c04414025103007030316004e400d40e040d144842c4e0541d400701100c80640400859130a5101001c8002040401c0038803143c0d12130710900540001031401a01d50704407507610190426031160b4070550304c0d44104c410400c2c0c1107407000f050329005000e20006000e0700004a582d234010030700400c00d5800e90410480640c80c000d003490401d00041c2e4071941e51b02d094a04015890294030340c440598100c0e03400e9440c103500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280906645 1250 280905395 280905403
    0x4030906030e0d02062e060504140616061109030a050601210308070507081605010f05060f0a0e0c0405090f040b090111031602010e03030a02040e090606030c01050c010b1009090c0c020102 82
    0xb006e01100d0407806a00d084908408a1810407202c001c400441c0c943e0b8200241c021f9026000750303007141100a401103101d0a02004840b41d0004071008100031082035110500203104011628030f020308108045092903a0410403100ea1303a004801511503540341081100320480150815107000948103900381c040303504040e4096002500b070429541c2c130000d514110189110381c0c0f81c017400488000c01e026013031000560113503243c01080300040009844001c10030502d0a02c1d02e04540d800284a58148034503054100e4098000030003441c0c02e41800e841d440003070f90451041301e6a15009107002d0400052005a203c001e40080035400208400104244c0c07420481c40700419010902070350002e5540110b00c00d40c44010130040c140280d0b80c60f410004000e1000c2c1d4828480e026040040c6004a60243c4011500b18004c2c10018010415030a1600055660350000410a8010355132400e034003a003a120280040412a020b50347d040030141030041c140100c1c1e075005188000c114010200c2d00060343c00107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280907895 1250 280906645 280906651
    0x41806170c150d02270109050901090f091401020702010f0804051b0d061b030c020106050616170415032703050f04050604031209151d060d0504030906030e0d0206 71
    0x902da121000344407814035400c602c2102070228401e8030001e0034009a11004c1101400c241c40154030394050301c1c0000044544d1000c50103907980c0300f4040ba004011a9103994043c40c5000507401003c00d581040b515034240030955580116501d03500003408008560380500c40c0301034801d240c100990941003540341d065440c0407840d40b516074402c440c06461090390b42c280c562080c1c0d81d40200d0502c18500704001b6014607902c09450000460704084100c05050b0040c001d030802d640b0302034151820005015008024020386e02400e40b000c4402242e11700568603243c00a00140c01c45404400303d034101040010103d800c03240a0014004d8145480f0600b184d40a0303c14041b16003519140d904c407010450b81c0401840765503c00c5601c294002000001c000d40700f188205c100c1d181d5112496847d90b110104600ca078071010318040010100c804500c62009103e140e00015540585181d041c4403402c500003044079400e5030103a011980d846000c2091907494010600910f95403c0506895914524042d607101005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280909145 1250 280907895 280907899
    0x6060a0509010e06100c153c020f0c060f0106120c050702010c2102060604050901050903040b0a05090a0306150b09061c1407090303031505011b020102070b041806170c 73
    0x2005e005615030b00c1804061a12170304401004041d0715000c0611000b804071881440039100503204a510001d00306041301103102200007005581e00301010304030002d520102524803c2c103c02d22070741100e81c1080041602c14000e80d249007a186d41840700152030600e002c5074529025040c2005619816440000d481c0017075420b00341564294550300d80785140e070507224024071039038040241c42c220b0550300085a40c004c0300156400c10080e260306c1c041c6402d8500131a6100701c0d80c1e10030070003040003d220b0700042014604034641242001a44c100040c8042c6459200361089615412070f2000c903862410310100504000040c14a8540c040000c262140181c24020403801520007418840d13010941040151906494041d4071901e00350a018140240500050300040c0c40c000c0046200c1c110b40740b03000141c80d41610740011440500f11125141d80e424a8101c0c1140144680080c0030090300000d0800b5141d15410410354440503600b0300701310341c4076500003080041410382035181100c1c0481c22a2142d0702c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280910395 1250 280909145 280909159
    0x151107050409031d0406050303030a06030204050c0a1407030201020d02040902070201030e010c08060409020f03121902070b030c03070216032001020a020906060f041e090b0102030a090905070c1406060a0509010e06 93
    0x100900003401446d11354400382c0c140c000003080104024456010f8070a0303920894040142e91515035482480e809028074242c00302c7c8103550f00c0500d4980300c0025202d407034400d200143c500030403895010181d800079805891002e0b0013080c4d4004660f09801070300c54018444000301f010030b60011004007812000b600203402659600072020940d1100300742c13950784240240456291645d03414000c1d40742d84c0150542010102034900d070301002c51010401c0c1c000c58006075012811600d038a41a100d0f142c2c00a81220103520401d0300b0340c4800044100b13510000d40c01004043e8108054042140074a03000340b80480c115081007001380c00507910000d285400200903a040303a295010300c01008514480c0703400c2000c1110395800b83c031b0412030300305c090a000d440030a2030900014204000682e076a024665800300800c2140c44248016541544060391003003861808035101324031030b00d806110600241424068bc0c11080c2001a01d080c142d0242d0010b04040d5031240070766151640e0090b20107406000e0f0341c45a95 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280911645 1250 280910395 280910447
    0x70210020c07080105042a08060402130905150403091a0d0e010e030f0c120702030d0e01030b13020417070b0706020f091c0302010e190303090c15110705040903 70
    0x8800c202e1000540600c0f00200950304150820168624806000b800030250b80605401d80394091000b1300100e400fa840200080c2c2c0361542080040074407241420076507507071a848c00000c1070382040748505000c0000c49128450801d410020500c421603080050321101c407440c0c0603c07400d40c0c13808981e402c0c4803040c00002e40020000429026210040354070000348000704440c9104800d1740b00824010703440100302d4255052488107002c25004400d03029500d0341000680f64042e034002c80c00c4c0c1490090503d40000c0e01c031034080c0050021080e080602d4401a4041400d006180d403001e500c07810001c080b40184001e92404035003040510030548010466500850030f00d21001c038a5007030300c1d408100140040003010a0442501d085540700348190015824000d82043d0520040b0304440c81351041c3c0c0f845d0503400d07055102030340904103610301101c160489100000f4111000c0c1200f06424030f083c0d441d0030545040100c2c2520300a510b4101c244990b00d800900c1d80000c1d008540d61a44146280d104500c0c11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280912895 1250 280911645 280911667
    0x30b0f120703151b050a020d2303091002040602010e060a090f030c0c0506070326070504150c0b04030305040308090f03180613150f080f010509091219090603020307021002 75
    0x2001c44494101204d400340a400348007900800905008109503088546460300d54400f03d4144084454035000f110b1600e281c4036012038540001e41c0c6c0400c051088489524030900f4920403079100e034ac09240142d548000300b80ba1500d0500401e50000120074091042100c076480d81c800343c621041008040c0702080d05540200001c811a0200030200103100b141c603400c8a0a02600116006900082d282130001041a2200e01d094102d40105030b0750b99102c1c00d050400b0b44942e03404141541c15010f004000c0030b92000251446030591240e44070b9030707002c0390905281c0b030003624198000d0046090b03038104400701d48440800100740d13214100d11041a5540c0303040100426a0340c428100b1414550880c810089600642e17107425030310901055542400d5114888400c84410806640ca041c020003281c00402035403600042d0f00d5000400c000690b1241c42c0d0030350070003c02d54801d00e00c00720030b80504c8140d140c00c2601300d6442002080581030651452a010302d009403542c4040102440b19a40418030174030071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280914145 1250 280912895 280912901
    0x38040b0109030b16081f05150d0f0b03070b0315010309031b0302010e160303050d020c01060f031103070515030402100509030115090b010306080607080c070206030106030b0f12070315 80
    0xb960844440c0056003040e4800b21100596000040d000c1890b00e0040381001490707440d4510001091038403202c1503030609040100800d9462455001c219050184190420284c81058008005e1f2200051001d10001c03d0508004d030b207a2001c01078940c00d0007003005100280b010214000b200f4a40051030b11810314042c2d0b2025800940140c1041154151508246e0154041410700c18000b0460b070b421049081c000031600020302004001640038007034550b03006072640242074004401c1c400841c0064a4021034211210180c3c8242e6080c8960024030100f424140200c001030901036442244200040741010b03911303c8090b00080c000c000400c2d558401d0791207041662400c180060081c4001700d14010011b9100c8071501800c01158909801403040e0340c001d110322000c850244000d0101030b6038484041d51841c0c3c0060001007540c400b041108016070300e69000714041c1c1001c1d24000750342540c00d030520001103950301c40c040c014075007101e03441d182e81d10020b00201100da20004600c80701820700b07144009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280915395 1250 280914145 280914149
    0x91c0b2206110c060108010506010507170d020f1201230d0212060a090309051c1e1703070e0a05130902030c040f140901021306080406021c38040b0109 66
    0x1d030502d0090306880801e4100000d0181000e2401159116600c0b0303001c1c2d13402c0314400c1d55aa030115030100312010004050082d644800281038800e182000380c402c6070201681c1c071200d08481c2d1014001802c0384424500c0b0282405010a4020700e03040248101c90740c0e9154400541c030328461108a00c10300c0842d070303c21426520802e1942c00b6034040e42044070620340a42800c647c00c6000c0b40b400400450399003401c0022450b00c00d400040e1003041c200da920b800341d03150404a40203000302000c48014010451101d40350b130a8002c6a4800e40c2c3c0d0340307403071031004000d800c035900070ba0b1149010807410006ca0f40c0d150142c0700c0c0d25074190000241100c981c4002403400c0c2400040382e400900740f01809075402003030340c02806400b010b5100c01d4200d43d00c8400240c200d102c1c007910044054000101405010720400d032103603000340f10703803070041c6030210b40010b003507050f4168103103084899154940ea07403806d058005842c1c0441c5201d009894041e100c200c55141607001641c0d0305008036541d0380b090300c950307210340d881c040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280916645 1250 280915395 280915403
    0x319110a030e1f09050a050102120315011107080a1202160302091905011212080f040b04031b0606061407020904081312030e100e0306040b0a0f020a05091c0b22 70
    0x3040410522020380413081d0f174803600d03101d112055000100e550010400c01e00189195500c00c2c607558950700041656513424034a903041100d14146c21450050800101000e40b0001000b401e4448aa103000e29074880914200c504540200403030035041055405204141c95045a002e82203030759040c99100414400601e42103544e050100002c5d002c010a80c003888428040e1600070180d495419007900c48640c02c0da001c803460711400c00010007141440410b243c2003407080c6002040317040d494556a450500d0904195046581d4130030801406030002101c0c005c4d0f020300f0180c4c0e401c10707031aa00052100342c0020000b41451000007416084080070680c600054206041e001c40800c00390304000b0104080b00800a001340100032589119502072605858013143c010001c00840da55962100380001000d80f448115030348950901c1d82105241c0050100d0a260f96100e0340c440d0740b050100094050000600d40700300c41c00140300c201080c5029501c81d8040c02d0150100c416810050960020100e01d106c0a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280917895 1250 280916645 280916689
    0xc101d0303271f0b0906090a0c120207120806190303120609020714070e010e04060e0114090a1a010b122206050103111e0f010c020901080319110a030e 66
    0x2920200030f0b649001c072141c2d2128003c2011034980c40a0196076031701940c031643c0c060315003400614006100c3d08440d502201502e441c003880b02945003036800380c0e0096003044038540d98054000c2401503000c40c9450b0b00c1102210300d11100d20020f94400410310b030303034000641005a011190500e2841c15001080100300404085560703164904083d10a03510300928101703d405420000501401c08260440c1600c1c00e50318010010b844036642c040080402802a820a540310f02da0300002c00540405640b1542603100544408402d621b0000700856030741d0841c1007112000c000511003841500d0594400c644880c80440c842e4560001700601448110490741c168403001145500308034403a000241202d200d00225180f043c91142000b810035031018640c13404003c55112107a00340f800720b0078840000b006040405540380d141c2c020841805003604050743c90341c400900c8040c0045000069904100c2d9450316030743d1014018151b90710751005002c09030402031102c4481d09160f880e0604207882010031706202c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280919145 1250 280917895 280917913
    0x151f030f080310150e100314040c06030b120a0311030408010519050c07050d0e061b06071e0903020f0a0b0a0306030201090603090507050402070c030203030c101d030327 74
    0x100e00799a208a503620084000a0300004c0e01c5a41c52001c0140038409403115408240c0d4041481000e40d1026a08410140c03584480c0d19695041e0060030300407401b910640c1c80107800c01381c0240035102c585003a98010025542859803100020034030f0b1007a540d15140071100c8002c44071289140d4003c0d034005180551800c824003c4083c0f4145050751074080c00c00083c4015690784203d60580d000b4508064610740000c5a0110407a00c0f4005e405400720b0000d01d2507041c200040c032401c0b5003904501000c4d9030340e4044d60500c071003660012100044400c803c80e15006c0302d0040840100040b020b40b00080c06400c104040032141e80e03070090088040d145280025848559440707004001c4c02e01c40c8426400300c2c00800001c5880d9100c0c1c00303400280354201c4003c0c02034900d0042400001e610070349003a070744024200f80200040e68240004d080c44120320000b40a0b2500d00e00a00003162020040e1040343c09800c800106c0c4c2c1c2e000441540d602440e043c105c0c2604810004088040c45010b00c0b10000c540650811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280920395 1250 280919145 280919153
    0x1c0c1101200a110603010302031506190906080c0406030503040e0a090b090d080f0c090d0c0f0605040311040204060801060804050109050f0f010501090c0503041b08060403080f060102151f030f 84
    0x40006034034020f020415004428030244010352000780400794040d0031080421a0008130048140d4001c10090945070100d861050a0b4400000580040301210b88882d0100f25410042104044000301140d0402400d442c5544d6139650744103900c10b41080c0e1039000006100305926030b2100001340c1d0422654143d5103000c400d001d803105160b030b0180000c1600040411041c4900c0620035200768080403446191010060410030190a01c2c0421a83c4030040000401c010342c940354100014119a111651103d00398603041c02c8044400000a01a51050008100d190742c05254141140c045013028407080e120707400c0040c0500350016024082d4070847c000f1880d405400110390721034001d014000c10041e41c0b078070031035410b8a9403100210005141440820082140705c072280c0703101c50340c0604280d0160b954190560078000210703010f40c041020740d800c10080500d984400c6501160902c040c1041c0890400340e90805203000d80340b0003c00c42802081111501d0099661001e541c008500f401115007900c2c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280921645 1250 280920395 280920403
    0xb22080c0d08090607030902150c0705031903050927010f18060807050108090f101a09060d0602030a0b040e0105100e0c070609060b040207060b031c0c110120 69
    0x40c85451600c6460240c1d980e151050580a00854002000d0005600c0f00300089002d0f180c0303038030147d134020304001e011040c1e103005034000c1c100605014060181e2915082c20103062144403140e04a0087c2803208444c00030b603028044a840007404c4400c2c4902040c849413620b54100c044602605103400f10002040b1f003480079100e032046412486020003070032007a16012054038400d1042100e56845404184103660181e600141d128400600700e0742c211000c0088140b902000c52a0f41c0303030555803442400b66001e9031807041444080280c48075091030405102045080e480c2940103400c1c1035010000c9017888a668100102180c4014001d00a00101260300d6000340310503129826050000100000d581c000c13104020310172804912400d042419545840c0080c0c0001c00044035056511407040101e503860740701030140c16004140c0010000801d005040c94121b802401e548200f00c051007801c0a035034032045100c22380c0e0b849040c3d40403041108005950016080c6024070a145a045030201c000e40001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280922895 1250 280921645 280921657
    0x303120411011b06051503060106030e15010b091002010f0e07050405010920030c091e0109060201060513090c0801061d152d031903090e0c070b2208 65
    0xe801640e4184801900d4a4519190800030f025102c5082c6010883c4e507401140d0200404c03060800b15401403000a0500e1002d0300102d0200356121501e0072440c00403c103542c103481303050012444a50608888040a000d823004403031241c940e0214081032a4800e4110184031480341805110804904401030b48a180381d024180c0500d18042c0001540300141c0102c4550f224203401c0d070115040490705030781c055880200707200300d0114200840c01c0c80303460f041c00c101d240340314200100c00142c001800040c1000c013194844001c5a051060510203550f0b081001d59078034076110400140d0341010700c0c0180d10001164007240741946041c10000d80012000c90301728081003204540c0540c0d5645100c8031040c200c0c8807060b1608100b050b1420110700d0f5400100d0001c0c44045403a4044584200c40040d1811006040ba44134001065010303104141e005401c2c4406071162000c800c42c0c0b0f191242c200e04032030140d80c0d00544800306000c0410040844405802c4102300001c030030074070802c1d042c1001540c41d4005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280924145 1250 280922895 280922903
    0x1c230c161401050919051327110607030c0f080406030b0108160c05010603060614030f01140f0a09050f030c0d08040b0402010807091203090e0109090b0a0c0311070b0106080c0307171503031204 84
    0x5070080c06141c8500c00c09030204e00da440404ca5940c90f0402c002d000141d049072204070144410001c40700301207401444ec001c0c0d07081c45050000d54a03414854000e040c0c4545440302410b103d445001d1000a00c800c480300d000302a5146080384512805060640c0035007442d0344058082c9182c100b0108007a513140b503124000d17880507001c0300c1d8001e4000c1a80c80c00c8503c502080c811300b001c07481c0450340d00000840c00c16040101e212000c10311003450340301c45003803443c0c03540c91508940c000070b40d0344110346d8180048201c80030607050140704d91806c0c6c1c807640300d038200c0280000d041001c0d010000302254001c040c0341c1c02400042d03e2140c404091440e000c2d0040780c0d03c1c0200d41e404400c400000803c08064054483c281d030b40140b0f000f0250712858581009082088500720074940c9400c7c4406000e1074180c0035000d01406020499495450103c0113091804c3c007410314032001c00c0810400600507040401890081904558103009a80c0c0051030002a0804800d41d42e06010000e03c42c541c801c00c101060b409907000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280925395 1250 280924145 280924181
    0x5070608130506060d080d020a03061403030a1205041a090705150c0a02100e03010f0203040212060105010512060f0a080102070c05031c230c1614010509190513 70
    0xc1e00040c415107518810010442e9001100043c0384c1e06001c1c0c007804840e407268100c28100680781c07c0040c01d81e0000001200001e03a1210100101c4e02074410454283c80103401641c035094401c140180701107005903c0019130368641c4c01060400403400816506c0840c1c0c44d0104042d410010700303040e1190707014130600e8424840e180241d510ba50b40441203a4600320098020301139000d403035003803100c401807250368241071101000050285442c00c2c051090200c152040050742da24081c0b04002240e904100d4803681d5501201c014452a6080801c96100e41c1000c0c900e94000e0340e4032000140310310b94080c0d4407600042000380014032071105401404006103e030148044950b15542496500c1607101140801b1028024080c0e03c081e0007806000e480c0781e65000d000749046a40034054445a010030703500c4146178440701c001e030540c0d4548150340d80074100c20a1504030148084000034042c1c040d000c005480381241940040103680c0303084080000b4a0054126642e210401440c80014070b4541d68001d58000c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280926645 1250 280925395 280925401
    0x408090901030308340c020a0b0c010f0f0203060303031b0705030d0504060c08040503040b0f3903070b0610170a02030a0e0c06041e1a0717120105270405070608 70
    0x116494410082410710000c18a000340389004071100300e46e035401a84c0011051002140b00e8041400521080111300d0020400e03424000711f0070121405140300b8107280e41705100380203003554040100c94026440100c464418050f1005621192103144401440d5120001d01d4003018100d5400c454420760203102d00300448005620162104c41003141c0080a03600304110920000909001824600082c2c000b1507082c0314860910400c4500041c0d0b01104c01000142c044002c0100381d00680214484100910706116142d44d0344040e280e405041070b0300c501016902c088103203200740c40c0d1784a024a400030714045420152002c200a50090340d40b02ca245d82422803405c041180080d2061119501400d500d190614290049030700c84070380c0f070b020002d46005400c0042d0ba080340100c0c0801c014010060540d50300c0081ca41000540303607814004d00360740d1040c4006210304940b00a1681103800584001d04607800d07217074140c000c94880d030414030102c05203075090000b407190004020080d0742d202c0e1140802a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280927895 1250 280926645 280926691
    0x5100311031b01050a02030d0617120f0301050f120118050105060604030201050f0c011b051201050a14040c181e0501021603110a030204020a0809010b15070602030408090901030308 79
    0x403401c407400c03842e1050380e04600310107501c510000d04c1401214410390f42006000f0606006450240d4004c481b021780e01c4d40c0e2195050414010140000e0b0078848103031504004611620082c0014810140b0907a804611002c15480c1c4070aa4200740401400800549100317482000c001250208103a40a41c07a210028010341000011039064a805031202400d04245034007610256220000c224010754030f0f10300d9050740804802d41d040c0d0756212074542c41d071a107500c1d0b060003d409205a010074441c0b0100d284c100681d940a580c0d5420020741a600810791030b00032541603402202a003075651420582031000507244008011075850a10003150b82c0c102d00340e4a5004980d1204944001035002181c0300080000618901000500c0d0001170a00000760381c0d40d0b00020200d81060b0700500100b0000003c0210030103080c4117074001c0c4903044844640c91449848540001d01480800903e40d0f0380c00004201404108800e032102c15200610040132981c503880d000b8100d41003a40c40e01343d03034071074000d40050b40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280929145 1250 280927895 280927903
    0x1091d0607020a0209040503160b0a0c08010e06040903020c1302070c08060f16020124030501240b090a051509090f0c0711010e030109050d0f020708100914010510031103 74
    0x70311002c0e4010007010141d9000c000424001500c22219844104051a06004031484400312175000d80e1081d0941d2402d035602e14161007007400a1001c000c213081c014000609480811070300444107403800611180a071a05a250002404506522180c1210308219002881e0010300c0710034452a00141700035910382616030348201c19182895400c41000001d0b0418219881c0c12288550340d00c001300300001c1003250501081000c11410088000700791090090110034080c40308507402450503003c4541e0f022002c08981c000c0741c007425100c2c010000b034282c03960380e0b030498403005400010803010740406039a11440b5558061003406008c3c15002c00000d500c20354084d8014410000140c4e200d241030403540d0360500354000e03800203d040c03049060030060079482c00d110707002e0721901c180014500c0c04451000605422001e184403801c550000310180301c10100847c0d002801080c000000c984009180b0341128a60310600d948100e42d0700e0003040100c1599038040c0001120b018101420204070788400741511 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280930395 1250 280929145 280929151
    0xc050a06110a03030221010308120108060609160201090206030903070308010501020a031b06230405070b25080f030709060818032d0d020d0c02030310061101110301091d06 75
    0x12581180c2c0e0040080383c000e8000300b02590800030305055442428a00b14407010083e0415120854003007400321119149400c15809843c000005052034030307290b400102100002046001250807031115092158000d400541d405a801421651a0700d07120955560341c0d00314001c10342c0010f107810000140e03540041340034810103805644107200207234404801b0040c81513405003221030700e03500c4800c5680c10100149600d02801940030190b01418281440352808040c0c1e0040c01b031052080228103d24042e03a24100300203144e4040000d0a00041e003418506ca000c1c2101401c201d070b070004100300d080355210460b1410b461090f00c4591181c0c48141004003002d1030340105034000d0340100210423460491a0000d02d20441188030a240d0506114440c00d15400110b00407103c41c2c0c0226400341800c069010342003050610b07100550a52a281080d0543c051313403803180200740720076610380b810040001e410281c90541c0706a40680d81396521010b2800a01c0c00e541d05c00080c81400c98402a500790200e01280 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280931645 1250 280930395 280930427
    0x504020f010e0d06020a140a020d020705041a04150305011112010b0f1210080f0304050f120601032004051509060406061d0d050d0c0b090a120e1c0c050a06 68
    0x140b114041d542c3e000095101b4201c001c1841201242c000c01814004000e1806e044168090300e1859480e01000e8500310f001c0d04014455070403c44150402490020404843c042c1110085845850284101e504201e150000b42065003030808000c4445002e070001c00e2041c150300020325440c0e17070700c07100c03c0340d0346c096a540b0040044040103084801c0d032403240c125802c0000c0e440c80d0f568480e42c3d403040606c0d09070014032400003904041400c000e54034000c0e4852070042800c0d0341c10010040b030503054076220a014080140550f0b6282c0c403102c0c48015840240c9074140025100300080c1c2042e0010a01003206287c03454803ca99810019a0605160088200315261511024480c90380200b0121501c0003800d2195004031144803900e001c120208010f1584d82d1040c2c65114161009040501e01d00d003000303061000c1c80d44481c00080000e141c0c9600314841e18124901040004a410002865510750620b00031100410148000a104141c22000308841003220080a0944d40d4101942d071002c524038214 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280932895 1250 280931645 280931659
    0xa050c03040f020102150f070e040501051c030903081602040605030f0a020f0d0501230c0c0a080a030908030403110607030e0a0215040305030a091a0316141c0504020f010e 75
    0x50000b01040003881c64a403050050300e000020304a80542c00d024100c58030100b008201d01130060654118440c03074411101620140000c0d81080e01040740c1d00c07030300040c501481030000307854400d00d4403503107050000e154055001941d610303180c030b840c81401a84040c00d900c03c0c1e00d801000030380c0b4580050b1842c1c01c80400b001030000700c100d6808001e00200e20100441d00311800d041c200001400c03c0c401d500001ca071110581c0400181c4400303001e80110010b02000517000200283c607218a40059203a03800340d800203100c3da41c0c00d0040e030101c004c3d01c0c00050040c60901c001c000d01c4200354000c48800640940f0100310f840360780e18200e04905580850849013100d400c10a464405410406840301d0034070020b004030383c0341c02c0e03403039990516540c000c1c0d040748000340d21a0300c107000030325091903400217603821074a5950440c1000303c3d4403084120000501800e00070400c800b038001e402031703105440c44000d48000002c170b0b0346541089074002d004102d40480c400c60b481803601c1c01540c0621240352103003101400303803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280934145 1250 280932895 280932901
    0x703061d040203010e1501080c120601090e0c040e0c090a02032202032b0915320d021305030a05150411191706011a1b1b090a050c03 58
    0x14040d800c0c0540166050754179505042e03c01001088410110325041204600f03541c0760503515400c090101c41c10750301c24103d03110440600b41c0000ba009065500300180003c01d111000585890011100210350f005428001800814a0080f507105140700c016a4418800e50b2128001000c0340702c12141400c00348410b0645020410302c6030501400703c1d00c094205c034a91651800031404010300f500f007014840004524900b0180e910015100080400104002040359040c6002d0170500340e2900c04882010050211108000700054440c0c050148030301540c1d0381c2c842d14080e10040c1d84035443e2094940322400c07000856040000e840c18219801c980a05a003007100208400c04038405002a00c501d1044509000150744480d605610300c124460114007061401c45c0d8880c00b0144140c2030f9520780c00c0000100b00303c1820182c0801860840c230a81956a00e03104944000100c02c0703801e9075205d20480c145070041e0029041901485e80d801c40c0c480405550319840300c400c0c0c600c101d80c1180050028008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280935251 1106 280934145 280934189
    0xa0e0f041e05191b06020322030c0e0402060409063b0c09030304170303092b0e1804060903110a02090402190f0308070308070306 57
    0x140500c07019940c8819031243c81420f81c90300c2460059150108104048404590408603200380001c800d8407060002d5480c0c0081c418880a04114060307008924199070f01c1d0400c4943c001501091030b4207100d004d042920020b03008030b800c83c0301404040340c0c1820a00540d00a440189140f0f20100c00c50300c0c0f91210014011406150000311420140c500031080c7c0741e242c1d0101400103100e58840310032010a00c0d601c2158405155103400c004800d142d4071010008500a81c410340855426405448650206990f89103040d200750200c007901700c0c0740b140546c61445410400904051040c00c03132181440411004690890b0071903600c800c403000301600314022054500050b0000c0c605901c9590108001940142c00070340f00b100c07090444a54003008040381e4014100880300041101d5803445c10100d00d4111103021004a10ba80c400655030707134031900c0b8200c103c40e180040c1c580402841c0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 280755395 280935251 := by
  have h0 := BRFrame.cov_init 280755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280755395 ≤ n) (h2 : n < 280935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
