-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:01:01.713313+00:00
-- url     : https://prove2.me/submissions/5da2e0cd-0065-4ab9-a072-e383ea4a7d33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23201444 ≤ n < 23381301 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23202694 1250 23201444 23201473
    0x207081b04060e01080a03030e0307060203040311100c090b030a0e0a03020717010c0c030e0a080616080c04080705120304030204050a02070b062413080708010c11010b0604060507020d0204050405 85
    0x6000341c0041e0f030070f1014030006004000000503440b0310302d0f405190200f00b1040c600d0782c06003980300b01d074006844140000208000d05030414441c80d1509190001c444240d81400382c200105c1c2c004c0000780c000038150040801000c4c0c501005590010719441e0001810030b00304052910300100440200c015802000c2c003000503091141c0c080d00ca07003110324020700880041040041001b101c490000b000c0c40010b2658803443d407502d0b040030000d081d1440485946041500c00340c3e0790760340c900f80110700054404c400074101c0360b542030640d800c0b035240c28014440c0c14200303410450060b034500368007041807100b400000301503035a41c026280142c1e500c4000582d240b4081c01d0003000340d5001481140110450080d0441884010134450b03c0701480c0581d03c2d84411420721443e81800300c6038014055881103102c042101c16041d44550049141c64a440343c0314668445a42e00340d48e04804203d521480a000400a09014a00510900d4401010950007581a600280441d071050300d06981d1940142d01c02d0505a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23203944 1250 23202694 23202701
    0x604050c01080703020a0806060f191101150e060114070501020a18090905060c0903010f02040b090102010501051516080c030705010c08010504090b0a230403050a0e06040302060711010207081b04 85
    0x12240e80b60035407804030424005400d0703150223010180103c000040c2e0081a0748224255081c07140c241c0061034981c1352980c1c004084481690200d4003075442c1800e40c0040c0c82c0c4070143e01c0112403660003146104e0780d40c5401512030810000811035450010803840000039420300c010929040a5104c488d54107820307800c0190012000d030040002d051402410002140740050003950007040078031080c1e0703110024004a40500310306a003603a0010b00104012035840000c002038542a0300a074002c0101780ea0751030030049010481404030355110000c2049145030300d061103001320b4090264a98901c1c240c04a441c07103182d039204103c2a04c40b650f49600f900145503000c60403e00500b030448041c050419107803200104088013178024051143d440d03071100311240c9486c0b0041b00701085042c071080e40e0f181c50f04010342140d00c0341c1c203000006803030011107a03014a803590030303113080d6500078043d141044143d95602e1810403812514a044d031184450020b01c4060401c03903000080700c80c61580001040a00500007138 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23205194 1250 23203944 23203951
    0x50303010f0311092401141c14040b0f10030c06110d02060c0f091201110705120f0f2101090c02070503010902010e090a060918021804050d0e01020f0604050c0108 71
    0x1891181080c0301c0f00071a5072914640301d44a005110004040031030040c1c0b40c5030040c41d001f140a030004625580760040c00e980329554401000c50038015209060032617112414115002408600c01d04041141c00c0191a1030725404040300d00100c103000e4490b2250721592059078800310000e0b5400c40503180140007400709007010002c81c0010211801c00e1400804907009481e01c03404005804030b0160f0f52551400070503110400710380000c00000001e2094400140d115190903181d0384990441448607002100484441d65407900945080c00c1404c249504182d00414042113210104220410f25070080c184d594000c0402c0c0d07100040300d00d25050060f0038030a403680068404d924190030b40d000340c1d0b040803a0800a11088942a01aa440030702c010003c022030741044002c04d01d40070380580000d1000c0c2c100e80721a8001c5a00780f012450100043d0400e0b00100e8000b4520b8100c01e120301d40140c0200c002c0080c0100500599408402c50109640380c075074121800d68080d8823a00b500300301560000d1030141c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23206444 1250 23205194 23205199
    0x100206010311010507030504180e0f030c0703060b0f120105150405160302030403020f030c010c0311031009020a0905130903030b03030415080a090206070501090209010b090315060d050303010f0311 86
    0x181507140d611425481025081094103010001500c0010140b1540499002c0c0c000070341074219000182c407041c40141160355122025208140003040c10340b50010036110a030540c04010420306055540361005042d403007403429004014142a04103540e201240c1d4040400d41f50f0000030146050005201e0700204010f0040c05146400181f00a60038841030b04481c1340c4031402c0160f030f6034030342c0c0c58100c3c038003412086030b650140408540c4540c00c08040d00f100c0d0055600d9a42030003401c3c0b00c00c10030b4406101c02c1d5150440407080c400c0800030b0000b29000b4083c0340c10a03040100910341c0c0e480104030035100c029260301039540d986481c102056014030401c68442030540040d07040909016845010b0300c1841c0074041071100400c009030130280550407045040d5400b502d510b0b00e43c4254540a03000c0e000130481203100303490320000810491803100c1601c54620300200104818504130300c1652070302030041c05903500700d842c5241240c0131076000c01c01503000f41072443c0c00821503403542c1000038100c4c0700c854041d031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23207694 1250 23206444 23206453
    0x9060a0b0f06120618090a0201080c030609070e03030f04120501050106020609100e0a080d0c08091f1109060f0a0906051c0506010903122a0201140a090b03040b0103021002 75
    0x1680d4a54009403014a8400b80708222113840765000202004d01c021214810303850480d0401c0300010780803031405580c074401c1c2c8a041454480c22100303801d03800201d8041d600304001e54005522548141a4902410000340070b480c035244c030f10440401c080d4010b070420003201c03a4000d090010404240b0450b801084107102401d01c0741400c02c103a50b20341e1034a5118103071a42d25454215660745042c86075440055200b1101543c2e00c1f4501c4c8140c02074446014810081003601000a403082c401060345180340389102e140c03002c5030b200280510300a00c0d41507a80595100240708030101500e07180b005044074110b0104058840c1594403008080300d80c250000404c0100030f000c02904102040002d003002d41c40c07118003054550300d1900498044001d0392020f024108030101c5003074156044030261408400481c1e41d41419100200764118601c00c00400034005415400e030202e104c5d010754090710704e051032850300c81d005540ea501c09107000d0700203403025291a0503560042085250601005420240500140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23208944 1250 23207694 23207719
    0xb030f0d02060f0901110d09020909070333050103060b0901120305070f081e032d041101120603060f0c0309020f130902030a0b0103020109080f0c04180b09060a0b 71
    0x94442c031001d40100c0240083d0000b16041c0c2900307410625010203041582c80d200c5511413007441c050020044281d028221034008505540000b03c0c090051f1ba800185041424828040c07c0c142e0000c000800d025110b00c007921300c180c000032400303258000e6004080c0400d981e116482002031140041e070240c101292440701110009401106a078900c030f030000d01ea0980c4606909182c5541c1c450038000750008400300340304940301c0c2e81300c01c084c50140c1d610f02c041150f5002810700c030b110b1108044c00012001580180020b00003000010130f207080020614081200c039140380440f9060b5801500220340c0d560311a006a0340c0e400042c4a601c1403100b5034582800009080e03000f207901c0e030708015aa0381c003800d0903442c6070301c20000c250044001958007030125070500c007141c01c1480d4081000c2c0401c03800205024030000d8600c0000600d075030801400030180c0707620b0541104000c010040b68118a44403a1204541c270701042e4440300e82da111708200c6c03010300320500d0010081c208075020840d1407440307501d16900c2c2c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23210194 1250 23208944 23208947
    0x30f020306011e090b1305040b0910020703020a150b030a0302030a020c0109060e090606160605060f1801140109180b13020f04030206070c08121903060e060d020d06020d0b030f0d 78
    0x60104075480c220300040c0704080750020400c2c040400900001c4a0304000501c400c001084640303e10528815060701c4bd02c2615900480a0744150a03024006a0001510102040c4d0551825075885e41f00c0d100040c41000460100341030000541d810340240e003000c070f1243c0b030054050100000074002440c0c142200c50601001401d08160341782c07918042c0f0003203400107010b03072200381c12120410006c00303140e4800700c0346203403500c0601021220305015020450b41e041030340c240004281c1c0044d03a0340003004030b5a8288400000d00b0034052140504115141c0350000d07456240c001e6068503016002404600206941c06002c3d244003005035070407109104000d840c01c0c40f03c8481c00c1c1c40c2a40e904a03241e82d980c0c0510f052a015000c840d0300240490300800c0312020751080818001d03c080c0301d070b84268607600c0d20a0380c0c0a50403a4114800c9100018a000c000303100c0345040c880504803544001c1100c800d814198031500f040760409482a00410f561300141006450100218400440c5100081002e442d01800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23211444 1250 23210194 23210249
    0x10b03010605130e0c04030203011104060c021e09040b01090c09030c150306050307290403080301060e04140709050120030a03020c07090509070509010e07081b0c0601030f02030601 79
    0x1c0304108240420701c804040c401800c3c00d001460480194001820000c11401044d481440200e1003907103420220558070404005950849409803181000424550240040030048000000c2c0402c808242e406069917820640c6020f070740241c00c60380b0a036040242c140c085030039000d120801d1180004e01040025070f00481882910f041036a03141541482220079000342a04d5084070f40d01d801020f001003095500c3d84041100d040101c207000f44203c0100200c1d409070f11032804042c0101e9002c00060000078003907608039040d00d101400005004060b440d40d440800000d55a940c001201304d1000c20142d03a100c10b4803455200712035183c880c400406400b8940e00d00c103000d515000e040d0049050034405006000041c0108007200c000d1203140342c95100e1b03d841d400c05002d41c5100d07201c032a0001c107078000d01d60840c600c00d01d0951290110b070303141e035500380e1420b96880c44c903140500004c000828a840087c0180c0d80258800d0302050012540c0e44101828500c05802c002030007003c003003903d41e0f1803030100d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23212694 1250 23211444 23211449
    0xa050f0414120c061005060403030507080f04120b01030c09110301090b01140406050408071401080402010815060408060f13020a060e04150e0402040b030c011409040207060c0206070215010b0301 85
    0x1d800c10391140740320341e064200400d00070100303900c900c08104101a44008219940f14038000c2500c010030307a44074010000d59000d41c1c040a0001a0240702c80000502c4940080074948103100710903040982d00d04400310081d2140c041101c181280000400070005da59194001401c13026009014039500e5040040c580e020500c80c203246103486030312131f00c4940d00a084221000314010011603456484203400703043e41d401442040d54510406a00041c031648103412140d90300070507503c3c65001c0e152900110303101d2074040e1003020b0710340211248451580c1c0300b0004000511002014141d20315007074000d60140c404c0100394208001c201d2100c00e0050b035031040300c2025030700fa600380910400b0750880401c00800500800340c0c100720313038441c000c2070b0740358110145c5200380d01c2140c00703100e0b4402e50b200740360725131116991050204210000aa807094071b004041c000c4400040d10040c248401500c80a00781d1300740c0c03c0020f01507042007051004c030660501402c1d031540b800c20b450000c40e524041c401c1405200c1407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23213944 1250 23212694 23212703
    0x40501061211040302060703090e010501050304020604090506040f06060306080c0405060f0618030d090806070c0b0c07030201090609080301050a08060402010816020c0d1101090915060c050307050a1a0a050f04 91
    0x55041400c02d00e66a800c0c1c4000c0c580190825465507560b103800342441485006860903509030b0400000e89601c01c0040301e1245601030404e50800f8a0884e916010b404040d060661180d10b44500003480c0c0a40d00c113120003820b0541e8081b41e4940b800008605218880c010f0a003d03608090070800162180014180200029243e03281d8444407020f485440154550f030362545402606404640e40d94092544415642900e090316141d865041080d82d0303081c44d41100a1286000100040900140001034008a0300a000110b03030201c03181e540204450b255801110081da002c4014031150610f914041c003d4186d107001442c1604150b000a071047c0c0000b0800a8500c4011180e0a80d40384240f0a0441c4150060000c04100c2d00511304000300620a805c0580040c001c1000010382c100e060041107100c101d02010740019a08042044418000c086410380303c038403080044100161040220445d41400740040046078800c40005443e8120090300101040c0d041000780040310382c0d8440002e030043d521 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23215194 1250 23213944 23213951
    0xc18010302070804030b0613060b0304020406230909030f03100905010b0408060a0c120203150f1008150103090c0e010303020c01080702061f0801020f070212061303050310090912020105060405010612 87
    0x1f1140003440c42002c0d0350140d00d2803418102e001038117601c07020107107001382d02c222010b102c4661210758500070000a900b00e282d106030014111072890401440107508002c2c0316043d20702d04500c0080b0408180c0c403d444060034045403182c100001c00462040303501401402c4092482c19203006903072a9207810140c103011032580d5074001c413051a40200510b100640c0303450700c10754a0345081d03440789030f0786558030300c51500030300501e41d1090340392600c00d008002c01c5206442c0c040003910361076651032030400400ba0745414503035030340c8a14001c11f110300f031003600902c0711a581110560451400034105040718624506000f01d80050242c0c042c0c01240a591142000d024001c1880c460744100c0b00242036940060050f500c00601442c1468842e801000354600940b41412044541e40803a5914070040310345400410b040020341e00068030810040d0303008031640041311103080c2c9814040c0c00300c0f070702808204c580c142012050b0444980a0064a0707000500315010062503244c580040c15490200c040c8280c0c1342da4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23216444 1250 23215194 23215201
    0x2703050a09090603030302070b18031204021c12021212010b0307020a080f0403140c0609060304030e03011d01050a0b0123190908060a09021c05150c18010302070804030b 74
    0x821001c00e00100003840c0107006640d907909011b40298050401514000c2c03007103000503440030001001c8803000074154000c0d0301e03100004d4451280c048001e81704070383c0078a0314214410b69420f44420360401314003811072403140c1d01410301d0291800440403000c0b5074a800502135014841038010b802411110541d071669941c0e80d808104070700b42207680b040100381d8000440d42402c0d201111000d0400e40344110104d092086004018076079603441440b05a0340b01c23204010390402428001c0c042e40e0010312a003051282091071000007030944031038400e0024114021407801000280900409400c01c5030420108084422180001c0040308076840304614840360500f901c20780b074001d070102c45a1058480f01894100c0400000400c0034502c2d110300ca003d07108100c007040d40d1308521310950102c941d005103948000c2070b030351040120002c2a0b01d410b40d501d00504d015006175200c170139030301403064000074520344c1c0d01c14075601d0040b00c41c40c088400d2030401d40b052102c200015482c1040754180c0b80c1200350000300b0b58 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23217694 1250 23216444 23216447
    0x80403030309020d20010e0f0d1b0312020606090f0403080f09070b120406060509090a06051503100b041503030804020904080f070c0501030501090c0c0609150e0303040203012703050a 80
    0x201c401c400184080d82d1451042c1c0c01e2000020203400f00b40f804d0342d805151003a01010030091100c03058400d903202c9868070b40427001032018000c486800e282c840030030388032545c0c82d2101c0300d00d0b1110403807801c0540c10010401c02a40352405505500071004400220141000e48009060420050005a20101c40c10100e28600000c100300c4006003160650141c0c0d0380070b0400a11948041130360f040310310504240b808039031450030354101845501810002c4c581d400e000c1c3ca8076005040b01400c80201c400c00882c01070301a07202030001089030344184001044840081c0240000c45085640140001c00e0144d424400039600408464000b601101c4044071902c07181000d142500c908140c13401c03103e10001d00a410400388400404c102d070f41c02d03203040000c1da98900c8003400b600c00942c82180040c60122449000850550281444600914880921441c1041d101c03086800c0b0071400001d540c0040100011440c0c24028240d40f883c841200300302c024202c81d8116240d600c0011b004084c004040351003400340d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23218944 1250 23217694 23217709
    0x403051c030b0d0f0507060203040812030c07020a08030304150606020c010c0501060e040302060103030801060f05070f050106030503180f0d11060a020123010315050405030405040e070506030a0516020a08040303030902 95
    0x500c4000d03d00081e041032032520110f54412910120b8081c02800030008009002006a50481d002d480103400303d103502c65000405984000c01c06141c9a00502c002c40140e02e031600380001601080000315503905150030140500d03009200f01c024207509200302844041d50106480028400a00b4504100340d0385182090140001d034100b0a100b001d44400c010034581d00180e00780c1242c0c041d440d14000c5903216a4212040d0383c01d900d00038040786040040800140300708034020000c034002c400026815403070355580c0e1b04542c030909040b542642000320b00792181c9040000003540502c12030300000920025500c10002084c9480b0403482414041201c0b0792041c000e400281c0444c030208801c6010300320701456240458800e00040d1000030384110411500c214a101709800345410a00441c101454134082002420701d0300c903000034602900a001581d40c80719001385004901001010650b4038090100c070004001000d070a00441d8400303450b890202c1e2070b83c001c60b0156070f00b5180c0840c041a085c004a24107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23220194 1250 23218944 23218961
    0x9060904110a09051804050c01050912060f010510020c0913050703060c081501030c090b0309010e0304090e06091209040b04060b0a020f010c09060206010e07200706140403051c03 78
    0x58280000398550381c2d80d403000e02c18058910440da10700c003002400c01c146420b600c0481c0d0041c83ca0344803d001c4406076004001421501e2401000c040c2e45110815486042100940b1f18100450f900ca00610403441c0c01c1541008034074441c4020802e0403101e04c0000c00f001c002800041019400e003601e6004c1c048140200406540c05c00340520029501420042c4007040480d455484106142e0703001d0842d61082c00740c414454010740da60200181045484550b6510141000e1081c0d9030fa5040b1604202d02031029100a04c0c0c9402e00098001103012a642440402000c0078540d40080c290030101000110a0340c01c134100039030b000100e15100c0c1021800401e400d4203e09001407000c102d0b00442030b40001c520040c9401c0c0f40c02801401d2210380243d8180440d4000d103000340c1c000e04010300c0700f94541d40a2070792040d86860710580f031081154081d46804980102c1d00b4450308100000d02101d0342102074200307948048240d4602d0189141c0700c0c00c3e2110004000e102052070170080c0d04040d2486601b00d07880 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23221444 1250 23220194 23220221
    0x2f031603110f030a05010504060b090103050702030409090f0b010801020c0304030602090102160e09010605010509010e0609030a0b0c031005011b0f0218090703060b0f09161107030308070e030c010509060904 90
    0xa403101d224802e08401c0e0821101d0294807420030001003502d003014000d92040750781e4500708a00b01110755005401420006141104501c810700c000101079125000b1501458011000d10189444506100c00001c1d4145c00101081c0c1c0100b01880300c5003400000c85040f20b401c10300041c0c6070003a0000403820011410380d0790320041481c020105039007a142c900c090045450f04000c00115036120019160741c020304000f02c0c08220141c56091440c01d108000f0705da402c0004054072403200f0309a03102c42c1d01c400d056404a04800002c000c200113014400c01c858041c0000742401031585456800703507210070990380342c000d1207952688040011501c401a4008081c900c0103000d0005140c02091107a4818044c4070948401c0e0078000e03030b40c40d80d003018280310a20b100c020744600400d58034503041051040b42c4012039020001a481d081207822828070091024502c00d0341d5a02c041e0601d56402840c95031311911140c4250084003040d184c0303a0300700d001c0764050b060a03a955500c66003540005002411283c1c4541d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23222694 1250 23221444 23221447
    0x13080d090506010e0a0f0e0303070c020d08030703050f01081204032003120c01060b030606040504021303060903020a1202060f04060b1c05010c080f13030509040b132f03160311 77
    0x440440c807142013441740c440c80008006211300311003d2015100004140c1e036850300100301003960355101da00f40450583c0003030a500c0341040140d0741c10105034402c68603900042e07521014081080155100b050060040000410380d843c083d4036518007902c5a440700402112404c1d6100b8000c13101d2402031110240d0040a4030840700355024002e8072076200c40d8148813194039258000c142101540203507030042d9409881c06003428281005c0c04003d51005500603010148001c0000c0059640d008098040e0700c41c0d0701900c00d513401490201403c58000181406540200d4200000090f1054025900c2038120001144a4107008045a54010300c130032107114078036180e0503c0040c01415041001c148500e070340c4000280d03481ba2403204090000750380c41d0780c0f4403481091030400310f171042c005020404001000000c8002d01f1704005245510a0003c487c402c5441c0d5400001d0440e80c150b8040c1600e10010010408400c0842e0241c1c1500c80140003007100c880c40740d460300010b8401da001010b2188010002da = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23223944 1250 23222694 23222699
    0x415051b0613020a0b0a05030c07050102040302031009060c0536030d08010312020606130b03070504020301030516050102010c0207030b0c07121806030c0e0d1704060306180513080d09050601 83
    0xb00c41203000c0c0c070300903400f81050301070000d007200f56401118400da09a6580c0307415512440d100801c07030741c0081400d03a241d6400744000310140e40c082c40b00c0301c042d05101c04001a510460301d0010180d5801c0c42800060010a10206046850488403000000141c101c4c0e40e1000341c0c0040280c0d841108000e2640d01480350804004049030803107019410780303000e444001021000610200e955950441e00e40d03811004840c04000e0903109034210f9002d1010081c02d40300d400707844402050882e0400d9205031007613400815224402c0e2110039000e80035140a01c001c0c015003462078800b95566031310340f00040c4140c041200180b40703a54400103690205900c080040034500c03030003070010708020101000d948284003402000505600074441c0c00500125078856080900c000c0701044281c0840340c0c4207483c100e04000001d07410007803003002480500301c907450011308030342000034a074140d1544034002c42103d0319000a01424041107203444c03100a44c81a03040b5078605904068a02800005000500d54810320001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23225194 1250 23223944 23223961
    0xe06160b160e0a0302030c0d05030d020d020417070e010b0a020106030b040c080d080105010f030c020c030d080a06050f0306040609140102030403030515061c0506010302040f0e0105150415051b06 85
    0x7696014503580e4900c03440c01d280c001000b400012620009605510000d21000035042030000060454001c401381c90801101030180070a9a1100c1251103100e40e0004090080b08101d4115225a440203c000c20440b810840e40c1130480310117009080407a01c0100e100d0703948910035041100a154080242d00d0745041c5072821a590903c0f03406820214019403011b41035140c41a03420710704030b030016581c5400d1294010821780c01804000e070482c0460007000202c1000c1d0300c080044902c1e85c1d00c1640c0c0c100f01441c103055100103d684c1500050b105031421030b00e00e401940e001960a40058014900003848020740c50081120070080050002950020041005054065020354820a02030250b070142c41884000c02c96144a9954280d0302d46900324401c20341d641e013591080e035000c501030400616280c0c81b450200c86040c0c03981d010910581c0c0340c6d0018400c0c1d0811508182154503045a041d08103410074110000403140035004c0b00c100320020510066403000d03100c006c50400c204009441290501e01030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23226444 1250 23225194 23225221
    0x6050d0b01053a030c0203030c070e01210813030c031a06011103030f10080a0501021e040503030a0305100306020a0e01020c09090c011808010509030301060906090302010e06160b 78
    0x941440b0b0303040280c1c0400f4401d0000c55001c3c45a440301d28640107401c1955001c0b5890b41d001109400300b1400c800e03441d0041e10b0030002044603a29240040c08424174100203180c014105801140f41050560081040821106000e40c82a507000640d203807035150b00c44402003412583d51001d807056555030000814000e804010000c2100304004024140d90380400558a569141181d07050a80c000c10029000c140c0440325240c001c2442080000c0759a9682002883d11031100000c1e280c90358002281440fa01d07014150700c001d0031454401034105440c1c40d00081d20381c0545481031f41031544410004002e420f10410300b0026542c0302104644507052060000e25660002c00d4141c0503106101c00c0c400035103000c140340ca01c200900c1e00148000040740004407038401000001b0318071501c820782d010500003001e0040510400703240f80203584941c03402100038040145540130200b0321840020901c0940d80c032410100d102d0b0310680e241955201c00c90b40f1702a400340e10f000003500c1600d4010501c42406c10901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23227694 1250 23226444 23226449
    0xf0d02160f110d0c1809050607030e0606090417031009021612090308031506070209040528030e091e07030209040f0209030c0f180702060711011a0402090406050d0b01 73
    0x8020401004a4000c1c8521010b0b5843c001d071600480036003c002c00c1648142c0c80c13800e41c1c014600031030301d02c01a81d5160300e80401510700b100400c0c0c4401081ea40854100400c0e87e00c00400caa20b1400323406c107525681c414010041400c407034000700000040e012501e400701d0600609107241c04541e580d50008901c2000c0c10001000c48186689201e0411007510540d00d08080c0da402000b001d26545441000e04da4400e11401d03080c0e0020000c2c040d50b800340c3e0300d020400344150b000b0130281540040034000e070203070314000302d0030002010604002e00010a50080307600c8003a0805407801405c3c1d840304140703601e407203500c5242c1c1d80b80d003c3e24074101308400d40c3c5500540040c00c0241c6051140703100d20303003a60381a8000d0070032032600b5a0040180d0b41c00d9240128203020341c2d20024000d007030b1810540480d02580d140031a9110050703480203081c0907a9650150055800e0300e10f04008005d0200c482d0090f500030352460207100d1050740c020a8004050766103a2100c030040c03500070401e0a11940c1803a200c1108402413 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23228944 1250 23227694 23227703
    0x90f0d0f0602040f06030b011d1315030501050f0c03070c0311160503060108010207020d06021b06010801060602060f13032f010f0c0c02030304030312020405040f05060405011401050f0d02160f 84
    0x344d10008a05000740248208410161a0b84a0800428814000541e44044165849007922007203070006403461080108402c01c81c0d0051012074118105203080d940d020303102d45030fa04243c03400c0080e900510415a50401f62a2411008410050500701e41203020a41c802da41400703603034000c40c902003022145500304e0300180c003650441d81c1c2e40d40d442c600b00d0150030b40113500400701c0c040c207000181c055801804402c0b0721940d03030003000400c5269030f1b1824000760000841d680d503410041c000290108411688959100981c1c840303450091001c0d03010345c010110040500c00500030103940a900005002c4122481c010248000803084100a010309100d80c09a04101e03c2d103400707242030b6031084120a01144d0040c0003185054510360381151555680b2005113407003503090002191361768950140315003604031420003240344e00700314040004499041c0d0111507424041d0714201c0560741c024065640072280140020b440d03556001c407000181c412a68022410801031601204100703020a582170807500a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23230194 1250 23228944 23228969
    0x1209030903160b0406030509030d020a2303160f020f0f15090609030a08040303060905010608180d08062e080103051002130b0c0f0706050408010f05010506090f0d0f060204 75
    0x85002ca00c090764500e0007410301c49801000309100060113a000980c20090785001c903888c0000210120b070407a00000c000d240028910000c9140442800203090400701d0701608075459400c0407004640c1407088001e0300800c1c040c50250a01d0064000c5c00100d4424a0300c8040c1c5280640140c2c41070348400214010070125040350010480036070700041c400d0f1241040000451802a400030282c40c50400180708404041d164940440d0401c240d000e614002d04d600c1d10f0710303403482c1032115203040c0c03080464281040d90f0b48003807444420b03207a1103000c80790084410f03940200c4039202880d0350b0600c5182050754a000389040c001e68000541e001041c503040b04c0c0a1f07001c3d140c0740c4208400c0e1409034411021701d818895102c0405000c00d061000040c074102c641c02044509400c0d580d68510b0030300d840c1c0c2c3c0c00360001c1400480e08102d05c020a01400c3c201120f0b880d030411030766040c83d00040060041416440c003942200d415144180c0300e05041ca420160418402000e8044601e01400a076001e4040c0d00110103d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23231444 1250 23230194 23230213
    0x1806010225030308090304080102190f0c0c0905060409080c0307110306040b010308030705040305160906061704081b120901030c08040f06090618030e030606030a030503010e06061209030903 83
    0x2610030724880c00940c0800384580925545080710140c4d4060107280d96800b0800c0f00180218003403004200321880c00b04004a450f9803034001524030510090803000348941c60396204001078071008400c050303d07000c00d800280c0342c8601012030020184404002c040b08000030310840b05510000140148502c121010404400908141601c03100181ca0040c001c00e1aa00103200081e52000070b9070340510b080c5400d0303043c00c2e525191140742c4824100300b082071002c1c0905c148048441e6008003005042a03040041005682419400700030300010030161035078002184143d0b0540045110b903686e00880002c40784840c00c50f41090b00c00e5400940d0060101c1e2034507440800c000d004070034061042d50032042e10300740e2001c0c0e034841070003034411100100c5a5942d920160514a986032554101c114002c2d80d4a90540c00304e501814907015000d0074a511a500a242100020740d01c4811207054550b00d00317450380e01c9c0d2030791400f042c2c8500482c400c41e4500d410b0368081003d03400b00040035000d0843c0c2102120714041c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23232694 1250 23231444 23231473
    0x5070b0a020903060c07022205060f03030301080705040b030c0a06080a0b0306070909050a091202030405010305010902040b070206070c030b19050612100c02190f03090e07120b040b18060102 83
    0xc030352900560113812010018001020070006000d860340058000c08511108281641c0030700740c1d8401c55820103030f9440a0015504080c441c40442d424113900540c40c6504011500359507100b148a8144100e845184030040c0c0e0300c2c01e11107c0b400c0000a4030f80b00d0340684401028001c1001200c0002c1000e24054a02007189000101a80101c00c90b440300d00c4541e0404205034003428006002c04003442e01d8045800028040042201058100b035029585035030a1000041c1521010703480345207100d006000600540c90813104451403d039045070640c3c0d07240d4a130b240402540c42e0a41c070203070000301400104500710320000c1d020008244040000c01c9140e48072400c03c09621001071691405a001148500e0a1485130748200e6031700d46580119411100000c041c007803084070001048a2800e1100180010150488042c1b00945040c26004c0c041c1d160907800146441c00c58800041c02c151030320711003400303622a41e0014003c00009491030702ea010000800c06c00c038a900703503821070051007510484252003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23233944 1250 23232694 23232697
    0x3120f010501021002040303050f0d02070c2607030203070501080403090e090307020f010f08010608100b0c01020a0801060f050723011a030607090302010806040c140703030615080402180c0c010c05070b0a02 90
    0x341e51585495040952b01e16103480c05400c1590000c103615070070011000819522003050000b17104002515100014944007520650086d00d074268807588608002d1005a4004c0703091015500286085100c1341c0d910305003243c00095550000d015882c20206020500001000900d01036000b595100010703a9600300454443c04010483d1002071000001805494403c107940c9401c04523600c210b55150b61101000c2d1015400f1405590107a0343c00180242003941010074035005010b542080929412881d20140c518410148002d0000b001c504d01403074440813030b0003200100d82c6410001c1085040b0401212098114206030303510a11946000620359480b1391000c400f40d980c182d440400580710b0b90180000303801c074520168144910b0750102001e41c242a07019000341402a075010400f180780100c40f4404a122041c12000c2003d28000c210258603a480c40d115011800188040f05a8906c2034840250068940c144255400d01c5c450032000307036004c0064a030160160704c0c40c0030b650306c031000c1ea50b04a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23235194 1250 23233944 23233949
    0x209010501050a0e0111031c02071103010605030d14040f0e0702010e0303101802070203060708040c0f0303081801110d020d05010905070e09101a07060b010201090507140303120f01050102100204 85
    0x140000900135130951083e010301301c004081d40b040701d062603416141c902078040440c0c008481a80c1c04140381c000d103e0102c00c1030041500c194020003d2600300000310381c58205120003c024091401c0000596240483c02c44004040341d01c0102c070000d80362030500801e1542918500019800d024907400c01000200403203002d035181485205074146040c0f00c1811a20055076499a126403d1181c2800b50b20140001c520540607a950440107141c5450004060311081d0444800402d1150081c400a43c001428a41028403143d002880702d000d402c1c1c144c007502c00e8084d004040030010034107411541c995005071500c01e803035480c2407095a80301c144a40c22124200c0341540091000031202429003000b096181d0400c1c1180ad00e10500b42e00c2d01c0e10003020280c0200c11030341d05500055035400b8090584134080511800344002c1c0003d840680b5407a49d0758400b801380304012000c07481303142410b950400c101c442407003405080130392920309000000391082091151502600a54821040b0b00e58070303108860a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23236444 1250 23235194 23235197
    0xc020904080c1b010f0c05070b030c0306010906030b01020a0b04080d0e010c0f0212090607080d1503110609130b0301060806040602070209010b0301030c06030f0f020706090213061d1308040603090209010501050a 92
    0x1c02443c2d0000c1240c031b030750381040e05980b03d010f03420001c81e00000c180011032007414088580d50b0b4a0802e400014a010741c581d101d241010324003645600141c0c0c2c0440c8101c01c03107801c101024020b8440d070400e412940710350900c1c0c40b4a03610307010403001d403244190001034503154944c46614001c4004242682c41d0f01c0d0b0840039401030344042010094901d020000380004c9400740742c00c0390400b0419a02401145c08115003070500c0210200104100706020254801580c81035a04c42d003443c8004000c90010407114241010b007075102d4104078410340b400d500003002080844112000760902d400c1c680025880524140d024000380070000c12900d05102c2101e040320340c003d21a102c414503110040b001806885a031007681619091440301c1e5500301d00140c2000e82c010900041d4a80c480d00c1004518031f44d800300c0d0700c00d06041510400c4041041081106030083c030a8080525585005107038017011128040105841000300c0e012901c80c3d0300d580121016407003a0752502e03540e40c803a0019115401034800c480b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23237694 1250 23236444 23236457
    0x10203030612011b080a0f0b090703201209060f040203060c0a17010303050c061501090e0907031403130b070b160e0306071101110f070f030c020904080c1b01 69
    0x80081c02c0203500340c0c0e0348815480c000180040768244d41182c078080080070100059048042c0040c9080754031603903000300f00740c001c104009078140c00458400d107001000310080c1640e50808c24082c420300c1d040c4000c40f0141c0018180d0311030840c1ca03110703000d6806840d40005d80c841c180005000c40a0a042c4a02541d0000e00801c0c1039610f03c50b801e0079a511400c0c6290412221650303d42d10b06640480d414040e6100e070700c40a856607900000c0c02e00e4400010400308150300c05461450032a60001524016545e100303803031007601e6841c011954a00000c60b07200600f01040c090840103603000210107044890a084054174065944000f08002c9000e00c042c0981150b20384004240744080780c0c0c03081c2525a0150030164011809800060308009003190a840894003035046039500b00381c20f20641141031450400c86051004400a800e224010044014081206002050300740f600a041101900c0c0e4000d010203040d14081c6011003c503040b007000b80c48a0320510500f00c5041c011040d5074001c644040e135642 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23238944 1250 23237694 23237701
    0x60e010c05040e091612140c0f01030c02070b0a0906020f0705011b050c0409080a030b0a030c0e07020a051902040b061603140702030a14060702161e08060f0f0903070201020303 77
    0x211441c040140c6005814850f81445170449650104443c00924407060001d80b0018541490058030701c0403c10010f564124007103d5506075140c10384101100360030721b800100819044401da180070410b4110101c00c0300e000c54200038255202c0f503d54181d0b8425800c7e5121048454002591049107018650200d4080c88000200c45481031001440700d0003a81103c0b5011010350114080304c029040680e4a000d00042000c85650180550701c1d58030425030782d40c50301c20310f1911540c0026581d0b019000d0450341d03441c08212014820407115a003240c10005903034500722800c4000c10307941030900049015a0420b180c1888501e006400c0e0b80301511011031102030f40c54a994210b070300c002d0f40c4611000005040c054580507031010005464224441c1070282032190107040700c1443d01d003004100e41c08540c001e48018950785c401c030044000315030140018820b400301c200c6400300c60507904d0700704074003e100f80c40c01c0250901c45e81c6111fa028800c22030070007450b0340303641000d00d480e0f101c0c0590180c09a40f040010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23240194 1250 23238944 23238959
    0x903070807060b0907081f05090f0406090b0f010305060601050903031905160b1503030712030c0504030605070315060201020412110604080d020304060f02010203010e0708180106060309060e010c0504 87
    0x1d2103218401ca000060040a6000290141a0036190100080d032904104000440030021403411060085000900c05140000090b40f0b104001c0c440c2c982c0f41c0303505020a0401a82d03822880c2420b6000107000558a4019002058008244020344182c4640c10100d1070795401036045135110310380036024525002482c0c481030074614681c5203010421504000d0007800c0b0310b0350900710301480c2c803030345880340c40f810b041086010f80c161141c800d80c42034200700081d038000b0311041d24261310010756080200d680d60540e0f00550309405180d00140c1102c2c140070402c1505541503008860305118114440045611200d00724200e00590240a030003420400303141c0701240e04645c3c042c1c401a0300800f50f078034003902c030000b103403d04440c0510301c2d0140e413021500348903858202d203251001d0501840214210741c50040d09500134070003e00048248988600401c501890301601450300f65480c40c002d10151380d0b00c40d0020020041c3d90300503541145080c40300c198109042c001c1e107090041660752a801c0c1401c0444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23241444 1250 23240194 23240197
    0x52d010b0109060801030605091e0c01020c04060605040e04150207080c0607111e03040f03060209090f0609060411070f0c1a03040b01060522060203041701090203070303122d060b0309030708 83
    0xb4902c151184c2a86444041668080e031528140c0783c0015084062f14000068600023500cc070162096050090600400ea40300e42600d0844070340341091891502c4500302110320051801003244034900005403482130201c41d20080c000301058100b00c810350b545441d81240e5035031200e9a924165000141940900001d010300076101da00300c0c40c10341e8901540c1c0c0c10040c6050500f64800c40d0714035004100e00600d4502075401c07503880b8400c04000e41091410b80b0000745e44420050515100c1e680d90b84031800304c1e50404003900d01141c0d01c01d264a2800407541450080c07010f040c801d884440d00706104400c0111410300550303004075400302e2030854990901c6800c1c0d80c1c94211910004110740b010f082070800c0d000e0869403800a001a401440d43e840c01c4c442d0200c800484000c040880c0d13810420300c0c90050720005a180e040744d4142c601403106504a841200107441c42c281c041c241d0042100325040c480a03032108411034450800820050140d4418411800340000c441568158105001900100d140e5a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23242694 1250 23241444 23241451
    0x103050a060b0408070f150c0f06060302060d060f0b0a08040b06010219060203010503071401050703080601140d0501050f010e0a030b07030f1407020705030c0d02010c052d010b0109060801030605 85
    0x30214000361030700980d0100390080e90003203541d0b511041040203007110048043c005840303861a40710540a0004014203840c010400c01001000c02c101c4080900c182948820040c1d5802000b003a51070b20f0704022640540b40030b02a048003d000c622001802d01d44480454043d14210344615503a41e83d10340f502c0325020700042c49641580607003c1d05002c101c150b01c002d001d1045c8130300fa00684035418081032600d0078505801000078940c1d25182e88030700342e0f048400e0b07410341689031030a91030960790040100d6100080c0c2400c544c080700e02050003441070002d9081281a11000e40d952081040c40030011144d0954065a140d000029160140089070b02e4000040d408140d40c2000b25501524010345c1c3c0440f16172111003408940581d050040da551305002900050408400410403849800001070b0b40a0b202c01c0c000781400b8646080204025042c091859080420340743d2501d004030245441d001c0301c0a4460f100015403a01014900e250f0042d4180c8050b01e00c5552070000c540c0c255503c22008042c043d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23243944 1250 23242694 23242711
    0x206100b1305280b120a0c031d0a03030b0409021c170412050d030c050901110a02030313030b0a05131104020702150d110405090402040c050403080703030209090105030c090402010305 80
    0x40802c1d41c1e00c03004010380300140c10107103040740c254040c019882c203e8031a070010761030500e040000300f01909468840a03000010460000780e00e226000c0258010858148002c0501035030b01d0101e945030a01081001c140c0740251810f00c074159109080104464a86000030b600401c0c1c411201d503803410403106071441d140f00f0120140d00e8071100e0880c1d0100d4005500600307140c0c0450501c42d0810170240009045c0f032030701e0b05080c00212003a18020b803460255144042c100030345101151451801007100e1152250050240c0341c1d038010800e0300030410016030006941c29606132000c40c070344441c9442250720030803840070743c03400c62401e03980c03a11016000d41c980c02d54015000e0043c41c0240c2d84507000365000301034000c4000d07a07696010a2020030b54051505002e8600401d000401040d02c40501041e44980d04a034006185045124140c1300c41c041c070340020b4151040032070301701d0070560950300800030f00e8811a02c0d202181c0e42c41e410141c2da01090380c00150440720300c0c0d01040055020b500269000b03080c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23245194 1250 23243944 23243977
    0x1030c03030e0d0c0e06010e0907080a150f030c090b0a06020a020402070f0803130201030c030c1d1809010c02071505070f050c030a030302070c050111060f0a0b04050a020c0601060206100b 82
    0x100c0d1161041001140c00c500089807034041403046c55038200810f40c01010040d00c400c0410701d00408003405c86c0c00010034071150300d500c034211001c1c90724240540c03102411203a100076291a40303905000705e251046001e42c01055141804d603000720700e4002c03400c6040300c0345513008101c4a08070713909000180d08050000c96120000c54917000c00112514061072003010109400304920116000040c26540d90341d07828028185010300350a0b1507584452103404804d04200d0a400348602d040100346490b04007600411140c0f070346000d000150320190015100049254201c2d820107440d00b07401201c1403101c3e425000400d03820060300000480905032a000b4600540c20b031162101c0c0d00d40071a04110f1100006c81c006a400220070040000a4905102074102840c0c00900d03405c4140301d0540ea00740240100a03030071042000200c0600c030540100d1001c5401500601c441d090284424029401c00e00b41200f090082c030001048840c400070302d603403264080c40c10700c4035140e01d018207054055004000008600d042c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23246444 1250 23245194 23245219
    0x190303180204020706050406061e0e06060706020c15010f0b1c1e060302090906060a03230a0b042a05040f0e010203130c060f0e0402030702190311100501030c03030e 72
    0x40700c0c03024000445c00780d00301061600d4103103864812654140c001540c0f071542c03503181c1900e900340c0905c01411f941c1d8000c40c4a80e00c0d114807001440301e02940000400107400014008080300d000726504400c0680074000ba0031a90301c1d182e0094404486000c1d40c1014002844200754100103c40361030310680076010001640d45a2000b0060100e440e580d10390b0009440380810403c43c1013292403e0b6004904001a0a041c1481800207040781e40c07600c0090300c51800194016040111600701d008040100d404454180000e80f43c03107001c02500f100c0507107840c6c540081d0107410340102c0bc060b20903101ea0700c200c0710096090004002c0107001c9003070351541d05952680c07050300c0a4400d00c0294000c12581d880d90760001c5c0146000d40d01ca04803074220300104803058440d0304110360410b803d01d031061001c0301d02503241d41d2640030032444c140e40c05280c0f015295544c0341e108103054005c90002007840b5154203440c2c4603010217001c02c00b4ad42c4203100040c98045800401c0000c00e11550b070b10710b840d410040040c1000712 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23247694 1250 23246444 23246449
    0xc0627010603030201050912040b0f1c020406020d0f020f0a0209130804080307020a060f02030904091401050f04060507020a030c06050c0408161404060b03150103060503030a0801080601081903031802 87
    0xd546400443c0940c2d034400520060940030400d454105500061891601d42415500380d00c6008003014260042004610382d010248d8045040c540c80c021a80700315240d55484400a698001035200c4da000300380705140d8170340c50910100742c500c00901090024401400320303500780041070360014859541410004203400004000c980140001e121010044d602c800032390041140c150000d5122100b4007902e50780d01d80000380c0200c10364813002803c96001800c0e81c1a401c10410000c0141c00e00315040d4a040e040182c1541640042d9000740d01540c0204801da6070004160307510003c3e010041c0100300c00483c685d000909035008664000118880941082e9642c080146418a480244200c0d00c0c1000d900340421421001013040606080b5420b000d42d0b8a440341342c40c09440007178500d294180c5404820742d9240d00a030061802010003a048a070303100310560f40104049000e000d0383c3d03d80e000fa0303000020700341c200007002421210ac1000301d40300e1003000c0d0b900754018046030074007400802e9200e2100025a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23248944 1250 23247694 23247701
    0x5030402092a121009060f060804020301060906150908070b120606040306090507180c050904020d0b06040b0408060603010902030d120603080703080403021504050705010c020a0f090e0607050c062701 87
    0x5007003c481466080c88035003980c1c040c0a68110001891404000304a5002d580107500700300c80f42403e200900762154004a03000d0100d036000103600c3d42c204000007a40e030301c1400c0c5842000d000c40d0b40d2051165240d0618a071900c40510400408800500c107600d080c002e86201d1541101000b00b00a14056403a9a030f0000c1e00d100310f900b9074058004840070231446540200f40c0d0b04030540351004004104804001034224054410214011507001c0740107904a100d40d40900d102050083c2501d450340d550307107149444c603402801812603502500d40801d0603402c0c1401001c03d219070050184c04005100802201c50954071074800200036210380e4000f0100e10240300510041d0f020342da03840e1013032800d401c0280c60210f6000440d16824070344810000030480129142e020f64401340303441301103a109030001641800941d0007031140c4040c0340e0000151124141d204080e50803000c01503032125501d4910942d0700380114603421a081d004040081c0d010701040c0010000e1100040c03001f10912295004030f800c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23250194 1250 23248944 23248957
    0x2120d1b0201090b0f01060215070512090d0f1d040b06070b010618050906010c030302030c0f16020406060807050301050d0c0806181c12020307090b0c030406090605030402092a 77
    0x15075540c3c1e80203c02e2000300903505070300007103180002c4401c2d450035130700946e124040040001c080100c440403d480910550840300c2d454003500d85411203003080b880c0191100005944070b07000c11510b4034030b66240d0b8081d02c2c00c40203181c9400f4400000d0741c01c03c02804007900010b095541d200c3c1042043c100051580344515000c4c010741e40e5903503020300c020300300a440c007219030704210302c262004400c100e0746030ba100040d848580e42c1441c0c0076840e07448a051400550113005e1045480c16804076110883e4501045d81e012420b0003142c00380400d5566900035910104280c4d11100040c00400040c441420a402d100c0b0360640700d00d10852406641d01c80c1c0e1400d0800545004200c07a9044050101184040081403403200d1400d03400d04440480c0040600110500c1c0c0c841c2c1411070b00440000c3c41540166013103c01418506001903941a44401c0162268420f004180c0410a07910000c21402d11460641e84100c0d8054000f0071035072101c90462032124a82041c0d00b101283c80c105045e54850400040e080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23251444 1250 23250194 23250197
    0xc0405031212060405010803070609110d08130902091f020a06060e0a0506030304050d0b040c030210050309010f050103020f040203041b0803070623070804110901030c050909070602120d1b 82
    0x1c441c04600350290450102400084c03081d070078880144280f40010046a83c60780d0f21131000101b140030b6182c2030901da8182d1800350350145040e042c07031041c8804500140b942d03400700c181400d54140c451400804900601d9807032500045c0181d0440381541d04000c902e5512030480c0100e600881181c1e5800e801d42d410341d0403894406090005000403000c203401071642241c011006541810305200204c0c11181c05210003514849540c4003090a00625880c4400556000350110001c20561070000e089c0d85c0c0141e410b03840940c6020340310703403410040c1c0c41058140c0394001c0c0f00030310583c030141c2084007035003025005031488080c10300420b208a00c020356490080c00044051a129201ca040100c01c449458440f054086c50344032405803d0140350044550005c801c1c1032480079511275082c100040305c506a915a0820620800801032214814036001120801c6410340e0710355a580300c0d000c0d00da45052103030a01580c006004105890f600e48040e00d11000c60040018120401803004880765124815010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23252694 1250 23251444 23251447
    0x20301060e030d0215070302090d0b0702030901020708011806020d02090a140406050103020f030103080715050a061511070e0901091707030f0518040c110604051c090f05090c04050312 80
    0x1e000341024003461089003ea40080c2c41110742d2000300d4030580000809800406900044990031691803420402465400c10308420207482d00a5001c0d540398007811000d400340c17044240011350030005000c4c0038a0f98a030b08805560b000a2540c412002e908035158202141d80c003404010419250404031000805015a503080b1256168060000f20340c03803900014101401085107802c0300418504503811a60302903402584c81c0c845040900012200c5007104611504110a1040700f244940052054407076020003034071308212414040d10840c840c0b822605441d00201d10400c9500c289403540380e40a01403100102d054892603580f10341400e074094108015040118041045c1035002c4e546d007608910700c1c103010340340089103001c098441c3c0030382010030306c121b84030080800305610941d001456000040100d03110390409203002031311200004446860785411280c5007005911a2054208941041d030f01c030040b030342c141018000b10300c9000741550442d6404020010b0342e0788007081124910b54505501c1c9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23253944 1250 23252694 23252717
    0x7030503061216051e030712020301020f0d0f05011d07030510170609071403100b130509010f1103060d030813050601030308070f03090201050405090402010c080f1809040f0305070303020d02030106 86
    0x140d04017a9041245c0012509516501907480000340780003510005091504051110300c006406840380c880f00d42615180810040c480400130303001a10050802c4000703103c07036a03c420741d400d049440c05c00c1c68101c0f404510007140c00180a64089078000c042c1c0148843e11503100c040100b00707075007002425001c0360f00420400c800401c080c044407024165041071192005000c000203640c405000e1808208141e890540140d156181c00381c2c2c1c604441510014001403038442d00b0740c4e0080c0100b0159558142c24005c510704448800011288620002042401200225101250041002040d4044440044100380080303982000131034001c51007542c2e040800d10300144020468044010b418007414140407114006130381110548054580681d0f0200956aa50004881c140042400504201d10000755400002d40a200402204c14000180da08502c41881030044801084030040c09c0f1091382840100082e10920041c468540a881c015041100e8070000608a9000703030301180106031301c000c00c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23255194 1250 23253944 23253949
    0x180108090105040f021021020403021008010605030a0f06030813051203030103020a03030e0d0213020a0f0c080f0a051201120c0b030403080106050310090608060411090106050703050306121605 84
    0x165848100d2500a011504140e5a52641440e600320001e1240070072050f58440184160302c581120f00a442e4007444007481d14440d40002d5010b808207034010300e5190b02e9001c0450160086074103d440c65a100c525507901c03100080001c1000d00c900f1054242c50780d1000020801181c06400c11860031203009603a00d20b004100241c610b144600070081f60414801000540da4500405003100d070103040029100c1404e0002031340e610355102000703600c08500192020703000e03e5903029203800e403444d032138010b40408114410b0311000d046000041c004202040000703c200d000901038481e181300c40c1412418082ca00e8440285031400340c004500310651891b011051004004410009141c00c0c02c0e840d2031420161001001c62005014190a000c2c00001282c1c50500007a058001070114104c200300301030301e425400b134890000392401c1d05d200030860301071a62841c080e0b840303034125881500c0d110710b4100155015542908010724050780f042c6820344410103070909101804800a0a40d01e010440d0f040004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23256444 1250 23255194 23255207
    0x60126150609060a181a12010f0c0c0507140105090d050a0203060c0901050915090307090501050301050601020f070608040201170f06040c08070c0809030a0615080d170403030b0301111801 82
    0xf014412000c150080000c40400e45029045a4400c500441c07000194128038800311640140a600b003503545080c499001301c10751201000c00c1c1a40707401c3c0000100c4180440300c0c200100005800380d0400c0710100031004082e000300384880c006041c005d091035503000c000750701c0c490f0080080e076894009015807000c44c50140000e032b030301c00c03071090003903003014a80305c0000d029028410780306000c1c1d13440c0710550b03031000501810740300304500c003d040741c0380251180711090240c402841081e006c0e41c24100030407100c0d8008140c190107086950010030000d85424400c90780d820001d401a410301c010516583d000c5a83c401e05075214200f0044248a9800d010061204032801d001c0700d00d04004814062218103507020703200e5070710709400005407910340061000090502c490198020710140c5000c03840c950b086240c4440e4801ca40540302594102c100d00f681c05c1d11151401001000d0003d06140003a0000c1c0c001d60000011000180c0009030b1043c07200d45900d1254002c0d0310b080ca100410046022596a2081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23257694 1250 23256444 23256451
    0x20f0c01020a0b1303020a0b09070306060803090603160e130603031206050303160203030f03090a05210306040c11070906230a030b04050a0f15050106030b03060126150609 75
    0x4001c1003030041607120080e82000141c404484402c9036151601414820007480200e55040611074015040040d49e5941d501581d1204070741c001e0402c0c00000350104080107917440d000c00a00b4041c45d40c2e403800010040441941206002e1100000d01100d0356112103991016403a00b1140000c2c0382825400d014000e4007007140070242581c00d001052181d40c8010096403001c04000820b1119001c00e48000781c03c5009600d00360403921000302c108010303a403000a404121900510958100140d40d9240b241c60713610044c0b40c0015500c0800c0410501e04055228000400c00707850105c0b42079810154441c28201503911002c2c000740c8891040c0001c07500e900d101e480c1700700b1000c54000da0f1500a0003023200368155200c00347c8404045000075052020611156204590103228085141847d184c46d80200c1c5002c43c410f21500d140c8400414001c0c06486541400007000780200301a83c03030b10004d071f4200901214000e414008903414039003204010400110b020072038200c803890380d1030074806001c0d1601009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23258944 1250 23257694 23257697
    0x3060f080a0203070b0a0201020f0304060b0922020108041502030709051003060305060a05131212050a0204061d0a0b040806090c010203130306050a09080c0609010b100e190e010303020f0c01 83
    0x719607410050750001059400c55800c41d2541da1070b814208801e074024003880b2044881071400008200c02c100b0f0b07540c080c000c07400080f140c00403a42c071b031301d400500d2a5003140d003443d00505031018030700c02540c02504117a1784184030b074020340ca0710507600416070140d030019034400c0040740d80c2c0001800140341041041140c0302076483c0401c416403035915202c1c3d80b22800340008400658880c08502c151407803403898001c00d07810117040001c0c501c00210090241d0f000b0801e030242c092514010640c0080c10703008840844115940d28a01c400090824211a07041030b8000c039808102058001220400d000180c0010300e8104041c1c200b0346400801141402ca074142214115002001100329a800003d882001c1c1d0307400080009481d50f80300302e0070f0010000d050018219a0010070b80003203000b40010b01d1440b07295400300030301c07405150406110100310a2007003080400ca800405610350b040a1803104120b041080b03001b41703c6559901903003540c413400e800690060300190203c8030120010080d80c00301c0d204c20f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23260194 1250 23258944 23258953
    0x11b0f08090d141804090308040303060e060d02040509011e060806010503160608040f0512030717070801090b01030912020304050a0605130303050c030712050d0b01090806040308131203060f08 84
    0x4528000c20420b08800e0405403c20042400c09100d0060004035140000c0036004000907143c506001c0c140200880f011000681800310200d00d1801c0b8050b0140500c8015110174801c95080c2c0c00c02014000c003c103000202c1d942c40c0b448201c01d05c1d203c0320320458400c00390800607074103081030308041c200340d0140c0005009510150991841030540318010040b00d801d4a000e0816448501d05464001e1440d50050810b01c5002010304508200d1402076009200c1e03070700c40000300c076a00c0c01180001c40f42201e0030b00200e5145001082070b6502c6402c0011560740500d000250300790030346c1d40d0070408202218503000507840860213010908000e02c0c0c42c130242004d0300303025003010a04035801c81e407001c55000050800c02c0104a41d5040b4604000f652107081e44008041440490070704004d1090700700d44140800c90381021948211540520f00801c1503c00c610086d200a5840e910141c0744428050181e415994a05091070041200c00c4495008500140c0d40812031038682804604000740a40190803150807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23261444 1250 23260194 23260213
    0xc09051b090603011502070902030f0601030b0d020d03030b04060b0309030d050603030301080a1104020c1e0c04090b06090402060708160203010507030513030f0203040902040620060712020c011b0f0809 88
    0x20b818050b40d044600e000c040b8103603101904012401c2c04c105a1000b80d003140048103204000c0c40c442c046c0740c440e060a980070011040e5110410000203a03001000e0b4000c900f1810340004244260804040b109014001086255a60740e044046600031500c034510f580000c10091002104c0e4020242c008070128025400d650600701e4080d1120218040240a0003c0b0f8603074050946841d015180030401d20f00c1603660911132406400c1d17410400c0c108001550050314034924003071909101d29001d064100300d695849980d4501032059000000c1d01c1039a0204c0c09200300e000081c2308000404450103086420400e02e001c0e0700c18076080d142c02510b000e0034942808208910a0380c080b241210550305440c086600002408059066104582200701c80d58000180402e9458200c2880c2000076201641004121148804552505070a441400004040c409607039010f0099401130301035540d8010000a14003075012050001e1380c0c0046010700809c0041640c048015000b0542a074001803003800b511401c032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23262694 1250 23261444 23261449
    0x5041404020a0b0c0c1305060108090d17060d06050403090e010f0b090f040e010501140a090506010c080c030408010203040b0604050a0605100c110901060c21020a0602070f0c09051b09 80
    0x502d140034090009a010501d940d4000c800c04c544c4800c004060a1110900304030154400600801c0300e00b580824007a80c00f1804840c03000541184090107a580c5580584c05941404001d400180c6083d51041001c8540c20118100d8402c107030140d0312a840d04082d0a00d8200640c1281405071700c0700400c085a05030411049007400110741221204455049601000d0070014004142c0310451169540c0f802c00081003035880c007008400032003802c80303110b51101e903103503030110035600c00310b5200380000c1100141a0010b5000300c040d0209014090580303050039210385040d401c80e04202e4090303401441c0d0308280103090a0501c2540c2d00070166500601000381050040341c61400301e800f04d442006a071103a02c600b4000208420724059400501c070b11440d5030b41e40b60042a4880c07803e0141c51044010400485860070002c0c10f9501c1c84190700a008403203159191100250001801541c00e1216003000c200051900080100642484100000c01c0d09080a00451804840604210940c1c0810ac2f101499 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23263944 1250 23262694 23262709
    0x1501050301030f0204180506061201021e030405150c070c0501030504020a0b0310050406120b0105090702070302061c051003050c030111120601030209030a08190f1e020705030f0303010504140402 85
    0x490300000b0754181c14161380b02180040648015050504010005440420101080c5c050050344200c1d480c1e02ca814481c800603080741b2414500320f248802e465105007101240350041c56125000f0b50588bca500c81140e14000d042070112804551504000354440c2007000410f2440080c01081c40c08000c5860541d000c14000121401080e010040100001d645540035126601c05440c0203001402031030381e0303200c9210240b4400031084548680006c00480c1c3d5090103501180b15240725401401d5188c511740900c6216808540c07614000351014120340c20f00c15481c001d0a02400e030310406100724a10714184039003040b1019240c13510a07410583d0702e141000d07001042c0d8590242a43d20184a5180c402c0180c1c028800d416030140c00d4001c5c0303134a590910410070094814044090b4001b4600014940100c551403a6100d1900100700d055061024002510000c429200401c4c0102c0e80a107841d00700091410304807050301c80040c3d00c004014009418039005000050f44d5804030090242442d0b40060b1a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23265194 1250 23263944 23263949
    0x210301030b0f18010207050601030c05030102090105031306150b09040f0606020d11010209092415070f14060a0c091203050915040b03040b04030206090a1203090c05060408010e061501050301 83
    0x440300024007264207044440780003007050b43c800d00215594081c515065465120074882941c0926002d2000901030606000721000070740f0503507c20740b035681c64866400d4075102c2a2000e40e480756130b84900c100d9002c492030701a00036190348080c0c1070301c90240004120a480d0782d213401c4040541003482c108106900055884122200b43c00d100340c1d5005076039030f410b00a009220207140e020851100740305211040c040c0c0d1a00d2003015041220301d41556a090180740031410100a095071000c02003400810b07040000004041d20840d9080c900c9890514072600d02041070340c19100140d519074800307402c6900508108014041074001e004a18510b0300c1c00740240c0107003142c0501807000001c0c100400110003040f039018161a5500940364149400c0003541074034202d5040340944074079004a101c504000903103400099002c090b0203900140d2102c200d019010000c022250503c041c0303030209440d56200044c10240c504030340001014210100e8081c91b0a801034000ca03e20746c0c803684521001d903841400c6906 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23266444 1250 23265194 23265211
    0xf091e02010210060b0301151407020d110a0608090706020f0a0b100905131a040c05040c0201020705010e03030f010501050c06010b0a050c0a060b010f1103160203010b030a0302210301030b 82
    0x586215900050b414004010800c0e00c0c0a45042e00c0490301020280285041e07e4040306407000891503164260340d8082d0b03200d00350740c6800003405090011b1611064050b00680304030200c4e040e1901181c00300b40e05030001d421610106050fa0108003584200f040f91f40d0042810b4801031912015a0265988800343e11001410003d590310005004000e103071920780042c090000304210500d0174001d188048000a0021034803581c054210700080343c1a50540e0707000d240c1207640d140303d01d490441040010404031280c50150f540074046980032a030203200f40c1202810301c0c00615668030300340d09060b288001c1600600c0c1440000e0200b40c0440000203881819900c0c42005280c1d100542e000c1070f60140100040c10b01c0034400c42d84244104a1541c0006500640a8035070300c0006070740304002d40c0c99214008401c0d00c0b5a0042c810551001c001082c0020b4490024000240810396030000c6800c251070340c2020350151340007800d0001c401503c40000c3c40380480c8800b0440c1194150313030340c8911000300940000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23267694 1250 23266444 23266493
    0x40b0405040e0a170c150105060a0e121b030d02010c020607050c010b06030106030903020618030711041d150601020606010e0108041a011514070c06050a110106090b040f09 75
    0x90b02c54420402001035a42100c04502078600c01ca4104409030f00031000c0d400d4034083c525411601c02c101408040c1a00e50042c40d4504128220404456500030312803050303440840c851340d03052040e10034001c6d044909220245500d0801d00501407605c1d0103000031681045a2500710648200707903010131444d400c40c40c9843c1050340e422103a001a4050101c02e02c400f60300c000300000001b901030709544020803c601c40c0d000c1e141155030b42d000900015000403a0310071581c008014100c001000da811007038000c0c2c8000c5c800105d00da481010001482c0c0320040d40310481c0d1040080c4801c00486c0d1051a5004c50248000c200c10b16001000030000465000319505002c4510b012804009002416012150b01040000c20700c3d0b03524403804041c40a0300329404007103032088454452140406013121078141d0020201e66a41d440c0280441e0694400070040f4104640707018150344204081c00b80c18010710b180c03000030910040c000104000c0340d007480c0e44046480d140036404400120403c3d0709208003c050071404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23268944 1250 23267694 23267711
    0x70911030402010917070801020a030c080f010302010813060e0303130c0e0613090f050f0d0e030606060a0e03070801060801020d0501050d0b0402060904020f040906060206090706020601091d0a050c0114040b040504 93
    0xfa8a00030340398100c0807c550020500f603603266450743c040e0708590040d079500e800b5601c031017822010008081c00f0180c00038181c80001106aa400d8110852440c072034140002d1603081a06514110341080c1c445018000400b00d0400500501e80042e0b009030880195808c0141400400503118080d9807090166942d200c50400040c8100c03322003417001a0480150380034541610395031a00d03a001000040040380440203110003a08001800314030880000c1d0401e40380071036001068809541520b002c940c5407080343c1c408201c0b1f90027805040c0c020540c1b84000344c1c8401c050407403e01a558160440c50041c0000300130f84c8086428141c0c010740143d0140c50660761940020f0104019100d9049030403001b1000050006901c1c0159101508481c019800c0d2266500c82101c55511003c05208000040e4400f4006108456696110107030780300c8500400e101641d21440d6590400a00003001d4995401901041c0c0310b03960401c00c200c881010442d00d103458681002c000010074060b50003080e0003a070355035200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23270194 1250 23268944 23268989
    0xe1902040801091505010603111209070302100807030b010e01020a0b10050a030c0905090a020112230a020306030f28020a0305120d0b090601090b0702010201110c0709110304020109 79
    0x11100507103611402400300c8401c90400b8008120078280e101101441d00c0b0001030240d00c00d10610500c0d8241d50030007442d02c101901c2c1c00c030b44035501401000c114000ca49000005a982c4400c0107600d4107107450f10ba41d2440c09590103411955078100380350500c90070500c56252130b80d0200f40d00c05000c1d031182900780c55880340d6015007981483c5800107500301c5011480841888007001e500d50440700c0d219014800d554a2240d80c640381c8040200c0203010401503083d1010400c13468100c7e01080c0d8102350200c036014041c0103144181e035000e039054418103070f000091000c075040a00c940b0784142e2840006044812154044450085607964440046004811117100310356613014510001c50700002210084c9106024940d910350002440e01e400e1440c000e0b041100d0300b88058480c2c804ca0058541c0d44450b4035041c075200086d40582c400b00e0455503562081c5140304007500c06040e50380510801000b0260900c203c10040344da050b12040c050300418420440141c1c4c0c4000c20034143c50030034a51440d002c1d4492030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23271444 1250 23270194 23270197
    0x4060608010c0507020f06040e0606030408090613060e03070e0109110708211b040b0c0102090907090f0609140402070206040b030a0b040b120c060901020c04090f0c0b040e1902 77
    0x10520081d400c02001c0103409901c10050041c0364005c483c0c0003140c684a40c20840d20344100d21a00f000c1c0b14124002a0f0186402c00c043e55000e80202c0300940780c000007100158182e8009041400000780916003405810f6115121241c1035105500522019007494451050b004052007a11780664907200b101500d40b05080030383d401c041c0e100d208151196511b50350060340c2c16601040301002002d6000143d000c5440d04840b181840d0350540061601d07042403e821750560002e1407118107503400704412443c589078400142d2140380c10b550740010082c04c00502502400c0b440e488801040100c0a061084203212048c070308604400b110016520003083c030108400d80156480014100340100400100010076082a0302c14001120200944c44404003082404511088a00c80da940300010001c55401d001c00200f0b00400140101c644414080c0d001500303407034401c401114844426802442004849550b001c013401218079039031704103410f201c850158400000c0241501541d0381c485540807041950 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23272694 1250 23271444 23271449
    0x30f06040b1203030408040602060903031003031b081801030609020c0304050d1e05010c0201060b07030f12020c010903050909070206011a0708040e01090207021002011104050103020d1515080108010501050109060305040606 97
    0x20b0b44d0300c80c5000c1c10101215000351044202501843d40040d94401c0c000c003c0328403034201000400c041d00d0450700c0c05c031507800d040e0a0300f1175444400362a9a010030041e1014211408580802d40c402995500006080d0761403031b40203e40b0240144400e006552012050b1026281c065507900980741217401c0c8441448014480d2100e04a1b40d0340c9007006102041d002480060384913002800016a102c0303a1000d10b00c580300340035001510319225001009e200f050ac0342c036580030101003d818541c800854a084038583c65088001c40c40008a01d8194208111500c2c0e009003140044c00c038941c5403929070340110b030704400e403000e12110000702c460402040c0c4003070f01d000d004080c000c00044d684484c0c003407000b54440807050340725a4400761599151841402200381c0792250281b07a50a2038a00001900607400086c4010002c5407100800345070b000160500e80010204408045034202003114080d0440806070455200780e410100144090b903080907100013124810f140020340341d6100c1c2400002000e094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23273944 1250 23272694 23272729
    0xe24040b100807081003080304060203061f020a030201061211120a05150117010501150315210b0c16021203070c030809100206060a0302040209060706020f04090501060302030f06040b 80
    0x200100352010b40d00001c2d4a10840e42501c074682c140d01c5101109005400b14800100b050500300001400542150051500140c002e007440400c12405101c0751604d034181d940c03001c0142e101034042414141e09020785401011148028581504036403034881110a80440b01c50080c20716003407442124500304501c2e100190860180c07054031080341c00c61803e5103000c0c404c5a0204460310100d00c1e0003001031240c0c5040750350590008005100c5554250046d2050b2040301004810b841000240d521400481210302e142008158002c04c6407450980c200f40409807840e4410001401405420b1460000c080c4d101601100c000b1941c452500d51f052441c03158040040c80d450f0780c1031000040210032400750205107802c940003442801d45c0c2104a944503403c80e0f070b1036403140e410345003040503040c0b035030003400300034030180c0080d181071999112081680d010900e0865941c50004041024810b80d02c40d0502416151405618506114400e440c480310301a140c680709940e90180302d0601d981da0290804a203804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23275194 1250 23273944 23273959
    0x30602030a020d0b04021606050603030d110a08180703080d0207080a020d080604020915030603070e0106090f050f01080708062202250c03150209060c030903070e24040b 74
    0x1814401c0280d004001900d8805081c04100c16043c034041c002d41d00d400b4411a0103409182c00364840c00b000d0705000d00901d0301804100621030480e02ea5000d8080c0100045070780d1a602c107145000204038100042005401c0703166140030310714940b00400d00f80c080b681c010000e6501c2e00350050216000b07200d1884014102c41340000c0d40951b0b160040b42455a11509031501380c55680c6110600041e4868125074039440f02510141c4511804090050740c0c00c04030141c01c031001640ca809020707800060a030024408500c0000042014410101400e0042c1000b0740d04c2100d104440d40019042c04805443d60040c0318101d00007a030306890b410480c1c008881210400540c01c07840904480084d0f1040d03130346c8045091444c3c10458005441e0014403c150750095104030b21514584503112100200707141005065000c0141c0070095032800b002e4242c0c0380609014680d241501c4040504d04681c0c4d6100c3c0200c040781c0420031242d2030b034401e000100d43e0000c4031204240304042e4005802003c0b9002e43c0b42d17004a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23276444 1250 23275194 23275201
    0x8030408090a09090308040b0615040b07060e1509070605070809010e0111011a040e0f03030c0307032004150e01021c0504030f0803040b090102030402150a020f07030605070e0f06070201051303060203 87
    0x10b06c400e5981c02180a80c0c0ca510242e1130b40014040b84100452260804140803c400c20440001e0f500816465010341000207222888e00314980c100035044030310a600c0c00300300060102c0a801807000e60b0007855a41441c40c50090f40e6900c0c00d4a501510f954181449425501903140d640144c01807460340c61414020008043c40c800c0500c292224841081c2c000d900e4441c006191001c00214914a102d9201c021030031980c3d1b8034005080e9038401402101003584402d50404e43c03040f0100d026010024003407080340c0f0f40b0304041d94600c3c001c501d00000007c00074103415101407642c000c1034920b11808050003030340c2d41e0b491290040d10588200d038802404001d20302000380500580c04c0140d80510700c10921019a51903007800d5900380d010684010750311107402286024810044801008211564015a40014203070600320342084899802514401d4031901004031140d07100c424030f0b50f80c900444401c012051304a0120f86a4021138600906111700040c04502a9144410410055a002506658a19 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23277694 1250 23276444 23276447
    0xc06010f0602070b07020d02040c11070b07060b04020a08010302060a11030d06030309171221070e040506031609020d02090d1407050a050108060405061210050f100308030408090a090903 81
    0x241507100e150014003d041d03004c903403030a001c41102c4a0640052921515401075001c01000345044501c410500000f4418180d21000c207110100040a1100009496031401c3c20800284c1d80c850307078610b03c03480c4104500c10070150030400042c103407a010745800343c036100309510540d13040190b8482b10725140b2012400500c0c00d150741d0804010b0368030039920300c2c2c900c070342c1c40c040c813140d008034141640280d811420010340c03030b000c0e4000a030000550b120440300c4240d14030b104896004001f5200c4070005040c40ca0385041c581080d014603500110309400400e46840c3e1900280c41401c018081e5020290300020a80301410389901654080e0310000d0059800440a1421140d513450045d1b40274854000c00800280314540002d0340030441f14181c465040c00e607108400c1000903e8020703e956440720080c8025208803c08210400700c229100a000440382800d20048411000c020305405411418003018000a4030200589400950084420382c8603003107a400141000a15007040044a150049800915 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23278944 1250 23277694 23277719
    0x90a091103030c06041203050702070b07030302090604080d08010b09061209010605040e0607030c0201050f0c070f171e04080a12030b0910090c020a0521040902040e01030b09060402010c0201080702030c0601 90
    0x254410700d011b4031140400c0380e068054a07011201d000140e00003803810083e0582e86e0005088292007450010f00e000da180e000154076030095009406545c2c48603442d0107105030000003080c0501641420b45040c0900740300003a01c0b44c4514801d800c107903400302d00440c4440809401c003001034100203005008503900c0c100901d50300c040480700702c000681041c00c1500014018440c3d01e0281c040f8614401d070030ba4030801c55803420707032100314203e96011001d03410385c0100747e12400c80c42c2e03180d8281e10b16555a041d85c160704d8000c151022049808a5000c200c100185078001407407002180c1d00416405502440c60703000d5004094070300340c5603082210074040140802003030310100c2c240d400d032190400ca4000b590404076900c5025060091403a03100055941a121400c2e000e014103e03002c2940070b1400b0340300c8508030142d8003e54000400d00074440d00500412460000496100d11001d000380030526081c0c000801c001401d0383c01905201000012944843c0b0900440d500740d403181e01110b0381940e68070f0304003945 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23280194 1250 23278944 23278951
    0x15030209030d0804020904020d02010c060608100f0203010b0a0309020a0b0d0212070309020108010e0a0b040608030901020d0206070e040506010c06090308040212070b0301090f0902030a0c030b15090a091103030c06 93
    0x10340140c2c0200005980204a40390245402610160640d0340d160309019001c40981c00c03d07410b001000b1018400507901d8080c04d00501034030809821104141e03030000c2d064070400500d1010207801400140f010281400035104030380b41c10301e4040f034006070031700100d42681e210790015595a08000303014041a0101c0e0010000864074002d21202543c03042e004804a50b00382c0300090000e403030040104030310a2910903980d0800400500020b00708401e00001e0101d0b0f80f20b9201103401c1e040030030713109002c5da010712001e07520054500151145280a502c003c0c001c0a24010551003103a5034404203d181e440f418081c0f40c11544a0020000b1a0352414007918900045a08030310844505000c15a80e403004501c807004c440a5120700c074156400c14a403d000341140ca00b80043c1d6aa4804014015940822041110701d0148165402090850822403d1100d00504103c882c081032142c003d02900e03a101e1069024a00c00000907051085241c20f0007181e0710601100c0e0300d8031000c5000c005205020410502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 23281444 1250 23280194 23280199
    0x1030b0403091a0a0c0309091e051602070303050705030d090809030c15090d11030a0813080304030309060c0f060f0209040e010504020306011a090a0b18041407050d020415030209 78
    0x103655a0701c024014690748201c0f02c020840040c0310301d18403580035030700d80d080e135910034101400c00303035292100d043c11503941000401200300302c0007103071000588602c13805411070325549148240c8150000041c0d910f091511006081000c0043c0030014031030140309940074140d1740b210a000d14229401c1c00307461604068141880b0b4090001441d10b03920b01004a200d00305980c400d4035042884c560100716a250b014003055078a904000c56940c0d60f50340901c0200096845084a961180c0c030720b41403015174000d00d8002002c0e6510800052000c42e8001c6104c00407680d15142000e03418a045c0ba0806803410030850084c00c013810300e00f240100d0141c94000d03000006050300c041111090100d02c050907940d05886c003030b405402080042c4612081f16921003924011072009a18210b200ba001c2208000d050340194105c020104164440c003040c444401c1032400c040b5030511200241c00140031041001812513814060000f070302181d03030801c0d50140d800815084240d14107800d040d03080500030354046101c0a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 23282694 1250 23281444 23281457
    0xc03020f0609060c070203030d0203011d07030b03100f140a061502010207200102070305060403030b09010b070218060a03050703060609050f010b04090b010c050303130519050c0402071a01030b0403 86
    0x156a0300091802d2040405034000e00b01e5450399080d111603540010400e0303030940410440d0034041141ca00085000341102da404810780d442600080c00c0c0d5400243c092070800d0f007443c500d0180e640d000a0b1181074154112400150140114000d1000305030300ba081041c0d41d078150003001340d0f07120f03ea4803480840d800c00016100381d0120100172401c034450300100400014130343c00c2d000d8108401c52101c4103401010300403240c00b01c1c0c5a449152410400311021000641c40d01404205800e0030a00940140b040c04041030a1031842c0d03001407107800a0b9640c00f07907100040360001d400c03641d0780c50f14032005681010942c1c088940703030b05101002e80000c1c000c042e582820100801c41e91042041014104c0d20703801c20b04c2d4142070600e030400c8043d04c1c1000c4000d04208103d0b0741c103c0482c50074002540102d032034504031a100d1500380f0300a418101540c001c00950080c072664040450340c0070940200c5c00b9011500141d86041310314000034060703103410508080146880c0080200045100c4a5020b90302907280d5a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 23283944 1250 23282694 23282713
    0x80f0702120a02030106140108010306020a0201182001030c02060a05060102190f0507050a03020604060305060604030606140901141809070906031202070506090d061e1104030201030e0a0201090b0a090807060c0302 93
    0x202080390201f44000d000491a400400106d8060340c040c10407510148000300d10952040440140c0280c091010b071a0001c000801071000030003e00e2400c001c08003800c090022200341d04000c2d480c0c80c8000d041e121000d0f224000114107a100f07001d62901600300540510b000032160030800803400c03001c40201e4440c4611072010541e460203500004c2126801000c8a00c0c20341802401c40c00380c0b4003c0c00c1150081c50501c404000101103006e21005828100c00903a480704034102005100f03041030b404103400c8508408144000d07244c0440032611103005501c0851140c54659004d443e207046030b0301400d100c41c580117000c01001102460b0140c84034059003142c81094466007041114445c0c45002d40d440100800804005001038012803600380781c2c0c4801003001403003415090113582d910140070440b10800a020300440da0144605010349881794010702043c8115400070780b0154143c042c01441306404a2a41505803241c3c40420242519606940d80282e5070703107014040c0004003404038054040c0040c0d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 23285194 1250 23283944 23283959
    0x108060405040b06060d14040f0506073605100801050a08030301060909110715201c051305010f0902010e030d12020901050d05010806060f06070f080f0702120a02030106 74
    0x2840d010710f40000306984151260402c11540380e10410400303810039100c5007410190184461058801e0380a09000300c0384000600c0d00d03905009008001d042030152880454a0040e4400c02642540042078000c0b0007110208070000031562013035100c1d036402220020703564881c944c0310b00c580b030490b04291141064903072500303205c45e100d000902421001070301548080042c0c0c4419049102e030007029492942c40c00c0f85d40d0b00c5a0f00c007035030003074100e644543e2141714402c000303825486040c9000c0009410070b8204865480203490156032090800f5a090702c49000c80d24445c0c80d0741c052082558400c008110800081c03c14002600340124140d02203a204c0d40c05241c0c0341408180d01d110030400d40d8a240000515105200094121343c40b00c50400006004030210194644070b494043c060040041a0714945078041040d8034112229481c02214240106000148580304220b5541c0c2e100352481d4440300318040640880c0940c01e006035001403904031610300c130003010803c034541078029402480441d466110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 23286444 1250 23285194 23285201
    0x102042301020a0305030619031209030b0105061602060708040b03041b09020f07060e07080d090e070c02010909050a0209090c030f0907050f12100507090f0f050607030c0f0203030c010b01080604 85
    0x10113008a81d00f08000b81440c50700901854502240ea46e8848025840c2d4807411001d603050804900416085041441406861a4a80c1c0140030484482d8074003000041c0e0b21209000001009004d458089048000c10586409a5010f0107466120035228a80740c142031807021203a00c40700c0c03070a100c5401d010800098500031601001080003840f8640801c0d07507521001408407407410340590260041c0415281170912050310841c40719901e4032142824500c11010440014120300d051140b80110840141d801c001c0c040111500345000151075580c002041c0c020340305000b8002c1d8080e1315101046540c1d000200694012000e445507542d09590f24035016a450a141c040c540e402900e20761f0f19015803914950012005050009955050300340994102c1595000d0b100350b008140118400d00c03107100682180300003085c0c6082c0b07601c40740e880d0201040f240d00c106000a800c1124003039284090044400607150880e034050101d03036035008030043d0580200005000d050000b0452404940145041e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 23287694 1250 23286444 23286463
    0x4090b06040b031f180c0e060405010f05030702120a0804050c01080103240b0d03030b09100e0105040e0c0a08010203180f070b071e03020a02210c0f040608010204230102 74
    0x84450345180c4984c6201c084440146403101d003e408000004035516001c08001d4510000380a0045a19941d075400600820000c00620380100c0041c407041100783c0e8408824440c80754a401d00d241e4944541134100e003460b14408900e042030200103001709e21540d0112030944214011000e8526600e031200044a01d00020300c406422007001c3e4610a0008154640b12110200d441d800040c220703401c100440c030b190310702ea05c0950200f07555541c42e00700da0811001c01c9070321500da10f03a01d12a4500700800700e40c11100c1801110b026598a1300c0110740c1c80c0c02007180f4402003d0041824000c15a5034150a010354801c40318420b0b1b1811584400299800001d0281c80035440388010f012010308000700c050560304601000c0d14a0201c25807640e0016820720f51070640e02e8080d40c0504034404441c018088540000c180c142c050041d94040110b102c1c80201e082036015034121002d5140c0c86580300081c0c050042c540140995510000d00091f06110040c100d007001c0c0c0e6103050b0511a0180b06006a0b01d07020340790b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 23288944 1250 23287694 23287709
    0x711010509011202030628060201050106080403020a0308070903021e030d0203040b070b0c0412060207050114010806130201050c100510140d030309080706020406020309030610080c061b1204090b0604 87
    0x22043c5103002d04690091a0b01072406055142668181c0714031003507640007120b5883d16203072514410301c1116828080c4d603000d41441c0c101b80006040c1607800035a5910030f21400380030448404041580c4a200c0d01c0010001c0d50010180e8402c0412020246160010302810038070034030540c2d00103000e079800401a1400c07108107092150138a4015100c0103140d090040a45550103820003000c20358504901d007680300640900d00058855405103003150840720a000103051204012004001001000600b10380c0030303051503c041e080610503c010303559401201104c800e40c3c041c0d890a44020195640440e2041d91042c41d48550182e0701c50004150000d80c03a4255002401c00d950400845d000740c11042c185031140480071300e01201525050200d0300590004001a000050703511120b180800429800070303c0c050040c100d03180341c400081d6864580c5c0ba2035601500b00410918070604080440d070b244409000e0a46070004600e400b00c1c11507922601520364114030304040d00809042480980702650380c007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 23290194 1250 23288944 23288957
    0x1060503190b0a020904020f030a0c0c080405120a0203030a0e030c09090d2703080301062705010c03030b03070605071709060a03181a01050a06030905121b03030705071101050901 78
    0x50741c50b00d8080301402002615080d4013000220610385076480240819010052010384034108281d1030025120404454410010644d60340b0004c6001c1c50111021242e0440d02e0301d000391b040e1040340d0304121540f24080c0d0701d0300003c900300507050341000c0c451038130003021810748940b44031030403c00c620352105039840c15160b070042c151142d02c10300602190750390944141c0c0100c1102240521b4031407a1042e40c10481e00740c075001c0010400c65400c0041e0800c0311024420790707d0b00c42c40303c6088802a40c2d9920039141000b00c29038013142850f0003688203108021018007909c1742c203512644003a0066101000840b580d8160303c40e4241c0703518030365050740d120b40e2004100c00d2030104000f0b4200c02401509000724400c160f68407a0a002400348000300340031508926040c3e11640c135010410000e1189075100400785410050700e031002620200b030040b00c2c400303911191600c03803d012105901e000d1001c5044890740c4800000c0c0b0082d0f0750401d011700007507440740e55521102270f02d6074011501c0b80266502c3c3ca010494 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 23291444 1250 23290194 23290243
    0x910090804090c020708010603060204141c08090a0909060605010f02030a0905010e150a021e0c010c02040e16060305160e031f150b0c07060206010302151e120901060503 74
    0xb49504024102e072054030456071826219001142110010381c800c0302c1490b40085c3c10403604290581c1180b0a80302200c070700d80d100c0201c1c0c0110b42d0ba42001c40009200b118001051000e40d5a40343c0c40c5c0000d81b040c10f00400080c925860207400030201406840d022516100b0383e900040c1c070000450305818003903515185040d1402e4015205a4030030a0a01c3c0e00406050426001d0200c1d000501102c01581d401001c88200108014848001c2182001d403990402e111540e4a40d81044070007543c6941610001401a82c500c0400e0074000d100c80d04004000724160300207402540b50300201d0003100c0440d40000003c500904c1955006c40410340c0c81e4044c0c1200000b9000c8616404502d0f0000410b00030100ba03a00c1198694000c0f00c1d00e9400c00209440e01040903204003104000d100007800701d81c001000300d9419034002841ca00000c01c54087c0007000003c0c0f60755201d903544080c980300b800e110045a00c441a1907045c00031220300f2100a55190700e410400115898001441d01c11800340396000c254586 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 23292694 1250 23291444 23291459
    0x409020a14030c06030406090308070f140c0a12080414010207120c06060515071505060109120c050301020304030801080616120b04111207090b0f0f03060d0c08060910090804 76
    0x10880000715803600078003052185a840707010042d48518494100003a400b10607207009050000003418030030400c600d80c00703000c2159410030f12941510301d0010b00740c0e450f6521042158909000c0b0385004283c3c0c0d03001104034410030380048000d400303503102d40500c0300010082c0602c41d00701e000b03145002c1c088140954030000c0c05030049010343d150600808011030314070b8444000c900d125502150509800e000080e086050000c02da140201c6c4034041c66060213203040c200b000030641c00442c068944980307400c0001d03c2c200003040c900e502c0140400f8000755282d14241c1030141100c1d4091042511601a10000959018051110701005181c54a5020300340f5041030b8800003c01e200458560816540d40d21424243c28200c013074500700800e0301060200303181116000f4801001a4855000440b00b80980441c0d104110261401e10341c00442042e180c0c3c2d00c01e000540940b03030707030700300a4a1702ca601040070030034490100d10584510800c80c01c45d090b0007400d074500f00c1200c9800101030800d6100348824031504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 23293944 1250 23292694 23292719
    0x906010c020306010312020d0206010e011412010c020706030c050307080a0f060509010e06030f06010b070201030f0b04021602040501140a150903051f38120321060409020a 75
    0x6161003a4050229404240380080c00c0e001510f924004038494010036504220719800e00b10301e0303c00740146515059801140308018043c0400c020b5400d1152900d548911102c0540d0b011044024000080c10701806921020103000d50300000e400e00000707019081c011030843c0e0060341c0c0303590703071a1160390307400c01d031800038105040b175000f44a855080c001425520100854041d202d1840c10245070308181d4201490403c0b42e40130300121b60070002c01080f03000c07245004e880c0420780a00300841c110090001c02d5005002110044c1c1d4042e102180740f0482c0902d0305040c0540a109580411141e601e480001040c0e0810b01c6500364001a42a804c0c018a552a00c0302c0e901503104d4101291455165580c081c02e01c40481d014550b017030315107101481c14406074060b14041e001c82410003450121410a0403d00403800c3e4940c54100520701c0c004ca5054480c800040020541300c001c0d43d0311040d003000d0341c40b80d0404560080205035107210100399585880d21901c45180d030b0082044140303915042a030206c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 23295194 1250 23293944 23293951
    0x40b070e0402041502100b0301050f04030804050307060c020a0201030f05012904030b010308030a060f03020f1c05030c07030507050406050105070308040c0e0103080c0616051b0a020a0605040e010801021809 90
    0x100b40c09010000702e0000d00500f103140000c05170042c00458810980a4044880c840c0b03515101c1c0e8144014454400c0034102c20135005a018640b4005655480c1055407461003044001058145003202540c8210760116150001310301c00d98041c004070070014000001c1d00d000780183d651a1b04480001714040b10350003003a0036150100e4074083e0034107660340c658a0100209a20030380e0b0700040001000008a43c5105070360140c1412104040d4050a54020802c0c1480c20788010f401286000c0e0345002c0185480348c050030080d400003c0340e0f92607145070314098458015200490741d500c00c40d1004940d500d014050b08040d110103964113400c0c68006c7e01e00300ea0410010b04243c41d031850300040400c0d02030310101e000f4041d60040b489541e07910b140450b00c0c0d203005801403070704441c1042c14807009000c591100449080f0a6848500408000848000c42c148010742900941c000c0b00501c2c005030403074000014004031082200b0807045030b070742c44000c0d070300780c0c0300d45441004081c4040103072998500c2e041c6c034007a41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 23296444 1250 23295194 23295199
    0xc091501020a1502030108100e030301140f0907031b030e030f0a050c1c08010b0703080a021b06041a070f0906030518010c020f06010b0405091b0f0d060f0e040b070e 72
    0xa10031490f40b54030341a0014030701c2c4244141d4000006016441040041080400001c08200201500c00c1c00c15a2240010300440040d1568150b03210050364490300c944681d160014194403080c100b1200c098020304a011100719209070f40d21000c0c803520b0080c40360782094003d40c07001d0340c500103140040003244e130302a0001a0a011051005030b030610b100700b0490812120103825180c00f40b507540390241000c44140d009102e08041005070400099001c181141c22503160302016845241c142110140c085050552500303521500c01044148165144200c18200100440740c410f503c0c0d00004aa03044015010700000c85d5030f10004001f96407090380070075401250032184103c1f660b18213040c030b03003941c02050b20f4000503400007007841c510b401c0901c409801000c91201603413800d0719100200e000420002d00080080c03c9503045c02c501020800101e0781c00070140c0307a1040c0d980c2c01882d801c500801d0035015a0300100e880100c04140c80b914900250300940d0804800c8500340d540e02da044892030740c2104601d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 23297694 1250 23296444 23296453
    0x3060d050307050a0b0a1506020a02010c06062115020906030c0901090308030406050a060b0910030908040b03100602010b040203040b0a09051f020a1e0c0305070c05030607030c020c030c09150102 85
    0x1011803824012403c40320311402071711913a0b01b00058000d00780c0d80c100c00140061a0300e0b00040207400d17000555035900660a081800320b100b4a410b01c440100345d0713548240c10440c003488441030742020b90221303016a14420302e00001080080c140c003404a0046e500079580001d8108042401c4d04442c0014003043c200514101400584903a175000150700b056034101c03074150311341d010b105821000f400313940c0250040e8000c80c0e0411591400250b6450355088103c414541d0313a4152900340b100c540100c5001d85a4149c0712503503401c1c201900468034040b442024015480c1801e140600c4c40d0a008a0f40510382012200d6165103e0317450510040100780404c4886100b00c445400c410104806030100740a80e039540180c552212080c0a8201103240d00c011400b0300c810b10031040119006401d1072141509407808a0312001139181602240d5015009140e0502c40c6404200304694590000702c0456441d0b07081e5841d08400005040d41e401640062980c0901071318005070000014890202035600144101d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 23298944 1250 23297694 23297707
    0x6090601170a060f050f0f0403080604020d02040b04031406010b1602040c050702040f0209030c030609150910060f03020109091503030f12060e0103050601080708100f020408010e07090f09020603060d0503 89
    0x4070032a81c003084103000c0b00e80c8032030400006d00c602400440e0700c02c8002c03c40061341d103000e0b0360060103000014441d170720895001c6079a00c010030440d4151130281c5103030001d0a135110344034244002d0115080c3e50301c4280744541c0002059203461502a54580c4d40d43c14401d4098140c15820400907000790a407400030088140814000343c0d0b10742c068070660310343d03044005030f032200340505050401c100304400d20f020790b00000c14407a800e0b07800034441c40e16518036421401c498039401841402c1c01b209080d042501800c04801166100319801203034100d0b4802d807114850b96039104240016904203000042860101d5901000424000c1343c0c400200d101900d4404e2013001c44130400700448241da0410422105080014000c0200401180b405000c02030b004205151400c07a90326680c1d100c003107132030600075154460030754408015016200030f0504a0002e11655444009083e46c441081c42078241080c20540f00100d0601c0d40d00c00c4151507600036080c1c515541e608410f000d001c94005030100d07521320080102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 23300194 1250 23298944 23298953
    0x17130b0f090414090609030702010503060906011e0810060305040515040204060b042301050903030301060c030e0a030b0610050a050a08100504060308070b09061003030e041512020a0806090601170a 86
    0x1100000710051000c0d4643d03003042101249001001081000141c1c03040094802607a00001030f07c1d80b000c42100c610010f070340c078040100d55014582d440340e0344030240103501c0c810403a005400715200780c0e110145141c401e17540750001c4054510640b000b4105030000e1401160130030050040c1a032050000e0800b2440d2561603030032203000e51082c0c0c09100c0c84400441d040c420715040d840d10b038a0409003440c0c06070404600e00300003620307448181b01e543c0601c46682e500800301809221840031083c001002801c40c0b17640c07170a00314011901202e07054420040010203461140c01101070ba010100c0a9941d01d082c003000c264103036070700300021b059051070307454481001031aa6540c1c0612405148611380a5480b0b00b650314020494120103000e9010300e402400070008070030f04a040f940e04403905841d140f9001100e040c0414020051080404500d03034910710041b40c03e2544151039030307000348256101800300307560352040c07a01d442065440244541090f00100044404108140403145000040d0b039a010314030fa69 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 23301444 1250 23300194 23300201
    0x2010903062c0f070f05010e06030406060b070606150807020d110f03071410020c03070f080d060f0501120204030b06040509122a010902100807090503060405060417130b0f0904 77
    0x20800b001c0c0e4000d0541c0190307a01c0a0001200604000320020041410980040c100c03000c25107283d8024000400007400f4820b0030b07044180100b240c10016641c500d0b031820401702074a440d0180b25450701b079a011265a09104421180c0b0424a41c0c0c0601000c210b014021140f80f01040d220106511480560110448041c0018640340384035401c034804407400d5241d22170a0100c81a50501d42e18814061140d4944000c070458091981c405099003e2900c1e80c9088500c600401c0c0240d40c9017403605c000801d20030050b005443c1503030400d072145540700001c0e0302e02e202680708502000344903407050804100f090604d80c204607085049041074440e00c0342c103107003130950781e0b04a40c0c1c0e442900b92050560758a00d406541e00070001c0400c002c000c0c0203120440e000b0401340c20303c84207008104820800050f42c001d1041015101a2100a042c1c661908250904583c0c4440c1900e094522102030905c0c044c1c6d80c506001110103052505096007000c510381007088040750001c0f80e00c615030107405c000e000010f5a4510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 23302694 1250 23301444 23301521
    0xb03030c01050a0605030604110103050703090b18010501080d0518010903120e0a050117040201080403051303030c060506030c010903031b0605010602010516030204050102031c0f050106020a11030a0201090306 91
    0x40000942e86846400c610694046510035400398001d030050002140343d40c408201280310a00300400d4039140c04004070010161080007905201c868400d000401102d0b105c15031080c040d001c024407150740c96400f1280c0705c0c0008114003010450400418050088900010519007014103011036200c0e0b4a40302c5046825500401d1400203550130a01c107a2440c105003a5400703041d003071a14440910310030400a03983c403c081c00103418800c03110000303010103120700101d801d590071070a800805a5901e28014141d841c0c2d034101114251b040c5000110700342000600c4080c1040305945007441d013455524244c802c1038003100c5025481740c0c8018002c01043c1e41e405031500922503940001810701c2c0c9501881440c606650001c020980100300c10007072680d0010541780402d04c01007011212112240c0c0082c001c0413001c1c81b00c64282d090000000d0115000304071100000c0c000c1010010843c0000c0070191201c080d4503000b0b002c541030380303014000f00b0182d522a112074815010360071a103c4401009036912035140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 23303944 1250 23302694 23302717
    0x509042c070303080708310203010e01020d05010b0705071503180f120c0b01050f01020106050a0305030406110102030601080f090309120d0f18090c05190806120309030c0111010b0303 80
    0x10010410580d111300203aa10204c5440d1480c003d040c040ea8030314500c10944074000b8080079018910501c403642c501100f0400b40e0080003080100b0350320f0b0707045000c1c1d044910102d80070b62900000260300c083ca64100c03070056a006018054550400152103420410409843c3c200755a0380c8540122281400401c11040d000708041110400340d40b40103041c4000000490042020701c6002d00d00281c0d040e85140d042d00c030115a10103c15845200403401000a44e015661004800c0d100009028020005006072515680c070b91001c02c208440f41400c1c1d210580340c080c001034803400014100c205245080f03130040c40701c409582c0742c265040300081030030f041c041014210360083e600d050082c07600010320340c10308800c5082c2607107813515a0004484d918543e1007400d40807030b01c1d8a42800042c1c1f01e03800311010751345110300e980201642e108005040040c01c81c0c01902444141c841001181d80000a9840d0f250004000342603000001004441e510b09016201b05150f4035061071242958042c8080c00189009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 23305194 1250 23303944 23303953
    0x10f17040b0f060409031709030c03071103060105060c0312060607020402070501060905090a0507050f0406081509070b0909040f0219060507110a2d0b0313030e010509010509042c 78
    0x42c1a030030705100030280146218600d8041d0860009410442c280510343da280018a01980c0f2000c507c1d0a601c070340702811400b070200150490800c080002d942c00c5409098048600507a00c841c14468584540004020140d0081c01086010b40000385041d81c0004060070460804056901041c266040541c0446040e5181e42c1c0074403050140d40300707680d84035280070f00901050002d034648a07200d0495018940c0141030034131015100362250781003200103242e090200c1e0399041100d845030811160a8554221600840d580015810814402d8030201c00d0001e150302160f8a440d81c440704102d009802c01c90300041c041c01640303801c1104545e650010800b5403101c2d41c2d107480c2480c201403181041c0d01c03007a10580030900140300195602070f0f07008483c1c1c4081a907506649501c1c400019030101603201c403d00e44000400c2042c00120300300b20446880c1f1a0f2a180c84618000300192824004c0e070b800d6900140061140e403590f46495000b2801e14807890b10f4003d1616540c401c0040404500d101c2021164003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 23306444 1250 23305194 23305201
    0x31c030507020d140d0207050c09010608010806070804030e0904030e0604060309060e06040f02060d06080a0c0801050a051b070f0203060a020c0609030a020c010e031f0e010c02010b060702010f17040b 87
    0x2014800c100c0f182d540781c500b071440f101c030990440c0c1050140712144090b41d5408901d1104101040002c0d0350311000c01000c0b1029503940b40d0004241402c2400361001500845000c6010f07607020b080c1c0640200e034940c58280c140b1920b0000e020784030030010000c4e81000000c81c408295900c41d5801003001e8501c0399000328143c001801c00308281c030150340110400b03500c00d10400c0003103083c2c80314101310240e04807451030b035948a51040d40041c00050b001400f450107605c140347c040045400401707046170b05000003401981e6030105083c044030001c443c25211410442e071407488400544005149040c490700055010028036004030b49011012903810500903800212b801c1908010085a03030711414420055152030400f00e0000c0d01c0d01000c84d601c5046c40b810b0301924045d07640a0062401d545006181c01c112821148281c5014000010000850b540b810000410203031040c01288a1103002400c480d02c0c2050306e40c01151b000400071040c204105d540416100718200d1151084d0149000302000f00301803c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 23307694 1250 23306444 23306447
    0xd110d05090d1b0b070c0c030506090309010806040c14090409050618070f030c0302010804020f0d06090c0807030c030f050114070504061227050c030a0c0806060102060c04090209031c030507 83
    0x403c681c51501c1d0032108011003000420182e040f6034403100b1807600740350000301031401c0c0c00403020300d400c010154080c900410081b440000050481c03030000341e0754007507940c030741c42c0034041121900c1c3c010800094200c510700700701450030b10003048030740b201500014072081da0f5111103081010580b0203002d0002004101944035504003d10f0340034059841032200e5040c510f0341c4d1154082da1503c4000d040c002054002400e6641c1c0d62407410301100301070040c90303c2008a00e001c200800b07000750b0031180004194070100e00d6150000710801600d0f80845441502429038940099104800c034040303500e99201ca074a006080c3c0c103a81c803140200b00b142c41301c0391180d0600790003901924091203440105460b01811201214440002d011940700001c40b07241003802c1402d02504014846010301d405101c0c2e0b105201c04c12803942d8020703048482003010707682940c40d42001281c0719041a140c83c140720100340001d1154403010360051950400040c01c8130034400d201500c09035522480b102032000310340e40e20100007a15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 23308944 1250 23307694 23307707
    0xf040f0503070503070602030301150306090e010209121908030405030c010606080906011d0106050a020a02040606090503010501090203070c031d0a062c011b030903060504060b0a09110d110d05090d 86
    0x810044005d0482c850400e00000d5590105208481000ca842c1c0300303480c511800780d40500013401403c5001c0c0b01d0502c00c5000c41d4083d40c4100c5c2d4a60050310350468660740c201c40440c603000001a1900c2840101041f0346941c00c0d180c10180c0161403d00040000c0300c80e2180900c60000106419101c1744510b10700f03080e109040c20416402407a030359006a243d49503180c4100ca0305415a0f940341080c43c0c543d0310f0128128582400d1040080d00645401008a90030703400090316011075000701d0082c40240c0e2100f114400340d010903200710002c01d58040040002074000c42541c50306d1200100c48004894100c4005004888036600035408246900c180d5040c4030020358444001811000c2e0000321941d140f80024603410003820119101211100362000300340c400c090603801542c2005050000d070800d400c0810007400180c072558410b900308480061111124041c00c0104220040c5860505102102a0000d008101e8420101280c00c000204401c02c1034400c0c1806581504005d1903100060040600301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 23310194 1250 23308944 23308949
    0xd0b06040f08060f0c070c0b030c07150f0b040b0f01081803030f0402010f11060a0507050903030408070608090d170601120e06010602070602070f09020a02071203020607020105070305040807020d02060f040f050307 93
    0x141c090800046d0007184c003600308401161000c48030280d0303035910110b8100941c001c25800600210f1041094210040366400c241e160090000342009400f031990104401c90300f000f4034554201491030b10120240d0701500d50182d0010202c0c0f0a40792204c4071034051070031940221a2541300342015024441596842000c4040746245170900b00541e100d101e0045540d00d400502d50a0265101c10000391010300c200241c40c421000a800c8036115a220440c041c3c42d8640e80c0a60000180703a00009801d0303650014000c040c1c001e4940f03030071034440c0c0c00c3c048080c1c50786001401d41c2d060100d401c5060070405058451950754581c1c40020740003a50500c3d00082c04d00d00c050340300c802154070058090201c07001d50a0b1500c11075445a500503964a4040c0d0180e0070300e40703aa0b003e00146004d2140d090240f640204030540300d00039a50081000340d44802007035003101c8080d903010380106c10602c24580103007401c2d88210700040c0001c1041341005d00b2031840701c846900c44d070081005107403c00c0c4200102d045c10042d4902 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 23311444 1250 23310194 23310211
    0x703150b09010302011e0519020606090c090d0305090a0302090a02120106050301080309040917040609030c05030105100504090309030209100819020907080c070204110a0e040608030d0b06040f08060f 87
    0x8903945184c000916503489080f20407040d201000315a02c0030f6002e11304070366110f038043c078046d805e00120400103501d0b40d001301c51050050442e1800070381070788840300450b80102c000800c3c0070a48075003a01d0481c0c0d15080b10380a00e4201d00702c1480440944d80b0140f20501c140011113000d680c40c034103106c010801e410103a11100a00000b07000502800c00007000b9100021002d1300c2c00a1148418103010b48016183e010103200b17050009800708615900074003c00580380140e0300102c1c100d5441c0107150881c0d60403165000d010242c0e103001c1c040f6141c15041a10000e00900c3c0c950b04ca1900c0360000350300400241c0e400070f006124400d0410589100f40041900c0521030101701d2400019900450801e1000506880401001000140903200380000b0780d4030058000d0300400c03120b8100c00c001005644200d01c1440030401c0d4803945412450140104005c1e2112000503500b01a1608843c601904499410702c0c8e0082c014000880c5681501c0f1301480145101001040507084c89840c42d8104500130b8007026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 23312694 1250 23311444 23311459
    0x301081903080726040305070209010f0308030403032d06060210050f04082808060901050603060312030a020f1305040c050313030804020409050a050a050c04060f050d060207050703150b 81
    0x4086034011811943c4001582051405201d101031080d070300104694180c13000e0300c1140c00344404c1c945e001c0701400403280f096417021001d90302c6098a8544c0352007840020aa28001c00000e8006486500403142032248040c07202d60300c1041d00022a82170410310b000300e90171603803820108071107a41040400346018041004100c05d0900840c00d210000005102070501000041d04ca403565180c84031480720700140e01c40800020349040030050000300243d0740c07988602010000400c2a2400008a070b000301c10050007404d801da1158800d802c80e41009084d01c50b015406c2c0112156400503031300510010564000070704250341010304100403150741d45880c5041090074010482d440d4210003000982d00e81500340500305644610004029049100c4002c125002d0107815004020002811085841c4194140d90b501c1f030f5030703a060004a856503c01d00f840d00744222801c02c070a09100074621420341c002d800c0907180c44450384a142c41e00c28184d1003164045114401010307241924031407504540790072507101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 23313944 1250 23312694 23312743
    0x2040606030b03070902160b010f08060c03130b0a15031b080601030c09020702030709090f030201110310060e18040302100612080306061c0608031809010e0c07050708070b030108 78
    0x1a81d1000d85014445c1d03c141d0000e080c50b00c940c545990b00e0b0b031040d84000525070541e103800d01640c0c01d15062280c4e0500388652400b16403001f5000c410f8900c0b9400366808004440001d80342c400700c15802425074400250748820005411005106641c042d5015109012130000740c80821603035162542c2c040202d540001c8010320000c2d040714510700c2290601c03d0051b89881203070002900700380281d401050b1443c90700720600204804443c1c003912941c0203030020009142d407110381c88114401290070802404a41c0014000a8001c4242072011140600000003400204507501d50f0440290b4041c0c0260b445000f503200c00700c000f406080040d2030381d03289166601c00d89030b0b10088a400040d002604c5103e01241e030382c0000700b80c0306c0745c90500b2904100500070313140d580607240d88039804001200c0050800e0142100d2034104040341074100c031022403040c4503990b07803071540b003499400088040f1080c1c001e8040020b0680320030454a0003900c1d61800c1170f03a580d40741614091401d0611038603150360300e03140e0494 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 23315194 1250 23313944 23313949
    0x1110111120c09060d1b02010504030e12010e031809010b07020d0602030a0e1605040c03060e060f01020a060606082211090604020706111b060c03060d03030204030605070c02040606030b 81
    0x399420316840700c4100c041516000c868030942c1c0181c00341160414004103407109841c4d441c0c1c02403031010784010314601d10380c40042c50480c00ea8804980103000701c0d8481042100ca41070041c02e00442d00000400019a81d07030942c0b406095910049007800105203040452140b8581000440d0040c001100c003146001802d0740402c203035105805024050765408030003d018101c450304011154000304065071004100d203002401a4032030741c000c2a0142c1d1500d00e0002400d8020300c2200c1c1603a030740788405520b581e02c03082000441a11800700d1811070250040039000038083d806000c0140ca0b8a4803641500d29000340400c65070395a50381a040c0c4001d0240c0c440000c541003105036a00700038251003a00c1c3c030f130381e5020228000e882109402454186040140401c00810f00080c140c402c04140c05103e4105440d40d50940c1c0700300030b4402c229400410004a161791038080441d80800d442800c0140c01d26030b40342c4505046600880c1c00318049009644400110b02e0309105900240241d400e0412240501d00003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 23316444 1250 23315194 23315197
    0x1080103030f03020a0c0f030c11040b010e240414040f090f060b150c0303060a0603060803030112060f05040f110103060f1403210c010624120608010e0a0201110111 72
    0xf03240e030004028920503c81e15600e0b14160f04000c0080150707074689801041d2051512090b04c01000508060007540b805024051101c00140e407142011003810741004500400441c5881c910050f181c80d100e01e04a802002c0e00c000c00e085411450614120001d100940b4000c0e0704141400d4505800c58000a14591f41104031075000302c800118245000c0119a8201115160643c03500010503d14032000c400401148544d0f03090320f4031440640d4800056082d12101d028406d0641c10900050151415929074030f4203d42c014007001c1488910581e0200031941c00b55019181c02c08021300040520100c0d080d000c2400350300303182c03c2007030740d15008000d00e900c003040c040d0092000c241400034041d0750301004590074043c0ca800000e100041c4142c120b400981c0103050240455003400000520200c0426142544000050000401c481c0c075500c02c43e021040303e405080040d54030702c40814100070900c04d5102c440301c104d004001009003400090070201c2420000010751303042c0102c00042010120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 23317694 1250 23316444 23316467
    0x2030606071112030309010606020708070503030304140309060d060302040b011d010c0218070f020d03200705010216050705120303040c090b0105071b090e0c01270302031204090b0108010303 83
    0x1200c042ca03003031648002501d482030210800c0b907944804420710545880c19030008041b1061030b003c4440751551040c4d81510341c0000e208040d8550000e000140208081800e0884c05210300c2c01600c2c40d05600d0800a5401d400c64554809015603a035030a00450801d0311a1000d040030900301110040b007040c0030403981030400c803112410003400c03031030310402c5407200780103400002d042480c0540300d8940080003c0110701e6a20003030006104400c11507611602a10940301845050f100240071518958880c84440c1e2001c042103801399800c2006030300f402080c4600c0403200340704a021304040b519000410400b00d0402d0929000c91b0810010b03c80050052540f040850ba038501c40400e00f20003c1d4010385441c020440050003a0803103a0201c0038080301481c20405941000008001860f00700b003585950720117242819007c00c107055251819002c030300302d200f0003881280822201042d101d42c0820300300a2024889502e803400441c0a00c1401d5050181c814001c1c402e180c150050343c0f4586000b03041c1540070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 23318944 1250 23317694 23317703
    0x2090d12020a020a1d010506070b010302040507140a03051803041d07090b0a0206010518130b1b040b040302040b06030403020712210503040606060305010f032009090f0c0102010203060607 82
    0x1039005400c0d05000707201ca599025002401601500d07641c0075002c3d144100409004990408103001050070f180020948a02c01c5e04001200c042c1c0e07085a0078080102009800902880807041095405456020050002080700e036000b2032581003c1ca0904110501007107502c805401c180010b10001412050740c0c02040382010044d286030301c410500f6540d100d9540c01c081c5803154000781d4000c80d90780011b060341c1280c2003603546940b000e0f0401202c141c0d1442c2602c0130b01407144c00d51903610104110801030354003d400c2d070341101c01c004444200c1c002d00350320030340c4042010b80000c034081040d481d01d44a40e00c441c02068945901d18a050b5a00035210015800780c031402059104619091083c0f0103100b000c0880028240b020500744a88003420307a070000c460844243d801e081c0c010030414440c0c0a443c3c102d910000e100b0360214119030b02c030740f101d40b90001d150141681d00c07008940300d5034504040074091100400030b049890f01c0e1a500d1800c2c0194080c189040d6801003040c000c590301c030345003101d2010781c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 23320194 1250 23318944 23318963
    0x70b060a0b1c0f090b01060f051312030e100207030308090307050607120902060d0605040b0409020105030105040b0102100504080a020706020d0503070e030c180907060c0812130c0305010204090c020102090d 90
    0x80c0d0440207083c08000d076080186004048402c003c09041894140c0c0c405841e0450404000c583c01c0368244981d0260003400403c40008200c801001b2045441031403080c10100907403152140881d0200440280100c0141e00079441081070581103190150400c0044018500e17000c5c1070788485070743d484090402070030031804044840c03038030519030f1222903000d0b401002e803aa07402061281001038020b501403d0b115525082001010b4074161040140f010303810303100c941c00e681c0f900003000010010b40c00600c0c15802145a102c044c0c03511407042506c514030a00010340c5404411100030301d08a51508a00c0c150761049004800307203500300c41600d03406407903490000f140341d040313802007403d003510b034100e580c3c104240c8042d003e00c810940c0c0d512846881c4000841c0e4007580d455070121440081c100c005008004100010302080344800d03811680058045040c81e1038103201c1c0e84d8041c011100b80e01c1600c06035401300b000d0085585d036000d41b985003182403009504000d200d0000801a40405500800d510803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 23321444 1250 23320194 23320237
    0x302010e030f1213080118060f090609050a0302010b09100b031b0c07030524010e0402030102070503220509071b15020a05070204060f0f030611070b040305070b060a0b 73
    0x10100b0250340d072044910300f0b071550220a800e41510700d4200000f021307180e2290b02c0012510800500c19450320104019041251248507298040141201c248900000380c030790480101081e210b0048400c01c0d031250300140b101102905000b0f0845017115640c5100b841280f041c4850404110641000e07180349049940e80ca4032100b82c0b040211050810810800340040355450b00c64030b010a01104880c003c5041d10298025140300c540c03059042c404c0707000d030403c0410040c44076589020000f40d10510240006280c4200da0311460b1a540102c09544840082014842680070110550400401040d282c00c00d46c0d042504d0045c21100900c0609108170400030902800e0008001039516505802201159920500400240154040c0a0036401242040c000003500f5400e0b052000845000014590205042d030340c0c0c4030090300350869900701d030480a000d40c001203101e980300240103510940b80c081d0355201615041480300001001540b16200b40d00081202144080407181f03106d1290014022100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 23322694 1250 23321444 23321449
    0x3040c06030c0318030206061011030a05070f06020f1804060302010806040b04090b090d090f080606010c03020a0203030406090e1035070e0403080a0209060702010309020102100e160803030f010302010e 88
    0xe601131403090807002c491616000c2c1600400d07540d0044c3c0d019140100701341da00315410340c2e4450004040020a50040041c407101178803810251140a00c44c501e44c074041001c0c0c0d01c81d1000d1360420200d4400d070744400504280601010041111031040554060040501d1500040e110040041410713004903102d61300380f481e9944541c40310516592200048d401d86c1000c01d40c00766940e83c80c040010211341d5688001c501800034000742c404841002c0020700099075640011124814014803c40561103034850400040c0c1d070500161014014035591107150030714042a207454500d000e1302510f01100d400e08180101540c04082500180d4541e00c2c00c0310034845441041011a0001a0160740b03000d03211000c03420542e060b640c0d501645c000c1e900e00303026071585202e950407803048031031380d55216108021440055010b41c004c02103050050040e05e40042e813440d078420580d454414540e12541200e110545103050b07000c4901d015210820045003140381c5200c0c84008260b0601019041c030140300d040d0811039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 23323944 1250 23322694 23322701
    0x80c0a030b0604090507080102210402101b080d050709050d05060106050309030403020a0b07020405250c06110a09060908030405010e060d240501020c0d080304030e060c070806060f0603040c06030c03 87
    0x3a0f911900f186c1d000c599404005000790040e400f04401140e40c91500c451000c015404940030f80e4000344030b010055412582510b40e60b400d64503001181d03044010010114840402601c849006180081004d19000d08002d26141140d081070f4443d85010001c2d2000c03034030014496040d01c00c00e040c002d0341c903200d001c5003e146001d198002503128280c040c02003400c2000002800b0b0052003a5014010341d11404c070346900008030150240b402404c0801007640e6030780300f03121600149008500c005805888814031640c10307405080864007164031207000b080540d61010403131004040100c00b81d07041a0409000801d000c42c00c0b200c052150b4004501c103107400c40c1a5010290281403044116010a82903d46181782003241c8207080c05030052910101c85810f20004030040607611034199803a540c0d0b582c5c0c0580c1c0c944080c0c040250402800d00000c8106101000385101904e040c10040500d86005c400b0040460050310310710b40110b9040c02407200140501088405a640c2400e002c9800861130f241103000703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 23325194 1250 23323944 23323961
    0xc0201021f021e03010b0307120f2c0105010503030f070c08010204180c020d080412020708030a0908010506041104060809030702040f0606030e0115090b061201060801060207080c0a030b0604 83
    0xa01410410603900103a942c010840000c441101c250880090010b00034180024407035440b8500e800c00000b41d07004c0c4200386800c1483d201c02000280c0032a04e90320b0302c0844607400386103000c08d1103518010001c40301c400c000340404004000207010560501e00402c0e102c0c091040c0103001030a01068a9003000703003030800b010280480000854071075a58240706180701c4010804401c2640c9040d0004a14a101107030344020304100341c50b1034070540c0b510b544450048001c14003000071800740200115048105200034000c3e03680c5661090840c41c2030082e96400c4a4001d41b09511a614000d503103004040400103540c103c076941d05000030f0340e1781c0f1035010904512440c0e4000794030038541f03080189200c84981c04801551015581000105203064407107007240d01c03840b1004541f2054110401500b8010b41165000503c0a1325644c20310641c0c603c40042c200003a003000700855000e1005208640e4100181002406554020000c021407100402c0c2418450300029003c05010000146a512242c114107034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 23326444 1250 23325194 23325223
    0x150c010e010c02011b0306060e0d06020909090309100c050a030c03090f0801020d0b0409031403060f060d05010614040605120a02071e06060b040506090d0f0507030501060f060f0206070c020102 84
    0x141e80b034401d1009000f0840c0055a0410703003520403409442034802d00c16007003a10502e49414000540c84020017000d80440003044a20b40c0d020003aa2015880c2c500c0064004c481c02001140c4881d45082040318550700660750070b007080031004690011410001d040131161f5054180804800c04505044601602a800060f58007400d00400034902c801540140b00310000404200b14517200002040141c55521750702a0002d40100c3c0d50122010300c01d8029a0407440040005020b131001e00c01164051308054405405a0b69039001000390030b80014410500c0c081c050b1950746480d0030640040c0039401403441c0010510b448200007254801240d044442c440d4004148070303c4034105250180b66601458403c50b5217904007000081c001c01c060042ea8140c400c010242070824a9000610950181690003039a10b0b0b00c2612504c00400d8045c40414041c6d80210f00101d030042c02c0440031000c50000b81c0c4003104201401c42c18800c1c040c2d000c14456000207107844d20340c400c5129800101c1c607100d02c0c3d82d01c1d80c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 23327694 1250 23326444 23326451
    0x203090d05030301030302060114131d07090e010501150c0b07030603080708180108090a06020711040e1506010e101d0910050a05030d0801150c12080106080f06150c010e01 75
    0x401c1c0900003003d18101c0c0e220782c1c201d078a1a81c884c1405000101148800d0b500190390030400c40d10481c1a41007140b034080050995040846d01000c0c09117046210743c490750400d65544011070010b1002e0007214050121185945910340c0e0b1030707078020300c40c88000c0400780078074040402181007940f02e600094011900480c500c3e84607006da0400424136030140181e082034110007100112254020118144a8a03030400a07000c110f0040d1a80c1000c1e50000710700300c48084910a060741c4964683c401c5d0810240200d00a00041e001220703c0307000040050b0000b0705000d1003040d10a51390340e90030340c40c02e084001d81c50110815802012101c5c100341c42c3e401c041e0740c060039042c01c02401c00119601e00040b42c0c3c08031540d40380a90342d06c081c16100c1074148582400200341d20010700100907100c0414241154502e001070f810340054131a107100048071030750000022203103c0104000c551000420f900881c40700b0101da07035401c041e0000744c03030809441207a050381000410150600794080d07025400c0c0c003100c48001e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 23328944 1250 23327694 23327719
    0x601050d09062d05010302010801091d0f0d09120c12060e10021e030105030706030b03070909060204060305060414072a0b040b09030703050a030902060c01020d090308011e03060507020309 82
    0xd400300c0d083c0c1c455049007103420007126110381ca0b29008040c120794041c0c48010040c2d0904402101a14050304240e1406030300103110000380300c0c20000c8150310301c812405015942800320004218030001c0c0c0c412070500300c20303410220201d40c003410114101c5801c00d20080481c406850b007000034000d100e100e24003134060340d070500702083c0c90380e0020200fa24403046200815480d013021881c0c10302083c024541c050784106401d005d00d0b40642e00518107207100038122001d4a607503030428016102d90300001c484168000c1001c110050309400340c5038201000725070501040e628600d0f070102e0352500402050400210403040e100c0e800b4000242400d00b0b44220400030f4a00c09421b10059140040c3e03001c5406081010000b00c40590100030381d00171707903415500c0358540341520404138040c2c0280c4200380c0c0c0c020810051003181c40400d100414000d0014000440c03102e1182c10081e0050005a02c21072000411200c400d1041070010102400e8903441080011243c50300c035812465401401420358100a0b50000ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 23330194 1250 23328944 23328971
    0x90f011e08060901060906020c0d050106050a08010614010e03030702040b0a0909060b03150f071d0a0905070f14040b0304060603141b0103020405101b05060c0a0e0f0105030601050d0906 81
    0x207580b1410041e519030810ba60b03951300444d03001e030003842000016000701130f015003145804800700035540d0040c03002280076511200010072010b49035000036a00d0707550b0602001260f501c1c1e549000c1c144000d0a000d0300031444800400e40300d2042c40c4000b84241da603404014229a12030700d014000d091034200800840303d151800741c0041010042051091082100002440c0c002c0d00415210f100c800c0c4000026442e0000c00b6074000ca480070585e4003080d1076014896103501c0e80d00180700203065042c400715003402d0440e409000c60040d41007810801883c0400719900884001c00c071012101820003481d940c2e40e560030503400a22850b0401804605000103001074500001442200c006c0c00d111003075600003c038001503003207100d584203844d0080e6940c540c00240034040c03448600400482000e42030125000d40d03a0b01e080000c1261a0400071801203669060140c1c44505100890301c10750b8000c4118400c031001030950b01008122504028000a0074216400c02e80c02280005900c0340c5c0510030a015100c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 23331444 1250 23330194 23330207
    0x503280f0f0507050403240203150f0307050306180f010c0c03080a02130e0903130323030f250b0702030304060e060f01050405060d0215090a1505090f011e 68
    0x14000d03100d81000c041c0c500c00101c52003a07a00400d11900c407a45040c0c40c0d90f4070819018141114403200d0004046001c0c4561403500040d0700c0f0300c140b0100c0000c0c0e0500070f001c00800101004072640682c1c060001408651030010340039401400e51410595a443c6100c01d41c1c0c80c1052426480e4035039400c02104088040d0403000030305c0428841c2d00c807546540d868008080480c040c0091280701c8441d2100b00b00011044000e07419000700c10320094a01c0d14103aa061310607580d1041e841161080f071280d119186000e6040404086110600055480c0110002c81800b0038001c2c4804d240c004200070320710500501980b8000000d11b9030105d409015480d0203440a902c80e04101c07400e80d0007034140001d4036986800890528442c0c4840d194030340c000d90078102444014000208030580043c1c40c1021403000da0f4030315259860001c04503d00a6a9210000034404401071a604c002103030015081c2194806400005640340310005031034140c5021351500c0101d90803c000c0c021607294190184105044650264 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 23332694 1250 23331444 23331461
    0x50f0d030b0904030c06020717070c03021011030d0e0c120102030f060f09041b050402070c08150907150c080a050a02010608030306010903150b09090d0201061202010906050328 77
    0xc03000c02039801c0700c0d000e100a610702102c00500280340b02c0c0d6070400140e250b0f03000d4500d17980220007680c1c144018404540349584103100607100d507010400d00f08114904050301c82c0c8410203d1a05e849001d458010b495620f00580f40183c1c0c0c0e1039119080405244000c02050905007401010b403503100e0403001c10203000b9030096500207003c003e6840012842d08061300c0e1a02d6800c400b501c60302c85aa516110000a1410512561725154070700350000343d903035241e0000d041c1c600d008090140c0030502d003031003852401002141e04500030038031200300010407030089406402c0b10f50100401d2110300c1c81d40300407512580b180304018465400420f207110801c0d404000381c02004410b800030480c540e1143d5405503640030444120780094138540c0184000703841c1d5458a44145814240811100d0000b40000d00c0301104a600d100c51b9440180d01200303030b640c240502002080c1d6218038921079403840d00000e0000803280100d905001000001c01c6e1402070b120103100d0703207040e0301c3c048600c081030004550b0043d10320702 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 23333944 1250 23332694 23332697
    0x6060f03180633040603050f01060602100501050904030f0e0402030106030e150108030306040207030201060302040c03150f08070608070e090403050307020706050c0a0f140d0e0a090e0618010603050f0d 88
    0x160000b4140c001e900b03000c0d070480940d0044803d4069142d488102c803001411403d150465111240000040d03002c00c9905103040f200d0002041d02410400001c4c0707808200707822101d4480c00c00f4010807040d200d0020003a0425090715003525132000285058801c9011a0105500f05100000020351103a06610a0002a0400084d5020721158800c41440820280500700c4603410400125005140c035900a2102c0e41c480d00005ca4010354030740004d07040f1500891032802190b00c82c0341d0000f403000d00c101c1c0c2002500601e15140c3d412414003194582e210040c2c0a6441800a00b1020611490042112410b000d500412020580c41c02d80790041258006540e8540980b003003030804100540204290741e51448900000c02c0400c00a4441008826100c00155a490b80d413540e40e040941050001c0071103042e49071192401840041c0c24480d201c0c1c2540e01c9164840d284c00d41c1c01d1300c100c3d004210b4035000086d8100c50b40e004224040068010300c001c0d44000c01a109490610303400c1200490791140803940c3c1d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 23335194 1250 23333944 23333953
    0xf0709050d02030705040e250608010b0a0c120e04050405070603150503060408070f0b0f0718030b0402040f0e01020c1506100203030406020304081201090b03120a09030b06060f0318 79
    0x80300180149101000d030000c0d410b4002c10070a00c041d04081e40500700c0c01450108a50307240c07415610f45182d1565a6070240800c1c0c080c09800d01c1101d41100e005801004104201c6162400e2038a0081c842403184200400c90041c920f00d406541d4440e002440d10610f0040081015082c28541695542903501c00c0c40c01103030600c140c00b1144500c10f5400c3c000c41d1000350281c08984c0d521b0b41c0d41440c0340e1040703600715401d40300301c0c0700800030541c4603020318840c0c2809041d4445909102202400720100c452040800c103440c02030500000f004414580d070416410307036020400045035a04200036020b08004480c4561001c500411f1030580080c039010101c003444940761158450000344000c0007101846040541e20410204000400941c001d40c0e01c9802030380c210b81802421f0420991500080c0d0095030050303110000c0c1c2c3c1e411714044c028143c420124285142c54203c8185001d03090b01d215120203000f241e00c080018000d034840c07804a170080e540c1d543e4855a6454200c3d10100740768900c1e20750003207030300c40d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 23336444 1250 23335194 23335199
    0x3020a0902030603211e0d02030103120923010c03030e03032701090305040b07060209090c0705010e010515040b0307030807060203040c0803070b06062104031e03270503120f0709 78
    0x240c0116240c81d11440f0500d160142ca03c1d01e84c2c4c03071411725020f1b0380340414003000209040d110718805107010b18803c8010320b000800180009083c8038058010540c44c5045a8440b04c0112006c8903c0701000b900782484005040e05003001d500900d40710482c86c1c078900001040094848001203101c030320346100f9904520310300c0300300d01032030072101001c10003000700e01c040000380320300c0d038204018180151007200c0143c649203411000c903420740c0041d24148030700c440203d07204040040078041c5005140041d0003c000600d0400101011041100c2800e0301840e0750343e801c441907407014480034001d1508140c2240e91100301d464210025401110180c1d000c98100d4804603010001000701c981440d0000100d55403601c1e50402c00510790b01620301961006d0070004520000707940f03802110701c103d000382c0b03c124000520101400207480d0810f140404c0502d807050444d0902039001c0d442d01103c5004042c124015864906a45103100e0f111094051200d19400c00c41c1508140729080d21a10103603446105455 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 23337694 1250 23336444 23336473
    0x50d11030f04030b1b0a08040b090a03020c09130b0c0a0905010206090309040f0b22050a090209040605040305040b0304052109091801060b0d050604060e0709091503020a0902030603 79
    0x41c142030282500001c00041020440340300301c6582054075a001d0009840380d0100c2480b55a110314502400b1801d040c0400091022490445a00985480103010040b5145c0d500035211900b00c02c040b407042c2c1584000c1026040481007100e940c81d03108801a075241488600e0081c80d4001c480e000000400550000c0381c2544045030490154003064000d40c14030101c00d081101030000b031402c1c85245613980c580c00074a9560300c9000028001c1924081c9a14881801440140c4c0c100a019402d440c1c1080349100068841c079080641c01500041c000509403642e2034102c034580300e180d00a101240c400f200740000e00201040d9aa40601141c80d1858440410705080b0306500640460f03560105038100010801002d0034034070f40b003010f20640006001603d81405070195041000c00e1400160384008105003810103102d40d401400401e030400e90240783c0305000408503103541c040c40f41c0709900c070400440c03d031403090681030207954020504684951505103040082d001115054031a1007900151021074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 23338944 1250 23337694 23337697
    0x10603150c050d11120a140105091515070c030305190305130201050a030b040507050c07120203060402010f03140a09060b190b0a0c06020403051c03020a020715110109050d1103 77
    0x41029842c1c041c14401c040c01010010114991081001001004145644c1010080061050a0160001400c4058100351400c1d020058101c0c80c042c04c00e1030103100c011003050000c034080c04000c44900c3d0b182c10410068184078003800d00014800668003001104045d045001742100301d011500c48513815071050302c02c5040e52020382c1c2c119220801401d204025520030030007800709180c103081c08a050000500801d04a035001c49008001850101e507040b0810b8041c0040e4001f017884200b80c500c0c0d4011600082d03210100071f08024103001c03442e80c0c0c24a005003ea005818401c003c810944802d290011403c005032a00d800b08444e03e6107081e03000c030014030307250074014880e60a1002e1100900d04140c490341c21940411082070601040074000c40010717030b45000500103184540064044191001250049654000421030901d8014440300402a85c0040c40d1303800c50701c88a40e40084000070140036a00d810a1858600786075082000200502c003002414400b191980e9445030403060032400695285d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 23340194 1250 23338944 23338961
    0x180402010c020d0318060509010e04050c09040518010603051f050f07030c0207050603090318010c150207030c02030f0105040c05010c03050d0b1c0b0108120c060403030509031b01060315 81
    0x101e01c00402000241c1080800004424400d0030004581300071005402044246a03100c2e200017032000030314064039680703c02c1c07129841100791000e1245081030542180a4003d2440d00d0380107682e920006001c010340a130302040d01541000080007440c1d100c0c20304544415001c42002185c01c1000c0c0b1601c3c0400052007018400c2d1920780c6042c840780ca88840c01c501401c1c81071104001c40c462501e001c1030540d10440254041c4410741d0041d03940740d107121000d1034441c4404100605200c00c950a031404031307048070189440e07120321180050303445e441850141d6402d0501c120181d01803080800030300103c90154040303030140e4010003807284260f9503140111800000854000c00040f000e0083c0c0741c544c00316400c001184c0710018400c2e800f98a4520b030106501d94481d4081d151061144010030044a05000c03021003c20500091854030340c89400c82503030380a004d00010101a65000003035524901442592143c80311000300350308014020040358084e004a000a070380c030170300741c0603404918141b51003009032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 23341444 1250 23340194 23340197
    0x506030c03070807050408010c0903120201020901080a0b030109200a050402090f040e1c02030301030308060a0b070b060f15041406160314160803070f090302011b020f0402030c0918040201 82
    0xa15030b00d06400701c0b00e989014105105000c014880070403241000e010b131407640000c0d80e40d002d81e60380ca1800c02c0c0020781400e0001c9030969204201025142c2d0b4440002680458408004543c02494601003801060030030400740552642d2000362081c020040e0103020044c504583c20310500351200100000c0344100130350580d10042d8281d103030045050a4201d0361010b08003c7c10b07900a4007107114821013003595491103000507000080180205a0011f00f4039820140c1914403e02403428142843c00b180f248050190070840b0030b034002810381d80c41c00030344981160060640c200100b00103c00f800c051700b01c0d004011800801c056074042c1c2e03042000a944080f121076405803c04421030700c0546095201154820015400b0001510720200007112804130900c654040c540da80303042e030001850120110920340402440440400142c4c0e404445440d10326440c10000c090b020b40340c4002100000382041241c1c1090010080105544042000d40401c20098a8204003d03e0300b080920500b203007141d0003030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 23342694 1250 23341444 23341447
    0x206010b0d090f050304090c080108060105090408070813060201060503010c0e0d0206031321030c0507050d05090103021c02030f070804050706050a03090b240303070b0c0306030102070c030303090c0506030c 90
    0x441c0e0084030340140700141e0040c1d40d05682a6007588038141580d200c0d401c40c019160f201d2406c5104281d11080c01401407070824003501d110350501001403e01e40018202901003100406c40c4001c0c00800000c03a40e003508801d0640c240555241c40180c0a000c3e0740c03044920a5180000021340340c0d0041c00c520006000007480102070b02032079030030840b070b40e007015259801c444026040600043c01520005088184c41803004421900d44c010090681d48030301405410000d05122080018100080b1800c9094160404503129142140124000e004400401c08541055800d45c0c0e20461144d0065001c0c5402400c5400d05a50307081c000d48a040c0c080d034004046030b02045c4200171480c0708102a00440f0b1041c540410501030703d4032500441142501c200641c000502e03001c42c0c42c44c28661014448078007d4000d035040042c84c1e03d9034640c1c04c0008008003c120b90000000e01155000c0d4103c59403d94442c04090406449050060040803c201e0840300d441c561200880d440c6402c0c01901c0c441c0c0501d0000a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 23343944 1250 23342694 23342707
    0x705031c050702060a0333090204140f040b0a090914030a02030f03040602090a0806070e011d011d03030403050d0809070515071113020a0e100206070804050f03030a0209010f0206010b 80
    0x2541c4001480d60405039a07070340d1095048941c0c88406081d1658981f10351036402c070420113940e5201796910903078046e84108000c0140744550403040c0c01d1403008840c2221480f1401c0c01007006002c10100f0b0507800030078650301040303c0c1c3c1355901c04002540200c2030808a141700c044403583e070348620100000580e0042c088110714100401c02540e01904c20310000d41401441c00100d040142590007144858012904100a40c0c0e8000999407820109103000c0d070b09a007015030f00140128038007001074100111f8460400200000803c6407480707000190450382e440380d032418900c0c4c66007040120000066100c0e00420a48070000a111054a10041c100d05085105a84d8409c1d590700c046412907000085502e80d216541d00c0c00c500300c80804c0b40c890056550708015100905808410111a02c1014110859490b1550010390035900222a0030200c480307455606006140081c1c0c3d07000b0140910000007042030240c100e0300544108134007078981c03903406004140140e07100c14090061515148051014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 23345194 1250 23343944 23343949
    0x604051009050301020d09020301050a271a09151305030427060b0406090f080a030503060d0507090603020901080d020607050a1205240a060503070c060f0c020705031c050702 76
    0x1010300d0150324200381c464580c0e07403030200342a40c119080c200b441c1940c0d242d1101c25030800307001b041d40c480b07144d01c020409003140d0003801b00750786e018a449101c000358a058010800100c0c400c10100d501c540710080010b460480000d0355900c41800c66256241d01c040d0108005030bd04255000300544d00c01c1c0610f00303007030030321a0315440b68030055119400c04007500d1040714403202c0c600c10310020740741c042c2813560341c2d0b41041d01c05402e00329198004c5071545134a0030304103e540c2011800310340c0309601d0300d810750b82d0703484101c0011030b552510400548280125200001c035070314142e100f00c08581c42500c442c2c0c401d0781e8448001d9151401d4040c1000560001c60006103c2c40c070413401410b1542c01414180491041c03844181c0445104485240a103284070104d400c40200c502c581502d102400c503081e0031f07820b0500780c00410901000c3d015800740540b03200001304006072508548144200c03100104010100c00400a40c6c0d2025403060f00d010f4018800b8051204850300305102e10000b090304d81a240600c5070b401d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 23346444 1250 23345194 23345209
    0x703120605060c0a0c05031b0d02041d0109050c010305071e02070f03060501050a080a02011d01030f0c0e12030c07030308090106081903020c0d03140702040905030301090920060405 79
    0x15008085a888401003966a11a00a80a0010041e00401d141038035403034a440c5072456178010510aa20200d42e5260018005401c1031041c5010740c0c280640381110b10105006d020040c110f10203d82c0d07040c0300d20300380c40c0303055000440c12030054048401e00040400154221102a6090000116480301040759010064408074005403e0320484480a5030f40403444020001500304071003103511107004000343e2400e012484d02808100001e40101000c50340043c00307400035450714528050b800030207180242c0c00b0b58072103010403554440034003901c007010f08e0040244c403082403081e03c40d040103189208075020001c15030740c0c0900c00030018084103046440a035403004000b090440d0540d240c2070b0100c4d41e601d09002d000c0c443d61018944529001e00f07403401a040050750714019014060765131900f4042513208200c4040340011202c002e550303003582d0010070060048140d02800ea84400000000c0441d110b601140d2818020402040c401101448122443e28445082c950080e820310003800503241042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 23347694 1250 23346444 23346467
    0x30806060c0c040e0d0206011403060115020f1203060315061e040902041506020d08190e03090301060303052208060a24240f080403110a08040b030a0b010809030703 72
    0x4445070ba01c5203400003802da07005480000160b800c1540a20300c400d80402505000d0031001151034030000918022980e610b07414401e040f15400325245580c078050007800440c014040c03c100b5900c20b0040d000429086500503500c203030080c8210800c0381c110030605503806000b0350005002e980c010100f41d244041c0d0004000110350b0255031250b10f100161344c3c0784500e607201d090798502400d00354580700d00642009041d20b2002c0a1004520800240300ca5442044c400303c1071018001500d81302801e105451400f0f480301c815015842c00202000341038010024110800001000602d0350300c40f84108001c07620603120300c1c0b0966205601150003005a604410b03d0400c41d1040c01905c0b207040d0b1003960440a460744007501440420b5248500c1d40000c900c2000281802d00b44410404403d13017005042d0100100301404000d03c1c150703c61a2840d0a008140501e600400c2d40358032542c41e911048141d42c07041c0d90f103c0300d09240c40e01c071000303c0d40110070346441240801c01070740c2001840c0e00c0588048800c0c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 23348944 1250 23347694 23347717
    0xa0534030b031203040b0103050c0306131704030501090b01080f030703020a120c0c06050403030f03020307020d0806060f0c06091b060d0b03030d050a020a0215090703020d1407060203070b01060c03080606 89
    0x43c0360070104640c2e10406103204a004050040c0c81d949507091542c10010305000c0180a50001001c02c000e1541c40e01261700c403164401d680035018140314121011300d00030750304001c0207542000c01c6d010038860b4a0070070906031072506054800074030b002c0c082e4990301c0c4500c41c0020050f801036400f05000c1014081403c600010900b0803058144550341c2e207140404007500200082900400c05000f03060f4441542c61b01480c2c00c1c01c0c2149903080140010f903940303102282c2402000030a01c00140c1035103400c0141d81480c0402a101525011000f00703050300c400c8100d41c880300903ca0a49074201d0402c4c0744035640c0c2a84070240c2400d1a00810034140405440d2042d20303141c051004101255007070f552441600c0c45100b11050040c0c44901c40d240007410804104441c04428240c0c03401e02c807040c4d4010031540101c0e5070441d00781440312400d140c5000004203151018140d4080e60320001100d680100007807003002d21a102c0440c0d01da894560545445400ca903014000520940000e566402d1007002801e4a4510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 23350194 1250 23348944 23348953
    0x121509020408030a020d030501030807020906030c0306090c0f03010207120f090506041211040605100507020d0c08070812120103020d0f020a0b091201020325090b030a0534030b03 78
    0x2605011000d0341e0050b07000c080d42c0e038400940c002d01998107004210b0039402c0391a003804594519200c0321200d01a040303001c0c3c41421550040750a5030741c03c0125624607140a0261001c0703103000c00ca5641ca50001100c2c2c1740c080e2070010717505240d5243c10b10850300c41d9a444407446c81c03410200030040750320031284c2101d4018820000c102144541d50b40c0c0c0500b009001d03654040611110358a403c1c41100203852400e8040c0b4240b01041c0300701e80c0d0302000426480c013030386401a2100340c54000643c5000c80048040c11180764440042060b06010070700509440b841000c40c0c000012622100e200d82c82880c15008464010780014001840c0121040d00d15901840806101841e11b40001d40c401c82030f0390101d040001c00290112048c2041c0c0610034070148030100840c15480d0003070118400403c0c80f00604126a002007400e4030041c00742c1c80030307805030561101a0b516071502100b0603000380000d80d0341e520500080c03183d05c03445140c07901c052003c070300002004441280d26404180d01074010f00360307465858003c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 23351444 1250 23350194 23350199
    0xa0902030a06050405010213120b070e01090314010608061006020c0f0406080f1605010c02030c2707020309010314070e01030504050c030d02030405040c030203010b070809010309080c060402040506101215 89
    0x2d007402030b64016402403000581d0b41101b9940c25000503032a0703102034503004030192141701081c040d81066600000320b081850301c9c00c030440012140c014603030b00000e00543c3d549591003070000b015070150065a40840407141309403285104840588464032403400181c2c009615082981806012441903160182000c50219103501d482c0c0c1c1801007084505d180e981c04440040c1d26610030804400080001307003860890858541c003c05d0b11001e041825074040ca02d2000d44608600b400c1d81951092912681051501e08140800a4480d803145c82140e001a0401d107242110f104070944060182941b80c0321008006400c10054014010041c82510203005103d000d01c103a8405010b61b40300c0760301a074055983d0718105800c10044407442030030309040510510040c03062080310030450b00819000704006440d07103203080049010f480c010400030031800f0f0206140c21580c0c00000d08a00803071003103406020940e2500284031091a103021114005600c0401510b41811150b00840c14110762041a080194 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 23352694 1250 23351444 23351453
    0x30d020a05310506030108100207050a06110a030b0306010f03030f020a0203010c0207060801080601060503180705150301170a03081515040b030415060302030307080d020d060e01060f030b03060a0902030a 89
    0x840c0303082d00b0661445149032031a50209003080c00805020101d4089040d541440340700e6039680d030758103a1403103010f500007203035414414204444d1108560041c010b01503e41e910500d0320b00e40e00080103030000700b810440101003501e80840c125041c1c4940f02a03011010385075072812102c10030004140c42c04e40c02049850000b40c1c80030b0040c1114801260003d003c075507c1c3c80c5008101200507400180c2d2904144010300c80f10744e01004a039041a002e112801c3d5076064601c5c4103007004c28030750185a000d074200400d0083c0841f0343c2c0240d41210840e000c0d0b8040c2ca442401203a44401c190f120050000d885000003401c3c48070b5007000e00c6000c000240011950071841d0010b0250396000341c10422014202108020406c0040c079850001d00c1c00c80a810300c0540d01c0d6a0200380d40c2e02481900030002c0d04040f0310b070402c0c1c00c0e03142d040d80e2507809043c07001c1c44032650b10045224841001c7c040c150006141506241c140e0703000c0d00591245030700140090a1550380e80713003000020121920120b034540640040c150104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 23353944 1250 23352694 23352727
    0x3190e0f0105060f04090203071a040806010e01031401020306010e120f010e0a060501050114030106050703030f0c0c0302010609021218011d0c0301060e0601080f0601030f02070b01030b0105060309030d020a05 91
    0x35269200000d200d040010800c60072060481c00d9030320841c2006490401600e003c64134a00312860b0340c000303042c852152196020030b0f015940000c0e2080c4100030002803001801d1084a04072806400d02500d1403c40300d01260030303844201c90b000d002c10070f45030340e9800714103003c00200c408200010686210142000049017500c80400311802c440e442503080800303001c0380d8803544c0d0040000742400e61404c046680c40c941355020502ca100c050080c042888420305000742c2003206070102000301001841c0d9843d1015080340c01196080d801980b030000003203052400351080b2501540c8448949440b0369400c022501e0b201580b40712540a9501c0300540419a8402021300c48500380070000340c003588915605140c2112815880a00e001800b60148011a40c001c0f00a41e000002c1e0008058580c5d80c001c0180c1c064100c0d40148661280b0002e0705000744036034050600c0c10f80e40304400c08491640d981c0204011400281d03010b04039034001300204050700040350300038442ca180302d04003281070603a2054003071440b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 23355194 1250 23353944 23353963
    0x7051c05180d0c03030b03010f050405100609020405030c041802090705030a0e010b060f0d140a020a090b04050a121505010f0303030b030607020c0114040902031f08010903020303190e 80
    0x50351190240056007030341251a0044184007001402c4501004000601844411402900740344d50303041d0603c0301d0b0304d00390068052406803a0080c065800e1518040781c0d241c05042c2c11302c50140c6461800316500f40740d80200d504517400140140001c3d2413840400c002001a4884d248003049201204001070321901c2d1040d220f185181c0380c95490f46480c09040e4196200c0456041099151900400c400d64840f0141c2c1c03110070600244944401103842c18034001d00510300303041c0c000b160340010003800c0b03415500241000b6449955060809503500400004c0c0c3c0600c0c0034040d409800104103025041908190414a5000320380900c0307908a000c84c020111002038004401c41d030781e101c409000b850707054050150400d005178010840b03850280002074442d0a444d601c18108207421601c00c40205003201a900981980c035011540ca0821403450075070050300e80030f03543c05051007480c001003844062190020301c6030982c0145107542e88000502681c040109006209075941d06210891140d042226411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 23356444 1250 23355194 23355247
    0x2205010902030711030307050403060908090a141c020f100516030c03030b03060f0a050601092d0f0602030403120504031b0905180c0402180d12090b0a170705 69
    0xc2d6030801500c01004108150103103a0715a00420501008a5000d0700b114112a001900066480c0c49031070006101e2154945140c2d00440c0c0000100b4040313000c400310308025800b240c0803c15005202881003c8110030500030b9030040d969540115241014000c940f98004203161052602c1c114000c0301c022100400c006800203080703074480d50109a0141b02c1d1109080c0100c004003d1460801820a0500700052030030b0013950b00c420102d15147d01601c0400042c2c28400300c450f501c880340f054004501c1c1c180f03011070a108101d1503000a02007803c0d654110640c0c1c0e4a9019500e41415500e031096040309102f0741e4000c0141c100b10000101c1c00d64498008100c04500d50049006e203490b104906071400504002c500c40c100030342400280301e00007402240d405d000e8801586401e401c016480958208094164001e880001c0104c1080788041c5440c82c541d0391500c40788180c0340ca40032078501c41e0041c40040c1000c204015117840c550796900c004c0035842401c07454914034024100e200c0a0441300070020420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 23357694 1250 23356444 23356447
    0x15030a0b0a050c030105030a0201121104030803040b0c07020904030c021807050304050c0102060903040905060f04021903060b16020d02030a080408070503010b040b090121020d0b0a050f06010207052205010902 91
    0x181c49150b0700900ea003200040b14010f003154140400a600e540d4003140081c1800b00341405016018142d03004440c01140042445807540d0b66407e014020364000c5a00700e5051021074000707a0120134030001d403070750140c001d0b100010391780d5166021364545204c2c00080e0f0348000c44250500800c05101c28503841032845a42c2e49840381031078500305d40390000030301106042d5008003041190103000041500c7c1118401d010119007512036201103001e0b01040800300d0342042c00050000b0400107005203088548215a604004180c0c1d21140c0c540c440c002d149482c440d101d015030200d800b61070101190b11203940010150340101100d683da04142c4e5000b035210681581104501b0002c078034080c85410200c00c2c003520103004035400e100028020080c140a203404010040784402d4200e55011040070400364007070b200c504114540e044c1040c0004040b81c0c490320356818240003908001c4c0e6010b2960241406030010000a0b052908015580540c1d0f807000400811100c060b11002c01d41d4024940241000007005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 23358944 1250 23357694 23357701
    0x90b0c0c011803020d0f1106090c010f030c08040f060e060702010605030106051f030e0a080f040e0112020915010c06020d050405190302121c02070309051309020102030d020315030a0b 80
    0x300d0944640402200a1101090407100070079008181507040d4101440e190305200711840c03013a15400b030ba6004610503842a20100241c1010010340c566111f642600d5440f0f04d08820b9208070306a030032160340c0d5800980081c02041c001511840b42c034880c41e2040c980854980300580d02c00349040012102c800041c0e468010400c1281020701c1084044c110640d6504c9020820388030a158600305409081c0c00c00d42d0394141d49440060a100d41d41c01d8942c01410584d5800f14451800d03603581040c01880303032800072000000b86144508403403080040e800350910000f079444e00794007054075900240c001e06220180300004001215032004101e440403500c4001000d08040c2406450000c010000040d00100c2042d5540841e030009111030761404058403460380e03082c1c5190120000210100321000040c00404d205040540003850102900c000b500c904086140c0000c080050b80c0840e031001e40540c01c200582880c55140c0d40046600c90580c0311325421280c0800c012030f280c60301d400002e54a9007606c4050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23360194 1250 23358944 23358967
    0x120f12090d08070f14010b01080c07030207050307030c030309050103050402030d0309080405041d0d020c01020616050d060306020901120b0a090f0204050a030f0611070b010e040f0b070903020f04020307050708070501090b0c 97
    0x250300e00c1000d45c0000c0082e69450b000207080700c40050204202d500e00801c1c0f840c00c00d4820000075010300405001e59130142e41d2880d00c240904554081103000c219038100110342941300b48a0075109a4004005040481341d6440a400501003800240c0b13501504020110b0291113602455850403021440303000829919240c980c1400321000c034590454003d015484540e0780d00040d401d030008440840310070032109019007501c117446000070007101d590030020000207100302940030b0041e0040030b80380e0708491000042d921084034900a403043d44288002c0303090206012a502c020121035000360018500381e01c6000040400541d54011680c0c00e0700500180c1c00c00100c1c5c0513a20031012408852418102c840d038407074821080500503402d81505520010742445020b0440a51058128136404030038202030b2401400c0c0d490500059020f54108408039100c5d05152080b2403140905a85503030800d14280c4d034075581540085c84c16244c540d240c1840001107101c0c080d256010303c0d040e05060ba5104240e008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23361444 1250 23360194 23360213
    0x190e1009060509010302010e15040e040803091e10020904090611030610050309120903160f0f0608010f050904050708030f03060a090506030a02040b060705070f05120f12090d08070f 79
    0x200c203020f94910001000140d8100c250807510801c1103e07184241c06011600c004a070103298450050180100140000e11101400031070041010105407007200b030604109001e6001564510720340c5510102141e190341409501400301d4420090000c55155543e849000a41d012802100e484100000a01c0681d151400300e43c6100007090030b0540c02e51410100712500d071241c1414401d0102c1c4005502000ca07901031100607202c45a01074003000e965290013000104405900402d90702c1d1800700001300d0018000d5001c03074100c804a82e01d0241c101c1c14201400703210700380503000301c0d500c0c4100c00c0041000c2034144060200710800350000f640b00c0c5491410001c2d4054298000c20450b8a041c0500280b40c0f030100d0300c140c07a80d40603500858516000c030302003081c0344260b01001d00301d8001c1c00d2020034842c0001300e900007116030490f0007660b03842c01503e07081d0711015501c403280740340d91113106205890f682000140421880040459140250545800d4880d03405058101d5080340d207019a40c00f00540050f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23362694 1250 23361444 23361449
    0xc071121100606081621020f1201090e010920060c100506010206070e060a0c03051b010902040b010807080f0402010507080a0e03010e16031b030602070b090607030b090402190e100906 80
    0x2c803040c08503c0340ba05c0c040e0a5071400c14058070b13410100144205642d5042d0104c40f400404050070b0742c0d41e440c008500f60310301d6200b0b0181c20754103402d2030301c20300d0703890014062940c1c2c00e038001c50341c44c20480107040300b081078140040803160090700c14001c01180c0791080c06a9100c1c000c0001d40424185032140009042c00001081030040c0020078035409550b49030202038a000c000c003824a18907481050034103455078007406007d110030072134811035001d03514070641154004038406c0e2002e00001801c1e00064035501000c54180c80002c250400140118a081c0f410b1a009030040c1407a03450462691610130482d802400c1c06c5002c2a0b508003d40200d040900c2500c044840082c00b03041e00382d42c40300c2d10966210541c440a01803e0540028450100002168500a65006108554508140c60714a2034494101c40b1401580541e500050440e0b029000b403096207480200460000c0d600e950800c0342211094849030b168000d41e00000c80d219048000b0035000300c40d1b00d4603000840345010811016a00240c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23363944 1250 23362694 23362711
    0x60f060705013206100503040803070e060a020a0203070905090c1314040605010e1f090b1318020a1d040605130204050c04171204050d02030a08040b0706050c07112110060608 76
    0xc90017400720719400000d03250003e50050b41c2c19074a840301041180e0050079480700541c010000110070451740e030005052000b95100341c1c01e45000964680390041180d008540928403908240d840b0300040c500201b102c031650b4400000010b030032180c070410b1000000d04590803203010f0b170307100014480c004c40c05580d10382c80030280b21044902500710310124a41611482480d5190343c42d0000d01009507a202c9024102e55280d550801201100360306002d491040c3e0b100584c05074283c80000b246d10710540f42500c42c2e2540200a042d02c50305c23036640348001840c00400c84000c0c52890f0021200503a00c038043d09004501640e2040c0d02c3e01d0070b150f26541e035840d641d00f186110fa401281003030210b4611500380c50840314112013000d011008be00119003000c4071205c00410502001402040e400c3d1544d01400856009610800059035900841d0842d80700e0443c0c080d10103001080404014039041d414000052010302038200100700c070400c0c403032406110b254881c25403501d0718028880682d00c031480c1540011803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23365194 1250 23363944 23363959
    0xf05030304110f0a03060c140708031512030901080a020409020a0c030201050c04141002070b0c030307030b010302040501020c040e16320607171605010905060906060f060705013206 79
    0x6000001d116030340035100003000141ca900c7d8401c002c0b07005825078070104084c50041c2d59160702a1500c005290b00840710700600e682c180b10b140c05a400c110904100302494980290701d88903a9074010b55910400070300001c1c510341c0811012440300114000340034030010302e8940200c8107286280103825207130001c00b10506124140710400000341e801c0031040c00c00c3c6080d5104511b048004000b0ac0c1004c00300e401c520000702000031142500d1340c00000031807040880e0f40d810441d5100305001102684110700c40c60380142e0100c0301d0301c01d480c0b5103980400520b884032011140c021803484028940300159501820001070036680545900e03103801c0c0c4004941e040c00320100b200c42d80c0c501c000750300b41c020704401515030040f20041c0380c5191107500c22141404807851240313994280300c0c40d10354040c00303440c4403c070b03000d008202c0822580d1200040c2e00d8050940200074801d114440028080b01e46c000010685040d0f480301c180c114880c0300d410340c5988080310042c200f240443c002102c01c3d620a0041e0115005802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23366444 1250 23365194 23365219
    0x61803040306050408090306090a030f020d05090105090307150507020103061e06050c0304030c0b04030203150601050415051c06080d0f05030403030b01020c0a09020d1503020d021c0f0503030411 85
    0x100845007541d42c450800070380c0340c80d02d007000e101e14001c3c121890741600c900700c144801c603000060a00d0f4418442d50344c4060a00c083c4100f26200c80d484500c0e180810307028020030146e0760261001d0145100007804032290a0307540e41c940d60300a6030070622840031500010b030300415541c1c0b60040710060702c1241070503050103091001100c0991568440c603000c100010505801c805003d00c21a030085400c0303480310075540c0c2c84031b1104050b503010f4407040303119110341120025901d2030011800e20450058503194181494840080c400c07801e80150842040301c1008120070003584c4021107122401100b100050150400c11a5440c0c105c0c00e0803030380240a400da85800500e68000110703580651300d0b00d0045500d1007000010b03442d000c50810a00c0c5e00c801c800c0004100441d499002d41044080000e00780500c0a8006250030f80e0501800060340041040f00003c0150038241d80c800402c503c00da0304d000c40854541c0fa030350030449100008440c5a08004140b10a1100c0701124524001003180d50b4030440f507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23367694 1250 23366444 23366491
    0xc10020405090106080c0c0111040501032a050a0203040e1302040c140d0b0f060a0e030c01030b010c0212070806010609030203060606040e0a0e100905030301030611040f0e09160305030c06 82
    0x103405120700010000b05000040b1b00e00542026151900c8441009008500c00d2400c00040c6d600720b8010580041d15088801c44088091950050401c415203500f1081600501d001c565a500105600080d80300800c400504070700e40c40c4805208100c3d00c9031100c1c251241c0d1040100f42e8603c51200010070030004c0c00030b840300c5c61402c112007107002040340000e01c1200040100d80c4048040030001d40c01540450050440340c0c01068200380100e0450aa4034004840c500550850b290440d4070350000303180c9001c500040c10602105a2081001022104c145545c0e0420320324110003600841c00103160140108118141000340b540c0049048480d1400c19080842d61130011070020004d03c1d0203038454140302680340c000c0c004248070550740c071014800b980140c05c1c9250b0f80da0007880100c800c0c0b464100080c1c5418810310903174094075040072420442c140b0f014002c9038040e8003d0080ca0843c02140c00588686040a4403035004601c54405540c6510502403da42072802c014400841904556403850815 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23368944 1250 23367694 23367709
    0x70203030c03040510050708070e0301020f0d0510080703080a02070f060807030903030b03070b13080102070f0803180604060606030e01090c050103110d0609090c0b0f0405010c1110050c10020405 85
    0x6021104103a481e40c0d90350a24624082c82e01c0610500c05141005101805900910f024850803442d1a0b180078214071102f410701301e104881c00001d10f0340c4140040075091586400407608840150b0940c4020754586100c035040c505941d004448072100000c45011446e0184000c0000b400700b03c0d81c040034980741c11000b401703c0100800e03c200301541e0340e4440003010700a5000144072400501100c0500c2d46a401e40740d0726520a9841001c000c50041c40000c0001050003150101c07a84050758568041865a403030784c5035000602002180403681c8410105040308210f42481907016240c08500325180c020007808680f0091000107240e410030000901048008001008540b0280ba001840720600d0396a55020b019034541100c2003410a00c0024440c08140c00c07900415000714901e00180c0e5580d0b5407190340e403003980800540090140020401580140342c00030b100c034080c2850307074400740c030700c800050445000b019484086031000c01c10340f845410820008046050360751046142c2410b010000c0c140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23370194 1250 23368944 23368951
    0x80f010506100804032102040801060803030103050a0201080c0712080a0b010e01020a0212010b0a030f120203070b040605060d0501020a030510120503030a0506041d0f1204050f1002010e0a060b03100507020303 91
    0x43c0841c1d440400e003007500c221000e4101090000c800407400060320800c20281d4440e21442c4015030900f00040fa1144000c001c580c103d03584140144040c1c81036500644110030010300b08001d4440a1212001188401c0c0003071500b10b1050b51003440701d05d40240508c044038000000c050400800c90b240141c1642c00007903c4c80f101703404444005003802441703049405460420203007a00810000000001c00840440c0e02c0400d41c03154040c02008002608102d980e80070b00907003d00700000a0740407034080b0340e840d03001c1a0007100c0541420350074000c5881c2c840c2a603110450450010365507030100540e00603a411010064142d0f07044008601109845080e92404041c2400410315624030215499503510f500541300000389810488a0640b008540ca45440d1007040d02c1c070340703401803117810042d01d8140d0084500740c8500404501c10340011100f480403c0440521130010740d941c0c0d032001c43c90580d0421203010700381d100d14004180201d1950030b2500f040d07001c00600b060503050800b404000364011040d41d60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23371444 1250 23370194 23370197
    0x6010306060b041d040809030109031206060e0d0809010201060306051e06040507020d03020c01090b01030c090e120d051e010b04030309081c0c05031c02090f030715030902060903070e01080f01050610 87
    0xc0584440c00c1010061141f1860b141d459842c0200801c209a00100160750b03109100e001000b45560302c1c0070903103d10a807402c00c242d1040f03040c10300f1400689400003500c03d610061000040580c1c8a0f515441128411b5907030095000501318018107005208207043d03804401900c05100c2401c0036070020356103403045205041031640110b500351030300d07c003588040710b100e0700001c11012a5070349007095403101425004007150a81000c0340707032200071000602003000c013461104040c40c00c1d04030a1514010030740900b4440307032008144005480550820020ba010340508181c00d40d90b945140390103030201e940c0383e008156a030881c1183c0c00711007240400d0001c6803a114106440c0c1400c0380e1030030504501c070700c0300b045550104013000d151310984e00e0740c0079107030700c3e14150f51a8030b020b803e0104250b0340c1c0c10f40b0300c01d035650442550074004006110360401c06240c0e10142415081540d9a00000d041c221907406c640c491084140c010044042d040046004410041c1c00800c1241003a101050311500031640000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23372694 1250 23371444 23371499
    0x201090b15042f16020301020403060b121603020907030b030a11030c09011d0402010504030803090703020a050303031605180d0b09061b030606090d05060906010501140a0518010201150806010306060b04 88
    0x4c060019424406144e198000c0003150703120707103a01d042401010742d1054240580114102c0703080c1880001740320710706013100140481c42140f6541c06c000220500074610710800d40c590b40c00110301d031000c0010040c218850981d150a840c0305001381850410b402d04803d2140b2800c00040040b03505d40c19030001d00d0144000c5e14180d035902c0340010b94580c400d5900c001c0040304000704003c000031002c6092400e0764402c82e00c001d01c0344c1d5a90704040e43c034001a10510082085240340355855400356004081d1711a005800f042209103000009401d40c0c43c0200981da640860402c1221920082c41050b9001440b1005514604600381c46003805000040c503060049200050302101c5031341d1f2401150303906030b2000859403030746080780a107034442d1420b1094601081e601e50700d0a000c1d0310342000382c4081140d03540d40d050500c030b0841c6c865082048050016419951303940681800c203449030090502400b03080c0001c1c0b400754514030348001103c07581d40c030041800105200500c004814010845501044401c040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23373944 1250 23372694 23372707
    0xe01050d020d1203020301050924010f0207050315040506090105070906030504231506060a05070b041104020f0a020f01060f06030203060109091508060a0903090b0a0201090b15042f 79
    0x5501d80c6900c01003c0c02000400465592a65041d0000c6040e6201aa220070840e02c807001404c03152840680007036001414192000d640b5407103107000d1884601c042c4103c40040303640c1d0011034240006000900807912105c0200030500004104007600020300c3c10082103140f8000300c00400100890103110101501e413008035003070242803192420f824440d00040814462040796950359036040c400028440b000c43c800141c081e01d0030006440c0701740c0301903c80620b040415035034081d8002d4001d108071500c1031a490021555250343c40a02512071800c8a001c4d030721025100040d140400c107910a4511b607060500034002c010501240c24201c0740b05040241e1252607203401038a4221054000e105540d00d8090040c498018000d41c81c0c0c05c964884050b14403940340c0c070380d00344280d410b01c0c03901030049075080030100250103544c002000100a2440009144a125603515001c41401da40074228031007407119038100341c6054400c0c0c01108107106484210320000c04c116617004440c1e402c1880c84820301103541f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23375194 1250 23373944 23373949
    0x611010f020d1b030605010504050d05012c16030c061209120e010e1504030308040503070f0506070e030102130501030c030b090a06090e07140603070302040509040308010801050903040e01050d02 85
    0x40240a80d1002055486200d00003000c4000e0400c8021000c51031104480d00b05038034064442c400c207650060317403010310b024146420b100c0341003500b4100300c60b190b41c0e031050020592800051000c102c4910b00b070980030882140a41c1d8505800307050442020801d605003000001c01e0042a030040f1a0036060107503c0130303101c0c020b582c02403a4880018040000d084910100203902c010700c81c6003002c01f621900304c62200b03101400380b48010020f603034161a03410007050002c20300441c5481c2c0d00610500860b4507200e200d594021405550502c11203142c1d01c190f00b8022802d8000324107482c0024142c008500b00760345040c80300240199803042c14140340e500c0030280c00d0b00d4803d420035000040098004c0c82e880c00c0c04d0024000400e814801c51030040e1401e00100d80846010403194212480e040a60049044080c1001034560028080c1030506600700800102912098a0184107074029120000a903140a50007400d580004000d0399554004200a0040d04500d054990542d1005c8d00d403080c103016513202 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23376444 1250 23375194 23375201
    0x7120201030b0d0f060e06070f021005100f0e100e040305090d020307090608100e0a1505070909050403021e060915100305070b1903091707020301090c080c04051609061101 75
    0xd01504804121301010b0610010380c1054503084051811141e580e0f4941204071880503050385a038005801000320100c41401c0e07074020a8200314550f80c6581c450390340b84030256901013164805452004038804000035100c18050040090120f140d40c00350303030704e0a0b03507008000340b107052002446114100b0700c01c81591800c01c1103c02600042e50204441600c4408059031043c0c02105d0603109030621305040c500c03010114460b414568000002c0002c06108940d803405404014050020015180400070b0000740c6030244500550280d0007400c0000450040c40102e08131422804050764031007401d00000780c400180101000400c032007503820304d482d60f000c2d00d51340f080107610241407403203040310101e440054140200a0f1039128030f480c41402005c440103a003030b162244406402400c5441c80101c0001034080100101c52004000048a40807035075002c24042e41c6400012407984140002c6946082a12455821a0703e550381144002108640280403242c1d90050001300859243c0d1510308102c01d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23377694 1250 23376444 23376469
    0x4150e0402160506060303190f0c020301020412031704020604091a0a081f0e030f03130b0c03011d010503060402040902060d050405030a0807030c0c1212090c05030c0307120201030b 79
    0x3402955a1640d940c00109803600c151410384290269070f001c110140380010444450a80c422040148035101c0601596000103074403544040c4500043e5000c0140d50a10080000d44080da0b0201c10b811101e040060205403003c0e058044000c0034014000540d41d40c04c240d0741101c0500e18041015802425400126030281544d150001d0742d8120108407583e0200360400d456100300f442000081d5140c0d001c80943d00c7c0b8001341c0c03581d80c00c1084001c00401003030000310f40c88107004010000d030780307500e80e14060408000c55181d1001c00000c4010702c09005821400409201031000107907855041500080d25120050070003442240e8a0550004645888094810103000c07854200682e142505005d5220b61280c0056000915128005640140248a80c180180090791685812020341e91030700d5403803007140c2c101c4003804024014a005d0399105d000b40320707140c0c1c400c1035000d82c10b52031301c014580741c500c0d42c004c901d100c1d41140c10140000c0d0740680c0c000105036024a80420541d00f0031300400d240b421356a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23378944 1250 23377694 23377699
    0x307080301080a060e060f01030303180803070306152d0c050a030306050405070c0f030e041b020106050f0108070c0b0408090607030e0108090105101211030105071d040506010504150e 80
    0x1100014403450082a044a410701641302071200c1c00c2401c4040703440c0c0b941200c9000080d4100801440880e21a50054006005d070f600709489007410340d03c400c50190000c07030704000000c0c1c1754042403124100302501d40c12500c0d81410032030751011806001e03841601a03031440d0103405600b03d1441400c1841581440c89003a000000c0c1c8001c94101c2c00d000340640380d60b0090a004d1401c10000c10042449405010726040e00200d81c2c0640703c40031394088a0412807075a425a0003520b90702c10055840701e0020f130103206080e0b5000019414940f01c240109113080240450500c0585402c003c0040d030062800c0002c55803148600c401c6036294074060103140640c02d000c039044080440c2540c00c243d007061a002000c00240c807030000e1517031884013140c01c0c0c0c1d41c2240d2600801c1e8684004028032000c410320304c00410b03c542075869503071800074040b81c00c46030100c0300f5400040030305100b001c9050240f6000a000300c816203050256107003000010b09a44100e1107103842d60000e54a6104000c0c0c0300b04a0722400c80c200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23380194 1250 23378944 23378947
    0x102030f0f160506040c1d0105061e030907030b25051308010c05030f150f191d1008120316050d090b0603070803030105090f04030c0b0106050301030b0108210c030708 73
    0x30306007507680300d04c1101c04490324803800d00042045410002d60322004101510030140c2c03a0b013443d09002e0300e0340061409401c41d000840d12200000c52a201443c46003000c1c000030039034070386141408800789c3c401400080400c0d903c840390716480c100642030304112510a0604039035550410076800e010b01c40035030119816519100c0c4098150f03034020019030044074281c03100002a1150114030340007049507001c850380808803010785851410290f01c4041420340120654003865503070301c86841d284546011410012020304100220b806d8000141c9010f000c1c000020100a00c00e029000e0452001801d24904d4000104003074503168441c104a803442040c9000c14008294540f0789036101d5002642c02510a009282001c20031201c00030640f81210f1000388021181e0b00c89002144000c0300207071080d02040001c0f000031020400b8840d0450090113640e0350300b41e89600d0f5050070a070549060b000b603602c0c0c0e003021141c1c0070001840c040a580181d2106a1603556280550440b03245215509005020600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23381301 1107 23380194 23380237
    0x5070203090d120e0405010807091b0e1c140706020715081504020705030708130e0426040909060f0506030601060903060203060402091e1203090102030f0f 68
    0x10f19060503020510800080340a56000760081c000c59400342c0f10402480300c81c1e116a00c003200c9055a941e0300080f00035001021891000e800c284031310340390500c00d07503045032002d0023078901d80d4011025003242441441c01c0b81c40da811f91268101501540e0f44c0081e0481400f02011360724411365503110700300c0d82c49410315080701d500043ea089d0010b500b8003001c000180c0400c018110107005400050303c485412410003079940007074000d100054101410301002a1002c0d085901242c544d0083d82c80c41ea045120042c0c050141e640200100c600b020245410700c0302a90182010004002c0b0500c803680d241000c2c5952850288500f0b00010038070b80c810400300d00c3c10f601850f000f0320001e102502d4020700c1000280308003210411548404000e1303c0000c0a446d05410039204101010091030900c2501000030351039016044410311981800200c01001c0090300d400c444c805044040560f40e61072 = true := by decide +kernel

theorem cover : BRFrame.Cov 23201444 23381301 := by
  have h0 := BRFrame.cov_init 23201444
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23201444 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23201444 ≤ n) (h2 : n < 23381301) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
