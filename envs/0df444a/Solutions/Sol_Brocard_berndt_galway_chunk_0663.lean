-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0663
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:00:13.327159+00:00
-- url     : https://prove2.me/submissions/fcedd09a-8477-4db1-af56-f4b02a9f7acf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119064748 ≤ n < 119244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119065998 1250 119064748 119064761
    0x204110712050301151b050303100513022b060302030a080a0816050d0e03090604180b0f010c030305060d15050f060109050d020409060e06010f080c010f0918060312020f01 75
    0x40402c0030800044c060514240302e105204901490440c002028410302039455010350344014056200110400c80040341c0b003480c400996405a84080038400c0c581200020781c0200410030310100911403001e40340040701c403104140c0c182da541d40130485ca80e503070b00401d040407139580c0240e601e1000019680f00c020780200103a9045222450346151030585400e0003891070280b00c00c10020b0325120407401e01034520030410349140d054014001561180c5d40c030b1100090841c500340741c104080c00d2411001051030000b007540140f05041c0c440c40200d80c0b00303030740840040c20000c0c91f041e8006006803d103804a01c444510a00e01c88040700001980e0400030138410f200000200407504012585006000f03a807525000c501031240c0c103441c003181c050780620300100034003203e5254161070702c91400009418103103011048201d455682c150f030841da986100449000701c40903d0000441c01041003040401000b030345000c561403601c98000f036410f84070b40e25a8030030022028103800582c883c1ca10000d03482020702c62071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119067248 1250 119065998 119066033
    0x4030c0b06150307030905071701140c071a0a0e10020301170703081b01060810020405090a060b03010509062215060305090d0e1801030506041502030f012102041107 72
    0x101115596001442c20030b01c0014074070010103440301350b10380030083d040085901500011381101d01c0e01c002c0002c02c50003045000a4110000300200108400c0b4101c1e0007110307900b0341c003d1000c2c43e00c640d00d240204480980540b0581001d07a550125a0300d044050045105d08ca5080b400540d0305e502d8690020410740d217442c3c40c404030740c0000c401040000c03200c1040310954000c00285580325820a608180106465804070019010300460400a402e6a500400039218100c540c0320b0035807030312032111088620340c3c0592070206170100f0040c441da1a061001550180009090640c407148440c0b56805403645503500180c5a515503c40c07100c682150303403c03040030b0300080c0350401c024a840084035644e80d80421100080c08100f610b00c901589400056440c0b9584100d034164555039a407400700e41c1c1b42c0302140d0035600f0959140b100041c0e08003070700031a405003400080012082e400d100c00c0100d94040c006100d1030184007883c3c2c0c0c0c001604c0703e01941e90710b08100710722661505610705000714401c1c031241c1e51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119068498 1250 119067248 119067259
    0x9060f152c0a05030616090b031b130b070c03050607050a09050d1e0302030405010815012f0a0c03052b05030405010603060e0c0a060219020607021804030c0b06 70
    0x700d1003007030040c840c541d5010784544154600741c90090041641c1841caa005581c0500920042100d650101151070185200c183e46800115a440102600c1c034042500c0000c2c600740c14078860b0344220308100c042d21100d880341c80c4800e0415500c0010083c03942c0440000c035000301030384030f04105012041c001c141e40001c40e810214a40101d0340030040082d116030142e14460710051040c0c40c2400700e8210055a040c95115024810040c5400c0c06581d03038219101d410700143c01e4400140480d4941114000301103c10703140c540c4803a488806481220000d09410340155040190300d444044c020080186264050006035100b5801c500340075042141410308070184c0e090070f811502600c02c40005440c0700300d02d00e1401640740d458600d8818090489544054059410000109032900e404100701410f80340031628800040c0e0f89400503a03c401c10300c0c02e12000c4203101d042c40809400d041000b41103692004280d101000700380601c6582c0d020007a42c0640020b07000c0b00e01c18080010290303400703130884011101d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119069748 1250 119068498 119068517
    0xa1101090513050406020d0213030512040b030a05090c1513050609061b010b27070c0b0604020a0201061a03100806010506070f030c1a0603120301050f041509060f15 72
    0x1107260320300020700040301590f03140001824401140d0580f200228000401e56031030040d4581c43d010b0001c83d020940307250003500441001280d95008407801c0390080d00070036046654100340b0000031702d00245a1405800b50401000269868241440d45000d00c0d0b0040b68032201c50181503070b003110143d00b143c2d00031041000035580300c2c0d86003000d0b564440f050703064000b0806280e0911901400c1ca504416030482c4d00700c1d80d10305d1450100c0c1c1c1d4504070058184811a0160755001003160a003032032510180c950703200200420b82904294008140c000711500011540d566201e0b03c10070b2281d20140741c49070200c004018000c0048040c1d0001c001400c070800240142d50405d400140c2d07512549200610000b00c50780079a0405001d038082180464021107880046034a1a016800009048402911900942828464001020382502d043c1c0b00b0150010004111440500c0f0050500003184500d06010b0040012000c845000381000740c034941d030b898010185024241907102c540c4c0e40d1400c0a204540c84d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119070998 1250 119069748 119069759
    0x2a0501021603060902180c0d0b030c01090501030e0309090a020c0105090a08030c031312031407390b090a020f01140a08041103011109031005040c031407050a0303020a110109 76
    0x5201c02500d80107540011000f1503403000610038148085001c600c2a81030041041c1080c402c0301402040c0750484040c040c8050107000c0607104d001e440350076408101c490b9000c2c003140d4400d601405c109402103080340e01d4007040f0000207210100886002821030380000d07002821003028040c56400c000c41c03000400d030700c0800c3e40d628145804010a080302143c000700020303183e0105003240c00c0343c482d001448070703002b2502104014080c05040c1c82050190b072034000400c26151113000100d4800040c00d022180400c2d01820311040048101640191505034004a502007504c40325568080c00d81c410042c84103122520612044030b09640786241031040c0b0180c540d02da810040300b2180030030903919180c43c040d40c3c0c2e490081582d900303140d40b054043d841d00c0b6820130301400b90801002c814a0407011260300d513080707040d0041a110121303001000382450036400c10019040c603040004106c800f4050710013541d01c1d0400305841c400700303900c198016444000c000c814802010b0503590004000e00e01101407a0919 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119072248 1250 119070998 119071033
    0x5040e0f030406050d060b16050114130303050a15060f0801060824010c05010204140405010f030c06050a1b0f03110d08070c020102030f0301030305040f0b1e162a050102 74
    0x388107503c2440302c00a410704583c0c03070a0784400f000d03014000c210f680703900032100c10b5030303000e460031604807500d6281080111040129040d524031984001107805400240c5507011000303400c02801c503420341a21401800d40c03d00d0303d440e08501800d410b584260900350b03208001003440760103a012200303014442c1c0510125000c00d80402d8666040580100304508240c00100d0b1080058000a092944003050224500000120305100d04800302d5081c480e40e41c9404a803840111103210040c440c2c00014010008540500080e0508030040d04141001d240c1101807146844400b401c100d50b010b04181c6200201a0445074041020007140003c004e0300844034005021440041c1040c02031109007101c003421a8420000c071046403813210031094581d6502d1034050515001401841c0d003a807010b11b00442e44040d91000e1347c0c0310701c0f01140c42c580346074001c1c11100c00562110120b520000c450800e80740100d148140100620300d031082c02a000705410849400d00209250011030454100c0b00f065020b18805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119073498 1250 119072248 119072257
    0x60507020a0e13060515030c010203040807140a17032104020102070524040e0106230706050c04170c0103051501020c100e3a15050402030309060c0705040e0f03 70
    0x703401c0b1034250b4548100c2c68042240042004124604001c01c00003800603c0b0361050ba551029400c07078049140c080c0059890b4080e5008200e00c3d0703484a0420000c04010410f44981d0038805404108071a07154010300070b41c1d0040071074602c4603510004401c0c1c000402044848080c1c0d004c0d0010101c82d06103540000e4075a0182e00c02c051007080c4000320600e5003030701d0a8048001d000030f4514130741c2d04c2d1741c0c446011094010911075480031030405502c1ca202c0f006060702c001c00b0801c8890100740303802c0c00360751010000c140c00741c019140d0040902c000310348802d0000c2c40c003180c8650036005081666400000400780c40000340801d000c02d420780e01c0c1c1025640c0001e203440500c4800c4403d20022400d60204884a0400300e404650002e400d1644511200119002901c0047c690540c0e140e50b0485020170704910015050090800020101000101900e9441503030001d10090589103001c4100b40003c8071a001200c0c4000c0070b801c000c104009034a8140720f0402c003100c03020094001e00e011500040d07140d009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119074748 1250 119073498 119073509
    0x8030601080901020c0a05010603020310050108060f09102d0b01050901111c0f1e050403020f0d0c06090f0503070503121308030a0909050718061b0b16020601060507020a 74
    0x61180120340b80c04020b40541c1d2041c05214112404034119080a5003c1c00b2984000da01038003d00480c42285000d07030050030b0603a40098000c3c4180d80390303085040c25a1000814003030190152140386070040d0500e00805c42100b09005080c00360403004034010803040303108000d41d100c1134580b072003d2101d40d030411f041d100da0b08000d0802c20207105110b024181004513101d8800c00d80d04500440091b441c0e002110841070071116501c81001041c3e11090000d096499900c0781c01040041c0004c0005140408981d8400c12010381705d214500100e036076626401120381c01030781c0415141407061080b00402190f450040500b10028240c2d949410042512440f078072125150084c4006020820460000105070041c41d550007100d50350a01902c00070633605581c0140d43d2583e040c034011811040c803444103080110071889502c008a0301e401401c0d901344150003030048004c0024000b0001007004000c10500c0b07103034400341824a105540c1740090408105030001428018103100301d801588665444a09444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119075998 1250 119074748 119074757
    0xe031009060207020603070809121314030a060e03092701060c02030a150510090b010905120705060304060603031403070c020402030a0608060414011b0c2a1401080a050408030601 78
    0x80e1103050420280c80b901034040c0d0801400424081250b83c03148080b4407500e1650168ac002e03094054264466210355001c1c02d4061640034401d0015120f100301c0301c2454000101101d03203c0000d6915601a02d07401e80110025800108441019081514440c0c400a4a000c0100c410700c000c0a141c0000c900180a4141040440c184400071910304118601d0301c01c1e048000e40340c02c022501c40c0c150150100b16003c144201443c21b0000c3d51000a025080401005844a040341c0c0d00340070078030400101c4680250903910442400042540318040114022030003100301056850540c100900691811602489115130230010010001e90000401890940c100c60240c1e494440c4198032002d48a1f03a001801140074042c10700040000c4280b4003004002210001d118000e03c61031825181044050030b0380210f20042803900c0024002ca5241c52008012124909400b00d00700c2c2002074020b9507048032503080514401d28900390380094045501020080b0705100d42d04d0070f40c0d10701c01140001f502e50750500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119077248 1250 119075998 119076011
    0x513091808070503031b04060f0809010f18020907050a02031905090411130f1409040f0c060503011805040812060a0302040219030b090c09120309130501080d0e0310 72
    0x8044540c0003041064000ca0340644500341400c1068403a881507a10010f0641c580d44040021011507098408a81c881c1c0c442000956071294140c40ea907500829000844d541c45a070b0383c20400040c803446030b001c2d43c030f82440032030366100d032060003001c801c0a081c0d00305010b41846130000d0300e6400011100d420040ca0490b10700c45c0302c10307201a1394900034100e40d96400350801448007004031102026080c0b0031040d501c1c205509a4807000d01c08984014000c07908000940241c0c100d081c10310341c0d07079550420310481110300e0f011429250400380340c5e0580c100c1e00c00100d00100420110300004d618807101e000704ca02c20081414030750b85001640c0b2a20381e41c90906d0180e0400100d15036900320b00c4100a58001e84255a5880035001c43c0785460303415510140480c0c070b4049961036604024031058468400345003e94903280e40b420421070212007094081e40c003807104004c84c841c41d49641c00b500c6114606118007007603c3d410422064100a440d0031594104405c4418402c0d2503070f40003583c40c1010010b9500017584 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119078498 1250 119077248 119077271
    0x30c0d061506112a060906040302040c0305090d03060e070807050910020102092404090e0a06090b0f060111100c03020705070b0c0c0a0e0103080306061903150501051309 74
    0x2811454a5060100d503890000041694204a404403a2031030f1600340d4004a41e04661114507800c40349510000c40c0e02c008100301a82004001000102c0d00244041d0800366250300003000c0c0c0f290061072030002502e803c00d201c4945010050040d1a1645080500c6a030f03060040203801091300800c01d0007089400d030003055419000d20220741d644003001d00300c0350b030b00c042c2254041d01039404204400d0258050800c01000e140348410f21040041045a52611f014904807082003c0c00f185944411640542206440011060b00c20a90701600c100460011840c02803000030501d9801007081303040c07150541e0b0070003000c0008118415206d224480006603400f60305022402402072600003040c03032041000108440c1101c50240070551011012074184407000c4c424445e46501a1054082a0003c44014400600c48002a643c0300502409003810405ca1000d40070b0001807080d80e04011a903112007083c00460801504405004203090040c60650401d4001c4110021885411038850755070325810403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119079748 1250 119078498 119078501
    0x21c030e1603030206011401020303130218070309060501060804020607020405070225180b0102070b0702151c0b0f030a0b1906030b07080105010207030809010c03170c04170606030c0d06 81
    0x542000c000807100d420045140c04162841e242c00260058400e0f5400011080c19402c5a81d00c0200103074003550854075010032096030b440090b20101da02801007400140c0385041956454418000c0340c0c0c0100b002c0d0b9250034003808032a0181c10800c10400031104010240e2100300403501410f506460008495882d000102c3c14489401c80c0182000c031165a001e1003684200011000d0fa621003004030390b10f0485000a100f01c400710500640582c20a4a041250f030344c00304041d1864a0002d44070030380e03d4032022142c3d901d03648550030340010013080e0042c80c1508840b6200d59070040d80280e82a2084d1086500041d5580040c503400400300240c4070001052031016121101c0b40e02c00f4100301748103841c4c413850541c0f00030038102d49400000306020000200c6602c0091458100c1e07170402021443d1001a00c011030700b40030310400540c18410400405c1d2600d8101c00c1d40710f441a952008030070386580c1001c18144e031040f0100307003246880d449102401440e940108142131180310407070b40449403414070301d0400d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119080998 1250 119079748 119079761
    0x507080f06190803070b0a150509040309080102210709030c0b07020102190b090f0321070e0d0b22080a26040f0c08030703120c051e09040e0a03021c03 66
    0x41c1c00b0104070001680c1d00380080a062458844c80c0803144642d251a000c1040303806075030f1020303180d5420580030131460810016240d0400e009207010030246450b01d10050030381e0300c018000441e00202c00c441d083d807105007540704c94008200f4035007245010300e180c580e040540a07501480c9581c91002402e2011a030080100c41c4100c841c58170140096602c60514030b11050303081762030612038000c07050700340f0401c000442210b104402003c511100c5a00c503032030061800b180100744100707020450704008030700e50320507e002282c030b4401d40c201c04252034211003200c14a500c2d0401d041040302078618030800254072070155040008207280210329102054011001160382a005c10b08155000c0184414090001c1141074000d01949014185c15902ca02140ea80e02c40c0c820050009046800f200e46040c9543e0010846616280781c00e506000781000d003003030078000b0007000100010780090307414094103250081070000703c00034025220400d581c1e10084d4036044003da01e892a0155140c654000c0340c000d90002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119082248 1250 119080998 119081029
    0x20c0f060d05010b040305190f03050d0b06033d0308131d062b12020c030f060a05071b110418031d0609010c0b060409060203090714040507080f06 64
    0x240700b030b5652019542e415601c24001924079000e22403807142e0120b45001d401c201980c0c01040a65406126103007101d164101000c03003c096620348500b02416510100554040c12818582102d4641c900d01c40142005028021079445003140b40781c1c1030002001200401102d0300000308607031b122802080401c0711072190b080111175594482104041c4081307025243c1c480e510689440c0808080d000e15034440c10300d030004000d5040c484154000c00540184c0008a44146900450b001051719400280c148101c01d201c04c0b0390380d44200200003210207a40038407070b0014070a040c034604580c490817960381445035145002d00541c00070b000c1000c9c03544441e400030008003a0000403d69011944c9001015640314090140315040d185103618801e203490300482c0c5080c04161105503c000c035580c0c0c0c00c0142c400040c88a0342c480c0c1e07110b00d80404141c00380025407082404001610f2014101203815909134802041b240c029880c0604100002d41c0012a042d00b00035901d040d11215980c2d400040c00750565144075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119083498 1250 119082248 119082251
    0xa1a03121c1e0b0a0b03041e0501050c072622080d090801050a0608031903090605040516090e100207081605070512010b0d02011107081213090c020c0f060d 68
    0x82030900007401c1480c0011101e1008240040030402c0f003006940d2146002e0701c0507440d402c2000c50f00242a048a500710941c2422003000c44580b40d45440b421601c08403002d40a42c1d5000482104201102a0000c42c0b04a14040c20008111803070341d261241c010701d844035240f422021a180021a00c907000c0c907004002c100300311101190350400c005c3c4095268842c4210646c244004a4181031a0340914825178501300c00840c05e04201641c44050502c001c4003190600d556801d212010030000d0090b1441640103030004c0c000503000780100b1041115990007507800302d1802d008001c000401080341525460311040c0581c40718030782e0501c100c2c20b01c50302081810302884448004200000403c443d000c980040b18103240fa00d82c9044500d0036984050142e96100e130045120400560140c0c08820b1002201c02c00c6841d4191111001d625000c0e120039403c5960310045400d069842d002c008402c050414a407043c403070304070307207403006550343c2c045001c000d2250f81d110304a00555115642901c03000b4078817010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119084748 1250 119083498 119083511
    0x4021c05030f0414030c0f04020904060e010f030203120a020303010e1b0a0305010611030c06060d031b0308060f120606150c07060507050f010207020a17010b12060a1a03121c 76
    0x61500c02e0703406480380c0e15142e050066044c90510b0041074503a458100948411080a00c0b44100002580080000b03540265200804594004141523035070280c0008504c000daa64110300405246c003950742102506020200580444150b002c02501c0c1103888018000c4403d4549006010f4005900300c84181c034407602080d040c03421136054000390304030b40c9541c640c9920030f0004800240c4922610a02d00b010740c4c000301c045109400c20b41c841d084854000c2c078000c0c20602c60480e1004502070000410b4000500d60350030300160386482030b4038240301314044400f003e404112030056500e400005000501c200c0260541c10758840302c40c0210b0b0a80403120f815180101d484001c003400540043c0700c166030038410080c02881d4004141300311502d190b00100305802c0c040c030344840c401060f0350030840c8142c5952039882840349901c5800402c0009480d440141400e4541020790401305e03800c0300f0310080049100c8a16400b1031f00e000c0b841002400c20203046540e41d140c4804a8011010503842c08814980b902c1c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119085998 1250 119084748 119084767
    0x9061e03040209070504060c0b100506040602060f0606041202010c051c03061730070204111b060709060f090e040b070210020c0303070507021906050c070603090b04021c0503 76
    0xc0d4440d40c4201c4007884203440e091000c4400340124058100400d10b590103aa02088200ca10942d000340c176100310228150b00c54011440d5900543e000c000581d12030310900039100a0604041e52000c0255034072800c0c00d18104001c1b420059440000e41408440701c0250300344082132049855880900b509946a403440c131900400404540c400c1e08140c40c3c85503c0ac0060100108201101120842c401c03003a0320140f160420307604074200c800a0f044001042a8070040c0c5941c0101401000080c0801d03403a01c42a08000c5044141d0283c0304940c1e412500c100101141c020000c84290381c86440c201000c4556590300740c6600304103400018405401170208400c200d580250a48a58100c1d42900c0500d03011007075080a84c0110380e281e401c0d503041030001a04507072203000a0503da9000920401e0501c0705550140891a0642c0003640003510004039608011002c00c8100002c218503d0200f0189145844808154002500080c03081e19200340154464545060203c42280c0000c1940d66410414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119087248 1250 119085998 119086057
    0x30225050c030705031b01260109020417030a0906120b030304180c02060405070e04210201060f0f0f09020702040902060c0d08060a0501050316020118030e0a080a030c080906 76
    0x104091192140d0f4a02103800d0030081061500c40c1da1007030079a49440325100041d1503400c080c09189201461480e1281050800860154006c00071003074010380c3d4504002c1e00042000851903540c2595004201608840d40d1000e500f03022203a0320701d000c030010080c10070518040c00c0a00300031585440b02040125501090000d000a00c240161080022800440d0241d032105070403600034010340c128520410210162560181d0700c90720400d80e030b03262512480030300305150b50900c5518005130340d03942060000480c1007601201400300c1c01e0160000500e080d412500f80c980b18000c040605401098072411034540c0e0b0030192032280d00803c81da495550116140e60756210304103e00c0005421040411120304011070904203440040e503416255580307003403032a1a500541840308085642e50110040d00081c00d00749205500d2003555040d1211005a08004101c02c5a0b000301034030341c04c078010400000b500070703901407040342d071100d0394540392501c4a002070364500400000c07400c28100702040c10740c6a06070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119088498 1250 119087248 119087263
    0xf18071a0c07050a030206030a0b062a1020180301020406021f05070804031d09010b0d0f020a0e130905150406050a0908090f040e07090905120304021003022505 70
    0x1c045410540d039450420078940d200384000707134100b0000c10102c4c024210325000880401c60150042d884d00c0c0700c984001c403030960f0308611010007440038500d21040107424091040035000096007030002100b040d100340442018407000039403e4100240c00510f060f01c0740d046580403140100210344031603450001a48a501c03e1251040802141d500f403d01c2405600c04c10b0300070485503983d00004e0f55a0b50f4184c50000a01081101700000c075003158a080e658200114080c08803c001d043e21000003070a01c4050352940e00604094030f00504c41c0034007031540a000e000d42c8a00454050f01c0d46140107400c2c10050414100c06400f07406070b850701c030801c2c5d6903e120742c0303001303034445c0d0020061a40d80c480b81e030049820303410303008060182c1003082e20043d10f0440389541209100070400100303070360105542031078500075070f00054240761a020310700e09105080c4610240b0154074401d0a15501d800e03070000f044420001d200b80c0901d03502140d6503042c50408184507810242d0060315140d408454240b0680e640700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119089748 1250 119088498 119088517
    0x80601030302060f07020109080f16050106181d1504080c010e0c010e01020d0c0201030b15030411030c0a0b0406050a051b0c04050108011404080304050a120e0f090f18071a 75
    0x984804608a00c2c4140305003a8400e82200c48213083c1f500145050440358000100b4400c586d03052f50844e004076000b0300c150390040c40d808499411701409a00d0040030b84410b011065001c007041c054480c2e0088011038403160301104c030680d040a0f86e40f01d1401003003d004400d101e509540c0303000c50100c20518002860219020240c07241c1c0c0b80080d040b0300480e502c40d96900e5607400100318020303180040d40a40c011400308440180000d04102440d050304503113400448007601c1550207100c03244a83c1c1002d200080200c6c0b0265200c05010342080d011030943e1203684600343c1000350002c0c2c5040413610881c140d515848014040a07122051071a61036600e29035003102a100c0c030700d050700008680005114035154010300c040003546507600da407100003040d0002081910039000311101100000c0960750509480f80207501c800c2c002110758818803807000c0003600701c81d02410765141800020700000d036880d58800c601c403044008a004041d2a10b017803148550014595111050b0005001c448070310240000c5070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119090998 1250 119089748 119089771
    0x706020d0210020a0e21030c070f0902040b0304120302070c0e0609180a030e030309040525020613120915020f0c04060b070f08120a020d1d032208060103030206 70
    0x200840a40482c85038604d0308003c00c440e8561a0250b003400e600c901d072902080c14020215401d0010300350300b140c0c8001d00c980d00e207810071074003480640244440c02c00030b401c1c04e007003c60520b41031000450003840040c00c068801c8511079019070f1081e00c40d8040b0380d40e0550005241e200280c1e250100703d01d00d41d0540380340d13100300e002c480042c0c9074040410007a1502c00c2c4100081a001c244c0b83c900361145592844d10700c0d05408100055075194441d8018507029022000c98070105c0c401c0c1401c2c0030030030308141240300c0440d004002849084508029600030300c80d000642c0300000c2202c00c506952242040d4818441c802e066014882c4950f001b00340441810b02d10400d90b10100c020300708000c01c5440380e014880c040703181401001c002c10101002c1c80e07042481035181900d00341564424482c516800c03560350810980005110f2540ba115005521115021140104004600f81c09840e100c1c01415868101c90b400120006500c10402ca403036402003544800351640d1b03513124280291036080440742c901064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119092248 1250 119090998 119091013
    0x3070f0c05190302011116180f0204060504032906062a010c020f0705090a0e030f0f0910031401140604031703070807020601061707090503030c210c1b0607050706020d02 74
    0x1e000100d9100b215505090207d03004038100414240e202c09507800d20007540382c0c0c40300111004045840284050801c1c0d0f25907030b03162451031a04a026000d00d001d050901c0c0c60300440c90117402d02038a0200d410031022503010751180c4411a072400b06500c0896030f00e401c025800003025200106501590041c0c9030395094819600f0040401640c9420a00c0b45a40045800c3d001464181455202c8051807124a007501c0c030345164110070310080d400c01c42000e414107400040c050121320340184510402c000b00d04040c8a107592001814410a805100e0102c2041c449a010721050781c4000c1140c2c0a19804480814034464910740060380e504211040e04c00f2a001c000421006400011100d040391404da80b16599104a0845d600301c1c2c0030003a1244c001e12481c10741c0400c55a900344094800018900003c0c8090b9034028010104071072410114004039404010080f5024000f10700102d510090031180401c40c990180840c000d0311410314040c020340203107072000c5001d980c0800c0c0c0904000d81c0764201c5910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119093498 1250 119092248 119092277
    0x90b0423030a0c081b160603060e07020c0409050106120309030210050304150b0411030906040515191a0d080a02011a0d020d050a12170903040803070f0c0519030201 72
    0x3a403142d84880070101e6003900000e800203207020010040c1c12500c0001c05046060071070301a140000c480040c0c00d20015880081c04010351606c28040109040d650300c40709410407480103510352488007241e500070313510b030f07003a00d400e0100c07d402040041c0300c11442501c111090f8200240448000e0200700c2c400e035507442174001118440c4094038040c94101d0b601c1050306029448d508014503500400581240d1541008025085481c014601c03500f91301d801351055143c03a140c80360419241d403959050080c800c3c0141300c41100052450f10b0104900303d800699059181e52900c0702030600c03661507070302c4045000c11404104c0307084050103621000b85c0080c492800304c441d19107200500c149001e90400e20700500d00000d0300e4034203440e96055009a09031244880719494041e041c2c51502c0400c0080789000100b821040503040d1010750024104014509050428450b25105d03c602c540240141031111500710612020390800801400c000780300480c0c820840b01a05004070035480302f81d0203d1000054000d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119094748 1250 119093498 119093503
    0x15110d0e0a120203060c0d0608030403060905010b010c1101050f04050312121302150901120f02030105010e0d0b01170f0706021506010302192307061b050f0409050a090b0423 76
    0x10b640d42c01000f81c820395a850901c1c08194002c1070300040d200d600e0301c10028405205000400245000c2d400120b00c2c1d1000b81032aa00355603040c48801d04000000000e140460154402d2442e17100307003460155911103014240003841d00541d00b11a91602828826040c3c106204000700b00030380d03110f5901503042d0b4924000345c50744402c15101942141000080c1c2c103804110100800c02d40b1814100801080112000d000454810108a03040b103540003005001039a0040840000341404568070183c0b1007455131a8900f190042c8526090341d503007030808011a0b20144149104950508201d955050b51860025a6120840001509040d5600c04204154402e0003110740d900b084030001201900c2d08001103450510611421700b84261a882681120041c08010001240031b0340c03001c03e15109050094600781e00400c1c3d0401840800c00112051103040c0e4199412070f840c20034002801d0f5221940d079005404004401408103107110200300820401c2d1890542c07241c01e000e25008a807030b1204a0a5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119095998 1250 119094748 119094779
    0x7020d14030615040e190f090213090f0f06051b04050102150702070f090504020901090b011b02010e1518040605030c090a0b0303030108100e0a0b0115110d0e0a 70
    0x11445a0104001a01400e103030b480b5000544a44454a00c1d080d17840404401101064800c400d603003041540452144085000d0680e00c0e60358050100000d170720f20380c001180c1000440180803d41d8542d00d031107090000d0400c200001c1034206000e01c02d101032620f03281000748000c071140c0c801483c000c41c1d580b00207c0a2400e80702601c070103800401c19a505086142c1c0941c81c020b00038421880340c15008145209150000e800900040c280031510341070520401000500c140c21542e07940b071906e140d03115560380c00080d441c62142d81c1c0201d500100414001240e490f4250454036410050640e10743c0341d0001410000d0000307200480c9152621003c99042005603403103440f0f400c3d40340c1e10840b895541c0389015100907800c488004c500066040500f0042415078109074010300c010780001d142c00e05034140034003802603c5c48125001d403200c181603584044c2c1c01e10040c0560b210400d0070124002a980c016203038041d4a21640742100c00714001d11000810303100ca8524031601401c6c204c140015151401c100c0390 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119097248 1250 119095998 119096027
    0x806010506040303080421050d061d0117190c0501020d0c230109062d06080d0f17010f150215070309080706050901091103031204030e03071a0307020d 66
    0xb4501469900d040f207031040043c01c10b60b07030441c4002c060110440c2c04a40e0080b04052620b0ba1503d40400d40b40a004440d40340c0d1102030f5948400c983e02425695003003003e0b05407103000045144c00c4030465046442c00031103030460f40c006101d0001c0b1005100b41c069485c4101c0e04247c0c01c0f01c08141c0454001c8460030914500140a20310009d003040c04800000c4152500e41407160001918103410b440f0003040e19100040100c100c0c00060600124581201201e040380514901c10700c891460304a4099a41c2850320350002044082c1e4045800c4510400c00e1403040e03000300b0040c44095031100342c17808aa075528890141080100c42100c0030b407034004240040314100380b00c014030085d60b031040b040e0050040f0403000c5030500402c100d9070000130041d108150081600000005a1110784d107800c03c4010b03082c0883c64829801403180501141140004a60140e0b041c5044490700440e100482e1800402d41c20680000d0303070b00c100c81c0b42c20032807240c0070758400c44c45907007100c24020400741c0030b42e80a074040141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119098498 1250 119097248 119097259
    0x60e07031b0806011701090f05010501020607022109040228111903020a0b07080a0f060302030a26210c04060c030f090905010603020c010605030601081005060f0405041b08060105 78
    0x7a854090b014403035000406042c080c5100c0c0c5a40c040d10f0180702e00340c1012260980c0d8030752464640340700d44a0a80500020700092a450420745000795440448105510080c10404000c1c44007481d43c40c255412010301810554844182501701c0d1446015030007612854000310300f9a0b50318a00c034941c2141c030018420091b084880c03403400c1144542004030815410b52160244500c0000c5440100f01e2260340c055680c0c0040781040f24510301540e44803244014044e00f444410302c0941d4000c034207100380d203503c0512403400c01d114031880003c0614007071207542d5000010640e115803860805000303250002c3d1810301d0001e075031510004c2d245400f8070302800300002c40c46210b40000900030300c2221669589401c029401e5503030b40311400c0584909030444c80c0025004103000c50344541c24000c0b60080c0c00700b02c026080d9981003104003580c8a0040b85030711145a10b40011071141c3d102c54181034044000a00180210720b001e00300340c101b08005803104103244649240c0003885070400700d02c050584000604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119099748 1250 119098498 119098541
    0x20f0f0717030606250807080c06010503241305010f02090112020427110304030c1407030b220f080406080109050601050301060c03020102090409050c0a1a091216030303060e0703 78
    0xb41c4803800b40d0174082520440200d80c40100100c0d4000000d0803003148610001a51205c800088a0500358107074030840c000c0d840311079441c03044004040c08030540c0131818410320095441a100c3d51022001000c0503200b03501c2d00316041d40090b81c80c1c0091614031002e80318180754040000289080f403042d0302c100017410040c2c400b1400982002100c2e68200b1718444004a00c0e81c4080c0399540440d44141c400324042413289074030785c0806c405202d199107441c0a200203040e0a13469034a0b1451882c0b00144854156010318001c02540450450703400170068002c01c1410304140c1510303109000d9440350003003401081c1c42070000100740c0b22601a4038030905042e900d00b4116481d040050300e03c118200070481c01d5540074403040915448034801c0c4d000b0540100300030040c1c103040000b4048204c03200e400c1840c0c07480c10084564050078288084829840341961880c40144019070b0071414444d00a0780c1c10040c51442c1000010705038160424010340b40c00c031000c0f02503501e07040c0c425001c0321203205030364081c44010a0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 119100998 1250 119099748 119099767
    0x2d060f030c090509070b0c0303061302090307030b100f0b0c07050a1809170304110103050711071406071203020702010e06030610030b0307170a1e030206010315020f0f0717030606 78
    0x1001240c10041358000c80308000c0c0c603180c0304030312600800740d6800f03140d0010007040343c1031038400c4c0c03501036800100c40b0440c50881280b010a0b01e80126000203400b050842e4080f4040a044056620040028080e141c400c3c0c2d0300c0710100d0486070b020001449840c0309120b00483c0500c1c00b00b403440122140340d038078001038514454500002d0980142d05642a1111118019180c02000b008500c81c0d03100c0e03804003c1c07203031000c1d00150403200041d150108000801c2c56a803141c040c00500c0006039403402c050085180e0b0010009034140c410170070010b01040101e00e900766038a405401420455201b622000c40440c00c1401b840340600048802c541d002c0400351032541514020703405400c01080140c1079070081ca880e17180e80c45042c00c10311001071a6030312003085141032249030f604801450340140100040510303c0e4034002d54840060002903c264685a20036a00007440e604848203960305010403500e03001144001551504500000d0720540f040d1300c002c079003042181d802c4070301c15400205110f0a000881c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 119102248 1250 119100998 119101001
    0xf010c2d02030910050a030c030608070605031503010204080f060903030408040b0a120501060f1407170307020f070b0a0810050102120703111b120c06070f02042d060f030c09 76
    0x1900310203601042001c0b1050380c541d01c051520921054403400d54441e04c000004084500241c800020140340080a02070414046042404c0301c1e0186816510303500c622281c900300c50b8450709159490741c40000c000602000c0441c0b0351058a40c2801a00c00b40c1d6501d020035a201c0c1303c2110002d00c048030810040c40500d02c18805050040d0041c0f0300000341d1440c1d6403000045400a80040c0007043c66031240c4001c00f9440103042d000804907090040c14108181d4032032288240440921502a10200000740800c2c402c014902000c5008000c65060659030320f0f4004450b070200910400003040c44000030070a145ca07a55620407103c042c2d0080019403280c21441c40780f9003101c5402c6042060300324001e01811010829003420441455501c84044548400c1021185d07000003002d2440d00040b00e01030341652420113881d8199040161000e80070320314030025004000c8801d400310001c403403d445400d604d410a100c0100d0010682081100e1a1140807555403003146210080602c0c1c0d49031418080c03041305 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 119103498 1250 119102248 119102327
    0x105010813050a03020102090a080102120705030c0d0c0305070f030203090703020f0a18060602010c020601030f060906020909040302010c0305060a03020603011517071812080313230f010c 82
    0x300580184041d049990b00c5081203002030096006030740100f41c650f45440c0582c440340003404208001c5160150418203216200d0380141801e0600101000140c4d903d0348000407100000c644030001c00400004800c0a00105001c1c3c2c0c050b400107420300c040400481c0640f0840c1d0290791820000c000e0a4510740c01c114104c20240561354020b10340000000d50132890b0311100111038202100451081e040c040002c9c219920803050070119440040100b0204001034a0040b0b1150040c0c4042419002c6091160291040203101900000d0303480c20002450b0341903101d6800c0e17851598051080d0b4559004020300445a401b0181d80b006040004100d1090303001c450790a01e1402e424489030a541c84002c05e9600c0400711160702c08aa04500d2100c01d8030030360641c03240038001d800390b02c05024840740c46113010b90000900c0c40c2507440c05803c4640500148007951541d03064105280e245480e51107040c2c0352190480f5041130115804c2600117003145020721907641d550000c050301c0900a82c490311040124114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 119104748 1250 119103498 119103511
    0x504090b0a1109060d06080d020d0f030e01140708040204051503190515100e0a06060507060c020f16030204060b091c03030b03070f180b1509040f0f090302070803090901050108 77
    0xc03c12880340c95841c0d00c1d0240481c2845544005045858004d0107400e01448814a0045401000740e01d0300b0590488040d6590351040d1400040300c00024580f03900412100000941c48800d04007008000c542c02024140701e28400e5a061141d500d50108070052003c451012031fa1540040c0645030b010503503e8200810b190145040b42e258001c54441c240d4031340c50640d12580000c140f202c062101312881007a85030001c0c01c40300108402c07450031400411500407541c0080c01c5544402009060610030010040140410340544245000e00041000508001c3c88105d000c0c90404c04006071400c0228141c0382d802002820f8000c3e4a010200301c043e03a6400c0a1049080c5030355002c0c642c9013503c080002c05e01a2003142d503403900c1780d4140008014035600c0d004803885654100303a10701020f80c80d125600d603400c00c0c042d064252142c9000002401400229904c1c01a0701e1a0102c1010700013015001188128043d8095400103526074101c0b5850b4451186050b8000744c0c154010400d6510448103a68843e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 119105998 1250 119104748 119104781
    0x6180b0405100c0c030501060e0c0c0a02060903150a050a0c08010803030408210c07031b020102073c1706070e13090203150610050c100c02070b070803100504090b0a 72
    0x40c2541e1086105a813070b4105a406a54440041c804180b205065a401215000040d42060200303013156541d4004008000c0c0205000300750081552420404104a0124810382c521140f034108280c4005000c210b501c2c141c81814a800c1c0404a809079824906a580e4640514a181e695895807a11039001b00074000c0e54251f9404518496560a52128020040710940680d06d0f003807403e009000410031040807c40b000b1541103031700142e0300042c03040c1c12075596214100d42402c00c40c0781400100d400c0b03040c29920014615040f0b03815840b1540c600143d035684400f000c0a0b80c4840036403030b594841102c0980100d101a444400079103030920241070042440c0001003988007269012904251141001c5002c80b1160f00038007070705207082c4541104542043c9402414182041c40583c1d4607180203619503104c558176503560502d144240000380207000182405130380e030180b40c500548940e00880300b0010304030340580d000c541803809014007001203070000d2032406161611154440148050201c86100d41d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 119107248 1250 119105998 119106017
    0x6210912230f0a050f040303080f0105180f04081902070306050f0708130501090609080d050a0507050d0216050a0f05060708060604030602091305010f0512011b081b040e0106180b040510 81
    0x2218200d001b040517500c250390340b66550400c9040c40100740c4060700030303c0c4034032842e034007002094081007640717030307000005103100152511682801c0313180e0f1240c100c1400c1485200200d01c0c03600da40001c1c110302241c1c8141e50403c040e5848100b0201003100039a10f8200040b00325010900d4183e14081702c0403240d00440000034206000c0d41c400048504108007100e1083c0d001c00d00d00540421442002c1d40051400000e12091409120007050380c840c043c038a1071100c0d07000c40c00c08081c10040d652441810351040c201c40400d41d00741082c05800751243c000716511302c41c000010314170b544103000d0540250006000d035803c040c10740d5036001c0a5008500340c03e41002500248100c08512802020b00a0501a5403108118140818018244220f403001c0c0003503810020300b80e00c18000c4500f00c00c2041c1b2603142603c000c0d20364900060301c0300020303095244822800f15000c1107040d80d10b43c03058101c501e40c2c0c841050301c4071404240b0ba01903c461140f078400e03040510041045003458905044442910314289100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 119108498 1250 119107248 119107267
    0xa181b08030d0501060e0901050604060318080307020307140c0108010302042f04060f0311090d0c090f0c030c080f19180507030b0c1306210912230f0a05 67
    0x1d64120041c0408100c1e29100104103054024104082142c030540341508198141004100248075610403007041564030000040c10010204888070b0241c0d0082005642c1c2c01c207480025602e0700008403e4442c920f6603016603c0d200ca000a0318100400c06844200040c1e2a640070040284040500c03400b21800c1500c0381000150351380100303031140030740c0400c061301e85042c05001000450400050001d243c64411410326540e404000e642044804541915040d542854840f080c400c0030f42c441c0418908088280310707804000e400a078900d20382d5680800104000c01c2048800010550740e001c0550480c0c80401c10002c1507580d101c8040c170b01100d003c07980f512403800038400341c29141420381c0d803074014060034020840325800d01c4e40c0003650341120340c3c101019903429108002992068400707110b43c6130240d14480daa000c0244000350009002040481090f0800300305410b00041402d000548610341d003905003c1c000c00203022411140007490030840d541224110560001d03140c6414010140074500d00e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 119109748 1250 119108498 119108503
    0x30c0403050d020616170105040207170409090615050607030c14100501150806060a0507030c0b190c0f0e04110c0a0c0f06140f0a0903020a060f02060a181b08 69
    0x781d0f64002e1006240c400c802d2248800c1074075542080104590b01c0c074000301c1c4400b442505417602143c0040e6241d4062a00480c0740403030cc000f000603894085000640c2c03800d030f0f511100300c05009000c14400301a50b40c101c01a10951401210b034043c1050000c1c0c40402d101e110b08444d130380d11412416920803410021540360001040300304907a2922000107100c141a1023006c0308004145003801441403d04000040050107000800c108101002c50300324245481540c4100000d03401070241000380c1468120003152144072a0168030045c10005010034032403103142400904074942c0e84550428010b0800c00c0081c7c110b429050b82c80500603c0105913601040c000500c4d032910402d140c0c5c41440c034099400e03220042a510403001c0c000c00e880101034005d51a01141c2041c0032a41c4400d50f1440e40390001d840042040c0c10194011040c0f000119296400c68400700b5209160b408a0b4a1642c80c40c0c428410b4488804814140800c000e01050000e040c0f4a00f541144880c20400e40041c1d841d09885413 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 119110998 1250 119109748 119109763
    0x2030406060e0a020703020f010501050a0303120213060f030e070609180b03030a050703021207210201021e0409180512070213050709140303030f01050108190f0204030c080a0c05010302030c040305 86
    0x3c5403503800600f000400d9010018541d4115400c8000e0105626140020301a01c0b003038803001d07040c08446035400000219942c111921400f0b105403124000d5202c0720010490150146240c010a1a1031501152680c3c005180400ca0b44603580e13021485081040d401705100c940c03505529080e0711201b00c49c15541e4180040c1100c0d0f15231355500f51f200c00190400a00d04095841d6000081c0420820320020400301c404582001402c5000c1488410410200300c1c02840788400520107001100780350140400040002c008503103100b4800e02040810017039104002c5413400c00140341e039016051400f800e0000f80b02411a00e4001802d4440072081d040e907a205880c41114a04002038444a0502c460007580010300b086080c00d50040d070562518400340d82c8043e2060003001e05200031800069032401e0207031903900300300d0b1407108144100012a03221101030340240c0811110701d0903003a404a40742d1000918051015003012040155629140041d0020350003d4003000950904020110216104004a9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 119112248 1250 119110998 119111011
    0x3020a1205011706161b29070e1519030603081303050706110c0904140307140f01111602011b110108090601050a0308160b09070f080303060a0902030406060e 69
    0xa251030100c03e84060620b1801001e21040e04107081c590090981c2c00710000513400079407401e403035038040f1500f041c44071842c840c9a0070340b10314454580b041d0741d09111140240208810f0f1107613440741d012042001030a01d452011920000d0043c80f9107503110070b070300c5a03a000d003036664100090201e0700c0791034500342d036400b4407204140040c1c0814100100241000343e88010956450100411983d902245844100c03d68000348542c0b10744001c0f40a118032203407a01001182d00003101e075140583c1c076000080701c040903040d0310790b4051b0914032a42c030803041c0900d01e100b034410b2803854544211751107455104403048005904001214825010484084901c01c1c2e5613030080045a480003828030004041400050170100140c002400400464552052503c240d0b64030010350368a602c1e00c684000c001c001c1440001d020023408000384101c030717100440d030f0302305070340880c2002c02940e40c44a00341680c81c803045c0d603200c0e00721a20610402500d060b950156401510130000803441a40d00c4144010122055586 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 119113498 1250 119112248 119112269
    0x1302041203021c0c020d02060a0306080d030902030f0f06010b0a110d030504110a05030606011211070b0709060201020309060f04140a050c01030e0a170913060308040518061003020a120501 82
    0x43e084600b03004441080c107001c2520f4020548034450780031a05c040340040300240550008580901403602030b41020020740000707070880d80700b9150000c004015149000b02a8002d010740e010014400e80040b0f039440717115000d44c000b08030381e03443c2880580355a40400f03096010841e00d00d45050080d142800902c0f0b004000742d40100311030800382840010030510f141500d1140b00250300410039900c01140750307513100c0301c05d00700f0320b885400140403a009410b00300340b19050850005103550800c0001e952481c000d007456a14040390a8594000380e08030310050303812618607070003540010f40b110130780c83c5090342c0f080c800e101c1000d24960141d00e0720700e043c004407000c4070103401040e581a51942d06116016130a44140001d00410400da11101001440150399642c010000103815083c0d860b00c400d5039008a80e544810010a03a8900748485240c01c1401524840d04541c1415480a94600d041ca40510750003400c50066aa219005900950046411005001200080c1d444160040c8221350082189810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 119114748 1250 119113498 119113513
    0x18010c120c110306040c09150513020307020106080a0804050d080d0203150301050907051302030a0b060403030c020102010506040507320f0d0b010302070804030b0c1b01090210110c130204120302 85
    0x1c0199000c02116803460281d40004104000304941c001c86c0f104640d500c480000700144111400513406c45190030081e00140f104003103001402e5a03500652041c0b0710342e4002c22805441c2d007050ba886000c0d400e0050010700c1d0600c0300340603901c1c1100248041a09c1404c60074500000d10410704240d82044480c0e01c40b040e0a9000112141020b00885a00424501c0079041d11400d160010b206203078103808003080d081d408400511241c62940c0654803594000b00200e07125981c030700c2d006185001910089005500300b00104046003028081c481c0210f80b09d44851820b000035042245028078401440c00c1ca4101c400642c0c0c0c2104800c400401117120b40041341907823000080010401e440719407240c00d0402d0700c10840d0802185d842410384058036404440f881158984800c3c150035402807280c050b00342e84031844c2c0b10104400541c491040d0501c02c0c0d5148045000c4100c040e00d804103800021900c5400094094080e8500b2800c0303045542ca4408006040c42c1d00d88035454402c84040780100c000d43c3c0400e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 119115998 1250 119114748 119114753
    0x2010207080616140412050703030f0311030c1602040e0d08011706070c0305070c0b03071b02061c0603140601060207080606060427050403230306030318010c120c 71
    0x6103805840354030020200341c1015009480e8801403902c4401c01c01001100644251011500300c50060001c014008a07580c0c42c1c1c2011a207801540c803048000c901004401c8010b18001d0084030a8030303074800c1c0714030b003565206c00d0200f400d0780c000480380318180008c04401005a8031407003200089440e4000030221500c0c03400001e4036207034041e007024030a4000c501408006080c0004d8490f4032111700e1904c001245804e103019500c1d4040c00400501e98103041602265458080c005140719680565805941d04160601c41e440b10803e00700103900002d0400c8070401c0c1102c881c0080c01c01e120202c00008a50b6034a85500940040ca94010307403440e00039100410840382d04201c064083c1c00440040c00c10360a019000400522131842040e1860200482c000c2e0b25451081a025004124500c18072692074249001040244901c80c44c1c0c00071a2050004681c4048100503a441500050000c52070140d002082d0144032110046241c1007105084502000076111801c60514088546481e84481c1152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 119117248 1250 119115998 119116003
    0x207020612090f0f150103020f0310050702010b0103052404050c0c070b07050f0f1504150c1101060617060f0406081005061318030c150204080a05010e03070c0311041407020a020102 79
    0x25a4000d04ea6104e0415034250814007501d4604407a4102d0301d0442d040d540e140400e061566015082421516150400004e0790301900300d6505107030241e07803c00486e0350b12040044c50448254046c8944980145030070614102940103d1b00309445255950030245041103092401c2c060760020401240040740300002c2040c100b0800700c600118001030000c1007064620b140c1d4900f03000d0349507a01a20010041002e000359010800f02500411a0501c0345030200000a0221140d12000d89259840c201c0b0029220380b242e0f40341402c01510060000703240c1c880038200442000e1503c446644650f0310304000400400421002c5007604110401254510b0010100b0500c000301039480602c050601c02c1070300c1c16009000600103c983c1c50704200c40015180d0802c500200c0b264403481030b1403840080e002c203000d0000a60788101da40304400a0240c0440030303540c281c490041000041031070b4a014003d000040c12800b4200405201500004103c0340c121800585040c0a8030a4400750300b120b0751110a55074103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 119118498 1250 119117248 119117263
    0xc080d1d122101230d140604022d09040503041e0603110304030905060a030f1104052d060d090602030a0f0e070b0d090c170312010806070e01030207020612090f 70
    0x2140520300d9290314002c22404c07a4102d43e00800203904c400046000d10b95a5030303440c02d100a4002d82064048054440301c40d80d54201a01c042e84100b0300c0d0103a80c00f4441c82109012562030540c0342d80d2824004060270311254002c0644201d800f40024000494001e001101e10110842c070210100600c80c903041014089642800481c001d24030b0810400000c00d4008800104640040d41d12503542c070754108048004001403440c80e00c44c0350910030004501440000a0402d450381100d11018184050410326010034200c00c0034055140d9804040000385400c4000c0c0001d40103140340071584032940d503564400c9134011600d03005141d640e400001c51440701e500c60681a032072900c00521240c0d092080c81c4649000300d03e102d1030200c0d103400c00c450802080c000004018240e810808c2d0140320040031241d00d0f034006c810400d140b800c508000007124180000c0150140071951a10700080078504c00440180d881008141e8110604100c0400080c0440d02202e00c102c095101030310702c41401c150b2050400300c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 119119748 1250 119118498 119118547
    0xf020a140906120c0d050a050a0c0203040f0501050a0507050105010e0a0b01020a0312050c04031401091a0c0406032c0106080c040b06030604051815070305070c080d1d12 74
    0x2000d029001c03590322030300112808150b086155204956800b2040c480d24031951402820ba54104804e1140a007460f8012502071000a032061100074000d5104076500e0086118074140107031120b5041029501400040402c244140390007854106180c441d9070035194280e12100c801400d010802241080c50701c02e038211100244003529004034079450051040001c219100803031030303491000c5600411200d04031801154411903d20706140600803681c004d090041041d02c40c202003036451450136111151080c07083e4003030902c0c00d0600342003076000c078000d103a490303d00228009001d0040745100400c124010070765541e5000801c0e660f00300f944680c180000c90249034015410030580b03000d29641c503400d43c5d601c80400d40d40050540d80d4280300049010b40341038144e6040c011a80203101721002042014410455501e040c444c0c2d80701c40703804498081104201504c0700b1410300c80f00c2e80c40c42c003542140d0f002503491080d4107200a9844807140c01d1280d0307607410490342d01c070000d06d204000e800d03910f0b0303082c2e00305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 119120998 1250 119119748 119119787
    0xf031911130204030b151c0506010914041a0a0605041a030f010c0903060e1005011e0f0b030c0702010e060f0403170a020d0c03090f030602210403052208010f020a 71
    0x40c03565031070400140011b003807001e25050043c0d140c001a203a0014034501c1e0080e8403041d201600141c10907030384501080c000c10080c9400c00101d400450352006407030380038a90003c040601000d481c3d00f0030a101201800d0905000e45591000a06a81c4c1c2c0c011b10070048280004543c10304120780805207840d05001c1c0d40c00040c0d050211020546402c290b0280c05c50760000b5010952090290311a0b040002d141d682d0001e80b450f10740040740303080c29408500180d4942d0302a80c40029120b4100070b075015018422486542d0040001030081c40c41e000260401034410706084491001900004a064000c81184200303640c01080c20009c2c030440305040e00b17501c40d079001072038580016840001c0d00c814a40c005207042c44090b4102c5c40400d0f00c502036181c0102080c0030356000c000d8032480c0480107075004070f51b203403100050001c007404460512905d040c09158151292850320300b1500e600b0540285882069242003045140001c80503028003c11442080b00c00f001a9100050310001d4480320f983c01180351801d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 119122248 1250 119120998 119121007
    0x5090106030b150607060e0a0c0e0112030c02181504140c070201080c0c010c0306061124060102011806020406080f13150f02120106021b06090f0319111302 68
    0x201a4801d01c1d0300599483d50703222140030100041042880369800c01844245480103608030f055011801541c0d180c4100d002d1610540e0391940c1c1440c0640c01c0c0215136011480400c10f8000a0103000071031082c51002d041040c00c00b10111a80c00011000c0300c3c0c41010105141040116141c203128420503900d843c116486142442c2c06020a98000e45000038144807081002c40c1542510300c0c00d64407003510180083c80000310081004004d01071a20981002c1000c0c0001e5001c84100811001040d5928400300c070300401070b0b90750b02d42d40400d01600c00c1e415950b031035410416244508884401c414003c0702c01590703840c0340a000420820005182c050b12558880900c001ca940e80c1c4c410303041d02a0809988101904d404041c1c80042a04144d0500c00c03910010301c001004200d075890b641242c1441c1c00b0348000040c0c121840b1400382c40b1241c1c1960041d82000824400d192105103c0c2c48510082c0c100d0340314000c0d20b602c070228500851800d0392266500b4100704003519080307800150900d0340d01c1d025400c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 119123498 1250 119122248 119122253
    0x102040311060903150112051006050f1005040506041412030307021509070f1d010801050603030909150d0b10051009030609030e06030106050d05060406031a04030504051306090509010603 82
    0x1050204144580315a0000030f107410a55410400169007492405902160f03580d41c0b01c029a90341e040910031074050184010100d4028000d101c0c00c02259000307015040707e0303000706040080380e0501070703078050034000e09200200711610b807070002c0d01c00b415000c00b8241c804c04e400c004025441030324540482c0c0d158000c1003008415680400e40c481d41d58002d8a404e5581e80700c1a80d018188556900138951032020200c0c005452480041c2c00d200c0340030401c25901c07142c0d80700c5a0f04d40c04d0322400c60701282c05500801440075503051103192154410340e21880d40342c207040c0b440c0004a40002c0c00e40195814101c1d0000d21100745041d50301d050081c0822204401c0841c480d01b00541030320b40034440501401e907105101c0007454062810200c400b000240800d80e290307181c40025081e6044928401e40c0c1b46e00d0107000a500d41400c0c0304006c10349410050303410481200320400b0003100d20040040741008820700c00060a9100c0da4862103c0704400c83e4013152131818080344a048a000a00c4101140c0c1404800c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 119124748 1250 119123498 119123513
    0x807140402181201060b0d0c0e010c0506180f06010b0903150106090e040f0218012309011703160606030209070305130206160203030d0b1011030901030c030603020303120601080901020403 82
    0x141000540f0201c10306654166010300511080d4441402002d00203000c2100361a241d10400412007152280f00b8105018401112442e050881c0140035601040104140ea041001d2503914050782508854440c801c181c000e80c1071910a03440078110381000b1a03203c0d914070307040c0000360042c02c10010303e1955603d03180d001891150350388180b2554400f10000704050242c4041444446500904a54a124003030a9070207139144003485610b03c1c0001c0702c1d002c00041500c0c00410b04881c030005014108076400c0c8151011141901402c81c1401c2c84100701c1d0040b81000c034400c1c40009400345400040c0300d07140d80140041044003e11035001c0518240411000e408800b03441820641c040e0341f20394a4601c8820141d01710540c41c0f40180d458071010480a00403105900b021001e0740003520f40707860314074040d001640e129880c29032400280e0001c0c880160203501ca58071940c0410707210f01d0301090300d6079690040790a503030141413103c0f0400103a0f07080100ca5604154219004a00d41000b10f2034240b964440703c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 119125998 1250 119124748 119124787
    0x30a0207031203060e040f0b06010e1f18120506072a02010e060d061401020a0206030103060b0303040f031104060b0c0c0402030a060e07081b180d030314010807140402 73
    0x2c00301001c0361035800000b8803a80c080805001c080d0380c0022581082e0800c9020355a2102d41161025640c6000400035485a4204c002c480009043c84034071490359805046c56050403045a810400c5d20b101107a101d03200c0450340c0000780600044c41c0310151807810441d09001d030041816050203040340900c002500715142e04100d207003010340341100352041d84c401240c100342c0c4000c04a0740314030040344051a81095601441c1103451000c41040c0b21000c070303001661030b288840302c069486030082c401000030503c640c01c1241081d1004048d81c0c5065251240203001d600d05030426100d548100703a401006040c00c1c030903100a8801c00c4d01d030504106031151841d54440250003407038015600400400c8010101350812400b401c44404d10b10305074501444004d1004004032070741c1190a00c503070403030152130b8007010440d941a208030103d10142c0c100c0f0000d01c00e00389210501101055a41d40034201040400841140605002005089102e1425600380d0100982c03101c0e161041d80304100402043d0f0404a040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 119127248 1250 119125998 119126003
    0x30601030203090f011d1005010b070818040207030e0102160b030118021b06060a0b03090c040c17070f0f2c01110f0102030612010b090414072105060702030a020703 72
    0x250340e0f036442c1c410160034a400500d07048136543c248031940790031030704016090658058480071036204456011140b42958000e1243c3d0307e00c400e0400201c0d02080300302000304000300d14441c4c07056000412402050880c0d00500c003c0e40042c5285125030100d42e410300051035140038002c00019018209202c450306840103200314415608810100f030700604041d01a02d1030800110549610351240c2680241c50f11800c640d045d2003021000c40c04140c1e80244030540f0701840140d40106801c1da440c205000003003200040a50500022001003102441510350b4907105d041203580d490381100b28400041c0201402050f02800e00503501503030104503000a01942c0440c1403411265020004140180d0f80c0c0b4284004154150260b66420040704805400860080c04151800001c0e10003904469080b00c1d50001200e600260b0304012a0114500c400b03425094507103081524465a0b91f510b00a000c01c210b01070034115018001480801c5c014244541c0307601c07030054000382d440c02142450094071100d42e030200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 119128498 1250 119127248 119127251
    0xc0a03030b1809060609091615090e010b0f0a050d1d0709020f031b091e09060d03020c130f020a02010504050f0106030f150f02040b19210b030a060c0c050c0d02010503060103 76
    0x1303003d0442003201204824822324100c4210361030700300c4074030b0300f0003000007000c082070010400042210024030301d141210b2401d010705003805501c50307144605a0060800b0402c21030240050050a07565203d6107071000300f000308460140c0c0342d070300c100342c241003052307000100302c500c1030041c5002c0c0030484007103031b03400a407080304503110041c04044c0450b01d024840c1d1240d0461401d500d02507405466003444943d51004490281e410754800003042203402d080c1d02c0c0200181c20640c0c02c50014141300305401d20350000d088010070304040d905001c00490b0001c101180041c0c0d103900c14001440b4080c81440850020302e40217001603419a1500726040402201c0180780740d103403c1808201140030780c405903a1030103d2405568840c2d44108040580d00a05001c03180150700d141c41e42d082902904224401c0b1003034044540d00c0c1c5500780d10b1600209aa59031241d01030084071807080000700c10f44036040101640303032101002c008840c05c2c054070344104410394501a1b041074110001607a04013040d00d5102c030b0240380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 119129748 1250 119128498 119128501
    0x1290d021908011404031d0d03030b0a0302040f022d190311030411100801150509010905180403120b011d01121104091518020f0c0a03030b1809060609 66
    0xd078030019040340d50185416501c1c01c8624091514500b10040c0034600a60390440c01c1440d101c80b00002039041c002c2194020092030b500d00c0024000c0d005408500c500404881c0f010b503403500420142d41e25444680c0d0600d6001076059561082c40c0006401111100d81c212404401104a800540328041c80401e0000d0400015003070741d44640c0284003405c418007245500d0f402c080c030b0127440301000c02e010148902e801e40306611541e481044114100c1c1d008440d8071400142c0e4200540700c2d0340c803000043d030412101a4001c039654032580e9038580c40d02843c020300412484c0a00b001800c0d4508043e450000300e0038461045c0c0141c2c1c5c0b0525000e450013001c0813040300e004019006945409194904a0459080600b504000b00d00c500150044800400d41800343d5010090b406422200e10701441514403400e2210310301500c0180d025008030002119001d192854031103400303240414004040300020b0301c9884001d4503043c80e0004008240074086a119141001e1a000c0e86401005180074090701c7c5040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 119130998 1250 119129748 119129779
    0x3020a0603051308040803040e01061e0f0c0b010806060a060203040806010b0a0309050d0c030e060702030601031b0e0901020304030f03060b0307120209060f090a0e010806070c0c05060c01290d02 85
    0xd82c1c0003462940311001584e65a686d100e500d889402a100f01c15012802500002c0e519028004400c0e1600400c040000d4886412a080d20401c000200c224200000c244465000424000785a8060141d0360004c0c555442c01c07908000c0030b0411a0400411904180010402d012001403800d05450084d5105600d803540ca500450081000304006040d6100350904000320780d4024030100c80040c0a030356101c0c0e9090541c0103100d903512540d40300070f405034080001000454482c02c0841c0e101103466042e202010751391400600070300e40c02c0c0d945070301907580002400100b58000d000300340c40c01e19508084c81040d24114a80c405404020301d5102401401c40c4c0903824040e50307034120740700103900511881d01d0f00700c1100128542d4112458107400350049010219400913400141c40c102c901020003490791f5a2410300840ea003982401c000c417149083d03140c0100d019036a000140040e5140c40c0d00024a86c1961180c007001252408801c401e610403180b49803165460b200004d0030151b405031002c1520b42d0010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 119132248 1250 119130998 119131021
    0x3030f080c160b0708010f080c0d05010f020a02070608090114010b03060f0303040902041e0b0702150c0a08191701090b0f09130c06020c0108040201030e01200a1803020a060305 77
    0x10442c000c6040d150501400030083c0340001c241c000e5105a4842840341c0c0c079018900c0f180ca41c5030180c050103034481c08022820b40b60801d020700200f44540300109840800810792004d03070304000d040c000540c1050400340076956010110b0f50303018141600910002007a406072482040b0103014180d114030000001a5198a81d040342d400b0204000e8200e80d60703075a0ba85e034910001d420900034a85017816a450b03c260002c0d051040741c0644040d41001c9103800880d40c00c00104007624141d0680c074910a10000d80151001e000003620070b07000d03c1c611035503103008807142c40701a14100308540900c200c45462032004141c400e249815240600000600950240001a6041e65021009501464a03c100811500303001281c89205200b6000820100d80301c0905984130f85c4180c1d1418001580c3e0f000241c00740d0b110740c00441441220200020780000d0004107000c01c54900e80510160000028109480640c051042d00001c01680c0c9203010543c2960700103010141380f0301c02c9608042e11040071a4814040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 119133498 1250 119132248 119132257
    0x5040f0b0a02181212160606080109060e060f0103021c060e030a0306050d050303060d06020f031f0602120f0304080f0a0e1c0b040204091412090306090703030f080c 72
    0x4040d480c1014940342109801952011400d1020343d000e01c46002820304040f10700c00b6105140342e0150011155440020341160000b5003081286c00041d071411010841c0c6100c2c8901906034100017140105550401009960384803001c03000c241e21074420070549581d03465200d819280d04640304254481d0b9400300b210700d10072481c3c0c0030380070901e40361340b10349460400001000c0c502a29141445090760314020850301d540c088502901680080000a901d882c0001400310b400c0e1080900509180b03501c15541c0c410f800407502c101d10141130f188905030701910702601c400140340a1000300b00051120400f031105005140007070b55100300200108040200590699a030180b0101075281c45071401c0c68020281c0307042c003d40350701070448a0001422440000c9038062455000000c0c5c02558440e94240002814850030541b180700300344010040c20682070000703c0042c512102d000e51030b904010205428000c0c00f40c444101c9911801c000c10000707411103403d060400c1c04c0e041900c040d59400d40034240c10710a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 119134748 1250 119133498 119133503
    0x307120315080c0907090617070320120f06030304050609031e03040608150d0206070515070c060e0d08160309021c050c0a052101060902071118071205040f 68
    0x50300c0002140c0b000c40003864105490040f58600102d0305c901d4419503915a10303000b0b800c00250381455501d44000541b006c590083c606250000344402c900788280b81132516034030001d1072202d0001d441c50140b02c1803580241c1107903130381d0340720662801d2920000e5642c1c40343c1d204203401480d000c50003035055901848180300154190541d0f41c440001c4030102500c0c0c0d4068000c00e0045440310303000c1080c124503002d04d1520640047d000941c20451502040b07000e0700075030000c036614414070102c3d00f4101e12a8120700d00416464442e6401005545092001da0b034200d404000705a2001d00c1c0c410845030301c03408064002c0440d00c40c911041c00e20903800c0300134109285001c0d401040040c10100c05811034580c01c521240500c05803550000c1c100d08120911019208440d4441c404c800f90030210880d401a00c10103060320701c0001180c40c0d03250710020aa07045070a06541400a00c5900700503814280c06802c0081401c8a074800340380f607d2074016205030b032510a5400910b503500c002504114010300341d40c2c0c0541c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 119135998 1250 119134748 119134781
    0x150d0b190303050307120213260708011b0507020a030b0c0c01020c03070308090d14030c0c0703080903070803030708010e060d060f0b01020d1704060f060b0708041a040803071203 78
    0x1e4690502410340d501c20303105c00d8005071503072a009000a401d44260750940441003400c4d00700d0341c5000304080c00841c0c0304400100c02003054403498050b510811502c07000b04481e4002185400307182480c0040e40003124107010500404110b4440103903102d81d424020707079501020340001515240e1258846018160880010f584005221411310070000060302003984260340300003071a0b48074104c650700c643e205602c400c04940540088031140c04008003459003c06111490350074a103180c0010340c42d001d0154816100c000c0001f80314a03541c1402d1107500040c8c03420304003c500d10306152800515200051040b0070101d50b00e44082405035583c01f111060b41500038a05101d11080c0c030f070b8900c0040081c880e015002d48641d0050252460241188140012001110189566840c0c40c0e800203042a15042124a580c1d410b010036154900d4018006840c0100900764903142000b111165900b4046401d402c0140244020410b0940c00021a000560301c448802803009035081c09802070600b0190549405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 119137248 1250 119135998 119136049
    0x80403050601030b1b0406021b01020c0d15050c0c060a090201031407080a0605010f0c020d020a1a2203230106090221060f0901170c031606030b150d0b 66
    0x907140407070251601710012007110520a00b446141d10a520031807015805c2400f0150500d480150f50009415040c0165164850f4550004041c3c01484004581c03d58420311056402000740c4101c5502c45225100c586c9800000200e80f959210b00520050343e164031020b1200031648a070f008038600c0c1c104003140c8000d0303040400010f0080303801100c002807003d1402400184561180800807101485a1a0241c0720801e503000d01c500c0c206001c4090380c210b10406d00014044120800d800051044022aaa1544504c002c01400c1203298003040e03120245900080c400300f000015900b02112450766040302c41400d50840a000d00a0ba07400b100071244003040c2904680003d45064607032081f23a4620003926920700c1c003040300c03c800300d003445504404031000501403503405070761900f00050f180c8100c5d00003014810009251454030040c201d80140c0c1c4070300801041ea0540640018020100d88448000001c2900c4c84424003c502d02e401016441c0c0700112115140e0340c20400354a01d260720110181c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 119138498 1250 119137248 119137253
    0xc0a08030a050a0e210f0c07060e011205090309040903030f0510050f010302040b0f0f0d020a030b1203031608060103060306020c0d1b0506010306050703020c06040c170708060f0408040305060103 85
    0x4040846403d00341c00c0c1415400043c282c1e0104420310344220000b03090000351401c4007406040d410000e26200118070070001c181400d04200144d400614990f0782c4c0e0450f92803000001842c40510000300c0000034100000d01c01491008815905000c0c2d0540d400101c020981c1412405403401d800707048180c07494107017840001c0100300c00c100e05590066079a80004030756440110102d04c80c1d880b81518495040c88451042d51142c8002e05121141c0900d5504080c910b07c040e00c00c80c0d101c504c42101003644c039440d0402a01f0400c11003200f40d240c20002c0c40c02c1d8a040055400136519014a40c82044044070001e40c1983c02980f240c005590455011911a170b130304800ca613a11003c441d4a0008140c030007080f1540c1583c0c1e0004500440c2c0d00c0303400380c241070346160b5034400900340181c00141403540a002c05c503410141000f00c40d1043d4020307440d100301c1e9860195402007010311800142400c0d000014207020245001480c1900003841600342c501e0b075a103608048401d40180c1d00700410714001d80000005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 119139748 1250 119138498 119138501
    0x612040308010f0b090915030718060302031218010c061d160b090a0308070816050105060a051f1b02030a1a060621071205071d120703080c0a08030a 65
    0x50b107050945601ea6a44c413610580d003107006254030154402403090000e00c204000c24400700c01d42e00b0113004c907404e185d104c4200c00c101c2e9045c0980a40050ba941c0350030002c1d45010402640e01d6401c45001610f8840c1503201980500c8080030760310305014a0035100c07410805181d104002e81c00b85030f881641c802d00380406480d25030141801007008802c405501007040c404020450743e5a00d80108081c400350315558800300c1300d404c040c1e02074038906400c0c80b110321411210800c2c002c07480d1140c4000102032804508100003200301da04000d004100f021188100b44848620300074048003c1d0600410f54142030b980396480c003410740c1009401d8002e11095000300261201c81c101c0d08000d080c91035065664000034007101d40900d08911400d00e610024400f20302e000240034580044d40d070708e8140582028000303602c0580d1800d9400360000744c080c0d50700c50380e04a84508400d5500d01c04940324001c100102ca103480c0d40d98094080600740c40000101030002da070042010600140c1d100011a4580c03800f030b280c910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 119140998 1250 119139748 119139751
    0x2070f0204023106020601150311071a0702070303140922150e100308090607050d050a03060905010f03030f020f0d03060303080a1e0b060405150d060e0906040b04020612040308 77
    0x3e202c40040c0d525059505114404030544520740c0c020301c02c603880c1c00003120395174000e01c00ba2420b051780d40307070311200d8070540c0c00060080c80d001e80342c1d035030300c0c101c0c141d640c02c820a200508810854002a000f413001039444104607000d0302000404584441070100000c0c1c01d05041c18114982c040001c0d800000a4441d41184003980400042d0350565a035800192090280c121845121420840030900000f00c0c0c41001d0441d64501400540c10190136650301464400305411400c007146e008240d944801c1d0b0306001b020040c000c0703c04144104c3d4902603464081844600008092085640e0420891407080280f001450103003421500050201e190280051140740000d40000c0c10700300019040400310b0040d84401580d08080c4400b681581c000342c0001e003441040181d2140042200003510344d10110601411200c0441065171500d01c0e102940451343c043d44549020780921017081800c1c0f030040340e61a489a04180c1d000f49651380c510010312948034a210546c3c06600e0031741800141984512841d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 119142248 1250 119140998 119141047
    0x611071d150a03030f030f11160b1003080711010c0b04060605030d030516140c0106092403050304030f1a010303030e010c08061e030f030f0703090504060b030a02070f020402 76
    0x18000c405400d4240b22034a800b40c000a008150b901d0304a40600d4420350203111a4450034078001181d0011000104455101215144800c9048035200c400d106145460503044481d2071403240025185649940080c003980038007401c179902600c2c0c0d956441e40622413526082e94407032542041c501c3c040c07402c030006006a01503140a880f44850260b00903001c0e21826010702d50700c00b040d20102110001c04c0314030302004c10054210110500c92000c40300800d00031a0081c2040300310114908a4100425480b20b00060410400c1c0e0907442d01000820350100032901903075044a6038410030f80740d07400d16034072081c041d940d0aa01c6410b40000001810390544c0070443c6590520020b10407521a100b0881c3d2105003514a59404401104441d0501c4016446000500780141c1a00c0c0903410300c1000c1404d64005904454100780002407802c02c05603c00c443c0c5001d0720040701c00f04101c0c0c2c100220414030713010060183c40c81c00d900154a20038030055084650f0000d0b4028400d42d6a02000030a25051503d0b45200c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 119143498 1250 119142248 119142271
    0x61a0d0b03032a010b0a170c0306160e0f060a05030a02070f03050322050316061b02150907140d0f020a030c0609050901050d020409030507050a1a01061106010611071d 73
    0x7803601e006000d4140308200007042421b004c1e00b410442e0b41e06412841d02c1209a1084c824046450b0b182484540c1c410b460001484070b000000e2040504019403100c030840c4914040d15158440343e032014240d400211540c6412502c0b540d07080d1a040081c8528000075010403111101c01d010564098002d5125041200f00c649109541940344c443c094242600105542c10922480004188109420f1050780c0110b4002c50580d1075904c40c01c410900e1500040010b8106094001820000f140702d1a00a519080280031103840c00c00d802500004902a0350301c190562450310041c80700541c0703120078050300200100d00660307032441e2142110700b842c0f1801003c10010040010f881c6828a0300fa030403a9809020050744480d1a402c000042c201242d00b142400b000344441d00c0441d00c01c0085046031031042c00300c0180c0d00d00780d50f1101040c00e13050788030008103c4600c8005a80c42000300300c00b8111079550800c0180030615003055030a101c100d42205d060740c0360f0342c440040c544200c071500a0140d03188281 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 119144748 1250 119143498 119143567
    0x31e061006030915020a0c0c0f14060a021009030e031b03011a0607060207020a08070306020a030b121b04020f0a0207090e0a0f0f0804170307060e01061a0d0b0303 71
    0x141501a10318500000c0c2151842136801070030840140c008080320350180c1f418149030150365480d01b03020120794001044c010002c100030b11401c4014803d03403014540032a8118104407a4040c001c0d81d0701001180c5041c55034035003400f001018012010000112002015110000d1b202d54465181000401c1c800348030390309101c0c600b070141c3c00c0699091b06020000d8845850091651600c80107036200343d004a8004040f0361000403520800c1c0b10150141d842400b0240c2d031440e000c0001000d4440055403a8031940c01040103000000700042c1c0140c20083c0100c03141d042030301c5040040c000340aa46041500c0002c0000d046c4100c603070120780d0500b030f181ea0352130800c5120229501da9a480c2401c0000030045080280180301040c402d00c240c070a81c92241468602c0c00f41c40d203002c07544219242d40b81d00650b50010401c0c2d0200121401010042c9440100030410589810b44418103400c0401c91220702c038600160400d41c42c841500116030700c100c081e0440342ea841400c3c0c030301c400d4550061403e13101c030040d490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 119145998 1250 119144748 119144759
    0x20d020702012a0803150a03081e090d15091b03170a0e011407211706010206060f010302162402040803040b0d0e2e020403021806031e0610 61
    0x805108804242400400c07002d100f0341e40c03d4015400034081d146a80c0c1c4038501b0480f15a209606030b0003941c0315032085a01c50a200a1210445028010352003141c4018041ca8505881c0c180b42402c0c1e55400c0b240c1d0f10180c4540340c403010024111024013402c03014171194080404040a0303996400c4030710501d00c244694489607100a850300034800c11b0030000d41c54000580442d0f00c9154007441000208014514210031a510301c0060700101051200d541c1110b016507108a070010b001800d00b101d4029604410315000d00000e4864000805d824410b02681c0c100b00191f034070030350584030003030151914540c0782e5045003819131040c029402c5c04c2558260100c0507100744030503802503800310f401a0b8000c5080904050320914903070001078400031220394460b0740040190040001285030324840401c0007100c08005c00c0c40000c40801029400c01d42d00400040005031141d180104507212a090380a0765621010000707800c090309010b4a118015000d6284d880621011900c0340c01051005000c000499a51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 119147248 1250 119145998 119146037
    0x30901090812040e041b030c0f080c01091e0e04050705030f0a03080103030c02040e01050a0f0e0106060e060309030c07031103060f040b0f040302010b0a08070806060f1c0204020904020d02070201 85
    0x14035000200c2035040c0010800d8404c120316068009100b11104180e40032280c0a0202e8800c0d158001d90380740c0c000000803c110000c0c110003c02812480004c5c00540d806800060004d2400c2d02c035614104140901c2002c1c50026840d0322000390068060b40d038003071b00f082e007031281e41c8845500900380f190003200450703200c007080087e14064896040d00e801d4074903883c585040ea03800a000e1401d07038109458410b4079580c40002e21640d031284184c200b0005460b01807070b4000e402c80d00c546101d0041030b89080c000b0f01c4040c0c1c0110000c2d102000480b0b40382d54a03034840c800c0b582540034900c5400c1c29889004001f00400c108000001d0903e14207404866659540601d06041c4000594020308400c100802050840110303c1074158071a0090001007210041c1d00c022488507601540300030796139000300c04180081103042c000300750452004c480c10700000c44044002103504000d403410002d40115400d00d4021500c8a8042d2980418010070464464541091183c007950081c070040340014110700400503484800e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 119148498 1250 119147248 119147263
    0x3060f0603021905031306050103120806100516020a03050607021b04090b131119030203120f090105070c03020a090501031a15011d060f130b09010e0103050a0b0409050309010908 78
    0x70800f425031035460030f84107850607400035018600c801852079050b40480d8060203040c8c02140b0844450f0903410040038014608a0045d090f54070038001c56845282d000e6110f810780340c052840090310440509603200043c000580e81c1d10041085c010501004603c6070042060107400500c90490142228003400b0001141c100600042202c0421000304a800400c114140c00c41072040a0900c141599040001c2c0100d14031410701d14420007801d014800c60406010080c4c01d0005072200505045034501c00400d50b00400141d28108500440d80205014010008000458001d80503080f880c7d202d000e00070180100340010703111040d00c0b03296400c03400401c108461081c0b00e083c00040e02d154080004413040120b00f01c41001c40900f00d1040c9100c0d6841c107005000203422040304c4daa444c0341d40009c54090b103110f0751040d201d507181400005100d903000300f17402c01d4030107091800280035035650320078000a2400070b04013070700310780340c16803074800c015000008148040c0c098980c00d5609645101c1c041c2e440c0f91 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 119149748 1250 119148498 119148517
    0x62f1f0603021005090d02030f0105010617091203040804090507050d0c110d05031308030109020711100807031508060403020a0507120c050603130b040503070605060105040b03041203110a03060f060302 88
    0x70301003044031503944030742c0107440b68040041c8011403c6186c2e40000345803000915902000342d54400041180581114a500000f900c8010b0542d241c9021400c00351190b101404681140710700100150410002c68103c9001d440c030104e04020a0410384c2000705150001114080d44a01d4031404601160060022100d10f90300003004141080314400101d5407034101400e1040d0140c51038001800081c490130155003e482c60200050715804a410001801048100c84034002d039443c4c1034201d00d040d444545103034003045508000c1001018000c050703929003507070350100959002e914180001c15502184041d42103000d4011900d10949034810307011417451201c030003004030f100200204000c2c00c199015591064160b40d5900411400b80c55001654000716401c6686400008080d0700300f1007980309080c2c110a003031034031509040c00d20b41d0340403051002403c00f42c05074050701a4004139500c641c02120781c87c842c100406840d00d1034190090090040b81c00b54810511030f4031000303d8500c2c802e1007500c0407000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 119150998 1250 119149748 119149759
    0x2040b030703090203030c010f0f1d060103032f0a141612050c060301030c0807120f0602031f090e010506090c0a1202040e040c150804030207062f1f060302 68
    0x8481c008260300030801e054040f6054003090244142c0f0040070b00c16060880700c60b0b02d02292505144d01c6a100316528441c2031400c4081d991419a500780d8005a1581034a5150600714010000c0407202694050300c1d5009103c230f4001c030010b6441541c0c021400e81e40d140c1c4a5590340501c5a5a01c4080e40c0340e000000400e0b0901c3c0b0700d02d804002d5040d01143c02040d16000e201603d0703402c0d51841c08113903164826042625515900781041204040030040307400140031340c6007580111402c030b83c0e9404500d0b010b4074014210a402201064051000352002c407050480c5201161502d03680c1c0503880054191f14a17525155481c200c001102414240036080c03260508410281c0360600c103400640d142d02d0034110080034150b090101045100d905604140030714007540034040708615051941189072488241c0b00e04112485052000003500010b44405a031003d040c00c0000b04031020401540344000b10018604610000604240800102d90031141d09402c40101000c4040a00d40344203656082c4002074200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 119152248 1250 119150998 119151001
    0x12030507080c070206040b0406050309150c04060c02040b0d0b070905042307050c060403020a020406120c17030c060f0a060515030f0601210c08132f120105160302040b03 74
    0x2d24840144081d52005120a080035203500c100720040d0080c1d0440e001040b400800d2150402041084040f88104a4481211464110a61881401184100c00c14807000a031020115a55904409102d0b41c001d02a0180c0501606101c840b1002c191b1340703080400c10f05900490203040900810900440d210f07150031001541003000072080c04018042820003405000765078010300c080c0b0016018501a5004141a004500401044402641c401540c4010030309030340000600403251241101d0b00c601c00040340d240d010151a0452148041c0f101d0300b8025802002030521080341c08a0160551078801c02200d03807543c06206d0304440c4501c0a104c816010b200007107483c06c0c9602c41c035070301407810714180030030541803500c11802407a1850071106407034985040410843e0310a4000e940066040c10402d40303034030292501c80003030402e40481c0d011102c5101c140210440324400b100701249019000340441500301c1a014008d01055404a0050005400003544a8070a000381c5082c1e41c1e0340032005d0b00c6c1d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 119153498 1250 119152248 119152261
    0xf0609051f150c0203150405120a08040201030e0f03040b070c05031f0203090c0d051516050a08040f0c08060a0b03011a090916080c010801171f02040306090309031203050708 76
    0x507890711003082d02000780c1d0380c0082d00162814044010390201a1400300d02505041c5403407400c14142c03151038810804103008100107960b00492098019030203080003e022195000030034140200e0a044900c948400580080c2c441010001055514020b5105c918456150020142c440700380362404030b104549c01080c460440065030045070082c03400d6003114480b0404001040390040000c20680d011b0301f012280301c0385445952115030380322110395070305060010304280150940c0140300400d002c00c0f00c10b07030000e420402181c1c8004581c5800520004d102079a50703402c9542c1d0358007119140d100b5414440781500e00c0c141401000020320b076030110840800c0c01b100601c80e00e4880203006009600c201c00000c2640041c9a120801800600c0080d0942c50310301400903181c2481a809090507041600c04a41031080100da0482d08030000e010031139800d881c04440c2030103405280c20107017102d45070904034400c054102d0885021240701d0400500100a030b2441074013202d50459401012841410004d0034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 119154748 1250 119153498 119153519
    0x1050603010302220f050f0601140a0f02010b030604080a020f0a0b06060a02011d0d020d0806030622122624030a0602121807030c06051c0f0609051f 65
    0xa004110711001340030428001c0b090010f90320403061282d0354660703480911049150340c00006a01c24800e00b014810700305414480803003445105401e10400c20b9402d24400c8182c0700b90400510040001d0481300710b4142801d0664541e4012181480503205940e42d842003401301007290888650000b006035903656035401406160b038421180c240442d540e41074400f0000407107110705d201440c1e11500408042c48821030190ad4003007018620000e1184e06400c102481e0340010714240c0c402c3d01703001d9109500f8120040140b01c0403542e10000c200e08204a13015072000e52183c0310b02d0000c1d075022032035000601c15900000f98a08203a4001c6161000ca4001d0080c010b4080c802207071205000e01164401c2c6029103403a4100d0308100c400303801d02081340080c4421000c10182d03d840c0403096801410b00e031851551280a00051072061100b4440c010400034608841159080184407011380140020494070f071039200280302c9805001c10480c60080494803030048540b08000c5140c40024004001e801c0095103031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 119155998 1250 119154748 119154769
    0xd02150705040513111b060117060406150e07032f090d0203070f0308090307080f030301090b06070c0306020310150f03090c05040213030302060705070f030507020307080613030909020301050603010302 88
    0xf00c11030384503804517882101000040440a590a0882151201c1540c4050411038180c0c44090f140c1914442d031200a40c0c041107151704558000e90001c1d2180d182c2003088d0301031400781e001c1607003240c06200300b100b01501500516400041000e6400b070400140c8034407040e60211000008140d04140102d41c240d04010054186840c001800c035001c540c0d40380301080140415800490b04c8445c04140600346060422800b006050a04c029022440c542c81c05c01d0341d0303400140f003000f4000b40c80701d84c0903520f61140c5044800b483c0c2c106070045a2180c032424880043c0d8030686030540085044040000d0440f00f1180c01d00c203440c0c8550b500500002824022405004d15800c181d841c1001a0000140f80da15440100180301941e0b54222500d0320318200a400d081d4010907550a0107020044000052400090300000a60608045071039480d42d00210303281000b150040e09a9101d440c0500c54103001c1d5a00c00c0780d40a04c03a5440d100300e00d40b140c4150341030340801e01c02c050b0045802d0005100616001d5880d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 119157248 1250 119155998 119156029
    0xa0f03060e01060f26070518040f05010203070302030906060d0314220f06020d0918020f070f0b011802041805090307060c090302040614010f050a0207170d021507050405 74
    0x10800b41d48500348002c07240c0c1e0310b6000285c4901e000381c90342c900b80e174040c8410149802800180c1546480c040104840708006171032103040810800004040080f081400f0034650b820800840d180c3c0344c142009002580141c42e0452948180c07030000d11b10f071400810b01c03806e11b171f819501c800c0b4016648508603541d411215541c0c0c1104c0cfc40b14102c0358403441611007540144060354603034a4007860928003a092400b01e103480c0b402c00c00c2c0e0341c2c030912020040c041040020b0708404401a41e4401c1707040c203500c072409440001058059003204110074088200b0510303040c1d03584030031900b04607183d84080504030310861140c01c246402c0441d821044a1316540710700d0307000005e0b505503880c0402e41c3e0340750822149020500c6012a903000e1050040d418140300f200c02800a00f030040390102d0202001070030041c1100001030800400044045002e44240004d40045c400030f48503851440da958407044d16000820030a100511407142d55001d602001c0c07120341d0040c01c41c2c0d106d1a103810306140038869800860b4200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 119158498 1250 119157248 119157251
    0x6030a060f060305150103110108040809010c0f060203090607020c0f01120c05070b180d0c0503070b1008100902040e0115152a0201030b03030901020706050c0709050708070e0a0f03060e01 82
    0x3c042002400b01d2445803681007500d0400758110b2824141460040c0103842c1041500c40c02c00c4005400c0301e0071904030b444242007001c2c0d50800ca1070450000000c0460080204e8004428410030307c4000074494000c1c2ca0507000d490312900e20505001c40d80045040541c0000c800d101c1030003143d04c02d5070108007800000c1ca005031a00e0550380310844204820f86581111a41caa1038407807400c541440102c0600c8003503d41301843c000540c85a0b41e4a004010000c2c2c245140040401c40d903140c410000e40040c2661021344080800e0122480c0080c0800c0302c00fa03015a042400b91a00c01c2010302c0f84040541410054603511402c001c44040b0192004048000380b000c0803c02c40c00341c030780d9149041102401d00120402c40c4c070b20342c40010180e40515101034000e0307109002c0216aaa0040f650600340c0d0994503090303888200c954482443c000c3c5d20762200740028906414410704540c801d40403841102191034205001c0340701014094101258400e002000c1d100510038000a1034540060fa8800d00c00d000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 119159748 1250 119158498 119158511
    0x5090a03021504150203070b0f070903060510030203190204050c25050c0901141002070605040501110a08040915080318090408070c06020d0201060e060319170f12010503010506030a060f 81
    0x303a41c942c0c130301c082040350150f800424884100710100d0a0350354004c000d520900080d060029003e00410b195000081c0029150000100821080c061590046030020704071000b644881c0c441c07600c004025141a07000e5420032002039114000302d8200c2d089010103c812141240c4054000e11110101c4e0804460134003030006a01d80036038607140c0040c06000000451642114020100b0860b0304980b00b4000c159080040d041100380d804c90b0a44d02210310130b080003c0701c1c01c0001d4106041500c854801016004089030102e1009a142d0088904030f04090310204080e171620030480d80c0340220020002d1300107040c05265140d08015035010307003082c410210103041000c0340da1045a0301070f0a810000043e400080c88917070326a0309008200003451350021041c2203040000102f62503904880800350001444407550041210000c0007400b1a1b81d001c44440c4c8880014040c80d005501404100c40d41141d07020000c125480e040c4912806480002c005024401850741c074980078090148005402c1d42c0c0c0e814 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 119160998 1250 119159748 119159759
    0x5010807090b030c130501210c02030c03030f01060201050907080709110d020c0606040b040209150f0f040603020a0f0f050706050907050d05011d010506010824041b090605090a03021504 81
    0x400b550103a1300e007004064136403030680c06034a40300303095a002504201c0c0d1034145030241c0e000d0700b002d001403520110011030b0750020044242d1543c4990309640f07000c2c1c440001045400d08102001c20b0582d0b0207039009100c00d031200d00100d6a1188280a032001907006501c0070003012146520061962a50340081400d0419903180c0004036040810b401d8100c1e0801c800300461417429200c0c2050924080340d046091840302001700ba5417114404003c42c243c01e000405d20700b500c0010069403030720100161501d5440b034403400020040d42141c092a408102c040f204050541c1c014042a001c8211a076a1513042c08800d4803490003502001c0e1060700b9900400002090503100c910110710440d000c0c40010904103008072005610305031001910341a645032000703204050703074418900c41e00b050110080a0701101e10bd8100c41a468180040702d81c80392800c114001e100014503180070149600e170300c40700070341603071010244c860388941101e55520050200c1d060005140801030141246103500b40e150805032a507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 119162248 1250 119160998 119161019
    0x6191806180501051b0d02030901020706050907060e030a11100905060307020102120a02040b040611030c1902030d0905210c0913050f031603050a0c020d060507270501080709 76
    0x9440e075500c9200140c8a4060010901550780c200c05003111103006203064240e883c1c2140501d81000e00b003e5000400b1540102007501614400c03500f0030000c001c4c03814081401c550b194a24400c070804a0300700440081c8038500401c40840307140d0001010594186002d0401032032002ca200242c040c0f1010b0000452181c55150145125140c7ca0700010f0ba07862124014008110300203104e54000d0707004000c00d11030340c4041b4040d40d080360b4039030401c1c14240040000260442c0070b628a41e4103e4810301c841e1b110b1407000b440c160700440d8005d500350b8a80c0c81c070400b03003202da0307624034020143c001d8440021964401e5409104241c6c40c0070301401c0e00d44441980b000a001000c0c00d84048040180d030b00e60100c24003030280a0325041c640d800008614200b0100034010306a440c112000e000d1203004515484100e0003400329001c80c1c0e5000302455880b100e030f403404400605080d03030200005031500d2858680314030308140840e0001c8200c11240401c80c5040700446500000505600070004d0106c00092481540c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 119163498 1250 119162248 119162261
    0x90307140c0114040302150f040e04230a12180305190203070f120209061c060c0801080106060e10170a020702040c0302030114190b070b010305010c0206191806 70
    0x3000c0501089020000010712010761103e18203a02c4404100c01c00040c0d403549461001c03001c80110003600c03050040040b1619001c2c4d40d124280c0b51284600b08004c0103020003a03030025071401e00c02c0b14264501c0da0003840e9142c144600091000b090642070000c22401150982c0d030079a0541c0681140584a0380c4080c2004111130702041201491f500308011072400b4040c2c41c2c0581108840848020310304103419001044016010b07003d0301404003c076500c2c0e19000c2c0244c1d2001074050900f048654140340c4400101f020b405128002a40070002242e41c48060080500f121401e5440d42c882c14132003c10810705406040c0200d00b8404058900442c602981e40d0043c0315a0010400580399007060060100303461200b08070b141050f10420042c814215611800b80c2900c000780c074803404801d01c41601c1200c207111074001180a0101041103001c212a20070b4103810313203100308028002c41c180840146c1e034a44045e40c130f862881c045030b81c00780d00e00901648103d50088010f2056640c0e803007141c41d42400c5860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 119164748 1250 119163498 119163533
    0x4140a030e130903051204020102191b170703020f0a0906060801030b01080303061509010e190f0503010b060f070303111207030c020d0519090915060206070c0f0b090307 74
    0x3110319a0700902d0a030031082071010109505000d100c0003550020910700c02c2d80d82181c0c0c102007120103d015039100b0001c0c1c03405240350780403649200d0810305000b02c0032020121389407041c0c0c19143d00800c03070682d0548907803070001602c0028411035040d64204482d00100c101016040658034000080c800c10034043c42c002040a52503452495046052200310704105820aaa90f60720410a001c69070302d0711003a00c200700c26859080c90b00c031000c0300c0040b0341c02e0781c05138259070b8407a0512502d180018140c1d00250221880188011b4410380da40d01450300340e0354200071556101e0b40512006090084040040c0081072192400003845000907030f1165068003d01e40f446c000c61080000c000115400d0711403d40b01d00300b43d000a011a80705200010b143e4881c3c01c0c4504454060b101c41c20042501500c0c12001802ca0a0001c0c400c030101c815060b138a5400500c074546c0180b081c90049000103014943c984079454000c008006c8900b01038490702039488001d81440d501d407100b004150046030340a500c1c95400d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 119165998 1250 119164748 119164757
    0x607080f03151009031703040318060509030f07030203030d0e030c0f0a02040c08060d02060d060b0409090c1d010e070c0f050714031524060a020304050a0b090607060504140a03 77
    0x100903040c40846690141000c0504c0a2507400303001041041115502500c500100a50b40303030f55902d42141d150490061030f521a4000900c0843c2c9550498081c04403580b0586c102c90b041c082807840b41e80c0d61055484042d4144c1c0040011819640f02c2da045140200306810489240c58004900c562600300d0166225505421011040c011072516000f0a1441041d901d040070721810b2030343c002104101d001000a2060b07400003810609411903030050b40040c81c0c010100380c1c6a554501010f006061540000c8844102c07100011403802114001c0c585c0300c40c1c0b40b40400031981e080c4001c3c10341406000e0441c2090001c00010100000c1011170f50051b4244620040c000e01481c080b15900d10244035080305100360041c0c1041080c10b080d00c001c00e27501540482e48500d0103088110200c17402c0388040d0055030084000562213502540010041003114400d0700c0d04403500f542c415920005018a0311500d030721035070030080c0303402142c400d402140e0860700903042c0201c0c0754008a040e900d095090300040300805e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 119167248 1250 119165998 119166031
    0x3080403030b0402190c0507091401290403060b030a0803130b0702071d0a09050604030914040204242c0102061311091e250c0308060607080f03 63
    0x1552602a0602d02c03402640c065003850b00151110713040125016000f020440b4040904040c80700400c00e1100620000100b00444400e0a1802104010902401c117a45210030300d0182c110718600d18080800b1071070100781d810039013107036070b850050b00d908600c259051182c044c0070b00114554000541c042c121146401092100d64a40005840b02c001c1c184030039900001800c21540c0c02c0d03503224030001200e81c025031001d80c1d100c286000080c151060003400c40d20524042004064001180c10142c0c2d51010a0b0012428250108401e81c4228001c1e0344c400c5005540d81002281c054050055040b03681c100079100300c1380a0350f01440f0030701c4410000042c00340804244c0465070188581900002c115403c42c076103000d41e80310001051a21150301d03005482000008403040c92282c0540b08680f0344604159480c10082c1414000d05e00c8a220182141c0d551403403565064018020030217400e80c0f50311100aa03580d10002c0151942040d0401e5402d940200040b40707007002e0300c80045214190401083c00b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 119168498 1250 119167248 119167253
    0x40c0312030e15060312070203010e06040605040302060f090312090c100f09082a01050f19110a0b04170702030102070b010306200f03060f0d140c180c18030703030804 73
    0x1400054002038600c40030201c00d001c940c0e05c002c581480c091089610103561842e191011030300404039050b046081d805014240300400855030042400f840c000e900f12001c58495003006d948040c07083d168030b10b60b0f138001c1041c40e000141c103288959000540105690080500001141c525140c090071040001c0c044900c007107003250089a110013601d850b500070009060070142a044201480030540c0c4944450303103852510740c0c400e00c11608251280c10950b40ca03807a900583c500007000e901020004100d8080f0b55402d0024005401003255401400642564403030f031711904501d065407200b8050f0090100001c0b000350700c00340014010f4521401d0464003540c594101001110200c009000d0301c031022102105004544005035240510760f191403540c1da0b00e861002a4226003030344c0845400c0015111450180450036482005000b5480141d400041865003004241c003444209401075201c088045064100c0c0040a44400c40d501000707100103000b4000081d01c0d150780c5600440004003d80100000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 119169748 1250 119168498 119168503
    0x21c0510060807050f0a0506130801110910110c030d0c050618030712030b12010b0f060a02030d0902030709021909050402043b0c0703030e0309030703020603040c0312030e 75
    0x282503280e100c08001d480d00344aa0340d81c54118911a0174031400303a2400e603064070395030f0401c02e400138600240681c2e540d0460004c072050b881c0e15807007580d1045d440c00c00000c8801581c3c5003101c1102d00d00600601600202c0c040543c0c10420091162113940f05060040c00b041e1420401c2565441c0ca0392108940070035140b0348149172910092194030303000b0f003824081d04c49800c00020348010035030008000c00503c0b0706940440c010b1a8000c2c046038443e107602c0d418900000d040d4000032561409a030481c8180c411b900c14000b0a100e100c080c100180c0c420082d40d021000c041d03115034070051008080e194134a540301002400c3e60400c90343d0980d010f01c20b411420450f50000110001488240c4080d07050900c4d040d200c200807060a900c411950f4401c51118950200c00d0f43c10300703c00440024124580d081c54403000d000b5410075041240441e2920500070110788001083c4e03021000300500404100d4150784c203000c015003000c0c000f184d40c09410403000c0001202502d0020840e0125500058400d034150525807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 119170998 1250 119169748 119169763
    0x222110c07080f07060503091906061d01030308061e040515120d02032a0a12170c04090e0307060c02010b0f04050f07110703020d0506071419080a09021c05 68
    0x80c007540083c0440250000c0410300b04201d980ca414203d403255259254075040c0403c0090764401682e90400c0002046500d0b403042c819614070307240140c032145c241d00e02119110310a000190114010000041980c5030140b4018118031a0038418504045540c004c542a50010b903030400c0780c0001090303250681e09080c5090800000c03d03000801000c440188084d4481c441c900c0507842001d50a009224a1032403035078a8404403c0600840f9400340590030700150f010281010200010100320244800607491030305940103104403401903180c6464099407100400700401c446190740424481c54001c14039503c650751240140e60004074401080d1410410545c5010710300601c50351900c800c1c04410400840309503401056818000f90301070858500da03203045000c0d44000e50110003081184104900400c1090240040d902c6c0d160f2043c0120742c00308a1030040d8140c004460303c1c07041a0010aa10034135070aa0802a8014001488900740d0081402c10072400081c00300098400303046800c2020401c103c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 119172248 1250 119170998 119171009
    0x20307060f1d060c0d0b0f1906020708010b01021b01090e090f01050a02070305161509080405030105010906030818040f020c030702030d09051e180127020a09030222110c07 75
    0x10001441c0c40c0113a031131280144055444041c3e511000c86200740c4130505642c01105009141081e0355042400c44c4441e6600b03401003400601072072200003641101402013503c900b005030040c4c07051001803108180c00741046c54141e4100030b050380340020001a90103c142c003813000d1401900071050000401c5082d01c0001c2c0c55a42c00a10400c858000320340c5c0f0205903000c8211a040d000350340740003420880e03d05401c1e0030342051030385d1900c40100d0800c400c05000780304035a0198024003032030f0390740c40c2e0a034112607840c40080c10880c0c003000102c1c000d8a0002600000704c02c000d00015811890840c40022600b02107421041d680c800900b000a40c54100070001241045141c0000c04a04003404270341c6a4a0740c5000092500d04e80f00d008031241d03195440424000c03001f01480d403056075108040400503100010079101041c40c213a6031100d08015008641d1284540c3d115401c4c8145107070b09000204c0342617a40450310844068541040d5001c0c0c4c02000429900030a0042e181c0610f8035203e8204502e07640700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 119173498 1250 119172248 119172253
    0xf0212090a0312030b040203132a15141803010b04110906071a07090312050c0607050904020c120307090e01030b0604090c0f0b030106080f060109030210020307060f1d 73
    0x40e42090362000715010580390300c5400040c000e01100029009415064052580540080100100000000a1030b0f0001b4040c42000d02459042c1101400d41040c101c481518110b10010a016000c10000300900c8080c4524100c01411524600c1c4496038109501d0403070001e903001d0b004200c0340f509001d074070049142240c0c100a03d80410000c00c00da8030031044c0250088070f001c1138003018404002035100c114085c4075210451442c0c540c42c014000e10346ca01080707410a040c24101c003806172181c1d0545072410010002800e0b51f46070801c0694071900080b072603d0b403040d000c0140f0840020180030001090241c0d03882a500e07410641400f4084110542059032030b2600040100081803190580e039420100607200024416031701e04040b0680105900100c08101160000280c41420040198101d44580d80e841080352201c00c4031141c0e07a84142d80d0f06e4005a03210000b4005443c2038441d58a00000038011240b501000d681c0340c10941c0c62001e00070b1038403944e8001000f64051307085228400c0a01c41c401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 119174748 1250 119173498 119173507
    0x703091104020a090302040f150f09060b030723070203100f0f0207020604030f0221060703150303080f06013e0d021b03070302090108160f050a0605180a03030f0212 72
    0x200410801143c80082e01c9242c03100301984500401d5402884800902440422690b84540c4056074102b124401e0324069898008000703a81031090042e42e0158801741d5852020002c0d50940454420403000c400100c4c400412210b0016601000401301204041d80c0200e85001d558008c642102c0c81e605c1d0307054005004001c8540141d032800300f19402d50b90302a9020401e4202400820303c400704a81d400342d03d2040880f02100d003241d0019809102e100650b809020402c40d00111040c0070032107200042c04100341d98081550800c40c200319070750106042c07402c900a8240040620603101e803c2d90800901a407084035819009100509800c0c0781c0b14400041c01b2100703003d10001d40d0307034851020814404550710b043c03001d56034080c419000103580041820205507190070016031a0944841561490640900001201507140081508448000709031104851804105032020340c044144500d40c410301e20940c644030307640d208104010f075000c0c2c0d83d80210b2750350045c0e01a01d49000b01da1031100790b020501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 119175998 1250 119174748 119174767
    0xb0a2003030621030f07030801030c05040219050706240f08010608060f04051519180503180604030203010903080f0702071202010e06120403050c07050f09040b090a0803070309110402 80
    0x122854180780b41030700c003c0c60340e0400038442400c5000382150030303100100c0011990300345507000b04828141c1e40076481600d4101d070744200700401c9100c0c9042c81c40c00c040402c0c0c1c81001c1070703004002a00030a03000301001310f15488070000318905001c2480c041820405021000e00c88070014080c60005099888001c000b41c0b41004d404c80c0d41c401d4018581f14251008400003000c111083c404204070b18056a82058241800c41c0609588051420006800c07442d20046080c003003440d032112000213800101652400d91091420706d0981065800710f5001038081000100581342440386000e03040c060394810713403c2d007001010030f044408050091021035000d40d5090180c8120518070800071942403c007010244003610100c0c0f0b06005054503160300c552002c0401084c141c01c0340040c03c0700d810800503900f1507600c4108202c503503a0744a00581d0480b00c1400010b00103081c40d001c0c035411a8180b81101d00c9518507035550000e5601c11602c1c00002a21540340000708612200c2c044131065040301c0550908441c031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 119177248 1250 119175998 119176009
    0xe150c0327030307080117010c080105100e060d0b01020c09070206011509210201270b030a0b150a022b03110d230702070e011e0b0a20030306 62
    0x340a000c54144050840c0089030028992100e00c4803141d4241d07501c034a400c180151182e5001d11031031501d103501c036800340000036041c814a801c0c250740c3d40300e00519909020510124804048668050024074003803030402d60750708006409825a10800031402c190040002814043d04501c418019244d0000348184c003900400c1082c196203a07500700b06c520080c162811218110183e00c094514094102032410000310ba6440102ca00d00070380f2040e854401b40050040e80d0703907481e86103185000d0115820312034903030741000564204140c41070200d0022092400221503212080c501203a01e2400a40e06004940500015200200c5c0d032402c11000f2452000440c9c8401d80c0c901500d0825940d5803049070400000c40c1a520a03800a10080004040c4052001500760305d04e4481041102d851001801451001804009544042a8903005a46450b030a501c2140d00c0c84040c2120110605002c04d40d014824081d03e8013205075969410002c0c070f5681c1e90004d010164150f10b06036041041040160340740c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 119178498 1250 119177248 119177251
    0x6060c05070e04030e06030a090c081c0302070204090503130e0109140403082a07050f0105010b160503042309061e060c1221070c050a080a0309150e150c03 68
    0x14400310000c0e035503c525089030f4a040054446a10000c003000303100b12401b45602484100f442188662112a11048138980d0380340910f200f01240240e524000040780d100b500505081d61010b44003051101f40c6076038142c156004032144140c0c802c29503c04001001444a030039004280c0040e082125641c1281048548540140050240184080452505920503140b0012a40310a02c280c1c080600d070103029440b54030400c42541c80d4422040100450b9030188115030407903040b40b03072030740ca4501c3c08551090002c40e01c0d9020f441300e0205001c0041c444640071014034103600b000c0703035001002503440100031091901401a5014085419800301034062402c440704a11000700e030015156080c2002d04c91070078241030f00c20300c080580881e00a40c2214282040f1824100d01c5c440300a8582e10808d00701c0b2412207000e40504141d20140404021a44100c001c0100030b001d45400316104e5550740741c5200c03000c401044c04104542d20100396413a084240901d041d000d0950200380c540c0c1c00e1425880c401c6010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 119179748 1250 119178498 119178509
    0x3220b010504021803120418051012020102070305010516090603090203070501110102090d0f0201030501051804081b03070f0309050103111c021e090103050105010801150e030309060d060906060c0507 87
    0x3400544000e0003a5040c4c1840380c110001000c07685070308446c04c80b40000fa000741c840c16490244000b0b8464004120b402298454441564600c00b4280360040703086007110020b50a0703055001e03561000c0041082070045602c540c0ca030b402d020030311184010005083d00140d511440800d450a03410800598000c0303a5902224001d10f00b804680070310707500745402881a491034a40c4900c3c44001201045000e21074801c88600076201003007075030384ea078041c8035540d09049001e00c46120441e001400103029080a803071140901000c0100903042490b4030340c070f5a440504151000d5423844034101c20540d105180401406c0c00b860184260404880454014024010012400709070011003502d221101c2d41903440341c000b442c003400c4411201814801c27569000c4241c15001030b08017400803070710754040c3c0b05440c126820006400c42e04c040c0818111400c2c0c0342c4c149941d0389800304100f090700607030f2001d016196003201c0c0c4030005034052400305038004407030140d488070061291051141c03022541c040303a405e0880c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119180998 1250 119179748 119179751
    0x81e0d080907080a11090609010302010909150e04050c030d0e06090f040902151803060103030c060207030903021504090f11190509060f0a110109120c05070e0103060203220b010504 79
    0x22900101079040a07180d4101285070320030000307000288000400b612a2007502550301038040e850b842e0900c040f09800f40400380c041108134400700810b8296030300c1005c58000c0a0101051030781c0f0fa002c00c012207941521f05a51a07440040320781070914041c8485400c815060608100218189001c5090b5020b00c104443c481c48804010307a40645841e0080307a04035070300511a40480e542880340d89215040078084a581011030650050030303050011f4510f043c0c0c0c1d0161115002106265182d41c06940405022030400c41903403800401612000c0400ca042c2001c042c400b9111410000a602182d10821003408210300b0b0003a41031038030140c9070880300407546100c4c0800100d00d02ea034081d03072144140c52060790004800910031115020340f90103041e000303450780e540036030360b42a11040354207071000ca0101901c0281e00b418403c00060083c3c0c42c400c1800e1054050b01c0c2041c2d9584040001080240c2c010b6500c1c58000041101400d60040c122052200f400700604c000d040716242c2c820801414091140541e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119182248 1250 119180998 119181001
    0x60702060f0307030903090807030203060a05041110020609210306010c05070b0d0614031b06032d07030c02060702031c0204050d210903050c13090c0f081e0d08 70
    0x645030002210404160704a03400d0307903428142d4009004003040716066001400c40c0001203840313080401c416003100d4000740106a41c0d00c074000d90000408026100f124150b900d1240c02080741c85032017004c44506501d0700603107031350315240312000d040034032494644000380910b0070b0880285d590b51050701d421071000e2901c041c0840351464114a0410f20b40c00414007040c0c0400c400340380c01040d4201000b660345002d19606049c1505050555440403550b029442c9468250582e045007441805964041d20480c1c10f5000c11045c0aa80920024500040c8100508190400400e0b90309400390701094161403000740300c6032400c1c8000a40324003400710010000080a820742d8072101d4503070103403000360400074403940d1b4456140c5891748a05085841c04d1000da07606d513040b0814140920f803540202d0b03800002503d907460700c00d82009041c030050b121a20720b160342e403e403200c081040c10a400000d4180500320311241030034101c800345072032904d441140002528010302d201c07031400419940c80d010003908248078035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119183498 1250 119182248 119182253
    0x2010203040512060a0f0c020c100339020604020d060504030c210e120d03020c0a0b090d0e040b0a0303080402010c050d0e01030b03160b0a0509030303040803220c050607 74
    0x3944502e0740080e41c400303014000f280d6000004541c10f40541035032001040f003c0e5007089980e0645010400e21400741c0c10550030321285007406500302644640615000842114031010b401c03030007900e00c190f182c1c7e0501c101d03c00840d184040102e00030104090004140b40d2501e540000c24501c003003c0e005140b246c61f200414200741c0034415048889a20080c03a5120044150b8030801d400a00301d11302d40080d11501000c01e0728140892185480e01e045030103890240d8800340c096000c0d5200d901d02d04800c1c881e032080e800c0456a1080028020480303400503202c02d021400d80102003014280c1914410b9103000c26907003a507510101c881003125414140b0031002d5540f800140c603441103020000e0b0a901907010f41c80e07003059120711009064a000d80b002c000101405061640d40d120140b0030045011000c1e1f800e2040300072400141c1581075a0b4078100d4585070b00900031034115003040d101251500408010310181c0009003249900000005148084803241900d60303040c50342403885014000c650010707940b0309 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119184748 1250 119183498 119183503
    0x105130306090f050c121c0e100522061704151401061403040807030509120d0c0209010905280f0e0606031203040312052203080106081008060c07020102 67
    0x40d40c201004000040b00307803c0068100080308811921809185616101032500118043d0907050030300041c04200e0b070315013811140700d00f02d41c500401e0000f01c0500311481da4500d40c095980500b81c0c6e40fa292280900e040c0d60070119500000d4040c5000c2c114018011203910146240c0b00d40303001d4152115603155810100ca01503a5122115029418140014550385498001e00d049801c207564001441e2051140030359580000e543c000c154060811801c00030034403d001404169000074100310110400e00d400310f150195200c8448041a11620540c0070340c07500e41c880320f00503c01c0c101c092109180820401042c6245040f00031200b07003504100e1001c1700305540c4541c0384503c14401c100500032101c6452035032401c0c21618203209200b09002024200c0701d9000380c1f8040c1d589521050401c100300e1a8160282c90001d040e900885040c100c0d44052001c2c00c3d007807030b400781d00039200c500341941044001800c5040003008514a81038409017041660780c0054520741c040780120328a40c0316815440100d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119185998 1250 119184748 119184787
    0x1d04020d0908070b06030601080a0302030912120d0f060b0309100e031308060603010515010801031212060b0d0615020703030305101a04081507082206021b070b0f090105 74
    0xb030440c2000300b1460200300c900d0031918081d440407005c6170003c0c3c0c4e1380d0340700540c0e9418120300100180c200b0710040105003000e2080740c00030b04100c000d850040c1308201d507001550308043e2440728190749802c0d0710700c0421140c1c4594006000142c6101f441d44c540301c01c100795207001004117038003890f949403204284080e0900035102d605039210301c04125155030326019640c80310240c0b45c0c14425484d20010030715000e0040d201240c00740040c3c480e03032040ea00e5502d0b914500b601010000050012000f10000017a100c1e124510180401c140b41c2512010302c460080102c46c25031700808080301030706200e4500c0540000c4c1100c2200e9040c50040345903981d0100490380d000140d40051490a804a0b88101c1900008064000d5440e501c0440b02c00d4030000c00380c4000a103058900c400400e0024003c02d80c07034210150141c074610001d01031600b2120799513032401d0407031740f00c65000108454a542c10122483e000e12900000b010034000360b03408c0c104100602c03402c0348142562141801000140d802c1c12058030f10020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119187248 1250 119185998 119186003
    0x91205221e080607080c07050a020d06020301061701030b0a0f0207060e0312150a090e03091e0f0405101e0e0702011a03010509070603050717011e061d04020d09 70
    0x140e4003503603507401071019240841d00049040c12003075004a4070100004241e403050146a40b5a922a1a25481e41c1d4142c2c2c01207100750748900a02c0310301c0700544c80d00302c007070702e23509200341001a62585000c0d00103100c140c0c06c1608003100c002540042012400703003504d050704211008000290800481d4081d4001d02c11039000520003820b20890494601020014001c02c44c5020f013103e44603070350041640c840b84d800001642d40301c8002d680501101400c1e038451034640c1c107441c0031249400401000038005010030760355445002410a403010040c28039400703449014006079414000790914440810b09100c0e207025519407404041c510001688400800400504462002c5c60741404c00f090003e01a000f4024442941c20815100344003608051241601c92890100039110107400c2a100310042d12000e440748007044050545003560245100c1050b0091030180008a10742044807000c0095040325807000041c0100741002682c2e4520071610590030800031140103030b640509424a40041403101c202 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119188498 1250 119187248 119187307
    0x13020307201e1c051603080a14040b010303110f0a0b22200d0302030a0c020a05130b030609010b03070308130e010b030712050108030d0f0b0301020c061009091205 71
    0x8000b100401040a60040d09015001c1d400e2611841e42500e242c41010040d000100d034408000d400f292003400c015030411803c1c00081605601c0d09080100c44006907019601035102c01c004008140d0482c000744e00011144014240c864031002c207194403012450005481008a5000211410425070614200710300e80ca0b02484822881d00f018010b0ba1500c904e82c3c4800c1c417202c4c5003840180b41c04500840311582c9035004503d03241b44010126842000c00800704e800134902c001c04540c03580e446918000c0c15103038080015880c0e0385001094644000549030700c4060349824050384076070b113010403a482a20b0b0000c40701070740d5a11121085036414480d900000914002200101d5002001401940900203550303400c04807542001e40c05003154028480c03920b0540c020001100074608680150941c000c007040006010072505011900f660311442c1d200307610b40c000c00704010008111102c510090001d18104100c0c098081d0750b4402000c08003400b00d414004003040c0d501c01d41d4142d5605000300881c000c3c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119189748 1250 119188498 119188543
    0x60a03050a0c090506010507151503020a1d0a020c1507020309030105010f06020c10081308070b1501260c09030a050f100617032a0703111302030720 65
    0x1807000c00e4803850f004034903440d41004081800d6612074002d81d0b0a0705d0300050000701070f050558064004100c1403501441c00b140003d8004056611200b0b010018812000d088090044c0070304010040b0000900501c0b5181c0b06205580d80002e0004240c2d540040a00312201c2c05c2d295030a06034514010402c134035030b042d030801d000480c003080d540000d45c080700c4003502154503041001e8200203034162080c0040340096500000100c1611400d91b600c10400e006095540c90000240ca69410510007120640c4034400007050760706132540d1050395445151045c0b0010140d201200c00304920404000d40000605040400c950326969401c2c031035150000c0d40401240d0088602000d210b454106400c88030001c140380000010310b501403600095501d00d40075000d1483d1888050354048504502c2010b40120406a442828440002c110801c0a1030068505201d081540c004100003090144c0f18032100394010f0080c0114141c124090b4030440a501514007140240b0010352803400721902d1082840702e1a818 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119190998 1250 119189748 119189753
    0x1b040b04031217070810030c14091006120527060103110607020d12050f030f09010f0605060304170f1219050c0a0302030c1b0d020d090b070b060a03050a 67
    0x410880388640203451501100c080d007550464015240207078400c040c0400250031320721414035981d00282422081d4200d64032515204007010154000048102440410300c19600e041180664030003590765903a40c800d801c090f0004c080d15040649030041135151800b0440d078080350204401c10f41c00c4c20b917811750400c25664610b03980d200c081c84203460300c43c540c039206241400d280c8104d4001d00e801900286024100380d4519003103118400308103003040814040e80311741e02074400003940200200d0b40f580748903092001c1d5190840d1414400304960b64501001049551180004e80382e002d504200c40100c2d4659000840f00507204000d003001d0300f03560005400c01e841070340d08690390040150f611495801e10800f484942221801e40d02c0240040d401d01000f400e140c130a80080d948003201202240c10502d02409903004140e4840300258180c00440070044c0300c03a81000a485134011524004a0740761915442c86154450100f004d04243d0140d00051010384070741c0d00000003144e20408a07484d40301e060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119192248 1250 119190998 119191019
    0x903060c09051c02010e04020310030b09100603030908070f0303140a12020d090c0806060a03120e03010501030c0305150601080a0f1401031b06030e0309010e01020a050d020318190e1b04 81
    0x20f01d0101c0c04280c42c2c0c850243c840c1014420359201b03001d82e00c0084c0d005821030300c2d40782c4409001080b00d80c0901c070750045400340d2107141c0240310046101f5141e0202c02e0f41031403181c50074109542c0002c0c201600b81c0d6000c00100e5449041040c6000c094150b4694408040c02d085030360700200f0800408081c000070f03e81d40742c2803995000034240b034040c0503e40512500c405030103407542d800b07598099000900302d005202023001068a80004016420101c40c21809000482d0035500c0907401030340c1401c0200f2080040c00380038000c0340b481840340c828402170ae103003400010b000c20070003811880003a681c980c0c6040400e16650300075800c00851030728020984da501d18012010075082c280d2203005c0900090002400c84c00381c0201692614150080c500f0f1602d10341c01162003a00814000e41140706890800021903c1408030a83d0403049601a6541d0118288000e251046c1081c1150080050002071403c2c02910096407044e11100345011000c0d1b01d80288805030001d07094090103940034000b8000070300840c00e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119193498 1250 119192248 119192299
    0x3070f03020c040c03110a05250501060603050702060708070810030b0c04030203010605060307050403022b06050f070906090506030414160501022118011e02060a0b100903060c0905 79
    0x2101c0c00d00130000c920000b20140e61040c20420300100060020f24051030044014200034030140b07600e1604102e0541079030f164044141810f942e80c0e59144020301c0404e607d4002c490344800c0741d000400f002d0800182c02412500014846c80c200580032010602c00c0200e5100140110f0f00005441c01500b071211580d0325640c41032108900c00d40c0b9044002840d07090080c1603e02c05c00c0d058550505003460f540034400d03841048a01070400c000710303c6600700108030000303060540501400c40000c1c42e207000203949420882c00f038411024454204000c00c00942e00800e254103481c8207854003900c0707807154948030700300f1008400c2d035400500844210880060320400c040085810903401c0310b2000065130300c0352051141000c200d0b0f8016104200da604030083c0e08001840c101c0040c9003000d01e00c001300c0900820308510b28029401600100c1c00e104500c03001e80a210b01c013510417507864a00760700070240507190300021b1200411040c1c45183c900c0c0030a0040310304000a10b00500070ba0541d40b84588100d0031841c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119194748 1250 119193498 119193523
    0xb03010204090b09100303020613030309020a03030302031801060b1b0c311422081804060905060102190521070308240d050705061305030d020a020d03030b0303070f0302 74
    0xc0c00000175203500340090028200c98158014104a48441c0301e03180062450741000d500385900c0713090810060720383c3c004990045000303603001600c0e400c0102001d08603148002000610340c1c1401d03010301010162030300302d40c80581443d0092100c041902c4005042101d507041d40c0398846407050912500060441c0d031506880814207440c40d8001c2e203940c200048078002601050704c5080c13500011041050300e45101d05035684901614a441c0c510741d958a100c1d800010211440010001405114100340c018035000c0c15101c1e20901031480e051000035030b0781c41182d46d208004649605540c0c2170010038000703800032800a84ec404070b080b1410400038000c1d40500401c44c000346907240014007200c0c82c030300b902c3c40082103803026081c040840400c00c0482245440140e90300d0003601c40c001001ea0310000246201c01c0300f440b042607000d282404050510310051088070a54024210550043c0c2d00c0106004c59164141000550064074401080c518000c4e200c00170850b40c64104900240741c1c000550f0510340740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119195998 1250 119194748 119194759
    0x60506090f0f060621010f090b0303030903030c07020d0c120c060314010b0a031d0a0506060a0608060409030302090d0620071a06030109020a030303020307080a05090d120b03010204090b 81
    0x8a5400000c1840141120030700910b900d64404034490385042001410800501c00c1c046007028849044600e503100d01303920140311000042020031050460740a100c03100d001c11005103080d03107044004691a484001c1004c49510390008040c42150754064400c00c0e80c5801c8400c4842403a150448a5102d540805094812041072603001500b20320a0040044c10450781400414a9280002810700c0347c10400402c0f05140d12039034130740d014185100010119400754401015804100d06140e410400f000d0907031400341440760f0041c890203030400d8066030000020b51b00013074206c055041c200e0080c012000c80740c0c1c0c44010201c1800a0108942004041d00705c400301c14801c400030f546408001e40305a00f4010041c40e45008003010940543c07107800d601c8600540081303010540c1d540000c0151685030801c8000c603030b000c418080080c1d44848116131200d1805020046820050452076581044440e000e0420034240d8a50881c508142c0140c904024060003c4d9102c2d5240c1a00700090007420b41c0c490b0044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119197248 1250 119195998 119196001
    0x30b090102041d04081e0d0903090306110306060703050904180f0c0e090a060e0f060103081804060605040e0402131b0809030307080103020907020c0d0803010e09070303050a0309140a06050609 84
    0x151a2288014007565000da560391911602031003d1010210b06040715a4500381404081f00300100d0b03004400304188282d48903a1600d0842c41c3c2142166900f05219000312414410494540c45000442d00403a030942402615003003c0c41c0014003400d0030040000501000c6410582000307080c42540b140280301e006000c50440c0c8402707850404041c00c9800d000b50350701c01d10040000c100303e58400c0298a4413641031f50007a120401d41039203000f00aa100b2940c00c5070015031000c04900e104041e0014000c2110705010701e62410600034424040ca01840003045042000703c1e0841d0349000d603c01c00900203090070300c030070f03100000c510340348841444118000c2000e42000980703030a00031044a00c911502d46402e401c136400d5800b840010b040050605081d13225020b10a08655103d0a11540320ba100c1d100351a41d070360504464460003500504020480d5002c80c3d010b20003c0e03000019603a44407514500025600f030ac5080049503030710713481e0f41c0820500035200e02d0b500b80f01242c0c00482c402c54041c0c0c0c01c000076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119198498 1250 119197248 119197289
    0x80d020a0e041a0a052107120312150302150904050a0b010909050c0f0a02030f03090703110306070c12050d020f0403020405070519030b040902040507020a0516080c12010204030b09010204 82
    0x10a0b2003c2110791007a01224180014581401c1000c614030440d80300c0407154590403a06480d180710354202d0b038200c0074110340004c01c15621180841000d034101c80300384110080c0325000400511781d800001d02c0342c40403009101c0e00181a46c195501d0344002072040c4482e013010340c01e800c01009040317041c1d80000c201c0440400d001005002d000c0c094841306001d61b20307042c5824000d40c80c03900050071030b4045000401c440040d060a0001079406504100003405105241d4a03081000304d00d020b070094042c2d0817040c00c00440c2c0b90040b0441c4035283d085440e1803078103204200d00716124481c5816000301c40d403001c5582500d00034100c0280c0180c0e882901c2c00c0080d030b22440c1d820380303031805490703851409120500c00c0b000780c1a1003504942c64600e000f070004903a040e070301e90008007582c900700c400400580c49a0400010300c0001c00c440b5101b07d010791011301e170f41c1c2d0030410101c0d200c0f08041541409405100c40d040b00f1a4800d60454001f560001001002424142d4110380130754000e00c51940f6a926a0040030354 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119199748 1250 119198498 119198531
    0x2503020106081506040207030c05030a03050f160c030e030c0d050114070e03070605071a0c0901030501060e010c140304031406151009092406020f061305070e04080d020a0e04 76
    0x2684241000881a00d903200d07403c204c080d5101f094101c017044286240b20002600030000f400d80d040e025103010132076103801c1c1c540e00704c035440c01086880d10441c0c400c07920b140340d504050003454042c3c0525019006e404400c002c0ba26112031300d1212600400078960707000c20701c041940114400035080900406980f20400215014009190f140303038990006d100c01c10034180208000c0800521600c007500003582110000c02c2d20100c01c4414206070000060403920740d41c0e0500c511805481142024200c041b002400240f1039110003000810035054aa20308800400800503900203590007048084550b41c001c400c540c480c0740a40d0000311003180190f14400c549000f51070310b025801c044d9a6a8041490039102c100500100815551040c444c49061104400000210701c007511035500144003010254451500d0814000c20b8603040400ca00d16501c0042d10104a080489100351002503098585040c046110b1041403000124144000340340c1252941109000c0f181c8841200d0401088051103070114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119200998 1250 119199748 119199763
    0xc010b04061d070e03010c03020a0201050a0603240f0c020c0a08030408030706050601033905030f07030203071209060504020f031615020c130207020a05031f020d02250302010608 78
    0x20030001649404649000030415066404070503132401c8540440e040c8040390864400c2004600002d40020b03405c00c03255024004c664015140f6003082203201d1a6440c3d03291031200d007043c0d0407034a00100704030400840315a044003243d140b80030b504100400380044080d554445030003003d8003030990400000f9040344080280d90032a008007020b5031900c8507550341d21000301001044030f418035036140400700e0006101c0091405e6603c2442c07003030a403502400507500c01d2210484051040140030810000c1c100c2c03074094001d4001c00107040243c1c803604e4600040d2458001444680c10740c1e8606a040414801203811103405140207540764208a07000105040e140c0311048881c1c014035410840c1001000340381d0030441c2c081d08840c030589004501200000700c424441141c5540242e801080381d60541c0b4005490100419040740100210b0311141e042100218030301d81c10800e042e43c082205081400c0b070340c0454040d03035041200d100040804502c0c1c0c0f64884d00c0176405400542c40d22502098004001031881c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119202248 1250 119200998 119201009
    0x20a060c050d121b020f0709062105070308070528050606090c090d0c05031213180204051807031103091209060705011107120801030201080705090307080f030c010b0406 74
    0x804812a64201c2910540c00c03020050701d070070355030f0071622130400c0c9000b4a00f1071351000795000e0090a090414901d2500c4c44076084914030b41c0c07070200100310410b181d42c0e0382c49801005000c4410502c0351414414180080703588098000d11002500030100600450000700010b085e001c0050405180706088181c100100d000030400e07404080480d074507103001c1c42c074503901c80000d440541c07502507403001150000802c16002c80d0381e500b100301c00388128541880314001841d56881d900f414140103103040c0c4801181071180700104548070302c0104840605804a8016000103018280c8050070000d105240e0300d4100d45041c0001c0c13401e15032000400d02c40c82181e0007540303484003c0068200010140902ea4071032050b0b19402a000c0040303034002030081c041d440444d84c0300f0a50a4a0300802c0c101640b003c40d00003200d404000e034110050005031f800c450400d800039040d01e01a0303110010709000c030f0300d401482c0e0001d00280c41010a244000040000108643d0f6a100002d01c18020004d09001c155402800744 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119203498 1250 119202248 119202253
    0x5031302090a0b060f0705190206120709031703070807090312030b0105120a05010e090102040b0301090b061c0c18050d0b060d0c030b061e090a0e010b03030d09020a060c05 75
    0x9400903141074481190000e1480e200000c00341d03800400103006a04c00032450b41036450200d030950a000c0d050011204a01c40d1200041d1800440e60009016207c2c452900300100c0000e004242028130420746000030b1940065a1110308060b0b100200c19500120f0314a000111301500045100e84600f145808072030344082100085111a18141c0180006265a40c1001418048030030a00c01c10f940b21401100c0c9007c0002c1d40394100260742a00c500000c0603618640c0c0100400c01c04e191100c02103d04589144d0000145140324000095a92044540180c0c80803941504001d44041603805841d42c01e800c0e4030f481d68142400c9141005074003241c400d55900c80711074281240400d49880a007940710710010312400000e0016a11894141e450b07030025214110035804100d00c80c10a842140d8280005514000169000c040000c1c100c1c1c3c2c0080036180100d03100c3c000640401001d40286802d180000e041e03076210900c80c07140c4001815001004e80c0708a1003448002402c50060100c141113503000b102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119204748 1250 119203498 119203531
    0x4150b011d04200a0206060108040b0a1802100315050103060f05060717030a06090f2a0504151214060a0603090503120c09040e0607230c01020412120503 67
    0x1045480140c0707402038550800d40f151402c0000fa040c45121450b0644a011050748503c19410024030745500200710605000c06002030102040f020364a255010120803001300f002040e00401a200d5504e207140207402036003080b00b140035960180c0086034524000640c1c141075503031f900011001c3e030350350340b10300744456002d084207003d00d09001004140c401d00848140f0000e000100c0000070b01d510484009040e0340c1e80c1c030018000052540924885016818030a2042c84c1007607049440060070101c0b0f041c14404014000707a0314900800940300108075100319010340301812107025014a00600050000b0f41c40c1c0060307810001010302c4068014000608406001409d25400344c00800410806072142d20040c00038026120a0700f031800c0c0300d00c229070b0580ea01d556003401840280d4010400190564000200b084686a4020f611070440152410034008840300102100414032441110640e01c2d4000075010805a40108600c400244602240c1c0691954210111580d010944580305071540905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119205998 1250 119204748 119204777
    0x6101206050c0906040f0f060903170307020a020424090e1c0314070c0b0f04080d09020a1d0907080706050d0e150709050a0b03061807110f030304150b01 67
    0x7800580d00110103840589803005003c0040c0141d042035010003490260b0070401d001001012082100034061070138680c1140d401c55842c8045601c0007890044491008070009481c00e100b08034100703910b50041e000704466084988141c40c1016103030003682013090207042c000303000710052050b44043d801e07000150040c80074104980b0b880c80c1c081c6149008058442b82c5080b07444204015560140c44c264595141d1035900d4585141c054000521518001800d10100404503200c5400c47d850599422030000e100002c510000d0002402500700500744890b001c040d01c252101261a01d0049520a01b150754a0307685010096a61840b4099500010818808407540313078000e0300074040308020101900c1c0000900b60b40b10038441c4044031400c0015041c45010070850410f640007402a0035100c01880c030310314000011a0985012592080e45030041c1000281300920960701054041c882900781e5000c0500c080c00f807941e9030415101610601081d07001030940219074400d850b001441a10381c17644007500301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119207248 1250 119205998 119206001
    0x20011e0e0a09060e0601030b030a0209010b0d0f0908040302120d0c030c02060c031317280f020310020307260a090804051306030b0105040b0d11030a060507030203070206101206 77
    0x5031899030048003039080450000494060900a0034600c44140340c1460080c2c001001e450396106881d00036003058214401507140e10810302d0656861203181a80c4480c4003500300024107440c1480c0b1245858800a0400c03c8401001031044038000c4814150b00358608078150f454002c00d10740200840e04603283e01c2c1c0001e000c1e140610200d030000300303183e0030425000d400c5811076204050082c0f041c141414140700001030710001d103d00240b010002c4c1100c0c0844610400d001c00600404140c50641c8080c10080003121449200d030181d001e400d584401b450a201c0c14042d4001756810700104417861480b00341d400b00803181824000194409a155032940c02c14000189445102070381c40080410000c1b880f6100d0441030180c04495800001d00e961860402400e01e21040e0484ca12a60a149501e0019036418104403c5241c0002510032100000300000745003800241009005d24145020010810b070503501a510840440d001d6840c00d40da0b6490110964030580a001c1c07501041018010120701c6d43d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119208498 1250 119207248 119207267
    0x501080604060b130609050610210e010204030c0b07140607050d1e05070f030e0708120c0106080a08091f0503070e0d020901171002070302030403030e010c0f20011e 72
    0x90b00b00400c6100d07030002002645d2036604038942c800d4556040c8032980c24482628401002646040c01c0d001c1038104903d076a02c011752441018068580d0303240c0540181c290b04480096a00440c184219940c806112080d1b03001000c09650b14031146d12b0b108415103012821a03c100c289554940c80c2c200059071745401418907510340240e050b41c4011001e903508440c0b0078203001d2102926048485400c0f0300000301901c8150703044c000644c2140b14104104400020089680f1400d90075141c2c841101191142c0104031543c0f01403107030300c540d80c414000e00664000801001c20291048440c0c10540042a11080b0040d8444070001c3e00400010301034921480c1c0c4000e242000030300041d044002d43d0005050750340280c00000c28003030001d0803050305107400c000b001480d100a074425030900c602510007039202e001d103200240030301c80c40140c80400c1c1e03072041905121180c2d00613003203100302c840c0c0d09142400641d8104503082c525081003a404580d23000d098040c0c1a407000c2018100360420101e011a1076890 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119209748 1250 119208498 119208521
    0x1b1e0f0d1b121106010f1509050d0201050a020f03030f01090b18010b091908060a23070807110f0d0207050a0e061009030b0c03150d03050307030c051b03030f0703050108060406 77
    0x80c00342c3d141c80c14160070300c0315a008001171008040300505150340152400c541c00014001c0c0028202c1c01c20003a150728040c03070710302a02400c090b51103c904620690074142c401000b030764507000010421400b05050041c031810788801001c10403003803848a06021b0b04405c1684942070441240d001000004d03d50130040c0b901da240078000d040000b40e000483d9030342020f140c01405003504110104500c480300d510845403810b0310a2441002d04100002d51840d90300041e01e10000c00c01c003900090381040c0204c1012004102c001c0848030307000c4d806145240c4070b2129030301d0800180031f0315100003070601c0c00c403c02105a030b05074006212107807208010407042280c1c418219041c0940038000001140486400611940050303000d9641c91800248101c1d02c2240031080901c02c10b0400030b60f4011991040c16654001124140040c44003203080c02035405020f8040c1e920608803044985c450068000710166008400010303182c105a1035208080e02514000d0161403500d034449000500411801e4002110585 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119210998 1250 119209748 119209757
    0x30f0a0c0908030d2004030201090303050d02040e07050c01050108071512090503070b0a0b03070308090111070506040b0d060e25180b0a0f02010903051b1e0f0d1b12 72
    0x40ea12402e4500356004204005007440d034503898404c60b40440c10704030b03101218031200c2d00d280505580c0044c217042094000a410040c001c81c64041e000c20301ea049230060003240003210158645404014100d602c0840034000f25424400002525100020007105461034015440d0b0030305280a01280c0078900c81e01201407013038482c100600800c100344000e000e19800b40890004620303003000320800307490f4000c40c1e03140240d00000b810000b003104031065880c2e4080900e0031102d040c20300603240380303400c3c2d55800c0181e102c0000580042e41007a20001041e0f0240034000070b003d0559901d480d2071807000d007181c101503522402c00d40d014040c0e1a10284c0ba1003a14242009800c11001c003581d1419004142c200c20002c8000090048100f500054046c0c4015881d1000303100b0111590b500a00d03a0250f00c142e075400382d60003984510300311000e21100b07505103803488002e114440001d0b2495a5010400c011000900680b100054403070700c90b8000c240203411540011031221100c0c1c1c0c980280e0007819900c4001c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119212248 1250 119210998 119211017
    0x1120609020a2f062706161101060b03010510020708060108160801020703230d02030a02040e0f0f0c0f04080318040506060903120703031d0a0b060402030f0a0c 70
    0x102071002d404004081d83e038002d58034071500041c0c601581400000e0b07256118003a9243d622090000340316074045c041c02d404807418410806480018088a0f54440c4a030141000300101c002c40041c41402c0c5100c160340b881030354a4001e145508852460007034610509040006010508140ca00d4070403001c00380c4126101c0c603991b4a442810702c00c003070300000440c0d00605410702c00c41040010100140c260403000714900b412994010701281007034003c144242d908503500403101c05400044d070b44401c0022800b9952407400d0203901000798400d020f82802d1115403c08503407810030f08285c4c98800c1100c2001c440c0c4a031074100510840345c00c6800b502c1c40e541d80030080410110824405400005018500001804454000c000aa920080001e80100e00602003032100e60380c0050660500c03032040300160390319089414220058410003050f000510450040550314820020b00400d40300e020307050701d01e181e03202c820400041e0f00c41070f943d071a1a03080c00004240280e4480d844000350b8240f034200b00809 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119213498 1250 119212248 119212259
    0xa020a14160209160f1e030e03040807030305030906011202031504061104030302011e110706090f08031009050106030b011d030a051c02010b0402040614070602070602040e1f050f011206 81
    0x620030b044035400b1a4601c0c603134000c0c21194002184d041c03030f035650b070900c201a4403e950b0001c80c2030400c002d12604040d10350081c01400342c820300803203024110540586401b03c0c0c0324180580f00d640143c8130301301d49102d0440005907082521a101ca0710303d07801005805800b1882d01c880d00c0d2404058410f0f20383c1641c0382000e0301c2910000c402000114030a400118030040d041306480740200706010030b03d5130141000fa1441045551104480300140d11640c00501c0c04918280f41040c401111002801000000244000750f200302200300202e6081803410f0149a07207801044064030040080d0b6400b080300f0002170000000303001000c40d0b00c0d840c0075080b00c00d15182030320b4140c608026200500c1403001a00080000383c2d9080c0a40788403600142c5007540380c42d25044004186490304402000e2400022501c48100b00041c2c04071151190008c006640741d50716034030011401e84054038407983c51803208900020b100e04c09a0386404441005044070040c403038000054030030305002140004819501c076004602d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119214748 1250 119213498 119213509
    0x503090c032407020d050a110c03060106090f0902070f30081e04050604030f0c0501110405010e09191a0d05060f010b0c0303060d02010509180406050a020a141602 71
    0xd51001d000301010b4400910007100c14096005007030a401c5411411003051300039001011541da2034042d10b0904428403078802e00318201044850b21f550706000318030000070301c15803015000050707c1840e002124250ba50b051640e04070301c14040700a00c100c40043c1d1040104903802c4484286d51031400c12003039001c04004010920011440c1d80c030380415071550a01c0041c1ca0341d03110410741109841c5602d600350420b5290150781c2c0100420040810020301200d14590307100d010241e4446034440024041203c0c1e0306241e000c036400a001d0a170020b8600c80e244c040500d0081c0c5203600507600b40c00200f150050f08120000549116015000c6101c2d00c0c00d09a0301503124849811007041c05840502030b03e080406041d203220307606034400400880188150742c207000e004821290400341c01c59801101c14a64130043e00c0c0c501842013156406020106120300724096000000d1140d44520302c1080342c1eaa81c064500b0490040f80070f032900017041480040301d0180101c00070580c51040441c1c0c200c00381c00d00d0340080d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119215998 1250 119214748 119214763
    0x61701120f1e170c060628060801090c0302090121200409050c07020102031b070302150c0606120d030b06040302030a14060703020301050f22060803090109080d0c030503090c03 77
    0x1a5540d0544001c6000d02121400d402d4642c0d200f0301c03055140400071403000303039240c0313029058910031020318665008540240d1a0000280720081e00c0009203941c0310000b82c05076800b481440c00d824204600c03407039403030710038421102044030584442001c0c8590042644240388040001d055241c0c0e90902040105010164192030340002420b155545040103000f005454001d0480c1d211990b05210200050b80c000c400c0d200c6e03204d400c20018000c1d5059076000c0e403401d601640065001124034081210079142c10004100003254a1b00302c4507151115800d00050040b058246d2aa40e0041c1d0003501c50207100e80c1240b11080d200518107420940c4039000139080070700780d0004844072614080002c0c250a802d01c0004c0d40300000c0d0404500703640c900408a400481c00d0000d440c81950a1080b818080d80352035074055650368010005c0040541fa007121960300d521640380341c0d0100761000350000d5458030008201c40011115a00d40380c0b80e000305e56054910303402c003600700b030214001c84079250f4054808110f0751 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119217248 1250 119215998 119216033
    0x71a030414010e101a0108061302040e070503010501030e0c03030a12110f03090d03060b0d020702060c060f060f0d15020c0708030d05010e010e04021f0201140c030709061701120f 78
    0x34101a031400501004841c042e1441203440000d035002c48450b41c2c7c108401e690700000540309a401c40b2011642c03c0004d22654102c45090b9007400d092045182e80940510305842c000e03242049407140d540e1000742d55145209006905074810016012007a21030318500300400700742900403900d03481e0f1040407e210b4001120700c801c0d410000c4204960758100f00a040f88144d6541820020341d420300c5061802485001e80c00e41c0030540000e8181c00f10b494075000c8030301c00c003101c205503511801c106090304240305003a940c040c4504d104030140040c504d030124130750301c0003640100c00450042c10051024003a41003003000c11500d004880000409200510080c99428401080047c0542c10405052418034060700040702600084003088010f8a13240b0600c3c541c041e00944184494a170127204230f0240c02c2c45402d8171411190441800a0ac0226402846c013440198854100e49030301e521049a0303a034440c1c3c40318851900c501d8010000050301d41c0c010175400380035980100c034140e02503c811000c90b4110414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119218498 1250 119217248 119217253
    0xa0506041a01050901060f4407020f0304030b1003050607030c02160617060a050402070503071403120103030509061201140f04050c04031b080a0f060e071a030414010e 73
    0x70640140e0904140c0d016190488400b0b0300d550500750004c00e001040070a1a003400310b480310400448006440d50316a01007407011002c0f550224810602c007140e1401404400c0b11f9000340421242d50000c1107503480350404000850034103146486103150710001400d0301845424854020020410502c13103c2d01c1255191404a00c1c1c1e840d492009140c107420114042140304402c00030300c420380d48040390400050401d070400e101038071031000003107020101c1d5005a40c068030002e22002003100200160140901444030b071460304030140003c0d0b40780d20442e024034008901d49001800064042c90141000c04070240c0440e080000040b03200340e000c070080c2c00040c464500541d11510f0380ca0f01c046141000d94040c0e90078811410303d80d0350910b03103004a0000800e00c5003e04502e208805401000f18010500c400846030441854100000c80c90301d054415200681401c80c007120031600082c80c3c1041315075014028034101040180071b081c64002500031981d000741034502c19803007182409103200f0700850401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119219748 1250 119218498 119218523
    0x170d0e123a0509061e0613020d1e0e010f060b090d0f020a0f050306060114091e0405011e150804150902121f0e07031b0e04150621030e030a050604 64
    0x40c50340b2407070072205c1200c44030740c400c0c00b00a8035031100d26403400120304403113025840c0e4150282010180c0402541c01c0e0f1807034001007480c099010203801c1245034030700c4000200f04c80250070811030140d035081d0065024030130007002050032034208580d031305c1d107002c1c02451700c1d01405103070f61f0002c0d201c20311961121124000c4600107108615050040355084102428a402600200300f00e084c9103001c3c10070241d02c1489018041060000300086028071740314020000c0101c0d6848010304070f1101c0002c2d1090f008044801004605415940a480c2c080751082c0c6440e882680c45550303080c1c0200b000203511000c50348501c952001611255602c1d071400e0f24901c090041082202038080c10b1200e600c0043c0b0400741400540c240040c0c003c50090300f503a401421540000b00c00d002042074014007a8001c2c1041c20f11a000c010a0140c002c004101e001c58100d8107201c2e183d50340e1816207076408044000d401004e142c210b0440000d002e1010b15410700d6020342038907528401a103e05003812002c0b14191a240b100d0b14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119220998 1250 119219748 119219761
    0x3090b0d05070e0616060e0c0301090804240801050d020604090507020601050102061608041b08030406081609030b0a150503010f0203090c0d0b0103030309170d0e123a050906 76
    0x60740080c00f00c2c165041c504083e03c208046688261050014001695450016090040c1440303a403d0480c0068000d00425503d440c10785080e038814031650500e06c4d07200305400da08102000c0d032201030f03940741e47e075004c056403c040c200f000714000401c0490303018404100014004620740903441c440c0da140e0300a030415614000000e0b003030580041841a41983d400c2c80542e0301504020456006a00070f5440c440c1600300f00481345051301d0380c1e04503009620010a0000d01185e000501c14420302c0b000c3c4400704074901218041d505900a404010800c8a00c80c0c00a414a46680d20580300710007050307000714105030760b1000309007100c140711501c480c0b181c1c002041100d2110100084a850001502c1d02c840b800c1c045d484103072440c2e0042c00020209600d40405c0d405009400d4046003200c181070341c00395034881a080e5444010f040c410759020040c000c0034690340744541c0c0c03074041d25a02d500d42d00c1c0456000140425411a0f07003900464803200c000401500000fa403c18400c00c3c2c814140d0000810103400d120303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119222248 1250 119220998 119221007
    0xc030b130e010c050f1b0a0606170706021c030903020106050a0f0302012a02090a0b09130b0a0501060f0f2c030610050d06050405210409060b0304020f010c03090b0d0507 74
    0xa4040d60030b1010400900c03d2003a010b42c206c1d03503500001800082c4a003608a065420413103460000b801c0c05080c0800890528111482c02000e13180c044103c0c0e10455540005030303114010303c0950300b446032240068840c0d80340a90800807400d4803c3c030000801580741d00009801c1036294100420f004441d25042c021540c001c14007010f1441405038034005007030309034540d401029031400c00a01070408000455140389086d000103250000060094481e03152528606507401000035058030a4031000300400d41041e82481107038182e91042d0b0306c8502c3e07000c0132181a41d00201d4448550204410314120604000488185c659500040c042c04426080c91000709850650084e0101ca0380120400c030400c0669985041402c07003550041e804969079665080c12810800f039125070090070703804540701d0081c100c0c800000300103030780f400d010401090751140c003500002d00088a0094010701c2203a1503200307940c01080c0710b01d00d640c842d2804200058545007540250f4004100080395583c5030018480c015400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119223498 1250 119222248 119222261
    0xb01060909150b191101090506040201030b04020a090e1e0112060c02120405150c0109050a0b0702010b0108040b0c040b040f061704150e0f030a08010e060114030a0c030b130e01 77
    0x1e190790b0040641807000c0040c0510074038041210107140d031014102c2c92030041c000e0201c1501c0e000003c102c0c102c60750030049e44031842205d04a000038908403141c051846d042c800d840c90a4280e03647d0b00c6406e428420b00c6286448007901c0c0599138150000e0303035020044807000c4c03140640441c49811840249c1d40c58110180d401042c1c41805640118001c0ca0b0341c14240c4060340c1c200c0300b003100d80981d602c545001034008c61007a14940766541d402e10004809109001452481d114442c0804807543d0307881410407802c85100f040c42c1c50014107a03601080209040d4107942d82c104200d025118034044d912980f000e4168401d501110582000d14006c11069030089c402c000100c0301d403140070b480d0385025a140c11003444400500031026546030b805207180c0c881048a003800340a403600b141c1e81d5183c400b0001d440d0140074810380c00080c604100040f800d52140c00080e00000361280124216190903a100014200a440f1603080596800007240555584400003241300106000000d40f21000790300070707007507d04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119224748 1250 119223498 119223521
    0x705010905100207080f07021f0c020a0f120f080d0608060915010e0c0d0b06030a020702040f090506161704060c121e09080d0509070509130f030309030c0b01060909 72
    0x106210040124803928100c42550701240106d0f0303580c0c0c0151000a241d1100c1884079548910407250b8002c69641002d1401e000e0340c0201d5041084c03540d95034110019458034060302e1843d4440344a40c44c00a0140c00514102c3d81c405c1c3c0e03526082c854510740510132600d09500c5181c1940c408424404000e10a0088040c0703084008004080b039814401c820410b09009401d2010b903030000072350f202c1101c0180e0300a0801000007803846036281040b002100203074110344000c0e8411032800580c58900d030348511503000500d07403180241046584201e44e10140c29a4107150505102211000c041c00d4010344040740d100340d1207148000350b600b16849000301340c0c1d0907043d103800060740317040e10082c8230070429030309040307185411080442c1c0d1840c0e5291084450080c4101c29070068280424018114408140d51064a605580030300b025034138860081425040640058156802882da0340e0120b4070a410160f1102c1c0071303040c501000900741d83c4080300d800c2d0982c8000c00081c101101802200c40c10b0140300b00d03054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119225998 1250 119224748 119224751
    0x61502010c020c0d0203150c0a0f03020301140603041505070302070b0108010b0310052e0302031c140a0c08160b01050a030221010e0d03050907050a0e040201030b15070501090510 78
    0x1140c800395840090902ca03602c0303035050311060005c55500f08032249002c07090036100c40b400d0401a06000c2590002d889000210b41c1100b40b00c40e940b8420700c283c90490320025a11713500b001d001c0d400e06c01c02da032000e08203071051103e80e0340c1c00321084c0312409030302d0042c2181d641c01a035078440c504001c1e03214041030304050305503410714142013007540c2c1c00100c1056182048900080e180c40d000108140c01d440f04922510020464003101d0564901c1c040410469000b0380030703074296018a0310a00007003019141c12001048242065400c0c09401d0405017181111074203010b0007244881d00d030040960410440c0000c080b040c54601c0c403c01114419503401401c1c240e40d011200b5041d0b07030001740000882e003900c1da100c182003010300306400c00941140002407541001e031864900d15440060203408101e508100c0c520803068005040d0500003142c04c2100da40c8080108951125401100036081c10f00c402ea91001c0010341c11503140c000780c2d0082510740e200e440005011a00c0380340c541d0070310702508811410103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119227248 1250 119225998 119226011
    0x901120203060720010908120907050a03030e030a0204020f09030d03051909020a0f0f03051b0604060305070c0c0f0306200702010f020a05030711012d0f0306090f06150201 75
    0x103881c00500c25030848200e00b020851000d2031018034044000c029000451507003801c0007101032081600040c941103210704500301c0e10f9514404c20035580c10091207100d030081006841080841e00c60740384542c08030401001d40b0800e41440e000141641c00154060040e0384000411800034a0200080780c1c648035903040511161500c1c001c2c1c20b28404c003415070700c01c9031034441202d9001c55503080b102c94064103150b03084074ce0040c2c5450151030041518001122540700d452800030102c2c40b08000c045019800a2051745054100201200602000b901c00000c0c49070303058130140000d040f036004030302034914042004102403450401c41700307507044101443c00c00030341e245c81240c2c407810704421101c210380c0a083c054403485542c40c08925004001001034601d000201e9182c04210205079002c9070803200740d9507095450061039800500b021271646200b13154140c5c074026441e07a4050340c40c80c0d558100c0340c1070005455599440c142c0c160b0740100d80180c1010f981e9101848090540701420500e07404600c0204040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119228498 1250 119227248 119227253
    0x3090102120709050f100e0d060b06040b0901090e060f0103240b090a120c0909020d060e060703051f140402040504140a05011707180e0a0606080601081b0d02010203040305060408030402090112 84
    0x3c0142011f00c150246000000711310601c10075400013103510b58060449555959101d41000700303a04081d0200f4001600c10100290080205000501801300102085080c14421005400425000e1016a21800c4107a000d85910328200c244400078a007100740395940313104002c100103002c101a0402c0b1001d689281004010a10b60700000c400e6600e000700000d0001c009000188015418030401441c0c50f0416824244440000c0740342c60146a0710340f0144800e481d03658000002801710b05a941000d8444107040001e0140a40c58050610300030700010304c0d0544600100e02a80d094901581d03080c01c1c140c05021510481c6e00c180e074010300894440c04907200294032100c0d2101c040b48100700c3c50201b90041c03c2011010350341b00801201900d01100c44448a1740f038840e02400c42c1c0d10445040d40a5140000343e90403000c0303070f044500e9241100c1022958962001c00030303403600300c100030ba0440c4400e120200000d6810041140510300840340542c42e49083d00c100030310440b0503004100c1d054408c0f80860300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119229748 1250 119228498 119228507
    0x50703020a0c020609030a0512040e0f150f0a12030206011d010506040e04110904050a0605060105030c041719050609071e060804030c02062b02090d0803090102120709050f10 76
    0x80b42d50444020741c0d1041c1840c0060f00c1e0402c1248043e00078018140080c1e07010202d10300800854030420349464240c0d4408000c0c443c12202140c06032125800340e082c0714043d181121410b401c000c0f000b0001c10f8069200c10402c0342da0407074410300300d02581c802d00050029003c40380784545e03401c0c0d403400c030f81c007a0f98100004038a035402a03102e010501d14030140401c0400c45402c400b584640000b51185c00c0c2c03440c01e41040d40e03451003031700c0095542c0c40ca4031000c140300d035100e84112841440340324030061400d850042c5410083c2039010b80c1c1c000c107000d403150383e10030144c80030541d5240c14022002809542880510f00e410060a43d00c000204843c003203918180781101c0181c40215041400c141d46070341d0722400c0c00d8400400d1108029030280c4005101a003010040040701450012184040c0c0c00c42c909000e01030482c030640151551001c1304075041400103c0c100003d580c0041c8000026080c21a01d1b40d010b4891b410940da00c0010034100c003c103112908100c681444100d908464050010012070300250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119230998 1250 119229748 119229767
    0x1701030804062307030903021305040308130c0302060a020106080708060609181e1b0909060604180b04030207050f09041101180807080d262d090d03050703020a 70
    0xb091010070400c0850783c03005072a1003400c00703aa550781030fa5188482e280041008945000891084800b64051038503c4540c1c8101441903501d6103a007500b039120b10340040c0521502e544212030f40212001c3c04030050310b814010b4003190340580c001203a00c60600c3c0e070032424a40305402c845403581c03001c400c1000940e6100700e02e45e00804074100310b516108000a1103030512544c1c403060350207456403180703074940700000159018203010b2000c42c40d210010301c00100045807400340e40341d0700590b00180200d0043c9c41c6c039621a00000d0b0b5007500304080800d080ea20809642011103040d0096040322208000c203080000040b0001f403411548051540340c00d41c4c480c107220032040c0406042103144c0c44812100701b44000c901000e03080d0300c1c044807551543da11541c2c0d0764003c124500c03400510303941d40302c100100c450019403035400b002260003030150381d44851f1580e07440c000e1034620005640340d0700074100c4400100b40003030203030b0450700241200c42e0120310090300780d42d000fa00c0341c1e0400d44104805000c07650300000c0312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119232248 1250 119230998 119231009
    0x10506010503090d0c020f03030310092706020a0203090a090b0a05040212162c030106060201090c061407021206041205090a050108190509030301080c03070b040905061f030b011701030804 82
    0xc0742d500980c004101518954501f20b600341c0b1000003231104140c003013a0b48004591402c042402903503400048000f00e030706442c00518031410300c110765400040442c0c0243c00411851b1048904004e80380740018038000080d0b002603c8260b442840444500b005003182c0301405040c1d4055252010b40316a120780088001c00c02c4402c000310502011059218100034840d40c900b48117000724415405a00c0d000018100f80454030039840c1c030310002541da006001c4c04071003d4011003141009031401c80d05644044198400c00080a000c0050000503951104032907100220500202210300e058030f41a074408080420f500c003882420b10000d01d00d5610306401c4000d0754828078204a41c0d40707070040000c24001a1f40d8025800e68105002c100a901000001c0d41c1202e0301c1c0021101642c45410078152181c01a005500410f0310402080c0900381b0079800c500e0b009035002c2c000c001c1c0780f0041c000d28548040700b01450342c0080c0d00c4002c125440c0da403000a8a0030240c040d0f01c0c2004c0d951642c1c2d6111031a100307034800d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119233498 1250 119232248 119232257
    0x105071104090602030a0c0e0a0305030301180905033c03161b0609050d0314010b0702030c04090503090103141e0402010c0c24050309060a0b1c06050603010506010503090d 75
    0x140c03911515035400c80000385a002409540b01d040041080f07024066113884000010f51b0b5600b549054501088200c003200d801c04040c40c9140d01b02001e80880e400380f06a800d00d41901c6a00c0180000c0d0101b0003041459000e01d01003542d400744601700e00600404203000c1441034000d8400c00c20307064a000c00c50b5000071481103030b10b022042c0c0260039034103807d420204e0072084d032100b0b0785001841000d410441d4054401c9050306c07501c60041c1025003c617410540c12000700400c07400107100542140c0c0c01400d001d40001c0032142c03007030b203a68002000e60f9200001110107410124101240c0c0d40c042c0285071031030304422180c95403441d00c101040420480c040c101000d07401e02c175010400b5a402100358000391034004506100181d16046040071000b00102440043d80912403450f074064810401c1e280541c54050180006407103003c0a4000f4100d4400d846902c005c004000b0000652100000481141301d98408561441c14104040c2102c000400d038905000703080041001c40f103c00300340c9981e51003242c00d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119234748 1250 119233498 119233523
    0xb04030906020d32040b090a06080f0703110c0105040c05100507020f100507121e0905031509010609060e040501060501110303130812011e0609060207170114010b0403050c01030b010507 81
    0x400000c1d544201204d044e0020028021445800080042446030b0301510b06100b11a81e460b011500c001c1d040307440c1a010841080804e401038443d411170100a81d8440c00345090140542145003111010303501114004a560420411030924070704018503c246820030700d050240c190042581c4c0b50019006a2041c0030014144101a016900751145c05800401da00780300c80d00c0e0f050113041540420000b0134152960512280b42c180702c0c0309840142c50000d00548400d16410b1102025520060b004071a00d540703850011505188520801d002040b180000319000e08007400c0c01800c4402c190041c48c100001440c0540700e000c0000b003201e070001c0400c4032100d11075805040c641c29601803e242e440d0441c0b0500b000045007160b42090350b200da180450b0581c0e640d03996180540b1410319501c51000545c01c61002000040c0148c81c4114054480720008a24003540c0c40404440306000d13081003c1c90b8130041002d0003070100800500480e14420b0a08000d4800c00200180c0b03103014404000340543c24049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119235998 1250 119234748 119234807
    0x10b010f120203090a050106030b010303080f01180207032a0201110625050c15181b0d05070f0308041806240203090a09020306040b03060c0703050309070b04030b04030906020d 77
    0x81760000ba50400001c1000d1910fa1030200100d002c00e10080c1d0001d40110081002c0d02001c150450403994485c5801c900402e4510900c1c000e5000043e00380c05019114000e080c0924440c41c800d5026908031511031100e034245d100140280145900d42d1405511a10401c40a400c19003c0507016014981c0c00c000078091342c1100319000d102c0c01c200e500340c501406412981d1000c0079110207003d040c510804500010310012025580c1200c103032446465200c0d0f0f02001ca203030070003e255141c0035010b0400c1c0c0710039503103400c1e01d5030000b01a940221070420300000c08002020006142c480d80d0380e140e10382030011519010301415001e02d806940314800e081c1c0500038000f10b00070402ca070f108550103400320352056a204107042c008c1d00102e51240c0203900b0f1451030180752901160140c440d50350810143e040c581140c0b800c0b02c0e81d4000400444a034440c3c03503008100d07802ca100140c8011f52182c8000103851070545002006010141e1002003550f020301252601d803071300540d40c0c2541d090ba500042e03400781c0104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119237248 1250 119235998 119236003
    0x30e12030a0e030c0109050312180a03030c050405060c030702010e0117070e010c0b0a090507060c240917030702010b0d0b0a050a0f0f0b28030b060301110a080702010b010f12020309 79
    0x3102d6103031641ca002d601b0000c104012025150301009036000c1d40460742c91408062240f210b64032054a20740003c900c9a00082c029070042868030918540142400c1c2c40f6001f24000d43d0244c200c031800c41d4404140e4604640e80500c280300c0c0358100b03281c400d00a1354140c0740f840920402a0080081c058094628500d13644113166018620f9040b5050351458200021413100610603400700f1b860340d010f14800441d4250158440003c81903015000c07142c001403600e6a1001c10704508000585541c07116008404103421048280340306107003143d6184d0f2402c10810203421a007044410030300421350222139001107610003400c81d501c5000b001d00030030307240c1e10203400e4002001e484480145091622900e00301d01c410b590320080d00780800b644c041454840014420070120070200c44100c0640e8003890070300000300945012030b0040000380003ca070401084004240c00e030060521180082c8060742004541c6a090203242140c80003802c2412060500f110012300d8a04e1244483c40240d800101050000908 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119238498 1250 119237248 119237257
    0xe0409080307030b0111030a12020c070e0717090a0c03020409020d061127060a26070509030d031a0607050708070b030916080a02090601050d0e0d030e12030a0e03 71
    0x120305580d00d141c202d0700540200a481c001e03d000074410525803542041c00401c0328882c10050b145c60213000f0181000300c0103036010900300318032402041c01c0028030100c450f206d00d008a6413911074100410140c80003c0380b00b5401844585181c1c8008014400705218030021015070b038040d140070034106458004540b00a401000c014026807400b16034039010196040605890811461840201012001070101304444202041d41c000c40401803035040c0c60246004071802c2d43c03a12801444403c0f0011505131051007159040041600060380d2100d230b140920401410b201d01f82800c010030791030400c8c0d60484101e0811014064200056158144507080007030400a00d20041150a480e4840300310a159030800d90f0904410321440408100c80142e0000340c2042c0c1d02544004d058402e401d8003004a0344030b003e408031741480020447c03047c0400b118012202c4005034503004100c820380d0403600030201c0d00045c03038105450308141c50b46c00a407042d02c41120341041e080c440109100d01000704c002d045109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119239748 1250 119238498 119238503
    0x103171201150e030a0210080615040b03071407030f030e0c060304050a0201020d02071404050a1e091502040308090603060307081905070510021510120c091d0d0e0409 73
    0x54480000031401407418092090b05070300d5492241e040c44000c02d040c0c1e2032440c2c080096100c0420010159614402c05405a00650003801d10010711004002800c681d80150024010300d400041040b5100ea0004c2136034800b800100c01f22490041580c400402036403030b100e01d2404064039461300e8006144104042d69258100410040d684c0c103142c9030090707580503038500032809409000e01e80521140049000340032150079651090220351068100002018020410071740d00c0d1340c901041e1081001c025415a403446000740000c0e9000d62400c108102d8415010303085000b0b0b0040005000190681303054442d40e02040d91169240d403901c0001070309243c1e0390b8011a08510540c141001204a4040c0044070780e0f019905580106495509228410031010400000742c3c1c0300c00c000e012402c5030341d050b490b4803221407000e05500c3c0d41c96130620300420343e05003404e0f101440040000e00144085e84030303466603201424600c0010700303d00b48206441f0f403011301004081c0320181608441e1610b5a41042c0a0680e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119240998 1250 119239748 119239777
    0x1302040b1203070606091e091a070f090f080d050d02162603040b1807030213020a1403100303080a09170d1d07090c090e04081b01060e010317 62
    0x884244141e9982e0b00f241070159509402e00740b00041c618024412100803000381c6c1e82000d120054018030101800c00310340c00701c41c60074011000300302c0d0412110340940580c0540e51040c1000325880c07001003240f40140c00c502441e441c071000401c900030000614980000b124100780b40c0390b1021040c00380003406151004582c0b107580711005410007004803240c841c102100079880c070601c68000103400305030104480c01001140076001244d030203000c001c481d0700e407101590200c4a07100d4480d40400d5804440b5400944e0540c3c022501a40c055044050600314220b00e091940c110300e00b0111a14900362240f0001c0c050104210104014020b5034200300300d45ca1708524100e200103500751070481a81c0c07082c150010280e1030038840c0107400e04d898101c02481510030008000f118100044a0000c046406e00c0c20b003403140b441d100050743c61070b0b408080c2c031071401a0002d80c0c0ba45000b000000803410b510702030950503403402c40240040407461103032606594102100d00051105c10f600420341e44280381e094039944 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119242248 1250 119240998 119241019
    0x703111b0d031806051902010605060d0b0d062405030c030606060307050f04062a2103020417030315091308030c040b07050106061209020a0e060409020603160f09030b1302040b 77
    0x20b074105e002000b025442440c89101c40c110320030228201caa0a000d0154000320411009100301801d80002d074100e040100458410001503a0702800c58a03e1182c1c030400845100344a4089200c1a0003400100403c1e806080c0a400c0000040d0710783c01b0043c0940d20031403000c00072618403881074069880100200c507149507216100c840c003070080c3c04c2c0507071030700c2c0f8280748408580c240124020341c201106900a11605082c4c0a9030022190500d001a110040507401d000018415001c00d1540782c1c0720703d40801859030781c00c0c04050a01c4180b0003d85c03041c0a4034416090041c81c5000d22500701100f90080350180c0c07030742c590044a06541c859a48a104403000100d032180c123014040d40600b003114503580314810248103102e0040d003a50040d800c083c1d8402403420f13040101040001510707903c02c0c00244000341800f101d0707001958035001070780c4507100d005c2200518000c05410901c050400243e40c20181d0240b441c542e07401c9486030000b0f140e085c2c0c07200e60501882c11902e640c0c2004c10341040081c240000e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119243498 1250 119242248 119242259
    0x13060806011202030601090b06073305101202011d04090f03121410090902040b09010f061b022d090703020924030105010f0c1203020703111b0d0318 65
    0x10b80301400b070280e202c1d014000000401507494443c44040040203081e00f4101007840d141d0555401e1120b490300c1e08072500d1000001c00c3c00d00031011802640d01d0030720014017030510807006070b402c084d0340e0091443c2c2d42422a61001607a00f085c4522038002d0f860b40503072103260820300400d02070305000740010034105e030031030105082640044011414906e181010050f0a480107145004040142d402c0112090980404d20044055400c15143d00740090800324420a840c0007144005034264442c60340c00c00c1a9109114a59016029075401d1724082021620801e5a400164050340000c040840c82c03e841c2e00344107910110765900149940e0010603500845c9404000540030354810f692182c802c80304903141444000000302e41884100840c2071840c01c0d682004015281c0c88450310454050148042c00305001500f1040e81c200c0000d0300d41d82c05a11190b041c9405042400095059600741c0c100c103245030f02c4040c04c0c414103014a00202e854543c59036050a040d1070282c071040d20380b0b000c000c1448002c0349 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119244604 1106 119243498 119243519
    0x1030c0c0201080c0a0318030e010f08040213020a020c030a1b0e01030b0f06060c100204060801050103051311060c060a140603030403050706030c0306151206050415051306080601 78
    0x402072034480c0915101c1000600840000d2400d190701c0c0c03180cad45d0103002200104070030304100006081c60b5000800380781815042d00c103056804901c6201941c400c01010036051b0000d030a65412807020304051594100d03c0002144801252000107540751841c40500e04813900301140400a840e4a1031003d006100540704aa000000707000c1014a28824002210111034580006036214a0020081c041080591115044c107241604000340d61030b213040c44462007a88410501d150055140000755140900400341d100c51161404002802403039a01004a01551803d018103540c0c50004040d42c9100b02d0000030041e82144004104040c0250005480c1403060b050129a00703442c3c2400d070342014490f41c00e20000910a100980c10b101e480d204040c0500810742e07003030100d0201c039030004940c0d10b410f10506000301010103c880444a05e03a0000f00a0407a00c3c040c2c40885d43d4074084401c = true := by decide +kernel

theorem cover : BRFrame.Cov 119064748 119244604 := by
  have h0 := BRFrame.cov_init 119064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119064748 ≤ n) (h2 : n < 119244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
