-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:31:42.595061+00:00
-- url     : https://prove2.me/submissions/88d64101-d74c-4e21-a507-3e3f2bed421d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278417266 ≤ n < 278597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278418516 1250 278417266 278417297
    0x509010b03070906150504051c0f0f050a2a170f0d0207090c032018031009020906090402101b170a031b05031b041a0a021c090501 57
    0x414500560300a081d034100c55107a400200060101d8414051011498000c0ca150580034100f01c03029100007800518028040104036011840c1c00c02c0200d440c020141d505c0c40c0801c04540c01c41000a100703001a0811215a0a002d000c1c05600e102031240040000e90b50b00c01300c030304142c03241c04541d034400a0b4156501b1541d4201d045c00c0801d50000071a005110700b40e21501da012079140b09541094904004c2c01003000384c114100c40c401306162803042503914103a08175060110160000091035490445040000f5003c00d0401c2c882c0040741c2c06007038490081c03004500d0518552540040c043e10b0891140c605a00065480d2518540060522403920803a1004881418000200941048015101d800c00c40b415900e1a80400030a40010707281c110b40f040c0e1441401812480810a60349141c21512040c0c9504450140e041c085c01c0390101c04c01c0000707125880b203000840440040b400e21503c40704040006800d007400080e40040c8108503401030700c240d50f008440c0c1c50664000707180c46224581c0c10032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278419766 1250 278418516 278418521
    0x2121c0e030c01021902063304150f14091308190c0b0105041509020a0c02040e0a06060806010b0703030506041d060105010207061103070f02010302070804030f0203011b0c06050901 79
    0x98416850000061032196140d0540080c00005003a14040039880c0c52904200c7e110042514003082410000f0350120f0441284c1e1043ca548418207400240c115000c800000c04551506d03640b2400b481800c5010460b407012415038000401d80b051702580c0f106881d00004490800003407501e4050740301c07810402e0a01c0b80180542d500d03a03115003843c005029403a4005020002016011144509907800125103418940146030910036101410b0b4002401e01c1a41d4001e5082821580100310303481c0040005a5540c1c052001241c2c110405080c002d00b650030301400b80ca0107600104425840407004109182030f61040314505a0942360010300c944591000030003401c8886800c042400250b0101443c443c80401c209040340c40980071580c029075500c0782a0f840301010440e03500a6041800301c0000b0400d00d024220083d0310500d0014602410396407030400e40c1c0c100c1d8005460382104030064408500b400d200700d00501c0c103030b5000308500c40040d003401032447d0751002c0d00400d00c035114804204c4104094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278421016 1250 278419766 278419781
    0x20a090308040b03010302131109040902030f0102220b09011211040302100807021c0c0305030402030f1203071814040b04140106020a02030c04110f221d0702121c 71
    0x36525030341d41d9a44212950f4076800a00041c0d20551511341e10024000c01e0b1b1007180150b00c0c10501e01c900f031203843c600f0080141441d60b401d036018040c03105007c0c002c0c01c00b031004000d00c1510b1041b0f40324140c3d030701c0009148083d40fa006800c145004100c03260080e0303003000081e00d8001100300081071050004a00130854000c030f86c00250014400540c022030607821101c494821300e000e50031103005000f40c031340381c200c000760a0842001192400c0a04d03004a4421402507a1140c006070407102100e107035015043c9025440900c0c041c0551f804001e0060455000b280c180d59081001000b0f0052420320301c00c1c501201ca01504903120340c1d659074080545484d03c0d00000b0102d04800d510b01c600d580d403401d0280d102d0071805822031003401a460b03034100919003446000880050502d1160400e4201c0e8a1174015a01000d41d01420001790a603081c0341203200300e00c182c084c00042505084c180d000060101c4610300103008481590080c0c8407040440520744103441040f880006180300c4c00d95003000700c078004c1480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278422266 1250 278421016 278421023
    0xf0c1305040c030c030b010e0619052206090e01180903020f0d02010b012307020d02130903021c02010c020604080f0702190e1e0f10120b070201050105030c01050409020a0903 76
    0x9060300c109080360143d0002c8100000c4d40c8051102c080300900440e1011580003441c2d0348003c00b44810584181440d07000b03000c1e00302c01c3c00d146191202c45168a080415134440c54404401d0056003400400d42c4110060000d000714000c0442a5062400c104998110700010500c2107507a080c3c52003d1510800c40c0103c5d2041990941d00d6840401c68028080c0040c060110702290010300088a40412040e030340200c4040d010a090a10b000e941c200080040c00c504180c2e0301110000b040c000b8420355200382c00c40d051107500102510004400c0506c601040540010156490880c90a59040c0c002ca0300661141e4030941096a84061813484151030041c240e010750070516801c240300360a000d00c4804020385017005100310742c3e0341d184c500d101e4000006001400c02242d02c107020440c0e00f070322510442d8001c1c40c0d040e2411245510b40040d017000e18041b584c15604185e9110900564507028407a0501500040d40070345040025800040d0072413260b80700c0c110b16036500107141c11380e061151300f4110185070b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278423516 1250 278422266 278422271
    0x70206161b0c061103040e0a020a200601031502040e06010f031d0a060b0d23010b1302030f060a12080f0c0601080a050c010306180506010e060a260f0c130504 69
    0x400d428159000140741c000c1c18003061003c4c0c00100010000030940c2e040303864618904000350788500203840a90802c008140034050441c001c8410703020440b241044605201000308503030b41c55030514421b901c032000b040a4505204110a004039094031036074581c001303400c1c03c2c25140074200403411001810706070050340d82405e004039101500b00d00422003420304c4c1e0140c80305024403108041000031100f200d10000304071022400303541c041404c0125241c80a030124800018041c140007001c40c1d0600b5120b649040b64650020400c040e8071044a0920f400400c10348040d15424141a000061f61506450180401801140780c1030403880181c00c40d250010302030192030039035035500c28a6030b0728010f210089845004412144103294482d1040b0422601c014040e1000d07200e2812290000341005040d4504105014035141425100c0d130b2300818032403601d60307654441044e80520070010f000c41700305603207429495231042c03003041603607400b026804c000c12650b031596070711a50042c2d20540003207602c012f801c1030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278424766 1250 278423516 278423567
    0x3020d020f0a080a0c0506190f050f13031401060308091203130b120a1505060f0c0a030e03010c140307182d05060307020a06020328020405010f020607020616 69
    0x800c0801d100511910400113030000b5074035031b03042020b40d024000c2d40c5850003c01054072845107124061614a1000600b8114a0403009182800301a4001c008000b2840001d400400c02c0040710384d414800038400900820009083da91405443d1164420f0648145220700b101c5280c410148120703408082407040200c071141d690400107c050300300c4204c40c0510300d1080001a0825594001d040ca680c000c034a11040745810102003207215084075441035101d0109101e00070910104001400569001c3d444403200009204101429101101c03d03080810100590b002001c0250303a0640380c01c0076003414481c4540b0b110441141d103285055200741d40e204004030108207145c0786049100340b00a6401d82e256152078660042c080c281c4010f0715034000507072002c001000841c403191302554204c40c00c20740a0584451626036001451072000350150510b9000600f00a03c0d81c000c001c10b41203060710f002410b501d141011010792103800c01082d000ea800640000c0c500010b2081c200100c4444050340c0648a42 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278426016 1250 278424766 278424779
    0x30a1404050706030c020f061f08032b020a05090607080f040b03060405150108040f1104020a030605090a36080a031d0319030e101d0118080403020d020f0a 68
    0x1210a40b0076600400d2034003030b1990840e8030216851f101d031001e08000701041e80340d2811405007002d41c2300540400e000c02400101d1603107010310040000700310018000c5d000154840340c221004c030b8540440030b00544104070b058812030300b100c01cad9003c0110403640180c81b05c2007403c00e940b03244603010000303404840000300400c43c40100c43c05107000b03000a035401c12890740c0d0002d4207403954443c0300c05140400c05e44800100000d42144525046522400d4a0700440038101e002ca016a00002d03007000229441c1d101c24401170812500c401c0e44206400002d000700f80b072860b08600300f04a1130100381200d0f8504468001c429175040000a40d043d0310503101e82d0b68031207096000f001011842c0c106000941c003071051007506200001a41c4401901600340b190030880c0807001e41c01000c00d0405410207004100c1c02c00d41440c3d40d4460007428144201c025501d501c107441105003145c0b003203000755407003500002d2000c003c2a0304a080d142540c0d030680f20001144070768000100009030300008154420401b90f40032426 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278427266 1250 278426016 278426023
    0xc091e07020604060b0303090f060c15150306150108040f0302010b0a0e06040b011106060112060f0b03040b07050f09010807020309041b02010b060702030c09061c0503040f060e090c030a140405 84
    0x4500a0f0320800030300d40031741d0030103031640b2441000c40e82c44294400e03800020314040009042440000c030440307030000c400c901da803c01c030701d01100d00c0c10501810f039500300d02c2400c091001540c031115400908402502c5000040c1c41c2c910058006004507000801450815000754070100c03480d24020100d5104594582a000380d644045690b02d00941c00d000255401c0d50017105400300030181c2c1d101500b10350359044011560048480c00450380f154440d000000c0c01c0c000e480b1400080e12041500075600d15090030038016850700500600e042203010060b60814402c040d00780d4900541c02d1034042c5280e00d40000c100d280d400740b410583c0d4024074110b8055403203010400f501503001c110307400030320214100c4000c0240c0c0d4000c402e400380d015001400031324100c0c580702036040d03804040100840380048406500a810700e59900c811207840d0b0000070103100c030402030f40450000704458600030b240421036601041c01d4403005480350340e402c00c0102c0841d07204101904244155000200c014a0910341400c05a64 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278428516 1250 278427266 278427271
    0x1314012109021804030e01030b0a03080706050412020d050f1c0e1c020106140d06061a03040b0f06010f081005060f1201090501050a0e0601140c0105060a05060301080c091e070206 78
    0x400d0b41c007081c400c883c01520390b140c03c0c812605501c030404903409560054002c1c04500c40d51a51041c05080c02000217600600034004c058001c41703001605291030f00e0058555900307440401c3c00c0d5071004046940c840d5000c070445007080b004c4c0c0c1c42162940c0d0501d14411000c1d940f038018601d441c0c10400c58110140e4000392440d1b0400090060803240c016001d0140e08880c3d85002c0c0000000015030101d0040c1003a805286242e442a6000030381c0b6692543c0700070340c5500c900b02803081e084000050005100ca580440b581003003280126a40b00e083c002c0000c0c040c6280311a1410034040c5400024591012031085840142400b900203595238481202810f150b52044d0709902810390300300004940c00f4214850507050f80c030043d2944c0d04207400c1c000300c852034070001080c00b410845181c6842c0c0620880202901010000800201d101c0c05c10000300500c2c5000b40c3c01c002c1c0141414001045035090026058041c89000d03030309402c2d0754950078030307000701455070318181890490000c05000701580d00040091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278429766 1250 278428516 278428519
    0xb0c0a030606030b01051605072105010b010203030613050603010905030415030509060915040606050d0804050325060f0c050a03050a0219030c11060c011118030102131401210902 78
    0x124642d22102d0603411030701c00e520b11900050040c00740c2011003414024019400d802441200d0242d69200e2a10364042c1d074a0312001d200c0065180d070b420400809014840c084413090000d10300303501d86500454504000c1c440070710b80c03007920b80020441c140c07400e40c088a036003600103055a542d961140860000b0603192000040083d140100144c240c0700042f91041c01890980c000d400e8400e01c420600d140b8100203081034842c2c0e0359071640018a42d641e22803408410703210f4451303240c94038601020181000742e0224082e01685440360f1103185419000c040e04255495030903d10840b8100c00030407180304807000344c000d0052103803a900e08107260304000a028074034016400c581041074407110007200034174603820050205588403a40000580388003035101c10900090304c030a04041583d03140f142502c0070320909400c581000503012400d111058806800100d06130025071410069001003880700b1600c0c418508410240510301809a1041818031050300381c007260380c00081203024240c40144218078007203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278431016 1250 278429766 278429771
    0xd0810050102070b0702090c04181b020d08010512012009030106050607150203150316091d070b0a020102130e090d09081c1b030207030c050f150c01090b0c0a03 70
    0x19041d03200054110a44100409071400d2003010b6003400811840a050740c2c02d40d0100303002c04a02440903800440005c0e11004d4049400e9480708a1040300c000b026603124110f4012710b400204090308860300c0d1341168400e07508140c0c0188004400c90041c40b080180c0c5002442e82c4420400c3c040d020000f5005814088008002c016900e4080054600c5960f1000f01003182d0328021891a0609501865020701e4101103600030044034070009040404101d0103801e2001a18030610844e4624810443c41480c100c09508440340a60f00640c0d07100140d1252041400c4005030382c0c20224802c3d0192040144041e410365481c94a60000d204040412a081ca510344913440d100d04206216006c001c0071207002c50050139200d001414042c481d1a1580611014010060b0918a010080100c3d2426140c00baa01601c00207045140c20342c1402032650000b80318101540d00201c1170780d03c0400c1c020001c8052034142d036a0325035130401580909045c9034041c0002c00c91804111030f040c68040101041d68155404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278432266 1250 278431016 278431019
    0x7111f0501170d0f030b010c02220b0109060c060504080912030316030902010c060e1e0c1e060406200709090213141906152c0603070806040e0d0810 65
    0x10740c0d41da44614226100014003061510312014000d41c044070020006140c90038046646801249010343c48500a0003d40007408ac10709a501c401d100e8454540c0e824600b103507a861401200030030720744541002400141d9a00c0204041100b003408079102260040c1003140c54104440d410350701c90300210b440881c402c207400d8034101c150344030740700d21200d840d816103030b203803032030800d5110400101a00e42010005100300383c02104d01c5030404010180612f00d841c014a11501c80409005845007004118039001d02c14080c10f1082d40d44680560b000e40d2000e00e8003901407901c02d41c11800c225175034840e80701b86010300c000104000003070f0781000076918000c0d1111041c0301584440001110040044859443c505e00082810b12182d02c0c203144080b400b6074004a0300d5500c4002d0f4200b684c0d42c0c00310700307004a800309804546885041e6000c03c04425086400003840c155080461000d120007009201003101e00d100140325a0b850f64000003184040c2c008403840714481d000d014007401e10640d90243c48801a140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278433516 1250 278432266 278432309
    0x41706010f12080912010b0109061e110a0c0905040308060f0306010605160c140916020c0105070c170c0901150905040221070807030501090501060807111f0501 70
    0x18800d040303a46a91404819614058460456103441c07802101c000e034040000d0409540c0358000003802c100f2041c00060912080030014041205560110040c000814131342004c0c49010103042a80c04410f0070400c0f001e5250f41086403d00215541c000d00081d4504400f01e01d422982d88810310461007074542000d1074032280100161a0340c0a480b10f40d269001000600185e44160040d040180961060001c42c81641ea159145840f058014004050008d014400245003901c04c15400c50501549100c0c20f0b880140000c1d01e0b251122665070600200080000070002c041d241c6100510380110246010400f9401c0140c440064075000b5215040c6640042202000c45685100b100a42c1e01d50100441c0f82c03009000c06900070107240b00c0e20701c08840c9180c617071400340042280f0038446961101154540110007804848040c0c000e20000b900d03050050200d2070300b01c40301d41d40000382d9080c44102d02c4452490f0350718090801280340d4411003030110a5108000c0c0f41c2110b8140c0304000109015228040f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278434766 1250 278433516 278433523
    0x108030a0f0903110f03240405010b010e0102031210090f050601030b01090b0913020408011407020105090d0c260c0a140609030702060705070308030711010b01080c0a0f170c0417 78
    0x10140401c2403907081200b9070b180c40e00103c0e606040180c1a030f041c4001180300d001207e6400a016104142d0220410041003420702c501c000012003420069200080e000000750349002d0815115140c0f410b000104400e84100c8604400a11000340240006020361030f82d00c018040aa4a243c042810516804d110b9070003a03581c0010b8851040c9000e00300b445207070420034214408204c810324140c0c20000842c00200a00074820103180d522548a114140392400908413880208042d00303e8111003010440c0c0360b0b0011900390500e8122900d05002c0080c030046034154510141c140c010300c1c90000e01c0459000b00402c08000351070190104414000c2d29038089a110740c02142d415149400030004140185032910203032603868010000c4401ca5a12952400c00301d900940d102d80100c0e02005001c1c203501404d0050205008080c40c6c65161401d1404120750b0b85d000e980140700c2400071509010b514544180c608910001029180c4078003070424280001c1d4680c044d01410300060b01e5803109169034807001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278436016 1250 278434766 278434769
    0xd2a020603150402040f141005030f0402040b21071401020303010b090d050312010303080f0105030114071214010e041b080303040f060204090507090e060103090209040212150108030a0f09 82
    0x40e1900746142e0741e240c280e104101026185581c020b600b072001140884914841001a00054064814141d041420401101008501c1104003c4c04008100151b01602003c80e0400d074140d60104880c182880000e03041c2152451428113984a03c420204030040015101d04441584a03490030f014000001282c803407109014220345001c003004907410750300380041c003209014020410b9a017404021910031013028400c3e03000380e001071a5038007803040e0790600c903070f4140c01800110020000081c0103a0310640442c00100a00b084c0032100c108810f40701019008030758046c2142480a54941e12620910300b41c0e0700540d429070b100210b10001800420500060700c058540c01002941540c0d141e5076420701d143d5400000300c1e62560240b00004034942e590240ac1d01a2039141c89200e02582840c2000209c3c08004100c681014200055000581c41d401e1441d030300b01c0c1e015102604040c00d10b901003484c103021840c1c800e8441040340000a90b0006c08006811042d83c590780c2c03000821140002110340c0d540b40e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278437266 1250 278436016 278436019
    0x71103120f040c050303030c0a1b020d20060d1a1002070314070e09060402030c1c0f0f080304142a061c0501080102070302061f12060b030d2a02 63
    0x20004110014a80700305076900a00c1100d0004010f80c45902103411030300140c440185a950101d000e00405400c024614900c0943d5402c0d501888401d40020752150f1405e0005054284a014980c0d680700407004003603503417074020700403555500c04400382c03034014640e44401000b02040e68100c48050f00c1c2000c6c00034907030000d0b41c3c0145002800d5485045908252202d062898801e20780002001401100c107140f06903000300285c501032070180107140c106184986040d1094070a102009d09040460715500e842036000600b110041845140044040115801c080c00b80040801044100321038840c21a42c407002140680b85a02110301c0d0076054802e40b4070111503090111212200c0354117094014064005000000a21540c007031261981211000c0e00040c032144d40014054051540401030319821a42c85040c401841c085044c401d40d0341400c601843e1b8020141c000160309003d0690030020315942c0050944020400500380a4105288014181407060b80c0127111442c54600364680e5495580 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278438516 1250 278437266 278437297
    0x604030c05090903070210031409010504081c0905010632010806090c0d090b01151809232505070b06040b040e0f071d24040b18071103 59
    0x80c94204003511100403c058a02d11081c000e500240c0e5499031105d040010540300062104844100124040d8000700711403c0d90b8140f03414840094035450403540090000990340502e0f00d80740b40802c000d00442c060203001d0b0343c2010804a4042c400310007100c0024600403800418940b90343c1c2c202c0707400481d80142c501042d9039034001051402c0049501da40010a450003d00e0886480c0c03d05c001c4808a40b400d4846c07500401c014003120000501c841d03110035050900340750720001d5000c000c00640050003085202902c0d2104418050b500404a01c03c0003610380b0101034500d4034600204c010324a00c03419840c0d1303c19586101000d1402607040301c2a240d0000c0000d1080d507501000e210181070387d0784405801c207907200300c0f4078007001040c0500141d0308201005419030b0740c5801103002001030380d442c0802031200b003d02072149940c6d4010000c00c1c90405901081085100305000600815030705200700c1d040b102d80d844420846000d1441e80b4492269511035003004a00440200d5482c0940c1100070344400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278439766 1250 278438516 278438519
    0xe010816030305030406180302010605040b2b2303030a06050d0812180706033207110705040c0201020903010f0c14030a0204030f0803041e0b04080307120e0f0c0604030c 74
    0xf807141d00159440350180d81c000c44c00e070071000c1455070764038060b01c805d40061b55110030511540c45e090188094070901144c80410706c2a0500b0035007110071040300c02c42e29001c241c5030f01c4008c00039940703800ea50100e014810304900e01c01d82c042c590345035401158912509450038202107000e14003161140c200c942c101000d10f01300120340c6000170802c100a41464180030820304124080030041018402901c842c2c1e402080c0a01800240180c1503e40d074007016500c80202d6038003400c0b000e915140ba41c81101c5150005115056000c05800c204041d08035a40140c00c0c0002608070700d40540040a001e0403e40003003010303520540004007200c03c86003040000545810340c4501040140b0302440d0421216480146025501d0390b444903c0b4124100c2102c140380e021003000180411144040034844144c080c1d4024899190394140003481c0041c001007511501002040743c40b8850500603070140340d008000c000311030009910b07ea6400308800040242c1c41118000c49050401034141d074100c90707020300d010040702d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278441016 1250 278439766 278439773
    0x240a03170a0e041e0b120a12050d1503050f0c03030f07080d05071e0302030106021203181510090213050103090203030d090b070e0616030e031509070e01081603 70
    0xc0e0310014161040011200b0400600c0d0b60742e202e20056010035500f0008010600c081100c2907030308803500c483c89024440084c103c40c0401044903144564000a004041406100f083d9002d000700704803d6511840d2800325680000030713940ca1410380e8000e8040380c11741c1c03202d804055590014000c41d1500f64209001c1c4402d451044401790030001d00c910380c01e034180f040d0081c101044402c201c2d02079000400940c1e900500c041c0d04021400c004d0901d01d0198a550704284020350789112407502040d12850000c0050344a0700708a0000c001501c224069a0700e0020304400c44808000507100303000c074001c0c0094006440c1c1c4440c0308540f01c00080650718004140382500640051036100800d9815020400281b241c87c5c1d82889440e138154444d071500350160070a100d000b0410b0440310f0055010300030801c005965280c1c5030384015081581440c11017000845200442e092030541c01c64500c60100c201c050111000c0049541010354002a00300341c1b0b180e07170301c91405a03101001c800030040c0401d50307001030011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278442266 1250 278441016 278441063
    0x117060103090b10031109010806041509080703030c1e090e0709050907020a0507060302070f170415020703110d08031b130815010e06210114240a03 65
    0x800504001681c6510358941c840161400c95910b02810f41c114001c0c81040039001e20342040c603d0a0300c450280d50f0500040036070f5400d0181c009000c152030a4142c00c0c80c181c8580000c40c0b036541c0070703501c00d48a045501d809130103004500c2c6200c01180214103403000d008460090131103440040d5036041da0180c40c003a41864000e001426000400c201814003080548841465500418903540184140d15042c101a4200740c40740c0c1200080500401200c40801c00074101c000c6402d800500310240305c40340c20340c50082d501c500d81c04002910244c0c02e036111006d0f008580c03202100e000b181045400d0742228200107020421240041c100c60060001c1343c446840000c0d15007017407010300030703480c6031641c0f488100928041c0e640c003841c580d612034040444224080e214960050500f1100c4030390606040c000902d0141802c03c1e0342c030194501308420020300500b5009a10789080c030040300420703410650513145000c1c01100c1c2144074641200c1c0c0c4001da030b04014113840300712074006e000c0542000203054030002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278443516 1250 278442266 278442271
    0x90315020c010e060708010807060c02040f0b030d0504050a0807050904080d0902060d051f0312030e030405120303040506090609060f04330f1b1404090c0801050f0f0117 74
    0x5109509010303641d882102441012003034400c000c000c100a10b85003a00816025050300100d011b41c000007400c02c00f4030740041c2c0d8403415607411a00070a049506101d400001c14070034400e141c3c94414101e091740096002001030069810540f458152a0f4545024a075500300303078030400e60044101400580424460406400150000e483c046100d000e190005516900044180041e042d558410b0250005070024001800b0711410069024a80740d80c0300d02e0401d44841c40d0950a15490300c8268070640420300444024060040c00d902c4d1405001003500ea90b42c0040380c00f1210f070701c1140081054160009042407154000304001d0919aa03001e54000e207a210151080f599100c2c0c1900102c500094202800e0501c01e66120405510035264411010b55040c4100003401c00e01e0001c035061034128580011b50360720010708000c85440f410140602040c41076a0103a145ca5103000307038604102d0744c80000c0d14100c60b07045924071640c0d8a10010441c0200031819814042341120720212501c21805e104113a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278444766 1250 278443516 278443553
    0xa03061a30010e0f07110a260301080a0501061d060d020a0e041b050105070b01260a050a0213020415030b0f06070c170307030f080405010b0a06052106010903 69
    0x1c1e440d9021400c640c1d1801802c0c0c00604078514003200f0440f024809401c81d03540b100319440c004000180007040e168854000410117025484544890f800464094480c00f046680c2c0e404819903070360f550074002c0d4a907038602c9003c41700f9500f010f00001d03200800c20001c1041d0038440c40112081c0d151042081004001508104d8002044160014502d05d0411256110f103000d240c86006540649080c0c100344d403040e8000a040c02014008100410141103269042d110710540d040c41d9141d5580305134200b5440b184040900e0b00c01e4201ca50100440440c400c00c41920a95100700244507006c1400140c2c000ea00840110381200c0360b005a6040c8603800143c3d9054020340080f4419210101244150f4003102c1c0071b0f44c510000380320800041400c00c46a140408503200654208019564002c0c101641e001d5a5020081440003260500ca001e520245024600038034445d03d80c0d0361a0000303000c0381c01512401e5003000f12040001d120601c160950340c070480b416911210a42d0031661202902c220039031a12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278446016 1250 278444766 278444827
    0x509030a08040b03100501030507050702040902040603050607020a060c050a0c03081b0309030901120c0e090711011a0f03010b010819060504020708032401022107050607050a03061a 79
    0xd0003084040000300080c000d8100324954902e0000c90000c0400c0466000314101894442040440c507880003c0d1030110f681214040b03040000341c0009800b800081e08064224040c80c800d0001342600003d00d4800e051054a0501107000d1080b01582c0500407040f00b84c0c0071a04128414001a100b00105a0300c6000160740b1481272040098846c215001151a131480781d000003501d01c21582c03c1405803120340f0b814001130181001036100101040c900507101800f404052001c0303401d69016028081c15040307407030002c10100c40710703410f60b81c202810302d00c04901814024044414070304040c010360852007c10f031074007030301030321840e01d482445120b0524007460160f90340030105440c0e68600003450b415004101d02d58890605035140420406000001c407a4015010003c5d0060703600032946a086003003184c60a0390100942e80b000410340b0036088001c00c180503a1040241454201000e03040c0102e140c1c0c0c013000210b131203842107402e1860f1144240c00300902803004040c2142d810700030b1019a610302105 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278447266 1250 278446016 278446033
    0x11030402100302360a03350c010902090117120d09080f180901030c050d0f06090f0b010504060305031806160605061504180e1c05120c1306050903 64
    0x1c0196201303460480c28a004411444001c101002c646103260344008840000000d483c541c0c0d0000210081005d070000961012800341a006a0807424614080e643c170b00303140d40350b00e8104118000c1c429400c0480c42513075810004070b620b090a010700c8000103080c9004280340f8101c501982a140c0007804145040e5495802503030010301e009000e40088429001195220440c0080c1d0f070a09051600d1441c2c004e0010784010404601c800344000220380050320404046070703040c2800d0391504850b944c06400d060600300303104101f102c003c0701d02051070b009501880050b44c0318010042554681d2102501760b510902c0955141503980740e40c04240100200902d1501d038088d402180c025850305401d031251507607102000280d040501890504841303c80825141a08060346e046d00d80d50000802d02080d071703507403404d20f0940d0800c0080000900440f00c0f000d08080070348100400940c40703e0101c420703110704100400c82030829107041e5409107890034080c83c00681803420031a40ca070031050940d68503103c0d1030710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278448516 1250 278447266 278447287
    0x607080a0e0d1101051303050f030a06030206030127020a02030d11040302040e0f010605010507030f21020c010b0112050f01030f05070f09060302040e120a0c02030102280807020111030402100302 85
    0xc8850341810303d4440155800340030309001d0071280014604c070368205524a0080c00a84e1280c01c40341c1c0e03440c4a042440d01e0703441d03c90b842c20040030700b0b810003504841c00000204a4004c10f0010f6005003001d041005080c4200c0c00910080e0b010b6000c0c001e003d64400d101000c1031090642145407880d400c05007040c00c00361389400280076a9848141c1c042c07140c018104181e030515082c00760f080a88001e00f000ca140500030798000b0250b40e032404040c810007407440d0700d20344a02201000390304043c9800300f00755100e41c0f219407514024002c0c446114003185000380c1c4000c07c7d071842d0003180e02c81d5000d220b891401e680307940c0303a5901c1d1181c0d150b0101c13000c0c02101004600c1890744240d031809001845d41c0000d01c141984140300443e04c41002c0001c0781cac3e00c030411040380d00780010100c400046032450300300309034200762011a0290041c2e1001589810340100c48200303400441c5858109200c0d641d982413030f1911140800d030300300c4001510350901c0110410015015013001e408040000c1500e1400610b046070350301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278449766 1250 278448516 278448523
    0x5032d040602040602070b09031b0102010f060807080706030603021318060c08270c04110c0619111327051501030e0d02030313060b0a0603060305070b03090607080a0e 73
    0x4404450442d07002c28140501681000074030054602da02d0054540800c441c0040ea40320403080030604104081c116070f8410780d100390001600c004c102071051107065291a403071030f280d0007a40a203840b144140b1000140c0140301c1c0c01102d0850390081d000700180550400c080d0084c040c400381c01d06441080341c07404000580e0318881c00d0818081c958a0344007604010b1a85000d420303000d00708034110001031102000a5602180b101ca15036821100002c5580403c54a0000350040c400008414001d00c0108806001d05094072032050f055034400708124141115444001d00480e10401c0742d01401c4072007030020340180501070324100d10b90740000490240f50140402070350740440700c102c0d904203107408800440d6014001d0b2107920100c1c0c0003626500749913540085da00d0000802d413911800c20040c0c5401442459401703103034080d070003a040e005800d03101c3c2400b07000703080d251104031954410b8400004902c04030b10241d0b0300074031108000d0505d544400d80d040300d070b200003c0c10b11850207035101c034024911107040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278451016 1250 278449766 278449771
    0x130e06060708121e07050306040903140706021c02040b0414010e040c030905010c1e1b12020d020c041505010c142a151b070f03060f0e0c0105032d 64
    0xb80d180c0d55403420584c45042c000070303078404a003000015000e219280c3e4014003038030340c044001d8900040c3d980b50740c202101ca58690044c850f10800000070094140f1400d500108074410220740c650b030744203403070080700e80c2288114403651450300c1060009124112291040140204051401c1402800d4060000b4111403050804202183c2d45501d9141005800c0c083c40300c4a480604154284401288410f81d5041081c80d1010400c004040e00504500c4c425400c1402503400035044c4048104101c1c0195035501304007400300152150152482407407038140503002c0e00058074015150100e14110065400c0003410404403103100c0e1000075042c607071a08025141280c2c500217000c02c0c50302460241d00b00800da01404441c021039101040060400114046482d01c0d4041903200d00f4180c4660100b0341020b285404c044403c5041c003500105003e002c0c0c000007a054000401081542e820700022942c0b00f96034401d8a0104500348002903941510780200395864815004ca01d401a09902c1c0640154108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278452266 1250 278451016 278451037
    0x30203030d0f1a1311070606030f0b1b0a030b0d0b0a05100e040c120206040e0108070e0109020316030b030a023a1e060b120d020c030102130e06060708 66
    0x8a600c007403808607543c00703110301c0030b6407072010030505000000100c0c00c130003060030f00c03844103545601c5c0340c00c180c094103021102101c0d005031081080545034a8902580e520054040d01d030061a00046441461665014a8001181540c1d0b502d085589181500900381056549038444c400744120b402145004540c544252007403240040c9600c1c1c4a4809100524250040c0503429a000200800680e24101e18030942d031000085070088001c510008803944140d4200d0035524418200001d0303124030000b480750540d12400c161000c3c5a80324046141203020460700107800b40c20f01034050010902aa00803091200c01a080c0c8040c00c5803034000ca400340c2c6205d15a08403240c1581d9001002c403c290042503044101015892800162501d642402c0e14401400d880321103541c88101f81081101e83c04030503100b001034038005111252017002078030740a20ba403d0801500078034110405600c1d06100301c81e2601d0070300700d50f4004941400c10080105000401d80f0342c0103242000390801145005000d080d20214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278453516 1250 278452266 278452271
    0x70816120c020723061213082d07050c22140402100c05060411130e06041b0b070611090901031217040c12022d0406080705010512070306030203030d 65
    0x113042d5010076641e480c043c424064144c3c0c140b0800c240d43d66902219804403543e8001078007900c036644040007052000750b00510f0100000313403841408070a07041032090780103120a02c418082e01026100c4552041c4c030306c001c1c0b0540245044180c0351800307600150744c0821000140031550038400202e000c503040c038101303a00d60711000e10802045180580d00051585050b141840185600380d0700c03182c0d240005400184078a02c603862140054a466084140c100b03110b00050060b210080364541c3c5401c000e0324140d42803a6000d00000945110600100864079034412503881c145158850b800207160b00e4a145640c0d0310100094519581e42e402101c0c040d6000d40f903828040d00307440001500c100300710b462942440c2e10390000c0001045c10460414111010b854040d0078200b120310008211403098800300744903060810381684000c40d032129020094200342c508008007603e0345e802079071ba1403040c81080e000035801c20110010807441198140c1200c054100403c4664803139000a040d03812503100700388042d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278454766 1250 278453516 278453519
    0x3090a050601090c14070f020a0303030b0f03011b0e0105071a0717070c240c05041505043512030406062106020a09030f060e01050f070816120c0207 65
    0x10080c0700d16070041298000c10041c0300814100501101ca04810b4444485404200c041c14000340195018003660b00a2002c09199103c0c50082c00504401d041c40380651181e10015402d402e0520403c80c8a0038461119200c0c025840c004655001240851a0400000384100c60005110303041841300c92040120182c0a45040c2c1c400600c13214030410140703080200d20f01071040a9401c465446840da402c10989a8010319600c1415030344000036103080f00c503a103003140e1291410fa20801500544d1401d00706002d503c0520041140d003070045026003802d5804101d000c00000d01034613000364940307010000845c00306039942d60b441c1c103000b0324200e140c6035003070000200002c000703540c0b29050280440d028882034564002803201d080c61500d1500500389980080d05c421624003858410004503444007500385015030030319000e00070b4901100c02c28007275130910000c9454034443c0f030311042c4107078141e035203031405070307656074040c0e20f1119402c0381602c11721440340040c030040e40c014000c0c1034140b6a540c0007082d066 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278456016 1250 278454766 278454773
    0x50f0c04180c03110103020c060a06061b11060d0e03190807110303060409112805010e1f0903120302030405070602070f06120e1e0601050f060313031403090a 69
    0x765407420190802040d003a1598001412031041039041d83d0b08140b080041190380c10041c0d00900c540245014548039000800c5412071007500310400b6200030303a49516540880a00d800300d40051100001e103c0328180682000b1400c0100c00b4010a004081c00410100000c100040c203690103807210651030454544c84090f07680e004805160030907058980b04816078480644191a400082c1c0b0b681d100342c1c0c0718003003001402410045411207407801020342c49181560904c800b9001007042d04c58112000070140041c0540c010078140c0c2140d0006045c1c10740341c085590f5076580c104c003216910414403111300310210104210240c0c0c42c400315a25140180c0da07043c01d09141e8985105580300c4000c5503c00d00c020b004200344000101c00704c2d805820091159252a60050041c0001300c00c0010b20740302c0c40b8581d0141000803d00c104154050360107488060344c9500c10702510340302e032140e100d810400402c0850b5219140083c221625800303440c0c40203031101c1a0202c10360503881070b2034000003076000701c10802c2030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278457266 1250 278456016 278456021
    0x2151e0c100603050d090b040e040609020a0503190302060f060d030507080f0a090323122107051207030504030e0108070e041e060b0702100c08070c1e06030b011713050f0c04 76
    0x180400704003423800c043c58403070b1790b800048000700000e01040c0c980380342c1421500c40c010f500e070180c007000301560a07140c0c0283e1036040c00c15104034203400510540f40030400d0080e250400b40d00441c406452031200307084a807820345559000600c1162200400c00008006241c054041d0480300f0706a51000c2c040da2a500f4030030118180c0083d40f400601c07c01607006011900040c9503841d0039070b11546c02d503c2c0c0b290b03c403101031803a500203400501c9103c0d081c100f001540e84407004102180082c0000141500c03400011822a20102d800901045901c90104019130141c50440c0e030251030b51400b143d501503c540850f06035040b041620341e04c1c140005074042000150300640780902a10158103080500580010307106044440c442c0d010320801c0c1c81c140c81440901800c6503111500140f24420b82d070f68440e00c07294800b40025400c0303041c0d42281000b05402d44280501c4c83e001e001603540c8400000685d102d8207985d400600306250305a00280310000240c001d1041c107a025008001401441716010280802d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278458516 1250 278457266 278457269
    0xf08190c060b031b12010e03030405010b0316080d1206120311071d060405070c0203061006030b0108090a03210f0e160e0a0b01020102131202151e0c100603050d09 71
    0xb013504185070601d12000d000f18041d42d0f5110407640190040d0000602d6030060518000b0b6041078003002040001f07100c41500200303c452000d508480d0580704544450300d01240d18091807129401c401440040c6a119a091075603810b44150b00013a001d654208005510300944001c60104480d110418201d01c0b05101510007040020020510039184806032000c00074018101e81c41241d407000070524062050080e4140c0035805001c03180c0604048100d40d00c0b04c1494441c0380e00007414041c2d408182c1d4420001d281c01400c02c44014a09088155029511030441c22000344102d9052031036684040100c0c080c000c03d005c10301900081c14004192000c2c180031070072441400d0403031032590420940c0001c0407d107600540d80c081c00102c400400c030040f80644659028515418107014010440a04072084c01030205d100316914150707100480541c0c0143e005000500502001511455040d9141b03c030042c50582c074808240c90500d0f035030303084690841d8490340050311558001c0681260154100c880d040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278459766 1250 278458516 278458519
    0xa03030e030f1c050d180f05010606020307150f1e020406090515040b0c150114040c031b1d0a0902030609130506040807081207050c010c0810030f08190c060b 69
    0x407494100c0c404000003d94031000701000000501800703050040c2d0b020050030140d94180c60791403084c6042052026490010036074555103400000141c99000108960401d0fa006100600400c0c3c01c40311000203204000009140b00e486a4a00b940c0894900c0407407900c0724611001600d072030502c5c50042980b00c06820842c0161440d400b11014441d001050380c04a6400640c0180c0e50301c80204d40340d0030801c0c849041c490f0a170b04e090000c142d850100b40780040c03004042d1760400c080b56249200301c00fa039404403429000300d80c1c00001301c81010711400006904542e008000c114a1640d00c1c00704400402903031210803400d0340030041c09400e00c0c1181102d034015a40902d000c6e82c81040d9101c2d030b9102c1030060401410078100082e0f45041100b514151200c0d64105040c1182c2072620060280166101d03141b095001d520b044108201e0038082c81449024111004040381254115500c0d0000d2802c4801c0550300d5103000d02218100700507800d0031180301c24940d0344101d00e89a20f4035002050304e03541035049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 278461016 1250 278459766 278459773
    0x100e01030c1a160c090e01051b090a080a0602030105040e030f0d050615120103020a09140a020906071b0806013c1508190618020a0e0a03030e030f 64
    0x4101007085001e410342070300c007408030b000d40a4404000c000368900c50218404406507403d0000810720003c000940308035180c5400038050b00b03001c107003a107003250350440703c4031441c59000c001a10b05501c0703980501040e0b00040c8c40744802c0d545a207409842c2c80071054040f00d80c5600000140200d082c50300419040c4003203000114107111018580e03041901031603c0d64000280d6850008409903a040c006d20510f80d00e03c180150380d2082080201c013050400d0106900078007540000190303d600361301c142c41000402e10000b03842030301c2d001c0310780019500c8580f810358450410f00840c0e0120b480c006d041200320244410200340240741683c1d41d82800b10580c80b065641814810305035150900c1055214228940841c0900d15019070742005640300c12034014039180c0d0300b00c000044400740c0040600c0e00507244103040580080074484e4150607100706000b00c42c5480e5500d26402c05c5542c01da00542190452810700701e1070f050301ca20105800f070145a00c1a80000c80c4428280c9450405101100749031740d07900c0c0074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 278462266 1250 278461016 278461019
    0x1d1204061d010207050d050f06150a050103020904200406020c09070807030b031e0d030b06070f2301050708070806010e0a12030915091a130306020d02070203010c0503100e01 76
    0x60903000c40c0030000c00c01c110080c1c1e02030706103a10901056002d040000d03c0d50748541c2a030b003000b561f0342c104803070012244d22840c0081174880e82c010044020904004124820349420000110f02135004240b800d03030000c5e201c1004192001c540d00440c04d41e120b0801c6015200d61921400030b00d01088481000c0c080d2030f015040c800750903402a82240c2c018101c3c1070201c0c0c0ca00460012910b0b142044d01c24103203d02040c074000503204408190b440d410411580c06000450704041000071318410404010402d8080c4c001038000181a04090b0303091f401303012680511070382c1c1e0461207803d603802112000c00094540080104644c0c00c1995290030a10070318185004961010100703a004205018500b11a2084045081058481e154800180c0580500e03000b90f2824000043c18102c0c0350b0140980c03100919004c911070340400c030180c2c1c510900e4400d0340c100c180d00d95282c010081d880000c0d82540f8540070045040503803401d0083e242038424607960a990380c0707821244e40041052a40100268000c0b0000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 278463516 1250 278462266 278462279
    0x60507020901140f130b011403100e0907031a071202130302090c09040e2b0822021c0201261b09180a0c11030d0b0f03011d1204 56
    0x3080b8107684500c604180d000d80c1d0b0b200003602d0046101c0825600440a4000200c007000c15048152020310a80750030090100011313894045000407940481e01d0642e20904005440074254459001402c020036240d41685a80741c1250f00382400c40020209c0008909013304d440d40407500003103000740400c4c1141058842202450420071502c00a80700e0300c0303004045031482d0040b0b021910900c0005000f00000f400780e000b1035807501220f0340039188030000c0720540064150446051807480b420342d0740300c407240da9502c001120030703011031480c059030a80c403c0c0c1e502c001a10782202c0b00e4101c038410600c0c0c6009400c0ca10005100b100b42d000740e0184a481c80d200c40c034154445c401420707007014031241b90005501282006410502581544640c010000560150014004081c45000c0c064109050100da01c44800640340b1494000e44e07450301d54000c002d49226850107a0141c115002e000342071211843c03003000068251410008080d00b800f18215680a40a008000d0b0040c0c41e00000710b00303800e1514008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 278464766 1250 278463516 278463529
    0x3120307090807090e281212150302030105011a030a0504290901050c040609050f0d051515010e0a0b0c07030b070203090a1d010b030c07050703030e13050903030601210513050706050702 81
    0xa401031241c200f110040f40d4007802541d410481801150040000030340e2714110914070150b5110580c000d502c0c14001141480d501c1c006003084105000310701b403035900d0340842c2a0081c003000700282e405180c002c1218560401000080121101c04411a4080e0800410540c21510060451410b0344000c21081000c590455502402c072541103d0918010005401103a1440080b010007000340c007901d138441d801800c41204d001c0c0900301010084640d0319072100103690303070504402010341c8550b40c00801c00118010200400f680020030b0190b1304099601c6d924041d1304c81e4280c40000158002240c1d41c0028109040c14600400306d01060401450b4500c40c81d03500140180207000c865407001001410fa05c48000c200c80001d940305044540c02540d83c10000d02480c078a1071018445d900310b10504c1c68003c00360080e00d0041c00382c0002395166403554801075449406096414442c0c0d00c1c0c602e09990700007071a1041c0c500c035003480da6070404d03011411f2a18500b001078a400032401d01005003d1440941c0741d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 278466016 1250 278464766 278464843
    0x308132303060a020d02040b0a0207030c0b040b3702010b01020c0405040c12080c0703050a031103030702060a05062e082a0a03090605070e040b0303040503120307090807090e 76
    0x204005a03512051017440000c0d1203a90400f182183c80002d100c1c1005500084000480f0b004030741d05605075403500e0020219201e41d100d0300505c40024442100e80240d031008500c101c40c4151141c1c0380c80040440140203411503241030038090307503503041ca0380c0301c07543c061040c94400401120b04000c0c070306d0207513940554000103011b16040d442071082c84504004482c0c4c00c0f203c46402c040304407070040d903681c40e0403070743c883c000c0e4011400120b5038159080c011100100f17881c011202c45d0090b001d16952401d000000b010002d00040e0300c000c020044400b10f0261600f4181010026440540c6200c4102c00181c4032a20240c04110203000842030029581c10034011403030700140350030500c2d0f6900107100c021405030803121000b0346542e20302414044030940140d0707071414885040c0c60510803c85d00e0420541c6a000758418150107410503400c3c2c100242d40d1900035a809140d41c14503070101070f2961040742c03610446030000818155900c03841e003066642080f44840102c072840b0f135031222002084084000b072003913 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 278467266 1250 278466016 278466031
    0x5040b18100509030f120115051603030906110c010204080f0d020d0c0f14160504180803060a030f03022b0906050d0e030315010e03071406070507030813230306 70
    0x702c00c04161191028030480c2c00444070b400d580764035046811030340d9520443c00c0c03040d560b81402080d128810540284281c0c3e60800440d000c40b42001d00d140c5081e000707401000c004a841550b10242c0e14100c4140802400000b200340000507100c6041007005450302065003c404190b9008022055a03d51b0004210340403242900c2d0072031242900d807408041c003100c1044024080000c00b40383c400c00e00000102c2c00110388690140f500426544c00c00d120071103d803021100441e00f460032940700072485020095801c60b0b0094030245d20940c1c0ca07100c2c0e002050002c1070490050b0000d055807202d000c060b8441101c8111201e49190381101e00c210054140555441b07020180400800c2c20446100149d100c200e0002c0c0001c282c03660b900e0900007986540038008501808a1120688052142400100002900d0070294801d441441010401c60180c10900086406216444000c0700180c5010040c14a903070762280031000c42800c0901c0c030107011040c04035002c0c0400410801c0849130303600003001794100740d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 278468516 1250 278467266 278467271
    0x2d080f090d14090a090c1701060e0d02060c01240801020405060306010c05010e01111b01051006031e0c0c020f0102030c060f1b04180e030403080a140d0f05040b1810 72
    0x3400545080d4901034280350a0b4021920413001451020780e03001108a079016940d032542078803445580700c102442c00c1c012400040c843c4010a655070034065144001035000621443c01c21042c49403003802d559610004c5e501e6811000580007441c82080400409031500c1c80c0258149418140452424000204020b041000008035001404001c0d4400c0e40c000445c0340007400703401441080320f04540d00004a1102102c1c01c44004849100306100f6140540e014059492845142c050101c02400c4d843c0e2080b0302042d0070705800e1030142c1305072090120749003054845c000115040c1c0100041e040c081d01015066400400090f01d03860b1000c40c0d0305611a07085094010241c4908220500701d21700e210000045880000340031803d181c0041032450000d8560304140030500090b581980c50340510310005111860038450703c2000c9000c2d0304800b04101c2c0101403903040c12840c0032048240c512802c10342d80c0866541041c0414060020501a40302070f01c1d00c015012034002080e41303a51585000c00c4502e80a9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 278469766 1250 278468516 278468537
    0x30f0c0d020a030803091b010f0207030206071712071205040f0b0903041203020610060e0312180603040609150c0914030f060f09061303050d020a2d080f090d 69
    0x541c1e0b000c054001e160403040b4641c803843d068039643c2c0d481d404080040d0840d076621004000c0b940c41405080303105030050b8085c0c00500d00c1c41d400d00103250404082141e0320014509512120b2240307001814268240322441001418103407005458644003440b41d106c2c0a041508100201d0b0b114000715580c958041e190915642d2010b5103603041d40260f0b004422040e501c00428424998005141409484bd030901000400ea6580d0261959808000c41a8040c0c22001600d0304c002e20780d04c040c003038074164404148004030f84000001c0303a0f07074011182201c0e8030307907500c41303400c00d2103c16204520003c1100004020786100e00f4809000340c0f40500c150f807910080300082030101c0c1c8040c00b0700c07509005903504940d400c4c240307035611142c2a1801c803100c00c0b461180b880041c03100840e00d8140480c4c26095140c00780340002840f4400040d602022980b010320001c6040161401e03000005c0c10000240440200c0d50810030b00750040c046070000d002201c850307000b038080c800c1001c00411840303050407040c14154280c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 278471016 1250 278469766 278469769
    0x70201090c0e1b041e05090105010215041a101e1a090d0203100501180203010614031e01090f0e2406010c0b0f16050c101802060f0a0e030f0c0d02 64
    0x2600f40b0941c03403140d800100c0c000400c1040d00000e0890303030000c0403900d542c031038450043c420911004d2280b103005a01100101920900a07403425822070b0144507402d03c00604890302c68106441502c0e0030303004554032441084014641c150794013041c01c401951107032032860071100c0300f81101c0701d82130034803081c2c8005100748160b51000f400e09044ea034081c0a0700c070f0b018040480800248001d2160019503450901a009103824a2084905a40c03441c0c5451103000c09864003038049400080200da4074001d0300e2010080740c5e5113200458002e00f5003031000b1803201c0c032000000d800d83e642c01164000590110042c1d03051503c90340c03085c1020b00c074001c0b4682c400d40d80d10001280c07011072452029181603070200600c8004886415150b1103111300040142b81d40d02e0b9a08119502c1c0300c0c0c45500317012a040040600040741440d0005400d0740d18030045089410555000144207901070100c0c41c00f44a030001e0710a01c01900b2012500c0c0900c01140501a60310420001d240c451090101c2c10b480342c02007071801400c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 278472266 1250 278471016 278471041
    0x50f06060d0e060c0c011107080f0f1b0a02011d011707020102090a060e010e061809100b0d02180a030b010e06190b0d0506041b081e041a070201090c0e 66
    0x4407502203089601134100000d0030b02e91644040072041d034650a0140c40200c0e0600031048580041c0d1169107140b4046210120754555008841c00e5506c0304000c2044414040c6030046a4036151000001b07015004854400988130380f01e040d019038500600020b41b28003580c0c00c120035102c1000701c41c0442c60b45560382d0030b04900910401041c04da000e81e4030703040810b1b030b60380c05180d20740002000c0c1c95202c0328900c96410000c10380174044450381d1010210982c000c0301c1c184841d1040d0841035204034800c280344c48588100380c54121003442c290259000c04e20151034008542a0b80d0708010035a1020040e904649070f401d180081402105008411440850180c0d00d58072104280103080c034a082a0894a5a003e041654010f401da44003490619000c0b8003146480e2103114403080e5609651408600d118209845480f401861004811040d500c01c1612680c180c0309980305034803a07150b20444244010a00d40c00c0301c400740001d021603150015600c001181c0c00102070a440d648810504642e03100c1e8801d10f007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 278473516 1250 278472266 278472281
    0x150d020c010e03040806010602010204240c061a040506060301030f030c050c130204060807020f07120c030212010c02120306090a0911040e0102040801060902120a0506060c03040f06030c03050f06060d 87
    0x40c5619001281d03107030a4010019100350b400c0a429680700c1d0741c0e0740504a0903402140181c0202481c0560644810404070341003110345e4105040845c40811551580c00880b0301d088644040c01c940289404400e240038451581d0056049900c0c80c21541182c0f500415401d0091006042c44001f501c18024071504010030465024001d01008ac41c20720b40315420b01075049072285c4000b1a42c59000701e403500f40045003132005003a0901c010010940307006040c0207000b21522060724a4100080040090b84900c00d10300414800c4400100d0b030700455500007480c1140103240d01401c00c20034001e10009540701413a8031741004c600c140103e000080c604000d400b800c0300c40d4010740d016190900000b2100c40c1074019104a400302c5008214496a82c40020164841c174920008a07515440c00104035414a03485141c00410150102d070600b8050120350f0300e0f65006400403c105c0d9002c082c10049940e15004109410445142c00c0c8802c0c201502014036004018203428030600c1c001c50f908544200030381c0080c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 278474766 1250 278473516 278473537
    0x1020a2303120901020a0809151b130803341214130504050705040605042615540a0615050306010605030a0f0624090e0105150d02 57
    0x1155041c912540b138002c1d44100c0910002c500007000142c2044004200d02100c1d8446c1c3e20b0030460741c2c0d0f62480c0d0352010408002c01084804c0184501003031441200000c1d00a0400000110b9030340a120368120310300e070311401401e610a16408101c410346400340020140f41c95010034482d001c0400c450080d01c04132140400c860003003001050b0309051030214480d1400300d40c400d03282001745856104003121188618001d600105404010800030f603c40c080e43d245640c0b00d410320b4840c6001c14160720070304016880341d45400c03041600b0240110740e070100c107a103005213600c0c0303640040030190807298412040c15102035801d00150000304513000c03004401c040c409201510192440e8400c5482c03d80010700c1031182000305a0540d02c40814242400140ca0b416518541c84143c10340e9203000443c07010703210f080340c850541c43e11031000090007120403400070fa520030720301d002d09001c81001d04010300e4000d5a074000c0b182c22015500400141d21548102d4200c15000036944c1d94410f030459900b070292140e0607483c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 278476016 1250 278474766 278474797
    0x110408030d090f0b0f040b09031809060a05030312040515040c0605180901081006080c01020a0b04030c0813051930120206040318140f12060106051801020a2303 70
    0x114505c013603509240f00d64407940400c42c50b030711a011510b9483c06080740b02c030451001d050150044d450102a40d581c0500028510b2041c1a1103901081c1560010695901860040c00c03d100c1041070600c14141c0004d0607400c4407900d480c054603038110012040c07292780140540099a03020002000800d00608103002e02000c6055035240311880e6030b20b0300da42202802074a81907011800d100301050130503080605a0043c0480006600c40c0c2d0701886018000b01c0034030602a02130000120000060803802405c1e400c0c0c0e207401c0340b0381001c1c011050320b00d20420600146801040c090f10200f07000c1e02044800341000001410303442c5903c50401e0403031080c05415492018181d0b9005a800144140310f00d209645240f8407808009202220008074051154480289080030300d441c10400c04250341d090004005181d0300c49a41c0300d05040c540281c10041c00a000020408040c0d4040c40403506000400e1008081c650519151064440a00031a10700c44108080720104000360810a030b0304c4180b2502040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 278477266 1250 278476016 278476021
    0x303150303020709060b0403020f040203090a061109010807020a03020a0b090a060603051605060313030e040b040216031103270105071703040201031508030702010e03032b110408030d090f0b 83
    0x81d40d1030f600c61148100d00c0e0b04000f404106c070000001a24210b0303a01600003013001c500c080400c006504000c160080d01e01c189a80180030403114051400e0050001d00c0c40e03591203044100041c01013200a080e034083d91301a400d0302c00001d50000d900d0a2403904145030160075280c01c814030b8240720500401510150070700d0004028000c0124240a0520006a071003464655610500c0391900088641500307a280310360300180070034090b40c1182c1c9180402080091043c100400240882c2c0001c40e5041042061000c0082015000044018140c0c840d400a50400300d1500e00342165452001d07141a04110007052108942d0040098400050344281028810202c0311001c5003543c204440590000307081240c00b184448100082409440e2801c01851603c04980c00548a0340020900c00381c043c0b108108401c8800480112084004a00c0244803140c51026004030700381c030001068184007203010401004040340000480b065103440c48401b1034a4040b5041240091020340e5020f08180f158004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 278478516 1250 278477266 278477273
    0x90f140f0a0b090c0906221d100f0b030a022101050f0f060d0308010621020301060e040f02120103020d2f180106020c0d060f0204030506070809010b01170403031503 72
    0x5441c4107000301e00444d0700a050010812201401c02c0e0ba80540292642840800904016206400c03640c07001401040c56041d1000403c0c0c032a01c4804041400c2c0c100d040314008005041c0502c80912024607802c0c4458007251001036100e5045030f100a120341100401e10810b0040480c090701081401c80080207039141c102d5441c010030208a908205081070780001514900e0308080865400d80c0690760440d090303007031a405032a00c0351034000101440c0c2d024812300d01c2011075400294044e040c690790f49075240245405120940b15207500ca032128138018414581c80092504800b41141d4048a220b65041d8641c180880c0800341c603044c0b5140321413040c18070451112544d920220303424003624000881003a142445800130f900b80688401a003101c1c51449035450721000d5012018001d08000550400030914003007268010750040303134150040000c0060305500800d85940c08042807000317021081c14413000a0020000500011108900c0030100d01814400c0e800680d2500c1401d0700f030086284c9032304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 278479766 1250 278478516 278478533
    0x10605010216060c0b06030313140a17060402091b03071e0c0507052403090c01090b03040f020405070e04180203010627090f0206040314010f090f140f0a 67
    0x2a180507100d210541900d019890307030804110b48030b590391604141201da035501c5c0200d2000e0a060303890304c014081c2c00c03c801c80301c021220040c80e02c0d41070040031040c560113102e1f940c001036011540c44803941100701072036107000c14120340c4140d0403500031b00903640c2d0b01d403240c01003520034240750301c001e1020080047d025008241d0019029121014503540f5900703c07021900c10041050092003a00603031001c214a0170405400605010040400c0c0402e0403940030700e001c641c000311031401040e44441d444400075604105110f01a20024007400d2661031b003620382108400c03400f080203004503030381d50004521500c074010305a103020f00103006100200280150002400c00360406034480c0d460504006084905040081c85030664030354241c6480300c03807545610040519600c240d9545840c80712400050359824002e0000d5071140762510984025001c0c42400c403640b4141452025140100da180842c0703c0230b10b021240d9a2000e5824400d0018610850820f8075078a00708200b13200b14a80c0388200040c65 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 278481016 1250 278479766 278479769
    0x136030b0f0112020d0f08090312180d0201091e050a0b1e03061e0a030c24020a0f1401110408010911040b061603051c02071406060906060a110109050106 67
    0x7012030078210b98076884030002070041103500039800005059103000040c5480001e55800340141003250030442e00b000030034100203040c00492401c2c00c0c001202c6c9840102c13a035070100c0c800700a950005c03108504c0d9001a040c08203a0141c8010860598a200340901c5615094005810050040511a42c0c2c451501c004c680141c0214843c6980c40d10342d11803201000c20a6034031a600041c5000030402c1550704003aa031910119503c0e8100d428510301201090241703a41c00024011500b00600340d0301640342c0d00c601c0c3c1c81000e1000c2c0464001135102d1001c507503000e0489803407a40042d0a0100c00001110b081e00408206280c00304480010400080b0b918041d4050300f20307070713000f4031400b83d2100300c4208120880b01c20000c22980a542484083c120803004520004100e100e400e0107468100004010b6000d40f00c0c10303074484000c43d0001041c0b8200040303e0203c00c5801198001090581045c0f00000c83c6e800303008001e1800b0701c01c045400c50b4028492000424410000e00080100c421113080c0180a030945 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 278482266 1250 278481016 278481031
    0xc07081903180c12050a0203010501030b07020d02120a03020d02130b0a200601060f1214270c1212030414011b08040807020a0510021006090603020136030b 68
    0x3460311071a9002c6025074105a00c0e50300c1840710160905007000e00654100c1c00400ba9414490702280f003005840901c00c10303004c0c6000c1e03111080a40341110740249058590700109007103400018081911095074019601c49244a050241c0c0b0740045080120090040e221901e050461000c1c000440c523a01a0091440600b02ea5421200e42c44080c000d480c07400d80321036550007540c014001001303000c0c4603100701c0c3c081c3c0b41146400400f0f1523094403448155007450000d03c0c074a480d10300500601c48564025198080c88100c0810b00d1420404d0f075207601c6907c0004011301800c2d01c2c41045000704000d102c010200d12410341c0c256100d091505003001502862050680550300e03000b911740c128484844041ca01081c10758500302c00b603843c0c0e0fa540507a60460201207810410411011819558003580c90706003200980c01407811400010b004004c1c1e031110703401140c10302c0c50f154043c000b50b6442814500c0080003182c0b0f0320030095a44200c49100180400400c952214007140403080102c180f00f02802030300c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 278483516 1250 278482266 278482271
    0xf120a1515050303040e1503030f04050108070e010c030c03050c030d06080c0405040f080f0d0f0207021008090a0204150f060504080606010f0c0b04051510080f12120c07081903 77
    0xc600241458070009401080d07490381c4103000400030501649600360380600f009007105d8514800601103451a040710101200d82400030a05000651f800001c0543c48611846c2800705401c0202c000303805146243c1e070250402c225000440c0600d402502202c219084100c200ca6503200c5414038134000780018040e1902601560b9188600d03032a042c0034140c05247c10541c641d10b407905962311050a40d1184c0d417404190b0302c0601001402c07480b40d11900240002c8102c1c0076960788a01c3c0b0411082d00c03440b054041c1403114810500c4980c110000c1c603e240f06078199000100800c240d10360401c0380e440d65026041e6400c0c00000400d6096201001d84101d2b11818101c5405803a0300c4015200b419000144030009070f089414140425000c4944a41103405603042d624544030b86078030394814000031540c240740c410324400f0820401d2001c00c100301c82007200c44098508094a07040d044035074420540303800d0703e101c1042c02107180c00720088115200d1682c061481070742e8440e07840c0c03a6805103151099110101c3d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 278484766 1250 278483516 278483531
    0xc0212130b0a0908030d050f090f0304090c03060909211706010c06090614100b040503030a0c03021501180b0d020f1012050f09071203020601050f120a15 67
    0x240980e180d8030001000a045603090081140705904142d008400708865a100003a034035100744014241d8904041c0c0c042076501e82401c1c450303000c00c00503014903010fa01100c2013407800d0700084269015109a1500441c0e45481400103e0180c030258103e100402d20b404072071401c11911a00807190403183d45160710201031b4214007540c0d598412101152442820000101150302c54014510b14a110707100000716500360b9101d0b00110340244091030000901c500520800e51a402c96143c01404046516403030241008040b0340c8070300821352080b05100700c500c02d0100b0903001b0710480032785004011320444550303500c00c820740c0c81100000c0481c0c400c1d4036000b003148050520310400342415401800301c100909000e0244403000201c07002d001c0411010048079042d07a100c5000d01da024030380d80d01c500cbd00b550500e00865820800e10703038040c55050240c810b020f0f000980100362941101c00882e261100038240344046111003130125503144660107011900410403841e4050a40c42d200440c00801000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 278486016 1250 278484766 278484793
    0x2180906090a0309060f090312080105030708030a12090c05090f0609060907020a0f230708060105030106060c14100c030e061503150603010e010908030109050606040308040b0307170a0c02 82
    0x1a248682c003d00080c8000005205690041148003582c001c685040801d0596a0300c0703469007000420403a07000250b809004001914040000d10050300710040a1442c040d070b040c03409040d1b0401d51041006598071002c0e03e4040c0a1420162030090001600381c800703074903044c203540521010440c2c2e010311884031603000c0b840a09011484910601e01030300100340203501501e992035840380b00030040f1443e8001c040c002100340c60108035107504603c500000c040c0d450a00f030f035140c107165058001078000d0b85031240070820140d1146a50030701a80200910b0441c441c2080181d0070200001900c86146042c83c0034a40b1007985548030045050003c025502c075511208585400902061003c5a1682c0b241c03410700f104001c070510030703600300034000c000051500c2c80403042d60035900181ea040d07814010100040003000028010194010340071142d441c5000d0850303452142d41c0c0a203020721001041e0120008201c00d0040300000c0d0511005000318582e4a80f244120b03014046110541005020b0b20317842c003040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 278487266 1250 278486016 278486023
    0x4030801081501180b12070603050903280908010c09081005070206240a0305060103050706140a0e0402120a0b130219030b01051204060623010c1104090218090609 71
    0x5030001030019030181d20b0705113400361040d00381d4000c10545641d6071001500c0e80d02c1007481820000100c010b41a0a8a0248058101c800041203038081760404c01c01e2f240f2404c0712814414410100404050803210150740480d0b4204060304100c040b5803a00c03020480f00ea403c411a0811903031904210340881d01c1ca9603021055031401c4d5058070250740b00201081d100211014200b0b400d0600c00d021041011004002500d44801e0fa4810b56a40c0c02c090b0041c01406010b1080c0d901402a505004d1043c60149980040c188500c10416042010700018942c2c03555442c0c0403509800b8100f41d606406082c440004001021100d038014803502c4e0f8450361840c00002c5000b9100c10709500729020781400c20040054000e0101c0740e0046040240c1003040e4075040e00f0f106e2549010f540140c0380050040c0c1091164031180001d03201c0880d418a901c45e612050781c2c0e000c22503c0209901c01030400c025004400410301908200c42c00070340c010402c0352079040001d2051407203885007103a1021640582c440e07841407500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 278488516 1250 278487266 278487283
    0x322060f090308030a09020604031128260f0f0d210504031e0309051212070f0302040503120712090806040305070807060e0d0e04020c0c010c110301140403080108 71
    0x21032080801040491982006142d00c4a645c01c00402d0b00e038456400180c5542c0300e038100729a0204a10b804a18500b40007000389071903d10b89185c14915030340204000e80c01c440900c100c5280c04501ca001c0000c0d40c2d510004100001d4040e800c49803010496a6066150005400110403520030f1040210107030348036003d111504184010915a1000340810710341c0034000082c025000d024500d2410041c1004082d403c0e0b4501ca641d5400080d400714a00c0d2850a1110314100e1000f119028001c010568280e87c0034540c120b0f00c1411f1460909295420a070301a001d90f5121643c1400303000944801580b04070000c204440c0b081800301110801680181c40c042c5c090702030b42855a0200b0001000240500010000540200e0885003010000e81c4d0384c1007680d01c603d51000207608000301c2c446180d82c00003902c010700e1000311000d40c18008003e031002d585220b410002410400e2243d1502c0610100c078a03501d0110350080e00a020151803407880c007007171610a5408600040d154000002c518102041c01e80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 278489766 1250 278488516 278488547
    0x1401030803061002031c1802101713080904020c0f03040611010e030f09060703020a170c010c020105190908041d070f020d0504030b061914190305210c032206 69
    0x4214613450000304020508500000c464814203480400503a40741801560741d4105a60f0341c2d1900628541c4a032b1401801400180d40c042d80c0159440c00a8100300a03102c4c1c58000350740042c1c4410030041180e00e0008914a40b4100b804001408182150301556842112954034024170640220b02c44042c1d49201d50040000e012500303200e100418500781c0011b02c0428000c0c411140106485d448494105580354450080f003000002e2312185c0350000e00881c465241180020040791811002d403101840803600903070b580c5a03840c10841c04000d03846051314090a12408400b6801c40e0080b1000f610181c155543d0f004941d03154038100c0e600e4800200c6100c241c0143d42c4281c00c0520b140c6c0c891660030005081240d05c000945044d401e05a44545c4c81c500811805280840300700e0040305102c041d4041101040b0002141c0300f041c40810800034131108401e59541c5100c000b02c20442c040f041c05c0c0601a42086140000543c01c414144025500c001515840104a00042c2d903400140e400304000e14151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 278491016 1250 278489766 278489797
    0x31809010e07031508030301080102070c142b06090b01060e0306010b040303080a06090c020705150423030a0206070506040b0c07031e02031e070b09060c0f0a03140103080306100203 79
    0xd116a072103604000100014144040d181d03075140e0b01c49071b0a54100360002c10042c3e50103d9168144400d40002600401c40c0d0200c04405038181d601050715203004481000c450046a42d8a01003150a41501807002c1c0e0440b104000c440a43d24000400407002c1c0300381340010740c02d440100c2a616000c40c0886c1220b01c80744d1510718051945da002e980d5118000d00c41c1e0415a51420700260b050f0075402803154000183d405803000c541008100150801d50b41c220200400050105002d01841d03d003451003203050031840300c01001d2071440003d203080d9031703402c000350042d00218248041240020306940224801d80c440b04140d034400d0042501401100400341c0010064070f1104840c02084154000c03c00a600c1603a141c6541d090800ca0809180858910700c1800010620103100c02c10100d40c0d004030005025050368281804120094094002942c941010000790001614001d603ca01312030440f2143c0b4109075a540d05151000da042100c40d98011100241a11046880442142c00031124510b03071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 278492266 1250 278491016 278491021
    0x106021009020102070b0c2a01090e0a150b19050738071d0a0f21060f0204031a10061b05031306170c0708180909031809010e 55
    0x260300600180c060580c1540140b00001c0303514840c03440204800e00341c10b0000c2a9503c480b5103091280c0b8100c0c1090f1800c03c0384040340300d072140c0c0d200b41c44504a580d025071020381c54940a0404000b06200e0f00460081e0303094070700015802e1700102c06010080d80c8400b07041c540344000f01c81600c0c40c0c404c4210080c0f8142404404112010b411181032003450401c001d000d40210700118800c5a0000c262117010100b849512021201c403130030040345211700004d030717a402c007518980f800c1c0140304484c83c01005e00c040342468a005418124101c802e11032500284148807030801908080000d50003400b0a0300c140103030510450b44806010b0540b070041c0601c800c203074003d618203541200c880184a1801d00030000d0003041c0008114204094546500141e0092110919022020300207800d0260901003412517403040040c41550340080d110444e070031003080740d5220035945510744001c15205075183d2020080060000c1d017403000006d0140d1400c5209100c0d0403006410803c024030000344502100066450300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 278493516 1250 278492266 278492293
    0x501050405040923070906080a05062205010603030831030302090d0f060b010f0207060206011a07120f08060a0e04080d021303140706050c03071b150809070905010602 73
    0x400c02d480e034010054004042d02c01392a10b49107100204183d90307581d01c003450a002041003031044500500c00100104410340080d507032180c4440004010525003107c03403003240c2800c00503280000017181e101000b004401e40300d02c0c010f0310300b00707083d01e41004108a4955400200743c1c018070030400422200c1224186034040e07602100654031160840e0340029116822800240602c000e501c6410300c1b440300455001c2600c0c000500e95100d2440340c2c01194064501000703200d40120300541503601041203904925982d01055687d4840c564005001c240210782031000103500a840208000055403060140c1d284d100c1006007404450240c05110010b64011030000b075500c00081030f017845049000750400b203241006401f500010303071068171041e054151401040c0000d02800c40540700e203041c06420310203101440c1d503480c01522401131202080000a100603c138502d9110018445016012100c8284110041510505075100b0f00075210b10100410074071620b0203114180c860039402082550350880c3c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 278494766 1250 278493516 278493521
    0x30c17060102070911030a0b03191103030f04090f110405010210051806160f030204030c05010809102c0d0f0c0606051c030e121e0f06130c060801050105040504 70
    0x10034a40c158400e4000005100406001c0c1617449500021200c0d103a03d04001c4035003c0c2c5842c4407490f80700e9001210703144100314402d1341d5040c015030041000f0040c0196a00824958407c80710084c6041a02180000321071010f9001040d03100d502c000140011705400780c00200354055801090f000d03800c0807070151480e55480d0300c0180c1c0080706040a01d0789a01344039605041410542d4442c0c0c03444000c2222004503a00714694002d0010315150441c602891516900c4842c60306006050420415402040034180200159049125000741c00c0042050700013059051034200603c840b1503281e007030382c0600d00320400700b1218a840300e6500c880c0c0380400305000440300d00710f0760102207801c65660034000c50301c2d4949520102c00c81e242c246510064400328240a030005604580c814402e401c2c4c0160801e00071008a10b11603505101e1540c0c101103151481c0040c20030b0305d03d29080c0c03460702c603c0007040481900c6c0701400035018002c11a9204164807a01c0c2181c18400034001e039030104104200070400707401c265 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 278496016 1250 278494766 278494771
    0x20d24030506010b0c0304150201051e0408030402010e01050903010606021605010306080304170717030405130b0a0e070c0203060f07030c080106020c06070c0e040b04110a0e1f03050d170601030c17 86
    0x81564501f03504c84820346040d03039070410700f84010f039502c0080062003200c4102c61050325024140e03601052074260783d802101c0c40002c100a04100c21803c1c52051640940c2c10340c1c0d070b02d8000900170302150f520303028029524454220301d1011400c915900146c030754044d1180d0415074081601451809082640b0300b8076084420f117400090340f0540c100042c41c1034680101803d04078000d07000e95580c1c0d14100400c0030000c070580152030000e1800d4064a000d41c0c50aaa103000c5440c540b01d521100d580c0c585040e549110b8412000c1c2d010b00601c4100004a01c503100c2041c4140340c0d6403403c200349504800b084905100900440380568880c605080300c2e0303d8110702030954544104000111280c0b6102c06400103841510700b11143c0c400e000510007007140900610b402414259405510300389000341c40100d060380602030300c849212a03641c160030341d8074036910f8202840c0c0200454908a00c17800e801880e20503140c51002700070b910300011401d99031180c0602404001c03550b60300c01c13121450061000d442c6e2800b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 278497266 1250 278496016 278496037
    0x12050403050d050d0f0b0315060103020f070305042126070c0902090f040506012003040b07050a03022802280603060302091e0c0d0609020d24030506010b 67
    0x18800000000c4040040c03500036403035550b4403a2103000d4030400344240c4044a813401542c0303062052090040d1000500210004040251070801ea100c0d007005a0081c03141c0f1103070000a5a0000700c1c0c0c824540c000008004a030a41440780a000d48112064070664504400041c070888006408601d40313412000c0e0f0300402e0050a0a0f1460080c443e55504049032981e4040f020094000c01d15120a240c00620510b844205540511051400b500001d02a502105500c0d012203800c100b071105202040040e50007415015120a51313501c01e500340103543e0304202c0b070f04500520413402d8409000e0951111043c1c043c0140304814190480d940c200f01202541c6100f182a0b00600349030072145a80c1202454000c0c00240c50001c0c1490a6006002d0001c0b0b004001c2043e56040c0c80303000c1c628010606036142e000380410100da4540d0b50402100b00506065803044011a0001c10000c1c1510903c0d400300884803840f848400300301c4854104150118214800980f140e0403400040000b08000030040020440c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 278498516 1250 278497266 278497277
    0xb16030b0301020703091422020d09080c0105010e0c04030c03080d0f05010b0a1701180b030a05060a06051206130201030b0a171507090b0a0f2a0b130201090312 70
    0x140d000400e089810000003900000d0210340d04010300070024940e5480c606058680c0ea5203988011150400050100e004416855001800100e00c541d107900980c0003d5111002d155038801d881540c034081c003001c0c041c0700d0600107900c01180c004145401110100d03507100901c2407034203155440c0c0c4001b17a080b000c207a141a98131032912181c402e080d4400e0902a002d00404940c5983c13680c1c0005200c551b28841740040d10381c03081c0040c885104900702205442e036a2410106d01001c02c03074082400d0180b0410004c08500c1080181300c06598240c0081080e14030584d0350102109800305d00d40d0b9520340503165401340101c11968100954400c2e003054100e0140545542c2e007499640c3c5041c03c055203c440110015003040b03000400c000a0700800303e81218041ca0066011070502c0c448440e140700c1c5480c0c03d01840081300500e00c020340603d00b0049894101d4500100c6020038401c40c1702601d0307003030108aa26000980020700c0400300c4524181c2c503a501a234a4040080c00c6964050540c2e111410b0300c3e05106 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 278499766 1250 278498516 278498531
    0x30b0a060e06071a07210b03121b030c03041509060806090a0b0607051005010e0702060f0403021527060c120603010b040c020307050d23090123070512070b1603 70
    0x3e41d1200c1280c042c1865a8815a4078040c0c0c444140e440c2e641042000340322030070403184e81990b48e4001b8140c2e0681000040c01962072034482400c10355503803120b4400c1d403d804081922002e01d0341c007201078411101d0118103510701108642048564000d140101c00118049901040941c100305e0042c80e480458030200003080100c0d0000500150405401203c86601550300c901c00c84009000790fa0040500032002c10b0a8203003190041d45412000f401110a801500005002d1501c20009035100f08140c0f44000403c1c208112010400e039500c2000c017414500d08030340d980c2600400610203210303000c11003d60341000550f0001070409100580030590542d00d031234900205641e03d04c01e4070840d05250b0020b40c0e81d482c5a1600324106030301c85240c2c10030300c4200059041158018484541350404404620b55907005600050314100400604ea810b401e19840c00070101c11500030040110502031011034500c4e080c5410343d40054454910010a80102007010030b008041c0b07440c1c51130442c0c219080c00b01d40301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 278501016 1250 278499766 278499803
    0xf1e1503021809130221070b180904030e0102011b050f0903030408070905060a080c09070302090d0b0c1b03030c1204020109090e010504021002010c09140a0f0b0901030b0a060e0607 79
    0xd905480c138600c0f8850400501d41149400d4036200c520050301851400e1055403401c650b600c1c1c02d500d100b83d900000c1c0016008800c0e441c405a083d042c0c040017400e80d0b0150605080003442c03a0340000c422409980b800c01d0241f20001751006031142c2c90303010703904c45280c0300b00300c0c03440d65041d0081c011482d05844140004280707030f801809031001510040c1c0740007811340f914070100000130303d443c0d0040c4000e400034046200c050f00c810411a40c041289e080160307a40c03000502284d994076030400c018000302840c505222008007010b0040801240c0700700d9205038a001d00785000d4580c44107590401d60360200b0400c41441d11950800c503a48140141020b030049a079501c40c01050b1494031000c025141d654608020031803074a05102c600c02034013071000f003240c4801c990b009410144640a1001c1e00740302007614120941d82c40388480c000d4180e42586505441d0358075009070703954012502881c0420704003a04c04429082450101049402d903a440380d5596102c0014000c003540810415030b0229003449000049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 278502266 1250 278501016 278501029
    0xc03260c0609010c0503012d08190318050d0605040c2112050412021e130501081c090905070203040911030601020601050f03101806060f1e15030218 65
    0x2080304034006404945092000380d030840e802c208100d01840414401400704204904200300040950700a804c4450090340840004060a91042000d4850121000300018000c04030044441c86622604501942c440304902c000310a4043d90390014000c0e481311700031030308035080190050b0007200d84240701611505105c0020300e201030710015004260340041d007000060200c03081018410f00e0890308143c18001285102c40080b00d0182c400c01d00f1816944040c09075540c3c100c82424002c004002c00044d00203144080c2c002403240348010702901110250740c414181c01000b09038101d43d00c0e5400c242c200350240c801000050b04540031480248004545595140700304e003402c281024295440303181408c002844c24030f0503008140a040d526205100b140c40c002074450484031035810105180c01c40b100402ca00d43c01d4804080c2002d400e01400168041860b20100705442c06095210501030141c0058040c50805125040305d202034001000d800ca8440da002d41002c821114a20b0601c401a8000404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 278503516 1250 278502266 278502277
    0x1080c0702031c02060906221a0709090e030405060726030f010305060a060b0d090515100e07030e06070c23060106030e0109050c0d0c0335070c0326 65
    0x140c000d281580800c3d141c3d01000007990001c4903100070089440c059403084c10501ca01c1c0456400801e6081190081041d855800540c010381c42602a54900c0c02c482c000f00103855600c1510308652408030781d0030100c04003104032130a0b140302400700c80c80c08442d03039104600c901d101841805054000c000074800142e0207401140110284664000503504600b00541011005010011414546441005440816415204042143c01c0b002070318461a0602c0390074040c002440c40d144104010400010441c08402c000a864189d04440b40700d0740c6c0e0040c15400c80714050328100d11540070800199100b84500441c1c41200c1c843c01c0032a0f03180402e8072220070003440c64203031288590085001030201e154107200e020b5070a54004000d0125060b90b448558562002c2c070070042c0540d2a68040340240560030b20210b00951f44a802d90781d80508019585518241a6150704481c1200c58807440a1000c0d0a040c1d60256070800c0c88819041d145984d491000e0780d02c0240581640c120854040440780648003034035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 278504766 1250 278503516 278503543
    0x10f11090f010503010b1e0d050114041a0d080a0302040e0103120305060613050f0f03030a030609052206021b070b040302040b012a1b0602251d0402010e0402040617010504050106050901080c070203 86
    0x2c0b1310340548820001503a81d941c0d41440b4a0010034841070301d558ed10b81c05c40e0340680e08a0f00281e5240381c0c4c40310840c0a4400c58200d01d8000c040100000100102e0800968550019607800c0100d529140104507052007548000d00d003182c16072005103c6403500ca162407108100c0100803002c1c0b4082040800d056821070307104040441d076150402c00c0920418003606070b101c2c50b07482154030802c0742c9101500c1c0c070500c9a00c029124540c04501c884211507a000200140b6000900312040540e03a07515102d05940140001c83c0074500300088407240b94003407204510090404904640310464084001c11001090308040d03a0514080742003040c400e1104148001620346640501500b001c915503126094a0381c1200c2c1d040c40040003009c104002c80d8800c1152080032040b18a001030311140012240413080c140a207500a1001800140f07a50708807009640c80a52603451f0802a0b99074010401200c80901c07600b00450010031501d0201c0d803040100d43c3d0b0003507510240608020098001c2481c2ca40c4025901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 278506016 1250 278504766 278504789
    0x306010c081318020d0c111f0b030303040807150203010f0519090e0a0c0527071202120a0c0905060f0f07170c15240102010f11090f010503010b1e0d0501 67
    0x80c500240e2401030040d241c02909254124814003c405551201c007100c3c00c46600c540c0b0b014908c0e400801e81c11040804c1d4004048030384078181410003200030390100344100e4201d41801c189100a4840b0700030799048941d100c90120003640f03000c0038000910174140e4180c0340c00c0001c0c54003043d862024420858140c8000d0002c040310401d80c50955807014990304194882c06143e0b0042071511400d0010081e00e03080349984406941f658201555410f080c1e0090000340e6001241b24040000b42c03000c0c403449031105080170301807044440700580d10800e181c0211504280c08009100408111000800454404030140d80c034160040d11549003000800f9503015407003034001090500528100a6010610745003917010a0604110540c00b5140c10103034000f2105d401800303040050380e0700030b510500030001d05481c20b00903115008180d501d01e620240fa6a4400c5206110350035031540f02d142640c1c16079102c0020546040c010301080007200f4a82c6000b00803101c2d00700300c0280703a4801c07130155a0080550a180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 278507266 1250 278506016 278506027
    0x60504090c02061003060c0219050d1409030709050c091509091e07080c070f03080609011a0301140604080307030201060306140c09041d1609110306010c08131802 71
    0x28001c0e40d603005024021035100b0028000346031110444281242d50083d00000c88004140c8182d0074000700050003030700c21141c0d1111100b440004203c0f00c29855899443e28030907018840700700748600501c0300c0c04d501580107010500c480f10030b5034048d5030049140e5030b00a091204001c0010280001030722150f1ba043d1001c07a00c00080e080c844115600100504d016012259515015040d4180c00501c8001080010004a20081c4000d0215241142c0089081c400440c01d0304002d0401c0000703980980c0175004030b00000540d08064282d0956407082c8254080c5182d01c1d1114034450786603003a0b0b180d0391060007000002590a400c000030000705120740c0000c02c180d491400c0c07520459420407290015000d00030200b146080804003142e840307110403680003c140306d004032550880302034a030040605108118800b100c250110850b03100301c036842c04061224403200341c2c680001d8082a2205800f00d000c5c120428001803208003c0c2202900088050740042d41d501015038880646d8030781419840e900080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 278508516 1250 278507266 278507279
    0x4060c090506070606080c0d020d0f060204032001020601090e070e100e011707150806040207060b0a120203010b06180904150507050304030e0111070b07110405070302090910030b0604091b060504 85
    0x187e25000c0074225018002100250003203907044d003803114010403249440b0302403000c01080382e0541e8069038000081130a180000000c21000802005040340548607080000410b00301501482c541100340300d0207081c0040c03500300019250b040113000c0d0310f4501c065000100749102e405a005008000d644140c0008021034800c2c0c46c28200c541d001140c1c1c9080c00300d1401556500301031401e4101c64103580040c1d0b40c8016091000041c2a81c06500f9030002c0201d9000807020840545856014001c80003007105003402d0f001c1285c5172003840c8840e5004141c41c041c00d81d0a10740402000c0e03205000e51382460000c00c040c035076141210011580c00300401e0f0003200f88000c1c1a0b008000103e006000e0905010210048160594980c500c0c840c0c1c0d107240e0f80005d4076108104c5010020a14440060011f0116080411019029400c1041c18a00a2180b6800180c9000141d800d1030201d940001c0203000c0c548600041c000031b00800c907002c0c1c580400440200f10703040b103454880030082190750707210f0b42c580c3d04109 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 278509766 1250 278508516 278508523
    0x14070201050619050102030301060e0d051b01020d08090a02150d0510060e0301050906010b03190614090f012102010e031b1003060b03130302340e010b0304060c09050607060608 77
    0x808680c0f10004051090165036000412070713055800c03901304131103540c00b00300c0000c038104000e140080850250388400703c0040c00c80781e100c0c80300c004c0903002c6d100350748c40b569030450321100c048441c03032007030340c02401080f0150500005515010b120741c05524500024a020b12041e0781d42500c030503000c0c0ca15084100550741c3e205022440d0210120001e0005080000300b19640c1c0d1018042c850500d9000004201ca4244001403d5004500d8020a2113046e558100403200341a41c00d00d128000e200420028581d0b5081c0300b0030b14165210030008548491039858100c174078041d8090124148100c0c0300e41242266401c201200041b202004075821000d0060709008641b070320b4070640820705041000510112081000f5079522034250032124241d07421a0400f01d2502001d40c0700c1c4911440090240c40725510300300c0754000f400d4209240b8005141d655080f004549409203d07490001d80e00348040380024420340c0107020f044029103010f01c80b603900c910000b4881e074040f01c2c0032240d40d81c0e13640f002c02801c0000e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 278511016 1250 278509766 278509789
    0xb0109020909280e0709050a09120e13060b0703022802010c020607080c0307141204030201030209122a090403020a03080c0f0706090b0f15040902010201140702010506 73
    0x84000d500340030a420219003044030150480302d502181001c04509041101481d450a02014800b808002080b0501d02c1d02c0d98141d003c4c40700040d0a01e4002100c001580c02101c1c29039600500c02005030000e260112084007440e00042c0d401090000010030344102d9014801c0a011200407496070307030200303190182c80c022041841f140f40c07070f01a00c07500701c50041c0102030011582e028200a5a03000081c40060002d12030800b00074107070744021030401c02c003240c000090500a48508201d80098030302845250350740031444840481c04604100501c01540709030080c14840710058480da01540e02c03030f00750b6400d0020b01ca50345440420305030000850700c03075513009011141605480b402101c0c201034600a44808031040c0207002c1c004040d01244403003003070380304965002d0701c10101961600785a28000026019a80702541c22a00820124440c10b1401406a02130b0000608442c035101d040000d102c06049416000da0565680e9451882203060f4000f50520a007225800001c9610f800da08002e00710540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 278512266 1250 278511016 278511029
    0xf0b031e060a05040c120212070206070216090f09050d0513091503030c0515092a0a06120608030301030c08010509030a0c032a0606090c05092b0813030b01 68
    0x41001e01030380b51102600321066410540b4080b0f202c4012403c1600d040b851601121a100c0c400110f66003290000fa0983d40038101c55400d480050300d0f40c19040381e85480c516518024140b00e403908103d03650840d404403454684500003c81c0e44603103a22024144100c5a0b20a00031900008101c0a080380004e044000b5190411041041004441d011070220400d80002014000c48916140901504100301c41ca018681c400880840c41e2144c1c59944607092202170b512134803100f204003c3c05d901e182d5400141d025014041d150941d2501404071004e203000340701c80140b00da607040302040000d01800150b01840c0510201d1181d2071034140f0302800c4410044c20000180c000340110144141c0c08002d040f0380540614201e100c0c001891140300f9071051803011f512881e0b03034003195a030410110390820001c0340c140400802541a041000391014401c2c0a0a16030200b42d008807246e101c004034542c83c401c002005115100b05282d580d0368207280d44100400c03480d82c101d84104104000002c0181c5000d48003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 278513516 1250 278512266 278512321
    0x30e070506070506010905060d080c030d050c0306030a110103110f0306031c09090b06040906060e04060f0f06180503191401020405061605150a021305060a02061f0f0b03 74
    0x809460f10342d2580ca041c050400110340743d0000c81e42c996190807a918005800c80c03000307039445440f101c90582e0b0b40e20411008880b2400e190015544280200940307110340c1d0050050216010160380ea1039170001c1251180c0e060603512040c05103076141ca213000c0d11906038200030080d503d081000c00c151800c0180000b002490003002d4150000d540d0012600040300d45101c00441d006d1942c1000030524007613604860101c5182100000300d550b408010950740c04400d0303404000007900c441e07100c0000100e1b80101044200c050b002000f6242c85100c44054a1160010301040d10b5201c10009003856084c00401c20ba45219486e01018003900024061003502031000840ca86450400410380d1341c02104001c90441c000070304132000380001400116040074080b80d4180c654a81900d400c002500410140300c561150110040307400c2c109a804c4030201c440c42e4004007540d40c1c4201d0003a20b2050120b031202c810700c80d40d0100107007071060040b0300c0300605000508103480346442c80b003025060820000d520541c02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 278514766 1250 278513516 278513527
    0x60506120703110c0109211e030209060703030b0906030d051b030412030c05250b0c1f0e010b0d0b0c0c160905180a0312150e13050f15071b020d03030e070506 69
    0x10f40080c5408c1c3c0c542c211001c00b00d0748480c0c480c2c0c00d070000d0080c10401504030701d000485008140d45a8081c03001400700702c40f600c940b0b8035580c1c24950f607201310f8051000428406c0162442e0992002c3c01c0001200900084a180c0f6032102a042126024030b8022004034071031410030400c010302444807600b01500e2031450041c02d07074a007401002914641c2b1034031714820740000d180340c0711072001d00100082500703100c11200101d00c4c2e10b44030300c014402094004c4080d460309416211600d010b010003401c0c550011589915a1944803203041a03500850300148148904081002c10f011030102d1a001884807002c00200d07880e0500b0000b00146c81c030032424a140d000b65500c80c0020b0380009102c81982111140020403021150110f500c41d02c064000f000f46200800400c0000f04842000342c044074422000c0e5514100c3c2110020b0381d03031080500001a0300107600009103a14425040350a0341e400c1803c2900d134284c41c5802207201c0d101c000f201980003a894200409000c103080281800401c4241c036107030b2600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278516016 1250 278514766 278514833
    0x90b0a1d06060d030504030b07020607031b05030a1d060403020c01090501030b090a1509060305070812030c0d180206030406051803030702030703110a17030a0c03060506120703110c0109 81
    0xc1c18010903a500c9443e006000e402031510860607200a940e000358800c0b407074240700002030740c0e07480100e07200c90029062a850320710720039040403d0504441140c45080c01d5454205209000c1c04d140c119500c4201e0011300e12800303d0740104000d0740030768001d03006801d000c1c1104000620980040d086181803504009910206442e0a9070f5680c0c00b482814001448a5808841e0328507280b4641c0890b41031414000003000f4060049040030844590002b02ca1400d0386820440040d07010490f1900c41403c13041c01598241d0803c0e4022a4660880301100e4141e10201c0d80010610340041d901964007564500c200440c0c064040450040319052600079415860070041c000d60b00c0c03081903801030401503014290034207400c08000c40603009038001d4202011394102c160100e500d0301b04035030482103a820a0b40e083c44180c02841000240d81000c2c00b510f00d01409034140003e000c401920078410999203402c4c601005000b80064564815180c0010900d4070783c3d0708040c1c95a810540c4002502c050001c804044c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 278517266 1250 278516016 278516023
    0x6030a02090a090f02150c100507080606070c09090809040c08160e011806180b030105030c0409030e0a090b01021b33030906060909030a0c02040f0f090b0a1d 69
    0x48036810001080f40002490005136401c075410b0000d40040032101c4005160303100c600a4096401d018084070119098800d0440136110180c0d000c10129001c640810a2820141e000b400d402d80640141800142d803078405004580258409581c040030115071200c00c0d2a080c00303206c440486518180031681400d0140b601c60304440e58008091000004000785d0342c0e4040e000c1113000383d401c51612040c1c180d44520107008541032040880c0c0c0708005600202c0c20301040025a416510003070b00800100381544280001010001c0050b018010600001070465540c80e40d070801426088401003952952400064a080444411401c03100c251000001c1141c40e080441c008104004d186442400c1a0455411507400d00c01400c10407080c00000308865030100164030b6003d02e60a40740f000240c1d45641100c0d8407401600c28002c0024140400000540b8054000040d5603c01d42030000d020880388546204032480c2d0001100c134090300c2001c11401034854440c4010031b0140080d0a10501c40c446a03803070700d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 278518516 1250 278517266 278517271
    0x7020d080912030901020d0c020a2f030a1a2d04020103020405030a03020303100509070c060b03031c090501150506030106050d090206121b2b0e121206030a0209 70
    0xc0100d88400101d8014080207580342045500a80c9aa242403000009001c0d510042401452a0410310072141207880003410106d183d41282e42000041c00c24402c031000c4043c500c027070050030041c2d0720404a0a58040c841210103e1140105400100c000fa66200e84080014454418108208002d20b112010b540750007111010304030410380c090366140b005800034015504401d4061041450f040209070300040218090808050f032540c0351981c80c01000150a0300f05c82200000700603810520001d01c003904211031600f00241524101040ea904040d00b20261001c8074020946402c2c24009000d02840790981c0031041d6941c41201d5418080460380500c018800c400810900140c0c0c1c0c41800c0c03041c1c4c031101003207600801c0c41c3d5940d2089d02290403071100c16a000e52984150071001104000200e08a455544180c04100300044584602028032001e10001000c029200c40c1e942c0b5000c40700740000e29618204c03600581e00c0340e0308011007101010005103107034044e0f48a00500d001590750041d10b1035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 278519766 1250 278518516 278518543
    0x406060f0507060915060b1b030a0c0f02030a0503160b0105120304030b040302101401061b0210200601030318060201060e010b160c0e010504141308070507030b0a02071502030702 78
    0x1e2404100c4c07404403849610485e902120303524125003c45d00c0340907100240b031080c1e1418441c51081c5d848021607922441600c4862010403201e4150400050900d41c0313070700c00180000c1c25629a001c0310380399a820b542c40305050f4200f490004c4d10307107010840030030400c07805080705840615080b00700001103a41c038031a034003020313014418000020342090310070805e60306c4050f00f02005001c0341e0b0f4911800030400000303009800200c2c1441c1c0c1140c20b2504d01450310044550020520074074864031ba00203917100b411900d01c614410304a140000c510b000c0800505009510a6441034000703094462160301c003808980201045906280003001022401001181526603100d002592803809410080101041c071b040202203414082c030005030b81800fa882c5c10704980c0c05940500440c8800c0850200010003261034803645529075042c20042840300000d00202c511500448041d070351a80c45800c4030f0002103031080e8040b5000110324003000781c40300713608a909001e00015400e505081202030b40759540300c3c4140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 278521016 1250 278519766 278519771
    0xa09080703021003020c19030906121509050705070803130c1d07050f0d1d01361b0e040201021606050d09020616060203060a080a1505040804030605010e060406060f050706 75
    0x6e14034020288140c0142d14600c00450b9442e182e103190207043c040c040d1207002c02203000740c100d88400300c0160144a0342034a0380c0c083c68900d00c0c1400c1e1034000408002e00303140101f090038000c1d40f0000f5000e0004500030003540712070400c05045490241e50441880e000300b54404483c0d613441d2842c8110700c1e405034001645081441e103c1c1001c4180c907045018583c04103904604040c07031041000c1c0e4203118012007411040007441140c58901c684400c00703464462501464007011104c002550071aa903405506203e185104c1c04010101c4441d80d60166236042130026040b84000d0004660301001007c0304840041c140c142500c1c6040006002e034000c5182d400300007601d50074041c0c01c650b41c010442c2c005401131a40c844961078503040820094000b1034620740a040c0d9000c020680c114009660014554810020700c4052003645c640d134040d0002070000c1307031441d00c10b020200c0023607514001d1601a0100070f000305041e2811800f08030542d589588810148070619210442e0640d11408443c80241c02a102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 278522266 1250 278521016 278521027
    0x90605160215130b0103060f05160507020105030405160b030a14070801061112030108030408010b04020906040b0a0908010f021c090c0b0906040815010518010e01140f0a0801020a0908070302100302 86
    0x180303843e12a1111008000020030f00003c0f0800c9515841030b8910010b0074001c21040d41c4049169061260304000800400c100340050300056201d4402950310510079420303102d0400e0a110007242105a81e0072004100c40084200300c18048a413040c1400c2110703c0050150500f84010007500386901800b4000c20404584a00032141a04011f40c10a14640508040d80c0c1e40c4d56200700d60b2030303401034000d4100c95400d002900c0740070324141c001da9210840c0100000d00d0720b86842c0e818201c40d4400c1c445242800503080f40022924420b00c00c0790b115034010440035a4809851001c840f13040d408901017090240f0b0a0300d02c5021940d01c07441c10041c0c402c604201650750741c505001507503c0c055035101805910802040c1c103034124080c075842d4120742d804d6800c07800c800f84c0030090000c000d609004584440700c0c000010000511040f040404c8980d01401515000e807194021414881864002c0700d41b682d00004e00c00b12481d80201100003c0a80310050103185040d5030005a10746030451b9070b04109500403c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 278523516 1250 278522266 278522281
    0x20903030d0603030f0c02180c1207260105090708071103070b010e06010c2114030109060f0f0b0d0f020d1b0908010603110405090118050a03021c021c0918090605160215 74
    0x1142cac10400e0104640c4000e00c1e0285000709030544004101000803a056594040000360200c90740c10303944001c08034002941c4034402250700004c02403c0400704020f42d5516074903e0401c2c0010000f0a0050700810301d55070500d52501e207848005040c80c1d041100618450010901784502603855250105152072070243d070410459003501445203034590b0f03030300000000541c00119440001200d0202d519803000d01d42d01d0000031900b10310ba00c01d45107050010040c001c9602071030b07441589942d001e11001800c107040719a01800b10b41e9444c00c3e10b040f06403004400303042d140d0808194001024800000d10038681076a4a1562108282584602440d15400800d42110080d00310300314075004000165460001800c16554900702a00b055000d80035182d1000070480e0041ca50440d1030407241c00428081d91042540300b1203c081220708001c100540c02c0200c0e0110f10b100403150810100c98012940d441c8074184602111006002081075030707200c2c2003100c0455008100e900780c040301f1015510f541d56581d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 278524766 1250 278523516 278523541
    0x12080f0712110f1303200307090e10060303020309120111070206130506210c13050613031b0519080c0603040c03151a030607051903020903030d0603030f0c0218 70
    0x3c00d00d081c41010a200c900050807460741e40c00c980c041c1d001814001d1903440112241c016221185806070440d44013848244016000780c0d4664580ca41250f041d1101000c6d080111074090300100c00580001803c0160f528140d954000500401c0b0003c01c4255441c48148804d441101402401844040380c640c00c0c61724250918001000c0103405941d8844480006c5240c80c4029405c00d0603252812020401c503c1040003916501c4c2010185241d26506040c00c100d40c0c0c1d08280360b045070f0304c0014240480002d020122040e8550801d00051104604080400c120344040789580180305440030070800003494001084007000c0e90640d00207989450300c1c02c00302c8821019400c0500b4540316040359001498095008000b100f02c039109444003440c0d0001016100d17682a43c4890000b00301740300518201c4035000400007000c4160600620b00700070b21001c01e003140c00c0010340c145003e0342d551080043c10f400076010b40c1035401c01d141080801c000c0390300150865468901c07a2140405500c0010386004440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 278526016 1250 278524766 278524777
    0x105130308152d100332040b130203010603120e01030e100213080111070314090109030809012d08100f0b09040204031a010f1203020a12090509010312080f071211 71
    0xa001540c181d26940000307806840c0c1a65402d0310b00e14024040c00907000034111045ca0382075502411b640d1074441d500c0700003881300007070020094030000000303150050b90248500c00065104141c3d034030102c44484e8014040b82d002008007418141040c4401110303003404071303059400600c0d03002c0058481e4038403036542d5903404550b081408251f203041c01c83d05112544801030000d082c0301e607441124100300900c2c41c1c462070140e80c1e14180480c02d6131074144000341e140c00c00307400907040615242d000c41d40f40c415121a0903409550009410031110b1148800c16070100d15994003040806850b1072451502c4054002420b10307105400324400301090701c1c9100d580d5a0111801143c10110300790b40c21a002084270402102881802c807144030854000825042d0b9000002143ea05a001744c001034107aa240c84400d030000150010810132100000710b8156941400d035406503005003001c640082840341c0c040e050300000351140c1301402c8440200a150307a4460315064407200c0321080410300e40c0721030a4405541c0980c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 278527266 1250 278526016 278526019
    0x10051503060403090f05060408031215060f030114091b0901051c0506190602030901051309020c0a050f150105100306090509010e060604060521030702030105130308152d 74
    0x7004140020f2560107440340b020754484400c0d02120a5407a070400c02d10b84564800c90034070b0740080c482d00e440c040401d0042980720303c90090030794a5a0000300081c1d00d0f64000c8801c0241e0682c0070005001c41c0c28100c40c1103425107000e4440562500300004990300501d07240d4408028440001000413090f44108141d446c00c10303020901c41c00c40b0300180c0c1031501805089842a019060302c6002c00207504924000ca4200e0f00703283c015501d40301c150801104c05a102107214000c50341c0405002030021001c1c03006041c500c12060103031940c0c00c2c44c2e141581c00c2c6000d00c00c140e031490b0b01086441c400d070090441424116001120040c506c101903040540141c80c850b40940e8509180604005841c072042d0410260302c81104143e81c1c256442d50100011918140210fa410410550700384c06001c00309002c145824006108507410b00c00641d0001e405e50300704030766a0701850f110412160805410424503900200040e24850f102c4010b400424080024403140780b0038070309045d2010a031008083c46000304c0100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 278528516 1250 278527266 278527273
    0x30506240d0326060913150f02070b0703020306190609061b05070b0c07090e061503031309020d1802092d0f010f0602030c07050607110904120905030f10051503 70
    0x32010f140d03412040300f1540f00d4081d024007000a250800e02c0507a428445500000a240354084101d541000b4074420305c0210310a5400c0003d2004101e9002c0c070244120b466680c056900c4c50107205000071040c3d844c0c1128400a1840d03c180240794101c81110150f03002494054001140142d410320349d2500741c903010f0300c18015030b0004204028213000600881c0d58003822903902c00d036a03040e1941154a0751141c004190850000301e03064040100f100c0344414401011a81005c450030440e510008070341d4020071820754005410100b80c6000e018100b9680740402411176aa00d1540206280c0003004110311088201744040a9050b1a503221400d041050b40d4034000d4031f482c14000d41007070710000f070060481c1607070380e1403002400da88008202d0300c907040c034a00034210503031400f828841c098100340700c04c071a08400125684040c0c2c17144010144694002e1640700c41802c1191006031103640e1540141c2d010350000300c50040a100c00003003220009001d0800010650341e02907110716010700010b1803662600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 278529766 1250 278528516 278528567
    0x12d0b0f16030903050d02032b09150606090b0a0203071511070807020f040b130203100506220f2909090c07030305010b03040309030803070c02030102040f030506240d03 74
    0x643c000360f00002e0340c2c8100100c0700c0d00c1d81d5072042640e403409a420b000072071000140c0a070a460702030369540d0101f07042070361020844810640d580e201c00c0340880f408005441d0348407001c000182c1e02510140050a00c1e100d840c0c980300c48030a00940340d01c1443c4000d003540300010200b0040c555258800c007445c011685025449920500d0004660b9002600070b0380b140002909180c118a003911400d094030318010254248980d0001403400030b03400044c11040c0f4001002d000060a44030380d401080d00095100312000c054101304020700010041c0d401070702c8000426542032116131043c401610108088280c600030807030404041d4543d520a4100c0183c100003043c0601429240c0a000340107428860f407000c1c08207a8948460407810300003260040c0003e0065201080403450040046422424514042414607082d07004070782a80e006034050552100d45010400c1844802e001d40c68020410b023050002c503109000d800d190415221141038818055030a09a040500a84a051088040110f80030100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 278531016 1250 278529766 278529773
    0x16090b030108030a14130e1f060f0f11060c1c0606050912010c2c0a0b1b0a050709020c070e09060f07030504020306010611030403050105040b012d0b0f16 67
    0xc1c4c20052082011a11000d10540888522010f684038584907000e10b820140c03074890b15003c109800750450325045200c4102c8040880d512000002901040d22070f1520081d0b1008000c0c56400081901000c2200f850781d0402c0f00e081c0032900c81d0700203803104a0305403200001c0b6503101c400e607081507030201b165180c104000355498018018103040d81c070484051030040a4503c2d07650130780d1076804200300001c0c0d25003a84c1039884082d80d041d10201d009038110a044080301c0b40410100034a980107445070070400308403c031001e030802801e4004a5040d030040c140101003a51402d41d92115401002c400c03640201d4034041031401044140020511060492003604212074060303200d04081e61140d4162030b1040000d131040d80640101c5005a5010380240084c1c2c1c40e090b400c940a026400b424000c80c0030401001021460034040c00380030702d0103440d00070055450954410784802000c202e12142c0792100031800c005051070140201140c0300c2c28100c030340d075456400c46241c551081403015016108600c0450051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 278532266 1250 278531016 278531023
    0x4060b190207081207030c11043305090c2d07020102010510030807060f0f020a110c09060310020309070f17010c032c01020c03030405060f0106140316090b030108 71
    0x41140395025240100d4580c070120340c4030840301000b040498403c000b4480045c0c0700d001100e010a00440400d01d00280120000e41a151a8602014070181d158100703d00f0001e54844580c00303188006021400902e004081900084014030030203129502050403030812600c54550868a83c4030140c00c0c00b021415800f0080300d030082241a070040d860a00012941c06032094581e041e01e0b008170003241499031603030720030000d49550354440040c90340303039a0001c001c5441400580402c0c1c42c06d803620140d6007020a4141c0c6401483d00c4110311500b00f01060002e59100864804000c0089200241c0e90b5910011040d143c650300f80d1203c00c03c4242c01c100001c1c80440349150100740761007400244142d14910f04100c040c2e0700d8444196070246424800c404a45030340541d4003e8028811001608001d480400389065800450f81614681c102500700507400800c4c50000380034080904090b0361000d42d1441007401c41c04001e01181102d01038503801001c5500803500400103255414019580f985c41e5100241c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 278533516 1250 278532266 278532307
    0x6060306050f040b100f0b09031c17060609011e030905030a0f0e010206060a050607020f090a06081213060f0e0a0902040602010e1f020f0d110711040b010c1104060b 72
    0x99591130303900840c00b0891020507000c115148441800380ca00d007001034121003940404540796040c414a031400348c1e4000f040812400b05041a02c80c01c590305402c08621520007801003a0501c00c160401c040700250b80c0001c600207590400d29100d400d20040031070254010301080901902511003c14a2001c080e4003030703092503c501c0c0f1a0740360401c00c100c450040e40d40d20344c1030310065400030b0303c01e138148080e0400300081d00c54107000030401a2800c0485000c200b0219054405c400282d80b540014050108104800307171100624a41240c039103000c2c581d5a00340490580a40c1c1c0421401031075090030340e48104005c9003500c1e8010240703610b01340d4800260340203500500c202405075003401c00904100001003a10184c4404c02c28444000c4070a8030341d018029404000d40741580c0d501400369240d110801d11600f8960b0701c00700d000c140d582071141092007000c4078105080748600d09003400d030b200a0b45c0c4404552211580301100340d030426240c20014001d084a44c0040c0303020140420300120210740e5050040303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 278534766 1250 278533516 278533523
    0x190c06051303051219082503110c0109021207060519030e030a0201060305161a030c04031b0302030c0409050309120309191a0703092114100b09010f060c06060306050f04 74
    0x1078003054070f5109941c1b030a03003103501400400c25400d0009107801d21034442ca04002c200d00d0300041a074211303925900507070042c0e40040d021382e558002c96001c50801040001044185000502c800c1d850550028040e119507880d01c240585007071351030f140c698000d4200c150782c0204030003507a07211092100024002d060921040d03989100303940c42d280310b030701e9110030361003d9542d2081c0040c00c040800780148056400a090b440c00c6000030800000414801300d80c502111100d404541ca440d8034500400d464402080d0322144910316260b01000086c0300041180d440280c1640c0c04c1400c018a00540c905502840c0c074a5078100000903075421403e0205840001070314600111852140491134400f800341c050100d00602103900b01005111100d41c028480b80a094030303c80c1d1502460071607a540d0305486090424070115405034a10080288943c05100382c01102500d1010300d940c581040741c101892030744180f200f800048048803040c043c85401c400c01450300070f40103101906024680900c01c88044600740d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 278536016 1250 278534766 278534797
    0x621040501050606041404052508040c060906051210090f092604050d0804090903090e07020a0809010f140301030f02010f020f06071202130b0c190c060513030512 71
    0x141152810380705030b1702981c031b0803c076000c00e0807440e00904c8024000605603441c90700009140004002c603003000c280c910407065072012030a0078546030603215204140c101400f48104120144001a032143c00ea40c251540941440c40d04c1d00c4120501e54001030701c0c0c110690082c10100078040700b00840e04014042403141c4803c0c110240c603103618040d0305004903100032200004000411240c0b80c65511060300900480009207090360b12096401150003d95048002c174103c00c80410414420082466004400d0b0018010100c440d0399034055a00c120640503041c031407184820101c0074030515041100d211403541190b40c0b56124203011001008422040340094815084d10000500c0441d05548030030002000b844161138030441664200c20704112509001d81c280030301d040b410b4815a0f9031005002d100c802c1603841c0303865803c40e130034408a08100c0440e6455074800c00006083d6200d0f04040b0398892402e0781e01d52081d50894480010036910107042445014a00c000c00c0ca40c400007044c010100ea4140e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 278537266 1250 278536016 278536021
    0x50a09090932030a02010b040b010c0b0414070515070b061801290a03050403020c0d03020c0f030f060f010509130201210e070303050c0d081311062104050105 69
    0x4140590341c2000c0010203024800c01e028049400c155403070a0710140600030340308500c0e9454091861508400400340050307450315400d22036400c0c54410444621420310b0001f441c6145921510180b1002410007004058480480e1140750404d01038003001e040d00416002003a81001c180d1023064110341c105072010122040400d400f4600500450700c905d42c0c00e890318040da8a030608003401d2404040303001c0c0201031205e0f0071050100d400e40043c000350301c072501c0000f01c1c9d00701070170f000b45440b001c1540c46016240d01100d0300046500082c050924113000c0300d4050f05241484c000ca41070081c42c10b14286244103038402c2c0000c0c1210b142e10f00d0305035001a9a9454541c3c1e6101c9581c00902800700040e010074031b0440c4520803020600c3d841c501ca02e01c140f40c0400e080d900350001624040741c0c0d41c410780003d007011641e030850340f40610110f402c5080514100f0081c0c1804550310101084141d0001e0035030090490700b5009440e184141c1d01c0c420700d0802d080411740840441030032088400c450449465280000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 278538516 1250 278537266 278537279
    0x50601080915060402070206040902030a06090c05091c02040c0f12060501170402150318010e0a0309330e01030c0305190e0c03121213030c03030f0e010c050a09 70
    0x984501c60607016004000d020701041d00c001d1407060180086411903001c01000d40585ca5001c010002000f1030740e00181d9030302c0d1208000342141d00581001095134104420016815404401c4d680100c1c0c00311800f41034000e401c80302201d0003050403070094100c2d081c1081840d929030407981d4040d4402058491142103a8410008000c0750740314015907001c81c4008030300003510820304071440e03407040c0301408140c041c0600080020b0581c0045a281966030341506103403104c000c0a0080f8981014240c0081014950990300078003450760501640450b29091401410505255907088503171808150850190b0035041e400204801c045a12480c0840d00b4500c0840d01030f882845410301c20b22a40c2000ca02c07901403240884050001c5012043e440e10074030085000f25030b014800c3d0030010003407420882c2c0d40c101d036008080c810b1500070005146184141c20b0500403e40007040c036006141d00d03140000391490b034120b58000030000c11a00345001d42c68801081007642c2c00000400c101c01107503c0c1c0f41445591200f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278539766 1250 278538516 278538527
    0x21070f050702090103030302090d060908031f0506040b07051204150e060c0d0f020a051002090f06040e0402060f071a040606080c0f130204030b0f060f01030908071401060f030c09050601 81
    0xa40003508582d0030001000464880ea0240100c1100140308410101c200c2e15500300340d40cc101c03002d55203848000f0600042c07040f44181e40100201940002d85454500000113120b8001c030703c42c50701d203414001000f0003002414480d044c120000c0107013003912030780c451100301e4030104c8848010300440c584101c0c1c1c144c903242000a8507440005030006100b500400795040380c40d03a016145074170662003011814030000382c041c0300041c8202c40869005807030b000c200041048e03000c411030b01c99000d244200000d01040f440c40320010750181d0141d81e2259120b846150680342d502c520a8058091100c4004c0047c11283c1c20001c18000c0d405400c043c48001e85036028981c5964820561642c420780e220311204050400101000c2c2c00d0400700c00040c1042d42d83c0d21400d94186040b036082c074080b41c908007086051301d80317001c0c00b00c9400000e18040000f212243d81300c00303e86c40350300c602502015216640440f40301c400d4010002a1010f6101240d1055407442c02c1d09140c5030074094507801c00e04210000d0300300e51290707 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278541016 1250 278539766 278539777
    0x409050c09090601030b0333070c0c030b070c140a2d020d02030f031b0d0206190f0b060406020109060f0e030924070804090509071a0f21070f05 63
    0x41c0b4550040c0c5940d80113400400c082020181c160141c054140c1d80c1001c0c081c606c00300e005c0d070b4525004405003681e02c0d40000e000001c0ca0801445040729110740880c41d449240c109907a44440286ca241d01c13070107000d41c1c401113202070007080030003400340c420a001c80201d01480b5140c0700c0e80481129641c140840d444020381c420094001108420040c005882c24400061045001505031083c540e9115016800c0d58403001c014203000203140c40c215507081081000c0c0e9981400341c40641020309103c14106010381860118030321440e1078100c0364900d540242c0c01940e844c000201f1903a42c2d03541c0daa002902070050840305030b410520700081407520415501514010315180c00141d860504040c04005031001c03c82071003403040c01820b103d103180c0b00880e002080f81d1809194490b46030391515408000340c4d032000305110305a80102400f0003840c080c811105004004049000352164020310400c041c07402620030b140d03d414200400d0300305c40106001418091201555a80c114180c102420369481c403a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278542266 1250 278541016 278541019
    0xc010806061903020c06011d0f0f0c0a26011e050907180f06120609021305130b06120402030c06030c0f030703060b07051606030c0c0206030c130801020409050c09 71
    0x100600090151090814014100c00f818010f0506000b040d040e407a00ca400d8000c2078130701d100801401c4884001c45219030380700c80c2501c070403030301850802c2d40d1010060024001900000c4007140c00302c40c25000300420306008904803004426000003070302e090300e103100030300c0344030304501c02ca0240c3c04030000b02c64002c205440c0c01809140f10b41e265403104172104810700c8035190f142400b541001c5881a802d4815500030401507481960740d2203060030a03011542c0a9120310281807041007038a1007114180150412541d0444030181c24800b1445c90030082c0095002242d4000000102c4401d49074202d1f0071540124001d4080700c4c640d900500500c4402c0c4400c7d6400c042e0b01005105442048809900840e80445245008201180d481841e444142c0110408580a401c1501410780d101c03c01d06c07448004005510b8140812100750320701a02c403d40b50343c2d019002d50400800903d209220301c0442d119040b400d620025000d41d9008c00e28002e410070b020320b443d414181000700d80444083c1042d100110780 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278543516 1250 278542266 278542279
    0x40608070e0408040807030515060904020321130801091e0201080a0207171218061b0f0c1e0f0c060d150504020c03040305011803020d2106030f02030c010806 69
    0x2880100c9100c1c25004100302d4030000100030200701351000744048001588603070002d1801c07030030013600418961390050200c1c0c0aa28400200005640c001030034020034181e1005100d016107040c682008107105940305914103e1403030b400042c480c00f05510800c416070041d9803081d81744600c0302034440c0000290348060300044e1103801040c404990b590041101c1340c41909000c0b0000d54220100e078041d00407100d001c0d400800d2038104254000c68030020303000c04101c0300190005241a002441000c5544004a0700070316001c11152601030070101100c41030074501d01120035100e600c0103111410001403440034100d010b1926000c0e11040e0004c1e4080045800a02c09c1e41060700c1118850000c0124940460800c1080e40740000d043c2c4507071005145401c1984003071039940c1d046080960945040311050700c66103145d22920700c0420341c00300b0358601c0802c141c41d252140d10004100c6030520340504184889407454004000b081281100c60043c0c200e00c264141c5a0180440c4015200c96404403030b85500001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278544766 1250 278543516 278543519
    0x2040308030f07090e040f14060402010504090e071d0423030702010c02040906050403080a0e12090f01181805011502150a1508010504051c0e010804020a3204060807 72
    0x700d06461035201a03d442d1510712681d83e100800c401840603202a81c5811000b04200144901e03da00081d00c201030400420490903d540020b00c58030880c454044102d650351090314014206004003001000740c04200c030307400c41490110303154605043d00e085030702000892180482c50f40800c8403600b9031100d000554100000d580054409520090301281c2c003581c3c0309517403000142c10744181c80c0900c0c02642c8411407440c050748040d007283c0c0180100703001503210500024915a40004880e07000109581802e11140500c1c0181e0300703500424140c01031100107030703400304549014056140348441c1481c2c3c180a0359aa406680e02cbd40403c140a00c4016003048449550641005061a80041a010000440030320a4414000350f42c0203400c2107180d0f035165400d00061182c100002040e400741405400b1807003a600300302030a0040e1a85e06603050000c4c6000107406d554409000200400c1b07007801901c100152000c00540b802d001240440c1d4103c3d009440c54070500317181c030a5000740ca030f01500a11030325 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278546016 1250 278544766 278544781
    0x110a0308040209060103020408010e0a03091403030715020f0a0201050a0f05010b0a0305090f030f1201060306050901030f03021212060109060918020f070203160609060513060c11090117100204030803 87
    0x141c1c0080004c2d0505408100c0042d03145000d1007829a0504544041c01c20804a072400600a04150b48040200b00000e945100e0a41d804401c5511030740e400488000640c450341d120074043c0c01081c10141e40c1d280c01042c084526501900594425001c0326410001d0405080424080768001c0c042d070040c00c6028012018914001e6000c85e802c01301803000c03900e0301100002000d18552140d0350840d501803010802c0c0c110042140d03c0305001d407045003001c0c03101c0b034100408070325006414030000d400c002500c070103902803500902049040c1c101c901c100c5596011009000300c090b400c141c41c0c450000b018840b00160700e44c803a03056401960256401e480541e108100e074400a50001c1b95a03507070091040082d000183e0b000c116140600c17031840e12a1240d00d140c854003820200c103035031203c8140b0508101c00351007980500c0c41c400c00d5452500b00400e03004a6404c02c840507200d140152034001c511039001140c0108107408080400803a0800c556070780005400d090700303900540c40010440d030001d10114800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278547266 1250 278546016 278546029
    0x903070b0112140106060903150c02030f07030302041a03090c0a180207050c09070207031a010506090d03030b1e04060501110304030b09030c06010605030a290f04020d05010312110a03080402 83
    0x101e002c0c404100190b0843c12030682103603003e40c00f00d0b001c1840c20104000308000744032442a214080c8a04000d011000da030007a45034800d140c20f504250030001014400c150096064501402c56250b95000c1020b0340052031040d0303801950702541d503115000c0d0b409802d01c3e02241c280203031940c0c80c0a000a441142c40302e00f019400c090300456403401181140e00c2d0f05e40740c0c030304058032900d0594000c7c8095807650428130800601001070003003040003040140325507200d90040300d41c910400e64001021507400d0801f10020907642410562004080305c031030880b403519114001c0142d03004c4a042019560f210015964202020f503140f03440e8005000800224900c030340043d074400c010310282c91410444458144c1402d02c00d070000c1010130780c0401803080d480420300c1030303010210924083d48469202170181d018100000c011203840f40701c0407000a205a2500e4066030740d0407407107000500c503d507124904205c000c110a008140000d403513400c55100080005603c40016805845d403e040d52210f40a0024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278548516 1250 278547266 278547299
    0x40201120e0c06070803040204060524460306050108040204020d09141b0105120a0b030c030f0f060703021213060207080403050c01112a030c12070e0903070b01 70
    0x165000b0101c202c440d07912210300a040e424032402503640e80b03161520400040fa0200e40049008103034a0001c56000000703c003a14446841c0089a0390711010313010011078001540910088418803240d48103d07174240f141c2c020300f007903926800d0480070605120400f20f00302d0300c01d03214a5000030403230400315025003880ea0040c040035900001c089914240c544550754500890f111465135a401520080480c0065101d45190700e603003460440d160080e2054018190713900a400c84928070758844080140b950100701e0301da803502000c2c0c01d441446034180451911003c221000030040e00403c40000c001034440d2080b10340000c4407a40400d216154a054010b40341036640048904c01d50822214000c84c07200701c080c0006520400050202c01840d40004207814081c1c1c080d02c00c15800329034803c1c0300000d6640c100b180c900306c04000b4200301c201880009d1600f08041074241d00300701d0751042185011130200d004400d8544880e2003002c0b5482d09049141e492140310382c0581204100300052203908281c2c0b80000c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278549766 1250 278548516 278548541
    0x10e0301020f03100311040605010e06031e0a0e0714030a030521010308031e0c03060f060f0a08010614040503070e04110406090b0102010e030c0a17040b0c010507090e04020112 77
    0x50800c9000480d580701c83d407066428204202c1d1882082040180801c2c40784200603080d80c00b07110051818002815005a9100c141d01c90000800001c1810483c0c3d817046420120079805104a030a01c6c2c080b0300018500c4854003800d9000303125001c9071083c610b81c482241c00b00050010080c0d1003041d00d00311101e400170b8500d203001c680807420b460028400c0d081e01e82d0185d0b01410340c6a40c3e07801c0001e0480c3c041040d01c0301110003c400c4030200906101c1e01020380e50710041c20354200d8414030302400098860311404203d1000a2004200808003503442018941660855200e000b0401a5a03403415040e024511485a05074000c0301c048c80005800c2074000d41040c031400d417100941c6140000a0251340d05030f001400001d5840441020b10769090240c0c88c0c0c00800000a5884d0100300c0c181c068546000c0c45014141c24005442ca012046e0381e88200c0b40140340210020381c0310720107681c071140600390580e00407000640400022986006901c46140510350503140c001c990801050351a001d42050800207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278551016 1250 278549766 278549771
    0xb0f04060e01030b1b1c06080604022407081306200d031505041b031107050c0909030c03030403022b0e010f0207050301060303120509030a05041a0d090f0302010c02030a0e010e0301 79
    0x545c10700c120401400d2130303108080d041407491031407030261811200254407240040e44000b0500015803107880c002104083c0200d0583c0d0103031090003e0042620444400a00d41e54001030f8030001e03400146014070641c2c0596580f1860080c2d9240400b1400c0e01ca6540400a40c01110301011654045c0e8005d4008414521485000713680d2000060100e030341d80031983e11000030409508a0083d40341c42900d0151070020003882c00c0c031041e0b840f01a034074100350070024058040440420a020400c0054541686881f400c07030340d40c1d01d01362400a40729030aa11290b56181d651208541060001d91081c4202c00601c0d0348250002c1c00c0500110740100b02a4805400d5014408000c20395881c00c0c090b40004d10b020f41c98624051911981c03900c01c4440007010380201d90000e100000c50302c2e0b0f00c00111800c4a1001d41e40030442c2c1c000101c017841a02c20405051a0180307004040c20800c90403001c0e42120501940003080045050001a40c0b2403103112003801c00101189003c203820341c0114070104c6180e6001c1d000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278552266 1250 278551016 278551051
    0x30d05150603011206060608071b050c1c15270c030b0108160b04270605030d030509060a0b22020c10061703040302060421150b0f04060e01030b 63
    0x1c102150b2003a04001102181c1c524808117200c00c0b4011080204443c0c54500518500607200815480b81405500030007600c0d42040001c3c004100403402a140e0014150740c80d810300c9000901740140034401c100d881000d0780c02ca082c2e006002d4072440008140020f01032040c1c0f00403c20940b13841c0c0e02102c00300d408001c800404070100302c595403854083c1c001364004000e201d6200c140c170b03070403100ba9510416400388208024007210914802d03024941011a0f060740d206080c3e054041c1c0038040700c0e00290781500c11100401daa066140d0030070380c02550342500ba81c040303881344010340c020707138081c1080141c102d607100030140c076410031100e462800002c0c0c0010040c00d22110881d014200081c1c4015915004d480b204180f01060419030042d41460074a07006500d041c0c61a400318015000318070814005001c4c11140061316502c0003441104194000c02c590000c0c18035040c200014110418890b0180d089000000d0403400c0600c03800342a555200f08000e5181e286542e02d141c0c030720000b0300c9440028041e510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278553516 1250 278552266 278552269
    0x40506120109050f160b2b02070f0b01060c05120307021603061a0102070e06060304031704151d070b0c03040302270c040b0313030306080d0309061805030d0515 70
    0x3006045031060010307240900d004d0340140d15003001850300a03601146a4820040c0c03034a0803080390f5240c450580001201c080040f000c503a280c8407540082e030001d00000c1e283c02040317100c20704034040500c100c0b40740119036200c0703000321900180030754010151760014004640510001d000b031980f0810500c103c900740400c52207816050300c2140e0080ba0002d0b00c4400c1903200006940605861000a10050048034544107229078a484e010302110702071200007000c50309143c8904183c00f05a289030b0940342441c2030500c0c0201c602d24109005800742c0e0300d0a9601c00034114550356007560005068014081c0034241a8082c0c02c2e640204400c0d00d062004000010041c5c54640400b5a21f1840b00d01c0703074040c000320404105c0f41041c000c10100780c03004200414440c070b1803050243c907001040c91000b00b41c002d80030301d4240c1c004d02c0b898000d6481d600c6140581650158550080308419104800034440c5a0f07245095049003058540c001f03041da00244981c01d003c800592019620044240c0c002d40244100b10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278554766 1250 278553516 278553521
    0x20301060f1412010b1003150308120f060411040b03180a0b150406030f03050309101802190509040b091203070809010e1f0f020415050406090602011107020405061201 73
    0x500500c16003a450b50b40241615024503261002d40c5001e000744a05d00610300000c650000070b100030804e1590303c00750700481c4415038144402466000740703015620520300710a041115021243c404035000c00070009441800c2500030304616107503a120281c02d1500b840f40e01401c54000411206c00b8080b110040b29100008002d11a9014004c921080a40c20b109080d90700f0105013680c0c6a006a0401724204000356005e68052100f0360076142994490b1120440d40b0b04150001d80450206410202c55202150300307035003400700c035610072540c1c0d00005000c0324000b903050240303202e02ca600c102c00d10002004603c640c0d1400741d1005254083d81c1c95020400080906a081a05c01d5000140e4050400103090001d1140308405c4003400020410080c1c13107040c3c3c42201c0380c808461076029480f082090442c0681d0b4045d940901a820310101c0c040d401100000c0440d00644039200c0000c08465000400d00c1c0107104150702c2d50140751045c1d00d801c40725000c4c000684000740025410560418bc408103843c020b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278556016 1250 278554766 278554769
    0x19090503160b070921080910020c0f0406033302030c1c0504051002090301020705070b09010906050301060905040b0d0615090507030608031605010902030f010c03110306030316020301060f 82
    0x3035240401441940c1025480c03050028030031804d20074441010f001c500c4014004001080e280c0d08103640300ca400c1d2800b54036a001e00720304190022000809010750710340200c1c10548100080e00c9006049042100b0402680da06100c06404603a0700903808008030a1410710b45030310320041c05001041c0c1d240c1140d88003244d004403110304c040e94000c1410707440c5240d048030341c2c0900c40e81c5a01c03e11480c02d107619001e485210754105042842d900082d0b008007603c0a40684480fa50440c1c02d807000e00e0b56a41030510190300100c10180022810310000c0382035070041007035034140c0300f00b81d44004056003440c06203c02880360303150741c6074003800b51101c500c0003801d107000b188800048601d0036001189070008050988401421820034141402410f10610500206a1325000c0382941111011481e40c03d005004080405002e50903001700d1030382c44804e40c8150032103003000d009036400704411182704851102318041a02c1803a03040d003040114840400c0b018007100412030000f0000600c0650780c8074810402c1105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278557266 1250 278556016 278556037
    0x304030f0308090c06180904230105190203040b07080907030b010612111918080105041a10030305090103020a021c02010b04050609040209010e18010f1d0d0819090503 73
    0x140c04102052001313004c245044103069442c14240381c8021503d0104c0482010203d02034015040090184a0360700c02c034000d140300f203c01207419280d0780d103042406444100c8032410000a10400d00000001c0b034402c9901c201d070464044080fa80f9080300442d041c0e030015041c05014441c205010000c43c106024241c021301e116142c2c0210b02e0810751180042d6484103250001045082c000300301a18002c0c0c61441046042c0d00d4085004100c44610b02108005600402001e601e004104400c20120341d50341068041c007540750103420b5903503090103007400c44a03001c0140061424048504e56500036005031440c103455006448000c1d5181c0f45c4010500c2c0707030a22940060b0b444428141150825119098109006903421840380c6400c0e008034180c92810b2182030b05031402c580006070101e503501031449102e00d4001c0244a082b07a18114100035125044120928aa40441d00c051aa000140c004050384160f190f03050581ea0311551100c4108200c3c5c2d240c01900d881384000c0c000100280001c02c028a40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278558516 1250 278557266 278557277
    0x90309041a0108060117071116030303060f080106080a03030e0307020910090e0f0703120c15020403110f100509040b191403030c0712020d0b04060515040b0f10020304030f03 76
    0x90708800140069005401141840840c0c8010304041201c0d403080f9900c101030b400c0203c050103989070414901201c13900c03d85c181790005c0c88048200b6905401c0f100c01c9940c01040d400ca8284c680c0622802c03551b19104589980e400b01c0b0040c0c1c0040e02070380100c1e078003170b4100f8107480c2886c003250003240c1164812a100080c5da0788101c014040c0b048140320300c00e40240000300a0503a0000f034291980d5544850001500306061080d4040c1441c0c850406040d100358404103041d2040c60010704403000c0e400c58001196480313061900c4000710300705120b5a5448100081c2180b2041c41d0401d402d50b115070103c1c0b4066001510b402e0b025090b92909014103c100c1c040b810200c03280d62510103400341d50f00c00d00310b0b0a40b1a4004101d90041c041c1c00051748415034512020280d00b60201d40f00245103003061400013046005040204000c1c80500d501040c0304441c61308803902c22450a400b0001101c0301080416842099071280c6c10841c107028201214911040c01203d140644a1303d40350501903184004400065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278559766 1250 278558516 278558561
    0xf0306030210111014040803060d051005040c060804110f040e0d0c020f09070210050703021b030703030f050601050f160b0c0301150215010605180604080f010b2709030904 75
    0x14080144408881300c02c070040004c2c03d0701d8502c0408501c0050005894510003202248165891102d0207541c16404000c0b5008000d0949221020300400c8509483ca800d115000081150040032054800c6900c1850801055130715410031140c0054111480d8009a469842c000c07000b008000e00070000f00390b034440c0103d12080b88100049141e1801a25009603880003d12241c56000603c080c00c0c1d000c00400030a81d995503600850081c010381160601390903503281080c01c0c0610101c01848030038000d580a225010344546d502081d50300640c0e02c90700240b020003020f810450181c02500c400300c2c0c00c9007486002c5115484032800c94000f5a00c0c0104034a0001c01000400082d590b500000c4a503400548254540d000720030400490500c030b00e02c10301c00700240d909902e10a00b410b40daa050030051400e5103490302c0c1c100340d0395980121004080c203076283c101d0b00c41451030984440780e80051035403c1207035030850b0100854003209002e04400b0140c0300620050a89642318000c10250412100b008440c59 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278561016 1250 278559766 278559797
    0x106090204090b2407030c06060f05090a2c2a13110f180a03030206070921111801150f0f0f1d03070f14120309010f0306030210 56
    0xc0d00b078542c003079103d444c0d07000e4150150903042c007500100c80141048940c645405040a5840341c8005000521040c68500049020241b0140322001c0d1001a140c2400c05d40e2118011000c80d051405100c0780380540401d40c05100b111007030fa180401c4401c0c2d0070340e544910506044580741301d5031281f80340f105800884009060502c40c0c036081010503000c0e400d00158a50001c01c006511500c1c4048010f1100012959564003840c0b0f101c040e00340b8060320704103405070750f41002511218107540840000b070342d19800044e00c144220f01c44404800542e0125092111541c4280ea452580c00c03074160441d280a140c4100d07200461082c500a141201d0702648241203110003d010715510321064080c0003003000d14403922540050f03109644841c03801c20f1222424115540780103007c07500c00b02541841599004110428540014001c40708c7c880441000c42a194040066100c5074800310146648140304081056101356041c01c000c280302d090000e501c645a40100ea0079510100842c408a801c00010b1700e000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278562266 1250 278561016 278561021
    0x604081e121f0609140604080607110d0908030417150c2d190e1002010e071d040b060d0206071b0608060604091e060e0702060105030a0b0610020f010609020409 70
    0x51452050b615000505018028000c40003901520940c2105100b40f00c50588802e01240c024095403c1254864030708084020294007004149490f18002d612207080401e010301c1d034840559801d100038604003030401c5c0301c40080e8a07100d10952424440c030213a100c001901d041c0081d01800641901603900d4a0ba61030b031045804c1c03020803402a2001e030152100c415035001c07081d50210007041020b41c0303615454542c2242c1d503110004400e40d101d451000c0d044a200d070158080c01524000300180c0c1c3c5441d56038031924070300f4203017141401c03000d084400c005070009840c118591382c00039006040ca082c007907554011a2140d0800c48080341e00480004038041480f090100c6c1400a1070b1900d010b20003803401c640802c0701350145220340ca000686405a0020741c0712401045401050700b400100b00c0160388440c6000c0000003640c3c0e42c4058000c03200003186504010883c07103403072508031500080a48880081c000a8000e0345201d0086005c0c60840c0101004280100350003045101c2c005030b2a10b0070f0050083c00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278563516 1250 278562266 278562301
    0x4020d021b1c050f07030e0310050a140a1103040b0405011512031106010b091306231c0b070c0f060c050306030f0a0b15060f0d020d05180604081e12 65
    0x140f0030103110084148083c5001c131681d8942c10b1501c0144001c211011918110942c8412402c05050404021080880da4805603240d00350034540140b40c1ca50752050710880c3c0c05c61704400c8039002c4c10800680812098030340d16410900c41d6000280c0000d18000b07001030b102c0d00c4c0d041a0a46900b00c21800e041c140e0081d44d03a003040104c0382c05402a075243c40c0b0400c5080c400d48005a0080740b240c0c0b1001c15038450344d072150000341101e4040c154070100c91014680c15a03441c0f2401d500c10342e50f55804020700c0005181c5010440d50004400c080d43d1100302c819110351240202c1242c111602030a04000035050740200840080551166503c90070540c0c201070804940c84407031881607100c00e0b100ca022a0a10301c07c1c030740001c0004240035885003407501048241c8541c994403400c8800020710507074041207541c01490380034500c01040140c0d866012000c0d01030041c0c6402c5a1481e0b0005000c1004125480020907413030712031030700050801c0741005106441d40c001300e01612134241d40d0010040c041104400100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278564766 1250 278563516 278563573
    0xa0308100512101109030303090c01020105011e05240d060602010e12070803070c0210020c01020d05090f0f040b040f0605150f03010b0c010609050a15050a05010c0204020d021b 77
    0x18245040c1c103040320399804a143c104180c294841484502000b86002125001207000d01500d03a64130300a4081c69603481c8280303d00b401580703400300004401800140784080308400d940b8840d842071805041060310307107580382101b252100201c184101940d4120040c18003a42200c0041046880c081c0e020382140c000c40480f000c1500481000642081c003482152011030340184070340c3c0c40b40c0380c81c98104c58403100220025004110403c0707503c00650001130700c0450b20000d80c01c886020740c42c40300c101c400c1d000310303400c580c2c101c011840940303054544440c11034092080904001440200321000805580303100c041c5000983d9602403e2002e418407843d900041c0324009a851b03d003031468845031000c0c0c80144030b00707003403404045a9080100029001000201886c2405002c20b04007002d04100800c1003101c1d410140144041c00070304c0c0d0901c0d01112044850585a100700b0b070703969400b0700c0702035804124044259907080200000030b2484840440d104a4007200910b400441100c4480e03901d4511040c0d203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278566016 1250 278564766 278564779
    0x15110304061b08060d031d1c0b0603070f03060536100e03123c07090605040b07020d0804030b011505070c0311030a05070b0307090611070302060c0f0a03081005 70
    0x8502070310352055141301c5650519005552400c65207c05c4440a442c0900f1a0712032000000c4900d00c4c01c1400c1c0080703010707000e07844045180d00c0343c2041665800d00c1d0b1061400f6045240f00030000b0455030350000394480c030001101c00700341048000004e140c8070958009c4681099502c03141d5102c42080090150040c0850000c0002c42160402965240101041c080d00c00300e040c80012143e80b109040140040c3d500b800511000c0501e05082d203606d000408240c084070070000c0081c20051241c0004c808952298440510781030600802c01c00981c031a8506a8018412012040c0007940c1d0300c000303100860140b403001d461035041c540c501d81d04100c41015001004424081d21002c614000c0381041180d80c099080400030440d034001ca41051030800025200740101000001c10041810043d4440e440e02d0b598510704940b100416101d120301c1d0340c28030016a201160520060400100401854500034100c841840500458518003074041d45c048001420503020300a0602240010401404040320714 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278567266 1250 278566016 278566021
    0x905040506060d1e140402090c0a08040303021b2401170c0603041a0702060f0703110904230403050d06051503070810050a03080c1203090a15110304061b08 68
    0x181640140c9807510491a5143d1804c0a01508100242c944440d444000d1002081d84800c1c0400904100d5090b4080c1c1c03011000500108080b0301180c0850f040ca07210700042c1d80b104e1b1000c900035084050611480c0d13101890310035800c0000c0040500ca4001c0f640501c546a150541e03900c200784043e84624000404810b1400300c01320f010400c50107281c0d069501640740e0381c4d07608040d0160000d1894048540d080c2c501888059640810711500c10307100300e100341c402c507210040100e04a41d04d06507980744075401030161a096103411342014001e8140025611602e4010700b403144481e0506a6045001c41c0d400141e80420550f580241001040f00f01d444680c01034240d203d08005100082144c000c200c015000101e5203075a9041c941e000c2c10b00540038103110303600c034038002da02c2e5441190b591815100d0350540d01800901c240440f44502e030040c024101c07001c004d548107040242d080701c0d00503c1a4650f501c140780180e861001d507100e0703400703600301003010004c4594000e0b00190b41d003404400c220b076607401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278568516 1250 278567266 278567269
    0xa23010504030f0e1302190806060a0c061d01060e07022e0b151809090f0717030403150b130902060a050c0102040308070305091c05060408030a1d0d0905040506 70
    0x4410300d10260309114552440c02000170750304400001191001e50310100f0030480c0c2041000716500c103c403079900c03032240d80c0d1180c4082282d02d000b10480f010003d402c0c1213200c000031f035260f0060135050382010001c0d80c04a040380f8104d425290590014040500d42400302726005030304210403210809800c003240c030070b03075140c011019030240044609440103031102500303400c50b119038007814080d092241f040d5448400400e0f05903080803c03441c81a1060303d060010501248001c54030f001c0351002e940c014003585103045244100b82204e0100b0301100c0c0000d00c00040825030b01061450410070400700041c2182c40304042280c50305406095441b8103107031900300c1c0c005072030f020115210084141003240d25041195249400b80c07242e604010300f49038006caa01010160418080c1101e044221002c1c1d00000b0503040f01036000501c1140a4005d5001030041804104150011508840010b03c04158507810440d200e4140b080d8600700302c1c15601500703a141100390301c00c0010024040c1100c00f84070500b4440c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278569766 1250 278568516 278568527
    0x10f171c230702060a0e0111100605010f030509030d0b15130303090603050403090e090304031403071716060207030309140f0f0f0a06020a090305061504180206120402120a2301050403 80
    0x2c1c1740d106000720190a01e000340c0c0a41e5822030980e0000003110000130b0307a03000b2000a04540d12a8501042c00d00303803031464490003800b4545c861004000154100300c00d00d0040e5000d4007260f582690030144264241c1729042c4150000c003080000c08443c2e11900e4035500d4001c01401a40e40716504040c6004148400241e05c00041c00443c0c00e404a81b41c182d03220658400e040d445280c1c4001c0c841006400c2038940650040082c02c00d090013a000003000c10a0308600741001e12a61400013510f0001d80c41c2070002441e20340c09451030600078580000d425449940f440f0621804482e000c40983c05a011000c0d00c03003042204401c000c403544090000009000d50b0560b59407503605004001e550041104e02071617108040e2203004581040880d403c0f0f0501440f1041803c6003429602e000d0790800c03580001c04030703100c4d011480345030703010b090f0380d00e061000340d40140e429501410407a80b0ac1e20302c04885810040410008000c00e000b04655020424042c0035117450780108156084241d0528040002294101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278571016 1250 278569766 278569777
    0x903060a0c051b01050f100e0c07060609060b070b2a0304060f0c050c0f160315060e09031b0c01091503020f1603030e06010f171c23070206 61
    0xc0c0390200e00600840416503807805001c0c010282401c820300c44208103201500494003e07007404520386402d481d0079490006072460790045603140600c4402007030341e0303503003000043c00300c0c9004010000c1c141351a40300c0700c01036800340e510000041c2c80200365282442503251800341c0281d101c01242c03041040042011103c2d20400ca130307001020300d010000070300348000c503080403500201c00201001240a000d00151240c3c01081880403144a0001c02c3d410f80c240001d05658076902c070000201c840e0345140d13601c900080c0b03003000658a40313407070b0702000445003c0c041a0500400c1d600014580b64100e405044c003a4101e5840d45807425484102042150f036080120502501d039100c0300541c5103a0a024242c0180c415071500d0300241e900055a00e00810016400030032043c4207036018460f00c1d9404451954a000a0090003100304094504100301003000328503984510000007a00c10b003012620036010001c203440c0d42c48010444900c030009405083c0c00004124103c890103050500000c0d4020500a00ce078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278572266 1250 278571016 278571031
    0x9031704050d0302180607061d0d170702010b0901080106140609090708062407020909011406010e03070f03080315010906050a05160f150c03090201122d150b090306 72
    0x560b52072461410a030703200425178082c107203640e00c071100d1800100505150f100f10b911002161914020310901040c20a4401840e0341c800f40b843c20106980a0346840160a80055640c0c1f003205112a444058440c0d00a00388103000061071842d004001e0076503541e425081e48540d00401c8640c280365134000f01c0c140c000c81c003464110500d650712404940524041ea441070013124902c0d504242c1d1441e100010204070380b094500d2107442d11020b40c10390a031000782000c80500224000054890751140c1c607030231a071800003800c4410503695152070540900882c0c03c2610184000420402d2650801042012803042072a00c0c9048610304480108030307010b426040c40802c440020a5800030020b010308910090b0440749110f00808113282110303800c80251402080070303081c40c1c0e88281441c064070820104a4041c2c542c82c5402000300c100c440100352143c0d190311541010a50000e04084000a840404100250005070701d91030303a4201c000700703005a0120321340507020040c0a01030b403004680603410682 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278573516 1250 278572266 278572271
    0xd1b050a0f0902030a0e060c030603010b0105040509070c03030f11090a0503030c280204020a0807020105010e0105100c0c26010501091e0b030a0501020a0504030c05060c030f1b1009031704050d03 85
    0x1038040305d50000c0c0c101c3d60344e038221502c111014420030704080401140a038000300c008203c1d5004c0034006554900641c404c41d030344540ca000006150a0180e0084420207119243c001020700e2181c0104040300c010400300008440007041040d07041c00c00701d40b42c20290500310000d5040241005155039150228600400a496200040c00400f00d05420140c0c41984c0100195211224810024000f4600b118118015030805000040441072640a1410307101c0150112103511000340e82034681d00b044078012108102c01ca0b40010304442c00c4c1c3c00da0000e01c641c6d0026a89011002c4c16014207450042c1c0004203080d241020901c0c40514070b402110440a804d040420201d00d9140043c0c00c2c011a07800281440d4000582d601805030b000c4010000d40f407080c0c00215101c0d40f140c05004450103011110002a80100440c0c2e1a45400e031028004580d4054038245070b40c00e44070641c60a01c1014104019816100c48005c0d04050b00170307004c858403c0049451041d145081e4640c207070b07149040c0ba840000d165 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278574766 1250 278573516 278573521
    0x10905030a1b1203240e16180f03021305010807030f0201020a0b070801050a14030c09061203071a0906040507050f0112020c0d03060e09060402090c04050d1b050a0f090203 75
    0x4060005070b0010307003040110a0031442e4400140107013001c1e1a03407469900000090340d02c0c03c01d03207100c5001503418000301500709698400c80d402ca40043c41480000b40703c50304869100101d50904050050300400a84130030726480e610601800c11030039404000107609120040c0045200042c2401c00c4a801441c200e05081c45c0c1e000603070804000d1100500100000c500700320f686078125003418100c450603102c5042d1541c0d03c1040d884103580f007001065058100203810030480c5080100c40380c1000c00109062220703800340032080d18662041c0011207803610001c0c403000f00c2d842420041f0394818442c00c0509180d14081e50740d11785407a0203015003840b904803c140020240d11441142074500c5500c0c504564851b40c11415907907a0440502e248002428042d0100340c911f40c0c04d110b54012a00040145100d0300d85508100e000000285414071481090000048580c0d91440144655006d20709011100c2100030100c940c0045a802007805030009170400c00402903d41e1080f0200c424a010058813034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278576016 1250 278574766 278574797
    0xa11010306180b0a090b060d15050d060504050709050103030f110708010606031b0509090f061c03050903070b040f03150902040219030c08130201050c0a020a090b0f03010905030a 78
    0x4161540203030b068104007400782071074140690700c00c1502440440f075404140340e41d4661a4180d9031462141600010300348015440d6481c50707041201544480910858074540340ca0208210a850000c19170f1030070b0303d031801d0100b480802e0201130083c0500420030b04c0a58110b03100a49403501d41024501008070600d103410301c03650184841d00141110b0310003440000d5807040000d020701001f071007038a04c445400b00c400c807032903024404596040790301034410400c036501c0726050381d00880c00500041d08807800d80b128a04801c00c40000d0700b0424030980320b294840340c0503000c1c185406101d41020100c50307030400c414000c0c00799002c1d0240460ba4443c101154040c5e1104504010b0900450002d402c10300101d901c49030007080750b8003601505040d590800c4009a121411101c036442030b55003078041c24080e200d0703d0155100b600100032045000c811109040502d5010a620360025402100340320343d01c1c0c00003801844c1c00c02c01030038031850840c028031401c0c0442d15001c1d224403548502c0014130214003240c1c02403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278577266 1250 278576016 278576021
    0x1118060403330513051209150c1603030909050901060303020606040903020a020613061205060d060e0309090907140904050d030914010507020304050a05271b0705010c1707020a110103 80
    0x3240e02d45034148a036040280d2080c000c100c0d0355004649600484d1080729041120b642a6148004000d08444400d80c5250300c0c3c01166001d02e05d481c1082c003448941c04d9540d8a030450240085101c4e5981c040f45520740400502101c1c405403615150342d04180080000c60f2380061444c3e0042c0c0120750020342501140340580ca02203410100a400102c04a14020310400590086040b12a01d4442040d50505030071148129030088480982c06003e080b5100049100741d8040c034096501c1e1400c491800301c5a100040c1385000885440d02107603c0f5400078050030340e4112400c8405402501c0044185c10107660b41910b03818481a50020190307202e03045400d002d02905061081e05079100200540d0130071240094407940070f13008007400b800840000240c14189810019402c50101000e8401c104060926040140014200850103984446100f00100240c0000c02040e0700c110000500302c60480c0005d0940074601c2c1211840b290b49108116282d500071030901810355100b03800c0720700043c0030301c0141d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278578516 1250 278577266 278577353
    0x403180314010c020d02070602031e04170c040b0a0f0e0717040b01150806090711070f0801051b030606030708071b060e070b030709271118060403 64
    0x1d108a480300e03400a40019404080b0b60070142c0d081c1c0b24000e5000c00d059a42e017040d0f105240040e401000455500560907241440343ea44509040e86071640d10b412030320540c04100940d0445410101840c50185803511408009a405035072a01d151850001c400c00305050744e210b1070b0900b02107140000c140a10034001384044004080402034641803e0034803900841d824065000610001c801c00080036008008091080900900003100d541e11304004a0305100780502c403400f1803151410105442100ca4900d1001d401038a00000e0149007a0212020f8400b01003400b1a0480003082440141c5c0c039400c04882e405581c0b401c18101541b0f80003000c0701c006541c84428481804003584110400420f40c1260408060000032a00310030349031504084c162101351091808118500c204001c8500020a0f04070703100d141e0203100000c0700001ca078880c103580c000d42c0e245908070b10006512a0416985a81c260043d90035a4400d0038642103a8171030184014450800002d0207000d0300c002a01da1006c5920203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278579766 1250 278578516 278578523
    0x309060b15130602010b091305010b0619120b0a060c05030418020418150501110c030102071109160e01050304060e0a0b09100b09010509070c060212070f080f04031803 73
    0xa42900c54003a000707030716004000c0030120b40810700300c002141d91050040400400d0024070803c0f030b42e103c1084120004254110891b401c0d5260b000350178035552400701030b002e201d00d031014801032440012001410518408003c2c21010710b00045401280c41f005507003000da8070385082c41100180b603800c115141d4096584209400c01203c1c049106420154003c1c000701c501803403101c42c000e24814518000d0741c960000c6191030043c01e0030708010940c450b00300d1044406d40e5800360740349103205402083c00d84c0d00c4a01700707640d5482c1c01c0d42d01d0150342c240290600e0740083e2154030451010403107a130042c040070716411040c0c10040e0200c00715061040c2d03a80034500c0030081c00101c4902810b50318181e081a2000c5800b00d4190007202d2805480c400c3e94001d1802c0040020100c22191703003800c00300008290040c040d001004403402e100800168240700130610701c045040c03100c08034500b2110003000c0500380300c21078007040082c50912003403425114032140c01c144d0500340b450722118a42c0524034021071551025 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278581016 1250 278579766 278579779
    0x5011a07140d050d06090917090d2114043501020703080108060a020705030d02071403030901051611060601031d070b03311103150408030907090b0f010309060b 70
    0x5a21482e0014000d0002800c4e0760800c0c055940e5071580402100e20102000c0e0544ca00400070030907002d030400040950900003404450b010045440e01c58101281c008500841940e0380030544034150070502c0c94805607100c24155203000d080c04c98260a550449c0845c3c505c1c004602c0103c08540e00d604683c03090080507030000c41d01c1f43c07050b080081542e40f081c8140c0c0c005e80a9640411000c90090084484c003607000320003140b82622500c51580254001c9134150b41e8102044140300c401c847c24001140540030850002c241814203942c2e20310820300c115408000e00c1001c1000403070506010a1940d80000c09080024901c918865140e03c00e514501403001d090080311808036080803000b000c0c600a0f048030071a0340440803590350300018864251003404010300c01d00024000101780e121f01c0384190304090b098442c0e40b0300c0c584080326040416a42110071000100c2040b103005410040c100c01000740d960709025004028001c40c2d039040b610282c0504045e11011008103111007030f041884500c002a058 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278582266 1250 278581016 278581033
    0xe0c270d061a040203160e0a1d01150e012709021c0b030c0303030f07120f0903020c0316051c080a0c1209030b0703240b03100905011a0714 61
    0x3820051603a81400369036140c8581c00b0702d0b030508042c401e82e84500403a4040c81000d400c100d4041c1c0782c04500440c000c5c6e12405094011601d01c0324002003022205590f0030741182541420b00c08900030103042c07920410440081010000c1d0381c3d11110440039200046410242070f9034411200311110501e4020354030240c0002070301c42c050a00314800341c21090404108103d205108000c240d190f80e103c11070103625078800c1c000301306405501209642c005a050034050620b04044034000107a078200d691007180c8544e15080c600505806115400c07003282c01f1400b50508604140d80e07003241507a940219030140d4480a9001840e208076812100c1264011000030b031540300c4580f00404216a01c00e0448401c4902800140340ca402a0681c8040d00d501990a00481e50b40f00c100304d005000e0600766040d600d24180c1c0035017882c1a500141d0018100e4100d40c1e41da646003d06d4200002c402c242d02c4000380c81e142c0700c01041001d03408001c02d2400312083d80c1c0700d903480c001801c0451070101c0340384011005005481e030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278583516 1250 278582266 278582273
    0x1209100c1119121803050f0703030306050f030714030c0d0506100b0a051c0b090f04030306050f030a0f050f0613120e010807030f240e010e0c270d 64
    0x1021148008403011211040320b0304800c8440102d00300c8006020710800c03001c0382c40c89801000d9039000302c80301840100e9510741d213403283e500c1c010300ea6400000c0d0f900f00300300620a255050240c03401a042c2a90340243c0440198081303030351a00c0900c2401260050501649101c2d03034240401450306000800688403070000d82402512007805440c0d80490301405040003411500f9002501c0c3c1c1444291500c90410215062204001e410f003040060115541e0044100079603414440600070001c2e28032100043c0740910b4081d0484040d600702c01e125100b010145038495034000b6a014240e9449007110786550b600340b40091601030340d02400c1e030142c01041e04026039508144510640ca80c058503004401c1400c04c002940d078400c4403000e00d4001510040082c2c101402a04540841101607000184d0f40c05521007603240002003034061511405000010414003241c1c40215000d0804003484c00d1080c1040c05440c80e00d4418250031030b10800f2001510030310070280e408130804552003d408520703c0c131010715 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278584766 1250 278583516 278583527
    0x1c050f0714010e0a030f1d0d03080702060603012009040e0106030302030703030b010c03080619030b011707080c090403110a0b0f060405131203110405040606030e0706030b01051209100c 81
    0x2581e280656190040c60031030803400064069449030580c81e0300d006282803110895a91310ba5003542d1092203940b03940e00199443c1c89000120b007602035910a022800c040c0c00c024181000902518401d0303040503640b002989401c40843e01700e40c0011b1030240e4450f2410041400790511072001c01c425440c205001085c190040000c00a8071310a0f58104500c0e1072407401541c1440303100d0b4001c1d0024600c2e4002407164101400e0030039002c400406050981d40e03a80d61500700220003600030603003041d04e4201c00c485449080185002402040001d8010310b803002c1c02080c9100c80040000d000c1082d103074604040b8807414400c18510641114148503d45040140c000c14101c09450b003a001c0e5190800003010401c1e9605009400360b40540186000d480550b401ca01500f454941e01c520044100030000350b0b60343e20300c0344400600d500d0b2404a40180f5030902c4c1820455070394816014581014020246a81d0100c00ca0f42d041001c0802c1640325140e014203540360805602c00300c0e40c004d02c0e0902c20654540c129 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278586016 1250 278584766 278584793
    0x302180a032916050304021915110319050906121003110303090f041e0e06010302040606110303040201050f040b16020a060c150b0f060a0815040504051c050f07 70
    0xc0d6800d89030000301071035030074500c41100c00d40d000028580c0742c0401181315100031500980000c101c22280110141c5007040c0961650003400d103850040000311501e500540300c000041101c601075070410300401201e20f08141400480300821100280a1104d030740c0b10020703164144241258001e4602c0c0040180440d140c2c240000d442c81d04500c2c0304010f161500004071000c00390050081c030f1103500018140720250043c00d241c0d50b00c8441314000980120300794072402c0c400c41c0b50703c8003c0c00294554014401180e0f100d030840d900700301e813001c0482405030001003281d820580c20b19040c3e80e01c02c14410b461032507000e5034001001c031351000030702034040c140840c2c01400c000340201c41030782c4959a1400305403a184d85c5200d00518143e015207a0320240d010310303441220340030000f03005212907540003400124568040800c01c80464625030502c035400e0700c0b0700e0481c812408261000c001e9820180c4074641c0c1e42c1c040c180d001480a01070003030700b1142c61040f01500c0508801c981400d495004c0c40c508400b012184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278587266 1250 278586016 278586053
    0x1203040312090e1501021c0302090612150d020306070804060204170309041a030d050309161d07030903050f0a02120409020c060a150b0a020309060d020408010b01020a030f0302180a03 80
    0x803040804c4030b02c0350030085558030790700580007030a0043c80c0c07540c001c41c001e20345580002415402d01c042c0320180c071000000c043c0034501e280c03218041c0c0740c03e500101032060001c0c0a00d0240900007541001610002941c0c1d801458a040280103640c440c6442804ae1086400070450030055003202511040c0c0000900b10440007220f0620588800940920041c000c4a00c0c681d41540251807506003580540c00075900101d80780b00752441106c6c40d40615a256901c0e034007640c06403407580d0399200381640c0d440c0002e4014400e482c0a100b00343c460340700108103000c0c0041c1d40d40300303801c0082d024081138000c0145404a07a4060a900e0b1641d940d1448800250050201c00d50103002c1c020001b601c2d400c044c0328071503d811802a41102203414a4a41d1840d500314482404c2540300401040d115a6502400b074120600c0e41b04025903600d00b80045582035031031b520b0580d41558084090200040e400c08101c140700e2040b4600143c40381319100019919440e010103480c0c000d00d200d0303004014005400c201e525201d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278588516 1250 278587266 278587289
    0x603030309020306130302060105060906090402070b0105011d0307061b0b09340306020f0f13090c020102070215030a15150201050106230a030225020a051e120304031209 74
    0x40750098000c917040d21800040060f0030000050005280280c0680a40300e400740c9028200201103010030100da0040c07105555007403c9a004120960740b01c80907007036091045905050303111420001c00c2d0303903030101d0190b40d050086000c0248102007054030071110b150303001035510348a07040c41d00c98a601ca04007060078111503000340070480003c005240030307a8580726038003031001551895910340303038004c0d0030210808041c90400c220b01d45003000913101800c00c0700d598000502d1402e140c202103000f10341c0c0d50001c03a020341e4010701041002d60350b50310913503420402e03c065040e42d0303540700c0324100000c0413000d000108040c41c0800110307c02c131303112040705c107640c040e50001c210301e90329508291b82c0c040d0070119170a480003217600079079040c1000501038405500ca5080250a105010300c030581c0c0540001800a00030b56100301c02c1c01913140000344075000300015140060b003031a6071000711190120a80b52103006410001161101d6081041150002c1d901320b6881d809480c2c01040c003c041c0b2100b440341500208 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278589766 1250 278588516 278588521
    0xb06030a03140903010e0d030221071b02040e010e01020d0507140703180e0403020a1b1202040b0a150908120a0f030f0e070605040503160f030b190603030309020306 72
    0x2400103150420640548680c0d0b00b000d80007440c0340c05035114010990b015500e0710600c0c0e00c0c4010070400d241a03145203480268032084200459066101e0f44c00300c0d000200718080920500e0b542201650044402e40c070072185042c811030002c94060109034040b00c400d580780c10510211314806601420f0145010f0b80705100c0c85d10307021800c4074221000c039840307024100d04001c02c0b000203000d4018048042141448100741a40c0da4045a0041c0401c50b016005070f0003d00e5030204001c07820b804000d0b4440002103605926080c9040012408a1036a00070301840c0d44042000290b502c24920780028540554103c1c500c140c684402404000c01d0b02c030302c104502c1040001808941aa0140c9000e80300e20303034444500d0307040b000d4120090601c030810040002d60301d4542d814030710010700c100c40180c001c688503503986070b103400c007410f01d040300c003240c11300390b1f60720f1180280300c08805480b0720411260071001222564a40340083d0350320801c1305d043d841040d840c0c076130000105a0181c1040f0401030003181982c1899 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278591016 1250 278589766 278589769
    0xc0c020307120b1303020c010507052107060c090806150109180e07060201050c030705071b03080c10020c03040e07021204030506040b010503011515020a0c0f08011d120706180c030b06 80
    0x1400501350040160700404803404c4554860000b402c0300c180035404896070a030f03a035600d0680012800e10740d00e010f980d000a41c0020b01205010718010301890713143c400c0c0c0551400d0700554450a018095200d0180c0d07030408905540e2007548000054a4810710911030503020b9840e040040c101320810417024000e2240009c0d030940103203c0c462140c008a441c071843c640e9641c00481d92680440d400b1500c4c10401800c440c421540c0d84100b00285118400c0036036603a040010145c030b0091501107100c501030040008922042c0080103a9044035601b44500b01c0d19120707104141c0c00c00c004100c050148079404600001030000024010b4000d9019a00b2000940d0701d500030326098603d09021182455041d5100300302001c1082c00c86070007030300e452041c0e030394142141e0703200caa201500c2e901501c1c1d200810602845950020b10644400602c0502078546e94944000d03259142c8d00f41281c00c011902c0d0120721031050140c603402c10a003816100904031441c039080d00c0e040b0300b2482503020540c0c1c000309000c0050150b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278592266 1250 278591016 278591041
    0x2040e0a091412070b0c070b070e190609150509030a080d0c03060b1209010b030f0c040507020303011a0325021f021c020705030c160e0603030304150c0c020307120b 72
    0xd0642d9061844c5003a6081d142d00000c944042c10a034a5104c08000e00340103e03192003040c3e030242c961681c580b40030f0340901040005003140c0d046c04420001454008101954004001c40102c40002d0020304e45c2214501c010395003800fa034414141c042c05080ca18104200c60380c0b00920180114000801072090b908030120202c41860144100200c0d0400000f542c0d100d1032003205034407100b1070001046448504011904102d5011020516940080b454480900d458050b007944900e00744000c60031076140c42c99071003001d80000c5000304031100000102d43d01c811346410744034545011941810005440d028029aa44a145040400040c0d501003c2d07602d92114021140e001006002c244001c00100c1d0703000b0002e50002d0400ca482d448100460300850341e083c04480703611000d003104045031a00e4107901d4241e40c280102682c2c030035082001000001402020045000c2454410008500f039400100340d6459441440196041c03040000c0010031215548480c50003074414200a40700e9140c0c6682c40e03c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278593516 1250 278592266 278592283
    0x8010602121c0905251d07080708070c0b04080304030201150501140c1f02040f080d0804060905030705060a0209040b0402090a030f0c030807050a0212150106110102040e0a0914 77
    0x148000c0005070a03045420baa004144421300450940b9103605031140c14880740011010894070b6004549000c208180d48080c011105490740c6540409510f401000100714000090111042c80482008600481d2240031340120595004000e440345003000e00780001d450f002210b040700158200090891a800c44503900c00071120180c407a20b145901c1c00c2c512205a4114000b480064441d502d003c064070300c81d40341491414000d070040107a0301e9080c20b040c2d048043e0940c01c40c02c0568400c4040d4a049940080085c1c0d201e038010030000740d5140c10385006030540c80b48100c09811445007209110002e01c46500801d68104119004c004032390740c0384180001d80c096203481e103a000000b0300041011800d5448511810740c07003141440c1d4000d80740e40d00c4d007800d90000381c0d0955865000c00c0b001c074218200180c03a0b1440030503503001011944c000081258036040140650010030400c100b4406502c48250151005071081000707158061400b030381e02030001c054150064034212512041200720f8900881c6100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278594766 1250 278593516 278593537
    0x120a0902090613020c070902040504060501020601061e030b1201060f080a1a0c091009050a090204081c0203190c020f090f31050627030a080a18030801060212 69
    0x3030342d03a031404101601c1c80e1011041c0c00c0507020845003040c0c090500108010303101030132005880d5410310045c0303c1240c11300d0308078605543c48400180a140e4100301b00c050041c845291450281c0c8032082c048014144a80c015a000314011501049490041d0042030648100c50f048404483e42d0f40c20640e0380da0180f44024110b14050f03241164006510b03900223074072500d208605450300b0021004221855040c0c40a0b10020346040e0060040380342c0310072154010032003140190700341030600301015105c0801e190f4488086148100c0041254001d00c2540c41451020101d1441c0609003000500f20f40810ba504900c64444141c500c0000e00d03240044900581020341204c1d820340c1c60a030a445641e014803150324031350005103820100604414a070960355807081d03002d0001400c10b48187d194031b41c0e8040c90858181420840c01c2506e40c80001502ca40f11300c18504001c1c1030300c1f040110b900400d0000440034000019100035000d068100204034100c5043d80d0032211641d6034107101c01c0c128001c2c0828803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278596016 1250 278594766 278594779
    0x60b07060509011812082d09011d010b0a0e040f020d03020c0d030f110a110118050a09091b03030c1101030e0607020c0a090209100c08070b0903120a0902 67
    0x8402042440d80220707030020180e40001a07081503a403400c40210a07841c01120210301004034101c0d50340d48810b80a40004841403135a0790200d51001c0380703829000ca4498100881c1090000031014282500f143d031a02c4940c841420703010b01c1040d001c501034496064114012960340d200014a010b148280c140b20300d0300b1100d101c4012000780e00300514601000c00580440c4210454040c0c1c07a5155448008901d02c07a4444128882c0300d010050040d841510f4829950780003440c1c0c2c000810f5180420122241003468040c0250350140702c08114054550002c6400241c0c42c034000c510340f10035600c8180720500640001c2d0101000f00c0081303210b200903000041c001070808084400040c011450740151000505011498142c40007545282ca11704451010069010361000710081c00c020104401034200a80d00b9468401070728049064213071203002c440c04009041040740184200d074002e460659a00c03001884150811982081e43d079001050a0b20000002c1070101d032521216205510065502500c03a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278597122 1106 278596016 278596027
    0x9150a0504090b010806030703060203070203162009040c0e06010302070b07031401080123090a0c0303030204030606050607051e0304051804050637060506030a050603060703060b 78
    0x826050200b8017090281c02d03100840c0380c100782c0340c02200c050f90b00c1e224813108903c0c5100d4600807085244a411485081112050002c642c020311081e288407940c55590412891b4141514020800c052444040005007500c1d00c507143d001d1014100107042c440307180c0300c1c1c0381000403c039802c50009a58030410790705400c07031603561030141c00085c008000e000c102c07400c402c0c40000d41300000400000414002101400c0030410350b0b2030554400e20704184156286009006904180406c44d0030604204021600341801001d0700c0b44150407100800c1490000070304190348842102200c4400d010400010885880d180900d0500300c1030b1119070003c80c038090400c5030411a002d0b0032081c00c02040702a8644440400303d95803180d200c420b10b22641904d0900b401c5004000c1913103c0d6400110200800100701c0c1140e010b54130950707040c1c8c03e8034226561100114119261401259510030303041c0b0031b = true := by decide +kernel

theorem cover : BRFrame.Cov 278417266 278597122 := by
  have h0 := BRFrame.cov_init 278417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278417266 ≤ n) (h2 : n < 278597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
