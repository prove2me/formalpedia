-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:40:19.843599+00:00
-- url     : https://prove2.me/submissions/bee3d1c9-d0ea-4537-9b99-942ca19ee5bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73561153 ≤ n < 73741009 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73562403 1250 73561153 73561177
    0x42408040b04020a170709060b030609070c0302010e070b040e0f091c030914010e12030c120a0b13060503120c0316020a120312180b010306020a050d05010e090d0f140702060f 76
    0x200909101107d01034501c0da9002120610043c02481080d650707103046140d0041c4640b901c039483d02e0b0380342012405440c1c032082c42c2186006200c80400c880481c080100705607412a10100c40948505100c05101c050480f001d00c1c064010341d000701c40041702c11400034181034851402143c40720306510740e804441c102c009500140c0e035450f40440441c10b0144a11030f07001c4248002c560440c58a24840c03101882001c81c900540d80c400b0380092000145a84000007030320024001008862407942060001c05240c086e45200b4400c10142d003980e58030260840300a61080d202850034212080d082002c40a451182268000000400030422201d4400d42000341402070b640c0f0450007078040c083c40119001e0241c2011541000204000031a14841c54241100d600c0440141c3c1c54500000c1104c942c041c0c6003035401e006040800000307110200f0304415009010b828283c0320140350000c8261224000c1c0d11400c8046401103025a412948150260903840d0020781401e103898811080d0112a510040c4820702d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73563653 1250 73562403 73562413
    0xf0f0f02060604150b040e0f100b0301090510081b04060506090a050d030c050a030e09070c080a08090106091d0d050304051209040b0d030f0e03070602100203040804080a0305042408040b04020a17 85
    0x2000c16003823a14030b604081c05455001c0c44506009a0500a00c81405100c4459489601044141ca030310003114008012000c02e035401000302011030b90b90703642c041c49064400da04104001c1150b03d4014101c90b800790008040007502840c08041c0305010110040580034051500407220201d001440080d80040c881d40e25450300380e051504100031361002500d19410040382440440008001c0e5049a500000c1810402019030780c4050703040c090b2500350803207078a4030708210300450098503040310f9040f1303000f41c0c0302500e001210468044509008c2202c02030001d5005801a4890402e030a001340b0300d400000d8000300d5150014004500303021240701c411400503c0d24500c0943c03440d8080e0050f04910800c4000d840000d1604c04025641c01d540303074000c1500b6038004080741c10402410301f190000c11040090324816016030801410382d401501c65a502604205074500c40100b509803005507080983e2100000c2d0b449940b22141ea540008004a80090500310080b49044407a401c40c9036031080d81000340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73564903 1250 73563653 73563661
    0x140a0b010609231012150b0a020114161103091503040303050f040b160c020d06060810110301030b070c020306090601050411030603070311130c0f0f0f02060604150b040e 74
    0x7904a00203a01c0c01512045100c00c02115540c1d6844849413440f007450081d0082d0044645c640040c00c511404003003140c0801000902442400d01802800540f50002c00a1003c100784680c806401200d01b22000c0c42e009141040071405103010541c2c2d000003508590400c5c2034180858441110100c1c00c18121401000b00b108050389030052030f900c492080700c5552142855540c040c0104c00103400269540e004448050721036108640340122181c00401150b004c21302070030040b005101e076004030005170054006036041011140142011884120042840c0d88c1ca10b40b114912240c0c06001c404c10018103c9c0404056542002558040c0030b030300c0042c1c07200303500d0f180801045039018028286020010303c10009a580d01085a00480390401020307151a90782c20000385010780c21040d9040e1721840c10b241000340c035611428001200340540c8402e034102c4541002a6002c40501101e0f000580c011000a1241e0516401412504040f1228600043d031120269400741c2c005400c01d18013101a08100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73566153 1250 73564903 73564919
    0x60504050901150804110121020702091608150d020303190906030b030c04050402032d120f0313020102070b0706022107090308030606040302091303090e060607140a0b010609 76
    0x11401802c04184070030010480c2400a042c0c3e0b032000708007900030300c200580c414070390b40954001d0038032003e2548c00160701104001444002e4004842c10313030051114034001340a440c4658030fa030451508903281c621083d0786079030200b1196031031001030039040000c1d48400c0005843c10000381c0400316604411180c4141c85001c002d04c0c060203988200b0400d03040440003611500c010441b8a050301080d00c010034250703903a0001c2803070002500d15504040180076081c0101910101406203124045010350710f00b141c040c0891030640c010110341842e940c00410115041070b59a64503003c800d4030600503169555511402e0030741c0c94116150079245150001141c2c2c14522650791120126200311107641d1190400c05401402d0f94202d000c014070561000010610326a0b90340259001158010b14402262921000c3c3c0302d40112a40c01c00c4011078500b03440403480910700081c2520070040942458240743c00b81d100c0710043d00ea02c20f1203403024041c80b40400007082075692103602034500c50b100c1c80d010a1405203c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73567403 1250 73566153 73566169
    0xf02010b010201020405180a2304050624040905120c03040503100c020c15090a0603021224060a0c060f050915010501020601270608060901150f0611100606050405 71
    0x596045910410050011f6640c00c110284241000c0700e640e10255120044c4800030144900c6010780c0c010f040103022030180081000d148a1803184c3d00b5544243c88290759011007001c50440d540008182c9820b043c05420180c3c0018135607800303031044407018500700c00d600d24113601040b8000d5168000040502241c00d0811041c4005032201c042049503003843d0a0080d121001e16481610600e04944c0054012094074255010110001c0255083c641d0f9990041e000b5404a20716240341c56800b800190850401c000d12400300c800342c4100405249550f080001942c0700714500c078180001c2400c8000481e0307480c8100c44682c1c245020024060504400c0986040003248014100284410061040e82d03400720303806046482d00d0050000c016040042c1d009001500d1021200a500d4110001410307480041c40342e004100d07440003000b103e040f2000c05008016640501c12419140c040100b10843c8078984840c40d0302401d60654088119200c00c0a080c4d500300d6000000044010400780010300e00360107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73568653 1250 73567403 73567421
    0x5060105040b06070c0306021b030a0507030e04051603050702031c05010e0108210901050f0703120b04020a0518010504030507080f011409061609050a1d07020303010506030c070c0f03030f0201 84
    0x3803c5810300d0050380e6130540c641d1480c040200055008910900102040c107aa008203040b104140c83c6c41c0d07441d0004c01030603600f10300000d500003040716082d1012410603115580c029800603614900604214000b5006040040c8c20a000c5100400050025407500000030000f080d090b900802e4a5142c20080b848401040e0810951500f108060452100d0074450548240d2031525806441ea11b0007001601d407800f40d440c0701d625a080c009402810164801c0032940c002036441e404200c03841800e000c0c0700890181d60940c2e004558100003c4541c0580340000c21005401450030740c0c40e00352240c0d0380c41d003040e41d198000300c820350140c0700707041190400303019101d1595083d0307001c550031f0f181821002d80e45e403402504002100d040444022401446940c0e0304004e0300300600110641caa540701c00e001c0380c050450354441c1c0c1c0682d581c04034035154400b1003101d04888000b40301605540ba0110168032542c0314a9085580711121540007900b00d100d01d084500a41c005c1c1c4800e941c031985024040d0a51382000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73569903 1250 73568653 73568659
    0x6060912010e070605120f04030203040504090b070207091b03240312030c050307080402060702010903060203090307050c0405070917010f0515031011030712020d0905030a14130e090c0d05060105040b 87
    0x2100c0154096002404039600c0b08941071f0001c01c5440c0d50400360f003948940c1d00860380007400c002c403a406100303400c180c0c0c44c0662480d900320344200e0303694070300f0104982951080740c160440100512001e00c1c804e401060800c0b5050201801c41000c0741145030a2001d039034021a0b004513110040524036425210345038845810f0309101d80b851400280050418800400c002d04c210008121071040d039200701e280314041e580c0907204650724280802c04554981020408450510440403000c6c69410701b4060f150080d0b0300d0745c584c4510340c2d081c80010040e5030f41000307050f200d07507607241400080100c02d405024003404952150642c101441c0e000e140c109500b00390f4030505141407100c00319a2264044c116540295189402c0004010000c0750070081e12a01080700501e50510798071806100000c401001c400110f138440c940320301021105001540144002c0d00e00b40075040c50200110071207044840e52090680069403032040d040c90000f10b40814055040e40c0316805840140700905080c0f0521034480421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73571153 1250 73569903 73569907
    0x601031208090c060c0102160b0108101406040c050d090c0509060d030c060c02070305060f01151704060b01050705060a06080f0c2116031505010608040f060506060912010e070605 78
    0x100c0002e550307031410045000c0c0204800980c94a80803020750603100c51341080080394aa2400c5030914481151080c01031010320300482c0c0c82c2519080c807900c50410401c511042c0b1403410f5480b0410403005254143e42042400f41c1003041000c444154481c10503190300c501c400440d820704010500405070b02c014106030007054600c01a1010070b07085941000c9269000390301054103200c09a04904280d02c0360300c000e10034440d50080c070065076980c402c01816107141c1c005415111180c1401203425552241c000e0420900280106001c00d44c2c0390402c5180c3e41701070602500d804202d40d21507140c6881201c0e03500046550340740501c140001403201e100021241001008000030000015484807491224000d5031141850407100e046800e02c00314080800300c106407105c1d66a00e00b02540581c0f404819007555a241030300101e016800b034800c06000d2600310340d000c5d0400a8542d110001844040d24031640000d0502413030314565540b00e000c0034420342d0b4a00100718610421119440c002c001e0704006c00f40f00003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73572403 1250 73571153 73571161
    0xf06030b040e030d050402010e0d031e020a030807050702030304181a030609030a0305090705041b0f02160504020a020c04020412050606030a02010507081305040207060203090f150a020a0912050601031208 89
    0x802e455850000e132074002600d07252840140d81d020045090160444c0d001c8005030107040e004061505400f20348441845404820103089890f000800c100801054445022401551081000e0860644090200da2a05480f8001194040000082c1c100019140d2458062100150107400640c0c18154010205414141a19622401a021003c04256aa4000803602c500c104644001460041c00c20010120000303070207030241e80c4165405000c2402e581f040503149100150104104041c130300200480d42c108410030002c2d5001e49141c408501c500c00c454a000c0d540e03031004000402400340807200701c1c03080c0e280c13907410058018a0789200750040324038440540d800400f00d400300c5e5032081c006540c07141421002e481c020902e4001c903411034400700741c03201042081d0380214040c000240884030000401c02000e0741e070f00030020f00101d41032407103008103c2e12030742e90b0013070a82602141072480115845402c414084a01000d090700c1035030040300100240180702100d001c0148941c540070f5100d00d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73573653 1250 73572403 73572431
    0xa0504150e030d0f02091c03090b09010e0630060a080c030a020d0f1509020a05093102130609180804030b1b16020103050c09090105090402010e0306010f06030b04 71
    0x1e405424610b07940c46008944c40c840032507048801c9100001e04041d02d44441d001c3c00101c4100c5070000301c0210f0984000071071900d0028054030000f120582d528802910a6007d0005030f0b00b0000f04892074a2030050100002002200c40062000003c80caa1034246450400c01c881100b642d8059000d6070080035441c00d02d910007241d450b49098042d900d54440500c0c070700c2c26040c200da0552000e85151004803424461818542000700d06a000719000c0c40c2070380d200c0d000c01c0600d00b002d5802c2500e907051951803800c070034040c0c2541001d00b0000f07012038074184820f4002c549440446a890305290745e80f40014481d0a40f80c6c0308411500b104546400b20303101c12603680261a210710301028004c03586042c00213071840d03c0c10940d0b0342ca85400c0c00c00307162910406545940e1305021100102c0c003081c10500001d00061b41c21080e21040a00100071030301c1c507440c0c40e05101c1c0c00c84024100345e0400a02d410011382d540c40c00c01105008090080800c0c403642c1c54040020111103203809168401c1c0e00301610320301460 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73574903 1250 73573653 73573657
    0x5010c0c022803141c020309040c030e100504020609150702120f0303010314070b0403050f060109050c040306020c03040b0c0a05010b010f050d0b01090f1502010f0501051503090a0602030a0504150e03 87
    0x1e07070000e2690309208221303403858035180d255424400309080d017864200c600c07980031000c3c1c021040159014810b034a8411030030f034151000d10324a04226401240c0702c000e0421160803030740e00180080c0050f898001500d0214044054603c1000b40701c0000295420071818804076081744070f900703c00980204841742c100345440b484107200141c4628201451448030110900000700109a0800180e079141e80c5ca142180e100e0048094600300c9000307550000400e00c40901416110708103450702d441c41e250456031080004d4100a0b18014544003d000214910600d100248101301b035060040c10f5a41091800a01f1b5605003048141003100b12101070300101e40007800d440700560a504085004251000103d440380041d03844446003412520000a91401210b141d040700e008641c000c3c407000f240505103c0544200307109080e040030402402010b1480300074003461f0841c510101ba03d608003c15140c000a80c4c0040d03070500c07503c03681c1e0420301080014080c0200800e541c200d0081c040c100200002070b0b224 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73576153 1250 73574903 73574909
    0x909030c0d050721210b010909020a02030408030706050105030d0302161203150b0315010e030307020405040c09020f090406150c060c020a0204020d0204050f1507081605010c0c0228 79
    0x8014081001410000511419072100550542c0210305419021005054404521100b174090a00340e04100c400c00040c0620081624103071904440750703241c260408000d4bc4944803000860009100102c1c10300001d100501401e4000e04002c1102d505203800c050070070303460f0340d007910074580304222407e1680104030701c52014070b810500c0700311703520030418080d03001e0003980300d5150b12810307022400b003154044d00011318003c64048031061401c0074a040155602c500320b4030441c0d4180d0007031103080014a81034008650140c820001c420803562384102c800240e0f00885d404580640340802c02032614205441a100104055813003070407104000c5201410b100035034000034103101c0d165400c0e14080e900800c6070b424401e5014108540c0d0b520a44601c0c40250080e0040700c0c41204500392400c0c0c6031909803810290802007151a5162811036030701c9042030350020f000d50000c0c15641d1500000b1610038460041c84503415160390507100c45600c10040080c0c0400c17880422071b101034000c00800c6491810a00507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73577403 1250 73576153 73576157
    0x6010617040606051008091606020a29070201020409110405090a0e01020c12070606060c0302030318070f03081c0510030222061e090911010819020d02090909030c0d 72
    0xa58480341021000f40c0301c16004a60000f03d0010910f03d0f031980151003511841d80582511801000320042c18074501c41c5129081c0160b000380c0c2542c000c5142d051140c1c58058000040c40c0049440c01280f404aa07000c03036004001d80d502040401295100f400307007200a00300c61440f585802c1c205000903820040c0035010700413030f5946400445003500b0950484004240c600b00321050050070000642c185c3d40040c44c200d03091070400f000000c81a00516564a00c1d95040d00a141145d5910f0440745084004408881280c4120031000a071140300e0b01c600320155004100465890f11a0b00b5410558104034030100032291070a02004903070040501c0460942e58111000c9100090720100050810425005d1841c12031410100290806502d40312800407900d04c02c440f0b01d410b54a9022504541750303908040c0098076041180040c075849071a85030750150600d04250040d2100c4844071040380c01c0040d005080740d9000401d000c451900c240c00c550300020900003145040311010b01c0c691100c1407400d00d001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73578653 1250 73577403 73577447
    0x18050a0b1c030908070b07060e07060c0b0907030c1701050615091905060f13060c15111207020d120605060f130e091b18010506160506010b030a0e060106 67
    0x41014803544512004200e00c02c105d982d00b0307884100c0100c0591142100300c0700c981c5003842100c00b5440102e2002c0440c0c005407110544c0c40516103582c2e00b0400c3c000c0564889010347d84001c00068002d0b65210054420410020140510040c240d0708541c4003402d800d21030355119414100d01381480f802c03501203041c1502c8d15007840c00400240818a8410307007010b80d2080300820700605218203080640910401c3c0700c0052640d036660300d41a1090b019400d8090480001c1e1a0400040d4030250045010b026450348450b283c0001c034a40c000412400f0741c1c3c4500180c000c555205101da074071203580e00300403101c0a03040004030701e020b000803064442c10031480852140441c3c0e0325500640400a00020300c1c0060007484c840c0b514003e43d130344035001062055103082003050b00300c0744c0d0b003006c401049195180103000c0c0400c0c1d0074082002300a410004d4680c048541d01c00341500055004c2c0030550080c103080d00e4407916401c0440c042c50540d010045c52294a910800c01000940da1103100200498042d1024070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73579903 1250 73578653 73578709
    0x40f030f14071101032d150801020a02070f0f0b031b0c0d080403030f0b0f090a0b1806090c0309030d02090117010311040b0a06020c060d09060618050a0b 67
    0x10780c0705440140c464880440102c0c2031028400107101c5480c000c002680d013000840c0080b00c1c2d407401491140701c092150702e07494030150264604c6130b01c10600f02c03065040c04001e040e0f9862480c0d09980c4401d06610040c0c0010b01c5c04c0154903ea64009009407100305040414907044c4000348c8240c0c00020041810000c01c3c903065110500103d04a40780c091001040c3c5140002040029141c1030080e10f080300061300d0001c06800e0000f003445103c0f00f0000080c04d020fa0032400030700300704610304007500020308513640380c4031034609503a02e42140c0e8030108003c88000a41c9403120411000c1040146040c41c40d080400400400e440c0200440343c1d82041820016160b141d603000480305034400301d403d200300e120600008400d00440d0032121030800d108a50511020311182c1c1440181003403071203044c01585c014540c0113103506e85032000e04081d40450500241094440c1c0740c0d20165202c6a000d6401d94411210501017034990b40226680810742c51800c4c04891502c2d0081280c081d20042403403034507040c6100d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73581153 1250 73579903 73579907
    0x30f0304060914160f031e11120a0b0906040209010e07050705030a030605030c0d0503030705070f02030105010605040e130210120f0e07090b01020105010b07110307030b0f0f060405040f030f 83
    0x1800105400c00e48035a000d5449525160744e03030042450540030480d4881c0001514080c0b1414202a40d5105044100d0f0018441c200b00440e089031300100c030480003400000d4559112407000d840c03500d0400008000d06407160604840551002d000c40e202034210608200141c1c680d03445550450b19200740f10001591200c10031039003802015002403071404001000c0c40400c1d40340c1c01c1441540c5c1c2c12400c1e10524400f401c20404184071850703005040d500203000048149005201510129024294144411425900103401c4400c240c110602080c004203042c040980d114000f940c1c050303032a158a40301d0b00003e0300021042c3c5144003040c4100111000000881ca04a42007601d054510003c1071114003c8860384a44504d603500548004500d408a0740301a0342c030502495040b5102e44044600d0b0950030b841e291100028601c1c0981c0510580c440000040c030210312840c171603640e146049109060400c08040701007009040c0c0b41c8101e05250503c00410340d001411b07030740700e5410f0030705a500c04284541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73582403 1250 73581153 73581161
    0x30c0318230a020a0b0901021e06010f120b04030e120f0105040501061e0504050606090301090309051003061805040c051302030106030501050a150e011b03020a020a08120a0e0112060b09030d03050108030f030406 92
    0x10700025812509c44800c00400103441c9050b10007180544c0c0403181c80b11030100d5451440e24002e01182015400314003c00e0180750344450b18000640b840070703803c40c102c0c9014500b02c1c1b0301008800380ea5591042101b402000c0c030070a0041c00c41c1c01d98002021340c0ca501c0481c0c48151900485101701d0f520700c080742907076803a1411141807c801600900c04035403d4180541088454400c03103016041d4802c0211040740b00780314240a0740c0101d261804120000e142d071030300901c40100220303400342c070380300c8040f600303641e100d01c400f1640560303040240e40ca45c10401c0080c00c0e24410b07030245003d000c24200c02c1c086c078800210000c0c54a0101c0c6420140c500d60a030040b9045032035030400700303903240701c0882500526601150103143c80b4020342d25144455601d2144540d81c0c02080f80043d0382120074891030100605c2a40511f02041052504995100c40308244004480340c6074007504000100052480d4142018414449a01c501e810b04104640c504090592244110301d01e00d0301e18140000001d08001c903d0380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73583653 1250 73582403 73582423
    0x20109020109171513030206060306060d24050c04060201060b090a060302070c0e1806060603010e0f18030307080919030e061b0d081e040309030201030c0318230a020a0b090102 77
    0xc0080064101001e55500071701101e802a0014003072540015604d042c00900340340110005004101d0600d0f1a8448025601102c91801901c0000356203541e402c0070607009850086400c03107202642c07503250902c06130840b0103d502010116105100070b0341e042d540c3c003140703508075003031410007590360700301d62500d41d0400880e500304032580003126091240c4100b240001d03455500e4400c007283c24507220402004201d002c24030410b03180b40740100c00210030002081c00391380c212544c80320754070b220407a1500ca82d04582080b941c100015595408120258504000d001006012030700502d4891405480051134444001d00d00ca015400005480c05a032844002005c6104050401e5643c2d000300c10074000c24490003a02c241c0384903c9040c1d80880011283c071707000c5000d294075440d5207041901d5036006401415510080d00181540d600803e04041c10300341c0d1880855100780603008200000d100d0590100c50700c0480680c859202010800041c1c13135240700303c401d0b9040b28814684030754071640102c0ca010407101c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73584903 1250 73583653 73583683
    0x20307150c1203060f091401060302070302191208130c140f0307090207030e090705070209070302070b090c0109060f0207050d0c050a140301051b1207030b0a030b040b0702010902010917 81
    0x9200b12075420f601da4003104c1691311036001998002d40e100c2d01c40046d10482034950a400780303154010080e02c0d019500030162203110b801a120301032310b4807a003a4444c19100501b510303c00180c1c90758400d0241e1020b12140c0c000c8000740c40d40c40d00c042c10b4641d1801d074641c50042480f041d91070b21820707400340e0791b1030f40180c1d020364000e0403500e4482d100c82d60301c001b94224080840125420324108142842c020b2010380c451220b99590f41d00b0210603800304008101d01800c0030003455800c003e400003280c00008194400e82c40340f4000d01094111900041508005500c081b04201e40d80c0601c46e030023640400d041003200c10485203040503080606048007800100d0344070541c01100e00c1030000d1f4000407103000074000c0300210002c02036941c3c1d101c0c0c041b01404461b031081c02d42c03030002c1005141100c024a1244c0e002144e5160029142d1000804100104910780059400e04411010881000020441c241d8813103191710080c055954a0b9001812070000f9000755891a907012648550039036042200c0f2041c08040c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73586153 1250 73584903 73584923
    0x30c04180204330504060506070b0c0306040f05070302070302101a0d0804080304230109031104090f05010507030207050f070e0403081513020901020d020a03050f090a08030d06050306010f03020307150c 88
    0x100d503100ca5540e50324840c3c24000d6082180007d02d514012040ea4401d81d04078008d98955912494405c0c40c41d800109419886a9680b068442e4050144034162194006131401a0b44211504000e407900b006085000807142c02c00400040c1803400b0702c5a010402400d9903445d046403103503c1c080380e4a00481c0c100741000d11002c5000100d0481c01c1140c0001d140010ba80c810444a40300011503422165000107004403d0041c0e0007a01404c1c6580007114450042942d1b40388404c1c90740c0c805007500c1064816400080c0c001c1144810b2290500c40012301c9101000200381540c9000390701600d464004102400b40600c03280050820114080c03403a10b0f443c402000c1403a04100320440b02e009411040e84280188641c6e044c01403042d0000070b046008a405846440c00e24904403c442620b5000c2120550800f00000000514900810180480c460460404a503a80c01d140a151801c0ca05910001407003491000070409a1804240c44090b51090308011000801924040c1c401400380d440c010001801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73587403 1250 73586153 73586231
    0x15150921161d010b03011203021c02031c020301030f0611040e070f031103090705060d02070807060b090606120a020a0306080303040c0e010602010c02120c1f02040302030c04180204 79
    0x1400c603803003003902d1101c01c0d268a99520040001c440c0d542c24098004452410001404405103001e10203a450388a0310480d560300c040910440541c500c00b015000240e880441c0d01c084082c15074a00c3c0080b02082e00c0304600b10761654071131180007803841030b01a01c1c0c9030b541d049128000e00d00300b04441c003400400042e1072450030f003160001c1001d2400c0c000040002e280005400c09180010101c0e4010140800240701a50403e410060716500000c400e140d00e82e42000130000007080c94001d4540240608000030384598508240400c1d0180200340c80d03c210820030000c004142800304403501b103517402d100162544000e150503002880c0e107030400c403c18440801007104021454450348292200500b003e401640d0b01c2406a0a0310b0b07904082001503000b194041184900800c050900580400216120401c4880741089074800f03c2081c20001ca400040510542c01e00300050303e642242500c0400240a100141e0030200041490003445543c6442c01259142040c00c1039040e00f00c09c9042d5102c84085e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73588653 1250 73587403 73587433
    0x30f030504030b070309110906121506031902061602030c06030109050603010c0206010f03080304170a020a050c0105030c070b0a0912020a060e030310150306030807030815150921 78
    0x706101c112054400c00c00015140f920074007032200c1a6501030401031a4080b440b0401061980090165821103040d68982444400400500d0f01c0742c0241c4c0e03014080c5041400500d803c0c10081398034001c400703401c5500c060041c1c40b0390080302c3d00400801e184604184051000074246142c4d00900c50b80b003680400085418121903100902903030048000704681d1100d4201640c445100344503107a40300603c81d008001081c40c40008543c01445240c14100303240c0d00600b65911608911010f0703006900034040c00040003000c001c011001d0320301342007060842ca41346024031091700c1031450003000341c1c000710b000c00c0d6401d910741c005400455115400d20000b007940c000003035032882c03848006d5920504040014103241d10210859000d45940a2559940c81c1001c90041c9071807460324690741007507a0f41030300001080220010304000d40c46541c404189050203c017401c0482d041401e0a845034041d28032900c00c40860301c00f01c48941409031010080e068003080048001565503160305c0c440d000c1c0348c81c1e03d00c4600d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73589903 1250 73588653 73588657
    0x3010c0807080a0b030d120b041418030c0d0c02030f0a03080603010b09060618030a050307080a080906070e0405060a0e0108010b01140304080d05060f0414010e1509041b030f0305 78
    0x1000302e0307070781c0c21142d600c07203e84034103680c6080440b0381c041c0c01403444400c0040c410f240070004074000c00c1020680161b2800801c00f141e02c60014902e100c55a00180010b1070f00c25420b040c10716200d90001c500301081038941301c1c0c4540c0800c1500d420300001102e090704544060245621207802c03001070f58440080d505010740b80320b004891040c42540707000100209454034898880c000d880242003181003013264038180b488903a030304034900c0c1d05109850303100001610800c0103256051185d000203840b65040c0034082c2c84004041c00d0000184c000340100b209447c3c9c003403d940c11100e802c031404181034440c400400d00003038142d0000010b152444001042c019030541000c1d20060302030341c4510f00200d0340c1111600034042a100180907040400c000d8076055540e0f040f442d00808001c1480c034000207824005812119080040e8040c0c10008004100d0800300380030713803544000641040c0c240f042000c0d0001d2120768000b88010400c60030f11041d0340d61010f903829100c3c09103910a540c00d003e407a40c1c0c20054196 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73591153 1250 73589903 73589911
    0xd03091d010807050109060c060e0106030c080d0f0e130f11040b04080c0402042718030806010e0906060d110403120203071515170f0d0309031e02060105010f03020903010c08 76
    0x2603c164000060030354455969003040750b001d942ca10b407840800b0b50350b050107050020806c0c110f564031041c0c0800861592010b00d0300a0192500400d0303199403103c0081e209440c440b40400600802d4807104540703454403548040b140c03080c1240020b58000c040c3c486802480c030444a12119034000ca0045408440c4000901c10f44004004882c801c1c88444100000d82c499400381a0601010500e02640380559459030303015101c4207a404200030410b880c552090f0803118000b0340001e0800e1050105558024a000300d1074801500c65a13524581080482c01d148961919080066502c402c001110320f501030036100650343c804050281d0a844101c0203580f5041050269542080c408540032480034521544011461001d040c0074424513100140040010311000714000c0d004503010106001001c1c0840070224009850000f4030300c400e428000e10744a103807012403020440c03184441d1100c0f90001510360443d0401d28040b5201713032260300100c02a01844212540540c03d100d4840142034220300d003c0e00c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73592403 1250 73591153 73591169
    0x40203100e03040f1406071b031b0519060e010c0c050a0609030b0106031b030e10050103121103030c090d03020703081207260109050703110f04140306010609050d03091d01 75
    0x148544400317000150601d1041e5a60340b0100420110000030111030b41e000c640c1041c00908030050360b4035280c2c850480140c005034002c1884024043c0414a0012003005800c1000506880d00509061010f0185c0b181c2684283c14060a01d04400401c20003001d02c074007070040a003250140c40e945400107003010945000458411451600224000f440382c030426010b0101400c0105000008141c00c1d801000c10b1580b504181c00f074900460120702c418024140214071819110140c800e40c04070040484400d402d0640381a0420000d118007602500c0c01da50b0f5415049800c0c000e11107581c5020f901d010031a0344001d000140100360041c7c02610300850903c5010b01d41c44020812500b00300045e0154420040c64072861a40c0e07006004140b40307607021551042007400c0c0010f82c204c4540e2100007603049104180d44046000509105000c1d5950883d0340c5c2d45c0f41035004000365414011b020f00703c5926801098000c000e503031090001c0c94400c18901e0010007440148407000f881500020715119001d014440c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73593653 1250 73592403 73592429
    0x1514030606030d020c0603070915120b041a060d0216120801050111060f0c13180f0213060305040f060609050402090603070f0e090c030601080d03150b030f040203100e0304 75
    0x603141008101c84120703d940d6409070403d050040100101500003410b0030080086000000c1551000b00304140b8203400e0325120905104940b044035070075074a14a01c103501035402c05e221f00180d0000f20a0079000824100c1d10ba5442d109170320000402809008840d1100240c06204075090140704000c101900346c20303903106d490f0b0f81c1e01c0d00e00544140690b96407205243c0d22800000300d0100309040f00700e4024444450b0b191402c094611a55007405842d00140c03014001e01076242084100c82c490801c0c2081d42d03010030b41c24a1050644040c0b43c0c2c0540c0b00d802c043c50b855a00103410844403c1d0000c00381c2e0361084c000c01c543c0c1d40307030f42c11180204012102280558900c4004c0392485c9400500d01c0101e50201d514412880d061514401c401d0034050b2000140d03100b02098503d16960900000e4046c16a044c002d01104140f900002c050310070040022030350315103070b15081c4198455042225804000b01c0d00030321850300c5600c04640f80c00c2c0703c500c000c080c180c606880c01ca8150b102000402c115640c60000344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73594903 1250 73593653 73593661
    0x7080c0303100305010606140d0507090f0b0a08010504090f0305070501140c1b06040203100e030c01050a0c080a0605010c0210050903153c040311030a02010b1509031203090115140306 80
    0xa0b40c58010246030508c0c00310280100381404010b1340045a000d4882c1c5420030b202c60303440b1001402c440080d0010320300c20b5004511a01c495a020f0000c1d4014030084800f409901e809032500f00003000300c29005020008002003c2040c0301094200380c081549600600c2102d140070888000560042000d42c403100d004440134041500000429600540e002400707040c001d980c000c841401820101030450303081c08103000240351048203100d541e1251001480c0402c0e980b840c200d000b4146c1c80b00a014140a5217071040600072a64030480c0c1710012a41a81d07400c80c10648620152568090706001590501c00c20100d0310f00d030216851002e00a82d10800102d0850b08000f41002c01840c10301510448890780309540345800002c1c04840e60003034001d00b000d40032400070301d00250456200c0c0c068100540e445402500e1182007407500014040100750031941001781d00e45c0002d4969a0b50081e00c88075100200109401e01401e43c00004016807154440c051103560354000041004e2640b0400e1090040c0c0c0005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73596153 1250 73594903 73594907
    0x822080106140402032e03020d06020309010c0507082d07030c0b10030f0809040b0604081c050304030203030a09021c030305190c0f1b0b070c02090c0901021207080c0303100305010606 80
    0x2032402403100100b1b4619500380c030459004a0640c03440785a41a0080c13840000c0962110b1402150050007100c0150380d034901181207500b034801403401d01e4200003040101c240815441c0c1d0546000729034101c041c4581081100810712100040741c003010110200084410805411142d100c10907441000c00545130b94a0015006c804c454505c0007501e00e4070b0718620034001401d001c00a101403580100300042030f168a102241464106800452080d0300911152148510740900035000511514040f407035480c00d0b0b90000e40f2030101a02120407142c036041c0340400c65480030102264030b10711050040c018034160074020090081998a10f114407494031050481400c4c0d402030490001c6c2c141c0760390340d00b0205050200c03400002c0604c96009401440c59041c001356007804003501402056941c23811027034160040000704c51028001039030040003000421749990300490b1020890240e480129107641a5040106440c4208d100c0b500c0940000010820307030201100081c1c0549020b903008011040d11a001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73597403 1250 73596153 73596157
    0x50a0306030c08011a0f150702060708030420060306010903062003151306080c100e090103120e01020c0a0b1b030c0105041401050402060403020f041b03020306130501120822080106140402 82
    0x258105007c400350040c1c488000c40104404c61010700003628116142d00c40d4000d540003030f2002c41d455040b80101c10901c1c11031300503c0104013012200c451035401e0040c00604840f2540c0b0005002c02c1e12400204100c0c0d04c2d0f11115180b91000710045592864100182040c000550005a210700e584104c0720002198601c00c18042c0d07000c900050140a601e00100003039001c5d0460850200700b04440c3c441c44130340f81c07043c5083c000d510944076410b0300d01182c10041c00d1a0101501c1c40d045500410350389040b030b9910007262080b24410301a00d9070710804603d40e10a124001c184082d002d102c00900b00615410541c40103101d1801116101c07805441c000e401800d840042c0ca01075440038041c003060003d40f4192107102d030b1018008000013120780e62200c003005072819148800b0301280c1d003c02040180c1c1072949000d12400e40b46c41003000150f0500003d50a42c2030001c41c0070f044400c000c9100383c004100100984402c035007445089030403036502c02025010b450035008000280c2e00ca424400504d00381802 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73598653 1250 73597403 73597429
    0xc030b03280b100305010c0909060b120c0c0a06060311010206010b0a020c060d0605040e010507110316081305031618050c03040f0201020c06120402040612020907050a0306030c08011a 80
    0x41c0720114103620742151030070020b003d20780d0a440840001000810912034000c001c80c1948034001011300c0c2030755410445440350312024041c1410444400c6d245801e402490748180f0110b40ea984800380300300c80074075141e226040208201e251050100600c0212035490700c000e4001d90840362079a8840f9001034107405965100d0000d6031100c0c2c1d100405290003030182c40429044640003032401c2c0e80300c00160a4130741b006460380d00c59540c0c1c014001000d03400710280400301e041000079843d0580c4010010850380c01074201502280c80441c41d0249500d204040360000e00009084404c82d15a2080100e13a910441c402d10880c4007420600324010300c0d81d401044d1140020524031410b43d55103840b80300c119569050104d0440c061114001d64954480c0041c0c0300301d0782c85040400091178075205000c03c840700c5030030102182c00030130f07011401662788481c21503001e8410b14009032640d24851098014100a40004000c0300d24042c002c90240c60560041e500020041e034840d000b01d4520081c0520800b82070703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73599903 1250 73598653 73598713
    0x1e03070804060807020c0a031110180501030504080906030702070e1f030308060409120c0201020705040b09010b0d090501050a020d0b010e01140703091e08060114061b100c030b03 78
    0x8407040001500031a40d041e4054002e0054070161011100095400c10341c0340c2080780c0301d6041101c0240c00d420603170700d80b451000e031504094682a051200107047e00c00a4800c84d4100364035003001408114044d81600c0c00d4a80c0500419182c2c2400c4002a444c1e28250040c0d9400e09504000109000c000c50340d40740094840720740c00e5650500b1524203c44d0f030b0382d00401c0190880d40b01c0340c036200010b1b0104950a03042910782d5407079036100c00b04e2000a04114060b4450b611440c1804000140c43da00c84ea4058111500392006680c0d61005000c0c40c00588607400e006880365103400300300094001541c00030464401d8400081040701c00400041d140408211442c0340000c4003e040320b01c4030040c43c802000c14030301a08140c0b040340d80d11000742c5000000700c00020315500b0034003420800303048200400ca01603e110408110300980e080e01041d5503018005081c4624045640b001e80c41c40700138071074000108001b2406104080507050050090000340c06154002e10400b01c0e4829400e69601c02e605c00d4100b46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73601153 1250 73599903 73599907
    0x905060a030b03010b0a03051b040608060703200a020109020109080d170705070f0f0b0c1608070215031e060f092e03050a06050a0606050a1206050406081e030708 71
    0x25010880040019404050f003665072102210201d40e10308042400562080d00101100080080e0210030700c0015010107009d0741c01c1c45014882d211010600503445203a03498001480c00744c1310920400b451a403540101004c40010300265103e9040d00300081c5c441c001e8032107a540700e94840034150f684500c1a001c50001e0001c52600c4c0c565030180032515081041451300750f0502500b40c07950550302010b941b003207070240f015400080c1046810410725030301803011003207039040401d02c40038003451101170180202100d0001690b2002c540d50344111000120030070701e40139107034580b4041d1008184c3c48080341c40c4c2d044005c00c0000700c0c5444d0440c0340c1078540c2c1011b44002e5141d2952845d5a045110086103000201c1070740415002500d200620800111f0240000382003401c02c03400d00504503000a000303544003504000061006035040350032100c0b1100586890105001d40e81807100041415400c829401810080d00103981038000610302d400b14074a482003c00c10500030300007a41ea119801c0010541d00007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73602403 1250 73601153 73601167
    0x90c030f020a031a160c022d0301020a03090b0a050702070b13090203010902071403182205041209080c1c0614010b040317040501080105103b03060f160507061a01020d090506 76
    0x9203862011048d41d9108040102d0384500003400da800843e5032070002a654500d5400b80600e0158075604941c10748402c00440c108460b0080d140c03030080c007400c420b821000500b007412611607141c40000700340301c0c0d10441d00c03540c50b05140000f0350700410041d42d50503030042d0500452a800b0003144c0000e56000c4c2c8071500801440144842007190703032400048034910085240b2809001d01900307129512917000c1e0f422042d05040060621000f580104055500c0b0b84001c0c10f498803807142c00082045d03a1010740302e1402d01c6203484406400c06865103501110150000566000c0f2074000d401a03034030031140c1d110f01d02c4101440c030649024501c913050004481d08010889030038014803a60b282c45440c0f0342041c03000094581c40b200006e0f00160380250407400c04a0f10801d400022040f401604218040c00c0350741007014802202d0640a0480b000d01020343c46004d0f08503001340b08841203141d1080d014040c40c0c0054200e09a80b084460303200e07000d40504040400001c4c41201d0f100107660004200750305141d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73603653 1250 73602403 73602439
    0xe03070b090d0203100213030b09030304110405090c180105030d0201050f01030809030a08030c12010501030c0f110a0b100e07110a080d0b19050310090c030f020a031a160c02 76
    0x203502c002030381c15001e0149509200f00c114001850030700700030a0110800c6203145060350f03140200510b000c0f510381080c410701000514070010741001030f5044030082050f0701c1d0842c113141402100c40c0104e03072241c01500d800c050f034001701c40703814104c810403010b0351780400035140140d0036103008680701d6000c45c054038014400600c0c41380c050300c0f650360060110341210840d0b907034980a6600540d4005c84100c000301c0c44006c0c80001460860242c134003860b00b806007800748200500000d609064820600c8105130070340c80044400c12440880c517400c1700c483e00c2c20342000c082244042d111070092070b4410102000141405020714200102c500c81c030002040d03c140307241c44845558000500b07801c00c1c03549420641c000d6694605c060b42c1c4500ea0701103214070180c43c0c1404c151906081542050486d4140032040740400d00c902c0000e804c036508580c60020072550b510006522589175080100b641c0b650142c5055080ea14a0745184582070420310303200110f036500310603202030241c54402580420908248840d8071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73604903 1250 73603653 73603669
    0x903110c03190f0b0a051504110304020918030a050c0708011119090b0a0f030c080717040f02100801030309050a0f06180b040b0d06050901140907020a0501020a0f0e03070b09 76
    0x40c000c10f00481c00c28819500c940a5400c160790301c4504585a17001d120848140d0035802c4118002100d003040b41881c9202d0504185c0401407003e40310350344410000f50780c82c00c0500120041342c004000d03642c0d6151a420041c105400030b0840107403612400d900410394000512071900722451129040d402c00c00040909200702c001c070350300c140400030203036000643c080109015201400240d213880c6c00380034480700002c00701e624040380760302081181024402c0c103580008590300c00b0000c210244c210b40d904c40c206145410210080250001400000c09950342c0d0701c1203006045e00e200795110307010959900304011800d182c5000350030b0400c901d604200300707160044401001d9400350380c801c0004541c2d101d5407a40d198120f035002031020714001498401e1401203101d504003800d011076945d02c055050100c001d003001c0e0061a0503024401400c0070405d8140200030504180e54804d0007075560b02038191000305409911451000403460344002a00325150214100041e05c0301006641d0810f0110000c0064507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73606153 1250 73604903 73604953
    0x90607031107060905090f060a0b070204060b07060b09090a05030306210f01060611030c030a0c0f170a1b0f03081503100501060e0111060403031a030f010903110c03 72
    0x7210012200035078034101800304800400240d04e90030004c2c1e290006000070320400810756280d15850b881008036655810f0f110409030b88549414645402e22840072600031712890f041340b030300700d0000305140003003050300d810240c0780590075180c1c0e000680350258915600c01468500070950740003400001d1483c2004542d400d10221070407001c004aa0b0240d01c081e04088500c003d010703a0380d4487c0407e004081d001240444018110402140307084805401907813240940e144035010882150301d100180042c1100001c08950481d0000641031781c080324a0245600980220003c80c1d81048020406aa40b1a1084000b03800c103400c003a003800950340449581b14018a45542201c0348030a07070f100c58500300004c0800804c1c8540016040d410410048c00c0700c40001d520720704000c01c02d40b002002c600041050390300300b6070506000c12038162111101c3c05d4110103c142c035815105590100315250015008072120394080c0c0c60b0300340c2c54000203044680369100c44184580640c41600b241082002e0f00d100603250b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73607403 1250 73606153 73606157
    0x6080c030a1409010b0a140105030a020711030f03040603050a020403080d0903091d0f0606040315110702040905010c0f0302090a05150d02071b05010819021317030d060b03010b09060703 81
    0x4901d100145140301c0e18403e48000724030b81e550356413081190412030700c0c000107801c400111600c1d9260010000380390340700003403201d42d0054011594004100c0001101c0400700001000d5135070407071441c5e19550362504540b0130100002c0c2420b01162440f18207108039070569401008881c9010180442200a040390450271020010b003020005481140c3e0703c20b65120501c411602c0ba000c2c185400c0c0d841082d42c01a1102c0e00ca004200000c000044c81c040900e44004156900030a070440f030305004111368002da401c003a41142c144071040e800c000040d40070018603034060300d4a2010f03451001c400c030700324003030f0b80c0851380c014800c600103000070b10b07007480c14841100744082001d2410210b001c07c0c00503078004100480d800200c000300441c20400d247d90350b6000e01000c0c03814000740d1030803444190a0001c104010180d40340d0010b1008440b520103034112025061004111848080140b03480e0380c2ea51040310781000d090320308171000c104100c1403c04c8a040380e810640c081d0900c84120208851503202e0780c41101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73608653 1250 73607403 73607411
    0x70504030206070c0e10090e06150d060608060f040302010c021209010c0f0606090b10050f03040f1109040b0a0c020f1506060d09030e090a0207170306031518010b0a06080c030a 77
    0x40e882c1c000074465114880c006d141001951510982c0021345030712003200d80d4203030041810080481c4103c51240c0320320000f22800c00e0040000d0600f140107000c0ca8119008901501c020080302005094105024a2103079008000c09040500c0c100c0c1c8804150b0b03481688427908000c4460395622915451141c1d600a14005407100820340d80e10045aaa030750105545a8443c511001186012140d07001c255490f81081c0b8500514980044903d10000303200800480500c008842400a4030041c5094840058403510701410a400c2c042030003e0100e95a808280c10524a0541d05201103804072619980740c00514100c2030854038100c042c48010500c540061017070100c0250035403076000302c0414500a482d05294003916509211000348007d00104a1070300401092001511810050b0016441070b0251503c0b0386500b0000707420461920200c00e0130810b004144180c0004003661022401c2174070008004001c60b1000380251141c03513203d001d0100c1e00c031500150b074124040000715800004068005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73609903 1250 73608653 73608659
    0x402150d11030a0e120403030c0b07120905060117070515090f13050906130803040210030e0102121006030c050d0509031204051f020c0307021507020405040b070305010e070504030206070c 82
    0x19810855105007655251640000e141c801840170800c001c031040394403441d082c20f6890260940080390001803507a00001c0015600350f124100c0021000441d450038031001246080881e03940320280034106200c8903e04414100c0440080c1d03100407944094076615455115044c48042c0340c00c0082c400780c10114502e03d1965070307a1012460020109c102c0400a142c0c240240359030315201c00200786000e100c0f07101d4600380100f0a0701003500d40c003541c101d0306044100d409100860141000c4035100c0c15035070010840d42040090010403520543c04000c182482c241d070b41c00700314140da4a0007144d1021a20805c50018519100e13003001d80c1c0200e00b241224607208810000d11410281140c054503150403002c110b00740d008602e03d520003143c11540c000d50030840359504c219204d100d03483c0001d1241e540359251050101c1c1502c2603401041d0001c00c200010f2806e070400b11417040f012500d5100080c80c010000c1483c5040040940c00b4040d81e40c2c0e4181001d0440c4d0900909034803180c000d9a200040400c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73611153 1250 73609903 73609931
    0x803030f070201061202010903080715060f0501020613030804020d030e100f0e0301060303021b1318030210200304020d120f020106050303040e0402041119170a050402150d 75
    0x940c014045400d90052600d0700d60402401c40d40150840d040b0301880c0c18468000d0313170381b00080a0a4907003140b2420350344c400341e2600d964100b0030380143d40342039800c00d5000500d079091043c0304021204281c094690542d201c44103403008030810707003000700415a000045405420100d9007107540c01d200f070a000607000241c034006035819403030441c15000115940c000070340290b440211954000001c2c0e0080c000f0720705540d4041c0d1560840d501401d90080c841061a00715074900c0e01c00080b84618020800055600c1041828224070311307030b400d8000d032203111200848040148114682107440c16401d910851629400c1c000780d0748003500683c1e025a800c2c03040404503040600d1010403c03030a07102c81c1030010311640d000e400e48801c3d0340100c2c400d40050101300a0f040b500c203610f543c4543c3c101c0340014080b007108011600b6015a944030304008004600c211409a00320003c2550305074203008001240d540d40441c0c8040c0c410840d4004d402200100d140b04c0700c01c1c0e0040103007400e00c82d91200401d5901070a00c0c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73612403 1250 73611153 73611157
    0x1815031216030f0e011d030a02060c060a05130b0f04060207050312091905070b0f070c0f06080c0a120902011b03021614150a020309090705191b110a0803 67
    0xc01c5000c04524040041019081200d2095045003428002c0d40000c440e00082c01c00b1000c0ca11001e24004108811204d5640c280212191a40d008003083c0d04c070885a001c0940d6900b08450703003012a458640420014681300d021041901e9010b41f10340400c4e9203180c5040340c0e210340a04100e581540a001c0c030b0300010000d202414594296842407a90b0b072400c1c1c60308500c0e00c200c68086a440410000032003010403030105007201510100c4600701e555001e401510b40c41072191140190444001c00c4000c0f44070b0040040301000c0b42c00036500c442c026195400c801c2418491055128081004000140e050449070380040507918014101280c0c20b00017803942c050700c182019000c60068020910554403c0a0001c441c0094075014135140003050740c01001c960705200499200360615804200707404420300c06c2003103c05181010b031071494681000700c0040c02d160080c200301d0540100c04158400070754400c800a0394054122450110050540e444802c60260400c07442398100285003c041071500302040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73613653 1250 73612403 73612417
    0x6031515030605010308070b070e010f08150d05060a05011508130c0801021306080a06060921060615020f0d2c0301060b031006030504050d030c02010b0a15090518150312 74
    0x106d190750b151f40c0d2070819502000100301400b07116040a4000311641c2c000096107080c451810210490b07140e0400141035400310140da181d20003014020b46003044404260030380149034150051081d40d0300d5801881c1000c9800d846000040c5540d40014004005081c1204070180105111b4050039145c034241d5081e40e101c4160310a481c1c2c1c103060100000303a40301403056403020350507078100700890400704024002401c61007201c000000d070814160405a6519245d105682e11000c1080015681d4405040c5040002500700150103810184240300c84045528030010b041070740c032604ac680751241c0c2c040008080e424803407943c079040c048400c840c1d00c0c2486950003401c052203131691030389011000a26600c1d070f0354101c1c2c800c1508000500c03000550019071540150300714100886d101c040b43d00128014078001c6500c950042004500241800c6031365080312039142c2c035a54407131003a034442052020000501850721500301160300056100303020203c000035805001010349540b41052584001c690304441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73614903 1250 73613653 73613663
    0x4090507170d0309020f0d03050f0d2705060105062d040504051b041a090d0c0501090b0a1b0201020c0306010303050301050301050f04030f3e060a060315150306050103 73
    0x814014403401c10000d8072229149843c0a009803002c2e5408540000f40344880a030140a51140f01002c15008805691010500c10034094692040c09400c00c081d104061028204040051107103400c1c00640d00d0f004203560300a4000c00b80e903442d02e824002258002c0280107517807040031810150140c030081e80c41c403e00349100440c503180c509050811040b103501500c2401ca90490001c64994a540c010940d02141c940c81c40c0e1510009030100d07088002d00c02d45500d9a403102c0b83c00a11f504202a110341201900e80070b90380c802100352944c80300078840c401d0480c9000843d141100404004081d402e64179440ba05c1881900da50340150b4002ca4949507003a0011008120003000502c03941c02d0904c070340c0d0342c4044111108125400d250314050701e07030340740320305070404004000d10000140725503291003214140101d83c1c0080b80c4460180b4484110fa0118090102801703803001280070040c1c140251010f580d08800d07000c504018540040005040d01750600c200c0a900301c5001011400a1088500840c020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73616153 1250 73614903 73614929
    0x6050405030606330403021221180f0a171e011803080907150f03060f08030f0a210209010e0103050709090c03110a0e090f0412080604090507 62
    0x10405082c0000288524001c03512102e00c80300307034103203100766505508082e0881d1841c0c0c403150745000340f140318a400194004122030024401e28000080d80000d81e0805035a40402c089030390941104c030710840e124210114042c100e284042e241c92601c5901c0700000500c0203000e1942e03425660404070104004150642002a40e500d902015005020315141c044008118101d0f00c0f90b85070310044201c2c80081c08000100b000682d00c20020000c06014188218101419181c0c03007000520910000c06140c0c0028105080007817102c0a080d6240e0035140018044d5040104141c41e00d4281d8110008000402c82c48120400c103050034403401c0c0c51203c2c3c00350005039640030a0b03000500748413100b0400c1c504161502080010720380d8803010300e005807640315030b000c50200304c0312404502620740400c2285088000150498049810481c100c0080b001564000156074550a07000104072084902400904600c2c20703104a0f20f120703195242d48900024000183c0036580d45910303141c5102900048000001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73617403 1250 73616153 73616159
    0x3030e030d02030f0d0b1903060506010e0a120809190308130e0f24060f0426030307080403110a030f0305010801060803120c1b0601051e03031207020c0a060504 70
    0x1060003081050000c1d80021441c100c0c03400c03c80c1d9514803a40c0005004142c1d1541032040c199580d44400c000c5c1c1e1448014a4009034076420000000d1a0030358400e80410004001915a400c1010800303040780c03450a14101134248a0301d43c0b650036408400400d43c01516200b030036140d942c1e6480c2c0c81002d180110030b81074541c019100750481d0101583c0104180c80480004c000c101000241039581c03103195001100c070039800941d0759002000c811382215501000c0410081075002c0301c4000350003121004007050242d42ca035108456480c0307050442c0c0000c0c5401c10070010791894003824019800a200340b5210107850b00741c0c500c0d2414050002c100305d0010307401019610040f0780c180209805411000c000700310712031030304800c2d540c1e0b441403040481d0781122000c0050b00301c00c000c03010386e080b0b21801c0313420620603510108000d4503544240030b00b42c4620000080c92401c0f140001d0905501c0364054021460200183d0100c130f807251005000b5800c41c446c40d07548884907140c400720f8400429082c3c0328161a141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73618653 1250 73617403 73617409
    0xe031902060c0c0c0d03020f030a051305120a0803041a180105010807050a030201031a09010b07170a090308070f0206160203060c0a0807080712060b040305010b0a0302150d02090a03030e 81
    0x18024005682c422402e12a2541d071036408105186168000c840b000720780886840c2c16070400310000d0543c1d045000204440b94410303000070080c042841c500261540b403540701c1040207010650b00c03442680f1640110505400901c0342802107030464050041410010348a1001408940d0221964504a04e040c03a842450001c00d000340c9014021210182540301c0c00d082c00304e95507110a200281c1007585034800400c842c03840300c00b120a00ba00240c405151582c5448144410740c0c00032070111000c0303501d29052190990040180c0d01c0000032a07954510482c13643d01c0c0e4034001d400c020001d50714401c0d403840020040e51072500400e600341c100c01a1425900040c010181001c1c0020100d09081400b08502890113a0144599500210909201e06c00b500c8d000421a03034180f0381d400ca001c01a240c05400719540034400e02910489210700000e00c00c8480d0a400c0c0b01d0344281d00d1000035001400707000040d0911740080c1c054022030148820040c10300d0604030009860f500e882d030058001c02c000004124040c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73619903 1250 73618653 73618663
    0xf060408060c1b1902192904031406070206090f0307020103020c030c07230604080c06071b090f0e0c01090905071b12020c0108190504020a030b1509070e01020303040f060e031902 78
    0x207200030f0000300300940340110011070010707101030b107c0e200c1c0482150701c42440d5400c002d80300234507000040300d05002800c074881a5108030076030f45207000d44a9900002c0b1090740000d90811010440c0c030140d41450000d41c010741c0650018807109071140018003581d000d90f00c0812080b4001c0c154000321244070310000750284000e101a121141c001d0108200c00d124844000883c40769080c800d4400e25528569410701c0d42c3c3d60701a0600040f4441489000015411700c0c1e608507100c607400c03500040103984800d0241c583e0f200c2c40c0d0841c0902084044134100151150b43d40302d0342d400652400c03c0d6240e4565501c0b04810854407030002c46001031440304c034421140e03042105403600c49003070074840710a040c81c0b4504401001401c154808d41600c4000090441d110044c1030f000441d4048442d0459040401426003642e02c0340394083d02a49461001504c480d00c50b8401003040031068000e103240d510b85460b0b0703c00045003240c05481c03564690003048035124040009064035000d002d0031034620001b01d17000a040c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73621153 1250 73619903 73619929
    0xd0c0c02120106030f08180a0311010306050a050d03030c0315061e02060615030a02090607030203030405060709051005031f0f060305010e0f0c0a020c090702010b0f060408060c1b1902 80
    0x6038540b075400d200007490700f094907544c0c0360002521905e647c99441380082800c0203012480d0026902c03075000042017003441e03848040140980f414400542c8070801e1103a95046da124032a0310070814004a000f0901903800305090300c2c076914012469410116465070440c0c019844800092144038510b0546020450f8120100c0c40a00c0078088508003200002c601e0010205c88004500001010405035042681116075900740506040c1e01c2d02c43c6810042c0d00e917001200c00340c420703000c0c240c0001c0700c161042c0e002100f5100010220340e02041c1a44080300c254000034880503602c4183c03040c0c5405410540c1d02880142580000b0b55029401e1003002419210180e11198540560070305121420340b000c814140d10048006002e611040c0d070a00880c42d18039486a2241c010300c035001407040702507040d0040c0c0c41a030025034440b40380c90451400d00c400e9105a101d80c0d5203940041c00422981007078071008244504114080c400c1c01c0311440c42c0d66003480101840c60003001c104100718030071814190182410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73622403 1250 73621153 73621189
    0x204051b04060f0918050a0b040c1407111305090d050c120d14010803030615070f0f030c0503030a140105030312010902030a0204030609080c06061e01080402060d0c0c02 74
    0x11140e200c0c0014842801640a0503082c071464101c1440050b01c100018401001c0c1468000c00c0c0c04c010401c0c440007494165140c444160400140c8140780c10140038844054030542da4000c8501c0c45001402e2030b0750070101e4120756244800c4448221a41c0d050484003d404104030009064140900e14a1600000d101210b081c0304041c04101940704010071b00304180742c007a140c0f403030380c5404000644004180d40d00c956038031000c030000042403004d0000041e51280c2c80607600040d1040196409550a00031a040200078019031082000001c090340b9002c07000724402c0c1000c0c100c1b8403983d56a41d0039504116054a8165580d1103800c12004103450700c240100010b4002c0d43c640700c245001c0e807107242c4050140410300341e000004101b00c40429070480b401940c100d1810400a066817400c90301a0b48001c40004492048034082200340c90714039030707215183d007a43c04825061030b2981c0055410007001002a64414424402c2481250300c9000b1081e4403165130380c80d0907501f003440c810030020100900940350 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73623653 1250 73622403 73622431
    0x5030403050c0913050703020d0303060e071e0212030c0f090d03121508100e072d0f12060903031b020a031103040602030d05130f030f030b09040b040210032007020405 73
    0x1020480211b500802d17030750140d40c004119407460800b83c2c00340645510501c4c009582d0820804000d6120b401d23600e0f803194007042c41700400c20642c422a507402202201030000001000460fa060308148000c03c03506410101c00b5003440f140c1800540c0d00c0c52503103030903008a241d0446884010415100300d001c81c00c1400b42c16903c450130101d01551350a00c10032003004950740d9103c0d030b000f1050300300a18402020045468049201100c4008030107003024030841c031011084490125440e0345680c1c00d603059074921138204180000c0f5440d810054400c104080d001c3c5071740c5002403a6042c03011900ca0031145010340040a05503414500200f220514403030090041e0403e00c010322017581e0200494588541d2082c011941e500d6903030401440e440504001010f10f0039100c0090105500a10302c0d04540700262002c001500d801c0c400e11603811400c503001041340071100e00140041c6000c0c502c00c00d8007003c074580000e00b0865165214000d0003000c2e14be221364600810a4401c51500d8005d0a51050510116034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73624903 1250 73623653 73623691
    0x1060206040f030c030e0907090314030306010c150b1c0203060601031a01030e0f0102030a0c0206070f020309100c0b0708090c01110d050306010507052d0a030903080c0a05030403050c09 81
    0xc0b07040049210040c1007044e10601401898855180000c0580005182c80380300d082042010b8940d01c00c601c003c460001b91035150014860011085c0c03441010183c4507000040f0160f99060f24801c00c218000100725565080d09070325466041440599802c4c03414031005080d0f042c0101460114014156410581403050303200d966030030080701e14810842803c010652910410700745003800c1c441c00121040f9880403080045064080e000101d0b022240c1d001d541540e21581d0007258216006140c1c1d00242e80108456001418428070100085490b1703c3d000180031950381d20400802070540320341001811031800d001035007030300b4002c0310704000702424080c1500302d88000311030700d441d500b44c03006d01440310200000c0d007282d00501c212622030b43d20034244e60720040f418080c20b820811801d03113166551418844040f0002c2c00040c00c080c030700c1d0580c982e120b41901e5552a14460703402140d580780e4900503000c041d80003030002c00c050720207103204e10050090461001c00340890900001c10303a90203040c00503580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73626153 1250 73624903 73624913
    0xb03061302061305030307050715080c0a05030c040803071b0b070c030b060d081204050d0504031a040203100e013603030506010c0c030809011101020307050901030b0a0803210106020604 81
    0x5840c5141e042d9566500c4680458018840e4001c9a00c101c2e00742c000011008100103022034001d041d01c01503121040301103822030048515032000c5a650078602d404002010a0b613008034051580050300c120340d689015102c03400c05040d5000100101c0c0d2001080c2c9100285c001030304056405032440c80c2d206403c1c0344203500c0c1c0640c0c04d0442e10001d018040071401041d81a1151801c044449410034601642c0f82965100862204411901990140a8040300380d0305070b8481c004071000c0741e401c0310781078140641e91081202e00041c080c0007243d1510401210a41001d802e01901441107a10400055041c00141e0480d0007552a07008400301c2d604079449401080480d8031004900030341628001440daa0b528005032044040c0440c0540044030a101c0001000044070062504030800c5c0d880721100071201035640c0c240c0c00162842004241c080c890713540309501c40c2c4d02c01385030607500500c12048190350341101c0303046610000800b09003041200c0d07120824050101c0d040e004205900c02000c42d45855110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73627403 1250 73626153 73626181
    0x50a081f030308060d0c0312030c0509012a02090702030405030c04060303090b0a1403100510030606140c0a06020c0102031008031e07050313090e011d07060f052206030b0306 76
    0x400780309280700442c003580c039080e00d9a0f0390141d02c850b8840d203a40c0c890511581908c2e002c40f6400021341800846070580f03110b00b0554a001406854081d4010190f0080c07588104151400d9007400c1c41110b100005a540c40d0500750294046402a6540c3e86c14001454213084200405500071414034008000181d4000391442c200c500f442c10041e1070f04002070044480054603003404002c04004400c0c000c6602000080b03600b103c500f101c2c0000c01c4140801c09800f80c0b5054807070308000c0741004103404056000ca000520b44842c6000c25906808141d40e40c00b012a0040d00807082540c0d400300c200883d00500485500280c2087c1c4021401e0920b000d21105002054407020300540001007900c03400c020b803c0080d82e103d020070403030190380c1c03941314140940100400075100c0025801c1424401050900c032031041d40c4001c1d0000500070003420a2815034503800e20089040030404200400c0320315900d80c0d0050803192903140341080d555864140c006007910348111042e40300e40c01c4402444100c40110380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73628653 1250 73627403 73627409
    0x3060b070c031b0b070605010e0601110703080309030c070807050f01091a07080409020a021006091404020f030a0f0503220602030712052502040c030c0c080304061506050a081f 77
    0x30400c1d0983d00d000e21281c004000b20340c08085090707004541403081102c075400490503220b149517400070596500c401140e100c007e0b00c1d03a142042d08022014008154040700940c1c0c81061a012a85484082c503022460850668001c0e210394000e9602480740d4501071081000004092801d408001c0c03c0102c90008003080340317455080200001255002c01c1020b00a680050045c2c1c0011900c8038050701d0040c0d120312032003c0c0400d400b49001b1001c9640700c5103100d10010592590b00c001429602d50f42400300c07102c0d010404980c1803007007610100008036030180c8904058451805581c4503c1d584041ca00d03c0e5202c0d615680a4402c44042480115400000d8820840c0c0211029000c03403c0c8200a0f551407040d940c010a4865141c1664503500c00c06849400e1254820340c1c04000f000d4040c0d03811004c44201d07042142c009401d42d41901c022400c403501642c1c00c14014900090900c0f001c0c603100c411041e40e50f10080200d400801c41149294000100b00e82c09820124180031540780b03003035000302314038483c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73629903 1250 73628653 73628663
    0x10e0303032208030a0c020105010602070f0302060d0f060f17030406082d161412010b0c0c0405010303031d06040302070b1806070303091407030312050901020d0c090603060b070c03 79
    0x8070008522151100d002e03440650401c40031a42c0e8203112180758040c00d0038086040240d0300b010000a040392000076602c01320740d443d000e00d091850070740c2d00b040526407045214454064580c080280414103502c00e080060280809440c030080c83c0c8050003482d0000400b0720461504103002c10450786410200259100521031a024039400202c0d08004401d41c64a240901e00c409032030410005100e040c140c8045160701c5d407111030754500181005a820312a51480034100145640100200324640003d40708840e243c000383c4010540b40c0700030a0482d04264800d5000a0300c0c0c201c109602c4043c1204806040000005402245025200603650302d05d9440b070340030800780006060720755018503140e04800ca0f500400f0142d0344c002030304008000d02094001600c0701220a41028a8508005071400450780c1c50b494400d10000f14450080c01001d00800420340e6540820640c0003402c0d00b44580614208248c507030a0798141007031001011101550407e0714064020000d913004140c80c490840104c940c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73631153 1250 73629903 73629931
    0x30608280b0405010f0e060108120301080304062102030c07060506060c15101d0601030e061015030e0604030801080118030c08180303030c07060b0406060f03090203160801020403060b010e030303 85
    0x92402d2401003130b031405c0d0034042c0d80c83d02c2040c00400402140090488000c1c0c01200c503000a405c850003098402842079480d5540108010032100703002d04e5030030900c00a500080f0754006007114210090b64400c83d0016400e820010381d4200304941c501c501a04100e040d28264148140d43c41c40547d9a6402150500741c4a074480000e1050b400481564000c2c144040ca940c01030307050300c0b03480c424801040e10154042070500203042c0e040600010301a1162600c0020040e00c0e6107403060048003400c40d41150810591916005103001900b00480380c091031103a03413000080d61410003c0303821500500300394120407010341038040129911041100d002500103014035544d0041003c0c1c0e00e038010a011310b260705804040100446c00c170940018101003070140405200c4030642808000449040d0b004110100301c18190341030b0b40358800d42c0002d601ca44003404030b0708044500360b82560115030340c0e480262103a40014041c0204201806044070809003070030540810064803001136103902005010750808444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73632403 1250 73631153 73631161
    0x60c05060712110c01090209061804030c020102070f1806050915010806030703060c08040605060a032f19030201020c030309180705070812011e0803041505040302060a030608280b 78
    0x40d80d03002003d07586040d440c0c295614010030440780646040e0100b03a1040c142e0300e0009100b800c005002d1103800c1800b640c0c1441c3c0c1e035113554040d03948800d6428103904510a0070b6010507442e0029034184003070703c51482a212801d4001c07a124056920a8100e60300444010341400490342b2204112500c2041c2400d02c4030250b0784100210345401c6032a40f014045d02d00340f0803a00c0c4003980001d07409014034003c0405200c203650f11410f2110040389480010300c420508890441c4000c2c20b0300055076100001d00600c152500a580054050307100022003030307465003600104204661b010418550001420350107581460032480000d14080c0490315024204443d040000310560f00c11030403501384035841100e141c0c58542c1310781c4140d101c080c240a501c59602941c009142400c0344250b01000b01c0704443e004524043c01c1c551640c01d4074900040c2c8400340079050101200503560312025080710360b07003039130005000c51810007000e02e8542100003228405440070012041001010035240f015600034425040708c0e12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73633653 1250 73632403 73632437
    0x3020304090209060c030d0504150c1d0609090903030603101a100c050304030606030218090a14340b0309030702040506060f072001181e05060301060f020106060c050607 74
    0x2042c1e103e0110280000910700071f08400b654000b60256001e50343d10b14402c0e041c10f005808683c5103a441c1004103015a10b407040d045100c1c00c401c0c00c644000783c44079042850000204851b00016070b44444150404003c024036420104410511085460020f00002c0c401010b1418815000d003c031710f0003041c01440c03000300da074050b80081d003601c0c0e48102280c0c1c0e225940c0c09c1060050030103002c101c2c0b107140c00c15480910020300b40d001c18000d0040b1b101a042c922400d54420001002250b018000c600030f05000c145840300310244050031201040580c20511040703c20f9880511807600010701c200c809105200c00b600c8004241c443d141d50554000480d40c40301070000d00035004000c40320070b441e000000c7c10000c001200d485181c207028040300500340341200d03000540b1204403040304000700c2c00000404001a142c5030860420800c24548164244c80c1c0f6203011a9213640260820008180d409a216164030350902c9010001c0000d4507010050403030740d69400e80c40e0b420191044003000b035001e0024036000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73634903 1250 73633653 73633657
    0x11b05071508060a06050403110904050c060a030b040e0a0c0e070306050d150b010e13050606040905040b1f0312230c0703030813050312130206070c210302030409020906 74
    0x111007200c0c100038801001400800e14003046859a0207010f42c0c00d400030300580143d040c0d0b8146c0e640f003d1110304803000780d002c0c8016080028000d03100e600c60648400030039150400140790403401d503640885d4a1100c0b03410b200030f8072501100c001480d0303c4101e45501284181406100f50380b00c0020580058035003420803405440945c1201e94820101d00c1101d040215458558081c904c1080741404960703a8640151184900c0d01202c90b0440d5034400c0e03a0003d4006a032001c0d900104c000e2559090607250640202100c4040b42c0c11505407480c501801000580d0f10b03080741c0c4000c80f484201c00d5450441d0303510713441318948040030014486c070503a4010640241d04200d00903000e0540c4840d03101e03140c4a05d401e40d039003198072054003c200ba060115110721003412855100c00c1c0c00c5002546424041e8040d003403400c10042502c01c002c2c02d40000c4038010b80c0c800700103200d03c60059041003089170411803011f2000b44841c070304044003859440ba020000341c0220030f0700c080f0b50b04880016101e4503140b021540c3c0e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73636153 1250 73634903 73634909
    0x80403030f0c0906030e0d0206190f0603060204170d050703052a010c0f03180809010c0618061d150603030d090506070906090e0c030a0609050a090302100902011b0507 73
    0x90380c14080d03180e10b4030f94440480b81c110b4110317541c02e1148000034000140c82d01d0840002d1001a00032000041d032948171607010f8558042d503280002075846c00000e101c0d0031103070190412514103070009001c109003601c01c00c070804842c0b01c11014041d011540900908a44212035005003441008940c011800e414803030840b8040744441c0d8244d000d68811002a4020300c1d05508074030114100c83c42c40c648481c407a00c115200358032041100c0481d030440f503c8405041e00100d1003107040003400000040002d8490007000030b95980315001e032000000501d000410354201c02e42e0600600c6002805584110300001e500e10402e24094034821a5210000428114801c032242c1000c1c81e03081848107030810030b0019410b8130681c0541c2e04c0090b481d469910469111f102442404100c40c0c116003c5150030013440c000b190400c031103030000500c4550703420710b1b00103440c0300300c48001003282e80717402a000380341c1c06201042c451906c1d176808002d040c415a0020f032002203800d50381d80c0c9143c0c8c007049110401c9800c01006001d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73637403 1250 73636153 73636181
    0x50a0605040f0b090109090b04060e01020405060c07080601060c0807060905070506070305091801051014070f080d05010905060a06030e01141006090506121609090501120209100803090108040303 85
    0x302c08406001c04080d104642401d809888044c000151107801807180245582e8008840800d913150354450348041c043d0f07801400d0295600300000943d903580c110042444a2004000d4000f06280c5400982404c03016403010050126040e030380c00008402d02e003192501c9503c9440015000c801d801c00d81c2c41c010a91b0411508288001a46814150000054100320760102c80980742c804201d2248100014203110f9170380c00c1491118081c02d01030041c1134001c1e40415014000703003800300c50b80790302242025400040d0781032607002030010074043c11400b450340580741c01c0074184007600740080400c410507040e200b4007040690750420940180c1c030a410a2580c0d00001d0940086400c0801e06280440d656118620110312544030001c2c460610300150f903a441c1804407441115650038880d0200b907035206035400c0400004ca080403070698031b5481914060621035425180065a510520501c2800a004012036150f44030041150780700c00802c41c0e2001c4000c0c13900d1030060710f46140c146c1c094080b102e000d00c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73638653 1250 73637403 73637411
    0x90c060306050a051804080c010b0303040320010c15020a050702060c0601050102070e070203031302031906020309010f110711060706020301030f0303140603060c0c1501080c0307060908060703050a060504 89
    0x5650364950001d8003942c40c101d600800c12075940d001c010240840b0740c90704c1c640038192000240460703109000f50000d2000d100000c02c03110450000a4103581c080d40003141e60038800b0700c0a17040ba0a50a8401c5002c1e442803c0011b03003000b0340e0715568818a80c07074030528201900080d61004207803298050700d040640c054031480c0c41f070600400340364950000b40110b5005100724000080d00e00440c9241501801980e0051031464603000c00c0d0056404040c64140e805105500c3e803901c1e9201d401900008640c05403e0041e103e0404042660070b413907c411501c40500d040909607c451042d01c0d0403550003503440314400200407011008100d080c0644100a81150320201c000818400e10a0040b030312036100b90b404100001103070240c5498544207451407501f41d03000e0b0000030308880c00b45000f0031543c4c950004485001c0c888403142072031410300341c000d51620307000400038518906040103100050401400c00d1102c950410607020340c0c4810081c1403030201a21040801c202c460300380d0040380581800382080c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73639903 1250 73638653 73638659
    0x5120408310b1308060a0f0b12060f0601020c060a020706030b0a0b0702090a020912070302031c020616090509040b060f0402090303070201050c03120108060117030a091701090c 77
    0x1100c40e0030106880380101d2414500c00c050184980640075000e900d1030700005500c0c2860006002508080300f42140305410782800301c0c030700d44100003082c4159a00603022818481c0788094030156101000580d0003464482e44c40c06e05070002040d10b40d4800e840300ca0001031503550000407460800d5400400340c00c40b100062300c2c01101d41c040b0f101c4080d511192001e1040510400078400c55880a05c0f510140d46401e05c0400014a80480e0307254011a0303007007025040142903c00500810b5855152452a9012100801c00c60405001e4100c4410b03001110004501c5410000b03511400028103030200702010300004444103000d240d448001d800c0250550714685050700c0c168502c3e50b815515144916071201e260718845c6009c1c02100c4403008003801543c100a40341e0300542c1c4e01e410101210305c07640402d014075151128100740250080100000030101545410b00041101d4201141c500d1513401c10440000303000c2d040140b800403144030264034030240503450815401000250401043d8640d400000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 73641153 1250 73639903 73639913
    0x9040e1207030507110303090d02010305040c0b0309010f14040b180a061509181218080d0203030f0915181c03020a120b0d0b0408120109090b01080a11060a051204 71
    0x2600905100c0d00f07021a5500f24182015602c8c0682d440c081d92040242c011071303005522075009207070004c0c49100040102c81c0c0b1582410342e16081268200041d0303640b620341290103560341c087c4d024840074484141d0b059043c144c40300400d4000060544505c81c000059002c0054000c02c002c11069803c200100803200c84180d9a643e00001445400c98041c00c024a1410308448200c0205a0a40c0100c2e2282205070044c4162146410300f441c481c2e03100e5514000284640c0c09101c1200c3c05249603010b90355034544105028401d20001d4642c1401d54441c05401994840aa500d540c014440f416210207012826884501c2d151a26031150003150000c5041ca00880c2c040c0c01a206a14075505c80c640e4440d041008842162038510034541c0c00340c0e441d0980004584618030070794003d40900d442c10301c3d013015001c21450b0f241c001e034452a0020b644c2d142400c280081e122a0b0303405001c132600580106503c0b80ca5485086881c803c0c0940b1070200080c40101d0140201c0845403885090f10307804009103014109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 73642403 1250 73641153 73641157
    0xd0f0501030b0c0a090e1816030c24051b010c09080d0507050303010e0a0b19061202070b040b060a080f06040203060a020a02030315040204120803100b030c09040e12070305 75
    0x11107401455030080f0b080d0640c62010758a00c5000e03075480011461030071a4900708284098818950910030202c2400b8428003800586003c00352510010340c42031031403804000500c41584030002c0d1000d0095035081840700c00501c1110030200c0d141c0a62141c0705400e41b12581d110040b1600303a40d600c1c100c1d24170302d6242c020300030b00d00704c44c0d20350141c0ba226040300c481986c0511404100400c0c50308208014000024600341e00d6400203690300000500c50703021404074221058803d181c00c40c051360b613135040140350b40c06558100a449000d5042d828140310b0350710106150000740008204d182c5500c00904140c03101c0540100518404088401a50f0100a01070302c45405540903800b0b0300540000680000c407074001c5400240c4260b004618513943c4060135804940341c0200c1542c080c1c1c00704400115540e9224814010a0083c41556541c1c1070511040510010541c40114150000e0080080d131107001c2c070035100300400039100403441d0304005400504090100400c603a00c44004500c0206250344400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 73643653 1250 73642403 73642409
    0x30108010c0e01110312090c0901030b01150e060904021b070909051b010f0c1514070e0a03020105031807080712020907080906010302061c060602030a1b15050c0d0f0501 74
    0x1034148245501c6001140e0109440b034407900c25a0041010b1003e03a01c04081b07480d84002001c0665030300c1a000c00000c0d00ba21801c2c4c1c0b055039602c581c10018800801d551401c0007441c1081d0810b030066940400c042601401020461031240350b001c030308010740d02d036561400007140355000152003041d0b032a5401c490080c4038100003a105071040d0305503c0e240400d0041d0f181354030b040503122480f54044229003202e550000d65411282c8001700c000c0301180e04e4041c081c1503000d484404071002c0c5864071400003081803040d181924442d032107080003040541d8120085941008140d047d803801100750202c0b079450a401c0394018032083c80380d501c00044100d82191607281c3c0c24801c50700f102c035545130224100d60500e01a142119990449001040140391641c0102185452020002004004050482c01f03c840300d611100c00b580002a8804200d42d020595914942011440c04400c8245031125003600c060400d0301718526036100d02146262302c40f0340a5400c484084801031110340541030407040606400c1c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 73644903 1250 73643653 73643657
    0x305010c09090908040e090a0c12140619020c0309030307050d030506031506010c030e031e0601170318010c0f0606090c08160e040b030a0501020711010e0619050f030108010c 76
    0xa001c01e880320b0a02407000f0300354004d9007407401c06050124510b16002c014003040818030402a1410000d080034885c0c0005280045860082c140941440182082c80c45e80c0c583c042e030002410800039100c000403802400844007001600c80d07507000c1c08945544100074119902d44000304e5010104a40010000340e103283c2d5513018411500d400c3d051660b030f0310140c100c10303040d86d00340000200c1c41d51196000301d00403802440c0100c0302c002180042030512000401781e0340c00b40220301c41948000360401c8194010105d4045444680c815124011f4a0f40242c0c2e0300074450414004110640b82e100d241c00081550700110683c8110245c0d142c40380051901c1d118007211241050340313164425004d00d2445126540b036813200a020440f001c01180c00035000d071412580160354141ba5540c0703072400c04c031440100d0b00c248001030350342c01f650400c030761010100350500c2d0411205101e181240c3c1c907078130262148290030b803409004540042400362501e00514403001ca129401000004422005401924481a0035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 73646153 1250 73644903 73644917
    0x42d081c02040b0f0702060f03010e06041b0e240a051b150a020705120309010e1c05040b03070201061a0909090706090b092d1e010801030602160501060305010c 70
    0x2000e030200c00d0b4002e40c450207108080038440901151a050b00900364248000c0c076191034540c4103c81c1e0100b41e0801e8100031109061030381040251b080034800c1e030310200541599443d4400c01480c0003400d210004410798010f020300d890001c2d505080c040c2001400042c440059190004044c0040a40e0001c1401031100030b10505156079030b040209a0440c0114080c00000c0e465640ca181c1d4800b0b94401c0c58126410310805208206051603040550300480c0700e80e00105074034071410b102c64600b0b003002071010820758021140e000451703006001c441c112090f000400380c42c0e03550401d09900403c00b07903004003042d40c4403206190548001d03000038164528111244503041e1200080550340d03000303900598000c500c04580c14410140c0d020041c200350300f4003c00145410181480750035104080e400c1010082d0242c510104051500c6205200c44401c81110764140103c1d000c0001d104850600c8041e11050380060703910002c02000020151032a0080000c0c4441a07581c079000d4000c010954005d0300140c28 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 73647403 1250 73646153 73646197
    0xc06020d15060503010b030a0506010c1203050109060b031509060117070c020405070315050f040609020403080408010605031b130e0f06011a070c09050703090f110406060314042d08 79
    0xc0e000e8a060b240c4c803d29460840c0e0348c4100c85801040c01074402c50500000000e13a50020b400158401403520b100d680205180d45440111000e48103150401803414006004004030010000b05500b2202c004a42c54400390301c03680b0058a8001550000480c04098203041119090308903030403024007442590100a41c2c2d071a80d0303084080312020041511000340741c000400079881c012401e014141b0008000145d80766441001d4003c0740d00560040760001d00200b0104551751003071161070b0040c132066026182c0840d5088440c040340200709005446041084d103803004000d810741c0214201c0706c1440440d482502c001107010b03034070007091050500c1c512a50809080d0104201c041c5e070000c80c1d0060740c014201d070900c8503443c0580070007040c0c4410141d0b180b49003004210114483ca21240c0160800c5c200481c25a040c00261100c0d0b400c503000f4103041c1114904800440020b05921039001480c1402558100c03409a902c5052034031611099080002c240043c0441038004180e14000413558401100c0c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 73648653 1250 73647403 73647407
    0x6070302190c050a020d0606150801050a060504031203020705010b060412050c030f10050411061306080703020a05091002100509030c0105010e06061905070204021c0b0d0c0b09010c06020d1506 84
    0x2c540c0c00610300d03000030030322400505040ca0034a00c0e9604c145404661585c646040c2ca404100c0c001c54980050b0050004001909250800301c015000c2450b1152a03d800e546810005150190301e000415078006007050500000707500c40031144070010219551695600c0b0f516881c12a208020b8883c1d0041d40001d95041c54001750340c04112110301c01801084401404500c001c00009009a070440c40350309100325295900802811031200c0b007800720842d45e080c15002003034824000c040c402410f00c1000340c260070a81002c00e49000e4101121030b81c00401040300300f282400780b02c06920803440d0030714052180052002c009401105c040c1c1c002004075030f90f540c088041c0c01400f582d0f1950844010803419002c1d0b00700705c0c800c8100d00031608109140100c141d020808030382c8080c02786006c200c61207809404203a60b1b4001c50004d02011642c040c102c1c040f07038070b5140340d14026100307070b076513031070002800e4207050340202145100290480b0085460b88040742e2514042c20b04000209441c042d2130b0000700b0058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 73649903 1250 73648653 73648667
    0x1608070201260a09030c022e0f0509041109090c03092109040c02190503120a0b01090605030718170c0603090a020f06090409030e03071d040b07030e0607030219 70
    0x856103168018645071224090020a4010000d1701007210400c0d00b0340150310b901140244c0301880502c2000e402990600d017041603210310301d0038010009481c90360a2001d0740b1000340c40f0075600c2200c0000701107041c0c01d000790061080114098100c908803080284010021000c1e510070303501d140544400081403400d5102e851000c4155120038070043c4204c50203401d040c2e00a00c0300111500456114805c0b0f000f00d00101110041c2c100c4d41503000203150710065650404042e08066404414450f40e004000040c080e11004e000390300801c42d01000203000544248031544c83ea00340f0f0450065016250400c81d1281c01c90581c0f02070140c403513410101018140718003140d01c5080e002c2c0203404040901da08002030b6007441c1542c00d84c0444240300c07214040d41d80b0b2017030321003241c4242c940340f0304507403400241828007410707a110045040f03054039039001c0c00c1b841209403548154010f60004055031135410640040480c0e190160700d6206071810082102c1d016801031104115080c103107045280c004800b00e0f200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 73651153 1250 73649903 73649957
    0xc300903110109050a0e04020d0b190c080f0f0a0219090e01080d05071b03060f0c0206010605040807170712080706050f1902161b0f09020307050406050c031608070201 73
    0x400398070a02000300036680c032600347c4c21030310040050314902d103903840c1c030324800740152740c080243e00c0c1151a003280314481c0c2c441c100c125a611b0500d0030f01890302c04078455400000802d03101250000d000000c45a00440d41111640402d0844480b100c4505440060401d00e9500400ea14001120008118a1000200c001540b66039560300b515100955030f4100d07054a1200c440c04000c05c07200c50200024596000b03440000c5524140014243c100c5c5100030314101c030690148052000030403061001c0400400c00341c1c2a114100c41c01218100032180e1140740074407070b80c40856000d805007160300402200d400100a180d0041409002381d40758002c22035050740d03080e034203280700c0c4003000b50101003440d464015110070a898603640300401e016886404850620b107082c110096403e10302480000c1d0710611503000f0f811588411811b40c90301c0800a859449503000301024040085000b81515200300100d5060510704c0841d0ba400c1f0342c003031414199540100ba000c9003c01c004910b0710070381503080c14000c2c101c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 73652403 1250 73651153 73651159
    0x2405100b0403080a020a020307140310060515070f0c060f020d020111090909150114040e0606030307020f0307120605010510030209030c060a030f0e030304030e0d030c30090311010905 80
    0x740514682c1d4240c2075900004180c0190b000704c1a82c10056582482824010608403580c030f92a40608000c0505044002c190b030000c184ca000818001c645641d0140300040d20352400c2c0907030b01c441c04d05040c0304940018200030105014800d0100e682d56010024281c40a46a02107030444100480141c2c01d0f100b910440c04c0600b4818000780c2c2e06850a81030b0550072202c1ca00544d08034100200640103110402d030032001c08001600c0c00d42041d1b04081c402e21540c07818400180c030041c24000000781e128400d2482c0a8898104040400c24503a424010700c0300900c0b90040b100309600c0f152070010007074a001d10441d4030460070094901e032168002c4c000c40b9040d48005000c1c0c05160318042c00c100ca240c00c0010400209036455402185400241c4141c0201241103c0207544a00e440d00c2c0080c903000b0900000c600441e620740d400750001e034014440342c1c00d0a600c448403066004588103d00d42c0721651a081064001d0801d448950700d94101480400f07030ba00a0900d601c0c00f54280c001568491900c0c400c80b0b030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 73653653 1250 73652403 73652407
    0x706060f150f0504080a050d0f020102040609090b0109050d0b040302010b0906010f03050c0f0403050f0c040603081206030a12030c090f18051302030a0c1409010303050909070306032405100b 83
    0x4040e11a2109070b906840c2418224281034070b5984292411207140c0b011101c41d40500307001450079810440c0300140d0003a41c4029071516050600080201129108030401e4645815808070180e0050304000081c04028010044540c01800d003a00c05d98030a80d02a8059440c100c11007130320381801640c0ca0301c03408041c1c541c03480101c00e4410880c02000000c2124580d03080c00c1c01003c8049080c4801071000390b00480080001e0b01d041d400c4a801c1c0500410302c85d12492030468100005000d00c800da030611000384154503629910640405d0900c00d050400400080700c10b5090900541c02d580004100756140c0c0c2d031030b80c41984031110040400041d0140e82000c014040000482880c55004154002c00524041c1d0101700c540c0d000ca483d000311583c040341c503205a0f900500540010203000d07505003801b05e038405119450340e00c0c06000d9119000c0018042d0b00305000150350035010342c0210004640c007100035108000c0007a40c03800b007011216004031100d0305100205554014000120050355456140d0b14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 73654903 1250 73653653 73653689
    0x8010f090903051c06080f030a090b04030f0212071e14040c021b181005030d140409050402010c050d050901030b0405060f0d1407060504050a1d010501141b01020706060f 74
    0xc80d198000044921a160400406c00d80c2050040401442d03284008540703400c64540080e042c1207094020700c81c01041800100082a8280f002400654042d200d55041c14445140d6178100701c00c40d0403c036a800710a448442e03560880c00c901008451400c20388102c40d001441c10402a070b11441c4014006a204005901d08842c40107480c00950a005049240500b683c5588500c0d162045600c51014003402d04c041080307040c28864601e00c00001d1030540c0601d9040a610f0070240500d0286124090740c030400034086900841013466441d070000c00b10303440400b0b040801800741d4803a80b90380780040e007480c03108603480c2440c3c00303640e020300c070000d015501c01c1081c0b00170f22008052480e02501c081040500101c4220f13070a1001d0005811250388080c0c1d51814001401110300c42a88007a4058410064101d1803400c5a800b0f039064420920305041410726001040c02240980c240c00368006040f25840d40c08520158010221284205820f00015a481403450804800c5220b00008208021034070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 73656153 1250 73654903 73654927
    0x112060b040506150a0c1502040603060b07080304031d0d0f0215090607060b0103090f0501090203120304110d03020106050a08031308030f0f0705160b03060a0905060a0501030b03010b040c08010f09090305 89
    0x3900c0005e10500c2c0090001025480700d00c001c4187d404d03501b40c00ca81c00101400704940c9406113a014101d280509840d2224680d00c281c8184402032014042103122040c2d518403030300741e282c0350302d28250050850305649182d040070840d01c000344c0c0080780b103161102030f1281216080410350398003000040909080000d640c0741d12000c0d015480d8998100b6079a2002e00c0009510300d4104201c5900503000040c40310780c1481410310b004520744204031100e02c00c0c0100000a035009410305e50508003903a100d075500e00306240913170161031650081d607030180c06514085038241e4004043c0c000980340340f01c003154095840510341d803288240201ea0350911001c01602d4111310501c80140f20b042c1c403580440b4108108011240070444458001c00c14100c4000309001c890700e840c02d00600500b039002410441400c01000260b0308e00f8080c4aa03605160701c4005480700e81c0d60030340c8001e00c40d45005c0e0048c8603d9801c1c40c070007001c49600340252610605190000300d40300d500d5108010600c0d0349a03c546160034598040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 73657403 1250 73656153 73656157
    0x21c030b030102090a12140a020a0311030c0a0b0c0c0402070c0506030408070204110a080f070f1110141602030406020a03050d02131e05040902061603050408060112060b04050615 78
    0x902a01503408102c2c494060300c803110740030700a103031031200c09903010407500c0c7c00c0780c0220f400c1d000d070090783d0702285c0c100740076964901d084000c40340d0101001040c1032000005c64107103a2068441070b80170740d643e000010b200146500404140d20030b541038560003c02902004100d0003840c00203032403092950b1003071186003010801107420071f0082c0c0c40031b0f05060780c1e6400581a14815051400c40c0000461600380968100841d0703074010350b420445440c01d06d80444024900c1140841020800080050804c0015406d0110101109040b802030040030342894440003210016225200709500001051207010f1001c41614180d40c00c640c0500301445081d107046600d41c0009810165450f030803c000c046110030032440034003c101d44081e110300c4040d11001c0014240403030713125501640c108281e0b81c0c010703a00d0b28201e8450a1a40000a980e80c0040c10220303114007581d0070a071850b10901b400410781001d62454400290f214103002d000f500702c12400d0000307480042e1038280e0000f1544040406c401031805c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 73658653 1250 73657403 73657421
    0x3030c0c03040b0f0d05061c03031a03061005011b0c0e040c1e03060608030a20010e060103030e0301061403030a211a040c0804050d030207021908010203070e01021c03 73
    0x85900b00707500d0b910041519400219581e00c042400110181ca40c0303014028140d00040441d421900d00d090328030203136544a1440001001c043c0d5030f10000368441070007002d40c6005500a01250400c3c9003404070a21324294600605001c0303041003114a00c0000b041902c8090715600c400c84001c03040c41c08020210f02c0f040504201d59400701e4150201d42e0711003110280066080c107480c203a021070329609004040707910641100142d40c10130001c0d44507180d00082d966240c200e1f0404088012811081c0060040800741d0000d200ba0284500000a05504c003004c4031125408900070401d103569080840300a407641d458164040e0018418581c0840c02030903d0581c076032402031240c04040c4214840c0048441014a4075003505030040b0408403400c0500c01c1d03022080c02e81c20030217480c0c1000d1301c8060313136000700f0818031080540000e50340e41151513210390b0001d090280c0450340121070f00c502c81c40f8040c0d0821225000010290a458510307580300050b0b05845100505080701034404d5100110301600b0051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 73659903 1250 73658653 73658677
    0x4030308040309091a090a060f030305210103030f020105090102190f0915020d02120405030c13020d0606031b080124090509040f0c0b030f0f040302010e0a11010f020a0503030c 77
    0x640c0010b400c11503001e00e80c1c102c00d45045544442c9620f60030048908001f4004210045c5804001e214036401d82c0c40c00000d0300e0300b6050050316500703900314421810200740d4801d40041298000003040580010004a5104070754000388125580d04041500302d0164440c445060350350080000180d03401607040019050781490241e40894a5020b44c100217495014104010781c007084820113200d0b8144079407640942c2c2c601c8403900c0c0611306000695100b03080d4000314460103002254801900c0c9940c100c2c1c3d08810340d20404d01074a60307150400f800a10b9054000c2c0301d060051075013201401d2050454070306892009040c407450007030300c00b02041112001c030f6441c070502445940110311303a80d441214611580c03080e81c0b110b50309202807500100e075440c1503110001a00702881400491009a0003256110340340c550010040e6460b401d0407400b5080d02c807101981030160131828400c0c414410940e07501e84d407080e21002e1742004010740c226510201031030040d096400a001180c00f01c03860324000c1048036150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 73661153 1250 73659903 73659917
    0x90c0f090d150e160608010e0612150901020a090803070b010314010b040608070f06020609030f30160203090d0602030a140901020c0c0a080a02280e0405060105090c040303080403 78
    0x2c1c0381500f19448182c0505980d48005000f050034400b0400034405007199181801c0c20b940742464000103940050543d510441e008c4913040d4415008001d003800890840320744402c0c40c18101c1d0360b80d000b948400803490002c0e0314001d001c01c5051002040b207032007a50201a4000c82d078613584842c000c0c2c652042c813013101d9540b80c803000c011aa0b030300d0107010050102d00010300b20701ca02c2c2901f202021603040d800300d419500000704010789001c011042e6442840d00c9605aa941c203420012588122140007880c3d90000c0311480041943d1903e8007007034480d250301c40000c480790300c0c41e40003a1382c2e07030084400c0d0552110300c5561501c0001c415402842c3c109503413903000315591612145c1c80d0281007080303500c00340b143e40c0450341c20103440040100c0381c11940b040d1000c5400303500b00007a4039100d407610300029000d40351a4603d41c2e01022a010024882012144690142a00c840002c0b07203507001a542a9000d206250011420b441c120202c140940f40c2801014602480c65400341e406034002481038041c4190 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 73662403 1250 73661153 73661183
    0x206040801060b0d0c020705030604140a06020c01020307030b0a08031b0c0d0803040507051e010c14010204061106010906060912060e030d0905010c0e150c010e0a03030209090c0f090d 80
    0x4240150b10162035003501558540128132110b01c02c40d0240580311007150300c40203080180340c501180c03040c1c02680102890303040110f681d1000345031080d1014010b01044c4000b0300d0000c948410340c0654040c03d0f4a503014049242800e04010719004140101d8103240c2082015101c0c40d5048000b81c1034805211081d6a40788110f00002110000b004c6000d40d48640008200b101700710303083c86440090201241e520000d00641020345d0740081704154520b0501c9000e00303003841800400000440b60102d00f000030b643c3d5540300d10b4010102c8440070300851451060f0300001c240000e80780201815141344e5910a000203181c01c0c000d40407a1062003040d1090b03a99046074101c0321070148010050601e04004c007080341041460f0071401c458207140000100031031190b80c400c2c41e175500f044091041d021b030300c00310361505030000700103004014151b4030002130b1003000c0b03503481096056005020029012140b451483e0358840c075070380e964440c05401305000c5404021449107071a0101605502d240109244403400c06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 73663653 1250 73662403 73662419
    0x15050a0c120804031b0b060105030403050c07030312060b0f2a0312160201140c090a0833101a0706020304050f0f010b01020c0d030203070c0303050d06051c02010309020604 75
    0x3500d0301d45400050301150422040c185c0052907030848030300104034813112082c20784a80e800340c0c001400c0c050400070000082014075100d0403c3e103130401c5c0b12106403020241e407468041c02c950119031005000034104100020360103411010342d8042004062504e00d84034500000510296039500c02031003c003041e10718940c8c03003d000c00180007204a40400071186080010300403079240001101c00007160304151518141c0d10280b001103400c0840d00c0c41850f1240c038103400140145080360031848040c801c044242801404500750a150041c120064540048480e0b6032614082d40c200c49441100c2c0b0000e00c200101c9100d942d2994114074480441402c0c182d05690740c200b0f0b40d009507010f0301c25501c400b070101032625042c09a0072148000c2002040301c243e11b000040d440d10b050281c018032a034508801d14041c14002d1040740c8100754032500c400034031034030703440c001d04242c1004604020307040c64408003051501385a0001c03440c080d180c3c0d0341d94404515070350044001d490410000c80c1c10520030301000603896 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 73664903 1250 73663653 73663673
    0x4080303010b070303060b0c031206060c0a030206040b06030a030f080405120c0a05070906050f0d051c1205070906080a0209190626010e01050d050c090f1f15050a0c 72
    0x200c482043c2c2d5030100390070000d0940d0441e401104052400304111160283c5c00811541c03081c006103000c4405903154000920b4500403040314428138052068040100740e4049809407089104030895202c030b8031000d00b490b0303880400c039038003d01152030044581c2501d03001305480d950040c4900c048481d190540d0741000101e03080078030508031640c45442d03d00b040244c24040c840113449200020031800d4a80380009561640e0403034494001c50030b2146000a1040c00d015110202900e040d200d01c941d141d400e402450350300140c5a08035007503d07000120b0b50b010311662681085408959a05200d40c0b9600310140081d40325541040d80944502c103003403003040075900aa801480c03503807112a40554003920900130359900808420100d117640780103200b000e1282401e42c0c150b40701074881d586083d280e403400d50300d41180241c0007984124818200084009881101ca10592800307054050356980002a00f40a466601a0301c00402d44516404203081c440e1000d081e140c050752a00070180011908c41d40508 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 73666153 1250 73664903 73664909
    0x120903231614060a0e06061005040806010b031008010207080d02090420030a0c020303160c03120905010614030c030601090507020a0c080d08071e0c020609130501061209020a05090c0408030301 84
    0x10702e0150180c1e040240b414803840d80d2064103800c0c00e00848409018150f224840200300c02d100f00051002c1006040c811000d60b0701509220045440c0b55865104d1010316410171074280303154a00710100400c0c6c448042c0203841002c1d60000106040c5060640807501030f400002c0034a4100741e484c040d1100a03c90a10114004504680071075600c0c02e118040e6800e40700c00d240220700350f42c400c1040c042d082c0000c090f12010081e0030b103002000610701d842c04448044088140030034060805c0c04407810b01c0019030080045071405d203540854001c096051580314183e40c52180d905801034001006910543c0d081507a1100d520b105a404c4140140e444242510042c0c02112240d401003000c0d0340755a07002446181c000c032860410302850408060b50b803002d100c00d448410100010144820215159081512040c10000b4007a4410201201c1d02c140145002d2007510700040158031341c08400500c2e84100030a540d009800040c00354100028000d51440140c201694224100301c0050480002e002840c0030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 73667403 1250 73666153 73666163
    0x2150304030807110d05070605100f0803090102100c08040b0702010e01020a0210060608011a0c0304090207030e033003060d06021210060206240d020301020d020a1209032316 76
    0x650402c800c0080400c0c0500d500e00050b0351040c2c644000319a0406c2c2928135590b4805400b051540c2c9100f1810b00c45903455110305400000408045038043c0007101900202d042030742102d102c4845103c00000355140c1c0444c03080490700e28030101d008642a4683c066000c0e045000205900081c5600c5c5401c9901501c00e0300010303040800b80c0c9802840c58090705000342250318240c0c28035410031403120001800d858120f0b41c00c5c1c0300000c0c1844001c200340300783d034000c286183c070840d20f500c402d0030041c1894403806100c600c68043c805070009101c2c806039515414500d0703441c12540c0701000000d81402580041d114940c000940c522240c0000d074140010001a059160485040c0c207103581c4400e1040140d400450035500700400304510000030800c03400701d805498040c10400c480200c0407032449101d2010194040d4000203415000300419001480d011103140c0d206408000d000d011142241d01c2004020002140340c40000d0802d01c4040c4850301300e40c0c01c110000d29003c0c4030007001c0c81c202640441100d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 73668653 1250 73667403 73667417
    0x3020a0b010f03150509060c07050c0603010e07020606040501030507090e010f050c041d090a030309031e08070e030a11010c0201051b0105010e06040203130b100306050a06030204151208070215030403 87
    0x100b04074142c21951004d084001050002c1d05189503003903240c0500a0400c01c0082c00032440c002400f50800117080c56030b90160029a0300e58550480d0581010200c0d1884c01520512012440c40d04061007528100c03174108015001e010304054601000d4080c00200400540d01c440751110070030320600c41c8600951960001503907030391034070b45114507000010402e0300c108071f422420884c40c2200802c48111841e45440c0029109034649415103084814000e00c030b804031040c1229002040c1c00c07508080c020750312601c0c0c500000c1c02100c10103030303a808841c1c0010904120b410141059501502075420181d2050502c1810f01482801414284c0c81c02c010320072040c0c0d102d100400120b52808480360b0060000e40d0b05615500d0035442d0403414004601c0c00406004140000601080c440c000003070103507500c940306110340d042c40d44620000c0c100c0c42c0000d9220342d240900d80b0002440c01c03454542100c5140b10200191202501c904482d038000b01d4043c0c2e009a8420a04105441c80000840c465486603c0c1d00b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 73669903 1250 73668653 73668659
    0x1d01020c010902040c0203070c0b0d09080310050901210803070509030f0304030b010b04050f010c11120115051017070c080c06040c050405060310020d02090d0c0312030501060c0f03020a0b010f 84
    0x4005e4485040d00756007550400c01100000c90301d0110880c1c1540c505000132969101c1c0f8114003001004807920181414902100340500c5d04102e010703103411990106c803985074690725000300303105c0749038800c54a4a405020b095410005800308011356071001381c60810505181d40540840d080c10700c2207100840c02d8000103801c1c004c1000514000c0c1c05070281c1c80c4000d041034103140c00706800181d10340803a41071180940c20402008844c60781e91101075805031060440b10075908840b406400d8100c6400300e514105000452581050440140c05901641c0d0b10f2420310031040d0309444d00e40d00070b4076560811140c600c003407001c925990002c082c0c41c0c001c400245050300d05800c0501d90421a6080702d885a403c2c02d040c89043da030000343c0403545a030314a00040e941d400d403200200003413148039003040d00f290308110102e0920445603045c0088a00840506401c5045103000314220b030400d00816000c42c428160000105c2c5c0301c00c0c41140c425101e8011500d44a58513151001c2e807142c26845020b419540485c28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 73671153 1250 73669903 73669909
    0x111c08040306151a160204110a030501050402090a03020111030705070605180d0302060121060f021c060f0605030c071502030702010c08010317210a0920131d01020c010902 75
    0x18502894008803521200d41c109031008404265580c8485114400030903100440428030b18407417201607000300100302030101e6410191454001c1c0c0b10600100b0b10b0040001002d0605000311114081d0040441b05c4840c10b5a0054480c1d51052149400c0c600c070a000050014108200c850b0140019458045d111108414415a4010345010f6103000f4038100c9880c0000a400041041c19515511900800d42c103103c20313403c03290000544082c2489080002150320300f50030340d00400c2c8900c40014140060000000b881003607889906c07443c901200050001c0203003c0c812005141c00905011b41c040c83c00140d07440d032401d0001d40250f4002070030740c008144800701ea02407080c3c4003012002d0610782841d602d503841d0500302100c81c001c03540c0d00b09000034072050a07a4422611b651650701c5440b212015050116441c8020500001c0450319054613103c007a1984a0007014000584c1c40201f404440c0400d410540e005450145401d1b6a1080701060003240700200307002405441202c5000000c00340e6071740c010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 73672403 1250 73671153 73671161
    0x605010602210903160905060a0515030606070204090f06060e0901090c1e050307030c0e060d02031f021911160f030303020705070323070b03070507111c08040306 71
    0x881000e5600600804039200c01c0c1c0210581000407003000305480f0100d84020034100294945000442d824580010454999540c8003e003d50005d541ca044803d880b8000e11050f1b10494000c03616a02c3c0500c0041c034540340400017040c00c5803010380049a5103013140c1d14448448880b030002c0750419100e41042c0010845200c41c9503012241038020300c4240c8464035048a0440680100140d44401418104054845880086c0240310140441d00910740d40e00700b12121044600032082d294642c0e4020804620b02220f0107040650003d01030100e40708074028071403042020941040100390280040d5001c603d00116000c071580c82500c804071403030a15001d0b103051440c8503070140501d680d04941408802958900401038a50500300107994540a04000380751207000d0b40020f0080c0625844100341d0202d81e221110740300b003010704681c0c0d040d4542031000a2800b088462100059041c002000072a00d60746a24118002c06040b4615080c025410b40c00b0800600340141c828143c005001c204100d0580300b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 73673653 1250 73672403 73672409
    0x60123070501050f060a030609021503010305071a0a050901030203180706020a11061e0706061e0302010e0109030b0a0f0b060307050c06090d020c09070e030d021f0603020a0308160b070c060501 84
    0x4c0b10740c1082c581040002c40a500901000e03043c565a42d450030110340381e64110b2427440c6c0d2150061074581da500c1c5481540c5501038082c00f005009007034055140020140d0541d880c16030720b030b1100c0341002005401140250001084c1804040c40b072440203440b01c0c802d0241c100508000d50144c1000d0342e080c01d06041806507502454021441006800028003035021101a038682c40d0200540e90141414507001070f00303054100382400210762140102c0b18540802e5441164400e0322542c1c4849584401528000039a10025041080d013200151000c0c04580c052408000d00c5500011103c40c00e00c082074840d0003c54420000c5070f000140c5d8588000c1c03c00505500111030300051070440034040c3c00a40b036840f18007105001e1a07078040803902d200e019860003e1a6100601241c900019000c0000c0da1410121000409601c40c20300340001d207101c9000304c1e000c0d00e4024140f80009841c555a00c003660b440b800d445c844c00c035940180d035000504014613450180c00a47e4620040311840d0030404100c80041c1c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 73674903 1250 73673653 73673671
    0xc1e030e0d090f3b0f070503040b06060903070b0c061008070f031101090e070e24032208030406050405060f07020d0f0e0a08030c0d030b01050403080306012307050105 73
    0x20300100710fa0603100c01c0410030754030082c100140d0908244128010940315082040d00c04000f0310000300c81e8001c01214600c2800c813012081d80c0c60b1204201030b205031100ba5070240c150116907001802500300500200303547c00740541201c0d00c1c80e9031881d03500110341112100b850305800401c01c0c403402c20340700e18910300602103000142080b107103840c180c141141c100340f00c000c0a0782080f0346042c40680c09500e000740200000b600c60a040d26107001c0040243c41600300309441038820301142011a008403d10f44004000c00240601c0c5803940500b0314007540005072108410001540b1a42c00201e8640145004074031420000c94541880d1901341e0404400515084000014070100301000390f00140752000c0f08900d08140c010500101801c54000031210742250300401c5607100000c1050002000f000411036200079124200354a8804809480c20003d49030b000400a200034804103aa9800854000038141041c80e00f80b04c1c4011018082d880e000f500d014031440c040340b00402c2c80028082c06900038101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 73676153 1250 73674903 73674917
    0x307150915110307030f0507080301090209030d1b080f04150903060c0201090c090209030f0715110a050c0108090309030d03320109020702030f0a050106050a0b090109090c1e030e0d 79
    0xe0744a030b40d213001c0c0c1000601004414050200190f0050742200d20300c0b038005184030ba6035a1641450700c0a0f43c04a04560f000c0d1050748405400d051140440c0580000300d4a910881e256290b101c030740150b00144e5003503801d22010000000c0c04050f011f2140b03207104051315101e035210700d142400012203141c0028041035904003103405000410030808141aa00c0e1a000141c844208901082c548640d001c5441c1d00c0e07105080c400728045440d03201c039022584840d500c0500c580301011020781c0350341c480c180c01440359010f842900107940c0102c281541c002d80102c1102d0074001c1000000345008204174203903000c203503108040030f42c0004241c084241c00c0500c0c608080711149081c0303170000c440707014490708429940c0842c0300b4045540074454030b000d542c90f0100311a003c0034503080c11390081815205507480340007a40700001d030385d05007601034a448050503112110180c1c9080c01e1940078040c0e19650f40c0400c000076034828116103180c0c0c00100840705e00c0d0360000e800b0a110b4035552610f03903035500060600c008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 73677403 1250 73676153 73676177
    0x60f08070609060f020c090901020d200405060f07120807120e061909080715050601090b0306040b040b090a06030b0105040902030a0f03170c0703031404020306040b060307150915 78
    0x818012030072508546001aa0601c00310030403410845101b40f425841066035091080e890015009450f00d48003c000400c00c03450b50500c464058070018503140e41c0c100041c0020885464004050b2003244644146149000015900d070050307542c00d510103c010a107890309211840b07a0090006070f0440702802d04001e0030f0f40e034103002ca40e070b001e0052070102041100d02c107910303101641d5000700e40b43d2607000070305135101d680610b05030341c072007248804401840340303003e000417055813040710700348216400b1003400392540d145c400c10300c00504000c01607075030081d4840c944041c0f41d842d03020085102e042400000107081d030561520207000441a405a48a64180b080c0d01c00075980214881c2880b0380c0c4040e030b021950b24146001e681140781308071000e96000d035810030031031014502001003038100c1c4259403c01041601d944440700401041d14040e425500c00c00c0003a0000300d0107d102078100c8802400c403222b0960f40c0354501d415105060311007002a000b5041004201c5191b01c0d101380c0c3da607070b90030f20b482154130b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 73678653 1250 73677403 73677407
    0x30a050a091a0901020c030a02100b19090203100f0605070b090607050f18040501030305180d0f060f0f0e010c0e0d0305120a110d0905150f06060702031002040306060f080706 76
    0x1040b14240b00825078400400c05140c0d00354100c0e4006101d600580781c58206a1201075100d60402c07041d60503840c10301051f0049441c0944801c940d041040301145081da0030302160704000e42001701034803401c82003018003103540313421201007500414065450329a48d5020b0328112041c1c450183c6042c415030300443c207101d58241c00c001520810303c03520412580750410341c11162002d0040400c0b140e00180307004008020f26070b10000400360300204400325a600030504080c04000f036050400a480f400140d40340c90005461a0444204403110a4011031100501902c00341113408141c2d480441c0e030b64903500c107101c4580042d15014019070488000d964911151000f402c2c5200d010200300582560200107405040c860780180890074420009503100d0400740311b8070f0014140759800380e600388184101000303031541d0038102c07070b00c10305000c2400c8900741c8466080c0189038003c0c0c04100c0e4103000b0048400500411817014100441c0990004551175180020020700c4c406290030030091a00419400d1241b01d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 73679903 1250 73678653 73678673
    0x6170d200102070b040b01030b09030f09060904020c1e010c05040b030403030504020111030a021014040c06081306141006050a020c2707090806010f03050a0206090103020c03040b030a050a09 83
    0x15a04412400403580036203060082c800e81d039000301140c00920501c002c0c0081c480c2018180c03403003402c840d49151550704510f0b98034080c1800c440b400074010400000d1a0820f640035102540340688054107055100c905282451a071500019a0031030040c0b82d421301c0705007405002100101400c005140ca414940300c8002444000c0000d014551900081400c41e40b0809076011841d80f01415a034881865420007074680508046003080c0c18107091414130140181440320740515401044603440328500745080d0f48408000b4042110030560b844e0060100c1c00d607000324040e4600481540000e0b01e040c5003860700700c03800e9801c12400c001c0705014005800780c001503407114225040f1402d0307601004c04003855400812140b1f00e000c288009009200c001b030380080b190307410f884290007641c919a07201e00c0c045020500c20321024240ea0711010360000581040001000c40c600107150251601e0301824001d1b1944d032066025401c04000001001000750341880307455001516504c0a000015082e11600810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 73681153 1250 73679903 73679927
    0x151109040e07050d030201050702060109050f040f0c08010c02030903070b07030801140d080c1605060c071e05191a03010b03040201030519052d04210201060509010906170d 75
    0x2960796049640d00480708204400081500610f544900d0182e40741c0203000e46002d039a19800352050382d002003500d10290003020301c05c0703c1d030100092503651584c03600c4040200e0b5034000d4800c0102000c1c0803030103680a01406642042c0364004554a480c0d22042c54038049580c0d00c0141d110b44144040400282d0068030f441c1110100202c07507450000d02c0b00040c4020107003120040241000007a202900748001c03c5103100c40c2a5288807010301c80d698003d000701441101014141600950300074000c0c890442420a040d00d044900c0c0b50305552a00045101c141e80e68100924900c4901c0040150074031718a4a4140d01007a83d0b841ca04552601044251034000900b0090515454000041c5d0224034000ca031038a40e0031150f4140034904101807141ca8021104180d143e21b40d4075030440c640b52000d190b040c107003d5a44001d50448080c0c890040042c15414444030342c0c1195200c11b000615a0b40ba4900d05019040c00e180004440703252009808601c81c2c0354482c00429005590022683c5800000803005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 73682403 1250 73681153 73681159
    0x9050909072610020403060e011505090a020c0a0f0803180118030e03100504080c010c17040201031515020102030105010914030a080310090f0b0f03150601200d0c151109 74
    0x5140b102e2401c0e0b508280700a070303183c039650303202080c000305000460f00284c05908800f4007c0200c030010340ca5007202c8881d54050b41c0e81115849000c204220a50307402007980b01c800c0d0007501c01c405103955420039400b421600c127690420004c001e02041d11000040e07214907a105c14000c10190394019101c41b06d0103500c3d100641400b80c3c41001006a4406200b15658001c880b0720400151803d0325200070b080c0c110202080d495840c042c80b100320240124002c25844140f003103026196500c1d98011405041d4540040801d019401000651802c8a84811303868280c00e4002586075818000010105c0038160f00c80207180c2c00c5040380842940340484c0040d407184d0860907440d6641c1c1c4907a00030400c05250b82c401c0d04514502094665000e030540d10100004404880b440108403158040550700c1e41c4200c80350700542c40750800300ea40c0350b00031140304414005881ca1f007801040c1380c1d4021070030038080440754400714210b6245142000b0200c2c400345ca504807500810081c190100b81c000500c0d0080d4241ca80c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 73683653 1250 73682403 73682459
    0x70e01050a0509060c0703030305060a030804051c0f0b0a110306061b0309031204091109030d032309060402030c041b080408070602040b0a031a010c060b0a150905090907 74
    0x482c41035088844200010309141e50700c841200c0c07115602d40312403009070300084c0303402c2c00f08219141514004040341d070007030781c00d5080c503040c40100103201010200c0c03524849081d4003400300040d110050b550711030f805444050304a142c1a1540350030345500d00520aa41c02c0e04104102c0580c0d603443c159004900c030068a40c581c50309640380c1919500c900c041040d403506c94480159802000c010042059a0340700d2824810501c58002c0c44245008605100368103170001030aa006c0c6a102c1e51160b0700025003403404035403015041c00030000084003a038110100781c20801c108015803c042000400d00441510100010000f00ca0b00b58104400b4503e80801c22a10340d002c981070103554015914846c3d00304108565803982d803140b12100398040194000460308095082c1c0e4440400b2000300020281038403840c0d01550a60b88850013040c100301503035444130018401140e03131080b5064070100d2211076290b183c0401d08103801c2180c0a030004001d0f152030343c0401d005000014889540070405071241440c0b070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 73684903 1250 73683653 73683667
    0xc0603060b0a1d0a270209030312040501200d050717071b020306090c0114120609040305070b0f010501020114010302031504030909150f0501030c0c0201120f020f03061008070e0105 79
    0x10310480803991001e5000f4600341300443c182005c03072800302524803150403101e040c1038a483c911069000e20900304d549600144092200500003441495215114800000d0301661007280c2e50301460054201c1080c10901040c070a1410f400c9108840d003180e4281404100030781011000081c81c00000c1c17044040201c421605114040445003042030389038010199102803414124913992622108010360005000090a03120402c40c041101d40180b10190803144c00d80d03492042c000c4004014004504102041001102145800103164010310707405000140d175501d0603000a0944190152903816900c0c0e19004000503940010b4115a060303090001010a40d558102919802000e40c461484d00f801c12002c05100210700039494103681000100c8005a0303110320045040320540d020781c401085010303c10b20003560280b00701c101c42000801d00415035549032200603050743c01000660302d1140c400700030b000070352030030790240d070590b07002c91405804c2d41c074000300002e1482950042c41818410005a06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 73686153 1250 73684903 73684937
    0x20102030402130b060405090f1f240509030102070b240d0b07050918090601060903030f030e100609090b090109050709050604090210020c040c0905150c0708010504030c0c0603060b0a 80
    0x30f86e00410b0014001c64840c81d040c00c4145a041c001c6407031b0350f030580c0c00714812481d0007034030582c41d4151a0004107100180381500003d80f0038200700c150036410b20000f4080350240e90341c240010440c903482030f00044081e05090004804590841403500e0f84c0401042c49112140c0320b0841c4510340c9030b00308246a11503140c030001600c1521495440c2c581205502070a44000c0c1000e00c0355501880f2500c0c200e8643d81c0e80c4400072504041135020040c00118030b55800c0410521070b800800640b00140191100ca018015603038040341e8041e03002072070107a19903001c041807104a81c1104c1c1d21400c10b1000380b00381d00c1e4954445031189244c1c011642e03c1c030343c1c4501241c19030319184d00514010b640545003810031031f07001c03502958900700180d20501c00c40c1000c0d01c50345124418201082159001f6214410950301d01546030100c3d0407180511107688129800001c0402090003194003450003511010350407040742c02d00c1e103501c00c25600f00c41d0034075040420801c618100310080703030641101c074078200522098001c030b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 73687403 1250 73686153 73686157
    0xf0d020612090304030b07140306040b0a0915080705060c0706080a0f142e1701020c0102032502120403080f1c0c02150603060c0c070e25020102030402130b06 69
    0x40c1d0300d440711110081002d224000802081644d00440b0000400e5480c2841260005140c3c02d031041d11f01404d002240c128100380e04001035a010003010701d1080d903100d140001c2124240e4846211804107514100711100c400c0c0880300c0031300380c1a00c00754581000c16034496541ca000b03200d0402041040380005900356000e0380080c0c00002010402c2c0145c110780d0041c001120340548100000300b11a01144118040310300d8040030188030101e215060520306100070030b580e038000b08090354554003042860412403080c80110300c02c0e20b0410002030138040c500c0760002c61030340003200300301554884020400c5005030b40701030740d046a5100041d0390742c40302c80210030b909a00035042901d401000b450f080c10f011b42e6031900720f42c00c03007802c0307508680004038010001204c0d0481504d415070190048170106010b0907030351004061071800c0b102221800c0b0b9031451103003580c8000325030707511042c9501d0754018100c80c00c590405007011442d00c001d40c00c5040c41d400003150000c2880c1e984141d695103c60400440d114101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 73688653 1250 73687403 73687417
    0x3031112040b03060a061d100201020f0309071409090c040b04020702030105070801170a1109041e030c020a0608091f0b0a0b0405100906050a110a0b070c1a01050f0d0206 74
    0x2820300c0c0c0715a81c9140b525642c0e002540da03540f2030300701c40f100407035003902c140083c8684e5816400c0809a010301c5100b4006011030502006085540070050380c01c00502076001580900d1803140208149894100400b600442c0035441b184261820800e0020705080002e100c040040100d0300040d820900c440003800a20500790029003650801c4100002d041d0403102107412600c070520fa03103000314090b20825848904036100100b501c544004e0b824580d0808888580e0701070302c11859440c5848000e100d600101800da0011000541c0c280d12170750840c1400c0641c07400030300040c14a011030741026400240c444c180701500c0b40c584900d14004820024660300008101100588812440b80d03e45e469000300394000e0003040e00514080d850a50a50701c41c001410403200640d8805082c00c04c00002206d82200320801c01215218400042011070f10b03d0801c40d005e041280c41d1129030380801c1c948108150056500260b83e01098030040109445843c2001c10b400b10844000c165140103200052807030042c01c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 73689903 1250 73688653 73688683
    0x14060d1202070914091b1e040b0307030f1406370e0109051b0603180307050712110406030816031205011202091005060403021507060e0d030c0c02060301030311 70
    0x1c01c206001030f8074035049a004894002c00e83d2070310641b072038880f1008881c02040a80244444000308040244182d07504024100200007080e40000c41c000070345842a903401c00c1d102d8070a941100c9003006009881c1240010f10350001c0d204500e42a284124620032601c5081c1f580040c40d0303a8900d515481048110007154900350410210082c240810300030480d0a100321040d20804032210650701c02108804030b8004010406481c60380e0b00750550340981c03000406259240b006101c00300000e0320610080c0017510341c552a9449800c507504241c0e90003059801740030f01a5160507804d01c0880c0304102150040e251500aa8a06020900d012100d03041310204451841d8986070000c19612104ca40c940c2449008440f0440c881d203c40c0038800d901b490b00d10a1030f9000c0410401040142069201000e40c50301411106003492440d484000c01d40e48801000c103160f4201c4140c0c1040550107102d455940c00e054502102c080310340d039003c03079018807043c0409000e201507404c043d42e4419080010300825540d02c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 73691153 1250 73689903 73689911
    0x504090503090315060a08010501080d05070f06020d02120105040b01080606090d0b010f0303020708030c0a0f1e0c090c02010204050f0616020307090606030b040203160c0201180e090114060d12020709 87
    0x3404c01c42e214141d40d03032407040e103403d03d00050300201405014140c0c2d1220000d004140003082043d2a5503215280403208401c48400e900c012034101d10190040080000300581ea0700e40e50f24500380300345c0c1d05030003042c49289050305802c01640d000c1c01c01c2e54010000d683c010b42c3c461905000401c980b10000009150100d4800045905089010208201c038401d800315801da64a8190841c1c40707000d0a0714800d03860f8005c0780402c002c40e5081c1c4141d40e0a82c040d21210851000e450201c8120400c960000d491948078800c08001201c03261090740c0d401081d6200860500e818039000840441c2046001031150002080c4220b01524950304c8006087d401000c07034003429a00c481c1c00010309080d02c11f0b400400d250040608460815008480c802c80380064a1610501654801c0e5281d01c031460b41039040001c03031a490344061503410301d540081d203074250194000c0c1ca404902c0300d080d1043c01c0c000d441c82850801c00d0001c03d45406803c003410586c0700070805900105c8003000c91030070f161a44000340d03550030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 73692403 1250 73691153 73691173
    0x2031c060b0706060e06030727020d0f050403180b0702090a0204050406080a05070f030c030b09011401060e1c0c03080307120c110f16180b04090c081902030705040905030903 76
    0x804c0d445041202c1d0220041d050641c1d405040581720911849500c156801d1050b00f61200340ca41a80142c460300d0b0301c0401030a2448070703540d20045400b14080012a144e4680921080c91340206440507841c000d036040e2000d03941401e0224400c1c2c081c000e8000d000311200c03008296a0314080e01600c0c0139100c09441000000c0c0d07a0a256507032221f00076402e031510b003e1000007041d04103511180c48152a08241e03019032461966827610445c100c020500311541d586c03580540300c043e0a105001340200130759520381480c1040c101c1081518513420a60042092041000800003040302d0719600450f90841e01c61610796440c120240c8841c1000481a02821700e0070000d080319617000501c0d200543c00001c101c03600b00311902d079150fa40b0038900d24000d0102403080003c1140c40c190248081c140007100c01c020034011400310120781610103100003107502024224042c00100d104219070201ca502c01c00c4003110454051300842e880e0401c23801140c1c000c503152001d13542884020411144440b101804440c0f1940e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 73693653 1250 73692403 73692413
    0x6040806070201090c090506010503010e070e09010b040801060801020c1009050312040303091703040b060402030703090c0308040e130c05040b04021606060801050106020f030315010e030d08060907050a02031c060b07 94
    0x2051a030105e60506003194041078048040c480e0321b20514040e1295032469082011031501e9110080c0140100040c01e054480151100000a4002d101d101312494903079081624040c251a0310f600800040d81c03050080c151080350014100b16102c0c81c9010000301b048260500c2402d61003044008102da03d9a0400c4c0300400d5455406805843d0150584000342070348180c0c110582d210940d00940022104800304200380342c5170340210f03089903203400c0004070700f0300555407850128504c3d801651034140c0440c081003801c903180c4030164404103203164000450b41e0740c0e40b074941ca00d5240c016140100e0b510305a4600725207855040342e211811040d0380041e03441203490a036010342100e00030380d0021750800000041c81c5000150b0144400740b004055070a6a0300d6a5000002051080c2e289040111010045003a514280502400500e01e540c0301c01d01803400c030042c81030a850240030f50040041c104444082c10b070f404415100c603966042d182019041c1c04d0741462001c0c118a4010110103940000d040f41086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 73694903 1250 73693653 73693661
    0x30617070501230307030e0316110a0503060405060a0c02030d06030501020a0f18090b0a05061908060a030201090314070504020c0a050105150603191806091406090d0e06040806070201 80
    0x810903a1880308420312a03d1102100c0741008048002500900c081240c0901a170408402075115608032810041e8900d4014001d1085207000d0b12480343c030301980f07011414074140c5140541010b400404a90030955280c82d038400c802400c0c14a50b564030100c00c000e80d403003802219002c000001080c405e81c2e0310307402d0881c001c0d80000038040c045641c18041c005920300948002803456604000740f4801841e0007a054047c001900c5801d1780452000c0001c2255074641010f005400300c607501041c2c1d040c16154025004420140c1303224401c8460390401c00c0180e9110300d840d0240c070344c04942c440c0da1180e80140c451404086800c8103034010700204003070f0000400000d1000306140110024807041d12072102464140408003406504601d0800004200c1700c600011111504012080021009004940140040e0b0030702170481c0c0250f00c0340514014840c080b03882c000703c90607610180850782029281d81c4d5444400c43d014805206039190031007000d41e035542c00e44008102d0300003a112549081d0714001e00030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 73696153 1250 73694903 73694909
    0x30c07170307230f01050f0604020c01020910050309120403050303042306180c0108010305030406050f12040b011a031005040e0a0c03122a080304020418140c0f010813020103061707 79
    0x280c81607040e0840c206005000c6c4c5070003560b9410300a41e03c1e403195018030010754032408480b030380c540d02005018a1503c1d408203624455009075146070300c5e0b06104030000c0c18500d03031811102c4906414042880455004811a40c20540c070050300e03204c0f0460107400b1681d81260b0001c0130100c0c010402001503042801c103030f40846041540903100c8003c6410010740d80241c0c02c1c000500704d40d101344018812940140010801030405154580c1016400d21038a81c448100310f40c111003000030b9600400601e0b000c5041c440c01d290f4040c01385130952400800541c80c2d001c003841000e2065459804840500c0001e125502071039820100391101c07030787c485c00c04818015040980c5400603540203904840443d4154904003000c1d0341c400d049201030000d8841107104e07003001d003099a1069407801c1016881202003441c04800d07108218190303c1c441c5602c0c0b03e508142d0342803e114000c42d90281a403225030390104150f40d01c4412000c21614441c06800100d000b0500c0c2d800104070b054180196085032100021a07c0031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 73697403 1250 73696153 73696223
    0x90911030c150301090c020102040f0602010e0c010c1a0403090503121210050d03080c09120d09140a060c0501020c0105010e010e010803040308030a09030c080409021b030c07170307 79
    0x440308402060004041815402045204007480103000d902269088111006c810303100142c1442e48407160b916240e2440c0e403005c409030b95240d000e40101c040a2240c072402d01400d0034150804a0036844051074a4240c284400d2414564400030301014026400300d000750801504a59801d60711441c00341c8650f000004602c0804182c000141e040381181c2820800c0c1eaa000e8810055800d1030343d0b042d03a190002501c4019244028003520b00e00340c40700e48610310360502c0100100620740b441c60000e072203600e031038000c500040000c03006003000b52145003991b011100b00d45841e002c45925400e025009018500029440d5424040000b030561101003ca5058030010041018141d0ba5842070990380d00c5184001403141c002800015801c032040e9003c119002d0182c14520000851907543e11000d6206400942d600355011a50702e600e010710581c1003080444590041d0300c1c06580810f2281c0da202d140c8034160809149000308940c484052040e100369650040d8107560240282c140704521000307501d0a110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 73698653 1250 73697403 73697413
    0x905121201080304061e0306030f230f190f060203010b070c080109210e030106290403080919090e060711030304020108040b0c0c030c01020421050c1909091103 70
    0x5100c1030040121001c4030035035107840c000581d08000c5400c6e9058a110707041c1c181961103000001141c1d503180c420031640c0c814501e192420740d0080e035202c036489042038003c3c21a07000895281141d90001000e00703d40c0d450710030080e0385070224a0300a11900e600c000c000c4c030560001c00001008c110b01c41c00f40240e50f1051031800505138403000607500b203920556018261000c150715108032020440e440115800301c40c9040c80b030007403501001c031b401d4070007941c044592000200300314010304022100301e0325429940207079a8076052031134607110070302c0c0035401115110f501080040c07a0307048074190000c001000700440600a00d01c822251607242c078021180400461013014107514010004000c50341300d01e60507115012a619507880300b030a9004000d000700d10f0301a080000c6519500f0070030107000050800000035940d50b00b8280115461114000203501c1303034140c840101d001035800700c0c003842e90090903150141c010300c3d100401d03504000b03d603105c40e0f01030b031518101106011045140700c2003503400350f045131 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 73699903 1250 73698653 73698659
    0x406030c1701030b041a040507050306060f0102070e0907170c030c040b0904140f01020c06090706080103030801060e011e081f050609040b04090203010c09060216230102010905121201 80
    0xa80c09109060308401000d1241d00140b00086040b00c450360090301900c0c500305403651005240102650980c0d00341c900381c4c054181040103207404c01409600400907201e14003081c03203a00000c2e50342c0c0040d00440e030b405d0321600c000555456040240c803000b40710003041003507034596601c03a81c0c1c2c40d42000305ca0107000380a4040c02a00c141042d01480c840d546001e01200d02c0741e510790b00c1d03220a183d00c4e00212000c6000f07640210014043c00d0010749000340901c4094400c5040241045242254070751000060040314001000402d410000060444500703041a6042007d000d0040b0382402c00103020b200080d40e02c004d51003d00d5031020340140f2034907006901c2ea184180809901c54400381e5840741543c880000c0081032030501b041d82000310b0707501002d440842e0300302e29075000a0a45d40d009540400150b9031007410845039038100300e008640b2040030403115107642003403407465900f0003410b0401e049429424400380d059100b540040310103500201524070404010002c5003240d032000440300020b0180344004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 73701153 1250 73699903 73699907
    0x60504020f090409060609050c0406020c031c081008030406030b09090114011413050a1407051305060703050c1b101107060e030a05030a0302030402040f09030807050d06050d05030406030c 82
    0x116024000301c40002c1c148140c000810000c0e003404001110f48680354000099030346030341d006903070241c2207124955440d28203040c0b009242201603101d1b107209030b0014600e10606c02c484007041c020002140f800340900d5417400b4568010310680d620074080d0344000a00020456410703404540c4c035001c112078139400d42c0c0710074044500303840900c045006004211001000882e9001c242c0d05e012a002070088a90560030bd0554411910102c1d4414107054640d100151640c24403189180d000289040c43c0341405480241c1030030103c1c50380941030042e000080c0e080c041c07600900030780300110b070304904071005116024200e4902c1d00c0c040305081d0080080380a000c04850050000f03050b426041402411224600072049900741d00e03200a01390580100250140807070000d200404070a1240d407005662400d0a2050100302c1e2070580345548124500070030800040e90000210b5003040c0c042c80c20f40d480d2100c0d1180900180a15401194441400f2401d2800c110010014104031907183d10100228a515141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 73702403 1250 73701153 73701157
    0x405150108070503070c020a090c0e01050301030f080a050f070c0f0f06051e090d030c02010e0d0209060906130603050601090608032506020d140907150e090402030f0d0f0306050402 79
    0x4a94042511a40081d00003842040a10b611a10318a0300000d03a03919078020075280c0b000303900401111905c43c03090448503508503202c521030000a10300240b85615648070801e04080c90807004210100c000341c15520786205000b07a0707298103e06030a003541c1c2d00340d500e0012482c140c02d1080b4481d5400740c2c040080d41501c2003c902c42280c1b902d449491420130f850b2141e150482070344c404503092802c01c0c0320080880d254101e002c44218440c0c2c035401d00c90352130b6000240c48406010f0b4a41e100c6c174455207201d80140c44034020140c22250941c0c0d41e603180c0d100c2000041d030340c103640c90b00d007444907240000000c24080d00242e2103040321800081048000d0b100e00c2ca4945038819070242100560411a1610340d14151040b11400f080c00cd000c0103060096181181b820f68800c0d2481122b005102010321824500c00d02040c801440840b40700b42000042810240c10341c0903030456079206102c3d0100180c00d6480502000329020307050019901c1c0c003204244050183c07603115004a002030314005000c03d140c02d144c82 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 73703653 1250 73702403 73702441
    0xb07050705031b0103181a090c22020703110f0717032b0204030602030a020408100e0706051c180339051501030309091401050d0803060a080a03030203060405 69
    0x5a4100c076001803c019030107001c0c1c401015030803c240090f0700c404106072642c0800714882840014820341010b04185103000107511010740b0541c0f14003540701440301405203445c07894084007805030b25629141801d43e103400303811b0000345003800351646100c80311102046a106407880c07000f96092981c1010481c503628020f0801010000e48140c0315803541c41d03502841603050f410581d001616180e1070340e0700d84013070340c00554048500680200b010700070618140800c101c20071b4142402c0180e1214a52805c0c0d546400c2e00c10003050000000d26211220040d811004081002c408184078600e07041c00000100011201e0643c0003407194451141007101c0b01d80d0221900c02e00745150f0041140d80e6001300c001d80c00110707007203c9a01c034407031804d61620640408039008500a440e10001c048c9484180010340e0707814110100c641d200200144026034800c80840b0b072480d00701d0721481d101c2d503417000498100011a004141c1ea440307149804420554540c00641c850001594240543d495205d03452204280d02c2c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 73704903 1250 73703653 73703683
    0x605040509010e0603120a02010605090703090b0601030e010e030c0705010806060a091e170604290a02160b0109051e01120308040c0b040905091203130b060d0206040b0705070503 78
    0x44010010f03c00520340301d80d0044001015149095915840034103541c1c400c90311240035035140c40c0200b140b441c007610503943c000c00c03505081c403220840b60383d44d00e03924500401c51414540e4500806281480940c040c1c28238140083c22250b840c1031031103446070385034020302c24640003e43c40c40000740c6030301703000e01600c091005544805d4292802e06030068441c18050b00103580942c446040010302d01c00034011000060b022401900541c2030900300300c0060701d400b18014548510345d10110121004055070740e54000f480c00c400507102e4041030a40700d481ea0007040d0280c91025070800204001810390b000328000c8020714100d040950341a424203100c94001d110300041c90281c0d00400d004603000350711041e8001d06c03034a00340c40d56a803101400c4541c0c1c0c00079000300d121355565808001100a040010720b0242010000c20350451030511201c82007040499001011541c8640104180780c45040710400c500c1e900604140e1990b8440b40308280300c0d08114801c0d00c0a2041041c0020b00b8280811518202c000003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 73706153 1250 73704903 73704919
    0xe0711030412080906030703050601030f050709051201230a060501030b01120207020a030501060b070203010f0b09011a0405041e05070c11060a02190803060109060f0503010303030f0209040c030e0706050405 90
    0x141402c200021081019202a84200403900003139450400031031052800383c8000031a030411400042c1200c4e00141081c0e081c1d0703e80002c1c0103070140c1100d000d900b192800c0307840f0041d90100d10358050140104907106050040d90b03802540d02c00f0005000c1910901508004100c0d45545100450a5035082d00582e40421103099a070f2100ca40c10b90018141d1038009010b0451140e52555401d0850700154031030303025404041460011850700307000d503000740c2016660902008003040b0018180c01e106124401d45d21841c1c0064907003604546042d80c006040081040014025000c0b4442d2010544c01c2c80300700041c5440c0c0001c0d01d0130f0050014910150f0130000c1910004c1460090000326482006000294030400e00b00fa807842d2440c5280318482441440d2098681c00c000f0000f400d258166000141840304168400c40800d501c003040d2030449416190209010041e503c0701340c000d10803450740c590454140f005030a01c1030f030076810510700718040e0001c8488803959000211344d540541c2c0203899101c195 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 73707403 1250 73706153 73706159
    0x2061f060309020f1002160b1306050a092d08031606020a0e191401080903120a090807050a030815010e090901020f04080601080606010e030a170d090303060e07110304 73
    0x11a40c40214494406421303a0311240340c440c001500095440403690043c1c0c815101c00c60a8a1008403901c0140688240ea82c180790107450380c100042a507004d000100040811810b000b0b61260004000030300d6020781a6184050181054900d0b0302c000d4217849813101c400d0340000d4500c1001049030304001e07000c0e54402c42110b182d5a8040030354040c0340c0780d000b0410101d0540740c00c0d64800e41407081841451003050181072811007084103110750342c40100d040c0b100b04410040010300210460301085156040b620050f035a41d10500c00501100714090810800400d002040100001c0c6191226000e41c450b04031654540e99410340f00c8070103940c024000ba8503140400c01c2e074207002c112107810040b080700150810b901001d00000c103412503440701541c2d03480f24004000d2088284034158110800b80f800002154a0320040303961400303e0b003002050403c000000800900344401a2034000c07240c031100780a20300700c0d803c0040180006020f000c80036240d07413012803241402000d1280411200001450516103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 73708653 1250 73707403 73707407
    0x6010f0c1113020a0302030a0b030102040f17031204080306010e040e0a02010c11090c1b061e04030207180906111603110307020a0905040615080309040c020c040e0601030302061f06 79
    0xc022440aa00840303100580402c40c1e0041c0090103121410395401a2285041d10740ba006548108651a000ba481080140158040200b030301042c0c515526a03015940182503015103107110302600c054a152641d02448100f0802200440c00340409036110713030024910070100320071901948200c050b294407485010006502804114040ba402030164043c00e203601c1010a0810707404840840440900150104514001400307141e11018602c2c0145800c0c03504202d2040180b49489010907200380140000d01010700c00c00c4070348090020360032003101000e44842c1d03800103440c071040304440c2c060900f107961718190780070000e4a5201303e6002000c5046022030318107640c02442d003005081030f80010055080507860b85c0080800904050340b00151526090030803400b25661101c2003e00e8a500000801071011700005030380348100200e5000490503903004050b031420000d400c10701d4102d81449118a413801001c510a41281c1c001c0d02034451030703070b03810344103c01e4124860100e80000003044000e204140c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 73709903 1250 73708653 73708673
    0xa0b030601140c01090305070c0e09030306060d090203121306020604020f01080601020a05030429070314090f1201050a180804061409120c01090801091703271506010f0c 74
    0x1c0000b2000510f0036902c040340a080d10f5040c0d00c20f034045030b030001e030340300c1009029483c21004241c140d500c868203080181e8140e031030b03100107041c280c480c810100703110104050542c051070080750700a0072900140d185802040c02900040032003c3c4820084400180083c004140766105a5000b050b6440e1180c150b00152004100985482e04500c560b100000000e03d04000800141052909074150816804070072200e00d0040308604250040500c524000640c1020709861100b0421407502d858000c07000105030760302000340c0d40552202c40e140341071076580410750000d802550450b10a0040280b0003810000700314101d4001040c81e6130401c010400c180c40303030400103030343c1046c02c5245142500d544000780504844044a400c2d0350085080c00d00d5541e00800680d00901c0040000d010004040d00d03480f0740c0651400101008200000000c1d81c28190146044044a1040012003402c80c4154050399502c50781208109070f14041c101088140d070061903130580b451001e548180c1d502815654038003101c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 73711153 1250 73709903 73709927
    0x9030807081309050901150e07030e190303140a090317060102100908090f03070b04030b0c070f080307020c010e09010303030207020411031e0112261e0a08060a0b030601 74
    0x200024021544041c0c402c4a800c00208260440031a403420a068664212980c0c6031400300c5d5000c2000080200180d2040156030050f02800c000405014501c0e019050240006103011000a4100c490080603015402072546c480782c09a40103003640c94074440300842c2c0f40c003c80903000c40c02401c40c5034145074403818480d1f800304040c8140c0c1c5619048a5450060323400000c4105d40112002c0b902d0202410080c0f66140200c40440051202502d40780b0341125510032400050301c0d0445078000213000600000c01c4441003588015900c249402c40d00300300c2001c0e001516814018040c02c030250b00d00398801c0305158040c4ca0014038103a070350b919540e01a4000c1d0720001c0201c2e0040d88991154400c0c0003200701842c400c0c25001c160b0503485800228240d80f01070142c05c1018040260007050000c1100307210107000205603d03030f0b5120a4520313400607107014000c08803002d80e036004506001500302650030160400d440591100072082c0c852004001c0200c01d9801009004207040c4002032a039881502c0207500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 73712403 1250 73711153 73711163
    0x110607051c140109090204140105061602010c02030706080f090c31050a0204050f060f040e0c0705010509011422170408070e0601080f09150c041518060c020109030807 73
    0xc440050500d40b0320440264404441160740e081210b00354205400b40c042d006807050704420040d030500d40040d410b801580c0c8000c0180014403a24001c5900801203842900c1d001411150166610800101109070490f0100c0c00398210b94003003070b2880d500284800341120010f002c1d244060082824030400000c100303001c4082e50b99505070385100001ca110700c50240c2c0304401e001da901c3e401c1400b48007800c5142031600b070103540b04000e1aa0b00c1c0c410304050b1000d6400c100800100b07520380f60040c103258041d2000141180d46024140319940105601c1340b130207026142070071803c0b5503030f40c2c48280c11543d40708004080501e03d4440c1c800000da84440041c6803503a045241410b240d02c2e00b8a031464001c0341d4010008152800060050641c0c10403000381d405507901c10250142d26001010340d880f101400d108054206c0c245010880706400c5005071000b411301034852102002190000420304a188176400038008400d08000c1071032407082803406181501a101c04040a1940d91041c020380c0c04804240d071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 73713653 1250 73712403 73712411
    0x9032a01050d020412030c02011e0c1104111605010b010c031d0a150503060301060b040515251a01090507050f1c0509070311090601090501030507020f0d050703110607051c 75
    0x42d8280c401e01c89400c5c0d2a006e5a51240e0702842440050941055440d4980440001c0360002108076440509104115442201e0168500391080850041c0003c2000514000c401080c222690044c070119004043c0c0a600207110140c003400041d55155410b000150002c0c58556001d0a80c5006010451a104003c0e0155002030342d18026100c1070340200901c1400924008140180740c902405003101401140e0104c0380340500e00307400101030544e540f0805504210218418a124080202d400c21028000c003901c0d60000e494688503a42501c0082d642945000c84400403811009900c226881041c950300c81610380890710740c3d0000660411401c0b050030451451009094a4882c01042e00070320050b4002c281e0302d41103141c40340721101040483da005429020030019a41e03800100c01046940c2030030001655160f00d40102e041c28031500b509501c1307100c2d40c03409200c05079000000740201c90099550001d440c40100940362144826078030500040c00c14400a039059142c03441039481a412031030002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 73714903 1250 73713653 73713659
    0x3020f0d0b030f121201050406050307030b0a0212100302011706011b08070f0308180d0f030902120a0305030601020f0613030807050409060f17010506030703140115080309032a01050d0204 82
    0x82c0c603021150400350078000021540c1840d81c5030300f207017160140008480c00d220050a003c082640d403061848054079003001d175008101c0e01b00c12030341113512921400c1c4205001c0d18042050420990140c40100d00044610f00c1100703500254952040c000c1205070340310181031070071105020180b031072440c050b91025020081c400001d080300c121070605c1d9100b602c0b042183c2c5000440d00b000ac0156448103500c6800c1040381140701580080781b282900414100010b0148050000c1003c400c0c09000e4004244140f001880605421030b01451281c41c09034200c4d25010605620b071512224140c0d5001a0311080c2c200400000f800380b05840d602448038508982483d64800303000c0103036255584140e54401034400c3c00e00c0005444d9000c03450406102000f03005506000d4086030741e0b40b00030700c0040d0841280480c03c0840070000e401810201d0041c2452450700b0b901c50142644aa0203501d03824824491100c0d0044c2e103101082e2200420000181600c500d000040019a4107030300402d0742070440e40d804c00000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 73716153 1250 73714903 73714933
    0x1090c030209040e0a050c0111030319020412060b040c0504140d0201210509060612101a030a0b0f090a05061305010204030b01080a0b0c0f0a05160206030103031e03020f0d0b03 77
    0x50b689951300300e001400700900c10b00344a800c2920010441c0e0402c50b114000140c562000011240c112200c00002404204014400002805590044040e10030100000418810a0f40007241e205004580401401c842c041d030940e80351003144a8062200310f0407004680610740707e00f02c00103490040c1010740b00d1a2504040109c403086403001c1400040c2d4401c00d10168840410010740d00007020398000d00881c02d4021041e5661030400e400404054840140c81d004148505140303040c80c0000e01100c400c2642860701808404040f00c0c9800d113074400000048012000041441e1002d4008000e48941d40b10561016040c1441010039100b40d0340801000000542c40121103008002250140c40100c003e450030840e841c901610000354550280804880341032414121000c0514506180d0f540d40d50b02402200a51980703000a9400700d0044000000d00d07820814851020380310780d0840d500100ea015007134049004614901e00c2e00003090050744940b640030b900260112000400b100d03a0842e82c0d1a00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 73717403 1250 73716153 73716161
    0x2090409060920010c0c0e0711120c060615090108070c0b01030804140a081207021f020309010207150912020301090204090302010c0906090b0d051e01030507170303040b01090c03020904 81
    0x11503010380010240700e841d0203400f8800c1400c03002481c0c00c0c074203000d65448201e030f44c1c29a401113136600c0303003420040350002e0b010b0411032a0303248207207007072700da50080c0b41140312240c0e04000030b0b0314014009c441c0010740a140c001070400c4c64080b08102036003413100010044502000c0140201d00380040f120352100818411481c480c000c62203524002c0d5a0b90a0440413020a0205845a030007100c003004284040b01c400308800e01052108500c440d180c2e0070310f0000803a2284c00740b0600c00041101050084510ba002c0002e0030383c00800e800300e03102d1503520100e100c10441560b40e4040041c1446070f040c0544407411303802d41082c81c0002d0004ca04d880141c0c000608485403c00c044000d41e640e00051501150818400002030055041c036049840ca840f11020b0b0314412030400044541c2e6900011360089503003809811006000c41c102d044641e103074a45180d507070000d40981500120741d00c20307010845000004403845154005030a024070303440c0001c6200039014001402090540a016045e4030392240e100d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 73718653 1250 73717403 73717421
    0x1404030c030201030b01030920030109020414010617070906080411060a080106030b030d020601172103010812090f0f0f03010f060302090f0f13020d02100c06050c09030c040209040906 80
    0x12880e14510b10014045a039031240860500d4100310011000c00d1644031101e4218815906003052200c038007000074010304495100941c094034001070480e5820146010714165a11a16400c01407134044840301807039139040b1040703000200d90480030300c41d0900c1291200d420610500e180312a0301500400607030f150300150f90420004130f050004020303050341802200140c00003030700034124001c4003900c000c0d1124014020320400310031400442c01c40510400c040795804641d440042c401c1c41c48400440038580c400e101c2ca0b03929200b103134242c541d04204042118000c980050803a5000200340f401d1102c1c07001d4855803594420b4850b048250a85c81c2806220000765002c1310024950781103104001d1501c1000d41070301400090042009101040e40c00c0d102e410018000c1d40100ba01c002c2c1c40051641c901c2c86100940001c00b5407040d402440e00410002c000030710401c0184a503668101e0b000b080c134025540450342c5a800300000c10014103080d4010300e22100d02070804580f040441d00c5150031b454600e5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73719903 1250 73718653 73718663
    0x602030c07170712080909040506151e100314010801090311010603020d080f09030706051209060403090501180b071202070602010204120b13060905070515130303050307140403 77
    0x103801903080506014440207030220180707902d181c0ca4460341059880015020b6076007490b42008610052103c03140503a40c2400300248800d42d41c1c689880c000d9142c0301d0650b8030300c40d80070146100051514012038146030303011035060900e8500140c08100000f1140b94406242490b58034481c011640404451290182120700300200d040582c170300e0000c8c224240300001084c1c03a45003d40510050750b40304040c0302240d800411076900c800c00c14081c0f1070140700d54a0480d038148142c4400140140c0c00c100684140b1444024000306991032075903403070722080203d400800180c10b2220500c820341c01445050b0003a15074210500c02151200038200359940002415550f82000c1075524003d640e04020140150109100940c00c003441c1080204000c4600c12000b08282d19460024010003035480f11000c03c66004002402288001e0400340d41741c20003809000e0064807001e0048540c0e15005049904c403640445940e04128695103080700c4541004d81000d0400a440000d02c1c00008800090000b4501030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73721153 1250 73719903 73719907
    0x6110c0d11121e0303010e06090402060d090c05010801081f0f0603060510082b0e060d0903030506150405030c0603070e03100204080d030501240e041a100206040206070f03050d06060203 81
    0xd1076203543c210040740d969951a8010001488080c50040100d03400c410190f9003240f844e1151720019000717020b6083e40c01c00403481c0ca0030b0101800071035003000045450a07261b800c1c040c1d0301c40003150f48814041d00c1502d82c602070351405407840599548600202554501e001442e207450b40d56640683e8010380300d044001c5080401031150175418007000c0b00145c498000640c5480c0140c9400303c610740d10001da00103106c5040210f803c2c5444070022505441c03513840c001c000e207048501e00503004080907950203028140c18005012002800c2c01180c081e00c10090042018035114020030035260310041822041121aa00350350048e1420000071010400c100405a1150300f41070b801c83c50320200e00b201744e00301403c000c01046001240451070100b001400b02103000286200c1c02500d804501848003030f0011324181e10b0940b0340c0014001241c28003400c8558041800070020126651901640c0c007945c003140070000080003c0740c00d0185a526071081c180b031420114542441c604441080e88003034056000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73722403 1250 73721153 73721173
    0x103060f090204090507020601060c080304030207150f02010e0102090319050a0210050a030f060302130906110307030b0f0f01090b070f022709070e0a020c0a02040e0102070c06110c0d1112 82
    0x103a005d080d521a00d0f92004040342d41c034125006113030b41007840020b8640e80340080801e0501d0300c2800708001a25062607030079030310008110020700d00444409010010352070603005510025040c000c0f05c2e40103030018020440c1f4410003004801142c005181140c141c803600e81c4090050300e8500c03c800160b9000e441c1c1e1031301d52001910140607910320b1004641c40c0d51030102c088c401a40e60118810141038010342c001070490003450044010304030210540442c81c004810003110540c550080c180746007045d502007200e8200142446120b8012940e901d000c103044010500445441c03401408290340100003010541c003071600400c091204010304c90800443c0000d1001000029000c1e80c0d0b002805000185129031501c401294a03034000b030300f454a8103400103101105940d0800c00540303003a4001b00100300190700c08050038003d500014088a45a441c1c07032000030381501402c0c80d5001110520b0185c0214a495070030442c520252000480c1e8400c20080c0c031901e40e84928401c800b52912000040c1400c0c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73723653 1250 73722403 73722419
    0x70e120f06270c0102100c03020c2b030501080334080403060501060c0308070302031803040b0414120c06070303110c0d080105041104150512090d0905041404110103060f090204 77
    0x903840101034059800b080f03960010342da00054201c08100b420100003240c4851800c1180a480703031007005c0b0b00d148645140c0050704402c8040f0b010111302410090a010003110b003050701613400912500420f41c0091100c0741828407480048802c0c900e42020f0b400d4401c24140c608980201b40e20420381c0d0601002c1010310401646100c2c07103014008a0070300640c191495540284038040041980e0205900071000c1070400c9010300d601c6041d0b92840c4180c0b501d441c0c5804501420340c0240c0702e04140c9841d60a0200e0040c1090090b030188105680c0151600c2c012800c14003500344c0c1f040d041201010b070741d00208811031b500fa8000c0e02c44802e03100c0290400441c03249006216030b50682100388901d00d002c2e54403504c901110111f070120303290f144803982c021000010a0364036004521100150400c81d074200031225002240140e02d42015460f070301c0c13600741c450301071004891401d1101c80071080d180c008100815007900200305403550501d8040307034481d00d4010900044817690301982c1001d80110302130040c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73724903 1250 73723653 73723711
    0x706030515061602010c05100608010f0c0306050a03260403050a0201080a1a090925030c06090b0f090a0b1605011a09071d0402070308090d0305070e120f06 68
    0x404681442c01d0004407511019543da2003030700203060050000c64001003007030a00c0703028404140d1010400901d5903861510340a04200c00242c0030040c030340350861001ca8000d00c50002035981c003a240b6817515040d55606000c0000d0300a0042500941c00e56180809450800400245104801501c0115203910000d050894017030318a622050034805c2c800c5424030442031410f082c8100b00c0e16000c030b6441c2d8441c10742c24181454000c0d2232292108000c07030149007000c0000c1045a104d082034440302980d0b2201200c605c40c01d802890083c0342d08201c0101012000805410f034150002e001d100c00c0743c1c0e14540d54104c0da1105442820802d007051719081444428441c14211032031110307024030940503805c00181004001098903043c05194080030806050440c080c090280028001b1540e900042c10003401541088945504d580300303440e1142c00b994420b0194030300843c0152100c1107013542e03420401c1504402070342c03044010b00c5100100d5003466401c2001c40d000d81c00700d000c0030303100001c062403a02c108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73726153 1250 73724903 73724941
    0xa02010c061b12050a052401050d020a110609120a050d0e0a060e120708070303091a04060f110c07060807020f0a080c07080a0c0905060f300c0916020a0507060305 71
    0x824500410400ca403400030450107900100b484647d203d0345d42141c0169480d01400f8403403c0c4091006c030310180c0a03500180362581c80c40c4c00c0030880b642541d400c20150b40d01c182c0803200710b20010007481000403860089014024080311040301058403140708c08454a040044a005e4402e0385c0c8421894902d0102031051280c0c096a80c0041d9182c0280c640303804100c0d1044a40040802d40d4800c0d00750309000303c1980000c803031b50614815580601341420000040d06000c1c1000301014900a16480303500584800c07900741c0c00c507910203400120f1a240042e1000e503001403000701913001d0091620b040000078407603804218480c1002ca6100d400c03540340c5510b8410389422000d10344d8000c4450002107514a0140c000315002d00001140c103076119008141c682a110108640048203c22903600318880c0040490000c401c0842c20949074521103a50b980e81c1c42d06001c500d80152040010901200e581c100b0007041c042e072401200d040481d190b903001d1400c0c15981c4051b00007507961041c040004001442a03140b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73727403 1250 73726153 73726171
    0x20a02102003010e0a11030901150b0a0e09060604050d0803040c140105030c030a061508040201080606030c0a0c14240109020a0504140a0b1c0612050a02010c061b1205 73
    0x5501c101c0e0352124502c4107024040d440800100003545c44030058010303a055070402c503641c50312414044007240c0606000da02c00203180c03810150200305070344413106942d818000c03a039074501503590703503030a02481c0c45000d801f19400000411003c102da80311100303480c90702e61103098865502d1a007030401c49200301c040d03040130801949032030800f04140c1c0d010f800e4a0b08947d03c200780641d2621a44040341c02050168041c0c1c0d981240000000c4c00380342c2100b4001e00c954001e8a0b00906555007400f04038091008030b40c10581603000b400740c2c4044520580c0291900b5103d1a900c0b2001c19200002910740a0300003800340c0e600781007d104580d404500082e1600410a440f004c3d4200040803002401c4c038000d41c02a1010840d400003411440e0741c622040b14020b02403e01250380d541c0800c0c1451240c0a0840480000d0700c2c141400050361424544106000f680c100c4042e000203140d60b1700440700280c410000351009925800c4801440030180c1c048820f43d015a00c401c0400243c10510b0010703a01c000300b541e40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73728653 1250 73727403 73727441
    0x170c090106090e0903030103032a0524100602120a0e12030304030f0c08030f04020303090a08031305030a0213020306130203010602030711100e060307020106030b01080f0c060703020a060b13020a0210 87
    0xd4020034540c0003602d102c4100800074141402b0f030083c803015403502400601ca100e40115440303107800d07540080501250081001590742400040f4804100e100d4400164090152900403002850107841a540d4074541079940000160000d040ea05041d10303542004d8100200307000816400814030901107016090480b00c4201c25200d000d180d01006090b01040242c50340010110f503018400ca4452040c001c000d800c400d80c0f624096a9030307412009400000b00c04407140828145800140c41756025401000b00c00250000781a0307401030740014216a8029019940004c502c904500140d40a801d056000710789504045c01c04200c0804101d00c040d0103084925078400002e3780c05003580c201c01c801500c2540c2d4a03240c00c103040b0700411160344003a061003141c2c00003007400b05010490304030800300001164030030304051041010310302c40e50400501580c42074200e0400581950054003e05200414400d03079600381d02148001ea901041b2505c0c0140c10000284c80c4560f070038419100414101c0200315 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73729903 1250 73728653 73728659
    0xf0d0b0d0803041b1d070201060501050c0709020915041202030d09080604030305041b080f07080d0503010e07020c09041203060b040b07020d050c0a031407060e010801170c090106090e09030301 84
    0x74182c030001c2c1010b800302e003a4103440d00c154032084901e00010900048100d1504090035030425504c4001d070703030b840c0c010b5080c84c4001034298425410380709860394890180c070038245050440802980080c41050308010758050f401c1e1000400301c0504014050b0300c240b028000c001e84109030030102c51b03079000010310018050a000b881d1300000c0b2250712980c1402c00044545a40c14100c840c040d02d41c0c110b800c1480c2c040c0d40030078446000318588003a89400e00454882c90340b11410070751920311296107800042d0042c001040ac400a41c03c1d040d41084c518015566100c4d5003002085003960200c40c1507500b03001c040105504613505208100040400c0b00041d401c01d0f041a4903002c0134803c2e0100039109803400c0c0160000d0050130301c032030081804c00402c0c641820b03581e4913000070141c00503280140d030b6004111000171601d00503590919002d1050707583e040642e003080ca110708010554080081d5038450b031040640540c46039441d40b4041e000c0307911640a1186082102005010000c28503080c0c2c0c1c000b44010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73731153 1250 73729903 73729913
    0x106050904030903060c0306180b030f01020c060f150303070308160311041412010504051c020601050a210c06020624030c01030b180a020d0e0105090706050f0c030f0d0b0d 75
    0x400c082d280e000ca4080386d2882d280c1c4044002e01034a8101400950181c000b108c6031503142d5001a0000000781d060b82c002e040e05000c01c074200d00130305145038001e0300040005001012038048840e807046101110032080442c0710080391542d001b40c071044020948002c2400240c505030000303c203020b95145014443d21a18402100c1d1500851103008055000042d5480da5075440c45182910170554600070803141c9018100715991300d1910181a113103546194030190703802d1011403500c0c145c0314058002001146005202c15100062070103500d40d44000040700382c0090300f19002c820042a1540c0100342c1800e01d04120880c1c5042402440081c0b1111481820350b07803008075690302018401d00f0300184007031581003c1094004143c060f803203d640300b0300c108020a41c42d5405812007540b055000c100850004512508842085e5242d010b1544079103001c0002511840080002214101e00e190608144000c0f080c55900400074040c1c194201040000d41e420b01c0c1c4c828240070540480340600000450340314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73732403 1250 73731153 73731167
    0xa020403060b121c02030c10090308012103050f09131d0703170a05041a1c0501271b08060415060c1203110a03090b060f011704021503040f05010605090403 68
    0x1003005180181341846841d54001c0c4265410300011a003a00d01b041440100b00c40240701400c0c040b0086240400085003008002c0a0307100c0302e0068607440c0c111002c0d0381c1c4080e94182c00c25000c03903010307040411100d01c0c0d40e1940c0384201803c0c1c910400c04030f02202028a9958098460208118241c1c0145410008102851000044645003000c0140e4441114504442a200da42c002d0032125010801842c03114420304004d1101140d101e0440028980415091090324401c0c400c2c00c1488000304803440421702d085204071221680107d0000c0c5a0f41e030010502a80001002000b010a0a0008020590429003ea00c5801c0c00c2da150840c480e03414024054400503405201910704a404640e044c502c03800b81c0d00181c00c04407030b1190240c4403410390000a0141c02040c10859420743c2200104d05e4a0034050b0b00d03200d401d90140c40700400186040541404c0c3c420013072041c1c0e400500c0d1307820180c0b2018036800550081d07000f10221950b80c81c4906006094800d80c0d40a18000e950007000c0202280e40030b16 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73733653 1250 73732403 73732423
    0x31c0b0901051e0d020a090228021516110105090c0108130209071b06110a020d0e01080109111c090201020601080a050718020c060a020a09050904020f0d021201050a020403060b12 78
    0x31304900b242028008244078a001c3e4008001c03241c170000e40c0541200031002d08160f451001280302d9a52000c001080340c48041c00903840c401903402034042440c5600b00c212101000c03001c0d10704552110180e029480c02c0d950161040c3d070090f000749440302055640310407100d90002c0d0054411100102680c0070807508031008000c0300800020a004640907c80d81c040c04c220f05400c06418450f02740c1c011381c3c2414690061100101600c1200f4510a42d40d0060200901e40369058403002c20030303032030300b80414060b14078030810622100081090a810103041c0079120081d040c031000c00104200c00c1d2001900e0210103070010f0710340b503111020300e000045002411505590003851101000d111507103080d0085c1c0035000c150340c00c0703006e41e200308684a1400e0380076081c95131081c2c1d298141c2e20307591414011351000a5030041c0d000440381d000c1000904200402425031880501001d100c4100d080c81d8034215031007566171a22040d0002400c2040c00580c1c01003410f404404c44a0040580c80800041c1d668407440d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73734903 1250 73733653 73733659
    0xf12131d070e030a05030c0606090703090312051305011e060e040c0506090f03010e1c0e011b0f050703030801150314130507050a06050c060c030106051605031c0b0901051e 75
    0x5182e98410761400d001800085a01500303c2ea15620707000400303030b1281c40c2200c42034010009140000c1c03055100f030261070b0340c1035010340740c0d1100f4590081c854005000020440d5180c00b6403140c485000500c00d100d9100c4c07002138442801140090180c2040541d2101da101741c50751001c010034072020030600071400c01100c9045134015a2003045502207440d20b02070301030003030b81540f038404c100c0c1c0680d0000c607001405146942c5440c05250013101c06807101114024818001448040315588103030f500014101a1401003803584180b61107030380ca142c58441301350402c070002101c0700010050403020500b0400c540712a418140011a5800c0e04060b0541005048143d0403100220038020b00c030090161802800c1d029004031820f984510000d0030340d80c40085100404e1240380000741c1351000302c000366030580b011580c58516210521413081403e00010074251103a0200b003005250342c0041c2504c2c12a400980b107404100c0f078104034200074101c50141d00c07483c05003050340701c881244010201700006000c012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73736153 1250 73734903 73734917
    0x603050d0530090c011d010507150203090d090e04032a06060b0c0c1e090907050927060103080318030702130e0d0507020105030f090f12131d07 63
    0x3034190b11010600e01181d00c0b40042a0a4010180d000c0d101d215481a40c648085411462425004603240302043c2428049076120210910131903200d103000700182d50203452682460881c3c0300742c00c005ca900030fa0700c582c00d59201e604241c00042d08200100014402451080b0781480c00b910003510001800423944c8070009070041e04400f03ea0205103141001390425000c02800d03880381c010700030560108211045038030900d183e0849500c0d100c058503a00e8440d42c020750100300031080c240001284080c0811086004101d0085180d0711007404091040300030700f00003c4000e0082d40d103c3c0c0400590039a1040c10341040f0014000703c3d400b6021070746c00c00d04040c400300152410481071810f5019400c80258001045203001e0581c609607001060780e01c4003400bd8400c1c5410552054031244282c41d4024007240e018030004e4901590310b4040359228000d41d05036154201490301c11418a00c0c0b03c8010700a4074004180704001404841c0c580f0090580c031a0000744c1c0000025107800c8800700107102c1c204000c44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73737403 1250 73736153 73736167
    0x30d02030c160c06120e07090b060705011b11010203101a0705030706060e1015030209040603050d021605010e030a060e0307080c01090201080703020304030e01110c1003150501030603050d05 83
    0x41c88201c0d907030000344030303000c0c6210001d515211421000c1882000000b901c0031000203124003c1d4455021525808401001100e10b80541600a00503152815034800d5050284401052081c0590034035101d0503050b45201c410300740c0f009451040c500c48017541c00da1040c000c100f6a0000701783e90b002a225100b40c040781d02100d40c1da18452500c00c12600900900010a80c0030411100b500a034082d94924012000719aa17012040380400000d48181c1c14030462241044000e0b501a900600c070035100600045521900c0307844003131420b0241c542040c0164400d42c22102d11500100844c0041d2000f460404080c0310f4400c0029914032440c900540400d541d40b4005400000400403a030105031b101d10419220f0004034070560083c03010003030990200310540005007003188680300f00c034400c5905807140c0d500700361010011580400a043c130b909043c81240b00995460741c2c1c4001040084855640c080f0300c0000442c01c640056010380c1c030642c181810114140300149021510510103049450b05a440d418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73738653 1250 73737403 73737421
    0xc0302070f0b090304091505030f0607080a0203130c180516020706080c130b04180203010f0e10091e0b030f0715030f290d11060d020c0102040e01030201080702060702030d0203 77
    0xb0a90f4491581d007490120101f901d080040c14540c01c80300d08406848103100b85aa100e0740b40c190844100780060505400920b11030035660282d03821400b12084100c004000c1da80c0e0100300c032401d800540702a41680003569550b0034a0040c1035010440203c004529030074998042c1d600d00f40790186905204a00300001d20100d103440a885421124a141c544032a41e200a4000168050701410203030520504280030b101c502d6000b2a4104c40d02101c072110742c5840c244075054114009441c040311482903450000d004601402808100da43ca050045050380401c058035007141ca055034200e000381c004140c80c407040c26002c1022022179007401004004800d4144046004245e034190000f4060700c2c04034242903040d00301d8150090039010100020548034980204406a681400001c0090325010201416420b081010302941c89c012030003d41030190440d645400d9820580000c2c0046500c14010829580e01c200529044031366030010f003030581000c1100039140c3c030442d00c070000e034076400101040c0031031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73739903 1250 73738653 73738657
    0xe010c0f0c03080c060708070c0807080d050a0f0e07030f111207061205060319030e030a0c0803030403031b020c0904080408010f060501030b03010605030a060b18040606090c0302070f0b0903 83
    0xd9030100c0e0303014559440c0d00d4610441d411680041e1941c0c4101030006110324083d0900502030091510b03281e0309440241c0e0307142001d502240c4103d034920b00174005480c01c203803c0e00940f0301036074240e100844d4076100045c900d03080b164180b503690510f9009040c1000440d515038190740c0c0c40e03500180901031041e03200c0c01090208000d02403400140c0324030100010801d82c07002080600441403c4180425201c100400d40c1e035006401074240c0405d5202c0d40c1e140080e018105000300303040041d0548034810580d843d10090303000f0076070144070583c00010800003095494400e074041070f8550110b24511501c002402035840300290102d41c0542501e40215060112050070380d401070190400038802c0c1c510118031940900058840d084c0802e044c0382d0445194075060042e002a12005801000c0318080c0b6107403d005445c0b421205a0480e0303143c2da045c1c1e045c0480242d06407085004800c00302d2000c7c45c0c00020000c607010202d6800405105002d1000020304e151413040c8001c0d000041d00c03500c0c1d101e40d03441c1030543c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73741009 1106 73739903 73739933
    0x60c0b0a05041a1005040603081b06010303080112080909090d0906050f1c11070302031c05010f060503070e0a060f17090312150603070c1e02010e010c 66
    0x21620a0f52210b0f0b004036010b10321a000c550780e002240031181250801da44207a0001806441e40b006200c0c9000b201031000014055507165490040c9003d0040c0640d15034400b903000c1c4401881042800e0701c01c04080103107403071801d00f801200a550303901000d404c000030800c10000042d10501036003d41d508502042003082c5400108a0040035007070b2240c00d90380c01142d85035410b20317819495202400e03400c0d200b60000e6680e50301011492247d001d034035a1040d602400e00c0c0042c08210380300101c0204a4800e0701f4240d40721f07115108262000503680d028281c2000d820000018420b920030815414010540c48603040c408407000ca1914900d000c840150f8954800c001a0341100300058007294458000c1d08040c81c0321503503100080556105640750710000b4540700c900c8052100c40c003481605194441e4804c104500c1d00d0740041c1400c11990100f506016100041205000d00c4245100c1c070 = true := by decide +kernel

theorem cover : BRFrame.Cov 73561153 73741009 := by
  have h0 := BRFrame.cov_init 73561153
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73561153 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73561153 ≤ n) (h2 : n < 73741009) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
