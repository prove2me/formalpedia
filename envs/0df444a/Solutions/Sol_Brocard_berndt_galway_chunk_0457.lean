-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:54:55.490391+00:00
-- url     : https://prove2.me/submissions/050bd161-88e7-4ebc-88e6-cc24dfe56106

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82014389 ≤ n < 82194246 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82015639 1250 82014389 82014397
    0x11b08040b0d02040e0a060317091c020103062121080408030c130b030603060624070501020c0303040c03141b040506030c04050907140315010e04050c04090320060c 72
    0x140c01c81804a500806410180c04a4025003003124003201c0d541051003141028180b00c0c0800c0b80c40c60010800c8040048040e1300703841a44070000c18004040b45c1080d01c4090082881c98107034105522164080b4010190b5008000744011a0701003040c8500030b414a2010194042031111042c00b86e4115221040c3c1d02420712a00290483d00f816541d031520365101c040d0303224070b03088049441c04142c8005103000c2c2c000c01840c40b0301810341c02d81c0c00030f5654800b0400017166038410050b412102003121914000840081c2100034803a1000600d46140303c8105880c540044500319441510f915050007009040300b144490496001d0062501c40481c410321111894115075230380c05207a8400c0000c02d5580c1c204802041108003404c20000e50074200c241540700c0c00c0341d0080d00708943c1108001d1340ea40c2000200f48051010b11240c68160342d0038103080c28010a07003d8000c1c0d07001d01c0741911540c615903c1c4d1190051452080d01c61043c0078014bc00d60081d1000314804004041d000f107010801c0f041c886c00111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82016889 1250 82015639 82015649
    0x307090b030c0112140109050a0509070501021009060609020c030306010f050c030405010f0c0b0103080a0207062102030402010c051002041508090d11030d050a090501060b030106020703030e040209060c0c011b0804 93
    0x2480300e84480f115803200911010a036002d00380900000000c040d5002c8e170000d401150200340900442c6e07140c441d80c0b90340c0c04540c400c0074010f0303200d5582a6100001503100c440541e210325008105155143c200d601660802c1e440d4862540001050140740d68000c1000b44000380700d4141503081223000d45d03800d9100c0c02207104040c14000c1890030600e90622440741000c00c6940701840c102c50303517141d04140031260880c4c5000d4025114000300030900d240110440410641d000030f1140302e070780125400c00c0c060340000d0022418820308418980001e0414481200100380306240140c80f90318003038040030a0f42010307160006014060741440910b4138049104d072880c8072682402134151032850034051039441808076610b441740ca85000c0c41042c041d107800c02c2c20500e015600038000640c60300d003107031000d210038401e010241c5d1103801c003000001d000d010344c0303149404001c200505004a0a002c00c04503030000301604042d401c6844150020760700305502e90580c441050016840346c0d11aa201000b512840c015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82018139 1250 82016889 82016897
    0x70306061e060909020a09030602070f0c05150d0b0303190c0302010b0604050906040e120c1c02031c11040f0b130801060501090e100504060b0715020f030402010f03060807140307090b030c01 83
    0x1801c806402487e40c00011640060115501c2e0a5800c2100290b0a960070444669000d5a00003865103402c600070841c4591881119180801200a1800814070300c9a20394040c002400500715030100c003054bd0000803600d441c1d000243c4124a002802c4607040321100d8030420003401300713100c41e0301e5104100b980030400b950009402131145400a00d00194001041c1d01400c001400c40d0b0f04480104091080002071104102111003004c002d07600c0340904550072003618101d034a6032805135065040f43c800c01c104401080e10301515141d00c3c0d0a0702c0c00542054141100014004469000c422042c00081078040020030409003000d00083c40c00203144610071945481c50085903419814401480c01020010000c1000355650803002c10300d600000c070140c40c41c00d00a404801080300354022188440b01280c110fa1540d5034560065449440c01c0d0342d9101010342d90040400c40040c10000c00014008840ca0b01500d2440380d07040526081240c0c008003251400e0003801640ba44000440081c801c0c82420 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82019389 1250 82018139 82018147
    0x509060d0204020d020d050f061810030602030a06080d2d030204050604030c0509090307050a02090c1218010c05090f060702060c070b030f0114030a03050d0e070306061e06090902 78
    0x10014240080e2098007952040c40000d100205010642c02048400f51010040c8029a55800780d5040c5941c112151134100ca84041b00700100e44039221041c1d03218110801d820280c503129102d06040740c0040f902110090f54401052211900801c03800e40c210944c1c1ca030528403681e10704425070501c0560403019048014000d880500207000e90140d4002d0000505071684813940c070f00381140c00002a2080a0052a0200100d46810320100889606c5a085070041103004c9040c3c1c01c1c032886460081c9072504040c03040c844102c0101c1e2007401c035070098003a03140d1810640c40d03a2001500310b45964001d43c0502508101c015540d441d0111081e0548408942e200e0720703034803140003142c00e6100784010700c3e81c140108030020030008810310280d03016141d1484441c410703070380b6444e12100cac0001e284211a0305901582c10400000d10444c0240b8405d0f80101003c40c040082c0c5008910744584e0b60811942961546802e000b100c42c00c48a5981400c0d00d1249000340c01c1c035001c00901014620b0107060300040d0006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82020639 1250 82019389 82019401
    0x3090a1707031d0301061a0301051c05030a051803010e06070e010c0b0f040c0b0a02010504030e180f0c2208101103071412010909060f0b01051605070e010b04030302010c03150509 78
    0x250081c030003000060b00907c09101107011a2003158000d009262050142415203e405a0101c3d0a40c80c4c540d449002035141c039040f40002e1b115a00300310301a0040000c0071040c0c1540d502d00380140380d8034100000040005003002500a4103055020088a040080c0302c0356150200c1c20501c0b559030401e07a0001c4c00300140e00c407801d10040d1448c85030003810121500084e403403540c4d0380c1540701d40d00c224026a607004030701e141328080041c0c480042c800240d0210450340030a1800d401d5805190b044201d01e44814605031040c02c00c02598000c80d5000c0d0b8454008950400841d01f00340600c444150018504001103014148091071340d00004d4840c03002c000c04440c0e411182c11040c0700300c0d0704440b4804d001805642c0e6a42d10f10002d403c000100302d070814107000051505910700d000307501d01c1c0901612001d09201c01c405040c1c1c0e82800555040e80e540c4504040020840d0360040030a020f071800720700c89651303503041d81400b03400d58031b11680560416150078941000b0a07100444041034802c115011130742ca480c3c0c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82021889 1250 82020639 82020641
    0x303140c01020309030d0506030d050405060a110708070806090118030c03050c01051003021801150507050c090406020c0717070b0a03021c020a0905030c1509130203090a1707031d0301 80
    0x5896822a580b0010601c030080768000b010345081010301030140921303502d031001e060701d40760390496601c00301c0d50500c4180320a1074248040c05503071910f440c061040c000740d180c846140c0b44560340114825000242c00b8080907070300303100e82984001c210b07009002c0442110828009252800400350810140c0704800e070405200c0d200715441c00ba45e40e0f00921140c24451080c101e00091880200c0c0f041021504000d40100c1854840d4100c43e01e00c00032100c1d171050108161066400343c04100c442e805540041c00b45a554107a50034016402000d00588414002d2502450844280c101e425040c0c00d80042004644000604a050b40c054192068a07101d402c242070b0064000c2c0a00000180d40300d2500b812147c1e1140c0c09480300421694440e00381070341d10801d145d21456504c50040d041074501840f842d03121040d0f0b0042c01071842c0603007941c0140184a031701104a800c2a211500c0300e401202084051000c940158001c601360754449500d0300d652a0b038040d204204040c50310001205182c5003508075642 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82023139 1250 82021889 82021897
    0x9030f0809180f010e07030507091502010204051305010e0916030611090d11030d050a090306180f03090306050601050307020a030305041b03030305040507081c0c02150c0102070525030314 82
    0x240754008041410b05080d10010f0000034064030501950b4a40050002032003400303a24041c1c3c2c0b05846048156050410000e02583c0c2d8001034003d540d000c0200283c0c5450b640c0800d25441171655000030b4550400c00f001d00d14031000382440100d17502888040a03409990142801101c0d03001a001860000c400070b03030406400341c20642980110501000741c20310212803d00c1c9a107103402c0302581c1c1d0030540c1078010789450096404080000b0301c01132040c400181c1c0c59028605410491404030340024499595099402d00d40c00700b00d0000d20b959074100100f19946c020690400c8090070300d9070135413408150003036449042a030301a04258035180481e041c4440a1040462500340030160090340780c5a04015000d00402d441c12200d0340300f080000100800080740c6210b980445138845091034000200c1190312010400c0140d0380125528580b040d104071480c02400300f001c0940000d07885800d5424814201b507219400c107010641c049540c20140c0da4146a140d099a038542845200f4007911140001c06011f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82024389 1250 82023139 82023169
    0xc02100c0c02040c0c060c050a0c080c0a051c1409060307050306040605030708010213050406080c090a0e2a01170c0703030603080304050a140a02130507030906290109030f0809 77
    0x200e42078070f01e610075a10061705854203020325005d20480800407001c032400d100b1080d08c0710010b60994000c1e000281c0840c014444006032008941d800025600c90908210b0074001c402e814011405501039800e800152503480c0b03150f030a03011410311110300003256840c4402060001004000030000d00340b03030f07074aa104501811000d41201c0c0800c1e00c0d041030138000d605c035801c004100c85240c20001900d14250188100b038a1360038000c0c01509800c0001d01c50901409422036101d6515811402d0381074004201104e01002c403015140b80ca01c1c4a4122122619001d61006041140070441851103c020240c1c06401003a03100303a55030740e4461424110000d10942e00f0080881c81e0000c03d100034024006444035506010f02c402c040034103c02142a50744d403402c00c80003904505880d40a0712506400d40c03081d07a000655003000300d2120f0b1213030707504001c50b24082041403580d10040140c204034030300032141c0d1100745820700f032207441d480c02e6480340f4116603038007540202000400161f81da00d075102c00480e1440e840c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82025639 1250 82024389 82024391
    0x50d0c11011e0e0f0a02010c0f0f0308040b0f071e0e031002030603060603060106023a020106090b010c0201050702041512050a0302010c05120f060303042c09010c02100c0c0204 77
    0x96065580221440b0142c280300302400c201c4240205a000715060071882d40420040c044144c1d01d03401560680d42c04c1000360b5200703404900e4280498515448548032612030340d0340d00142c2c0f42c94a0034007034210700501f004034841101010003411980192458140e561b81c8049880200948401203406880e406205030301805450b04000e00c60140d034010358080e640460640d803580d40d0320414507a54102c2407003400010790250502158210714400d8600207000c48451140105500103000a80d02c5a100071060050703554041c100200c1c02035110300c216601003464080011170068000a04c80c0c05103d1000e4421595100980c40c0340d11080640c60003420401c1d411940f030415410819110030b100c5030103401550800d1841d00f800d80c4078004644600c0090040c41801d5110034020200c5180010a0795030144420000450b20840e0b11840d00c40303500070040b00c1c5000704070441c0c001d141c0f14406030509013680e0606220b0161f0725000310304840d107070117a000000780d0f1901d8402e0031101d04010f40c2c0081d4000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82026889 1250 82025639 82025651
    0x30405191515050406082d0106050a0e0702010507020105010b0a18090c09092012060d0b0c1b03040501021216080712030c08190b2d120706050d0c1101 66
    0x90450440c208542c003c1360308012040d0b480c0001900d5080f04444810705000180c5c0810000300300702c26040c11500c1c20400080d19a4480c40410824502034110710710212501e000c001120b50309003c0c0a910074820b200901c615450401d001080d40156007252092003e03c07200c1c001c445003564500d500901d40040144000d00303100e0406000800340b4024588440d0406882c41c2440d24041400003940012900a61410010441c0c800400c40050705a50340642100303c1c0c18086100e08271002e02a02c8100c00069403814000d1000b8810100d10004880b0790b0800c1c0001c1000ea030b000710b00d4014588a03528040d941e1043c00b0188600b150075510000d0080c00d011401600303112890b00d801047e0a00354a080040d60800c50b02960581e50803100c0c004082e10080d24803581d0315003500b100c01d440c0c01c013400c080b405030341150701d07401020200f160401043c0001111615185088100b088298a007000a04a554244800207040c0d1065140d8070b158141c6400034070b24403501c5107107402681c805403002040b03e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82028139 1250 82026889 82026911
    0xa050c101406090106080712020c0a02030601060e2b020103090302150901050708010602011b180b0408060703060509250c020909011e0c020c04050a0b091303030f020304051915 77
    0x1c406544190246144800102d01e00d400380c8503aa0154007540c5a40201d5400c00741907002a601401c3c03164842e02448007008010380341000103c6c0600030720340301d2840e803100500922201d0004640300050409402c882c14403281407681232100c2064081c0380105407106c0d18101a880c0c807000c4400d41e000310141d0401c0040703840381035000e0f0340180c650366038906684c2d07070b80d940803401c0c1e0382c140d00e203075403104002c4242c062030900440301c007044060440d111030001c66840341d1442c265001507028030102c1d0400b00030004402e41c548620302c09410210f904044506012581c1a100322000c40c2903c01107980083c2414554056100c0b5100264010181200391600140b0700c0d010303001b00c4c11680c0998102441e02c256220b003601480c0c01c94015540100010b00d0154100300140401808040340d250340c84070201801d441e43d14540d846480110603030102d02c0c2d054940101210503141142031998414814400010004101407081c000718410340c0e003140c0114103040d5a11405142540c84003807400c010118 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82029389 1250 82028139 82028171
    0xa120e01020c1c08060109150c031101020d0b030f03120406020a12110c061513050606070203010207030809100212150f090a0605030c03030c12030408070606060c020909010c050a050c10 81
    0x70f503261440c1d480c0032064481c07900568031583d02d401030443c0c0c48501602c560340f082c4036103107580c8007500a01d4413401c9002401e03544c0b4220f82c020800080c880c0d8507070200340708908042020301d40340603620b0011403400e01c1d50781507a114601c025200400c040d0b00080d403214454824101c0801c40c40403080104071017003000007180d09a602c040b40030700c4c81d03004010000380b140034951504144080054417004121001c00e5803074008090040849620180c02d1011002585092001d099801d2003a11903a159003814102180380181c0164042c034103600400024040300502c0c1c40503500a1955028182100c0d170020005007091003020b0444c1d04401a0750820a010f40181c1003181100d90039401c1d0b52210100b071040c9a200e1184100e89000d0b50701c80410840030402810095030b01c2401100f070300303091641035a92182070713901d640c1c0300200156505070401d080d40f40110701590030210040003004482080341300035149001c4c05405c20b06029020405400c1c416050052404410381000108010140d03a20b00c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82030639 1250 82029389 82029433
    0x121602060a0e03060a0903080705070614010b04060801240c060f151d0906040f02150a2a0f0303051308030103051b0a060c080702010903140105090c0102030a120e01020c 74
    0x503c2442110003198034a0414860900c00d107400d6512132143c0d03070720f000041d01e00d81d00003142114229a100000f0000c120002c43c101c1c060602d0a540c2542c491400b1401000c1c2c08068221815844e004041c062000e150341029009000050514001582c0603080c20f50080ca400c10781040754038100684010020903040d0310b202601c1c2202c8c42c600c0c4420410741100c4c045041110340411503800700011901107540c50794103600d5a0b100400741000118940601400c5410107002100441ca072108403d054802140c40c0038442c03a60075200008050180c2c4a07501d004091480c050b080c580c0e0343c0e02062098800000701160a500620110b41d01d50752450070325601d042d10b00b904200035090b51803006a0340382200c81201210160303910707090b1030a40c035110300d281d60f84090f00480c10300800503000030024401c00700d151aa01010b2000040d02d182141209060031000000d5038119002000040301c41c540014480d040310040d403000107401200360904030700a205482d8401090311400c5021129010802080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82031889 1250 82030639 82030667
    0x911040501060f0507140a050d030606091a1e0f0a080a0b040b060712031d0c030f010507050f03060a0314030310050d08070213090c060c02150c121602060a 68
    0x811007607a86440c01c4411110940c0f0010010f5010001800416100403554405110032000e03600815031301d64a0a24181802c5103010100340ca401040150540002c01400140031401c0070001800f07024144500c00d22644061000102c5d03442c08041d0080007850584a2440c40d0140c101d658034561f60000d809014112038a68840b4100f4001d81140c1c01c3c14080c102d038110000d45054142112540d404581d441481d0070001059070380d05410300c4140c254810a4000c0d1a2030020b0104030b06001c0605003054a800f0700000d80c0c7e0b042409021680d580001141c1078032050380d091316183d8580d10001040c810796940040d0041c941110301d00203143d40803004500034090051040c0c10541d0381e2003030000812001d03a001e44000e4091103400b015043c1222003502104101100246a80040e0303206242c5041c140c0060340000c0001601c4004c6040084507030036088500c803403843c1041c01e420781140c1c1c2c803044901d40700c41d8004045941c6001e20400c42800040540c0104002e45400840800030b00d48188002d80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82033139 1250 82031889 82031891
    0xc09090f07050d170d150e040b06010309050c0f01140c030316020a050703020409080c01060f080f03071e020a1a070303180f0308060d14010203040b060307060804020d080904091104 79
    0x40040c0500d003d0759100c203110f512400d10308800c0002c403c80a450b030414030208904680781e203068141e840f107014003c40941607007007559146040500b440b240040004049a05051a0907445804154000b45111a01908692070b103074a00b00840100c800c483c220030381c2e40c811301e00811110307070343d51001c00034511a0103041100c1e203281c004035204980c1d038440001c004d44503030041c0034244050305250700200d0400b4000e2802610f041d180800c12800c580721607010080c8002c00601c00e010445003803008100b0014000019428140c0c591103c0d4543e01c0701001c031540201c1900c0c0d40b0421900c0e1350022000600d426140e561400c0b0710b58408880d01d81c040e0b24114002440c000d80c1d40c500690400642040a40040e03086141500580e425103c07907034040c2481343d100c11105001e00008601c00c0c401010101c0020001d40c481c20945403002da00240504403e1007034224607003d000761030348000700350340c4070317404485d80007046045080c084146d01c180e04034a60810b003010504024041d0032401a9042c3c5002e03a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82034389 1250 82033139 82033153
    0x10e1b0303030103121803080c06010603060f180203090f0a0606060909050403020c040908040f0605040311040204030206030a0504021f1709030405130902040b04020a17060402030105010f0c050c09090f 88
    0x208240c0c40c0d200074080113001c2280c0c00c49002d501881011407079012607007090203c50040d1a6255102150030a80212442c2d522205c0140201a030500442c40100764004996469074104001d0a0b42100b10441ca010350540c044000307002c0440c200200011341a850040c1d41d060403483c07c00070054941401201c010a01001001901255621030180f10b25010382c050b20540b0360380c20400c00988516903080d10420400d10003c11401800b1501c000140426250503540ba07141d45411010711000c450724500c80e9205010410250700c684045a40c055000701c1d000420355200d10000e500c981e0419034101400c03400c40480f04034140c1222200d448181c0c180440d1b00c0075914065119682d110f68040e02d40c020110400c0416990995004540118402000850070f00d60314004039003281c100c3c1000c1e02c00981c07800c7c0460480e504d10f20b0495000b64041e00c042d461076040600180425108160201c1040b00c02c0351a001403060900420b0100040142032130402e05142d08020b60b10f12204c3d031200014042e803c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82035639 1250 82034389 82034443
    0x4141602061006030e1c020c120304030209061003020408030409090b100302010f0e0321030402100c030801030b040503130801020309190230060a09120f08190e010e 72
    0x812512581450300e20640312803d001044000d001c0c00600354415100749804501d5a44801383d5a11021104e030303009160b000315580402128110440034403440fa007041200b840075840b509001603001200b40c0e0740700b14040c050a4114000e1250b40e2119141e400080780202c0c085116801c06000e45004502e584c0c107603180c40c28442c0042005110090100d0301440b90b00045600501c1d4000d140c2100038103540c2c1c000950340100b0b981100484010881200c000104011460310440b005541a6503240c10510307894159800b0f0403208042c04040c03c568105800102003240800c06c80e4041e5088804503d00d4650351561a4085d401c141c510200a0240d04003100f40310200c0c8aa407058150014482a000600d40720b210321708000d007410408150a03100011100c8400412140e0300030012a1400039644a041c2403017007400300b021001004100700c1183c224801c5501241c1c4681014801082103100f80000031030342c00611170641e44040301d500b0501803604110000c1400144070b020b1071041c940b013866407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82036889 1250 82035639 82035643
    0xd060504020309151f09050f090307050601062a0c050109080a03170901060e0f040611090d11060c0a0320010c080f060d020d050a05010b0103020c0c041a04141602 71
    0x210f52081d1581d0201c28241e01c0700b12a14000c0e500b00c201241d151050203441a0b1881d11030744030780c012440d503644500910682e2005415116408400e60001c1d41c24468160b0f00d00d40c4410040c407070300c03040040c1c120f48944000d0b210b014a8084030080c0d403070002c01403218078040e141511144181070202e0b5913000001042d580114107100541d034540d42e80c00c0110601800c0f131306070000141041031559614940450001040301c03880d400340410801029861a05160031015a484028450200c4c4400d002c2c03549183c6860041d030162a07403050101151050703034404201e03140100880807805224280100c424160480030740002c0305141420341d0001c0707140c0b4810320b00307880a81c10030a0004007610f000074086000b81c0c0c0802e40090004240102c405250340010b004070b60144000d60b000c0d045a020001000800d208040c0c90b500207090550500d0041d02107243c0f03400d060f2060900803030300c900c04800750b04015030103000d8101740140204034030b803002242c00c01c1e148408c0340d150401495911400310280c3c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82038139 1250 82036889 82036891
    0xf0201060501020f100216080310090b041a101701060f1d15130305100b010f03050105030d1103041509080601140607120c140d03180507091d0a03050d0605040203 71
    0x11400080c4010305d2131441c04002548000d1000d501c0c019000031006c005403072000114040c05c4080601d540103030501e0346420480d081d02c036549105a01d8180103c4126040004611000301c045030341405003c00003170140e9040e1034600541140e158500008038440d40c01004a000d2001e06545000c41070201d040c3e110412022295400d40c071941030101e03000a501181c00425050f00c11180e14100c0580c1d075a00c061815104100c0074010589452400031103590240103841c0c07040709454140807951400707002c25200c4850080c810100040c4001a0141d540704008403030003885800c0040488261201d0028420021750041e44518060580000785031120545400c60701038004101d280340400039540e0702580384c55100104280120f90305c400001c10031000c1840b050000c0c88019260030010024014100c0305195000e0300d400300d0140000000c01c0000800c5c00c01d46400781c0f0001350b400302d8030520380070000740300703050714524824a609002090b83c0040545000011003000784402501c4404200603400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82039389 1250 82038139 82038163
    0x40203040b1501121103010314060402090402010e0303071b08120a020c010e0a0e0f0906062718030301030507081e0c01030f0605040204030503030f090a050a0b061507030f020106050102 81
    0x20701c080420807a5400c20104104810141428002210662030020039200020405001048048010010f01206a251555070280e10300984981e140a500007946c601c400350019042200181085450792003c108481d196a04418092002250001d03040c0005020b4003c4440703d018614440300902c800c0c100791105900e8035005084a000e80c5001101c0b00300f0031044080c0e01103800340000601092540d10b0074011400716654041c0d41c9884014640382040141070240107040b0390b001060042c43c1e40c903070294444118100041035440790303a10300c2c1e0f550329050510700041c000040000200b0070005803480495004000b070754115100c90b0460f00c2403c441c0c10282c3d2072030b00030700c40c6c1d20b0196129500103200090320300b00029090f41c50340003080482c2c1081d0070490701903100000b8440700c400c448094a901100030001092614829601c480d2545400c2500820030511040403507543c3c1ea54600c1c244601142c08206c17900c40c144c5007001044591441041009075180c0040400c955101144001d10030f2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82040639 1250 82039389 82039403
    0x908030a110c060705030702010f0218042a05090d0b0108160905040f0201030c180b0909010803030402060f0c100c030903032418020d0606080402130213030b040f02030703060e070504020304 83
    0x160304c00b00c080e201c81d40010080ca00315580d81d07800a580600c544040c02c824250030703401702c000c0c590860a00c01184c1c07001004101e0014892900941c3c4204e00d030b207484c41201680b41568941041e2400700d0303081c03410302000030200d108401c00441d10141c0010001c80c08422003c0500c02c01c1d60325228502110416600039281d84101c00d501d00155020741c10400c8410080e240400c090080081040036502c072982107101131510018a03031a540c5880f088041c050301843d00030390b04c0c500701b507070000303106101d0010155181480402c00400d50340b01440503090082010304144009509140010020107009100701c000c0707131030700030580e030001003030940748009000783d00c8d540c0290fa04103c000c8090300700b040b0202040f241c08000302c3c0329902440c0207000041686031030b02c2c841401c2c544104058002e501c2c03803140d2045d10501c240070300580040110001c80b50811a00c004588450510b00b260201d03006020f0340500c106000003040041950003042118800010395003400e031a04104000d038881960058862 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82041889 1250 82040639 82040641
    0x10504030f0909020f030c03060d060c050d0e010e0c041805010c0504050a0b0a2703020d0b010303020105090a120c02010905060309060a0506030d081609050a0e3112030e010908030a110c06 82
    0x40841f04004503041040102503100446c810380c2c500055404031408030000030808100240800b001d4001d05680020500c00ac1c001e2480786000345568400c501c507503501c0340d03890b465908504000524007514254200b0009d002c4140140da01400c26403061103200d0060703900140010781c40130880300703559060040d0341d2080000c2400c450341c5290005400b240b61044d0000c0280000142c0c0e8240406640b50300c151a078900075032441c1000703421030714010014071003900710140740d0000618001140f558016241051010a6040e000490b0141c803c1d030403070380d041000007044c4083c130480020440c0c802d0542000c140b105503204828942c48401c80303134480000c5841c82d001b05182c010b0442d10560280c03600c1c904030610a5607900000d08072a402c1d80144c00c0f0366412024003d0754807200c0701240307000b0400da000d4031000e241e81c0c00a420000c40d5000103005026603c41400707441e8480d81050310104074600003848188118208050701c0d0b8402d07541d811700d0034645071003505048049410380386141c0010b000307040c3c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82043139 1250 82041889 82041901
    0xf0e0601030515060406031b030905060f0c1c02091e010909020906070204020310090c0c03080f06041b180e01030b0c0a0e0d030c050d09080c10020a05010504030f0909020f03 76
    0xc2e010150200246003800d0f0704a0740e59440e41c501802c02080c0030342e008200c00c0c01900c040903103a00d51507400400c0504041001c0003043e00040c402d5004422031403152501c0e1b8078442101c40c140940c2e103da4680848010040c0301085441c1c000d402124400c0700c503044d0700d01e011310120496030036a40d0480d0209100701c1040004a0310b81d8007034004850080d282601d4000240e00140c01ca03401100e140002c405a14801d000c002c0362441031041e03110360f5007000c000c802d4013a10050701c4018010036090294810400045040d2244d80058107121030000c3e0030051980c0c0340720040c0030000c400d40755044041c007403080003030b9810540c52194102c3c9c1e00000e11809d503407584000c00601ea400103182c14180014261040b071a6250465580300c800d000e50f8450300000b90030301c0d045042450f8080f2000800010100c180702c852008140f42e80e040c1030840b48000200e850600c00c2c0d041609094002e80f60f940380c04100b2041c19017100d400d071312921156031014503240e115195503042b4040c01c00350040c2c201040c400650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82044389 1250 82043139 82043141
    0x30b0307150207050306040f0c0909020603040b0601020a15020a0e0603010b1b0703080706060518150405092505010f090308090105030a06050303030411090915061c0b09030406090f0e060103 83
    0x8007040c0a403054a03001d07616403002c41c1c50082c090f90200c039a0440e0907040001c4c801941c14840240c6021807043c4001240e43d000a005400090b0003d008000040d000c64110782c0200009410680d2180841e09000d80d04c8607c400250852007403040461484900030340c10740340c07400890781603071072040b07841341000c00a202c2400f00242d060079401180c4540d1101101048032403000c1c2c025203206600c046002c50402e41031180d6800e45c0d08007440707941907c406111103500c1215140800c41340582d400a41c0ba40c800c1c660034580003403000c91f019441c104800300d822122042804009482c800e0700c1303030510003c0300e8030100c81c20300c01d80c07201804200082c044a0031642c403880c002c58024142c55008030301c00e031302c9000280c215481030b2800c442480d189810202345003060961140e0102e00350024000c0c070614040441484200284114403690031640710b44500090300c110307080c0c0c090b08013030006194941803103419502d901a00510380480d2041c07a00191300660440d01f207060350280c036203028032521a000194 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82045639 1250 82044389 82044419
    0xd0b0115090807082109180a180b0a111c0203100b0c0109020a050a050a121712040c0909080a030507120e030702040e010c020705012001050124030b0307 67
    0x240800040110009616204001e4040a4a1008080c1c07120881a102c02003c9040801481040d81002d001c000040e40d200150501411f4040ba10760784036565841e0b4220051098840801040c01d9050840080c011428641481581020410040d030b41c10070600490902236200340810141d58802080c0c40b0030030f683c014503003002c44586c1600c001a2500905403485c0c009220b1400c0d2a95111030325002e6191800c003c00040200780c8000c3e200e00c0c00c040206180c010103003d224400b8003c8907009040089454560401c0d003400c54002d5190b140860000908000c10788003520007030250380700031805500c14824000701d164006010b034602106d030f040980103420002d080300140324151740790310f0b182d80090240388042d0b0030308401385917284006d1042101f101c840c3d40c503c1500d0307850440410492500010010282c03407007401e1582d42c0e420396032003c8862032100c079550700155081000000310804440c0305000d600081140b1085141201a011400c2354195084164035901240c001c012100303150b0107003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82046889 1250 82045639 82045679
    0xe13030c080406030509060609060109050402090307030609060914011109010c081207030204060315030506010603021e0c01020702010f02011404020f0301060e0903041d04080421121107050d0b01 85
    0x20842110803901d6110303103034215078444400300ba1944c08200800d00180241030f07000340c00f195001036034208000000c2110740c0c00e00400740110303030000b02c0003240d0741c013003006400031070307101d142031209a0072442c1030005441024030480d178204940f100c49400c031b1018010302a40c0900074030940c1c01c0030303840d000440b1081ca8401c403c1e141d510040042030701080380042c815100300720303940380903a03100d103020340090803150125541c91014400326818400608046007076030441d110791801584400c140c0801c02c0e03085201040300d0054041c000f070350031070036041074000d4899035000f44c80d80d03078010107a04426802c0c1c3d9030040404012100c000300040c010329062105210210014000045281e140e4601d0003071198142d0302161250b201040420101207995200d00014155080c4444da0b81401e0fa1421194096400340e280d0381c41c9004d074020501410200c500f0109900b14088900000d502c03100503000b41c1400001070514007460340046214100394039014216070b0310032582003450b031a00c0c00b0343c00c0d1200342c5003076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82048139 1250 82046889 82046897
    0xb010f0819020c032701020307030503191b02010c081005060304020904050f0f0c0f0a0b0a08091207110a0812090402030603030409050115030c020705060a1805040204090603060e070e1303 82
    0x10a0011040014244c140300c41d11783c80b117010101c00500c0c413159984082c590304652007007104070000b0394014252900108543d51100c07040c1c2c0c503840840090600e00c030b032965071001c0c1c0d603200c1420a541504003100da030300315489862060b201c2d6052202d4181d03040c052241c00c603100f00b020500505007448034bd40e0007405a800d0310301240c0340000b4036042a00026062100e03500c02c11403900d251402c02041c541c541c0040301c10300c441501c0d0900301032640c050340030203000780022000065200c40d1f050002c034240d6407201c194256a054240381201450b4888000a80256503509000c41c5000380050391801d04110f0400c85800c1ca201481000003940c00200501d8040c08144400213403054103004881c040c04400e0305107a209620b80c03000404842c5c0c0302c0c0b5507504651001c0802c001039111101190313044129850410012001d1032558145218990301c940e400c81d20006000602c00c00036402041039a104400c1442542c64603e0540c1d90342ca80750264100441c0c007503000ca1801452210012212803103414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82049389 1250 82048139 82048147
    0x10503010c0f120b0a090b150a08070c1104050c03090613030e100e120102030f0a1514121c140310050603040f05011415040c0f030e011409010f0b010f081902 69
    0x2041500702d01e640501b40a0741c4500c003424107440c0400c24200303002800c030348843c00c00a420300010450900600944188070302c81c0031050611005a680f031841d900d01900078001801c2072400100c550b40229480e1810b4018480407aa00e030b25072010008900717426640b00d1002511400401025a00f80001403050040789102455651208510b42905020940c00180c036490708201448548500400b010308186c90100b4400c0166070380c3c9030840556038159142d08021400402180d02c80010f25604401c2e407107502034034400341d5102112000c2c09440c0350307140403c0d102490b1190000b0f010948090150750106842400075050032009140c0c014068880485603c0403502c595084030040b0303c41c1000b24280e001084110724450b1141c0790101c3c0242e0b070410000360740ac44c0052044081d4030840007055194041603c50b0942500804030000050805d1901c50820448050007026007181496046003003002c000d40e19809181ca80c44d484055032030300c1e111542c4461117001e0070700007000c0803078449600b88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82050639 1250 82049389 82049411
    0x7050408010f050403030b120a06020d0b03191403040e0f09070b0d02180a0b0712021e0c15030f0106030e12030112050f07050607080d0e12040e010503010c0f12 70
    0x1015084000c0b18031100010b01d410503083c000d0646441e110701a0160594660b41a4810800581054015002200107860741801001c0c000548a102c2039241d151040d00c00030005002001748102c0c010340701d281c503460b6203000014056100d00681c4075044501e8061000100040d80f0304d503c139980030030520141ca456644403600c400f0f540c0c2010081c000803c2d40854116075403d01054202d400001c11180c204015250040c000024840c1075070041052800e050440c0c40366000300000c4242c00c01c1c1c42d40d07584035403500c0d00400396240e03050710000c1d100764500080070311801052822a401908100c1d422025030303003130203410f40243c5a40c045009691203214462885205036201641c003804840030221000403c0d403d0403440d1019245140c00c0d940c0100c0410020365807110111121190710503003560f240c900c5051920028001d00304030503154000c00900003441e60340500144141d40200d0080300c40c07642c03a4000c0c58201c8030b15400c401c02103800c10614680130350007010303407c01907100300f1004254581c41c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82051889 1250 82050639 82050641
    0x405060a1205030d0b0a03081c1509021c0c0c02010c030c39051c08190c0c0f05030a1419060c090504090b0615071209030c150210050705040801 63
    0x1d4016110354001060b00350340d0001074050007118980c1203500d0740c00c950540d1241e540c20701c248100300d030070903c40d48900c141c15203e0390800c10803d20280d046a84495884194030060750040b0544000410070b040c10743c120f081c447c81340c002903040c10340c0c541d001094a80d0054420a00d00301003079040c00f4240c00c44a0004100c0340c003048014100e114000c0724440340d0040d0503003100d44140c5d03070b501c0d02031044014415500c03011050900e4000204020401d4541814088210b100f0074002c5c7c1c18864030781c10603405040c0c100f100b9072180b5208003460490a81d41c0c0b0b51148081da030900030941d050700144030040c0031451821200302009480016500103030b611114031103070041c0b2440100c90503500c6408284055400800d0303200140030507202413060000320383e04c00d00c0c040c00c010302c064807803031000c40201c88103091201516602948503c5040720850a210f01800010b442d200c1110011904038000c41c080d0303040034500003030100a4000f0850a10345030a4100603110041c900c101b00503050000140000702 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82053139 1250 82051889 82051919
    0x403030201061412120904060e0406020405150a05040312110a05070807090e031605010908040e09060a0b09150f130f06050102010b01090e0901090c14030f010b0d020405060a 76
    0x2298000141075031401c3c1852442400c400d42c502d01c00c09030f01d6504040c1000c0811302680c490400550346596414080000300101030980000030f00c1586c40c010002006116401041503d50481d84154031405444030448135204203a50000054028030041001510603004c5041d28042c5043c21102140c050303103540c0c50848120420740e180c2e800b5040030401d480043c4444000791020100c20301c615000380610b1540e074407030304148000e5001d0141e6010203003e0b00303620050b80c0562007641c0603921580d601400e103400c1c1d02510f11806502410000c0751000000f4400c064425401500f4410f0b580d5490061a00800040102a4120501288010099542c0000b5013920101070000151000117410300000b290900d40020741560b1501d1282d200782e0780c12840140448030703c94004282542c1e020000c90150044a01c005d1422204030400700e0000f2100c074030300105100c150215260741e6180703000182614074425005400c55032401e5030101500b002e8118a500800103080540780c591b0b951120f940e031100f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82054389 1250 82053139 82053143
    0x20102031606060902070305070303110307170c1201060807090e01050f0d061407020a1b0e040209220311060a05010b090402090105040816050102190b01060327080a02070902040807170f030403 84
    0x2100082760340030540c06107d034088803403801080d6130640c90040c10203081000500a54007a104003203002910f480c0e811803c42d096407072045000c1000d542d4502c0080c20352134054a440c004075200ba0302c04030304500309084550403130384001e1260306012000030621000801071081961081d803036202c1c02440c0014600070a0084903164000c1c810351404d41031440b42c10003107030f07030f800840100d6240400843c1c80c0c000b41f141d04190110380e02e90094840710b180314083c0400d00fa49115400c8502019001d1641109281c0701c5041540107844055a81000701c500310344007401107803400c0c0010321110402c0e040c11350250000c4081810131034501a01c411a0b80d03d0035004104810101c00991800d00031941d05020041100080c10041070750000641d680300e1101c4014040c0404141e92046109110302406000c10400c0d40c0140001c0d00105103420500c1c007076070100b9040000340c403070301c280010b024201e44219000ca0307031164080e154490401d0348100560745481000c4419129082d64441e01480a00003440294 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82055639 1250 82054389 82054397
    0x50109030e0109050d050309010807052503080114030a080c010e010212011d07021b010e0d06090606081b0d1a090f0d0e011e05040803130e0606070201020316060609020703 75
    0xe0007003000400c0c00c3c0b5103410041c000c0c0391007040000007030000015142c5440d0709080c443c0481d03452005c1180c0354040d45041c01c9500007641140306510b02c4108003081194020b07920b000c1142e07220383e4500c2601c04c00c010019010751000c150030300070485400c0640004c803008c0c0004180c518000c9491420380c2c2100c4000e100240891004001070010b0300b150985982072031206010602d8814400b03512a4000c45003030202c8400441e800c1040e070b01c034540414803520010080003803070026082400040201c01c6086440c00d1401c8400701d80c800e8000380c2c000408407140c2c101da600c0c140c21418810040041c590444454900030b089030000d2010036651345c40f901c246401030484d006004075a62424614141c0310381400054410303002e0590b40300140e2040d81c00480028212060005002c44003445154088201400041038034850000d8103030b1440700f01c8024464418554a4a8081041c03a1040200c000d0251b0f10407c00c0300f80c03461882ea0040c2c11640641400201d4580c4c0b200948c0c266444001d0890000e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82056889 1250 82055639 82055657
    0x1704060207050a08010b0303030a0b04020d020a17071b06020c0f06090f0106060c020603010b070c030b0a0e010501080304050a0e100f0603021c06050901050f060706020a022d0715050705010903 84
    0x50078080f80f00402010305100074045030100b000070944030b11000d09403e80341c5860781d6110003d41c517690121400405854811581c401508000a0010b9108555003024134040d0006c2900d6030b108904200c0580c1d0294240d544135005a555680254000a409001c034011140320381c80e040020311515100e4107440d07014150100c881c010321405c660158000030140903a044240016844001c00d490640e0030080d141c568600c03027414110150b006541c0b000744550100030400200b001c00d03811007460300340024001d11460341c8556030f40c1c0d164060f50107915000a0886d204100c0304904d43c6160342c201e050000c911440907120101200d4a00c0d10740c03c00070201c2d400107094000c241c003000d1a080155402e100400c812810080010881c48061003603620882440071200320641da01d40440b200541c1c170050455a0b404415006501c80280542c0448000e8442401501844d840e44143d003100744684040c0403ea41840544841e045000c03444c0010020240103040026000344070b40d41e28039000e51241e901c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82058139 1250 82056889 82056899
    0x118150f15020d0203030103030e0f04050c13050d120e1c0308010e340509040207060609060e07090303080c0c0102071124070807081e09090f0108191704060207 70
    0x60920205140710840d401419090b40c0181c0c00b0040e203055a51602d0082d410508000008040c040803503107041c4d000345001c0a100706403a10500500c00c07000225200c46800343e6034010030405540e01d820107000301040c9040448680c1c81130881d031042580c020030040c4070030309804540101c60317000c0004030b01048040d00180700304031449105d9640300e01001901000b00c00c0c3c0200750121604180b520503c5490700b0501d2104036401340301592008100580119124006810484003030200e604c500764240b0f00e4483e02082c0c903e1160031861107205262208405645140d400311211400101810281e403400d104541d103c034001c6c0010710119010b02c11008141741c0e01802c00800301c81c0c0000c0061218045c942c400c00c3d02d0311440644804603000a0b10640782c91503410321800b03900c01c0207919488040c02204070a80d00300800701500d0a2132069030020b03840c1e81c4154514419280a000c0e0b00003a510000044084600c00c40040650a1181e006101d584502d440b0215043c0c0041d0004005600f054000b400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82059389 1250 82058139 82058159
    0xa060c021006050303090d06020409021c0b0922020a0b07111810030813030501020408100f060b0702100c0209070201090308060607120f0201020702030604030504140a0501080118150f 80
    0x1d0120032201c01002014a420002035a80c0f051141c000c0c05425440007003010b21026a050720000d106500003556030b1000d00d00c02c08003a0210b080c92040799407a0410308004c5080c074142c1d851056007050740d0b4018920003070741d80034822081140e04a07403040b401d40002c5007a0342d011010340490ba00c02c00000380405a81da00300003414241464080052000c4010016040104071031641101d80242c40c03559100580342c40402411240c5c1c02c0600150700000340050401303400a20801500002402004099000c0c0700e140e084e2680b40c0f14648011030140b2540002d032400d01d03c0c20150003507504004142d19400d5001c211986000c03910440941d5580c0406000d0682000c00c05034400c0088810504d094a42e54440c1100e041140c034038810841d4184c1421003a038000d44c11222840d03001400c43d100b5141604c1c00400d15841801030404000300c0801c11300031400c09040c2002554816140c20308075038240a113900c0f8051040e0300b44440789854403224000040204002d4014114807540c2188540c02e000100c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82060639 1250 82059389 82059403
    0x3161b050a0c030b0a090305030703021305090103081306050f0a0f03090f1202152202010908030c01150510080601080a060504020d0b010f02070608040209041719120e06011e080a060c02 81
    0x304a2418113401b0360000e139101e03040366481003480c140144c50b01499017150034140c42507001135801c10b5030b0038000700901c01d181003d003010f0752510002c403d0243d116501210706001d522080c3c0282d00050190840580c001c00080340e09000c1c901e00081c8010311501c542c0071034a00c170403042e00d0701002507143c8418641d0511400101c40003011080c0c03480d09103503003090600a8121100c5450700c825202e008210ba10840011f002025040101e0b919502d9100103180204103000041e41c00c1c0318140b0000540e030404400d400340240043c0c481d0811aa03800c5d00540b0300f9a0020400b001d0640e452030003240c0c6580342c3c1301526082c0140b410001d440c568480014000c2d180540d9901d0541d804130f0340402025502a5801e540952f040d40c2c0050140c8461405800e140d1510294881c3d0610204120400c0000307115905000d20740b507920000c01a260040000032541c44c0031407001e40e1707000340005100300d692541950301c0c0d1404801c0c03a01101903844d00b100f402c12070003060489806455401a658179513041000c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82061889 1250 82060639 82060651
    0x10203070f02060c041d0606070506040b06030106060c020607060e1c08060906060c0703060e01140403081006050301150e0f10090f0504110403142a0307090203161b050a0c030b 77
    0x5480e1500300f41d0384810072044895406e002c0b0f8050000102c040c0c0b82c40c8103a070320042e444800c55500703080a1410200404044508034040d40ca02400014554840c00d481c054440d006020180b0340348550301c42034050502d4248004851040203040342c1c444090780000728960090b65510921418000200440e402c8088c040038407525060028020152011642070210799105c08006040443c2017042805403c0c46071100748452200320410041c581c020300d0080c41401c825400003005c549500090725140030a0080c60030100385141506c03c0c140c018002003200d00401401d802c1f002051000240c0c5112880c81d038907000944020080003000f071620148400f80804880501c080c4090303402c182400e029070320020300b004080e802101d14044060050302100c81c00c43d40d00160160310300307807a1022100d0240c106400f17885030758800034250000380f00340c81c0120010506942c0c08070940380c044905041100c2403203100281c440101c80040c200b0000e00c1261403189a42c072a40c1c41c078500304042064002400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82063139 1250 82061889 82061911
    0x3040206070501091202011d07082802041407030b0306070504051e03010203010b09030d0504030503070b131a070e0102060603060106110721030e0303090102070905270307060b18010b071103010203070f0206 90
    0x10500400b000452410421802143c0840401c030000ba544046000c41c4000637401c1441c2880e03000c00800010001e9201d020305440038004c0080d00014103984100c21209400003074400e12080c40b252900542c0384a41810040c080326044404400080c01c9920071390010b40b140c8400602c0951500b000c2c01304503000092780c10524101391440d01c840b0344a1056003002004c12a49400244081c00c070940d95658546d08000e010300004465503102c2a540015219840415150420345502d5880050010700c60b4402a028000c03903482e00c00305a602c560b403441d09084500941034046030140101c10b01400942e040d00d000c103020358036410003620f100501d40d42c141c040d800800400c9440c0e43c000407910100e0b03410010004481e500c50340040031120303102001c01c1116070076805180c01c0e041c0c000041e11074540150401c01200b0f551070b04102003480e07147c1201c0c054004400040225100d82c1015010b0316008145030071150f6603071400a42207900440d1084045501800180703070161b41080500d501c603440c421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82064389 1250 82063139 82063153
    0x60203070c0603150914060118030c120221010507080a0912110102040801090303140a090b0a0915090b041502040f0302130204080718050f0103020603040206070501091202011d 77
    0x1c6507504042603010b0302040c10b480352540c0340c840204003c4031000b03058044040102c2d1480c0b480f42410790741d05a582600044600c00d100e01b5240403451003204595000d420020302600e0159548040c0d4441071080e0780c40b010f00001e80a180100580745400b9850360400051149030140016240340c00c09084400c4071441d00310380398002031000000e03400384941414004806007480300072901a1040f600b140b9510350804582104158154005c40b82c0b4018000c44401c850351400c2007242220440310001e09200c66042c04900501016401041c08174003c8041000008003002c24000396881080300f1507565400c1d4080105012030003070200080c802c400341c25442c0504d42075086203000b5040c04003900c141503c03109101011000d41c111001000114113681c101036840181800c160a5402c20513001c0781044002003009a2420b1800d0680303034020007090440c0c649409119140d00481c070100c81a65860386480003140400c210300444018170b071300100c3d81c0701000810080c0c40310b0030045642603600c284 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82065639 1250 82064389 82064393
    0x30c190f06051f06020106081b030a030804030e0d030903030f2309130f0204030c08030915091207081c11060403080408190e040633050d0e030c060106020307 69
    0xd0405210340d608200042000e4aa0b01d403c0102d0240700c003c02d12410440c018001002c507011740001007101c6510b0181e0341500140c000ca400c4204448c1f18840d8143c01080205000901418607141c000d4024a00481036002c50000704005154500c415008075041d80000c10401da403001440e99070300c0903071410301c1e4101d0341d021044d00d45071070300854450542d0000c01e408a81e80c984c00701100200b40c6a1009100e40910084180000d501c140400d43c1d801c1072284000c500004000b0465440840c09402d00f816012030f0310000c0b041e50840b07081c03203a2107083c001104070b01030406c01c1030a002d844624080c040d00c40a0300301c0060345109000004003804a58110f905c60100b01140c05070f0700035090b04117050700f9a105e00d0194068070440501180251526002d00300d1250301100c138000c1d036a8241c40c1001603a45400542111408208101e079142c40d25200310500da9125803c1040c800c41c1c0c6061044c18072a10b40c0e040002d17101201c850506030b0b40f01003040440703514100021070040890780003a500c0c0100079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82066889 1250 82065639 82065653
    0xc05070b06061b0723010503070203040b03070507020d060c0e190504020309190b0103030f17040201030b0307052e030203220f0215030718050f090406110c030c19 71
    0x5000a1250b64041403921040c03a80d08903045500e4685001d0303441d00d54503842001c0e21101030034141010f0b02d0700f090500d01994011000c42e4043d41068005605042c40c0c01080d0503c0d40c40141100100007041c440345c0300586908c014010b00c00d01c500e03030104420b41c5004008002c000c0c0700728000d10409280f401030800c810041d62403015148181c03405070782d03950780141d01c0340b81c5040301c0225844003103a0070b0740e0810301400c14001c1e03042e01d100796500081d20b900b105045903611401011551440344c01d80115005600a610141c0e4440001d4156100581d03614000342d14881c42c0300b5000d18800e20707900d2800c3d03148a280106414070724a07080450450502020310400320042e10000d803443c5901c0d08043c3c0500000c2c2c1c040c040b01c20b50083c01c908141c400480c045082da041603400700f0100e0304800c1114040580c21258405071040a0591400c407511102000204400940142e8020750758100b102c03c1d007644075000f08415072002c4015030f0788420b044801e52a04030707103100b810040420020090005140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82068139 1250 82066889 82066891
    0x901080903090a0b03040c05030a0f050c1009060e0d05010617012324060a05091e0310021e030a090b0901060b180f03160f0e060d17070c080304090c05070b 68
    0x1d013115141e141ea86520300303903080b90030b5500050343c1846185000c03070410603400d01c03184c03006109105480b110044101480000380154699401040010360180500b51140070004c02c40000100850701c0303007406841d241d00b1540103400414148083e00441070b0001c000b40549071a000d20070f01c4240c4075942c5400f40403e5620003900c00700540710078000740e0380200c21651001c400b41000070410b03540c540a142c0c1c0076240c0c0d44140041400f4125008001c0d0301803001e1905440f00c0140a0040d18000d800c14032207500a5000031154030751514001d84291400085801861007680c4008000071554030714200f0300400040180203685903810714030b051061440d140242e4078004d5141190903c0d81c07111000194041001c800c00b00d401d44100250721602e0b4000a100e28101c1e00c1a4000d850520340300c00301c002112200300d5941c3e0308109074103c048001913031030f03600350b1700000300d42141805c0190aa8828910350a80d600a96141d8008102403060b840c1902c1403500e02c40c0c07603003005450a0a5a52002c42c0554 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82069389 1250 82068139 82068149
    0x40606031a1e1224010501030e03031003030f1107030c06020729090a0e150915030a1104060506030a02040303120b0f010305071b06050a06050f031b010215010b0901080903090a 77
    0x2c00800002041142046442000079505112130075014603481c0d081c031100700900c50203001034104003941e50a2400070044030b010f40100940301011a045890555056055016000400c024042201d02d00703002030202c1c5c8040c61042e01d403c00b0f40c900e40070000b841c000381da4205000884140500e442c01c00c04d00081e024801c01040c06054982daa179000054041c200c0f03900c46c080c4800c1400030070140e0750317a00c5000842c1b10310885007094182c5904280a001d01051110150580e2021104001040c40d40c80203581c101001031000c100243c03a94003050480d0402d9403c0341600d500800c082c0101038218203580c90041d8108420400b070400240051055030141c40e009051640d01e101186020f4402c00e843e801d01761041e400b040400c0c1680c0f41a80080c40110350500c40c3c51700d01400803e042c54500300d44103080c2c10040080c40000343d07401800e038403880399151480c1984500d42034040c1030100914228020088285090307203841200001400d1040300030485041504200040c8445170348000d0781c0c0307040c0c0b2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82070639 1250 82069389 82069399
    0x50a090e060d080307021f0204080718061208070309080d080c070c08030a020309010306050301020a05030115020a06050f07020c010f08070f0201020d0e060610050306060301090b0f040606031a1e 85
    0x9115140480e1441c02a0b001c09481070707400200704007419030001241801e800611a840fa0100c054110840890066010b032038076513044200c00704040c045040100b0004511100c00003009a40ca17120900300c40a1120126014a800b0441c4404e0641046800f4000e004130f00c003a2110302f0740e44000918801d0300a0201030360001c041410001d00c448144940083d265441c1100c0c0ea860341141d001c0d589070484004580000d05001e004681801c06000751100c500441d1241800c40e400c0c03001c3c0031082d01c0e98100303620451040030085004104140100c9008060750407030501c51782082d0340d000b4141407403c2403850500c0f10490b0300000103544640398990111403460804080d16402030200d01a02c29880c4072141c80b811b111448070306000118149000310011100b00711050000c0c0c90a4490f0b00040366010b86c002001c1c4010011141f00d034200f20403405001b0300c0900740424000010b4220345094000c00c0c0000e55581d030489030104010f009801c011003c48440a8030120440c01d2040d440e80d0700f0400c0d002e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82071889 1250 82070639 82070641
    0x603010f061d220b03060114240307030e031c02090406060201020c120313141005070206130204020304061e060306060518151503041a060d030507020904150c09030b0601050a090e 78
    0x80c106902500c28004d000301919450b5a507412400c081030446031801c0d00c91847c4103011100051891109415402508000750865076100c505a00520700301e51a03000c280030802862aa082c440800003449440000c001629100800c01b408100c6a281c7c0003102035a204110644040c1000a40910810008200f10b0f84d241c1c2c1d001141c0d40c102c0c6000c00010040040f40312501203889001c12020680c4084100402507542c80400481e5107000a40e15012005081c0f1600d00160515400030750307106001e4440030070400032150700304061504a60200150b60380d03c000c2841007001078007403a4000d200c00c9a04240c94021300d0700c503004500d4081c1004840d2442d40d50017460030345840300090782c041a6003c280d5100e1900742405030094460b50f2138a00c16680b8600080c41901e024415014840c0c0c155444904100c0c442c0e080c040d1868000d00141d40c041032500c0c100302110841d01600b19a6000c3d55102000c0c03514614014284000250409051000c2803058450a1f5841180d100c2110803ca190b4285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82073139 1250 82071889 82071949
    0x10503061c02060f04090e010b0901030320010b060c0d020606010815040216021020150406020a0c02031605040b040b09190e011802010f02061005040f02090603010f061d 74
    0x1144c4100d0a101e400d40340003040000d00a03800394020440e0201920080c0304200401041044c0d4001c240002008150140e00c806400494409045000320240000250030580c0000084c103503003008800d00c943d940520310201007107134140074041e0829001e003000b070008d0600303203444201a41500c0310306018a070b020603d42030800d1090304110300c1980186c10701c02e0100c01900c00810000500c1d04c00c03500a55840783c924521140052014410100e511f440070950300d440d0343d110080d6000542610400070003002c1c44002d65004d000c06900c81e59070040f82e8949038034000600050791040c1c2c2c3e40724481ca00e0b20b40690a16150b81e8070065109442002091890040c2e8012000411301040c1c2050150310300180704440514500d20b000d1814001d89481b4104032112404980e54003086074020301c2860504d800304854102a04802082e17062400c0140c1060781007004140320382c0003680181c0040f0003450040140303e40181f414181f140e198846061a1860000882c40c0408040340c4410128610801d400d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82074389 1250 82073139 82073149
    0x5090a020919030b040515060102060403050703020f060106120c030605210a060207080304020a120f121b0b06190b090d0611120105030d030603020102060c0901030603150204090605010503061c02 85
    0x44020b0114404400194aa0500400302801100c01316614440c1c850310600482d0829030081c80340300305a004208960f03480c1d60454003600290700440540c401d64100043c629801d000d903502802180d90f0300c18402080709101026241c41440f40002c1c103242c00e00600454480700003080c50311103108a40002c2d8440320b0b0142c0c1c50000c0860000c3e0180d44041500802c02948030700640c000d5000700c0755000361640300e03a02240c0704800710b500200f040b8850b001c9400050751151230624034100c02d04004103e81018101c5040350700380140100d445500c0c1604010f4140f41c160110034210380c0d6a1203c00c983c80c00d20700d070318246104100e51148100241207008041140c1c98001941040060000c00e484401881054404200a0040c1c510074050742c0c6100a40c640f083c85558101d91b0141d000b84515140c20148441a03844880f0f454101a150b16001c0086140090ba0850706045c12100581e610328000310302049420780d4204d58100710041061001d2540c1d9440300c2c2e5050039001005003a0b0100d10720000d9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82075639 1250 82074389 82074409
    0x140d0b04050c060409060617070804260c03090324040303020f07060f050402040f0e1009020f0d05150a110a05160605070e1c030c03050f040806040b010302011805090a0209 75
    0x3640400d002401007660020b540004003212229211208000c01c0481c0c8044006011141c0d400066800000100860500200042412003c0410383c41d00c081010222020b41c0c88823740320200d500005007941c00e4242044041000e0910b000105100540c0c00707100303101070101800c041c00f015000308403518200449030440b070f012035002d80200800110541d00801401040b40d00303074070480c41d0580110403120301c0e000310800700703611101914204151610380001003140f254140d030440c8400234100016121080d5145115000302c00034075965224003095411000010282c51f101400d02c0782840315040c440d81964140203460070a207848a07142c072503040b540301c0b00d03400203401e440c01c01003800a915000504e5900c2c03040140d600210b5003a415401c1760b11028466401000282ea081250010a00c904040d01103c0784043c0307024a00b6a80f00f01e06468a60140c03020345401c1c007a03400420843d83c000a1010482901d02242942035107824002075000f68001d02c02010550005091222540c4080d400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82076889 1250 82075639 82075663
    0x301080a021003230f0a09170a050d0204121707020604150c1a061003020405030607050307050c010e01021b0606090106050a0203040e0f06010e090f01090207110402030a09020a140d0b0405 82
    0x60b202c44e40a4855076801101610310780500807070303040825074101c1d00c0c1c0643d003a91074010340d00c6002c015004005a01581c44403c10340104407051002c20610403860005000900040200715541c41b00e5062800c9454894030144130f4000302040319500589800c0c0c217641c121404010390390b80510300e0540544c3c031001342d04401001250001500000442e070b44403001c0c0614419140d02441052803a001e400b284154080e60341d02d40d10680014100d1032143d0003c541c490356501e00076050851903140d0300c0c00e490105c02e0011b12650042000051072018000c80107500d003d0000405d0281010400b080f01c43c4810b000e002d0806c03d001a84404080c000c0088800a00c114400c1488a01e0a4444540301400c251000c900180e02c256290303406d40340c401348840c0580b05198080d0302592030141c0700e10080d4094101110124182054a030741613585202843c81034805850128000c2c1a900c104040301680c0d8104403201d241410360b5000700e17160368083d402040d41c0b00020f2005a120b9041c050719000d120294 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82078139 1250 82076889 82076921
    0xd050105100311010e090115090503030706050f0a112d0a080610020303010f0b070f08070809011202031003020d0c0f03080a0f0905062a061003050708030301080a021003 74
    0x41c030400008012025089900465401e4031000c00140110350030340c0c4607203215a00c55143c00041c800300d84243e42c514080c22440c14040d0309103a0300c0c1d01203401d641041ca002d8450030707035800c200040c1c1441040c3e180c0c0c2c0700301910f000700821603407034009250a00980c0082884c0c1c00c40340f11740102c080d8080003250303000364441c0e140c2a110340041800070052001180e046000b19489107605041c42d000006483c140c0f41c0c035011400c83c46e81488160300c0240c2180f2800d81e207410365200c88001140c0f04d8801043e809001d030140c50750b034424074000904009100d10114041e540704000300080150700100101c103890703040718241951810760408100c50f40c4550008005200b8069000040228200007803044062540b00c1c50012000600140d42034095031007100c5e00a0003c211f0f075000c2a00d8014a0282150280c4840420201c1180c601c2c0c0307400c004aa807403481c000140d60900a01c201044080b008102030720081d813666041401d02e43e00d134032490030024040c214100040e1074a50003a0030480c07a803100841 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82079389 1250 82078139 82078141
    0xb0901090204050f04020c030403030c0c0905010e01050f01021b040f0b2115100506030703021c050108010b030303040804030615080604060f140402010e090a0204051507060e03040f03110d050105 85
    0x320900003036105100e01c91141c0016000000e183c10075000361103c04003000044d508061541d00c0659222419900481d01c183c5c1030080420010020320509028040e468001100c941c140b2041c0101c400d50487e0050555204024a02d002c0524464440000b030056601042020b1a901540090001c003104958003504044d103041107030945d402402008010202201c004003081e230410217800e0025200e000e003036019444284218107084c80116040301e05481c0061138815028808444001c10b04582468030f0f48410041006002c04d000324031400008402031451414140d56041c02c80c032035440001c20081e10b80100590b00f221249800d0000c145007020343d00c1303074030345442c110006000340c60b4565035162910704c0da1280b00014444041c40f56906848440c45e8401036420040c1c40c1100602004150350200000710783c2ea2100c003844c0e01e80716207240f280b5459090514154007950404006200300c1e62040c0300810403c0780440c00c040440c2d4105884a00b180034000101c0c0d00d0402c55030f005000e540c2444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82080639 1250 82079389 82079399
    0x70c06141e030702010606080108031912050a06030314040b0d0c20063102010804080405040e0307020a090506090705070204020702091f06020102030106020307030305060f09040f0c0b0702180a0b0901 87
    0x200040d0710800b0f090303008000ea50b469050035182150300b8081d02205500038426000b0914900480c0101d1035442e051540d014440e41ea4500290b03030702103c400524035243c840c100109500007030f80c1c05c0c00c0603900040b1350809040c1030540190340103d100c11440c141e107464000d90727100c1c05280c004500701b802c01c0404c4100f00c916017907240d8503882a181c940c1868250b0110801075403c00071400409407044812003450344098004440401000d0000e0384d80b440300f0480001d4641d9a80f0a01040c00c103004061074a4101e14010000740e50095480004010305282c10400b496450321810366002c2e5070303400c0035501c48245001050080c06204402900700d00320009018440c1c59410301020b000740c02850400031152039000481c00d0740020f01c00d5001681c0144200c0000a000ba000240d1050000e4092414010940c0020b908802d040c0c40a9891440b8004038034113101c140c02d1440c000d072081480741850030805502003001d424210100319240640500891016000b5410031500180014a40051541c5079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82081889 1250 82080639 82080697
    0x5190207030503100603020412060c120606090303021504030806100302040b0a031b09030203060105060c0c0405010303030b0117070504260604030e2407020d0213050702060406060506070c0614 84
    0x44da40b100b40811301c0b030710009000d4800e008440940d11a036035041d4202890703664a0f00074041c2f8400c02c109100d01d00440710303d800014032695004120913941d4071001c9242d030030068209000c0700000108060504200b102090f04100126003013082035814a4210040f02d00890081c003550304501202e40303000443c87d00003a495084000d1200020101e070a400e804007500384c84881e441c3c4002909a00b098004008a1030503501400f4480d070090180c4180d40c00f503100040850b2000d810403804a80e540806212035680001c86d48001c03484117881c102942011034000c0e03c203005034030407404044420f034415840c0300889200401c0580d448030403505070341003e01e070181c02c2c50090000a405040b428004001460b4441340034080d4001c2e90f000b89142c18807a401b400904440741c101039030400701c18810051151070038452030b8490207081d4098401400e00c0e1420000399007023548000d12580301400750f0004121107040c00f804940325030408254200c000030450440d4041c50b054580d43c10f07200780d0340541803804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82083139 1250 82081889 82081891
    0x51501030b060904051b0607060609050114030a080f0a1215080115180c0c020a061d0409120305150a030b010e01080601150509030304030b090c0102010c030e1005190207030503 77
    0x4141001da10541c2d071030003844040142120007a2450348024110605441c4002d241029094003130103640c540400b43c0c072200c0c06e4548940c07000d10b0195442004020100181139000441403003180506200c00113900d55440f03600469103000c1d03404800003124400c090007000c02c03103413a0081440030700400407a041120742d5140d641c81060b14170b5082c900741700c0c0314006003883e002c1a503900c102d0098000e540d442031500101125881502403002000654001d030b550007518100401c40c0e56201c10000558520a15019500400d104c3c02141032018020003e440e151802c500c006d85807600049a035690a04101c100000030300990b004100e03d50f0200030310504400e1241230300d9440d800c0680591387c80c2200d684da100c0921030380c1150b0200080c025002d81c031844c010700d45468010116400c10380c40703803551802d0042c00d072a4040e180d80120015211303560207000310302031580c0c00c0c00c003003050313a00040c0c1980d110404428a603e40c1503840c000605a41000225800d80c08a43d1100f10345800043c5800390040e44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82084389 1250 82083139 82083143
    0x1030209090a0e010b01052b0204031a0907050604030201081302040609051303090e06010e0d140102130315090213110d09050102030403080919080c0c030a050706031109030304120201050705150103 86
    0x401e110414039554081c87c1111200c12030b05000300041e12407007c0096441c8004121481c540d5000c11000011581c001c0d0130320b040b8013400110030401d0401c1d001d624034020041d8400c0b4002d00082c001040940c0c0c210040990104d001050064181101e01c0014000d00054002646182c548018400c0045030301c0940f064462081d00c419410035282d13820445510000c4540c031340000c0070002c40125070308020048420280c03242208a90103240c1c4004c01d8260b030041c1c5103003c802000e10004100f4001100c601135030a0501c0117081010540c42d4002c90101c4801d00610411213454801c2045c90072018821500c08620a00c070400c024203486c5404ae01030b600c140c400f680002c000c070010030b45860003c5415030044000151a021700744096903021025004100010ba0b82e00401d00d00c203c03142c0b0180301c0400002d110700054140c09080640c0582103481c0c080101d2148402406101c01c03548000080302c0c1a9128458030300d0f03001d1403038801250244116007006045010b80780400c1d007070800300040ba0f1f05882c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82085639 1250 82084389 82084391
    0x40b01061101020403020f060f161a0106030c020a030e0a0801090c080606180423060f010e0c0711060904150e07080f0f1f08010608030c0d03090b04080901030209090a0e01 75
    0x11405515803d0f40124000a90300145860607800980b425800030150104020342460404044580d02405c0030002001503c00d204840407202c2c020807048a0240944120f0800b0803c441d0781d410000d5544140700c40050600140a005051b00d54800300824000c2008100070300c6420007619004514482c144100b54480c46040e001c84e40c1840c0024841d0303c1c80d50040b0315228190794503115500010b6014181c0301d2100152440b18007074050a10003107218260f60080ca0300c80d540345c490814480e2100a02d601c1c122281402044001400e150502655010454a0540f00c281040c005001000d21800075140c3c81968032000400c900c03600740703191080a03140c0700c480441e56641844003041c10b04581c0d8005800642c3c0c0010300c000401c03000c2600d5141c0b100e14505560351580f00f05801c40ea241d42000900e130784003060f100e0b01900c08020800c0e070a8602e02e0f0510410500782c0e1040310f071a80181c801084c815010400f00103d902c03d50644103018401046484070f0b0902d11072940080801c0d0580c2e030565 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82086889 1250 82085639 82085657
    0x709060b0c0c0102012003060a12031701060206070c020420070c0305010c09050d06020a02010605030102030c0c06060619050c010908040f140f060a030c03230f070807050a0302030915040b0106 84
    0xc3d0300600c12032100c1c82c84041d01c00401001140000a644d00003408035a0002402c1c1d401310f1080c00f141001c80300a84240c40700701002d20700c6d0440008020059008008541c0000c081001c01c40d0b01054501e64240d054501155480c9a445034901d0300714110780c0100880700200350681848888420356040702d0003034008011000910104803800d111600800c0d400020300056800050503981c000c0203404094400014002c0d02d90000030700307903441a0340d00074480381c01140e010710300b05041c402d10b60032050131100e1526040c8030060f59101d940c00c414401c2c0c140800420884e04c0c04900390008504141e00c82d4240341c0c2c0e00c0d15181d0340000f41d01c0d607024400c02200000c025a0013410521800c0c8000c8200600050601020000450103840d00c590510100f6494504005c2c10327450610300d001200700f15000b03800182c0f800c0110644075032b2001745080100301900080c046000d821400702c07950072030b2070300c0e0140c4d5035600d1800c0c40340340c260314000040c4195140000c01050092280b01c0c14144d8080755038010305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82088139 1250 82086889 82086913
    0x60c02031b0d050412060207050604080c070807050906041d0706090e0105010219140114010b0306040b09040c03061107140d030606020a020616020a150804060c030e0d08090709060b0c 80
    0x744a4402c11580085041040203001c460150794400741074074411743c4054500151603803032a085c140142c8040310003000204404101600502c03186014240210041802c1494040000c5c0d5000c000b5020a000d10707520b10074540135103c1c3c400d20034a659400812214210768a403402001c0b11113501c02c110703600e003070180045034540c400304514040440c008461002e400041d00c62100e040100180d2064540d41c54442d058023240300c2c9503142c02404100521134603864a80e0a00055a28a85140384206010700030040052001c2c054041901e400203000070702c0340b46001d000c41d0709100300140070b0050099144030b030040c09800200201f032007819590030710170155641400d80c2e071007003010002035208105000d074404404401300b02010050000300010b00c0c1e25a03805075484070310200000c82d07002070002d10401092100600464451030b015140402c10f0b504205c407444e84070083c1d1b0425400300580c100104480c0c2c0420420030340500444a8204060b50b5266900ca0440d404000ca4001e21f006600c81150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82089389 1250 82088139 82088143
    0xa170c0a0608040209091908070b0f040b010b0304020a0506220f0501020a06201902060105011b080702120609012304120c06090605190e01110a0e030a060c02031b 71
    0x4200c80080c0c40342d00b865242c907400c01c141c0c070070020010701d50f40c41941c40141940050202c1808094016600c042e9550824245030210641c02810b40800710940380510000840072588503045507a0140055225100c81c070010f801071106500c929800100498420800140c1820a2040407400c8040c0342180c0d9443c802c40c10748115500c6620b0158001103c207030040744503074000b42e1406540b0309100885c600340c1c0d03440407c0c5070081861948400140c84940480c0341c1c0400c8064050502403c200705003215840349081c803000036000080045202042a00841d225001c41510780480c035010703035010f8584911704500038008511914000010130400d400583c103500480d0b8001c0b900201d83c4000484003010503601c810050008944556840d00b292011031040c0c03140c140501c00300702d03110454003107030038146040c1c0d4002d50350386d807040c0d02d001c400c0c0010a200070121a14900241840c0000241f00b000103030401c0782c10040a8000303070070010745107429603004c0020007e081e04c682d40d0324408801110455 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82090639 1250 82089389 82089409
    0xd150e070903110105090d050a03020703150509100f020909040b10050f060a08190203150a060e0117060109050904080403030201050c070c0e0415021321030507020d02030c0a170c 78
    0x15041c0da20f10b1400d032000e5481a03004013000c10703002d0020014030b0a0303607480b685400300d07855043d001600000414001c2101c0c2d007503e06506203a2020501241c280b0030301003a02e440b281c04456003055619140151894200e80564058481c002d2240545151a041c40180040c04a4656071484483c800114092516074801415684068007a43c10402c2c1c3e81010740700c05001501400c650000c00101042c030030080c2c00150310071145442800c500071800c1080c80400030447e001a002d101c1040764484843c0d900c0764401c0344c41407404010040e90345071070300180e0b80740f0041c5d00b056800c403500b40100000c0c0003080c1c004004032846640200060b5031004071512581c0107a550092244803054010003165800724409034025001e00044101c00a0420040049070b0088841140d1514601301c2041042100825a00075518500b01c80e0294640303540e0081043c4a0a03c00034420250390fa81e500030f40d142000300d000c0b6884058100d900b09500c5d4036581e0b100f00070052480071300d0306c1607040380c0c8120708248a1817 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82091889 1250 82090639 82090643
    0x903070f0b06040e0a031107270b1504090506130921021203070804151a0904050c0a18050105040903050f0c010f0606090611060705041a0d150e070903 66
    0x10000c0d10000c0e507214120044040c00040e40035440321103400c000c010520030f1200003442a00c0d00001d49900ca1003440c144000c943c00b0392040740c081c84002c000341c08850300d1070b8070041c10035000142c10f090403000200100792007a104005800e0220340814402c0e0154446400380900306c03010302000d00c11070792030419201c00540007460700c001311101d40310010450020070036080d640c0c0190b82c881d03018010b8502040e0422a150380010309200d081c042070100301c1840c841c03540c0241e501400080780c1d1142001214011240c481e0241d9000740000301404001d01040440d18401400000d6183d0b54107405103803d92070401c600c42c00c44c90030303000207030602e40740c818406010f615864141c03c00c4c59961080000d50000c4181e80015500c03044d14202c1c2c10518410302003d031031243c662150050500c0c000134001c00c9450350840d4a40d0044c02401503464000c01a01e003124481e5558036000c50f20b190389050140115204032a400d0b041040344440007901402d95026120442c2210f4100c2d0b0703440004a40d01d07400c0b4400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82093139 1250 82091889 82091903
    0x60f0f060513030204110405131103071d09010902120a0e0a02060702041b0908011d0606190e1302010e0d170d060e090c180f010510030b0306040c0608090307 69
    0xc100c550301403000703059a90501076400d030909589802140030340c1c5003003000d04c1c502c01000070148000d02d420360203449514440002004441400640d0380c88900c0b001d4012030078041b807002540b11020b0f000c0e000700c01d03510001e00046c195503500c020b00b40103034024030a40c03041c80c100000001c1140721740c0d1103888440381a000041100902d247c003030190355448110140d8019490b1130408840710100c00002e00e20410a984d00d040e140d161011040c02c40d040202142030303241c060110300490850006407983c02010441d591201020b03050b086018041040c0d203c102d060701900200700b69681c083d885200040c0c000e8a400400314400010000a5500c05170700038200076581321040c019500740400f8019040c0741090018040d610768900c2d00c03250008961150030365104011100441c1000741e10120032a03258a112852414090b6610602223814026680a00e60741c03034100020f14465007100c0072069000c1c1c155006070400c2c1c2094010b2035a1406408040b030b456001155100f40c00208a912a03904108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82094389 1250 82093139 82093169
    0x212070821070b070504030f14010605010908070b0901020c10090501090504020307020d0e0a0b16060f090503070305070f0b0705031b032e1505030906071e0c02030a05030a0c06060f 79
    0xd185946100302070003013002c00006001c08400225401882010240641000300c2030701d01040d134490a507a1550003090411880c803104100002000440300c042d00c0115100f05e441d0700f9807000407441c21001504103980101c1501d45d07440e205411804000039503100380c4e1030075030058070b0700c05000c1070384003c2e201c000c01607210340ba00c208040d204024900c2e008400810036060070b56035120b014500d4000e42c0ca0ba000101b02035603024200000c9210b12810b4800ca050180500c40580d140d80707842e4021101c0103030034454000760420412042c10303030401100e40c0c0040e1101c11030908000c02000c90304129031070080c1c80c1d01c485044040c00c200788145ca21416615844d410380d51910901091400442e491490460094400104800e0300c010305241000800c0c0d40d07041d48030318000c1e0380185800405001c1c02c051000c030060310984c00144e089620031f00c80c611300b05008907028501c0800c0c5400c0700c0b540b01515500001c03401701c00f150760041c14125200d00506082c403150b600c0c2c01103120008050321407074440c500000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82095639 1250 82094389 82094393
    0xf09030e0405070e03030c011508070f0b07110604031110020106080715090b0301090b010210050f0a23010602030d0f0614011110050103050304030605070810051309021207082107 78
    0x140296500410138a8010755883c000070100c0e166810410301004503945401e032000d8440d80d035540e4500209004001802c4a900c0c14808500d02d191034082c020751802c001a0f0003040c80f01200d110320101c0e0003e048265503030b0340e074208449160640d616080c0b0401d02ea204821207031f0302c14041c2500762840354001d443e00b24a40b84485180c04d54024500e001d000000034000785400740100590300919583d02c1c08038201915200081c100b442c00d4000390001d5240000780300030200c0741000c10798846040e640006100b411f500f40c1040100e140300c08075010881c41000072600640c0032010b010003a040240922101c42c0c0e1807045000d50b420340c050384a000c00c1c1650400b009603c140c2c501003620981c102520543c80109003040d099881c00d030826212070717000160401c20800706200b41507114815140444107070412010013002d10000f848ad451003000590414038900c08103034040251194001e0400e680200b0303020540340c0781c2030644680b138002c0c002e4081070741000c80d8040c03000e10070310411050545002855 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82096889 1250 82095639 82095641
    0x1513020a091a0303030a1a03060717060607080703030903030e011406151218211e0d180b070201060b0d0507021507021617030414040b06040b0d0f09030e04 68
    0x1100360002c4220107004003005480600055000c2d0f0429400410f04400e00041000d100c04448105402503101070304000809a2150340441d90040350360035001c017611208001062401210009405d0300d80024840042681584c0400030b0a0711a4a050010700130340c01203903080310520030140b200301d41050005071075861700c9261400310f04200047d05040032109100980c0c1d108045403080140180300d0345410031203c0c100315803014400344001c0d0101c2e10004039155a1789010f0091035040100e030f0f00b000304c8031807a052400c1c0c0788201e00c0048100104d0340300550000ba440e210040075501701c40c100008c40c06051040c01081c090300d03e05002d0070f14018003044100d004100c010181000c50086074109a007103401c2e4416140502a01d5005012122031945a9515021280d00a42503c3c40c50325111609400c0401502c04440e510034001282422100108000d84015180f207540541d00117400301e82d0800480c06401c0c05084440d040041010380c0301d42000b03d400d400390190100320120170944903803803e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82098139 1250 82096889 82096901
    0xf05160e01050f1902030d15050d0b09010603050105090c0112062106090501020703050903252607030302150a0b0f0f0607050a0b011a030c07060b211513020a09 70
    0x20b01c214070f04002c8002030300b44c420107011100016000041e40403c2058107000c0c1220044030003c1001d03c10b890400081c80d01c1d51142d400400086c400400540902004c1d40403200130341d040300080c400361401d5009140c850a84035030300f5001c104900d03808500c4621912a00054454031800e103402d0303100307040c51324025601d134480c212070194558a404c80011001c0c009044028030035100c40761580784480c200341c00c00d0580c10407000c41c1844a0700d0280c111340e040c200701d02200c0142040701c40c01c002c410002b500c5540d03009000041e600c5004000802c15900298840f152111000c01d8101600c0e140d0075902510048070740240c0c04031b240c0301440107a18001048011024000b016039141440594484d030038041c40b0311068602c10810001002094404801c40200540c8274468a140d8600500c10140380c0c01807a401400069803003249400d9500c42c080f081c94250081140c202d0300c01142d02041da514065040004800d034040800b05070078010b44d0003000c0507550f00030007503440c42d41003520072001080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82099389 1250 82098139 82098157
    0x12030708040803070c170a02040e160806100806090a02100905040c1e050f120a090503030109061805010b0a0315090e0c040507020604080a0c030905040f0f05160e0105 73
    0x208885400a2030140040c07006010140156441c1e010604100c00c010305990f111100310301803130700c00d94504000400e400c460b940c1c1c100d50004019550b003000600c0c0c8a2940c94141c40900134140209041800103007503407003003502c070049091a0780c4039803495840e00030544a6004682c000e1032041c1c01032800c0d90a000b1a02c080303142148000c1c0c2d580b0000340c00d445505c40420045410500300d005100d5100c04480002055820124a0401000900302d01481501000040d0078140408200301d0201500300b00a01904102202d40300c0d41c550108200511007442544140c10070390700f103800b07096014000c0c03038100d41910708c003d030074150710050603005040c001141c842c4480204c2380104042d0418440c00001d03150788001450a4010001404111600508040151340c05030003080002a00e040440c1d0380581a460400d03039156043c03a0030745402040d9008980c1c880d080250844100d030b495404200341f2000039a091015480e1008001180d210320003004000272600c440e030b0b40c5954061801006248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82100639 1250 82099389 82099393
    0x905060f0a060e13060603050601030e07080a03031d010e03030711010903090603090309080d0309022b1209122108040201050406050c191101080711060106121b030605010906020105041112 82
    0xb159090010040345c801343c100a003c00d60b60006d00c0165681403107011900e05204004000c841d051a82007541e80c10700510042c00c0544440c8205041900c0c0104505a484550001e103c801d8200007034540b246c0044030340b140081c8000d108032010520502070303200c0d41d0b50103490768000300b070621800310081c100e00c10080e010300c100301d000040c140c03e04000c1012200071507600022607107076500c10890903909c000c0d203140001040602602c0300c0c01010740c11407e1664012815110921000c5055514480307590001c540b80f810900d002051102c21688100c0c0080401400d00c00c6202c5c00f41c041d220800e0a55000c7e001410600044c08154051001018030b6610181242d50103174952091a0842240701411a042172175400001015600910132a0300903000d41480104120108000317075594205205c2d4a0401410200d000b0043c11503521615260142081e060b048807440348010300036240500c582400941c4480c0c000409520602c00c4c58080caa100303450402d0012680200034000c81c48202402c424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 82101889 1250 82100639 82100659
    0x120715030f0905120405100509030c100207030b0141120a05100f06050303071a0705040b13050a090b010801090903020f060a140c0708030610050d0908040905060f0a060e 74
    0x4190200044d8048450306029141e907541400140416400c2e8a05003d05008050124440b40d41d0041000c040c03418054441054403540307583c04a150000b143c3c170180030541e0345030000c50300b26112098a620341b60007891143c10301091f002c240b0041c000b41601c030020319908008099079450850550740c1285101e404883e0705901646505080019030390702400800e54a007958031155105004031002404101c0c083e50902e2010344070004030903400001d8088180403880010303a0b00d4000d0090314060130382e18a01e40d894420080d2075161040040c043e01e03205100c041c1d00000c2694103800355080310b01040e5500c50b01640b809106801a00d10b9030702c201d0950080c54942e20031103500f00300c818814000304502046104540c04000240200034203582d1140d00d0800109010421070004c803904110103646604010311440c5048030300d03000c1c2c80410b500283c00c0682041c24000204064402da400c2e5030700811858494004111440304d207008042d41045a4072000c1140b107010f4410030070f0f40c03400504180d0072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 82103139 1250 82101889 82101893
    0x1802031b15040b0304050d02120708030a020f030403020c040f06140f030703060903080f090304030f1103070b0a030c080c090906100302070213052703030c0a0201110304030e120715030f09 82
    0x150b0030640140d0091a4003000708001d20404200b2000d040c40540042c145a105440c0c18a40500c43c0c0000504030110020204190320a6135041743c81c28050001d80c9900e900b480e01d8001d464180e084400743c840c0c2e0030040000101c2a0300e105000840f80888450084480560107002400480d040c3d070781d0b03050145000010101e500b40c0540030b0420b00c42da4076500a850000b9050b004070b08098011013084d44180070900000301660303032400c0d00c0da400a5010078100382e600d000070315000741038000c4865800041211809545c01da00700211101a54403140c5440d9106103020301035005a81c10198490820004900d050400410604000c101072601600e002d4998011999007c144c0000b9204242c3d80c60810a90318001c807a1102d120408111b039405504603900510b50f01d0101808104541c00000354480441c1c1c000d602260341c0c1c42e11134102a4076860a0304028141005104017603000358071801c0808402c07540403a503c401d039604028011040007003160704500614100182000d05540c401070800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 82104389 1250 82103139 82103179
    0x3060503010203181603020f0402090f030703150c051c05131a07110105071709030412060b0a12120f0509030a0b041403040501091e1d010503011802031b 67
    0x310582400104480e40304d5603038051840d200c10682c221100540a603020f1005a50380e21071029000c00c200c03005600c62900600194000c10340340d014a0381442284c40c00420000300c480b004a1422401008010f982803200081d5070038411050350001d5024003102481800e025a800960050380100d000d600010403542c40b4000416085407041728500c0840c00c0040c10307a4003240c940141e0210000a014a041021024068901b56025000318000450005240003000c0064500030901c48094000c100380a091603001462044040da00a0034081c9002c103085503110441000c40c0c1e440503520308586c507000c408540c44601411508208882009036500c50b980c1080300401a0b405100305e10024241450700000c0c03050304001902c03040d001400304001c540c1c0c1120a200440d0041e075840302e00034158609000082d5001e4102c240342d03061408040010101040303001d4180c4a0a500802002c0c5201d48000c80007145081c0081d45640301503458805034195001d482c48105c800f078100b5000c1d84220702c46072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 82105639 1250 82104389 82104391
    0x70e0106020a0501050a060b03060906061e09280902090f0402040e07090f05030d0318060c08040c08010603110d03030e0111090a090507020304120809180105030105070f09050f0103060503010203 85
    0x40d005a01508021051220a02c00d10350045d25000c0108a001c2c0b5041888065001c002c1502d849030010200103507aa4503010304646054900c0300050100701d629600c407121a4008122040c0a0a5079070b000d10540035076048a800d1b240c0303203010030040e02c07841d01052401075442103072955000299030300000a00d440d28005030000e0420341d21002d40340e2170301c01c00081c2100c2280e400110700414945040105881c082548180359103076142c0410424100e1001080000e0001d000419091a0201044001780d11100300ca00440c46210001400b135074070103000e82640d480d40405400e1a1240709030380603901d41f8101022229101e81004100c403001c140509007141c50144041302e1003440040c40c0b5800d854060808005055119010030070f038140000025074a01441c01216010280710503100c05020410056481c40d01e801800b411002d80c44c04d40382c0404c40d000b0b04c40c09019609000204003081e009180038000001c1c55640c40000b280340c40b040104603040d58054905040e540c81021400b42c50031700041d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 82106889 1250 82105639 82105649
    0x90f06050405060a1a10090b13170105070504060f020a06060905090c010302040b0304031b060207050304060f0e0904081b03041403070b0301060c0b0a140906040c06030605130905070e01 81
    0x8140c0303071504000c0d00309000104200780aa1034210360341007250300c400c200380b82c01c0b00681e4035880240c41c04109881086080d008405100c001056484e00c0580d003004030000e40c0c03101521040300401c1d4007000d60a80e501a00c40302d01050b010710042c04001e111392403103c0c3c4400c6610441e01c024416031074036400c0354000e402101c40d40c1d481d4010443c146104002c241860310b400c0c6400c5141a203844803407652408081c10040420a29032020540d4540c1c245105c3d1302242c1040b000c6544074003902d4001d5076032b802031080d580410168604943c5190140d1102c440901e0098800c00c1a03940d555648003c40d0b00410a9030001040c180184c01c00c418100040d0000c3e2550b40b00f448403040106042614086a55000c2c4940d40020801440956446082289030541c4450911220740b0703940c14007400f5002c80c401604e2203c104404114081e40d00080041c052401902e0ba003403d0390705da80c03044007940c109018850700004101e248226600c10341e4040c00316280a5000e81c1c1d131036519081c03103445100d800e070f1007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 82108139 1250 82106889 82106891
    0x6091008040201020705032a04090203071e0501050403020f1212040f171c030902010c1e0b0603060c040e040809030d1e0801120303022b06140d1109040501090f06 71
    0x70402156010030520300a004120b0080008030000c582c078116006040d80c001d090035441e004038090945954010014495004040e80c08158070f8000500ba0445000e44094014070358000004003940903804032020f5a0300500804005002c180030300c100e021318001c00040d81e10038511100001502400170f817024021b5446111491440d20804140080700440d00701c04580060202040030410403000d0b180c00c0318581404903013802640016150b8652200001c0c01210350384c103105100e001c00c0e1b0b00d00144070740700310700381c244503220101419614042150050010001000203112100051a0032070384184140e0b030305403900340001c01003070429914118450224002e03020200040301e1782c24440585c0da070b841c03401d04880e40c90042500400740600d10050300741070303001035080c401041c00c20840c803004401c4448518820256003085000b41030510030040384d2492949088810300d410840c0c444c41b10740101c096181c42148038100701c0303005000703801240c0640d600c0030060001800007807080344442c000d4030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 82109389 1250 82108139 82108141
    0x212030406030617061f0b040f060f0906022802060d23040201021b01020f1204060f05090306060108060a0801090b0601080a0b130519050c07050d0f050f03040206091008 74
    0x700140070340d07019400c010700c0126040604078451000180b403942c8900c82081c2036031000c2c1d003e0700402c900460b5401c80d010369000024045001507400901070120340e0b0913500c2d5108482c0b252803c840d0b80c2194080c800058015040c042e41c00b10802450b506d81c03a00c0a1041e00f4240c03903039030000303085034031001810f15619142d541400401c840801a41c45e8200a460703203582034031b050381c0000d403650740400800c2c0804288031101080345e442042594803a16000d0b0031180210301c0202000c09603002407082000280001401d076107102d03c00c2003503079080d15000d8020011521400b00540e5801c40040003541c0040d000000016000c0c000d0082d05080750060a50a6450401e10b00050190200400d80c1e080a07003060b01c11060754450724004600407081d04000903260b12407400d0f4005862000010700002410031050010791010080180565840340d000c9480a00c90043c042d0742c103001c140c0145000c00d10610814004800c031000559000b480200814504a9001e0000e15507003090708a000008000c3c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 82110639 1250 82109389 82109399
    0x80318100e010c0c0507030201050f070b10180e120c031903060e15030a1704051008011e0501020715030908030703020d05011a0f0d0e06041a0705070f1b0302120304 72
    0x222400350f2425280c500005454002d44605a680c0385c5488000d04102c80040c1c1b425000c087c040c1a540020750001c070114407400e001c1000542841240161000c8070302c40d0f0151020038085106134046a1988806010388011541c1544401d804c4050000107074081040608001411840f6075100311b1465100000c2c0903040c00c4804882d9540100910b21005401c034403010144c2d000500c09000320b600c40d14456441404054500d00e07405142d12486d00240c000440e801c1c0309400403440c3c1e040c0c46001941c412000201e40304c0c0b9040720707040c0c8501e502603041084180304d842280158103079103450500340401c003482c03981e42e02e00035030384210b032074500095011030715010303415550140c41d00501c400c01c0c000c17009400140400c6a6849840d5003150410000211000d001c54103410501d00c15180c2d5041c1d40c00c9141c9814a4240d000c0708032200041c035031820001903902ea02403c25685a1313900050301b010340226a64852006e0403039400d003402a49002500000142d407250400182ca608400285464034545 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 82111889 1250 82110639 82110641
    0x80408060901060e0103150b060a0306060e030d0c030c031103030a1d0f101a030307060b0108010e040b07080c130618050d0b1303090b0a02030a080708090a080318100e01 74
    0x141001007030340d040007070400c11019100600f03070640b034222111044c1da61401e80c501c002809442c0079203400020206151000ca6013640c020b000b00c07444c43c0c603030b01c007070200700d9040544030503035511a00f0100c0c40030759003080400e10030054082d08a2080c20046c040300c201251306071550f0401c480b81c004840d21502503c1c072001c000411091002d13211401402c0102040b00281c0d1070380084c0841190240d40c0e900460a240d8108044004007540941581d0341ca50542c04c00c0760203441c0c96075045020401c624000101c04c50594101440380d90010034030800d68441c1007089500e030001810b0fa80f440c02060210306d42226140800d04001e1203c0d4480c4207101c0004010401456103550105104495004034440461103402c0d84d00e50040126102d24010b080c5490290341000c003075001342c2e0600c0da02003078a820b019000402810301e61100e80300c03500d0f1680c5151048600000458640900f42c012250903400038241070040c4d074000c2a01c002c1044601410b4a0f45031411004441c1010045e40b0b0790501e100e00303402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 82113139 1250 82111889 82111891
    0x131406130215030717131b03061407050921010c080402011d03031c0204030b0a0b1302040501020c010f03061a0316030b06180303160b0603060903191407020d08040806 73
    0x103414240b07070940c40c003014041c102410018445281240c1903000a0b4034040c007202c2008890760104817a03628500814a80058803840d010403201c035454808da5901d5881320150140c850036091765603030315020801060000b481c0040b005c0d51011701c80038983c1841d44100f030140c40b000d020386550b41c1205240070300004005031000c403d200c0301d080800c50900c809482c08030480f09247e03080c41150b5200c080d0003044e18000c1c45160320180c80000418184030112005402c2a02000c00032034203140400b0101d01c0d000e049204501c02c441c0540d00c0207400300440d5000e05e02c22800e1a8281c18001403255580110f26140748840c01404100b09001003080b0f402c5500407844684017640d480e04002c10188140807a240344141300b001c0203400d000d81401c2d005d603075040080b00c000030a42403a2039416210f501e001e545840090710160b20038000c1d00000b6081e050000b0985215800d8040250145158403800341d03885180c2480c26190004204039480c0941c0350006902c030064800c10764581e40303d181030301141c1020700c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 82114389 1250 82113139 82113169
    0x1c060806090115120209191404050d050324040605060d0f0f060b040e0a0e030d022502150702030114040b01081c050301150203091e031002040e1314061302 68
    0x204200c000c0c80360307446400301e154400b45d05440c80d080c1c68480a90032240a50402054501c041c103040202154641c59190140210b10800440d10030021904040e21b0030b00046403100c281400400b00c1075140303808600c1da13a0000602030300c0010178641382c40100300715502404501c51156203074054190310100510071954080d41114040085034242607644020f40300d01c1c0305140440800c6000b142818030694130900742d001d8240c0440e40e40c0c40320100104040d4010030a491800000307049180c0300c00186a0002d91184c0c4d00610800d808503d1145d140519002410b003a078143d9030f40c003051005200109102c42c012790045100e50303ca58944400f6a02d04802408440d9203801004ca04100854000c0203403415111128460311001800c50070807031440c000e0b0810349034440c16540422a0140d40041c02e001d0809040d81920704c2c920766a035980d0241d2246102d03c2c0403200e4910006003d02010448528109224095607203e0b49040340d0360602d803004c240c402180e1040944240d00461070031000034003a0700c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 82115639 1250 82114389 82114421
    0x110904061d0f07060804021305010f030c090513030f020102090a18230406020d0b06120702010605030106030807080f09150405010e120d083607050d021003021c0608060901 75
    0x70b2000c00d01c40d80b10110752054509012009000c5800c551301d940d100400004103441c10402980d40b414101c0c40c1e070072a48015034046100160114400c1014020b0f54443c803060205d1414803104c540e0100d0b0011444283c07a81113550a104c80f48a82d43d9540010000704541440f0300d8624144c0c2ca20501181d03080c0482a0303404a41403110b05524200611107548660441d50051700c1d070381126042c002410f0880360841e48006c0001e011451840c0116805014060540c000c100d10b80d1208107240c2200c40e9400090030042050100e900001d413104001c204403481c611004d42000080404125107081c1c21154041103500810180281e50380300c2061020102c00300d031222042d07007260102d1500c5101819001c0c080281304000070f10041107484480c003041c10b01444100221051222030398241440c0b4070340c858103000d020030000c0d4518005500001c3c16400400300c49101d8032082c0d0a600a6110b40c1c1e080c1540c414102e440150011a845a0402000750308050491460409512821241003a412100d04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 82116889 1250 82115639 82115653
    0x180806010f0621060308070b0702010b010905041a040510090c03150e040c0e090726031b0c0301060e04030e01170a0e0a0501020c0d02060f040519110904061d 69
    0x1084a50410303000701c4005007000340009140b4007814010f025048510040b2a003010400820442c40310f000302000390141c2c0202c01a0b4a5500d07040742a1002007040c9400200b92a00a00c03451601c0d611002806540d1400580b2070107440e000708090b5101114007592032440c0100420004015018000100c2d1840c601041074141d040c2508014813250f00a6104600d040000501007013480301042010381030402c003050903840d140c0143c0341d039060580030b5000741c0c480c64605185041154140a042983c071180958208003020356040d0700000d800d4102c00280c8078080080c0d007551802c2c4920f4000d040150f0905030103107000d040250402512240752810010104c401e0740710240d10218280e045000c10501141c03074040008441d01e0981c10050142c959440000c1006049600007440b501d045078913000d50b6095514001c0764081242c0855014040e42c0100c0701c0d40300030083c411744003150240f0a2145400403040403004c100004001c503070445140755075951801a5400107880d414040600100074102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 82118139 1250 82116889 82116899
    0x60403170c0f0f0f2a010e060c0901032d020d0b0d030c020103020904090b090303040b010b070302060103021c0501020a08060109080c0102070902070819052703060f0c040902040618080601 82
    0x14500c2141c0d81091250f001043e40b4100650700c030304568520701705100c92681c81030205050003202c5136030000701d00f041d8030f8103104410b80d0801007062482a11001090303800c0200c500c0042d005480101d980304d0115a0441d000c42e0641d8918800000c5401700380d2006031a403845008410444d0352018042d4400d580303849005000941c0f042281c51540c0d42880c0c05030b140c0c0341e074901042c0600969480103042010060400c00d4108001000c4c0d44a40e00844090b000c0d0b99980d001c0864610410304050010b800c4400148050f00740604500318082c010900104d401c0b0564865608903004401c2c900300282642051190341c4d81c3c031034050409052090090103180c43c0d8580042c1d40c0303103006c4c810141601d80100d412003d00480005983d162828807200703103600c0c001c2d0f4400030926409802c440282d01c41d013005164105801e10b00000c0010000b82c001c2041d515002004034171110003c0080010b144100701c041500304031400500f0003042c1e1902e91003c1c582404d209d008900d0007980140060340c2c01b803001084 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 82119389 1250 82118139 82118167
    0x60702060a02030d0507030b4f0b041503120509130b0102010c0807020a110a0302180108012003150f0a0f17030a020304050105031e13030e090411040b030a0203060403170c 75
    0x48401a100709c41c541c27040007601c0601214120030b444001c1c6054594400301e00e481d060f40e4122808000007007000318812000c100001c0b590110040045049100000e0000400d132005030080d18180303052680c20881c1071780001c0c54184a0080e000d00756511106c0100995809010f4002d1860190030318010078581510300035a58080004007606000d4801c100041a45038150340a01668002d4843c3c0c079418000059603d0080f03081c81003088642c60540b02041c2800d50241d04003800c11482e68603841d42d140e4034000084500482072a03075100000c1e50380c405185da5450004d000a100ca810f220207a40d24018031902040b002c06d09038071043d0401c0240310f0a0650110464095075002d003030164072525101c94640c02038080300b90740e0500c0c50000050040c81d500e8036a074441501d10a98410304044050300501000810548000b04001481c042c04d120030b142c19006030102d203c02804503070380560542c0001e0700d410400e64042d00854841903400340d015402e8154142c0c01a90764055610306042020024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 82120639 1250 82119389 82119409
    0xc050906010f120c03180506011a0301030503040512010f0609050603010c0e090610050712020105060f0d030909020d09060603120e03060403081302060c030c16080109080414060702060a02030d0507030b 88
    0x900751559425859a59500075840014440030000f010480c100847c81d1180c4c0e10351b030a000703c0c40111900208c400c01025101e08030b0341601c3d8080042c506103850001404545996212005255502c421610644020920540c0d00401d51030f240822541031100501d4211340703100301141c0401004e0394a1800315100d16a0f01500b222040e60190450503d0b51411511030080c3c2100030444059104030b00012541500154001e9400319222584642d41c0c0c01088007070100e8000c018045281c41c2410400c520b440d5002d41f01c0a414000041040441c50b615a400c55031160030031128440c210100003811b43e8800421000b165083c0e00130711440c10151006003040c1001040340b10801250101d410840d01e840c1c0c00d072102d840c0c03100112a01e81001080840d11400f550340007000070540c0c02800100400e05008461810f40c01107006460541000641c8003407800210303105030001c0301048006c0c0182c0742c030700041102c0c2e2103d50156440380c1311801c00d00d0548101030312410805040c139641c01071540e00c0034100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 82121889 1250 82120639 82120667
    0x31215010e060a0c02090f040228080a0302031c0905100207110a0306050910021c02090a030219030312021905031816052e0f03020909040c050906010f 66
    0x40451401110048075100c00c6060308980200340414400718258002c610030350900d100300d40402c1c0c02e40d42c1180810b0040c0c8201c8001e58008a0f08041445008600d0502040c60304045200a421a180c411061800d02c042c5002c0300143e00020f50900c82101d4105ca004c001012050240081341d003039110703580d44078030809880e65007541c0080c40074100a0f12591400e41404050b00181c20340e61381c3e040c614000c242c00c507244205d500410500e83d80301002c2d07208490220095100664a0307480500005000390080380d607c079081340ca14500030016a5681c800707408103115400d94440c03010305615000b499850013100d45240d5a006100b9412110740c882c5419410940502d0803030788079500c0c1349510680451000e410011806900500508004104042c0c03007035036001e4401c10f400280c100f400301a40809451510300030080400104c1065106080b46100c5210758074025082c50305410004038000d0054908480361301c110315042110342881c856141d40502e090801c4094840111005050381f50302000c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 82123139 1250 82121889 82121911
    0xb070c05040605031c0512010b030103060e150a090503120c1b0708120f070c080106080c0108090a03080c040803040e1801020304110402090a030606032312040b03070302040519170312 80
    0x80b05c0d2103113204800342c0301090201c80103130400796950702d144d0220358020300068852504082915010010005e9008c21071b09107041c400700150744001d4404010005030742c04680601040000304500c0040740900d9020300c0c8582c00031565503440d80302c1444c8009099486031425044400100614200842c1c001c0300954200380042c0d403000c030030134010a01c0c403596200403d103260044003c5600d000540c45101501c030f42404172891400c1c43c80040d24200c50032110307406d69511070108840041d02ca481e6982d000502c849445003429203035040c59045400580044e210000b0150030048202e0480c161100d81c1c101ca0070003149107051a403030790510701c0030100c0000c1c02141c0000703003000c0d29110300c01114011504494204245600c030710f024800b086100c0118a0890203403641a2030180b804a07272602c01400d04051039103440d241a0030f0f00d03000d8000900c003074141507090000081a8550341034585850002071040b107183c0d1305107100d4849805026007a56555172003888001d995040c44035141d078111044d094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 82124389 1250 82123139 82123183
    0x30307030209010e06070c0306150308160503070b04051c08010e060d030e04060303021b0a05031018061107020a060201020a121d1510060806010813030908070b070c0504060503 77
    0x10041e10014101a8045d420603800038107030341846000000039060707c0c4101d00c103021704214100500308444641c0000340c14040100250002c051032000c00d500c41a12500540c2d08110841c5c40c0c5426010040713a050b40c40e5005410110554480c901e03400c0c942c21354038102001507504003c03018039034402c0107101c64042c0104440c041c0030705024082d46401c060000b4414481e16850340380013500c40b44030604028240840328140101850010000c000b5124060b005002305008101d003e0040d0204803e108482c1440260400220740b02d80503004011408450b081d079558071070301c1032000c40c6100380e00a0341107900c1403201c00080d0741d0004000301030080305080813502c090081c01c1300201c0c540304004a400f900c14495001181074601121500c1503884440704942d069850b101580d028030102c1d030250000d4100400100c040c54050030340c2c1020750082c94a072030300c0358072080550710b44800d582049691071408540041044401d01c0c000c805081d041c3d80030310600f8134000102e03554404c80503038060100c001c09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 82125639 1250 82124389 82124407
    0x30209040311010c05040f050d0203060402100c08070303060602060f060a0b1b1b0307080a030507060504080702040903050921120715110a0905190b0d060909060209030f0d020303070302 81
    0x12001118142c8000c0208040d202e0140f010300b02d0390243c030070034038010404000000d540c98010002c1f040c194018000d0320361541c5541c00c0080707000e411101c4400b80714001c80c806003c1624103003c1c0041c10300c81e46000882d01c1c00e01c04041e152000040584422000540030003005440e440503140860348803d4090380c60f00800a10941d15139035040c100186c9204818402d41500c12181b881070301144141c040c0c420140d168100701d51182c1d200d800c0600441c1e82040f07000005003039940100c1c0e00c03074040c1c14001d05044050380090107031a080e07541a80016030200d090b03e40e500d41040c07901e4a002400c100d000300d41010b50052511a411610300c1405c0c000041802000d00514015020200d6041a070030401c41580d40c41840c003641221002000113481058003155500300082c0c0705c880c070005130180e07503096458400180496800008100c5c40c0e02d440700f0002030580e00e640141d0800a1203554003507216441401414503200000f542000c096001040200c44c0755004801c49412500d90b250141e40c0c1c00e060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 82126889 1250 82125639 82125647
    0xd0b0604110d050105010905030303011410030209040e0109060608010603020109050405070915020f01050a02030c0d0903030e030d020c01110421030e0d1b0b0310060804020d0614040c09050705040302090403 90
    0xa41c200c0741d51040c00111003242c02040e51116060729402d8072800f42c1c40d616501032507502d000c240610f400c0c501100d00c030b103d1185408004265498030328a005440e100860307000c5000d9812021a02c0050b80d110702c031b00b90403c6a6401641e0191000c400200800351441c0c000038150201403180030b008517a203201040c0c05900c604901c00140480c041e50300003014522800a603140301d40e0111002951030100030802482c443d0080700c0c005e5160901007400c203804001142e000b01840c4c1d90803024943c1c1c4020f42d840c5030340284058410901817840042e211042c0c6841c02c2e003034860002c440400400c0400c0107000c001c1118400e41c4440c0400c65020004211f07624090702d039040c41d102e89503403004c1810500010800144504140008a91300c1c904600759aa80c2100131408256125800c4030498001400020300c11642180d0190000f0000407001410380c941c00100d4560b003094801031b421010810041c00038950000004052100040080e4070741814020400d018500000b8410050365020509042c85 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 82128139 1250 82126889 82126901
    0xe0f09060604080d0206071205040201090501120608071e0905010305070b0f07170c010f090203070623030106020d08010b0403170318100f0605060702030d180803040e1909020d0b0604 80
    0x1810807130301c950381204000b0f0354403802255148001500c42c1410422451031b401402d005590607100d01408908142c01074401d04501211411460f5690000164400c1300b08680c01c01004541d008014005e403406030540d0381c40076500b107a00302504103001080052400a011001c5a0321405010b4882074400d0040c0550b100b14400600040d402c144079064588550340144241d8014200801c05200c121f900442654070ec224042c1d41030708810420070405004800803d0324500f241c1c000000071150941000f01c0d03400a8100744010b0f17201041200186400c0446c050141c110400c01074142131450340d450884034185105041e40900100205051740312500045d51100301450540c0d0a03210804000c1c0b00070542d100b406000181041c1000030a03042440894040303c0d00a400380164840400081d82d00461303000440400c1c4c40c3d21480060411070510140025151032070207003c044c2000c01101c4002a001d40c40000c0c05454948800f00681d04c40440349406a0f0021986109030f0b1007400080003088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 82129389 1250 82128139 82128149
    0x50709020403030306091404020d0803060105131415161e050102030a0920060906070201021903050a1e0e0d230105040209071e08061302280e0f09060604 67
    0x400071502004054068100d50142c42d82200100000001014421280b00f0300340c4010307400c1302114482c000400c0020004507800001030400c00e1401c001303584040c1e8040d10b26448445007070251004600d01c1e141841f0030b0849240710030b81142c02c0000b84001c0300660b0304100c8000782880040760813000e07140e50000e803144800790030400131910f0f842c100c401c400251010032011280d190902d108410f81c1095605580411340002c0d00440c1018501001c0c0062540100010ba05601c80c280300d81c03404d07401c110f010b1021540311f69140e0b0740f205803180d8090200041c1c031001144011894580141c6554025251841c0034003c40700d840d42c040391341c14800d0040c21540030f550440401426000d9440c641504481e005c4c0d4403d465200590781ca038581114031601d000300108102004024400391948102e0059821040c01048040050015040c40c400ca03400300311021070308031141585d000c03004802e00c1a0041c003004c504101c5900c080150001c0c0145996007401445101c203c004904103440b680c0940b8080d00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 82130639 1250 82129389 82129391
    0x6090b0705030405010c05180112020d090f0b0f0403050901051e03011d01080604080306130f090b010602150622180501020c0618030304060203070302190905030f0109050316050709 79
    0xc101540010560350080303a00b40c07425070a000307040142a1042e41210f070924a07002e441d0340c10044c100011202c14405240d10343c502a001e118041c0d40c61068820002c20324803a07002c0030603030490b500d0950344603072001740075484000a03075080002003074000303089815044007464241d50f2040c88615040c0031118a00300c10071030b03910202c000f28001103015020f20100c24290511011031307980b115456070fa823508030750050049400b88046585401c04034048103800b5442da40214100e0f0a0703010400885a403018261681010600100f184580610100205002c01800c0c135081d03107440400725001030302004152a0640c0d0800b5849032010b12035020407000e11109848a06200031420440c0c040d41046080c0c0303403503008181c00300f021484051502d24040c944000910b003140c0d80e47c0c59080082d00010700200c140340d02000a00c40103560006594650440c0f6100c103a0124248800d161410560701d40e130540700c1c0c2c500844000400c60010984d103688803d003020786503c1c0410b00d481da0500d082588151912 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 82131889 1250 82130639 82130641
    0x1219032303192408071703040303030b06070503030a021c0b010f080a0b1201020712090303020a060c032a03050109021201050f2205060310060506070605060109150905040b04060303020706080406090b 87
    0x3200001d1100401ca131481d9049070501038668030f00300000a403041440069034030401081000a02076003203501e138a180203000304d00b000304540321103040d548211001c04625500041212400386400300108020449a10400019a00701c3c0040e1108030765849803800c1c041c030480002d0800c0400e030402070300b03000007500d1009200c504403441c0f4080c1d0080c0c0300440b030342010f00d4617004206101e44941402c17250598000c00e10003a0359211440101142c851803000c05490b9481c064284400b0f4405856625002c1000b5908101900f4002d08403a41a00301c4480e490040010009200303c0340d12081c1503078012101031aa08d50b00e1000102d5000a04c0c0ca22200224100341c12054000d05a00c107071721942042e0700340c880d02d021540107041110014001d003640b101c804e02c008004074005601c0340340e0129040c103141d100c1c236480ea600080b0918000c8280b40c00142036103030a021030f003041c5c09500c8008805480031f00802d8210b81d030107034880f00107015050410500c003001071309010040c0c00c1400c80369080700b07468002d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 82133139 1250 82131889 82131941
    0xc0a140309030a060b0319030909090c12030509090108030f090f040b03010513030801060206060907080601030f060801020a1704080301060f05070f0c030506090d0801060e121903230319 81
    0xa8011090103510a0081421f504000b0421415074005031382d050b6280c2a0450504030038600400b04581c041e592203030082d101281514187c905110000e0198580039102c0e0241d500b000300d441c405810100b903940051000c0e1440700104d1040e10002002151564450141c40d00868010140403d09940c07660806013842034400c5050b04a0360078900903950251540c0c0c817180c0503a0340700c4080c3c603000e420a1680c00014045403281480c10342081f0145000306000307800030300090540e02d203a0016076170750b50700103560001e05401807040c0e0718460900100880e50324080c0c980c001280070522130081407101c0e110001c20040e1080049600b103690090031008062858102a110b2440074003003120680319140200b090501c00081482841d2400d540f0200702d0303800e2101c00c039152412000342c20b8003c412001b04402d08107080c003e0000300c0c20600603680a040035400e00a042442e001d104070302650700b0240c01d4004144032802c0325403040c6441c0c1590746045601005900030050041a0703032005c01c50a0040030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 82134389 1250 82133139 82133141
    0xc1314010e1603020304020f010c050c100503011719110616061506031505100c0204022706040e07080c0d021c0b01050c0a120504180605010201110c0a140309030a06 72
    0x10058603554004902820200d8050f012440241d5029520a030880c841c5102c0d58410078000c01c6142c800c0c415106000c540ca000329442c101281c600c0000726070040014099020a44005440015100300a00c02d48440043c1c2c841101e00d0410040c20341e5903504420901910707000215100d818012588045d07900c01c0e401d001c002440122600700142c1d841010000300b00384680180c4428a4840300712907811481c0c5003c01074408510f0502d201404800d00181e00983e44502c05002e03241d802108054002e4064441e900c0040c0f904005540f0501041c407003841603042807084643d005290341010ba94a84410003203907070600650b000428a82d00014039024480350440d4810b540031043e0340103029072030048005481c0750281211494a0350320214403000440c0005c42041000072081c00c00b286050b4035a10880003c2d000c081c078443c4441e84030b010400072540e0901c214502d444a0340a11410107049411454540001010243c0003800d00c2d60b54501c1c0c03000c00d0003201d2124200a0031a10212100d10f4004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 82135639 1250 82134389 82134391
    0x30510050708060906041e02120a060605040e010902160f0501020a18151b02121c0903030509060702030106090c020709050906070503180705090c0909070306080c1314010e 75
    0x2584103040801060380a80a070700d6082c0940001400050780d590b50209000051014403200da4072200101a1400c034a601c601c000c050940c150071805040b841c1200aa0f416210168812010000d0411081117a10b40c010030310b60655012500c0541d550319100d400c1da00c0401c00b14000341000c03d81041d02c6080000c154024195480a0f4407900140a41c1010000381d260313440c401c40f80502d10b20350400a00070b220f031580c0c5841c280d0000c0c0c1034034600315075000714003202d1211251481c5944203c240d03103003102c20305141d400c1c0d01045140060f17801d402e60ba4001c1090160045c098021900410240c0465900b074000c400a0039a016040210140700b100086d5601d59a20690314440c0c079260102c1c00ca8040450824440d050503110686591181c00701e0030310985003030441c03030f102e401030913400b042d00d07968441094040e048034001d10781ca80305002d00300b000841c401f820b590306051818000b00002880031032044000201210382c0300c04070308520486001741500e40d1403980d440241c14000719000400741902c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 82136889 1250 82135639 82135663
    0x503071d090708030406050c12070501201305010f0507020d15060602010b0f090408120a0203060906011d1003150b0a0311040b0301030f0f0f05010509061003031709030903070305 78
    0x801403584881d4a02921034800703005452494100300020f0000038000c200524414403060b04444e04040d4661202c0482e40002c6400c5075543d441da0b104100e6200d9030032101d91000e006681c01d520713041c0340c0c010049241d007445c4500c905201c100d040c82e18515009100340d8000c150082e046903130f4890140f0f401c03160340c50601c00303c1c9103113880d285000c124140305208000203140c000d0910800c88807a40100a00035400a02c11181e2010070003051804000042c0b00c40d000300038010300581c8070704000c0108904940010000e80c1080040800341c10354512030304101c0c0d24440c040e03840042640031180220081c3c11b156504808124031014001207807007a0340018403e02582c0d0b41c08019080008510b06030ba441280700c2c20302d405600740014000b00f43c00108003a4110f11544c101141081d040d56000414242d1001c1230312603035521070802c80d1a5105001d2503a01540110600701310605599026003041030034005140c40c84882d000040000340104115080d5600080481300903960741c0c90000da0310103040082c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 82138139 1250 82136889 82136939
    0x904050609190201090306050a02070206040803030910110d0e010b04020a11060a0603030f14070b1614030105010c060207020301060f0e07020d0201050f010504150306020a050c060f0915040309050307 87
    0x80042e01050300d510b203881e598143c0d00e084e04546580c44a101400c030142045560690802c040001070390383d00000c000134000000a541c0783e150407421141000501c4400d40d0840e4105020740c200d44642c0c0003200e20b90704d125130740000c2035117254511a004000410090740c04c10b00c0000d80c00882c98005030034400d500c10b5135045170000d0303445002d9601078440911000740810110000480712138080d03d000100340441051480c00c0010039151000c04540565054800002c00c09008050981c4814040c0c0d6145411020500d15454000000c0401c61407040c094805540480ca003030465400b9013105004100d0605155480741d20384502c200150030a40b07030070001d481070200500311680103004162041084500c2a24107030318013020712014040c415000e031000300c6903110100c0050b41c24405000c58000d07981d105602d400d5210221072900c1c03005402c0100245d07043c030402040c1000085d15207144800e60940e0302558403035180a80314004146c1110380d00d80075030311003c82c03284100c2450440850030360301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 82139389 1250 82138139 82138153
    0x309080412170a0c0b040f05060109060e06030109081e04050a060206090d02011812170a020a1b120c0215040308180103050411150d02181002030a09050f010309020904050609 76
    0x100b100c070107100701e90240e00800e102000700b10100703019100103980103020f40c2c0c03543c0280074070b556a2070800400b600600b5210b81d50301c20906c202c212207444940e0200c0158020408041d694640d80c2150040d039240300d00724100c22845801a50841c2c0c191002040081c02e40ac0ba1151559000394031048103c40c055450b20a169604e81400d105028150514444038420b40b075041141e254103144060101c268003c0c060030101c2c1c80d500e810401145071164602110043c1c89a82c00e9200600c0c200284402d502010088031107003001c544503511000c9210700700e0800e8094800f0501c003003030ba2941d540341c009664100c04203000061000e0000105401d00c0e4000e869005441c0c41001901156410b56000d0441306500c1c8050300142407d0091280112070f00d485c035800c000d039405c03810081e039018800d82c00011050010301085400c12203450f000801290000c0d40c188900e04400402c07044c514440d1a102d12510300030700307210741d0190b0321030501250003400040040c135240c02e00c680e481600741da02c28940e1080341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 82140639 1250 82139389 82139423
    0x8060105070b0112060e030a0207051003060e010e04030e0d050106030620031302010509030a030c060501062c0a05210625110c030601060207030c090501060f0f0309080412 75
    0x201da45140d403181004400307900340402c0703001c01500c40380b0481d0543d980e179504107250382041015050040b015030060180a08000c140400d0216100800c028582010002d00c0045001034056040d034001502c4d03100260b41c0c90078121804d1000e01111500110b0250300031090007019040b042c1a00c0c020030060081c0900c0c0304042c2c00c6a40e00810b8004011800c1c0b01140c442e10500035403000d0540149400c0f0b04244220b40040d044c00080c10088000c5022001c1c841c1c00c2169078000d06005050030f041c10107084001006042c40000a401c3c2440100c0c000070030304401c0d0303903500401c20141ca00500b00360010f80bc030036902c06034844042914409072007658001a0f4503455841c040d8441c000b528440c4151409140c01030752054540c0c29400390340d0045107007a510780c2c9c030100040c03070081c034507907008041c02c034912304143c1e020141d141c02100100d410100103012441e04004071405d08603c07403070b2000c0d55000440c002c4005288424000300500d800080004442c4c1c04c000e2006c019501910883c00f9030f800718 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 82141889 1250 82140639 82140647
    0x816020304050108010b0d09050d020a03030f090c0329070e120604020102030d0216050a03020d1206060806060c01020c01050c090f010203130306150e0a0203010e130c090b010201020c15010303080601 87
    0x25218441c0004c411000510040b08550b024108001d002d00010411920039503526081410300c10400c00140c2c00004101c0074964107004110301007280316003c00c111719880c0c5a0020410490001809607812514440103044100b480c200f0741c00307041101c0703e80a042c4120000e024403081e00b852803080300f00001c0528121300200750103004a5050b0000d51801c80b030143c07103c6c0a50090040148a100c03c1c104100c040f98040c0b011041591007503020745514544403502a00410040140b20000d44ca0100284085500071032040d0300514200d80598640e41004102d034060700c940121540d03603508080c01c0c04100d86541000d00550482120450781610126004a0362805500300030114420000001c00104187c0c1c6d00911948120310a414560ba444420071800f24800b92500502039500000401100040141c801d410010361403203540440810b445030058100381d80190a400c44e07440400c80740b00d038000d504440126221304107407411100503441501182d07209200a0f804540300d40d00090417036200b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 82143139 1250 82141889 82141897
    0x60906121401060e03030408030d050f010e010b030601031e090c05130c0e0607060b1801050a1a0a2d0915031104060305070309081209010c0f050405120a0b01030308160203 75
    0x8241c0000182e0310304807007201c1e2a41c9146076035401d404200030109841009100800c2c000d0000c031004151402c10740c0d18103080c014168011680b07240103400502807030b0200c80c11a9000759091030302281008018a0003c1000601c820f41803c99240498030307001c1010542c2694210780d4212102107414035002d00b110706035840f40003404d0005014a280ba8003924200014100c03140c002d00b000100000910007052240541c0144502e450a0b800c00400c000e14211085101420f5002c000c4020500d0b1106d0170340d6607002c3c03d48000107110883d00340d10b5122500d90b050412107003011031414403e16071a0700c080c0c072200241c0940b00301c2d0302695143e80c0015000b809003090700e20361040d01c14601342c50480101d00404010301100105034650f100341d0702081c440300140417031000e84c1c51540e00d142441d06060342112103030001d40041c00882405503101c10b8101013541c0c00c0381c074140e5404024420080740d9a007801d240c0c51000b80b40c032031110300100901d82e01c02c001d41d01c100c4008a041000402c1030310141d0352402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 82144389 1250 82143139 82143161
    0x40f090914011b1b050609070f050102120301060c11030d0e0a05091308030405012c0d031a040e0c0301050a0b01021501030507030311010e0703030324030c0506210106090612 76
    0x68150040c03c0f1403041041c0c82120355100d07045030030741c0030594400742003030410794440500e94882c42c0180112031884020740d00424003400104200c0100d0071040000d808144034400520044d002d014090110801c441e10402c0740c0102a1140d10008083c041c1440c600c02410714040e189610022501d424403450781d07400764000d180d402001d09419603c0d134900d40d10003041100c05540780c0c0c066159940b4660607202c3d00e81c0555240310b0b640f04005800c1d618103070a94184004160900c2540c1c121800b004203a07480305030080d90045407808116100030314040007503102541640c40c1604002c00e03400190302c000c620403003d03406d4030701c00c2e6152803090000440c2800080c00a0300311800410004e800740800440302e000320000810940c6405650b2410003109074019008039450b00225a000106200e66001c00c1c0404e0424010386800c4d42c64200d121001d5000d0740c0d001d10302c00a5181410b07520000040740200c6403405079455584c40d28002086403040d0701c204008101c00b250021b200c0e2090340101000700f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 82145639 1250 82144389 82144421
    0x50f1e010308040b09031c0210050f0f040221030711211005130807030f0e101416020a030503070203010f020a0203070f031107080303010e06030f070306090206040f09091401 76
    0x9428280c84010907170103800410792601c104170040d415011a410704654152094010307000c642102286242510301c0284489554031030b04003002100110500c1d4503400503015914900d40c1c20901605c96503500c24400018418032000c2400e0080250320f00c3c075211003030001e031398804c00600c0361064000c4180d41ea481c900807641040040203500301c0b0580c0000d80c006a00242032440052607201c00c24541d03c1a80700350001380d50103140301115508400c000484800c2a03c2c40040721040c0300001b0520803480f0294082050006100890001c91209840c00c140d0010501e1203019503a2a0a694a50214104074000d500b031442600400380c10344251064081d20344c010b1442c040d4241d444000c0301410580031424803290800f000e0030002701308034080142c81000006d550342d50400c10b181810303000003012540701c0c0c1c0c001341c1010001a000305020b01140d5000c100812900000d1000806500a642185001b8846007070300041c0e49489810480942c2d003e055010f401d4450001c5035401e8071481c1c02648410303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 82146889 1250 82145639 82145647
    0xa0b0d0b040f05010212040501050609010f260f010608100608070f0915080616080603160317160303051f0e0106053601090905100504021c050f1e010308 67
    0x120b441030041c560442c1c800c4000501d85582c00c40b01c40701c0300c0300640e025601e0b40c0d50b4108100b050b080c410201409071403140740c0000d0440c605085942e510705040c0c0f401e02c0d81d1101168030303804000104083c3e0310208424000344002521882c800d0703a00c0c1d00c14101500041d05081000501080210380c2030300355001c500168080c41c0c201807403070300505080340c0350060458950030000b880c030400748601400380400b0780b10328021003a51000200300b007034040c0040b0f110350808580c1d10054200044800212580800001c9500c6a402c9030388256019594515108401100b150300816a05501c268400d40140e88205a81419445030355000c00301e501480d40310110120040c04818000c40c0035003c20111844030b910300781d5004031200200b40015101c1d25004d981c1005a601d19030301304000b4005002d41040400c01850000d40d840100d603a18070905000c0d560004103280340410140388600b4200340c0400070700942c1024242d0001c101001c448003003a07150300c001d42d14017810581c081281203d030050103450030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 82148139 1250 82146889 82146893
    0xc030307050c10060e0910020f070201080603070b0c0303040311061509060f040f0c0806121c110a05070906090c05040509070c17030603010f0b0d0b0406060803120a0b0d0b04 76
    0x55448081c00003030b075100703251030605103140034095980640102c0c14900500c0c01c0244e07155140c9440c00c6007200b00b090051115000c1007030b6001c10b4070250358091130101815143c0501180c00c2203101d8020315903644000801100c4000000019401640309950706954031408820349512440107480b1441c28070480349148206160180b0140d42182d0010308003600e045031000040d0495142505044031107440711492115550040c2507154001d0b01621001d100d51580440a500c601626078100070035490a2640e0b11054070800b04000d00541f00301c01c580d0780600504002d0741e103101500c22516414105500400c800e0280e0080408603a034540318642014107000402c039035448020429800c22840080180105156102c138248004440d80d001e940c0382444020301d425102007002001d43c050a1850030300c0a0b071105c144494095803c521040481c1e00c5600e0030602510965200e20243d01c0301140515015803820800d074000e541182d001c104125402040c0700311a03031003481c0030703113030080900c00a00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 82149389 1250 82148139 82148147
    0x90a0f03050d021b1002030129040e18250e061f080921090f040f0606261b130506041202040e010b060f0706020c0601080a0b0109020c030307 62
    0x5912442070030454104640200c550049800c000c00c4075401e0304020038000700220060009a482c5480104194919810a000400d04550034002007030380d07401540f44106000050340c1078902408116000039454105036011070030303e48150003048a03900982c07840c00c42031502450510380174040542c8200e86149002d50070a0200d10007030045401002c1811740c42c0c94110019000c13007902141d44c50708122801c0807000d0b0343c40c0011040c9000160840d48040020b409501425a074035404100d8a58079000c40e51400700b0047c02c00400411040c034103000c40403459541000c0d456031888050241c2408407240c3c4004900710b00800d541032294200d0400d600d483c2c0320041401040da0740320520560303d40c81d81e514041503103540580d0280c0c10044980325110114500303030041c8000928903900074004080c02000140f211b1160300c6c055a441d080c00254642003224540640d46407a480c4025501c0395a0344889103512407080600c2140e802c20094004141e2032503038425182c0d441c503c40c00a6041d0703034480354103913 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 82150639 1250 82149389 82149413
    0x506100f0518121c050406020c04020c010b0d0b01080f03030c161b0b030f0105061201060819050906010303020d050415050304060f051003020a06030b030a17070f080a080609090a 78
    0x3100c00040c84011070b0352a11208803072880c00d1040802801504060305140b409600c82015010400908200400420354002001c09608004940060391204c5010354a40101104001c95800c501034100440500001c500c400d8100c07003510301540c0514030b0102c9855105d02c412240310140340d00510110020002154662082601c201d22031680c0f543d60810b07800e240001903204ca0405000082001501032541074410300528090b1002410000600007140301c1c03c105001303040c2081849000603121058000b5a00ca03651005041044203042031005146c071000709000603409071150380c9000c0a203d00c200102e8084601b201100d42c03c1198503181140d00b0fa002901c03d462494507480034004c001c417140310f194001e14a000c404c20101c0e2451040c4103802859a0000e001d051400715100c0b010b88021030800ca940e07500001c000414030102034030100d81c5c000c4100c050048036103d20000d0410602c24000e1803000484c0d10342c001103130303144e808100034040100c0c4c03c4031039a00302242d944000b170b070300b92140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 82151889 1250 82150639 82150657
    0x30201080c0c070506070501050103030e09390a0201090c0b0408061b0712030510091104060c05030705030c030a1701050a090b0d1b0611010b0607020d030909050703050a0506100f05 79
    0xe120f5042c2d442c00060b003550419007068440382d554400400405800c4414841504804d0b260301d0460301e41100d420500e407041407404030b01101200b050580f000c01c003371184c19802c444034801d80d441c0d2405060082c02080302080c03c84038003250450110307604444c1030565044491240040401d55206800340f6445803140314a984078540a005181c00070301c008050700040c90181e5000540c61a1130051040c034840d00ea403080c4031440c070b800f030000c520403500d1049405568080c200740100401601d0814650b21070f0380800f804900011078110030700c01011000780392048150340e8808240f00f02903100e4441d84028402d42c1d0f8007400002c8108038211458104a00300200248400c00810040d1210380f46054482c50010b148000980140210340d0003030941e000100524000300080d22000022540d0b6106e43d08020b8401e00707148051604061241c084c000140841035801e022506110384040c1c040c1409544610b04141071100080603803c058050f10203445a40d61211a0401a0801520198800158 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 82153139 1250 82151889 82151893
    0x1e0212060a03022809090f030f0c05030412020102120301060e090c0c0a110f1201060512011406010503100314060402040c08070207091e020301080d09241404090504030c02040510030201080c0c 84
    0x80003a080300a4480c029100d406400013401c60447c1d85401081c4002142d030f14000c0c0301c080030450380407540010554069542074610065000c440e4001030b0315008201080f002d407640f0020010440e59442a0388003048507040e540003019881c1c0350f4561045004204890700c0c964484000781001c44d15410012203103800181911040d01c3d2600086040c5a051401c1441260344500e020419414610101008880080001c01014800520307108007890090001e904000001c03012500d01081d1310043d00c02941c0c092550f407840613402030026240c58089505030b02c40c5107004071034154a0702803016180301d0703801a40641001414003211000920b0855040000e0400180c2e0f075040c406918030046010b80b03c0c2d04020280b11100c3c0d54010f014000680101c9034034041000385c00c84013913204600b85034440e5542803002181d504d201c1c0c0d142090140e540720184850601080c0803e01d80c0000800c05240d0080d01c0505c4507540c1c0300144040c50103030b480028001401080000c60414001c40601000094401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 82154389 1250 82153139 82153219
    0x1050c1507110d0305240d02040504031803140606010915140d18150b0a0308250b0604060e1003080715060f1404060b0306060d1e0212060a0302 63
    0x22100c0c6464580300070003021035654001c0c001d40441c404441404006da0448001850070b017480407900c444680070f00240151745402c049002c0502903401c203c450081c1c1160200030503603d0a0000d0581210b078100e045a0080501050740c0d944030300c840c0b00545441c882c541804881c50f0720200c0300e4011180811404c000c040c013101c00403003014041e004912003c4c1846a501001034281060036400180214110070316207a20b02c100d64840e00c00540032260041e518503182c1580c440d061101000c55a41031440850340da024100f0028001300c428000c1c1c500f510200611a128401c96400f064159880002c40010700c0701040019002401480d626114a14042203a01e4046a84054650680003034480e42c030414400c0c400d040b07528403028510715049900f032020510f091595001d0744800742c0345502440d00045c0b5070a8400c150380041039070903009080c002501181120b01b900030b400c01044144441d480c40040b40103480c0c1040303520181da0300102890f96035150240d5070302e660483d4510b418110308070a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 82155639 1250 82154389 82154417
    0x100503060705040816050919020c070b12090105010f15031b03020406020d030504020a030201030e0102090907030506010320090d05070f080a11100914041e0b09010501050c1507 77
    0x110006000e81074503114942c855041c41c00d07960503c0c42200340400d0390380c3e51000c104800c0d942c03854450303003000000108200c0b0003001e43c00d00e0040c1c42100f602000303c0c401c1d60400911020144000c008041c1e944c51170704035035201d0a901034260b44080c440c00703a21000e07861041c13040c603a038285007022507030031802c0001c0d07001c03140211a08002082c6402c8000700368007190410000740c06000f030401c200004e2030208010301d441c0c1d0000e000704c6030900010f410550359039188000c14000354104e0303c1c0070030014a03110f403070700d016007000740030304011a203003400681089405062400025941040d140c00810b00350704211550003884204c2d040c0c0003003a07640340700b441c0c000186000c0c28030a44000c3c1c11044050300b100a1142020480306504988050183d500d00140c1c0d081958404036080035200800080461408170400040250201d0724080480e001c0c010f600140880c0d03141c0c4039035821030090340d0010f400da90380c0c0c0c0152460b020708000c00415801c81600b00d5116045c600840380d00c0800c42c100280c1c500620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 82156889 1250 82155639 82155643
    0x21e030312130c1a030a020d0e15101d19090c0e010906060e030307020d050c0604090204170d0203120405071503020d0b060913110706020c0a0c0e0705030f100503 71
    0x55541400140b802c0d0011018031015000e0a800750207800400c50010200500310040e510004105902c9603134003040d9505000f8064104403100241901150400f001d24460500072240944813003114404480300001d6685400070441601601d20300d503036015a503821013845222912540700810140d40c0e913210300000c0d40c03c094080c05070849a000c101c2940c10300103c001160f60700d401074014040207401a00385a81c0000c204c82070b803981aa644240d2041d6881c0c40351800107420101c5601c200017240105042025501520481d082e102d0b0512145500401c0d081e10740b40e08414000041c4c10800c0011108000d404c1c0707068001c3c0c0b0410440340b690f9620b101c41a10060307101d04420010303400141d0301c1d901445034041c14204000444445203400780f100d000806140c000d5030203920040e1604169020a080f51042d1200140c00803801e540e540c550441085e20b514804c20122003070310b260000031941c0030f4a03260b894845e054a40b29646941c651300c0b2240001903005280030041042e009020990343c8003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 82158139 1250 82156889 82156891
    0x403020306040b040317061e030f191506060903031112030708060108060a060f12180f0b150105030609060f040914070501020303191503050a1109070309021e030312 72
    0x201805400c905051400806c201b01ca14442820850100240000c554548800180d00c0903a56a00103241c0c2e040c1002c0307418145c3c0941c00d040140504d0760300b000b0710484d950f40f5020052044030600f040d4141030940c50200c40590082d034000844461080c00081c0c000c11352807049089080440c1c0d541c907080f070051541544110b88103000a284d040a201141d40c02c40d484a0304500222400d812a90500d0001030100c20103122140801190001c5110184a5a400a0404421060510310101090030040b884a1031060101c98a25040340012400010081c50070b040520527904c25145403510381c104120f4440180031b096020003a84e00c4030f55550382c0d44c400c4d44909846072011250700598003880c0b80c2800420340c04981950030030000c102ea0041160000c29107030021000001c0e16003807984007036003d4222034000911074400e8425041c1401262034110507451411980129179998644080b0250740e229900203400142180c000c2c0118100c0700d443c20003003100541164245591814106d0841030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 82159389 1250 82158139 82158143
    0x60303050d0e0a02010e0907091703092e14040e1e06010905090415090c090207060c26070527030d02030f0403030f02120c0c01030c02070f03080d02040302030604 71
    0x40001942010728550740180541d00080b80081d00c0c900b0030035000078000c4c0209941c41881a540e85000580341405442d544020301083d01710307400d20b41e0b02010790303a50340c1c0d1108000e1840784110220400300c89210743e00200d01100a031441040a40c840001036900d8541c42e803e084840b102404040b5150b02c0301007805103c1e0b14141e80c1d00300c05003060f9801e913120f4800503003854100500d00070300380318a848003101d198203d07a01241800902c44560000d50040109040043c114104003000080f11034a0350090685240142020000240006415aa26103840c800c07480000c5079486050341071084040d101e0341c45038060902c145400d02d45015034480e0f00303040440c561507204045400c0d980e1308007006440001201400110302e0b1181e18040010faa004510000701005400312401c0912442401078100020f00745a2144d00c8215040b000f03502da221501b40940040d2400031680451880042d2000880c0e2001903130181040c107548508290358010018031075881e0702007100000586003004210700c514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 82160639 1250 82159389 82159397
    0x20303120c1803060903040308030c0d0e030c0f0a021003051b03011203020c042a05040503060a09350a0507020a060e01020d0908150414012c280f06060303 68
    0x340c4548070b81d550b01c01e46182054080d501c000c3c204001603500104440540f50400a00c9461b41e5662103e00c00e60310036000c01034030641c00d14103e004604800005802038104450917100503282030b852080d80d8002c0124040d612030300000a00a90500030f070311281d004004213207a0800c80c01900100344195200713074090054a4000c0721344501341603046c0a81c00c0400d0701200c043c440c808101680300d141460305040d05038001c40003081d03800c4842c061002c4500405024003501c0141c0340c407400f024010b11000c00306641806031640c460000c1444031000849840f42d21828680240c20349164805903000012003805103c0308001c00005a520514018001e000e59500c081d50807420200090a0a881c039018009210301c1c6841445081008503540144e84141d44580c600c1740e98500b840d15541d8580d5031f00200702d510341000103080c85140e18039501c940c1d500003e404540024002341a0762002540c500042049160710b02405106491051454440c042c0b0101a119203003615a4170032643c1c0e41d40110085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 82161889 1250 82160639 82160647
    0xb090309010908010516030e0a12030f0f0e060c09040e030f07030315060930110405130201020604020f0f130b030c0d0807030804020109150305090c0d1e020303120c 72
    0x6580e020b140380300904400d0000b8003160600c0084940b20b04100c2000f10145510b44001356a4600704201e0344080e10781200e845100b480b051040900205080e031000301855003001e10b40e5280380b03c10300640100c041e40c1c6004124958501490040a0700000910b5038403988038250800d5807042000900340701801d901e00d4076034481d020b28001c0d003122013043d840040c403141c8100c20800c00307030460340581c1107079480460341c00095801d0b420b00c450f09a1440208034800c400311010000c2c003803223018640c004d020a07601040f064545960b10040781101c148005c0c01640b0960000c0c00505180140c1d801c5210060800c60f0450020710000c1c6d9041c0b800c039a403114059807221050304030700e42000b1881698000f070b52040d0148c0c6ea0760700c43c00b5040c801c0300c1d070103018094000081021648550325410080c81c0604242001150f13080c0024081c2c2000e031034081c030a201e00c2c04142d0079450144402440d45078445108036070850f4221013440384505a000607685030000f4800a1500718003140a240705051041140e5070f0307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 82163139 1250 82161889 82161907
    0x140915120312011703030c0a090504060b09190b0d270305070308010501050708030f091e03040e0c0301080c12030706050a051f060f0c020f0301140709141e0103090b0903 74
    0x384881c140d01107126a000c2d85280c007050107000c0100d0347c000d1003180c109940c5a003c18800c0c0e0303030012540c2c071154115140ca4000650f6100f03610160280c2c1101322034546400d003806010b201301a00310300801401140030411750b40d140f0311a0748100c07074170880003c5100b0808000100300300d0310001044242c000c076000056450402d0350240c0c105025140900780031341400c3c05a190125203000040911401101c034101144a000d0300300281030200c0805024215901c0c100d156032602e0360081d02c40e501c3c4481224000c90189142c40060768180d5800c08010a04a5603480c1001400d94001c2e00c05a028003042180f28040b03941405107e01c1030321043c90216450400400d140540814480070249115490605206a5500080c440c00c6407440b450301e404540c10038000151000c0c0d450700c006916618102c2618400895010640d10561f526124030300d605560380341c24003a0301c8141044a62021541d090840080444060081c1e0340006150009450415030340d100c58400003030b140321030039500c0460100c41d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 82164389 1250 82163139 82163167
    0x330f0b130b0c0d0c020d0209160219021e0a0e0c0a0f02010b090403030b031006140102060105010207030f020d0606180608010507030e1903031b05030106090f1409151203 74
    0x5280d9040c507207281c140d2120200303840d812241001000c000098005800390f50720128003020403900184000350b01c0c101054030101d200003049042e401b500480b11000008000c602c62614020303005820746807046024814240c041c40540a0b03150302082805020416840300e04c0c0d1580315881c01d00d0110761f2124001405001c002041001004580c109200021540c48640d49103401950600740801c1d00c40c0c007140040c2c00c1840001c000c0c01200d142c0340c0005006450950f10850b841401c1e025100303035980358801240c540d2030381c1c08050404220100084018108690040c0c41c440c003c4500140441c3c4806500e0110446c40088000c05521044140002c203000e110300c5400c02e01c541010000ca0320341c0002d294841440c10b5810703507c81849050081414040c4e0440d400ca00c14410100003224a5080c0280540d003080c054540022681c1f030000c101824050300a105031140d092510703d840d0109410441120002009426000c1d440c03c807100c49034030386007850404c001c50f40000e10b48600344010801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 82165639 1250 82164389 82164427
    0x9010207090204140f011202162a150201090c06260910050402150301030b040b090604150902130c090509060d030801052803030503040510330f0b 64
    0x19001d501c1040104241141c10920140c9542d0640b2000765100c07070000140c1d642107041c5651910940002a404c4051680f0403001303e0080c85640004032007021807041031010fa5116150300e0481600e260240a56290840c280c444410b091002080b01e000d5035888250100c9c05611000125204007888070070030344030141d4200e4010660841894510f015200c01b940e5400b4078200c070b580310303556601203000d40d150b040300741c07011110902100760b503941e6130b192103e0703180401c41d41620690b000304c000c03031a61300c0007085050060743c00401540006060407200b0303000f0480c41a00300d078401c8082044500000d1640942080040f4030f880340100b15142c101030040c5910020412445100e5241c0443c0c000390300b1048990660f101a180c0914070407034140ca02c0c000c00888070b00d0704010145e0a2001080551003c01544102d100b04180c400c48000d10a44205984401460b0303240303015500d0404009a102c0940582200b00b040e410030f00d060b03a10b080c10381000c24103401c680c400544c0041c3d0404401800c41c420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 82166889 1250 82165639 82165649
    0x61c0c02010c140a0905060304050f0601060314010509180114011403010605030d03021606020301080a031202070308060f060f030a090c06050301030f02010c02180f04050106050307080618010608060a0209010207 92
    0x380080c11241c0c00040070800300c3e09228014860100e004421148603014a0f00505005400203a43c0c2c10b0034203005a81fa0003c911250a078800c100020620500c00c1c0503031440c0c52030300450360010b6424103082050500008194502070070680a05011120f801d0041403070301c101200c803420203541019540391403c600460081d000e03030b040c05810009610b0000d0703c04442d00d001d00e00142c5943e6002e0a032100c0342c18051b8064949800480041075000c03000c070744c894100c4c1c425200e1151041841100c003040e8021100c01a0120703441c800082c6550400998444e100000149124500000b52096044941080c0c8081803440e903a01030b148100800c0f03032558000340c005402c0076821985942d440110b0540e041e64001c1c10840b10311415811519050794030400c20580c2403100311941384c10038840004250445041d900e560800750300003242d007408268542a81c2800018068564680b00880c2c003c0c512002c24204070742d40c411300001c004406100c85401032100c3c40c0f0241c1d17100c490900081c54035540d078101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 82168139 1250 82166889 82166891
    0x2130905011203230c100f0c08040f020409080903070905010e0903360a060c03030510050307030b09100921020105060108180c060d06091103040503070818061c0c0201 73
    0x1d02c501184d0081d02211104903100b4078011011520720040c019801038207483c0c01548901015040308010b00c0d00700d40c25507001040704003c01603408000b15180d01055802804c0c4034078041d240b1000d410250800c00d1400e000c1d071030031413800d001c9602091400c3ca55a00c842c080300c0c1d070782c801071098080107030140b0307003014100000b10b003000141d00e080400441413215094040405031406d01c2c036603c3d407260701c01070110028448440d169480d0780181030301c0303510350341140064035101c00190400240b2480380309685002d80140301190540d80e50716060030000c4d00c89a014401c4808205501151380982d840051240d040e80c10340001c0c000320b0202d202a010070b068150b906200803c003059920028032540702d030404d4414851444000c02e10f030b040c0408146016040100060001e81580c2c05400c540304641500350204140e540201d00c0d08024001510018840e4004000030400f0900c24006854211100513044030100e451100044807079200401c02ca08442940402c00400c40140c440c0d0441b01ca01400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 82169389 1250 82168139 82168169
    0x16021903091e030203100609050a091203150803030a02040e09030408060403450b030402030c061c060e060f010206040309030303050703020913020c0d05070c0e04150213090501 77
    0x40e018144103000d004a03010185841520b410190020826000464002e016111a40302d041402806006c10b409100c03401400c02c00401c0e20800c543c45500389090300005d21000c0c20303039110b8045018103074942503a004c07070180103800b14000100b8401940902c5541500503035a510b0064440e440b541c0c0101010b145401c103000c204012000412003951095141c07a00c04694000c481c40c031480301300d50f10420061101410480d020b4a660042602559031036003840341600d6a40c1e5620300b40350301c8100c800039016003111400300401c0c00c080e030107000302c109280782000c004140110441c08a80c160f5214500704020402400381900b021203d542c6003510030710150682d07141c1a10082c2400d89035210060400d81e480d40010091b0340701c1d0741560320140c0001c11420030030014240300c101a4012410b0310000f030042190710600c070780c01101191640c2c0e030b01058400920f0700e0068020306143e4020415505841c1c0c09481c01d442801e288018400380c44a003101c0302843d810000c100b422140160400401e4191543d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 82170639 1250 82169389 82169393
    0xe070504060509042001050d05070e19031109061807020a030e0604060206130201030b040c02100c020303010510120b04240b040605120a06171506010905010504060c050a0b160219 78
    0x1c072400f010f038001c01c0d2000c0c0d50f00507900403030300c88c444c000303200400380e2071318041c0401c0c164441d2001d00021400c0b91140d8501c0c540f03080400f4580c00511000f00380001c1c00703d2a00680c2002007000354010300080060841808a03c5880040c4030205c0b031200050b00440c1d090000c15810100e003609014050310024101b078140040a0356454000d010300003400710382080601168401d4019103080c0b04060411310101080c40c80c0030b99200c1c1503800002481d424a001200c1c180e1001082e24100c03007005081110906010a0940b000320b0400c2e0451115130f107409107100141c6850144010802384404841d80c66600c818409140303601c207030400c6041640404c010494564003c064400b0050300c0408642d10b511006115001003a050748020100011141580300f0b00f10003240030320382030001d44840d9041c0d039203190046900300058011b0501040c014001071182501c555203800c503561041c41103d647c0c402c542c031114000282119420780f180c42da26402d6907081c0e0305103c0019114440c1d001c00082924913 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 82171889 1250 82170639 82170653
    0x11b02010c170a09140111040303080609130f0c081905010b04090804050f030a0609050102030403110105040510050915010312090504110906090a030b070509090603060f0714040302040e07050406050904 88
    0xa090f06003c0c580b0f4010300000d03c40c20786884100f4803072150080181d4075800b19900d8031500b2030321081e008540f10304006480c9003043c8130014450002c5034840c2c000c0c8010303680c82880d0700741181070540c1d0400150307101158443c3c040080240f000100705003054042c0c2e036840c0c03031400d480d420804103000310300b040b20b44c41c0016469026142a40e10890302c807030103504182c021914040344144054a1242807a50380000d100040d030007503028a000c6c1e91450152004101c2c0b40d4240c81d0140d4004009920010207e00d01d00c0440d8880d981007594242504c0314100b490418500d031034400c2e0020b9800c0c4619a2280340d180da000fa01120041034240d40c1407004011010244455029440e0614000d0000258605070f42d62140c404401640d80425415070070304140600900c070390031545a10740151190004180240f40000f0070a1050561507041803696466070402c0799070a0b2003403102d1343c50300d50070301010005030341c4c0e40549007100f4650802400c07410311b400c0c100416103c00b80d000238084c2d0a00000c2c40081031038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 82173139 1250 82171889 82171891
    0xa06050705070611010b032401080304030b01030b041514070201050a0e1009110a0306060e1806070e150a0c051902060a031104030b0a0b010206060f010504090509030c011b02010c17 79
    0x101d007010994003003000c40c03090246c0401014541d040c010030407580c80c41145c00d8180c40604a4081c0c1b410742076a01c6410f160340d648203a0002600004070540100001603484030156806881400a0354084134402c03019016112003032030988040c602c12081014031542485201c0c0c1c400ca40d42c0c0e05020715900e030154207071a503039a40c0c01042c3c0b06441d0a104030520541e1000c0448118015100030100d0780d5a042800c0201024050680503804500208803039040032034194240084075005040251500c8400b80c851001104d0300d80d030040000d9500ca01d556000300050540f000c010344801d10340031000d00e0604d0a144051440500e140e01844880700580c03141c41c295000d840180c01e0029074030358a0242c4940601803940000c2c107107401042081300100e110703040b01102500a03000ca072a81c0d100c1c9410440d40720070701c10788607001a00500c420010451f0320341055400015040590b40b03412079820b00c0390b003900c00d10b2020082c844e0a08040400456091003850030860940c84e00420040c000c5c040d007480040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 82174389 1250 82173139 82173149
    0x1b06010f03080f04030c081b06030601090e04050a0c062a030818010b03071202010e01031e0228090f1202061b010227040605010302030606033c060a0605070507 70
    0x8070201e035540481c3c5220003200c0165401068406010355030310310959039140620003d608640e2003486030724560400400b56406142d050b190002806d050200e5180c460600070700c142c2d054420155010f021035120700014018220660350201e2800d901c811714880d44030343c001c2030070024460b02c0503000400d511016241d00009040340b80f01d002c01b041c210390760141c00240070580c1d05009100000610071602e01001b40064801e0f04e882c00d070075044500550456038545804e051991800c0c0d110041d03034203254001c08400204640d8076400381c01200500e20b410a100010402042040406020032007048120703000409150010300c01c07001440d4046141400749122100c90800c500700458241103081d0165041c405407625120442e10000c9a0300c1d4240198241c024022803a158000c5034651007402101e210713a00161001c0d1940c0c556440d43c4503e5070810303504a01022900c170070283c40c10058160043c80c1060711002142900b07042e010004a03451642c8004180032040000c8070001c5c82c00718a11007111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 82175639 1250 82174389 82174403
    0x50a080f03040e04080d0513021518040b01051309050a0e03071101030c0e0607050a0b0c250206070c1401030b0409110d021c030207090e0a031d01090e0c1b06010f03 72
    0x7807601d284c05d1441c0d000d5820b5180d0f0b40380c00c107410052000d482c074103030000d10340c003c0720aa5003d00901074048800e1151045082107107101c040406580d0404e600079a910503010700d07245240000360024450001c1c4950415074015486509210300c0c00740500401100c000d0150145103032108542c2c0d00307030480b0a43d40c0c80740d05040c0c480140560042c0521900201c0301d40c00762080b80d84010628226440d00402c9504543d8200f203c40414513031504a8103881c200c520809040a0800c10710b12040d400300120001241c0c040b004015990020b49484a03100c001c041d103400d444031345801000054107075a44d9407504c5000e14606210300020400040381d0b81404242601d46019110040c00481c47c05103032602c103000700014212221013003503800200042121800c407801c024141ca494000c0342c031440c20910107000601754006105205801189050800ca0141407605a0380d9460700c207004455011148080302e410007050a020001b000c0c0349c61000a40c1d250050000756040100140740e010103408040c01c81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 82176889 1250 82175639 82175641
    0xc0506030105180405071d040b01080c0307030201050d0e0d120506040218040903140a02070e1008031c09020a0b0a26070f030b130c0219080a0c020409020406030606050a080f03040e 79
    0x100074244208401f40040710144c01195120620315002201c0c1900c088640c85041e00000501007000f00d4040c02c3d2042c002c02600703d00340b0b103400444d401d4008070b07203100003181c1d01d40034136540580c1000240701404441c0c5603044c8a00c5884c00c04001c42d54000c4c00c9038080c034010002c804c0090340c6091a503000074000c9500003040340d0039040440f900f541150740c10107104000104e00c1250750300042c0100481e04005a08c90150382d404843c0b0482c1074162041c01607a6105001c11007816542840030050300220500016a11600c0e1700082c071951820b500c1002d40c074500080d5450403036400b600d100e480b0b00880406150304c2e20f00c281082a081c10083c4490204210241c081490901c2500716441d5640018100b00603001080200c40040040b00015005441018682e040c000b00721070b00c400480ba0040ca0150800c0e044410507140104000400c981c0150f65050800047c0e0355481250b010b50f010388000a0024182403c0c480003904030f403c000201e5004101040300c40c080081114151142d41e605c030101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 82178139 1250 82176889 82176893
    0x16060906031e0504030306080f1b040203060d080d1e0b030d030e0c041a010318120e0a030506040308070f17061005090d030305190903021e030f0f0301030c05060301051804 75
    0x600d041440c4080341c85420003050200b4175905070000402d4907003540583c1c82820386110081c1e40e808144016000b65941c00300c841c4250325042e03001e560300800c00781c000b080100355070391b441180340d1100c3d04000740305603a104030601d900c10021008030310300c00d007039020805807000000195960340e01c4100802055203899000010300c400780160036402001034030074002c071a20303249603810401d26003004900180c030708010201c840e800003413042c18298002940444c41d848480d003c0300c032640b4103003525400c04c1000d100000018030030040c6a100d0350080d6500c800c1070030110390003018800c03180b03602c1c41080b1400c05042c2804004088032a041003007210a482c44100c080415940b900a08450781c4e4030440c0441280e0034140c250b00194495088482c10095100e5041031400865280460160059006200141030440314200078410b13085020216414124080c0021220b41d01541c0710301041d40d0044010070420442d004060301800302110b0141c199814080030076940b142c0901a10a0102d145003c501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 82179389 1250 82178139 82178171
    0x60e010e030d020421081b0102040e0f040311030309151510090303170103110603070e0a0f05010206010b0406020309010804150c0309110d051b1f020c01021606090603 73
    0x4240500442602c0d2070300480c52245000b90407a02c1820410410780d04154002d0903800f207000c04160740242103608104250082582c01046414003064940d030800c0086611a15051503071300c5001040b042000c980f810f45001400c060b0800604915540144140040c460f8081442c135407950056482070141c0c0d070b0b550200a951007141004607001a42d0b24109040c003a4031020880989000342c5800d0300c2420304162804014a003448090000c036180d40f5603a819107050030055400250510f020b01024510760001851140c060b4801c100b514140c5c0e000304a156010700c6254010080204807d08203480d1090180d00c0e80704441c40207041249500c002010007418860b4547c2a400c0c500041040c40044680a0000c004140c801d80e070744000501000c030b56140002154116903800006490302507030401c2641d00c1038040c54110b55115600c0040001d07110f032080d410080c90321399903005201240c0900d001a0829106928000000e95011f03070502c8070b50f400561036000c035002440c0010b0842034542c2006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82180639 1250 82179389 82179401
    0x13030905090711120307020c0609010509041419020909010302041e02030c04091107050706030c05070501050406020703030506010c0c030201050703030e060925050d0b0414100c080105010309050604060e01 89
    0x964040d01c60014000c8042e03002000001000b101d1044a06003090980316003c14042107507403400685c0b1020140c1c1d8075041c00030143c1749601042c100141070009950000d0141c80103003d002e25051106003c0103106081f42180a101c21031001c0c08604c0c0c00e03061008200803600502010703010f40e484080d940071002c00700c0c01800d41b02c2070041003152039041440f864030103540284280e00245090611038500802078104540e0003da00c18018060b5903d0b010040d005446410745034024411300f1300c1400b0204d1400c0c000d45100342d00c28100141e80348018640030301111000303494141005100400e05000500f0341003041c080d40d809007811a201c203503d10b02100600701540a0211394018182801103414000a8000c5510300317040410030b0400031018494240c1c04281b082991146a00403018040750300303034840c1500715010741c0d025008150080ca902d13240c40000c018841d41640d894590788031041e805050b0380d0240c002460107120014151301e41507503c031005040608059544e40d150180800709502c50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82181889 1250 82180639 82180649
    0x1e03090a0803041103070510120f0e0d020304031515031104020708070f0203100c0203040b0d020910020d090b03040b010e0603010e340614070c0302040204030c05040e07050108130309 80
    0x42e0781c0c0c503051a2200c401c034000c10b80c03a07001c0e1158007804a10344c60141064414150140d80c0d083c0d020060600c200060150380c03412035a03686d5620541680000244000312007410103030002c42d80c1d1071640c5000c4180c0990305540e21000c03843c0551807140a440d21f2241800c481e00b11382001011036010000038000c1c8600721004040e03d80c000341c81410007141c0156410134034001c0f8251104100100b83c00803d0f1780c01c9412010061300104824482c10043c0005090706c29000540141000c03e44804900e080340700f5160100542d010f8000603003240d901c40301c05005403542100d52800d6060540e07421219034018003400403ca180d03000083c000b82c500754480c400300f1462104889101e8018408403441c0d00d161449110709620a813183c0c2000345117540c103a811256641e0720a411800b4500f008070180c0c2100c14112203061018000101690b59800548081e5002e00201d018140c0b900301004202c9556840d0280540c0002408214903070704a0b80ca194032804085056012404030310301103402880325001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82183139 1250 82181889 82181903
    0x160503120a05040203011406030606010f0e03010f0615030c02030a050f0d05070e190807030f0201050f13050a09050709090b040b21010e12030403030c09150f020607051e03090a 77
    0x10440c03014072581095010398000e0307000b001440ba01100005a1803403c0f07444503016440746010407807030b52148103a40b210509500d05a0307441409040001c1c25601c004680040158680b81c050220044d00e07144606081028103040040c80c0076000080d44a014640c030360070030b001d0041510040a0100c07812200300190040d810040f80c80c1c2010007034948454001d80d01d00400701c84904911900c0c40c5513500040c2e9a139140142460b43c5140e0310030080d2410040c04a041043c144182d20202c01c0c0d003806064426201034003034000c1c0b400c003030500c100360702607a2092118501f00700c148401c45400010620a884004001150b9000d5001c0814007400f010301c141504a00c003007400b850815040781000c80d00001b408002e00c2050805481503545003000250701040e81e80800100e40024000e500c0762560000c0ca040080b80103943c0d6082518549a800007103003c150306062030348034541c2c140300710360b80044a03080450030000c0b45da2225002c594840203440c24104000080f801a00007005010025940305c03034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82184389 1250 82183139 82183141
    0x100312030501061b0804050d05160f051507031704050102130e0a05060306070f050a021e0d11031c0b0301090605040f0507050103060b03040633031103030405010516050312 75
    0x20004004100074403920b0700051040e1100711280403107041580310281c000f902c0070b04081c102420403280c4482554112694847e50010100b004010f03c1800020b10440410300d040d54500310500404542c1c00750000c0c145a4108034640c00281c0000d000e00404d1444400d000055480d80744c01c600901c10000c1d44001481c02c0c40000034a04aa5621540310700829071060010f525003d05160792140301769420000b0540240070740821600c00d4002d4000144207204032038181042c0d140c4d0420b2084200c10f002280e41003c1064080590000d201e5030520b02108021403919011074414204502840341c8066081c0c0c5904000303c01c0e64094025036142e07600403100300003d0415180804039590064000c41301e03070003000c0d80000c06600030300ca20030458002c859910b03d944e0321035031094002d01324a6905175030750300071110518450740900135040b052400b6070f14054a440c11800c003a084c1c0007103000503510ac2d034000c02080c06181d0f8060140d03031408200f00207400d4081c5580c036210741940102e403101521400140c2c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82185639 1250 82184389 82184423
    0x902010e040f1a0f09010302011206090c080103060b0d0b0105060f07150e0f010507080117011e0b0406050901150f0210020c030d1109151e0705280c030602031003 71
    0x507000002014002990400e043c2143c41440505a089052503503c00740c2c1100400141d4080d04a9003448200b01e0300c001289900c1c0c500080841d481c00f0b032100000f805010041c002c000340c900c00c100c071500e411140480c480100b592000501941402014010135011a0301320a061002d4190744100398011929000d511441e00ea110007080f614400481d2441041c1902503452018890180070b8425070352504001d0b0b003051a001340b082005564060103640c1c0d1a6110302092241301e0b0f1140710348030100c01007100100c01c030801c001d94001c0d400051191010600400030443c409400442c1c052250404d00200e4a03c0750040e41002011000d0900e50b600004034102d4001001c8000d2940784504072040150079140148494a0301617403c0d440d03080041c003000c0000d02c0b01118080c0c0701c943d405d80c41d03100c1d05441c02d4107440c403590416403040340c50340e20080b5054440c5854040070204500314012601013021075454039401068a480060481035001011503c06c05104c0265030185070031500301c1c804070303c082c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82186889 1250 82185639 82185641
    0x5010e010c0807091505031027051f05090408070c0b0c070b0a0f110f0a060603110f030607030203130b0c03041b0b070305030604231e190902010e040f 66
    0x10251000000c40c0340d030000e03e40c0c50080c107500080c3d45414101822800d011340e01950140d1020348a8601c4480216000411702d911015100e2000002401d8040704d40e540e18030802500e10181076000741e920046001003440c01c0502840c0d0845074203c0708050261654207050280c0d221b4000c0181450f904040040360b03c0400c54020300ca602041c0007140c660656401070090076004000f107080015620008481c10188204071a200c0d5410b41c1003541d00c201c4032052034500c0d10111041c1210500e449000400501c106840032042c15001a03504560480c0b1a8001a844da6401030244080c0355010000c244009030160030388041d41e170700103804207003400c16605204d07040c0c208460894084641802d01081003050384e00074411120781c8031101c6e040c252140e50656060300000d0241e5005a40c0d81d20302020f80c2c02c500d0042154010008e4500700074140700c2c2a03043c8445658810102060b0743d030080c850001d072040c10450303440802000003d541e02a0b480100e071026038440340c0c10b0340141440f0310000840a6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82188139 1250 82186889 82186901
    0x909061c0b040516030b0609061207060c0c050307050a06110a020d140c180a0f0b0d110a06020303070801030212030c0d0801090608060f0109110408030a02010903080a05060306010303050a0c05010e01 87
    0x2001120000c080101c0c88913041445804018036062103100407070103a040030f4071720941150000b040300c04101c0642d9201842e000041d1b110f0000502816107030340500800841c4603001e46420b802030844070341024082685840c4074031600081040c0281c0e000d9582c501403040e25003a0b07070b0003841b2651a400c203041c040d00400d0400d100300d038980100300c80c0503500d1400c5080d440960112500401d0b49655222030a0003d20b080d23000f0f021615240c000080e455641e900002745550b00c9907042c440b50928a0b03060104072001504490155401042032003412a000040641141d5040305c6609204100906480c250302403641c40140314814400c1c9a5035468009a80358140c1c1e1011904000d00c5507203403980b40d500e18050f00c40d4100288200c0040c080080d498204448081120441501d0315540c0c1c1e040303d18503071208061000503591980642d040581c03007240701d07402540403c800d1041d410000000f0361902010300c002070911800003980d9011038058041c655966030031400800c10150050111406401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82189389 1250 82188139 82188143
    0x20604020103050c130e0c04030f050706031104060219020d081c0f020703080a150b0301062c010e10020c04060f18020307020303040308040206040f08010f050703020c030909061c0b04 80
    0x41024009090004d034201558152110031a030300340c0007031901c8000120100060882840c00b64204404408100002061000e0030321034001040c659240aa008044800d990703e01410a2400c00c03080000e10342c0001c1c00c15480044040400c03200b420385c400181130f0149020004c00811001ca0710f0700d400c0ca0039036a00d20201946842c18002c2000e0717105800200d2241008c02004120340d440410a000c805078016a05108210480c850003030700c41c403200c400c1e074009901401c0040ea6090b00050040e480628008111032280c0804036008480c00010b007180726240d124601584181282c1d04003a4800c22000c0c0c6d0030000500104000d5484005c54080d090340f0303000b4101071140c46024006604d100e442140c0c440c00701640903500315195560100c0d0031030702c00742090343e1240051001080c04250740101d40e0003080003000004604035400701540603150300405020030f03d0b2040c04060000c003000b1040340c1022400702e43c0444503aa400002400d001d41da401e00044490050305030f4400c0141001c0f541d03010703034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82190639 1250 82189389 82189391
    0x1104020d05090615030321100506030103050a050c030c0105040e07020c060a030c08090a0206040302090a0906020a0503070206090d0f03020a03060807030507030330021602120d2c01050708130303020604020103 91
    0x140b40c4c003415070341e00c00d0a5644510100c404109081180004440c039040004076000c01c058598034400907001c5c1d00203800030350f0b06400030700c0410200801000800a002004d8015100d42c1a03001d0020741240114800e403045680c8000000e072030180700303015030000200000e001980b54916a2802001800140800340116041d60007041d52440001002080160300601c500d1500741075500b48a400c0701c1c0509180380c00b5072a460800b0004296002404c440115591070680700c0c83d00010003031170a0030180c40340080d60040050040b50780d6003d80282150320301400e002da510050060218010907055112040b5400f900c1d2001c0100072001c0303080012280665101030701403103a03014541945007024058140d08401e0b8801007030301756682d0080c100c1c1445440d402145602c90b0b40100e500c40b40d681c6010000d40c0c020103480001c5640102809001d5000c110b030700421a9050030705500741c40046641d25041c00004511642003000c1c1e0800c4803030075504038000e107003013941e20f1030080d544003001e4400324003007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82191889 1250 82190639 82190671
    0x1030b0907111501050603130201120903080f07031e02130b0c0f01110a09090c050f0c0a020909341211090105060f03060d0c0b040f090c0306030b041104020d050906 72
    0x43e111040980c160754004210b185541c40d443c0d68000c4140c6040d81c1207060240c4a004460600814402e0405890194541c1e50380c924004010541140005200300305040c502104002011044031428160b6141054010b0ba0b80c083c00b0b01c41840e00072250f124404000780050510181d44010a00030742a184040080c0a4101541240f03400c80c05242d03000700c0001c45c180810084440e0f40c0d0821548141103003030481c0341c03407004803984040d58000d500012460344000602c40c1181801d0403104d50000d0000041c184c81c1004107800310702c05040046c80388084828601400322080034400080040030150046d182c1890f05190140c1c00c100c0c0740502500c103504c400d000080a040c400100d407034071003200880a285036600c0003000304046404030241c40e4094134100103e85805001d0082c0064076804036182c903402e262401c1c000c142c0704070044000415003451420000644c1441c5200d8210b42d215180000c1500450b010800a0140e807030071588090030b02d814403c0280020490754003d050b043c3c140716003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82193139 1250 82191889 82191913
    0x1060801050103210e06041203170106051b0f0d020a050124180f02040803070b15060702060307120c030903021507050406211112010909020303030a050601030b090711 73
    0x7214000d10001c1c001c608068064240031501c91300e1031900c0130355424180c555000c2000070450750b0b0403640050f4218a4500014030038150804000912002507500303500b400d6041a600034854015100c552008400002e201c41c2240000d01855489201090868100e940f440c40000c2d55000c51280039201540f0707100040b0310015461b8543d08010020a0324440128640218108101828088815a1030740d81e0301c81e484c00d40c0d60380000c0000381180d40c020341e2110203d090141c0c1324480a070220051b01e08003051843c03142c03038103025545000d0301150225160fa90b241d005891f1841c0d00061000c60510f0181d400301540e4069010018207800b036422100c3d0300381c0c0203006840554080e100740c3c0c00f1850522042006500c0750350b10b0080260000020b0181090740c903881e009a521161748a10054030104807010000c00350640e050041c11071000a000c1315502d0b0300400d440f848041c0c850a400c80d107590004041d030b4041e4001e038400c000d0103400070345545424000140600540b6500311124000c00084900b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82194246 1107 82193139 82193141
    0xd121404050f010c030209100f09090f0f050c09130b06070c0311270a050a09050a06200c07052103160302011811090402130e0102090301060801 63
    0x40710301c1a40b55000d00f0f5420080041d0101403040c0444190b80d0380b1585552020105810610368240e600c1c49c00722003040035a08480300c83c5040103091480c2d84845d0307200d5041c030780013480e00304402d442c1c1c4610f00c6c0c4240304070817212707130b004805480000d5491240c0d4011101680014645440c11b040ea07a030700d5101c0c00c199401920000500d00590003941403d5004a101c08590102c0d6044064405282070122001504400320b640c3d440d0002005c0800641c08201515005002c507400309450340340c400041c0034084107030500c160700143c07402d061001c500196a1030b40134510244c45c0303060414062000030340d240381000f050f46842d149030541e400d00500050801c0340803440b0b080d40c2100c0c40e01b0084c0c01d59240c100d5044403a0405500303000440c100d000010740750351085418040136201c41c00003070203004640c1481d8607102e28204520b0b9903800305500a004d244800e078000c1c0103580e41c3d1801c2c0c0e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 82014389 82194246 := by
  have h0 := BRFrame.cov_init 82014389
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82014389 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82014389 ≤ n) (h2 : n < 82194246) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
