-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:51:50.14967+00:00
-- url     : https://prove2.me/submissions/1ac65602-e051-477e-92d1-c9daa7c5dcef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 447482014 ≤ n < 447661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 447483264 1250 447482014 447482023
    0x70e031e010e0624280806130f200a0602012007050a0303050603010f090c05090c280338030f07030f02060c0a150f0510060309051518061602 62
    0x7038000d0a4004644d00c4000058001405481c10b0b811080018801c0c800c1580140408002d44121000704c45440e103030141000309100c42910010301c11401041040700055224402188842c4044901c0d141450850005980041035810403001070703550781e16210f001c500500040c0c10f0466400190351030302c03203036484927511513840c10009010b042d158004107200380c500f588140d2180e9400e030b0b4204030136209450700d009006031511445118696030b034082140b8200460454154901c40c51881034020b94082c05481403094540c5580c0605135540311141c54160800400034030300e00c055909880940900c444060025a440c0241d0301035801600403c00c01c05000900c24243c07900200011400340e010702c001640c0d0f2046030100801e9006491541041058039075801504c0c4090300c80901a0782c840c2523052044910849180800030700d0580108042406607021008490149088c0c0340d4047d00d040b019415500d0503a00e0382d480c0c416903581c42d031801d10203201c195048801555284600702d40e140000b50368 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 447484514 1250 447483264 447483301
    0xf0a0b0a060f0f0c3e010c030f0905130204181505010c080c07081e060402182508010504060806040206040302120304180209040b011107030b070e031e010e06 69
    0x1442212540024950302440000b05156448501a8032241740081c4580c545c203401d801d005058150340f0340016100704141404030240c80c0696480005000302e0700c0440e4201440c09119040c4104400041303119120500026441d231400d80c4c001d40d50302c0c6080c2e0ba030300208038048000c082480ca0003ca0144007410682c01c1000c490003482d066070030f0002424606114426072003050183c0c8144040001c90510100f61620070115640d900f0301c01c0d11000c0060303512180100c4000358032034030292440300f60101e0010020380103102c4044c60b03141d0500640038808021240c4000c200402c043c031004000c41e180a01850001e004c111001d0a0241040d13408100c150103103002c0203100d865803001e0701c20042c00401c1078070000c00340240c084051030a03e100190082d8480380b400707070080303040400401155003c0d0441119064540d002002e00b545151213480d000040600311904001504400071a960f90400690f030802d40310110310038152007254011400c40d00941c400000e80e030021010011203042842e1200d41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 447485764 1250 447484514 447484517
    0x32003071710020417061008070b03360c010309030503013309090b0904031d0105090a080f100c080c1c0203040b040606091a1309020303030f0a0b0a060f 67
    0x81c1001407031416070402d150078071030030304043c40420005649003800002418040c045002e413206603c82e480d44030846034043c01104107903030103032204000001150009550100d2400301160111110b0801700540b00c4c108220039545010540717110781681e0080c040e8188030394007401c04025180d002d070f5014040b80414481c480c10482010750380b501c4a0050244001aa000340300c14092203c03103180301506039806030140ca00020b24201c050346a50070000c855602468254841c1010180c00388015074044100042c014104902030240306110780f1641d0f2400064144040035080b840300c00c1c00164a807003000c4d42c290701d181e0700306800d0160264000420035082081942140d50711504800100407545002e202c003001035100204220a01445600e842c2c003981c40394100380404d40d504c8074808141d540014406699120110300c6044914000814552842100310040f4184c1d901ea00000c0c29600200c1d03400e54041e094404000c403408552080c5003001c43c0031283c40e0025420020b00511409001c0f29000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 447487014 1250 447485764 447485789
    0x40308040909123932120d0c140a0903020306090a021c240e0c01110c010c060e06010305030901110601060c020d051f0204090c0311030a0507051605030403200307 71
    0x102e40e50090750021502a8000c0141c2d50140c042002505d0f03040d001400d2011010701107007100880f030102191061461140c1c2102a041040ca80c000d01c0c0181040d10032941400045c040c402010125800940a062015240c91240901c1e500600d420000d001b042420075401250300840183e0b206101c50045c110810f9186184044038904680d600308034545c240d800310510f550640609890b50401130030b0010351820f650843c44480015610300ea90441000d019802c002407003047c6500c284030000b40d42c1d010f190040303001d00c03107001140e007030141c281c00540305038000144401403542c10050281d5038465a078024515036240000050400b01150700080c400c80030607a06405202c0100801c0d80108115450620201502c13240003000394414410f03882d100c4d0a00c4070516500380207120f0740628411150350384d0318698401c00100700800000f4a0708050200a00895004107045910401c030284544002c1d983c883c114100800f8143e946000c100340b1403451960901641c0300829540c08a84c1c1204221 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 447488264 1250 447487014 447487097
    0x4050d0b07111c090b180111070e0405100b0d0b0708060d02190609090605031f1b11060c03040f03082a03011701061203080c04030804090912 62
    0x110391000041e5007480042c89040008503c4808000c40c01c040d07141076032600740b10349560b102c2035001401003400000880d143c0b444407000550084d2007441100081205450702140c60382c000c0c90002e8015030701a501030b0302c0950100c1c0f1403006846440e0b100c19040b500408080700603900e890405074001d00e0003040140c03007808a112901d420300e01d00724495005021410040850500741100010f030322402d000030390020340000d8400010b01c942002d544004c0c02604214210915003000c1050f001c1c1010310f00759850b0403e000366480098030380d501798102da60b444140c984a46c1e4103031505d140a0410724101908006000c0010403204800c0007440d81030500f030740715a40d246100041c102101710340c640d4504251803010101020800110306a40304182046c200a00080490382200c06900540e24070030380d030b1200507006c64020140140d00040c94441e0034902912580d80100642103030380300d03290340c0c1e484506c1d6004000741580d0499200f0501d00d001820708180f650710100b0121040d09002c4001c5c03600782d56 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 447489514 1250 447488264 447488267
    0x90e150a060f33030f141e040804090e0f1002040f090b1306170f0a03051c1b0504081b0108160c17030105101404151b05010b010e0604050d0b07 63
    0x141c032015410f4280b0f07407607501c20f0440003801800c3c0e4040b0150380d59241c0784100c83c0f44030080c1c66403800b4403070703500c1d03548504030441080710210031000c1d00c103a074000424400020103088500071040c40d00c0d0034a0181c034030604c40b040100c0c6484030040034a00c1c0e40b40184818003400001c5e4001800b224440100446c8981c042000f00354003802c1080b44d841d98908024000c03802c060701c0f6803045d02c00c040d51f82c2194507110540c0205501c0324409034001b000240200132218906c0c0c240d40703090705140c40c502c400040c07032008070352952010820401308002103540410108000c1c1010702811005000710782642c16003200300c50000f4100c160003480d10500090080c004142244610415070300c3d03690202e030307516040c661808030800c0e503002481024840c64040344600b40a80c400c2c0150071040c14102501824203081034480000d40922405080411500e60403c903846500700c903075811158024400050000da0210004000345100e0790010b0064100308410440d5448105403803090130b030400000c1d100d64841100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 447490764 1250 447489514 447489569
    0xa030c0309020306070f1d090a0203070203191e050a08061c020a0e09070506041404091103030304062414060a031d150609190c09090e150a060f 63
    0x24043d41510070340c410818000d401c44102503101b5016100d5440004561000c2d2601140c2483e0480d082108800880c90403061500910380000d4240140c900705044020841c08007401120614001103c7c00c000002040301e00307201080d00340303807840c04a1030510442d2001e022080064a0f482c0101540703041c1c440c0e00f004221200d1b00681e030091035222016542c0c00b00c511210300035a001c80c8217004500c0c001070289068000c031000ca91209080c038403070b2000c103010000100b10040c03003928224001819200c40d42d40600080d8440c522801000995400351360070f6031160080c0d010701d00d0800410078400d2003d41a0500044250001150486d96810404a040700034194440d0402d8504041d00e4201c000414003055890003101c00e4088694030303540e040200118204240ca0551015199a4a04142c0714043c0c0240040d41c100342031008642e0356810042048845c8000f52a003150003010b14034054020090905c2d0b00704200700070502496062080c0651035048501c81c0c40c0101400724280041c02d801c040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 447492014 1250 447490764 447490781
    0x90a0b090a050618250c02040f060302030a150219051305090105010e090c090d0515130b390403020a050906460305011404050303011206410c0a030c03 66
    0x18030359905032032000400341c24140c00c540c0c102e10a13400c010014012271301c103104500849800a008013181b0f0304d0f60f00c9119410326a00c0103041d50507001c000b401503003c56590340c1308079151070366a801d40d60101b580107013802c00001d4004500c03e50351400104243c0c0e034080e50646402c1c5080f40c91000755120700c3c41d080784034824640351540080b030310540a024440c01103800c8041e610b0b8400072685603a203881040c1e15101891a00074013000d1b01c2000718107030b1860940c0e40e800d603209620482001d20104114401c3c99140b2005400750407400007401e20450800c40c28840080806507251841130900400107840c00b00c0643d030040c95192410a000004a0540e89000c000c040c0c142c040c0a00c0e02e20840c0c00488180c1038002540c6a40c2018450100112650166446690400060740c1540d00f03100c2071401d4803014850588005803200c082e10040109040f01340a04421030400c4c0801c800c40701014111200714800c0c01c280c50345480201b02450500074101c81c00140c4a140c0001c0340035031040142c00078081031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 447493264 1250 447492014 447492061
    0x9040209150a05151e1c0c02031c1e050f07180e0a0f1a1806010201090c0b04060806012a0206040801050403171f03060c030b090a0b090a050618 63
    0x100044c0740a015000145640d40620100802190482409036068841d00343c1e51034280f01804000c0744204c505500558140380144152413405840002c5040c0352a100320307040c0b0200d0317074454042200081c4000784d580107154940d0144014a000811078030f602c000100580180000304284400344c500c1c140c1d401025041046070007446061039085680107091039015a81c0c400d1a250201c041111400030242031008000c152100c6204500c21001e030b844e03800b074030b41415992154508400614842c958a004d0042c0e04542c40e203a515041005103a2040648828140002000090310031820091440d03c0d002d503808000803440c6040c40030074103038800c0754084050f9503c1d03c014841095449a1114810ba0903061078900c10b4a0b03014012051445844030b40e40d200920901c1000002c3c03841d00100680081420700040d0304d071100f804646c400f4000c82e1302404c81607884003a600760b460424007440d0421406401000b844c684100030030040340207042e500642078000800661000e050b51582032851800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 447494514 1250 447493264 447493279
    0xc010c0f060915050f1509070c1104060305030c1203010f120201090518040201030b09090a060f02070c15080c070c0b22082103100e04080706020a170609040209150a05 73
    0x32108100062100b5501024625181c0c804200c0a84500c0d01c3c1b4a0008401004d040182d01e503120309844812036484112031140ca803561105103a03403284a000c3c01140280081d6994003400020f80c0c2c1448111040390780c80f07203c18001880352501300b40d090b5040d500304d2904061311105a0005860815a581c00300341d11106881c00c0503443c0324480c041902440c03003a03c2c103224525590042100c0c000c0202c0300182d56078070124000010810b541c00803101c10203102001480c00c001c545401d1060041e58114402420250141c0c074203169000c1d01e000e50000c402c407800b500309112940c40c01c40f541514403410020410101d0360754000307410080c01c45020805010718040496440f170f00d032070322403103030580401d080ea000350070840a0038120800c5170b208511039103010b030215040090130103004001502c180c800c00024404140010b10620040012120701d03120103500000403c4240140640144064042c00e103000a100040e202c00c3d443c0c0748c10041d89103400300d0041d41c1d600480e5071144142e00c8142d10621 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 447495764 1250 447494514 447494543
    0x106030606170a02030d0f03060305030408150c09130b1908060a1d0c010309170301082107200105090a1212020f070b09180a0516020c010c0f0609 64
    0x446034807400c112190381c100420034829402441c1c0d2034041498010b9010b803c1403851068031403184840100d0410141000910280c49488403403541d08280c00c03904941d0311601203028510b0b40b8050709940040c180c24031900d40681000802d0241080d0f000710381c4042d0703c1d1108180d03540e03265101c2c2e8482c0840f40e5418038206a603080352581e2a40b00743e48102003207103000301d80035000302d205082c02c40f0450a0f1005000454034000118000d044601082d218010309258440c004015100254001e002503401810814800000d83d110f80110801100b65113008112103000034000048140e00042e003004072250042400006852901c103508008d6404030f07040201080f19141c0c041043d402c5401a03040c96456022a0020b81e55003200100d06800c42c0d0150031708011020700f00c8000e0090800103401007130f64000d001e01440e800382d4190381c0d240c803050329a030410094150104103102d0001252009000c1c030506440041d0080365030000180c02c00003414a6030307051028503049400a00d1307200000e00440c94 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 447497014 1250 447495764 447495773
    0x1c1208012421022704140408131a03090d05160605071209050304030516050604140d02130516021b150f040b1b06010b0301050d051510050a0e070e0d060e010603 70
    0x40f1031010910a003410404c600240c2003501c84c00e0103110b00349494011a8999071584245034100700e60744610202d025001107411410124500c0e400609400d0a949905260345454100880d0090010400006011680c2d9507001d98411100142c1c03c01000505030f04e601ea0212001c10142c02d01c620300c0c0c0d0030080030008000c800030040c0304582c010420b1310200401d092940703000c02c605104081d48100240404d100640e01d0a54250050034000c10b0600c14440b03590100307200c001412504400941d90788204001c0d151048081500007140f03102030035980311414080e46150f41c510f00d03850f000352068844481c0403162001255806605c0040c0b098942d036a60b24640e1069000c07003e07403030b045111410300d614403c44c0010101d0584030f201d00302d01d0440e130912040c4044400c2504050700c4a20031081d030154000a80383e00c860041f0800c518010034142418288001c0c00d00990215030b44411010030490465401910540e4602c000c46483c60091014140b41c40600300314050440e0725440c042d000010070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 447498264 1250 447497014 447497047
    0x31202030c010e12190323010612050423030c030309070612020406081b1b01050109110c060105010c0201020a050303010b090a090e07090b1c120801242102 68
    0x14103468003d0014402d081c68003500c030600f00007801560403052003038181c205108010500304440e2031500203100281400d1707140003800e0320318070046c2001d01003006100481e8000510068142d14550501590a02c0d46c1c8010010f013602c2002143c2c40c001c904d40b0f6201e6807080c0304840c49800034108580e01e90030070300c0c0010744450760b070720a041c0450342d0140d401e20401c034039000382c0d402ca4245440e2510380c0d50f0740f592451842d0400911070300c400030341040b8408000565041c00a030b41d07103800d0000030302c41d0b043c9955282110b1000040c031007000814084829070b4900001c2c0b580c1960780a103014040300c2d0b400c0c80140c0c81d184070210000c00d6800040000320b68050b10801801c0800002c4880444990b070b240c841904852001d03400c0030481c0c2004501b801841403540059207621400b60102c0281c412248061049021041e012103902c0001209032550315800502a0f02501c1c00c04801d0444041038440c1001e1001060050400d008451001110b8207124a440c02c80208480c0c206656a820007041ca0800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 447499514 1250 447498264 447498277
    0x90105040203221a0615030f06150a0201050601020d0c11060a0212160b100605030f10050d06021809090304090c09090603030e09070203030114060c0c0316150e060f0703030603120203 80
    0x10542150000785c800d1504541c480c0040407481e840307618503183e82e0301203100d0002c018009074001e811030721a03815904808000b0311912090360300003c2c1506100000906006030a640001005200014003000c1020250b4520540c0411100c860783d0340004441682848000f1044200e45c1c400880c818001c206042d04030b2400c540309074806240c039500c269545804401d58000c1000082c81031000401c0f14200071913035500840581085490256100b000403140c4103840d20403180c141c2c0105021520303901000b001c211a55080350044104c2c50500d07500350380e07030240b8400c07041160b85a2a560b41080d008006510150600540c2409010f0312420301401203140055141d016003044070000754218804019203040e10000000c180c200440802000f581e50000e5124150601450700000c000388e404110340c494802c1c64140c01852180303850200208501c0802100c418021a040946069900c000880e09044840420507440d4062810220002d02054000800039841e51140e613080701d0300040038090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 447500764 1250 447499514 447499553
    0x4021804051606261e0a020d05060a0303050f03070c0501060b0315010f090b0c100e011e021201030201030f021b10060807030c15050d0906020403030f0305040209010504020322 77
    0x242035620002203401c44d11040b5200e500145501c24201d40d41c150041481c1c0103081181008080c03401410021884002075621500440c2d0000d603901e94050300e401000c2e480041180c130080d0382403540d103002c0c02e40c0c480c60070380b0b081d140e070000005910f86009400a03051715800030000c208254640884411a82c001c1c0d4582c0c0e103c00b000107410140d9881200340c11645450780e80d4215000b8603141c280d00a03508039180302a2240a0003825007206d0320036106000c800c0c2e00c01d00010070410440004403605860003000c2c00e00b424010032004d200814243c80880c1100c0d82841c000900500916562009004500c50000703680811391000b822018002031000441d0500d4800700000f9a41c0c4182c1c5640f865213100003070560200e036108200d507109000410b151100c403801e0081c541050042940304a508284045a1541c0d0101d42070007410b070b0100d0601100651420704003d0307410582c0014584040c14440d55100e0740d00080014400c00342074159107000600101d0300c4022400c0c42c5885501500148034040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 447502014 1250 447500764 447500803
    0x10b03040602092b1703160e130212070e0303030727051306050a0506070b0a090302070e040311120c060a09030207050a0603090501050a0b060315031501090c030e0c15030402180405 79
    0x401220b050001c40c1c0c09041f85807036104174008803040c1520099503910f200b55000360340e0301d00340d041128140020f03e8030a18880c42281c240c9400e543c040e00030718107441502d019074018400c0184840c0c10425000c101140c9881141c44e601090003481c440e60800d801c001d810012503c4601c800c1007140d000ba5041e6a0b00b00ca0f50308407252940c1c1404401d014088015007074070070034008104041c0e1550f00080b074043c080d00c1554003070341d155a2100c0c0141403d550880009617003000d0700703000d08001e120180392010001c0c1414681042d1811680d80ca11003e005090f40c1980c45031358108042c000c000c07030001450040e000c80c0400c3d5446402400401c580102501c00303500b00000110211600d1060407060040144600d0039510f1754002c041d0004110304400ba0144143d0340703840031a890401034507008115110000c160101d03500001070544180c1c1c003100d80c160b480b070b480d0703000190f030390076545002c928224802d01d441c0c0c2e890b4000502405128800c1c40200000641404180300d0046400840500f141c85040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 447503264 1250 447502014 447502043
    0xb011e0314030c0d0f05090405040809180109050601091409061f091703090d081308010914100507020712110604030615060e0a0b0714010e070f0b03010b03040602092b 73
    0x5c0e0b40f00c500b000c2c0341e10009481000001c4007841c003a4003041d0403600521466060410384000f003511460800b41d401c3d988144540100241050b5000307546e8402d80070702e003c2c1032661420101034619840384014600c078225020000c0c0442d190622526410520300300021440c03c90f6103001f80c001030560003035040c594900000c243c8a180300000b1100f9516016150f0168040103460b0ba0034150849540300c04032900f00d40f0b0000741c2e6142401000440c0d4003c51600c070f0f40941802c009460022a0003510442e64280380400a000d5000b00781070040300c008550f85402c141251400e0080c103040e2402c01a07020b40701040100c203020842d40034071891030006c0c0c80c08902c6511000b00359050150841603c0d445074034030a09011a0152601030324401d8031600c80e000b400035200000ca829900c030001c06603ca5407009204210740d004815010000b4044401c1141c43c550500306202018480104060005900014208081c0e10380e08801e2400d50308602d0402d114581c10f986032031544034100401d448040610106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 447504514 1250 447503264 447503267
    0x102100926071505040c170309010305060f0d020105090315010815011e0501050f09060a030902030c04020a200f0f0102070308160516081606020310080a0b011e0314030c0d 75
    0x1180c001c160000d0386140280100f079190405040000c00450b8200c803114000100c4941c294054820140e400b0301440d21540044001030444100401103032288050340d641d90120b84880705692221a020b20781540c0d00c0c0c10002c0400e03d4410450309481140ca2000000985034001240344000e007000142c84100c56680c5100000350148482c400c9126002004010400d40d070142c0c0061200c50030034401700b0f04204040e00007070081d030801d006e2400800d0701e4101d80300171417a05220040e100a07045a0450904808080080000d180c403005014000f03000c00740c03415601d000304101c01c1403110640485d030b601c514241c026400307900141c00c1140800c50802c00700780495186e854403000205555212401c280003020720107010074940100b07550b071020811288200c1e5070701c255150482030140102603541d0600750716065140340d1503406410a03070000d5001000043c001070850b41100c0240e0503285031106814001100c01606500040159440b0840d8112451000c00540803003c0b00c44142d80250001200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 447505764 1250 447504514 447504517
    0xc06030103021c030903060e0309010908010501060f030207050a052514010507031d04020c1f0510170f06040f02040b0906150d0204080307030804020a090e0703020f0102100926 77
    0x8020b5200c3c41d02440c8284261103906550300c000e0103494100d00903075a80c0c80d00421503500523234005281d040055810001c1d40c1004661009146403c000c10082d07141040050610307200362104804c00d40c0004000c014030100f0040d1801150700001030f601c1985155162868540c000013060758464080c481c0003c1450105088031210141a14ac2c60b142441c5942c00305c174035049420128100440740c50040b421512640701510951090130002c158085c0044000f090350b001b0040d07070491290030101003000308481e00d0302034011100b89051600b4202c2c4003808080c14208000440d00c0c00e8403443c005c110a100d140813410060f28001c4e1410010950f20702d0900003400700c01c0318419040390303200c803000000c540c44400928ae8200d00810040c14a038544002c03600719071103180b017900050101c900703010642c42c16690880041c6003000c0201b10311441d1100c0c260b00e880c213a100182c403c0c0e0440005030304c1d59009204000b030103030600004100b5042c2e14541182c0444003030344d001103141d81880d481d1070800807100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 447507014 1250 447505764 447505769
    0xa060f08070e0103020f0103090b01081e06060a0521191502070f030f031103010f06020d02030a020d050d0f14040312021c15030b0f0106020c152d07140c060301 70
    0x2c1c10b1100c50307825074080c08001c511407041541055560b94020011034010710307c0780d01920600c0b010746204802980b0107203641d03c075200b14100b250001014005d5039558030240c041211415036628440d44c0010340d250380c20052401c600210b07030242c1e07840a548003030a81c035640c032424415500d00064886d03c8898404070700800030000c0400c022101c1260220b030280320240702d03420b4689408034400c1d40004006140340c01c00c0c5e0042c5400007999809014441d010710088007624200c0c1b00540c10400501e00c02550384c0d0f10702900380709101c0005810200594150400c03030081c660b9600910120120800c0002185400c890960000f05c402c6002048985640203e40c50f001040303920800c0d1604812101000f40022100c0398440010f82c1000000506500340c094464a0300c080c041105600d8104068101203c14904c0d80c8034051403600e0454644407441503800c003a0b441d10907005a1a002c0824180c81001d0755940110800c010803000200071241542e9001e148616050340d0070065140140b007c140020f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 447508264 1250 447507014 447507029
    0x2a090209180408040f0b09120c10080405030f070503130503030a0e130b030d0206040303240b130503030c0102180d0503090d030215070306060e030f0607030911090a060f0807 76
    0x20781100e07024545a150054105000304040c603c0d003a80c0d6040d13020310f20800ea110820241c000300d140e010707500d0300d080c2c40c40c1e01c001715402414520240100240c0d211402129071414014840082410f015040054035282d810800210382c1d610343c203003040c60713a0780c005050044840c4011032011a403420088240c504c000d2858480c070f031542004400f0820b104690248100c07070b0950390ba20400ea07030b41d07041250406448164001e07000c50308290400405403040a004800100000015110a21900d51007002100d504220003905c4110001c031405d62a840c81e4840c03a81031001080d4241ca103e01035009244036034504000702d460100000c240400c042160402901a41091140d41000e04010004089003882031065030100e0550141c6281d03035190030349880703000984c2c034201400442d412070ba1908d6692800c40c014003072a4040080540d0742c0f280140501c1c10941c07540340384000c00500540e50300c420360006103600880d03d03291582c072005003018801d5100c2041c45070b00005141c1c00c007203010820384088 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 447509514 1250 447508264 447508279
    0x200a0608090f0c0f01030c050708121b0304020603150d0b2805100306020901050418020a080604050402030a11010509030a140106270c0e13060311040209011e05072a090209 75
    0x50055004044c040c1c808011301c00e04002040014ae400d00c01040707210100c68100c1e216003401051904086401602400b005030304005000c09aa181c9041e00c0d070114070700d4000c40c05050b0f814046103843d0300c005001803031902c007482448441aa15114609030481172240f04020145d140c5614003524801c0d9007510038841e00920620100703465070000d0480c0c03041810114a0aa9905841d018070840303010b0050b0900c1d80404ca110007170303a110701c8994101000320b40038050313030400c2d40000e0303258045400000c00c650340c1707017500c1c400ca64020000e031100140001c040c0d45805026040081d5689510a141c0c00d981d46801c601007480c3c911000d1900c46001c4120f600c201d14a0390320b500381c0051016091500c20712181c5c0445a43d150344003d40aa200646800003144440c80c52a00380c0c448003501c1c180c0342c8602c1c0107101d0514980d070f000b40d8a5250351005a4001551052228191281d216050020344901d8910400d140082c030565644140c0300a0090420b0f983c40e51403070b056081340111341d01c03503a00206 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 447510764 1250 447509514 447509539
    0x10060e06180d050c0f01050403030509040b01030e010903020a05060601020d12020d020f0c0102070c05040506031902130e0609060a0207170307120606020a060605041107200a0608090f0c 81
    0x8080000d0080850074201c000d01d41060382000800309200c1c81800c6941d41c0c000084148a4245140091002502803e24604003421540d000d4100d010f0424040d01490791a0310a2019030b110f50011004815000000c020714115814000d403075038100e003400d541c1031240101241055100168040f25240c0325541c031100700c00c000ca0010040c0d44801446000e03c0d40a02a00061030760b0b070801041980840c100040e50345805240c028140091948613074491443c20040110795200850700c400c0490f02000e445003060740d113100152180d4510406080f22900c2e0182803080800001420350040400c2c00840c0e07083d07a64111792000f42d10914600521515050008130200d080300e002440c0c00c10014201079220300c421002c6041190255405440144c3c411030301c20040c003046100b504090602540c1c10f00260544150040303d5101c0c10500800a14400324480700f080101c605113044aa00108118007a582e100c900901094040c1c41c5500207000ea5a042681d1a01c000ad4a8003991405850748145a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 447512014 1250 447510764 447510769
    0x3d0e100b0a0518100f022109040e150109050403140708070b071704051608070503071202210c13140c09060f0f1803060c1e1b06040b10060e 61
    0x1c201d10260711004001024039141955007604d110600b000301c0d901e01205510240c07000780740070041a5803e00418a1940690150445030f049800000099034040340750039114016030b242070245450078420119032400840c0303048640d006140540d01a558500591303a846401170202c0c4200c050042484408000301000181c4407030440c0c0e031100242c1028201045948520001074008607402c4450380c100340e82c24040070750130f001900d0251804400502600e420100425511542c40c010381640ba9001076080c0115521148020418114210742c0c0c1e2642c0c07041d2200a0f510481059150306c160464040c5c0c2c0f03100c1031680304940c1e5280d141590b83e981c584400030240441c0d88aa2001d5070051002c108000460001c2c800810581d401c55000550752594020f40d902c8034170b8403d800510a80147c000d0156141160054544003068210410030010700014071880034072959800045502d0400c0803910302c02d10218416114074020711400802d9a03891196410403140c5004010210f80c5144c114081030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 447513264 1250 447512014 447512017
    0x7020c2d062d0705031b0708030a20011b08040b1b030f0714040311090c0703230d0e16090c02100b06071a090d090e3d0e100b0a05 57
    0x50510b2090350710344000360311244d041d0350101c0c034030300d511107004510b503030340c4c0c20041119600800b03008000d1030030121081001410740e0b00600f0142d403407240c40c5821102d010030a60060001c60411440e81003c43c0e44101e01801c520320440301034420f03000c49070016041410300121240341e9031f107042d606e0345180c1e41d6051429007014080c2515082290881c00303070400161a02c01000914014900780541a0f5210104031511400508400040800340103010000b82c0000d0440c0314a0001c0103552800280703500e02840341e000b420341610406041214612128a01040282d40c0c80b0320030300c40c03100382ea84070748420003178911501c0c03042c005034840c4100c050790030b485a21140f0900e10007060030345480710f2b5841c0c0c400468000e0010100b580e50402c244408018204041c1818401600b00202403518040c2042e2112000800821011002d0200041c00c032101001c0f40980003c1d00c082c10410143e03503441008442d009000e10f420022a40000ca001c00d40c000c081d243c1103c1c03113240304034074006001208031b17040e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 447514514 1250 447513264 447513337
    0x703030f02061012111908060c0c0a0f110402030a0b0f010201060605090f0d050a06050603061005100e040f0e07090c0509030703170f0a030506040513051507020c2d06 73
    0x710310110b0500311195561400c00003500181090301b8041500705180c035403d00300042c00080d440003040044c0c005018012420215007600144e08542d5031030b0301d090402a10031140d42ca55481032002040001d8001c131680710702001c803002d64841d000030294200582c01c917480c90003880301060301400013001519110350074202404018025a0301482c041d982e0b41e141c00004ca01c01c0315050784603c200320305030500700012a03000145d03d1145500a240601041c000390f55041c000c01089032489100c1829111034103c10220040d524003042890354040784c4944071429070260784aa076090848001042d8410010303140f036820028042c000c0203203140c1d50340c1556000c444241c22002c0042c06007102c44090326020b000222103030f0f1008910b603e0901c1c204000c5170b900402000c2d000d581800000d000c207030000751000711555100d1512445403183c2c0001e91900104219281d403204045e900006041106040020402c0010706c40518102503041000880e004143c21410703000c10492450f0042403200541040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 447515764 1250 447514514 447514523
    0x1505090d060f0e0a0804060f090f090f0b0603040317130b060402070303110412110904030203120a0b0a12050d020303070c03050703030908030f0f060406060c031101110c0703030f02061012 82
    0x8112850f400400c4c1040c01501054601403400b0404208040c0c1202c50a070701c2081c41c3c54248881070900e4400314840c1c50314052103940f00c4da54429501144000e6010382420140201155168509890010f11100d4820080c0c9094522100440c1e0750000d401c4801c0300d140d0380a0354a58040e035a0f071042c00000c0d0880001a0304154503064104041801100100007070706c44226a0906c0042a081a0158000200d03046005e038012204100100e43d0101c00e44030031050302c0e5100141d6807a940c400c04003070040383c1e11190b480320740450005551001380e105080070a1140b0140d82002030464010781e101e0008848030700200300c000764180d000134890001061070b18804c0c140080da03c0fa03d81c840075082d810460f10a00c5030400441407010416031000e060354030103000c590031300080b414058010804503000100605000c0584044140b01000f900007907113007100ea001c06902c56801908050740d401151000364003180080910f800458400314290340305145104040c0c1d0301d540f8101800300342c4101e0000031742e0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 447517014 1250 447515764 447515771
    0x10e030a0504121e2118050616020616140102040f051003021201260d020c040b060405032407020a031b1b0605130902040f12020303071b1505090d060f 66
    0x3681154100d030804e11403401102c1000b4880c0302041100e620b489001d2921043c031480420007012a0a0000b011099540a17907020303031100d01010380845d44600c00c2320003c0d0300c8500400d01615210550f10000e54190045845e01c1d6160100b400c803508034404c50040500d0b04107a50b0050082d41005060076110312002d20300140341c440c01c50700c40020740d04203800420400195030380901e02300708265024001c85581202800e510200b00340d000c2d5135102c04401a0b0300a646071410841c00d503030350f04152001842d019046d6052001d0764064180c0928400881a84072101040814031301032002038800c10440c0e040d2a4100a442000741c610071607103a0034021121098440149010300d010001c0c610010083c5858081c2c81c0c0407807601d069800000f540140360500d10610007048065004074005040307031045201501c511025002103800d41c4200f8002400144d021005035007d021171540c454200d840036406070540c1c035503020003100c481c800c029006a22654451040010640d50341c444000b0500740301000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 447518264 1250 447517014 447517043
    0x115050d0204060e0a150806010e010c02040e06061804050307080d1b080403021b1e0406081b19030312050a0605030d030614060a020a110f09011502010e030a050412 72
    0x51041e42d00503004200050541c08240c13560f4104411808050f0869200c2e000040b6001c40d40140f00c0d10b401852181002403031460825036900420000d400d03650081c0003407150300840140c65a130380390b051350000d014200c080d0000030800c0c0c48110340c3e0300865120b009507260800d40d449401c242d8000e04649505241d441403021480c0044201034150404903403a401c5042c0750900b806400c00700030080101108115002d250010382d9138080e032000701202c1d241d000304141e6111011800800302038021b0002441882c6a042d04000035034018048404e0498401010b090450740d02e0310b49082505c0003c010480403809500b035001d8a820455008a09000015550ba603480000c0e03d0000781e0a00c01c00400c2c1c2d80c0100f84009120f40180c4c2c441c0c0030090b5103e41c5050005c403c000c3d500c10b051070011b08001c540c0040c4420a0369036002d00484408001c1c900000303075858005c820181c0001c1514000036610346400481b1107140402502c054000300d0b00e070b1a080c1464a40b1222031412101800c0321b1580ea9102032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 447519514 1250 447518264 447518287
    0x6080412090b120702060a0b0a0b0c0f01050702030c0709061a070f020901060c0606050904120503041a041113050403200124061107051f050706090b09010b06090603011505 75
    0x3812407036035a254402000d0800404c0a0304041e0007030300c5c045c5203d0a0003000c4080781c5074070700c071103085900d1480711541d2508032001060810100c080743c02e845500b088180301541758000080c0200203d43c40135a003502d40d4139000b07681203d40354401c4001c1c49520302d5040c101c40041c5030151405a0060f0003600c580c401d41d60018004401c00d03046600412a08080c08013480110700c509805040c00781d41c401c81c1410541c4a01503a0144e41d4403001c00c0081c008001420001040c0310310501103141c14040c0a641854500840c2501c08112810f0140d03803290f038a5095880617000d5207004a802d5140c99103280210180c0b00d002c4401e0351012809076488141da5204020788002040e481d10141221007019414030f0801002800c0d43c11011599521520041c080e6a030b41100701b100959031744403465021291050181c5580c040c2a101810280c0341030251000e011442c10755511940005000700900807500301040560b0007580c0059811400900041c401c6584507241140c01044500b032050506400214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 447520764 1250 447519514 447519517
    0x110d080f24030d081012020607080304031115181b151e0c0c0108010b03060415030519050609031602060711120a1a040201020a110112022d0406080412090b 68
    0x10590b00044d000000c21104503803048900e0042d0400108044103480360303400058040c094500060000c071740c000041400c060141d000041002442c400f5588424030741c501c401e07400b100c01c80d0490000c422480001700c1302030010990744008040324100c41241c0450a042c01804045d40650a036022010083e10904400074699081120b06c01c1403e959100701c010034090a003c0000d0905061142500060028080304400d482d4405000d590000c0e203428803401c0340c40d24624551010742140a00c030f01c440034100c2c100380c8400e00c3c18020000c0b19110b03212a422595644a80c0c4003020b00c010050340000c00625182c00207000e2540581c80700c0b01c1c102a23000009a022086195902540d80098103030800c00c006030300303440310103c00d1440200140c9491340010f03441e8442128000c00d1002c1e603081310141a0701600301d020004004010440d1281c1d0386003c508501d00998402044203102c2c140100d180c0c40c891030440d07054a515a0b43e041081e100c0d9520381401c416503c11301070074000001008610b4105410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 447522014 1250 447520764 447520783
    0xc1c02012301090605180a09020a09090b041a01122004110a030b011d131b050429040b31050f1e010c170406110d080f2403 54
    0x81c295002035240158100403144e41d540a5401034024141c00f003454985a602d50b40c0c072414030200425119550f00c005850511a600101903031842c080800061120079411544210701c2985556007196040c032890030015801d02c80e0410404494030044006802038074809981520081415041a04500085c043e0b410403040e1450058011500b43e07101a854010090203a1003030a200c50241c42a01c03131100c614442024441c0102102c06841c600c8071200d6021505035001d2384502c00d0307c426407210042080d400740c418020380c0c540c0b0801d4a01406081c000c80c0b2200e40000300f00c24581490081c0602c80394000b0325451894000e8040f5401040d07589501a448280c5141078031507980b4140000c100107142e0314181c044c000d560002081c0344142d070100020701980c2090904841035000c0d842c20344008a0182a03502d403411021800045003500002c1c04c5e000a80030409071482c151403803004540c01c0e01e00b01c031f40c0600014070a0102d094a01c4d0148800130a007c64030018100c0240040880d103404400c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 447523264 1250 447522014 447522071
    0x12071406010e09160608131a0f060406080303010e070e0d08070f0b0c09100305091e0a050c0306090705040c050c2a10050723070602010203070f050c1c0201 68
    0x10380401c900d07402c0038008210144455400c56401d039082410081c03100070b008000ba481c000e1f841d8081818012020a104010f18212140310607510f400080c91a203802c0684a081c0110b0800341c01089004000c41079a05880c605c0a0035034490ba601c5408a440ba2000825240c000301091140008112890003c11005000d00d8460b40301e00154034181c410090001d09801a03034800348440070055440c400040100b039040d24001c507054880d280390a0034411200b42c02c00011507a51034048001d50085080241c941c003440c1694001c00700003041c5503c52108860a400640000d40d0610440c82d00764030810130011185006030600c01032000b01454909560000d010484607030044140042034007150f0f501c240404d03180b80822115104000d440c078001d9840090195803404003540f01d00400c0d4150381014440e80d0304071240030365600c00183c001c0d030007070f01c400380000c0013110f02d008298043c00032103101c3d901c54801410811091420880780d55100003081046540301c0c09845110851040d54115001c0c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 447524514 1250 447523264 447523289
    0xb040b0306250c050c150408010c020c031204270605040e0a0c060203040f0b16020d2009160f030e06150a050411031b070b0a0b010305181207140601 65
    0x10080c84894600c84001820000c01c0124180041c0c4c000c035000456940a4800d88841c1515400002d04d44c01203030803003d1250f10b810000b075101d07a40054402d01c404019001e41d0082c02c40c0c0e920281c0c080c0314600450203d20710303003400501c541a40c0c08540c0384458440100090b49a19074000130207a441ca0800f2903803562200d078822003400502c4242e04001c264a00055150178a08081080380290603c034002c5070380d07404900b000070744007204115403005600400d4280090300741e14080110111440b508081e801e0f200c50b41d1001414000b030790500076001c1944108031060408400c4a14100c1c126030001010745076016495488001c2203454040c1090811140880c5d03074140c00e00407100c40c82c1d48118070603410848458000341c41031040384c0e00440c160070f04404440440011007051300c202c000041030384218004005501843d90b2003407810071000d80c3d0a1000341c41c2c5011031919400c030b1581814042e00300510000c90f400804008081541c8280303a4100019061f101c000d00307150090b440301d41041c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 447525764 1250 447524514 447524551
    0x4030804090b0a1809020d050f01140f04030e04020f07060929130f020616030906030b1207051e2718060103081309020a020f1e100b040b0306 62
    0x1400b605950620640382c002103a85070019680c218040003889181e803907550303000ea10654403448114940641c10404031940b080c17103094690f00030442ca040d0702c84040181c0001c20b486030100000039004031b4256440004d900b0010040200030f5001c0b0040d2010440100215400100b0900805504a01815001280840805072b1000701a0200c0a0041c4078082c4802c1000c00108119141d21198200c0ea00e03c10b145c0c024404540785102d80d04011501e802180400801c055000001070261a40d540d02030010101141c1484038010000d1040c2c03080350044042880036050000002002c615082c02d6604038591160108226078548030171051130705940555924640f0001c0002c903000900030003111031040074100f0f071540f03e09040c08001d2107003400041507100c80f280403d140000d010840821995800070440281d601d121007444001c140c042e102552802031003000100868609e440082d01e150b0b4280650900200319500d11240d00550b40c8601c054a5101000414814007411b00744400115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 447527014 1250 447525764 447525779
    0x40e010c09050d030518010c05031b150c07060506280302040510150e031f0c09170706050d0e0708100e06070c030f030912050901080f070207060c03110304030804 71
    0x401c9400ca203000368954040600026801411100c000310700c203d0029184030040d004031844800b00740d0152070b5200114402903240320705c41d03030003100b6141001201d05011601562000c2d8580031140c1031a81e060500c020f40c08030741070342c20103940000c004200c0800d0707030b0446882c03a0510414446240c07881c0c41404c1c040c02141000d110301c54004c9122406850014500500340c0e5405100c90a050104001803c2d04e00254400308a91504050141c900d03020034030f03500480344020514144240006140500009820350350844143c00003540c25016103e600e0030502c2c25105a402401c0e180803d0b981d40000b21045001400f00c0b0000d0580724010f080c0c03000c2682c1080c0203884906140d1401904080140806140c0003483e008106506050103621080e0300041500100094000039000d2980c0c2c43d02001580e5000c001400380c2c94017602c0305c841c00d449003049002da04004aa4500c096801440c040c041140508444144a0310a02d010850b0101003000d081c1503070403c0d4011181d00b103000c1014402d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 447528264 1250 447527014 447527027
    0xe09150301141e060d111903021503150d030203160503070c0906080601060302040509061e041103070f030b030c190b0409060303030b04022a030f0f0904180b040201120209040e010c 79
    0x503040310743c03142611050710ba51b480c000203202d500b03108030071803001340c540100f400252800964004200300040c0031041e110f0447c0e5802103440c08011209101e001605242c420000401550183c0c0114140300803030b4500e80313010402039020340c1c2030b2005100900003d61062004800760640c101c002c01d83c2894603000514058041c0c0000f814503005020500c40c07912407044043e44107404840c00b2482c1000da2014100301003c80048a4000c0c2c10a0300c7c00000b542c8003c0114002c12a6564a00c03000a151400701d049800001c59154950850f607a03002152411300386050102d646141a40c0c60346903540c1900e141c66110340e00032900035483e1042001419094801c1843c1300c2c4045d2415480c080c1500704401e0341007100350481f8030711024041c1e403501c42d030010004d441d48100101c50103070383d13000c0f81e2081c902d02d5000240c0c0c4a00c6142006034580c1d59824800100750b881340c0c031000c08420380d02c583c1d005603255800020840c61036982400880e07000d98683c0a0610307045d90200000176890301401c0014201c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 447529514 1250 447528264 447528271
    0x403062c0303090d030209062104053703050c0a0302010519020a120914070902030609090a120f050702040504030c150606050714150103150605010e09150301141e 71
    0x30390000c0c4100f1811030000715041151059a20300141d6980c1d11500040707250040c1010301802150564024811064120b00280140e0250080711500320f01c604d0b8004041003056040d00e0350140400c0f030f0001c40c91010140700d113058800c2c2011402c0250701c0c0f00d0315281004141043d40140c0d11001030005009402041c5840d103102c3d900290720b0000c0410b00034000d208400d41840c1d8240e5034128007020b000c1c500ca208071140c2003c4060f501415900c401960107074100743ca0481c4160112804984140c034002041301680d6800311007a030316030081728015107401410140c00313000d0002c01c020080c01a80ca502c200c03849180f188e2592480080c66003003040d0045000b0080048c2c107460034034148907071500f20f07081d21701d00b5500c00c1604e00034070300c409101da0802d843c102280d0b0708046500008010822411060a1070103e40d19013041056501d0f00115100080c1c040e1060b0072020040204002d07a80c21025034080c0c000140010414029001c425001840c0031941083d481c2012950402d01440c0d07588181e40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 447530764 1250 447529514 447529601
    0x30d050606090f090601020c03031801110f0c0d06110a0c0302190209011502010915091203050609071b12030e07060e060a0302031008070312080105011803080d02040306 74
    0xc2c085500c000c00ca2211211500a209043c0c52000403200d0780308108104d1001409001c4c1d984415200c007844010380311080c0c6481c08600303d180080e0702220005004407000c0320300703402400c1d16094032082c094224110342c0c003681c0c8a0b482e42c1d051666440e8800c01011418000e998111780c02c006418002d08007141c600c009214a00343c840c0000142e5a4000d103075042d44c003100c55490a01c8080242a401002411001008207020305482c0d0362034922684081030741809040c000f000c0140984040b021200304030384079940b0810b007002040400c1c1c4284402103103804400c2140303a0740503003516000700b0b460302c51411400282d1240c0c01526060000e00082d4000d01d0103003000980c081350100014005d014820b0307420100b43c1c1c044001880d40c0070003080003004080002c142c0300441e40302d0503e50b4581010503440b1011410b075000004003075101e400c50000c1e4545114061105c41d065030b50f2030141e544041c001d11540c82c2c082c8030210106c0c0041c451a480da04100312403c120705203413851a040b110392140e5444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 447532014 1250 447530764 447530767
    0x8070b060a051801060e04090b0109060815011d040311060f19020906030109020304060b0a0602100518030702121f05100503010908030c160c0801020c01240b07060605060c030d050606 80
    0x50b50070250300243c81c15202d150501c1c02e00610801c012400924005501400415004000040d58440740d48020103803443c1409564841e640551445a254400e01c5603000000402c1200703642010641ea00e541c1040c480e2402c0c9a07800c02d0240b81d1450914280c0e803915400c4400340a11442041c0c400c1044100c0c00106400e40c10200d002001840a00051007a2680d440d0004001010018030307500c251172031800100140855511b0701c50081d40c60340c41c540300000091405000c22005460038084403442448100154a051015403e028a440450511008510a0602c20325840070444050490000c40c2a00010f0507d01010702d2816241d140e440700e8000d074549040c074008a100b2800b1281d00c40d050210081d943e080300440020414401040504014026280801c031b41c0c2c410340081c49040c0d41d0600911803060351820b0400042a0b003440c4041203030000d00100560581e86015100c1c1030f00620b0002030107542c0d080454200e038800780c04184141c1001604000f840420f00c98150080400e45071035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 447533264 1250 447532014 447532039
    0x6031407031112041b0e04110303042d090e0109032a0b041a040f03020f1501051003110d0e070603060e0c07080912011a03120403080c0a08070b060a05 66
    0x2d42c01c81c0300c2d081e5001c61200c0040c1c0000e0601c40303190803c811262008100041180e5954403022008000f80c4040301d01d0030210b900c0c1181d82c64000141c80980c1c501609400e4100e550060f20b0300d21102c40e000303580ca001c4180c0d07030001d00c0300c40901c50410004001c2002041c4000c03a803500401e044c1542c02862038100d4202403005120b04282d88000425a100c41e28445c80e031142d00b0504121103032410b00c07403ca001200e040100f08140424121071403171103074088626100c070a1313a425403251850400c80742d1008900004020519203414506e13404101e500300080c040a82e50000016036000c14101e1080b03545810551001e8481041203500401c0340b072600b00001410440101500070001e02074078080c000c0411308030706102084c0c007298404113000741000e41466988075040d029103042041c40030204040760304c840541c200031480d1188200c0310702c0f801e40b0780f50540d41e0710500c981010040d402c241c8540d8850400207400c4500403c0720300e00800b00701e03005140540400c030104070507421960064400c200d56 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 447534514 1250 447533264 447533291
    0x151905010f0b2101030305120f040b0a18050105010e010501110d020706260f0118020c1504031407031706010306030222110409020408060603010b01082e0603140703 72
    0x1c0c1c81940e80840300c0035510464015060b00d064019414a001e403042240000109a0058002c0605d07054029283c11a0303a0341f410402c15007001140e02811105049000482090090340308041d4020382510440218107030742c45580c21910700360002180c5011001c010702c07044d80c20041c508020070b003020050440c00b0319010003d4440c0e01c1446030b1307418030040d41d241103403440003001015603201a5503020182440d1070000c06668010a2040142c10f0388851504100855a4000c54684034032110040080302078640c0d9410f041d09008105804002440750443c003881c90300c00c02050030710300076950f281050006d200c150134031541c050046070516142040800050b02e400070040030354042080d041800386000e60211014003038541100c280c4040000f408a03541115034007510580ea0034400325802662028149801c07205001c565134003041440000030312040c8248809843c03101c0a51002c901c9010144d80040425034582011780070030b443d01c8003c401100d8003000389502040300c0c0b80074824240d08540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 447535764 1250 447534514 447534539
    0x31e063218040f060c08060a0603020f040501270308070507080106180f14070201060e011a1b0c0402070c0618230d02030a05060906010608040809040f09020315190501 73
    0x700e01c41c80d0303808000280074805205480c422064100800784140d4070105002800c11030120740480c42028a1040420701074400e1003078901a4000011084ca8141007170015564451041a141d00d031078000c1c503100710360100c840800f00096101c0c128054888074145001c03810010980c00008003a8900320040099481d2090300e004529250340000070407032030b010060ba0190605081850408038140248a5802e5055218404950400c09240d10507603c13885001790302c9110320044001c50200f4000072002e82010084410700a074408101c800740303051500802c081c0d070007401041e16400c1400e1420402c150300035240000100400f50a500c450703050000903001030005500142d465010711b1400d0001da1500015108566001012655094a24a083d50381c901c0c0407204116a80200400080c096009484031030050743d001d180c8a0038201a0300c1404000c00c1c0f4190750000258803021000302581f421303c4110140003440e49002d21070b2600320b602c205984c2d00c07140d29200700751400c40108422107410380c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 447537014 1250 447535764 447535789
    0x3021b0f0601261b0a0b0f0a1b15020d1b020a0809010e0307030507092f030403050702130504112e050705070608010e0105060a0c0201031e0632 63
    0x20f0303011022098039040842045580045800782d1180d501c400b40030108030811410440d40072101480080d4842c1d0410440740a001600055403030b0510144982501804560b1140c82107403402115400d00d07612080c2e0452051f080c1d1006040d4002200c40c01d0681600500b040001c403003503105400b01c07a10740001d41e1008107100240681a0100d40424140c0c807942282d50b550310014211525540c03241030450312400548121501d4030324140d01c211030a65502061000d217281200440c1c40442d0781101c104c040d07440100304600300b000400c904001690740701052100c40c0500341c000030b07087c9007500d4002c1ca54503508241038030440780b50300c0850f004544c051a401e403102c01030182d42c0c0700c1c59000005888500a4480c018001c1c0107841012030226071129040f4101c41c2540c2103516181d0b0380780c090184500c994802c140000e0480040d03400554083c1e04030041806440c6c030203500602030b030180c1300300b19074043d0844001400722071400380400c040303044244603052060740c0ca540d0080554000a40c421181c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 447538264 1250 447537014 447537029
    0x8040b0d11120609060a0801020f090a05150409020c0c0607050c03101a060f0d110a140721020f0d02030d0b04050603190302010915060501171009020f090d0303021b0f0601 75
    0x4000170001c0e298150048018042a0000e540f038692001585202e900950f4a079805005803030000035040c984440d01003001c0710042035152409040601000107544a80001440c42c0305003441c21016466440003002c0b518042d001400070409850201030400b084c00c4681e200c81803c141145841280e0407284250b090f10465801d9601d17555104036024a000f00040902a14508004807203204900002003009407460750b14200c9030701c80380c00860502c1c01001c1002d80030810941e00505408903540c0c01040703100c2c95004031010700c0482850300c2c2c5006420103d03203005800111b100c160711440341c01196505142200e081c407161601740007083d564009101ea200d4800504800e11042c11300070b40c0010203807604032181d104484468503050015240c1c911455000440444100c0c0000114032407150083c40d101602d02085072400041c1000394002000101c0148000c0141c2420782d0740d60406204160700c251009038903009a8800c91a0100f05240dca42c02134202c10501c00300c218012940c141583e03500c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 447539514 1250 447538264 447538279
    0xf090309060a09050904030c052a01030b030c120d0207080a05030901030b060417010c0f0215010317130311040c1b0b100806070305010509100e010e0a0908040b0d111206 74
    0x4000301c0340600c680d880345410188001c14041030651040d24000c005016808458200c2132b409849207041c180c408900da000191b10f0101c0d1103540c46600015102c000040440e116a4030b1840000c4500041d2035860503640c0c0b05c00080700420380c0503c01680280300000182000500d243c81ea16220701c501c58500b410180d447c1d08607c41e42d0390751020b4501400409801005503800c12110b98020072007000840b0100700748001d005c03440c0e44009005619026274440204141c0d185641d4050081500b4802004480050211210f00d51040c5150b00095028100103c150350f000b40500007140d40e41d6258408000490f07040524070703050240c3c031104140d4071524a104660b62821a100d0b001c00c0758000384000d00441c000c0c80705669242d003040741a5403084502c3d00311900c82d200300e101150580e10400c0700f014091401044400962040158460301c2102d0109001c00140da034002281e00c07982020040d0b0501240c0000c8a00d01e91140d01c0320451201130187c0340c09e40c0d4800200e1251402000544101d10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447540764 1250 447539514 447539527
    0x120c03030403061517010b0a0f0b1b0718151203021209040204050a090c0f0e0f0d1a070c0507150e040905010e0105100603050c090906090703090c030c0306050f09030906 74
    0x4c840f013180004e20315040d00c0750784041c024030403038040c14520074014420381d12810301044000c00c00f000a42140c6001704403d10300464030f48160500c8050240740042d0340103000c4001041604100d01d00a400e80b01c01d0001854401c405041d0380820380307a00050001d80048d01c4240000e900010095a04040c1000550b1101120030000300640b003580c2240e6080714280400040030440f03504900203210303030f90b1140c407540028903074100ca80d054650b584950000c400184014942028200c04107a81d0242038012101c0c0100c10f8039a5a03084e040c0d5503100007558155611040c03000510803240904414140a1141c1d248240010440c0c004072000c64403da80d00c140380f808001c800d50000d2003100c000402408a850b00c0e00801a02c84614401d210109080c400099181000d5500300c0d48040001841b408254841e001400613a40004081d80e042c1550f076142c0d44041000c150304040114403171028003460074151b2420109440c800f034130101104071440e0a00201180c040166149550181d450644404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447542014 1250 447540764 447540791
    0xb040501090210030f0c0e012a140304031202030901080a1107171b0106120b07050f03040f020f01030e060c16150501090b0d11010c0606080f010b120c0303040306 71
    0x100c00ea00080d4071144020640f00c105805810000001c084254108a1340195400a480c410a003548290010b050080c004440006416400076410440c07801161140020750b100d0950885000e9669203550020078100200182c1040c08941850288003079801c0c0042800040c0c1506405400200b4040e00c40c110305103040c0310303907050780d0055030002500300c2c0101014004901319440f40a2103544406101c0c00c620916605024003021100d68513048401006180c503000c44014014000c1d0080280c100103030352040c10f00f980078500a0340a2482d10b00d00312414410006000142100315051500340941c00c04940c00125039998001030305255107549810540f46030012110918000b07000e9990610780e6240f00c08103910160580b00c903c1410080850050100882c43c42c0e031900040001000c4903203104694401d01004a450348103035400300759661240c2c0b0301800e115160b40007211981d9140300780102454001440169145218081d04a0100480c003003a224880c1c0d01000d04075a464009010206 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447543264 1250 447542014 447542021
    0x61a0f040308071401020a08060f0307120b06060712020304050310110a0c051905250b0a0302090414070c022409010c020f0405040b040501060f0e010314070801020f13210b040501 78
    0x2840704d10000c5661702c081d80c002400d8500203590f40d07030050944110a1910b8140081c5507403d851f501e070940e44141c050b650b121802404c0c01025690002003e0026200050100c90303a0350810301190003840d2200e0900c024585000d400521803d001c80c24580c8544101d480c90f4202c4007200381c83d140c841a054840d0402d180703084402e10104606111132103010303092000c00704813803800caea00e510751129402030441b880350a41000d50003803005440c02002800d2030240070354003e224501d00508042800f00a144469401c2082140c03000040b174a960520f90445c9860007080d151a2a00c0c003800460002d01c00001d00c07035000e0350003a5414040b030355004c0020340d950301c030440c003008000400c00d01c21450907103080040b885e419a002c49583d0f01b07044000c1120001890880182d554400d4441002c1c2e20315100c0040880050031a51500d000c0c1038408a0720100a000510310020101441c6580e104050540c480581103076000b6013450a502281c060522102c484c81c4001c582c0140200c00191500e00707000303004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447544514 1250 447543264 447543293
    0xa060c06110c030a030b060c15100f090b2e050a0c020a0603061701020703020a11120111041505040b090120030304051b030604030903060f1e061a0f04030807 69
    0x55503070114003051400b00000080c44025100e50b014096203110000f44406800b071101422403076001200c03400803560f81503e81580c802c17000c6402c103c07a0740d0b039441d110340014025005283da05440d4035049055040401d007100d0085802c65035100b56188000c105180c510202050104004000035001021449008240b28058004241c042d45958a110213401030801f40305064126507494814a0074250620039211115010303005171510a401e50b5500800c0000c120340c02d40d111400e6480d0809048091250034000412240b031075540d18241043c0c5084410160f903075908000c1d042200780103816403031094883c00e14007800c103015809000f142c031031008036001d0040c0e0010710010042005100340021201c2020760300000354010192018103043d205e80c01114060085604490208000341441d404002d2440380070900181c2203c0311a4803800198024000c010031907100e03d802d11038050001d80148800c01c04102051504040e448a000207014610014010200200f0820140003070210300411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447545764 1250 447544514 447544541
    0x313050123090a0b0f0a0f08011202100c050d02010b090c071a04110310061a0405010f180807060806030721080a05040e0112141b0f041506110f010203060a060c06 71
    0x101c5c1c2c3e0344002d0310003040d009400344400140500a01c02d15280c029244281616144110400030361455000d00c036012490007070f40c0b02006101c10003000400c0c8284442000381150358000700e0182d20f0f5000f04200014040c0c00c04560400800403140003032400320b61401c540f07280202c269840e540d103013007810004a54050080e014001c440c45004c00c05031a5000b4070a4030a40c0202052a04003200760000034007c9014083c00f1400281002081302d0140d00d03400800b000d014000700c2c001c4c3e00c81c0d101c0c50030a190b950004011588240c00d20441345010300008025007113505004850003002d80d5103250706040484c0150201d030703001440080480c03280d0b003120041c00f8960040d8015503554090641a03440e06841555141948104400d070b200c4042078145041e0003040c080e02c84810712408104540000540b691760007503450201074240418180308600a0006031030f280010300084100504080c19101e10b500641d2040041250070303a83c2503030791010b40e21240f403c2041c071002858500d0081520f4110703800e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447547014 1250 447545764 447545767
    0xe310b3105120c0f0f010903090e040c03020604060c061805071e1d0a0c0806010807180e070309050d020a080418241409012409170313050123090a0b 65
    0x700503400084d001c4510394950741200c0c00400218401070884280000040004038054010483c0d03055545030b4580140c050010040515926800110958085d83c81940810910081c1a0070720056104400c0881c11300081703880710b0000c070740d01c69803685041d004aa40e40c104030054125000404801c6030090000065444ca8201c0f05039025440b00c202142d40030002800d21000c544643d10422110f80030b40d00c103840b4041507407074107042511860100c1031209141c0101d8100000c180040001c054041e2015032800200308440b810072034100b0111040075001d55102c40000c60028513003070700f03ca086407415030310100d00f000d500da0800080c0103498000102240d80c4210b01c074841080048907012115406500052503004200784027402e40f003440341a880e261703400c1c04100302690b102282401c1824034585450700a4407459003e003500c00000560b5807a500c040348070019081c040c4c410001508007402e103007443c1030070420a1034565041008070007a4500208892856480d43e5160070060591103c403607 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447548264 1250 447547014 447547027
    0x516060f090b0c070b06090604020c0a0809010809030c0c040b0f0409120801090c0c060e0f030406030f0506060c060a0f1814071403070e310b310512 65
    0x80301501032600c0640e0103041400c0803944401244003103a01d103d911010b460b4465a035541041030205000f80004d0b0041e408006480344c4d100309210540d2414452074180740ca0305e0f4040001840c0310401800048180d20800c01180d103124002032100907864111800301d4404034841c00f09900c004180d00a81c0c0013400e02c030030141080300075801028140070729900d9003841e07aa61191102600d0442402c0f0700800c20110114000c6042900042000b208803001c8810302820010a185580d00ca5401500044c0c0da441d2852103c40443c0222600094111042c03400c00b900c000d0b2260729520043c1c01da8071003542d2a001c0e1074244803107400005140950305a81c6262032014103208004031402d0002520314012079074007207108026800082d40d04c8c040500100380b001e040c00070418003c0b8006d01070380001602c01b89900c1442a58405a42c1c41c8544d602482400042514111043d0003014011114000c03050f0000940c03003001c001e614103440310307801e0f00651144031800c015041c84a9883e102d1030035080060310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447549514 1250 447548264 447548291
    0xa050403030204091d01141003020906040e120307170123030f06090f06010906030308010b0a1202070309090e01050f160905211b0105070305030c0d15210210051606 72
    0x45d01072020701000a00140c1404081c2200c100001c56140d08925440b08041c8003500304903280300e90210020780001100c40c605404145040c441344000c0e40c00000c008204a003031540303d81904124000c0501c0010306504107000a805071540000800e901c1010111141a5079010082041940c003542c3c150386942c1040000d29842c3c03590841c0851803031003108000515029284282070880e070f0999100c111a90801a042d942c60344404401e0080101036400c41c001700d14648001c120040c0b198a500e1141803501c0080350903a84c492504811913450481046030000031186800d0384020081010105926421010341d0700b074005412094111208400b0354034500c95201d4901d2040300900101d99a80045280c0440303610545440e2600040040c4540d80003c0c0c05040955041005081e016061269908030b800898012155002e03400c1002e07c020400720200b980c0300e03041f01440103040f210402c15900815240541c140b04101000400501410b605030030405c100d13042980541c0c02c0c0540c407404610b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447550764 1250 447549514 447549551
    0x21506011e020303180c0d02041e0627020a080403051e0f07050118170a1b0309150323040c03020909070305060a0e0a03081b0c1606020a0305030a05040303020409 71
    0x2460018030421001640740100b00044c503801c6c4800c000c003480c1c0f1006696007888023803c1205003100a51440402c0991b803d15540202070181c00741c04448050404600142441000100c2c0c00a001c1c910401071100c4131684228001d5026405040103903481d1642e1802c4540014080f03011042c8903004a054040000004e0052110b6401440240701e809205822503610144404005140e00765400407051001c036654003414a81d14181040f00500500c41480030001071120411000503030448410704c0381004100248843d04010302d41007100b1841c40d15001030107400014401a2a007550001604009202c00c0400146034050140a0f050070225803890369603000c1d0004641d180162030006030920070912480d00a17508000c000d103144002501c003030b14001c0020785003500345000059040c941909480080007a9030a10008281da00004444c09040500a4004001319008985900023190780001541d4204019400014240c1c486240c168004e01c2603501610007c0d00780341c1c00ea40d00005556 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447552014 1250 447550764 447550771
    0x30c061509071209080706050115030f05060d170906070302030d050601080408091c0b10080106050f06031b0c1504020117160c0204090b040c2103021506011e020303 72
    0x168051002803050208103405100300c0e030190001c0d40e25210f9250282070341c1c10424280b8000c800705841c01d500c4c5d81f01c000c2940c40980050060080c805000640d0301e516103e80c0054500c410030400450a0510000b80c5130304025001502c800d08903006810101d500c3c0d81101c07290f84009103002d56034062481c0c065240d0f0045220641509c1c40c1c00001411540100c00c140e2155034817a00403464500450100810b8030500740c10b401541180c1b140c06000985000920707030240350089041d00c40707d07241c083d0351384c00c0d0303800c41d04102d001d01500e03060070b0032a072641c00541780c109007265071191648040c005028610300844440340c000d407061842103100e5000840006000303c0c001c0e0f07148801610750000d8660f40c02000e4901800a298072401c4055180c820080710348101c0c0b00400100c2c5400c025103070f1002810041e6410b07108540e01c03403001c11016141c82524200c50581c001442c020840b5030f20043e480c2c0100c90b5941c0d42d031240040c00200584e100304407440500100d00d030500805408800000c0d81d941049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447553264 1250 447552014 447552031
    0x60c03021b0102070b1b070e0105040f09020303030a0b031606090e0106020604050a02090a1e02030601081308040e040309120b100506090a0b0a05120f070315060f0f11030c06 76
    0x1c003010703038000d1920948072591071010f80090000620300b400d09100c1c1d038800304081000603225490000d031000c05000c1c0c1d40081600e00c29090241d4102000c00c41260210503220f800149021411030050320044152941300300c88400001e2000c01480c0400d040000201203908020819100850b645401901c4082030310b03a054a1503402c1e80e00c4030b0040c0d03641c03001a64007614a41c841c0d03c55000601e0300c004c2e4140c2c040541600842c03007180c41c000c003602084a485284251a802200300f0103296488036036244d00100e1b209035440404401d456003841e074415805400111170024001405242c00b40b803001c4001d142200d03000c4100d9585041c50180364000352410941c010f07000ba8001103915204061312503142c00140920522881c295110f5040d40c0030141407020f20106000c3d4200e05031071308401074840c0409070400d04052a0030a0001c042366a185079840c3e2403429000309210580c2d01a140040f802c01c903080151441a000c00c040d40ca52003203e0140c02d05100000c3c007200c150002149260041025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447554514 1250 447553264 447553273
    0xb0f090c040f2718060903021015030b0f0402180411151e0a0f0513030f2103110703202a0604060206221712180d03020c010213060c0302 60
    0x14042501c040c0d4640c44c2404c06a06413508816000c5a0160311030060144a4011140e90043c0c4600a0050700d8030110080042100300d40200180003111054503441500ca41445a99180580c0041c0b02c008090320400342d03000e06d00d4000340c20482c60782e203130340b8144a0041a8a940348000c0c10060402d0b40002205d541010200c0d00360050401102c05641500400d070302d500840104c5404111296005800c40369400060040c000020480d644030084000380200302c0d044001d07400a508800c440725103002c1c06c04044c9013100e020302c0b018601c0242c860f00b55140c5031650700b941c400c60107041294084d01c500301080c00ba00b0904500000d010034006003402c680140721421030214410041180174510480d00560400c00000d000000705004501190324441e40f0030141640ca612585200c00203200c50341c0c0362030303400900a4800c00d01c8200040d84031122100b13a1703d251303880c1d260141e112801000180e05054001c505000c0c05d400a4040c0d8000c00c04122880c2c000c01d0341d4240040c5035141610050b00507014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447555764 1250 447554514 447554579
    0x60f090804090c0915030e24010f170304030f0f02090f010f051203030a09170d0c09120f0215090909030405010e06161104020c030a020105010512010b0f090c040f 71
    0x7413903644101c0f031013003005602d1180c1109040d801781c07511002039011805580c8615503a0b0007a041100b00342c0d500800865110343c18805903504880094004001c000a042100c02100c0d40010441c3e06907580082031001c0302c040d40c540b5610000100e10001c2d880600101040550010303888031904032440450340c501c1c3c080e0b4030024014070952020091105810070400541c500305241c00c801720003485010f20032002c410154403d11242c00072039900c20000d842d5211480300c1d940c4051400040c1804070000c818070000d581e0340d6500518035a80090060002210742c6180b6400402a80c08400001e40151900d18200c0c000540b079610600403070707000c111440942c8916007800801c0d5184811446809000c0904035241d0212030704c060500a40d00c29020003040307503814030034406050b5040980d0004291541402d0800c0403581b01e9804090721130307250100f040255510006107012184068a400d06680c941c11464256841240c1016a4402d17504e5000101085010011a01a201400010115034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447557014 1250 447555764 447555767
    0x10b03310f0302101104031205040e09010e1516120e010f0f060e0f0a020d1503141c0905010c0203010e06070512010b030f010b0306040603050d090609091b0507060f090804090c 77
    0x17041c400d2903032a00c6600744070a100040010490310b0780e01c145410103604140d03032402e006030404000c45058405035102e00d80c0380c00c0d403882001107841048014406a07032902d0030300f031005001c0c507058100c1e904001c40303400780740f4145100d944030381c9030380c14404003c2c06500d0640440b000988000e8030904165494a8400605118070711559800f44100c40407266440c2c0f0380440c2c46020750032450002d001d240d03842d020607000c1c041164248004600c00c1d50343d5850b10602031807083c00c100390031385000c0319414008041b0b100e560740b0580c00c000342c44003401e280e0200c04240c0041303401000b26040f100c045100382428407a02c95088006031502800d21f02d100b02c11a070301d800840341180403e0b1030403a228208000180801d040c0321f00a140d004101420000c3c0c1140d403030300d8282c81c041034403900e00082540034100b4407205030700410010190104141c2449002500d41028800056240442c2c081200100d01182003080c50b0300241068001c55209000f09001410162a1580b05104010100d840c003030f04443e015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447558264 1250 447557014 447557021
    0x6080f0601090b03041a01030f03121515020c0303070c0f060c02010206070f05070506160210020909040b0613021c0f09030903290114010e09010b03310f030210 70
    0x2240d040e036400102d145400044042900060070881e500e0042a41d65170512074a80c1001d4020b40c041d80050141a0032420050b01420700d0f424203801d00c074144044000c0c1400059038840440752900c02500b03960107410012400c01400c0c402c45503150000058290500030000c03401c1e010303960494154144140e03681c406507403c6078000b02c02400b40c0c021400103400b440c012401c8140b50015070509070b10300416a40d5103810b182d4100c481000a004207414054190750400c0648441c400c441030852620a455001642036180100010a004d26201c00280b0702e40b15800c000b122030304549015501c0382c85103c209040501481e1000a0341c034034141c006000101c41c0d0080c02a0b454040d104e01c40090300b10340301d12603011066142542c048822403140b611107444049000e00030074456902002401d1085c000520810482505e24402c7c090301005100d9801c800c4212604000c0803280300c5041c813400074900003c030746a2a080b112181c0b44a400b801402481c4410741c010920a50039a0341c00c3c3d003629200b4086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447559514 1250 447558264 447558271
    0x10207080d0807050f0c0d0f05070f080a0c0804121a010e0a0e03090a0801020301030c0e0702030412110405040b06040507111f2c01140c030a020a090305070f06080f 72
    0x1d074424400684554050007816812000a1425524014148445081a502ca111951000e40c0110708140d400b951003446800b00baa090f141051502c41240c4803008041d00c13114020f005000000f8040c4071741c6010703200a00c0e50507405500c2035280e5965201820154030f10040036104540c410311003030204c2420303540f00d50507214818442000307030b1118402c0d00002c01604100c42c0c1544001c00540d01254dd81d000307001300506410001682e2581980b07024100004594045002602c03043c0a001c031441d00030055509a84241c840051150f9031403c08a8400242c5d1900740d41043c0360005010900035038051940c4224000e48051000341c075440400c40c1c460303003610702c1d00307145d6000b4401840d201111994600d10343c03041000b0114025104e11102d4006030410303540003584910030b2000b140c1c0d092080c054280c0b0801070b080030807250b180100c6816103a100081042e0049a4002071440700750f8007940b0b82d80b000d5900b190450300b54545808100455031414003903800881e021400191800a40c200250b12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447560764 1250 447559514 447559529
    0x15091b0102190b150a08071a180907050d090c05010219120c060f1a03100b0a0b07140a14070e01030c03020d1502210903180f01051b01050a0b010207 65
    0x44140030341d25044107000c00645848144ca07100b0580307030400c2e600c00f4000303000f03080020040c0c41c03100d190004e84142400700c42e0400e094060240b1100d40001c51a0750701240c0c01106843c080c3d4103540e8030000315110320458070030003c59443c0042003018000c40b480e1031015a1001e03000c4840e0a040f0a408141d82a00d0b2400100040c0c10003940a003140d2203803d00b112864440c40c00031514050b0541c0090079250007031280d440986004030720f42094034041110310700005644030100408107081b404070b9010021400f074001d401070001904420442da81c0b0815500b801150240d541d411894940b100c1b1400e03000c580d241003442140804155070f0b0f04a911107040301d03413110502c3c01845ca95400e01c00c0503401801c1c01d0300d014200c9807102e8800c40c42800200b0f0105145640704c0ca40800c58140d2551803140039100d039003643d206116842c03803815804203910850030111428002c104e00540104c600744034420110300202d400380d091180c500f00540249001e046255000d00c0141e19110049966400511407002c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447562014 1250 447560764 447560803
    0x80f1918030627050c01090501080411010c0201051908060406080309061611150c01050c03060d031116090204050301050a110313030c0f03020607031b05041715091b0102 74
    0x10004030141c1c080704480c45030f4010381d21a411050f041c42e1020b20f24000581d019003042007850910341c1d002580380007601007400c144550b42022b0b110b01e03400000580250781480040780380d41007568000c005403a600400c8401900690b844c4010003815500103490450150b410200d010500c40408010707075400c0f90025152504100c1503030700c08400a09190700959200d0607500c1c3c0701e505a29800e0001000c3c0b02813200c0c26503246441030010342141c2c801000c00c0c20f00c1d0b40602c24040c81c1ea88018a0b42d2050f605890312968081313070074050508264410311201d003a010010b0000640103982d030040d01c100c4500b200200069900d0080302001d403100d02d211000c810030108002207410b10040d06085410f07000e850550502050340d5205012400000310550240c1d104604201e1055454060414519800180c4a00c2081c004034003a11074000c0e070140710380c00c941380a00880c8201e410010490003480080d0021040d0504036007140e2208103440c1c200c1d0032800030008000d015400020b07800c0140c0d00203214203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447563264 1250 447562014 447562019
    0x206060a180504020f0a0b040617011508040c0b030114040605040509120708090607320d050a0e102015221202070f05120607050a0903080f1918 63
    0x34004042c0280100d03884401001d6003503036034490b9000000074008020f0150f50311810010702510581e103188007030151000d95001032000c290040300c039a80341d4201c1c0c20710740020380307440c5840215001190041c00c0b190700084000285400a07400d0981020300a030307030810860f43c0311070a0005550301220000e419900039445441c0c0307684d40b40010f181e02d60166180070705045940000411a030300c00780c4150390300713940c444024601485d00c80740380705520101904610f003210691015600c60a8600c03a4a090000200e903160106014000c03003841500c000b81401144000702e07601420252031018419030960168000e482c000d00e000818081804180b000c1d00900d945d194820100c5020008029030380380c610100d0b140014036900244080301c019500030304141820240e0151400f80c0035401140302e4020b647c2008104c02d804130740c980e0000064134007107036962401d001c00e0f102c5020f90303400180042800070341a0201803829014103603c0c4449541707144a031401760000c07107010300c0002407a000c0c06c0c90341008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447564514 1250 447563264 447563309
    0x1b0b1008150718090608030703030e0102090102060609060301062402060c130504181209082e02030a090b04030302280f03091b03060b1c080307112b0206060a 69
    0x42800c1c0080058141283c5a04c4900360410794542d40e106455652011404804240d0103001d00e20070f642d0990001c40c208400000001d542c0c4002a240c2401601c440020a54645080d004038003c0c00034480050300c412a1100072240c4400c02102d0300e0010300607800401e40d080310762002c5a6800e2041c6004146080c206400c22008091200100c0e9240300c115400c00c00054030761000720f110481f65140d00408a1070001014141410b400784845581000811000b085070903190100d81e6100042005031607503076000081e0010441c00001612411b488001c0104140d4190002d2021150090401080740300c4403840e040341781c1c1090614000f240c510b070703001e0050512a500c803039146400340e07090003002000e01e070415480d050203401c2070700c00b940c41c1c407406030507410100c2039900240705171070326440400710341d07164100e840c00003515240820072003113801c00328a40300308040000c2141c40d115003401032101030341d486010440300c2209400340c050304000400e1442c0c800b554200300c1c1c8071826240c1ea8074404850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447565764 1250 447564514 447564527
    0xf07050c24030c070618030e0102070506040b182d0409150504050c0a18060510200f031206040e210f190503040203070e10151b0b10081507 61
    0x200c1c403030f1030744180043e40119555000e02040c103450310204910780d80c894240280b442e03000a00960556200a20170400ea440e81002c4404a5090401c05034940106421b101c207418040002c95900080480c81d07100b10500328000c000d2042c00071152800e80c818000240070590750720081c05452604241c3c400b06110b0a55040940d000d441a81524110442c5400290300041103420240e2209582c00340059030f0541d0303209844c05003802b140c4541c501d440b4040b000b00040b4601c00760b030075240400b8a0b20001c8030001c1020b0703140240700c807040c2c9854429201192269074811900c15104034100b011111843c3c20204900c681710395103000c443d480d41c21100c139010040c0d011048403020900308001c0c0c0741d29203545819144000c0c240755612660f07400e10340101440c001c0e0320f4002105d440004411f0004040d4401111411a04c52103181140f250b001c0d43c041d51252002030443c5240711400c04014104488000310718899140b1560107104140c607405150750b90804804202940001342d00807655050080c030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447567014 1250 447565764 447565771
    0x2011d01020a060c021f0501080303040f150f0b1005181e030604230d020a020108072604030807020a1509050f120a260a05060f03030f07050c2403 64
    0x40b1042c41e5840c1d40e0702c2c001c07161182d14000050b045016003ca814482030041c0c241170500f00000e1000b941401c040c25268807019000501c034406041d02e40040040720a564010044022410081401010b840b40060b040c00750449109227588400b141a813401882910b1a8000101b0b04200c11224402445021443c0340030b0000d0009000351140d0413664100700c80341c421032103040343e4810782d480051074010440c00b6150101e0182c1200031444009640050b60402140d0240303400800358903900001e81d452000e0a220710b045005000c10314440c690000145030085209070340e03100c029078540c0c60490b110080c5110003004040c8905159500f0845a00501c0c46c1501550035120940d68071183e90b8640507101038000d99515002c078068094a8100c240d58114503620301c1c1d021124014902c4c0c54010010003007440040c507980d030001c06e07050388903a440603031104006000c03655500c00510258006400840b0121198410340d00040c4481c100200c5807280c401c40da4103c2402207100880070a01600010b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447568264 1250 447567014 447567017
    0x1603120c060b1509100305041511090406090b190f0e06060d0504140610030206040e0720010b0f0a0503071205030c1005150904050d0309030c02121e010902011d01 71
    0x1400c00780c126550b00c0c0c242c2e40c100d003c9510000c1c0d40d801d12000303200c0d0070904120300b041410b01d80000c00001c9044110320111811301c00e0300010b4590030004182100b80074002c1c2e4190028503041000c140040d5981c8984080102161301b070061404007500000034500500840001f5030360000c00f0007000107034002950300200010f0019080c400901035510803200f0844041d10b9004003018038040a0000780600b030340220500b260300410b2400d540200340144206e10550141d90346600015120320700c1003442841840941000c44110404008910b02038480c481c1000c1c810226500c60780f07a64905000340f00d0032501d000c0c0103018028501007030310500c5200782d0001e6407107020400898140715828001c0b01c483e207040550002d11400d10a00d4144000094090680220030000520010450005814080c0311813440d011403200100c0c07408a8003030800400084d00010f1000e0344044000d0040389a0b400d1104102900801404d5036814600b620690640640410740354055401d400741024944202050103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447569514 1250 447568264 447568271
    0xe0d020c041d0a0b100f050f01050c0f0628020408071707180c03060b07020a170c03011104060807020a12030207060e1b0306100501020c060306011814031603120c06 72
    0x2000b580ea030501904000880b448041202006040c1111000c180040c02d80c942180c4145814940864082d00c615110607040c41804140c07815204e00822641d1491b8200da400d9640608003a561a2402000919904c6902c85003060b0400c0c200c41610a032403c41c0c00850080c901c8a25066401e030f05464400e01c0d140144c0203032400030031416100d9030400583c0100610001d0840c1242c1c10042c101c2d032954200400c0590100030003405a5100c044200079200809040200510f000300468a4041e05a40d00ca406509013101c2c5140c03680780e40060702c11a0019200c007490769035848401c07a1a0040100005c0c401030455402e102d000780300354058401c0c2c1384202e5002841c0444e221020740303001c10001c05c002400d403400c100ca80685c20184981c5400c408020040900b071810240040d45824a42508a0041300007200188041e80b2500e201108540d01c41140c4400d1034a41e0110340b440104250307000e02a1040c040610f889083d0547c5000c121380d00281e03c540740c401d0401c02104e201441c60401e5034070644 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447570764 1250 447569514 447569561
    0x11d06060d03030b030d05090901090b0d02550602060c0906091804170f040608040515010e0106020f070b0a05090109170307031206032315010b0703030e0d020c04 71
    0x5c00304800001e09815480b40c680b1202410704021101c14140c00c000d42c0c05080002200c56a254072440002c030359412244007400341d0308a0f0b6260300940074018150502d07440038a8000f00f03151580203440105a000c1864002030b41d840c8a5141100e116100307031401a03100c800050007154642e00a00001000240060314001030710740007400c1d00021030032045441c1060000d00003000100740f8094001002200388904101086050208074080c5100c1c00d000c2c414008006000c01c00e0500004466000681d00b913030940d40c581c0740c500c0301c0250074050728015204038225004071410014403501122002c5c600140f41c028151800c4559070401c600c5241030003c980c0380403c41070b81c004586030510702c81c43c000b1900e4003031906000300015000d00c00010728a00d0500c0c184081440d0307829046010744040902220302d100100864a0212006818140d0405e160004100d11250700014417a0038081d50b4180401c1c8a16180319481d5001ea4040701c000d6801294008458182078000c41c402c2c51244109213403614 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447572014 1250 447570764 447570769
    0x1501030f0209040f0c060f02061b04050d0501060909050109052505040b06070203010f1b05090a0b1e0313120216030b0c1309050718060f05070602070204021803011d06060d03030b 78
    0x105d4942046001c1000d020102941c6a410010395901500b5131b11981008194000552007602c00d40c01500d0280026003205014003800750071001c001d00800c10100a60055820024000c200c01c02d0115030b41e00503440003134101040e808480201c0300200880c2a641440c00c000c104c010801c44586a400010074044840036950a1040940701d00c0c3e402c6022407440403402400c40c84507860304222041c04814080c444654458041e0b403020388203048501a40e42500c181c0b1741401d10340e003083d400110f038000000c00100103e401c890b407500038800c0c2e4004840b180100340598a9889141405108000c910010408184000103c0ba0403454541419107000c4900400040704101500b12001c40e40d1100184400303150303c09401400b0f2a0742c48088517045080450081802c1d41080d0320704100840800e540302403000f640e04607998142c0c0284119600d1250319040443d41d82c100340c08503c25480d000c0040280112030700301c0d03c0706604010180840d569544100500141803500580415640f00407048494 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447573264 1250 447572014 447572033
    0x9120c0b1308010612031205091f0905010f021206010c02061b0a0b0612060f10050907030b0405010e090d05030915011205070b040b0d0b1206070509031501030f0209040f 74
    0x2201240c0316503803807600344001c0d9420741e0940d50107512041c50442e001d1001c640c1c4009003881c00d42c106100410561244c216440c41c08001491040e11a46844245010b070300307291b03000c0c1c0d280b207104800074070400410941d80c0c000c80c0a94454070101d032a2040004281e58410540a0002d91000300440d0601c4039076441411500302c5000980d03c0c40d07018120307103404e102c1d07039080856000341c044414a039000300000000f030700ca200c0035280020300d1884902149503881e02c4031314040034100240541075145030024006010301409080b481c0070f00c0c85c010010410a000c2842c1034800da01060042c04102011801141c1540c0004c2002a0301d00486103e59200928500f019000b420b07800c01c0a00006002d050050404260394011050380c081000204445061501655080341200030002801201c210101d407a04104a200300d00302e000d500104008940c000b800303800080025400c44e1745504003103444e03a44000e020b000103843d480c03c01c10000d0042c80c10400396030b0300070703c40c4910081c0d0340d40c00da80d0b001c4c08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447574514 1250 447573264 447573277
    0x3091401060302090a050403020a02010807020304050414073b040e0604050a0317071409130509010509010c0c0809040504080d020c030a0e0409150e07080715031b09120c0b 75
    0x180d9464010070429450140c010360340001c4014810007190405070b902a43c0d0b04c1071424000c1c1880020ba000440040c000c0c01074600a0102030400c0c803030685a100c074855000c00c1142c411003c01c5207100e9803000c0301c164807550248024650350140d204080800060140c5e90fa01d03504646c80381d195141d032100700d10b080c01128010751007000148401c16062030094114480c0c40c0301c0000140d01d500400c1401070340010040c5816040c0c1448559911481010030501c2622400c003200b610300301818011140b0056002910942c801402042a4608030004460000c01d030100a400a03c05020b0280d030342c50706a00080d0004d10a1400078581103d42d1498070581e0414141b007912034101240c00c4851315040320314030400c954202c5007044035448690780c2c582c0d04402000045030341c41d5079410201e5910410000580940034170011903606030798910505850001d001c04030800a800c0101a6450310005400717194100915110901c8040c249000c84907168005202591000900078000035203c90b00c0008181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447575764 1250 447574514 447574553
    0x20a03050f251a090d030504060209092419090518150403030f02030108250f080606120706081f120b060a0506160308100b04060801030c050906010905100309 69
    0x1d02c002428032503c02c0b081440ba031000209041c0070060040e07808200140c6082080c203001810f510b440c20004000d00500d10915000240001400350310441010000d9a148d0650395080d0310403194024410307105000c55001c16055418181404814459040150f1140c01010549079481072010004d2600c50115a142d08040d000000c1c0801d00d1380c14003a191240d03032030150a42c915450f106a0319602c4079512460380010340d00a49016845036200000c0740140408030034038074096228403540f0340b1040240c96442c4503da444807100c20580020848400b00c912684a00360160303114080101022004c1d18901d945034010880456910310785400042c409000b45c5019255182a009020307400c1210307004184665001d104403642034584000d2003c07801d0781031901100b2625181517001c0006815049800c0a00010a0118541e684000183c1c1201d00a0808408070b80d81d4000b071202420f0242c038010f0006a171040288040d0400015285041c1ca60b4500006c0944c1d80383c4a0710030f09852601680c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447577014 1250 447575764 447575827
    0x181e100e010b070b0c070201030b04020d1a030606010903030f09080115051905030c0d020a050607141b0627030609011b171f0b07032c01020a03050f 65
    0x218000c48100c40a0142c0020303400e06151004646801964080c010400e180503100040e00c901164030a400ca401c0d000b01c0600155110100a641d00300a801009400c121011400d08201414500019040d0140c501a11690880c600355102210111101084001448080e2000142c070400074828003c03210340d010b4920041505103002c0003203500961048400b441d41d000c00510041e0780100d22525100d5080b20786503002d084a20204040c0c0e410b030ba000650011006c1000c41c20b0092141715618407928210540f658014250101d00e005004040120780000c018400d0280d51101d003d541c60003a4000407100840200e2040003a10300503048402c0140381e5140d40814102c16038203c2a81e200740031038106802a100400ac1464070401c004140014041101809650505d4400341d900b01502413410f04030b41c0e8541c030382005000840b05100001c2154100c0404811030b42c4121100030036404d05030302607e8074a0b000e4170704440c1900680020040344130100b05c50105425044c40480b080b50500c0d4646 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447578264 1250 447577014 447577019
    0x108060f0609070f0f11060c04090b0a06120b0a030506040c05011404060e0613080d08061f171803070b1009060513110f0412060b010509181e10 63
    0x188035003401805260040515100f03214006030010045060703100c192a2a001c0045040002c80300c00307814030104810750084206001e601c1c400c6000810546100010510000e1185070511200c844c0d540305200004d41403008142c0070401d2a0850103000c84018510394440e0b8a0341c032800e00780308003510304441e06212404104405e51b0001c400041007000d25500504052611801070070100c0d400c03c64520554000601440d980070f5100c8c0f907406403070120100e5003002c3d0800c0000d0700c0032500f9244e00c1d202d031140b55204004c0c2541e564941e03540400c2c07940d88640d00c03819440c40b07a04591000c4c108205116003116150350b400410400303040c42038001d00403c2060700f0814410b60f008001900089611800c01c1030611403503d40c050160540210424006100500b520901e4018055445c0204e4105000500007a20003c05501040c0840c016101003055420b6100156281e200d00211181c0007552900818201d2901c4040c41c1d0f48889121400d44150650030a90284588200c40201d200b07050355506 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447579514 1250 447578264 447578281
    0x604060e0414070c02090405011b0503071b0c060323130308010e15061e0a0908060709030b01121a0403030204080607080103051e031c050601141602060906070b010806 73
    0x404440e01805900c84070b5905040700001e1242c0e90b0450040d00680321100403c042050035800341419030b241d051102000800c0ca0401002544295441e400050b102d903c02d95503000c440a049140c16886954a41858036107901035025090704c8078540f44030380b1723a952601e000d8101105da16110701402c07126082546018900541a0b41c81a04070034502c000702001c001180000c410700d42c00340304084690907218000302c148400820050110742c40e40e464007240360740c3e40c07942108002c0e0a444240e01a981c20380d9a0200841d0941d0381484081c0c00c0c0790148004001e44000a06071181e194028a0481001c070030084403412400b40545045000960002d0100503411051144580100c1c85284c00c005552450f15465610324802d41c540280e00c0c80f00002441d024001c0040b200c4104c03da02255171005070b001c80341c03c010074040303460a01180008241c054200200011590113203068180d0411060303140e024000143c120340c0031903400410410502c000318020112072030003403d030780c401001a40307800b104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447580764 1250 447579514 447579521
    0x60503100b0f09060304080408161a03090703380a0b030f0607080720011a010302091c0204021303050c030706080603060a1a0d05070e09030a02060a0c0c020604060e04 73
    0x450715154090080401400d9003004a40c03444004880c1140c694540d424002118405c6a01c02c80003403080031403000012004408100c222400181006005104103550b011284130032110210300f9000240c0920005003181507601040004410040c3c0c860304150701440b40828034031202001804900400c121450240201c000002050380030701880e60342c500d12955941000741455050002090020b0f005500c0b901d140000a80d00307164074548082c0021409008061260f0b9603242c403003034401206100e5009000701c0d046c01c4000740c0300718010000a0414003803c03484003401c990164003040102091071f59100c03901c016501070005030400715040010180b820036668054414050500d04106140d6404a80164018481d020105c0e000c0855200003588200b000c401552081089010308180000028404180c601000c1c0001d8940ca544070265928002e1a1003800168090b400145404040b42c001c2141c152071390922082640b040d600180342c0c0e030401e800c00c0e000980448a4034103c1d01e081e02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447582014 1250 447580764 447580769
    0x60f060207090c0e03060711120307170f06131d0601080304140405011d04060f11090102010e06090a0312060801110a02061003020a0924030b040510020c060a0e010b090106050310 78
    0x108005071000c4030000c6138646e0703070040c045028803044600310200580140604035400c040100303095520701c0c2002c0c001d0003c1280c8080c1000002014002030251442d50700001e00460005050015a50788015480040d16041101000c451211041c032041c0c5402041031a0103054910301454480e400d1100364807100003004c040e68400e07801c00004008003880060011460403900204112540e21410090042c2c84000b920007815803a1071620341d0b50800550103800b950400340d0003840011f0481301541e540d104c0641d01282e0740d4104190510000c2c0c0918580100c1d80c2003180042500b56580800c076003150031080001c1ca01d00000103030720a00640c144800c030360041082e80748a03555130031600854080c040714000c1031b400c2540c9285002d4103d50600105020303400c0d6203990f0455507203a15040b0a00c041c1507604035018810805844070a41e40c9009403021800c2c2c04005054564a00501e50044d2400c0914070509540e649040b0b4060b0700e4101e0040d0103850036071109035407401c1150400c101450140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447583264 1250 447582014 447582017
    0x1e1201050c0403060207020409050607090503070501080114063001090b011d0f010210180209090d23090301020a110c06070c140612010312020637060f060207090c 71
    0xc04220300c4440c4a420741d002d69400035001600c4210a101041c01800ea8060250080c070401040128a940c001d03160010358a080d01500d00d0203a4510054404042c28001c40003101c40d045050142400c008014000541e44140203c02608114520794020b80c149107050306096050801401002564054400101e03000e1810051031418640710301c00600da0b081b19640324918100c40321866070300c20001c146240000301d6007081a95507141c440c43c2304840b004800c038081c050304400a40100d41c04142d40c42c80c0111511043c02d90305844140784031220f050881104021820b11003615a0b440074406441e007210180c0b684402c0c521690303105490010f0060845200303400c20403800001518107040d0104485c3c4000c80108002d0015001032100d011300c816040848000000002c14844a508010081c141c0d80e021303940c9a03150f01d26642d07400200701b002c1c1000c428015640c5444031203d209103110b8030390b203c540010150703100c020442403889150700410050f4045542400180700c0c5218041502c81c56 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447584514 1250 447583264 447583271
    0x131b0302091303030b06040f030203010605032103060126100e0c0d15090c021b300a0b0a060302090603010e0712080706020729060306010b0f0403021e1201 68
    0x85034001049080000c01c500380b07025000d0300a6040500031380085694540080503152290348034080350f05c1d03e441c0c40c4004da1103503003440000a01d50402003480d4080c46004030500c29640d440c00761307160701580701030009810400a140041002041c600d43c0c428030724a41401c11a46003052502e0b901405100c0e00091500d001d82c030140320b04071500f0303404c540242c0c010301004220b24040c810040702c0b401459000d15059400c0500c0107161542c081542030401c001c0c2c2c401e481c4100400c1080c004242c0310384841c590001525405602103240f2070f501d420008201c0340440b004a030703090b0749010041500703030340b0f040026403108428404c52404001550b40b12a00f600204940031070024203590b5a000c038480c0d00c011041038038a03c000d0050072803ca4907219003000042d03550700f480b840d00140b01c40f11410901e00c0c5002d924407010100c00b0900807c0e0180e6030040c0180740907420508040c06980c8082c000c0c80301101d0400c80040141c0ba5014501c600c100207aa07100c264503040001d004d59076141e030300c0032000c3c0e034503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447585764 1250 447584514 447584519
    0x605060f060a12091a10170c04020913090c08190c060c03170114090105010e10050306060405090a0e060f1003030c03200105091216020621131b 63
    0x80d00c9064404140c02c034640865403a0001803218001c00204502501da03a109206801824010401d018000c07040303440d40b200d005581e040415200d40711060110f0705500001401d02451515801400301140d00829001515146400000841e000900211020001e0348002c0080c1039003400141c2007402c3c80800c00c58912050b80d5403c42c014024000c00c070a002107030001c813003450320450705461107180c444e260b14881d58441100034001803000d007045201d8480c100003c1081d510841d01c9030088500a030140702c0a0352580401d444c00d82000b0129a00801e007888000307034554905540740d02940c8001c100040d134104039894a07040c0341d8000c0035200a42000c1040c001c81c05c0500a00804890301480d0501181c11285011519820f2071200d01540410311080e0130b0a003201980b02e1800b503000d900c11100e181488084091460140b0100d44000039441c50b009009420540000e14000c0d2a1410032260740c241e00d011503100c1d01081c1c44904062284403074030410415191329005103840c1c000d82c034000451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447587014 1250 447585764 447585769
    0xe13140105010e13180813030b010b07080a080601030b060d0509010b01030626010f05073c05030c070606120b010b070804030201050901030e0d21060f1e030b0a090605060f 75
    0x601c2c8048942e5007a549850b100c206895020380300c45c42e281e201380c006507a400c002500e10700d004514082983c00c540784000000f5036442c01c82c202d80751580c0c00140b0b5403c01e40003840c2501d40c180020a02c0f414961900b505800a648620061152403e03403d03001441c0c3c2008810240cc483c0e2140e2598189071501106000b0b0340c402414040c81c071070101204070ba420401440081c007501402000f59612410f140c10300c0702190700408081c2070301c489244410302542c48020110b0b00e17a00202100640d042c800000e44045601c21401903038030401c041c2c2c45c1c5240501c0341c2d8a00c4221081940040710010400c0c00200400603421440341c010001d070244282080d500381c481150380c1c402d500c0028140800020150a00c0e4020340284842004400503654141c409013006000d88800150000d408100803010310031850701445000103650506030380716621810b221503d004c8400c03510b11000c40c3c00d03400400000003510313a08182e114082d20480842c0c85580d62a11000740c1e01e000d4080b0303100310148010320341181c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447588264 1250 447587014 447587029
    0x1b0f0304060203190302160f0614060913030507080c0c090a060617040f0605040809010f05250503120112061406090a0515030307050d08090f03070b070e13140105010e 73
    0x20301e0382c1c0700d26900210a40040d0007d20491090807030b01e441c0481101c0c14441324009a2090781d018240500030b108091405036034000f41214102c3e8071280c000c02040307042c400d0f44c210148951190400900e424900e44404200b0740090b01c4d540c000d54840300150449083c00800c4542182c00c140050110b181071000140020400c64050781403250010001401c0c0300d40c000d05802101d0b00300004200c0742c1820304041c44c080e845800c584d40800c2001d082e02c0780b0144584111041450080040795040e41032603004d101d9803542071400c0c0e45a100130321030750010f05803000c0154000d122050000320340780810301e051410385007400c803440601c21940301000b4154840e900107985c0300d1110f42c1d00203403a81ea2107010403152080308800640510021624a00300580000c141c003c45215846032a07182e566034074002d5917224410400801034109000040004a1282402e600b02269040c8514401c0e503800100c7e03890f408039a0340c400e21540740c155000000b154103200a016020030f08e00304000601e2500480da10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447589514 1250 447588264 447588277
    0x53304050604060b0a030f0302010516050403020f0d08090604090b0f04110d0e030c03070302060f060906030318030c0d030507060f05090712020a0f0609150e011d03121b0f0304060203 80
    0x988a84080f03071580d480300c290348040c0d43d007e2009502c024003814024004c002c1140d00440b00f01c8802862802c403405041641c0c22282e0007400c00c81541c4003c8148110719241140403507100134180310301d98040d0342e010003a001500d90b90383d00107412540782d4104081d020710010b0550040d841c00106030300c0751005c6411100000a030314000b05000c08606030441c554454842015800d00001c20480201a4082082d90203100c41c201c8500c00394543ca4104231a149054683c1c03507055104102290801f410089070b0590000001c1c00ea0311204a020003062080c100b5402c114002280005c05000700900fa205928600301d66503410401807420b01c2001d60303603101c4d60080420030884465900c086503a801841c00c00b4201e9003140d50360302c540c0d031039000e0714440d440c1c01aa94090f500080c00c00b040f42c45000c9071400c8840517590b510041c002030311000b221403c0c80d840700750036004104140500c00500c800801d820310400c00344060741d031481103a09051501c4524580150307001000200401640001035400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447590764 1250 447589514 447589523
    0x50c070b0601120f0f050603010b0102030a080c07050607030f0c0309021c050a0c0e04030906051806030910060b030a0e0601080a0b22030306051c021305070c053304050604 75
    0x58a848401c016038042e2642500c0c4180700f410b161351080c20050a40008244005e980002c0c0a1921007904160a031510791400b540164010700c0506400f034455202d0319044205c6070701c194902844c6860742400d04408813581408251100035074000803000d441110004109841d0030030041101e0350010382c0252508080c2c080141d4800a4682800000c0c81240310b1190310a84c8007000742c0d0396900711020910f08a40990200b40301c1c2400051803409441140c0b82d0100c181021884440ca42e02000125080a862183d40e4411043d040440024030310616024083c0d420303504d82c41c1d1400740301c4103080c0e90994403999095006040100080d41e0005121581c080d80202008030301d6440040d40c4109000c00b0594a6004c4042003450041c141c26a101a003500c0051310f020540c442d000f90a4445030100500007900201249048210108603500940c1c01c01d2803464001d01c00d22203a203405242500e001c050071005620b0f1980c00311160040e00308921030710580c0394100326a14064840c82d03110300c0c00610280 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447592014 1250 447590764 447590783
    0x1061707050901140d050702070509010b0d050408040e040c21020f040f02090904080403031d030309010f0306050607061d0a05030a11070506030a14060102060c1e120f040b01050103050c07 82
    0x2100b5a000380038140940309035244064981c02401e200c0805443d00b070743ea00d405400b84040c08603a6040c4000114180e400e55902103150038052070710100209401042503a19040501020815042140009000f10300812001c1c072898108201481400040287d0750354018681c410f6500689484444a1048600701d40005240010742500c0010b841143c640700c3d0b109422004020030002030901604c02e81e4000c0e0745201c3c40200d0781c030b0848520040600c0343e96244c0e00c207000c8c000e4690300c00c45070002d8408552030041032590b035800104505800c031002c04c6580e81c2d210900741800c040d52503002410001d0500080c4000c00141d121a07440e031040c1c02c0081c080107102107054214030300401c501c00c010140605541d03a41e28200c0d0300b103401021100d401103400075580010910ba03610008116002e10340c0001c840e464101c0c1034074800c1b138080b41c02c1582040150240070748401c2c80d0303140d21594840c0110045416052400307142c51841d10005030051814989040c0c00c0c413800a044606a07084140e0002c0e010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447593264 1250 447592014 447592027
    0x1c0c0602030c070206070309030b0a02070f08090316060e12071406070c12060b03010f140106050d060810060302131802040c02030c010504141228092c0106170705 71
    0x1a0403880f410f000a5005000000c03810105513000d4981001c80e80103500e80200713510740d02044c5060b4071441c003010701300b41d101c0024000031035440360080c0380e0404014101c501a0a94150003100c8901c04d41c0428007240003042ea001c0d103402d021507a00640f4404001030003815007001c03281e6034241e0300c002c4454020030700411103c04100e40302e803069000d0502500312411840301c0d864950301900d03158075003d0095013840b550b030504062034094810403a0040c641850940e08041040702c482d008221910000c5031100d0000030014000c4c400b810358a544160049201400d600501240c0f800c0860228680c6181005081c8800404000442e90130390441d400f180500241d80b00700c0c65400f94042c1034505503c0d00007407008100941c400790310084081e006455800c103151a0103225406100342c0952040c19a000c60603031410700d510041c0440400d070514010698a0f442d800050504240c0310140382508051451800810288101d00400d403500d025555115060728100c0c1041000c0e003520107112000c0740c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447594514 1250 447593264 447593281
    0x50a0c510c12140415020309070603150906030c15020708100b060906121803180907020109051501060210060311040902010302041d0a05090a03200c06040311031c0c060203 75
    0x402c0e0404120110a0010210703528141d501d4803400d0b07408036051501d240c4503a02c50601402501c0c810080d0074050600245444400d42c00f4140d045412500c030310590b4004074041040e4032030103000d50301a810094000b410300101c0c1c0100050302c071016017554003201f02042aa0300000d0103200114101c903011030170307800541c003242040c02082e02c0b80e81e0003400442c65800107843c101806201c0c450110203d015002206c000584a1113a101420001903091401c00020308225020a801c450144000111190715032105810081d166012041341d5820b20010004130390b040120f1013055000500400070a8030710f9850721001c0c1245e900c524001c6032030303644140c156802941943d0003405e0784841c2200b642075801045031449012103071041610728001c00f04d07a00c00000503008081503803503254481c80390700704d1545220503808008404424030501a40c2041d0741c440202900042d44911203c00d401b0092208042c14100700350100d400e0941d400c2102420a584545c690280d0b40d0042c80040c4d0304e44411a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447595764 1250 447594514 447594527
    0xa03030c05011d16090c09060804170a020607090f0e0105210d0309050106120206030105120705220c0206070f030209010302070c031208010e1006050a0c510c 69
    0x40b260300e680000365054500500494039044c40500282c01032261525240b0b58012594144110400201d0500701400094011824160014061320b6441d41e0581200036181c0386074001020320340144c20500034032070341541210100024048038001d00380000d0a00e40d41c40b4488805203c0c552095180f040e5140081009451090800c003502c0140c8a540745c2e50b00000d0090030624804407510b42c6060300014203010b01517508020150f00500352442e42e4600000c01c4000c140030b1401a4240c0294017001076142d9607100306208503010400c4d0503190f40b011002d1601140d050208040a540111040080f00c960280302030440044a05006854002c0100102c1c000c0c022040018104207401d003001c4180000301c2e071603c03060b000a075501d4200e6030301c8207840b4061600c113644604030b0484032a020f1022034015009001d020503d881c0223081c100090b00c40000d00081c1010502139051100760740303030f24411400100c032010014080400c41081c0c11418004000c01840003010006030740364a24400c0b948a0302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447597014 1250 447595764 447595781
    0x1218120605180d020303180601120204200406030b040506010f02060c160203060906040b10080c04050c070b0a09020a050301020702211c05090f041b0309060b03010c0215070504050a03030c0501 84
    0x3c0f10030540f01c1480281d5690f000382c80000c107115032000302c80036807a00041c0c9141070321429090300028003480e909200c05000d111080750980e05680c00517500c011401d0003e030008180c0d540d00400e6080f05001880300b2510080c0c2a00c0c10850b40c0212580c0c0180c0020305c060308a03040400c0142d990410641156a00c1c10040000354140030f007205014515000003040c0d80070791f0050b0b001e4101ca4807201c60070710041d6075a224001c0c15070001441744205203040c7e03000e41d612030b900d00780c841d00c0c0004681c0c1d802c0c50079808440d83c0c03a241b036030f0307200c4402503060080c2d00c10003800080e0003c61030310301550005142c0d0101c50544040c84101603800d890164018800c0413001d81c501803013811641440b45020b4400c1c0c010400d8680940c0303e6010303101542c6018010040c0e400508102014110420300f070880143c0507501041c1c4a503603d03201256015102489103000c002026409814040341081070010700e01c001030403c00c10404144014003159503032200039002c596260520040070903603031921901408160 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447598264 1250 447597014 447597061
    0x140a18080d0818060105010206070f091a18091b03060a080102070302030d050705040f03060b01140a0905030717070b0a020f100507020610140f06090d1218120605 71
    0x200071941880c0d001a041da015054002d4040741520740c80c402e640d5107a1003481890700590088001c01d103018000d80c41d482d01c0806900d0110071060303c4140380d0401e141000a201411100003c0e0512401460b80c1045800c400c110340c00c122908042040d001205140070102d01210781c000042455a60381c4001c40000300b004400a6446803c2405e0184d1a074008004403440300d8203001c00038162a2290040f00e05030f907591810441d0150450300c1703400003040340c491150b040c000f031000410801c1e0140009003181c501c6903940d6050b00d41c102428582000107581c0410503a01410a10398910311012503142c080c0e1b103000c455a40c8030780301000d04a2420304024800305090055076406c00191245421162288a503902150700640ba4198030003d5084540f04d88807038840d0710441c4880d180381281c00c1c02d0605800038030007414071100c80300003410120004402c9a60494040185013681d4000c60342582804400000c03040c20b910300104420309204051004140660f6071002818260741002d00302c0500101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447599514 1250 447598264 447598273
    0x1f05090301050c03060a0e070f1101091704150206090c0108060114040905060103140411091005040509010b100f0504271406040b0604140f0303070803091b01140a1808 73
    0xc3e844041441e802503905a014040c5c00d10081060051181814012000765503403868003401038004036140500500c28900c25521045241c0108001140c0c0d0005000075118030760780d682c600b002d001030f000d0003902a001550065003c1042d88400426114100f820a00b0003401e00d0383d621004844110f510442082100c40114020404c40c0f81c0fa030180b482000f003a00d0400003510444024072081a003246c00501346c1c0b1003036003860001c1c00c0c1068041d0700224903529004401ea180d000140c00e841f004c4a01d008640e5441e104500d8900d8140e0112001140341d041c141c00c0f0038004103000300705100d107028804e0908140800d8034404035505401c00788290803200104805001c070800c140100100b41c032000e10540c00c0040c00c00e090714001e0200c1c2c0032200700c10b290112040310501800407510b00d81105c113606000521204012805030b40c0210f00c1031b5060f0b0050f00e0b100d403240b41007940000081a86a041004120340c140600d1102000c4450142c4641130020104042e08601640c40b10f0b5a00104510301a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447600764 1250 447599514 447599521
    0x140a050a05060c0304020d0f08190203031b0910030506060912010209090a06080c27041a0703020406050319060b0a020a0201080a09171c090c1805061f0509030105 71
    0x1010880c01050380c410400c1d10550b40301c000c1c0420060006890181d071004c03010441e00c000428681902d401c0c1c910900345c4ca81000201441c800311002070482c4040944c00000c200000c012a0b1205c01d00128a0300141c9402c00c80c204010a8415180c50841c1003810b17501c4d000300b840c581c1c1c0c40c000c1d80d094400c000c05000c25160b00d030400b207000c1d4008101d0280070303182607004524420020b004910940d9104402083d508486904000e0402d41d900040750303c0c0642c0000e200b0000030021001031081d400f410100b440c0114003484243c020200030041070805105000a0004642c0035040725004451a048240061b11420303402d80144441d6105805032180010b03030411482e004102101e840d4000d0700c0728030080d51188514015580000b00050040d600310030400300c0e03170310481c0c06041c0d03201c107840b0540041510100d4000444a240c00296406c120030030042200a40214104880c11071912050003a0f04001d070104141d00c0d000c0b00b030305003802446221000e0301c91040003969800d20b00107000780541d05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447602014 1250 447600764 447600773
    0x80403110a080d0f0b09010501140a03060b031003030206011202030604020108070516050c040b1801290c01060510020c012001110d0506040b011404031704030f0b090106050d0c0909140a 81
    0x4030340c54582c0c4d100c40c204400d0003001c5ca042050b890490354181c50382c00400203e501070315045c0d40300942d4902070542e640000715500c423400c4082c510032818600228515819810060724002c2e0503809243c3d44a80b452603200141c4022620640065080c00c0c609160b40390340006480c207011701c000ca294003240c0808140213101c1c00040781c007145501940c00f0840c0384143c0090201f001000b12801c000d102e41080104103040c4c01441480c1c032450402807900b00c0d19920804422158490907949259a45804045c03041f0b2405010b042182d0b441760009100040c003c000192541d0307480040322425038030b061003081960b075084d042500c0c100040b000c0175589002103105000180802c1d541a40281d242104120283d40110794103510080d2404070315040615551725000004000382c600065001c0c24000040050260411106107510034040840c503440e0807510b180c21a1b0040d0b00661042c920180d8007000700d0b007101e0380c1d00c06503a541ca8000c20002050b0421240340c216081030880e42d880348440400510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447603264 1250 447602014 447602021
    0x11070309050f0a0b0304080c01021c0203011d040f020f01050d2c03040308181912020f0415050f0a08160317090901120c0b040f030b01080706080403110a080d 69
    0x6480868500c2d111055003014008400304500607140c070b90700200f000c03c0c01705d0103039009070058a8020001602c0c02c04000041e140384044c003a0310360002038010005111181d00490103000400050f442c41f00341e460b0585510800f010b03149400b81c01814a0803122146e039104104460034078180c910140004100e1400b868003039000d85481c40302c1034580c28007041403580b01008590450f60403400307a40c101010201ca6400c4500b8100f1426400781d04190f071240401500884007000784691012004030090f1030060001c2101d81881c8684181e103858a17884400069a0054054030230590300312480d00c1105010841c071101a404c500e00740d110755001c0282e050315070010002a00d00c204000d148240013001e50b49518050145800c0d4000d1181005211407445c401c0b00380e40c00c038000c124540c40745a8541101d001540260001211034600190600505c000003200c90b00500b100c400807c913291600314002c04c40034018000030304201c15264200c00d600020407003652800d411001042d03441e0711088625005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447604514 1250 447603264 447603269
    0x4090c17010e030f1e04120b09010b10081504020702040501090c120603030804080c010f0c0f0f0801030807020913050d0e040b0915040e1018060605060f1c11070309 72
    0xd560900c00b040030700c0c650100a8500c185061504c550400200e0030010f140c1191100202c1a454800c0c0000940b985288204000090180400300702034100560481d01b0746404912441c061422001040c84d1b41d90300c240349550005015000a80175041e520005001c4c2c03080c00700181d4010704000010460141692020280180a454841556138502403140a8890324400500800c040e10005070119200400401c1034806410000074990600d90241040703c4000701540c0001d500340c1d204605a540204001441c1d03110780c00c00d820603600d140d039550314034410324800074019807219011800d140d41d100c481e0b221040e80070781568550b11580b0b0f001840c60040c0310f0458408c0e402d061161301d4508100b01c4490180005d080313420500e511250501001d00a41c56800340944110a600ca00060781ca00c82c00441d101135180802d01c450f81c2d800d104042e203109401c00ca220f031070200501c1c145a5a0b1504443e000d10001c000b5030343c80300c9100100c40092039412007460a10100185030410554032105400c10b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447605764 1250 447604514 447604559
    0xb0f1527132103150b030604020306120604050d0f090f0506090f0a090f05100e06100207092a05040807230406090e1005010b0706020c0c181005091006050904090c 71
    0x101200700a0b01036400174400c505109100304003248807801d140d0019580100090076000d40b141342420200e103001c004842c29502600140d020900c1d42d54440c3c01110114900c0c540408000d0410b09030f02c0c2e54400c40e10859118080000751036a1a0b2584078203151080300c018140c02c40710b0368880034800a0100064651070322480c100c002011510f9001c108810345140d85564031540c1c0d12141480204400c016982d415442a40350006045a00d170240c540ba5126101c0000c0c2d900404d840d107201a50b10014002c014044240401d015103400003400208460f41e1408034a8103034001a41111840040415503030080d042000c04510031032190000c04200e1910300c00c4940502e42a103100080b02e9003030040c0340000d501040031201041d99500506200107201d030542d14909040000074903980e4690b8029200d41c90072004000a81003d2000440200700c2515804054030f072403000f01642100a010b148184180800e9000b01610340742c4c0b000141d15440740b031808002d0b40750902988071841e00c0c1d41219 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447607014 1250 447605764 447605771
    0x8060a050702070e0406020a230405210c0d0c09050f041e02100e040b040204060806011205091c022d12040b03150105070b0f1527132103 60
    0x140071030710010719101107400002800c80d050305c45607a02030180d8800c5a0a4042006684e004041140c141448450100300c07030a415a682d440e000901201c0300704142c40c4c011020103c03298010550010901c0c012031142240c84180f420795901d0182003550fa26000034405901d084104808440840c40d09030185028410600100c2c190500307440310032000da00f0094124a1a460102415005606408140c0130050001c83c1440026011400300d030855440100010f1b0703210107003d65035170032518040803961b20b80d01c00d010b64900154440d83d07030728418040c810000c07075803018800e605109015140d000c100f03038100310741c034460a200320b01d0308a400c031b21081e0414000c00c010242e0359003012049070203c4141c1031440d0f0559541401c11001590400c44182c10310001304100d000081c4644451441a440a00080050b04000d511001c6650001100c940148102040700d003070100c0030020300d400710b84840c15100d010754401082d41c980741c1140d040148456080d031030910b006807449101c51030101442c0d4081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447608264 1250 447607014 447607021
    0x1a0402011e090603050a06081906110f04050105071a0f0610171308071e17090d0b06041503050304090e06040c090905070f090b0102060a05060a050d150608060a05 71
    0x914903000c0c1c600c221012942071503007002860b00030340125920013021075000031429501d400142c00c02ca40040c40182d03000307a00314498108100e500c10341103403030b4840c501c0760300304004280c20300d005202d50702415061290100da4201040a8150300c6010013031150307005881420040c03003180880c1c00959001d032064020b01c50350f0801f1440b4013800e403031610000e40a407900784c0380d202d108a0034840004080e550048100f02d403502040640060010301d05442c403a28011850f81e040c2030202035019801701101c07000401c0754801c01e40c0d460085d0030742d454200317030b60302210388825000400a000c0031015010103c000000002800130102c040c00c00c41e000c048d400c1c090780c3c8030140038a4550704205c0f4000c004024814050100322802c0c0c0c1311403585445802100c1c60b0549845a54000ea152541300c0141c0503107030180d4000950307042c016680c000c50111410700440c00c5c0500003a074810706a00542c1c0c0102c10410280042c0309014022020f0404503010801409849a2140e505d0b030b0021144088281d0418012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447609514 1250 447608264 447608297
    0x20f160b072019080d020c0f16030b071b050709020702040b0406030206030c0f09151c06140d0201170403020d0f08040b07030209060c0111040617060306011202010c1a040201 76
    0x1000301c50a200b001c0e2509000d006034900140d2141001614441018020b0740707416000d501c0108188800140246044032004050388d1420550031500c3c15040546181000081c041c5560160001058101380600c0a00c0d1408a05032110a6901070058403440b01d0001e04240258002c0039214001c0e101840401030304401c0c00700707071002840300039000202040020000c0400ca8040c0054028503407a05140ca910700b400103042c80211141c424660b0300000301e14203104c0d01d90303804050a51755040140705803843e204204140c00780c40c40300c6a00950802998000310380c031510a1f06c41c041c04000c080c001504090030003d640e45844418200411000804070100038040e07002c0502c600c0d4059502d0026503605101203019400883c61590051014021412210780a000d01082d20602d40c1c4001c1c0c03260725082000340075030004c1d55070758100d840398005e002a5450200d2140d05607581408981c00c0d503e070520048500c02c0800300003801d51800c85007460f51850080461034002e80c000d83c1c2d00d62550381c11900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447610764 1250 447609514 447609557
    0x50615040305030a05030c1b1e0f0d0302220e01290712090b0715060f031a1b0c07060207090e060402090612030a0e0a060e01050409020f160b07 63
    0x20182c003d5209010000710188110010740e405070107a1b003c0c505144039101420360306150906003440640000300300b000c88a0820080801d4603081c04000d103a0040200b40c0e40340c8681d041000c00c003c0540000e0300784090210f0354000e450358484468042c08240e50b0f18580602c1c450280a09000040307039940880c0c20803540784007400e0045800148900d404125640e1141130b2001c0341da03170824008462030002d0f40e82c0000002c0c0800d28001c034100032030f45012611040c119a203c0d000900c0525010301e05101243c40d550000c2e500103d100c5403401591079070403016400c021400410b03424030900084003100142c0110703407103007200d003140c00b110b09484d2102c20394000d85070001d038146850350061000402601c1c1414445401160107024031142e084440c5000c1d00b198000b590304004544a56000c004030305007200c00344020301c07051074003410010301c05e80002c0030380c0300b50300c2200c8a25401203082505030005404840300c410740c5450a8213002c0fa00e1130000e40300c00003101d201c00072a0000700c000c80010704829 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447612014 1250 447610764 447610769
    0x2091f02031c0b1e13050402030703020a142b170f07030504080f030f090d060f0f14251d0607030801081501050907210606080105130603150207030c02040501060305061504 75
    0x3c2444050040f0301c17050a008000040003640d051140100000158407041d0346031010300324081c6002c07480450b05041c44078145010310300803400140c019100003c0c1c010300c0060320090b90312401c203002444440600c0c14950003042c02005004000007101401c0603001002003044031a01826103504e038681d501201d449004890500d981400208908406807800a861554542c440c46c00050300032580000d05040396121090364080695500441040009030040103502c4110000c11000c2441419400140c10201e8100d40050008103032080010b40c00403980794998500180240c1c8c0c48100c0d03814000c00b030030028807504213103010701c00305024810800e04400c0e0584038050481750660300c0d00342c4229584442074125801d2450700303c003014188070302405980020101680c0d988480d50404c0308111408500c000001605490700004000245c40d03412006e20740c04200b0001a121000c604081d9115690a45e00030f60243c5400004a681c2d030309035001d40e0081506403440c12150103d0303201d604441c07003a030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447613264 1250 447612014 447612019
    0x1090e060d0602070201170403081005030609121324090e07020c01111905031206010503071d060c030309010c09060e1f050f0d020a030c0302091f02031c0b1e 69
    0x1140501c0400c1c55a001040d0152043c5008041a80300162441c50000d040d0340450015051109000c190300148061002600007140500744500780000300d603650380443c0a1080c6d0100380403548295070317504840150020096620108204c00d02021504000040864141c000c01c80211000c200c40c4800e0452520804180c0c004084005c650001954003026200e02031155104404006001108010040141038880c000071511140034006090355108000c0c10141003050a0040003030540d40510519aa4184040c105640035048030114100c0c1c428030124694600c0000b085c42010f50b415400041e003036405075580b516443d1901400c507260b81c07003091020b900013008800075a9602c81d0740c2f08086003002d24141540780480d80c0e50b440341c00380c002c49036103109240d011511010080e018002d44940310300c246000c628000c2810009241d0038120300701c00311984911078040003128000c200b12808025130912410b05401c1803080710014041e03c04400d0301072210110042d4880c080310352801e038107030b800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447614514 1250 447613264 447613279
    0x7150c0e040e0f070f08060606030f0a0203190203040b0a050709080d0819090804030312060b0d0e12220902030702150915040b061f020715020703060606050901090e06 73
    0xd600401016246602c8000741c01c1c050081041d24020041008000510f07028030a2031420f4176203500207040ca0b400504843c00744000f00100442449109242c5512610403c001601ea131070f171410660600084940850400f8030000c203210610042003075003407148000303580501182da03c480b4200d921220038801e111155205682d0b0b4a00940500240303030384281c00a101d403002010b003082c0201500d0490314141c44071180000d00340145070f4405040d0001e10360742e00060068a160016a28640c8101308070004003541c0d0b45c00103011614103001521020060010b01034442c00e0342070700c40240040c4c10f00d210f120703207034540c0f0001000009030007664400c807865005014901d0b560300130350302d25400060030f0200034002c01250941500000c464240500d0098580e0308146c60310700f06001c058005c10707103191b072401626200d182400d07500081840c241c801c41c0400103102203036440141e01d001c00310b0b0402032260b0b084c8680801d003194002d0190404100c2603075002c03400fa5847e048034101c202d040c5c0b0240c1c2c02260 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447615764 1250 447614514 447614537
    0x60c0302220e0c1b03071208010f080703030c030c1b0f0603090209060918070f0509010902160821090102090102160303020d08071205090d030b0301060b070215070507030807150c 78
    0x203c04003800000c035030002414011100c012040e815640688821110b840341d200c001d5000a1707120750041d01400302003418a802c18140010241c0d1005203100c0242080480203002d400c2501c2032000b20002540070f103059220740a00c200380042402c06014001c114000340742c000810a1007802900702c01c5801410644281e16007800384061481d008120005107000304100e0790380d250b81001048001c00c9412405140302d42050300b0000c0c06401a440004100d0060280401029a02c0b4210404640c00031500c0ea44500346049540390400d01080d601f0f14101d80410001282419002018200000d03826203054000750054400082d045000c060b0040c0c0c042c0c040f0750003081c00b8032034584e0030040c2d50401c4894800145101c506441040383c1a01983e0004101c100d1000d03014002d400d84540704800922015080151190300c5018a0001070721880c0701c1da80310701c200605541256501500401030312209903e071f040411322a80001d60441d40b0003001080840d006800c0c0c45040340d2003005550f0001e00c6c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447617014 1250 447615764 447615781
    0x70b01030f050c061804150506031512010903020f010b040e070e15100c020112051b030406020f0426010b0907030209120d180b0405010516050a060c0302220e 69
    0xc00d00007118a80300e12108142d066540c08090480002c0800752005c07168852810700c010b89007244030b40f11000130014000d115503a204016642c0c800701c0f1860184000300e8a0000646110301c42840403119441c1c41000028944c0c003182e0f2140d5480d280c40240f081e2004001440103c5001044114150b0030440b400d000c40d43c120030005821400445120590f00c2d4114002802055104030007004203522505000031540c0015410f001d24507111801c0090b45000c402c2464910300d402c4807101300b0100040000c00f0400c0310743c11703201e624815608031b540f9980c1b0341c1182c565000c00714110300e82030304010300b1420601405001d40045180068243c460588903044154040d401c45100346500c051440c0200c411201c080142d900d17841d500d42c0d10280804c136000140120a01a07400190f80b403401040309005a9801c6800c4451400b00741d17410700c001030840d09215080c402c4500c030040146060403040c104950385600500351482c80c500f0950019004804900e0703480300e1503c24041441e01c6c0780000b400c3c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447618264 1250 447617014 447617033
    0x618030e19030618120212030a11070c03060c110f191a0f2403150601050408010c020601060e040b2101090f0b101d0c030a020408030a170705070b0103 66
    0x20074503698104000ca403681ea0f420207680c2c0303061407091000c0082180c2c8040c032004580281d40120580044c0c001104030302d580310100d1000031300c00801151685000c01c4006176a90032180e0843d04400600c603555242d142c204094035a003003c0f617001546088401d09401d401041800201034001c00a040040c100e10341d42e0301d5404054415100050007000382c3c0034000c2042030152055616040074429890070100c89044c00c5000d555a4901c20faa884180c0c4054400013000e09114502c10303611402a5a003000403141c911031900002629420440703642821500007902c6030580e00b00703460f268402d0b414803080c4030407100c00b404e81d15404411500d90280c0c000e00c00d005003001902800c00820200c08a48510909a0740c07107108450b0314030310201b00708002280304154405000034082d2200078440b40c0d11584443c81002c4c02c210450000007000c00c02c03050959040307030010f1440d88240c03902e4046c00c860240403001c0d000c070b1030a41320154100140341144990102c0341050781c41960903501d039080d600c1c3c69002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447619514 1250 447618264 447618289
    0x7030b01050c01020c0604061a0307050409060b130b0f09090d0f030b03070e011d040503030c0c011404080327031806040e0117011425021f06030618030e 67
    0x500400b080b10401c002028001400c1081c4004020703e00c901302031900e0341c00c4a0400c3c6502103221280c0c0e10100f520b903404125039046500480b0049040801c40c208400100030301d0070491b520006400d0340c000040d4a5810a8440c900c04a400e01100c0f40880c041c00a200b40894081540d03410046041d41740c00c0c0144400700b2190003910740041d0b510941760102c0c1c07914059401c44074820484100420610140c1000c410490302079119a800d40d0070550344e41a5203000140102c00d1b00d140104400c16000025030000c03414150322003207454a4102070401d1102039001369000c0a04040f0100b503d448503500c1e1400c840d00ca60300000851a00c50074030302085110a03e12221940030f0010000084c81440d5144058043c200749444d80710f280301c04840031401c6502c14801c0d021806408420400682c01c4a0700201c41d100380c0054030070561070b0041049040101e4241c51042416428a800e0401c001581c44001940e104810810000407042c81072208040c08590040024144030300e04907550511200e030020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447620764 1250 447619514 447619517
    0x50705042702031009051509011518030b06031c1b0206070c08010c18030201090513020d09081b0a171e070f0c0603020a2708030d140c0f0307030b01 65
    0x10711a08a0251000741d91007130f140e1a49104e00d08030705000310b8582e4420b09400031652500c18841400d814040750003c2030503c03c4030a4003007003604800d00d0728081c3e40607802c1f0100448400c41c0f200c2e20f030320b00780c030700820240c2d0326900901c601d04d4001078044800101858031540368480f440700381d44120701c074084165100f00813604030320b080c022a0b0000b42905070200140843ca0004125401c500100400005841348202e001d180104010009030b41c000e00e500003610029541c10324241c0c0d03040c00395400391045e1100346524910740303518003061058002c09002c08043d442c51016810200140e100c1e0b40340d00950018040c2c10401209074400100d10300202000740d05074039850000c6140703510310380480e08042d9040c0c2c2d444400c0c00e8160200105414005d0240c841400d04505088000d00000c1c801c00207210b101c19078030b0084816004414164400b58005d00001c0101c82c0e44030402040f00e0045c001c40d41c1024071490b500e1020a0034039100d60103550810444540aa0850340c4240703084000d4071804d0004d50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447622014 1250 447620764 447620819
    0x1020307020d050109030e031222080a05010c0e0d2d0b010303090e0705030f13080904110d0609020703122003040609050d030c090e190204081f05070504 67
    0xd0068550300c200d148290b014600000d9174100f1401e0252803d0004248180700388c000300c40b61000543c00754161000c080ca0454003502c0e034040c0c10140340358100203412942c01c0744100d035110700c108036054002d10740039040f07591224032240512040c40026614443e0060034040c0c0351004480d01003214000c0f0045000811950a192041d91100307000b1080a0f042500050382c4108140103c040080c1c041c0c0c0c10800c1854501d1a6113429030700d045124001034844141c611994040e40c0c01e00000c20140e928900b002001000a01f4a82c1c0e036000059010017544aa55818280000b4030082c440c400d4505158040e201c140038800d80d043c0c014000d0010004050345200603231000400326065401440c8583e2081e54002642d45250030150701d01580030244038201420300c4501c091040d40101304900f140c0044030a480d003525061040c0381d01e4940706000c40c5069201050010715424000303209503021140000c3c8801d40c04030f06071001c0503180300300c0701d44001c03078000c100c02c111900f02004100c21550f40c054440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447623264 1250 447622014 447622027
    0xa061a010f0e0112180227130b01030b04020307080d020f0f150601080408070b0103240c021e03090910180207080f090409120f0e0303040f03030e130e0102270a14010203 74
    0x18031751070f50300f020319402c030305058200d000c00b81a94803015801c048c039261404050045a668660041d0050200a003200c0b4040c0104085440401420024004820640702c8151642900035a65040103107100003620620680c0f121808002c0b4040028203a400761042c10b60b9035440041d1503040003c0d01c100c880440c1041801c2c0401c0401e440c0c1030281d4846c600b0448120000300000c101c1d41540c5101c030100c0d524151184c00896000180c1d551809848120003003100814101c0c0c506602490006a4005d1580c0c0204034880c03411800c500141c9a002c0c0d186044099400010070490181c81001043c0890070000d180d050103c20015103054000244042841d034103503590348a01c3d8010801c00340c080f03085103010255503608101440c03016141500107505181c5005241e81a10781c1d41d101c00307001d101c60030020321a140c4542405082d0540700036000e110f441c401c1c88001d4000e500c000e0850002c58105540d0250304004421030794001a80200194403e50810b0001000c1c0505034a07024103502c07081191 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447624514 1250 447623264 447623269
    0x51506060f0703090e010e0f04030305100306060b120c12060607140a060b090106020307080702100306080304151701050609120322091a010203070f050a061a010f0e01121802 76
    0x42c08454403c1d690f040c0350350314000340845260b40c10381001281400f40c40400c43d502840d412100d0307000e44c16250118203a19501d00040d03d01200d6000508600d090800204504025400130903425102c1e02400407aa640e44a051601d40a02c500c940c00b8018180042901e501d41038002e4598140030320340358603c00910404d41450b01001410070ad44440e203c050310032803450403410302401010b071342c005545440742c40d60750b808980c4204107000707100b942c0c915a5100f000d84a0b070300c0391014100c0d5400b100da0311a2100040c0c1010f960601641c80002d00309809648281d0317207802d00794101da0024200764208011042000046e28284c9142d5949101c284016900c60780d0712841d5a10380c0200307642078141141440400f0090760740000b5490a4080340e54007402560744d000003140d011a410a1183c41c0302440703882e00f03e08000465101a041d00e00b414481001040310030240180e084098840b551200081101a690241d861a01501007004d0301c00342cac12100b8840d000340b55601c02c0c00441c0b000340d0b15150b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447625764 1250 447624514 447624517
    0x9010f1101271a010807050603180f060f091f0c2705010e09070e0603070c1a0f063c0a0b030723030c09010315090507021009051506060f 60
    0x403603928154810b18544140202c01e1001d01c84114481404140e540c1007101c40303a40c83c80f491040e0f900a550001c00100c121443ca030454121162100036036185048a01045d0b68441c8103413000e034000000c403002700d0b070340e2440040e14800e030101500c4810040c514903115400109400540c0c4400c0c010a109655801d81a100302d0032000079001c20031201440c1843c00040102e80c1e40e400107030003041084140140317150810b09a0395000811912555699203c100c00c0705d0701c0e88030800040c100c400102030001c03c04028000c06103d851410440122580c8000070049110031650300c0b0070403a00e1401c1c030070b0582e01041c1f080290400c010000410502c540340301041002480e03502009200501105216115912042401d21901c038402c0482d580d2014140580303003848050103100c92490002807200490740240c102e070507a215902c814401050782c458140010300400c588140c0180076001035002d40305440d110302e08800f0b800900401c0401035074080c203001c0510180129602000074408698020043c90 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447627014 1250 447625764 447625811
    0xe1518040b04140c03181209040905100203130b07031811041409010203090610081005070c0212011b020d021c0e060d0f0513020d030c02060c1b120309010f1101 70
    0x12005e13501d00c1d00201080428250214114141e000401d441100c3d03c840070540702c8a08080300d00049030011403800c60324200300030324403a1115002204000c2c17100c401480c2445498094082155181d4559800720100c0301c01c640e40744075014180f50030304046403940d2044c0800110150000840061120302d4582a01e800c84d03e00700d82e80e40001c1044603010041c009290801c0842582949007810301521680740c0d1070440c14079200301d0f540c0740003d4401d0710400e540c00c455500074010103405410385010901034100941c610240182042085d80e1507480082c0703a07002e500340c65003d01710840c0707540d0341070082c1404000008204009941d80544e00e80c0ca41c0c0091400080e07038480001d1240400b50120141d8000a1901c01003003541c075840405610303510b40c40426039600d0f2030889105e1549d031000458071701070042411160720403121072002c10001d48074080070b02441192000c0c2d0808042d40c40341da8910561004900140ca4880c030541040c0c042c041c5242042c001030004942c5c0703503044040c1220400f41c40c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447628264 1250 447627014 447627031
    0x5031b0f0f030610031506050f16080c120406091403010204051906021506061c0603170703020106120507030210030207060f05010314010608070501050a020118030e1518040b0414 78
    0x1050003e41c0c0340035a10361071345140c00e060501c0740f00100500498541541d11601003481400969840c402c04e082d000c03030389910b103900d07480c42040036035080060340c2d80c01040b0700705038510074103d040424650a0083e05e040310780b1a40c440c50100d080c11801640a5214285241c00d59000d000c04a40ca541c1d000c0c51401c4001303c1c29805400d285007040091806d05041a0400c2c082038500034011642c8030002101d0900080a1603020380080c2001da060091401e6031010b002c002c0141c50181503158044000c242c0580a68002e024481e22011910402d14030340a0060140d0300c8042c0400050500d0b030301d0a42c3c1c20680303050060030090152185410782d10000301c1c0901c09130340c035001171080215100d001105900702800800215013003d0000f955058640210350502401240c2171114600c00d40002045e220030150301c07829510685005400003150195483c403a02d68030030140f441c84022002e603125103e090404607200c8914405010040034000d0109410070303280c171048203400c081e4219160184151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447629514 1250 447628264 447628267
    0x9020102011104030b241309021c08030a0e06090a24060909140c010909050606270306181207030e100908010e0a05060103021512070c0203190305031b0f0f 68
    0x242c014820210500345042512800c6c0e42c02141c82501c4d803010801c0d0904071408000381d000b0701c41c00052040711100302c402e803003441d00841c120200080040514040c02c8262020b100c00c0c01c50342202901c901017102c007013040c2c1c0e11040b04030f80401c0c0c17400942000708646a4056642c01c0032030316540d00b030703a04035003040c600f458440101200308034042c078082400380800400740a0805250000130401d11242c82101151034030784022903502d0f581c840c2161300c3c0301c0d16003020b00800707080c620300e0b003a1000624080c03d00c0b03801004006544685407035660710208040801529103c0043c0e08007842a8200600640c20040500c00030a0b56403500340329080081d44548516411518150950342550307140e04e1403002c99008600c2a000048001a003107055070b0741215941d0000441c180b1031400c0d070188e4400c0540c480918401e004841d6000000349400c1070090b41661130f500280205524140c251210090005500300001100c1c001000c0410245101a4a805240000e0368500b000399420401e900d00f6140c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447630764 1250 447629514 447629521
    0x1e0f060f0609150c0f2012061b0c03041a07290601090b04050f1512100e010f180e0303090705040e0d0f0c052b030c03050c090409020102011104030b 65
    0x110311803c41101c0d010f2421802c0030f4681d07074543c0e00d54120400c0c01420304030084c507100c41c603d501d00c41c224514040542640d008016004020360340c0c0205076403083d03840908001c0030b0002070320b0741c0c22501007141d40c030005c5190516000014200459850407020844400e00200b0000381881700a910401051103003c1c00c044a40f003011b00c01ca10000d40054144010b041c1c0030044082d42800307440885408546c2c52034007454000c00718200e44036035821b001050030006641d620501c0e911080340e0244c0c000805c41c00c542030719480b1107030030f923942030043c500d00300307207420b42008003800403a0044204031040c1008240f50044849403451508180e45440c555002400d040c801d604103803240300f00b6154000020002107041d04006001001903401003401c1103414995102031000404c40c951101580198815045440000700c41c0780300303a00525030380080d00701a0344044c3c0c584240500342c01000c0d400f0340c0900c1d150003001007000030803004004034159501c650482c00c1d2815103901800003503000b80007600d028a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447632014 1250 447630764 447630779
    0xf0c1c15020a0e100e04022a03030405060711030409090f0203060c0d0c0c0c05010c031707020106090e0c09180106031e030f09080624041805010b03011e0f060f0609 72
    0x4441e210071809800140c054500c0151702900c0714010480685005a8510368841d01142d1400064001d40a47c4a845580760200c0c04c008011131046000341c050340d40c5d644540c1c82c04c0380c0da02c40124020030301d6441030105101001595210014040c401c030001c02194840e030780884d0801c1c41c1110148041080414038050b10041401110300000c03c81c0350203400d06e241540c8080c4101c015002d0507042040c0c1101800400d400741e480740e4810b0700c56181400d40e074503103008000e0181109006603c0e5241c1060b9800594540000f10300c144800c00400340b1030241e8445201c08610303844801180c20700d6480306400404100c4c1540f5200300342c030003801c0000d280021410f02a24200c03009220744200403100204001c040c0300414025001000e8100c150f8240c0405a020000c901c0640140c40c2e00514002c0c4512042c1c000c01002003032580318078000c1c803100381c5d0441098201c03524882d04111503a0700c1700c100007100303405512083d10305044200c00102c00c0c0e290b0340030350080040c603044240402c0c0000414440d45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447633264 1250 447632014 447632027
    0x30b0102061e132108070203070203100c0c050304030c0311010806032e020706150b040e0c09040219020607080a0506150313061506120c0e010507050c1c060e0f0c1c15020a 75
    0x740c6e40e0000314a805030540c0440d42c0c0e8a103002100302707810f83d0382e608101d46038418840801180e03040802c0304d03211078032400c0001960321381d071104840a0b0b410100d480c52070750080da6464401e04004002c0c004808040e041d0115144140e06007082400107001c2d0103406407401d1000e088131a0251200003082401c4200320358000c0e102da0080301482200f80810010001c1c0780502c2c66200006c0c00440e03841300202c46c0450041d015144160101e4582c0300307100820319078001072841c8a48200d568400702a22081c4403030007102d070182e03003e54002e5200701d00f00859201800c001c5030440ca118102407000704540c1c40c0e03002214851410084452020202009240e602218a2103280405041040492200b54001d840034000d421a0f90600c48040365020038080c003401044554803000d0552046c3c0a05d0012241071000c01904c01c4070814500380010458400016a800388103060500030114061031100304100804482c0d0481e800740340e00f160740400100c4030807418400c10400b0301c000d80c40d035401507009001e6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447634514 1250 447633264 447633271
    0x605060c031b100603121803051b01050403060906021b03030f06010e04240603110309070e040f06140a060e040b040210050c01020c03040303030b0102061e132108 71
    0x15600510105110000210865030101c4105016014501d00501c81ca03052075809021070600300c0c5003040000a02254a5564a040c03030680d4031030b5520108a84029540d02040c0000741003071b84240010f03140f66000710b144d01b8a10314141800303030505076295902030a13203641d1401154800e401180300000b000c14102030b0800c030140d8001035411071605460002840700c000b0304490400406108541c803135213459002c0260440c540e510b25140c650155600501130986100b45000680b030b055095085125400c00d4a00411301c260141c01024030706010120b15000151060303d2034080d50b104040026490710401e10130728000c454102851400304050745c21180240d1008030381d8490b1004000000d0041c0702c649500560403200c00b00030b8440c031101295180a015002060b562000414003503a900000143c0200d0b032280d0340a00c01070110b64012038036808203403151a0450240783c19807851440f078002580c5d215030b4a070f07024403003028281c40b50614881e000e800781c1404074850a19001c941d5000380c0b160303407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447635764 1250 447634514 447634519
    0x20a0e19060828020304170a020106030203070f0b19140408010506180108100911281403100209011715030f011b05030a18050f0106080703110f0f120307060605 70
    0x4103d102410024041d071400c0310b12030a581c000000340c02c0103005804001e03558a0b44919130345800c5400c1d8041d00803c80c50000360321a20400c940042c4850440c0c510406550010340d655082c0a29080464440c8051841d000c0c103000f50003c1412034801c060700070b44010464407002080354200b42d010700082c81004c070443c0505182d49001071140e100300040d03c002c002c49140e0005403400841c200009105800621a42d110002d4541503400440c0d144484540d41e5400400090341d541d41d40b54000d1025400180c90b415400034420000c82c1c0ca0300d0743c09030611440604103200506803581da0300803500000c540e4481170440c3c801062420b03050410151841030070590003004400d11440140701400354880c818002c000c4004000307425116650480600d50142e881d010305507403030030319205480d0b0000c105451000d610300380780007403c168000f40e410f04481e0040701000d0b03000300b0341c1d007400031518410702c20907004594100500300a03120002c45d1245038003010041c2d43c0700c40c0149014810350300e03550700851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447637014 1250 447635764 447635791
    0x30f0306081203160e03030412020102100b03120703020f030318010c020c0102101e06060305061819050c16080a110a08160201021c08100e0415020a0e190608 69
    0x4070036040388403c6981048945a10007180300b01c0701011946280802d20b096014000404c00080c85540301180a080318070076000d5485050841040c402147c07900046c2c10b038540d10000f02c06000500400050550324020300c10794a0101900ea14141780d9442a590401c10560180c00b1103a00c400c00e00c41c1c0386038104a1320182000200c02c200003590740b550850760f1040587d454180800500c1c020880c13201180c0b61520602c003490ba16031010740103201c00c136489802800034100409050182c205054420f981860401441c4086080d000303004040c02000800c0e0030354100400183c0344d20001d9041ea0700340c401c4128554a56002c1d0f001461748482c4c1c844002c00307500102c511400108024192419640d00002c1846512900d0004034945042c507245c058903590846250040c6680c00140e55114403080c2e88a0790001d641c802022010400844020742886030b040611701c01140c29800034050000146852140b00c107003000007036641d1444407102d014005012000b0007000e6000401c1c560300015001ca0070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447638264 1250 447637014 447637033
    0xf0c1e02130c0e0f010e0d0c140303190309080d090f02150406050d1a090f0105090606070203031603022e0f0e0a060504030201020d11030a1a0a2c04030f030608 70
    0x18120301210f00c2094400d0301c100a02c04116445180381030007801000b0040412071740541050160f0301c4041c011005c1805002d0010401030070004111502c81c890030295584020f11040c00b100244410700049278241001c22029040c0c8455001e40020b1034018103100501c0c40c100d1042210405503141c800d078150b4800c4c002084035540003016030303001c0c80d034100300400c1101020140041c4001d0b0324180300d5200401030b040c000202c1594550368181c81c02601c0441e880c0c0c98500400a160041080096240d0310800c40403007013607502d1b01c510030b942e03200c2d00450362800104800d1040070080c50761001a5412642c0c42080011b0303150041d07029103600b080f001c002d01f00781c031031925407240b45003000940107544410200b030405200f581115031064013001c2c2040301d01003410341c0c840301c0c0e0b000b40d4543e5009070604e4032000254595800d40d00010100800b4030078070920740070a41c80c0c2003003099584601c85149100102d80b070381d420504c052049100781d40c0c40210101410000d400c40b015500902456032060250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447639514 1250 447638264 447638267
    0x60c160609060b04020712081f0e18070b0a0311040b030a020c0c090702010f05010f08030f1308071508100509130609121710061d12070303021f02030402030a030f0c1e02130c 76
    0x744059800046003680a41d62f03040700c06200400c2c1d0340e8a06040d102d1001e0001c1d013203488001821003110155401d0045202501400c402802640152030044c0420004500740781819401056002010000d681d69000017400007280c9660444008016075120841c900503d203d512a0320702401d03801102406c1c0504280300b02d40d5034000c41e00000c01000001961205003203d9841d803400070a0351a0031a07070b8250312405014180c04421820801103038021002c920307807038003c0d00c0401c25030700c0182c510320060f500c0d01c20407089001194416203503659110340c0d442c086920b0711080540c52040d07032210300c02d4005580320119554070041808021038483c0505000240e44070801001120301501c03090800404080040c440c002020840c0180d4402e00070004109078010a048a010800b0b6110580d43d00c010341c003c0d8240c1c84200c2e0b00030760540101e040b800001c0d00070305070284190070718605000254803d0340d817049082000c00c503960b54550811031450452a010304100f6040b1082c1a0038405801d00e01c030b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 447640764 1250 447639514 447639571
    0xc0215030a0f0e0304120816030f0914091603020c03030103110a0e0705121008060a06030501151d041a040f0528020108060112060611060c160609060b0402071208 71
    0x807440c200c001d1b03103001003c0c40b0a07c0251108030202040e0032000c03241d04d18002e04035400004802000c6840308071300088a81fa0400101584400504800e009546aa00004522024080481c20b069003071016681c040345c1000a0b40c040e610550300164040d00f0841005140011540800d044900210400501a40c0a000e9900c032000d08860880e081c2c46100203030340984c0454102c4412440380d42c0801c405c180f0640c000c002102d000b20001c2000b031200c10120098200140901e50001410060f003406180b01d10442a5000b806040b141900145884c650704041c0d0080d9016211846030071850340502c071050045040c084488108416100182e5158070fa08110856019050000e810300182042e401104955045688810100030395602d4040c05080c0402c3c00c40c1e8040c55226090024202d41c011401700d911441e44c4c64441440b01d0450384d220005442440c9040b10b08603140e60000350b03175480d80c0c00a861628450301410f10a00200480207248660041c10b02400300400c01c540e00d850f40c0c1119 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 447642014 1250 447640764 447640769
    0xc010c0b06130c0203090a06030b010207050d170f1e0301030201140706060801110d061d0c0a140d020a03180c0504020c0a080a1125060804030c0215030a0f0e0304 71
    0x2014030441da107000000c2c51000502200d518250b040ca0100c04940d0390110003485449001c6070b58484190316080c00710100e905000c0c100e070145e84078007814801445c2412808101c24030039280b0340007200110b0803002036504040e6100c4d01c2080c012480d51241c509443c811000d90003a10b4065055603d10f40000f040880d46e25496400900006044010b2101541000000d0318000e0001d020035010a00303804555401000e0051040d0315180000c42e483c05009443e4600662001800c4480d840b03800c0f01d40c5055000d41559010b0003448256848560000c130b01601c0324164000d401a1a10200a4080c0540d610307200060110f800c444c480d880014100c0380e0400a2701e4080e900180c0f00e2415810b0b091801c07014020140c8202c801007845444150312207210202c1d01007803016160f010985141c411034503591a00400304590464005100c070500c9801e002c2e603c58024a480c0009840c6c0e500499220101d0403011803c0d128000100100c01016008050030304048600400040ca00c03481055200e00460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 447643264 1250 447642014 447642023
    0xa080f0f0403110102090315100501030603050a030305060109080d090e0906040201300203040b0103050106050d080301062a03020c1912020f040204051e030615010c0b09010f0c18080c010c 82
    0x42d0b10f66503c0c2075003541682c000b560301030200d400030030b56a5840d0701c8000044600c502c0f0103244500101755548280030b040206d951050080c444003034141d4047c0c000e0a00101150704002002800007011141046080403441445e1181400d0a00f0889840740f1000c0c002c01c84465940b1203c107000041c2d902000e94602d20036820f94114900c101c1d9060710b0105000a01070700460b03030001c82404103110f80e4940040c1205d10603070003002242d0b80c0d2418071050550010029061260600c01040018092503c440841c43c1041400c2c10101d10b0ba41d00c00c007c0012003000750011381c0030581408850070001e0610b0002c1c1344d08542481218507155850703042146100009004d0071913001240c00b07075105d07901504c001d094010216019410806540c981408003603501d07921030b200b618007240e02c2030040c540c40d50032000c040e5034100c480c90950315061503034030014110800665880b0908400d484803442141c030002080c4c0d0b1405040300ca68a0000c0d41400c1ca500001c0780c50300700040651031030780c0000143c807085900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 447644514 1250 447643264 447643277
    0x6010c0609170c01141e01090209030316060c2d0509030f15040303061202150c0c030303130201090b030709060c051c0302071b06210b03010608030a080f0f0403 70
    0x180b40c04894032041d0006004140c8011400405251064100f5560b030802c003030b9980910342c0c030400a0301c943e1000d0a5203500303550072400144000520380c0c00038002c61001408a902e0005041e4103520111000107090303c1596440c0c0c20f1003a05540880e00d070008004001c3c40d0460107030306a1401200c0d2204d017138020f01784400010610540d8030700b0b1141001e01040340094591182480040900c0900100c400310000f9142004c0420345c0c015a48024412a03009401c84042c220b5048032601e40794000841c1003600c5c4214640320000d6601080114425000b07010040340191403440050500072103034101c44440e1805004200702d030341d402490801141d00030301d040c0000d01d159003000c0b402c2c01360211050104405916000381e08581540040840b68402c420050307812403500b0601c01e07094182e028003000102d00801030440011034012100045000d02400100d0f2038100c000030382120120751103641c0c1c640000c00d030701c4801f540000d00c003030707001c0c030ba40a00c3ca040345424521302c8802130b4004c0005043c02a03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 447645764 1250 447644514 447644531
    0x60503120c0a1205040612060f03030503090a21020c04090b0a050640020c0d180503010221100608040f030c0605190b03010c0206150315160f0806010c06 67
    0x1c0400661a81d40d4000601072502d00e00800020956803150003240e0124841074681000007015200c0c0030101e030b40310580b10310782e0b60942d5011922a40003500380314140c85001c0c03000c00810380c0308da1500d00c81c1648540e13034000300362240c8000e41800c0380140c4062240e454942c400e400700e92220300182d4004110040007820703a0b01c0c2400a40b07049500041211040c4070a1000c03580e800400f2000316040003040c1107001d80000083d0300c142070384a0710b240410280c001501603104540030f00032140078000003605049015480c1c03800b00b400ca801c484840ca240c8591101006808903212000e1a000920307100002001820f0500291040308090030041c50300e25900c08800034184543d40d984101507005405200a041c07121030210b075038182000149001d4608914015203140511980d5a02165038000d00b5103507440c0c0e0100e0008145581d1200d800d40921540c0c0d90403039401664661160010542100081540800051409070354010580a20242205212042c1e800c01200c01c501580204040790909 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 447647014 1250 447645764 447645787
    0x30305280506040e0607020c0103051302061c06180605090a1107120e040c08180f100f0603060c021e010605223b06011202120102040f09050105030d0306050312 70
    0x80130b242c11411501468083c42141c03a400305404c0042842660140f01a458404803603010b1111190002d611076010400c0c01d1903035001000c429011824071400252140da07074107014079140880c8412580c0c0c1980c5040c10f12031751070468121070700040720000800844810b180d00304918461320300050128203038064015501886080c580e015039002074402d04c007001e01014060040142512500c0c100304e42983e03e000c0200340040c1d4000319040010041544103403203902c03003004210341d203c00e403034094481c000803002c940580103c4940810741c5e401400411c82088510803034014844071140e02d41d041c81400c0203907640d454a83c4800050440042350b51100214196008000003049070381c811030418034104540310031214440058400d2144203443e00030716008103440381000d02424490100e07424000c0054105503c200664860007000145410303107841c41c00000031505e510415205494030018803250030300b84103260341500c507420280f1400b0300742070010b0b40f03903c81c09940c04265071001c20300c1010070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 447648264 1250 447647014 447647021
    0x10c020d050c060f0315010c0b39220b0403081c09030f020c0303030f0c03060a0803041e050108150114130b090103060f14060d020c030a02070303030528050604 70
    0x1044001c0c00f00e6915804010003808641040b1002c0c41c001c0c940c0c0486108550091016981e80c41c0d108113810030760794640b100c0038054491420482c4c160000031440710410408946080c2c45000d10150903610307800100c1d098140e06001031040040c03502e801300d040188098800030303502581d030300103401c0340c890310700349140302c00101b5043c40d10900c079003050410424541c0000510034a074131345500f90b80405150f201450303942c0c03100752141e4400c54031210004900018400146400030b2004080c00070f011f564140c2145180c000d9088000d0a03012001e107411003c00d5602da14004000a082203000c502d080302c110301d640c400302002e0505001600914070b03000e800001c03ca410403208282c0c100300603912029a007503203421210f0b40318046031814001081200d00170300a08121201c0c00314622110b802001442407680100441500c250303000d0241354100c08040c000707000394103a6603009080151543c1401029900003509032200310f03c0b0206400303a682900645400038024412002c078294a8100108008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 447649514 1250 447648264 447648283
    0x30a11130302150403020a050f01020c030312010e070f210e070306020d0f0509030304060903091d040c0f05060a1d060307051206040b130c03060e01080d1d010c020d05 73
    0x29010018040049041028040003600e000f500d4110b0030042038205180c0c980f259010180d48a558014104190b02d000d103112110600c0c1807041e00c6031919004042844c0d41c115045510070b1f085514018000c0000040602c0c0c2d01c10700f1460700ea101400c1404c409484116440c2540e980c10700b10540c004036030341c071a070010fa80c41111041110482556130404000941205402d18101c6042580300e5029408034055540181620f1000e586142c5480d5034500060032010011400d001610400280c0101c50340f0520901e450030014a01f128640f601d411402d80710250814406000d40c90130a0120752258400c1e03404078002410034148600340840454070806140030b00c181d1194000003002071099121010708054401c10102c0c0b1a161100d50420058880e00300c152504104c02da859066030200c243c010a00c08412410001a12a210018045c982400743c000c004186d00c1550315200450303001c01141303121641c0c6c190180c034000c80b000000f00301040b040300103885001c8400517001805402c4c48160324 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 447650764 1250 447649514 447649541
    0x1507020103200307091a13050d06090c030b090c0d0c0618180b010f020f030904020318060702011a0109080606041112070c1403130b0d061d0435030a 65
    0x1140d04c1e000c039000b0000062030140303850f03048043c001c044908400c0005c1c4c48000310b072558200545c030308000901112810780e40c03096850f9500c892010001c00d02141414004d18002c00c8400d03001d103041801a8503148a040c034090040d0240100c4c0404100550140c0d416a451450334a58404040071000e9150499401c146801480e000d100803a980495001400008003a00d0728002c42c0040d420076a01d4104001545016410030489100316140c2540115801400c0039185c000d0740d43e40050306403900c3c008807100310140c0c1d0340e0109035660315060390400d20102c200f403034220519030900f00c1454403210301074449070150f6180c0e07078806140680c51040d0380507081042e0f144101440c4c1201c00910001400f01c050318200040480002e0b01d01c40482102d481003083c0c420380e02c61314542507403181144d00404548040940d100d00c041507070400c03900240700a02d03074200602801c0c2401c0c10101c0f41c40039040303031406c03d0142c01c1d207a2041a02002d604010081d200842c50742c1c41c1e903144001c980140007003c3c10a003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 447652014 1250 447650764 447650767
    0x806010309150b09010f14061b150708060f010905040e032b0c0504051c03050f28020c031203070c0b04140d021f0b0402040e1003030e150702010320 65
    0x40b45480e441e031080d800c0450840700119145d0f690301050304003801ca80544841c0c480c5100300d43c5000e0a10340010010040f4040e98019140c08042c515401c051170752034060341d001860400d11080980c8020025080903080703d03d8007081c201d140c0041d00e142024070a440c0203d868049010103640180180c903005d45600203c3c407040b1301284501c5541948003a20100a1454142c0c84406c0360b206505603000e0b02d001a04804440d0700d00841412281a4510700300c4c10410200040c040c0003004402a0110f41440e010a210280440d500c0382c21807904000d03d40210351101000f840c80b0b0382d0008880c00840810b143e65603807a00d881d1000c41c0d05075418000074015018940900c41040103038000744407258240710030f031401501ea418049880700c2040c81c00410100002800c1c43c029007085d485510720311002040186499030380c80070b20309035000450301d118081c84908001c200b49600507030000d03c4403804031104600c8450041c1050114040c0c020701a041655801400c2d0154100e0b6202e494450059041d01c2d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 447653264 1250 447652014 447652043
    0x41e090b0a0e191d060702010614131b0c05120a0f180503030301060f030e0a020a17010b090103050c09010602030715020d090204050a020406090617010b0c160806010317190806010309 80
    0x4422400c01c240905021744582030016400907c10b05c0f4400c19182101d003541c20b01d80782a0708000e00e00f2000d400e8413a90030f90310b010171080c0c00701c904a120000f40403501c85d41c0407003809007849824405030454038104030508002110381c00d617011201c202c2503030b0542400c180d0f800c04d060b0801d0140c511608404d0700b51100000208036250000c095660303642c1c01c2c0c2e4090100d046055030b01d0751a5150460000d41284e0080f4092240080c601d1048948000040c0002168011080020594a003e034419a001e42107001c030b5074114184061038501401c5d10780005e41c601407056440b141420340d0040c0d5810031507404206070000010382d80210040ba500200140480d0030807440780301c007e5209206540108450210004616010b0039072502c00303008180c110540b5038a03140441c0ac10b94080f260020090107011104401c1e20540ca5450002c1d01c0448018041c546c1185424801035480040d00c1d000000e080c803041c12101004409403010b5441031400f03030740c10307100d800060700a40f550850007880140540e0b01c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 447654514 1250 447653264 447653291
    0x60207060b090903090d060e0f011d0f06010614090d02040f060801270f1415010807051c06090302071a250305031803040902041e090b0a0e19 62
    0x3035403044003180d03940c1603503e4007003800c0d80c3d0b4800c021010b5005421500e401002c40c072294010188454500295106402c1c00c680d80ca00b19001c0400d4800d440003003104900350040b040107422600c5200b0f5000381903650410b00090145412552501a90100040c12003480c0d15040d8000000c1a8007a00030312001400c002040701402860240380515880e1801c40c00c1e603a040c02c1c1d010400d4029183c02e2802400868495010400d45030702c081d91381494810124080120810078a0070f201202054003890754145803100382400f0059115600c124416600c4804800d5540b08000e003c0b40d004c1c01c000342801140c6001d90a00400f64070220360703070010030081c02ca4900c540c002450403110f5420401e058041254015000841d1900c020300041c50078400a0fa0190b80d0b0038140742c807181c2c4281264100f82d0794030449402c0c0c2e84950090820004010b0980c040b114600c030440015044100c0b040c0000d2045a0206404604030300c5100e200e480040017080c09034882c10310300001030035036000600602080700030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 447655764 1250 447654514 447654521
    0x71b080f030708150102190b040602041a19300b060c0706080901020406092c040309060305060a08030d151701090201090e010803030403030903021e0d0f021605010c08040306020706 79
    0x10790f1310301902c0301c88107201c056202040110b0051220a403000701010641c8480d8148000100115402507003008007241804c00900000d8210035040c1c581c5541c2c20501a4885112138190710150030310902818141d5504129040000c0c1d40c0765041030036543d0711142003400040c00c402c01c0304541040000440407003030350000c500b40d0103450031034031500325a81b40e82c10861b080f0300c120711542c2d000076034019041c0480740043c1160f1100003003040321801040f120080020b188002968200c010039400392082101503010b004041d402142221007551070b92801c49129180e109400c0424601e907650800d1108070500000030304003400e10381512017629011002154001c088140c81680403c4461200207105e17034000301814107840b0307184051411521143d0f000c5d009050b0380c03035086080d40140c07205805505c00fa0403808100700807030001000022401c0002604d1b04e913080174824215000001c149040b002e0400b4184100e9900303103803050381c5001500300f10349a4025900001c0c80c103400018100d040c000d1640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 447657014 1250 447655764 447655771
    0xf01060311160311070306051e06030a150b01180e09070e070203160303060302090a0b01080c2109070315020a0201050c040503150406061a031905071b080f030708 71
    0x4400304541070200039080c0460162281c0d040c0703803442030303440301000a104140c14910042410300720b800d0141c4a40c2c401042e28012202010404500f12865101c844400450b0b80c2040e02a006043d131910291190940385810240151006489605042d0264410101c00990344491044000c0d42900c409082081303040a07194030b0258421120003040c8251001c103074a0141e040f0303170002c41c604040010100c0680311030040540503d80c0e01c06000000da1a04080c86c0d209641e903000008000c0d03400340003d000e401003d001c0305032101c030500900f01a4288004825090b1940c0d8042504641d142803080c1d06c0e01c40c9982009002c880c1d1640d00c0e099040094024041819080d0001d000c190350310001c3c400d01e4041c038410180d05500600c42007501803803207201c0d250041e025240104460742c4841100b50030000c9c5000d00c0d42400d00000c10040202d2280d00703c2c21465000c901c050286090032000182000030300340c0d60748040750005070f00c80104070714002100c1c00081e00c07440054403880c041001400c0c980045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 447658264 1250 447657014 447657017
    0x6151602131b0f03060b030a0f0c050f040e0405010b030a0b0a1b0903030509010c080f0706050a060e16030f0912020d11120705030715021b0a0b0606031e0f0106 70
    0x3045014440ea60b40114620034403800c464080c485101501120000148032104041c55075502010601c0f0915400551080c40d0004020a4004518002c4002c403002840750408010082c06410388072400142151b0488240c0500d02105807510f0a040303004240040d4a00c3c2e043c07085c02c540c0310800c44500d500c0f0303205001d002d40c104001d804262840c41d45035042d400200000783c0380e540900c002030040001e008400713010703d01881102340036960048245d2040550744030322800800c42d8001c11205001d020342c411079903401800464a0021005032007140586070301505000c00d5940d00d10584207900044042c0340c50343c000c2c006c02e031442c140410900b002021103001401204c04c2d58606034040c2c3e07070445500c00e0560080440726201424441340d03402a400841d014002000030381d012400021324080764000d4210010394038009444000700e601d141056501c4241c100d11001000305210603002c5501240c1070311020303a266038900d0390381c0c80d03000350203280c41044004e9810700041141043c1001d050b200035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 447659514 1250 447658264 447658279
    0x1e0c110706020109020105030a0c0c0215180301090206120403021911010801060305040c05041d030c030301060216080604060f063804030c1202010507080a110111030c070b06151602 79
    0x50310402c900307079841c0410190114200304003095800c0c46907070024110105510780908444029030024000512000c0c6641a203040481c200d400d0030490840c42140d1082203002b0400c0c040c241c0d011500310301a648030314441d80914000181458000d0101140d00507140680940038002450402142880c00024038002106d5800200d4840c4c000c2c0300d03141c01240c0020f01590b440d0320345400c000180c5030140070201d041a031074035110981c28081000d0040700107100b010310389a40c180314000b854041c100d004d07000c042d0f00121040010942c0031410a070080d40081c004103074003031007a8142001c1c1040f5405484400c00c040020b02c1886280c00000c041d0010905261213892140c1811004502407400003030201e90340401c0403c24008052002c1100f0352045c108a41010159100d4500030f402c001c2c040404110220040351500350b0038807800281d441080081c5045003820f410b4101c4038010503000a00141d03240010800a50300c0c0292140b030382d0082001107648504035510640c111080300c008034042d428 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 447660764 1250 447659514 447659519
    0x2010e121228020f0405041b0c0318150203090112050105061b0a0606081606030903120203130501050a0f0509061302010c0f05060f09060a1406041e0c1107 68
    0x34490803a061140e51a400d0115600c811039142102285407044031640e403825442c00079801c03400c2c00a08103100b0300307104a80d180c0d07191000780010784000516412004101000c0d0f0100285c010003d442c5641d014a0051880d040d0141c0b034121521164000310f40100f03425a103c00040c0d800001030500b0b81003030382c40708500c1074451407650540c0d0003809030a52101c0244103401c9055070340da41403802e607010f00d0304945044890351115003c0760815003010a1940005403429942490300c1440e00041003903260411444180e0b8500801c518900d440040c4030a0300000800c0500d4080e516249165070040d0003003000e03051041c401d41c0240100d2002814107804d1000017a0001d00200c0e4080c80f0b0450b20685507600c2a080d0300455081d006001c080381c0450f404c44600d4003252017000210306c1680a50000003160604500c014541b150040c04a90250f0400f1002307800c0011012556030455009d03034010405140701c0440900c0f02c400d21020b82c0b03000e8500010880c0c15540140d0b890004c0c0e40c0c40b0709580071b0a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 447661870 1106 447660764 447660793
    0x30209150c0606150a020c101e080925030204090318030b01060e03030c0a140a060e0c01030e060f040206090406120b0402010f020f060a110405090702010e 68
    0x18001403c0151509100c01803502c80c10341440200d08095010340c1c001d42e5540380d000ea00d80940c400a142a413094050501c03070140000c2d0540103000b202c00200000c00403c0b048682511904c100c44100100785042802c1c1c84240f072808041925041c01d64080c007001d0700141104404000c07140e129540c02d18100a020310142d44201e1010f0030035450140003c1003410004501446038004000c442240f02d8001084140d85900140503013510000305141d901700200300c0000f5124604000101d100d1100100d40c6040168090300c2c108502c100c8540c03100e56136201142c41e00320401091020901606c0c0c0400580294100108042003183e01c9061650368500401422181d04a02d10280700071980c1140f0034080e0210b081c0f0090041c0d02d0000001a0303515005044c04200356a01c020340300a000000049a001d000b01504e1540c05080500e8003e000b01940b1074605840c0c0030341c001001c01c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 447482014 447661870 := by
  have h0 := BRFrame.cov_init 447482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 447482014 ≤ n) (h2 : n < 447661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
