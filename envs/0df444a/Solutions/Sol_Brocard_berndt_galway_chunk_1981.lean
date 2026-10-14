-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1981
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:53.006411+00:00
-- url     : https://prove2.me/submissions/32665861-dbab-4096-ae5b-1a934e7485eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 356115107 ≤ n < 356294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 356116357 1250 356115107 356115161
    0xf091202100c02150601050c030f0d021801360e0103080c0c220c0e090a0606020f070f050d21081605072f0a03050c1813060b0301 57
    0x5940001c5032820041002102e5850100b42e03a01d21070054040100c04030b84000070903a40c096800b40c408030142c00f013902e2074554140c103503c00551007140382e070002c41c0d80461201002c40c0e066401c11a604403e007030444101c00a401070904840b060340c0b08603902c02c800c1011180b20882942c0f11002041c008001d00d64a503140d10380707982c1d140c005448540d094171815003040210700e40001c5501c0d054010700c00d01d5149501401280c8050045203e1020501030190801c4240303403103d0141740d1090105c142c000600c5420a00300a017442e1a4085030700d0540c0c080d050600c46280740078990380450300115051134020703040349486040c40c0500600e1348108054225840c200540000f01d0a00c521044203041171305035001c02003510345018165001e003248208800341c071071010f803103490b5480441005442180c60302d00c02001404422050300202d409410039402908142008000e018440025200da0f501ca8075080051092070f519150024145507200d03041038105031020350040880b25805101a489000d88003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 356117607 1250 356116357 356116363
    0x90e1b1908010f0f0209010801090e190302030a020105011a091207081204030b010803030c030408161212061401020c0d1511030106170c03070c0507050a06020106060f02011104090f091202 82
    0x202d40c240c043c0e0801c071441401403600c0c402c480d19003105845001d1103900f8040c690000304480c0c44034a48030311400d610708020384410904820401d1007940290b580d0441500024251001a03001003440c0c8240440e44107030302c800c2c03000d5030401c074425038008000c040828103451408141d070744002b40038010b00115040240381c003c000d00645c1d018070540700940e6038441c21030759203100444030700920b00c2c41031001c100092141c0c40140307044144040003080034146a141e52a110062801060210b20100c0c0c0d910b080d003210b40100001007013200f424055038203206001030340781d0358401c2120340f18841503130709003041000b03d075500d541c1e44040321030030400c41c07060900510280e8021300841003c901030342d56040c2500000d040052003410009405421626660001e07039507406218400c9400d4050581e0220b030540f11511440014001e5074004201107250840140411408400300b030110f90402060b1a600a001d1044070119020040c00090211014207080018580c6480042003030101600103641a9400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 356118857 1250 356117607 356117621
    0x6130e07180501050403060b240c01060501020109050c10090b0301030c03031209170a020f060903210c0f1308031804050c071106031f080115090e1b190801 68
    0x55280e44592495828403181c0341e45075407080c2c1e030014008100c1400052010b80004020380703406048061b01c980304211204182e400f02d441080907020110f80740a11400901801c0020082030008108200c1240c860580707404555007010b005086559101d81860b209105940c004d00380b21070344a8403541c591611300050442884150001100c03070039000b00d10107843c8541510164000b8100400c9005c5c1007022220360803504021066005141c901d800501d4113018581c4200d0341140595501e81083e81b03ca61072481078001d4194440ca072a08000701e91840c102115a5410032481e21903c58203001406040301c04550048885400003141c1d00c0d51498036050b4500503228211401e010550340d1b40c24080c44c501820b800500031010b800054540c03414107500454000c40000c11071182010300f02c2c11010807034030301c1d442340d28182c2d501c0030014064071070641c0c080050030104406001c485504902c0c50f43c1c5018460b03280309003200611000c2400d6498004051303607014043c030141c00c000d9030b801c1206c1c020102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 356120107 1250 356118857 356118871
    0xc0e011202091006021b0102250807060e060a1218060c1d030c01030902030c04090b010e010e160813390f061b060f02070618170906130e 60
    0x55070302107075407041d0540c102801c0d00c0003a8002c00c1c4a01c1c40c500a42034031b00e1140e01c824154001c12070401c0c0782c80145224010341c80c010200f007034070903481e00c1007440c40c20b10f040e4406010403003041034008696561004590880c509c2d032800f401107080c5000301c14010034584866038602c5642407035080402c203003034015940e940416201c808042224840b2070030954031000043e0341c141c200e40a0400b06600136884841c180f4000f4040f280701c1b4842002050850f40010020340d1020740d2180108007180c0701301c40d0741d0301410062415003002d04090070350102c07801e413040d81c3c0d0040c04200c500003007614017042100080c2d2078105041f084986021a0b40f81c01000050740407584c841c034412496050806400a8002282e050310341c01141c451900504495078002217180300b401003034180c0036201007512030140780550b030b0f5410b4005075119100d01e810801c50b03480500754120181d1000c08900840e03010304c414040f070080c98a650766242c5004001030f400e84980c80350422100710b030351004600e80f91900d40c401c0c8560b038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 356121357 1250 356120107 356120119
    0x1918030305040210021b240c030712020a030530042006070b0f190618050609060307090c0c080c0d021203040c06030f06030b070c0b061210090c0e011202 67
    0x24404d003240c03540c402000c00c03144103450b04580781c0a07082040080c2c1d4583d01002a1414180029000b0781142c2c0c05100d410f0b1f801d0f0300c007080c51424041810048105464140002c004e500d0007950060424000ca0101444144001c00355040d1203986144440c00c1d102d594448803160b24251400d807042c00e0340440c04c041c1d0f4a510440c010301d9410500100c5040c5504003200401d1655503184142034040020113a07a94240d0205c08405400d0090003190b018040044080d1900b4595105500486000812181c4034080003c284511611f003ca040c006440c0d0002d00450107922030101540d042d4110407001782a83d40009030701d5040030003c110700800329003d81c2036801419505000ea0484d020554014240a045807030410120b8000e131f001c25134034001c0700300c045800e560300c0c2c491981c080f504032400004544081010020810410305096120b0002c9903495403200100200c1540c403090003060712081e50392800d00034103001c0728091240003409000c5c1c1d11002582c5030000130a4104540070100d000d05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 356122607 1250 356121357 356121379
    0x2071515060206060910050306190b09010506161712010e0108010207030f260106050306010806031902090a0216210504050d0b0a06090f021c02040602030319180303050402 75
    0x1200085000381107503195030003083d203612032504226602c20054010710500c1c445880004041c0c9050007058420300048440034118400c1c10f1f02c000540c0c0c50b8601a500c00d44031303900103000d5640c445059030107421515140000e440b07441d20b0a103694000151520300c1450300801c0880d414907149840905a0b0f07600f070181c1215980c0c46c1d428a0a03401035880c002c0c00710f0340b00207035504000e102e14690383c411303022803009c240030824002440440c2d6074281c10680006200008011155030442411030304100d060300202103e074401102c0091030f000c04c14000b0300c186510004a07490214580655104001c50403aa00c8e40410600c2e042c40185c0c07204082d030038829010404408881c0c0500c040d141110030142071040e610f407141c0d45030191304000904400070315903200b001084038050752144404070b00020f080140e0314119001104141d50b0101c5220110034010030040c01010307070101c2030701d1f04000c2488072000f0012012500b00c0103400c146841d240d86030b06103440d810500d0303410303000607000d03a0007951301080c66 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 356123857 1250 356122607 356122631
    0xd0b040b0405040f02090a020405060721090b04090e010e030406020d080705030907060c02010512010e0105010207230d03301103130201080c0c0a050c0405011d01050d030c06020715 79
    0x20b288100e4000e001801000544000360400d01c00081e80310070108401451301e0307214030006807640c214a0090f61240300107003840d01d41d0f402c03000c080710801c1031350304101044524042262180d48614001e03205c20f10384a1030000071030300c025001849245c0103d0b080d01d84035911580002c0d031342c09409140c8000100100046403107140134000f01c84c040d0000e000a0b2030041c0c00d152041e2181060048100e040040404c926030030b100c0350076005406810251208400c81d45020002407a0030010b070071100c01c0307105081d02d91841e004601e08a6100c0b800540d554030507290141003e648542c420220104000007e0203412078075268000c0c06d02c00000340710070410150020b241064204e0000f04e5441200d400c03184a85005503005140d29503112071141062850300248105160802030b08020896841d1b021416984403031819005041c0074064031100b6003001801c0d01380c030402c1d060701845103a01421890a41800345032054810305422604108150760ba402c1903d000351840070420013400d41d41d4030384036451301c072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 356125107 1250 356123857 356123861
    0x40b280e01090e2b0c150911010207080f03030604050402060c0f0102040501030606030c02101a0607080912030309060f0c04170d0906080702030d0f0902180906060d030f11010605060d0b040b04 84
    0x4c0e0340201c1da24030094042642c000d4480c504c080c0e0040c0d5540d40499503c1114000c9401005801071007007945449485000001a00d840c542e50441002030300019a01c0700c1002e0008182e03903010340c0c03c03507021803541c5580c00428030324070a500c00c00c40b1500a2026100009078150000e008035007003a41d08200d030301e030341d000d049046a140381d2840c001600445442c0d00c9501c0e96030000300c55000c40c48200e0030349000801c00903c0591102034211200390011401800c02d15011100c5016049440f0155141d854031652150700e804d0001c09000c8411076140100d4032010b140400c3e6000740194022003e220151000000e40e640303000311149001801140010601350700c180e2030a03010f8075468005608000911071010f028100340c01c0d20800444d95541c4560140c0c2d02c0041d01036150003180d00e078403881d08110b07403601d04015000704080d015504e0840100e0010b603000d61062140324080c030f000c0d00c1c4503070382132000c9015005560000e5440308020440901703404031540803a41c1014201c40c20090b210610041c401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 356126357 1250 356125107 356125153
    0x1b0e0d08030a0c110322050d05191401230702010c0923090705030718051f03090b1f0602070503060c160f030c020f040b280e01090e 58
    0x480680d050001c00d0b586540c9400c400309140c01403c0c11800403920701001461600300130040e030003440f001801980446081050940070701001d950700780d81a01c03207445090792402c0100c01084240d450070306020a006100c10131800900c0c24600074811414081995907440c8400310800d03a01800700300101d00d405005105192042680d40c0b5591911460291280501c9690000400016100034030364031140d940c100c0c00c00e03c1906992207083d00c0c0d04107440020b0a10400c070940007042d11809000380900e80e14600540b030383c5004044a400c0c2043d03961002c50180840d090300410074201c1c503003800340103105035043ca012411070240f800122a95030a040741d079054680720305a00741d00448082001c0a403404028200f002000316000d810307409a527550049072800c42c07401e5001403005101c4070118502031092021500c0d08031000c2c0507810a20001404100901c40031841c0080001c8500980700744d440c4c43c4100810b200c010866640da92482254040c0c5459107081c40b49001c0c9058120b002213039130501603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 356127607 1250 356126357 356126363
    0x40b06010e030c01030c090513020a0f1d2b05010605040b030c0a030b060a0308030702100b1e0904060e12031501140d020a120f0b01030501060e130b0d061b0e0d 70
    0x40303c602c00280042d070041244110800030821000350100d090748074101e0043c0342060009005075280c40c8400c0050090078180700c90010801345d2003880d154050740b20354000c138140007102c180700c071660000c2c4e07449880954003ca41e400fa903210700324501800410745c044000c0b80c00503901400303403403003810415860b1024449550350002d40d89200f4004110801e1403603030721420141c90062a507490fa16a080e01d60400c60300e40005030b1003080e41e442c3c2c201c0c160044140ba140c0c00c0d150444142d042c0c0000c1003201ea1a96040340c0100d000d000040d050000c29000080e46c0a11507042d20100d6822003000041980100e500b07103804803540d11a41c6241d4411a82071810144c20007403641442000740b28007001e9488600c036101040010188900400014030400108000d1180c0016400e120b040000d030994005a0220040c042e0200d981402078941d070400040f40701c2044d81c000790fa1020f1000040c1c000c941268060b0030503207070522007143d6641d4a00304142a08450315a40b0500540e0420000419920300b002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 356128857 1250 356127607 356127613
    0x60c08090307140c0402030f01170a080406120b06031906120f02150c1e010e0d021f0216030503040c1a07030804020f1306090e06100303052a06040b06010e03 69
    0x5501044506403030320f80001880303042d81d8034100303d0070018059070019111111218940001000000107041d02014403800420203007001c4405a110300c000c500651156000b401440d8081c4a025103096002c019002e0b4000e10058482c104240006a00b22078a0f030130400c0d051500801080d082458401c14141d51ba2000004079040942c1e4240602030204071540030b000c0c0300a00400325440d80c20303c415054594100004009440540702c0340c0e0a54003500c414845581001202043c3c1e140c2c041203040300d030707240842488034804950b8091030091103441402050200c1c80e07105681010b50060045010386c0c01001003100c0796440b51301e000020b1050150403800340e0010880000040d0182c101160300c14002402c4620700d000400c04640e58181068104c81119520482400403c40d0341c429190300b80200c0006100d01c0c6041d201c59400c1040301d000140a220b0003044190303125114024003c900d5a07804884259204050f50304c03030b030300c1e0416281203900c2c036640400960254400d000d0030000d21001001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 356130107 1250 356128857 356128867
    0x70311041404020906160501020d23010302010818160512070b090d020d0605130618020303090409081309020a0306060e01050d0c03020408120403050c01090e07120204050d0807060c080903 82
    0x3044001c0d070044c0007180d0006400d120100742c40800410104409000310300141e0b0310b0940c10440400c03a01e241c081c81200146545840364144039078620a815654203092214003501c079030f4000c6500c4c03118099060314500c80d400c040d0101110f207803010320032540c0903190300c0300c0707901840029a243e90047c0690494048140300002a40c980080003226a83c0003401e030083e10b017520f44a1500742e5004880561180c082080d20b030702006114410110100307500c00280750600e00a900180d268411070341400c0c030440d25801c510060203041c10858440c510310b008500d201c0da958984030030103500241c000300042498690000341c5640155640d03030500c03405079900c502c1d00074009529402402450152400c1590034030000c140700204000e041d8581d04001d1312141c949256141c6a4602848a80c5040c1041000c150402000c148204810b81003071131780c1081004110b101100c0c000a025940c4a141c0c010088070600b020701041a00408000340a007000340f140000c00c0c141a03481401c240c0d0580443d601c1005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 356131357 1250 356130107 356130109
    0x40f15020f060c07150c020d0e030601080c090603010f05040b102907060906061710060614181306080f010c0e04020d09081b07061b03030b0102030c01050106080703110414 75
    0x41c4070061140810381c2d200345c2c01716002011910713540004800346c6c4c04400311401a581000912447c080b00701c000705129070410103860348441b000c26000b030240319420b0210782c6595081d0040844403100b05403c02291034203040c000c901c0c00c400c1d9078002108100110206040083e0b01003110403110f90300a01100710340183d40382c0700c5a0300c40740094840070390300e1100c400061002d0061070700038488103100c0a0020400744c441e0342004400c842a18619140800402146800c2544c1e0100320319044502c0b902c52948201c8004613600107594141d00c82141c4d081c0c0c41d050200c2c0c2d40290140c40d80407007211030303008000003142c1c00c03200c2e05641c150103c1e110400c800c0b900d00d072a40080c803410003d84008201d9010030380e604803464200105d180d0180142520019000c9010050b280003051140340c034415900d00301c0e200c07600260600c03001404050300c0e14034540721a4000c1040740c4004144100030031656940b0180140f01c42000d03585500000e0400134234901110a42c01542c083c0c03400d2070000311420280d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 356132607 1250 356131357 356131381
    0x52106010302010c060e0f03180105090901090b0604090e060a0609090203120a0201061a0a030c2d0516030903060b0a030822080a0c0806060a12030c051002040f15020f06 74
    0x700c101c40e100d480e00050904c803601802011f840030103000080d91074410020a0050b6080c6030160241002000d1180412642c1da548880341103441a510024090198001245541c0300e59002441e0060804200300084100000c0240c400e0140a80400050343c8940070107042d140b00b680c01a5055000d48031130705a05584070024000d44109000004402d6940e40200345002c0040600d0300085030b0224000700580c2c3c050181340440b4000307191100e048118007002c440d01d03804000d1010400102d40d49000e0140d409601100c2d0807522a0f0324a000651061400515201c1e00307000841b001410b140d41075045041c040146401d89901c00ba060382008805c0842d600241940c00c40003030b00da9224100080c1444090044402d007a0091895503405800c1c00c00983c5009805000309000c0c203050030041005c0f582c003180c1c1920300ca40c035181c0300a0800b001d06142e494041c0d414001c0a200b480018001050842e18602034201c4080078004610001c502e01e013a40c4031084005c80603820b070000000140443c11035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 356133857 1250 356132607 356132627
    0x121e011208090415120f050114010807090e01090c12020a2301051303020a06081f03030e0f0d1b05150a090e09100507030c0e03014d0405210601030201 66
    0x2480c01098840d541c0d803a000710805d20000545034546039a0010f001e10000b8000c1c0b10714003a4881d58050554546130a481e0380e10114420b500c0d110343e071802030704a034039000c2d00070000d43c80c0c11404024000303407140091414000030000c100c0c80b51081460001d50b1a100d94040800c409035a851140d030b0ba80582c2c019112544000300d090503c19000078040014ce540030070540140019944541c124500081c900003040c49000c004210b0707090385002080000e078800c41030101141d080d00c4a401e80c14104020803281c0e01c4c80e400c02821401444540c4800070403081c83c550440c1c800312607a036046035020a072108144211820000050080d54052240c0f00c5002080c6400400300000c07141c43c900308100040455006440910000c3d84440d2440030071344e4402c0140a041c43d08074001c1240e11905503200640181d60f8016101c803418040750300080490764409440300701d890008241d296403806015020a6101c1e01039280b0a810034180310740c41d2000801d200d8500308942d00148016400c68005464404030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 356135107 1250 356133857 356133881
    0xf21070f02090903030609070c02060702101707050a0210060506030109050603031b060105091510110102040503030d0b0102060c030c04061407052d03180d020105121e0112080904 78
    0x14030592480141ca810988a114402d0319000e9900da040000401c40850f0010700380c90200b00c0504805005039031500111452240d048590001040024000b0303619084002400241403403174004104070203070400c1c020301408503254261200c410a00003c40c0450b441e80c02800d4211005000500003140300794130950b00644010200ca0034400043d80240100c1101000040e1942206c4010440c0307060040785c041e0401036030035a40c42d0b001022804281041c1d03245e90080100417405d03d12000c6c1c1c1c1d6081d81101c0241c2005015070b0313600c0c15442c1c1c500c005440011204ea00520403080054484880d81060f0380c0990341c980070041c80d183c0b50074004c03242c0c06410100d480070100c041240300b0001d4003c006540e40e2000030005198100341c0070b00e00502e00c106221100326103820402914a010305011481891504108c41c0a1010042c0d0f0004071038900400c0c2000140b40a040c1c248120011544e02180f0301c10a1144640a00d03030701ca081c07a41e0548243c01005101c100c1c280010320480c50150061602c0b018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 356136357 1250 356135107 356135123
    0x5060906071b030510050402030d080a1b020106030c171c090b0408100e01050702250e0f0a0510211505010605040305010e1b0d080c01060b03090f2107 66
    0x802d88032103054000080e080e21144000c00400c00404c0000d11100040e6900841c00700403a00e080d0300800d07226201407020b6000c101c01c1c00005403040400b036102c0b0010303000c4846064155003d0410103402845a8041502d000410325000180c04a240d0003503100d0584860107080d2040c014006072440c001c58814000900c0300c541e401044c010141005000100802d100501d41d40e0486a000710440d10710881c12169030741000100840b5580001c0e19800700001e6041000500e0190030042044184580220300c0d40352800e004e0054030681c520b20b03103025503044481041f541c0c0751302c0043c0000c0d44542c480d40d01c059898007401405c01d01620120200d01d8002c0010a4271803045000300ca040700c2090300100c002c01e01c081024010700100340302da081c8541d44c1e6002003502d60507550b0740c03002071450785405600c160240f0030b041c0c01b0040043c0c19a809140048020f011250301d4100070700d81034004540003080c40c46181a030129002c000159980e4a6030614035500101d1001600d0f4042c0c0da101c4442a15403030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 356137607 1250 356136357 356136367
    0x1150b13090218010e031219021507081006080609010e07020f0a05010507090906050604122301061401170703111213110a0303171e0906010801060b0f030105060906 72
    0x51070b00081442d89803403691620160030441c0003501c40038000900d503019900c00d1260f07102030701c480780c2110f03104040c0c6038100c0c1020305104c03402c07440d02c080400d01c0071a5400200074030020581011460740a915800d0302c081000d502c0e104100e4249600b00c034620b40c0250204010404103407003607045a00b10300c10f4815a031094101100d81407428442d400c2c221190380d034900c100060a548280c1800241110150900520789010001a42c50245002e041e402c68180d844031820848210000c69600da00002e44201c07000744800614000c1546115103041c034212500b01050542c410b0f4441894420f01202d540c0c125290010118010039107064500481c4508000d0317001001e90504030544134400d02480e1400e0018907141403040b036120b0381308050180100160a100081e0003d20400350001808075a0500b50781e4192036101c240500a05940101607600038080c540d80045191410b03145444000e100f0142e03030b2102c05205110381d0b80c402c3c03a400010b00040c000c619100c4000d10103018000c01c000c2c208 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 356138857 1250 356137607 356137619
    0x30a0207031b2d050a140a020a0902040e0604050402031c050906120a1503030f0309030c0204021c141302010c1703090d0908030a0804081308030c010c1101150b13 71
    0xc030b0803110207641205858600c8949100d0501e402000346a1400d00301c20b40c4840c0c0d5444564540b80b45400a04e02600041191501e000410406400c20b400034801410b03c5d59030302c0144000d500c00c0c0a5084403544140020b03090b41400e010725800703594042c0003080108610f448480148820540e10010003004000360241030f40c030300000d0808480c141500c03980300d0030105190b404031076103192024030a100c000c8081000c08d4010308494a801500d0502142c12205071030119510801c60301c0003540a440810304034141d04422514042c510b580c41c804200f00c1c90680c0c800c81c40c200d003c0301d41d42103009218030400d00551040701d0705c02d02103101d080301e1480c1d100102010141600110b030788108a03800300302003020107a8044411002040204051403812080e031000400560b80180050710b01580054403007040b54114042c20028119042a00d844024507180103021304a080326100c001103054000f08034411062140142680d1100091215103140c014021302c181c0122805511480c0403410000700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 356140107 1250 356138857 356138897
    0x70b0309010212090a0b0c0a02010612030309111504050609010c020d030e100302040b19020a02040f0f0608061012030c0c0b0d0e06280f110c07120503030a020703 71
    0x30341618030000d41c071a21004003a0800c444001c0c5240160b61000280703001182e807a814003070300b201100c142c0700d981d0040400c0c164090320140d40301100884941e0941c03400d0607410350107681c445204140000d00c0d02200c10800c00420340c0760019841e401020003042149140c25801054400c80604015901c0d080940010381c3d18030000000743d02050304101c0c001840c3c80c00300d10b80d0618030810f060450416047c05000483d6000f80c04030300500418000500041d14000c01181400f10b50080091001f229986400d0020b08800300c80d10910600300b1901040c010b80c085802e85c86031035981140020207190048603180d24004060035414000640d121a003c2114a121600a0070305010080d6440e1025400c41085a80a90010301c581c0c000000748242c00d801424043d030307003403000350014802c1c0510000150081005041c1203019034548001c0000102c0b084000e0088041d80c3c0040d00c3c1146c0d038070f250068131907114a400038850b403c100001018407019030b001d000f40c0c40c000d01d05005884945201d00030303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 356141357 1250 356140107 356140111
    0xf060509010e0603010516170615071208010506040302010c08030402040b06030a09030e010923031204090902190308070303050c04030c0303050c010f1803081e0c0a021603030804080705070b03 84
    0x1010702c0008100450f6007000d02a8503003116000c6020003840343d01080092048011581240c08907110340046a01556511507658034040400d900710741c0c0700d0b01c52400b401d29003803411727008003ca110791000196501c0d007081038808403034060b110302c02d00c0d0000c4e59400c11b070381c1c0c0000c0c81243d00550340e07030101c522900d40401440c80780320441c400150b687d10307030f0030045c1c85605180e00d1281000f445110600001141c1c0900c008251036141036999988190000130b800c0a00b111404800781b072000c074001540c02c1594004601c824000e840c03500ea039404e143c695903c603c82c94000a005142c1c10400c00c0d000038800d91003035611507040084a41866140c0c2c0e90341203101c10325442900058800f080504034a0020300c2003001294421104006414951600d907003440501c68020f4140310316100004c42c142c004080c140074030325844c0d11851292504030f65150b0150400350b8504d0041c8100001c0a0140200000e40303415a901512000340c26030312075481031704507030008404980e60700611200051110781500518 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 356142607 1250 356141357 356141369
    0x1020a11120706091d060f0603040f290a111204080c0a08030f0f06240c1606090e0606090d080705060a0b0411041503020a0c0506090a0b060105090a090f06050901 71
    0x304c03a24549071500c0c00004040d40900304000d02d01082c004d407595507941c0c004241c0400d0340c185880c1c1d90b0300d040140004910041c05003000340a0364100001031011071013030509c21024807950100381c40d2441034a08483d4101030704843d01600b003004014031080485c18a50241c4118a5a8944140300c020103003445034074a0b00b03d86051002c0117100d1a0106040020350214001507086c04910b0494006140e5401440300c00b410840c401c240d0041540440b80ac8540042d4a101250604038560301200c00800a40c49031a0000303c074082e0110700d40c02c0311102d07540110402040181810701e03030010003041030f041c14401c49110358200045e0002810502c086403090301511070000e40f40302c084050100303480e60124401700007102044180420200000744d00c183d030f0254540141c50320401c500a0f01c12048441d006822842054200300d1410000520760300340a100313903140b41840e100c8400541d682d0188018503903200c802c80400b8062510550b100717034a6a045100045050b940c2c95000c04c00c0b00304203030016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 356143857 1250 356142607 356142617
    0x3020d150e01050f0603010b030a08031009060806090f0a050a031206080d030e0c010c03021203060f0307030b040203010f0e06041b090903020c040c0807080f04050a1e0b1501020a11120706 82
    0x1955030007080b0503c0c1c1c17011041d0001d0011000c4030001035154142404004c10180d004400309407007245c10700780d17140507000d13403101002400d0701d42d8071059450a0031140e4200900c5600d40c0300c03006c035501085502207168000c0092210200350f43e410796424140300403944141c0d50f100030002d09080100484460444261000900c0300c0b07010407094244000d01224a0600c03444070b0385507000943c00515040541c45074840162030340c640b0b00000e100e03403000c8020107505228031400801480114000140100d01c214001c002d008114880d00042c1c1d211300d8400c02c1103401c2180020042000c0700d29401c0402c800c541403615140d100e40e20101194094141540140c1c4120f1116015060074807580d00f000059090443c0700d4900031a00405580300140f206c4074190500e03021400700325081001c0040164000c0325080d120721101e8040c2603407545150191484404080820680e00110394990100c0106030301a1502007140d446807220500b9104606070884a1042e80a004100070b201a0018015903039030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 356145107 1250 356143857 356143861
    0x103020d06060e0f03060108030d02090f0a180608010902010804120c06110d1401050f060a051629010e07030c11070f0612060617070201200307090e0c0403020d150e0105 74
    0x90040d90130004451500913400b800c01844180c0c0000207031942c002200e80d01680da81110404504041c80340c044080d08903290f14404213480040d01c00902a810703c0741010082644e454a1403070036a144840d010380452500d0010a000c65010030101c1a0394109040921042030950b8510003201d411079074800e658035000c901810f441382ea5000f50018141e0740301c0c10f010720b035040c07100050f500d011510b401446104000b52181c01c490280c5c0c2519698003107820320720050030450601c2041c40c0c88000030107002c448e0b020300c0181a0141058407a059400c5610204171503901d01106070028000d000207407082c40702c8180c03079003481801008603d020304000c01d1045400340c6402c00241601d2505620811030b242410010310071580e12111400318010343c81c0112005481c1c00304140d005002c41c06604275150041000c0c1c2000c0200d40006500400c011383d9034103a030b50307a1051085840748080c1e8402d14048030070401080980350805036581c0c5180110941c1c2c0c203084080440a0840b011056051016511042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 356146357 1250 356145107 356145109
    0x103060507020d020304031a06010c06060e011a07050c13020408032205030a050d0302030a0b042a090609122d03020d05070302030307030c1b0f11010912110103020d06060e 75
    0x8149040f4404038002107003080e00b10b40d1152950340449401c1a542c0440c000000e015030b04c9181d1013241c09400890806c000c9807141c404a0265009009190304405218810180941441c04459490342c0000c050f2616888034010054041480654061495000d11011444040900040c240c1012489038a00451000c3c95080708950655122500c250041e40c2a030010071404981381026498502d070040c2c0e25a00c1c0c0b40200000d010300802030b50040d01c0d2140b0a45080042d80b00c042c0b9031003c00101410300c02860308101d404c0310300c902541300001e020180802c40e40340c01d0200c0e104814401c0001688101000d852404900351880c0440c10341402e4a18510502d501446420f030300d65410301d0158604021928040c0d50782c40090010344c10507503075056030b50343c1c03903c5040705042d5402e04040d10742d02c03000d1720700303125408dc010000156500c042c07902d80032115600070200e050888081d1000459002d209407112000303551070000044c107158007005512145c00051142401501090b244c0d0240001a54 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 356147607 1250 356146357 356146363
    0x30406120e010c05030703020a1b030f08090304180b0402091c060c05042601110d0e10090c030b0702100204030c080607030b0609040b0303040302060705010c080c0406080f041a010306050702 83
    0x241c41c952035034500445900403550250807a0740c0000c0c181000742c2d80d02c0c500743e01103c80b001001804003581e07000180c5401016072110580c9242c00700e96580d0441d98903001c3c50103850f80b080d8803c540001036240c07011900464a0b422a06003104014401802c00d286200403a404e41101c070940305007802e030380c00c9880400c440c512410147d400070307160040c2824140072451510400152100020b543c0e20550301d080804250080c0141346110500c0d16201d185401b0380030050701c05829461014007980c1c80000c1e050f0010b110701841c0907000345403003505074550b441e041080b540c0a03000030214028000072128151403400204025841021500c0c40b691516142c0742c105800074001a04141c1040004007080d0b03a001c050713604503c000c036000216251040002032840c8a00d610080d08100007040c4c00301070207810b5011030111062a280c03e4210b682d00401204a84210b01450001c20a10404180c220850706022a4401c1c414503100008140709000814821001d034012196246c80704200207071541d040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 356148857 1250 356147607 356147621
    0x3070c0c06080f011403030d0f02090a05040506030d03020a05040b07050a060c030902131d011415010801060c080307050f070f020f0d0b0429040303050402091b120a0e03040612 77
    0x140c505102d09081c422102c900340c080c18421925004174140401c281039030705000301c85220b441c84034204810705148506802940000d008075203d046a4200003c1d5800c0c40d0040d00d104804c0280607140b05046947d080c0e0003500880140c008003c421300c0042401c4054a0082c80c80b50301540003815404410f1410505880306100408101406d00000700f0050300c0301000c2c1c800c0c054105c18040b4020300d122144000459011048884070360030510701103440c0c040c0e1509180115500222803050304a01401500c0c040028441c0301d00042d0081c4000f0041000303e8081c54101026180c41444d083d80c91401301d80c65000442d00359500c81227003c680f01145411201e00700108000e40d0701c0041d004103603c0d15942d800c8000c0028002001e0740300c81107048100041409454484005441124185814010003c3c0400c0310102c0c060030341c00001c036a06800a04c1815614806851250b182c4039858041c41c0c0c9900011b084000216107581300c1140c00340b0140060006481ca0345d4481d1420682e001c07011041d1421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 356150107 1250 356148857 356148869
    0x80d1104060503040f0201020f0d030b0405010501112a0a1715100504090609060219030609091e0309030203010e1501050402090603010b13030204020301170606010f0e12030c010203070c0c 82
    0x1040008101e81d41c2c100341070300d41c80390700480072121404003800140e0404140c45030040705409074805070480107401d54420001078006941c10801d42c1c1e01d82c001507940e44c0005044a519502800d0001c115812203004110040013141c04540181d40f8034010940014807a04840c0005030b044d00000c0303000302c0810103088011405a5408020304150180c0c02c0440c0103070181034042d9855a0405040c8034003034010400540c0c1c007120455513281150424410000b044030321070006800e1440000f0540340c036010b4010002e1704115800190840402020195004250210300f07124441c3c50003c05a40c0a2260b1605104401e024081c4042444802c100640d4140c20880c4928814410114903845100589056401d0000c03496601c51950644480c803051680c40298040d00010002c650b60030080f8240501d01440012a201c91301c4660056640c980c11002c0c280000b914800303400740e103140186550703031620b2800d41030f2031918680d120002d0980e40215180340200d030b203c03500b000070810b00882c0800107102c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 356151357 1250 356150107 356150141
    0xf0405010e031c05130c1a09120f152203020c1009050117010b071e140c0f01030b0d12031e15051002070e04030323010f05060403020109150903050604080d 68
    0x10540c1c0b00c070362084130f600961034000640604004407080c2c050440b40070000c020000c201b140700203220359607a02c404000c811110300030314020500107a00c920041d8014140074033030110340b520b0500d41040b0608261405e5046204079400c18207aa15076062402900b4815a41d10007014140700000d01001107251550b1241d040f8030004100400488055486660380b0103050846000c60101c4224010070000c0094404042d40240c11800c04002031410481c2105440240c1c164007213200540803900c005100c1034001c169280c000c00000c9c0c403001c079900d0307140c003d09000414414070060341c2216582d001461141c5035448044030800f40344412400000d0200711501080d04c040000b009464955912440d03510480f03100100703003010300a400060315030040d242682c50f0681c0c40101c100500400307105100c4c603d200180013045500b030003001c54080ea901a110b0000140ca0404c400c084580b01c15081000c00144000100016034184091401a40a01000b0b511a11410801c004070b450b1000f502e50200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 356152607 1250 356151357 356151391
    0x80a050c070b06040903090302060a0201061d040f0b0601090b1c0e120d0e2406040605010315181b080f0601020105040c0605030901110c0106080f0c090f0405010e031c05 74
    0x90041c00c5690f0701c80e6003501e0214032206030307140980c1d000c051a000290b003c1030105020b14001d038158800412241521410070b91036206050504c08800c0645000e00b4140c840f4903410081400c800c82d99800540c1071400b03003107450745c51203152400e42200c00315048094400b05620401c81040c00b404c2000340c0300c04c000d040c0104103030860440307038420f040d4401c0c40b803600e03203904000d0054144000d04003c0702c0104d2809050b602c8010075144510704480c03681c400c81c035000c00444c10394844c1c132a41c943e03404458010241103007409aa4216025526900200151140d01059003040c5000c81d02c10451690740324218141400518902e0542c1d0051140b81160324110070000030481d5401e41a080b103100782040c40d600d07240d100105015142da8641c5000c206000504401c40307040541c8100102d90104040d502101d040c044059160000ba00c00540d1264000340031036054100c54007495000b9214400000c2c41a108040840c127581141ea0705000c0c17107046002d250444007090044561060f05911069605 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 356153857 1250 356152607 356152613
    0x1050f0105041206020c0307060608061302060a050d0f06090c080a0b090c070623061003090b1f0e04051e0a02030604140a0606080d0f02070e161e080a050c07 69
    0x90082c1d110716403d40311405a0001808020b03412686040303500000c0da607403074185050600140c001ca00c1060468132540001a03119104503e80c0740503180d0040865181c10b80a503070407100b903000141402c0b69207a903800034002242480c86000001c02c00a4800310f600340301ca14001d400510014800d207860b5003040005030007661000c80d520b1340f180d030315400191209040d003040c1c2c0081c00d1850040004c4160380002110b07000040d940b0b41c0c81000222146050b00d462100c0c02c8041c0c1c1c014036801040e40b010741000c52035034055032807802040000300300248001c96031401c0d0000342034030903902034849400000c901ca03070b00000b468607916645202802417042e61041d0303000c280c0e100d1008002400c521148079160403030041c1440f13144c01c0c0903004441031000c60b4071242408d80740d00c084041c1c60042084403400b001c0305400492410102c5443c01a800c0c01590b0f004c5a6082c00640940102d08104100003200100f0105a02c2207a41038031030b40d16081d9601c0c0a4148904a8001070910300c88808140464000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 356155107 1250 356153857 356153867
    0x140108090d030c0c0b040f0c0b07030909050c071712010906181d070e01080f19080904020f0a05091002070b040311060417030a1704080a11070503010f1401050f01 71
    0x42041d070300d00042c0b000c81c0f000c0111071014800000403d200368100038082030207040c2ca10702c80354030701810300711020a5581c1492000e52045071300007008503074401c0d4100a021040d901059015590380c4a0520b03001081d80c1d0090750103880b5000499150b80481d01d80640002c6865040c0035058a031410806141014441c482058004124041890320b5502608d201c41180e40c0c110b013484c191800b2200c0113038980c016440e41304024002c000b624804d401d40059403540001c0c00d50308104d048100c1c5400500c580c0c81c3d00703645600c18901c0681140c1c0802ca440c2e04001d000c801071612844981e43d141c0c4580d400c0080081000c02850300400315032165805001c0c107090682103078102c0354803030f02401d5a01e0303104002c640c06004a40c07041504018054030501c145001100521090700c2d103a4841c040c2402440354071003812425100940004000e21a00120f54040e0072a001b5414490017190380d01e550300c500003420340b0040002040080e0700c4803c210701d0316900b000440c1c0503000445038500e11582000000740b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 356156357 1250 356155107 356155123
    0x50d08010b041a131a0c011503080a1d060d140a1505100201110309030702130216030302030c12180d05090303030a020a051201060305040c06020d0c02061312050714010809 75
    0x50383c0c0a0014590380d0403a480700c18040184000a2401c0074104038507080d4005800800c0318000035402c1001c511000b480d0008520203480d4411410350520008401c02c5403000802c00003040e01c0480c040882ca03155407042d02510480481c030b000420800c01d040d8000c01e9524004d000d0004c1c46080429502d0b000c1c00108450080c0d400c1503d0031010984e038094200d01415900e5003000b040000002805190b107000320003020850300a5034070640032004001c110f81244182ca40b048166101c0d801e2200009219800564010260301c0500d400c0071b0191481089a101c1955071030071207807042c0140c00300600b0902c41181100e510341807460400306c0032000700b03481c1d1000a05608999a0018043c003029004600b50340b040480c400c00f50b1403560311101e01400601040e541590303000f03801880021010300c0040e044004a403a59140000c6000e1907003030240d15042400c504031006119100440e4200101c101801039500440c020595070b481c0c0161000c0003410319030b1060400614070b0030807811803400500b00c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 356157607 1250 356156357 356156399
    0x50c01110c01090e1003060207110f0d12050a0507050625261806070f1706032104150203090a05090105180712060810060902030105011b0602070f050d08010b04 70
    0x1207259580c005c0240107412075a0401054180f01040342400e1092400d03490494400031380369043c401580c0c008116008003450f0005001030940c110380271003280f0800c081c28208a0038204241003001d2070b80d07903900305902120f15001a4400f04281c006849035440a140b0b40d49250900da55048480866001020425031460a000e02c083c008688882c00c800c6a103020307000603205694490030013020050080d00d00c0484940011400128a003903064040300c0c00b8051000180104140c00e050004044a440c4081c80d15032540000d00000820301465100340140000381d82c0a1039481a8660402141d0610f5400090090701a00014001d076100d100d450f00860448200d10314007079a5412048512101c1340041a91190030071900041c030381400180000b0320301022100b4010941c8a045050407400240314860000307144802001001e031000d04441c003028011203000d460b114490f141c8607600c40345c45208450342d51054001404059006a50901500b0658034852805181483c02c120303d8071151554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 356158857 1250 356157607 356157629
    0x3020114060d060b1c0b0702061e06040b12010615080115090618080a231528060609170706080a0e160803040602070605090604090b1903050c01110c0109 67
    0x43c13102c0b41d5400000c400505405140440075000500c1d040c0d0481d44282d8412016110b041c01140e6400407400c0540003140003d80b0a500c0caa8901c41044003502d6075807041d641100202029400420080c01500c019207a10251500d280400c143c00410907101644100e844034071004144181070f5010604504441c40c0f03103449542c005104e00c80c00c000e101640e00c207034003d206501c0795208104000000e50519681e2190700d41c0503425200600345c442d1030130303034800c0300718a0f0f400d000078040c01d0540503a0b0030600607001d01400c0c0a0802001c141103070415082000403403000c420070030400c6443c40d19031407280d8851024054982c60f041d030103010715801600345000641c44030210140c5100411400c01c81104030100241d0711543c071030b40c1d01e03125842400341000501441c0c00206e500c502410403901c2001002e0043c0f403806180c80913204c01899500c10b825072009445a0100a0703002049144000d10f01940241024540e000005401400a076036240c01a410011009000b60b80016482c011911251301d6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 356160107 1250 356158857 356158871
    0x60b070303020f270103050903070302060610020f030c07151409011409060d14090a020a030b041103120d05220b060103061805040c05010e1f030902060d0903020114060d06 75
    0x9020030601a00d981c2c04c1c3e070741040d0141105180c2408a1920781104281c030100b04079100d03a5032641e141d1003031031000b5000d039004001240050a1212483c0c030110324610540b51542083c030080e43c1154040031800c4015032120f00d080c01440051807000a1529141c2400149200014042140c40c01210607140c18003a008808004030412541100c1064400622542c0d550302e00c8070341200204200c50b02e03a026513007607000082c0c0d6100000f80c421000d03038000300310010041c039603503a04400c044018000c0b680801d40140f12122078608001c01903901075050002616035092185103012144000d04201c10041e598100c038004988801e01c01c0d00040e04101140141e540381d00058001e8940741d40070312040780400721035407000c0e41903034059802a40b041c031705074241c90783c1c2d9001120500200c0c03040c554000c0a40d503e14001c2805030b200650480182d04020640e40d045400251081c0c0022400c0041152a0010701080550a20071140c01c07980b07080000029007000e1003c240c0240c400e442c02014241c0d1904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 356161357 1250 356160107 356160127
    0xd090905070215010608070801091a0603150d2603010b030402060c0f0d090905150306060d030e03060a0207060b010206150d1b090b13050405030a03051f0605031504060b07030302 78
    0x9003103100424a254143d5503550f0300d00031701c1c00000f280c5080c005048000041290061400750840d01040485914500c449000403c00c0075071000d07251035a2003112009404403502c1343c01201c6c3c00305008044c4c0c0901d41d403591050854400c51405420b42a103420030051000c0d101003829a90003c0c4c040d200303661503010a0401e07524040951000b44200e00c00c600c04409050752101800f030980c2e805c10402d00c0240c5039035202040d564414680954150058130000707103541000b000b04420f2601031f141c03c618903002c0d0404a070808005554a400340e40e00042c4403020b02c44a4000c0500810081c40107010a01d080d0b05600d2410107014140d6100d0303070303d041e245814003104004041150031514000c18401d0b607102e6041c07005240700d00400d409041c81148040f000d00b036034491140701d035800001071840c1c404200d100b1001031400500207406021181e010030822850b4208413401b034000381e101c4d036641e82007480c0c0c02050300c6010b981f058800c0f0700340601408021207107010b4544460b40350501503204c40580e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 356162607 1250 356161357 356161363
    0x3121e030a02130b0a021621170703030b0406060f020d03051504020415020c1c020f0a12050105070201110705030f1612230c0a150f0905150106020d0909050702 70
    0x45100107030700c00ca40e03c04141c404034003000b0500c5013455000c6880c132540c0c08070314942036030b4070744541c103903161810645002c407080b55050802480d1180150250000b80707a031460b501c6801c44034050700041c0d61a6030640c050b06040c4240c2000d0001d5061503512809100c400965070041180841c00701500c81f008190040426215104601001003065440d5500d5010402c035804100c0001c0005220300ca4a0010300d082c0003004400c00a140b20410420140b039400b400780d43c80924102c0c0790880d008200005107400032240798211548038a001040e035003080c080080c01d440e404d42000030050010050840040c90010898046c0d2080e010215107031440540041120154078802034880c8210442c01c030506680481606501e0010130341d8840d011406140103052405240322590703841d442016078034003140b2800c01c0c000f803402d040e09001c610000d108100800b540c10407201212140d0142d90071075985100515181d014104c82d01c010a8124808103004007043c2c801d208a5044039514404102c0c0e081c030078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 356163857 1250 356162607 356162617
    0x12120e070b0c0d0825090308070f0b06100f0e03120408030a0206010b03010b040e0603120d060303031d0a031d0405040c150e060a140c06010e010503121e030a02 70
    0x144040e00c0c45250755126035101d540c09011040c82074000d80c601c41207101d01500889004070107001038118010f003000700c0110103c486070056000d03c5544440080013910030001840d14620030036002d50707903c40c0c500d001031000401400c07081c4901c40d803250417140e032130784942e648528050324541403403010501c4c400300e810044019003c0b15880c0000601044600e00000113120f4810240d0032140300340eaa801280b1000e00007030240910084003080204281d99042e00266004030000b03080e90b03001d4401030408541036001d01d40402e00030762204400c0081c150144a07082120400c01d0301d140d02441c2110155888804005005050104d48104024a18400410720079050405002000541040d0600c140d800c10f10384940310074007240040807290103100c5c40d581e12000030080e00c0300c0e04000d241d2006035411070b04080100281c1005004014106800704072050007001c108a00d14025410f0400b41030814558803a040000f000c20800783c5502c21700c0c1d2440e51392001007040d5203526502c5002e0903101900c55 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 356165107 1250 356163857 356163881
    0x305030601032c01020703020613020607031101020c010e28080702040c02100203070c120e010f03050a09020612090607170103030f14180108010f0b09060304110a0608040606121212 79
    0x5044180443d81c80154000c0100501a030200e030000e44e40c40c2072400200001013030083d044103007407092a001030300440c004198801c0d90000541012245250796084885800304e59509a00c04100344034041902841800015401c03640a403240a003912880c040307225010009004650310f26105030b1040c42401410340c902407025096603a400e000d8801460003154210690304014101529030625000d02d01c0500d02d9401a12a1241102102025001000c1c010301d4800310079159900140141d450a00030061425208260030103800c00440c1a031621000514980c00e200100360081035100e401c495007070440307070305203407100d00710045000445030811a0794202d4035180c00403a120758003e030748041490000c0ea083c3d8490056aaa454030107000c2e038190b20401032a00d00401005006017888401140d2050284162075600031b0350401040c00000141d0bc814009140ea10030710003040440d00032500280149042ca49204800e51110035055103681c4030441486034900c170320300740048543c00800345224 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 356166357 1250 356165107 356165171
    0x1a0d0b0607110f09070f08040c0b0f030f131e03020312010b031506090112090206120c0309010f0606090b030a0902270c07050d0c0305130b0a1b030503060103 69
    0x180a10340348210710003200c02c0d180728002100f010b03112070403d4940c842c816900c3d6074903000040c52003001606c81c0b84c0c003c0c200355503200003034001060101e00a00104180c01d40c0501281d9070b40b41c010260b024420340540801b03020003a02c0281404140e11203e03d540512000c1c820000100071483d059245120b42003d580305100d00c2c10002481c1d80d003c00c0694820170043d000414032840c4c601c10080c09100e8481e4042c0482d056812182c00340c15190b008420036031020b00704519115500911081800707003100c6c03a214800e0000200103503000e081c040e41c1c110300648002405071504148001c2c151001078058140c42800100c00244148215003003045100c1d0090140c0b4504010300843d001c4c101403131b400003444446140040f400c1d040ea000100e4450b9904a000303003040c0300003904101c50205d520341c1c00f0780820805021035035282c0760001d6014010320030405039540d41c0000b00c80c003034070f01b2217210000e44044000c100c403000460381180841e43d1125091800190390708521641e80030308248216080300040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 356167607 1250 356166357 356166367
    0x70302061803010501170d0e0108010902160204020f03041202030307050d2f091503091902030a050d0c0b0609070906030c02010908191803050304030f020d05012406091a0d0b06 77
    0x1145001400c945a01b0038815910b200082c80c0d4190b65072034132440c1880c0054802c000402544440e40c1c003400700c1000c4000c04810340b50103500000c080e41c100440210460800009000410030f51458440b0845c2c0c050014500310710341300101418900580f803030740308420b8444101e0f40781904103841e01c905801c90031a0b50300c0d42c0806e43e00c61204070740020000900600e801405080ca4020070300a881c89444404003c00826185030184e880074407081004980620850104000280040c001400c40c3d06142d501c09000060324145202d146001601c00c1d40121441011b100585034042c4440c42034a45505001c2010300d100706c0c08a005141e0204c01074103450300403e0440d20f00001540c0e114150026a84814041d084161405030514240c40001d04a50040100300000b074000701e0080d500c24001010102d907410107444103800e4480904001024042101c141040b041480a0003005070502d0f14290040608100401b1202c441c02c186803841c02002041c47e040405207030b008a120b4010140071142c0f0b130 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 356168857 1250 356167607 356167619
    0x209040f14010609050c090a170c06031e07030e06070f05040b0705060907050a0b040e0c0403080406030f1a010c0f02190611071d0712060306050112051e070302061803010501 76
    0xc0a2134000c0e01491070038035020500c400000d5058030b2103031600400e210015450245505500842c1b40c00d00c01d010b002c0c03060404900d03035030107010703610500d4040c0560305013114421521036a008020184001d040ca0004840c0c1c0400e000141584d00803010300b0724055401803400161010700131075020400d0080700080b8030341085004640c150089c108901110843c9448000b000840405402400c0b4440c20502040040350980c20200350421003c001e1246002d44039280c51401c2c1c0c0c01078010001094940c150851004d10350300c18070740d280e4101d28103d1140a1003100080000010040c040c000000c4418504150341c0c0388903103107094043d8100c0f1030711480d5803254040c1c000720000c01511814010010000344200342c2145200c00701415440031070140d1ba0302c034002c3c0d030904080c4010034903490760f40a0200c00200e41e4031501d400303041d00c0d009500c10b01c22245800c91500044004e14400e01c065103a80341e120040020f4030000382e80d8110343c9180c41d513044e01c469070242c80e880000b4541c5582003400002d02c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 356170107 1250 356168857 356168861
    0x4120c0510060501020609070509040318051e010e12100b180708090609010203040510020723010605120a0c05120f0a110a08030a0f12150f050910080a0209040f1401 72
    0x1150801c5c1c083c2c440c590780d400e13240c40d21205244502c607005145e0387c0000300040e100c2c3e182c0603c0c001040201080d00c94483d004100c604189007000808100000c049003030a68110485201c50030049900c0c10420040300308542d102c03909650414040d50700c0d41d141060f20756940d4560301040c021809d00c003107949007070180200b6025043d5514030301801010041044400180200c078070940e00f142c01080d042400c4240c12000b94803861058600d0398a03103000328044c42000e44105004000d04001003a090b09180800c841e07180b18100c0f02c2442c1e4001c07180a0002810b00544408480c01200d00034128100c501e0075030300f04010102c41240c01e02071040001c0800649204080c0024429500d03820a2a00c0341d40306580d0344551004500414050841c14950754403030305000e8200545540080752440da1800e40c000214907542058400d43c40c7c8071414007103420610320741f0344c2c40a094110004920b28002107180c803441da0b610080c4c0039000401c001824040c3c4481d5421185034450b01e860448010070b000240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 356171357 1250 356170107 356170109
    0x605070801060512040b0c0904020309011e140a020a1103070b01031707030c0b041415041e030818070314030d0c09060e04150503060c04031a010e04120c051006 70
    0x1011403616000030802a10031000c0d5142000403540d0002c8548035501c07404c40e1910000d0511a001d2001c006095058480e4005180601e15032000842d40d0303030100f80d4040340c0c2140c54400c4500546044d0303280018004104000f030f00b1200400780143d8035160303c0c00c100c54080301c11060143c10300c4000340d0901000200801c440c100c034021803083c0b050070700c5000c08500500c241c410140008000d01078a101280d4042a111b401074450300d080d2134100140611a81442580b41800d268482007008000a0104103601c01032001070300d051030f50804c0d41650300504400000350010450056010b0048a4680100100c00286401681041152030351018031030303995005c0341c4484882c0e402c00314800f049034028800c0009403041c50b140d0030449940841448000c1003c102e5504d4a14180c3d40e0024140c2c60621440c1d0040700440c607416550303807c41c1091b000034446840c0341030325070b11400d004105a040384503c0c42e8106602c031441c1c100001100d070040302c0c503480348035014002d0300458425800404465102e64 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 356172607 1250 356171357 356171371
    0x705071e06031406060309253b04050705150d0b040614120709090b04030f0809030301050f01050d2a0e15030618010303081e070c020108060f06070605 66
    0x828098580004409a4100c40c0f01000080c6880020030301c0e41c0340ca200038645c8100c00360100c8102002e140001a018080910b40e582c3d000c8001c0414445100610400300110303241a14a9072560380400c02118106050314409214030700340c0c0007003400c00c902800104000c0c01e00a06900010115041d035000c1a4061000454003030300d4007070f03803403079030b0a16024000403a8034058040d66212010824881e07101100d0190f01c1c0c040c01070b46404241e003000b030b1040651160107140003000904e071500d005010351001c62a40014001e00c2d03c1044640040041128150344003500d41d14290007540c00107a646000303c0c440c07561680d00348250703070b1810a140c6a0503104040040c17002c41c0c221004c1c150a032074110312a041da641244803012100300541225005641220000d0714440c00007811040b0046040da081c0c00490000b07045e00305000c94007000c2e001254401b5452082141c0c1410710074405003001c0c2e0724800c000c0c180524080025450707070300c501142c140814081c2142c0d65880f044d10b0501c00070700c4216000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 356173857 1250 356172607 356172659
    0x1621021804230412110304031a180d200f0a051c0203030c13030c0603091b1d07180b0424320f070203010b0f0d0611070507 54
    0x1001504200e01c02c001044100d1940400a0348440d00c0d0b101a1020360800c207018891081880c068000d001c00051005500948002c100300791400c50903503500d038002c2c181c0c69004d951140e2013560000045000780419000f400c040f041c5101030380340031495551040c03081d11280101b2550340100c44022440c12115482403080da00d05580d594414190240f0400322880140d0080c40000c0301c05043c10014041140303412030004c051642e990300e45801d03605c260041e10009131120300e030204120148004d507200700004d1840d15455420488810135207440e0030381d6140a4041e880118150368018184c441401ca070007501c900c502500e03018119800c0e88507100e80c51140900400c05800d520f0055111051f480c0d8599038411074040f04100d03900049008841402d010220f21184006411620000e005d401e00100d2003980b6040240105400c407070351715803164000c1e151040845415915040b10041050b40050001407800060040c0407260103844c0004090340700c0d014000c142e102e566a882c1c070401007040c680b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 356175107 1250 356173857 356173871
    0xe180702160b130b070204090611070b1b070b04020103150807080f06060604050d030504050618100c02010e010f09082b0201060501020a1119090c020f01051621021804 73
    0x50a40c10320914000010540a03500d050080c41c4c1110003c0401a00003440403443c045d242d240c8108469008501c0300c0750306030000310a010440010100c5910500c420a00c0400140c594044042881074281c001c241501507400a821a8040c0d0701604210400b0000202d406454481c91941e0b4000c5002d161504d116210481040303140010700c0f03c2c49940e004c2d000a003014a002d0130700c582490200001c40c144582844041000d40702c84028085200004d905071020f60414010701001d03000c16054482049400c000d8000540d81000c60060074140a2902c2c5140100740e800454103c0140c0c0c00200242c0206000740a6442c24002c1003213004803c02100601030301465001e03801c803242031280d5030150708010b411201181410b01a0714040d00e000d040b01091404528007014021084d0300040c12155584902c203038229410405210700b10440d0000b00010b083c6405c2d14012000d03444028000c0128220817003031580c8041e000084000d445080c15519110360004291a00d40d4100f140ca01941c40d00c2d01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 356176357 1250 356175107 356175119
    0x30828091707031703070903050d020a1505090a1b0e16080711060f0a06090c0c061503080904020c0a150903180302090f09030c030c070f0b0f04060e18070216 69
    0x24888003200d034400d084204c0009140702440840c4c000a080005000c02c04200002240d23051218942c0003503203a01401d4096054909821024008821481d48900e4001045801c140000c1c03050b06503900b003117805580364181c1341e0249070803000d900000c4102e1900c0d01801885107c04548504110385911003d00f00d503545070f07080701c140122080e00320b419480307000815225051486e0650f04104600780c041251501e500141c000d40386a1108000002c8450064a0a11200348150440800000b020401081c5103858903942405000c03a2184541c2c0d0002e10191500020082c4150540c1d1045142b441c2d1305c24603130323040001c100d08002500851380c005680c0759041002d10341c0d02c00762680104903c09540b0f5507070811259002c010500e003001d2100b08840994082c081011f88001010035008100d050f04203490004545c030b440d0b00502c2213900c01d001ea26500d04002d81a201900c41c585031840c11611214000307403034000b00c08900701141806d00e06020301d6a81c04103c00c207410200c050686034403a6940 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 356177607 1250 356176357 356176363
    0x9080d0c0c0c1403030307080a06050904050f060c0910110a0c031a01080105010501050f070f02030304080106170a0809090c040b030114030c0108060a14120f0d14130308280917 77
    0x406650617003080001480d4180180b00742500901050380000b07840ea01ca0000c03907004207003075409841c140d1090134041c000c04c804012031a480003500079043c0c20701040101043c1c0c41605201d1302c1c4184042e40d000c10079203a02c200301c401c10f02500b060488104903542e00b0440070203020040840c110302c0c4801c00105508a050044904840069603030341e2030100c140c2c009820700e400c500c900b120700b09000100384015903004c00280014040350742c00080e01524060000306041040f000280f856000500000e000c02e0a103000d403481e144060fa10072150382d0300c000707240d040d911860300301419070140400046000307180641e60160303000050b011101c40c9800b0300010354516400b1240d81d68002c7c0c0002c814003045019003507c0c00b071114058103240c0703000000515682422a03a486210300c1d0391156543e0071a50780c0c0400d490403c00004e46280f85461142c1c0010203284003d80009014101c2c0050301400c245d05041c0c0c9884501d44000201510300c41444005000c4141c0d8400c980f0304050300304036010040408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 356178857 1250 356177607 356177639
    0x2209150603050c120102130e0702190b01290a0518010219020402092202070c0b0703080a110702040c0807120b220b030a1127070309080d0c0c0c 63
    0x30000805008180700200b01c200c4c4a07100b4884850b54003032000401c035000e44a13010020740102d0704000310510380030000920700b01461200101c01381c2081c0f0394102040750310f019a41500c0031343c0c101c075440d20b01540c0c40304203c9902d51070071850410001003400d103040d0300102602d212141ca003494998444c246004981d541c02d85d16460b00d42401d119900c0380185410b50080010000c00750008a103c0d0142c1400d24121958110940300d0540000e400410848080020000380c003511002c0b600345200743d10014080c050080c80c1000307440e0340c0c104003500301110606a48100741c1c000d10a001d400381045008100c0002511c1c26404207500b150700445001090240b80501440078240700104ca0305806c5a503000041242e0782c9010654804480006443c14444e070b030364450050441060b6902c0f41c1090106050b41402824180078840b80d008020b001402c8c8208c0d0048064980410b0044040c106a1401c3c13040c160b550b480e251800760b00c040c5a5411071460a4090301a144e003028082d0368862401e803d40003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356180107 1250 356178857 356178863
    0xc1a0609160e0402130513110f0702010c0212150703021c05060f0405010806010612020a0f1d0a090f06051806090a1415031006050a060e2209150603 65
    0x800001d459501000200500d6003694079010359207941000c041400c0ba48240e803030401c0100105802d003c41e0a00181401004501c0d080802000078865400e2225000e2002c2400365964005412415603201d6010712003410b80041c49040d81d80140001166910351006c5000c000c4100c0701d001800846c000d2081e26480079490846caa0f556403103a410000514005104d580e0000d0140400e54594866210f010301a1040700e0003020154101070001d0404400202c02d0340816004000310004190f102c1640d02c0c3c3c43c0c5450070000310030a042c200000c00b0101708546250403c241400006e007520341900704202001850303008005243d1a8424407050704500210420710300030b200081180c03410b00c59185988580442000a120300b071500c2c5c00200c100c801d4940c0c60040d00c0c100e407160704034a0280a0b0310002d0078042c00410600c2d14103008900d103042e1070b10600c4140201e0118120080e207404004101002070310212116003040c1c1703d030150051295101c11f4502991b400d038248880c7c101b500c10002030300d030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356181357 1250 356180107 356180119
    0x103051311061b2413080909040602090405090c0a0506040305060720010c0302040e060906180a0207140703110613090513081c0e0106030807080a05090901060c1a06 72
    0x1040621041c1c0d4000082601d14240381a20801e0120f024421000d0012001c454010364848280e8400038440c4042d002110700d18204100748009140d0001703c80150806513041149030f0380d43e090660007030062000098000e41443c0c1005204c0b84045489513080c5400c031082c00d40c0d0307034449060090a0060b804000c1c103e600030b1000c100321900807002e1030071208400150003010810300c0941d80c02c1d0f0340180c1030040171940220302444002441048141d1028042c0d50000b000c0c9818000a000c01d010300e00b2211f181480c11000c68284106a0111080107802042e0b01c80d071141c441d8403d40d40c802681c4402c0ea020f00d50a03600c2c010603e400c4003225040f91a02102900450500400c04018031000d4514203103210f00d000705c80000f0b600e5002070001c03c161030280c4058220031290700710907550751091342e080b2a49845002e00004600c0c03c02d07170384400c2d00044069111300142c1c0c0c01342d407144620407102d5030050700d41c800003c0003944001ca13400780601ca0b1038841d041c2d2200b580c0c4102d015000380c8403d54001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356182607 1250 356181357 356181383
    0x14061903031b0203010e0a0303060e160215060112141902070507060e03071508090c0a210215030c0318010219080403030f1113080307050a15090b1501030513 69
    0x101d2621100b040c0314001000000d40580c8185003a19002402e0000c50200303072149000c220740340310281010340c4200b011061140b500c00901009449540016004e1540c0302d070b01c0b0100d00103074815500c09564100302281080313001ca000c50fa00c2c000000807640040c2030790f140f45040c401d0034500e0094031089030b80080248000d40c104075003980e4621025009a415205a0303a0000724088081042c0c01050342d29107426400b420503185803814560306c04400760080d401402c0411071030810100140020488107041c14640034548002400808203212010500e031001c000d02a0010b0400001c50054840400b0405101d4841d240d090a0780140303024200c0008582402c2c840417802000025480707442844d001846100908501c000c0b076860f94069102e8160100711032402d1010034a400c000f0700511001181045060760f902d503074030340d030701c40d00200345140103d245101265140c002c00f20190b401400400c81c0c0c50124212030814484100081c000781c285400320b044900745101da0801c60360040c20030b0b002d80c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356183857 1250 356182607 356182637
    0xc030706091203050c0d0809061003020a0b0d020702030a030f1209111309020406030b01060f0203032a0c0a050303071403190513021905010216060905130e011406190303 74
    0x451011405a0604c1003c00001c400c1510034088152900c03015140c110746030410b21030340d03841e200005000359500711200c4018800741e9292606202213644030810940d40710f81e0034220201900520300000e415100e41d55000382010340003580501200c3ca103a42c1c12840281c03460402c402d80d205d461014164050150002c040e6051400e48103030280d4800001245d64940c0394042001c9a071142d20545040c03010308014410740c0e620040300c0f042e0207014801181141803104000990f0b20071048245d0110003600d40080150007840c06941c1078030000410fa94005560382411350b1680c0c4200e0b0300200041d07000ca580f09440c550401a2800703088400c442202c007403201d1401d4001000081e01c42d070202d8048044c080010b81c1c0e00f40d15095081450540d4410452a09002a1406074000440c0c1042c2c4800c40b0305010050340580034004680080360b60034200308100f42c8001c0100786046200e2110350030910320140b802007101401e40141d4050b0742a0b03442d602c820070322031400541e500000b000202c00c42019881 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356185107 1250 356183857 356183879
    0x1905030307170c0f0a090b07200301020f04090b2404090b0109080a0201200d020106140621040c0b04060309020a06180603050a1112070305060102010b09180705040609020c0c03070609 80
    0x3810760422070955a03e5691f01d14641e000304104071500405100c0720000c07802d02c1d1b0040317080440103030029402c040c002c11106429000e10300801003465940d400000c15551401c401240d1203c0d40c0c0407000b0440481c0000101a5001d80682814641001c64481c0d07107500c1100020110350b400c8000e0480600c1d1507004583c181c09600c0c0d00251400c141d02e00200e0004140114000c2da040ca400020f145490000b41c00f2020326030407107032403003100c0c1030046501025902e21800066900b0702814071450307071546080c04a6001d9038018189505d004500030074615050381c040f00c80a0b0003258088039007030380d80100304c0d407440c0c0145501c1c000602d5020700b0822031b4040d420458100462510108019241c00c07003940054010241c0110400801d000b071060036034144c8911500301000784003c0c07020301425808510140c0c400390200400c9907440380354200300d807018042800234001c000d10502040e0350721070100000c0e40011550384642c0c0201400105039180c0015804111089601c0d10390803a49461a5581 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356186357 1250 356185107 356185117
    0x1b0906050c0a15020903150103020d141002370210090302010b030a05010c1d0f0f0f090103030807020f0601051f051e03011401020a02030c040c021905030307170c0f 72
    0x80325100b1a04180005071110703000c10708000e07030b403100140c44444030360802d403425000c0300004600318880030050001d41c5882010310a601d81024034502001d251f01041c42c0381c11000d1503e4981d103803000c5100028000219070b00030740c1e040499070745000351242801c200446c19243c2100405680a450405001003a640011014034003d000000b403600c3c0500200e81055880407080742c150350348070400074800b0703040078103010a02c0c030301e60100c1039447c03d9101181079124129101c07440340c10303002413240c8295140880a582e14001030000c038142e5941c0d240103440300300140c80c0c00d00540940c9000c40c00030040022070034100c400003080c492440f0740d0803010400b28202c070200d20f02000000c01406126001311822003c0840c8884c041e20341d41c2d0f00d0604c1c040e00d6140c4a120f880d0442d00409200300c0581d900184130100810f08440008400c07020000513490214078030300350440042c0380f22045040c0031001c005144204126129654041120348009042d0903007103c01d203c50040c01e00542e07401c4400700c000340c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356187607 1250 356186357 356186377
    0x1020d081806010f05041d0a0b0c04080a060c080c070c0b07020d050303090c1503190e070504090b060306010f08070b030c12040f0210050f120405011b0906031b090605 73
    0xc0c01e4940d800c0e00541820000d8100c01c60725a081034081140b03042c0343c85840e03501e40b01c60810300703041d01c2c0380c00b00162110b048503005040d81511030701203121300a080e41201d006042c200201c60000d550340c54200d000d01500742c0003002240c00c5c6800603a21540c81e000300c0d541c41e80e11507800d0741110308210043e41103800c0940181d8018030500422000204104011070184003c1310041c5101070000e8100301d5550318203255500446410700a000c100b4100452540e09002542800700b50001c101c0002c51508426038400c030ba0084c00c100441d000d100c484010740c0e00030b08040d82a10740070380c6c031200d01c4203c4c000507200d00e062540c400c0f00e08100c0c40d100400610340103580020f17803034070300300320031540c005030305804d50303040d00e90701501d100410440ca8242c415110700f0800c0e00f4800d0134064800700d10348407801400c2003500c4088648001030200035080d8400c152a18400703170244541984a01c00502d102c007a4080d40b000b00f0300c0d01c9103840010400b240150621000795468101103030401d241103c00340c0241c9680 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356188857 1250 356187607 356187631
    0x911040b0c011d07031b06050d230c1c050f01030f03020c210d030501080303011e0e130b01080a05100b1809011a0a230102070e0f01090c080601020d08 66
    0x21a1401c200111502d00794070000b001444245e003542007001c0d54021141003003c004042000c200050380d040010ba91041e800c02800060840c0784c5c14110192085145502d2109180074080150601d420300c05008268900410307801c41d210042c01c00e03800c0702c0301a21030303104c002240d800400c00654015a86d0344c03000e11a106840500b071610f0302003010388081981440000d12910f0016040c400100036681840c0b40c5890706000d207500d0724040b0f40d12032206029140701007111420706084800c0e0800c1d1140280044c0305400c9803844c1c03d40d04200041c1c400402162a000060000a040140000d4040e2045d801101400d110300d843c10f1036030001c011b454034140d0048024a581040b0081001c0c41034482c40401001241a40304141a10f07905000d009150740718894201090014103020f0307120720321426454031180c64410340c10700140c0c43d08030144d101c0c5100398609401c100d50040d190085904076904c0c02030034804a05442c4082d0382290b01120440c0c0182d1062040c41e8095119040f460303000b075404020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356190107 1250 356188857 356188871
    0x1171b0f0c0106050f0402070b0403050a090b040b070c05180a020d110307020a05190b06100e060409060e0703020403110f1c0609021801050a090b0a050d1b0911040b0c01 74
    0x1019140c1d00180181c1c41d0a9641e5103081003070b428003c41c2e110381000701701c42c110329100d50f40d40c1d22400c1c004082d1024082140200300203c00b9400f0300401c10140c8000c0d10b00c1910b955840c0809155640b08100c101c80c1106501c0c40007456040200d1003622400000c00c9a02c21682e071071074000002d40000001a00d02525101d52030604c6035180011400ae103001d9000e00032100c2c290505030306d410b9504d45ca4a50400d50311074414085031804203825000f1604a854040d01d1540d403500b2241040c0b0f4007800c80d0f10110006000924030800d502040484100080049441c0d44840b401d030f040f40194840901113820741c03420f54480d8948114510540c031360041030706131005142c01e00b612140c800e14808448039961110740c6815440c080c1602c003d03402c3d000c101c000f15507051002203030f6540803034851442100d482c0d07243c0444596421550304d02500340a0140c448604250804001c40440d02554601861000602240a0003d400b032070a101000f0142185094605002e64241e40e04c4585074003015561210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356191357 1250 356190107 356190127
    0x926120c0715050f090f0307081803120408010e0d0e0123160218040210110f1603060b04090305250c0306060509070c0b150f090406020301090b01171b 66
    0xc000e04280070810000200f510b04012404240078025100140a50000880d168031810020032200015407142050703455401c0076843c501002c20581c9600e51501807940b02d03d040320118405402140d000390000d01170000c41900c40ca031a92402e000d00c000284000307421030320f5540101d5140303030380114600700e80b42c034140419074082c410341100058645103d01038400501b5481c102400f07501602124245062604080e400112120314410038107050002407400b81d0200c800610250124100d09810384401c03241c81c0303200305400c0e8035500040350803030f141ca0358030322017030901d13100321208107030701d512980c2c5025240301a00c1802c8034442c9008000c49034841d14440002e195281d00001148078039000705527913082408221407000010580340c108036a030015070000c516030b82034060304900507404c001c9481010001207861001422030b01e68105503204e0501c020415543c5c0103504841e1504010445c040f04100112422500a0411550610b5100115110a450011301c2140f01ca6101c0014541040380c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356192607 1250 356191357 356191373
    0x1d0d2f03070e04210f030b0301020f09120a0b040b180c090c03090304081c030e2a0406030206030f160c051c0306080a030207031106040506270301020d0926120c07 71
    0x1c0c0c0344c01e002841072500f455010303030940194504a00214025400c1c0000c07000c12200a0280d1010203110f400d501c1c0741c104080505111030507541c1d400021803c2d152601c1c2c10048089007040e01c03031101c81e1400040c1800402c201040d41d14464100401c0c4400a458090281c220358101804220180c0420040020200000c000e2484000c55140100c920186240b0001d02142d0305d10150b0b0310700d900228003040486081a88010601c1c1d0300c103040b205081c5150000ca40207003003641000b9002030303000080c4401184e020300c00340c2c800c0d5882140034603000855101140e9084020400070b00c26444050380d03506400144000c208114400c0ca0b001481c180c0e211036261404082d1401078001d80c02c404070a0061014840d00c04030100820340c1d06c1c40c40d040c6040c0c00700d482c2d440b541c00201ca4802078449003c10b40381d1800090141550300500941d250300e140039510005005078007040340c9e10048445140c03107a03500076114408000610381c0560404443c2c0d450100200001080a955a03101308a008001604a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356193857 1250 356192607 356192663
    0xa1d0f0604140c01020a030507150504030507050708120d02030a150f060f030b13090c05040e0115150503040f0302070f0905092b1d0d2f03070e04 64
    0x900018152418903003095102c1d50000c842411103504000701807812070340c001454080c110b5040c45c04958444007400c1c03003040c54803481d001d004141c0c244014001415030080203440c40c02c3c0110191802550380f0240c4e10740c3c83d2564600041103820038011031001128650103554005040c0102180c2c87d403190000d110b5894140c1c2094000c0701c004d90040c01441e501113a5190350000c24201000103031080704c0086d002203400d545640100b42c5400024041100e00c0701500002c04003c0c1c8107011407500c13400c10601818280d0505050104011000610700c031241c4000c100d18801d98a481e4a1a02d41e078507004860500c000081d01580304400002407a040130001d01c0d001040700c40c2c40003e142c189150564101a40b12900c00d00e0f10751a103124522100f450b451104410103142825200c40581e81c1c80c1494103059540080d0784805002e10f035806100200401102e42460f055018135140f8040c10340c0d20101c3c4c460814241c240d40040428031850b210740d05a40c0d04140540e9403104035514aa070381040761050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356195107 1250 356193857 356193883
    0x30f06090c020d09060306050604122406051c1703060604081204030c0e04170306030f160608010e01030b04020409141b0316060815010c0503070c05090604020406080a1d 74
    0x40000003580c241e9028525a000e840580780902907c1d1030301000500500032406091442c50480541001b0040a40c852858550b4150f51030641701c0102145200242914410b07039000b030309503529004280304800440c1c41c1d4bc590218000384454901c104140158000801c07042e0007801c2004085140c1da000c20007513a00031000d40c0040e64490030342c689504060306503030203000498038a10030700c40050f817001101c181c03100901e61001e0320b942c2c0b9130000900e00032061700b0071012405206003401000f110140744205440307641d02e582c070303080e42c2c0c44200013900d900c244005013140d2145c2d400710b0018036040e04078078a201e0140816a05508c2004443d904214100a80840204020000350f10380e0500340901d24220140303074404650f25250900180c24100001e00200d8442d00c050005007861703004010140285070407034116078940c60f0074502004078010500030584101c120500240281c0b42a008440907101190759111040d00d9000d01080981074981240300380c8600000c0c10803040308100071074140680 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356196357 1250 356195107 356195113
    0x150b0702040c1103220f120c05222c0303040309150e01080612010e061008030f040510031b0c1523040c0b030c0301031e0b07030f06090c02 61
    0x8852040004448005026100b03000442c14462070441000c02503440640280715030440801016980d0f02c43c043c010f81003503400c05610000460402041082d007042c044c030420001d140355485408104040c1000c441a00c2c40d1300c0d140c5800390f03000959810101841e403040300c1602e013008040d1908003880b00c0030403014040341d202000304028164885900e200624a43c4107100d90400402c0006004072040300b50380f414042858081295a264148000000c000360740080144211411016031204420340d1000e2050038030110210b4044004001c540b0103030b840c0e014491804d45040c042c000342c0241c40c4281c00c01c0c1655100d024502c1c0240c4000c1445032017403661a00600b55032440c0007119980b40c0b20405900070325010303051b140502501070054091200345c011185958403881d180c241011b650300502c52415005c41808001e40b41100514140c03813261205403403c4070300039000c00700a6003104000d44110f0f208070114505a01951010030b1101d10500046101600c0e800443c0569091450702e0300140c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356197607 1250 356196357 356196367
    0x31308190c05150106091202011101090807260d0b040b0a090f270b090a0f030f0e190905090703020a0b0d0b1207030b0a0e0d0e0406060f140a03150b 65
    0x1c04203010540f0000c1091108014650610f4001481441d1500a4250140f042101c160a40e1b01501c50803400c405107400a2060340000d00d8100442e0b0407085040398900e180021424407004414000c410103640010b0841c10304100545a40140000301105074100f6654803030480c01e5200c1c0d081040252256140c0491000214103001e4100c4103c1c0e0040d440c50004004200d403101d004080701104035400c1640c0340380329268081c22500f4540031400003014140850114000c140c1c00c0301d601b1145e102d03103846001400c105402484500c0e4046481e4202044044006100150322644002d8000c5031807402c41d401540c03a0b50210300c0300c010f241c0040100410103d850102200c05002e5400d0510051f84c006001c44007120b4066034500c2c550000030b203250040d000050460680d036008812040144084803030074010640b011740740e078000358200f41c01a414003002144d800d020300c42c80c031443d40351781c0e8603c0001d45480814034400d42100000341c0030180c450704aa401a0000301c0080050250321038510358072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356198857 1250 356197607 356197613
    0xc020904060501031104090c0311151b01050a18121407050c09090c0d06020304030311071a0718062102031918020a06320c070812031308190c 62
    0x6020701e00092246040c047c0007000102030007002c40440c0d60080f4100203642111002601c21081c0c00e005003010000415a140780031038600900c0c0242c0c5c20310008100c00e03241c1540c84030039101e1f0030b4180f00500b040440300c50005001c3c0e603440508805030b4a00021801c01946a10f80030b5030040d4026255540914111401850280d0000340c200100900400350401c0c60741c0403031429103075074070b014002641c0400003a050500940103590400c90150071150b4a83e01c0b8034000d00d80340540c8103010602c00c01e200c0060300090003251814800705d43c41e40030b40c0e42c051410308116420a404031962041c1300c003640740f0948030180d500245014410b10581035032140b003400040400c0b240040e800f481d4080300600c50f040036071903100012054840500e8980039419080c8401c0754190040e90941d100540041c2c03044500e01c84c0e02002d84801c4050034280c41c1000c1c0e44200709a0756040459018018000400104e178007150011b1808000340d00c6603403d00c0c1030806212200c602400030302c07485d00205005c001e40e8410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356200107 1250 356198857 356198873
    0xc0114090c03070e07020a0b2a220f0b09060702030303040302010917180907020115030507170303090c1909140a24031103011e0e0f060c07120c02090406050103 70
    0x113007010511002c03051410344002995100c200101030b00140029001c20100c030600b8a00c000b103421360b000060a01401c00b05042d190b43c3c0804244034101c0c0d02000e8505041c0c030b0000400d01118520801c00f0103060400c4001c078130a07404000301c150302140130080070005807014000785115a020340c00010b41052507040000c40113404c5060b0a40c80401003015100d04158030740304101d000e0094800032a03c3d6290744040e4010084948503410f010a80c0500000704080094480141c6049841d0403e04a0b41c180009650780825510b0015a400444260700c20307044c800c20859405e0200712841400340d0341c6a100504540c4103003610258500c00c0c50401844403054094411155030708000640f0185041030311401005240c0002060a100c02042c01c505581c00d4128091032510802c10b402d40c100340d0b00000005003500d5003521007500032810712003211107000c06c0c000c3c0b181691104592030401aa0b961010268030121030300240011303087c0c2040541c94900c0304070f118030b10034040040c07603505508000c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356201357 1250 356200107 356200109
    0xf01050d030801120201210c0912030c0816020a1d13050c0d020a09020a09090e070609030314070602040605120a0b01020703020111120c0703060506010509060f0c0114090c0307 77
    0x30140654040c0d03500020350010359107045400322510b031080d18600c2d10040343c25030545081c5042d10300f10300c01e81800c2c020700f60b0b002c100300b0b6039187c4036000c50740d43d1822100305070a040400600451214004000450744400052819514a1800c48218115a40007035000b0606410032807628210100604511412807040f941044007090441074150303d0f80c0d41e150362000d0f07002e0080d000751a418440e50841d00c90200e1074000e0301ca080d8095440d25100e0310001c10a507047d102d048000c50800030b907080f0a50300440c2c039605590640e50b5040e07501b03095450a4031042060b040070f0340d1400c020880070340400d07094400f502c01751005503961a554000a0640301c50707400040d10f1080c01a203000801c880c240c0c5c00080d40c00440380d080c01d14031006540d509550b0f09020400380b10903081040021103a9001001140c10b4007600d2054408000340d4036000011a2640191240385401107000c00503210301e204c010000c0c01000b00c0710000032804002200400022603815030310703030581c0d03804a8203040c914941440024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356202607 1250 356201357 356201359
    0xf0114040c1205010b1201141f05060714030708090103050604050105130b0a051e090c0c0c01030b030c10050408010608010524180103050a030305071b0b09150406050f0105 75
    0x4245003015110680d41005a22410075001040520107080100a40204283c0c4000a203c6003440300e141a0380d6010742207054400b01d008405c0030005422a10750b00328500b921504505000c81c0c42d00701014004264051079084d200c8042001240b21250f40c204000d0210328410121f1a4036003206070005400e80c0d0015050b00d02c1030f820080107016989900c004110340d00a03000e0040303a000c00d0403011800c054942e4000075048008400c011000e00080200844051800d0b2565400350b030341d04140079402c0c02070a82103c500c0c0c0210a004415610a07008401a02d00090695920100e080c1c00114805075002d18580401d01c003044c00c2200791400e120300c1000b400050000c1c01b05180101481000c01560206020300d000c2e90504002c080d00d5026030202c02d0400044104000e503100e041041ea00c1c0311032401140040d0030080000c401901ca80c103180c54001340482c1c000c407100c103603690b810344c1d40c58010101001071041c901551160a00c0d0f0074210300950103140001000d08002e1440326402d54160046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356203857 1250 356202607 356202641
    0x3120a0f0c1115060f0402040b03090d0503071e03110a0309051006051c0f0c06110c0a03020f0d03050f07030e270f070e090a050709150f11030408010e0f01 68
    0x20b0040c1a2001c1040b0118040c0c0d181c01d281c3d103581c2c2100065002d00030790380307041e006071012401092001121008500a4071210100d490042c40d11008855500c4100ea84100051a0041c00307800c0c0c0d02c40486003041d410710780c1008140d0030303a4180c10100b00c0d0820400365002a48640161050240c00d10016a41c001c03510018070041e410800410344030700d00c60408404040440c04c6400c18031280b1642e42c02c04a0740207210394600e664031000104a44040d03c01e211071030103500c0c2c010503d8980191f900044036405844441200650420040e00d0040100e098060050820440284d20000c1000306025031198036220308011240e814400020f0355a0340319069850b01000680342000e60500f80759010140e002901c0107990b42c8101251a0f40903040c219802443c4c513401c1c050000b0954000c9032140c0b543e5600d41c80c10f1550384201803070200b2000c00304404a198030b007035151014421300400c8810110101140e02e420340d905030103803c6404686102c4865002880310414028081c000e4204409080c0d001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356205107 1250 356203857 356203877
    0x2011a01081b03090a05011103100909020a091e2c010204060206011a09090106081906030b1801140705070507080f030405010e010216261c030902010203120a0f0c 71
    0x40021203880b594822801ca10740440025000da400700618031201342d01c40000e104410102d128040da41d007003a1001c2c1181c039204440418118000d2180d8415507800a101c201858600f01600f8010081c0b601c038524a500e41244406128070180a60980b94080e0440d0400f1894007801001c0100300503502500540d004000411000ea0f000503000d0564403802861007062001301c031026001e00c604542039401c0306900000140c42c030f400542c954420100050a403c010202c5401c02c0300311780a6000003071906100f40c0104440121900100f5240c0c91003800014100d920b245802d007502c070b4101e0b100d0000a0740047c1c814200300047c09010010100030000b08031811851512a840f405607010700350400c60040400d144607882008680b01070034213003000d510303110303252120310b600a10800d0303003d022140f40810140e09040c0004205004100d44419243c0d01407100408502800020382d080c0c0c110702c401d005496825240b11610780c002d18806400095040e208942041614500170620f8148940546 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356206357 1250 356205107 356205121
    0x81b0303010e010b09010c0507060810050613090b060408011b021509070902070303290108070f08040b1005130605010206070e060304060c141305041d030a03092102011a0108 76
    0x12034541502d101c13440c2c0b9612041d0410040311074185101c409007051003a1000040c4c0302d900a52147c1c083c5c1120b0614015280d1500180402d80c88ad0074991410149000c0c02041030660507405a4840640189118602503a4903c00c0f400c0d115034403000340c0c0b0b880006000c050010740402c15000a502070b8005500d85241017501c076501d80206200780000c60f600024072a00b0188242c0c40741d8480c4202c040890000d0707102e025107680111901c4041804074207a100800c00f0355010300c480a004880d590340340303803a43d502d80d5559500d800000d042d00e00c420082d00d40100b1540e55022600000141380440040c00c14907207800280380020280060301070107018a0704491a48031881141d91280d0000780c00308200d00c126404407000780e03a81070780f0b0680f98004503036801100500c2009400b00c5c2c2040741e0a02000e40b607144403104c3d131603502a200c8015401081030241180c069006462114020420301e00000130812400b0352540a44006100507550b43c542203200c07041503030358445590700a2a00c0640340c94042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356207607 1250 356206357 356206379
    0xb040b12130210050901020c09040b0412050301050f0d050307061d0d14030f060d0b09100e070807120c1805071d0a0501140706020c1612050c1e0d081b030301 69
    0x1c00c420f08002d00000c2d9051140d0081049426102c1c010341550301d00c0c645803d10300391417101580d00322284421184808480c0d4810350030740341610401400b104404541e1010011140b40c0d01d031080311180014400100482c580c0e1007802554041d5988541c0d1101d0103054941c14004403462200600440305c3c0d072007200d146000c00b03490b40845c046000e0089510340d4000998007048207000200002070040c1080b2004201180742030030101141800d10059040124668451010780a009510350122204100c01c3c1d00191007074040320300640b0342c452815103410070581702e10450381039a0410b80e110010f00c0290369125060301e82e2440c41e0b0341051008401030700021030302c40c50340c030805040120800c041104000303d54100e40002d0ba001c0f208664034161603000e02e4840b032044030440d40e94038070b02d040013a502c00c01115460046a010000c9c100a030210300400c24207203581b1408610141040d0b040180c47c0d22102d04c440c0700c19004070405515020181c0c648401e909a481d0b003881190400d10040003948070388 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356208857 1250 356207607 356207629
    0xa050a03050901200a020f060609161205090c0906061602130b0d0506011e032a080d08090118020f060c0a0c06091401030204081b0303040b040b121302 66
    0x1880d02007007984580260038090318103200344510792440d111001200e10008001010000c2403502918100c1d9820800030b621401d08842d640d401501500c0080d2107070841c44000410a28142400c481c544803020900046030000c580640250340443c10306070700ca19141d03005c180d02000444481d803800f250750044110200311804001c1c0101c143d10700d081c402c01c120703400c26028420041c0c2140f070070210b2414640c1ea01c2c5420702c552441180c1841440c44644440e020314019240c0004008a82e00410001d40c00144102c91118803000d21504000c240d03c07000b4811040119066541e20300d25040c03800c5900c0c2101c00b803107c1e4000214983c4030342401621b88051107281d8480c201c031050384440b178040b0500d003000f03807041004150000c241808118190004425419603120035a80c0161400d040c2c01542284a24081d01060341d00c807903a407500b00707040c1b941803154025028050300d04140c0e8a507a040c80c02e820a4205c40c20f00e507c0032408806191940440039480351903041d040302701c910550003080e944004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356210107 1250 356208857 356208877
    0x216051f050d1125031b03090510030f0e010e07050f0a09050405060403022103061c05010f0c03050603010b010504060f0309050d0305090c0904030e010e0103110301060503010512030a05 81
    0x1480c401128850044050340c0c0400c190020900009070000014079056100ca0f440a002140100e2003082d0030001007042030310590b00d80c4400740c03402541880806c00c0c502c071200c110300f000030b0403402081e25102c04419810301d102030b46022500f00040e2020380240c80d00c401c4005420b0b0325100c4141c3d000e0100180c07903c01c0300e40944814003409098030108030341002e42d401c00e00005003400b0501c0304111000500d148101e0095003a0b85c1462029045007244801d44407107407019100500c045800d030328140100210a03000c80d070f41030b8031000c1b00d0b945040c03d4070407055018106a941d039403000c03109a0140a42680410228003c2015001e0400060800d0080340203d90400981c0814400e52034000c1d48a030038a0760300001140d100c000b410300b0003409000c003281c50303007036900401400c03080c142000c080303150280340c0c5a19440003100c001401100c3c110261a074860400d600c5046058041e090640103501802440da03803159170b5810001440400d400d0300e007010b4a90380c81003180c800080c1d070080513078400001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356211357 1250 356210107 356210149
    0x61407111c140c072402060606030a0e01020706050a020408150115050c0f01020d0f06060c11060d15080d0e0a0b0906030c0d021210050604061b1406010e07021605 71
    0x2e851903100b010303018442c0041c0140c8034610005c00d101482e40c4100310300910f50103030159014a00d41d81281c80c0d800c01c1d40c8140e0040014008120f90700216007003c1150f42c0410300040c01c1590a45440f400c0d607400395480340c0c00e690b00013000d0021030800d1209a80c3c1242e2588030b100c1c1d55141c8a2213858000204015004009011905e05030140d001d02c901441c010b1014020364035103182c44508002000100442803c0524040340010303168040c0310000d0809420400d61400802000244810f81d40070808040590340c6d60f44040860714078800d140c0024201410003015400c95400001d030184040807200740c42030001d0481000010101422500020000d903441501c0380c460503098500b6018108600782c0301c0d0300204203080c50f12aa180c0359449100f5a060f0007011030b0341c55040c04118800d50068600003807210b03804078050074480020030465485120019092081e03211250f04110b001e8005c40c0a024480d400e0110030f5030304010320148682011006401c040c6030074005050b014000d00c02c0c84401d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356212607 1250 356211357 356211377
    0x304020d051203040303061d0403020c0d03030b0a17150907060311090a06050a020610061713060908071103150411030a0b070306051309020f091003061407111c 70
    0xd11010345840b0454640a85030b003424500a00034282c41c0c0268200c01d401c1c007042d80b03013808001c074602d40942d0f090f401134103600c00d00d401444040402030030250300b410303100c000200c0300e40c0310f03001418003d000440c0036940540b075062101d414044070044084c00508001c007031200740a03005c109441281d0090600140d03021200714441e04601401e440359030f22900f1101c00090381d5070000300810f00078005500707450003a46c07070030340e40c46007000300740039900c00241e12280c49a1181800c038403007034000700d110a00c16003c03545d591740c0100303444940000b1284480b000c81c90400f080b421542c0240c901d0001c401030301d00c0244860f904640140000c01c00703011210207130780115443c0c80500200d80200e4000d40c1038500c85c40d24903000390141100c3d106150180441000c60403144400340304140c0c409500404c0200041100800c100a10f04040c01c3e000740c0700c410840000010300c0c41d1180e802c2c0310800a00309030940c5402c40b00a003d0480c50341c030251890b04100398804512143c00c40001d455049400c084a0072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356213857 1250 356212607 356212613
    0x3050405210604080c0613051b0103060305071e090203060d02100302130f06020f0718050711010e0a03080a020310050108070e0a0b0903070b0f0304110402071b051201090302030304020d 81
    0x703201102032021160040344180b006000089000340499040f01c1d08940d5552502c107901540d81031f00c1c180c040c0958202c1c1c1d071014004064000c590011400514010440f5900c0e0380703c0a040450360b0340a4140d840c4103070702d620051000442e1032002405a2541142103181c8500459928032010100a10072199001c40c48400360084d410790300c01c03400446030407000e540c5940c40946483d00601411000d48500802c940041da0300003030100556040740007844c0703050b0380604280007510010703018400303100300444402e03882d85c002d109690f45140441c004001d1462503043c0a40000307400340c4007440340c50042007002003201e42c43c041081111400e01e0541a56030761300c041141d0344c8081301092030b0301c490f02010020351022914090000300300110305a6008603915448010309116984a00d048102c0500c001404142180d04200d40000b028002600e44445503031504620840d0300d40d21480080484414003160400001d03a10404c0702100c020001c0c0452902d005e5585d0200030300c001e210309011404e0b0307410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356215107 1250 356213857 356213899
    0x1b020f04110705070f05030c030c040525031b030e0607080a0e010207080903010f0b01080c0901030221070210020901020a20030303040f0b1501090902031806070c06060902030403050405 81
    0x780d006032004980c2c03241c94503d4800e85581651151000b10301e00450041001c0c540411a1004448000c00412203600114203103c054480202000480314003000880002c0b080d00d029003400700c000b0740d0f00042076241d0510a100c0c841490044000b0180f42c00c4808103401000195260000102d080145443d0780300484080075014107142d018195002003217100400c10030720040d115046085009001c000e40c130b0189002252100000e2600280034580800d01c0000c40c04000d00c101c40303062501510782840910304540c03034600240001e0310701a00504000e03d10307506003d16400c040c400e04066103007043c8200000c1d9107620f5840090440600c7d0344640d80b40710380c04e000c021301c252800f03801e13281c882c40c0a003042e503103408100c0c40585405c0205000140301421119104002d2541612801851420849820020740004000c01da0a2500c0e00b40000541c00401c143c40c400d40d0701d0b50320340c201110036107800025101990300c50181c8078014818400000e030010203a8064810680760600050082106015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356216357 1250 356215107 356215121
    0x501050d05280b0103050a1a01050c030f1204020f030106240504090f09210813031214100f050a0603020a050d020a0c0209061e0103180213020a0305071b020f04 70
    0x4006107048282d40e04190054416903500340c900304916a030b04089841540d60001d01c11041020031303441c2c0c004a600030f20141c40580b40f00c1003201d040116070040c92403d0750007000400340010f080f0341000110b1030f00e81000c0c03810f480e09800a00085140c04d500484070400d281d2903807101c0560301c4035a01d0051080c0d0648d8010508130005010803044400450001d26a070070040d203500e0440c0401c4041a01c0309072404001419950300e01d58156202d83c640451302c509030f50700310304025959480c86c40340740c001d0140c1c03043d10248100410450403d00c0c000c10b010205503000d802c400c040d820301040160390300c0e61000110b4009050140c0d941c0c081d520111454820401d400c84103070b1000c41c110690f0755000d5032001c140741c070941d28001c90b0b80320b00d0208000e007a9500c070354004080354001942d40e60f5200f504640070400b00710302018801091780c1c1c00606444111f40c615032059a02140030f080081d410f0090740c3d040303002d600741000003028102648010344206a006030048c4a201c1c6400c02c2501e90340d206503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356217607 1250 356216357 356216401
    0x902090a0c2115120b0106211a100207060e100302040e150a05060f070f0507050a080f07050d030c0b040c0e16030608010506061204141912090501050d05 67
    0x342061400d0031402e4002e000c800c652110041e1094004030b0b100800f03025220407183c100c1c1c0c14841580c81c01104843c14603100896072441900c5003101c0003540d5141c000c80103054840041c520805a07620305000ea85500d03042000110340c40308008002a5801ca00516690031040e6061100586c10f407009a001e8481c96210f840d007000f1490410035a40c400d11480c40d41c5010032100d4111090f643d000b0402940600c22041604408c10851000016480030f81745040b030307104d030058580741d5603118009070b4440440d1f48024259003040192440c498402e1040300c0c0034107002c0b9050380741042a43c4000707040220303a0714003c049204030008141400a882040ca00410007000301300c4103440c1c041c00d07840e641185600020003003400c01c0c802003074200060103000e02c0351034040c12480c28000c1403c0503100340c54029205413400001e00c00709010300a000d11000100c5402420346644c811a24034240b590000c0035810401001f0805c0010301c06603070b110046503401c100120001c101d540740c410415200680c1a50a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356218857 1250 356217607 356217647
    0xf0f07110d030207060e010c0c0b1e0307020d26011806030f082206020d0c020406050306010b03010e070318030309020f0a03062c0c1909051f050102010902090a0c 71
    0x1e40205607000940500380c4446685110582c45d000f4019180e561000038000d141c80c6140d28284007450a60307029065800c802440c601340b055100c903060790340b0b42c820f89040740180c00034103000d840750f85c0110718008145101004070382c1c03001c648410300c030200350103000c0d00c03500058440d11580b4a8619800910107160054900e25160030381c0e06d08040d5641c05202001e0201241046202002c206c002c8108104c5146401a00b6503110b81c03e01102c000e480f4100c100c1c0d00542d1540c000c83c0c81d440c01c00003107000c0e00d09500c4969072941040003195950500418420806091140c403804900c2107641a803160342d0301d0b040106840e0036610005030443e50898005030050381031600041805100e420428a41004480c5003500c034031030414422018500d01d60f0003003942c0c08051040c000f0309050440000080d1609401105c25803261107d03030a9420658507006480701c030444100d50012030040e45001040240000c01a204460740030a100e0840144009411a030b10001801e005004600c04980c101401a40d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356220107 1250 356218857 356218879
    0x6010f0c120c03110c0108150a0b030a060602010b030d022107020607110909013810230412060c020c04020c03040321090e09100c0c1203020f0f0711 65
    0x189418003402d03040c2c0000303007110140f9807413000110700307840140c6040e90b80403640c6c0c2e03c00c01e20b1030807207403003141c2c45400440140c8005000040000a503000705141580450900d05d0004000e09480854428500c41c1c0c004000c24206241c00103600c4403090801c41201001e6124240e501e000d03030180c000c0c040e4110400103a020200202a070b213030700c0201011941c8041584403051000c2c22a0112180c020b03500b8140038040900040002034200250039000f10750000820820100315012203107807048020680b20030108000d41d402280e03d80e1024450100b01d82050700c1c01040728480c034405203015000c0ca41c0c0f89848401c280c801e10404481d807a01420565a032001c000d10140e580e4013620060768204c103220422010410800d006100040040d1360b8050341602b019010b44115002500a1030303d849884400840c600442c01407104a00300c5445504814205003003008003450303114006410036204000d5040d108100006444080411240c0c043e00c0e104c6510780f101c55185d6074115290311403501d0b40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356221357 1250 356220107 356220143
    0x4020309011e11090f0a030203120712030c1416020301020412050c03010203040201050a180515070b0901090309060c02040207171b03090306070c05150f060a0f0e06010f0c 75
    0x11038840c60030b10b610403070071842d4501001070031201c880c414602520320402442c4401d2400c0c3e500151620070041030031480d03503625030000c4e1405505003005802e9990201d685e405229901d209178001c07140905050040000582e4010041d5810500032803560101003003000110708007c40000170190302400841d03039a03442d10242c0c15030b0311007402c2c12155840389240c80c1000c2d09041c000d49001c1c076410b84545041c02100d41041d44e01c20b481d010034812283d040813001031150b0f644006101d00d607020300650317662030015007000d083c0220000c0815441c3da0411083e000001d610869143c00c44403076103449014400e040c40014003901c5680009003c01c160080c042d00085014401401d00044945443d10080c41c5000aa5168014544055412303080f40c00007440d114012001103101318445c0045d2048440c141561620142d0203507101d20610901c4000c202c1642447d81400000d01000c06880344054034000c494190240c008202d94100f214130f01c0c002d08030fa4042c250100301d00740c0c00a50300300c030140500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356222607 1250 356221357 356221361
    0x3260706060b030a0608010207080d110d090b160e031011090904060b010927020f040306020a18140603180f0d050306030c0105030c0702041d03072a1d060f0402030901 73
    0x1d50400080d84c501701e400190240e0520880e880d056100e241581400006d41d000c10042c14007480f00e01c1c02c07460400900e00e2030100c0d03116080a06104680000b0241000d0070340f03141441005e030140040c407002c5554041c00b50350024103900101d14080c4045405128080781000d58092541d040d500488240c080c00b00f04181c80d084105a4002039848074500e40d81ca94220a12225820b00c0412a04044176860712280d030301e400500d02c0c10040d08000e4500b56596840318101da01c10b079214000216920b40c0700d82c2d040400307000c960081032070403029030200001c840003030039511024011111245014510100c0c1c60800d00444d0120303824501502e00361204140003a2060740300f00c13502d078460b0107860b034244615805101540d004140c0c00040342d081030301e15400d1000802115401c9010001c8000e00c98443c00d1082009200b007600c00d1400b400315100c1c802c0b001c400d03021030000040e101e28640c43c0a00c600700801d6080b880204412a503048562034030b01c0801c1042c511850101c3d000360002042040c815815 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356223857 1250 356222607 356222611
    0x10c17130f03030b1c0b091908071a01170105090708030d0506041d060f060907051c0609020d060306110306030a1205090a0f14030c010f0c02130c0c1a0103260706060b03 74
    0x406c01580e030340e17952411031030700c03901c1c41000b402a4081c4800c070100411038080241a68a00c41c40403411540c104c2101d100c40c902c000d90212041000146124000d000207000e5250403456500042400d58240b0306501d44a00130903540760b030030748d030395500144140c0d0340c0340c1040c050800754007805000c41e00700301007260300c41c582120311210700098000402c004e8105100c04500c588034566596040204903180b0424003241900ea040007540c507801c000c101d84900b84010b041140701c009000810074914901002520104800c4842d1540140304022503910042000d40305503a0010380000d0019400d90141d0b80da02540c218a90051001c00002c10782d9075007920300310140c8a0728038960750301200389000c260355803030010052800601a0b200c0c0901c0d2600440d11140107034801400900c0c1c00c02c400c4422021a005036220030001030900d45d0200034000410242410305043d41c00210b1503605580b66020008000c10f03c07210314059680880780c10a4606056038103581c1d00200a10019540b070600800d50703003003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356225107 1250 356223857 356223863
    0xf120403020d020609150c07060b1e011202091c1707030f030b1002070e192f0f0717070b09061602030705070504021614010c17130f03030b1c 62
    0x1500d00070480703c0c1400950701b4180c18a1756403203074196072002e441d401160000b000458030301d40c0b104d1003c11130365650407082c010650a401c2040c080da803900d0004044849007181c0c0380702c0500c10454000a41c135100130448a880ba50040711300481c0c00307840c0c90a003451400f40b28041c0c1407008103e507820554483c030000e42c2c4140c9070390180850b0396000100b001444107680c400000d640440740401c00d1b039814158040c0e20070b150110210300901c60411030001c1d900b41a00d80c2c440c0c1c18110403032100380b107900403500c0b290340b0450304c8003810300100700c1c03180200780b081007006401c0800560644074100c05101c212460241c0c0b0100302c501d9401c00d0403041d82c0d1050240d40d014003204c0480312020340c1c607100105032180300b0303009402004114640707014070000394411200d40e200c5840d00c0b00f445001c80d00c3c880c800014001c12400002d00c04200c001c00403c5e41e004600c85030003a9894800784600c0302200c2a08042080c0c02604001402c6014a4250000c005201d041030704201011021040412a540705501443c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356226357 1250 356225107 356225113
    0x8090106090501061d0102011e090b09010c021b030304030f0f0212012f0412080d0f1a09060a0e09150a0c08040b0702010e07090603150605060904020f120403020d02 72
    0x18403101d00006480c801d00071540010040344c00039603040180c16810303410b510180000280c0c41d10100c60048040701c500c0d81c02d071205480b80e2600c41000403000400d40d10140d807800800140d441600000e44924400c18003201802913040c0c118095a81401210300031a400200880c1400c00362500034400b50003000268460381c42100000d0040d034040c01864040218045a082c60f0400c24424a9060500540000000c0c50074013020030420f140c0301c11410307018001d041c000e4540c000010301d0310030744a040046004a07410040e0f00c0e0035884005541030700100049561075859903558020484020310f59010700c1164000205004100d0004203031469481c07618050b040c6183d558202200c150b03038116240d400002c1c43d920010b80070401030504107030400740d01e10000c03030380b0341462034400d1034400d00c1d8004203280390b40d8403010001c00800703c003402c40d03040c02446d060101510f0200011014001d84c4a201d018540000368108009032203822141e00c2d0000c54070b01d880d94246414029a20741d040c86103600944 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356227607 1250 356226357 356226359
    0x1207021908032110030201200a060203100305060714070605150307061e050c0d05031e01030b181507030b0103090b0c03062e030f06120f0204050c04060e10020c0a030308090106 77
    0x1040b0032131010b098940684580c80e011040000d8100400e00d41e0f10207100320b005007a0000300141ea2400254051030383c12121101d85410341c1014cd040c8840603040f40c051005905502d044807075514162000190041c03000a80d541c0c0da034044d21710641c1c900c84e000b98107001e41400400c156400c003200f040144165507008146c0d2844000980c0d00703200307080004410780d00c1301c00404160340c854001140d11800648003518085891070040180d0102078008544810203e030070003000030130365006c2a0b10b0807030309401000b441d4031f80b064011600034094036080815440b111682560b0740250410500581e02800b80e071414070340001c2d0805190816101c1510a01000542c407010b51403061540240000c4070566090900c2014400e8000f04410440e00714020786072180055140e8901c09182d0b611801100441103441a03032042204131400140031500a240c14082407111503030100480003145130507a100c54038a1582c580a83c5802c0c10307030800591042421001008059114500c41d02500f0754030028090a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356228857 1250 356227607 356227621
    0x2705060709080c091b030405030904050c090108161809050f060301060803160303060e0901020c0d08011a070804320d03050909061801080a020a0812070219080321 71
    0x941031900c02c0030240e60044400081c0f038503100110a802840b07540009010103c00d203141c011940048605071050380010404000c2400c040c002ea40d4060341d440c0800d4501600200041c007407800142041c41c80d514004404002c050040e240d03800c141105409591407079556840040c040c150403a40b049401c214840031500b1400e0501400342621300381d002940c20b01c913020740f5900f41401c0c0b41070190101a205d4000248000b51481d056004408010000d80d4410880c0c8400346858a034a180c4003c0004803001049401d084421032541580d5008810b40d64095134240308030b40340902d400c40c00c042600481406011b00c142c42241031082c01c100b450148143c0c40ea030400003080e441c4900a00421010460010b0900e02110382ca5030002c2c004148400306135500e405090a80c000b45c11103a95079010741c02c01c0c000c6d84bd041031118002c151410042c0010400e489403204640070f040b60086c00703006950300074682c4217219420703800a00f880008803501c90300d200d82010761514403401041e500c010140e000c1440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356230107 1250 356228857 356228867
    0x10e0601060903030f050d0c0305061905130923060103030801120b0109021b0a0b06041406130902400b01090614040305010911030d0f0e100327050607 66
    0x4a0301d10b074a0354464103103152800d4450441c0d040e804401c00008100d00940d43e103052140032050b054540c2c0008085c90150240034480e030341c241451181610100007000a9641e417800781c109520504c40210b0701c403000f85864415104d40060300118150078084401940700c0004056049900940d18000c05907a01d148c00c0b2015a0250300c0a000c0205c0740b801070100004580003401e202c05c0c03020100750702058002c0310314100710b0804011035a1740c046109010383e42c50b0a016860b900f4100d049954100d003040340010380c02c6201c021410312140d4489a2400655a4034982e03008030b074018074588580f001c9a4401c1c51446030300002440c1000d0b0102a010030b800d10148501c801051042e19849100c509044094401203c2c446089184c010104000310000c0c80038010a049144103255518008420408050820400a801204110481521150f601e60004905180210682e20394844002d055022406003000c10b141c01d120a00626400014803244602d00410500940a444039601d40300003c540f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356231357 1250 356230107 356230109
    0x1e0c0a030f0c0b04110a150306090c0e01020624031504022b0b0406061a04030606060809030f0c01111c2702120c0a0f06020601060509010c0f03030b15090102010e0601 73
    0x112050000207070010f44002c007158685c9000820300c007070a031755070390071440400e68404410001a403074203020069401a402444900307000c905010140c80748400000756105401488080c507448902031500d00c20304140c4555403008000350540c1c514462461721840d929000b580d040f070203480c2e002c00f01c42080b8000b25545001e20003003e50000c00352019100e12340610400b03030098032041c3d0b54420001c1e601c2c407203a800304600900c10800c1c0351a035156091035802c03a00d490344102c1c140640c6404015580b80048111204101120350a41d12070008100c481e006001c80740e414401c0b038100080c926603c405160078032480c1c040c00d1800380158100c0b00c0d0800040e58a101d11580b02c040405050401840d0104545a8944031002120141800f1400151659407290f0007021840d20410080c00450f5040c0300d41d501509290074124541305240c400201081c207030384005844e800b100e400550402d807194100f031050150051828000c1c085031204000a40d0020001d50702543ca0001c1d1401c0e00d44021030418 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356232607 1250 356231357 356231363
    0xc033405030c07360f0e0a0c0b0a081801090b0a0501210c0506092b021201140411010509040c0509030c0a2103090b04030b1504180303021e0c0a030f0c 66
    0x621320310300c9603036680801e11030304c50340b104060f201c280c401d001c43e0b414130454600b001c058004059400c0c0a05242c10001c440790040e16118008009001c0c10701d802041481e0801c4980d038a802041c4490703041a07006002e2103800418000c10300e400d02c0892103040c0c0060741650341c90b181c8500c5d400d41940c1c158140341c01c0c95000605201480314200701c2d601c1d01c0d101400064001504a603c40c600c07451040c46110190758000f4540b003003080400741541009082e448014480c90020001205041c24546507480c0c0103000820b402c4204c8000710450b44518151041400040c000b80200c0304900000790990308022600e078020712807242c01c41c0e114604124214102e40c44021100250350740300c03d9030100d09101180135024411080030000310051250010700040d07000328001809400c280070310b03e00203050141c01d90f11441c00d00841600c0d103140c40010b410081c0d031508005a0f20028440442e1131700d100e00020192441c00411006061440400d66080b094400c1d940c100803845000700c10744842070590b0b406 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356233857 1250 356232607 356232659
    0x3010e09010c020d120e0303090a0b060102030c0a02101707090302031018060b03031b010f06090603030e01081008070b07021201090b13020f0d03051801050c033405030c07 75
    0x1449400b80100031080038410b002d1720203d054a40540c5c8140b540c1d04c25a400440c643c8074421000500140604298004200344083c7d032500070117010300341e668040980040e104918806034114401e010744c032900300d07500c40c0205403112841c0c4178802402806107803000b40d01030701584466000ba65418440c02c180000626180c03c4410081e440c2e403001048040d59998042c8000c000503101e40302441c540802520a040c00851584181440c071800c1c2e4500d40e01030382269091190a1000a0700054543c61940c5e0070301c5c1c110344d01e40e10100710307503106103050b440f0040f40e0003021030110710521010700419a80d070007a5424003072400600350f42801c8402415000e0141c04806001c116188c121072891107800780010f001c00900007034180010801030140d04200d02140300011310220000410f505444502c1c000d091490920444108041d213a109906107402004540c2c000707071040c0b07a105282640c0d401003d803144405e004040c40d00d40d82e40e5205c482041c1c662b00c5640030000b613550300d542c03070315100480d07400c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356235107 1250 356233857 356233873
    0x40302070509090d11030f04271103180a06240b18011b0821090111030a02070501061707061119030e370e10030f021504060503010e09010c02 62
    0x411140005d844000c1142d074001005201c0e007000c9010060800390000415000c188205181c0c120840d000c00110004054140801a0070000340790080d0395001c3e01c080221203d484a845100d4148680341c40001d090500e041104844549a8020101403600c43d01c17104141503100c00741d1049a00440c80c61100c0c00c54103206081c0d5a510032203030800c1da9104151203400c40d00c0966110840ea0300401c0c40c82042c1d000903001a2031016401101c140c015030b03e0740007003008218070000e4402c07500c0000c203044070b00f40c0c0000320740d410088254017640081014030014540320311061203032a240c200314400d5000144c000d42c81d11801c1c540110340e0200c0354840c81c03c3c40420020700d960075204a00c184048a9101003038864010300a000707a07107003294202406c0d200f046030304102d0840900d0308032190840f0510092078020071110481c09840b0340150303504042c46c0c1a00c181188002400e08800310044528000081000a40d80d80c00c05d0145040c0c1e0501100d22800703541d0102075900700c44121008900507404180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356236357 1250 356235107 356235133
    0x60608160903260c1c12090218130501051f05010807050a0305100902071203180f0f050c030d030b04061202011e1209050c030c060c0319030f05040b04030207050909 72
    0x182845910f1031200c116030505401d400c03402c1c00c080303905a070700100e888201d54070700c070490780f041c207004050350085400c100b5041c2d82c0d000305007440ea816000200c0c10b20b903e00403a9000c14080703015400b290740310740280081e14100342070000300e0240030100d03904414001400700301b0b58000e00305140314080d2075030b81505044401104030043c0801410313201c0009030f0a2008588642540001c16a4070b0003040801261001c0040060840d1a13804400260f0060301417154009820080e60030052074100c004e02d01c1c801b03110309006080a420180e9180c1c9071040400104440b030f0160440380480320115020050b06a4461011b10381100202c4002d00141c00050141c0c800780002c80e05c0055103296203440001b01c0002c54aa008417900d20205036103903800754882002c2440c0410940e005d144090380d007030b810204421891540c0707016103600c4a601c40240354000140c00d20a074030052031404800c005100300e0410303003841d00a02405540a50060186c5c0e28040761a048c558106802004d9a00040405000d002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356237607 1250 356236357 356236403
    0x180308040206130308030402090108030f0403030e03010e011806060b1e070302010e0706110111160f050c041a0f010809030d0905160803042105031804020d060608160903 74
    0x108100d0b0300c9034050100ba00c0b0b162055010401442c800c0c0609030762418280108024500142e00c071045543c010480030444000400c19141201ea00d404c3c0704c40c04802080010340507044071002200c1c1e541c40e0010300c0d107039143d0414440d02c015020300420000740351902807448240c452800182901504100f00024940e4090002c1c070b07000380644000038040a008071110704200c40366000c2d900103000d2601d000f02040c020b201e44001c161345d48102c1c80c6440d8121144d014030040b09040a0158010003800c201400300520035030203840c6008000f00804412240e20048041c0600401d038000c0c50712508400007540161116401090400300460038040c10140c90f20103007800702421106401800810950001321603142070203400801c0286031140c0c1403010b8a010700c5042d4009090080c480034612002c62004400c50b0342018007000d03005058a070381c40102e030292003035064844030546041e000003075041c0d01c0301715240180c41d110100c40030000e4001c422140700002c2d0001030030120009136000702c0c002040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356238857 1250 356237607 356237611
    0x32003120705010b100206060103061d1f0e100306060e040f12022103160f080a0b0f13060509130803220804090c02241503030f0a170604180308 63
    0x20030000c5440c0440da0007045003202e8042c519030150b8021014000b049d80c242c003810b409001d210a0006880c002001c490300d50ba0070140810004550440760420606c290109c00c5c4054807041c0c060300181c1c105001d00d5030500900f803100303548843c42c0c0900410b0300380100d04c0703080c0a5500011307020403400c41503c038141900d1038185c0e540154498885803940850140f6440d8218020121050303407203160801c0900082c241e40940041000b908040b84483c158110341e04c1900001c0c60180001d90809004c08520030341810034a1540c0803c940e00208000010754000505070b50003a101c03216180c603400000005c49060090080c02c403801070000400c188010301c1808000c00c022800366491000300d403144c0540d64056041207101a417116025525984c0410000310740600111840303000b2407220802c00c821034805005040704401c15440c83c02c8c1d41d075007081955101d801d150920755440c0400c4e200034045100c00510703440207005600004085207000e01c00c8041e0a90055107030004601c50740e8044a1460300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356240107 1250 356238857 356238863
    0x42151207150801150f0c0308060d0b0103050f0c0102060903040303120609020705061e0c0a031a030706032009030c061c06230307062102070501020a090320031207 71
    0x4010000901c401c03a10106101059a6224040c1c02e505100d0101d0b0210440c0e01381313000b0b0101d24120025510f41c05155086031035014580900c0940b40c4000056841155002c041d02c0300c48110001310a00001050710841010940e00716206072880301c0c010380e1654011603080c289a00244400c10211740594142040e1100c0c40034005a0152503109010403030304540c9081e149540000c0400081c401000c3d001e00195900c0010800d1a1034a24402c0002d4454618560101503d502d000f10501d4a800c1c200b80c0601002019101c3c0d0070344881001b0020404000f101c5d210000101c01c4030202c0641c2313021a0030200c00500580030651520045c0a2540c0c04000311401031418a4052b4803950210b21680300540600b20004007908003182e40c0b5507041541c03039021813090304200c07010401c1a40201240c5440010000050b04002e05402054024000d900000d401940005510003d495210480303000380d03440342e1280c180b00015040da40d5a5802e10420458140c0e10454209c0104140034020b00725181c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356241357 1250 356240107 356240113
    0x302010e030c0706270b0d020d0c0806040b09040c0306200f12060910180e010203130c0b07080315060c03161514010902070302421512 59
    0x450890a80ca150702c10401084180c012882c1400711551100252848000a100b05909445010f9040d907804189105402100c14002815001000950192a01e01c81a8882040400703001d41002d030254104035006846280380803640c06040c40c002c00c00a0113990400e4100002c241103a540700d006065661402f04040e829034598850404c030400100400700d01c00c90603d0701c0b02e81d00d202c8d04031040c0b4080c24180c803400581041010314ed15086004003141c090000310300c1080c00c4141c40100030008241030480030350002040000c0301d40080c440642c2c00d8403904040801540d00c2054443d01c0c062070744010701d8840d040010681c580294012040c2036800145040d242c40c0d00a101c0514650004210880141c455514501480145814030440b4a020300d000e110900e1840280c1c0d1801d40140503842140394003280d1202414405c0010700480440071405100c0240d11a40e01030301320226401d4480500780080a141224403020880c600640c1100c0c00d030fa0102e11150704012079000004440c3d00184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356242607 1250 356241357 356241371
    0x402010309051906060504060b090409031407240506090f0c0405090a0f06090c020a03052a030c1605011e030e0618011a030303060d0f02060a0509120d020601060507030201 75
    0x14509101d20b80c0c1090000415000343c0380646411000c1d120145e00452150f46000401c020001c82d19040380c50780038084400080792200d030f1400f540c001c0120358504086c2240410140c08001c2c0ca2420602c031100d000c802d0500e16000383d9100c40c00c1d41ca003110031a8110102c007004c0340c154800702d0300c0c141e002803607d2000c600700303600e500c0803a001d9041161079400140e103a20b614584102c0314414403000e40881c04051080001c020750203561000104002000c11100203045200072121800203002c0300e107043e40150304034110500b2955a034100e02c2c0031016030b010395220304101c0305200140c101180d0040c2c54200c662014910f54039480041401c4890030706481c0d14040c05000c4050044034810840028402e4000b082851107a0840d0092900d20703060800c44d6850f2011942c001003601e0348518210762071041c9162a02d0300d420303803140d902c00c02500700d032000c14a00e101c2034102c0301806144406440009900328072403005691210841c1071000560030800060141c6c500c5140206000c038081e0001103498 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356243857 1250 356242607 356242613
    0x40302030d0c051206030d091802040b070807150207050d12021c0614030610050402070804030f0303021215010c061a0315070f08161808030d090b0a020408030d050402010309 76
    0x40c490744014980043e00000799089035565403485541c120ba000d4000f0005003ca0071009403c2080c14060702800740b44900c8400500c2084d07030102c0300507081c144502c6032241d030980752500042c0c10114041b0348800140d4070000e01503295209031018240c01c03400501a01c094601d042d940616010b180d0903149808001200b001c0e9240d03000460110000350300000d5152034003075141ea03a50031081d8a54032a420100a101640b1040c0d100c01050b0b601c21030b801641c5042c5483c200100c1d11850f40010000742a1152a6080c10b4140c0d0242c81649510441c8969640d00c01c0c0d10744010760226401180402c10604120340415616032104565000c070440001c00c0c0400c2900003482d214140c0c1082114078011000c0003600350344602180700d2641703107081050707a03030400031605480e03d003000d841c81c000c01000b109201c00c08000c0103000001492001c00b960341e92200c0032480005011010001c0d04c0c242021000f0a6410801c0d100b00ca0882c4d000d0f030003450401c121171841c80090f100c0507200760304140c0c46003140b8002c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356245107 1250 356243857 356243861
    0x1e04020901032d271416030b0106080711150a0b030703080405030c090709030f08130e160219031d0604150e090103021f18090f270209040302030d 64
    0x164800410f0f020f0b100300c001010f6078240c0301c007401550180603124004040407003044c1311850845034004128100100080c0740c43d8500070000b0301010074040c0045000082c0011a034400341aa012176403420340540e929001520032041d040e5488040e0380c888603280c1c400f00440c40c90030b42c00c0a4003020105022603000002450045e1541007641c1141c0c00040401c03180c41d0400014040c12000c0c1d841c1241440c00e8103001d004100c0a20003d440e2103a540103150411007604102c94200c0c0b4031286a03a103564031402c80b030483d088111a10340714500500101064580000703400039056116075403604d04003204da0b03821245604c48a2010b02c1804081000c501075964841c00303840680400b03a40303031341040780e40c41d801070a8040d080407a07805811400014070161300c0e1490b000f000011807496458002d101c201e4111042c5103141e8003070078500c480c0c413804661407030303d50403242e410503e0180a0141c240315a41e80b4064000b52a940c0038801080b00c02c540c0181030001e20664810f0003401a00e0030a050f20494800f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356246357 1250 356245107 356245151
    0xd05180d05030f0d051012020607030c0804030b01080d0207081009051002040303021f0209010f0c050f1b011205100302190812030f010b0c25080f03070b01051e0402090103 75
    0x21034542c011030071314050307201480740c80e61205041800c2c0c50042e00c5c107000c3c0205800c506901030700a400004401c42271601891020509070352051a0a950f150791b424142c29880c820b0140d400345014250310a01401d20014001056a081034094a00e000607615040c000301648001102d01c1d00824104001d1648244082c0000714040e401a1044000d84003c1702c214070302340100360701b00f5441840f0792a51070b640500302c812601c60909000000501c0c0c0e090240c54480d074403481d041940708071941c8003c2030b0311303c45032000140d40070f03214400c80b44010804c003801d0701ca0454140003022007420081015192198100020408807654002090b03101d2081c00d00b0440310350031a032181ca40000c02c3c0000040328404841c01480c1200c42181400c0050300710301d481d0108000382410000240f03e41c0e00c082800003400c00000c107200c4046034850f42000385502c1c0c50380c00880041e5807842d24103000107203a040c240d1041503040d2180b840c05411f50380100402000350040e01000d810103540b41c0f906040012111071540d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356247607 1250 356246357 356246377
    0x81602070911040f05150a0315150c02010807020a0f02091f08070303021207020d15020d0207051f0b09010902180d03020c040b041112090f010219080106020d05180d0503 74
    0x240e0303900c0c14044d44540e007120703503884103006112401da040140319004090722142012450045560040c0603603a00074610690000c002c00103100c1408a41c041d081580808058400c3c0c03601c6e5040d81e510142a0f0302c60402030001381107900750009440c014582620404d900402c140101c109900710103402701d0203071030030350010780c001d60002d0381c01e10034150100940300414410400042c5011840c0d40030a046144036000146861408000c0035105156074068401e00106002d0854503a140382c01c10076a02d034450200510390741c0d810280804070720b00900410001e50b9001c0c1540b880340e44ac242e0781d0b100a602600030364a91180200c86003c0a41d188640700d94110b00035402021280d131000c0801c01190300503041d007445285014a140f40d803149150980d1b108541c108081802039558003041824002071b201044507552002138040a41d13018406c113803064103820350724600c81c0d0303880d204180d03a94160700440a0110700b05012740b12208450702d80d1000c0c8420050400f00103401c15640381d9265030841c41c101d07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356248857 1250 356247607 356247641
    0x4030228260c0a0b010911040605090d0b090d090506160308151f0f1d04020a030b0312030916080a02131506030c110606100e03120c0c0108090303070816020709 70
    0xf050610008164071070150804202c1086003c400c80b552441c3c1c1d12480c0301c3e10081c000b000c56002c11a9440c021280b18207038114402118907d099000e041d207400c41e0003a00da021a00a40000c40c29080c40c409482c09108030f00c0d980c00e00070310a601c0548841d80b009241c0810b13082c03440546515600c0c0c40ca0b02101c400701d070720401c68110031403807030240c103002201820408002e600c030444219441c90340407404002d5070654006070303618030414044000d0b003144800f00b0f0b05803094040c1c6081507803851004611420f000d1054034094200031182c14007040040c0328a0146612070901c80c805858641488041991802c1c070004000c0d030500c21083c000c0f452540140301081c0e42e058407140c0c42d90080d2486650b103896074090203452030404001144031001001000400005404000039903c04018184400c10303522405500c80d00c040314404d5851040740002070015410b2004140100f2000051340d0003002591030b00100380d41c17072034039084400d0f5951034503400b148556040010002d0441c8940340c0c50001c0c0c6410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356250107 1250 356248857 356248873
    0x21e0912030a05120c03040b07110a06180309050603010f05130e011d010f0c1202030a020f03090307060c0504050d0209060307051306050a080d0f050a1808010504030228260c 76
    0x22440d0110017446203006a001b0070402000442d4550032540c01441403c0c2107603006140e1280340c2c034203112980014411b40c540500c1151700c00c000200e80d9980d5200f941c8013000640c42d402440007a01080c460240c00400c002014003c0303181500040e6404040c42c0b0000624400010b80f150035145007882c801e080206220001e1295002070141404da445001002c1c00b220003103141c018441591288003004156021021640221960f011249221000c03c12035480e070520795100c644940c0000341c201c420f20b203050b90f420035641c000d00030f440481d100109035400c4407405809003c400c050060807aa0303d03000c0c2d80ca0201c2c6503a10f4005400c550310800c5000140b00c0d040c1810311070f10000c140c208440561107404801c10640d889103241d504400300f07103401ca0311800709000c241d40c060800c1d500a1100c2480c80c0b004a1140015800944218000d9003141e00344a184a612044446400300d02c14204074000451004540307a1083c50303e1004208032869207201581e0b40740015604048100103c0303400042c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356251357 1250 356250107 356250127
    0xd0603030309061406011209060204030215030f160801090c020708070b1e09030a0813030f0311061501120b03030706060b040609061107031112010c09090c03021e0912030a05 76
    0x31584c0c0c40042080155071107030500300006440340049000c200f01e000e4484545070b04110302901690001d543c00760600c034a514100d006404250004c0301c070702d0301109859002688400309450001138401c059183c80302640d0800b90050054120034240c1030546c072030b54000040a860802411000380300810070680c64040d0f41e0f90601c0c2c006078007400300c1d41e0102d040c000c07060340b82d6010542c6600356a1180d1140e994014411121540f03250741d03070000d081320030300031807140174160040d03481400ba21080054850a64074103e00003035616105007210700240303640550700116000780d4441014450000c040340e007080070540c0c6403002e0750740c01c0d004101001d10100e0300b0459540c01120410152a490800703a86000d0865605542e8107003500c0054801d100c150b21442250316030001b4020000c4001e0000d110010001c80040c3c06180319110b0300700700500e010142c05c21240319101382c0d803d40d80358174030341d504030301ca1f03180002e902d0b412804400350b115200401c503900088080008000f00b400ca0b0703e940c0c0c0c0303802000c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356252607 1250 356251357 356251361
    0x3080904090c17070506030c030f04021c03050901030b04052521060302030c090f04061802060a020c100f021002090a0b0d150504050108030a0c03050c03041d0601230c030d060303030906 81
    0x3a11240c086e040c2481401005014501500e90004040240201c036964a000242c0e001c5c034541403031403a042e41d41c40d0a0b003d241c0d02071700408441170203880901c100b901e110144000c0342d00468110148840b00c040344a00b1070314100c0d909521201c0340c50a9035040150480c0b0f03089480c03410900d200d2a80e44c9850030411070034203000b0902546012a61070159113040040d22032030480c0100001c2c61181d0740c4c0d06010001100015400384070b50050042d0351a01e48954010350399100c2820302a01c100714080034480a1441400100c2e8001c0d03003079028080301784105020b2801780d0017201465078004d0074501c0219440740f90902802c075032100442c0101b01264040ea52000381046508418056402d020060121000000855190741214544403418001a00b41120b6501a60b6034103540c6000004000416860b40c04074945c80d0340c001c8505404545a841c015910300400c0c82c2c02c0340b18840c2c80440141c11201010180c08030105180c250380c50451503000a0b400c0300c1301c40d002100802d903500020401c0c07250364 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356253857 1250 356252607 356252609
    0x90c1d04060926090a090c050d0209040f051f0b1e03060d05191416050609150f0702210d14071a07020d030b0f04091a01080307020915010903080904090c1707 69
    0x140020892004504d40c014050301c5800c000811158001030152f525031540c1d400010403408411040100b03040c1802c2002100240c8803510403511101c1c0e0700403480e025a076045890400c030012408410340d41203590343c480b9400007800590702c226103400100c01303d2070502600b1900940c0000b000c81c44c030a00e00d460943c561124500191507070024a0560301e218080f038154003600c5089070480c0e2142d100d00c00040340c6110240c02c08602a002260355220000d6070000341a40034400c0f2a04c51451a00b24800020800030b540001110b0384000040107400d4015442c0500c620b11081800740342560540300c10031402d48141c404000e5074200340422065540c1806203000925441c6000c0c007100c00c8460008a416a0030503085e880382c1c0d0340e101c47c04104003903130b40e20460100614000301700a603035034082039469801080040c0e000b00c5205000904032481c940014800040c144c4600380e0307040c00c58030b4400b01f0b60811810107801c941d444a160000c1010307030b032000c0010310500707001c00340b560100d140c014201450303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356255107 1250 356253857 356253869
    0x6090c03021b0705010e0402030903090a0303030e010b15031f0b0f04030c150c0803130f0f052104090203040204091a090c040606080a1808030703090c1d04060926090a 73
    0x11103e07051101d0780e440a01600b9040f4101c4015841e42c44800070300b811441400d82c61640031481c500008105038040d00050309100109008101249031603060194025494003205503d106c10400515240032020392000144240010a2421a1079007500c19103540015007400007a00003080400404c019050108003030440c124080360704040595000e060301c1c056610040c05d00201000180042903d08400b000f0305030840300c0c000d04500c0b142802c0740b41804010094595001d00720071580c4485103455072944400b900800c0a160a140500400003500060401c9a1160311064028085907100e08100b00007905602440e0701d9040100c0520b1515015070080c602441c14504108041c130f4024503000d61102c034456010490b42e200c290110007000107a04000e103140000f2050042c200d40c50f501c07006850f0320883c803010203951121b50a211484405400d030100218003000100000c1d6540c0000308420310071402060b08030300c1d2607207004070b80c1d0039808055000200440d005949160082400008200c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356256357 1250 356255107 356255113
    0x301030807061a010804060f0e1014070503010302100c0809040228021b0d0503120108030c0f0319180e01080c030c0603060d081606021602130c020712050106090c03021b 74
    0x1d07052001170041640140040d001d26641c2d03c01d100840718039006110442e910106035107500b85100b42d02802081c0d902c1c14503500c0c1c00e112002540281c05001168160303034005014070000341066100b101c40e241d0b02c07102151510010311411400e51500d0025000c0c01000548481507078810101201155100010400440d405030682c0c4854101480f0b221700034000a0f280c2c4146500341e4100285148a030740085140c40140c034000080e84400440039203034003010101614100d98400721a66503034041c545a64040710001c00f0405c011a00a4440c0100012040c100d4102c01e43e803a01d008906207801d07800300314940c20405e0b130f402c0b81e498140844101440100e40c50b074290300f011030204030098844040100451030005009621602003015180401e611100030f642d00c4d0003482010194859640f0100e00404080806040c503222601807103c060f542680205900c2c0d24020b1458908141010107a42c0c0c0c0d56240000310342000f03a40508494504140c4000d640d85a19845000302081c0140004030903070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356257607 1250 356256357 356256401
    0x102010506010801050613030b0405070f060801060503011511070b0c0d11060c0c0a060f0c0f030903080613090804082404120309060b030105130b1b1b0a08030103080706 74
    0x3a03000f0201d5415030342c1c00d581081e00d9411041025076003d20036000504142298402c2008000d40001c010082c0c81c00301d2032401f08155610020b80d00e0031400e0080e540810b00900051290314041e80400640c001145010b4030b001107404282420400284c00079541c5034030018001d040c0650422041002e051035141c0501000c0391110741c1038070703000701404103020003000054a0149040c00c000110b20b0b81d41002c41001642180300304d0000408600000034080f800030081c01e0303c098064820907001c2c6130940c50700f03a41a0754000c10080c50f12003912000040968840858010443d00305c0540090010301c0024003004902c0401d624031140541a01300c40c4584032030170040012170030350902c100e150060902040d005128504800900740e101542e60300342d80b070042082111140c1c50000c4284d140075841400003a245d2035113500c42c5400c00c290251200c00104080c200440c40c58804400400d0b401d81076500541603990780c9400340e4003c0c0c0c03090300d2603000891311000380401803103404003e6800100c21000c034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356258857 1250 356257607 356257609
    0x20f1f0315050d02091b180301050105100215060619111c05071b09022106011806050c071d0403030b0103020301031505151201090b06040e03030105061b030d0b0f0102010506 76
    0x143c00d10f83c0c000d0098100e00082803c0f541030b001d4140c95040e500540e1a12070000480034401624a00364242c440d42c2840d00000d03050405060412080d0001d6010308481d80f0703a0300c04031580c0030000d4138450f007114042200c184441032841c0c0c101501da04a9648031003c0d85910062481c020950a04020802c95100b03101c480d00e800c20110342e200c50340001c2c442050310703484101240364031240c1d000c1143c660000031081c00c0040d4001c2206919012030040a5954507110011161040300d441643d82c2c44a0052007031008a00400180120166960480780010340b262115007030b1b02c0c01700c3c07000c42041d0000d03810b02c010180c02d1b0241105060082c40c00710306642c9161240840c90061104071242180d8841c041000d640017410b03001c03204c20015010007121214000032134020200c1070f8041d50104542d101052080c41c00f4041c039520302c1c0d0f06070003e604507400c180c10000d00d03920038a50301c40c0400e00d20310108250203080c8040c0c804001000c0e00054040407100500515200b801001030440e4506810440d0b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356260107 1250 356258857 356258869
    0x2010501141f05091302030105011b050c0409111207060207060302030403080114013609060b070803070215040f021021020d0908120901060e0705030f04020f1f031505 73
    0x5140708040121541e81001c18243d5140c810003c040350809102840d508400c04250019412500c0a0369113020318001c1518458501c0041c07040100b09401c10110b002c62351509801007101c080c000c0c001110800751000002d095030708622465151500500801c0040c9034062005000811140c00c0a40c0b55140a5a000341a0307081406410540f52214540d074220344d220350501200303100c0c1800040070303854201d034010040c000f03005080c513a02c4685c00c4000c1040ac206028502c2150300c4807030028207014040da1a041c1a8100a0040c0d0440c030440140700b0301005482c8105004600034241443c681e0224011f0000401c8080242c0e410705c890080c010024681c2c50400880b0010f002e040103032039a4540c05c108019103d550380260840b270303000c20000100c480b590005801541d00d00d00801c5010b80e40c1680e41c0030107004031061000302c0c2d41030000a005803c400c014540c005c2c8014004015807050300d00103485803550300c1f480c0c4c00101e01c4003070106800c0d070103106407645207001408143d1410310340400a29 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356261357 1250 356260107 356260129
    0xf1509060f150f3501080601080a0b0a050a022109060601080106200f030a030e160509010b09220b0405060a0f0302150d09200d031202070f020303190201050114 70
    0x810001303514290820b10042980d03890b40d110307241089490760700342c4002c0301084c3c0100b07000f00d80c1580078071000003a0610001490396583d43e030020304034103d9a50818034000900000b0441840f00ea0200000e01d0482000030340c4900c0420899a20001410245210391900780010b03c424184071205005010154100b240501ca000b0165200900c4400c2c0307101c1c00d4208400840c00704a0342c403000c034600b205c50303030141c00003000345030724000312001c2d13a080100301b00c2c0c04061071107080d4000000074018803964805a0041455420203402e14500d003254034203050801e0204103425550300d90b80c000040d21890a4040c1c50303004081159a92621410440b40140500e80c13071100034400c111484154840010031020350300804251a400c2000001906010324400504601007000c820300b03044031a4603203400b0054110540c0c040d034030100000300c0107000c413009500502003030721003da111480c0001079034100020710740c0b01a0800300c2883d00c84520f03006825200180c1255040c0d1555950810451300d03800303000d903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356262607 1250 356261357 356261387
    0x308012c06040e060114030c030a03360e01060e030601080627190309080106060f05090d0f11041401080606040903090e04030507030e0102030703020a060f1509060f15 73
    0x1403074803081d0009004240541c0020754a0080800005843c1a12000082241c4098040d00c0c2d24030142d80415840e07259122000b40071502c001d20b907013030707007694484000c400381002d000d181c074500c0c00e46180324845103103640103205003418000140010780c0d022980641000059006001c0c950610321003603125000205031704685030f80c0600c1c843d40b941c030b074004501000b80000c0c2581d6040300e180c16900a4000802c000b900030a83c5030800091800051040900715030b5130366902c0c0c054500d210400c5035030354401c4401680c40101c0d410410042007110307500b140b14a12030079a54056002540a100a840c41c20500c01145680340c0010001c1d100d0200784198000d804490000b516005468103031405182a040800e42c0c00b51802000200b68107c001460b400e4003a03252039842c120388000483e40ca02c40d1070402001030304940790210005805402043c901c2c01683c4000c51200051003210700f0442c2e0960003003035070701e4888030100048803084511901800307608600d0312103207114207806030500369260861 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356263857 1250 356262607 356262689
    0x607050a03020702120a060c05031308031305010203131416090b0a180e1b1c06020903030d0212010503070f031103070b190f0810090506040b10020a030801 68
    0x5100c52003941102c46942e8002e11000300310102c0310070903a5a07021000122440740c5800a226885030080003580d114100d64210140ea1a03280e03554120550070103032680c01c449840c0010900091001e0001d14400c80a0b04100c000154243c00c001c0a000d075861005100d9070050842e40600328880c0d00e200043d207101c4407020079034000c400301141d0414803030780c002100401c405d41c0710313000b400f09500480140512803045a1500099541c102c00e00000b0340c0109a0240100c008440c000980c80e2180c1c150500078240141443d2120010174150317440f80c10101803240d40021306d20b031600c6a00f440180500800d40041034814185560307400c418000d400040c0c04502000958031081da802c000d288042d107039600401c0d40307038042d520703001400000c007104400118641039a41184180305200c01e911550440305c03040851032419180c000102009000386400c80e44032009a145030304c4080714a4980041e990080003800107500b0020b142d1030040e0001d2050003010041116501304200e04000d0070340440c201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356265107 1250 356263857 356263867
    0x21e0c01050c160b130803040f09050a0912090501080901060b0a050715180203150f0a0e240117061506030a1d010209011101090203100c1101050f060418020102060705 73
    0x8032483c0981c1d0140003890002580008a04030040c20050300c420404007058200c0c03191200c8040b502c0380624014102c8858400c2c02c10442d00100380c01480d00044a900b00040c22181d83e200d400c10200311500790004604e01120030481940e004103095032140d0010004c2003220f041200741c1030944074881241007000310104155041c800c0400440c5410f04512604004a00b10b041c11500790b15043c4905a119006250b10003000c00d5861010b14850000074a104d9946c0d90359440c003030300903c0c100c0300c2d0110b64451041c1c0303041c04040400602c0011409186140d00944c0b4000702405801c03543e160501c40d84d0800f1051007501c0007494005814000f0488030b680d00e99560704104001426050080d80d0110412195409044010340c02016030721401e030381d03004500050300d0000d030a03516118030094059003e6200c859600000364808590680d403440d148488070750707540a19080d5681540c00c040e0401e145010f100b01071801d03124090000003003018501d0800d8040d00080e441d003800a01da07806010000034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356266357 1250 356265107 356265127
    0x5090913080c0322091407050d09050102040321090f0605030c0c0105070c1119091a060c1b090f070f1e02010207150203010b1b1f0c021e0c0105 63
    0x3598074010b10b400c01c82c4c0c0c070f40c50b6002c041d0300c0e00081403e40c0804441c000c9070200303200c68503004000c680303a00c0155480d42510350000c11a019803052002103459030744e4141c80d60004800380002d0004500038a002003800c0d40c0700e00c0b040e1038840c60744814810310641403020042d0800301001d440031120641040d43d2a40d8450300d50245612440803280f00c00c7d4a400d0030001002d4101e000114014010b180c1d8100e400161420300c0700e0403400c03920402d5804418441009905401d4000145d44104141c2803100c5202000100d0416088003200c0f140700e8000046a01108080b920540d070040c0c803c4440c440d140c1800501c40a903400080e0104040100c0c2e2502240c10f98000c040b154400356400c0484003807000e003060028000e4211220440c1c0c850340740361900305c52141078000e90303041c0c038400342e9564a80656400031103104140030700035100c28013076000c0280c030702300783d1107640c2c409400f459401003410041420300030b09209011400c00441025500010f0815100007100c100560017801c0a5036a4a0180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356267607 1250 356266357 356266373
    0x5030a030914190b070c0b040522180f140307020603060409020d02030613060612030905130f060902070311060c030105040b0d140312011706071218030e0f0105090913 73
    0xc1c0c400c03500c100e070f90000105181614020407840e130107002003504840e29000010b0084c800c0c0d12641d41e000080c0c49002e6003032066030422080a000c0307401c0008400404082c031b20b1029641c600242c40a51802302c55009011000d1502d14180d42508040e61500c00c0550009a007800054440346c059541d40c0d60f41011900c5900394081c0e200d4004040390341038a4003c0090100c0705480c241201c1c0c103410403000240e00040c103111000e000340d01d40c80782a00c41e4200400d10907110481e02c0c0c3c907107003d51140d982c6030440045208200107000c2300c1c02d015a686000b420041d1808000480e10b00c0700c2e07400081000758400e8440143c0781501c10445000c90b20215000006030510201c0c1c2024100e41c0e246010361819a100000410031030306101550300850703aa5000600c02c01000f4440c94441d0b411240009114502c02c08201d0030124115030001080c40d450704c00810100000d000840c0032030350000700f980c03840c50600240c00d02503d091034060310300000c00004c40c10021028245c183d1070b5940e0380240b41008404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356268857 1250 356267607 356267629
    0x61203080c090a09020a020f06060a0603110409060609060905100e090601020a06050f15010c03021c09122f061911060f010f061403070c0201030b1206040c05030a030914 74
    0x418503c0d0054841800100a40c0010360300346c0540701d040c002c2c0202c12004038035540301d114018000c003085ea2030114182c0140000c007210304a65803080201145404151246801401c180e80d1001070407401c001024102d4109900000e104003049a5002003680c1e105016668602003a03a10300701c2611440010303850070340c04403c024101403c100400c450140706411192003a00341e844c250080400680055410700181c10014005070450a541840b6200d4030380c11000d0ba125618154441325510301201d4018107103100115401c0c50b43c3e0b1944003200c4060f41d281108010300e100400490380c1c8407000a80c19209040715846900d600d00d4074035458a00850b0210155015002516020b1500c1c0c3c450030030300030090080c2c1a07214114440071480303920a00c4908000710b5040c121614640305c404056908500c1c02e0000c07410181c840201c4141030300d036005d03100c0340620141c1c02040c80c0d040603d0071803403d42e4280c0005009504c0400700401099114076040c04981005038694201018035012440c02c90301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356270107 1250 356268857 356268859
    0x403200306070305132616050105060a05030a06150b07050105180616031e061d09010207120c0c0506130503010e210a030b0d0b010e160801050f04091e15061203080c09 73
    0x6c0421512144210012051030b01ca20450080049540b85c40c204846e008072401015056481000c03064009440e503440203201c0b00c0c0c42c151048006503a9030800344554000b00c82282d01c1c0e511503043c09603580c42504440301d400c02d9000030305010718085084404200c0304100c41001c0586400e0344000305d0500141d00000c1901048051103c0c54030745441e42c009003a400b4030000c04000b220001820030f503041c1700b0b0324456584034140b445010400c80080f5104a69514140c80c1e0410466000407240e03034030f500910350b00014441c01401d942c03425040500b110344100c5403c4942e04403924018101c101c000251012068240c005a00c80b40e803814110000c003c800c11564024880c02d0105003403141074840141250760300031605440303645108074640c00b1510580700c9800f003070400c00140903a25050f003261b103481c5005403000500b201a900c0704c1c07101003408014000310441c425051000d00c2900c0c48d45200c1c19030700b41010311049140640e8001222100301000d001c000e4440e012540e0030310703c8000c850300160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356271357 1250 356270107 356270183
    0x408190915031409060118020904180605070e010c05030d020c1207080403020f040b030c0418020d0b150105030108250308130f14010206040215040320030607030513 72
    0x4601c09014009000b1030704015461050b441c001020b40200150041c140e82c0c003803190045e00c903442100311020790810030300307140e201e900d03035400007200b2581810f48000030f0300404020a40d800c0c0f6038005004141996030141c104081000c920021803400400c5404511380b058005a503480c001e030529003480b403030201e41405203000041e103509001e00c0c44054015203008036002d0a2100a15041008562280361400e4050300071000750f92241c60254814400c2c038a440c0a03240681d4110350000702410070701c650848094130080180480c0f031182100c03004c03030b00d2000e0800030718550500f11141d13500c240c0c1d00000c1c800f580e4610003011420a00707456101c0110741c0110300c645c851002d1040340350422014000c9000c0d6a0070b041e80060351440c4035540131100f00d81a0054410342e25181c09210402c01408000345107082c00700000000104025410440789100d078072981c000b060340310101410008040d10b8041094142001d0242c5082c2e032a0400f407015610002c480550341d0f0402e409040822060544510f00c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356272607 1250 356271357 356271389
    0xc210b0f06040608070312020d050301060e0d032006040b3909060c0f06070203090612060d0503030708090d030c0f0509042904060e01030f02061c05010b0c010c0804081909 75
    0x201c011f01100c029011940c00b550040d02e60b2507403c8800b40000d110300c00000781d8903030b6075403110300f03210b40781e0300c04240a1324000c00c3c0030b42e8469142d21504e50000140301d035507100108010a21003c40c803150f03049035089014419007480c1020005180c41e9243c0e40260212010521104e0b1401d218112400360314082c003141d4541182c0d19002d500c03003404508810b103502480002039041d510100c00c45075034040003482141427440e00e26404508031401000b990300b1541c3c01d640940400c5003000698491001035640c10030910f0040041ca080c400d114104000303040c1484403802226400560b032401089041c6007081d1200d042c100010b014024141003c3d50700b1b55034007009945554983c012160360300c42a2014441103139107101100c9525404d100140420145507007400040c54800d00404403824a0445401313600e07001c290090440e2000e900900900f0400074070160110b00038011040c8005103810900e20700d103040d4554581602c21096440c40303c440722405602014000c0c800e0501910014054402d03403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356273857 1250 356272607 356272613
    0x207092c101e05060a030c060f05091f0f03020c03032d0f01060906050f040902030c0708030f0109050c0a0f050d150e040201020105161b0f0f0c210b0f060406080703 72
    0x1150342d07400116240e42840001035441c2400134640d012240d0106084210f24505034088504401642c0b4650400c0fa040124a015aa5000354020240f544043d01c814000b43d80c10003a01c3c001f0441444000c1c5030050020090700b500100c140e941c805920b03c09440c002035185140b44031002401d003111104421001031206401c1091681d50603254142c499217189a2030b90002c0c2e82c83e005000b614070410904000900401c10381c0d8024640109040110301c0c00c0401654459145401c1242c082c0e00c1d0300c12010040000002900642da0001142d000c0c0900d0f166501100420700424400c4c000240200001ca45a03600380e0340c0c0c0b1003849a8a1440340135542c82e110742029501e1101940c06900540c00d020109001000251404100b40e100761612000d440d44854801641404260306072010f0140c5020000410308404251440c0c5206107850601541040700c290340388060b1100004440d502d0991200c00140b5980e00182c000f65123000d0629980d8030700e40040d0280c46e05030403207601402024000010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356275107 1250 356273857 356273891
    0x915040215030435070f050c06040305100605010f0503150a170606031002280201021b030c0f0c011205060604050307080607110a020904060f0609060b04060207092c10 73
    0x40ea6a51182c100d004c01561410080700d813940e154449000c0720811044d000225504410b0070340920500031b031b80c401c072503a00004606401c150310548290300308481e8045818294403440010704424281544000c0b40f0300340c002d20030301008182c06c945407510044038046a0350a1003003401800c460718031a030307051240c2e040c20f0303203540c01500c040d4005e00c180c0000035008042e600075070b4404500d00e107241400c1c0041c101015050a0444140d6096542c204410080c5215000003140100002d800031035603440c080881034604841c54400c1100c0b0703001220350314210b81e84124018007010f80b0005c0450140c90701e0300001e040d8412035101c2f079410312400500046000f4007050840c0310fa4100d40b0781c4981002002a0a82c4403c1d071828000d51080c2c1c4440090002401640802054481200c001962030b403520140d804444080d048496038034004141003054a80c1003040b000a4458424180301045d511601c0004070740c880344a18010f0850701080103040e1804011410401103242410301c54801c0d410a00c140d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356276357 1250 356275107 356275133
    0x6060c030e0d020f090c0903030409061509150507051c03090212061e040f02040e060603070f151b17030f09010b0d020103020a03111b01050f09150402150304 69
    0x894100140d0120620b42418490005500500500c0103058002c1c10000d510070003c0c40103100031014001c020b0592005c00150001e403146003000146c66003012038822036130628a07110001c021401d003080c400010709600c11880340099040c400d403208a246011030800410181841c94041a4001519640d9041e048161a94000c0c0c4e040541c0c2100100c40940740c410031617030110f1051500314411000d10080c407510754003e005014100c4101281d60000d0240c0d03002e5014181e480d8005401e002d50f44c03500707002d55130081900b42040f505240c40d140c0091603a184181c581c40070b00c41c8006254982c60300102072445110351000b0b461400881c0c1c1d541003090380e00156480d6281841c641d001032080c1c01e05110b45021b00780000c000385412070036030f80110040d5100701003107010103031500c4800001e0502c0001420080e84d1a180d0501d94200359008a800c5a40041440b08145950b005000325000007090b659450741e40074071075090b95929400400d240240c0c500e01407441c08800401c00050081401c0103003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356277607 1250 356276357 356276363
    0x7271805010603060518041722060f0207051507030c080301090e1c080f04080c0f0f10090305032e0312020c01030c0e0405061201090c0602060106020d17090f0106060c 73
    0x3107a0b15901846091400106e21083e5046070101081c0070403a8103040a6420781d020007140d00e8180c2c0024920045260700130350340800e0110180600003e50040010840e421140c4010490240b41c140010003c1804c820400f0380300c00002010f00500d4410400c0c2e0f03000350341140c1125a20350f0b40d49003400003410441c003030344114050f4400c1881e0303d600341440d0f2660403800390340da0b011948400318100170800303015108a42c140c00070002d6205804d0b0510000700c28808507009001c480225440c854103060030034207403200c0d407403902c041400000e4010043c1d07504040c19407046081c4a26503682c03d5105850114200150101500000100003024040c4070751800c1c554251590001c81c2c0006609550203031985001103003e00d4155401d070b09199003c182c4c84a001401c024a500c2c2d1010058210b071003a80e029120585508014440b0075010042c140c01010603200402e0100710304032004048050b00e071201c030740700c001c18030118040760390801580c0c801c04013000c001c2003907540d682e0018000c079040040803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356278857 1250 356277607 356277611
    0xd080319050711100510060513050306100e0a0203060901060c03090909080a020114060307150507080406030b21060c0c010b33030603250e0103050c1807271805010603 73
    0xb1076168000d81c020580690326012410070000c7c103020090b10243c2006081c4444030040712030008499408103c0035010700846e1220784240c80c01c000b44010b029034020040951640100280080c946032222590b04548003480c000d400707001185000c0718070800c42e03400600200e04101408060020b030400034003080565400030040400c40c1408040300341e000300c0702c069140d00a454100310403401085250403024942c640b01380b508420703968444440d04150802c5000039a5a1185001810400e9006010940a00c210040194205100c0d03a07206001005086031034000705500100420035000718040d000024140c181c0800d181c00011080f01c9203a44452940c0b4030b00340200b10400c020000c0b02c2c0150030207409012500d19080600c0b40d0203c10041c3d244083c2c04408000410503000c1a0fa940a0b600c110050280d0740d000a0400004c0c0d41025070480c0d0f80034500d01031120868100d10306421000810380031100d0040c404940250709605a40054900c0700700313030100c8130740b50f6881d4006416031309140c4007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356280107 1250 356278857 356278873
    0x11043602300402090a11040801050709050a0e0c070c0b0a0228080f070c15030b040b012f0c190806090f0717030415020d020c0f0d080319050711 63
    0x880082501d508400110038180003040150500b448919402040b020f00412400c0c2c0c481d10000d10746d801070384412000e0b555001400306a0b5404400100240f5088582c00d00c040e00b040f056900d02e1a010b024070150050005842080220010030b01000b0480140401d49a150a16001c2e40350a00c802c0b49003100d00c00030400c40c4403074030003035000d126440e00725465505040c285001080e281e4000e800036900501008000a101c64189040c1095808e050f540812050855404e0000b6100c8004006040c0310283d100c1c1d41b450406d01c0140440c640c0035080c21100520903130700d00d03401c200503901c1003500704482404503d50010f65084a070221881d443c1200d06603a50700300c20544940704504004542e4122203030800001036540e00c00072003c030360f0380e042d02d14180d500c0d4441e040c181410301042c00036812001003110380e2501803000300300801c41070f03414200009188001640c0451840d2004107040310101c0800d50603c1000c4c5000c82401c40c95904105508103a18064489046028623070742c20711400407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 356281357 1250 356280107 356280157
    0x8010905090705040906060503070816270c09082401050609060f0d0b1c1505071b0501060509090c120a03122301060e0a050411043602 59
    0xc64903100c1c031042005010024140010007000c1c040303624094800584400300401c0c0d56806220030401414218014a05043c41c3c4a49400d5006c8039804049003c3e00040c0003c2c3e8890241458112055000340000f060307510500150349006030381d040402913114180b1494800d84049110351011004030308040704583c1ea0b0700c2042480e1182500e681c1e04004140000e8030340d8210407010303000000c40100d012840c3c03045280401d1000030300304074034007081304408984010f0001c003e070590340100b1600024085480d00043c098600c81d84c41c141444d0502c94003040301d0a2040070761003030340948001032142000c0e00380304500541d105103541c2814820840c45101c4040524001424200340351303d40ca0b03070b94115901207200c0d03008140c5c1840b44411305d0114030b03081d41092200c0c000300303001c3c001c991240d0070924400d00512006600c6900424000c0e851f224050078500d0f24a81501c3c2202d06000f0229804590b0107103943c485404001c22400e071400b41c0359807443c0f004854014242d12881c0601c200b1002c0360080f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 356282607 1250 356281357 356281361
    0xe060123060d02090604081920030703080a030b040e0312071b020904020a0806070c14030403020105031b04031a06040f0203160f02120408071401031e0c0c02041803080109 75
    0x40d10840d4081010070650000407082e801516411000420341410300e03550310883c900340b030a80703000038000c240c00f01c0e5904100840e01c2e4511000904085140d00244040004070344d07945407501024003241c00205501c500c9503c26041025504006007041c00311044480940b540c0e500800c01c403100c030f26541130024803620301c42c584d802c0c484c0c10b0680e0341184207103c40c0c0900411900140003030303030029920380d0042003614040144034001e508580e90094101c1c0f03142000180a88000c0301d005694204000800c0541c2e448429690019804901150950b9442e05203920b544640c0d4001001c00b07450000440c0300e140b500c03000310710405042c1c40038400c04409202d028100c0c4012142c0300064501881e130410340c80d101320303201c240c00441c500499018003041604441150000d901455055000c0c800502c103034208800342d01c101440c00e007014801d01e1024600310900703c2205001e500300542e03610075001ea8a01c0b444540d011103801800030481c40c130000403d41807042c00028240d0200f0a00000040c11003498 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 356283857 1250 356282607 356282669
    0x80109140705070809010201020d0218030c0105042615040506040606090209060a0807020a02123a0f050d090803011403070308030109090c0e0f1816050f01120e0601 72
    0x10303990203283c00415680c5801c66040403030020704640d0f00f80070020129201e0701c02400c010403550400035101444c90105803812008019a0f810400c0500c4100110804204031903005440d020070040c2207883c22000b1864003107101001c07002c58080744140002d0040c003040082c003c0340904400d110f443d46031f01c1c1d03a40c164802c266560340c0041040210b1200d4520400005401c03145e41d00c1603074840d1645400244541040ca02080c0a94202c40b8094801400c403402c4603810444646c003035070035017000700c10740d81161038a640464140030300c480039207100030b1040782103a400d03940c0e00004105504050510a16540007401410903941c0c200051280c2407400007031410803640c0c458031540c610b030300303019904010340003821080341d11280007040410821119900d80380b1415000741c5000a41c81c1c14841044080603e060110982d0820702c8240c00e5081103d072600181c43c401d81d210800d401860300100c03941c2d40c00c049403520040c0303003045103109410040350260486982d00c0500c0950001051450600700710 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 356285107 1250 356283857 356283871
    0x2011b020f0103092402220302150c0a050d03050f0124181701020c060f091506150c0d0e0105042405070b10030201090b030609040204090203011b08010914 68
    0x7084501c1070340c80782c3c00000416104034840030920020109050103019a481c01c0359803c0e4010480440c040305c05a01c0d07480c2070301300c028440380c0e8501c0d68002ca5804c03126900c2015031b15000003001040c0d450104020210680c2c8641122610b07850014020f0003820103903620044e03e4100e80000601c0c0e0241035019004002c1940c1d40d8020040c180e60581d101030000401c491143d071003407000076100381d040040402e0540b40400240c2c0d212180700019007804001060013000c8055a401d2040c40e0200044030f20669801070341c42c5480e41c8501000815002c140e51900b280340000040450712007a0115200c1412078081d250344860b16455001500c15005600a40090011f595448010340c0544c2503d142c4000349800d10629150542e22040c540c03c404503941112101300010070011940c1c03040e4800c0c028a8108100b500f9030a020300061305d841400791000e0b01c2561151903100a541c0c0c00e41c022620f030726100784804d212139161100608401003d111f4072008034a442c1c05442a6010300c2e003207074032400f2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 356286357 1250 356285107 356285119
    0xc05060a170a18050102040e0718060c0813030809090c09031005040804030203070308131d0c2101080a02041d15071103040b04291608070602030f0402011b02 69
    0x1907070402a191118008080002550b100e2001e6298041030419042005000300c0c0056070780c034104a807090a10f00e015050714108806051707009044015002d210003030311001c0c0b40c03101e51100d05040c440c12500440d12075105900d80303143d00000300000381c001045410381c1510049010390703480b280403a140c052450840d404d908640c1114141c446950300040e8014800c403141c90400d51030342c02207840c0c08025041100c401c0c60001744640c280404121040003080721040800100f40303540c02914810401074402a030100c400308a005030701030744c1000507003940040c07041d0600648c0c0d10410f884e501c40750804141e005918060030142e1509000e80c405203988501402007412003012038414070a00401003c5c8030400408079643e120b4510140000d000078140c280d04662a581084400c8400a4400c814400f000e001f00840d0400019242c00703403440600740403c64007844c00e260900840e144211a8010449480001009101d8035402c007011f0241c3d000782d940180310b5a002e1300c0203c0340030794640007079403100d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 356287607 1250 356286357 356286377
    0xb06032d0f0c09030319030905060903040501120e030d0e060601030b060415050a14070506040c080303150103020a030e151008061506090f030a03080901050a0606050702040905012003040c05060a 85
    0x2900760002405403c101504072407a111245003111207284040024100080d01c070070310f240a100007000328581000e1400b0146142078500700001e0240314403a4032040d0310589034410800f60350400d00030b990716031b103d80c00148100c000002005498040807a600e80c042860020300500320304101068400b51403803c43d4031400643c46890984058221031554020030803005800c203112280c01d4042e0414520800052060741002d189c204a81215500700a125034005e004110640c1e4400c0c54803410b0310300a00303005907141c466030001c402820100707858134854400c400344842041101844030384070399800078010403050340b1080c01584591059617103182c031310340c00e800a01d62071800e10020301c0d0030131000744090b03211414031303001c01d09013000c2480035030119221600b00500507000f8000c2d10fa0241000904000c10341c10100d01920038000c602001e401540d8406a000820009611400d1342d0700c012800c23280400d411f489151744651045800b103414a68503d000551400d02d5010f96100341c0890305c1d210b400c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 356288857 1250 356287607 356287621
    0xc0905130518071d0903040f03082a06061e04020f19180303030c050913020a08070e01020a0b0a2a0f08040f081315050a0e0306010501080f07030b06032d0f 68
    0xc084c02400c5174905010403c00000e6100c40119903400030352041c8540d1341c079407000301400d903000e00400d0303007007460840c103c00c0118801c03802042a039401035003228014240703900c0b602c0c0c40142130000382d4026001480082e200c030140121001900100c0389031b44030b103c482900030310b040780c4800003019440e04817144da00c000d0000a009410140c0c0b140345a144c6142460b0b4401d00140304011502c080c4900c0d0f80e40051007100c070a0380320a4150b03011020782011090b042180c00000c3d0f9a81c041c602c060700001c8044c010078001c1c0d05d03580040d1038072480603980c143c0070a0700c00c590702c0d04001c620740300ba40414a1300e440d0b6211036000b0100c862140e900f1540541c0c0c0c0e0f524175120040642d2201295185203c6140e401188013088244d601a42c03e119503520342d1200803140014004985001c0050300c668030840040000da0b9204140c0c903408442c15201c0401c2d625050342c164060b201c0e10102c55484800030040088a0f504e4000c0056003415507410090907000c80c14121b40b24950583e40c1820100c00701001401d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 356290107 1250 356288857 356288909
    0x6070c030803090a0204062304090c06050c0a0803041406010f1401050c0102090409110a090e070306090c080703030203120a0209150c0703050303180d05120a0c090513051807 76
    0x8070200e03880c292000000c02d0345c001011112a60485162140c0c00203510030600315202c2010111030b016034081000b4142512040c0b1780d03010600c111410004d001402e5680100c1c00e001388811268046001c0b900d0342001c0ca009107603c1540e0070382452501c2840000608a9150501d030012500c0d075028201e0f110b82030000450b0b6950040380707003503115034007044405078070b4031584104200c041c01849201c9405040504200b118085a800504454101035100680140114064088030303405003001400d030b1072901d8049450110350340040224040e011000051640210003090341c400013508143c0b050307940d4140c10b4205d008540d076643c0c01545248403105501200b40081990044050031925181c1c0d817580d8039455030744210360318441801041644060500d0130882102841c1c0b841c00c03c2801d0200c04400680c8645e00100081d40054461451607111801803524401511016003401e50603020500c444016000507100702400758644072103600d00172004601102502c82182040300b04211888401903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356291357 1250 356290107 356290111
    0x9030605060f030f0705031009080d0b120601120b131a0606040807121b0e0c0d1404050c131b051b0a150b01080106081f090c1d06070c030803 62
    0x5004a5071040703a0071241e40c2008480c501140540040c1455400c6c00d0a150030309003085d03108409107040035010800a1003510503078107808030303200700003600310148400181d4080314030510380340c54001c00001140180310000a24251030040403880070a44400682c080094a04017000d08200703e200007040900000451031500000c00814503070502c2e4490f1001d40c1001d40c80d03808028000e50001d40081084244141c02c150010a42c804401c01807401110414159005103094211100017071003803190405640901414608a030003050980b40610300540d90718a030711b5040d446091103190300b4000240c507015038090001c0c24050501c00287e40d01042d5619084803008003824821102040401e8104001d5180301c213008041c00d00400788d95080d0b84080740d1010b0b20280c100004c4400510800390030070305840e004070825004002043c0c065400c0c9043c030010790401001c0f982452041c2c410709074010740340c0f030340c1c080a80703c0301320b6003d50002008401d10684000503d160f180c24000c00c042081c3e000515 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 356292607 1250 356291357 356291359
    0x501081e060d06020406180f03080910020f0105040f02011d03030d020a27031202010608071214100614010c0209070e011b1a010b03040c031202100504050a02030d050a0903060506 78
    0x5485544803001c1e170300150804000110400075181080307214046000c010108070b07203a02100ca0641d21280c1c0c85120700d40c0d40600417040d08000c228094420400c110740781074840001c0005041614010710075402042e4280e0010700c640d1941120401050500507020380002c005500d0810b81c0c61014010b50070044007a000d02500c8010011102d103982a103900c1c0484200c01807100c1c038158541b968003040180f510104681c0f41a000384041d4400084990980309810f100c0005c0781c14516240340c0c0741e05d12100e4130209001d00400d0b502805800d030028002e5484500910310070540c200011551031060381006980f1134643d10204042500a144200f00c4000c1850700c0740c0418488010a0f03141c1080c5a000c6504800003491071282c1300350858590302607c410342d0060314504007034035527070700031281804003620004810104a51040c0200025100c070300c6c2060043c009403030329041c065154a10060264040c3c0105082001540c0c03080c07040711100d20716920b0b1040c196007161145002080014189 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 356293857 1250 356292607 356292619
    0x1506090f0c08070f05070f0804060201051312050d110a03060501120207030c0213060e16200a1401020c0109051b0105070c1701140a0203100b0313030516080c0f070501081e06 76
    0x2000440c0090030020305148c01910714079555031034944004d085810003400f01c0e504041c092a41c00009208101030024403441385040d90325130040b55603000050941c4201c800d00030780e0000e202401c6540680200e070840348240c886040580d07002100c0420780c801c445005000480c06051a40103182401080302e2060300c0c40d000084ca213455440c3c00940390025140700700080c1c2148260300c0d840742e1217a2840c04a440300455501c0e0340328550080c076604c882601c0000c24150b8000c001e25028202507042e15440c0c90204001d01c4070103002e04001e9269890b290005d1070074001c04849001650180003200c5000d0303489504d240019190605108800d00d038094101115500c8614143c2c00c118120091401010301803001070303803420710320400038643c00d01340d006ca20381410900c104240c40c60384c4142d007158250181491641c48404034103c1c0c00080c00403600400701c500204140c7c0c10710f000013580c0d40f012b04219048a50003a10b0300010340c1d90000444003911543e0880b00da03820380c011210f1a107074001e140078041e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 356294964 1107 356293857 356293867
    0x717100608131416030311010e06010308070f0f03030b03010c03050411101e02030a020f0606130b041d03030601120212221506090f0c08070f05 63
    0x2c150400301c08a540042489041d100280020200b842510040c0c0c0c5003d003074810301d0b0301034041940042c401c0442c4200b07410052103150520000d000080480783e01e16641e031401c5a0207440100d43c1030913103040100003e100e40a01c910554401d031008140d0f50508004e1500b1640700400800405043c0000c2c040407590380d0054400c050303415180080121074203401a03c04090701c8054440d502a039162040d1102c2c0d000c40945112141c0c0d5080d20a500d501641d1380b5622102500c500754401c07090b609028a210103a030225001860281001c12014030a20703001000341041400320100e600b00108102c2c40350390021910540f400140d40c21400c00910950f000e406400c0148401d0000e5040c0e00ba40c9045103054880c0204c0d290f1020146e00d00d485007200001c040e1006200d039124dc58100a55000040054003d10f0100c50480d0364991460341c4001d411240c10840040c030400380001000 = true := by decide +kernel

theorem cover : BRFrame.Cov 356115107 356294964 := by
  have h0 := BRFrame.cov_init 356115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 356115107 ≤ n) (h2 : n < 356294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
