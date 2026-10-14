-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2822
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:50:50.530494+00:00
-- url     : https://prove2.me/submissions/270fbfa3-1ec5-4840-af2c-ee0acc4d55f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507374100 ≤ n < 507553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507375350 1250 507374100 507374113
    0xe0c130c0f020f0312060d0b01141e062a0607020303060f0f030d030f06090504050a06050c04060e1011010e0105070e1504141f020f060708010501120c02011805 70
    0x5000341500380901041400c2d50020b4100e404071020100940d07040036000d1600f2880c82e80e5242c0020380039a110080203199100b8640045003120314801c10203000081900d41d088014050b950b402c040c2d01c200c121041c1d01000800142000c040d400120070300340640d48400d811001683c2000d141090012554000141e20104c2008101d00c1c0030340005d0385540007a1802d00001443c1d00c0860b460310201001d0a0074580c6036540510302e091154010b900501040000b0491410175141550300c0740500d03041540c816003401c012881c0765074a1000c441c01c80c0d074191181b44405a03c04244032000a00c0c1c080807050180b02a201b8540c48802e008102600a00400025585ca0040c1c80942907800c04102e5034000e07074005254a16200300030044800ba1030300310344842550003c40c4000382c0188040406140e07003100310700403c030710b10f41c0000303200d1124103803d17040c2da404d076540300d8086031900300034402c072030000e00c4401e1201b80302e03c401c0c0d002200d5075a40348008108081c02c5062854001c5482c50222200d60000c4c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507376600 1250 507375350 507375371
    0x11010203090607050a06051b0316021e0304030b0105060c0714010c060608011e020a050a0309150c05030f010b071101030525050a090e0126011e1a040c0f030e0c13 71
    0x81c0319465000b00700c0103003c0d44c3c0702c00141c0001554000100701507850181c259055040e103008100800880014174811340148411303002e0720b501d80e0002d100459043051000c0002c0f4840c42c00e0015502c2c13403c0c00100610207149440080051003a4490010741840302d900090310208009009180180649800200b4923020203005101c150300c61204404000348140030501c1256031200c101d4a41072528035000c00c4035409420000038049036801c070040c0442c43c0400222070035400501a41c45081c00c84104502c42c0c0c4d07034800e454079612400000a0044507001d0700284150700950000ba04410108071411492813120410074048400700210400320740f02099009150ba40040080301520300c5141a031600c1d450504140144c0407040369000200c8010358855203100000d6000c1003125a47c0e046c1d1204070a1400d1003400207120300c40000d012a4590b0805c0055800c15005101c01e0808603907565440e5481c8000450040c1140407280d400c901520a41c8511a981c210320700d188140c09207000a40c0003500e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507377850 1250 507376600 507376613
    0x20f0d091a07080105010c02031516110309030606010c110d0302010609111e09060c060a05010f0608040f14030405130f0b09090c090a060801050a060e2211010203090607050a 76
    0x8180403110031a04001c2080341260f40660194111207081c2030040c03400b041840040d080ca2001c03070750395108544c1a0108505400c0c4100781d222018120f44424005c40c200c490526107a20a001203d80c06500810204403107521070090301800c00c3c000c401c208519241c81c2c0016440180018050300140e440d501c09000d000d5aa20070245000041da07209460406001c0f008003010650074000034802001150007403035522400e0841b0a160300d58002c0d90081d2401e0a0100b001703003c03c1c000c3c403000d8411518003081c0140210700984c0200c0e08000460020a455546d0f00e0411900c41540c61540c0428031002038a40c407010790046100e40b19000100300c001451502030101c1381100101c0344504080c1040c08031210002c2010005003109880401441d5551001e10300905000c4e03022818640c03a0100700110b0742d21980c40311041d22800c9008510036210044500d03004402202c0c0c000039403083d0302c42800010b10a0309260001201070050b031303060814a5000440e03d401200e010307244c5402000e804c0042098 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507379100 1250 507377850 507377873
    0x12110901090209130209030309181902030705180a0503010c0c150203010b0d15030f050a0c150203160c080105070c0614041205030411060f070b0604020406020309060706020f0d09 78
    0x881903800c609144603e00007806400200f04242c07410303940042d000c0301780e4a040c07080f54000c1c0c02c098072443c180729194101e1100c4220458840180340e860000074031046440740200d82c0907013829607a59003041041000302c0c8200c40d007180d41550013410b11030009501d480a000721030025906403030300c0140000c142849202c0c2098240f00003070700c510400c01406003204074400d0365545a154500018440783c1c40b00308401c0c20000d504042c24015030721300141c08110300011503042c4648110000e444459803080301c0c1c055603030070600358405a007080c813540b4503400142001d40300700c41c016004080001e94030b615260031240181c45010008803c400b40401f404081e01880201c09020304218a0303a10302522910341004944068030100100000850180144148141c0c0c66060041c030407607a40c042e13101c10380300c182c1c0106401c903a41e040403c00110305161501c02d440890314a42c001d5440d0001c01002c1103051781c071451040b90076541c28422038402c00500ba0113004d401c500013000150040060030708a10519 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507380350 1250 507379100 507379109
    0x30706050c24190b06030114040f0b0a171c03050103051e0303010b0f0c151501021b0613090c03140606430c0f05010207030f0809010912110901 63
    0x1600721808001c14410030b2103a40d00c0000428860400070780255244080c00358659000d50203036002c000424030100d029030701c1010103c201c400f0011011455407090503550305070308603580f10111103030030460100c0300d1000c40c0700394031184281c83c0e000081c00c0603400c2405015800d007000036940d10040c000c000301000400300030f81170315400300a01d2600994090b074034881400b40007010700b404a42c02d00d000c0300d100103903507228143c03a05544a0f06443c4003056441e9500f10b40d1144076143c0000d40e40540e50021a100c030740c024005111001d010b8403802440101d07840060346001c0a1034000307000440c0c2d1441d1003602d1000410b0365012a0100743c103403c4641014019100a11480c030400c00e032041c06504144164900250807441452800032840044088001c5e20b1035107001d080c0008441c040051003004001038451010100304034948a4004a82d83d50003070000410b0303160000c1000010030b42c8607000d00401c1c44145894040c007a01c42c035400400140025044402100d801d142200501d41000001d0150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507381600 1250 507380350 507380383
    0x19060e011a04141903080d09060b041503060b06120907080d08090a0f0305040b0a091703040602060c09041503030201050f09010213090509030403020603040c210f030f0e030706050c 79
    0x7800c04640d0001d11070482a02d070700c19115080c4d00c0c108403000355070740e600964020800390340f580894104030003d04916402210318074075000e41290785180902c103100807904400e007000c00082c00c40d5150401003d09590307071079100d1000d112a051041400c00d18500c01d020043c040c00e40989003881e01850000d0721510704003407043c00c10070070404940c00102800c06603000024006048228141992140f195420088900c040003c040301c00d00d800c64400002c40f0655040420071a0103210303810f849000750300404006804c003034082084103c0140103086040801031000a0341d806143c00144a114541d00450150351100704100c03904c0e9586820176485002c49001b50318125854403c102c0c0800d8078001c0c50300040e945c2c030100760210300400556010b10fa010b000c2c0b07652410281410718008410348103112504207003403520701e00c1c0d000c0c0c0828a0f822550120354003540e410103039416520035143d00d0401d0104245084003d41310303a42080311000615190b00c0d44d5907100051540941841404060650304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507382850 1250 507381600 507381607
    0x90302064e04020d030509011403091f0608070501050706060b0409140a0c0203220e07050702090907050a090902010e04050711070608010302180c07050102040f0608070e090a0519060e011a 82
    0x140e1514a1000046035041c580b1b140d40e4813006005907880030309000c140c43c10600200420484403c000b500000400d50000c11115212411a12009403001070150148580203a0030030000c55010b5405815414418480403031502d45500118640350425800a000141c840084000c0902c01000c0e564000715401300c00d114050071068069601d210351500702403400c0007426112000c10030355410b00f016048942a42c0824188290000c0480e044810168440c1c0100f40125150400010303c000c1101c07006420000c1d02454014108020725110300103a040c401c0d00350f40f816442d982c40c414184104155120800c444007031440b91840e18000d0f8002e107041c0400d4034014000750b03480070b024060301410303604005182d940f0b1050807a0b0754003c1c084018090f6001140100d010004043d41c0400c0e01c220340e9842515950301182281c208081440e6107070000c019501280f103aa0064000d03a900c0b402c80c01218000183c0a40c180048440e598000c40d99000048010700c9008131341d03c509202c000929468604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507384100 1250 507382850 507382853
    0xc050f010917011d030c01060e15060a0512041b080109020603040b1005060706051504090f0f020321041805090d0c020f040f0507110d090302064e04 65
    0x41403285010b648000084599a2500d841094100c80e0302040103500b00c202d1002068240c507030365003050350081c48039401c10a02203801454015228403418100600d04090751410040c414254802c01c680c1c0104030003000f1007060141500300b150300492050a0b040c000d5442000d00d801d940040d80c01442c0360380d05000b4504050384da200107070794201c4e4000c0300012541e214107030011f0011000350702440e0880780c082551800c0c044550310072031041d80015400c21002c8100f008000403038014100c02040a00c0c0f024845000c202542c0c1031042c401c0c030190450302001202004084150207405d006129040c4c002000d12041c0d41c2481440e4200c0f04810040c0014141020000c1d103607140c01c8844410019a9841001550798a41d0081c80e409000b40003080004242c105100180008a5141012030b5904a07903800d212400259414400016643c44044505607400c110b9541d004611400100042c07202d09207600388403019a0840200c03504c4404000e600750501c0c1d09000e00c1c003080903203000c0c045404110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507385350 1250 507384100 507384107
    0x303030c0f0d0209030f030d050106090b03041412031305010605090f040219050d0311011505130b121c0206180a031103070b0403021e0f12090114160c050f01 69
    0x840c0c9200005010b521a2911505440207010703c0d03202d40d5040c414852003145440d130120003032032030b9104d403a03052219a0b220002a0341d1440f03039109408411070200002000300e01104400301043e41900d0603104018101d10841c06150000d1700d00c003150486d102c140c6001c0000c2480307028014401035541030084d00d01070544002c0c2500051020740260000035003503070307610200c3c8200009001c00034500154072005e401d001301050a0751200b0003096291842d0340c2806191071560780c04842c0000c000c3c02c0da05031541c40c4800036005400708580c01214019040306802c2c014842c030f440e4500c0081405021207003540f0003d14008002d00f00341040110703011500d0464401043e100411780d054102181d1240501c03150a00e94861100041c01c03954126043c8400c1590200700c0d0302d401821403094640305c1d0b02945c4d520341c0701c0300000c3c0001d1640e03115221610b030452840f000b5090041c41414110b803000102003a040150b803006040d100c0c00c0b10744981f050100032080d440c1c503014110030703a03c1340901c00c148400039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507386600 1250 507385350 507385357
    0xb091002011e0b24070b090a05100f150816051c0803040c0b190f020d050301030219050907022a010806090402060f0706050402100201141902070b01230303030c 70
    0x126480d607120114020f0303030344401c03031400c07070407205902e0540e0b40003814506054240c000d54003c60342c0200880100d030340501c0020f20003602039000300c0504404201107a84800420a00020110751760b00c8480c48640c00e08080c0d1352100910108024003036040c60842000308400c1c0e29002541704072410a401e03000c40d200c40d20900c0d011030b4001030259603629603003072901c46c403940c4c4d44c8501e86d0b841002503c03e01184402c148043c0005042d00c1d144a000c003803480c1070340c40340c81c91156000007030001e000404c051f1805115903103940e040c8004c48401e10751110081007464100300d60102c00342e409803c81ea400d40031841d011042d110480c91110202030b10000000306000400f4103001d1040004070081070a5580304012a003460b90325100840c0d482c805490510081c0004403000c0c1d10450310255030400d5540103000d64220240c02e1100b04403243d6540c00041c00c5412440c44050045500b841080c00060b04d07811140e0183c410800707034041c001c411340c0300e8540741c2c8840700005000e90018811b010900c1b904070182d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507387850 1250 507386600 507386651
    0x1808040308030a02130312090807060507060209040609090503181c03050a020c0a170601120b180c03070e011809080a0528080105180910090f0c0b09100201 68
    0x40c1e96691a400c581e00b0290003100c40d4503034440f80341d400001c10440000f03100030300000030380c4520038420380e60314429403203140d18407803040410400c009441c0040c1099004084140000304001101038171030421100311034105000302d880ba88000b401d600b94024400e124100080101d4820f491414120b408103044020544010140701001c502c1c83c5030140240038090b034100c4050182d051540d541e002e0844103810308881003940d40110400458900e00300700f6030301119500414030901c3d5413140055040d00e4410b1040903000f034001d080961141350390600c07007000104034a000000352941004094845400c2c40340714034139214644200d003070005140300d00383c85242e205c5041c0591030308642036601301e140600ea0005000d02901100d0801d20540002180303040c1d400c02d032004001d09204c03d46115115406a48021456000c03001c00c09007001c882d08400001c61060201e001c0c40307400c0340d4a014039000d07150400b4400c81d0b4080744043c0b8608210583d6810350b50584000d11001d5101d03c9012640c005d40d040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507389100 1250 507387850 507387863
    0x170304050114090718050408070f020607080309070e09030c0a1e0c0906080610031e020f0405070305041403040e0c1e0d06050a06030e03160c051008040618080403 71
    0x24060000c29031000380c1c202e0080140c6010b51400e1440e140d284c0319030b4080c0510754610144060b40b000c0d6980302e42032180f54002220751814609890f1841d40500b03a903c12644840208a6040061150000b0b0750240b0060401440c03400e0402455811491006003581d00b00c0e841400600c20341c031000170f4180f1040341c0016860840145a10036803003683c10500300a0100302e8450b00001e22403220703030f01c00d01c221081a02030b1042600c40c0c0b92400c00e00b4609103c080e01c5510381d1088403510031110300040c842c00788010601c280000000012a003035031411103038100400c1c3d1b5a8204030921000c101c030107011840aa01540c075050a1410f429459040036200548440d8007080389030035050400c1c40d055855204070307070301911000c0b81c1a07400d02600b01e500406010f88000400001c6c00c2e402402800e06900c001c002441c2040220a5804600f030617034031b0305071401088213200007202c1d100c3d81502c52920b42241d0b075401403840c090900e0300640390f40ca00c0361103020b45900200c10106503110107880c2941d51001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507390350 1250 507389100 507389107
    0x10329040204090e030d0b0a06050307111921140d0203061324060914090714040602030a090f060c03050703170c0a020105070201140105060a030603060c03060314060417 74
    0x200030400901072a0020340000e07180c42ca08401110000014056040048800340702d07851364001800301a0759180300702d0700402d02c14408141458010150710406030f0060741101d5210303028000180f00c2c1c10848000760340f5003008094140d403008120740c14400003803850514010f4043d103445c03c55800e2090054044810b5030200105103155603000e40c49402042c3c80c401882040c0c00041c11060030341004034540c16440c120000000d0381d90160002c242194101742e0402e14003103210041c01131145008010004001c51118603c2d9500b2405020300042c148030350046813107400f440750141022075142c0040d502c1c0d48030750b201007004607404458030412030340c90300c4d0880d1180301c1403405039040c81c81305e0114164002082c0401202c0440311003e0014526554002e00c52629070140c00d0b8201c2d0301e445121448000032030014450760409000400326070002d0301c5d00040c410f940361150750444800c0c5400307400280e03d50f4010421301010400981c0c415035500c02034085030520351740300c00c1901107100301d6180c40d10300030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507391600 1250 507390350 507390431
    0x9061d06040b070605090709090c030209060303070f0b1b04030f06090c0803030103200609100e0112060e09010b03030a120b040b10111e07030807050f1204140103 71
    0x281560001c00c0c0750344140383c6500007481c00c0809002d0440d508942c5100f21000001c03039804900500030001d40102480c003c03241960240901614014504c1c2e4040c402040181c0000710b0300034150401c2790003003205500034103014030f80084407000c04001c5101d0301414082400452520014410180c1d407140001980801038a0900d01d0081e00c0d500c4140640404400001880401413215003542140c80d0350400c84c2e8160401c100c994001ca1040a0300016451502444140100c0203820b00c081c0504140302001216a030941c151085600120305059084090109a4409029422183e0703c110060b508160f008140100a292420b5030940c0c213648810041050392030b00d604c05442c0c1c050203028003c0f9070608000240014070000c4101a940c0301d0700802100500c001402000e40d071a4560282021038510f4640c2e5005400500c01901c540c0141d2190304c04001080003001c88142c0358041d40394680349842d4681c1c15030310f010021300f41498106910400244501910610182104c400302d1440318100e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507392850 1250 507391600 507391609
    0x10501020f1c0c051e011416120b03032107050705060c130906031b0509060105180f040501080f0f03090918070302030102220902090d0b04140d11060709061d 69
    0x8884001d4481c1c00303100581250201da00085c03c1c10003068200034415501c02c4000d1441241c4111a0366180e619480c6010344c00c5442006000d01f40307441040081948408000064155442480c01c0140e90750f110400c00c0c800ea8003d0329081c1d010b405801c01c0740c1007680540340c031070712081c000b008200800c0000032800e003c000701024200150980d80c00c1080303869141d2602043e20088c80b5441c22184041c0c40e0006020715008072613071f1003000306a454500300906010300e0215851055600d40d84408102040003054031544641070007030039164000e000a00c0b51034403c504001ca07452040e00c05070401c024450302a2603900117240c02044074401944040c0c40c0c44640740c201700340c0d6040294594000250080b4a510880c0c0c60041c20348000700c03500f00030355200d1700041288580d80e0314540010b900091000801c0754400603e0b401402145a402c1903041151002d05280c0c2a800250201d5280e4003003040740c903020800164494454104145030b1400d140d0044c010b4607070341220103211003041c0042c40c1d00d41c94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507394100 1250 507392850 507392867
    0x6060603041e05030d061419050102072c042f031c021509010614011b0605040503071205070c1202030618030903060c04090c440a050708010501020f1c 66
    0x11202406c0104a807107914400b405583c004199118490081031a007446015a1041045400580003416441c0c07034485034006d01c4001c0b0390307900c0c0d0103007101c0c81f9000b80b80c0742c084480303108912900110a03410080a0401940d10741503000302c008101d1003120b80085d8800141211102c0c0099074451581c1d07098610491405070f0300c20030340340e20004640c107000b402c1005402c0306090740c040c480c0c0d541540f02e03c1001190030041425500c0c0c40180070313a00c0310340880e16603401b41e6001406002900d00d00946a00c50740303ca42181c0140c2d10019900203444814442840e50351805800482004c0303c14002c550002552600c0140070100c10f00301d9590000b10307003102041121740003540079040c0d07081860269980c0e20250400d10032042c900c3d040004a440962040c00e0325400c0702641c1c42d0710a6903144000503a00c04210510414960310310b22201c2038030405112450701e11414a4140100d5640360948004041c0041a03001318150b5021181187d0680d0011441c892241030300e10070042240c00f0660200c64030301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507395350 1250 507394100 507394117
    0x5011d0f0406050a0b0628030e1515031504020f060f07022b1104060e0903070813050a14040608210309010b09010803070b01230d151b0206060603041e0503 68
    0x850000e181d90307c411410301558805544105403800300300c401c100c1035050303c103e00310200080d00b00d00b0580481e46419030701c8075001195500c0050012103c4000b180c60020342980e00030305040c50604000031864000c00c81150902c080c0c440364108042c07112141800e00820714000c1c41502d00101c083e2124540c04513031450700e01805458041110141003900001c03901c046181c1c002c5042510202d140303003a030303100345000f0041000110318080031500c2d80101034020a401c4c00104400650010381d40d41c3d0100c0c424007515003150b50b5010900600f04000440d602c0350b0001e02181c10000c010903c103052500500e24007041c4c181101e65a5032035860040c0180080703106564810302c8003002154400000001d0480c9920843c0d82c1c61003640c03120501c020000181c82c02400415184100c02c82d81e00f0810310f4456110710a4070ba21044490f03003d5410180d405059001c0700400c4d23070700340780000c1650400c145900804250fa180349141016243c445500311040710340031038428114883e400b00101081207a1202c2c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507396600 1250 507395350 507395359
    0x170a030c110f040c0309140105070207210503040b041d062b0602041e090b0306182113120b0604020708040305031617160b100b07050105011d0f0406050a0b 68
    0x480c8401e601a00810514a0a5600030780031001f203496241f0511031680526041e0b001000e11a140981c4814080310050850326090500314002000800410140c4082c152500720301d43c5035410401e85203030a0741d6009070b80480303c600313105005030f07030f11200501c2c2d400984140600b02c0703d00300742c280c00d030a04074041d100911041c40010001079400340b4009441c01d0842d48940b403050340f42e940c1c071080291040ba010140d85a04080040b59060304001301e0401803400781c1742561058150581c3c0b5a6070702d06084503c0c070203220002000b9000c240641b24034005007040c5203000d903454002ea10742c020340407001000307103000782e0703002070071078240032807501a14000c560041c02ca0743e990b69076900c0f0a030014080747c2e084a8950001900fa2807c0101034191a1800b045a03480b00030a5915115603654540140822a15400c803e9010031180d148900070b209440c020800803d00d94541030b0340c000c1154a07500300b402a107030580c1c140710b2310b0700514030140c2c1c009070040c1d80490903444d401c0540005007418036450354807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507397850 1250 507396600 507396611
    0x18030708040f030c080a03080f041505070806010f0906050417150c0705060c0f0901030f060b0a081608010303050d050a0f06080c040501050418030c0f1704170a030c110f04 75
    0x40b00d0307030301c00380055030721580003205429030b03031081580e407801c20003801800f1552100014418160766401194010f01800401c50b220203070a0a600881d50180c0f030340c0700021440002c00c005035812034606441072407245407040a69107007840090540c020783c000c000071100d60120010410b03004000444031a1040d9298282c641002d000e8028558001c00e0b0454441c0103000000b60b02a001c0b0003542d8280b1907a0802916107003c4c040110001c010a800d03407190140d9071080420320075840c0703000c1c0100503201d841c1c0e610316081c8101d0010503021800104420000c0d03000041c00042e40c0401950b00c441212400490780380c40700d0b01204090410700d1000c5811524040001032010030009000107451000e807000c2100781d880d44184000c2d1041149041c1300d4517182034882e8002840b50460702907480c0641951451035185550380281c11000c050505c03035103d408101803054010140c80e84c08002e00810003003100d41410755014100c0c0040d881e01a1102d078140005000a45407000b60300a00c4130001d104000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507399100 1250 507397850 507397859
    0xb150a2606160e031605061b0d030b01020f011b0f090503030703030b18060a0b090d1e050615150a201006050105030105130e120310030201080f07081803070804 70
    0x120310829400d1980000d500d46002411818003143c10450581406204441d00781491b050241c40e42c803400c00c8a03c043c04203030000c003000000740040800c0d46580da9000c030b03a141c0b615000a03c2c1500940c1203d0280c0d00d0400d000c5150402441e00403050f1f40c180c14044550700c442c0005654550342a40a1a050300000495070209035040d0b00041c090407089075505600402c60342040400d100c121107407a04064500ca050003a040400c001e090503803001070004481c1d46041d5644551039107030030b2070000c1c02840358450a00708242070201a910002d940c1d40019484240000140481c400c62001060480d0005000001e940300e110b04603c10703050040b04c602d04004100031281c2d150b940122600d541807800601285a40c4107070101c0e8100c820003403140f02a01d80d0303481d115006058840c045651352141d008107405900c1900061071003011203035a0349408929500001d00b411100a0180707540303003501070801c01600e8002c44190b80240c0f0b919084900c07448001401c40c5140710329440a855040c01090026 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507400350 1250 507399100 507399121
    0x71a0c0a05072d0501051b01060b030a0e240703060b07120e0604080c13090c03081206012c0604080102040905100603090201090603020a031509090b150a2606 69
    0x11240c443d58007181a008410503410241d02241514003803060b100c10030043c540c402c02c0a041c00e40c07800d21464200d810700a00c000c0c01c41c3c0041c0c3c04480c124802004101d031290982c82076445a040d04400360188102c4a0315207080950700041c900b05005038580841c55203442036125802030410f0030f1001d6518a414207000d0b214403154a00040050000400514641030030000ea40845005100500c40c0c10140740c10400f0400107000c4501c0ba040c6e680c03107000c000c01d440c160740100841c0500e64031640c0e280703c00030f00c2c0c000a600406050602c514195604856040d0200380840041612600020003510400060b0f46200b0303940000c0c001c4d03002040100b0014110f90090780a141c000c03100000f0300755074642c241e064809420010b40403c010800400426000780c0041000d107141d442d001a010640182c81006007510b82c202011031035a48500000b000305a20000e900540c880b40c0001300c8000250026080340914000c0820700f440c000072101c00055404503806a401e404000d5036101e103050040c03203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507401600 1250 507400350 507400363
    0xe07080c0a0503060127020403030314012102040203220309030c0801050c040510090e070e180103020d080f0d0c050d050703090803060111011404030305061c05120c0a050a0b06040b04020c071a0c0a05 87
    0x750701c40102d03340001690b0080031004130038440300c48407081c4440156003c11000f9000100540303c81c1180c00071380241031060040040c4070740c1c801d403280f41030181503040403041010141c028100a0303142400b40900320500c40103076400c40780100d8445180c90300b00582190100030503401400503207032600c1441680f0342c1010004103480c80644107161081c14400800e82c6c2413000b0700c03000e0b40000803c81010080790020b4010520b007400040f4031485d107402800a28100c6030740d9000387c0002000401c202c2d40c0e1040702e010707081d0445044d240512040304951660445448040c102c03905000031021202066407003904500c000d03500020301e511507440c003401c014020f420100d4480348149007491300b003181000c1502c0c11010351600040109100200700d1001201680201641c0119111304031400300015000c000701401948546202200c0381400780c207000c103540309242101d10890051003000d42d80913001070743e0005c5a0080010441501e050a040d20042c4613111010603503007c1c2800c001c044c0f100003e510b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507402850 1250 507401600 507401621
    0x30418090203241e1e0414060405070e010b0310050108100f08070602120a0518010e030d1d1c061113060801030b070905030d0e130e07080c0a05030601270204030303 72
    0x21555000b000c07480d0f4016440702294070b42000360300300c5c10101d42c04c21000c1409600a1042a140b1502d0243c80c0c1541d181030801c5030103c07071a03800301c6014010504510030440c01881104103d0b4218200b000da104c10301d034200d0003460b040003032120000ea9005030302000280108003600750400c0362610f41c0002c41d2100c8450140c3c00142c031401045801c480040c00844d126a441c039a00c460510750010382091030198003d60a43c100000a0040021030b501409031881000d002e8451a2900340351001c04403001ca007689180e80720340d041c000c0906c01200501c94840c0c000d5131203c00010520442500d500d6a4042e4036080321075840b4489000c40c48540107071005060301d01441b64907075150f8880604440c80300203805120740540000e04045200d50240c058160300e0300700100140140c0300b110f11188115070b41000c0404540d8031039241002298001c1c03100540c826001d40d00b4511480c105004a03907514410710a034265915010b06141c91a1b0544e49100342100740c1c2207003036644503942d08006002d000703600341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507404100 1250 507402850 507402871
    0x62102091210060501051e0310170d090e01060543030909020f04030b06040b120c0a38040e10090e06060312090111151803041809020324 60
    0x2241e158065820788440803600e42080c004910040404481d5808c00307001e21042008820000c1041107088444011000650004261544035980f00800764a102d600840c0e00c2407154005000c0d80340c0c49803c4400d10009031858220b0a0341c40110415102c0d40040c800600352454a8912800e0b4080c141c032880030342c0613684148501e51034491070022417040494110069104100c104001415411640d500c19802400041c1d00f00c108804961200003e07410080c00e900583c0308800149810708080d000f8051912880c900302200229140c081d0764803a0005002d81d000150310b56041c0700d02e0b0211000303803080300c032103010710308010340741000c003190301c0c050b0b0909541482c0401d4050707440003c041e481460020000c2c00c26070700c2c103032640c10140d10501c082810040c170301c0c41002e00584c00b0000b070400000d0841c0060310b9450800c64615074541c803e4608030305604104030030094010a00000b10088a540d28005107100803807000078605034240319800b69a40700c08007030550f05a030804125109038225603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507405350 1250 507404100 507404111
    0xe0409230312010f26150108030903210a0e0303040b0d0209011101150303052d04090b06041d060d06050f07180e01030803090304080601031202070f062102091210 71
    0x10084d03000311a03000c0c4004800d05400c4407503145100711002002290100161a401c016428900034000300076004a0629400061018604d08003003254202c45062030250f1155049403c840305001e02c1141300c036100f01708e8610901e155558090045500800d840f4043c1c1d82d41d41c140911480280d0020040140821035525418001c224180589886588002c064580040c1166419030349038200504181103240c100b83c420383c603107002c0181803408206d4007821a03110f81c6444146800d84026800c9a030188000380001c101c0141030040484922070300d40645512562890f0224400448107000500724509002c18402031140c9528500d00450301980d0345008801c04a0041400446911480c08454180c0004101003410400550f8011600209491410356600e5601d0f01d414400e03041507030031509141601640741c0c0c0401800c03000b80170070b243d130340d035203624010010f00351023400100c00402d0002c17407001c0c400c0b42c203007941203c08108009042140c0081c20040c0590b641e040c01100440f00b61424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507406600 1250 507405350 507405359
    0x101407120306060c1212020c070801060806100305061815040308070905010201150506030903070b0412120c090603020c0109051905060a020f1606090c0b03040204050708070e040923031201 82
    0x188071518400d0303080401e071034031791072030080454081d03002c0c030130300341045074203100d5a00050001d200d030b07000a101b964004140c2500740031b496801d0107c0940b000085080c41c036401c01c00a00e001c1001503109040803000f18592404500f03d0781050a203080d6403010400c03050070032041580040605001d180d850f5140210b49807035000580c201c0300c0240c41400c00c005510010441c0d842c1200c001c55100d01400240d81c105055591a0403030540e003034504407100c800f00082020b89661200f08642c952050b10000c0c02540c5003040080e00d000b0480c0105410190001800031103c0802d41207042840c0d0b1100448072150240030039000c60038110007080702c0038050000402c900e03042c079009135042958a06441403400c580c00c01d0100c56508a903030200c51035500c80380e60700c01050105072070a0041150403c20b82d1359240c244100400c54000420041c01e200701070081c0101d055100810701d9681c03505841c00100b00025082500a4450901d00c182c06a120040b108451210200182c6140084040320701026601c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507407850 1250 507406600 507406607
    0x315060f15032a12050601320a0525150209010e12010204090c0e030c010c021207141807082202130207030e030f0c060f04090207050c0a0801020a050910140712030606 73
    0x186c4d5142c1c0061401d80c0c035068010302c041380c580d09030b1803c10462910960400310a2a05800402107180400c0002c43e030120300f00004045454245135510300080c051200e559581800c40052810a40841d408124500316900481035540040b000500300aa2642c8440c0141d0107903200f8055403400604241540344140c0c0190051440708600402520b041d42c200c00c0112162481c42d18141e9100c0501e40030890b00c3d00040c048640904075420803a004c1c02100014055402c4010000011100c0701c0c074104450320398400d40c001c1c0c00100d060b500c404110042601e40e5001d0180c100d01a42c080018035140303003060003d900400021b4481d172546100304003c58101501c4207800c401d9000c1c2c640001d5524101ea1406800411441024200796410240c40e00342c1401241c2000c00100ca40d6030240c0324000c002d2500c64603c60003851000002d40c41c20564070300041c61809100142806400c110b401c01401c40c1c0601812300303078110b041c2d0002e511041c07241003c1100c2c00c076802c510f8000c246001e0011618620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507409100 1250 507407850 507407861
    0x130503251b090c11300a110712050c0108060415090506180103030507030513031a0f180c061c0c121a100c0204140703060315060f15032a12 61
    0xf030300a0850314440483d142454161308400350801c5d0016014950082c0501c405014402c09650b546100c40c1c81100c1100c0c6442815004044000703026291071001640c0080c640540300800e20701b005240d01c54102040160035001c00403c80082110400300341c03040e0036030101e40301c0d60702124007241d00541d2400700100000c0a0102030300052040101c0030110f03000c0c400a2034030a010703000c461407881d6613484100c00c030110402c04120100ca0001407064928290700403a40140c0c0380008488551080e8001030b50b20108128698003580011801c200e8090902c100a000b28010039014001c089044800a0001d0400440441e4031403800d551502d0301204060f0544a480d03000e807071480504206d21055881001000b401c9074482d8076010f210040c00c1d141c029041c0240825100820361608500c1d09501042c140c0b030358003100515104040240c0e46c00d41c00e00104a80c81d40f1503000320400801c0c01200503082030396455040c44d0b0394141d12400e00c02100e015800e41e0303806a845840c003121000c1c1e500f00750b60 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507410350 1250 507409100 507409127
    0x30c0c06060f01020c010f1701030f020f030724020106180501081b010801120204020c011d0f1207020d080c2b03050f04080d020c06090109030206130503251b090c 71
    0xc0c01703c000601294000c3c029203102001500386140107078080403200c51000000d03002125960f030415040300442c10f100e031446500701411000381c541282448840c2442d40b5010041514011103100b054005500071340c0303c0c01c0034200c10303812078015103d104c603980701600c401c1c81040c8062041060b08c004042c0408083c0400500595640c17056902e41880e280c0700074a09030040c0d034025401c2180600d0b090f401d03c50450004400d001740d40c450649001e880d81085844000c0c445e454008880410020107110115000f150341207807440c46514031410007103468050610300c000184241d80c11310081c0b03c04110380d04000d03280c001400000d45550310781101a102e00740d640c01e080a201202180000e84201d001d0152111008401401d040d0396003030082c50700109440d40c18040c1d650384d2103501819814022154800f011500152030402c0a640e03103503032440744948255060b803000555a103035400b00c0364031460885c4c005a01007000384490385801d400070700c14490031001d249454400d4014130302075104001c100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507411600 1250 507410350 507410353
    0x306041401120c05101707110d020d12060501020a0b04110312030405100b01083108030f0f060114210708090106080c15090a0504020408061e0f012603030c0c06060f0102 74
    0x44039214064031b134040150208044c001244040740104600304403180b07130128a640280b003003650508000d0700151b001241070175001d082110071700003a40c00060050342036a00890f001034580c2c0b14100100d1400b080d00500358980901403e8441c1f00c050a0003440c0284e016506036230740428103001c07903012100d643d4902404900e80340001007980f14030080701602154200403403445007010901c4400142c02e614821a0f40300c030b000c010f00090a51852001d54409000e2099425070300306070300040c1c200c01d0044103800744080001810260302e40030f540c5001020300708020b030500a0410040c060141c0d24110349160042d0f1900c680014100d0340007030355107803203400500480300300d4407070100c08801540841c610940024085000250649840c030061004120007000b800b00c034142005500f09107271489080d034204c9a0480300f0f01c01d81c41e244107a050b04664068100b001d41ea500340000b204200034070b403206a128040401004080940b0070000c0148020b000c041d26501d81e105420030041400101c06030b8010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507412850 1250 507411600 507411617
    0x90308010605160804060c150b3007060c0b09060103020a0b0c0c060703050a020609060103020f040b0d05010f050115020708060403030b0307080f03040302090a05090a0303020306041401120c0510 85
    0xe000e50b0040c8411190020240f200001e10344441c01c1ca94865800100081d01d10320400092041040900d21840e01000052042c3c01c48000045c03c1a00c407801c440d01e1040c44111560310241460170010602000c2206039502550b035440007500f0500341c0e1006580040031640050407a520100da5181a00c0d801014940d1803810700d400d4007090f41207504054002d1003554079020003952a42d0107483c143c3d101e03aa076941d03684444400241000f8000c0e064007001d901040042c00181d91308170303648000100075038000400c81d820300001a9200c14556000d0039a5113481f241c8001e000e10360b08914140c7d803c0d600303000f009051500040f6030b01c113807034810b549164002001142c0024800d41141505030401012201a5030b16054401d042a5801c1800c2480d9880000c0410450414007a407503880600a0003c00442c074051200b55160a0024401401c040c0e00000059440e501c680c0280c1c4100c82c5000180d4031507850307018202000ca41e08105540030061004005003a20709801d11001c41d001c690340781d104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507414100 1250 507412850 507412859
    0x91407110604171809040c031b0819020d02092a270103110c030a0e0904110112060b0c0708010e0c100809070e190c360e04051c0309030801 61
    0x10207401c0f60840c083c110502c61340c2525541d50f1251214040c1e07000d80841000b052461a0181c602038044a04884104074981c0c1004154008104034100050300920386516129030b200048120b418040700a61000c00c0400780300c480d07000309092a51400100d003c20300491100305401500d4002c42403582004210b00b8151740160498140d946940401810b010410800c115803001281e044564242c2c01c40c1e00c0812815012070744980520004003054901c00f0b040d080c10385a8502d40c0070141c1a85050000e200e844400c2d040c595071201c0001e142e4a8640c03910f07001c0089a99448043c00d1080418540c01e062040602010228404010381402440d85076844580c02d4182c1e10008000c0c44400f26001da01c1e400507101000a0303481d48035407103084108003d080800e211004542030880c100c400c010400c102c2c81181c9041c01c2d881b01c08040e400d010b003000c07220580c1c0650800c5416030008404050035800f8003080110000d80301841c40c1d6044180c101307404990074204d044400a0340041d00103000e100c0100f2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507415350 1250 507414100 507414143
    0x30e0c01050c0304050604060c0b01060c08043c0503060609010b1614060c030103060c0f052b06140102060708150d0f05012409090c0e10091407110604 66
    0x2000542c40203032800e280c0d031400082d0894205510010103e0b0745414101c080049911509001d421039040c1650440c0c80c82c0c5070f90382c1c98080c0d80960000a0a82030704060302e000d05401500d43c2c9c84d8407400540e1f1008001e121a9038030500c0b80308250103882900041005440c204100ea0706803100600c0c52030504600c101c406100c00e00b41002501c49030581d51144140c1d074028000c4038031440b41c0c01801c1e645c0e54910319280e01120750700c0c41580108005c130704000810319401801c0f44c5000c80103031514400d170100c58403a25020458500365846807440d15500046241c080c5801443e102c4d000d8007a5450b03036840050588140000312480001c58105c12815501d5117490100707450624014030010310201c40340e030f0b915404c41d22018441161628251910340c4120010030002c40500800101802004200d6954221501940c05041c04510007403002904a81e1070a000c04000d0688140500c0030301514034030300d14801c0b400d44818001615019a507442d1303560000e0850f000d0b1b03511042c003881e5041c01c0756514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507416600 1250 507415350 507415357
    0xb09130203062b0b04030c1518110411030a05010e06060304030509041e0f0f0b10020a02090618070522150c1b0b0c01050f07080c0a121b030b01030e0c0105 68
    0xf041241400d45440000c1a50008110701c500e100346c90380a00ba05031801d00c9400084060240c40d0b8080c00c10240300d20030044155038808496201c0c2da824401407001f00010b02801001d0450b80840d0b0001c41001320415054005504072018800e0607000d82d15240c1c11b00081d88412a000707008107208004405113405e240d401800b038003645201051140060106c0b100692351001d01c0121f845884591000c2c01031020711942c4510704049034100042d00e0b51210194881d01c08160181c81040d044000907615250f04841c001482d542c036410100b546005040036000c4e410660801d940d180759a402c1030300f51132b591501c120036a019402c200030000121041202d01c42c40c0c040f001c842c149044000481c2c00e40340c07400000d01030094a03148940b1040784d4450719003142c40050080c11106030301000e10940680000c3c01036000010240081c2e91816621801c0d20668482c3c2096903655140c50400d0340d0000040c146c2103107416156405200804d10900114140c03000040900d24641040c0720440c040e60042008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507417850 1250 507416600 507416659
    0x3070b04060f0501030305070c0509060f09130203030c03030703050105010912061a031204050414010308091315090519050c0a03090309030807061409150606160605010b0913020306 79
    0x440c0b064410750322442030781c070b0030391045020400100d07200302001101402d9002909007500c0241b04ea20313060f400100340300150807030140200c80ea030000c142c44003c1004c00ea0b0080f40c020301180c0ea40c0a02d00c00d641d9403035004840c44000a8030303140000c60150f2040c000340e000c0390300344119411001a2500e40c4001052018100320460491140c02c02450b142409800708460002d032469440c3c40c58642800240c4203000e50f0406010100401400091000c0c1c007500d5102805a070001d0855000b03000d501e00030b001000c655218402d510034001030300042604030511070060520032401c540050301d8140283d1b42d0555207042c1030365040c0062201a40b003130780100e040700d0203444d003901d401e80e407a10f540c03804c0d40c0481e20645801d074403020207060070316541010f15045022040101002400810354918001000c0c00e1607110386400240a64070007481c500820880790018010096540e44091040c416071004542600030010380810051000d201c3c42030381c1c45050b014081c0c410f0300c900303910005412880004c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507419100 1250 507417850 507417863
    0x170403051e15010312031109062d0403150605030109020d0b0c07150c020d1701050d141e060606090a050d03051e030717070e0904060b030f0a0213060803070b04 70
    0x400d0004540c038402c00d00039800303584141039010049400806841020f418076140050400c640760342074489000712200824650109907103840850460b081408041800000801000ca004000d2100540d50850070850040c1e080200d00e584105060a898a0306006035112003900104000700e20301c1d10301d181d8094140b004c250324008081d0f0311f03480f1555880070b64241d01035076164660032440d010054920440c40a0408007100e140c00c0346140c0c400b5405005040c020342240144c2420003201c2c20a4540303500044040d00d60310710315102c5192843c0d800840c00300e42803251201107035041c1000130459410344005880c00710400d09100510000403181b00c0110100b2404100200400604400e2148044d840d010031558a0600b60002040002e007130041403c05080d80042c48510340c0c0250040e0400f140c1641c903814140e8890400300002d10680b01d15503014010005840102a000303d90040c01d548200c3d031450718242400050001c886490140d0300d11a4010000030001c100224050360f4414860607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507420350 1250 507419100 507419113
    0x102010204120311060f0606030a0f02040510020105040203100e07030308041109070f02060a05010609090f060e0c04030218040302070b07141623010f0507030e06040b0403170403051e 80
    0x82e01030040846a00c1607000135402c40c0000e4101c00140b0460382c001c9041c500d081e58608000380025010711000e03046050701d503a01e00320350650b000a034060340c0043c0070081c0f1390706005160303040103406014210b0f0304910078020203030f02600c07080ea030344150b00c014900200107020403810b56500350f40b0b8007409401640c040e0380c910702d805455603803503202c40d110f1384059842c40701e005851440070741341003006000820701c03c3c142001404503a40c081c210904132181d111010500c5100c08149000510f1036802c0b0345002d050b55004c000c07117041002c00030002c0764030aa4010040c0d0f0b01a51604c28500c8055900038010303041650100408881000501002801b50a1807614581c2c038600141c03802030340d4000030002c0c0110314400c108000e61906110124404500407450000d4000002449040480d44001c00c0c00700c00702e43c0ea001c0c1881100000c020102c045c014aa480b40c4443c0f00a003e80c1151204072140300e4902d400c0044010300e5810340d021240e1100c001e001c0c4404d8100c244101e241040d060307011620452 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507421600 1250 507420350 507420359
    0x50304140103112101060c111011071707080c0f2808100e0a03170912120640320108070303050415170a0c03050a06030809040504020102010204 63
    0x103c0c01001e25070b0300000068080030030b4081c5007600800503030105044c02254980314000c249100880305900404440007a0043c84000082d14051100c2d00708604521401501241161001001482840c00c0c1002c448060307550f00031355561100361011450300705443d08003d101c5d03420084404912032006a41c00b92140c4e142c200c4010b41c45615510040465118007001200d54400e80705585410905001416440c40f04c0d840180600c100010400d1042c0c0300b040014804d0b01003400000300e014a00351000786d95a1284500c940d001e81c044ea1250f100da81c0002e0b09144000c0466070b080c81900d00c011072101c103140401c40841c10f10000c591400f100540b80c245407a21900d04100b8002030700c0101103864502d00070310015034a14503050700700303000507400120140003094104007602c080b030f0302d1020a65041f41810400311103562450300025018580e4806016807082160400118416241c2e0104503d03600e858034441a11114400585400d40c100001000f508054200c136a01074010700000d450071307585 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507422850 1250 507421600 507421631
    0xf0613031103010e190209010501110c090c0910020a1e0308190902040509010519020a0e09180d020a120906090501181e050901090504021c05070b0415030507020604050304140103 78
    0xc80c4011000217a40c45000c411807503c10b22a6014000170328000011039500c00e00c07181d45100305a0050b100d055000300080903000c589048940030303c809403c5640c48440f8020181d0b81d0001c0c201d0490f003020342000c103403058440081280c402c140d01595440269212000081040c5400d02414410540c8408800c1c016881e10f000b00c0d070140000000004107441d14042d4031406034200940c9981c1c00d80104401310720164481c581596003032089400c0c0b19191100c0700d1920b042050759898041d40c0c021a6441c08030240c010840300344050140c2c0c0c0074034050307091800c00c94020700d1a00400010a00f803000a000e25407141c80c040195071000c0e0300c0f0040181c1c44a21f20f0700c140f22646101000040688018401d0b2700708019600c0c0102a051000c0c82a4140b40c0c0c0010080512244200b8000750100e051006104041000304c005040c0c160006540d0b40e00c644ad800b48281c40d5003070003000310b401c09000c82e581510001d452481660044042e500b4541400700c0880502c01031070b6481d0400d030311111030490a804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507424100 1250 507422850 507422863
    0x4030c05100212090f120904020a0e0d030903230a030c020d0b01080d030e06060a03170f0403081305100f110114150a060c0308010b0901170906060f0613031103010e 72
    0x488070100f80091412500403850004404948031094110080c0b0078106410384056a09041084902584070302d01346034215a02810718441c140d004c504c9801d940c1c103040e080703419130b41920300400c92100c229600b0f400e00c0c504040e0410140a0340c1e4805141c25001c6840340080da62800d00c01004041503030001c1d2101905104203800c040c0d041c1d00007443d400031030f80d05441000758044c3c144000e042589044400034180240074032003d0701541d1130b0141c80003d9104402110959510200076035225501c034104006540c10512043c107501d6408440821a4600005c500b290710701c0039a1207050120b110802103c01142a421518096407103543d540e0480480c0d8a42c54400c04420104220f00c019600400100c4042c80d800b4a041c041c008032480c4c0400c0d0b00072245415640c80c01941541c61441c100100d8281040040303981c81c000742402440410314010541c680500b07000c49507004441840c0e02080038511501089000e10340382101c00b04001600b0054105942c44014000140c000180c540c00e0b05040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507425350 1250 507424100 507424117
    0x7080c160801061409040606050306070c0b130f0f080d0c0507350a09050a14040b040606050909101d04120302090109090b0a03061b020105090303070804030c051002 72
    0x1002000d892095140e5695410024204a4024443c40c3d143c1003200880002c0344604d03074026208000001c00340000e03600300000429000c3e0440394545080c0714024004001d0090849610002002058a1f0315080b82c541c50015007102030030070001803c3d80c8801c0482c819140c00c50320140f0911a0308140885846601064400343d00d500e03980d14054900200c014606501c010b175003800300241f402403607940e807035450781d41c410138184681c1c0c518040c90180c5400e41140d11542d44810f000c0400304010f410b1070b410501c4102d00f40c03000e02101e0003407010081070304d000780503681c0000c8081c810f500161414a080039085030070100b40c4603c8607224003d001c1c9a00c40c800e00500d0b1000303102c3c244130401000b52901012a61a490110300384002d00c00006d042c0b11140c0319140811f9268007404859130f6518580c20000c59004204003c0b00410551036110040f0042400015504c1c0000040450201100b2688a1049c6651b42803c1d941c8a68040c1e030924854403003600d09203e105c1043d5203000d001e100404504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507426600 1250 507425350 507425353
    0xe042406020f010606091505041e05011e02060a0908070b0405060601020f010615111509010c09211b03080f1827070507150902090106080f0105010f0507080c 69
    0x6a050200107464400710503448032150b072401500f00b00403944150244207591102a44280005503200101d03070381d00558100d0001c142101e05910303410f00301050000c0c01c40e082030321100710751440034006030142c00c0c2111382e040140c0c1109000806201071640001c40e12881500b0715401e044468907500707003c08080358210703a15407182003404007a40e010482854030210007002840039a0034691090b030308021082e8840c0900800d0303080450400424011448545640d00b0565a0f900d07002c03501da4085c100340c0302d01c803002c038941f01c0002c166440d890080d61400411540c0c056040301d00e84e40d445802e01001c0040040c100c18400e00440020202d400421840071020f481030785078a0741e03e02c1c485c0340d1341d200c40b5620311640c600518607075003107480380d400c002c400045032460380b00d6a111081a501840f641c0c0c0c00030308884000c41c10180f0b40d0b2280d0b0100200e03a0080e0f0b40c040e00350b80c9440c400da43e014800e03104148018610030041000350301c00c80d0302800c08141403801c1c90074104681c0d01c0003016040780b615014903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507427850 1250 507426600 507426671
    0x5010e0a0314070c030609151803030f0e030412020d02100512060a180b1504090f0509030307050f25080702040f02161106090907080f010b090108070e04 67
    0x9050340101d20b540c420215000c29480d0148540d2081841152440000c00c1d0b151546600014014001441481542c0d608028081051600c1c54071940025070201180401e2610451103011501d5214200e54528414025490b0508054101c07840c00c4550500701d0380301c42c0007c0000016101c1d1500d220a5010707980b100c988070340c24144607400c4500001c240038014564800100300d910901c0d6403650302141c2c5e002d00060842c402e41c0101d0b2008400740003107106000001000a0040b0305640b004c4a0000030340c0d030800160b1110310f04681c40784020b4a0240010f001848481c3c10000200c009068107208006c0b09094500d503404a0710166076400340940e00c0300300201c0c480d02542482c0c002e611001d111200c1c114600b812440d100519911600c00203041318950200406054540100310f82408100401014041c50f15200050107000120360b040c0608208100000c1c40030f1b05102601c0301810140c560401c1c0d40d0300c000e02103406120001401e0b40c0140c03500500e802c5c04d0760240d90b4003500615201c10608 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507429100 1250 507427850 507427853
    0x806040606121a0a1d030d0f061406030709090623032a0f04050a0c020d02060c12130f05070819021c030c050f0a02130203161b05010e0a 60
    0x1110403540c09a222039180d82c5480700010103c00c0080c03810200203030350081c00e4071401d14410040806a000108102d03014400300042e150000152042d1030401e001845003141d218880400e5510500c03810f244148031000018840c68904090b6501003020f1801000042e500c0402c00700396003403036001907420000d08440c0441074550800d090002c80307065008054550051090b2960300c00c0c106000c02c100d0740c201c00c03c810f0a43d01c0c00c1c480084c4110090042c4054100a52100000c0c40d00d24a2500584a42020b04a03000d00118045105011440c145420002507202c8a07142020003080c0101d428000046240002d00c880e089802041c000d8000f0492603080000c4280303031031a5201d42202801081c0d6560005a4a44500b03809450803000c0c600c540500914058520340d246400080460058064124003201d000400c41440c600131108503011504ca80d021000702c0c84291030341e0001200c42c07450040c805000b403081c0c50007241090a10040e20b4a107403641400c69501c070b00300303d400340c201002c000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507430350 1250 507429100 507429113
    0xd090b0106031d0d0e03030903070902090306160c0b040f0210020607080a1503080c1e010b130203271207030e04050c0406020601092a080f070806030a1103030f04080604 74
    0x42150710f00500500c8090100b48010350365001c0440100400c20b2040312540140c805000343d81c1d203008041c0484002d9500c4542e040c1c06900903884081c0a441418001a10000d0505c2c42c03000045042c1c5030b103c110007803a11800070301100184269241d101d99401c000068440d80703c00c9080384556800781030b09062020004281c283c02600c0e81c2c55590a1070800c2200c03640d0b80c225641240d61041c13182d0f9681c4014040c541c1044d074a1a04001d00900b80d03183e02c400080190008032100c0401c07207503804014000384103c2c1c00c82c001a40d040d61141d00060500c0844501c100299905000c1c180498128507039980c840102c0e80c0c0160300032000990101242611420b10703000340c40c1c0029803000c5c0a824207091a04c000c0d500c1505120345400240c40b28140d01da800c0060b000100c210f1207010354809020f07503000c0301a00c518016510088030b41417100c0041d0f03d040c441e04050b0300404004000d0442550662154000340550648803903140c0403c00a55000354203490041c170041c49641d010b0300c4a4505402e198 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507431600 1250 507430350 507430361
    0xd0b0603030f120709350c12030a0906020a0b0f0406060302031002070b1e1611120a0818060a020f09030d0f08011a2b06060918060f05060a050d090b010603 68
    0x1070010040c4890080300a455500202440d14041d1b50010070244800c04110703e003501e410b8102d0340140c0c605800500800002c0001c0004070303180d0300e40c880400c0c0c1e140760481e03580c403414002604c00c084070400301d05018404075407240c22502598000c510540c880d0002400c0444004548a40e075500060f085e007000302c460303966607100d11005c4108102465101c000d040c0c9010040c1003414051a40300d4040c0d515003c0c03054803074807c4081c0126010034080582c5000d150340000b80701c2001c549c5507000545264650030681c00100c01c8140503011320340703c070030590001e5000202c80c03c203000070030b010084894400700081c0103903088582d1113000c2410308c1800902428010780210307105003203501403059003140070011140e2070b21600304402000307148a2200104651a0b50340f01484038240320700080c0c059030041401f000c1d54000ba0310000031003640e840072000c541c800e00c10061403164207a010840c5141000c060815410241001071401181408060032140021002c03201c101500005014040c2d052060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507432850 1250 507431600 507431609
    0xa0b031f23063112320703050307060501050d02030c09060d0f060506040e06072f0d1206080d02100b01030204080d02030a02011a031c020708030f0d0c0507020d0b0603030f120709 78
    0x5034030800f0015200c5981d2102c50301580d00c3c134170008011203100c001088402403244a548401c1e04c1ca12a140c0c0341094a95021000c141e400e50308013000410740f442c10f41c140e10281d83d4002c004094031041d50080c0b140800c0c0090032540e204451040b80380115403099207501d0b01c50310501c800521481c208040104480a0401540c03155204804000318540c00040020f401c1a80d500060461182c1002d0380c26108868400510103001d07620401c03884070b4010010710b0030b80307104074070501c00e2030f813034a1b01e06580d074040f035568100590081050315015049030b804803142c440180f60161410343c07284101894007a40c4014180181e02c002003800700c2c41d60a1084d0022070f012485000b07481850031300001c2c0c0d40c907260580103142c00c82440100101038020840c2d04000d19828003666101c24100051020641203018180500d0b4100005005c200d0302c81d9007181c10a81d4020018400e81c0095110380c000340b14014030143e003500c001c2091131084e0720b6040c01340c43c9104d81c1c028518a0751800c504020700c0c0744a503500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507434100 1250 507432850 507432869
    0x9020a08030a0504290c03070209091606050315030106120309120f200a12020a0e01061b0f050601090507030e0c090a09020f0a0b031f230631 62
    0x1000003016070100444003200e03009101d458081007281c0304280701d0217140108540401000403460400400880944003c0b4022540d4400e1a40e405101036140c407464035050141501c007090a221050086010b941c000e02c0c0b0010102c0040f130f01e48082070840d02c2c2c54000d20003a801984004042651091032100601000c1009915507441c0b5a9010790340320010b039000b82028840003210f01901c24908490f0741c8444020181d10443daa2100001c60341c0e0000f0000f071340601a00c03580071407400f2103103405504840b281d80c1d0306000350b00e20052024248121100845141700d00003072500105904000c614080c1405004c006410708100d88060100c0e540104010343c01d401034001c00e2404e681c0c500c00d41ea44064151000310308a0310780d20002d1806020101e0042d03124509000c04a0002541c2c00a14491103101d4a440d8000305030300d0407540843c15031301c01c4d0079000711210740b00725581402110200c03261001402030741c00e066280d509a804201e68031980a822040603190480081800e400c05008151010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507435350 1250 507434100 507434107
    0xc120c07081c020c0105070206121f0501080405060a0e0304030501020307171810151206050a0c1814130509010b031b03190c030503041403010b0f030c0114190309020a0803 75
    0x1130340360074441a40c1814028007255074010754950038120b03103d00a0000900c80c0314078280804800c0700114603205460078403041c4001c1055402003030564000ca401c00c0042c40c056071000a04000303003450fa03180f25401e00051200000040c000d001540c000d0100d41c4a1001c0b141070b081d0408455071000304041d061a660745402003010b04045020907007a111407402180080402c030200f502004558003450030141081c5150062041950100340142950341007030100141d69442110f14150201840c041458181d104204928510b4401d860b02d480c0a4120105206810740400440300111620300080e51a5500c4000740e2070103001e403040110340481d010307a4030b00c02107009c0f07599515280459850034071640b000702e050100002d40040110b60203422281d455485031000181c888080d442240030f9800d040c0500c1c02840c00211150296001400a04c00d50550000440705d001d40d50840e0514050304210300c0d50f155140f00001c001001080c2c030081803002aa205120300400554024204c2d600f061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507436600 1250 507435350 507435403
    0xa0207050d1b12021e2a09010b0c0a080705011b05030108070501050d090206040305030d1b0f12090210170a020405010503012705010e090d11120c120c0708 68
    0x440a4500b0190001c03c183d07401601c00c1810780c50042c01c45851100c01c0f580c14400700c22044d00089480031046024402e82d0401c40342c61103405c280c2c80040344103500c95039030801407020384104030240c490718a14001700d60070941d51b600c42400941c01070300c00340c40903511101d01d071404081d01d621203081a11646000707861585401c00f0140c031203403180507580c10861b0004000e404240e49030403500c0301da900200b401e952265280341ca00d60b030f544070080100b03183d8101080900c4080600d21200d440002c107840302141460410021541c13083c1d0301099020099981c0c0c1d0010268450b180c071100c1d0701d4482d440780704110300c0010b44190010710082c5292103407801000213001310b907030001c1603a04554003004820b501048000900e4004640740c60b0000e1007914101c0006250b83ea032219990007001504190356004240d00812a12905681046800d40c0c0c0b0164010750070905050040007880c8401042e5203512000c451415015400704c50388901d982d0050b0f0302400412014400305010003e001d000380c2808105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507437850 1250 507436600 507436637
    0x160605070e100806190305030301060f140c0a0f02010512150f0f0a06050705030c1506040b0603040b15030708030f0a0905010207123903030210090b0606031e0a0207050d 74
    0x4065074040c02e07401760500d028005084500c40030310381c044c0c1960b84a41c0c41741001020010024810b10028414114602e03410146100716007015040720302904a0070600d80311940e900100b80d404134104101081005c4e00098a50700d8a4064a405240080c0c105022001c0265142080002521400a00c1c0d0703440b1403a03030b170480324030111600c5092072500d5206900340035084d8040c050f07110705580129a40503c10b083c41c041c22030b20500341194104001d400003c14040719001c205c500038524020b44000c1420242d40c00007a03803021138002d0442d9500e54a03994083c0c216007040440030030351000480c0b0300c41425008181e50002d840300384020202c1c18a44030b03564803900749112010707000401d10a601441350088002c81141c2c0d00c04d400c1c0c1404040224540d03841c13241e94511082c1c0060256842c01e48082000e80552007016400c0800340025840303100030800d45038005046800003013611400100d240302180c428501ca420380000040e207640d41802d200c2e0501c103a000c1043d0800c180d0001e4100140039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507439100 1250 507437850 507437867
    0x60408070905070521010f0902180f03010e0a0609020f030307050712030935010209060a1206030b13060b04061a070501062711041d0a02160605070e10 66
    0x2044100840c0d55151400c080d1282d01c42e01c2c80595105c040c00100710050110951428122005100081a03440c0c3e560f904a080b030080c21800325507142d1170a1848000d191581c0c0a00603108001c0002808141d0110000e1500003c0441120381c2601c414480095203054504100e92103801d4003e145480c24581d245d40c2c0722442805040244040041000300b8940303c0c08450025140450040401c60703255000a00101071004810403044000c8519040030341c1c0c18002c0c0c03054404068000390a02460300416aa1070028035015000e881d501daa002000ca407141c12013500400340d110700400081000e0612000340d444440040b0b0280341441070400201d0124000304694600d001260764441140d442c3c1075001d01941d910020000c1c0140b4a440101041e160303048200c007079540410850000340056803101801644a5000306092142c2d08003480402017002e10b9007c12843c0005140c0040b40300c1e880280a00000b0680d94555a0010031010a80000b90002c00c458211101d481c41c00d446500205800e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507440350 1250 507439100 507439109
    0x2070b0103031209020a0e0f07020d080c0f0d111c060b03010501030506120a031d01080402030303073606030e03070b150a1214011b020a1211011a030c06040807 70
    0x80f5003041e0000c01d0b0301d0380180b0555a001b40b65032900383e902d0745080c00700041a24001d0030b0a00401c0400c982c180002102142004d00d83c40301c41d61a6200180b01082d0b030002281c01c04079000420801d5240c03402031007440e1095440d202102d4070b50207001203220b40022000c0b40b15130000d01d0600c0a000b1401a0001d680c1140d4092034041240e946981c0400c0d695428486003009603c2800c44c50003c250b0046030423022105041d1042014203044001150074010913280a07415800c1040420340f024031070484541e00c43e1020480c10106401e00c0d911010000381030040500c02c90070528280522945402194401c03002e41c1c0045003080b040745c440c0000400c0c007421400500c0041e0307c2c007842c079480d00054180148158401801d40402c607042400440c02211400c2d01e00c2c0d482c22100503010000007400300c91100103a0f004200c40c1155540342e1103850070070482841403000c4d058648510800900441d0301020791007600c0085072100d40e091524024280143c0b92141130b06200900c00c41030001440c44c100c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507441600 1250 507440350 507440357
    0xf12030a0c0516030c0605150d080a020a051203040213021c090510060f0e010f12060507030b1c0c0504020f1c06050402070f1101050a0e041e050a0b031002070b010303 73
    0x280d040d08820b80d12482102d0340c0c19819407000e005082810f400c83c844000c640e0141c4401d12041d1344485c0408010500204e8140c2e21045809428002ca2110340c01340500c1c5460f030044466520b001c0e19400d141c00030a07804141c00050010800c0110b0406901c2c41c01c02840c5500198140718405401095550000741614001ea6030744550405001080190340002034440c4401c00c02a82c40d182100c0810b14a0f000b446100080d600c0002042500c0050f42c030b007120010f10b40040d0941d5565500000b520f005042041016262020050b59030365602c01800303c040c42034802020301c5a2864101301c49000b580c46180300f148107020001402e101e603070856a18100c2d01030410322060b83e00303400e90018050303a04030b250801d101050403002c10480310f107034585060050b0000301407088480c00456840c46060011000510b44940c145400d003030540108001c150381208205e403035000f07589100b0890304100c072944500d98070340a440400742070612800c1000503c114040d85813941b940c440e20341c6950107220040c100f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507442850 1250 507441600 507441611
    0x3020d08070213050c07020a05090c030621070b09030f06010b0d0c02100504060605130b010905040902030c040e01052d01140a0b0a03020a08070c1703060d0c03140f12030a 75
    0xc66486141103e10503404020400003070074051000c01e00e03030300401400c030300079081001c01003803914005100c00d01c0b41014560161440c1d035418140042c540445c2c1c8640c0000030070102010a540e000e20030800a02822800302d5210380c940804c1601c0c0c00403848400003207402880051005220481c104d6548010788100840d0405a96000324074050341d190f03440610354601028401001764035004030040701c2007100e8001d940e0b00203c2c1d4281c11121042601c0340400c2001808018906080d00040c4110340003c00f81c80d1038245440210302a01c0c4c0c0070950090a035941da04015005048415802c5c4034454003125140c01003454102915180040c084c8080101c0810410606a9180f01041d80580803101c20180c0700c1c2070840002e4040e4120310341c00d1005c514180d00258000b4440c010f2a001280c01403001c0030100ca0fa40051102036001500c801d820051426400300030840308440040154400c0c00101c0c1452002c1c1085400d11300035164500703040c8c20103050450244240026682c020b001c1781070020b40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507444100 1250 507442850 507442853
    0x71a0f040c05011d1503094c050f1902040b1b070b040303091805042402040909080301050a0909021807020304030f032c010f0516060204030b1b030103020d0807 70
    0x61610300c0704e0181d9006022400e0060480703074800181d802800b80c01c1c00c880f411001051038030070ba0480c0d04007460050342c02e600340308040d10f2001c80a40c0600200000600d103036180d1030b0108261003085a10410100d4810b007842820001a0741600c5030030040c090850810f4104209140c192052004281c1115410220440b01c580140040401400b4844c0c155690715902e10b00a4903400e203c6c403035801c001c0841120002c2004850084030310555000c030907580c40401c0e0151458414000c909074030b04580c0c2c20f00000c16905150710a01c0340040c02620303415107940c5048200843d42001c0e0708800c120608001c0000c00589a2014041d03500103484510400e0f139684e041e0480c9103008039400504482c100301c0601c03041c59005190b204551400c201070f0711440c030149018001d030074001100a80052200101129500e120f800607160b2100300010121588400b5100d17001070f44c1040e0001d503151074404041c0f001d56001c504034404200c480034205402d56140d5000910301800014000c2c0c50700000160140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507445350 1250 507444100 507444137
    0x50a0b0c07080a0f1217070c0c0b030901060e0912030c160b040804090518070b0d0b0334050a03031d0406030507080f16060c0201110102071a0f040c0501 67
    0x3014001000407210540c083d41404030070089540e409580c1030b104115840e41c0144103140c01c280b014820180080b6540b0748080440b141007098600b0b90303011070862000f0031106078140040d40503440e2000041950740c1420110a10b440d0090a0071041d944000c0700040301c402d2000903242d0044d000f000c0c1c9529880a812b100490045400f0000c1081d84000108810001030314040c0087d01d0042e0400c000300e903070341002c00d20841d0009e41c10700b00543c4888401c100c84a4a8002002e0021440d0704c00b051010050002c24a0043d0121550300301003112407802d07400c031150035070b1310100701020040c40801c185010045030000426010103004c0085140c0c0c0102042c84200c906c00c41120003420402a059490508603141c1d0250b0007a42c0240c020a0b445a520304000074080a030a4500f07802d80798075620f0b011081e034030030008403800c80c140a180c00340464031100070300c007030715400b17005d0400d03121600b600c074000c10050040149554222140c0c0340501010800c51041007098038020308108500c2d85450f075916 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507446600 1250 507445350 507445363
    0x70c030b0712051612050601030b030304080a1b06050412063207050703081f05060309010c140403080306040f020409020c0328021902012d0e0a050a0b0c 67
    0x2600319032100051014103507009150a50030800c5610800650302e840034544d00406035041c2e0341c000100700203070310b01505046a000c242c115105041c0050070511010200b400c542056011504d10713080501110b0500c5207101c14500031460100300041c4242c2002d0010b00640614003c101c0c4910015160340104103c5a00c0b0f600c40030184a05c4074006100c400140e00300c135001c40780800d4940502c0010070760342c502400544016542c0350325001100e503117045000503010300108150154040101000681d600c40200444c050701c1003000200302401d840030060410b00064102403803102d0100310400102e445941a2908020111004075600c4140c01901c80a8061078105130700c020b100040c9980130050000050070005160703031b000251001c00c0116200001c1441040c0030268101520307020701c0050442c8a201d844e441414a0882d52402c0d410054003100020303030811140c2001c02d8100710644d040401c01c003104004540710040030f81400041510001c141c03265440440c0042a0f0b15015102030109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507447850 1250 507446600 507446603
    0x907090e0a0612050a031211090409020619120b0102060c030a0b04090c06020c04150f1701020c012d050705040605071103062e03020a1502010b03070f0f06050c0a08070c03 75
    0x5083c0e81c89254149651a900b08800840105064901c152032900c154000e11865035001d0307065a050010708020310001d00628007040780d100c1c074100694042400354104419403504a990b43c0c07000050200000001c40d04500b10442c1594000420008860460b404482d88840721003c0441e000d4000808a009040307403000c0102401c0000c503001c2130b0268005810701c80d0010840b024030000400c880e143c40c00100ca80510054143c00201c01d0000010508110b03240f01c2204000512308050380500c1d90841d0045004201a11070a612030791510042c51005c0c121020002003c11113414015005401c0c3e20540c401c0000380040420b4071030500842c110003441580014058614510305500c220340c0c00c90700383c845d08911000002001d100c600c6e080a840040c0c0764080d0003191f0f42d608082c440c84c20b042c1da80032a0000c540d03c1c3c1d0218050350b00d05000d442c0040490f43e00722a030a5040c841051180340641c2c10036005c005041c03086807022600040d040203015001035489598107a6400c003030000718840d400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507449100 1250 507447850 507447869
    0xd060e0a02090a05090d0801260307060908120a0c080f060105041d0a110f04180204091b02010b0f010c080f121816050904060506040b2206050907090e0a06 68
    0x8000000d4034a402c2136200703030580426900103040005090f03a0508003070182a00080c0c007150b0340003009001180c0038600300c4800046a080030066501d00003605d40385c0001300d0305210003086104000c40d10f050b0b00c0c0e420815171001400408150b04000b000140018840b0180102101c003280c5940d00900c100c5018140c0188040c00c00d4181c0e00c0218403851003038802d10390b81803030144122007040c0002e0a071501d411a1540c150300c0c1524190301c03401003000e09501c800030150308100000300ea600c2071040b4102414203000095100706c02502c00f0342124074074142140103400c40c41403581d4076a4020481b040c003036807201c042c40e1611034000b408101c902039401151a1400c0750028407580174440404800c00d0300000003110ba500004140c010418104d9200b80da030044001c1c1c3c0410b00082d8540c10003640228090b000040b04014100012080c108a01c0d1090b80421000d54401c0c1d00b103900e028410141c0000d54030240c441c280414028403009442c45511405000d0b6404110381c0301c030f141c0040008000261 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507450350 1250 507449100 507449119
    0x3030d02090a06020706080141010f0e0a050402180409030c120c11062206090608100806040201140909191505010f140f0d090c060306050d060e0a02 65
    0x840080d072148140c640314268a1000151080c800282241505c41c2a074501940f6441e00042d1404c2012270021810300300a86042c5145410b480f05801450300c4a1482c0e072855100c4c0e550015000203405c1c008101009152650b414554540700000d00488070160360051782c800d043c114445101c0d02c4014040c5d40036050080c2c1c182403540c4a014811014041c48030310141504188040c0e0b07200440d01c0d40100501d40300a9076111a2400c10f000c4c00403c40382c0310710303c00c0403c0700c103c05000892440d00188003191481d10140204d9520400156112000d172224281140c20440c00c5c07541e42c400140000d04020090350391142c2d100301c02c07041d211041405880c001a600f02540c60184496041880d0005c0500d000c600d619590b000c080300004660041c1c41d007407480320b107112048031542c0181103403540c01300080054031079240200c00103182141080c2d0b0000341900007440c00200016240d4040420035081c008280305903600c1282e2442050340c0000002030400324050ba050402d013081c40c0196000807040d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507451600 1250 507450350 507450367
    0xf021b1c052b090512160306020c010e030c070e060d0b07030c14070c061b0c09090c05060c0d2a03020a02010801060c0c030209040804050303030709182307030b0303 72
    0x410340380c040d5485040000d0126026100c000c0c0c0b02607003590000140f240348042126044ca50302c0c916008030030038240c0349084048090400003668643c030071111181d0001c0d0342003207808288182244144407a014602c2d181c03c4615503030f41c030f20042c002c034440d808650020401a80c2c92a1885000079404950b0404500d04640c000d40104448107000020038030900c8003039500890724007150b41665001c281d2002d8141800000c40d0a186542080710b020032944283c407010510103d240c50007004c0c000c5e070101d03920200d450444030058156000d68041c03c030a2080e5200322201180e8450304042034601510320601c101c0d04420f840c0d20032400f0210308000940d80000389980401c8144109000707817911001c69a85101c211400b60083c8800b810401c0007074018401454260442d941040c05803200b50304180c0c031800083d056038820b42d804008224003050422090350300c401c0d4001201c958400800c59452414140d20b0f07450322084002e01440c0b0840c3c0001c00060299102c1061010050100ca8407807420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507452850 1250 507451600 507451603
    0x901030204181b0309051b12010905060103050c01031119090302090a1a031c080c210703050f160f09180204090b0405060d02010c03020c03030d02040608070f021b1c05 73
    0x151100e04503d015000150b00c02140240510020183d00c2030081401e400034020100021200c01c0409510101c10810032504140074001c1400c0b540c000c81c090000c0b0752561624910b01200881494141810800c0c00d0880c003202409807101c5804640960a00c64172511040b00e2041460b00000d520000f90700c01d00c410b04441e9032141c402d088668203c03000d4441c1c1d000c00c040e9180d102045901c600341d4100e001110441c4121159030300314040320341c01c5040c080c0c0c0c50ba03508400000700c0c1c003510301d510842040091141c2d05000702c40d00075171240c44000b1981000800b91040445080080341440809091040e000e486000300c1401003011a1068000c420310f201081d0180d44644142c10900f27040c03031040da1040c41c0522034103000e0030004121088040541c0c2c010354464071349440960a60041112000c1240c81c117000401411000580c01691641000400303070a1b0040503011a0811170b600484821054001a003003e80c440c070403150100b0740c08003400240d22480803500020220b0185914507040090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507454100 1250 507452850 507452861
    0x4030c03030e131a0d080c01110901021b031b0d062901140d09080f040603020304120305100b031506041805010e040f060203062106100602150a02090103020418 70
    0x38203da0b00059000501420b006071986070807040c203014088074400740e00380b03046005014807511a01d0f071241041c541e2031580f4212044912010702c50745001a01554035a81030000c100281c44804010904440c40c0c00032aa64650011f207540d000e07488100041a01d036151218040443c0d407145062000052890081590720b4001c009a01b0544a4048803011980141c00301000410105030b40340c1018014240d09000e40302441003600e04a17010024a0070603000d07880100003a00ca10b4a0150307590420789052038141e020f03d542d0341c0401d49840306015214110010100448004186180d100d80303d00c3c001141d5503601a038641d5008200180001d03550000380080881c02d85402d4003041b003680d0b00c0e41d0358a0b00070800c80c0c00500e10403802c081c0d4070000d40944e016542103031001d0042015234041c011f08607041078440040844c03551003901040400044000c61101400c818800352600e04816204c60340300c6000505801062070b0040380c41c0e12aa44a54103a44c02010044820f00b032008000348100010031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507455350 1250 507454100 507454127
    0x103021b0d11030429190903020901150c0b04140a030c02030105010b031308071b03060207110423151f08090318010f0909060801060e0109150509090304030c0303 71
    0x1000c000d0b100034054404410b0304c003140c07081c12682c022408150141005418500c0242c20751540502c0800c03110b400344500240e800c3c081d5180e5600b1603003180100301e00b004059200d05c20a400300281c8035481940192459009603102c00510015203c61802d40401d5001c00502d4410303101d00040709003403541c400035000c94507000341e000b000b041e40ca81c030014006100443e00c0140408400c580e00d00003a00180c010207900f409030250341b01d00354070072008042e490385a0340140c03540f40d004111034080c0000001c000b03074480340484080207031090b110a81810098003800759000394105800083d101500c0325008001030100920f20200346001651100a1000c0007000300001112200002c0c11a0000000c80d000308020f4090300c80a031041e00c00450301090540421070400115002c00070b100001801644083d203400760003c00c5860a0280d43c21009005070b019001441c103000103412450503807680c000603aa01562039170055902c01c0d05c040c0c607510a41d0700c01031090880c00000810315034440411021036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507456600 1250 507455350 507455357
    0xf120106170a020d030f020106240e0406050f04090203010605030f1e060c0d02030a0b120c040b0406050904110312030403022103040c0b0c01061e06030b15040909020103021b0d 77
    0xc8946a20660745514240b0300a40000002e003c0c0300120f030090801d49001d02c03203440040b500039141d003230750980016814032188803d07210404002030107400c45108405240c0540d41080070074640000a00c9400c0c00e51900c07070080b540c522190003951004c2d0843c101821780035044815100c8040602a55041d21150411810081d000c1806804002141c1c4e0360003000d03d5680d0a0030180f240f02c04070001e41c0094501203203945e40d1103c0c0340305506c0b003d65040e2202d810402515a4203401024841034600590025201d1882e1500503c219a1209902c0e40c025400c9200100051491008a4508004031100c1260030101100300700800d80d0000e00001034020401c0c0f01b146c4800e01815001503800705807001421046101d00c184440520032000c2c1055100860021030b05999416400a0380c00200c1041500c000d2800c40510680e0b406009580c420041542c1c0042c41c1144100400e48501841c02807460301a11140180150384c801c5e01618080d1200749200391510310300d01007084d0b07145510561380020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507457850 1250 507456600 507456629
    0xf11070516170c1c0f0f0b1503100b0d0507090219050304050a032d02100b0102060c070611090913060b010f0203161a0708011a070305180f120106 64
    0x8000c12002440d0b5001c0801008220048031242041300002d1013010010a10321303440120004903190074400f51070300f401904800880d210718200600d02500082c80d0041c0640d1110402d0890f80380000c003802e241103207050020b0742d5010807000411541032010040c000d071191000108411710190300514001c0844034400183c000b046a040c0d80c1ca000c1180c0181c2641c000900f10400f1038020b6443e1070543d03928207520718406a644404030010120505600010380c007041d2002da00c0b40143c4a001c9030440c00b4001815103147c2030701c0c0b80c1c02512421400078015501d0b000c0c1c0050040140c0c05407941e810b4010147d2460345040600c0700c01c5090020070598409003030044003c401c1d4094810b01c0500215940030710301c0d03c2c2810f2000200d00d00312002c21686296101d0a02c0d0310014101c400d28020080347d0380d0355140d5403400290a410849110401c00c41440030070445000940010440c0c148420030328000790001c0c0310b980000c07100305280002d01c2d00110302808101054106600200542d03c10f104031005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507459100 1250 507457850 507457859
    0x304020a030c0f091b0c080c33060307050306060d110607151b05091e0d030203040e010b0406090e130c0801050105040f1a090919230a0b0a0f11070516 66
    0x450b21546001710002c41e00e02200a00032603080c000a01c96911450300302c8088032004d035100021a5221002c1d4048100300c03500c10310704110100704090b08420101c009042e014204000283c9601c006040035119800f0640c03c0c03000c0024200d92920031320f000030503d0b603c83e40141440300c410186030165154052818031620045030a1404500786800d81d0f6540500b051460300078880508071118080d41d5442c1000800280340c1c1da090180120035100e039000d503845030300c2d22608004007481a00b0240c6081000e220600000e42d0220154007190b00030302c441d80c0c1c50744074030483d00880604a2401382441c80e0075003000c1812041500490f0403502c00380d408100d12140d6020590445202020900c0750203a60064030740d5515203540d44a80046508080d1002010520410324589000c0003084481005190000740702c2202c100d2043c40594450025180358200c4d55164099614001c0c40c0f210115501c80c04100c08404a50001d200f204660b42110f44d10079407420702d00e0b5100d82c5949168031030402d100d070214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507460350 1250 507459100 507459131
    0x40308010914070c1514040c09060b0301062a0503030f0106020709110d0b0411070b0a060e040819021623040e120702010e0a14010f0503070c080304020a030c0f09 71
    0x91098041d603440000703074400d56940c021005c41e11103064070001d0b101e04400000d1421000d2807809507100f0245240313001d18000e060000d4880e0391784507212ba203105100401040741c002c524614000c2c1c00005200115190201d441c0c9000d0107140060000c2c8004010000100001e13a0000e0588403d90200ca60065a810200c1c09956650040c8040d51a0500400d146215260081e11090300000c10100c0e04481c50401d200198110785c4051300d6400300c203828808411024400c010103800c2913940c9828a00d041c3d1106c0840348600c004ca1030280b0800a1007400d61032003808080d5091101c1c0710000011655a014441990303424400c401082162050700c0b9481e240520075100b90907100e45c080c00c038403400c8503103000300f580003460107070705208108209084c0303030340c0b42c907480b0000c2c01041e100001101480000144160f503000643c80612500700144401150000c490b4603940d40e10070841981c0703a44910108196803020390005084070f030130f888040b60740c060042041040e5201880304001004103416400b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 507461600 1250 507460350 507460391
    0x9060b090112020c0f160f0506070b100b0309070302041d12031801020d0606081509060f010210050702210a35091b030105010302151b060403080109 65
    0x202880010030100310154014042c02c0000b42c4420340c01420544030344841c07820302080940410321600204c20001021302a9504003016120f40410340103082d0070203010075103a02c9188000b4000c10b00f80e10001e40c600d00183d80c02c1c40a01804035289440e4113148550541d02c0c549400200e22036070411101c0c640404000070301079441c1e11180e004040c03984074440c15a50640c070142c44d9000c80d00d0a000c00f0b51300c003503003400201440c1201e994000b138500e20b0100001d0609801074005401161611803100240c3e1b0781409850b0080300466404641c1c2d1140030043c0e150030114110000740d42d0400041005054000c141ea020a8580b0a100410a501004228094400c2d00758000202d0a101c1c01c250307120b0b074050104108400030f110140754141107118204143d03070044841c20718075405400f483c40d124454118071400d20009900a01040d415a40090b4a55000320303c601e40550012900c51202400714107940c001d04416819135440d0304007400e0003804100d0900903441c4450401c08480001d604e0940714 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 507462850 1250 507461600 507461609
    0x2031b040b031506040c11060c04061202090a09050619080304090e0f060f0402010e0d0b101a03010504020d090c0602010b040c050301030b071419020303041103010b0a0605030405030417010c0206010906 88
    0x900c1007a5204c408000040000c05150000c00480c1448248040010440c086c051045200c1103a1190300e041e90050001c0241048000d4680c010300480c5195100e0f504000103036445842c020030309035544000726401d40e40c80d52a403c030307401241400090b004030220007001511242d6000f8060f10030403920450f07841021140240442d1310500024810040e8600090340003481403618000e010403c80000e19900e0800f1820380e005420101480340307004224408100900b01aa400703aa95600d248a030010f902052203880d00840d00010401545489c0b51b0190300c410303501042d007445035901c45900030300a010042405004524150841e0390090040081c4c80c1284c3c0e01c491503007402d940b200d0040b9004815452000e50f80790040c0b181000d00010050340c600c641e402c9500131034592505060601c0540669080c8602a034500007a116454407201c0000046d0b514900b0300540c0e985481c50900d18512903940403a40d261403243c04040940b6064019549402c0303a40e00300c0783c00743d0b02ea46985045440320321a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 507464100 1250 507462850 507462883
    0x10e030307140309031b0c0103060f060c0305340620070f05011401080a1a1e0c0d0f051801051501030c020a1712070318170702031b040b03 61
    0x2d0000c0c00266004503440904681500d0030105040d10010b0300900c0d185840d078598100e01e02c169015681849640d0042188054589146140c601d01800e04081410043c040100004480d02e489259080d2800f90500c980c18403207806d0121201c400142101e020700721001030a007401c1c040089044008000e102c0303039114000d45007494503582c0c0300480c40e041004660079501d865164069000244004d40204003d802a16080d070071840c1900200c21000c121040300d0048034144003014000310b1a81d06903882c039420184d155101c0c03a43e0320031b1a014100140710b4207030601540007421582a0402070282c407401e40060270329025480c03005e00307884048900f400560215104045198402d40100c2e9000415006461010070181c8807040a002460301d8405011000902222192440101c8980c440c1803860100840700c124140d850483d24108005005200d1112108854068003001c82d5070003a401811a0a1001c0100102a10741a2042d00c680b18030b142050359042d6040124400d840c10340c4006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 507465350 1250 507464100 507464117
    0xe13030207050103180b100603060501020109050601060e1203030a06050a060318060c0c06020c0304140a031a040206040e070305060a142101060b0304060504061a031009030e1011010e030307 83
    0x100114028a0341030b035480c0003000e60480c170034003040a500035603008100d400e840764030050130a000503040e0794041d81b20504580c5000b00100206201048882c19104146881c08202c50810700003401040300c017120440500000040c88000710725a0701407421950b0540c1d21000ca2650b070141601220600c1c05100090fa0f404507000d4006945a0302c2068007a026042c124404005030301e030b1404a030841000c02409510015042c400e0803041114114038100448041d91441d045680f80d1003215070303085600e403050a081d00403808560b074050503500500f00d0801c00340010301d040d0030010050441600c0340783c008d120a00b800320300070081018050f14507002812042010400408600301c040503502c0b4500b865580e4900440c240080d400210300607801500d000c6050705060401e10101c0e00040b40143c03191520308591030303060f103001c00d4480e068852414001540501418142c501d000d2840249030310111030058445d107a600100e1074000711220000804c15004160140f40e82ca101c240e80500101d0400e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 507466600 1250 507465350 507465359
    0x30e10200306130b01140c010608100b030d03020a0203090603040605040201140f09090a0b0405010e1f0302010f0e031e0d1101051003080f09030313090507030c120b0d0506010f0e13030207 82
    0xa40140500c08410b25000c6c00040c0d8644110180e82c0090300d4000d09a5100d00d410010440d0070004590342a0321a0410001d02d003035000041e5481c1d00c1da07042c1d0014903402250f81254107000b80240d501051028000a5603450320303240202c014401228200e020030112125600003050310000d4a1504503000800e5251942c914100260101d000b800041030503168140014203441c2d90017154001c0100c500030410b6800d0401071080a012100741000020100f05010800741c1e0b40301501301c1c03500e04d4908106201d9803004022134101078106a04114100c6541a000d04408000035000b0a02c0100c0d958820945010080c140c2604c1055840131032040c1401d0341840890003032001000c60201d60018186483ca020020030b0460b007020f107084880e502c204404100864141c02180e070301100c54501004960016480546038000d4100c40603030036992401042d40c075840d130003d942511904a0111141c03980d4500c40180c401660303000307038401400000c010407510030040000c0c1f80300c02d43c50b0300030305201c0d07040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 507467850 1250 507466600 507466639
    0x604120515060f1c061103160f0503070305180d05091c2a1e1401050304051e0703152a090e0c0d150305160b04030204090201030e10200306 61
    0x504c0500d2074180a08902c1000040c0d2920480710481c221803085600d929101001a18010807180c0d00d00612406504072003241e40c3c450107ea910807017504001034241c5451617110341c49040500740315124452032040f1040b0342d41001c080c0c00b404a00300d41030524074002c420300001401410900801000c008200700628808880015180e42405052181455074401d4107030500c80c2894154125a25203841c14041c8d040d64556064181c1401c0c00d110380b46007480d0b52240d54480d0781c45034038818020010014448200b0a01201c0004c58100c100000800c030420306040c01001c41d19001d405801c0c042c81d05101c903610082c141c02d5100d5032600c03025816481c0080d8450000d000824590710001e01708100609203a4910400ca5400d840380326180003582075183c8140f0f4246030311410360701d50184e24400c2158240c0a012142030765030544003c21100400d00c0164090845025009a1401609070b9051221142e6101c0a61a2000c0c16802c0100e08800d141c501c25100942d00103412540900020601816 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 507469100 1250 507467850 507467869
    0x1419210e07050f0d0c0f08190305121b0f0310090e06010b030702190b06030f010608120c03040b1605010b06040302150c07180c0311040b160f020604120515060f 70
    0x1000744c90407255a03459a100c2ca41d0036019001030411a45062050000c5581080307200440103480c030742800c9900041d200640075000b680c0c3c441081c10b03001d1000882e04040f07030800c441030b6048a019540c807241c2c264400070710394104840c0407400d1000c003900003031403585d140200c072011222413000c3d084590810700302e415154401041c8200354400c40f068000b0b03205042c418112818003480840321681070180402d0f00b8514601c0c03080005078107040b0140030034a8046419050b401c0d20031031455558401d030540d2815805941d100400a08012514500e01c4003405411061988100d000300700e201c0840c0d04004150050380006904241500c1649003101050740c01000c00d0030401c011158100c1d0f4501142d40035004048810703c08648401c5c848038020f4242c05132a84141e02d85010500741411701c05241c00c0e40c02038060002040c400c50261008ac05005c0140361540d0ba0040d045554454442e040080c0c41d0758200c50889082c4907892161140040f1821024000c40000f446072143c0300001040204982 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 507470350 1250 507469100 507469129
    0x915041821050f031303020606010e031b040603050d11191e060b0310020903070f3b090c0f010f1e030e0303090a02010905090c03071419210e0705 64
    0x2000c20001d039915041102441c070458864002c40c80401c05d52500905241c0060300d4503050010070805100349581c046541c5400d00c0500c040032030003524640020780a0019075102038102e0140781d080003c0b041d8048404103500503440225505851600b141c01802c4210f0900688452101c9aa071002480c42445020409000302c20109149081d00006400d01214180c1b8021030742d8001414401401c06103c10b1000f4200ca083c03010500789811540d00580c400501e00520300407010886604061410820b990008498091031110b031624a2005aa511040b40030740e00c40d040c12000311004d50300c504c0d040d0204d5041a600c0e40070b00d0307003200021b07020110060405014103448241c045001102040035511418184009001c0308480c0d00014002c203946800160083d40b01704100501a42a04110380e00b186a929010340080c60b040c0e144181c0c0d000342c2c14003102414009821031501540141c2c1c0c03409680070305414990728105590810102c8048110144c1d540c1c0100c0c8007001145800541b0850342d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 507471600 1250 507470350 507470357
    0xa02070608070c1a0403140c0a0f030306080703141228051611040608010203010e0f060102150c03070e03030c0d0c061103101406070305030609150915041821 69
    0xf44240c0d40c202200402010703e5000002420410041c03640c000d440d54038032000c400000e45001d005102c4c494403840c48500140034403216404150816201e940710b4001040e41e0000c0e04c0246440c1d00d00b230340c0002c0100c0f110920b207100d418440c50340c20008600f10f076100c04210300e1004184403508082143c40140d10402014480c007070004110f101260f030742e1a5070245c0720b41c140d0000325484004010450fa11900070040e60b80c810310050001706d00d40303405140c0181003401502030390b54070100100d26144044681c0a4581514024024200d407850099405036409440314850414542e0038190f40b406041825803141d0300903004030440030f0089015944040c0a00d00218203449000384102e40c1d680b05803848000b0042e0303030404000c080c2d00c4072042c41e0042011a1107901c0e25200340c800500034040074181d2440b541c1150041550b04c0c404509543c803030100a02204040d1914040c02c510381035005c81103d0050381808548603c4042001c5040140343d40121000f80c440030204070500301400b808040d2052 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 507472850 1250 507471600 507471617
    0x3140c09070f2c0414100b1602040609021207020d050f0c1203070c0b0702010b090c0d0912020f0d1107270e01020301050a05060913023610050a0207060807 68
    0x5806009104052846040050450403141102403201701c90100b801100355001100030f1003c0740c83c050140310200c4503400c4441d500c4007007009508a24903e24003000350700c10f03e0460700140007611034014106a0b149402084c00c10f40c2c81000076601d07018a004030780c00047c0b0811403400741030711320030242044c1108001203c41216203035410004580c02910024042442c2140000c10004804c9805a01c004103200030700c44400f5420100f5400a006007012940e00c0b03010170310440700e280c40e60010100582040c0e10491001c4209406911005e80303910703204040c000c0e05060040746015400e805600e0131140d0080286618000d080d608580ca11800d02815070a84036103a17810303c4041c00f07540c01448501000591f207502d040108001d11034280d001034001c46c02404510382c2ca0f9100b00005120348503562016981d102c1c550f45c03203004028450031500c1d810103403c411b0716446402d143c40401c074907419506120b0490f0280310a8545004550f07440c00168012001404200e00ca043ca450304042d139801e18516 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 507474100 1250 507472850 507472877
    0xc10030609051306052206021c09030309170412080304050a05060103050115063209220e01020c030409091e030f02060106090f090b0d06020a050403140c09070f 70
    0x64030400e40383c4500c0c41028148007824840c0ca881060b40240f090882e409062503149418000e001c0e00c208041e194583c0402d5583d0b9000c1800d0810603a141c440800b00140c0d103280c50094020807011106983c58a50340005074400190340d400c8400741c071812401c61020b80026940c10409910080c01115903006072611100010820054240038611900c0045048218840b1752540144aa404402000106066002d1400c228003141103441d04e00208906144002110300c01d203440b0728005260000315020703290713000e810850400380e6044894241131040070409145103090307000d202c0b071101964004000c200070390710f201c0d48199820b512690020412003100440b140301e80a605a06601240d080c40590613065418090701c0e003d0300c1306050544607103041015004000905ccd0080c280d0140c0d8034004400035955880400b00441d600110941d6116400302c402061904648030441d261038000c2c1c40c3c40c041d02030204502455134406494038425a8581d407044445402052054081c055030481800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 507475350 1250 507474100 507474119
    0xc0c090c020304331e0e100f03060e010b07051005060a120c0b0313020f030a0b0a021804020408031c020c0a06020d021b1f02030405071a0c0f0a0b01080c030c100306 72
    0x107541c43c00c0703072191241084805c81d10243c2c031504000c5c540812248914800d01030390f4400c4543d00d0210240b07070050301039113900004c2e07004103130b243c010a40041d9400000220542c9800044c40510b10900503984007256101e1f003582a528153352081d4040d101c03a4040c40948600040362010780d000b80000340180da950120080c00b81c2c8180d42d41c500c011401c500600550500104d1245850b40c158010402070103240c075003070303c00c802c0545404045034001030200f08181c0d044e1000240d600340100115070300d50346d440b140c0d56646d0103c0881860840c210402820300100c1e4425a6540207180010f8290140580c1e40c00d0000d50144a1048a981d802d000140041028014030006100060021b01a2804120642e40c045070b00c4000c0c051703818010004c0200061010515500701c840c00e0f58008802d0f40080024401c074085d0385a006018420780fa13034550f070004005070065a41d4007038020008582d80b00c82c40c050b103a400d08014107070554401440502d150900d03d92481c40c900071407074001582c1d511040b249 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 507476600 1250 507475350 507475439
    0x6030d1e0507020114030f0117032a160801060602190c06080c1630020a020904020f1e0f1e01210e010605090f0906011509150c0c090c020304 62
    0x20310b0175011f02c000502140c0c030041071004803d20150f004604043c5010402d984803040900070060102000000e02101e1404110348800c4420105064104540700d01899000700014429040144200200b51040e100d40300c069220003600301880382e140c241840d00969003c0301c040c0c1000030142c410004001440300364811840102c4c4241e06841c0075010b040410100d00322020070028001c50400c041071441500001c090800c55810b4039104501c0e910343c0001822040103070328039508008441e10150035001d40c1400840308100c11a080102610400188045140c0d6540c107108404040c0f0b0040354150f008140c07000b08000c51403400c40840c1c2c400405502503a00d03680074a10560b444800034082d81c0ba2a02003260f100e0f400303241000c040e10b410b0010603030710b030300c1840380700d04182d0142c402c0007100b8807903d03181014050301055040801e0200800410074650000c2c00d690a41c107a10011814a8460203060721140041d130043d03052600f000750a1520b2030712605040c210340b5003010304070b041e8074011866 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 507477850 1250 507476600 507476611
    0x1707050c0405071715010c02150903030a020d0207060804120e030a290612030304121103030f0702190503180307080105070f081003080a030b240306030d1e050702011403 74
    0xb5848200980a140385124402520113000b000001c04d683c65187d0380300044c071070240d03011680b00c08410051a054801c600c0340000840d0140000a1048005500007441000061303042d421681c00540c0c03110b01b101c031568262002001150141c00e020301080c843e20441c00e8402000303050f15a0b01010b5a14030000d00308042d030540d00304800f080c200c4520141c04003090350150080d15031030740c2c4c529181c41c0035443e4070005000902d0844c8040641501038803d0050441103c4c60310200c2c0c0e03585c1002c00c240a105001101e16000510406100e01001c0302510080d810300c90b840b000945c201500c40b520391700c0c01801c56161a415203d03c980028001c00700340900c038025003d0f525040224010ba440040a88100809445044800010801c000341c07040003152203044491800292101c10003000a1108002900b25920024507603168107610050100460081400710100d8680c400f0382c2d6825140a0b00008a098854101d00e8465050320701420080000c644140340c04030886c0c20201e11082d950f041584d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 507479100 1250 507477850 507477857
    0x60610110a0303051603020c07060503070203120a0605040f090c0510020c04060902090102010e16092c2b0e060c070f170106090902092e121208041707050c040507 71
    0x7403107004020020300c580c5d050b0081c941903180a800e4001150b0f60b070b145214640030080d00000094609200344255800410b0900181e401420301d901c81c180501103e02640d84620b19296100b2000c0240303214840c003280e40024003540991511080090a1a1402001c03043d4064685100060750399842050058841244010380f5080007000081c01c480c0e05130398000d1568480c07820384a8001466040408a860389032003c81e000000c0882020500c141400714441c103152408123042d000c9000c5884130001c40012200c0541c1d64480340004950800c001900020a086c00310905c00740c1031580c0100318080c1c90b2411103003500e5445e804841e601ea4961301c15490000040c001644074607017070003900c0003881c02c5082840006119000980982c402400b032488699080406c0c8050385402039601c1d48507003950111080740c0344c0e84c02c2008810381e41c0c0f0400310381c08080d0307507602d21010303024000c0a0b02480d0046042c0c12003070340e00c0042031020380c0144410f440e280314849401c107055a96000d202c0c41914103a0313 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 507480350 1250 507479100 507479111
    0x1d060f0720030a050714060714010221100e0c070c06021b0415091a0312090405060604141507060603080c0d030c020303061504030c0306020910030e060610110a0303 72
    0x384240c1518003646510700ca9003003040703c000030640008030f8001b50f0b802000d02004401034500026040e11800000420800c080c0160340d110080650141038a02c01d11050603220400403015100302110407a15050030a0b2035000c2400041400410340707038044000c0342d9031071800a135919030064403850b03030b4071050041e80000701d40d8000320012544054154001d540600c13810240b5125203c00744480d02170b25180f503980d03c13009144000304078451072001c0d1024054a182000c914442011039200f00071041c043c0e410700001c16100e003003074000c1304d040f40d2a090810004090a800b00449111046d640510710f01092001d2008151140305d8a0000d504c1108141d5841851016807400d0082000440d002d00d0300c0c00e507a50244640200440f036205108550a03003a164103a000c5807028001c641002c1d20300359400c400032082201c0c0b640204100b0714115041260144221421020b5441c0c0120310801500410041182030808801c0502800c03a207040c140c007125214410341e840c2c0101040250300003a11039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 507481600 1250 507480350 507480383
    0x200a091a100206040305070f0f0b0907090e0f1c1e0201020405120a0b071202040b040b0d06170a1121011e0e0a1202030c120c1504031d060f07 62
    0x758003211580d00e5001401e8245800e40740641103019581001e005a203074042d0100400c00394481601650f580810303a0102402c10703a029030f94a80d980d0044140042c500005010250070014000c0c40303172400e06008003940c9011040c6084900d5594007500306114444060b4180c0d071980da80390003100620740d400142c6691419080000c64003101303c24610301d8000c00b01c044081007401c1d50f800d81c00a0346e1708004042d0120302c0300d210024130440c2c0c410000c404001c42c000c548030380080c00070594100d0088d000e220b043c0d00e1703440c1d44100c85c00c160024501c640c842d4075100700081003c113212928034001802c03842c0d00c00500b605420b102a444005c0302e4142d640382c80300d02c03c00c080011485c811035512803040141c0110916800daa540c6101f0000e002001c00d4112020300510130411980c180050070141d82521a071100f01458036001920400740070b014100c00d0300807125078813109034400c03a01030741d800d07074104110410b0b80452454040c650ba0400c1d020001101c0071003ca02c028292948aa241c110740c50000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 507482850 1250 507481600 507481609
    0x5040201090905010b090409021c0f26031f05060a0e0a0e0c0a0e120109081903021804090309031e0203010b03070b0909090c1c1e200a091a 61
    0xa0740280b4034882c0381c4401440b90340c03c41402d4542c0782500340d0f80010000c1d00c0e400080c2d00943c80d00800f500c100740029408040000356a200200680310340303844100d0f00152807410100d452123003030442402c0c80900004101041c400380518600100c5848010a0390301c400100f0000d41c0200750701e82c0414407012200b540c0b401d046500b040141001074008109040c0503002d410244210742c481ca003001182e070014101d6640c4c0d64080840900c84400800140d0264940707040281c101c29400d281c24100e078030200e84442d0082c002ca4140b5201042d4818801c0041c008010050119a0094007000790401011000501000c810540ea0122a0154481c801244105802d58104441d401c0c002e4022003020400040d002003510307407180341160a004a41e6950003400e10f001d525401c8640d000038440c030904004d2003420f0400001d17074000c03003810700d200010608102e00c00b050400028103408100001003903075170241e0700e46070700080014074441d545a560f2084400380d840110b00001c004900030031070f0549261 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 507484100 1250 507482850 507482867
    0x60807020c01050405060901090e04030f0f020303011d0403120c0e040b0a050a05040902060d3b0c06130504060308281b02040b091905060f2812050105040201 69
    0x415100400c1007100580c0001d005009500c140e6004d49000f19001c0496802021100060b103080300e0b81c09070714a4503007401000d600003400100042420708281207440391000c0100c0381640c0c0300565503001c0c5104410f00c3d205401c0004c1c03042e002c20105000c0100c0000e21401911060701031561f803482540302317100800c401c445c0c412810612890b1070040800003900e907103000300308442c002c940010b0301d9003160000c40d0302482170980701c0d18007615103000c10300f151100215000780407e404d0003110803002000524094550b88840104840d88140101c10a5281510060403c4800c401e01c07503240303aa8410204041c5c80050704110707405000410720110000f14400c40b1440030210004007030080160b80300207040c038030b85203014110408146c801c00055441c3c9800100d24013034043d001e610b50f03281401d2580c0f0a6145283c6448100d81010041211450412050152507a00818001c03910307440b000c0706120608000001c80403220805d800140c002c00700601840003e0141c070003c181c502d000d1000510071031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 507485350 1250 507484100 507484111
    0x50a05060a140c01150305150a0501080309130605040c0206011e06121a06030a0912031109060c010b0604030503070606051f0302030901090c26010c08060d03090506130608 75
    0x540900c6400a00340d03218494840e00c03800300b0201c540c1c52901880302c6015040781141c104030707420307a024004100080020151540c0c0c403030040441e2513031500c044040a0703500c00e00c61381070580d00c140081011071400c030707410304482d0152070800035040e035550020a0540e03100802d5030000d038000f540100302c042d03c0d0780413840d1308114910820208504000001e00310f0340004043d89020790b07951903942003440e44204d00b504030040062000380c6a01e0101891300203000c806200f20381c401d108644100b441da01900806c014009030103245814100e404043c000b1719003001540c10041c0d0340303507001c48071242c981c0c0b40213002940c040c2015590301d04e50b906024003a00e0052b84a580070b4404603498600b44040d0b1b0f10750042c40ca00d18500541c0d41d881e2080050b002d400340c03d5000d004100080800260420300004d00c3d00d05205080250009081d01542d240c01c840c44501e6007801b00f42d240300065210310700010200700f280e200e07042c1911b615880f41d0209605810980c69031030400d00343d1318288190303a004401e00343d000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 507486600 1250 507485350 507485359
    0x702120109030c03050307121d0f060403021905071a03101a090103050a1517010e0102160210091a0a09080c0a18110c0a1707051c050c0610050a05 64
    0x8181c580d500800d032200809000e001c110300803010511a03031080700c84510508a01605000201441551180700551101c0e810b081d03100700c0041c1a00e42002044c0c007807003a5010740140c11092100c2d245c01c512034100d040200c1d507500622a0108011311400041c540a00c4c0156070107840745041c000e9051004d0f0250845510003c0025444514900081c04c44d50744000c2860702080640342d40400201500302c0414250014421550118029401038908072042840200038418650744120284c203d2040020210310413881c00800c1c00035041c03403885500e4051f6035190800203540c0c0c806044048840000c400802d040b40000c0e000304c0070b5405502d510160801e000641030300d050700c0001032404034045c03083c08240e400f12810b6140c0c080460f803041d144070400352080782c1c0e60000080902c1e1a1880f01c5c8044070030300c2c15803007502510f8078914266815a43c0c420000c00400682110300c642155516984804129042003c0c140005091084a01520780007003584ca0030f604240401c035055010340c1005004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 507487850 1250 507486600 507486611
    0x5040c1a0301060c0212150613022502240c070b16300206100902070c06080402040204030c17060603030c150402032508010f0b010507060b2407021201 66
    0x80e1280c0e400c0782d0460740141008490b070100c910100d00c40c0c202401002403940600c0c0781100343c000001c81001c0c454001200c00f149080442c0308040300724013440c00040d902c07061400b124005d078040012180e00c0240000c4c62100440d043c5074190a98001d400d04085200c00003081c4440441d0003045403401501c0030407001da041908507441c03204104030882d000341c6581d6404420b81411811944a103081d181d080000c0820034032010000b9544d24801c0c0c45544404444660004440585100b80c420f900e0f444008591494030b4072004990448000d00140d80c05642008004006a490a0040020f100c004c0c202d800b40c419002886051002c01805a40207400030030000401482c003040c03019004054546c084410b0703d503400428641650000803108880502c94074a0481c9403064820044441050092001c5c5007100081820380d8500001d06010030018413071240010000c0d00704803c013030809000100c443e040480d81803481102c08107140e02c0803200040c143c0a6040ca000c00034402200c100c001e101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 507489100 1250 507487850 507487889
    0x8070503131d0606250c060f110606010c0b1b0301150809010c091e0b0a08040519020303070b070e1905010e1804020f13020307021b190b0d02070f0605040c 68
    0xc0718801d010150142451a21700006144101c07001d0780700e55900114401003d60301ca0340c026011980c1c0150760000f00300b64118180210341e001071000e201c3c800c180d445141c2468a50340d541015040501401541c034041c290008100080c04c02031802000003018250150741848009040c502e0094110422030f414044420703003039508051742004031807144912030300013849036424060a94068100c440600800a500f800480e444508203003c0e9000b60240d84d114a481340c08500e1502621400941680041c0000800700e001c4c0522161700500d035003000360740c914880300013900454004000302041403d1003400d00c100d50b400f14940403541403c1d210b8140400303000840d5803040c1c000a10092041025140440c0c1c291210410005285103011083d03489040840000c0d4491500222510118280e51419101d41c54050341041019071814000005203041624894281d40400c0304284035640804c0741d580021140c80750140050300031000050141406c0c0b414032480c40c0310b94407928000c00380841d4144d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 507490350 1250 507489100 507489109
    0x306030c01050f0702061303300513120f030206012702031f14030d053c0406110f0706050418110705010b1306120f08070503131d06 58
    0x21440c600c00d0070440d440712469a6000d069102d45000250003107404100144841c4590304003205407845110070340c00828901a000f1070b0941035240707c04284139000c2080e4001030298000308628642589070303464480e02d07032000c0410f81500003001c440410250001e4820706506102d06405001584841c0095030b00c14400c60080b16403080000341020743c00404510892a02c0c0c83e1041e0404c400c03820105c50f42d940b03940003100040c0d040340300d50080c020b030003403404998401c40485042d2500101d40c8120301010303002860b2008499840c0c105950071203914460091070903009040180b01c1c1da134501540c3d51140034443e0400381c80300012074050788008005d115064115043e64141c03021030010901c0315840412400250441f00401e0203240300000f0040c051082c190032041e18142e00b580d4400c2000b040080d91822a4041c0c86240c04e099032072003800c000074070300130b80c01110310703005400c030b14102905601c415003150b005481d0305540182c040d0b0108603042c858040c00080d250303460107594251a1101c0401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 507491600 1250 507490350 507490363
    0x118080d050f041e090605030606063a0c171611010b0d030903120e03071502150f090609070f06030b03010e070816050904200a03060513030311030603 66
    0x88050101c0420314426000c45103041c0c40050058140200030710302d0b018210740040311a4000c042e101d0b810200045810308002076014040c070400341c511490003a41003080c001307074a51503420011510050504010954003480340d401c2843c00c181000403071050308000903108140c0104005500d100607020002c0b08402e046c11002c0e040c13050704180f21180000346510b030042c000460784139403060940d0a100b05065204d80031505aa00c60750311524101c01c0d064080e04c007040f8000040f50316034440d820510100484200040e98004640105d54150420304c900d4006800f0440d4403000e45d04101c010494803000c100945a00805910003400300d031030902500304802840b6002c2c00c0180b507241c84680aa0341ca003503100ca10221010030130344120700e441d8420340351508d000f9118420005501e00d0040b03070324544560301c09d000360f602500c0c202c103006035061689001d0317041e2914543c1c0006501b50000118449004e17045c840c00300d010301c0e0346982080d0715014044030a450f0083c1c8040c1018000c204468030b001944 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 507492850 1250 507491600 507491623
    0x30506060f1f0c03090b0309120c0309040e0f010605010f0c0b060604170d11070f03060906091e03030c05030105090402010c050f100b03120f04060c170703020309011808 74
    0xa0401401d8000d01007a000498280b03198205050201c4001038554094005000e540c402c4d610320310741540c0d68611b83d200e8002683d020611750803a0141d400c80301d10513002080c0e001c03d0fa000303403410f0880c2e580000d4100c4040c014101c81a0b000301d9058a5108403e119440c06800242045400400304410050000701d058500600e10b05800d004601281c1e21001078800400800c03083c808102c000701070054a0b54000c00c54032000c03e251103c09644240e010a0000c1682c1164908034429440d5403a5040a410b04113029645180d9800c40e13400820119920500c0d004150b412142007502c0320300d002011034642c406503004219050005000d2981e030001ca681c0c0003602440c4c00d004429903414040d042001804101d42e5a109100741c90100108036040007a440500b182681c1c03042c04440c038482030510441c280c00e4030f01d0350100801e00450b40079962400e012805001c100042ca501c411407110581c0c0400d805601581c00402d00c071006603401301e07800c0217180c900b01e10458104d2800203540d6031400c08918 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 507494100 1250 507492850 507492859
    0xf080709060b0a050d0209030a020d06020d05250e28060806060f0904020309011e0b09090a0b071b061401090f060b0d0906090c0b03060901080303090d0f0c1a06031603050606 76
    0x10701c107d03580c1d400c100b80003105400a042ca03450140c43c0c07074200c00940c01030195030b1280f400c1000140303000b006602404084801000205500030400c501119006182007402c0d6100304907030203500c0b18038000c5c254401011048012070141c00c0c01d105000e00303203840080c0740611030401004000c07996030a40c0e041d651101c100b62009a120b031541c0341101c0c00741c400400320b00b46441060710181488100c50300002c03401c1d141640e85400f19110031420a44400010390040d280148030008682c0040c451070004c00840000f01444021282554955040d260010035003664035620400520a0030070b14814445150500c180412426142101884540c0542c03c260380c02690744520042c20b00101d42c00031030859500c0088284450740391401050280c00c00d50780e6902070211440081590203001080741e004021540040580d0282410304541c005890656001001081101600040c0d420148a07004010007a80503109107405421f05151403d08440c0e2030180544000c05c04c0803407404102c1039009030081d00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 507495350 1250 507494100 507494107
    0x291f02030403170906090f010c170406110606090f0601020f160e090109021008190912020f07060c24050901091709010c020d020420070303060e0103020609010c0501060f080709060b0a050d02 83
    0x9005032440244404090280c41cac150010398070f040c010740c00400c1610510f469211000b91003641407603941e4002c44524be017010510340490301e160394171440c5640c403440500c12035612402d52003205040c120f17000c1c0d040701c101902e001c06025064660b0700c403a0388200300c21700070440b401441e000900c0ea448120056000c4c020300c540450210654117403440079061202405002c0071240e441c0220003404404110070050003107030660190f007400810120101c9806655400c44190140c84400311003041007401c0503005401504a40c1c0d5107414003400784241c0c1c0e0030000041144081c00d0020b00003041200c0c0658181d0200428002c507030700f0801161145405039440210980c3c0c92020400800400c03000c5120b02d0301d0199031401c02a2014010322003288a6502400f00d541e4821801c00312607001e0000940c00b40c014400141c60b54450b903c2c0b01101b900480010034000e83d50f04a030403201042c1d40240d100d541040d002071007515100c0c05001c0007013912200c518903080c40040020400e00900e10f58422441c0c001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 507496600 1250 507495350 507495379
    0xf03060b03070815030f0d050702091003051011070f0b040212030a021009050c1c0303150608070507021306080a03090f0b0403081c020d02030a0b0103291f0203040317090609 76
    0xc00071074a0003101b44080315009031788040050001e801924049104aa01c10300090304503d2020aa504482d4803900610711804030101c030701c01030a01e0400d003500b5100240246c0f4042000800e0a841e06400342d0a4440306040500620081c00504044c8242e640d0041007262501580006c16819000041c1c0300090344000da40742c2941025206400907500003006030390104025441c81b5450122807007071300c040004000103002c03801c840380c040c8102400f0032044000122600e029800034059544014040003000b00180d000c03e0403034501d50024130349540883c07152420580c00c6400b000c080d0150410f0034004030b10b8034503800e4640c41940801080d16901164022056003041221891f410306900c080d525082c501c800c0000a400440380320402c1400d00e4020b910075402803041c0e05102c1a00701514240103003e44055101101703800720a07400c010385004504030f24078107800c00b9103541d407243c7c042c659552070340c03c00c2442010318809641c02c1c03c40420055081e5612074003220006a0251814902c4402c2c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 507497850 1250 507496600 507496603
    0x90d03090b04030602090907030c0c02061b0a0606180e0a1e1e120e0306040201080903070b1509182104050301050a1e11030604090804050d030f03060b0307081503 71
    0x11940007002072000864040b042208035000350003802d20039203000046640b9800201d00340c40d94154000041410003180c03501605007440100703824401d0b2440825405510343c180d92130510080780940d42d41c1e039540700500c05152074440401d030021103e101400f0980410060342d85811450500402d0600001070302208020314050b5854900d41001841d05640742e404541c1c81c08444069049034034501d02112010b61781e000300042d484c0754001030000c0a02c0e03a2903600540d5036460180444000703110034000c810000e200910003e11441e01302000c0c0c0c400c2c000000501010840123801151250722103440070710729040c0040c5031002c8214104a0407101482143e0216151040c2e810807501035081c002000395238a102c5d004403101d0541081d600502c0b215400c0c10100f1550b580c500050120801c2000c0303002031400d030300a45412400b07105002c1c41d140c2d03604001140c007014403804802013105103070800c8425400d403203404001e007011800c0324610300d0402d00080c14001e008289070a074020000d10303036956450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 507499100 1250 507497850 507497867
    0xe100c030908120f0109050906071404081b040e010e060c090a0e070f080912160213090c030b15060d0203092d01180c150507150c1209020105090d03 65
    0x30008441030f03803083e6907648002d010f2030031240d904444040200004080c4040c0c4100d40c420040b10b809010303161a021800c40300401350000c51a540703d400d1002240d030a44c10b01c00d038607081420894550a941e03203070080c40282e074030a04104009900d070429441c03824101144407a40b10450440b05a80d402d800f500280028910350070400d290380d000c0c0100f20380c080d04000040340e81c4d0b400f5141e0000a030f58100e207041e038403814025044201d00081c04404c0e0080b103081d0000154502c021f0402403644401070010013200d040c04403c0c0c854440c20a01042407103400b0144c1c17600135215008204e0140c400c000460454030659100c82c9420780d00000268124406105410800e13014001c81c1c510000b584142c09110020b00c04008281c1d481c1c0010641100d0742c0c0c3d0951880d865002c01d11305a006d1500c0049410480444000d02c140102000081d00080081c2c20103240380f5494000020030102003000181308560010001003454980010500940e81041c1550011203084900004a40341860200ca8004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 507500350 1250 507499100 507499103
    0x1b05010906050916060e011b170712050f09060d0209031002031014090106080910181101080f0613021e04060e0303030421112a040e100c0309 62
    0x14a004898000c20080b9040180526072460860318000e044c00c81c400070320b42140c814900801c1104036041c0f410b50003038424100900c034000907610795420030746a1201c0000200d44507640d0308000600c1900304581813811070b140d0340d21403400070b040030003036051034456100300c6030f50510455002c2503400300f2402d1354045446035034001d0281d40c003041c1c0ca009880c0c00b82d0030540d42441c061070319210200350401030010141c03040030300410b84e031a1640b03011400e95a00c07038050301050090007580c000c90300e0b03012207010b03041041c2035070351100d1048092801e00388070b03502a441150313042086c51424002c04610100010b5000312046821aa9620507044030302c00a2048180c4580340c1054540441c103082d0319540500100c400a803900d198102d6803408042e100e10007200c00a20301d5428009103d0200100807444a41078210704042040800c11510070345032080501000400d0070071141540c0026401c0d513803200ca091010b84003031110064102045485010078195107d18660b1803400000f5a417113500a0705445 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 507501600 1250 507500350 507500353
    0xa020f070501090606050f04090b04020f03010b0a08070e10080307060c0219060e120301030210120618050907061e05030a02040b040803030106081605070b04050703020a080115050f01050a1b05 84
    0x715038601c4c1c00c202901e410b00c5098480d001c8028299850309040c0206950304d03501001342c0c820703a50380e0f90802201145495491750550369400e04c100f01c41c0c40304180c0502400c4000005c0180c207141a0125400440c020105918001c2d42d0b00d040200c09000416208441d60280001c40e0201a116049180581010300e0011801c107040c0010203001c4a54005522010604240c440c903178100c00d00c2480511017072000039000b405d0580c04000b174600c1205030041e03c0c4240c40c0d010603800d581c0e8110440d40340c0b007000b03051f10565541e01849070f001ca042014000810704c9040140d18a03243c601e52034107202071240100140b0600000041036032049a04560183c450352480c0d07a2215119a8a00d030f481e0000d0240c0c01c003181c0c640020450004e01101d01c031003130744441d81d1510304e0705030030303558202100d800070780300703c40510036010040016a1a005848094102c400c00060012074400110107034240940c4194019244000e40e04c0072a6481400c84000d141e8509210360441d06415560a000034450f0010301507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 507502850 1250 507501600 507501611
    0x6030106030b22082209090206031311040507030c1b0503030a0c120203010609180b0d110303120f0702010b0d051e07211a161215030501091b0e0a020f070501 69
    0x1c40c000610301c40c0305c5500c0c0e1401000102d88036446001280c0555402070351000c0207100107650000c10000c03d1500d6880341d520310201102d400042820b4480940302800842c0e00e4500001343e50303078400d5500c074034291180700c007078187c0c030b610b42750b50703031240b00c0580140550340e2215100c8010501681e00300042400c008011035032580c0d43e04e4000c2050285002d43c408121103403806a01ea0f000e24050b03102051001440b55990890960b0780303880d0414030240a580600050106800304a04840c21601c50591088ca0004601d000c080013821100c1c202001c520071a091264400031820005501d0151600140b40040e55411446810703d8400140d0140001d0326041445010301c000c0f54981c034001901c9441464041c0710942001c904c100021900300f14001d219180d042c0c0301c94411017007455000a10800000e003003c5100800c020100150000ea4440c6c0d1a403410400304015840e01c4c0c020000000b4078400e00314144044000c0c800005400903a1950300410001c50141003401100c0d101030303200008210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 507504100 1250 507502850 507502867
    0x117150108060d1a0a050106051206010c0c0308030f01051005040b0f07030c150c0305010504061404051b0f0c0c0301023c07030e03010b06210c040f0e0a0506030106030b2208 76
    0x130100d08490b000381c201d08200001404c540503c0990b03a05861400c40103e1a503680340c01118060102c0c4e906803003050b0000070000c08941008011802071190349218282c0d58100000d00441d4040795503c4020840c04000401c5801d061009a480d9400740d013030b50703581d03d08403410308543d102030080c0090121283c45441070b40341480c80c1c1c001070281e041d03514140500daa03600100001c4440d144180c0715903080c3e41140020300d10340741d0302440e804540005100d0781d0011000703010115400c007500c0d0152208000549001c200c104102d0441a04401c400a518082c1c04001aa200c448100403098117080c8429004994a13103813045d2400001c81148440c2d00d4503968280101003600310071400e4042c0d46003e4401042d42001d604461103400c800d041c1902c03034201600911a00603004110400c1134500703000101d280d91075065048000e01d00407075070240710709002061a0844401a141074420381c9405420070000b0562010b80d648142101d6003000c00e12a800c020701c0c518800c2c03400041040710005400c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 507505350 1250 507504100 507504143
    0xa08070b042c010e0406060806060109092309100609020906070803090307151d060106020616121802030d03060e01030f080d14010807120c0e1009020301080c0117150108060d 76
    0x5d201c0c07400307003d091201584e0f0700125511141c09642d100e0004100010070b001124072134120821550708600b9804156204002100b10340c0e078190b8031084640c000c91a03049100c03071180100c20240c11841d070114544103039800005e445214803480148030f51404400070381c2400080c004d80d0401ca400603242c6003a039080b41d12200c010480d00000c030031001c2071500b081081030300001b013441c103803002c580062107207403102d400c5103114912a5031440c0030404085080c0380d000481d07020301c5a00c4014202100f20405041c41014205107115109200705072408808001a00f9650402811250801e90b12141c45405081040340703489590140301015040061100d07180070459030b03c6040318080d105484d540d80e00c0f1141c0c0c0d0295000c880000c3d010901b100c13418400c0f00340c031920007504041c95a1350311032000c1e0f8402100c2d00360382003644018a0368001c03500d082025604048150240d01d005541e01003186031924000030095041c0000e1030410242200060198450f02c1c40940c2240d04128102c441e56810790300794 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 507506600 1250 507505350 507505379
    0xc0f0f030c060f080a020d0605060c03030906070203070309060f090e271203011401170106020c0411210703020c030c010911102a1502090a08070b042c01 67
    0x450340010003180010b2064824103100d401c0010a9a94400544034400140060f400c40340321000c54580d2100c00082e80d544450045c00795590000145446c3c0c41c0000c03010b4101540180071a0964004008120000341e110040e01c2c1600c1c0c00c4c0c2082a85008608411507074009682c002140c245940004d0042c0364074214420842d1003402512810620170f9400d096848601c6490b81400700c140038801401040484074400503800811300d810201d1411281000400314000c2c1d00c1400540c0083e00c5094080c02c01c0d00480710b100d070040030814607000340310004150200c0224001c2500800f400c01003003000d48682c04885481c3c41250407280c4514001c4041d40c000e18400c0000c5441c503002d4803010381e0310b00303060802c0d903020b58441d240c07100c161384c400c2c491501003030123200d90391403004120b0300d407000007114100c1c03010f01a514003100503100c2c05108144800a0000d0304220111742c4030810400c8101203140441c0c007503d00610f03a4988408646c010301c140f502d00c10440c100c2d08000f0000100c2e040c550320400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 507507850 1250 507506600 507506603
    0x801090f14042103060f0e1305030310030506060d0f14100c020f0127020904060b100e091f0b090402041a0a172a0c12091302040513090c0f0f03 63
    0x11480003c0c01601100e017188203440c0c1c000c240003400c00450340400700e42c5034028030707440d0f4034405d0030743c0c40e9203180c1150b00c21101d4810308401d01c0002c3c42400001c001c5582e118030141c95000b892040fa4845100d42250840c0040031740824101c02860400b05010500110b4103252050010903031450001e51103004510a800c5150b20305044054281d10f0035090050340000d000c14103502011035021701c411080018000e81e000b94540125442c99269100b103204840d80c2503a03642008030002c0f042142080740a80036025034044240c0281048001c4802401103070501041d41e03030745804100c00324000c0c1c003641c2e000115111111340c0442da0b42542c0001003910014658809401071080001449920415502070515070466104442c180c022500903080410642001c28103108501d070005141841d5101010200000030807248010b0410507030041c9202d040a106605082c1004003044107140b6003c3c40e16080d648509561041c00b012080801c050001002c0b00c0c071542da02c03042903010400e0103100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 507509100 1250 507507850 507507893
    0x30d05180316060c0203071a13080607080708131b05032a090601030207050d02010f0b01050a020c060f0c100e0c0604050f01030b031612060b0d02010801090f1404 71
    0x41003041c07601041c2690203000b070078201090141000822581603a2221040380c26105034800401c0c1030b00803407202031400200c18901640c3d98031000b0156110307000c660000d50107038010010300c0b00d00c0d0b4101d082c0039440a02131504c1c800c0d65803052a003440c00c0074014005004c10541c032108451407000d05142c50181c4900340c003261024000094400144040b0031080781140d000c0d29940340300d620b0703c2d909c0d00307411240501d0090305107003e6403900c40c203214a9294800c0540c3d540c042c2a03403c0b0044d03010b0313480d140b542400c10b00d0038400045006903d0700385981c04107114040000c1c0c542e034141c2000080d00d601c0d5681c04221458403480207032400040158143c4402644218107084460745015411034080c2c51000c0c2640030344148150054003e04140702c0e09541c1740c002d091000c50344480007120440180194000c000342184503040c05001c651081d10341c18011060a0b04070005070341c010a03ea03045035404500003410070040c498020041040b80280845844440d00f400300b4041c0d00c3c0d500109104c0900d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 507510350 1250 507509100 507509137
    0x30603120702011e03110f09090703060b0a0e04091a07081b090f0109081603170408060103080c01020c010903050702011e080a0e0f030301031a0c0f0d050a0b030d05 72
    0x510605801407500003800690400301320202003102410340062480789040205001c50000340300c85503500101042240003070301094052031460a208540d8000d00181000c1000508040c20229944a12200701d800d0100510308801d03030340c403203901c800b080c1034000e19020032072136143c1241c650108060707e8080010310010040790090300140c1001c485203141040203483c00300030909210f0b2099100b0701c51410b102c051100010745060510500c032010740b400c5030100009045140850b10728007420444038000400f484140001d4500040460669030071000058440c0c0c800b0000b0b9019100d01e418000b44d55003020000e0702010f030070802801030f06200344c0b540b43d8803003400319150503158005022000002e41c11800700e1004900d03035100d128030100f82400d81e035180000740e0b10549198000c2e031048a02c210600c4030341c2a0b580101c0f1150303400c008095416881e018500520a0860181c203000c0302070141d41d01e0114403014100d0744811940c9202900761103562a001c08040d005802504031046c6422418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 507511600 1250 507510350 507510373
    0x1333060f0e0915060c0d08060109080c0a030b0606041a0d0c080603060103080904141911070c060834032403080d1404080403020a0e040b0a151208030603 67
    0x44001c0000c8040191801c81c0d9036a4840f0008100300665080903000700c400c2014444640003440441600840703511001203900309040010706200b4a60f1003500170ba0040c45007103010750764903401003003260b070401c03207081140e1140000903907107224070f0f0f022998400040034070340c501034181e038013401c0c00780f10410040018400c640010341d003035103086507034642c5604821b005000180c031003800f40000100150000428441210310f44ca1441400d8501840c80c01031500038140050381c07801603003a608031030303968541051610303070b03d0305d406a220340a44400d000211002620342041891000d410344241d2841071406900c41a0601615081500850009092070401d201e40e6262a000050000680074402d4945e469070311492280c1d042102d4070820584c60700c10f002d61003444030072228000c40c020b10780d80d9038840c070b14070401c542d00c0550351140001281030410000494507044000d6032110700c1d540d000c161800142040440c007082c40e00400c0400207a104051306000c407079006144203c4c1d040d001c0391402c034204e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 507512850 1250 507511600 507511607
    0x30206060913020108091204030c030b0901200304110a060c1a01051818010c021e07060e040e010e0106170f06161b21120b1333060f 58
    0x11549000480810703100b01005511544406501c5518101030342ca15501d4142800a55405680300751000011040c3c14018010010141500030390980004c0141c10b840c9803c010000c00304002c400f082950200c0010184a250410041e000000808018a1a0b100c020141c07800305010b01c15603000d031040a0b058482065107541d141602c0d401001140490b0348904000c2802c80024010551070f07100191a030500c4e0400d00400d441600c151f0080c10802500320302d1070358410709aa582d5840342c0c0c0103c104000d0641c11115100c01c0e010f094501265044800303c00e9409080d44802c0c0c01165860480006040c03140e90494880c1900381d40d05032203514200b40c00c2036640e91010f40d06d64205400d0a4500c824240c00307040200c9080004600c4003d480800d0b8035007280b802c054680340700356405120500c191385580b04c1d208842c01704040804228030340269020401819021440710000c0d030307540f240c0c050699100b40c0c03130541e40310307106444500d40c0d05000110904603a580c41400d010482080300a140b0500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 507514100 1250 507512850 507512869
    0xa120c170717160f03060503030906130819140106050d080307021e030406140f1b1606020a030e04140103030f020f030c0304030c050604030b040f0305040b0d1b020312041b0b0d0903020606 82
    0x100152b007440030800030403001da480b1a41603000d54a61410001c2c00c85018000c048000321031031003c0c41b01e25a9130402001c40103000c0204040c6c0e0b450309005225617550348030f0364900590012003080e00e0361b0398140f05905e04080038410766034511140081d912003410000040c4151005075880310307000504104540641c0c06080d0001442017001e0000440519900040d0b081d03640080d000c1715501407030350300000b02000c0c41d40c01040c0140c110007050b90515804c2841043d0a4405076010000312100482c0e0808180041c00010b0410800080001c0d43c14820030034035140080480c1940e550704148850a580d0368801d110441e800c000540c40015a440e2800643d0120b82e041424407a0baa9500d40d60101c000c04080d07000c4050000600c40400d00b18443c43c05402d840e07024102c0080c5603c031659401c00c003402001c0c5e166086500400100c0001411000140d03007113507011006551145c2c07100c0b00d000001c020740e00b00d6600c4c030702c0124034088100b2140d00302d181000d0003a021354219480c1c103000d2160080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 507515350 1250 507514100 507514109
    0x270a0c060f0203130902031005060403030f180302010f08060102281202210f0d0c0305040506060406060509120c03030316090905070f0507060f020c030a120c170717160f0306 76
    0x1421130a040105402d640c00560340301070004003c4400c6500c520000c1c2c2e0b10782054000343c1c0060024106100c000f50040c4400c0030560403800503280b0f043c81d50340000c020070240b2114004000d58131021030740d40d9000300b04e40c100386d007440e582d02c0c1ca15151500ca00040480300d0181542c0e50104400c500001500104c2d135039000d4000300084011300103541800501540c420031041c62800750030007601104406030711502c10120b04035034002c030741c60406080181c9402e401a0140344183d02d07002041040581100c111781c5600c50645011289040ca0150b460922655611700c0703405001c0001040417480010110700102e8001b5120312590503214101241141c2040b00c508011820340288090040c1c081c0024102852050201040000000c0d40318400d0b80c1001d410415540e0000c00c0302c0e104160042c50001442407105400c02c0980c1180d0f038018203043c0e8125616919030020400b05020341c1c4144070348405041c6400c40e142203810440e0a00d41e040d0030a05641c1c000070018054166801d01c01d010710400c54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 507516600 1250 507515350 507515377
    0x518040f1a190b1206010b03040503040b0a261006030b04020c07090b190803040521010f060f06080415050702210307090803090108010e060d050f0f070518270a0c060f0203 75
    0x140e091881031f42c501e80c0094416203a511042c4000189901001c0041c8003c00c40781d5207a0010300c0e00f40030b81c40154034000e0440c140c0d554184040101e4014002100812184107107404140c408060020800038810700d10020003e02400101048074406074104240c6820150303400e000d9072013005000c5100342c88500885190707400800082002e0710b4030609014000048031f0004580f006446140c2c0c3c04c50f03070300344001488103031901c1e400c0215250140c816001005541001d041c1403909035180080250b018815458a03603890700131524480c030030001542c920368010840c1040c0103514a0504103600200c5205001455216021400640100540b6441c07601a114410f01d40d0074080120311900c4020a42a008103c10101030003003081082038682a01618002c0c0038800d504031840c50501ca11500320601030307140c586c10200c01414241c0070540c051044401c414010482083c00c0300a42160000c04031a440b82e200c0d0402408040008441155040d4550035150920300313805a03283d0285010840c00c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 507517850 1250 507516600 507516613
    0x2090603120702131b0809120c07120c0312090905060d1e14070306061505070312020706140a02030a06050405090d030b150318070518040f1a190b12 65
    0x107040c9084e03403d00c0403040400201d001d040002000408030020075010000030607107070510100c0501405450071040c3d08246091400010b807080d40d55648117841590746019402c04004103000b60301c0080c1014503440101d1844107400490000c00191080c02482031180ca04008540d042ca801c4500c48200380e4014030000702c409050300d8020396080c5060050380d03804d01c903490060f8181c1d030070f2209201451080728000b0b840d034101400c60a40010446140c014400300f003100c400840e170812030301b840c0c003d1049005aa2114645400c034042c0450b450b40c0070034215440c0510071102c032542c001c0c42c46090590002c0120560701c3d0100800d982007601d005406400200031020118882e230040041c840010303200441c04c203018442101107034000c030f5041c0d01044400100d85401981805404010310301110140da64516824140070501d802074402480c0c1e00c0c82106010420480c22880240d0321103c001c10481c41c601000640003181540303a04034149483c094441e295803920b8407210202c40c5001008151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 507519100 1250 507517850 507517853
    0x30c09060302090a0e160e0f0105030112080f07030e01080901060b0417120d050403020d021507031812120c092319150f020102070b07050d09050106080a020906031207 73
    0x3e6001c50100c6800c00c079202c0000c11403880c40c0c17103040c1c0590060b01000c0b08100b182c038001081090f442099138400c50404189412585e4414260b80c1074403135440700241001c0d454a0a207141d44260314407040c440e0b401244140031f140c0c105807140140e010a07283c5400b250303250a000c5080311128010078240e9002803100f400601128507500405150030811280140006445a401500010300c0310601c19207800803c0b08041c7c0c18010a00304406da4001040541c0c411a403503401c010300104484101907031129003085110f215504080855003000c1001d03c00c901c0d070301000380f400307440455440b1402d08240d038408449200d106110102c412055180c2c104c90f0044191408103101e941150b5401806403203050401c034900c4c02241e0040c01d104480301d40c8030854442c0a0180018607100c0381c29a481880303c003012444410115512100518005540707004544003203000340f260070001307083d071b40c40e0543c0400c14000001e00d0708511802141d0714020380d5141810140d80e44421040c08003100d030113001038030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 507520350 1250 507519100 507519107
    0x40c0905280b0307080318150307122c0724020c09070302040506041203030b040b0102030702010e030f030708040e180703030c08070816020f03190807080f0f0415030c0906 75
    0x452200b0081c203480280e075070740748100d18507001100200c800240c1840301d84518a00b800800c009020051415411403038a844082c0020811104051469496000701c40c2070708246500d14181604010140441851038040f181c2d9a0109000302034003120300e6180c15103526039440544904c07072146e50003000c014801d541400300c4042c004c0c25160500d0703004d10000c81c141d5643c4000d030010340031203851010414003e0070f0083c113a50501010a002d580350040d1040d560b6408002c07500d6a179028203000e01c49a000070b000c070345003c0110304001c05d50700000c10140c007000880b40007401115001b0305907081ca500c6900000404040346103041200e17500040341000001d01900750f041c2c072140a140b270142080d1241d19a807055520107240a00c0ca000c0c40c0007000e045190590040b050302d01c0a034010032201c61440305c17283c41d0360b18041018180b2040420a002003227080750440711540c02d030345101b0703072944165501300c4965000703405140c0c608070b98090380b2110a40b10b4412021000c10941d184c3c500c0c140f80020aa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507521600 1250 507520350 507520361
    0x60906010f0302010c1a040f15091e14010c020102131d0106110102090a0b0702130b03060a0e010b12010b01120c081602011b0909060b070f021017040c090528 69
    0x101c2d071a000012040c42031b40101940301e442140039000701a2680b03840e1034a281000c002012442e0464034201d1018080355448081d03442c501411041c0451185060030020210402141c80103420760a0081d0000601e5040d0003901d072106604c0451034520b40c40b03074600a01e0003032000103440305011440041040c2c620401041a00000c40800180340c0401080800c485240e15004980d0f040400640310b41103007058003000e82607200c4903030100111803d1500203501c8075005040206c24684071003a0800400e02980880600c0c0b00c002d1052510014000015002e042c900168074003207004030300807612078a024052016040c03155558040340b0b030340f914901c03800821141841c0045641c2d510590360385103050386201820247c3d903102c0d000303001e103050b0300e15058a0403070700410900c0ea814004c000000300c1e540401202c42fa030485000b008200300c0441100c0750405100c0b2034800c5000e51081c0800d2044001880d0203071440d0010a0003030382d680c0060001c60a0b51580e0850414844d140401d003038000c664000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 507522850 1250 507521600 507521603
    0x14040803041b03030513050d050a06110904050901050403020f0a050c01180b07140d0e061e1e03070f0903120e0a090c0302090f0d0c1208040e0703020903060906010f0302010c 76
    0x8080c1c2d0000100001281c5110794208074007144d000030350031001404943d460401881c044405541c0100c40f603403001d0300d5107001c54000300f40303039207884889168004141c10703039800101c00f0b0020081d82c6441510381d80640400c2e541900580101801d00074903036030110390f160a643d082401040c806403203c1c01103503e200c1c80b50f079140001111480105248000c000141055400b45500115183e01050818288080000804284075524000711181d45a21098640f01100c51184a007900003a039021010381c401c0042040c1c220f148192504c441310b4500c1d0103103000301c800da5240d40f10640320081c280c5a021040c007014140b8000f012048510170310038061024090005809032828694640094007594200e40c916404213030042819602c6040103409800001011207c0031a480300035210095980e209000e81c20850703070100d03101c8003480060b404440003482c00d500b010505180c1240c0081c0250002c40d061440f900910b40855a0f803400050124160303100c0c0005000420f185600540c0c00c004a41d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 507524100 1250 507522850 507522863
    0x2a0311190c0b070527030c12010e0610120b09010b030712030f030212010308070f12020a052b1b2001180b04170118111503011a0c0c040518010e011404080304 69
    0x903a141c7c1078454248400c0600c01036400803810b1003280c3c50642c14040000c151480c03500000c6000c00902141c010a520040d80100185299441e00c00c1118050400d480c80141c0511030440e00003030b42c40c5500385d20520580250780b40804d00c24030711b404805a00c900c6200c0001c00740400014001302d00c4090040030098800c489280c0002074550350340c0005080307c24154007680184c82243d00344207090000c1003844001c60000d03540d10064007044420030030250310711010001c1c0c580c1070412040610341c0c0400d0b01c0d600944c0445a00c03d014000b0a1540140a0807500241c24804076480040080207014155011440d8490034641460400300700010707080120b0015640364004282603031308542814603140d0062032401c1c4108034980502040c231040f6981315000220070001000b54001005200b80c020740554072950340d4403019160986000030001a090f40b007403900e800c3c42240485454105804901100280f1081106c000c640d8201c42003140180c0b91a1000000034000074041001994840e10510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 507525350 1250 507524100 507524113
    0x10902070f030e03031c05010603060e04020a151107140120070b0307050409020d0203010510020a0b1f0b0a0207170a05031818192a0311190c0b07052703 67
    0x116541000545106c5100189940d030700180902075245c051100a044028090349050a02e80e0100701082c216100711a8102403030200001c6c417522030001d030703100c25202c032040310304058903042e0313440243e901100d0315800b164000c82011800c2c80e00403540740150f80c4400140031542e103081035000c0d05510080c000307420080e04200101d641c03000361025002441404000684135810201440009003039102007106640c0a11800c01c0060140080646d0000e0b0a02c1c0200c01401952498002c03403001d40c2114140b60000f00340b14a40b5079001810f24121484031080304064400d4404285d15031601c01809000d64004004041b442c112228100b40d9001015002d00c1445c2d810030b49140d1008000c0d222003000000c4001c5025010203076004086064250144601c0500e001034039122540e01400d0700348081c10344a00b07040c00304001c1c1c88291089400b20102d40c0d4007400491030020400b00804404690400415012601a500c200c0688290701e0719039102d82c010071071100c403642880000d07111a980c54452036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 507526600 1250 507525350 507525367
    0x20c120d0e150d05190209100c02040b1e190609090207020a05040513140d120b04090212030d060b18061b0109080405100c0206091306080a0515010902070f030e0303 72
    0x1c12020070982c40005160511071240700b404401d0701c025003d843c0c014482c85247e603403079003c280688000c40c00c140c20b15892500c080740141189010150703000d0441e41c84600a180401511200104101e441c521204104002207441401a02034440003801c00f01c0c0038001191554001c2c24181d000034040140640da41c0001019030b40110750150380205061a03900401c0345d921182e114543d20755003c4e21150040c840e00500c104800707407098425a881742c426518039111350340510009078028003da0f50415034200d00b141e032540400c0030349030018506070f0002642c0b0030100a0780d4400303c2c1d4807140c0003040209420000c0342d82020708001c3c5169101c007029086543c00348181e1f64000e110f00c079441d0700c480c5001c0801174000c03c1c4003001c2c001c0c8030709002c1d0f8800507074506d411200540412199498481076220400c0c00030320385074101c0b46d5180f01c6d41d0043c0c0c040c4100001d50445d80ca00d4035510441c160b8941065100760300030030070000c060100305040c43c4006801880041c0d6440300c040c04890810402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 507527850 1250 507526600 507526639
    0xb06070c0b1c0b060304030c020418030206090c0a08070608070210020c070f080105070c1e020a0e0f130308070309060b040903030b010e030109080d0c02150412020c120d0e 75
    0x20781d00001c5910000a200c06048103080c0008080990501c401c01c0650342c05070114a1502c40148020b00f040b19403102d04046540f030713a00401c08000c40d801d8288450302180ba01035960001914103c08501c10406485003174500f01000340259451200641004e13850603030305a840b44405042c500560054a9401051038003920184c001d2900c2000100381681c41e20707400507a1841c6c141c02081d002e07410441001034140d0441406542c550f40300c00d440c40c2040d013008110b60220b102e81802984450480e400148103004500842d01036103241c409404981c40d9140c08030101040c0410060101300c800002440c507900983c445904a8040c90380410f19003880030001c0d040781d020a804601180e40c1d00920880e44d41d2206501740d008a09600070400020243c8550015020f42c03076859500585440260101178424440d0001c24022410507644034100381c54000e0017200c0180c071510041c840d450215003103240c417810b6034000811201c00b03010401d0503040111002103480030405e03049132030326801c04611640b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 507529100 1250 507527850 507527873
    0x2121e01051f0311100302090a08010209040f05010510050c1c020a030906180b301b040338091b0901050105091e15040303110a0302100b0607 62
    0x22000000265407600e6581251154624042e03007076041d9071484207000103000b006034030240900844400e15244615141200644100d81c00280c000b07030384140c00646403d0540180c001c51108403801e000e0b0b10301d60921041254805d118030341d0301980544a21401a00a000a00302e008004003900c0c00600311800c4a2101a0300035011030040e400f0611100905520900300c41c040c084070b01d031800782440d84649020103500d041c003a4030202d5100185020403000525207a42880040300f03d03550360100035210b0820b0640d4100c03554103200100079100341c0c1c0d100b8002d04540c2a244e001c4030b202e03010070003c04209146000074425130301072612220b503203020041090002e80f24807042c2000b4040401c540da100c0d0280000061035501540460300107201d16038105054a041c08015a43c00f43c25030082d00c9503040b01030206020320b41020902d540301b0b8030801c20900800560303009460300e010600103410700c0c1d9540c020a080203801a00b01d0074607607030328511a400291049a00a051500303141440d02c1d0402d4004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 507530350 1250 507529100 507529153
    0xa09050405180d1107050f22060f0b0426010e1c09050414131b2603120a0b06310f0305070306050606282a0212 49
    0x24102d0030441e06107200f000394415010752444c205004c616590001c0e9030b100c05c1c0c0c0c0503180c07051f00b1410310020f107074070b60507200c2c0d42c260039480401c2066240c405c81d2100801d401c1c0506045041a2400819801d2605003102d04aa0540024000c40308445e440f03400d0b01c03181d4607002d1065542790140ea0905400030040c01d26a0481d41000c88003c10300762a0207071890646512290048d4207060b0503501244904410540c001c02c4580b070300e034031080145482600002d1500100c41c14000080c80030820021010b0030100030f070100c01c4072700d91601048000715520300030005108c403910820000208652202d8210b0601020301904641c100440d04e11010820744507080b0081b944003201d04044030a001c103100781001800060701030310403541140c540984503411030001900c40382d10b0b10003040f5152a075208a82400b412000c02405000303c00011507503a294041a09001a40489242d9601c03060031150060880122942c07440c640156824840000f44000000515010b4580c041900e11051981c80d41100c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 507531600 1250 507530350 507530371
    0x406021f0902040e014a03130f0806070302160212030c010c05030f1008060a05071e110105070806030703060e071205060405010509030909070e030f070b0c07081c050a09050405 77
    0x506e001103e400010300e81203052190341d541040c50f02291140f51050094145021104000f00202d20705180d445003940d86400c5102840300001c14072819501d03001a070f44158292002c58440c100118142c0c0524000d0350305458500160b00014600a60041c0b0521580c100307990901050b4501242103482d000c4078800031603000000c00c6403c1e070051003225401080d4120b03800b000ca0a04ca011503135100010319846002d9a90400701c0e10190141c41a80f0160300840b400c40400411000c2c024161010004c9142240d03091101041085002d42c640c50720410019000341415491a00c40d40050406000701e0b1300da0303024000d008034500100311040300125002d440104628101440d0142c00c41d44002c040114079001480100c0f9a550703a00005900012039240484031902c0c0200020309000d2100400c000c18842e04100040c850704002c082d0101da5540000d40e04441d6840d001c050b00c03242041d140110754101c03c03101c004050300900142400306401d240480c01282c458011038100c4e80241d4440c07052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 507532850 1250 507531600 507531611
    0x81b0a0e01020705030d020a081602090a020702040513170a0306050a031b140619120e010e0f03160b07050403170301091a03060a0c020a050303040b06010e060406021f0902040e01 78
    0x41d6010401c0c2c2c0000c101c25401040c41c1050307a8402510380c0c0124000910402c00000c8859000311611800c0600343d40003030095810742002094030780207502c0700380120b00560510740083c8003807100c1d41b007003a1500e81103881403804101c80c0949402a03440b8507a0102450795602003c115600e4400c01d0744042d40c0b08488464210f034a101c804207000740154030040b0039688101840341c040c1c40301c0054407103c07c05410444500f54180310b0030780e20014910f00d0f54031898544000415899815000f803500b698000060744e00000f010b80d030090300d034880c04210300c001828010104001403076072180c084c0d10400c185000d5013042c0c3c403a515004809160001420707403400100052000fa50540f1400c9030b070b0805800b00321040441c100119489100080c81d42d02c0240d034610100b0807031402400b042c0c1a1542c8902560754901d810700d000c00c4141d82c143c40e03c0d80000c03400919021181440d5003140c042e41c459400401a11841c03140c4c1c402c8144403600c0c040c954079250070317403180141c5680c06801c03d00050301001040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 507534100 1250 507532850 507532877
    0x140c070f05121f022107231602090a1401060522060f0c0507090e010212130f290109020d242d03050706022407081b0a 52
    0x40d042c11600b5189410180c500b900300c0740c0c1961600c101e0038040b140981c603400e130692003c102489100d540402c140070340c8100420180d101440744001c0d800c0c05210170440ba50503010405c01d01444903060b03400c1303940071148005840c01c0c3d6440c640c402404030b000f2a094546800880b00b091007a44104041000800c2d1b525103000e400c01c040030300c800001c1003490801d2418400074800c2803650320100c00c1c0105a010ba4091200501c500d1028040751101401044962040d090003035005211000000d24060f0200d80203060214409845d1034011000003044007064031802c00c0d030301c42d0704080040880e070080d802c1d04001110152078020a4000c000607102c444891072002038600001400d0800e06c2601c84560140903418402410f81303c200d0303075681038410b00c401c24802400c2e00c083c1615140310094000800c101000480d82c0030340351580d007034442106019501c01d01d80040e0302d40303030aa400391820009074141d119031115988907082c0128084540e5000e44a04107c1d4001c0c0c202000007000080000e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 507535350 1250 507534100 507534109
    0xf05090a0e030a0c0c05031f020c010e0304080d030605040605090103080f040306050a09120806101b0503070b0702150c040302010e06160302012c060705031320041a03070501140c070f05 81
    0x3402003005501a0500c1d0034600c02c40010140d508d2012402c030341c0e02080c0707000b12000940c130141d40c00e00000300301c2e40d0320740c0c1312180c0c996a690780320380742e200103400c0080100d05401c15000c1c4c042200e4014081c4a00c69086a4442005400120382c0b8043c41a084c40004007081441c05010b0042003004030004010302c00e400c0c9000040a102c404a09000c41e45003401501e8841c1040c0d1042e481303280c500b440c0407040000200d40030240105028009220200d105010300c660b2000c05401204580c08039280c400c512220b042d4251403c40f5000310b164401c0c0410005075000b54079114030f02c100100442d15005d4001c2e0b82d030030b00c03225100c0c0076030050b035403442107240702041d81001620000900c02812003d1041840003544c846004200300100704011020684480042c032004022a40c41110344420b00f10b500c00401e16800f03403081c003038400d44c200b4070300e0204845151440004580058042c000c45810030005603904200c96615440301e4200b0095003503c9103050043d10040c007006042c0e080403d29000420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 507536600 1250 507535350 507535373
    0x221010e1506070b0f06010c0b0a06171c1d1207090c11030d2301060201021207112a040612050f030405030712061d010e100203010f05090a0e030a0c 65
    0x30380c080d0034200041400304603c00211381c0d00010070022821583e4440d001202d01d0b0325140741c010301150800c0148095004290446000e42d401d0000200c0c003849140400c0f0f540c1d0240c170740782008941c0d0040f003260b8070620903182501165003035124640070091680204d0300010441c821034405030041d01c804e00084200c1c4c022014104190310300802d003550160001d030785912600380b5099001c0d41d289480c04e00c0404d5031760540407018004a4525140d13079540d0b0082d010303510009030710058902290000f51002c1c003413506c40040e000c2d22001441c00350100b02c1540e0308030304096a00b102c41d580f014a09882e80d51603000300c801510011410100c01e9600349800c524180c2034075000301c0507030010300c000d12036614001001e0003203580044085003070f00c8007824250020300c00507004150110706459205251441500140c00ca002e1801c11504402e6461407000d00320300080c02298141d0300c1c649401c110900e0001c000f43c1d0006140c0e880021901c11081980d4510340c01580e09101103a4803003003400901c0310b47c041d032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 507537850 1250 507536600 507536641
    0x7061e03151e091104051201140403090e0610090e09010e01020c010c080f060f01140c0319081f0b0c01111908180304050d030e12030c0f070b0703030221010e 69
    0x10f0101d008408090113090045000b9180206101d1200c1801000d09400000d0710300c0c3c00c0402d010f080d0401d03003002444614540559841c3d1441d40000c00c4290410305110440b0328495640c1451250924101c085010f9018245070a65922a0750102c6110000e100401d403031700103440005003810318088040e02f603a4004200000e4100fa20f07007080b0307180e22900f1aa202c52002441c013504448c0b0410401380141c020040302111621000c81c41c3d4070718907414031101a41410b580c0340d001c4507a41e04000c9003403183c421040301c40c52150080040240f1340d8848060507400060340c0001c110445016400c1c892a00400d40c0101e8481c2138003100e02d00300da0001003c2e90030540305c0c549592140c1c1c0b950350440e0f40344681d02c207850203910090303e03040c1410720512009090041c01811600e00751f60035502640d0380c0e041404c624085028072401d01c0360942002900d02c085450002c6541d00f0030440383c800b0f400940180301c049240088040015080c14601c40550f4040d00d4145001d20090501c0341c078801d440341d907e90300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 507539100 1250 507537850 507537869
    0x3042604090e010e070506071506030b010501030501081f0b0607061118030703030206040201200f0a03080703090309050d0602120f011805090a02090a271407061e03151e 74
    0xa504c840b0f60004541c11781134400a8420a640b5052440e0840c0044401c20000411a01c1c086001c420001c282220342e049031003d90b02072016980b0340074003030384400c03540c4aa001950758091203a0600c0102d9045220300302401801e0f2828032140ba1124400d4800000d40506042030014960344108581403801c0d440700341c154001d24420f411640c01170b54941001d0b0019043c40300d40b1070803501c401200d10b19481e414000d0b00a03900741000e2101203d0f0f4910b02d1541c00c0b8007080080c0c00080046100740300300c030090754050b030396803021138600401d11004807000441a66126000c01070301d001c18402105440c0181c400c09000103d035803514407602c1c10800120008892a4140002c1c04040400050384244640c0c0446000010781c03030304142d410040280d00c071503090121040c559401e0620910f9105480075019100046082060302030458a41d0210301810004c0380e0700d80402c2074501301c5c1320b84090b40c0b100d031810002044440709a160050704010360080025800d00110100301300c9610f03080340c0042c102d421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507540350 1250 507539100 507539111
    0x30210020d090e1b0412030221040b0f19090806010501021204050f221e0507270515040602010c030501080606010f0306030f0819050a02100203042604090e01 69
    0x307034010460b603020302c2640303005881c00000c226800340d558094294007003a01e901a13901c035510074101c44c030041c000300300740d01600840580c40810151940800d16512481418134500ba0602400c6071b025041480c5401280805115407286c603111509408040c244544802031171038a050011442c4c5607051f0400b504540104410400b000013030802e603800d94104444074842e00320340030302043c00030091028042075140b15101414440416500c204041c400040a220084042001e0041941d8050720010005030702c482c60001c0580241010a50003e403820441708560760b140c002070402e103611321045002002c00602003000540901c101c401c0c0f16080d081c24071a6614010616840d03020050040b810300002e00c0c019164548207a110748044c5034020003041c20201c150405003040d411600c6c40400c0d500d0b0300600784000340c0c00780007500e0700241036500601c0c600705590110f5000e9080078200300c80d51042001070101041c0c1c06c003142c8500a0780003400d01c1e241ca00d03001c9000c080e15085454829a03900d0701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507541600 1250 507540350 507540373
    0x90306010b09010206010e130f1103010b0618042d0f0b040506030a15150e070216030b0604110705010e01050609062b03021614011421060f1903021002 66
    0x4600d00d0304503043c3c204084850f03540c614040890703680f03234400200f100c0c0180007450200440c141c400240076400f60000c0100001d00c2c400d10a1a20406e01850302c0c80c0d0702e00d030507143c075071170541c0259109000709811010901c1b001701800d4520000410080300164492001d15081c0c0800d209801d0b500d181190107001d1410542d010a413645110b840107420a400050600078070000c0703030081e430f1100c8500c08800d142c0a43d510260110704005490000050140840c1c00003900e6240e040c072800e8a42100103800d180d00c456003000002d00c0c44500304042e0b04410311502c004030f942841040880e4940100100f1503242030810031103c00c500400c070b240708030300c40800040004501030300230010085840c10302d0f841503007605041e85061418505800014040385002c61480c0c034042078951001e50a80351700c250508024070900b114014a04100244840704071050350506c2145002500300c01c0141c8a120164480700200d0000504a01c020b003c2c007660300b0042046041803420503c4607542407010f45803007a100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507542850 1250 507541600 507541603
    0x904050c1c0506010e03030c0f190b0106050a0e0a0602030711061c02091311040312080c0a05070204060f09090b090102040303050a0c142a03010b0a170c060c03090306010b090102 78
    0x16180c040700640d62000098070716401030f03c980418480003411203449503c0034400390741d07070030300091100d03030340d0040d0801441803003101c01104070b007541d01400d0607007640e081c207104803032a0300864030304000c210203c80b81c042c850704c9018020014103015406140d941000341011b2140d0039280103418004c2c03408128554004505206800d107800356242d015a843c600b22002481c5520342001c0030010b41d144c5a001c44c08002143d000b00101e0f0311800380c02803044241e10701554407040c2102c06000c03c00c1d0801001503614071841c0140800380c0300910024405803210000e8440000f030303403c800081556055200284405558825844080070000f589441c0c00d580d0001c0c0701e405403030201010f1100c1080c1c140c0401910203031664106d49240115294031044568604484222100c803454050030402c04490b2800e06004801c00803070042c1c00315078020728000380c2141540030b51480003c82e00071640c0e8518070f556104020900c004c0160700440c1c8648400c1c0800d41042d4040c3d0000383d010320100003140160742c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507544100 1250 507542850 507542887
    0x120c010c03050405180103031704020319023f0705060a1107080105250c030206040b09070e130c0b030411040213050607030305070f0207120b0a090c0b0904050c 70
    0x42840c0c2458292440d140a40c0c460189400840e40540184210320400c41841e80580c102da0080d42e0b5000380c0e008128021000040950740650550090b1410400444003111945000c2d4806040d0356400f4150590141e02d4544881c620030b94444091550943c4880c41005001485000c001800d5080c3c070301800240c99214005164040c815617030000d2040c61000d1007644018580c90f4001d10840c1fa10000c00b03011104419682284e4100c040c41460040b031140f9540342c004c5506400034405602e072615809600d450080c0025018440c410340400e94098000d00d19002e10070041000c1c105080f246403040800c2465004034691000c10b104200c0490012909000c40784426900140e03550200789200940803900e410060704440002003803410103925034096841800e240c0d40e00703404540809c10880c0c0302e1440e4807035070745c440031400a0319001c102ea02280c603400c11544c0703030300090310000350b62998091152a44030400101d4045149c100508150080360762202000442d14504508036940c18400700c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507545350 1250 507544100 507544123
    0x1101060b0d0b030f060a02091504080d080a1d0c0306220f0f02180412020c03101a10020709050c03010609060e01031e0e010f023a02120601030b12 64
    0x1030b110090340b51140c40034080e451803407000a040d14020f04e03212640001950062803c640281e46032000d00d003100550790709550648202a019000700311110310111442080030701010306090761103401700300c2e00b040700e040824154030400181c0200c10b43d840c201800c19100419078100c0d840219045401441059031500c90b2952010403000e80c00100d090003920407000c0140250041d442043c1e111404c000841d60522552250140170f05100103098204d03140c00e1a110003641550100c2050032012503142c101502039203500c000303408011041c00014250294003001c0c00b02603007000b1400d001708042030064950050045040b94990351420303000601c0a03155104110401900045d4244d542e0b2081c1c2000c5406d0a241c502000c001e030388001c11030000c1599800054882d8039082c0100520800343c002c0c0c40001052405100704a4046007802c0401c404250544004166440721002c0c0c603600fa00c064184402c0c11581c0c130081d8038007240007400319001c0d0088180b142d004411002e0f0b8070380002a8440442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507546600 1250 507545350 507545377
    0xf060e040807060f0f02030603010b040c020c060f0c0d050307020f0d120504060e0601030503222103050c060c09010e06031612020d020f0a020c0d05030d2309010603031101060b 77
    0x21045803d05500500900400031201410074030b00d0b020448040c0c01441c0a00c2c0102d000300311401440c020002111014140a0b0144c0c1040100342510314020000e0402c000f064070035107162032000450282031048580c42d200c0810b0303010080c00035140e410030600d203803181a1001000300c209040006001c042d0030403183c03a512a1204c00180810845030010001703040341d80126078003940c591404a031240c109055407114980301d550a0101c035851b18031810129502c681c410030400c000440450a1100a402e0503024410200310014010b00304002e174034400c07940040c480d40c903000104001001e8400981c0d84a205140c2402032208001814281390811038141c10f100100400c0c59040d01d01900601080b40d86492001c9542206c04501c1750051940c10f0760755003913840c0362003880304110b07a00c0702c82c3c4c402a0040e8000c0c08040202d9505522150145101c04901d4010000d0b04d80074194412080320b0030b40403a51070b80741c208105034001c002480d21010f4800240003940c01e040840701280100001050f51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507547850 1250 507546600 507546607
    0x8121e0103060b0a05032b02010c09030f02011110020c01180203030a0c050712050a11010906140307030f060902091e030d08040f0c061e05070206030103060b0f03010f0e010f060e0408 80
    0x10f550324900540001d02c005025910b031880325440c0d030706521001c1d64030000b02e030815000741e0113000e02c11301c074483c0c40300281e4941d0391600b404c41d21100000c00341c554040741400b281074482d80070660100032021407000a518007681e9416505800ca007525903090560300c4609000000f040141d4011065500048003032400c048907072501d0426901d41340455001c2e1071110b0724180f0f441c05001340070504501203400b83c1418804000c3c0c9100440e90004503211700c40004020b00d017161a40241d98008680082207850041050bd030314229980403910f06520100d042e5600161580c014201601c0742d0400c0240c01782003100101440002c2602c5440312003e0400700301591000808100c02d040710000d1041d000745204c5c05035030316401c001e0030303441a05941d4080d0300390000a21079414450310442c0c082e03d038098412801d59207903540d414040c0460441c220b5200c0b10002914075592024420481c50b60418a23010440b1001030321401e003100c1040351910350741801c00748107002c01c2030003400d1160000d5224600d15038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507549100 1250 507547850 507547871
    0xa0603090507050907110601050909030a20010c0e03010c0807120b01171314030304031707050705100f0b010c08040e191a01080f071d0d0503040308121e010306 70
    0x1000900c3d003041c0d51110003801480340c0958002850550741d0b500c842103890310b98031081041f9550208807804a1154010040029040d2049810100b400154141403d020000b082e4260960751001c0358a0000381029249400c140340900400c0c00903181c40c1002502d5081040303004055440406006810544030071080c40713030707034031504140c2e80a86011042c0c480506000e1040c22076139036031180c140d0301030760074005a07045d40101000b242e001c0c079030644820442c0c070002800b00507510001401d407818090240104004a581400329034489107071400c001032456290001842203881140c4c4043c10400f040406000041890084509554240c440d1a0071507440d2074041c002081c003500200211410040f40281e408104100c400034800309817101e49031a0380da400c0741c0b5964982218000c001901580b078404103034810400c3c58114071000340c4503410080c1307262109851648254002c40d980d000000c1d90385d2044c2441806242c00c0a16a2400240d80d06000e1412900542c10b0201600c2d65950f11590007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507550350 1250 507549100 507549103
    0x380306011d010c15051803032202040e100507030f06030525120803041707030f08070905060c06010e010b0a1d0f041a01030e07061b02040f060b03160309020a06030905 73
    0x6100c2540304013204985105000403030f0203020240c0c6c0030f410b00d0884c4c80c82c11600700e4000c8240d9200718a840d4441d20184004203550401008004050340c009503030740c0c04941096000c0c00030038421101020003142a040c4a18000e04030381e0002c6002d1070030380c0303880b0003400022400f043e8100304600382d06032508401d9020b00000d135805c0c40c4c1e41c00108807042260142041004180c0510300c101d003c0e5624603030321100501000c1140c03141040040004816110308010f49004903040780d0000c8407443c10510064a4001040b2258800c03c40303040d5641c0b103c00100708180305012401d0240c904a40c401e4203008142c2000b1b01051040c42c26107051224503110f000b825214403201e8441e94400802c244201c08131842c0001c0303000e24a004243c002030605244100030100058000111045a0b440740001c00c05030750b411201c0b030000e01c401c0f40d01076100d843d02880403401380190000f400e80280744907940e04001181c0c540445400c48000c01b85400c041d908009030b62100ca80408a035682e04006c1618030306494400d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507551600 1250 507550350 507550367
    0x40f1d0705010809102304030909050a0c05030a1805030a020307050118320a06020a0f030509070504020c010f090b090f0d09090c18031b0e01080c040e0304380306011d01 74
    0x91609440b1b0100424168404c0b510021240c040c502004907072aa14440300c02d6400400803a000b080701040450000074540d8024070245415035100b00100d0500e90f0b0b21800c540c8034102c1b040040c0c2c00400c4020038007a080c414011a103403104446044040c2603560050204601c0c059200103420b80c002c04452494141c1e00562001c001c0b0040d503018424600d4a0b0000790031981420b400140c8000c030700b13a42c2d28020b1007802d004029a000404000345007d04000282d0300200c180c019654807203901c100300c04070700d000b0801c2851041516040f40d1408031806443d09014511a0b00309501a100c15844580c0011408060b106042070204044079102c0095454503564903c003c01002081c50001c01e00100396410102c4100c11640842c07a160b0f0307505482d162240a000c1c245154000c011045101c0c5802e40c490890780318040182e90500d40d9a0300e4841200032a07034402140014601d1071303400d0100710240e40010720f050f00f5100d40c2c02c5080c0140001c1c940c0100813607106a0030005070761a5075907801221071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507552850 1250 507551600 507551651
    0x306190c11060f073b030c060c01050417070b010302090c0403020607061d01020a05041e150f1713030e0103110a0c1101210902040f1d070501080910 65
    0x21600b040c1451201e1140c200310454400000800302c00c1c40180304541d81c407500289882808111120041041001440014244000781d141c4209111225240c0f240c80c094203204000c080009010b01d80750429103029440c00450046251040008a0008004800b81419a9019291142c1544d5005038070507640c45640c2001c0c3d800000440c2074005c201c0a03030040352004140e0382d0b2207400607a604603014280c2c081e03841080701041040c002442188148240c540d1003401c607140b210075042d40da00c520407019041018410000b03110651182072690808030b4003204d6440d2401a00542c5010160503007283e909400080400084050f2901ca6038441d8000303c14405940001a60340c0c03410560150821010800031180c004001c00c80000300c0d03020303c07211124001100700e0391b071264060b0242c14008003c520b6089030700076070700c2404a010b0b45440c0715640d5410010079807401d03502840b401d031b02e26090080e8001d44c1004070050070007012090116040103038404140c0003249044400c0100461628180303030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507553956 1106 507552850 507552853
    0xf0304151104050310050c1b0607081f170c04020c0109050f070f270912180807060c05010b04050408030609010902040b16030219060501140306190c11 66
    0x203588018014011807900c0d04023824003010150800c0e00104680c8000c00304040580c1001d41700703400607408034550415030b4200f90f00d42c981070440e004400e842340a07580401c14038201009801d02140c0010300039525400d0790580707030b4020041d400c0d055035079108181c50084041b40105184041d110040903040b0f101d07051203138401c1c6440311000034900444918842000040261140e160b50702c0c407996411b40c1070f04c40110010001442c10906c5003601b14030344000c00c484180028582c1c00c83c0c5480c01c25030030300921401c005006021122000782c1190603e4100410880220010b504c1f5140c100c841d0031807039899948000880c00740340110f180546040100d800c1d50b4109000d804800c0d8803e10448030102110b50b07034014101c5030318208441d01504e49005101078058444410200308e0154018001c501d0100040800803401013960710080350f441d40740c0c032281c1d4441e45044504458010 = true := by decide +kernel

theorem cover : BRFrame.Cov 507374100 507553956 := by
  have h0 := BRFrame.cov_init 507374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507374100 ≤ n) (h2 : n < 507553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
