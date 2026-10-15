-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:54.126742+00:00
-- url     : https://prove2.me/submissions/a3d4cfda-b25e-410f-bdab-1f7fe9d2d14f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 940647482 ≤ n < 940827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 940648732 1250 940647482 940647503
    0xe09010c050d0902180c04080105010f060207050112020705060c0c0105070f1409010c1502071a010807051e0a15030b03031312080f2101050d150c0c0804090203040308070507 76
    0x4810b203040d488114014001000c01c0d0580e041510784140d600c00035101103c40380c10006090100070400d0003054010f2115002c00c8078050b142c404005e440e440320380900c50401c0b000f03241e1070b008a1401d8040ea2191034006c0142c40307003400c02d0075902d0703540c0e4040384002019500709000125030350b015507420b140c038440e02d03220b40c0440e00c0603844c600c0b2a9402a502c0b14184480614070300081070107003000000880e48140016030f260300c1400c0804900203840180041800e0f0400188412131011410b04c0444e0401c0c1c03070321000000c035071510482400848840c40d030481110361000a4812070345103a030085070456282000088040401d0545901c0340c01456041120b142c10100032180d5244105042c03503002d56180381c107001514103520110383c000703040f022101c001280610f48441f0340c000c02c0b60041c8400c560101e40c299031b95450100b003071701100213030560564610751841950b00602e00f04150351307030040d10b03143c0e642d4032201750800030340064070b054000409a03c001050f01340510100c40150307800001030700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 940649982 1250 940648732 940648747
    0x21030f19050c120318060108060f010e0714181009060810050d0210020a021f030b01053a090503070605100509010b09060d0504050a0213150b091f0503010e09010c05 72
    0x1682c40d4000390512101400d00440c0c5d107220300c0140280c0707018109442c041c108505148000950300003068100c00d450440c1a03061020f003d40004020110143c505030b001d40303900c1c0241c04004244403c000303c50b0031a8242020380b025a61100c0294140c034040c0e12103501c1512100314058640d0000d005403504240c03546d82c804003500d0406641294040303144115528075800d0b5020810b455551035001c0c402e05600c200040005800d40982212101c081c40c0090a14200090308140c80e02c1d41e012100101c0300e00c841810000c0500e211115410120030810b200081141c03610b40d50740d07440141c00341c03041032400300030a0b0320350298000da034200d1300001c2c0508040c0e403d221240c02240d100d585d410740e0002040115135580020b078050140b049000720082d18000038107005011043e0702d00b0314419005c07072510840c0c1c05200102c0c6400000d503454071928940b42c00e10301c4049521400320781d61a101c0c6a21400000d80760942c403500541c186c0f03070310546071009034030b80684460a0300d1003c0703c250040f42c014020f6a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 940651232 1250 940649982 940650013
    0x5070e06070c03021909060803030f04020d050c03030f0714010209060a08090709150e0f040203033a0606140f0307050f071505090c01180521030f19050c 67
    0x10109240601501550250740780e001600745100d00405d0a40034014803002c1042c0501403050300c0041001304055481d5181c171047c51000d41d100103000901c40c0440d041804240302c0c00300250b040707089018003101e50b22281c1c6400a04581c00c0740004032803000d609000302c3c040d071708180251200074070084c14460a0a408940a4422260003041c040705880b9542c0005002e9880c2c0c050b01494600004580c52900e00382442c007907102c0001480c1d10b141c002008240300058800000702d4030a8401c4014210b1408103826040d41c3d445064800c041d0060b140c144208007070300d036907408242203400540783c1010102e01003c1c010701c5c03402111280030801c0020702c0054205070054004140d406003150314145800c7c803980d070781030820643d0b00840c0d41c41681c410403c200c1e000108090344008409003482c0e5400321103030745111a0001540035842c0039444480f6112500c4a01c1c811240080303c500069a807100d00c0000b00280b0b80d0003010320190542c0024440902841c006d50480b000c0040801c09060342e8914103a90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 940652482 1250 940651232 940651237
    0x9032a191211160303030903121401170304030212010b0324040b10090c0228020913030c020a1508010f06080a0c091a090406080f030307030e0c0a0806060a0905070e06 73
    0x780302c01400386100c0003003012074a000c1d00010790701c17075100010780080c28203000306800160761f031303840d081864524591148001114032604680300301c0c5a2203c19130300b101c0e0050441c016580300a41000303007031080c1d150160703040d0010f000f0424141e0407541440440740c4440d40c015420602100919104e2010401040314006015800b020000c0c4240308503590b2501141201c7c00c107107540c070060300055800b0070b025200c0307404000d080b0321034181e0003098030ba650009944900040c103038020304004c400411b010036005000c2c4070140e0750001c1c241c444096079038000c0d10f000b152403d20000007a00400000c2503523101e01b101c03d0300750790f207d9030f51410f50b03a903084411300103143c440342c5c3c04148450040005101110304100300e2490908080640d201c50814042c002940c1e03031504411465000b5448801c54a00000700f41d0b540b00e100e51802003128800c2e1040c00e82480300d1001050b0b0010b00300180400c003014006a414061072056401108296450400d107044403401d407004000a0f000e12604561440c02001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 940653732 1250 940652482 940652507
    0x30c030a09020a15020606030d0e0103091a1801110a121802150d0f0212070507060f020d06031e3909061d06030c040509032a1912 57
    0x2000240a0210307000643c0c52007966010204080d0258a404030f621790520a607034020390241d004207015502480f0180400051088503410960b07030312850002d1001600f10490000040b00d10143c1d6030401602411951101c1c21584110798200305c90b0b00d40c1d503100c150407903603802d1140e035503151400d500102050151250006030140503131418456805070b13803107500400f108504907082940d40c03580b850030403041d580781c14214220750388140b003e500b5085448102c103500ca950fa150a96030b40c0b4003850003c000f444858802c9000c14030206065400d008141e000000f543e0182c49088080f04c1c1140000001480c9900c000f4001854494071494a0090000900c2d030440c9002c440c1580c041c60784c42c8480070380760951241c140e207519542d00f00302500c804414040280d003a114559060b241c0180482d0303441e05160445801150780d1800900c000c40c040c020b6405843d002003019024800300800b8011002842499429901445900d07201d6a10703840600094a81c1c0071065400c3c0113038640c0c081c0d401e00c2200380d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 940654982 1250 940653732 940653751
    0x30b0a33050c06071107080f1e0703050708060601080a0b0d021215100e091204050d080c03030901050109060503012a0903120f0f0306050108270304030b06040506010f05030c03 77
    0x16084083c00b845119074281d030341e00500c0c04568140d03240ba002e1298040f45198200c040d006440e1500400c1e82059411102980328100350130140e8646807000740da0010781799024114001c1035880001c10818011002684da0106030780f07447d004a422500002d000b00c0e40820031420740d41c011308220103c03d29400742031090380c0c1c28410300d0402046604045410300e942c1e0844482c144a031a0420540c44e40010040005205a031210004041144118007a2910801c002000360040101d00c804a03583e0801103400c1c0c0362a030800306003a074040c0000f07001d0926003508020021078581414420a1310109817013112107400030002e5410301d21a4842040d000030002038480c00700210b04401205043d8003840e0723480c040c0046440310014084682003003000c0400d07081c103000308810381c0d0280c20260820804040400306102c08040540c2c550303000c000b01c214901021400205010321190094441c0400b41c1e400d004640c2c1e08001154840c0c04418003502254040c00441c8a0ba0260005140e02c5240c1d0f9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 940656232 1250 940654982 940654987
    0xa110118050106051c120810030804080c031c09050f0f0402040b04031104140408400e010509011e0305030f03090c1219060b060a030b0a3305 62
    0x1480e034100000d004003a03659039140c240070013090804040032056001122000c031005a256564521141e860740014020021060041200a41e219050200465110225990326562502c0403602e030180440d10502c240580c20503104070780703108010465100710594a52060a040c01c08121080c3e40640b038141d0041003401c640007003500d8a10040001d4003480d01c1c003545807031540c030388200190700f040710301030085003042461505c41601c14802a00b0581c0700903241e44910a0103890800d113401c08a401c2c00000310345000c0c0ca42181c0351620b1180d08003240e400314101648074518250745031001e11585400130a444010441074030707081e0038a940c900c4680d0860024543d03980f613513850b50708502c03110b40200d0800000d20100d550300708445a201481a18000da00e8510902041d0b1140c0e0112100c0d040352101e036651808000d5107178411002c0d80001418280c440701c940c00018020018400020700500303400c200441c94007031404001c1d034100d078641800420b802c0020f411841c00e411148105003448810f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 940657482 1250 940656232 940656251
    0x3070b0c01061805040209130507060f05070b0f07090e010b041403120304030215160c06020f0c0105090d0206090715050a1b0b060a0b0f0f160b0106030c030f110a1101 73
    0x34a1403940b50030300e03d46012035941854010032120103409051240d90080074002400050002714540f011900d01303041100c01ca42c02d40e1020780e903078400c103200204256003040800178401690550140170354582e81d24041140d0301d4821030240d103c0280141c0210001c248400c00000f0040f49448100310700250680d070b410300c0400c07500c810715041580c0450158001c441d071540260500b1402540c0310716410360f501c3c8401484a0003508010803400090725840d000100c0605d0106144111003205007000c000b04030724608035650325154008080843c006000d044049601c0000c00607620b0203031910103541108200510106071407590004400e0402e00024144611032030901c51007002c2910701034080107005161403002c002c0001d407940c1007130300004000c0c4200b240300d40088041c3c403c0c0c48036040286a44014002c2d01420044003003400415626043c0c0021815980c0b42d00000c0c01c0442c3d0362028050f04405881003400e47d01500d088a000c884240304100c40e840c441c1103203541e03003540000000f590022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 940658732 1250 940657482 940657499
    0x7020f150c0f0d1d010c06020906130e101d130602030112021513091e020a02030d0c1e0f1e050a11010b0607080304060b04020a09051e03070b0c0106 65
    0x40010864160011524400b02a106020580c041129483c2c20348a0310400441c003251400700c811018100000030800c0c804101d02a03040b550303500c40080407951510318041802a4610a500408000c14440400714140d1110400007a080d210300400048502041001010700c11500800140109511021700004a5064801940a81030961038042021141c0c010301268200380303040461183c1040142e55076410002d03400000307644249101180400c8440c008038a0b00b205460300065081c800910816401d400000400046114000500c00100362140648480d00720000050b200b040420340c1d8420301d03200e000003551100c000d0620110b0000d003007540944641511000c41d0105100007003202e4415004000420411f002c40700078040407940310301103042e90294100042a602022000c03904110450f0881e04a041020304210740b101080d407801000183c4e58890207005030b200549010203504d001c1041e00074404080c0041c24254540111f843c0036901424405055540c0c800c1e0100c1e2050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 940659982 1250 940658732 940658737
    0x50a0b0c07150e06060d050606040b04020712090f08150c160b01030b01060215060a050d050f030f07150902030c01050a090e1f0608150f0a05040e060a0b0301090807020f15 75
    0x100a903000418141c0010440e103004d1002c5c00300d620500d05a100c00c0009000001e40365404079080d5401f094110243c00414068010024000d201d009001030303240078254000244811181d8141000040a547ea8582525142c2088125101d1116100000e000081860003010024000390300000600c040b0340311101540420380045070b40c9034902c001040306960400c0050305104803014242b40c2400c1000c0084d6070040d041c49400d00550144ea03032002440024400000d1a44102007a03981d540244110004507a204001c112011907440850340010300c2a4407030024a030341d01800800032000440d00555040d00404c065074100919005c2c081200030a041d406405000b0784c00c0c04203040300003071100705c1c1c0c04e403820380101e01005550b50802c480d043c1c0303150310036484003001e8410002c07080c0628007044000000342c00454105041c00441c00001d107000a0b058801c4044140403ca0740402008042c00d850f001e00020b42441401e000c4c4a0162420180c01080428000d00725445114440d50361120354 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 940661232 1250 940659982 940660013
    0xb060a0305060a0b090c0a020a1202120d0501210b040609060f09031e030c02070e0709090207050c100914040506030c0d0b0f090c060301060513031401020702010e06030103050a0b0c07 80
    0x356100c6044c208542014012150040c0016400d1410020081c1000307550780b800c0107002c2d040c070485102c2601018028420781d08000214070400d5514036040d50b500010300801c5c4a00f5103804119417000e10f90503c158800300c0711580c80b00e0103101c0354555484034400360040700c0d010b981d540c1d40c420340d0240314440c80c454104450b100752611801084200280b17503260118034100c106160130440c00c480f50039404195041510090030f4105042c0c0c07100d0b14211001443d0343c000e81510343c40058044240003001a040500710300450359842034040d1301d0380407620b8820387c0c42108030340346400380510318074a040d40205500c400007800321000c007a00d1783c00054070801417101c19102e89107440c0912150054040304194003454420003415260031181c08a15288014443e4000b0000041104401d04280f880900700442e0860b1007410020302c40705200b4002e621403101203000c140400015005828054252030480703421002402c4500c4040d2075091005100800c070780310683d41041307013900040c00c20040d186070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 940662482 1250 940661232 940661251
    0x30c0307031509360f060b100c02040c020715110109050102030424020301080606060304061d0304170f071e090204080106060306140a06031d061602010606090308070b060a030506 78
    0x10180099400d44d101d101d07290700321600d5042c030400e04002d400441d50003114903500c40c00d035140072440b034102407004141c0d80d01c0305540b00020a18505c1c48551264000030024000c0701c081000b4001240241c0e600c182511483c104410a81060703000381d801416440b1031242245d0010501c9449540e443d82241e00840c5c085654819800550704152010320b0794070710009280c042145554141a2050b503500002804144540000000242048402d4018002502c2030203110003104d44002c0100d40c903904540600302040c541030f100000940c0300021000980d0002d10b01620400381441c62008225424100b5262086841400062118500d05c0100020200c1500000300d090a00100400380e0710182e00003928111410114440c0d903485c2020101295480c0c00c0c0003c108000c0d0204d0481569021f0701c0b403a041c01950204140400104925909040742d80e00030081103072a85810703140f55005003c082c1981d10140310f03a200084545150641040b0020480c068244d521b0781c1d22803400500f00c0c2c4900d0f6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 940663732 1250 940662482 940662491
    0x121d010207140d090e040c03020306070c02030105390f1b010c0c08030a0c1428080f0c090d02040c051305010e032a06040e07180b030c0307031509 64
    0x18412080303040680204050b001d44005600150000d101c3c0c0c4503805240c94110240700414100a000d0311031100035903016041d03c84500c0e140c04050540c0090600603800f03942000c0008078107860b0b0b000d18000f10040140d0144100c10100c2d000d98000c42d0300b60828031110010400301e4452400d4201038044c284072100d564176200f10900c0000d0135554100c0480c0c042c05041e800c0740d400240c550040d07941c0310009a4001030784400708141140e101c0030011411801c1c07140094a10007490b45c00f901d42c0d00054684510860840000f0000c139012581101c509240a074104040340766a00201c00501c95154010081c07440c0c075030710b50001411626480081c002090300080c442c0d20010107424044010403003420f102c910705a4002c0860745070742c5821480038106c00c45800300038142040340d05070b010102018020f19103943e1100d46083d0310301020b440e00307008140c01c40c00401c0800c8801c0c80010950b8140e0003592300b192503980e5014403903080540984141620781288a406080801d044070060054a02c0402e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 940664982 1250 940663732 940663747
    0x30f140f07030f14130312060611070b09011b1b150806010e060d02090d15052a070609021305100f0501090f120206070c06030f05090319121d0102 64
    0x10b0403100c608021403842c3e800c2c9100f04040c2401a0011035000521201e00303880220a03103004c4070000d020140354030400d03207001070118400340d126042085215502e01200d01172038903000c54403224050070009600150f204c58143c1400c1004410000c522889682c20141000c81d690a0428841c43c6400c1064044500c0e42c0c180c02c4030f6800217401d90450007e080039800e00103c0380100b405807080f0b01c84c5107106900082c45400ca511502000701c090740d00504103c42c134160a01c2808003404040e03a00b544010410340350001e465660401c000e030000400864603207449019501d80c005415004400d9a00c1510791844c6c0842c1509806080d12403003d403a09640380e03608110150841005542005040216559040c4403081203440d042d019242805004051803800e480042d03001c0c400c0f00700003856003001100015200341c240c2c00182e5540391038801032085036a0030103226540d001c1d02404101d1003210031529146540900203448403810340716000314103104040f540c500d84070444a1a00d03036580d40042e440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 940666232 1250 940664982 940664987
    0x51207060f0c0e0a030219080a060b270a0c050408010507020607030c0203070221030705030a08010e01051c2d0f0b01120b0c0a0504032108010e0115030f140f07 70
    0x5401c50b5060500703501c0c03070420b40049074078090103000081c0a800303000c240520940c20601c2c40c80080c40704000301c0d000c0c01920b1074900042d002d00b01500380121903421402480903141c0f8031803800c10401a140d642d850341d0740d1034114003070501d504048050080420000c5520395080c090302e4447e011540080100c5e0900020040884158040010841d0010f00c031040040c1d680710010f2644c0748805d035840ca031401810341c0c1603055202e48540241984000941000303503070b41100b80103048070505440c6800300d030303a100180840c088408950901030042080d8010011300040011001801005006c420342038180b0402d00d402400004203441c3d40360101808070401c4000bc1416016064000120208401990310980c1c5410302402d03540341d04002003421524a0301c00c0c0152401160048401041d103817116aa2540701c117207007004840000c920900110301201c1540320541261250203400ca25000d105000324002c1c8284031894152035180c1029000400c0c24015650203002a481c00103420309203844007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 940667482 1250 940666232 940666241
    0x302070c030609021207050d0807052e06094b09060e01020a020c15070b010b030610030b060f13030c0306061509051e0111251e030807051207060f 64
    0x5e8a000d40c4c408001840180c540d2000307182801c2e809420161184602e03d001d0741040c59298a0300c5c210500c6070ba0004000c21802c80084010308600010004151110400e03016036042c1441c001091400c80b401400e241c0003e0710040340b085281d004d40e00b10700c84000b0042c1c6900680e0010303148003600c4156600c24014240b2a030000249014000c500d000c112010203516070088190b80c51084280250b0310106503803220890f5580c2d0351180b650300c2e4941e140c00c210307045604280e030345500452101d01c4a1103024040d10892200020082c8941c0c20441140e80c0c19851b68000300040600d130b0143c48001001800356909000650301c941c8012910720b00b0b0070b400003032000410b05a4020040305800821003074403542107403135115030042c079a8950400c400b00141c030040e121a910700710902c5a900701d4901d11030960907040c0319a41c0300c0007245502e0364074000ca4a01d0594a24070b00d407801000c43c001c0000a030420018041184580d0a41d200c828201100c00c2d171300c5d00207200540e42c01d03444281080102459109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 940668732 1250 940667482 940667509
    0x801061d030708011d03070c09050c070b0415050603160b16061e0c14071128030b0702031e03040f0f2006031e2208120c0301051c030302070c03060902 66
    0x5500f00901c94484503d580346a104d0350810b103585101240c0c00400c00700841d02000d030040c3c041e01034ed0a06e40340411042222140808070207251101140c0240340102e40d2000402e41c0c0c00c0c41c01c102d10300302440c1407003942c811503202d048500400030100001e4441d00520aa0035101d00004410003094201042500d170002c01d440c0030040127180c518403291a65040d01e10300f070740008400381031040210118055031810710018466200556010121004402c594010740384594072015076034852480a03640d0f07000f03949404025001d600d0400d440b14000c140a55030060141d1a00d01601050f6110011a98203a4006550100701e00007414404241e007140185051019644503103540f41c096100075040140c82d0503108410710107804501c50000c0c0101c06076025007d0803581d60000101e00c0d098401d039002d00c800c9905808000005201c4040740c00649040300c034050010825031000a542c1d03000c03503c150360b085040c99402c0c010100030602c12034006002c2c5201d0100091507000d20300401100b0f491411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 940669982 1250 940668732 940668791
    0xe0c1315090e0307030509132406110c09091606080907050a06090b1308010203130218070915050c0d0903022d0103110405030a0503090901080109030801061d03070801 73
    0x20680060700b00c000101c805040e01450141d4a0300f0080f0000395820b0040c140d81c542850411283c00342c100e101e00500d88480004143c0341010603642d10058804c8140e0408402c065040f40b1005595401c005041a41c04000b130b0b4161a1102020444c4c503400c0c900580149000440607001c02104040c05c1006c0c8002d460704460103080c0d140f62982c010402c110f94040c000308207001003940601010b00d00c00040c054111039009646a180404224100106011090b44242a55402e2408010162440302c0c0900440d980d181d480c2401c0000f208140441b0200100403c9020003410701c060800f44090b110380001071342da42c03440c1c03807450040050017403d10b2004034045001800000b10441284c00c1b1b1240341c2001e0801045403a00c4104e980e40901441d449030380c041c00750700e20701c2041144c08001081c0c1050111028502030f43c80b448960300b281e14840c4010301003100b500040c003040f4050100f04556906048541445c0503640c00400e0803c2c005a100d10f07401c1e91103201d440d500c41c0c200002c10341c1c0c00720350a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 940671232 1250 940669982 940669991
    0x31207171312030209061b010b0a0509010e07081902070606171f0e07090e070e1b0a0c060209040e0f071703071104230103050715050d0e0c131509 64
    0x15140c020006002c1c9000034145540004c940c4120344070039068500c0d015800003c807951002c1202414040c1c51101c030320900c80c3c80c00d188045024986140350b9416940f01c5c41d80c01c0382e10750300c01001365040e80c000307803034444c101d4042070b0244007400d0303c2e000918029100750b001044d5140390031280d601c23803a9004000c1a03103400090701d4080042d403401c2e100c024043c45103c08102c0c80c88500d00e450500000703400404480b420183e20f261039410010305101182c8500d031051010380d6a803030606544107190b0104100c240c204012080d0703900e1007444070440c018043c110040c40c141c4c034140082c00700c41c000b2030355104a42249103c03144031030f01440480020402801807000a8241c00d0826450b0700c02c03490001d0070001855200022615140c0c03143c003d0796107200d182400441801800203000c40240310848031440b8075500410f404110300c090039103103405621800c5c1842c507040b11600140006c001d030424a4812025001e000c0c2e691586600009900c19a0001e5820022001310b5001d460640080b80402c1c1403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 940672482 1250 940671232 940671271
    0x709050d12080610050d2a08150315011406040b0706050f06191a0705061f0501050a0504030f02030c030d030c08160219030302122d010308160503120717 67
    0x20a041350f989140a10740004e200040089218000355021440c1c0d07120301c1c1030300300c7d0015160005210f40c040c0c074000c0403110b4400340741c0041550f0340b40740c1c5403a0f200703600c007030401004842e01720044880c01420003448603080540302c4680c62610380118030180e880d20b8480e414020780c01f180c40d160702c0c0c00c40d00c243e50015600b20380c0388550a1201081c452014164001c2d100d004250700440300f43c44101c1c0c4d0000c151805401c1c198800302c90150034100203801c01e00e00f1800001d55601510071989440c180e922824106440e5464407080b10350302c1041a601402520b04170b41e15070342c043c40180103440151b1400980a0412240184500300041c582400b036151100000c108540000c0d07104100c1c401d82c00210b642e441c0c2490220007902951f0340c54141c1711a202c050115041e0802112004403440d03200781d5030820032840420300c200e5030a10001d441c001c0d00b0010a040000c02c2043d42091a0080e42200e25210110101e01c010100845051002444c0c1624400301000c03040029a0400c2411003c0d8a01121 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 940673732 1250 940672482 940672487
    0x20711010e04090c350f06070c0c050907050903060403030606030f06030203120a12110304021e090c0a050c061504110c06070f0e100c05010e0106080c0402030709050d12080610 77
    0x854003801c500903c80900400b181d0703d103d910710800b05d035880864151101c0c109500d680d155000e19035590079019107000100924410380460440542004202a00c0c62601e01801030000e80034007000200401084280b82c50348040112038052842a80d000403100c0c0b8000000302184d101425070140941000d0042003d40d60001d03c107054180100940c41e40e8100d0508262407403042403ca1418940c00c007403104084404400145204e11300aa41080407a000d402c2100c03a0600c0301c204840d031041c040b0010800050146015051030b604608003079141046850041c0d160030f100325004910a096a110640e85050078028043c1209022111a00301103655000c03503200c0400503d901d040001c4150510031591040056001401c0e010349a9201c4680d0340200a03c070070b4108005550560805504400c5a04144280313811256171740e01034900b01c3d8035a03007004003075030014045000308448864041519034813101c0f0719185c184143c0c1d0208520301c980c800030704010b000801551117511107080c1c261441c1d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 940674982 1250 940673732 940673753
    0xa15090512030c072c0c0414102f0f01050a0b03060717040203030d0e0a03180b0702060c0f06011710050609040206070f0803090109110a030c0e19020711010e0409 71
    0xc000d814040e4031600c5d201d1001d40e803003805103c8408040e00440a0002c620301303000050054522080444412048800500110310300f03d500318400a84094604084008181c2c00510080248103426180d8900d117403602e40f4040c005628480e1036503489042c464808a18824840340700002c1d0050f00e124a00030002030701c5081005210526484008005011542c00b40210340c20004880420000e010244000340e41c0c8000100c2c080700864043c11605101e0140b01000d1003c0300e5500108a1900560340e003406003e070084c1c80e4110f9280b10b00089103489180600c6214064812170442d43c6005d10306c0c0450700e281c041000a00d604485c90501884502d0721214030300d551207a0182c0c0c8450340e8140a140c0300c604030040c1c81000c0e00060300070003031225040040d0000041640101d0442400c880c0002c10008506520300c0300070068410007c0800c0b48405211105911102ca000c021802541050b50780c0180d030700110086420201c417100b030800039038010707200c0210900141e5042125846692340c003003086 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 940676232 1250 940674982 940674989
    0xc0609290d2912010504111311070602030117011e0e0109060e030c12030c0405010c021804030504090f0509190f080408030a08010803031303050306040b1309020931020a15090512030c07 81
    0x1c0f8040d611823424800c590b044000d030048a4400e2960781c241c0d40c00d00070000d410a018868202200016061070048140500041200780740d8581941c4019120940300503c01c40140540c01e548680200e000b0801c42e104a2041034a0349001d10f5840c071540c800c560034450449451180020140103205000103264159400d0b1a001e082018040001d130001440c5000c80827000404c080d080c05c00c010806138800d002e001258124041403014144180500302554003c44001100d540922914198038272210003e01d00300d401180032300858202d42c0c580c5266648590000001980b0000d41c6411183e4042412030040040c20b0207581141096000c1d0a90300f1a40c0c1c00c06000c010020003c0381d900ea0301c580c04810703951030091043c5040343c0c01e0108000a4107891105034802c17900000002e42c6030040b4103412014800208211100e016240714010001e44908402da810148800303010030b01340074000000034203508540703804041528082c1000119907250000c4100d94205100d1412a03540000e0000141c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 940677482 1250 940676232 940676239
    0xb0325170a060e070903030905040e120f1204050a0203070504050702210c1b03011107030507120c12201f0b120304030c0609290d291201050411 63
    0x550310740d007036150050292074010a003a503c8550920002a81004450080301d100ea00d40c890103507603d004110855518890502050308445043c3c50f03003400e500003d00c0341011b41c4007681d00740040c0110f100c48501c021a02290b0303652010a585082d4641089200010501244c2c02e0045140c00000292600502c2c490086120908015224140e07061815600d41c00245011118502c0011100402c10b101440c4114001d5103842c000c400e44501034402ca0b000c40707405407522413802c5026980c00980489007144081041040ca10403800503104a15203210300d2141d60760a074580c41110003640c030342c2d555034400ea04958803c1c21161500045482034000a8884d1300380011542005404100080e240f54101a0103010010300481000008040308041d10402d9031035600d540c0c0c4518070b40700c042400b5807459100c2d40c100384c030f500e00c071952000083c48400a120801700715003030b40e601b801483c03400844038980d801038449094045801d140d4441950222503000a01c810f041c6074444e030b002c01c1742c2094410300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 940678732 1250 940677482 940677527
    0x1030c021b0a0f08211809060414191b021e0312040606030605161b05150405031b01060605040b03040201121406030c010c0804060c0804030c1404230a1a0a0b0325 71
    0x45580e264421481c000312b4030603000715443d2004070b1601c0d05180382c01c0102050700d4464111404480c89052842c0504103800500020480f0f00800c4c14101d01e20b1152045032001300100e40014402008880c00791b849074902080709402c42ca4003000340c5000911a20450700c80d500c1c000c103620b600040070083c004040c50a240010082c1c10014100141c007801100780703e1406050008100c80000140316800e0041070740c51202043d400c003107090ba0050b03c03070000000e005000074040c02c180c40d00210742040c41410003000c8281c800b000300381650f0280c00c014188004c19002c0007001c0c207040c0002c45c021142407810313506420b11680c84100c0c50145000c0d00080081172440d1740b0403c00132008450180d03400815440b803003a951a4000c0e0f100700b8600056000d03601305044030b00c02d00c0c40c03c220081080f103441d50744a41540c440310f1f110020840c20004220001c40217500809588424058101800c0c0406140e5540d140c810013021010841144401102c030f5080b2482d548150301c800310f4101181280640007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 940679982 1250 940678732 940678741
    0xc0b010b13320102070303020a0201140d05150906040b01120f060314100b010e240d1a19050904060e1204120209010501030c021b0a0f08211809 63
    0x40d000301542c0007000e0003003080002809106898503000780c00c200103180580e1103400100126100d003031502c0010056031141142800560091840400302951118024101491080780400b510b505548038004400c84030072400081c205200ac1c4c03544408140c405002002c8400002040c3c2a0640e15602d4400d503a211508041101e80d000a80210b030444d020b000c003e40e80c10384454440c1004008041894a8481d40405650281a800988000003444540c10314191900c0c0130000b401071511002100b810001026103035524855600440a881e40e101075101d501e101b403140e0040d0a0a82d50454018a582000f465070b071040040e0b80b2580c02180815074a62421906180000a0400c04420360f13001c500403550140720941882c00c076000316400341d4541d0b600c0c4015002c4424034008000140c10188007001840c003144a0302030040d00103041c1070500c3c2e9031508080313103003006500031410705e400c6402041051a202441c100a00c900f1408881c41c0000074501c0c8850040c103071080302d00945000d000074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 940681232 1250 940679982 940680007
    0x110403061e060303050d0b150a0f2a0b0901050405070312140f0c010c140d0b0112020c031b030f0a1d03010c0809010e0106050a0509040f0c080a02010e010c0b010b 71
    0x420401c0c10704142848155140d1501400c260000002212080d290408110b114074146d003600b070250103a28035a604c2c01941900403141644020001000d20801c500d2654070061180888181041d83d03003081490491742d8500003039040405014512903a06100138070021032000724013201103a9006074000d202130030f5010f0603a808181501824040c940c08600454000c50940003403c950001c00020071290b4100072056802030303e6060f20122420041c0318480c44042c1950210030051814140002142c41002d540030991f880240c1c211116000032803030001d03107121115020320070940c50016604120320700e280020301e40503202c0d0f92010041e41134201b1000c44000c64070a014008058000d000038800b524000c0c218807400e5560201d03540c648944011083d074107200306025280700406503d142842d0204010200c10301800c11355403c5904080c9000080084112500903d507030009007400b45800d0002400b1101e207004194148003054103c100000d000d401001d05441c20b46080940f900304c542c402e07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 940682482 1250 940681232 940681271
    0x11040e0a1415010f4506170c1602120f120408010606050c1b041803090501080c0c0a080702030f0d080906060904110405071115010911070302070b0f2a1011040306 71
    0x1411407403005e440c00816050391055500001200c1c00310a40a1602d40034020111445039414000d4064082900780c40140390034001d01c0640120706040703a044103100d9044500b88883d600368150740b00000501045410340a0240f01d0080104c0c0c14001e0030b00b490803081589454405d080034009524075500c00007150f40c1c5510020346d01950701c070709150031122850003500d0f1a01502400e40860305d10000078030341c1da2641044a0140d0074003c0030b0300300f0230002d50f501c00441c2c01c40841207a05004418203466258010428000d10700610341d81c4490504004202a09000c005808180500550b03405c0202080503444179004903d416100042c2d02d0745e0300181104c01720080300c0c0c0e003e0640a00c00e40c00100804200907641a1400380504006060408804501c2449201c0d03000340541c00c1404204011120a8050071b000040000e0311440c08000030350001e0240141d2840c2c12824003c80807000d01004204808030116400c18002c00c024001c2031115003075400346100041240e0745680d084810350024150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 940683732 1250 940682482 940682597
    0xf0501030201320a0206040c05040606020d0309171c0b18180c06270406120807030e090c191107050d21031b0311040e0a1415010f 57
    0x9440e004c401100039103510080d5020384451004140100d001d18140c814607003140e1490f0018503070502c9026050b0064016030780d045c5c0c0e071000012500d01c1e11054800007031200704034030380b0280d01040c1540b403114200c3d46106070103402074a203001c0d06800e16102d41081a00001c4444a03402444511000d0300c0c50050b01d604c03459004500800c2101c00c882031500450004803071901c07042105030a540a01040384c59500c02c00c00310303e240612003808104031200615005009142091248812030003203601c550041e0303070b03403162070200007030315032200d103034a41c110190501d039140c44c1c0250704a8841443e51500c5038000c0520440c51114000100719007190713036103040719403200f070345404050081c000703001404550b041410881d5045a103080252180c40f0f0580c44a110419560425003400b00310307075844000400710200195151884441c4601d40c02d01c0343d201d0200c1142402255400100061043c0043c5046000b030140840b540181251005480e032500e400160002101e440d141c0c0103000940d08030417 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 940684982 1250 940683732 940683827
    0x8061012050f010905010218220b0d1415070c05150901092001080711100b062502151201050d0804050d080a02060708070503060d060e030a050d0f0501030201 69
    0x11a1341040019000b0308400c140743c0e04183e144601210a11455201007440e0010f26010030546c3d180041e204ea200c003c81903006481e20394244019542c01516111058881040358400640d00482c1e940e00180310f60f01c03959526040108000d2642e40d0790b51100c00300f0034228150704000000c1c0c1d148200b50b1200300503940001410030026400900001303250701450b01c07070380000c96a20004100501a00c020441d604020f0700800b048030120914200411805505a038054020803140300741c501c1445548070004c0c0d038140d16a6103861540f0421910703207210100c2c0d000c1c031142848008030030040994454112007042c0d48050500e040d40c6049606c912491308000e80c464101c240c82000d02c50000042c0c215540703560202e03003da448251059a00e0642103803010009101000020a10b0504040c400102c40c49036130082100d40c00a00780078110f0708205003082c005030340484e08160355480350262821041c800a4100074950440c2c00080c0200c85000c61100c1040000c4142d05050103000d51418416030004c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 940686232 1250 940684982 940684991
    0x1090605060705031b0322090c0302090306010e280c02071509030b0a06030f0305191b080a020708010614010e06130501050c160909030201051f29040b0c0708061012050f01 75
    0x2c0c0030b07511f045505005846109140c101c00c81c0d075141c024401c442da0700c10300400501c82a841c000d61481ca07a04000c0941580e510040d2004525a103a864007059000090001084140e89003100038078000f401c0e80304038441c54647c4201c0482c0d03908160101d00b6a03401100d42e50142da40d04070064080c0c25039501c000c0c080300d00c40800d40c051650041c003400403000c49452110b01d6a84040341150080c81c0005001d00345070b840ca501c00d000400c0c60004202102c443d005807000a5543d00d5954211007096103d0440130b1070145415080f5a800103050301c1d503200c201c402038100000621641d01a42d00c40c02400d06002c00021440d5501c10304014403012855141c0d1110701132030722010b03042d01400580c00300320055800d00010801c444540403c5001d542400b4a011014624001c1000660720350308003000c02e03400601d10038030076030800280200040c049100c9a10f9942014000b054a0b0000a80c04030209030442c000344403400c20011884400c40c1d1004c91300302c00c58806418500c1c1040d81e0262807464a40c40c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 940687482 1250 940686232 940686277
    0xa030f1116080a020108010f420809070e04080f0a09030b090a03090b030f040b100302032b2309040605060d1d01110d0f0b060a030501090605060705031b03 68
    0x510503c20510070303a030380e0b1a141d0740c80302c0480c103040480c05a0410141501403031040291143c50740a100740d0180c40003103c082810b41d6010708400d60030069400034035034100304030400310104a07050082c58010354520203850291280c40301c0f070044501e0000300f00b800046040e0b43d540324616034405190001c0b403130510340c200b000581d41d44945000c4201c010581034080000c0d406440c0b02542c1c0300d480488900121542d03207a0380c5d2103400b0350040c100003492000a50102c00358404210907001013004200b11450701c0624003030381e03040c280807402d988100482d40281071a5041c0d1003124a03030755041c4d240c80d50380b504020380000e40a0a0f03e0f410440c0c1003c0d01150210041d03c0c0c0350018001c10000032424038155584280e05409c1c1e851031552a47c401004001d07844000d482a40a216a9044500300141070600076001491590140c002800081e48900060090390224031070140101011907030246050345964586840c0d0040b075034072280c0c2c104044010241e070a418000c80d06031162104009442154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940688732 1250 940687482 940687499
    0x20d0203030d02130b120403081f08010225021804051c0507060606020309010e01080a1b1e0e010e090a0e07231507020d05030f030a0204170a030f1116 66
    0x10b1142d01800c50440c0740001005e8820604460480300c5c2c10b0100c10f080d41d61520b0540b0b5140c00034041202d54155405600d0300d4080c01054040034005010000d070741c4000f02d1215105104414211490081c402c80c0080c0040e40c5e45444410a652103151451045d40c40d41082800c20743c1b03950480e01030340701054008403515400b01c011700c0c1c5076100b04e504120031a11003900301e07900e0155110890206802140c1c17581030350f0103001c43c3c542c80401e94501054840c0785c44804813a00044e203040c18045441d401e844512841c4880700c100350028a46040034849120304002031210783c040b08018000c0030104c0118099401c0d0b5004000c60042d613900319440d05a89245000702c038002c8246000d505902d02c8c08146c01c904d00003061700c000c0610740d15460f08041c1d141c0c082040c01003009604961900c01003048050070030b030080113184620b00000005803140c2c5006803e824036900300d0032030042c94000c01c0389800000d400104000301c4e0241840c000e0103083c2040c000344d24082c200c1030715840c030a03a040d0f0005403115 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 940689982 1250 940688732 940688737
    0x40612180f1e060b33090303041502030418150b0304020f0d230c030a030e030312100306060b0901020a060518030f2203030906030b0609061b1c0903020d020d0203030d02 74
    0x140150350222400010800c10b00f030b1004251010309017500144000d0120b21890740281ca105500141a00d16280e0ba40b800c900805004180e100c006d0381022500b00f0180da404618091550141007040c020f40c24030443d6a00741d0003060090080982008c400728041d03468000000400040141c5034400b0900c5500f00510310400141d46001090102804620b81d0b00021034078000d00c00001e401031071030003103d90302501c6103503424104c0780d0144024058100d80f52083d0040d03d00980c00b141421540d28190300709402138402c25081444070103030030801140142d0340040e8614940b5004a00015a91192b01c022020400b610416150520010582c221015010302c000d041e00d41d009051114040c40c4a0300c2c0041188851002802051b5401c1c0c1c100b0205000c2d420290003020020030b04c918281c8034800040b51a040001c41c1c5100c0c0034030022103908a2420031010b00080300202c0d002c20000c14401c030003003c000315808024010403070164040119121103c9182c003155005040d26281c80e0608020303c001d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 940691232 1250 940689982 940690001
    0x4170d05070806041a030606090405012706140721020c120c010e01090c06054e0606071b08030f130506030402060307050c0a020303040b040612180f1e06 67
    0x314036001d00340030310300c1d101d445a942041000d409041f903965420f081000b10040148183c1d0195201c0000079170300e05280301440681c150346542491240e40500301881100c0210941c40341304032720b02052040d0f1541050b91003c1d8080740008a030316406091017098041d00032818144498480c1c070a82c8401c040058000d40407220040e4020000b0b404115019800c0c0c400840000d050030465400501010344254000c000c03143c07a0301c4000c100c0080ca0000e1208000552280c0140030a01085500daa484000c0c2c442001e501368039440705040c102100003035003910851a004248003d0b08440a241c401400712000040c02d505064a84030b440c04c100090301c46d0300211682ea404900d002000c201490010166401150041c12060950781d88000584141d8801e82c2c0300d158500c40c02c1d0032040107036802c000403c043e0140268040e11030b450082d02030414400c01c40b1485415041102c8142c1303281603810303071117400c3d9002901824480c419041013400c500302800d20f070521203a144541e109001e0365401c001c07100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 940692482 1250 940691232 940691239
    0x6040801090b0a0605010e1002071a0a080702150703180501060306020c060f0c0f033402010c020c0d060c1202030a2a020601090c021501092004030b04170d05070806 72
    0xd0340c8590010003240e010340105c50114182c0c14006049007400744041c4400e03242401110f00407a02e840c1464403850803407440604503900005d01c01d60895010300140d03000111b500040401c014101283d4110402c01041201090380d204d00c18004d4520055a0707402c05500000200b182940360f04100c000703584610440140f0f0301c00d003000b01d000441c01000b624800c0c5040002641420b1000f003051a144d8405840651400c0e084004c0c4100413980392003850700036443c030301c2c4010705200c210400b03400d6405031241c2805640000081e0041503d070b8010049100360f001e08006440c00c8100ea0603134034200e02c0031101403054801310820091f0074456024007200203081d00c81c1250008510301c0b12900d44460000c4000603005074004101d00f01e00d50b00510050b035007500580d4540f0701c00c03000c85481460264800341060741ca0740b84004c0c0700d00c02c142c2c0c05200c0e4010244000d1401c0e0030b5803114540038401510041200b9181e88042c1030154003101510041400c0360f8040c061400c0c0700000401d92441610000d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 940693732 1250 940692482 940692503
    0xe1314091203090c091b0c010c09060e031002070804080a03030c09050f01051812030a080406110a080c09030c0a0603140f1306091a040b160c0b01050d03030b0604080109 74
    0xa29054001030b40d1140c0050001812400d003103905011502c4009440d01080c841c0c42c010303400061180304060922000881c000140204443c080201401c0041d440b81041c020064032000e2152808900c10600310100038001d40d0b1400c0d84e19040e40540f16a50040c1c51501640042d4002c00d0340c1604440c454100b181d480004140e211001c102d910340c0162403181c0825401c005c103485078110307000121040500200b0716080c100752980954115800031010f0000541c81c10100801c201d8980f152040b0900d0003110a8240f1404c15001b81107800050181103007010080ba0b4028141ea04012446a07050080c0c940420740b0380d0b411014010b003034000005111419000005090382e075019000510910030305200c515100c4143e02d909009141c842001e4074407a9682090000400355a84001c0c002c42c814a190303d0140f800300c100102c00540c80ca603040400401c01c548201040c584041c46064800c100c80c1c0c0124520140b80550040c50780d41d408580000b808030b000a0178400640c402c04a043c000d442015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 940694982 1250 940693732 940693753
    0x1905041a070f050a0c02030c0901091d0d0509130618140604200a0c020a030507030c1202030c09072706020c150703030518100902040f050403020d0e131409 68
    0x40b22060151039040000d001400303031000580c032408218002c50f0001d0142c600c04125500858440c450903003000002c0c64a130480030254142100e9026100041400982520480c11400602a1040d004640e100300700a2180340b00c4144261b125030014007241c40401d541e82c0f942d450041c0038201c40400b8212100001c0002440c0341018000c0d0040c001e51011041c00c103641d02d01d4102c0b81500b10780401030801101d544004016100c204004c805503000d8001413018518520b040e0303500612a40000e11f101d40040c100303400503103001610089501c01154030300820740e690041210f00400100001c2511840e07031a040c0c0d01c0b0307041e0b40d001c0f03015501141d0070340c0c8461442000703111010040c0d1004041a200401044c800701c0d00c246d014a8122010040c16688000301001480c9000f03043d54101c64407542ea0001e02045280601c58511100d030000014030443c174150324040e4880c80041a071409003c0c1003044199613a84200c4141c0c110043c05000700516003410701d1182d1030030411280700700c241c8180d13200d20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 940696232 1250 940694982 940694987
    0x90507020c0f010c030c061a04061403071d060609060904091506050a060504030b0c090d08030a1d06241306050307050a0308031503011104060206062b03081905041a07 73
    0x1240044e4140d1503040c4e11b808140e0f00c010040280901c0c60682c08842054804240c0e264000d82d002080c42c0c0c0d05400c44d00e1440f000f0103040a0340740c1e0154181c09015a042c1c100c04494108080d400074040b550305495800480100c2d410b44160f41ca125803003480d29000c1c0c000c01c030b100e070005480c40380c0d100400c1040903216010f00505d1040b80c011880070823418041080028081240c5079800324914180c00d0401180c2c0020807a44030180340201c80b080404020005581070714401c5002e00034140502500f000001800b0b00d0b1034100280000070030102c00d0361008403080f148002c000c1c04020242c8180903610780300e2021801001c01d40501c922034011028001104c1c500290f001c9c043e030360415110b41c80c41d1036200401e100c01c81140306080c0c1554032010b140042c0c9001401600c000c2034207801901e654500340040199002030a16240403d0300d114514201e40e60130800d0b00a20a80c4c036050821594480764141d8030101e640c6000004400d042108100400070410310000366500305006a955588412070113 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 940697482 1250 940696232 940696247
    0x40b120901180f062705060907060c060b03070b0c0703030219111027080d03140c07020d020907020a12050315010516061a12070f0b090a090507020c0f01 67
    0x7402040048100e01c0400f0806140c62410164441c80000600e03016180d20011201d0005003d00100c0040801050a1080a1040e10751003e81c4002074421142000e6024003604400e410160000c0d645000f8002c8545041054070043e03c0141c03459a02c80c3c88106800f613417a0014001100180140c407040b810307034000706150031046503001110800d01c007002c0050242c1c0300712031400c14081002150b05202107501681d000701400d001101c950b0000c600b440409490f01182800084c205440c190900324003020075080c2a820a440c2c89102c8d60716003190000031130074030701076030043d5110031a941403040b8140c00146007405584624544004140391403815191f83c003040310319080c603000721a203170707901c644c86880206a40c580d44c410090500601362111000c95085045410310794918002c2cac240d591600c3c000c0e04914110000050122605240c440d2440c1042d0744a00c1c103140d0004559060603545240210020704a610b4080115241c0280020f664600b4000c04501030880090b510a40e0b5129000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 940698732 1250 940697482 940697501
    0x309010f1a2b0204020c0a06020705070e15030d0e03010222060f08010f0501051b0604060b0a08030408120a0917010b130605090f04150c111513080903030403020402040b120901 77
    0x30b064544505800340800f070f6011158090940c015040020300044682c0301801d10640034200600410307040c05c04000c00c0704005014424080c5000f5002d250707690780091001e500001c00c0c40d00100c01035010002c01c3c00390148500301142c0e41d00058022000a512941d04411501c40780c0d610854102c2d0184182ca00320000e004024500312100414040395010340c004001c10b5142c03c658280c0004144001400e142055800729405038841d559462a40f03003046851018242c1c0d840558a0135203032880715507462022944001c04094003240b220b061038050003803100201b200041c81c048a80b995103c01d0f00900148104601c10b07604400c0400040b80039104120540714090036840064940212868510302e00400c100d81c0180b02c5d2540c0318460482c3d01030740050405c1c80d26000c0280401404281c03c028020614070180901d1504100c2d404060700041c800c0640c200065036960400e480c00719041d07218030380010350001d00006000404001c000001c003500d410344000030b4495124040309030700381c981d0b460703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 940699982 1250 940698732 940698799
    0x17091f02120f1e04030c1202030721050d0e0d0b0414030f12150a050d0c170304080c0402120c130807270603200612012411120309010f1a 60
    0x29060060b0b2007506406007c00e40010308030780c900d5a4900340c1c11041096100b110240174407680241c000c010041181d00201241c90403c11065200382d00850009940034401910010340c0d40301180501001088014841c0d003004282d0790f6410312900900d0003540032583c0080c10b1461140010640c203002c46507410078060003041c10321074a1a007010018649101e83d011750340407040110004042c03100c81028410754081c04041c42e02d8500d09040d05047c140c420000318001c03801000000c0510b84161071050380030b00b03088400c03a11a1601c10b0301484200c0542c102d04035900c0340c90408140c00300c000101040f9841169034800300d106030090090103880301c620000744240307440340b90030114907a40c400d806078480d0042c00850414100c07090824900a007a480080c42500210340c10400500c04580000c00d91014104101c001d030320401c5480c9e944039000e0f840c0d03088403008400704000c85c07005c1d0040c0100500d00c11040c00410f0748100c00c48000c2c2c0c07c400700e8601c1a5040301412070840e0003451242071109484 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 940701232 1250 940699982 940700003
    0x14090108042a091e0b0d03140d15031202010e1507030e0102030a0b120a0f061e1d060709180209010c0c0603050417091f02120f1e0403 59
    0xb503940102500d00c0c101d41c03101c845056060b40389580c8403a02c0c441c00a1507000000724201c98085140551100c0ca410701c040c034a81801054070340354480302400369a195161070241009050107c80000600038114004c1c49a030400141e50b82d031030104205081903034021502c0b030b2044001510268201c1e05401a680f1450b00003c560500083c103038545a40d01c00d80742d007004a00300803940c410a00f2039104403650211242d40c1c0440d180c0310b0a0140082c548503454200038107155070782e03031140c1c0300309410400018072680d1944104148005050f0952000101d07642c014420142540030a404c20840f020580e83d49100b01d50010315480c1c403905614046a0402900c60500c26010381000c000e940f01c102c46034180143c5249010010390403a602d6401048a50f800003034601313103498100214040d20983c245002c0c024040850f140c0d03201607680394045407030403d080580d04111002d9017001c19002e085107141e1004500b01c803e4a2005c1c000b41101d01d050340086901340103071004005640200c5c0805021644107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 940702482 1250 940701232 940701241
    0x605150f010f0504090c050301080607110a081309060920041a0309010615050c1219180321031404030206010b030709050d380610050405060304080301030314090108 72
    0x40c070b2000040161440c2162401762181001c0c4107a8260340c5449000480020040101940c248406504501c0d03a1410101c61090000320075503442d51078101405034030300001e508455900307800904004107840d61040c46260b40c1d5005d000e004009130340b0032070f2441070207440e03101014040c201100c0c191a1441041201c9054918111034180c1004003410865944c0d9100030502c031000c010312603a2004250348160741c039102c0010305c606020106200c610149818040f80041340403105061b1040240e0b880c0480000700b400c841d003800a010f590000d0f2060304000c4200300003143c122041c0c061038105440501c0101800c00002240b404202d130040c0060700032078018006005120002c5030881101e03c1c001000f1602c2d04000358440701a0700c4105d886069001048615024180308900346440744032001c0c8115146102207004c00748009d1440c2d11659a24034208d10300c3c0d028805507805081c01402d69522454a858804050b500c203010a81c04100c070810310200d801c006500300c0d1030045041e940e500712900c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 940703732 1250 940702482 940702487
    0x2090f04120e01050906030f061305090309040507031d03030a1103010e04080901020f0d09380a0201291206070e09070912051c020a050c1216120605150f01 68
    0x40d0303102043c108407040090300d000350390b0380b4041c6001b191040580091801c103001004440340e289400800501d00348420440e0b2800c000c010350748134034010b40d40414555a1200d0031030003081040540000003020100c041102c88c3c0000c042c51040c1c0c59813804015040d4a0409400719000c24822a20102070140c001000036892101034500460b060040b12046822940b8040c02c0c03603001c000401c00a00e40c803504004094441e610030240244401e0844106030043e10f001c103001c2034020901d80c01ca180001e00d03440f0f66100b540b15841146110a41d85501c110b203405120100f02e0003484640f1544811010b03a4800b00085929402240e41d40c4440b00b80340078030780c24400c1e6424005d1002c03040c0702c200c004c0054005000340007440f48500c00c1c000303413803080402c0f072031111031118401264007194009a00040003c5000501080d1068210740c032001e544028520507152080d280c844078402c410103c0005050b4081203042c4036960310480d801c1c0b2040d9128401600e0340c04a1b841c04a912507485d280144d803d50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 940704982 1250 940703732 940703747
    0x60f0b0a1404020d1b020a3020150103140c1c060f0608010c02011a06120a0e1c0e01082401030b090903120c04080303071404080d03060302090f0412 65
    0x100380207030102d1403101d000c0c0c02c42c407440381c85e41c1100d000d6084080d00c0002c10410054807004c007140000101091000f40c1c03201e04407040f100101740180103da0080202e4980310040340c0511725131140c212000d005c02d402810341100030a200c00c03110300e1103503500d000740300300007103482c00c900000030f01100350044030b1001c4070201d4151084280c620030ba23144540420090b0a0007000c02601601d00042045500c00c0700081c2100d0401c0280b4000140b01d00280e0400d40d03980007121240c0680c035042495540301d13149898000c04011001550b00d01c0b410f0404004286910a40a9840c074652a0203018100ca100159a00741041300c40c00c00e400003055807800a1900c581d01640c078600185800280d051503007000c01d880d070805881c0320041b64030106005000c15206940d10b46d20045808185080a1500860b5503990101415501c2072101c06001d42d00d000b00b40c101503500500000c07044a00c09a1741c020b002d80148900e0005034000e40c1280c00040010a541034414082d541c0a41c02c04200920283c0444020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 940706232 1250 940704982 940704997
    0x100816150513030f0308011403011b05091f020606090106090501090603020d0e012a03060b030f0601180906091a010c0206090112020301090e07080a0302030d090807050307060f0b0a140402 82
    0x2104002c001001045510f0845032815100351140c070070030350601d640c01c0c6000403803248241c400ea043c20fa4401a205070a08040360300001c6007000703030700d0322002c82c00503c00082c00c0c00c207031580080034040b100c51180d0010741c0c28028035059840015590303c404d01251940598010940403c5900408007e21446a801080702c229410700000340c0d80980e6441742d0944860310b04614580d18000a2426080d07041803058509040c0e50400f0411989030013207002040c080240001c2c0403286550000300c00b03034020b445001142181d0b0442c140e41c140c0b030740c10060040c038445c0078641c0312500e44011803403100c0c500c82158048001c143c5403106c03c00c9156080100917132190403107030b0400050000300c0c62003400c540081d6010780360b040f50200b504c003040d001561810386142e000003140d5004081000c04030780c01100703c8100b03c007840800718031200103080a03d094891807000074070601c0005141403e00085c3e40c04009210129001800b11010040400c8404845401040c5010000e1101080185070581c01415803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 940707482 1250 940706232 940706257
    0x206071b080c1b031504020405040f1a07020610051f12020706022517090402092112040b12130602070c031104110d020304020112051008161505 63
    0x4128181e56008142d400c020401e4080c2ea2114041c28680350422180503055442940200f820320344155021580f190045c2c030180c020ba42d924013140602510280c0c10840982202d28003004118006105450358000c444000041c056400410700e0090307646411022240010000410554803086459210148130070003410b1203d103007803450402080b800517041d401e0003110010307190603140d400c0d461074216034800204a01852181c1c0e030000350545010250700d40723000b900952549120000324000b48241c02c1e031164452413503c10304103600c01080e110114040c0c03440a682c2c030042c4400300c61196001f82c2c09150300841d07041c892000e01344010600303550302844050211144040c2c50300c0b85002c07640040e0054503c520000c0040c42440403125102c070320030405813401c0180d100f4082884505001d1026092030040d00000810b00b568850b0000192142c406001001207040444a00041c10300c60701c0307584031600602100c0d2200d011081c0e140c0b0200c5641c603000761004a2221802c0300c0603400302000001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 940708732 1250 940707482 940707527
    0x70b2109150114210a05120c0303070c05070302032a01030b01021b0a050d05061e060f010509010203130b041404230603030706091a012102010f0c0503180909030406020607 75
    0x30b14140c44800100321307101103c040c000c1121103081c106e0402d0300310110510305000030022003418500000407298029140d20300900103460a150031810502d0903440a5414401c64a0036042100d0140c01840c3ea420390f00e041d014101040300041d01543c1100c910740e030158101c00d03401412015089514204034400400d0a040c841c1c944000039000c86507034001b40c45c560301a40401070b80c1c070b40c010183c80031608290003038641c5242060010b0030a0a201000074100f0030041341c050381a0740200250ba020400c0944080c00d0607440d98549841c94019108504216504904e202000e091a1190000601e0500c000f40c01d8181441003110004002402d0306801d880100700c05804140c040c804d15003804d220398100030a0310403404a0101514040e00841500d0909214440900d450007640c00481d0741c0c2824000f081c2c41104800391079001c03903ca0050403a00001482c0c0140785c660b02a0f400c1303460740446000c042911a10078907a543e005074003500000d40d1001c80842c1105004000108104514a14109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 940709982 1250 940708732 940708759
    0x1005090a0204090f05010c08040803040f0c0b0316030b010905090a05090703080c0303090c0f03061807090603060b150306030312090c040603050f070e070917070b2109150114 76
    0x1401c803076082c070f810340d0021203803600602000000e00038590004803e1034a1517450409403681800c03840040d0006002c030540300b219408001820196000030005450700988914060b0061002454482d403c000000e02c0c04556040e19802090310505071180038062080c10ba880c540448010440508548160310503504d0000007d04c981c0c008061a01d41d00010399141c0c00c044507100c0c5004a41c0162a101c0c4030744280c402d05944000960b554001104000261400824080075050440d10703081036214a041404c04800c0c0100da80141125640c00d5680f81c0084001d800d011140340401d0b83e13821703455041000740202280d440c00700140c204c46000252a002c440c0e410005044030346a6000702c0711034102003034844400e079061140d81e00404025903600000c0c500b926008000d03c5150140151034008003000c02c00140081180101030a1404050303035503804c80c610b090702ca041400003181c5070704401c2c0c400180c1c188008230b1035030400303525009451030690800007040e18030381604a009405c59144050388 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 940711232 1250 940709982 940709989
    0x20a0803040b1b070e0703020d06150c0c05120a02060a09091a0906030109020a05012f0105010806090a05070603050a0212010b0a0e0303030103020f060702030a1a070906111005090a02 80
    0x42000745444003480c0d90f0f40c0b50800c1c410841407081420041180c10101c002c20481d00300900003a071000c02403400681d10280c0c580b41c500101000e0308000041e96480b41089002904585443c2810303008a50450029555004000300c440c1e038004003d5231904210b10744401820f002000e04408416814500e00d00f50b1601040b2085840e1311000d00c5140c00b240c0d4695030303603091052806400440079002030040b00c0454000c5039015100c2d20906041140501000948102d40d0704c0c1b60500b640920350b44000301159401c010f010302030038040c1e02050b00641012500c0c00e6000140015150f9111000d00141458a00290002c080040c4000720031340d002c0019020306002c19005901800f003814440b5200c40507050000d0452104a00c1140030f0341c000c20062016a56a0300307840c58900080b508a940d41000744080303810984150740041083d442918144030200d0311510451041440b603440c0198555503003012258004841018040340d0854042c400e007004031a0016644403500b10101c1d40b40d00c1160307012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 940712482 1250 940711232 940711237
    0x80c070b0315010807020309010905100c17070c0b0415030c1e08040c09060305060a05220f020f0a03030f0c02121f050a020c0613031b0b0709170a0f020a0803 69
    0x607405220720040c0d0902c5076070840c4046420140720320085080900507400a0100d09842c041c040c41400301d050003500303140c40749529068a035840400e103541c2000400c40d550150300b01041c02c031100300001401181c440302e090b00766402c075224016500d662100d00d150560040a050000b90700b0020009401441560756840313034841c07294141d07155961854603042c500304110745504400400c1e420244100045070000480781d4004100d4080021191611b1588136044081c9201031001d07485840c071618203000d1881500c0350098000c1e03d446540c23244000c10080700c1d10481c0030080114181d0f24100200038884c0b10050111440600806000182200030600d407280c100800c0701807180584100c01c100d4118060075400103201c5101703500f41100f5144c86921060001d016002c103108100020050602c2429101400c104121900c0468200ca00303003105100011500c040c00b203032113190005071110640f01c0c50a5850440c0010703003086180750b5100700c1c9030707105a44181c1e0305c610301d40008510b98109100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 940713732 1250 940712482 940712491
    0x10030c021908030906010e07050906251a0702030909070e151813140103080307050f0315190302010e0f01052106130c05070b1305100c020f0c030307080c070b03 70
    0x200b41e030312498140480b82c0b804605030040b400f843c010b2010301c4590390b0410189c0328414030440b02e0076107030682c000c4040f022041412240703400019031785803602881114005005500d4018a504034140d94000099a80380b240111032508103014500040300d440c82000d000706161001002c48902c0411565001d22603040310804d0300c2c0e8054002422a0289003810a90f0840fa1304044188940c0740f0640c4c41c8010214144000391486030000001088030b4820b10071201203022a461064a9060682d41c9040104140c030bd014051141d2030013600310802843c0d50f00003103aa05a403105610718600d4280000410003001e01c0381407040902000d0190388041035421055112490502d1291809004002554660001001c0110b00c2e044500399200d612030100e588240e00042007011075102d44903245140110103034084c00c940100300c240035429010f81c12a000e100d6140e03080b00d451418081c3d5058440441142490341070f4001c105e1400010390800c05007882c204084145e0314285d68030a901d2440783e10455 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 940714982 1250 940713732 940713743
    0x405040228091d120f0409020f041d090715051314010f080f010603110705031204110f0d15020c0703050a0c21061e0c08010e06090610030c0219 63
    0x481c24410100740f440364886402c1240c20001110341850042510b4034810152000000c0d4005100c42d03c0040c040308030760082910160441d5078010710190382c11560464042c0f41d103030b030300c100480d0049000c281560074007900c810409410524a0990803405004071100024203109041c4405100c407999008950010500e0416219501c80e2550005100001142550041c4a0000c0070300940b8207900500318151800e41c1400140304041009015045c0600d4900403e1031200094581c444a050030300180034600c68180c190750100d00b00704003d07000340d1000c911904000214014808661488030501c00254281401858944031b241424100b045981003940c0941c043c0a02000704036070b0212802c010040f04141303400705d1442c0902e150740d0303407a0303c400030300107540310340449850800c40340d4a024510150081041802c00020700034028203424812400d000541c1c100189007820140241c81c4100f00050141e01e21005440c425070060041c10702c002d0451148840c0321800242c181d550b910600d0141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 940716232 1250 940714982 940715059
    0x801050907080d200c12011d01060b070206070224070312050105010801050d060f050712060801050108030a0c062d0f06031203020c0c0a061e0801060e04050402 70
    0x41000c52a00d26036600c001015030003403892005a43d444091a0480c0c0904020350f622026401e01480c9001704452042c0d03405007001250010b241d105500c000305070b13944015101c5040214030f001a080780c900384610203110200308140001450700300f001340134072440200004804c100c1a11020300300c3c040f02240070b4034548005080c00500d90030140010500c2c1e150300c8103021560424000030071041c01071041d180101d81004402c41085216000514201c946020400c00c0346092900240000c900311104400700340341030740215003401c2c1070080e2030503181980001c600d03243d881e04003111351501544d01a19038513510340c41c100444031141a4601080100100c41401140c0901010f04a03082090840031442c44d141c810000591030ba06240704551203801c0c0140c0b200700d40441c0d28100100307400010343c464590703600821010f40022a803ca81404000d940c0342201d083c11080c1c407500b000780180d0000c60851401c414551415820880d4480d20203006401c424505039428070107094079260038051030280 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 940717482 1250 940716232 940716241
    0xa050d0c230415030207031b060b0109060302071e080705010c1d040203070c080c0c0a0305060901051e04260706050f0a1103130c030203120d110406050a110115080105 73
    0x1101c002020000c0d16400145007900c1c042d0380700380340e00f5a400d15805158002c2401001d05004d020740701040442d425070700c9805132452030000001c00119524a020075007114001c54018424400d030750703101303510a00700249100c1542c10405032044814080b02c500e01b0402c03031140002c07000c2c045c0d640c0c482c019458020071010310316006404215031208141c0200d10500c00c001003d80d201031400350080d013041c5616513550980041d141855a6a058190444208040003007085000100b0b9441815880b0003000117481d00c480071201301c0da0309080486a00d00341c202241c04101982001302d401c49440084080381e11510702e00d040030781c000440c05e0355540e41c3c3e00d0800020100c00d241d0664003e203071120812000001f01000a11804084d01c6000461540514101084268201d00014503001402c0f103c1c5450f140350319210b194400720403144204d08090b8000703450401c14040e6016202140c407030310b04100a48104403200711312400c90f5007044d9258503070f00b407103e1a41c5141c040031b080c002c030000c10140f80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 940718732 1250 940717482 940717517
    0x809060c03030a050703090f11040612050606030d0512011403100f020c010b19090e01020403212c220510300b040819090527010b0a050d0c 61
    0x10020f045e030b028035003020361880c00581d02021031391100da8400c071441d00091240c40810020100394000c4060440c0c1060481d05000300015803a10803e002c03801c1358492100100212800c0c0038100d00d00b141c00981d040144601c03611545d5104081002408039200705081d80a150309a4031094040d400403036002421035400303202801003a00d400015039420306030071689030604048624910400440503581c1030304070000c080c00c0d01220021a00141500180b4a0482102030100d00b00714500000c1a006481881544c490108030010701030b07154641e0310303480c50000c01e010500c40c004d0405a428142407500d0580c1140381c0c407503240200202c415a010403410308030780055840c00c0850002c40e00341501070116040104043c0c0200031a4419180307001c640791890900e605010f010300c000901685c0441c03002c5110351101041c402c0f05c0040b5442c41c046480a12404050610b00b52507201ca504483c00622041c006800107001903041d030b1501c186881211490001101c1c000384080e40015800c001070050040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940719982 1250 940718732 940718741
    0x50f01060f0e0a0c090501030b06090604030507061101050c1b0c18100902131e0312180920130b04080601090c090b0901030b0a0b072301090305160809060c03030a 71
    0x3d030944004c01c01c9140b071842c081c00e00788441c4a95810580c07140e442101c1c035102c00c1d0603a0341020002c0c10b0301c0e495503181e103440c90b2104124000c0704009469800a5038440c4414083e0350b00420b58594400d280c00d14041c206070340c0716038907409805a4890a0310304200342c0c603860048403000c00041c6100c2c10350708280c000305d035102a1903030055055600600000800d1004a4100d6048550400826181550640484100c0303007007548082c090240c0c0b00c400110168001f4000c02880f151600d50042c00781d1155040c104940e1090106180380d54400d1008415171502c038018086c0401416a402110b0398461884400350300a40010f101600070301c0c01081401c00358050188400743c4c6051140c07000713013011056140b42c010f6208140c105903c0c0e0100c1d00d42600e03a16001001b5101e03070000300e5510112800c2070888d816244600028086208012401040040c030030804010f034150b03242441c018a400b814001c841d600101501e03840400c02c601191030340e8100003000c07407100a4000e10b40b070b8540f0810440485 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940721232 1250 940719982 940719991
    0x3110703030212031305030301080a0303060504020f0313060204050607110a0801050f07030203071b0501020c100b150d060519060305010519060f110d050c071a0f07050f01060f0e 78
    0x5922002003440040e8010031901107030790781c0300c01c1c2685070394980c0c0300010b0040c00480040e005002c0000085110300011841c04006030081d1001d000c00c0b9503610901089108201601c40e0001c028030203e07044000fa00e080e41035082c05201c001d4142074132900040c03a603500c401760450320908d0721400c0a88500385509500014406003000300090b1402d00c0b000085484c0c0103040b0410564000f0001d5481400f851601036000d502c0325050032800200d10b0128000d620500750804a0300c941003e1070061a558010307035400030701c081c1110b0000041403100644d16008190003400f02c984401005c20b440d1079009040b4010155140c42110b11480c05402508540707040e04146d014070803031004194a44440190f4030308903800d514001c7c0b03c0340d0583c1c20840d0009102401111540620800700c405c540d884001340031003500100580300842d646044811101000e04901d00d034540e020700542800414020241c000e0a00904c1601c00c3c9200400103079003101c816400c08001000c407101e0a00c1901d01615015510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940722482 1250 940721232 940721267
    0x705090c09010206040f15050f24030c04090321090c0b04080a03110f060a0c0f230c160e0103060b01020316021216090507030516090e0c0f0703030903 66
    0x10180700c1c0700001d4840c030b0000c00103000401c1600c100020481003010b5020026181181008141000a1503000c090b200b40e440f04841c00c500300b82e01800001c80c0240903404100100184208501031082c0b0002e4052010142c0c2480403d00c840310300b0300301c4070500b03048080d031450300010464200d180841c00d101468108085041041c007050107080c4001841c1d03e48581c060408103011100d8680766481c0000040c40703d28036000e81c07414060070b4526900300c07035480c15164607041c101c0425107508a44c40345407021021011841c600e140c220200244d8003d15120183d6400d860003400f01081c4c1d411030b02500e070b10401c50940307040010014811140302d81c4e00130307803030900c042c5141100f402c008002d03c60b20174034040c0c841d04c840075680d04103190400242110882c1d40c0010600c0994622103000200400c07106070303001c40d00b001d001810b84d00040c4d02c8904c0318a241d4540500d002c5c00c0c460050a01c50000301250907880c0104201d180c400c190101400040b8865500454101031914000f400101e0000034001d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940723732 1250 940722482 940722487
    0x170103030206041112030d0504020a0522151a0409050c0909061e040f1506020c0102101104051804112b23060f060603010b121503030c0705090c 63
    0xa81e010405503002070b0411551100c99910301c2c0025071039a414a8440880d2100050141009405d5000703030380b10303a00855955001540c0c2307409202c01d044140704c5c103103071100000c0300802d1401220392108414050051500841903181e441045001c101603802e04007021000ca402c10503024140915540031003d41c21003401c149000c00410311540003e400c0b40c0c0709440280c09448005200340300c0f40207030303100204240203600340c00c20040c00038116000710303030000d85c1302010218449000251441082d04180d0081411201d01c109101c02000800440c04503c042000f0000f4203545484401c85074401541c4022101e051528013209410440000385001c0d562060116200c1c5d9181040c04000c01d070040300c111118481e030700e0800103a025815115085000e10004a841e0001c00200705100d9802e03101d8460540e1921800c000d01404248102ca030754900400c07180c41e41d00c4800804a400c1110301c00052483c02c80c0c000040d08613080111004519808104100558a40710b0000b94000c003600c14940d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940724982 1250 940723732 940723739
    0x31106010f06140705100c05040305061302030a0b0a0e07030606061707050a1107030206070b010312020109050607110c0306181204150806060d050903040e0c130e06030f06090d1701 79
    0x510145030107940510046004c146042070100520018154180000b010091801521701c05402070704640800d071503500c20a07001500243c1e15000c414859500107006003840c112503601e084082100504544480b40c4400003550400b10401c29000990300c60340c07010494a051078401483e40000644040a40018000b44503c058000c0b048900c1d810861401894103140c0122172854020160b000940015001400105101140203220b040e240700301c4050307118500303d1400300e00361191003402600b19003080e0082004a4020351000c28090829800c0e900c50f4100c220000342070403c02c507100d104080780f40040c95070042d0280154021003103030418603030400e810082e180d030388a55001c20071014488258041a8255100303415140400c80481c0b0911a500c0d0008500b0707140c7e046071151461400c0c1e5032010844001c20801902d02940f8040000c6151a00e0071715080000f98016100795090f00600340d4005400009200152061a03114000c10b02468420b000500305e05000084491039a0301d1001070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940726232 1250 940724982 940724987
    0x601080402060a02030c101a060a08160905040f0903140406170c25021c0f020409080d060f080d090e01120501060e0118110903122203031106010f06 65
    0x6541041e010344441e601c80b400e610040c1c4c5035114031003038648588140250803100d500c1a400c030f4003060b4418442c40c103003041d2500601c1414000d52840c00003054070b0710001451103e801c06040d050b81524941070f15030b9583c407800f281c1181c1008441071405501c0d0214038090540002c0030b12138044014042c00d00e41071900c400108a8442103c00f00070541c0c42c10045030307200070004240d45c40280ea182c0700d44403a204001e203503400c001841d417049000e000c1104002d01c5851000d510038202e0350f080302200c0640d1b4143d5080200508907400120b40303101082c00b4440e40c003800342c41144007601c00c0c943c000303501c2e078100091680351548684103501009280c030030901c0f12490380d003101d60440c2e202d2008840032880c40e01e0711038050b0800d0b40180641c4d003128800050180f101e01d180e000c52190404040104c1450420b031ba05841c85007102a41d0507611108401405030101070050404545105800307030000c03026404100b03100919072007a00010010404180c0d8a20280030705401088000b01400d081b03860088003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940727482 1250 940726232 940726247
    0x90f010519030f0912080f09070b0711010903330b0f0d0804030204110306040f0903020c0d170705030903060f09211911010c0309020a05090c070c030302061e0601 71
    0x1041c04054030348000039480c10964101400640e806880700c1c4101c1036018005200c202c2c1194903000030362449020a10400000c100c05040da4078a0000030b00d0001c040d01e40e04070b100e0705c65503241e0410030208000000308940848495503100365090200500b0f051180b0038030303c03802c031804c4001e01030301d0100da480f42e998035998039100e50501038411a01001d80b034100714803940540c0d440650810308103910244205800b400951040308100c4007004800d40b80103144003266911038006005da40b003511088110302e441700e82221001d00c1001407140d8214008589080342d08030030022a99035102083c840440d03e024840540e1180e445259580d0740d10700b04640559032280e14079000390400d009400004c81c0c0740301008540840a06000c19801c0006104d4010044101c0d0b0403141801e529202448010078460700130541c035590000c11418101d4104000c20400a6014107445440c51b41042407100042d80001d000340114000d4010340990b00d8540641c64101c4290300d00c0c02c50162000003009256a0001007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940728732 1250 940727482 940727527
    0x10b0a05040c1407080310120507140a05040e030d060518060405220308060f100806041812030c0909060617040212010e0a1208070504120204090803040602090f0105 72
    0xc001c50300b900d8030b0100b0384481c48450380038699404001040c90521001e0070085005101030032102001a82d540300e4101d0304281520000c100da000700f0800c004482c540300042e014003600409000762140e54400141c101c90190000c172540e5003012803112040f00711846400c0c000d10091b126a015003801d038003055807201005010b180b2442c1d40d40b020070640d4110b040e10425080e15040d030a81b202e210f90801400d1417408a81c99842181c90760180221030800c1184009004a00d4580076025181e610800c406440c26078001d405011034407404001040315a030f600340703030300001c0d032000190340c541c1d000010300395503040d04000051342c284041006480d07405107482025a000c09645d246076140d9100045100041402c205580d40c00c01900c410101800b04a101041d4803038617031001c4410034000159602c420445101001c60800d01081080120011342805107610040c070005180100780c0d14044541c0082d141035540a038003141c101800c3c00d00c0d1155844240c130034200107040c904409050400340c0072904 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940729982 1250 940728732 940728739
    0x2a0604120614190c030f14091b0d11060c0102030c030109051302010540090e010c0806090702010e01110304020111060c040b0c0304090606020a031d06030412052206020708010b0a05 79
    0xc240d013820301c1c860381c8501455106014140018001e210074604407103030039504100c1c94000c641080340041d1458103104a442e80261103001514003e032200d0f9040105140d000d6000141000034008050b807c0c80114030400340307070410940300d5040005403803c403800108000d217483c0d803215803600981c0e00181600d060721070410b0038031340580c40c4440744205404114125100403c40d001c80b4260f910046841405071110b83c0300c2003100d0301c40c0c04941801d0300c5028030b49602180c12880882d0160074455441e551080090001188a51621720645d0071902c124642d1441c2d50000b01c00c0c04210340c0e101c45101007001d00d0400a001ca030030600e820f2034440c0300300c0c85a007101400010702600c07815001d005482c02448120000c1000f15503a0b6006915142c480b039048000440b600200c42e16101021260b411711680542141c1c11503886643e0b020380310098408400601c0418007010480701c008081d2040700001d42a401d00482d8504072001c2c0c944105500200c0d6140d0500b6948442519145609030468100700c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940731232 1250 940729982 940729991
    0x140a05210d320702160e0a2c0601030308090f1c1b0b01090605150a080601030b04091104050c040605030c090f100c1b082a060412061419 60
    0x1003004040c12002c46074602c0201c90604195042072045112500ca240140c00f41d4000d01214662605000e405000d9075105e03814100209044601c5540009040014002800411161401100900c4186800e2a141c0350b010030014001c1580c00445107412400020081220200200241e03407514059a000d03060b46503128440080548a200042d800700a6041854440700050030220520502401007564045c1032110024150403c500080d0060305c440b9007081c1000307a0070303030304035a0313418040d098604240d1200344221060740c880c42420791141c41390480303007444182c0c0c40c244070a80c4d43c002c0c4040c141010a2004010458000342180d5102994074101551001c407030b000110711041e40c034041030f00b0540080940003d20b81041c41c51048602642c940310149400380380c5500042114001c8001b82c0d08200c4001c0c4a0040d0013540c500c0500c0b100c1c09820400c618000800c2243e00f00d5400350318040409220502848412b11801d84105070a05442c503103458040c2ca02c1ea03800c180c944c41c00042c00ea45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940732482 1250 940731232 940731251
    0x30f0e06040e100605070515060103061511010c0201020a140d150608010602070b0a0f030e010905120a030501050406030c050d05010209030304060e0f1009150507140a05210d 76
    0x41014144a01008285507261a12490700844804088a101d5280c1e5140741c0c0114120307000d801a1660035600c0002009808042e561440031008043c00d8581416201c0202207083c84c0d0482c09908201600e54400d0415124201c00c542554500803074001503900c1004007010441e0f0240704180410800c20506545481d24080ba41c011b100c034400603580301407003910101d0b1450307000c52102c0c101c1c1c103144d0803600c010351603040c00c901c584079420720322010852521032103190724043d4001e40b00002104000081d00c001c1c80c0c54060806654001d0f40c03000400000d60488215010301ca00340c05032105031001c000d007900315030787d500440c041801958887c4500300003403020041c0940450b006d1090140c00e40e51280d0384c41402805d0b159103010400e00c12640b07510840d00500b050240750050420554404071924034202d0394a00030711444154408000c020400300000c01c5110300c104021041c2080204446840303418460b042000494440503243c080c4403040cac20608007642600d5601012180000300800d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940733732 1250 940732482 940732487
    0x1a06090411071a1b0f040e04140a03050310080f0c011b0c120b010605090a1a0c2515020606040b01031b020706020106060c170702010c0b01080307210c030f 68
    0x2c0c0d00001082c41d0358100600828034585910b560140315050141c11a200703401e421281d05000b1040d10044220080c0420003011042588068019009502c1040d24183c0c83c0b91b41d03820b241610600340e020400010038070880e6181000d07200c009002d00750103840201d02080d40203880300d030314000441c10031001c1c400e121420006003015910b01030784064500c400d11764036104c5c103403441d10500c801d407030340c07450000001411070241080398002840108107090042c01c00f00c4d11039021001c0c0c1140350781080c082c4a40c03500c800042109400c4035441145229064004030fa0400c1054501d0f0003000304a100b01c0c100320302c4244c000600c90b40000c000c490200b0403e1480300120000d108200f544001c410994510665903600072403680240c0310190300034040d2a40310001542d0b024401d003c020000c00c8141010103106400c8030183c00c07803601c14540740304030b8002070f200c00001210070b030001c4c43d01d60800584042004a65014000c07440111a00c49804c854070143c080d12141c80300e1405401d0140e981c4078610142e2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940734982 1250 940733732 940733737
    0x606020c0f0f090f09150f07140d11040305010e01020403030906211406030607030b0d081b010504030203131409010e09070308030c130e09060c0d0608100e011a06090411 74
    0x102e01401d800f1441c5004680700c04001e100781c40c2071040c0d010f556141088040d5554000d4895140048001d1103034540740f408a4052045010070307841b00d01c0501103807014220038000d0200c1c10420700303440d81d00d480c1503052450840703440603100c02e034980c8104020400650400d103600200d50540c00c1040702900c8905e403600004a0000300203099034507150318068483d04480400780520002e030100d9113180c5d074200303041d0100d907400b0200561103041c00b18000002001c00004002c1ea42561042118601541c0005425140f042d5002c8016070004204a4445950300034401c008100c0090380340301c424001000b0502030348060240e0000c142555001480c60360702080329100440d17209206960380e150400a02e841a000340501e10205c3c5441240010104088034005008014100c0940995101d501e52030005601c10102d0008154403a034000032144014800c62641404c0d6400101d0340340d020003c2035086841d0325200480092428544070440d440782e0741600ca40c1c4006071400201d02c1c1c2c040006e0201030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940736232 1250 940734982 940735009
    0xf060f080a2f090106030f0e070f17010204030506070f0f0201020909070c0f0b0a021b0106051003051e0702280317090c1302070326040b06010e060a03140603010606020c0f 75
    0x20207600000110031b50f059100b205011580d1004005220742480b02a44414482c440c615404810090610000b169034144421207d1244001031910740c1c0c1e07940b40d03400c0c24021114030000c5030b902121010b25903003000101000a01c540300840c0b0f00b055500005180b01805014081048407010300d0004001d021508810342c15000b000c29100ca1034405104070196000612840710404009481c0200c042e05000d103038143c0b4002015002c42c0407520004030000e100c000e1200d00403030811004401c0c000c5d466a150741c010704490740588041c01c0c61000d400345580c0306155040c490b81800340f2071004030794080002d0031551135803d2010702c1a00d0b504480307464505000c0c0d60300d41c0101003403855090b4034119801404000d20039141c1400782081045465104101034045101d454046030008000801c2c2041d055030018050404607040d440b220007280b6540c000c1d11009003c240d50310703400c4003080c40603036490340d2102d002c03070091054904101000b07440d5102401024018881161402000d9407002d2548000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940737482 1250 940736232 940736239
    0x1b030a11070f0e370c0e1311040e070e030c0a0b160c080d110601050d031b0203010f180b09031e09120313030c0906030819120f060f080a2f 61
    0x3400c05800c4d210040703c44503507031200e2441c0c003140041541c0103c4040015120007402c0203558a0360306600c8015022005144990003810071011400340340c0440c0f941d0040185540d40001d40381c00200381440d0002c901d06591155100310000c00404a07481c007211942483e0a9100d04da410312890140300481194001c104103001d242c59640d40a98800380e11000c401c01c65084411a9031780e2000c0c000c03031a40c02c031000b8001a0b00154445607071801140c904415174400b8000040210907070720b50008642d40a0805606107a042141030144201d0000350f6810001d44400785140001e0915150161080300200802040022170484040e40e05e002e00c9218545001050b00d6030392200b04101e500c0c504550104481c0401010320101e0112002d1040d00180ca901462281c40d00102c0311405194001100b000d404016a02c080002081043c2c000c0c001c0319140034a01040460601081075001c2555810a841036030000d800b10001c42c040502c200070b1140d00381d0b91074041c0307030030710300c1d018500c007030445030740d41c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940738732 1250 940737482 940737541
    0xf041e030507080307050129060a05120f060f01080f130614040803090d0f0c0327080105240d06091e05070e0606090108011404021b030a11070f0e 64
    0x200ca10f404070041500030300c90b030000c001c5500c80b0181003c408150801d075080e415815040d070a450305101c00100b030702020760708000c2d0901c1c0d02d40031410b21a407021602c080900103030505114450401c000349200740300c0700342000031140c0781c000100d0041c0a00200440d044606030f5040e003042c001030b41d000c501d514000e00e41e544602c0c502400c220f12661f0080e55810b01a2050301c2e5585101417080c440f10b1645d032100c0d0b607406a10705080d00c08a4040501c84810544207000384140450700702101da050b0f00030f02841e00041400d141908003406000c00c2880d000402e81104c0440380280d136560b607203010045611031000070342c1c0710203030901340d5940e02c003402c0c1d00001180c9070542c04107014000500100312176444940710f59660b03c2c0814000e4500444664a02094000006000c1c201c80000c8045034a84060001402c00c1c14008151400d4035006501c0302031508000f030140b011642c001601074440020000500441703107003240e039551508041c0719180c0d000c0b41c030f0ba002c5007044005a0070204420340c503504014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940739982 1250 940738732 940738739
    0x50c0c0312090c0a0b0a081504150e09070f0e07050903030d050a061502060a3305090a0513060b041d010c0f08091002070809090403020a060b060f041e030507 69
    0xd84044156003968141c40f52020161040c60810f580d041070343c101c50421400c04403e0a015109040003910108000c65a1705905096071954800e2a9005001c006a19034041c0781c06007203584401c001d07000005a0b00400028400040c090620104031079108854010301d50714250104d81ca409811a415850701000940311454075640e0000c5014501e0f850080200c039503a0078161140c0340022441c0005600103000107a981034241c1e2094a804d85501403840d013600c02800c05040c90445c0750181c1001241a81c07040c8154140300100681c03000500c0d408210350700740303159002000300c901c0d68024200c80e03c480442056845070341185800f812542c00703a40ba18401c442449010b4964904407100003410100100d244074803400b0301071b01680030040a4801c034650000043c2c003a5200000031b0b903a00c070040180c020151124401e2030710a502a5021304039028482c50900107603094141c3e094441d110a0201038002e543c813104403000c4a00d0540302010465510650415140c2c0d26800030f056400b8409000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940741232 1250 940739982 940740007
    0x3070b07060609061d01120308040f32060f06240f040308030106030e010b130c090305030708090102060a0218060a0c02040509030a1202070507050f0a0911070c0b07030c06050c0c03 79
    0x81292159517021000603070f80340c3c0c20040025a41c100d010b40058649000f140224900d41400d070745807405204d610441503d5400d859a28841401e030b00998440d1001c04c1c0c4005880034051140c001943c4841003901c1d090800010307412241c0c2400703034a00140d04c0324103844014002421120300c28a0040d540d0344403a52810050501c0d0000d04c940c101190400146003400d440c10701c00c402031030000030200b01c40001114003840040c0b00912801061181c444030200c042041003001d800380e544103418080d0b0b500642000241052800b80100c0e540b18014040510310080c0c44074000c25500051710801d07181c0d08105822034840e00d4020000c6c0d0014504000c0c0202104c001c40104094030003a01c6007030b05515425000001c134414400003a05641080c0c03024445440c044501d05d4046100501090805458090000c04c8603401c0c007034060b0807a000501d170010088080302242c001d04441900c1400c180440e14081c1c40c800415800401060380c0d0000552520f070b800c1c05031590f038602007044944544001e00702 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940742482 1250 940741232 940741259
    0xb0a1401030c051b0703170324010309020d060218090106020714130f050615040806010b07061b03060f090c05030f07090909030e09160c12020106171014010503070b0706060906 77
    0x103540c41c2d442ca030080036607080a4021a40070301c10304d0b00034001d00074100c4405c40c544c0c01012740d0281016290322004025980b045219000305000d40380041c1d84105c41c80c90802240050035826005403103440041004940204204007107504a006607460102c15000264403c00080481c2240340d1800e41c060403401c40f10303441144664400e4441c109100d405084c4c0103501d004030300c40c0701e1166000b00010f0000048440c050450988600b03004165071003070344009802000500801c00009035608c80800c451116803005d5070062424940400809508410040c818400100451200c40760f04001c14a10b6205019200c002c102d6020100284800362500400081c0d004810030f105c0d98000011070007200740071000d41c0680c3c03031507191400d01c038000740c0d200c21695600d1110101903540c2c410000800002403115403000540e68070140443c1490f0fa9215802c451003542d02c1010400401c0040c442ca803400501141036a00a80c0f019880d8a11894074001920941d000030702c0f0242807000000c0d003000400c28 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940743732 1250 940742482 940742489
    0x3070302070b07020303010b0409110d0509030307080a1103131a07020d0822030c110604090605042a0e150f03040203120304030c03110c090711010b0a1401030c051b07 73
    0x9140030540390303c6802ca03a00c1c04203004044812100304000c00080d036159001c055610030310241a070034590b1840c0590122a0100c5d5000381682000040243d01c3e503219403410ba1000c40c0341030800103040b02125092640c04000c0aa21400b0304910700002440145080c01c20004c00c280c51003e1140b9007140d00075241c0c049480c8a0b00030810b8040800e100e551100440341c103220040e0102d00184503103460407500240800d009680f0580c40b200307248107a80b2600001c102034102080c0201d000c03403401040c40200c0c0c01c0e40d21442500710300c03100c175660354007540035444a2080c16450812211680000000d10b816031302c5c0c0c514041504002004241c42d82c030758014503c00d50080382641c0703030a40103180312005844202c03001400281c0c40c2c2d01c480000390181c000408044807a004075803c540901021407039060091b6601780200340d4444948081d14402d0049140994080d284401c03014a043c440401140507048032071306058503007841c0c50103d03101d80292902c0b2000c04e89103020102ca50f0782c5c1580c0b9082c80d1701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940744982 1250 940743732 940743743
    0x60702040c020106050a050f030a26070503040612020909010605221401090e190903032d0f060b030604020309030c190218010e1f0906030606150305060d260307030207 73
    0x190001c2c542c5420008c001c1080000b6000d0100c0140c40d5480090301d045110020b621062400b1400101a000001070b0160318821401141c1d603d040020242103860280404603100c1e00400000e50262900c0602038111045420880c0d16010444c3c4200660a0001000b0306440c1d00b1700302c0041c044180000b01c11004200781c035034000042e140ea0040304982011281c0b503008116080d0001080304595102c0713055103020749000a14084c0b803511403c2d007204110600c805484072005442598042440381c0750142c0070040d0301f04041c0745081182d2145003c020451403146038003000040000784240122a5100c5150082c0c0c0c6081c0da00010340032144a84c901c007070f030061003050101260100c44003446c5040c1d43c036000403108070343d41d48500c01c881c01c1c0f00720300000452415104002000301c518080d070009540b0031400441ea45003001344110300c88000105000405007071001f409699215045d03280220b6400c0b41c51001344c10022180c04c00c20440541e45115007030300001c204025541c4c1a40a020081d202d01d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940746232 1250 940744982 940744999
    0x232e0915050609070c0f03020a0602070809010e030309100e04060503010e06160528120c0903021305010303050403020904051c0f080a0902090703020d0e1c021009081602060702040c02010605 83
    0x4400340402c003c0c048070f04c000424414039015001c42c2c0c81c11802c44040e4031034030484428290799a2548107070b030040d85045031002e001049980301036070025080d404189080d80107508081c190000900c118808500c200c00b0302191910502c0b1a441d20b03000304000e00340c040c000344a10030036411102e54401c030031200c0c03400c2091112504010703144074a0458401015246e10911002c90100310098a041f4180c0f0f12020b10024540341c810f100c50900540d4070503500790f1105896107280d4014416648615158a10060304d40001400066005016503091b00c0e0140c0350681e40e80d40e40d00d4124540064100700168040d40a100794070010750200307441c81622050b68800600c0d0310382d04130200c182e035031a07840254060780d00e10015003040c1c42907029101d0105120804a010341005601e1420309120555a410f06101c604201e000035404000c40c0800c4042c02c8420030000e09581c80344040c6008101d86017080fa20f071a4028030640d601d5000b6107035255001801000700d000300c03240103402012940700fa41d0088054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940747482 1250 940746232 940746241
    0x31c0f111f200421081e0c0601081608030c0d0f17100513140a0c020c0a03051615080403050f070b0f060307051203070206090415030b0103232e091505 66
    0xb00c800360041d90781e1121609040083c6d25080c11401c003800222060041401d000a01d1380e804c0c10811103000f000003401815010000c7e02000030285d15581003c0c0c2e09600c200002043e2800001c1c2440c0040264502841c0b41144150120342c1000110203080070348004409100002c0b40a560071011100112080580c4030031300b4980d40d06880d0b044245100c5803500c0b0000a1043d040d6422a60003903090344143ca59a03140500024030400e1650019221940300108040c2c61360340300c480005c00f400f031649515030070b880480d00c000c0c540070008000904005010900c0031113404000c05071190142e00c0f111010b824640240074502822048071414480d01c83d042e4001018181108140110840c0a022b0b606c1c0a8554003448204c0d8007505181f81c005544482104030b04990700a03800103140315a4038140254590b0900c1c0503c04031040d04400d170b00744490066440b00e10006103803640c501c1141c04140c2d4081070f60745070380710000408a440b240d0314201400d1400f00006120401c01c0d1315050301080101d03484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940748732 1250 940747482 940747529
    0x406110426060106030e060a0b0a05040e070e0f010f03080a021614100f0207050118121203060503011a0d1104021329040b0315031c0f111f2004 63
    0x6d09030f5040d00340d60802004609040305507082401c14100143c50b0701c209580c1c83c400304d02111039503002d91082e6040140d007404001440a00e86402803641c01201781c4e90b50514114006d1994584802000803000040140d4064000e00921200c0381e900701040c00401e40d0b455111100f5080e03009904d12844034035100c110f4460041000c040c0720100b540c005c000090070f0500554a888202d02d8150300c40304146000620800364030180d0400c03610403a10017444201031310018060300d010b130f04006e2082e414076405140f10402103070602d100c603c0c100c0d200070038980c403400c1c04807141e0003e43c20b9076002400003d03241300c40501c0e440f0380c070111038100090213080384041445c036100d80054407103800e800790100401c00061691001030342d0899005041170141040b00c40010385070444c9078006845240c0c010103040750f216000f656144a003203060a02c54494081d4904240e1169a0208108403407610846003805400b00c580c01104180d0714901c0601b51f00d00d82c5116031502d60040c0c450702141180c0070a04446818 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940749982 1250 940748732 940748741
    0xb011e0504050f0a080604063903020304020111070816080c0d110102032106040b01020118021c0c180b03070b0f03130f0b060102010b030a0308040611042606010603 72
    0x10303600d0504003030400041144100d00015120741c050100e14000c81e10403000d02c19603003e184200c10004250f02d041d03041c0b41442c0b12601411070f0a400410303640406080415000034601c03298540165a0b503203030310050300c620321b61b00c001c080148200500403501c0080040c41c507104002011500a503030343e4a418041d40c030700070ba01860390403032402140030300001c003014203201102c0b005005072418007140d100082d0300485030041c000c0410045406000b62807c02c0e1184243c104c000784028807007103901c03142c1c081d10000e64400090081c01e64024115221510040020669078064001045580d561000b041640f4815030800c444501e0000010070310b1338009010801c4504000d040b905020b130220120401d600002c1403c1c0e0307550040d0611600242c803494500e45227900c2203e20302c100d0700385072000a007100c000c200c1d554001e0f80902210004688c0016040398840d52000c070210b1032028109080005020b294000d0211400c070465440c01a11451a0900d01302c46074000ca409507030744c0705801c40903103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940751232 1250 940749982 940750037
    0x12040b0a062102060f120a14160e030106090e03070507060c030c030804031209030c15050118050a020c0d1707210f06051011011d03121e01090b01 64
    0x308045203094807030103070b07654607484480c0001c1a540c10f00110504a1075941d22120807045100b41c1e14003000460710300b84c494407110780d0101507585180c0ca007807003640401e4504040100180700c404c00701c90303042e541c00f5084400074064611003402501c1e40b51540350b40c1d0b5001108115050300400318080b0301207100f41c488500e840d40550303d00c4000440e68500b62a0740c03001600c19030400501c070301c00c900612110301444100d58403d644640c950100c9041140380c608000005601e0b81e03050000400001070540312460a00203c0c03600000c954807010060402880340300c103450f40c42c0c02181d45095100380c02041001c882c61400c04032560b01d5640030004c90b10f41d03522a980f104456000e0300a80941c80b110703404000c0ca58802c0000103102600c03070001400c0750407868240c600241c100d160801c0c2c401028010700d250300800c0d4207100881d030300885546869028001d4030004030131905000800386501d080c4071104500d46098041c2d06541c40310044800340203206921404039210031540c258280d01c0300c13a40e042d40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940752482 1250 940751232 940751249
    0x108010e07030308070912120f03060501020606060c070305060c07150501050904060c0c02090f010614090a0303390201031a0a140d05060a020901140c0d0302070f0812040b0a06 77
    0x765030035a0340545404801a00440400c0040040400c250010301c00c0f01007400e020307582d100409070003214010154400158280c0403d401c104041040b070741c000170b40c0c0303400031007c0350744548803440e4101240c64a0b50030742c0043c10b584104402e0041802003007004010690195040e42103007031140d2a0300c02138803020702c00c00d5001a408400100171030441c2e800142d00c0315251071715444401858002504050058400d070540403529001004155003005880c2c01a812004a42d0705054a041c00100303002100d01c409070901a11104060403845000351000c03245c61065030343c0341d032104520703040c1c1c4400d17058503000c0340030a25080c0c000d000b0b41d038841ca0050382184000c245183d00381c10007001c1d5010291005080303804c01044045032002a174280841072085008580c01621140c0b401d00044c844407a0011058500204200c1860491004901d007120304616007405a501c1105103001c09419040400107032200c40e000c50340713150300802071105901071401a5064915a183e0b900745a01700c813058494a40c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940753732 1250 940752482 940752493
    0x1200a03090f050d21110f070606050618150301230121050604060b090a091109040c020a0201080a111b030c061611031903050402150a050a080108010e 66
    0x21414401d4001d10051032042082042000c0103649082c03410180390003c1e030200c1c03107103009100000304100c1100c40e0b01960040500405000500620707041c4504119003e20b4100005c00c8404c4c0071443d002103000b48405410305a0f600a000b801d0008448201c060350300c5201079407100030001a4000940b81600e1700c281100280d040d5011011011995112140c1d0502051100c050b904006c441600002212020000314052400000f000100c461a41064801d480284800e80e481d880e1844800240e469050000444140c3d550300504140101055242e105082910b90034500b82d0110b0099043e5100307032210301007600c6a400320425105031080030900c1840a01102001060a002e10459014000143c03803604079103060440c1408021550007558004060491250300d510008a00c084007c00d006142811200846624050507940040703040545130030105041d56524030800e81c8a0402414071590341200e1200a070198001d070b040700e4042181000009401c200c10700501920000c000050f00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940754982 1250 940753732 940753747
    0x10e06070f0320161a090a021003060b0d1e06031101050a1413060f020a1e080d140703060611030304020108040813080a150209031b0111030d0b01020120 67
    0xa0003020341c01c07814a44110480d03280f94007000e80a000780040000b451540c80000b4440c20112442c4081e82d10240c01c0d4181802048115400031604a4405604403584002d107180d001e0101d0250040d60072244c000d1400284203503640e00240e029100c80c2e400584900c6e44c90700988412030445074070b480060084040d030b00c01120151311030300040a81480310705040d50613400d054020310f41070300922118840d20f1500c500a10810b50011124854030301c9500c020600c0c8405030388c42d02048410b60100c4105145040c01000802c444001036400507124081d04007d035a031028010ba103034401c180c0d0840c01007468820049410382c0320300c208d049004240c000961543c0c54503030046031050030042082e122048180205901140c0d0000c90b940200709140003400b111603a42031035441034840000b100e07890341c41040060010b0300c0c00b01d000301c90724610785503450994404c20300603079110315030620034841c41c040014800c2e00c50105d588200b406a8007a40200700c52120202c1d4441c140c00d801d180c4280c025000c3c483c0c40b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940756232 1250 940754982 940754987
    0x408011407111b1512240607030914121005070e100801030b060d020a0b09032e09140f160b21150a080a03030e071805040212060108070602010e06070f 66
    0x13210415040ca1181c2e1915802449401c1d00d16419a014149003000110203443c12a540c640c1215101c01100d03003600d040b60b5698082c26400803840303024040000700320004055130701c2c6d07002e40300c5000c0300c18103440e01d400c02e040d4180000c00b0304139034980200320501070f5941c16040884800d10f001c5032a486d522040c3c1d096486034003203640002d003120703031001c0885400c0340184c541c001d036800285201d00c1c2c078a0326911001c04050030050001101c0c0154003040c0c0c90142841c2036180c0c1c0300010042d8010015100c030b5942040c4008a025400c4000340b4400c4644200090341e00160382d52250031084580d0031881d40318014010248205d44180700401c050300c2c01e45010400e03100b40705030401c0349111040c41e4541d181e0041340801910341e00c4640c86811500d540750030b264140c000d07a05000e00000c00303022114200300040321800281c8042d403000c00d550b40700240440d21800c0b4445803100082084071903560f9103159040c0c2d28602400760300015420008403480c0e410000401a000300902e40303070f10f44c0c510f0680008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940757482 1250 940756232 940756249
    0x20301050d1112070609060906020307210207091a0312031015120501060314090c0306010603091a010e01061d01080c07020103091713080303090309090c0408011407111b 74
    0x2c5651043c065480314070b02c1d00042190100a041070b840b030203005880c140d0040e120052903404181950410444800055002c0301d240102e210741000000c02403030b01080032890252542c00524840b403800d040e46d140c0c8045540e000e00d007080106c044960109483d2400c1c2601d00041c3ea01203d01000350300b090104940200642c44500c045d441d0040f00d00784c1040311030b07064400030703400440460354882e0b07442000b07103961300e0035503202030b8030307030061070f039521048042651170b08144240e9040683c0c41e2000420410305952401c0c4014100f41d01e01c103d0358440740b005808410a104002c041a0084038900c050056000722111620781612080761545e20076124180540c04240220304059a072040c0b24005852160480100000e002009071140700c8081000c0315a00300e40c111078017503071007407041001c81d0708000119413881c0003c1c0c1e240501c80e110300b1540002070045401030340e0300c4d50a115440303102c6a0a0f1384820320401071581c450312000d04600b40c2603240e01c0d51148050a8043c0c4a13140c10450510b4004c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940758732 1250 940757482 940757513
    0xc191a0601120c05030a0e031e1303020414220b06040c142805180409050a051f0f05090327040911101103030117010908040605071401020301050d 64
    0x4002d007031160b006203020100c4031000401d00c08134001100b41300c0c103882580f0605200070340b128019850030300c0c0c243c0c0d540d18103060068041c4102c84006501007001c00c4462008008546c081c1c000e210640c40d80400082d012003c65071280500d01008211924808458500e000b46400405074061a01c90074203010141441403008024800c10310a9005195082e000411545503105408281d1000030800c2c1c505101406040804001d0140035294031403a009281901d1100216400565078030b2034a8191700700324010300050080d004008a90180140500e001040961010340403c107c3c24036140500843e2404d98544956034000d100343d050b10580c003a920004040742030f1320a5400140d0030009000e4403000c002c01c85050010005100003400d10369480200508181030050f4405640420759a03a4001441100d5001304080311030081003000b9030000c1c402070340040c00a03075600c1c1c4a440161480e4060403085512150312120a0340182c0f040c4213680c180c9a0007803860040340c8903510b8400c0c0b014141003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940759982 1250 940758732 940758737
    0x203160c031709061b0307020309040e070e040830072303070c0b10050919020708040b0712030905030a031a040e010507170f0f070e0409030201020c191a0601 69
    0x842e00d051807a4919085489200654028580d43c54000b038003502680d00341c0d800c00850035003403090001c19500442524801d04041c0c4002a8030070082054502c3c040d100c2d07115101e2442c211052105012101c5d0051265844105010f441600c074081c160300c021174175a107500c64458001c404140c221748103a04c100e00d40035604034030710031614203013042c00303025403040e15001e020401030040c1e07008008203002c2c0658400441081c00d00390318980004603440c0c0d0740c01418242407040541c008082e000c12a41603600d03094000203203940b2113456001d0114aa44051000c2d03a1602c6200614400c0078464000c00c00995840006107040a8000005138040c1c0a00101681541ea448941411a85640c071844403015400000404d490801180c0642000c0482c0e5507282d15031800020401c0726203000e610160044509031100d170880e61005011a482802581065400303420040c0c1d90040c541d05401400b038041c03440301958032000880d90449400d030200f0000801d00c0301403550010407401e0a85920b03902001c1070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940761232 1250 940759982 940759997
    0x907050901230a06030605190b0f090303071202011509020c072c13020a21030804020612040f170c07050d0f021801180204031e140709020d0b03010203160c03 69
    0x104000350f000342d074a411030b0000030382d200e5040100d0328142d845400c200c1003c0c440040c4041c10150b001c07003244200340c04003001c10760000f00030070140c404204807a080d5401086040b5452081e0100034041c2030f100c1c0d4154180d107015800070451405600c211f03184400c1003802821983e1405000800c10b00040d0f144184440c140380d505000000c40c01c0c03e162195400014040c40c0000502c1080300c0b9003291f8001e180481560410344030400e92641c10b03402d00c41e405041007001e9645501c00152184110f682c1015941355007001e200800042c1140c0003030f40da10a403c400a00002820f5004190142c580c1d041455403000400300600d003082450348051500580b1000b03040301c040c1d004110213030307108140008100c040d140108030280c590224546c074200085003e602c1c0c00d02d19121800705241c4410b9900d04203c06402031810008807480e03407601c1e104098251110151785241003c025002000c040314510308240f0300781c1d05850107200b181e100358001200b000e2000941031080b074120700400000c40510444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940762482 1250 940761232 940761299
    0xf02031618050a091e20031b0f0703030b010206060102190807062406020102030f061201090203060a09031e09060c0311060115020f011e0b04021905030601080907050901 74
    0x12000107038081c3c00c101c0c00100312541c0b6107810710018070201c80340c5050b003032a01a14906d124016103440c41d9640700c0c064107984079146d400c102d0072034152400125034078280c0040c0308440d040c2c03030f60090a2143e000c0e031800c1005081c08801aa25414120740c042e006170881c407010182400c0c07a88820310b020f405420018101310103a81c2e000201c40d0300c1c0128850480b02082c081d07080113a5008010003900242c0300075801d509101002045424003d0039407441003040c00c02159514409500450130980c0040c01c617030103420001c0c0380d100140310b048403e80c00180030452500e24a004071009034116080e954075225100e10b00710080324803241480c81202000f071070304070382c940c0f08030208000b80c060074050103403010b130b03800c0000040d240c810012003121899050041c21000d0740c009010100500803c4d80e4041408030041000600900c5810000591140d40340c00e814a40d590190107117228039400e8a0310403a58540c405141c0d61480d140c81070320703800f0030341e04014484881c1c0c00140a90f08004000c7d607903500c114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940763732 1250 940762482 940762489
    0xa0309050313030507030b0a0212070e0303091005040612091713030c06050a0306210201031e06170d081302010c0f0209070c0b010506130b0a050f0d0501090f0203161805 74
    0x205900584451748150814001e00082294490b04540d0141003141ba03d0b1350702840c1c018003e4000c0c192018041080c18040e0030b51414802c6034540c90000745003d040a070410302c05400b40e0030501401000411520740709200c00d0030b40c41007040c15500b1002408000c021400002d42c198000f0000881035150040300000054107281820f024107080c0c0c943d1a2200c2610300000c003190740d280c0c0a4203400007107a08070b5403400c400c021200482ca4081c80d0110b00c80204600d85000d081c4000c040070081403508500082200c509495140c0c0c00c01100e041e0f40e4402201350044410000a80301b02c60010300d852807040040d801051039006461003414601d40030342c042c6d0001100c8080884011012980f215a00c00030011003806c046d02428003100e81c50300301816003c500c52050240c0c01161060036000408110250052007a41c0301c915029a195513242040000040074044c00e00c10220414184814407040c02c02c1e0703009803881107441640c8e942c5440c540a10072240041d08043c110400074140ca000b050300c0e00e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940764982 1250 940763732 940763767
    0x31b09030a1208060618010c021906020a1124130308030103060f05281d03130f08010b13092102010914160b030c0906120f06040902060a03090503 64
    0x80c0200000c062440b0941c801a01004004008922421040000d004040c00145006403803590a01c3d20200e0b42001e480840c855a40c198594103108110900005106500050140920b0b1241005010b14002e19003030101c0090682e98840f44050280060740300c82030034001504c0e980c0c40c615414410945d50351125042c540c02030300240e4103641c82d4800c2c40703002c04884c000d460300110703690803099071507940c41070b5520103203500044004081c4e1901c2400f0403c210f0400715908048040007660350b60701e01c2c20b004074a180030360711803240c0c1c44e038030401c00099500040c41414500080942018000701e1190102002403103080c40032109059103c0d400348119400d010a0912504a50000550384000307003030009000094105100c100c3c1d000180889410080d003001c14116a090158240c40b0344500115403140c3c024950580d410080200c2d40d03050008842610f1350250514980d030880d02e85801c420700050b00c055541c0a50010403c1041804407031299002052003030003542507a08205011500c4403802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940766232 1250 940764982 940765003
    0x602070f0605010e0906040b01120c030b0c03090f0705011e032004082109011b0b0f0a0c050903120307021e03090a12050a06092108010e010501050f031b0903 69
    0x15030301c80040c011003003144d40490300700c0302e040b00a03d42442c1541e64258080414012290510500540801006000c02000e0003039a4010303100d180b14a0082100341c400c0e0800c07603650120317201da82c1621600040204510040d5101a511103181080701c0c0b00040c00d20384c142c0824005c25655003540085548003444005465488a030b2841c2d0740c9280618441c074100003d10b8611010035454510742d05401c80400700da20321603081c02d0226481c40086542c0c1c200c581c000402400c0440e600042013044503a03142400c2c8140ca403e48100062a00303031400316070302e014a14560350168054021003603900088409907a101c00365104039900c245c9940016100c4180e018402e2540e58408503820405161916401000c1c00c51001030612030031807030301c40903034482c802c0a01904456444550205000c400c04881c612141c1e840e50802d103541f0b05800c0140410424410345020000030000420b5562192041303130102141300235540d0454840441003540101d41311310804081004000f04000c0e03450034025800103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940767482 1250 940766232 940766243
    0xf140114041506060503040f0c0b0c01050f0f040807061a030106080a06050609130b04020a0902031801050c040605070b090316030923130c0e1c11040501150c0602070f 73
    0x5074100340c42c0c60308540d206068801c2c842e9043c1081449038582c05016070394070581051410309021f086090515902d0403903000503541c5000020840c01107101500058050111511000c040d40d403201d180b000b6007030040c0c4005009943c20054200451303038940004120103440b80b43c0c0c1c85400c02500020b406c4400540c4244900d40002007103105100301841803640c0b01e0400d55607542e0518100ba455940401e81203001003010642c0c502040564644400c024060071000d04110358a09003110240d918000c080d01d94145503003850b001482004502c81540d00b240c440c0d0325900d00f01502a035a400700544000e0040d4207900c13051028594100084443c0d8000a000340c45038899141890f80e08030130001d18141c0c1c900e82a14031241c00b5041c0d203801002d555042601d1038005103a000540d812185810054501544040707441d000000d0102030302d8a540c00300e071040c00c01c1c81d806051030052100b82c4a0911404042044610700080c0d00b134043e81d0015103061180c03200600c2d0180c0c1daa2000d0b90048862420f0341c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940768732 1250 940767482 940767521
    0x10020a06050a0b011e0c02040504030c120c020906210303012402070f06032301080d09050319030f090905160f1d040b0a0e040807061b0c0f1401 63
    0x40c022103101c0d01e6000445501d0034003a001d00100007800c007090480041800c505001404002280709200061199074014406d010900305414000c1c40b8008540007581c00c500b200468400781070081810310a425030291000005554010401014940b000058401c1500640e01100c03106010310095000e8844803920501c02035661844502500440c4010020347d80700000074083e40d1201324401045500b1071402141c00d280d101481c0040040108202c003d84610300000708008a01141a410301d9203649d6564900c10740d91030815960b0410700301001d018244006005000c00c0c440c0b5801c8c00e141205081010b80d660741d0300e86900846d0802c071800301d8698501030201041550080c100d8101d0607103850081e2400d0700c4440c01c4048100c000203424843c5c0e0f506c0c401c140c0992600740c0c200000b071441c1840203c042c0745c40d0428000319170151200303e40461400b06402d15502060300c502c0d0300c042481c0e0355070007560103640d038142110040900503100700102040c1c00345440000d0089800c00c0455402700711 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940769982 1250 940768732 940768753
    0x40e03040b0d09050d2a0c0503030d0c03110a090b031e040302030a030605060306010519030e070b030925171002160b090d0f08100308070b1e0c03010303030207111002 73
    0xa050894681e1104204101c3c031b00d508698003e8a2001442030300404081c1c3c080090b180782007002d150346079000d20741500021400d00c075502c18a9210f1080003080307403414444d80501581e0403401d4032400c83e1020114401d0041808200a800040c3da40070480b80100921840b61103100322200d071040f07804070016030000810080d40e40d80f602031003000301801e0741d880342982042d10010f03040380181640140d4041820b80c0840c1c0140c420b4220300203002e250800e03249111388801503402c41d54003c6038025030b10320a0400e03102507202444a420800880c0c410802046410000ea030300d204450f2004001d0140301c0c0c6007103800041450b1000301004100403141e000b51032150714003c5100100100003e078107421555001a0030394101c03501516039501880c01005681c1d40e131100d402c0404240d000070342200d10100e6184c04000b003860030b890152201054030414418500d0400308c8081040301c14040611003403004000203402600070b0f1015034400c015040c40303135a812010901d42d04004000c040140d02c031000c2071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940771232 1250 940769982 940769993
    0xb0c12250c1d040b0415150915080c0f06030901020d1503060b0102060906061c230609010207023a050c130b0a0506030705070503030c190c030905040e03040b0d09 71
    0x2c0c45100c0c00300e00e20b81e5840c007902c41d9010184000e101902d05134640d4403010300b0340007a40c803450701e804201c10485400c4da1200c4004004003405031410529501d03004000c960080300140d500c54120009040e0450321407218184566900003612160f40c0703640a10014224251f180030354082d150441410340c40c002c2c9941400300a881e0f100840c6411b5422480502451a034041503460340a0300c152a110b040e03429500032121200e14001d03010b40300c82d001c62040454808074240ca0f94421000100b00c44050f00da06410b070f8202e20544100940c0100e402c2e04003d0208101c100c5201e40c1c0308207400740c650046603c91001d044a580203011102031708041401d100342d1030511a40602c0070b092403010040d0044039000b00f1107444003406042d10a0707101000051603548aa0300f107031400b070362000c10f4980704e0600c24815061034110804403e6000b071800d04000720325100303606440f0304680607503c13420814508001e20000300b08072032142506010030007004c12036000304401031419000c07100c40081c1041460408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940772482 1250 940771232 940771259
    0x30f0204060b0313120507020306180f300715240e040803061f1e1110052e0e09011b0e1f0f090b0c12250c 47
    0x10b241055814030a10002d00b82c2c0c5088410704662040c0c001100c401110400c0e41e41c1c2c011224001d515200e41c1040050b4a00d61206181481c1c003004112160950b0890909444007841035012101d131115400100b4058842240154a8840004c1047c0f4010362602c2d0b4a0144240004c000c440c980c45218400c00300503a4107810060101110326240d5a034108092040a0030001d0400780c01c0c0000440803a10780d50341c041c41004105035500c101c0601c1080660080c151105418221501d18007a8070280c88060050580c0380e540f800d914050080745508620340d1004020140400c001400360030b035030000308404240c00f0a40c4220010802200360300c3c1214804440d08020540406c507418800c0c0060805980980410921004e0620030b10035103030b074800706061900310400045015440101400c40d990001e000c0c000803001c07a90340c44c40d031300e03201c420002241c800c40349a004140d1018034069420182036018012101a0b80c0514203030020725061a8240740c0729003002e49203032003030480410050141214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940773732 1250 940772482 940772489
    0x31d0a050c0405130b0402040f020c0f01060b0304031e09050a09020d061d07050711030111090310050403080115050d050108011e09080a11011424010c080f0a090807030f020406 77
    0x80c2405940b03014034880e141d80136000c07002800b0211758008102150350766003181034003d000d5a81107454040c12410302d9500c85d00c04003500101e519188011500b080c8034000c40344182e8060b03c4000c1d40401e104200c2403000540b111140812503625070100711940e8414089000304140303280561100400201102124550360045405000e4041d64010079045000d005031f10141d5402c0080e156850342c180007480b104085001d44e419407804000d42017040f030180281c01c22201c02d808503000c40712015034031800c5034010b98002e00802d80c0040104150000042e141c2015080c51400c1411702450703040900036200207821007102c59445941c40d007182c81000c104e00c0748440090006004d903888589613032141e8400c02010300c080110024408130118003d401886500c0b0400c41c40703280601d40001c0507001d590030f0500c0c2c0103110745c40c01c1d41004158851f0f134140524582203100c85203007130401d2000f106990700001408050001c542d40001f0078050600503100214061100306660f002c0d0b0344100700c2162003a40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940774982 1250 940773732 940773739
    0x10c090906050108040f2a0902040e010b1806030702030c010e010506090c210c071b050f0316050d02012607020607090b1b190f0512091f031d0a050c 65
    0x411012a0074946c0c513105039038100c0c600801c454005110034003042c2103800341d5400860ba02d540012400e000740e008100700c41745046203820590700d505003041d26124400b81030303c1c18049a0b0782598680782c00f01c003c6804c000140102c0b8500403105d02520309581c0b141c1c8828507140d550ba0100400e07404c206030340d40e038468001c6403d0351601c2c0c3d14801d9620100f80000c140e10a980d2044000394540844c1e900b1505480c1e04441c40041902c5852503816400e0704a00907140039501380f0348000454103000a5000320409030b040f4481c543d50a00060000c28a222101030741044803100211006202804851019801e0580a00a1480c0010700a807400d000a04500308000460000f00003120317002060b2080c07008a526181c2605526014541ca0420040f01010701501c10b041010b040101328040400a103214405407801c41e4138615400349140a00c2d0503480c0c00410040d4000601c1c1e0104000751041545400c001841072a44401558011511114404158000c0c110b00f01441402c10280140a5040303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940776232 1250 940774982 940774997
    0xb030f0702030a1d010203070f05010c0e0301110901030b06090907081602071508060d05030d0f110c0d11010e0102072301052511030c3715020c010c0909060501 70
    0x100001062942080b0031003244800c4e5000002880c4c1c400d20072944020340160000045510b14148903000300703240c0403400040740901042242c5424103002d05410880300611071030600d0000300055010b0907a400c2d2666111360104030341005c6650782c0d0000340c0103001e1030350f510403149860098400c1241c10301d0340c07403015035002200030440701c001d60300c2416a4850302e1800310803941f50302c0003080000c510b801000308180004125806e882c12158082001d00590060510440c0d004981d0343c0c401d44130b0295015055080070305014180d41c000e49051502c0c0441400000704618014089401c98000c0d0743d0450740b00c0c9414448503001e80d40d04002c105104e903910000c01440c10280e41902c1d0b070a242c407403501481c04800c0c400c80006405061101c400550364000d0b40d50720540e8040640c2ca8083c0f11f0088668002d864441c00a80c080b2142da141503000640451141c651540e140d4034220803c60204002d1300ea001c0100804086080c0601200000103489000741c00d0f042010070350070348825401042c100a0070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940777482 1250 940776232 940776247
    0x5010f03150306021c06240801030b0a02071a01030b060f06091e0a05030f060711071401050913090311060c0901021207020a030c03031211040b0a0311130b030f070203 73
    0x41d40105422aa4000c0c0f0069480740d03180300b0100d00008098070b80303041c2c9140403400222018207a1034807800701240345101206140e02a0701b520240d0f070a000103070044140c0c600150040c12564000c000050041e0541e03107215180102007684103074241c1045130050700e00700c03c1c00b4a034101b9008070081c0000846100d0708000c8010301190385e2a91070404012040300181e030f038400396203070281c1305405410082d040e51148107034808501d545040540382500020103564106403030890109651040c2e41940341d00f00c0784011500d0046071680c001e0310010f54404da020450004032603481c800d41c0c0d82c0c944240c8923100b40350625140541400c000400451600000b00051003481c1c0c1d021440011616819406c60f443d80b60b14008914200c005820082c0064400c5501006140c0c0000c1c025220200300074003070240c240410b40d49941c6015a00c521240721a0502000540a009400030300026039080407460a100310304000d02c40c2807085911000346400d0000038401d140020440c22980040c0b14001980350205 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940778732 1250 940777482 940777511
    0x9090103060f2913021c02090306090607021b1302030a0b121609020c01020903070308131509030807141902041113031e060c0f0e0f0105030c1c1505010f03 68
    0x7401e12880d1040d441e203010780130b0440c030360b41c10783d035401c0100310402441c600d00b2011381d4001e40c05044050321a1090358009210b40000282e40ba106881583c0500385841d0304036064981501c608032a5544020100d00080078a501803015601c11000b0203004a2201120401d01054540c4245e9400b8542c015110f50001c08003051010070845501801c0103958140b1100c900340207024070701209515000700d0b0b400009010081018168520200401102d900e913200c0c051a0886030400c015004607001c481c04002207845080a000034500600442040580e410f40043c20000015415941d04c2030006029043d0304292040c2845680b0a42e00305141141c16400f400c070703641c6680310040488996558602e2442908158040c1c8154031003820b000307252100e000684070740407518820b0001122100b8514062070100c0c51145005d038180c548a00d10b8032201045801c0342e11442800c0c03041048081701240c580b1036440b88e4402030004000d9014040d060600040039042600303c410f04060a140c4182000c1d403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940779982 1250 940778732 940778801
    0xb2a0306060c010b090405070608090105040506070e040906152606011401020a050111030a050f062b0813030501060609242a02100f0206040b060609090103060f 70
    0x36000c80d000c545500da1848058050401d0380800d036040300444007403004000703000030a1825940542c581d84169540ca0004034202d440c12100a0215400b810200340c240740130740c5d02c00e035000e400580007094948407515804140c49045081c400ba4071a4404200450002d442010151859101c0e102152030090200325544907018010340d121002d0b400c07200c0b11544c2c000c105241c15143d005009101000d44008901c1e15070300129801d41d19a800d040006601113102002c40d071190400400c2e11a65406031802040040d44100304040f00603c0740c1c4508001c204110044c0c02c551800c94007101ca035a095150060039100d0039840401809a45101446900d0319056091840e14a61007070305201ca50b402021604044810300d03100341d0690000da40b101c400c0c1c10048501c0f900d0b00984d0381001c40605179030201e8800403000d41110058205c480880c00080c80d0390082c603088034008015030709110001c0c00151840e5000c1c0c0c0203c440d9031340c42d044060000c0c494040c010400d1a105214810100030008802a50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940781232 1250 940779982 940779991
    0xb1b0408070b0d270c050d152403080304140c0603010b130909140c090c09061602030f0709060608010e040308270309010e0d080f07080702030a0b2a03 66
    0x164003003070380490003031240d1050700d10a49110008158102407181d180510b13056501c140d608042a030004075840c24481c0954040395403041d0300c0c4555189a950780c1c0300800580091240d44100704158902c074250700f01170303000598082d03a03442d5600e0600c3e103401410360450544005031a0040c4200c0c50042da20902036904440d039070031140c0d5031f42065070060004414030fa003020341c0c1d46180000c51420f001c08150080070008846040f500e01c1c48550040200b042d104960344805260100000e503107a05040010300300201c0d210411400d001415400a8100560a00311540c00d903c01c200410030800203010703c000034040390034000d00650501c0050010307044020000707014800c02d40c01181ca0000d000d900c00300d45520623542c0d02c0220820b00080354072640001d4400d800100402005c3d0840c0c6055980c500b1401d6010041c4c0349455103620040043d40c1040d40300307458101c0103104100143e1002d11010031003e01c144151041454080740115000031110005010000c220000c42c6048904401b160f821 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940782482 1250 940781232 940781249
    0x20100f05070f0f09050a06170f0606040501030b01050c0d08100f0506070f020f12011d06060d030323040b010306050f2403030c1501050a0b071e02011b0b1b040807 71
    0x200a5100054401152076844160024640040050007560010105200b200c00700c402300001d8072282102c582d1010b00b0b48100b81d020b0002c020401c031560081d40302140c00d401c18104913082c428803d0201c0d04248004a020300407074070910800c0030b20341c541160b00c0054074120b40c40d5402e4a0401000c150140500d100003800034021020080c25580d9085041c0c030416001421442c5801003428a2030281030032a0a01008940124803114015008200a441250090700b803000704401c0391400c84c060080d0851807501000c5040488507900040140a032086020b20504c022b20f51443c80c100d0102c640007030014411034001d00501580240b020482d85030224020345080042c1c2031200001d09610925000114601c50782c1d41c1c0d1a401c0402140c41c504859045406c6460b0540c5c400300c00c4540d01c1aa60014480c1100c606c1d42c001e0ba1a01d5810b013003180d40103150186d0001c01c3c116903501042c11171603066a9201d10502080f50990307c544800d00040010855142040d240111880ea00e03400c50190525 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940783732 1250 940782482 940782497
    0x12040915080316021e090a09020a05030f0616031407050403032a0f0309080328020309130218100c0c09061203110a0609140c03070e1620100f05070f 65
    0x4050282e101713085120880201039101c18142240034400030001c2000c2240100381c0b182000030280390101d40c10303581014010141c0040c2e61120039040c0858040c2000905040d515425030f100072066180940c800c01d00c2d40c503415034860560038081c04010b001e034280c01030003550340a100784004124000c80b040b10b03070005944901c50304510f0190f5500d0910313042103800c0e105c0800c002d00304140c0e1140903039070006413014580c43e054108030100e880e403044880c000c0e08038549980c100a89d10301940100350351f508000c000395446142c14001100c65031002941000500019090401d0122488507200148803c1e00b081280515180c141c074421106200b022b400e00078000e01d07500c0c2020b024066032624550184040081510610304141c90404181803441240320301502c1c1200c500303000481c0300031750310440f0519070240d96281c4100700c1c8403503140042c8104030700300c8074032082000403641030048088680d024040a203218180361089502e1051018101424074040c44501d54101d80404541c1d03255260044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940784982 1250 940783732 940783759
    0xf030303020a020c040f140c040602120c0c10050301060f0e130c090b0409060e0f0709090c0210090b1b071101030c050408150615030f0f091204091508031602 69
    0x1c0c01c1404208440d50020f003000c01440300118158400c040454060005101c99210a6540b0000d1b0140703000b02b00141e880f520f00c0c03614441001c070152601d2080320b011a802e503203118010a5005110084080102d900840140143d58000e00305420b1003020b8680010b000f4a00d41c009100001c054800207203130b42d500d0074080d500b244640c80390005010001c58582c1d40702d039646039501c000c0c6000e00c5503030091249040403030300e80d20750362058900445469950400f803500b8a04080d00619086210405620441110b803452820034004d0382c45090151003181840d1904a42a010b120580341d60102c2054041040344001458010101d0206100f840e0016040540d00d4040e03d203842242c0182005101e030029142443c00b000706414403440003611a2030590811003d81c0689000560f0f0310001b10004d440023858160518002e90f5208020100720395981804840d1143c1ea9403081c0c005481c0d00d61114a40ca9a1000085228005002c0b00c001185850321120160380e41c00260380b00244289034044010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940786232 1250 940784982 940784987
    0x31b0c0603020c07170f0d051e091206190c020c030601170712060203011a07020d110103110a1817061801020915030a060816031e12080a150f030303020a 67
    0x4c0700a841e50103082503506417400c070031030303940c1e0480380803861036110341c41c1c41c0c900061003002901c0d1144101500600f804502c02190720b60343c1c0101c401e41380c102c0c0110001d108000420050075009001240300c003036607440201c407a0001e54139440071002c1990310031000c803050754034001201811580101070700d0100c030318401e000fa410060395a00110241c4440c50300c2c042445419401503040b12150310110400065615803040c56004010b0043d6004452202c0d140c00700310201c0484080403014500080d10000d10b0100d072410303802c4502190006030020031104840025410100701400d60301d07545001070b94107003545603640c0034010003034545a45414121009210250191008000c0082185075048106043c40d040340d0802c4800c06001414002d00103041000401d90003665900400030498203800d40d02c5010740c2c03450090701e2640f0f0201e184d4a920210f5103007150691003402a9468455a09000c0d1081d01a1440311824041150748807804012710304201c10390000b101d9140c2000b684031000d04606 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940787482 1250 940786232 940786243
    0x522050a0b010308031006030603020a0302091f0807032f150903120a020c0f1509060f040803090108070314150d0b090f010f020403020307050910150309031b0c0603020c 74
    0x3001c81d6200800402044580401341d4802c040d1034075034100c241e95a100c11030940381d040c03101a40240300308200703102504090901d16030018881c6035105640798540c10303099524409500c440c425410101062003040b010102c201400107214a6164266021419050108940302079040c410741e10200c420080004802c142d43c21840001c00303036540110091000c0c003135540301190580050250040002081c81d00900b00c1604a00103021003072142d040030780c2d00c407065000100aa5200e82d041c080c05901805048c000d00107009441d0140d51a80c0e2620000340c02007102a10030f0b4241400c00702000203c15604043c03da12020410307200202c0c0c0d544401141d590380f00303142c01405440e80c480800010341e0000034048400311040340200407000895404500728041e41c00025072682044004204c1460441c002a400c400180e50000e078056450841c030900082940501020a880340d41803c149504111501000c036090791403140080070b55520400c0c2e1810a003d5801850b60101d07040f245207404216 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940788732 1250 940787482 940787503
    0x414030708011a040c0f080a022a010c03050c07120305060d0f050c010207050a030b0a0b01110d0c110a270b030703030509130b01091809080a1110052205 67
    0xc11083d00104801c10701881c44800d000d0086017071844040c1d480740b1992a43d000c106041d5109000390722075142d0000a541f0503030011520004071408820011b484400d6400c641c012500006100900000040c0036110010401c81026406000240108000c0007107085400b089140005c0c55564600015511a1b0a82800307025485800f81500c00c001d0300007407808100c9130903000c44250341c0e550000c0100400860000401d0004810701080d91003145400801607201d050402e52028464400020b20300100264007100140192108009016150540c40101d0405a0780e000a0303904214840c050300f12280c040752420202d0710100101d201081e8844035007190001c05403000c55599080003003284c1c010389202840b0300c400c28116040404c41d407141700c18031003068403800c5849107440c2000000355a0310b459440f407191904104000a44040001d004e98011a140c00500403242400c152402c603039505031441d09890b2100380120aa410082c40140445074807a009002543e40317442c40c01c1030800c50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940789982 1250 940788732 940788749
    0x305040f0b090f1e07031b0b2b1407050304030c1407080c1905150d020a2a0507120515040308040201020d0e010c0b041e241104140307 59
    0x605000b4851804100900200744010032104460b0b151428280140440500000c603507001ca201000001c017049050b150482c25640380c20710070b5079188600744140d03001d01e059a81422401c6a0a00c3c400c00b84035400902d502001810045c0740303044401110156170190555083c40740200c00101054030403005840c25540c0f06545009400c1407220040d941c0c0000e00880b5220300400c06140460f00708882511082001a8048800c507854102408011580f5007800800c041d0200034081c0c401d0081d000a005d4000c130343d41c4051034025445003004125202001001a103541260301501080c2c0014080d400d40d8100e801c900c440c02d07440e280c0985004014800d10200100000c02c00042c55005044035103e10300030703000e80c2c040089684003215200c11034600356012410400030600803e4055030416402440b60308110051030110306c026000c0e00303215504840343d611400204404000c640c0520702d50709000301e02032050403200b150b038800034025400340d032402c0358244070b0030440c0d0703642004058024410b10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940791232 1250 940789982 940790003
    0x403140c030c1203010f210305070f0803070e010e03060403020c060a18120303150e0c30010f08011e0e01020403240b090403050d09050c030d050403300305040f 70
    0x3240b0690944d0402d102d043c080ba00011000900d43c03c0c1c1c2101c0301e507104090318410507060007654090310a60000802a030b400342ea1151901c0c00903d00744015402072000c2d454503840000041d0005161001505000780241c112405000c00607800140c036901d0384004480d80f41e00c480d00c1880488100c40f030921800740019100c4000a14105804280ca1005000b680c080c0402020101030301c2d18200244905442c000c90b060000d4003050114000c2c084c070071080780303411820802e50f41e40d002c0384241584420f21044111401085440b540412101c01000400028842400000031020610155542d960401c9440f400951030b0004c080d41100e0143d0b500a41c803400390490f0f031510203030391100c020701c0142103464a5008046c51420820131440355900d6620325207001d001c0c400a0000c0d1070b0010080300d00d4850071010420302d84d420f100ba41c0e0b00180c41d60741c076901c980c990b0500099291218460182903a805141400001b081d180d400d1648142418042520345480c9000d02131704400010140084800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940792482 1250 940791232 940791253
    0x10617060123040617010b0a080a0f06180209030d020f120f0c0f030a031427010b04020a0c11041b110f01020406030b0f1519020c0319020a06080403140c030c 69
    0x720906000b5244c40d15170201c4907a80790721109030355110300000200400c040c0000030f21510080d03086558220034170072010910580c0c0f40d10045011707191100c1c0003070700c9801194080c110b0504204154a4807928801084140492240f40f51600c0c04202c143c040003900194444401c12100c04841d400b4908034100c40c0344002a298607900c0b504180700102c0042d0a0041340401c1c84220b4003041d001d4420207030341c5036a00d040b2003110a03c040b951401200c8a5403110b515620380d0369148058050326210341c0710064005681d00e000c0c034244005810b4107120f0f07860301c40c1d0000709d90310b1403810682490031418440f4207011400521440c00c00074801d0340e0100c2d0700005000c82da0943c517400c210290007044d540b61041301070760005c00a5030f44010711695070100050180500203c82c400c01165400c072341d801910b000d00b60200200f402c000341d450302ea00b50414a0700889003141000800003009020b40c0c5007070341881c2010343d4001c01c0711210780c0c0c0d400400c1030003084001d400c940034800c0744c840703089d0309080301c00c001d0a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940793732 1250 940792482 940792487
    0x61303150203040b0106032c0c0a0503070f0905040804090e070509160c03050d0603023607050f1803030a090906051507021207050a1d0106170601230406 67
    0x1a00084851084640201031822014002e41e40070766030014050800745e003409022002403900310380155051000802180b100e55000c4121041386407180042c111001d018000e004502c1481d0340918000c3c1d10003002005008449500d0b03006844940f40042090f803110700300b41146020340d8011600c018603011400010480015440b41105c0083d59510354030354400301001c690309994600341c800301e0000011840003a02c50310042604014069002511946a4012a4081403001d10842e0f112082001540c85040c40746050f5240200301c00401e0180c0c43c103001d00400d980100d1110559182000c43c28821140d08006050310001c405421603495205440d4010410308407446446440c82c0f4244000ca6641084501d441c0404040f805440ca80103081e030070700c00a05030002508580340111003001c1815580d04140381c1c0241100c00e0b2a0285810700342030410022010fa10060602c14072000c00513000d0a40504c1c240d0004007400c0030741c0300c0341840030350381060f54005040300916035001401068154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940794982 1250 940793732 940793767
    0x40815041505041a040201050d06060203131a07030804060902060c0307020f09060f06030a0605031f0b0103060e0604020c0c090c0a260408032805072706051806 70
    0x5018419028001844404030400c503001540c01405080c49800281301620143d00c440360058810300d050751820030340030030800440c1c80d0381d04800010707000040d504041100c002048006007141034032411000311099040d00e814810a10000c041c014808001402c0c450300394849020b8603005041c580d542c940d200b45a41d01c0e9400044c04910500d040a2107100380d0401a07420b0303110f950302610444076031205500f080800c0d007000f8440e0b0046911902c0104060302c0500440a092a60744400e040442190004000b520310003030b061030415103807041c208020080c0540590300a001a1001603a0760303203082d0b04c241044000411290071480350014021440148002825101000da648509123040a03004541c4000042075007004004280c0108012810840003150086101100e5680250a15444035054031000c0030b003581540e543c60400c0f103415000204007101d20880240c1c040480441485248500030300e000c0c1100b00400480c440311290111500e810400b04000c4c075890300e138440e0420710041c00307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940796232 1250 940794982 940794991
    0x41e120602040501031a0102060a1802041d10200a030f060e011a07080702041515030207060b0306060102070314010207061107030908120403060c090e07030507110a0c120305040815 79
    0x2071809000280d00c0510300f4106d07500c0201680a01041d80320a8071800203011100603800700b9180c03c8014000581c1c5610603000d003071040c2d007a0f00a040308842001820035001d130408800e16400c0007848201c0400d00304066a003942c0d01100d841d00d580e011b0900714003c050380d50312070f040b04d841c101c1b020600720800305400d41281c41d21002010345021840701e544044c0074680380244044800c0c4a20030043c500343e040341c1800b40e00c40e00c882c540583e41d0650041e0408801c00c028000c030340d0002e81074081c01118000c440c140f480030340c003c1216042480000b5540e900c00d01c030261804161010050968400f0b404031010150802e5044c0023680a07a808002217074000c0ea400c802040d0517800008403c1d03404680051407840e041d400d2418140781d900c40401520540006d0410491003c1e00401d120a055842502640030703543c1c0010145015103020388000d0307040a0f2861568494010600003905c0d4800503014ac84040005002002c1989820750301400382d5000304446006010542401c0380309800c2080c400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940797482 1250 940796232 940796237
    0x20f120411010201020715022b020c0607030501030218091f0f051302060301120c0e04110108090705060a0e0a0b0c0d0201050a050f04061d071d09010c05041e120602040501 75
    0x201c03100d10005900301d201d10207009102c408154029000d400c2c00358080c0402004228044210f511440018020030300b00d8400e20000f10f60201d403c00390040c041105c01d0b07001041e0f00b0104490350550300000c10b9840c0c0302050000c0103000300006210941c0c10b000f003a06600060b0680907412000c40e5051000d4190020b80d4058180b80c04001030341d0410318030132020416005041286146d0910300301c141280700701e08095030028030740100050710060054a140c41b0303074001c1055800d040d8005c000102400d001401c1055290300003541400b06a4901c0100d904994040c1030410740c94101901180c0710701c0341d541c0503441420020860110b40500420070000742c115641c020001941c0d40314400040725030903168115903c041703a00140004c2c07a16440340f12800d1000148100c04010401001e01e0010260041c000c95055800800b07043d992040c0e0707a90f002400d200090040c1058080c00410602a0744280c0a014127507041590f0420710950821010388804000c0d01160a070b10305042000e503100f80b20b0701c3e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940798732 1250 940797482 940797503
    0x51e090f160b160f0c0b0301030515160e010e120718050108030f0903160305030a0905060708030a110c010903030c0f1d09071103120402010806011e12020f1204 70
    0xd54901102110141d811402d07800742000c0c1d512052114a03a0141d1040b25140311002d0001c01154078182c08800a10100300700310b551750b046150160401941c1500c030511110b0000520030801b25403151034a1500e00c518049200c00012401240c4901d07100808903000301140398030406500d0f010031440705450304114032240c0c0e08903031411901100c109120b2100c075500240300040e0044c62040007841d144100508850b4080c0003134041c1c940481e40c61b40229600d900c0018080190b941024052000789801c80741d960a00300241c803403e5544c84000d1a800042d581c0f85903000702080e20758140d03007880050800801c200c5009107406801000d205c012800030404041c82c201c0e47d184541620111802844c591894030b41c2039405010030440040e0025003171015460350640701d190108090500654003103000441401c00780005450721002602c1c4d1030400c561250942d0700300b01c0345061103503149800d03d071560020f8418041c042c02802030700b047e0003a010002a42d500911414080c8900850044140c1d80d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940799982 1250 940798732 940798753
    0x7050904271109010b040504020708042103020606031506060c120307090806010e011214010e011e0c050c0607050c150a0c0f05181314100f050301110904051e090f 71
    0x303010380f8248100300000504010500031030500390003808040f4800e07440f0720f0a050320f071803010180000ca910151400b110f801294414540e0400c0307001d400807020b074050425206180d40064040344010002805504002020317030901c00104239958500c1c200010083d1641405400241300400d03034441c0314202d101d920004141c410380f44800382c0c1210708045605154010540c1c070b125550304161000d00c02035503901d5040c0b0014000703006021042c02140c1420059906056081045420218556040190510142c022803800060f2540c20142d0750410503250241c54890503d00f1000130304404021580006000b2104c405030405810440d65880d0308035950500b100c21110b60245805200404d04021424030003803e2101500341d00d02203050b030102e403807105000802c0344a50161070183d903d0401100070450300122840d2240030780000c5000340105900c000e401d2110340107040605105070b5075031000c2000602800b0680360100d150007075071441452b00805c80c1b030310313091040c0300ca0415006064048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940801232 1250 940799982 940799989
    0x30b0a0c02010605090601110703080d0f0e0304050319050a06060b030403020c09190e0f0a0507170c0d1e060c030606120e07031b0b030a0501140d030206070509042711 73
    0x506541018040c4025a41e807000115001001c0d480001414081c1c27142c0840410305400c02480312442c01d05e40403840400d011000341c00c882c0c017880c804440741c1003840107114075a07000c0340344060b80d641c0382c40f110080c0c4c030907050040c1001203000c07005080610700540090151340100186104034080d800f69180340c4514010301071720b00c0d41210f02c00c14240800c801c4440015003540242c0c0701070742c0503084546008d010b8001d03624000b118081901e056201110810690340b20300d40c10074800c51500050204031103011f010510704e070b010400c014203c041301001016130459407088503c006400c408184081c1c0031140e8041c0051025028074070001f19411822100039109000d44178200070024002c028291450f107403845101c0440c10a4280940e071240000341041034003028601842c2041000a165490201c60301c606905101006000790200031844010030340118820f5802481750518541e102062000a0f00034015082020b110740d01d1141c039203105507079201217844602e2151802c20002b10b480c0040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940802482 1250 940801232 940801241
    0x906180f02090f061308100603050d09030308010b16061401092906030408070818210607082820090d1101092412110d090c050a030b0a0c0201 62
    0x64003e0045642c1c0440c0e4149000284140c0e240840b008282503160400c103030806410103600c19a00d0b85910090003402024000f04400d4032903820802c594614554001d042c94405100c0c00c20f5145c07021401141c50300140c0c5000d03000c0c0341c0c4040c0400040c6108558100100307806e000721800603290400302155204050007514a00c80746400c0e100c0650100c400700299940000c00072110544140003040002c6c0741c000160a414525032840c501c4414550f0600161907046c1040c400c04070041d569184c000c0101041844d00251149031000185d6980914202406c192610a001803600f4100030b00f05842680d001c0e124600c1071745020031183c480448209040d024070a40c5503032004203901d0300c0001419169412100c048c060608203280c6544825190030600c5100d1504665000c00070840011540201c80026981c4031040801c0701c290f520300122620700450803021800c2e23030788156042c280b12190302202d0081c540100307080041d544038a800040e0250940784402102d05100e00255594018040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940803732 1250 940802482 940802497
    0x80c0a0e0d03021e12090d05030f040b1209030a05160321060e01050d030207050108040f050706113a0c32121608070210051c090c1a040906180f02 64
    0x10341c181091006d6081098803e10107004072000d110400034008900014006400102508244642c0b07506290600c442d07a20030060441d1b0303590b001007002b802c4a82e0040b041d9940103190380fa1406440383c4510b425115a108810441281c2c81b10640210b240d070016040341066aa0b0305034140345070b90381d6005011401c1c0b01d400c4000d0141c0c00818007800325512901c0b18581c0301e4040c1d11403142c1d00f4400c0d102c2509024951300440002121140364802c650410080e4080913913035480e1055890000c0050311071000a0700042804407120b08040e14400352160400700792458100b01c441885143c074081c08503219000400c00d40400f00d10380012240d211010406000106200da100e5240c100c94607440c10000890b17100440303010100780480005a210b00d41001d6000d070080d11819a2000c00485c0c420f131031344600e1a1919440c0c00c00e901745000910399041070084500400ca41c06110f00426a03114090045800084646142c81400603601c4003265060038040e03880030742004454400c41c0b020041e0700c50700c00b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940804982 1250 940803732 940803763
    0x1e04050109080705091f0f08101802100f020c0a140117070e010e15160b0901090309031520030a06060525060e0a14070603020901080c0a0e0d03021e 65
    0x1007031145003401084d940803030444220011600c1f4425040103060503000710031290f100b925100900c040c0361103070000340b08441c02c40c45090041d0781c2c00280c0f00180c0a140303038100499204003010f024020420011281c000400002865458210604800e040c0c5900580003400c0d01c80000325000e83e51003858002c0781c1310b5a807941ca00500400540b03124000c038585940001090f180302641c00d84030005000d2001e581e110b1500500c3c0f41e824440c1c075900015000d200fa5034504048600020340099680040303a50051240e40700440c0620002d000302508411071041e99824a2a403005d508000c008510941c0d51140030090103484d220115480c1c0200c0040c40d240000c401d0740009068201004820124482c1c03501013220740156002c2800e0250080085600d042d00ca840e201d00e880007032140c0000303041d00b4941103041000040c0002c00c0c1420141c8611114040010742a4441d84900e5020101420142c15111400b8062400070359406403150030035204d00030040c1c180116000412603c980a2508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940806232 1250 940804982 940804999
    0x40f0e06010e060d02090103030807031d03041a0f03010e04031707080106051b010c0c0c0e04020a21081b0615010e060c2d120406080406050c1e04050109080705 70
    0x51490580c034003a20b007940c084013041c0d040e0010390710034100c40d01075803080d80c50b1055810310b4100501902c9200701140c50780854a01c85950004d07001060314202c3d2134904052800904d6000241501e1141880020106800000100b100f02000b0003460042e80b103544c810080701840c03040f426529a064502000203005a8010031185210b00040c00b0b200f10200340300785220b48241002800c44901e0030010303000c5100d41403a5024001c0011000000b0301003109920214130f01540094581501400b5500060082c1c851241e00d008130b4100100405501c0201643c0ea01443e6030521040482c00008130303c2031091400203240340d107a240014041d0f0030181c5864070001c074500108019600241540c1c0c00500c180520948034624040d42d540809820600325900e01e1004600ca905090040c1d204050802d000c000410041d54040c0b8030960254014074009015102d1a00324481031080c601d02609104046080c102100c40707980080040340d03c2622580c0800350303240001621001d09200752580f16444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940807482 1250 940806232 940806239
    0x62d0d0f230a12050c070303020105100608100e1b03011e091509053c07021c030b040b0904030806120a03050702122104030501060906180b030316060b040f0e0601 71
    0x82085412400f03141071160a01020181c09403805050340e00560050303469109125402c8007107003a500243c429850040058580f414402804107400d21546001c0c85020300050905820200ca600e044d4040d03d08080e980d5a4520780c3c50030420320403000da02545055000010084a41c1c8103400024050403048152640341c21300010040100a041104203454803d1100c080d0822152441199034a040d0741007805a10051071076441d4002001d480035548a1384100314102485049400082a2848c010482510590200c0c0107030102c1148250007081c1d0301c060204141e0030504240c0320728000e41e8000322200d02045803559030303902984081d000c1a001c100351005402e20101c40100085010200e4640c2c80b10141540300740c0801098001c4035400225090081090a02840c0010301d855074042c0081420407260b007050740c01c05031000043c1d540d03400302021152018003d990448148524420780c04609041440c0078003000b21020780710741d15107404002c400e05507200301008045650000d2005a08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940808732 1250 940807482 940807493
    0xa0e07050d150b040b04060905151207180f02030c09030f0c01050a050306030a1a0f0601020a0b2e0801090b010902120610090b0a110d08062d0d0f230a 66
    0x250034400c3c503040b41c5c4461102d00b4030b403501e004110050900e160002401e28010b80c440c3e0f1000e50f10890301d446080c00403420072040b9400250300d02600c41e5810a441000760b10709070b05000b03006103444044118004410001003081c0743d400392120080a80a6030303c1e00c3e02d26500584c885c0b0f003280c0094042039041c0100110144942e02031540104082d0442e000c410702d9072622480c1d0321503028003c5100406204001c0b85090403141c0c950445401c3c0001e005614150342c9619452400805c3c00e22145028090050000c05070740c2c2e02c1e00001550300f007001c8007a443d620f109007c4d10000805680c3c0f8005d40c400000c024895208442416003030400403900c50b29484208005940f4100240c01003041560380810040c2d20741340100303952003043d221004409c2d01d8a5815082070904513005051000c80310403c001074a90107031414600c40099801305031082110b003180d5000c0702c031851380c6800402d15000001002100b03040508498003541d207418100c08803410728203440d05c809035164065084141c1c01400640c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940809982 1250 940808732 940808741
    0x41d1e030d090f0611031f08070509130b070905030717100c090b040b120601020f0a060b220e01060b040609140126161106010311010c08030a0e07050d15 67
    0x40c0310f100001d21400098480b0002e8455540c00c8414101d000028800201420444040b049070402c1d042c5421a01d0004d46070f460310400d10560b0302804511000400b1260000290805070307074400c0c0d8a070034609040d040145903101d1401014000d01c41e04002140030b42800d01d404041007034550042079605200611400a024905005801c7c0400c0c140d0204000381000c2c0504040d100d403002c22500d0301e0110700404000325002c0c11090542d00203722000328900e0101d0080041c3e07803c40d101003020928040407902d8032441c88441001c001c030840c03000c0744144080e004448110010f600078050142c6898a0203901d00c9a885260003007112140704022100c1d11144074150b840d0141800039698110b55001710030455540134100c80301a01c00100320003445211003030303154a20b807490700c01c0c6620640c1d84ac040c0d8905040c000a8408405d03a50640ba0b142e2043c2e40030000340703510603101d58507814944211030240403500340d1940c090050410204241c18aa2001c07074605401842c204582420601803100a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940811232 1250 940809982 940810001
    0x6032e0f290307030f140c1209160602100e0c13051506040617090601060c0b040804081504050d0810060f030e1b0306150d02060a0e041d1e030d 63
    0x31a504040c19060980000074521890b511340340401c8408a20004c07000b195404002d00001d100601c0900c8802c00064040c3c07661038a109100400f507807a10001e5030300e031880b43c1c10b0301045810740c5200031400c0ea0b800311354141c0245c810b080c01e000803020303500c0e825107a000103020f4640000c50200c1c400c030b018800303412243e000082428000304880120740460040d0f4426000a0301103001c00c00d6120402e10401d0101c3d5120b40148003030500da504103100203103007050121000d880c4a041e8000300b0107101100c03040714020510402150740da503d15002115404a04545c1a50b95006106620101500443c1124440c0041c07100b000340340da04007802610281c0100c4480401c01d59520320381c40b20300c60200010300c42c1000401110b50a0b100300340c101841c2c02802854510004011030028000f07480c0c880c4001c1d20154105c5c0c0301c50b00d4289400b021a907200080c080240d00c1402d0040b09074603008513030200c2c60113031420b0f02500e03866611888ac0010241d180044400d40b580f04010501030b0481950128100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940812482 1250 940811232 940811279
    0x80415090b040803040b0a050106050306150409052802070201080f070e0d2f060706090302150103110907030b0d03260c0a08060109030c090b010c0206032e0f 69
    0x1102615241e0100d2600c0c1200d04a40403100042808103110001100c0ca610058845c03042c8442e40c10500018a03500001e0202801415045e0b02c08007030201381c0c0305407400360181c00002c00082c90003005000740c010b0680c098000c114a107030000101200940219903980b0740684a4103001e8452070a10700b080c0f00c0c02440300c000c02100c544885420382e510b00c0c40300c01d242d0044800d4074904540b0b62000e03c0a0000100c082c281110408824080e0344490307043d600160741100300000c0f043e0060405078140310003082c002c11000b00090000c4204040c450743c10241050a840d1900300d85e56480b000c1d0200c7e02e00e070b900e15a10035940c1003902c1c00030784902890102c1d694401c03803111107001c46c641100d034802d400740c0764824561008580c0e0310700d00342d0100c00700b58400390910700074000c103240d61100c6100824074007503403010585451104603c0d07405080000d1580d40d000d0301055480c035280011204040540b20b551451035100500c1791440f0f004010b502091f01d4000701e01a08413880c21765003030768207d82640002238 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940813732 1250 940812482 940812491
    0x6011106161d04090b070801120b010302060f040e0c0c0d08010509040222150e060d020d12031b0324051809120703110606040c0e010c061e0605041803080415 69
    0x6003a10f45028005140b0310130b001490a07130a0040c07003d8450304050b00071050b501404101c040104880c920340038111780e0107030b42840e9151a04c1607619020700c40c070b40107148071180c03080a001b0211080300042c903c03080000107440032a8604a0200d40c00b000070b1007280c0c1e010f10b83e9408038015240a52010204955000c2130007581280f0340d0048003a5a1351050341403c0c410504420002900310303911303a030703804841210440d14403001130b40020180002c10700301900a601540f0340d141082c0c081d600c2803510074442240303140d08851100000b000b40000e00311800041040d965040080e5200407281d600b514001443c803031441d05654641e4001d100e00900b012050f00c960891f010a4032060b0b002404080d000f80c2c0c2d100200c00c0240c0815240c9013001d0026030040d0320f40300d80580641c2c0d00c181c10044480d02440c100c5440c4c444c9080c50809440100201e28175802d200c0310800c0001c800d680705400303c0f40c06840c01c2c00580014007145090034500003004d0003003010080003c0002d040040301c0c00c4081000b800016 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940814982 1250 940813732 940813787
    0x911031003240507030f050a0b0319050c09160f080912090102070302090f061c0201171807061d040e070b031b030103230a05281502030601110616 64
    0x2070b5003003540c0950200356078040c1c00010940c11f004103503005500c448180000d40c401000b09548210220404401c20700020384181000740501c070100281600805104841c200f05201d080c580403010b0b200c01c0840c5221000c059180d014600305803080200d00050800301c032403010310340c800d81e0061140c030741180204007020006944140b00319006445030708070715405140c014140103041e81e13085503a0406a02c442a20401070384d014800720360b41031005034241d409440e500054070a04c4584060504580110366011504a174003104141d003014002e0a244068203404d07084c0402c903000c0302c02018407078010380400c0c00107140290003150841400164204500030802e01e07035071660000e0300b084503100300c2a0002c102c030902840c503510154003003034040e000d031841c190f0b6030b20343d034144510380c0800e442084450700011075100e61118141c6a0007800d4203219491a160301c0c0020f41c011103200d0701113000b4288405003038900280b010302c02e403542081a8000440d04106990b120130141002c2d0f42041001c0200703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940816232 1250 940814982 940815053
    0x2e0506030903160804090c0504030c300302061b130915030f0506060310050c0313060f150317042306071712010b0f07060f02071b0911031003 62
    0x10300741c600a28104e0744170b500b8513080c1810b948502200008020040c402800840c0d22940e004c0115892928114003400d10551004032100c400384589105401d40e501203030a260700454032030f1003015403082e100c0c1a44c042d5000c1c00211f02546807560700d400b040c1141480003401035070200450b60702146400c41401d50f2990b8111601340c1d080c004503a5074102e44244081800c0420804001111202c0180b00c0c0e890200c52910707480c007004202d035200040145840d4280030b015446911560540e0500b481000ca400c0c910003d1010070f403004907a032070407208100e1444035000c0b042e142500e800e503214001030501c180000007d01b1000c00c003203602c08030802c02c600c0050f0f0002c2e0001800040d141c401a00c5503210680864180f030b0507444240c6000c0308001e1040c03180c80320001c4600803544140002550050144640001c1c002c605005080000e01c042c1902054000c00d4980100d41040405000d040151070003030009000a03030300c000c21025940030903c000341c0303950046c43c88010104040d03103800340c0c0103d22 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940817482 1250 940816232 940816267
    0x1d0606120d1214090f010e010207150b0d080d0b0a05060a08130515010603060602010b01020a03020d0311070c09021209030403020108011502031c0c0f0309020a050103020f041206052e0506030903 85
    0x402004c0c1d40b182034202150b40703080c042c05820b213060000841c01d240d202d460b0519400d04080c0e00042007541e0380f032000000e07070f124481007500507000150305464500070504032005060410710b561166500c0307140000d0703034917050084031482012039551842030340729a6604050884142c41c01c9031203004500d00d03000d40d4808881010300811a41d40d000c01e801d8900b00003c2d0031035146110150454111583c1e641c0842d80009440025203000d250000d00a01001c1c1c8850840c000d450005085010920b800143c01549401030324a100c0c90384101250750b02c46002a1780e691049103c0240415040401004001d40078581c1e075001c4001801a285000c654240d200800904058402022691044d203404a554810040044810542410401e0300601e400186440b03400c0e10078181003640000390001001040c40c01da40042a101340c121090100c2454001c018003030480d803014414000b442c1c0d840302c96044100d40300b60001d2000403410b50900303010500805510007031942d142031108100003013060152803031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940818732 1250 940817482 940817491
    0x1501481502070303061205150c0708070602031609030c0e0c07050a0507031401020a14090117160e1806130e0a08030105030706030e07170c041d0606120d1214 69
    0x10781e40c011a03d0302408403001d9400441c2104807406880c000541c0010301c205001301c0d056408c124644e40e0051001107880341d01e100500840c4040703400b0b41000401d0b00614020946081030074200c0740f14060443d128051480003a198052544080008015940c0416000b81c0407442452400c6084e44a4619041d80700340211841e501c038104c20030500c0207a541da4501050407600070b528003164004018a060704010354071485c0440040e00c0c0903180e001d0070f00700d48502030948204085160295038100001d8120300c4000110304000c040e04041c0c6071000001c80b00c01c0754640617840c05d40340c400c04c0c13101c1e07440c40c2100d600c8099030781c1003200c0445408011580b420f40c0310300600c0c1e81e250f0400d0706150818100380c2c000170605041c0b420344400031901059030f01c1902c071001c0b030307684403506c140714103501d44003440500c01e410a2600301c80102c4101c401c9044250b05a200c0300b00c03090341d00c0c0c86080c44900c0540c422903c1d0303e50800140401c1c05071180c100620300310740c00d54001c100c00d6480c04046c0050b21040d80d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940819982 1250 940818732 940818773
    0x13e07083909130b06040b0f21070e19060b220e0a02090f0402030f0609190501092309060c0c030f1902060711060f0c0d05150148 57
    0xa1420411080c284d446610110039507040c000f602c51840407441480c0b0324030001c0e00c030340080000704421110b00340c080180c100407041180e0b02c0c01c3c0c0d02c1050100e80507080d15001084503c420021800703844901900089a040d5440c9524120200050211108114440802200c170030840000d41f113281803009070003210041c400513a2010322100704200100407241c014060750040c030400803c0101800035650040c0d0a489008407595040468900310320049504034201e03243c1000440c84060301d90102450340c1d081206040303414250759a00240d40021035a48010f07a0052000a01e000b0018014140d201816400c9030306014103d05012015084950215070071f01c0350341540c0640560400c04035420007400d040c6070b1021071020501075141e01004001540c20780c95040403031481c465078801c03603450400720031040100c0d007000042d0803101111520841d00040101000389808002e100380b20104a504182c1d01141c92906d07017440ca038581340d14844034520304c082c0b1001c0d00801c4050f09102550603120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 940821232 1250 940819982 940820011
    0xe0406090507260103060902060f03160801050306040c090c110f0102030a1d0703170c010507080a0f0e1009060219030e060c0a020c013e07083909 64
    0x40c0c40040081c1c0ca041c502441100c001c03241104261028089213065907040074011407296014008107006100b0400d40a545003400020400300c04c2510803d1590b141d8550381d4011283d9035101010b40d2542d09032000b42c61082d04090800c817030700c2640e02c4400c1054041c100804080d2452141d81c2c180092000000d406035000005c000303068070903205e21495000d1440141e280c1e1003007494415a144003500000f022039040407440c00303049440030280c4140845c442c0c000d101601e0405002816240306a8043c0310030760610404224103000e60142106840120b4010100650f00c0c4c0c4440010f404000b2090b01c000f0b600f003100602001301d040b1112075142031920007041c03210000c14850700d008401081c49003044000e000c440001da50219803408000c030240782424507810407211050b138081007141c884e8141c0c100007041c6040015401c1c5c6c044982910082510302d07640c3c0d10b000382a29003407600d0089124a00e6004201b00e80b4811841d41002122498500c1c600c161581000c0f4044400035a52841d051820707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 940822482 1250 940821232 940821241
    0x3060203060a1707090218130903030c020318012607050705070602060f0112060b0901121b0620070e0703060560070b071407060c0e04060905 62
    0x84000020910100407403583c20008202030b484082502554030540d400007021b80011400e4101510f01c03c000802e0310171402008810300d002420303000c2c011000b1a0904003d01a03003400070056810040c5414541e155182c00c030f0b8011200d00f000760060011800040d41c135000e440841e009601d22411040e11602d43e50326160802c940f80040c2903010382708651001c420460210400d500b102c2c1114800d85080c5501c1c0028546071000d4080e100c402a0071469000000130003e01400c400c5401d030380100102c8402030814161941e94030100e014903070119414280c0301c0c803410004404070385800d484509440c0c14030b86800707411002800640360100020384440042c000d508d405101c03603051801201521030860780c50055180c202c413074581d00200000d9030341030140c0f0300281c0110700850001100c000b2400f8610707400071901903800000c030940c1c03c4402100005c08403030280c044034001c41c100c06141800d100c4603513116000b40500c0104031081103089101c152083d03c850103002c0107480100c5022031903241 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 940823732 1250 940822482 940822489
    0x60603090b1003110f010c050a030905210c010c02030a050f072607030b06011e0509181303050a020708070306150509040f0f030c05030c01050115020a08090904061401030b0603060a0507080619050a0306020306 91
    0x41e00c2e501c90904110744481037849140010884131900d401c3c02c00e04810003090001904107481c10340c0141550280110700101500f000c1a130700d041c1c600c111450822000c00d42190012040c920b03000c040c4641c0301040034004641404001356010805142207911b00f0002c3c079241c1c0c01c40d04c0b2220050049140450a400d082c503100710440f20000c41c43d141c1c1c422600c0d01c03e002c08400380303a203500502403140009540d02018800d0183d540030380294001c442d0b12580c1c0b440c103100241354200745e100e205010494040741914000405502035a080070071592249915126031207a0020380c481201413003031041880002900c11710240095421190000842d5850401d8014410000b60303207090454010a48190002c0d0092040d650031040079075152506a40b02e29202c801400f4420f458007902500500000800801c0100b03503107d030740d080c2d056954a849401c010b5054540c00d032072007001724280e140080d0f0315080c02280d0b0484110f0040720350b54429601c501041d503641107078100f5241c45400104102c2d0604 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 940824982 1250 940823732 940823749
    0x70303030f0c03090f0b0405120c0c0301150807032a0e0402010905040c12050a0e0a0503040305011401030818180c120c0903060714070204060603090b1003110f010c050a030905 77
    0x9096080901016025030b66100d0781c10342060707001b4020768180c400709041c000100301841c007440b002c1c00c0081d039904165800c0c668070305086881c107110f50301b0300c002d01c0c50781d403a086104400c8410600003403c80703504603559003980003280e50803100d1140588282010b13860500280d28000e06401260482e1030400d03000040c02c1c0919500030711300440c02c0c000c000c030400e81c1c08207102c40b410040c2e000004540c5c607255074a001030404110400c6040c465031000a0a1200c00300007481161320a000030054012000d07047d4404142c00d200141c0111018041104800e0304288210900040282440b805401180109210b20001e458022000b00302107004d485940c402d00c00681c000004842c05801c02d02140c00081d501d500090882d41006414403400300381590782420b0740c5402c0d5008009004c880e80b81c20008004000201c0d06689443c40070010403020b21610403108142d0f074100c00882c0d02e0306a00000e0003170350804c2e040c0c00c2d03042105d903070008008200b00340324035030000e4442e64035200c4880c600000c200c03842 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 940826232 1250 940824982 940825001
    0x10e0f06041a120133062307080c01050c0d060515091c082701050c0c0105090607060203010f0905010602121213080a020c04110c0c0609060c070303030f 67
    0x1d51400e104500520344000940800400803034600c441682000d03030080c00350400000500d108241414407031501c09503a005c0c41000504410034001150ba601800c80d03490f04500b020145030010f00905142d4642003500500707040f07002e00303219071030544280c506c1c80c00c40d4000c5030a0740b0f540c20003060103110079140f40210002454100d480c100d41c140050f00e0050300303120314440301d4803440d00704694100c660001151580000c2e0000b03082610b83c0202100000c6c828941d0120380c4c04240180703d401d00c90340c011000c0c1c2d1b1442d88410000c000c116641c400540305a44510b60050f0303c07000600002c40011000c2c0020350103011079608000c40940f510b114802681c8040c1c10003c2550009401904160315802c25101e602140d03100340101e64542a01070340c55034000d10000791440c0710004540e01059000240032000c61810b8504005140c0001911061030080360f441040384e4100030008178052400c0009003800c080c0003401140380400c015945071070800b43da8011004a0b442c1d070420081e0004500c141c40b001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 940827338 1106 940826232 940826239
    0x1e0d05120703090f030f0b0c04170109051002031905060105040e0702030318070501020d120b0409120e06030f040b0a0f0509010905070b1305220203010e0f06 69
    0xa03540318807801da011402c2d072140010324441e442c0b42c2004407134118010312400307016035480c030341105005450048600414480415228440854903680701440d10001803050124902582800e0003215500c555510610030040c0c0c80c501d8500402103031181366800205540c4000060f100c41c002c80d041104055201c40802016540002c0194010382408880309080390f44840c015079101450b0181c14010b8029000c6a04a0340c05508000710180c0b501d030000c139008800702d022404441080340155180481d1443c08000c5a4010f810a02440d009482407031a51038210000e888081024000501080603d80011008081c0d0361040d1209040140180090704001514501030518010203444a0290400016100042000b00d49203000101c410101b00c2c2d140c00100071030040d03016080c0340420341504042e504c0103458802180a0120804000058140346504191654000340f07558007 = true := by decide +kernel

theorem cover : BRFrame.Cov 940647482 940827338 := by
  have h0 := BRFrame.cov_init 940647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 940647482 ≤ n) (h2 : n < 940827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
