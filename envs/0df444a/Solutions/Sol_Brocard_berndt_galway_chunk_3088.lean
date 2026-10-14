-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:37:12.165448+00:00
-- url     : https://prove2.me/submissions/042ea108-fb0e-4ef5-b23e-8797e8b13217

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555215827 ≤ n < 555395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555217077 1250 555215827 555215849
    0x2070807080c1c140d090204090c0f0603060f0e1e04050d0f050a02031801050d1415030607021c030207060e0c03150115110106030602120a06061e0e040608030307090e01 74
    0x43d0801c00620303d071446201892449408143c5004480362544421001030340940300304107018050030204080003ca110f080c0d111002c5407404a03039030788640614802c541c40f1400401802c1e040004400b01007000030000005001040c5101c1c929101802c043c5004600540140c02c00d689041402041d03502484a46020700c00c0c2004407048280e4000b08982c680c2030759412070300c0c80c0517110700125010700c41e06a2400c082f908040c080500840061071090051041c410070305001c0301d8901c01c0c107031140300481d0010701507046079400e481d003094034441c100c007c10010700e00140b50150b1b503030f42c800450b40c0d1009148126440203180d0901c41c141042011507201401c80314403050341c50400d41409060320038001404011010310144020b4800b500844042e591106040d03440d0200c485072003040c400e0480302e20740d1071400c026000501501030b102448110164650358903c5180b0b00405607616010440309036003140d691000003440c0381c000d0014502550541e030380c600102d460183c090026100682040c4c8404d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555218327 1250 555217077 555217123
    0x320c010e0109030b040f0503030c090306060406030f03120603080a03090b0906090c0d08070b3d060c260306040606020c0d140f0102030a06030b070e090c090402070807080c 75
    0x70303800c07104030003c803584402c00603240d030343d98900075000b44290f00008041c3d20003c41400400726028001d410030303010580440d01c883d0741d40020001038413283d11010300042500145440400c1c0328811134078a440601d034020403540d540e99242d81655026030b06810010795a0361140701048280c000035504000d5807030090070703103040031240503841c1c01043c5e200d284a4010f040202c07007040380300410b640c0700d140c0204880d2001d00d4841e0910030b44020a05070301560312901c0d40c0c15412940d002c00c0c6c54100c9c2c00ca000c4031f558110f061060a0300c05940f40b00c42507485d200707500c001c1c1803290031000074103030344007a20480d094036801c2c02ca05020540d00c0b030342c100c1415900700080f4403050b51100f00100b88042c0d042420150041004603a0b80c0c140750000b10002c1884d4000130801c410728405401400440f481400300414036a50360008454140c0c00360a4542e1201d2160040b03110340e007070700c0003034040024010f000501d07150f020380e1030314119445800112200800802c2503551003106110100f4a80d190b158619094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555219577 1250 555218327 555218329
    0x6050a0603020705060a021e120106020c09040c090c050903030a030b0906030c031f1b090302100f020d0c0c051905031e030318070b1209060603010b0616320c010e 71
    0x40a0040000c4441c540c0400d582c0342c00805600c1c100081208c8005555850300c0c03070710031840480800d000300c0015100b004402c3e0514100710031310742d1003550001e00105045042c8280f0501900361a408501042024860540780c1d40d018402440c002d0410b450009044060100740056900c0040c405407003500010a03012a42d00c000c10300c41d013901031100c103065404c00c2d0300c00403c0041c0040c0d1b02d0031000e2019210307907001064028844506607802110b6450003900b40364022151000c160409000581094012405040c000c00d40168503901c2640301800e510b8a980108046401800c1c0740004207562107010082410140481c1d081c80c21036a1103110042e000e4441641c0da484003605007211040c12414800c2ea80c0014452580034245000030b5960f2802c0c001d00060140030103680c8080b0901400d00451580e2505110b00615120054511421300500081c551440042c522054441c8444a0705c1c0b18100c50030110551280004407080e0300809030100c1c64145411030708291203040c480d81200b4100c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555220827 1250 555219577 555219583
    0x3072f030c010906210e0601030506060603100e04020a1701061d01080303040305071a0a1a0a1a0a0306090e01020406090f06090b03040302030d05040c05012a0809030307080c0106050a0603020705 85
    0x5035482c900b0400b0383e4100902c405d0391200d50f036506450009140030540c0c3c41040c070221781c0504071790042045507043e454180422a05110951320a03081c80c05400c03040084030045501d281e40507000030100d04c661a80e031500e149801407440b4100106964864051056031801868106121454200d00001c0e40c180f116156480c4001780028082c4140458501d08001c0720040750b0840c220b40d182880d00740c0c1000f00a00c1e02900903414081540355060002d01010f05001d046001161100085841c81d42c4680303040d0f076650b83c05502a60f0406031641008a448450b40c060386071025042d00005035a03a1800700000c0066099070017002840c07001030030400940d644100d07480140c0d40342d000b070540e8030789441c50140d10b540318824140766020b042c401044288074010b90000f00b1900c0a07210910041b105120f00000d414414644000300c1c407030150800d010032440300141041500180403245031203950740f100c3c0c881d5007110445e0540c0ea912000d0030301c6a401c0944907400200040e040a600784803143d50b40d036031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555222077 1250 555220827 555220829
    0x10f0306031106070203120a020106170c0307050f060c0f06010303080c030f0610030b1e1504231909020c01140411040f02040906140906011704110303072f030c0109 72
    0x80f103202d01082403800e5507402d104003408400407900e616a114441c40002e8003824491181c221020844e2801201c4481d0100f4500481d075001405080b8443c1010108212510309034005500300c0003d00120103915001c01604081c803c07024014100c1d036156160003407290300c0051020100c030b201403040c440d440500d406003641140007114025040c102d10001140206440160243e001401910064000341030004038405400300361501c188503c1205035040b958400e82c410710195556280300c09c0d500170f02104030001c84540040c40640d40d580d0052080445031783c940c103c04001c540c000348400c0c0c1440309110f2158808008071001240b8606030311942c210f00b201800c1140590340b100c9240394100c0c0954111005030003074460802690ba00c0b01c0d2000c5400220203100e13400740e500580442e48540c020304000d5100b4088503a0510b0075580d650320ba4550b0700c00110110341501c0280407080000d440d140d04082c1d1000b0b015181303003901c0342e08035401e458003100c80040b90003508800a804804c2e64010b849070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555223327 1250 555222077 555222079
    0x21507051902180f04060615021207060f0e1c020a02060405010f030618140a110304120504030203060a0c030b01090b0a0f020a02030a14070b120109050403020313030b06010f03060311 80
    0x120700481500115010000210156030701042c4082042000012021028019402103c042103100e4580500303d03041da48852034200503074420715210803000403140c002d00a0707521426010480810122900068411302c0202001a40208028020402c034005117140304850900c02426200140d03008076200c1d01c91030003800d0400854264803c1c095001c0d03080080102449401d03440800d00c3c400400d001410085414030789524514040b44060000340100004540c1030003000d881c544555441000d00b0010301e115500f0711a05000000140e076040c80302c40d00c5100c405a0204802c0040d40c00242201c0e0705003807050610007465000e00288403000161107501070f8908007119030b49003101c02039241500c002402903061050300100c0b07080002c000d803400784000c551001c440809841d054440810302030603880e01c3c00351805400401191849410640c1c0160180c016a4502040d40c030f4880c100051a800c161802c050f0340b403c3c8400c0c1d503400191451840c0c0586420403000b411541d81440c1a01319495003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555224577 1250 555223327 555223363
    0x2040e0a05090f0f061608091902010c0b0411040f05150f030a02060d02041a0a0c1104180f02011b111504080304030303060501030c05070308130c0504110702150705 72
    0x2d0b548140821203450120411002c0740d410440b411003040ea511000c44034104101c82408840d0b20013401801c6c403602880810024105500c020001c01c0510508244c060b410002c503601c120010400d84070701d681c0110702611000c2c0740346001006000c1501c2c0c9443c0404101ea2406040000c0495000416021021304440030180d03941040c002916111468101a50108001840d504002901c0d07000700304480c0b4105242c20b10250300105800c030f501640f418880480c2030500c05200142d0415030605030307040700a200080c0c0400503903030051804104d1101b00c8022410003211000d560304280180c0b000c0c01d0640d0840c80400c50355481c030052080d400710050040c64681d81d5820b2251200051301c2c0076200c21000c8944481d52401c1c001d02405007442401c0c0170071703e40600daa066a00c2a0101c440154140c1c40f0f106064607040050119850035001c241c81c10f503510754010400383d59038040c0710944006140740c50b4841000d4010460b074401e01510100d040701081046800241011554a14016060800d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555225827 1250 555224577 555224581
    0x23070f0e0411161104090f032604060c0e03060112020409020607120f0801050a063c0201060e0f13020121180506130302031b12070c170102040e0a05 65
    0x10038054440c4100801030100045020305400701c00103026035540b40141131254051200000344000c43d00302a07405445c00400c45104008240991800c00743c00122800c44201e80c00e550240c401702c140d060750101c07003036911204201c1006030701118a4800503c00c034050800741d49058280d1141d40c40c0440001d00941d242e80c090380c25075496a0640d100d0a80203518000e0b40c1030000c40003440006441400e2001c9100f030300012506051200340c0b98117880d04e45e00c44a44040101c3c5c20041c94100148402d4070b1139015000311064240600d8030503085500a0700042606030404800c1100c0e040014202c00d801011141005a000d803c1041d5500309a020f0901144030302030b8550541030b0755103c403041c50354541007042c03221540c6c607100594071400e40108152402501c4403d0703403011002c0805000b07001a80280514104110b429014001d0840e0380741c00c881e070000311000d5906c0150884070082d6800d00c6040c8007002115044484808a50310007002180b07481d003809140025000060042c1030065546c41c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555227077 1250 555225827 555225829
    0x21f08160e0325140f040203040f050a0b010609090506060708070807080412060506120d0311040801141b13180609020c0c030c06040e0f040614090123070f0e 69
    0x400441108081c040c2d0700908001c010b503401400e941e002d6800c40b0f4800c81000182840c0b59a0412107603207004184883c06041c0b2000c21021f908041d01c1503c8024541b044d81e0b000880402071454604d100e541040e44d20740c5400005000c60360564011609241400304106507641c2d03003800c07611050350110519441d0089400d15a07030300e0103171102c020204040043d002c60000b11081515810f940f2079a03080c02640c0e00c41c0c050080c0e051085a07520960f9001109815100740260024610301c0403c40916042542e100141402c0d03450036850440050900d0040c0403011540941c542e410381c4007045003a1074072207180b01843c0c09071058820040c403201e10822081113400315030800801405804000d540361546194215107940c50348110074131a00c9880344203c40c60031f25401340c0c3c0840d090110011800d40d0f54410b140c01c0c009004004413281030b0b5540300030340b5100032100b43c64040e0b44c24500024911604d01c070040640002100364641d05002d00f000c000d80d5582c0010f1a210021a0307160260440034010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555228327 1250 555227077 555227087
    0x20f031c0e0a0e1f0e0408130b0906120a1e020c0c100804060c03061a0c060708090312150d142a010e0112051f090c080c070c030501050106050304021f0816 68
    0x140000c40c5c580d110805001c140051940540200b0711001e200002840c1c0e6800440a2440307040c0c6455001380d800d0000001c80100a081103602c984040000311380c460650319010048818101c0c240c14180e40400d03000e80100007000380c4160b40034181c074584136605642c00041c056290040c8010803058407102c542c401248079030003040c0201869019104072041c01700f080350b0b280d0808159500c3e244509800644558482c029040c003601021002d146401980100c0f92821301008081c12071282c0380c15081140c1e5200c25004070300d02405003280c1e60b801e80d04543c8003828075101d5110030b1416484030003195414140c804440421840134240034000360821030060310b000800c190300c08002490b020420842c43d00008189030083d0000f2003502442e9100e86440c4110703130712440030100103000301000600003a0010000c1203c40c0c01540300000095076951414203594090300b020b00002c0010090004609141c5080c081c6a11800d468103214108150f00a09007030f8000c0681d500e00702d0405074105c00900035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555229577 1250 555228327 555228329
    0x503010212160c050d1106060d0c05060d0209090c0a0807030b1c150603050706031d0a0b0717040309170a1a0703021b01050718150c020f031c0e0a0e1f 66
    0x4152a0380e1726210300c0280c585c1000040e8100036004050004260b40751400141038115070200407030b00c1403820f25042c80b0081d00220038042103075500700305c80070386561041e211034400c0c1020360603da520990041c004200c0d02000d0b1a040502d0706000000c4c00954424030080208030708000440d4040c0b1150428620320081110140c0569250440100500c40c01041c5641520303240d071424002d0000303c40d102e501c0720380d40400d2404141c000302114000250110710305500701c0018034020705449940130581030144000c0da022408155840c0c03080101160348502460850140e00140c00b1561070754440045144125891a250000410003ea5503030f000358140c400810828101e5258040307544c096500910094401e2404580c3c0c84145211842110300d00310103860b01034401940d000300785074081c1c2d51000707500c3c412a0b0028010203505103d0700c4c20410040c20100301d4002e1044425500805030030300c0800c4031420301850086400f4400584003400c0d440e00840c1207c400501c003640494589240303806 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555230827 1250 555229577 555229583
    0xb01090b01051b0a060c02030406080a110408030c0604030e010e1f02190b0f01090504150b060702062d0901200106051002030a03051e01050409020411031f0503010212160c 75
    0xf00f8400c00c40070303090001d0881000c5125040070046403040d114141e03581e004034030820001440b0b6000081c0700ca03001d50403405a00a01111840c201a12003c4090450b045001c2c6508503a110104100500da40410221590642070034465140204000840c421420100024883c00041c001040b0b0300c6200700300c11074224001d400b00c1e81983c5ca540c604100d500e441901c000d404400e0410000c51004028441c081c0070f9507000081d010002d04480d02c1c14058100380c1c6c2403c0c2d01040034440315000da01e9500007009514180f12000101110100d030f650b50004d0200300104101105114040b911790f04074241008510840743c0aa45009000e81b4031809081c8a030440c03600444920b1400220b107800002405101c8601c0c2c030140100da440d4030307a10912140c615018103054000310010005030500b907010303081190000d480800c18003010442011603a005581030300f021501c0300c0305c04001417249002c00740541800c400940c80e1450361108490416000740c2004102948120066405401209107051540d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555232077 1250 555230827 555230857
    0x405041a120d02060c0c070e040c1e06021006030228030c0b03071d01080403050901050723010c050f1e0c010e0c090f092d010603061505030303040b01090b0105 70
    0x1001c081c1d9100c0d801460810054452180400e1941c102e100c20f84080101540041c5031051824044950741c450150042c2c074180842500402c0390038406c0e42c00440c3d1000c50402000d03007480e020001b481d21120149600c2060314000060005a0715110382240443d025100122035845080000d40a003265070700082131903201c2c610001d000754105003e9441a411515080d04a25000d01d103d15807401c00d090490000c3c1c000b1000800090040e0003a0034200018980380d0b003031416030390f01c2a41010450389018814506806e0144841400b4011801c00c82180c6c54200e04001210483c00e0f030314000c0801d44417041d0310706c021490440e0340e000c0036207080404000003440300c0342d40d5680c1c075a01d0741c5031a1005400381c03240b900024a034659800400d4041c10b00744000740610025040000c41d0650100a4462903c80507400c00e0300004090103514041d501070140000c40490184030403541d40c01d5540014000d030410310130030000c60f001c3d48280d41152031840380821030b0b41c45500102d035140f04501840d51560 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555233327 1250 555232077 555232099
    0x1020d06081617030708070317092128030207020d03030b04050f010b0d050a063b0f01060f02100617070e0c091207170307030906050f0405041a 63
    0x38400079103601120001c02001203820b49540d079402d11080f840e91041103651042155400042d02c1400408145000b07203050700e0890055544001d4210040d01c040625034070910411124002e001481080383c10681c0742c40b442c1813a40758030b00c02140102c5403240680e821850703045d0901402501107400d401d42c02080c2100b5041e0342e146c003a00074000300c04558045d44c6403000141030703545015031090589122101542c141103941b034800000d404010600c10286803200400924443d241c1002d8011004482140903680d804840c1e01d0000289280160184940c0c0d0b001e0000c4040e2000469064940700d00d07040f07064103010032069140800c19026910401c1c0740c0400001c142c0150525a4a540306103000e440055540f2507144040e400140d544071081682046550210301c0d10341c4501b00310815a5054442d06683c0ea1104010030262502c40001d0360400101e04040561201d40718000d0000d81c2030450420400f100c000c40c00d4011030040c507005556800002c038031074125082140c442e40c401029501e0034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555234577 1250 555233327 555233339
    0x3020f12030712020c2b11090a0b011101050105100c05030f0a0815040504170919080c100c0305072004050712060605040b0d0507140a02070509130c090b010201020d06 73
    0x6420410f00070014000c540740d50f009460003110392244403281600a03044101400314103560380000d0801192090030303818440c941a15a1800c4501c14000d6010019603140c0c0780002424524200001400591416005009560b68076244c002c0420780c2d89044460b00c81d50b4078100345140300385051840b442c98003103a00c0d540186c1c423101d03041c404c41303901040c1e1109500309028441079031025140100664010850402c01c80b650901038151044002e110601044a0f40d41038204008560050342c4e55030015548000a401c003c80c4460490005190088500f413950314000c21501075010002c1c404040101c3d0140b4101d00084400a843c200a204000d5401e0154002c1d201e026086041c0e0122414010f0016440d03020320b0507070341102c051800b003903d40034140710100e00030400204401305000c04010300c103d141c40400083c00101c2035a03002090840d040404014184030000c107041111051510800001011030110404070703001600d0100d164000303400140d02900800b40d00da004030303181250000d02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555235827 1250 555234577 555234593
    0x4140304030b160c050c1c06110d1104030f0305031509100302011e0c080a090f06030203090c040605010c1202191b0506030c19120504051e030306030703020f120307 72
    0x3d211031a0030b9411a01075298155111890742c8030143c102e030004240350205081555282040030103401082c40100161307680c0d5022200103111020380368001160700c5032071000612a100d0f0400207501e03114240742c6181d885200010740420000c04100300400402e00918894000d04101d8400809083d0240f601201c00d004032000c0d032000764005510f14892101e2200b03862081c0032080e503030b1780d03c005003000c0f40c0c0c645283c5640140300320310400c07020f500002060030301c145605014003c44e0364003503503c3c00c00c00ca1003032a21110345d400a100700d182002c100050f80e000304102c000b059201082d500d4821011b04182c0c20108010007154544154008180422801d180440400001c10800881d81900c8005001c1180801c0341c41c1c0b50010700070040c0d05400414000140106002c43ca050328140d000d6004030340030743c2c3e029101120140d101120488040c11803000c1c400c4d00c001c4003c001c1d4214501440084e0352040c1501c03001c0d00400741164860099191807002c1c000c8100da8904a070b5503a0020700d050b0304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555237077 1250 555235827 555235831
    0x1b0308030a0e01111602060318120c0f060c040303030e01110d090203190222020903101b0f09090b120a2109120605060301091a19020418020304140304030b 68
    0xc0b6946480707664000d080d402d0003502c20607951801d041000b0507455080c031640707500140941881c00e0071000c41e03080c01501000341f160304000701a10242c0714030100304041c1c07600c3c01401103000b0b0b61b00040100901c003a039142c182c1d400c5075010324010031050b81010301540105041c0c40b40c100e00000014400c51010301d242c2111800034825011512215010442c4403050140c507070009521111424140c400d52000341001d18074022a2000103103441d0031100040d10b0301c0200c98606d500c1d103403100320309030250303040c0034000d081c020843c00d05803819030f0b031a90300030400300d094020081100e640300443c62907900d03130b504850360f25080036040380c00540040c1010381758811201e84600700f600d64540402d11341c510401070341007140c101c010f0003080e00c0d5181d5958006000020003880d019035039040b844c0c1c041030442000c08950110224214203e0909002e2040c001c0c1021203603038000c600401040080740c02101500c40711110071400181c82c0c0c1c860307103400b42c04a440683c800303a0b0381c0300c0030402005000c0580c0d4664 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555238327 1250 555237077 555237101
    0xf04021e03100e04020a1e08010c020a0c1e180212010b071118061e03030a1701081f05070c0f061401050f0913021306060206161b1b0308030a 62
    0x18040d1a59281070402c503c00440c4e0007504185607090400c440c13a0803080b254403545a02031034018680d11000160f08407400400c0c4000145c1c4800c105909100c203401400300134240302000e034001c110882003010203958085c0f048020b40e940032660200703658840c6d0705a079190340203e20341c500d89581d45d11150308a1b400100054401e0b240d076110ba40954600840380d025003c281414018a81e42c84a0410610f01291950380444c520800c4c896a0f00e940c0900091401c40b40303d8030340001c1c400d94001c81003071120058101807110390182203c0f403607905030504600e525203000c8501041c260b031072980450b48066240002060f10002d80f90510130800107401020b0400781640400c10345030313614400c221081c580c0c209a1a04000e518000c2031665451000c0c0303c08580c005404105581c950003140004c484d03136507202400603000a818400540c2e400400e00481c070105141c42c010f01c0c0801042c103227206002d601300800c0f41c0a031034502c0842032407802f1194021900001c056480e454607254803405081021074032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555239577 1250 555238327 555238351
    0xf0a03020c070b0412080c0109120c060615090902030408090a1d0903040513091a0c040503190b0721021b060f220302010f051f12030e0f04021e03 64
    0x3c258240700c141510300300c0d42102e5220744a103180e07444840f000d5001003c205e40d55500d503064503004c2903003e0980d00956242e80d480000c41c1c0000e0034020116001d035009400d48421005c0706e80400ba9000b64000165528401e00598a0700c540c500100303244164880c4640040d1003410002d071030080391b043c11003140c482520901075030f82d6103020691031344154007440c1e43c8011842d1194000100035840a8030142c4100d00018040d031205c0740c2004040c0b01140e130740c00000c000040c00c4c00103040c144842d0a4160804484d800d461b0001d40e036802a06400400e014204442c4445000803203d80200ba122525910301046544a840081c29441c0061550000400388104408034505a4110b078229114540040e041c00d5160f80051441000684c1640140d08540d00c2c3c10350803118840c42e205040c0504006d100c00d4403114400e042c0c039140c584460340700d95054100014080701081c3c204494001d206d500b100ca41450b140300c080068000e008640c2c110401100c05000c0c03080e040500301c01103000d00c00500380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555240827 1250 555239577 555239579
    0x106020304060906260a0b0f03060402060d020a27030b150307030b0c040b040909060c0206100e06010c0f0c062003070209040201030e0a0b04061109012001020f0a03020c07 75
    0x41640d99206a2144000241d01a4402c100b000c0c400e035205016842000707203400d10524140c1d25020a000150341c501c401d180c0d10001c1000914140c0780110703224400340c02620052403e0b40003e071950103407465500b0140c1e00022581d0005200d20380a0880e0352109800c0c0025003554424901d1401e51170004881c0d0610460200c0d900400d0b021401600c240003d000740300301411907072010443c440c05080c0802d8544103001c04507440c0d81c0071010344040d0411030400603941c52641000f8094441d8240180c0564116a06010100040c508908103440101040381c02035141d10300104c406203040c0d10003500110140e01003804101c040b14900f0111036190781e41c81641c0b5074200b4545418101c111102600c0d038010081d10bc0181003140701d86501a005040000b1802520302020f81016060742c81283e0b008104000c001c00c221152051000071a407100c0300d2402c2100c2800007078008540d45240503059245180e80094461094044414110049042c6501d4001c2010f000c1c000c1e42000f01000150702500304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555242077 1250 555240827 555240839
    0x1320c0a1a04080a030906200c01060b120411010c0b15090c0a09030b0c0405030a0b07120203010e070c06091e0c0e04170a0c08340503031605040503070608090601 71
    0x21650140390401c0da294a03004110700f05500401c1e81e08000c40e02d040c8c0346c2210700203a08a2003000c900281014038030b50756400300c54141c0c81c01c60380c1c41c0d04508403004040c0300e182d1080d80c03c800f8a40d4415402440540070031507650050318500d4210000074880750001c000c024400150381c1c040a44e917070007500c1c0c030507aa07110404151020700483c911030300050940c0504102040350782d0031030754001800001e00d91601e44c171200403908014030100103503078071002c1105201409501c400041c845000301c80c1d0071130540d4106000300c00420b002520080400040521841c148049517000b0707101c45900c410211101c000b90500384a11a07007003a002d0358a040103c0b0009031800c2030703002c0e092185500060304500d000750f00b2030000480c0c01076030f92101013000a510100c0021400d50041c80104031300600c4206201c18200841a84a840d403882e030807105810510800084002003034a0b08855500e83c000a100c0307004800301c465008541c080e036454440c111000804c250003203140c41c001c00128064807002e1780c03100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555243327 1250 555242077 555242123
    0xc090c0206040213270b1909020f061c0e06010f0617010e04031b112b1113060906031b03120e01030204080d021b03010b01320c0a 57
    0x2d6000e5045040380070a4540000b00350700800c2c00000d080b00e85007550554050b0307000f654064200c04c0b40c001103200280b00c0c181c584a102c1c00303080324060900344651411075000c81e03002c1c00108140e5004174030104e0541c0090030b003907065040492008004028801e0b034801410758400083c07213100141888030700d000c1515445001000d9038440050700c054001d9103000001c581c00c090080c416410000c011842e101507408682038000d00900800200c500365510100700324646484041c5440c2403111084444001d41c151100c2402246e0000b4012000e401c1c500b01103000990107100d80c1040301e03e170103000300324816640d00820940740103a45091030f522044c040707051490071501002d0010240310024007103a80c4200b200030300502c018075015041990300c901c228900a058219a0091307040300e0480c107100172402001d01000302d8101c1c005d000300940d08001808a480080e181d00074640021110540202800b0410381c40c88441803500d81e5584008001e0f946821190304202d0f4042061420080001c03a03030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555244577 1250 555243327 555243331
    0xb150a0503421c080c150a020d0b0d051506010e060703030911090f160309060515090703021c05100e010f1d041109040609321603080d0e06040c090c0206 67
    0x38240243c011100350315198400e40000440c0707070f0544a040e10981100841440c064060034009201584460002e56840261100c0007401c900440c00040c0301030104d0f80020326070714070140d208006000758a50b0001200c0102e039500241c4d40204001034030908042d8154010041a40141d00c403140f1107403060300300503100030142c4803100244a0781c0003003160407003070a50f1125001c5a0b41400680c10103542c2d100d000765142166403004603102c901400e101c07400e00520065000a90380740451505005100c0300d07401d420149000000660b81d2000500e00b084841c007110b000e070148540c0800c4560303445292156404103800350403e00e00c0410103616044ca0b1030654103009035808100e400e80120080300388000c0c40d82c001d200383c5519032a00c0802001c203a402c540c080120290500c400803862080d003001103400030b140c043c00e03101d078042c004d9001001c03840c0040000307480c0d00003642a914514a5080c002600c5000070f0306c00d003405101d0038007040005204035082103402c848410302c184a45c1050aa84440007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555245827 1250 555244577 555244609
    0x60d0201021c03020d0906020405180405030301060320030f0610090f0612200a03140615030408040f1413200f0d0203040b0603010b150a050342 63
    0x249038050890038114215510b10710791443d006003480f8618100c0401d6903401e40055518aa00040c11f202d98280302e0304410941c0a04c0303500000600342941c0300e40d42c0e440144036400406598440c0b10319445d02081c6204503004107483d2094a908265488420300074082d14914030460104803440c4446000e80e0b66081140e42020718450214501030082d210f03032080c20b00040b80c0941e40c00c512406404408280c1509000700641c8c03589131004c4201c00340031150060118100c0c4601002008034998a1104001c4c483ca0780302a600d45a4460340b40140480c011a00018040800c104010034944460100000c0d44801102e07248001c54015030301000316448606000110b64090440341d5820402000070100074094030034940c40c006090191008a801c242e504a5903030803450b090090310314090203203105078881103c0e00d43d11181d02143d084400c0c800d040203030003403101c08800075a4a0400240704101c0c0014190707054a00031240f044115010303400308910000c00d02c0a000c440150504800c800c00c581c038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555247077 1250 555245827 555245833
    0x501120302030f092206030b0c0c0a060b04090c030f051524010e0604120c0801140106030b03150f0a0c03050601050d0f09080a09030b0a0c08040b130b070215060d020102 74
    0x4524481c850394060790704c0b1600080244c1e088035004c0301342043ea00e800b803440030001030041d055260040c1d80c1d460150078100c1c0100c0501100035519000f068a1440c0e0f2741c041000500d4110700404a400342000750b1001d03181c08400c29001050210354120300703020324030074801d03600398101d048080e40d5540000c0c1c031078842503007801c101d01c056145035403a01c8002c0755050402c903143d6038a5000189256200342c00c03c9000c400700700228020417021140e200040c03d0b00000900c668072819501204003c4148607800c10107860b64125001520248004490035041c0c403000e426034942420400b00056085d5043d100061600c21903209640c400d204442c000c180594030907107051103100000002d04028200c1001c640d50b500713000c5e40000d4082006140403c03007030701d03a030045030b1031810109507510004000640c004d0900c0125030321150300c014051341c03040c0c0c0003103840219104c040040c0d035490982c686c0142514020024031070380a400080710381c0704188002c1c014203260341d940140603110f82001002800f5074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555248327 1250 555247077 555247087
    0x305160c030305040c08030d02090a291606050c0c19020f0d050f03030702071502010504050a2301110c010b01110613080c1f0501060f1d010909021b01050112030203 72
    0x24841d0300555001345c0104c0d14040b00300d848403000c508540c0181801d580d070540c0010700c19414200740800314020061241501800641413a1900d00c00381c1c0c0c1c1405515003000011103400c85180c3c0e4454400180d00040300b04070780d18110403404c1440e44080d01e108168400c00c14665624000c01c806640f00c40c0c0e014181881c000321b02e2080c05503003190030000711603901412902c0307400c0440802c091403080c02964000c11032103180040d031100c02115800007404590405080202051000400314611903111400b5070750000c488a92651402003c40a40341650800007100c08640999001d050a00311a1008001e180c0740c69006440f0500041030004840e0020000104900104007840c049280a0380c244c03843e008442c43c116080c002e03480400052242007151180c620307030461003a54050409802c0c000702012000b60090558848110607922408400f0143c0300d859100c2d803590801020310803005d5403200e4807401850180405132061081c55031812000040071a451317650312020340d0301360300518584 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555249577 1250 555248327 555248333
    0xd020d051332031303030e090c03070c0c05040f0906050a0b030a0b0406180311120a0804020d0507151110020304080f2104050a060c030b03030a121404050703030305160c 74
    0x491a04100302e8110891401c600358180701030000f403056001c1e003018030480c03c5c1545400f03842c54210703400d81c60140e990f6204021075401442c0c1101d40040740d904080d506041145480540e6015540190b81c01ca401d200603c06045540e4108200c102d1140c2e4007800b6650b102c260702c4048071041c0240d1685680042d0703012000c52050000d4541050042d40c0104400d842c00404071441c5080c040200c00140032034140140340401406601c1c00701d11000807071441c02071514002459518040d0002c0d00c14041d1000d02e00c1000b90400c030301402001d941008042140d1149409001044001c3c86041d03180104040756003046068802c50340314660042500742809001005035031980c01c03100a2001a0f54611806400100d40300d07031040c407a510410061215a01c2c500e8040142c4006c0707070b040410f05040072440d103a070b07580c08000d5a454466501d802910aa41110500043e1000583e441e0909001106020912030042542c0c002d0700d000e5242840661641d55548901200c0302c451600041c0c1c8220300b003000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555250827 1250 555249577 555249623
    0x5040603050c0408010603080a02010c090302010c0201050c0718020705010b1f140d060e0a1503120f090b07030906091a1204080702040507120b0319060b150d020d0513 73
    0x41040ca050301e50078103890384c4103203086404a4000340d0385960007203440c212070755090090421589030361a11900d5145941e0018000207102d40c4000d0501c0000b291003c480070041203024001c103850241030314440d008078400c000079030080c00d068a00d5409c01c203039243d0508007051200d0070712501c541d00c140c0b240c1a22200710341c0b18008001601e51080c00700b00c043c0e08010503000d1007010b08911400c0c09000d0800400d0075044031059031740400300410310842007003c903407441e514401c00052400c100718050070904046400040a40010031102004501ca03c18103078011a200b041c0c4503940c66890107a40c80c0c0040244a80302e00001e541d00b85010498131840d1940d80c0340780d5400034410a14141400042c0d40080d068940c211848400100d0078402c6a180ea0218010f50b2101c00080d40a4400010ba40a41c0901c1d6204180d018002d1515403a2040c0300d5207075116001d130f03154210865280c89080311410306019500c907039000f001c90750618005c80c0402001400a0428070740c800c0b910b4903101d01c04090180e0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555252077 1250 555250827 555250831
    0xe030d080115180b0705070f0e090d0509010201020c010e06060a0f0f050409020a090221060604180b030f0d09090b04060b12041b140307080102090607060b19090c09090b010504060305 80
    0x3c0005202d49002804d2205203003e0300a0601c5440500102414154025201400307a4030850b01c060a40c02444141800461407d2512445251041c1d0311100d820050703029104201d9050000d42c40c003642011000d6002c290a405544121000101d8695408103c810104103001d41c1c2c8540d075101e581001189041d911610f140b5201510200f40d05684284120490f0400f00414111a02260191a05070a8205038903070002040740c842e403c0c6401c2040c183e5440b107001d000540c0d800e03510040a41250b600300b240c0024040c0b10801c40e006e10400b540c006044031614480c020045c0d0030030707480c0078092030180200c005071400396419030b08040f0b01c24507407850323114003410590f9003c0182c40c040d280c0040501e200400b8080d05000c2034030300c01c1d00d9824146407140c55801020281d00c10f102218a99803208121102660481c00c04510b646c0440c00149242001c2c01a5000f50304020710f0001d800102e0b40c002c0d2080b0400c58442000c0a65104903981c00d031044045118000740d0704101c180b24650003940115 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555253327 1250 555252077 555252107
    0x306010b0c07030602030702030c07050109231c080c060108070605030601080a0605031204140901030305070b09030d0219021509031b070504020708070c120203030301090203061f0e030d080115 84
    0x190100d0f541e51a00720032a0b0080d0703442c03001030b000050b07412440b1104020f5800105405c0c0b030448036051412107000d50b00d40307841e94002e64011800002d6502d585c0c0b8180042c200005540340d040c141c0791603181400681c1e0010212041c00d00546000084490001c00c50000300e1380c164984501e15900c0e44011110414000c00d900020350b514180411662000c10101d81803900b00f0307080e5540da03410510a20819543e0f41c00c564820b904130700c01403001a5000c7d06a80305c04d940070b103106d8810b446241c24503046004412081c16010310109240b011080401844c0000709082d400b03403003d002c42502e0300c6824400c1120140c0c500d41c0100107446030100c0c403004800301c90756036000342e90304151144005400d0307a1013900180d40e003901c045100c6084c4000882d44400900c1f00000f80398140301240e01007610b9000500c1403101e03c0358044002078443d26000500c5c00b101030000180300d10050300140c05480c075000c09014900030302c52141e102003003034082c810780d0341601c02d25014414024984401110780341da10341129 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555254577 1250 555253327 555253333
    0x60703020c01023108160605250f14010218060a0207050904121403070c0f06090b191a09040f080f1908060a033207090f0b0f0306010b0c 60
    0x48a4140540082000c04c481c12100100448040752200281489a030041c12850300a451104015400403488408135201410150380395030f110b04c510a1184941c0c2310110104c010780406c40d00b0000044080d074100e62050021b49028500b0b00b0300c7e40c0c01c1303000701d09110320501ca400d0100030b0980b0f0039502174115035031380344129100140c0780c82c0800d4580d0700c260380440342d041f114110310f44002e0304481c0c2015020404d040d494210b2415050050aa180301000035090b01650303a040c105200c025001803030000e42040c1440100c1c100340800c2c881c256540341c0c42221042c07a089a600340e6895040280c1208003008007120880d44550b241d0030740b401c01c3c411741164025400c100c0c82c620080c1c1c29002d40b20440404444100c04101280702404440e0010411403080300c20041c2400000c009440040300b445202070007541f42c101003484840c8a492a1150030524880c8020004e1a13a42076008a80003105000c2c0074080002c0300740c14455035034040804503625400802c014000701c080c04001c0d1840003d03c0e012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555255827 1250 555254577 555254587
    0x1203060b16150903020c131b020a020a060e1c03020c1011013b0c1906030b010504030221070b041e090204050303071502120406141f06030903050403060c0302120108010608060703020c0102 82
    0x3623021580c3c2c5000741c0c2004803210150b2410341e001400504084c20042d40030040752002402a01266092210105100c04100c080c940b003009159085400541a500c44900d160f10241071131140034081c481640c288918004421203d611120314500c1e01c1c0d4030100304001042d07104444d8010100c0310280e501c0b46000c6444160f488131102158240103540c820b5103141420f03001015903007111542414001c0400c02003006031103000602c2403144403046900e080745002014030f410301c5140c0e03001c40c0044001007004940d000040d00d000140c1c0d100000722242103039503240c0e030b40d09074080d41c45515455081405010041032080c1d1031803080c0014064018600071012003207400c070010070f880a0300ca16540c0c1c200d200240301d0144841d608003850440399080e00da004000c07221207001900500c020551211140020103001d1419200515840383c000d120310311600c00000d0081d0403a01c194048810b42200001e4a0a41841000d0a03a001080905015503928800b82e000e90b1110704031107155942040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555257077 1250 555255827 555255851
    0x1609051e130f0c0603022d1c14010b13060201061214150f041101032a02100524063a02030907061413031203060b16150903020c13 57
    0x840c50303000c0c00c4e10740c50050700c0f007003c0b80d403045840050707580819144040030401c4400b4050710056481c0b854201e00302e11001d000c000d50704005043e584017000744017541d4500104903107041202034000b410b203615108420310356510089080c0c0e803580c403802001e8665403009002240c4418280c0c0045089074040701d070000700c03905503841044011141c02510002c4041880704204032001031050341c0d00c00b4a030034030084a40c0500c030101711041440b298650204103020165241c000c0c03004840044408100b084545032807651840341c108990000f03c8244071004a19049140070010ba03000500d201c2c4203906030100c983d640f03840048038409141d010410713055030603c0b6491503000441c1b00d05c50150140181c1803070010050442c4d10362108a03c0200320501c00420b071450011010012a6041500d07524540500c4000b90000c003a1034120894490000075003951907101703a014040003a00c51240c0d0135203000c074942e0000844601450040043c1c03c0105229080c0c9055102088082512040000e502c65021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555258327 1250 555257077 555257093
    0x41e0c0e03100903020c04020a051c0b18010e0606030c040303080c19030b040c030e030a141909061e090e0702010b030d02010603020a0519051e031609051e130f 70
    0x14012201c2e07540c035660b030b0408259050110504d454800e84080d401c114a000c0054924002c015461805140c4c008140081e8000e0350028608017401421071030440810300d1a110154009000c0d5601240b00345011412608041017164131621000340c1e0f03541403504540d0111801c21014003100310006080c05420420310541e5418060340100f61000216409060140420354807071195450038103142a90608101c4408011121881d80626008610b200380c561170784190b00071103266038031200142080a013200e8201c0200300a0704d095840746c0b403000fa0320810110001071128461000150000e00030017918140c0030800760040124000810030080c114080713868420b1a00440d00181e445203003c00640c10061070ba0b1015001c281d4044410920302d0f400c1c41080459841020f02640d000c401038503119200000708240ca500090a031800c05400b0581d4220312552801440007040c80e00000c91900c4945204048511510081c0500550340d00e000c10f1030614824002941c0207908100d03c5400a4424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555259577 1250 555258327 555258343
    0x4050c03100e1006081c09030609060914060610111011041703090303090f0114040e06120a0308010302060f0d0f050106020d020a0305070209061c060504030806041e0c0e03 75
    0x101c0c0020140340c20a00c461501c03418001d03201c0c0080c90400280610000400c00c55080c09a1260b69840c0c11012441111150040d520190001d4a0245910200304e8560488030050740201302200c00200500d00141d2520400e4800f02da001c60600115801140200182c00d009142d84042d00c050461941400301680c1c4082240035051400040038002c0b45403031540c1000c512070580045081000c0700e07000c00d5480c410740300c1032807090554904c0c26540e40e1145940e2211104501074154559941d00c52525507580d007940c0c5a881512610820000c4d9200040d41300603060301540c0c0d110480c1d1964083c40b10302c1d80306c43c42008246404100725014038407280036444c402c0030000b03c001040c0d803600c1c40090030300b0f18107294101103410204074000401e03480400e5641caa9012240c64255031210400600344e00e8100250103400d4180f000c1e8402841899401144903600a8491000b0b694810082008460f940214040740e00c400b0340d8400310409040d4402100c01c981820203410b1410342100081c40c00c0c0325 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555260827 1250 555259577 555259603
    0xc03050108210409021b070e0402010f0804080306010309080904062303070e0109020a0201091502090a05030d09090b0a05030f030301080d08102106050106091a0f1204050c03 76
    0x645004100203041048007841007000031100b4101001d103030307019a81a109601c903031040039402203500460200800b2030294951068400c40d82c1c80d1350f85810086c40b034401164140c2c0800c03c03e68403000c20a0007014214030a60303010a60a143d5030b0f803200150010600d44805843c0c02c04180000d5142c0d0712140b20b500040c00c9031403a0303000c50180300c21641c040350102119450280d08444002c0081310402c4c0c0c5043d0540c3d5951201603103c4030010400c0f0300521900c00058074080f01d601c41a0241c20300c603401041041429207022441c540c8600605035107514400341000001c6504d02c0400110f0b01c15840130043d1480103001800ca159610006450701c4c402c003420302ca00743c000200400541c078040007500f02c0d251482c00d1280780c900e040d040004503601644114520300014080341c024484054035000c5280f54001d20410203946c40d0040100040c6c410f018545003182240a044010030360202035403088a822702d182484d110700b0810024524001400403669071084594509407079030180030342c0c04c1303400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555262077 1250 555260827 555260831
    0x30509011e140c070203060103030c080903010c050a0e01020c0102071503021303050c090a0e0a140a200f0307080703170c010e03070209011403120c030f070606030605092404020d060c03 81
    0x10b6507070b402403810b01014090980742c1200300500801030320040740a50450f501070400d0902003005080c040205d00c201504581d16528089403c4646500800948810f640507940c030107420410f00010b82e42e07201114591800f42e4000c803010420000710103400c0101126174030300542003242e801008181c2ca04950000c490b0383d080b54201780a1410050140390b031220802da0280501143d260610307031101a41e4501801c200520402d07422042d100704500c0d0201c580c01b42108146400f40e40d020b040b80428a00d00b01c0c400e13006500c0b4102a0710300000c0020581c2c580b81c0180259a00d503a1354002d180e860700b003040c1e41d651824081089500001c2c410141700961100107140d0f5900c440c810017402c12300581021540035800e0400360340b99200000c2c5884020185503040340e86e160b004542d00c2c55030044551030340c54490000794140401030203070004812284034120500c4a80c6810303168603202c014900d4880c46004510303424080c002c15042e18250468005441c0c401c1d171400580f01c04003903410410955000c20317 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555263327 1250 555262077 555262091
    0x60c030207051c18031e030c050a060b0a0801060303120903031103010303080712020304032c031608160b16022d19050f190f1706010b0301030f03030509011e 69
    0x9130081c4101c903214428680e08003e480c150f07564040035140b1110b000241860242011040500483c131420140d0342050407200344803010300d45400500142110140151010100000e8007101405190162540b40d2205058908443c00325802013402c540260201900c1c1c0c40e0035489144114000c5001e5070095980b00100d1030f0100d005413040344401010700d038580c810410400801d9001e100740c50001818080e02000301403086803444400103c0d032110b945030244036941d6808a680c2c104c642c048603020810303176241d80b03902c40c04c1100b103590318800c4540311f0204004940c2900010048182454401805440380b0144001030075401e2114030309032069000002613413520740c501034404c203c14500e109040f10025033000007052140313041059550181010b1002c840012468240010241401003030f5090320030f645074401881f00f100d542c2c440361030340034640011510425610440b41038a42080002c643c100031075400310010817009040808a541e00d0003082e0755040101481e660080c0003141c049205 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555264577 1250 555263327 555263383
    0x1081506101403060a0f080f060610080408130905070903030e03060108030405040902031905032a03040302150c0106140a080105060906060702061c2903060103060c03020705 76
    0x84402620062166010207000c0001d1a4800385041e0b114003039400094036030321020045403503d01c4c650030101c2c0c03507640b5200200d040c1000107811903001c0031001c01c5405940307402c401d00ca0044280f40110700010010303000500401c003004028208550282e440100c840c0e681c1e01e0280031513005482610000c4e0f0b41c1c1d0410421b0542c040041c00c0050000c6000e004d46516000031075a41e4821032141e980a6610380301c8260941d03900b030203180e048025144d0322034851042864119240e6101c04008001e04003d0b108600c070044800064007001c03503610004500d02401c5400300580032403d0b84081650410820040074641c10a000300340042804003248100c48000208200100382941c01000040e0b150008011003a981c503081c007500903509844182c1e440a503030000c42c00502c1400300c0544c4a405030300304070b01c907440503078000c80700300e901554069178481c41c0042a80d00383c1156550240d042d40804014008103415920540c46855070b8140145848a540d42e003a04040f0213103040e04050f14604100926 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555265827 1250 555264577 555264613
    0x1b0c080a030e1f0f02101b08010b0309071a1b0a02010201051806160311031302090a050f0609060a0f0308030415020a090303050706020f030a091709010c110310050108 73
    0xe0382812500e5890710400030801210040c403a184800c200004d815106058600900001252008900c804d002015460064074080c40c241c8981b071000070041c0000003502c00c4441c0903640140e021b4805017030b00720316000c88903001c4c1c0341c0d801c103240086508111410000a5a00ca0041c031189402c0140490b1500340c0006401c5920082a100185e490100503416600002c2041944990b80d8200503540100d0500110000d00d4009440d040c0c1c030000205000e92180e0050070300c01c40b1842264242c1007a560030f480d0500780d940c1070f03503050181c0c062070021540760314221000640c051005041c00d0740d810759501292000c0c4180d9401030b600010700100f0320003400010f5003034258600c0400300a62815511000040941c03415110103010050089009020408690112064003c10b4000151070341481010280100481c02d4100c452241820600d15526101400d54980030016100c400344c2460170340766110190880d400040d03040c0640401c0a03007a0742280b1505028000c03010080004c08880000d41503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555267077 1250 555265827 555265847
    0xa0b0706051b0c0a0326010b0c0706020d1d190b07140c03070e0a020903030d0606030b0406030206030a0c0c050d181a1e0c0f010c090504090c05011b0c080a03 69
    0xe050641000f00b4240200e0005540f00f485038145002080c481e0f19580c51052003940c00c01403003841c000880000392142600014004102c042e0301507461441e0340341d100340d0340c4400b00f49032100854401c0003031501048640058000b0100044d0110080510030720004041034a25005064900c1300441c1500034001c0780b550440c001d41100c0000c0148084078400079640703030300034820b0400030000903002500751030064040c0c54500c0c1d805811072b51906100001c030310140040b0b024a074006442c02000e44094903041c001d540032280c01600b4645141c03a50500390000c0c00341141c01a05100c6e0a0f03110303400284003004003010521999a4000303900c2a100101071440c149a4000094100f80040f5000e9200082c8221235a910b03030080401105107100440d00f0380c40c01446100a1030340680205402c0c800b02c103401100407080180c1c0c8544c500d50f1508100011501032240c0600380012842c8140f0040d4061071440c120010b50120480c100204c0380c2e81d88910040b542c02148154004145420405400c024290 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555268327 1250 555267077 555267121
    0x6050709050a030b061002030d1404031103090a0531021210080c040525020a060f180b0c0f070c0612140a0b12010609020c06060301060803040b090a0b070605 69
    0x10b14200e1458562844968000d4445031050030743e4590144964000c104a440810034800144040d904600c000d1380311002c112425404903170a0006005a0400403046400040d0300811140045003484240b00e504000c0c0e01c10b0406a010380200111303001500740000c14880180360000da03881d105420120720008e030140015030040382d150300501c400b10012a442c1c4201406480000d850f1307540655184150310b598001c0c0f00e00701d13000b0740c0c0c51a00550124005881902a070000d214003003020b0310507002c0320040c903103030f00ca100c1020411500003081034482d40d4002d5105844035081c410010601c08607544082000c55880204050800c011908014141d60381e2180400800c4603070f9101881000b032180c000c100603581c9543d071090f24116500c2c041a03a400442c1a0000c000d030b1900c03a141c100096001d081142031520501c00000d603a0b207414003912040e1040c00707014600340341c179014410b45107402489000e84d0009070300c18041020000c220150150b80d0050b080803030b1034100028200c0d88184046060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555269577 1250 555268327 555268339
    0x1101080103030504060c1b090e010b01090506040302040f0b04050c041d011a07020a03060e010204060305091c080c070203161409060a06120b040207031e0c05070506030601030b0d0605070905 83
    0x40002c2a00442543c04858030341c2009038030021140f034401400621a803682c0001d0007040c10102c1d5008107684401074030300001c0000c000034440c1320f00548546600348650360303002c40104030603c01402e0541040911102214000c902d4090048c0003405031030b4211165034010030041400c00018000c4012041159820507401c3c00c43c0d41004400c103894a00d10f00400c02c4054005030180c2103440c0d0403680c200541d00200100000710b41034000b0742c00f030b501078400e180000c0d04210100b400c1e07002c040f80303e800e21510301e0441d404400030300406803041000100403148907030040c0198030250700c0c24811920120b002e2070414082e68145058500850520800203001d00000c2042203031341e86139000d16500f035680e141040a01e0340440319115000d82001035030315410a00110712941010342148111860108402090503056601c0750101c070f107000c2c6e114014041c0c0c2d020080400403805c058000703542100044c5800310702040c00c4804555030108501c01150305031750798001c00c103d890380140c090000e00022211 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555270827 1250 555269577 555269579
    0x12031512060f090706080f0c0a170403090521061303230415030902010e0613090e0a020a0501050711090402060c032701172220013b01140f0711010801 66
    0xc4415050402408c118111100250382c2080d9030142401d99001089010484541d1400d07103401440b1111074403400340140d020300da0051140e181c815070045503582c114000e10359a590b83c003000450811043c0c0980900400641d42a21a6200352032990311016691080e0340e528a40031400740e15001d181a50800c2514101114005031717030010038220301540c04c5a030b0588400001009841ca54180e44c40010010301e400d040100020340072662807940c0c1e00850307c42140d03d81d2a40151494407494400816501644031041c6031407501d6916540c0142c00071f025035042846620060f85550b00500d00d000a4008000c010102100f9036203007207400d1759080c85c02030030044220300c3e882042c0001030440c0b490301400568103121340c0315042003009105e0f040705c201c1c1c248021465480300d070700c607080c1603550009481030081c00764110f65200d4044000d0400a2409260009840e041d140a4480f440541004003640002041803503840180c8022101d00c50300781d0361041180b9000c070f46c445c45100b01905005075100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555272077 1250 555270827 555270841
    0x81314030c09070e0d030e0a140901150309290108030a050f1b0d18091802041d0607090501020625080903130303030204030b0912031512060f09070608 66
    0x100810081c0050b40c80340303400d407248442034580c1e6110103001500040341c10848818150711064401010105642180d40c00b515040b01c1e41a281058003d540c20a0060004000207403006100403180011464002600c0500303a0b50740e1141410051055400d41e2010741c034810000070b0f1001140144601002140750168040c0090124000c090038421000d8000c680190640c03484038010b0f020710102d0094500c081c1400c0d00c0942080e0400600c840c4200d00a0f6000c80d01d610540314010441209161000d030300410f030341c200000f0f04208003158010326549800b6440030b0754200b0406015032a00d464044070b4500b041c0c00286054002840d51200f404420000b85502c08500c0d00466440303204e10f44204965501e41460340346200c1c2d450240d0305005012400402e06a0680c0580256031051442210399142c00c8200381c1c0c0d608001d449280000b204001140703402000c160f071214000c60140c1114a54a03080101605112045130f01500c0100c884080001d01a001e1045101500d0036042ca40c6c0a418001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555273327 1250 555272077 555272083
    0xb03100207050a05070905071205091b01170a0e010b010305130f0302070305031c0b3a050a150c0207061d040e100e011107050a0809040603080708131403 67
    0x99201000103a00140355400d0100a00400311615041412280003c0e91600880d004040c100c0f0381038001f507455912090446020700505004841c500024016404041072061b0b0240c4006030326418003141c040000c000c20303455120b040c03040d00051301c001141d03010700074040d007520f80d040c02e000d04045c0740404200c0d00c4004811902041d41d0010f6400f10100b80602d800d900d01121508040c04030b10012401103507081a4400d00484074400f000107220740c0f0019002d00054800e00445000b80b10302050140d0f04000e2810042114620012030281c074400c0652140ca003030208600064620401418807034110301c1c0c26004225500a89100078040347c0e14201c0700500b20403028001800081c002156640e8030355981e0804100c44d100f0409844200300f0000300c000003071a507005400040c0d400c1520950b1000d41c0007094503d02c0da08003010740307010b47ca15a544407041d0301400c0241d900c156140c00c040b012518a03c0506032940c411082c180c0d8a10030301d1458010a48150b01c013448a1400c940302c0400303602c002c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555274577 1250 555273327 555273343
    0x10090c0c08040b0c030f18032b030c120e01050603070f0513180b0a14011703041e032103050622091104180311161a04030c140907030b03 60
    0x20f10718454a031018080d400d4214458820740e4401ea8a001c22140281c201d6169105507080f400c034111100b80c0c1c0805a00880c192961585422803200e8081a000d403d0103604490741c2e40807140b5200c000302d0071010386001111010400c002c2940c1d922020404542020880000500350720001d01c60b5407881c020015400c0e01ea43c42c20701030810b845070781c00004154845002d5400c0c41d40160b4040c12490300d540c51100914840b0f0b8040381441040c400058800c3c005401702410f030300b401e805186400e003000743c0700455280540704074038600007500001000c02c48520140351500d4621403500d5000008907001010754030090003040c46518803041035000b030300200145904440c0c2d03448011503d81c103242401d104070000740010b583c00900305031040e90a4104016407050340c6129444460a014802c0d01295075120b00003902452800e11110070f003d1201d004444240d1688a141200d10f05600d96072800c2d000c803025800041c41c00c0580300480711034030f0084800c036848022842d003044081500e0700003944c1e42101d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555275827 1250 555274577 555274589
    0x2101a060c03070c0b12130302100b01090f080705010908030a020d0807030f1d010e0303130809270106030e010203091023090c1206041106030c0d0510090c0c0804 71
    0xc0081e4141100c01c0a109440505400021901a499580c10800300580c400410750340e01e80d41e00000244c82036500d500080e00c040e0182c1c000c00f03010394400006801030540a2005041c00f0581c1000190f40d0340615071a030142581c0710140184038501030000d400d2548030b80121319650001e0003d092020360009415000b0311180c54401d14076100d00c0300607170040c4111000301c0400c0703040005203480210200310783d22000043c840204140030440040a071a80001d42e050300a000840710440b0110308414050050341000810420001c0c15880d07486441c0784080d8150811019140c00400070300742c240c494548003143c110000d601d1450441c0510351142c6c49807070380190036555050f80b170000c3e00c50304000c1c80c0810a10366840780e40c1d081910550380d4601520b200703503108144240c030304c60364582c021540a014681c0200d400b84d03050848010040141c100425201d101c030001e02182d0110720b80d5009080c05404234143c03440031a41041c92603815150b2825685091281021110000070b51307030012201140e030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555277077 1250 555275827 555275839
    0x50d080d02030c280f05120c0a02010b030703050601051030150f03060506060406022e09080c01050c031003020d061b09080f06010b0706020304030e120d02101a 70
    0x10310420045051300a040c001c20070600580c4040c4407660510725400c10b002c0c090f45441d0f000024028040f03403540708501424501d05480300c04a03c41a80c0c40f405002e00c50074038000442c0083c111000309241400c294025580344c0d001000403c15824144145078101c8403500c0c04049201e070a01c0200b05112185480521404004058600c0302c0100da006200104075440502a0a41c0e07031600002124400e0205441d0945032401144680c03801c0c500300c4040300c41c250090840e4480c488040c641d80780c40300d82e1a00415603086106144080b00748a180841417240800d940c0b51002000140d084031030080942d042050200180400b55084a04840071240d0440300c6120120503440e00c0b00c05044107140c1c240d201c984201e64850513980142064060310001d00c00c907451501c6400d440b84e41d4900c2840b50f0200311404001c450302280c080d4005550050180c00c000501a16800109049003120404c035903090700200400403403a981804600d0701307080c0d403e005002c06080da440d10310002c52004802c9105072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555278327 1250 555277077 555277081
    0x90b0f150f0d021917100b09010e2d0708061818100518100908030a05180609010203060a080714062506020711090f0f06040915020a0207050d080d0203 66
    0xd13407940c000902810000031180d280316500c4445c079200400c8105221014042c0900c3c2e4441c0d08850721078600110700050000140340d18101c001405502e01400c14140100c13580d400904c0c26103c0d050340741102c15401116452454080002000040301401480c4503d0003500190b130004030a004041e0000304503d01910301248041206140142c0a92a2101c8a04140c10000044240d000847c4900c615909940034080d000745164102c038800310004184580038030103d101c80e011540a50b40c0a20002c0c1c02e50800b48412102c1407602c401110360181aa400004100030340c1003015640000b8002e40c4020312a940c144110307001219034260050f80100400305a03410f45000010500d643c85034030700090380c0b4a15540c06d10502070f41c4114810b90700390380c0d0318420340c60034140341d2220b520841c1e00d507165405544500300400c3c1421000341145500548520140d07020904401c111000030310314880040ea55840018080d082c54070b141e0180d44034221017020380011400030b00c00c40d450168004801656a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555279577 1250 555278327 555278329
    0x9070308031f14030606010f09060c0609020402160236042a050910180902041e060f080a080a03091e030314010e09070603020715090b0f150f0d02 64
    0x914160724440440b54000001941a82041000043e41016015165640c0c5c51000640c1c089818040700030024990707043c1040200d1142009004241c0700b03600200c0c0c1c19006070001000d036080510b480c0740c2d11805040303407002c600d8400d401e000100010700e03c00d410220b0002002c541d941e0400500301080400c0030010302001900150b0500c0b500c0340000130508000c803000e06003409889405043d00480c02e1101007120b50300b03203111440868224207103401101c030381d450480f0048c0142000407a0415151071841015a56103100c040450811880000301c0038582982e1856205040d0b01c500f540750040a140c1c0086075981044a000004500380419401024a070040e000c00d205411001502600c40d12003003015031641120545446400e02d0119590300d80c01464290b0303c0650381894503078800c48080004500a4014100c4180202c2840900e1201d10801009407a102181240c443d4290401c000e0080380d018000381d0816a4040e280c541b854038140440c8045410600e45413041d41c505000d9011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 555280827 1250 555279577 555279601
    0x10e19110d050106080703060e0106050a060f090b0a0e181e040c03020301060905070e1207050d1103012f0f0313020d0f080301050123041707030f08120a050907030803 73
    0x64160b010700200b04169a500072140c9980706404200c414500b000942ca002002c1402503800359030000b44003800913442d2000c285c1d00340d003028010340103206201000091308c0e4192806400ba5a403181c45190340f842d00d950410030301800c01d00900107048411001e01a48003060040458114503400a48040c0e8540303050801400c0d0701940029030540c02d00101090401c22608024003603803240d214180d03c8620001000760016041300b404510f94050700e003c20107854132a0340140e200b4041c180035501a1041c801181c203489080241c40e40309901c1d0281109403508184022464001c907524440c100142501c150503548409070500481e051404c0c1d009055507126403070303c0c1c0303429400041540602294500300700c40d070b0070901c40d09002c1111101c1c1d5082550b82e86965032500f031440440035260904108424081011500d5190a00e12a404000c8005640001c0381d000c00e0303004601068407a40c1c05890041c1c03a44004100003c080d090005000c0070717010014850040d42d500941d40c41d12542c41ca07550301a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 555282077 1250 555280827 555280849
    0x21f15050f060409060603090b180a020f04291219032a0f11030c090a02071703040305030907090e10050903090604090212070c0203152d0603010e1911 66
    0xc131515010b8009a481c0e0554480341a4600c5002032805582e00d0f000400c0c02d1507518110002c550304188460001490486010b2010480041c40000c40a081c844008445606884407a41003250300790048281e1424100d250110204c1000030703c894080314020f06c820503500a00103017400034282903020f0110798001d0001c01c0c5a2031070f101c0e6a00c8005070801000c46414035070280d941c0031244c0c0c0342c40740c00c0c14045500d8040c0407016007007006030381750805140000d6002d60010b0314a101d400800610640d000380046019a00a17070760707551a424010051810850f065000c0e00081c0e161450200081c0c4011680c88144480f40c20300103400d030b95000c030207401c510443c00050340c0260005400314402070154040c00f820706080131010341554a180c400e0f540c4090f5410040d41c113a00a0384502c03d4172002c00030300c5d170b4441d201090001a135125607080c865044809a803660b00340205500300110790500344950044d043c180700052252002d580d6010700300c1003115074042d200052200703044140e910b68000440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 555283327 1250 555282077 555282089
    0x2401170703020a0e010503010506041e0f03300e0d0309080d120b0405071b0303110a0f0f0c02011e0c050a0521120f0601020a0210021f15050f0604 64
    0xd1401140050081d407151003210041480000c40186551060054a05036000039022a01d45414901503480200c007906440035401d40031100840d030b64580d10001402503110314210a81062440d1148048040c44071104c009a90344a01101c0741c258400120001040182c0d4031550307219041c00d0494504c0080d80151032684202d41d615040241c1c81380a00f820b0703131110705041010602201c10481518402d0b14040b000900160071000e0043c244002c0804080c41390500140d4451900304180c032640225140c000410001038050b0f0509800040d004281ca0241c42d07c0200381c03c8a500180c15050341010303c0312452030812021068a0081e43c0c6034440030381020490b086003180d450019910100c0030300a4000381007141c242600f800c0104c098034070a1300c0415203070300c080c6e440c82200e00d1107520090006046111360800c400250302c0e01c02107a02641383c91782c00361011500c42a803c43c0b1004110042006061420004609908071200310f00240c4204458036240c40700d0313100002c3c105004941140f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 555284577 1250 555283327 555283367
    0x909051c020f0604141209240c191103150a0510081c0906080c0f1e13030309060c022107270c090e0406090303020c0a050705030111032401 61
    0x2104c1845841da0300d03055550f00c22803c6418040f14005c1c0c800c440c3c0140356886801001000c10764030081603030003009210301078a142890401c2c2c4510500d030700d0491174080101009115125180a0040c1004101401c071003d034010300d200500d54071186c42490b8024207641c021541c0f54089003059126503484802411180200c51000c034410214a580d5502000b42002107030718100005a007600840303840d40302d8140f0000f020b0402112030f103a14001e40c003007548849003124a8001e10749106800001d00008001c2d0405400c0c12401c2d46405003d06141d900700740140034415000f400180d940500780045100c0200d460103186028035a0945031140580061981d11042c01d00a007820b41005042400794000f02000d00c80304a1190042c2c0c0c04817030601944403141e000c80d002178041340003902f042e00120300c245001458402a80780c503030b060007056481220300342c120325401c0003186001d0180400301032a000f4224074500b007210f4446040c80301d140ca00c40304000d001c0c08042c1280e00034051506905001004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 555285827 1250 555284577 555284581
    0xf060a0e0f01170406050c0d06260615130902150c011a100305090f010204140307050f0607030c03170103060b2103030712020405060703080609010909051c020f06 71
    0x9000010061a0300e070203030341c0d1481e820302198800d401040c0981c09051081c015a1501d40303600c40a044000d000141d01082041444182c3c40715104600040ca014207101180f5a007000000c04401c82c8003410011035030154051040c0c2080e031411001c50b010048402da181561b034446444c020342800700001c2c5d4490080b40d010500c404c0140c004240005801c80200300b0307801ca442c10103403032500107180c0340d40260800320100d000601a50040740c1281d20a01184d45200c0401d0000342680d20540100d491002400090700a60508200603c080c184c00c456000284070600b02040c228000e4000c05410807142c440d84c9401c0c10700802c2c0034802e4190141d090140c0e5a101c1c14100e0103414000c60080c020516440e2180201e0034043d840103d1030340110265140d52280301c0100e9045d0003d01700c0790280e5908000c0000e150b59108000c02005100c0d403a255260303d0620b04001c0c0c66001644190551824000c1e18000180302003040c40d4201c0341500316407103c03421003038100c2c41c01002c0c2010000c24810081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 555287077 1250 555285827 555285847
    0x2703030f030402120312070309021f0f03110c1902220912020303101e080616090b0c1002030709081e160303140c010905030d02071104020f0703030504020f06 69
    0xc01180319500a6500045683d00418000c0d96842940000c00300d0503031410103d041e42d4803940150138000c0c00100b1050074001000d140300c445805540c0b446011646006050790300b00e0b01030083c141201c80b41483caa003010b64040d4010344401011b01400002943c2070815011175442c1103203000a28020340700c21181071270700c607451402008005016104510f00c0741c200740301c880c0300100b101d2080c080083c5240d280d924200c1c60548415102e00004140c5006840108121404028462180d050344001581c0c0c10000000038181e284140c01810400d0020000043e1a0a0019140c40062071041c40103035280c0c3d0301c800454000307016401c40207140c0156129051034007107125040f008614410159000381c00402e01d400c81e024541c0c407008001c1109602d040d0002c0f4046409001403500050010404c0c11032551400c0c00e6500a0074030541e41503002c01c824050002d070325198010640d043d14210301e0500c0300001c2ca01e0900841400400301a104d600041c115281e000121500c40c001404050f101c541d07880d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 555288327 1250 555287077 555287107
    0x70b0309072601052202090a0b10080402040e1501031e0f03030b040f0b10120f1d160e06040207020a081002090f06040f030f0f0c061121270303 63
    0x40702c1003901c0d42c2820042040703001e025160407400c0b8030903001c00b842c0126a60038010780d02d000510041c0c40310b90b200480c004a4607101d004c86c07503040b001d540d8000e0074a803a104000841e1101d001070030180c0c2c00401d01c40c954403280300c2c3d2141035031381000210700c040004a80804409211100c02880580c004500908161b01900909082d040449090000e020350700e10000403600d000f51401c1e0b10084c0b2500000b902e601540c0d01c042c0c8140c41c0040491403240c0a603030201500e190220039045651070261030002d52405004020401d03030000070111143e480c4c40500c1708501c50151241c1e100d6540003e00c0780031996507540241c003c014400543e20490749000c000d83c0203400c0003803518017684001090342c0c89850503504690640f11107902441c2d40c42d0840e11a0344903d103c4900844010500c11180303804500010701000060480b552801c6100d8245c8001c241002c101d40c007110907210300803440b82c00500c03030380084e600c00c204511505040940340341484402c02c1c070b080031903a03014040080d401c03446003400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 555289577 1250 555288327 555288389
    0x2010e120a12052122230604120c0b0105040b03030d1b02011d0a290f060f10020a030e060708040b0301050a08070f09050a141509070908070b030907 65
    0x440000c0b0f480c00707201e40a807012074040356170543e142a030071210391007220020002c102e210b004012000229800e50462004031401e002455526403000c0108010021070803010242140545040c5110f2469a51a85c0c0c0664041c0143c1c1c0c42a61a03664007280340e1010000e49a030759075424003d01c000307a040d41c80c4000d107100f82c40c0c0341c20041d420a00c10302c1000099001245048203184001c00d4101415250a550134902500555107481820741034802101b0000340c45001d075034080c42c01109070804408107d085d03508000c2050046242075141c0340415004600108101c0e0503080860200b1070540c0081c24500c24644001c4c40c84030003181c042f86071890000030b14141da00540310300180503190f10840c0c3d034030440340c0f15000030f00075028803d10081c0c1c8143c07c046c0d00540ea0301ca000ca5108040e10160100000c226001d940048040098000750300d44814000c9e0403084034203051110908000c0082d03100c001c98068001c40640000c042244034a00700304110042c140c56400319002000745c41050120101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 555290827 1250 555289577 555289597
    0x30504030807050c03030a201201050301231506090a03060b101e0f030204030f030804030e0f0109050d0c0801110c1b0f190f060323010302010e120a1205 67
    0x408005035540b4003c00480d010b10007800015804e41d640c2100141c082c11704906003950703520b0810001000d44816501402241080059046556041109050031601d00181c0200d940c1c0d06004100041e020f030301d20a0341c2100202c03903d01130f072440040226103184103030300c0b0560308003062003c00002d120302030f80701400e0040200c420034080031200800b1a2a01c2d461061507081d000c450f82c52a03039050143e10000a503a44a040250902e80d40f03864080d03c81c40c4083c406d90124110f8800c12040544c45080203500c0701084440000090302240020419140c2e4002c05001d0351a07114008180300304c446048006002c400000c0c0306207e40700038000c43c142c0102240c0d091620880c03c851218242c0e0442920740200054501c3c502603c0031420403017600c529580c580100c5884d10b802140809542d15400301a200c15107012407020100c00c00441030740003107200da03d0103612040041c40140e0307020b06007009950301103074249980c40301d001c56030b82800c010b004000e1000b2841c42003081d8441e00305001d09000c00e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 555292077 1250 555290827 555290837
    0x23909010f0f091a0913020301050c04150f1b020406030804170d0306050d0b270607020c04020903070e09070b04060f1713060c021501081608031309110c060703050403 73
    0x2a42e18201010b5600c80700c04950340a42480b1180031609001600360383c0911078003141000d00c82e0640200327003150000d03900d100200200140c1030240c60010441c25004803010300e004a9a5900110003c00007003c070404441f60a21890b00f801c1995510340001d0003540d005162140e80e15a80c13556400151041c19420015008810304c402c21a0300038440c1d10110350018051b20603491856680c0e0114001c000c14010700740d440481c4040350512181c400726210b40403a0001c0c481e50405400c080c0c9407200c10141c1c24800e60040202e0313003d60b1008207584040b85c00c1081020140e8840903891824031261b034029400441003c1400688960b1207404943d11903055210700e84100888040c0a02c100c07801c031032590480703c00e04400400100280c0c068034102c0744a205440e6000c0034441c0c1d031501d0000a03030080301e26600014100f032040319a0500c480041840d54001d615140707403038044680000707152003019603465031916062002002d40040300c0c0c4c1c02940b2000d8400ea450110000790042000365020f0340012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 555293327 1250 555292077 555292079
    0x3030108010522032d0c03112802030304051008070909020a02060711070f03140f030c0d3e0c01030204061d0301230403020d023909010f0f 61
    0x403883c40c0991003072180e0041840c1c10030038540c0301500e0111115039aa1181030100a00302e000507012803440300000c07201c0d40c45c00710500c060300340103280000310311800006030030800d1441d404003641100000301503080c1000d16010034481c00003d0841c0950b610058203d8120b001d0704038111743c0401e100c1d01c034018030b0b11406006030f15038807070f54207c1c00b03141050409681b0880c00b040c5224002d8955806000c81c01003241e900c00e480d0b888000c014211a841150650f84041510300c05034000d0001d030f100d01e90312800660808090202c1c10390b8940382d100504041c000301c031802d80340754002201c14004400c03540014584402c02d123000d003402210045451800c0d40203c81d60b5088540c401c3c000c8600b201d5865540000d6207064a40e0039414502501610354591758402c0c40e8030160000b00100482909007078195101031406060190030071b8100c800c0601150018440f8511410000d010f80f040c510300d0024106051a030345642e600b150808180c401d40c072900040001481a400c1d00380c010075644442d1031448070b9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 555294577 1250 555293327 555293341
    0x905030a0807051608091908011409030703090e04060621050c0916030b03330108010c0c0305030c0c1015060c2027101415030a02040f08030301080105 66
    0x940130f040d02000e15045000a10b4020550a030041c020f203100080884681c891400c02144d25881c5a40c00012165141d410001c0b00101d031034101c56011b06084040d610702802582c009001068a00030303091031a080300045400c0c807045a00c010080c01c0c40490040001c4c0611000444001d0725040c1140c2070310418100c000182416101e40b4003558041c00c1d41c0c06040920281074028002899031b16415101e002c04401411803105c2c00380c50141d802d1035220f0358000d4040030320300d4a9001608000c200e41c0c10090b002d03907056030215000c2003250300346c681141c5988070442040c0841c0b00f038080100a074451104184080103091744030079040c6040c14500e0400c5548d40f001503942ca44541000307840d80c1030b10400e81e1601054000600c48081d40140248c20101c108400c40150481804044a005005a040007840041000d640300504841c0c0d0002c003428240000040d80c5103a500808041c0311800304c081003040c2d01c1601614080d11600304030316030380d80d203804915940c0c4d04244143d010941c2840049a03038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 555295827 1250 555294577 555294587
    0xa0c060c030e04050a021201031b15020c0f061917070e0d080a020c030a210c05250506070501021e0f0f0a050405180702060108010c0c03180302040905030a0807 70
    0x30565041d01c4508006892000704001841c00030501a00c1c150200300090504a812110501031845100300401102480039042c8600e0502e070000290380000455040c074072034000484626081c42100d040903400d2069020405500854150f58003010150400c4104590404a05607524202d818114010741d11020122000c0c0c00c010f1960750003104180e10b082c041060040180840c0302c1c640104e6111101041c0440c0c500000180c082c2c449064103c0120f00145116083c1d0f001c9804900d060306000380280c0701d40b0b48800d04044446101d068401610344a2804030180c2c20051000a00c401e449600604065000c0e41c803007500c14003000041818804400140c03415110301c3c2014004d113a09150626040c0031030303680055201810300805100024040e6203020f41758440c04054810340740c180c1091035000e4039205041c0c00c03041c2264146080390350305a80c0110b940c14401d0b018030702020742c405ca03420841a442890303000650480c0c101440035080c010b00000078018040f00e5582d80b4200c0e40d17605001c4a0f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 555297077 1250 555295827 555295847
    0x405060a0c120219020d0215030c1909031208150901140901051504180b0a0f0806061e0f18160f050903030319150305160504020405090a020a1202030403020a0c06 71
    0x20303250701301c00c0b924805400c0076101c180c80300c0d1002e0921801c110810700d4480c0203401c200e6008001c5400003074240c019110903002c1d0a241906030078221420350039075a414034511082075841c030400185000044100004168200d96030002403c600802e58440c11001044c621300b414bd20f020301245400003421341010b0700c1d0403200880d2500450700741414000c0c1c660908104590103816151160400034180da984540c0400800f040803c0d002540d20308440d040c140300b401400c152240100842010b03180c180d201010b000e9603000c441907514030702d2540c002044100b080081d044641401c908210100c03148400b0340303420078102d440700040d1001a540c22125881620816905500180046540c40c1107007070b820701031401d40c0080801d9440c420182c0208026442e481513580d030b484000051045500440c0d04005080269002e510f03085c01c2001040032550003601201c19036a0019212008a10400b000d881443c60709000b5596400c2900307000f583c903525194103480d0303240c41800024696001c0c1017114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 555298327 1250 555297077 555297103
    0x10905030703020f01050304051513030306090b0f210303010e2710051e040320010605031c021f0f1425050417151503070b0702060405060a0c1202 64
    0xd038131450200c0045a482d00090421a5584540f44484404905d105503003442504040f0705c1001414143c10024281c9040e5805024001c0c50f10500d103425454030a078054078294240c1d010120001c05508040340d0002c0d1a2101e00280004800441d8140301080001d0042402201c88401403280b518803403041c98910f020710080b58400c103095140246660420790b8860001c1501da90140b900d402d0210074803508840c00c400140341c0040aa100c1c00b0301407400f9440301c41f410000c006840c1450046a40c031100000b050145280c49180c014056200b000306520048411800c3c0707140e20600307143e54018000c008c013816002c0b070078480501c440b10404102a8070419400c185244415002c00c0c001d107020000ba030b600340820100300400304151035118038400c2030b0a1904020207481c0c040b0f11090030407146c040d0801c1410340c0b100e00d480b001e540d00000c00000f07507026400c2007a42e8048034400582140b10700d9220320303044400800c840d04c415401c07400c0c0d140b01901a46903982c2170311044008a813038500c41c080c12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 555299577 1250 555298327 555298339
    0x1e1403030a0c300f090801060609030b04052107050d1704060c02070302100e18270c0a090c020c01030506090a0c0c02060d1b02150a020708090a0e0601090503070302 72
    0x80340c0300b88a6520412102c49050300d032029001e400080c80d1001200d01400300307462184075481245c0c4090540020f02c00722008101c5d0341e08100d00146001010310024003a500442e020409110301400100740303154804598810304000d074442c10032036401c80348082c4c1c3c030f40c018013044469413070065010000200c80c0360228038040e82d4580c0c0761030040100600b250218880d845001c001619501c80e603c41d0310006403900c40e5500b152004000404001810180c507507448a030512a400b203101024809140b1220f80c040c4107040607501552500b101d80c00035a50150020318002040001c07540700c11401e003507580c00d480f90750015038015000e440c0d081d5112500b01c000640010140000c030b50044101c461149020b0a440d081500002c000d43c0002e540001d8417960342160003845002e0315040c2c0202d6941e80060b103c5004001001010f500002309001502a000540041004400c0c42100d902d000001c00c1c4001c000d840c0c0c5c4101c04030501c21290540030071500c0c10046210301e4005950030440b0f90003008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 555300827 1250 555299577 555299597
    0x30e01080106020325240b0a0f08100e0f0303040c0e090d1d01030b04020c0318100905040b0d020607110f010504080601230d060509010507082e1e1403030a 68
    0x2c0e00030035060001e01686e0701140300040380e1801c0450f4000d131401e00c82d000d502140c14044c140800c84078002c10b51104a1100d60031070100410300703021a4241701d611503240002a54403601c04400e081a0411300f40c1c00ba580030000c200000c00802400303036801d840d144036204d80315907a91500c07603603604e82a148140109032640781d100c2c80e03002c04244200b0b05039410b240201d8083c54200101e01603800240c215256a0808030740300207000304034140741d003a031407003242d800e10340381200346014040c400540250b07401580c480d220b42480b51521590022455400784c170b12503a40129041c100004008014034501c15480003101200710b42c031603401d6800391580031000c0d061070f034601040d114041c643c17480c0d00d81d14030908041c004042eaa51711440c81085009607030205040c40d05200035421680020001018440c0d00020b0103403c03d03001c0840756541400701d406002440d1240c1c0c1140c51040b483d488424076003022211821220040c40b1550115800c581c18100f00340b100c901050b859010300124240080e082483c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 555302077 1250 555300827 555300877
    0x21c091e03051c0e0304060c0b07020a170c1f02220f140f0301060602160e0c04170f030c0a0b0109060b03060d0809040f020901120606050a05070c12030e010801060203 73
    0x10101905983c3c0600065401d2181c03d9540c1076400c1503100201280c000c008072000e000c10f4544072548807980e48040d0000d19010b5a030020724049000544011180101c3c2105401e10108490702c54240007903e000c60001800354614081d40c4280c901c40b103101e420424607801c07203c41d05155000d850380750400d4002e040c00c00c03002a04410000c0765035a407100020044117410b0300d00784150005840030303a01406140c4040600c2201200955115419904000702004402d04086c01614107407249240c80124043c1401c2120349041d03101145a4840d0000040e012001280015103041c050720641d002c01d80740c2c0c0d032425140101c84241c03140301d40350041040080c1c0a45031030b54205111070320400651b41009035130700204046404290601841e6640068840c2241d031f00015121031b180300340501030003003a06000c002445805110204400d0040200f088010400764464900c050484404010402c0303c01d81402007450f01070100d075502190001002044007172012084450001743c101840d0401e00500c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 555303327 1250 555302077 555302107
    0x605090c040605090c0904091b1a070c14060706050a020406110c1e0a08010501090204140d0f020105160506151008070207060e04110c0a05010c050408060609040204021c091e0305 78
    0x4500c6c03907009a5030341600f00002c0008542c010400c2a401c0c0b0748501c00d04046402e41003010b0450000103200741440000d0000705200d180c0010365000d00d054500707141501000c20000e01582c0002000035081c4020083c07400c00710750180084422070f642c4d01154110304050181c88614507071035183c01490140c40c1c801c05050701034600d020343c81d02034241c05e03045550b288076600b1100e0a0304814103c9070000f0381040108141c4407d05ca206800710b4403c048808543d9075901c0c0d030801201c000741404000300b41e40c1c1e00b0801c0f0442d0060055002826200380745000040d00410041c054411803283d15034007032421103603100300300d0640318412a4005015250403e807096820032924010b40383d129031a01442018000b5072000b41c40030041d0303600149820f500c5072920600b920340140f0558200310b0300744420000400000b1b8040d81100701510908902d8407a400410b0183c0b10b009158a41c0d03400031440280704e411741303921520917140204015100c882e4040d000150b0803000003005800501d0500c82004030503000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 555304577 1250 555303327 555303337
    0x6060f15030c09120c040b1c0b07120207080c070b0415031a0a09050403111b0607170c0703030e1509010806131a031c05040b070c030c030605090c040605090c 69
    0x96460300d414a11010002020000c85024500300c41d00400300e20045410140102c1e100044111680146402c0c1400d40341c6e6101105c010241008011601198070ac034066a45c0d13620111108609554a031030a0030a03078560350164181d060f0502c01c1d00d000044840b164003d490030365008080d1002c1200740315000b10050004154004400000c404a03002e036903444514403001400340f50001704043c0303403908010f00a4028008440c020380c10240303944e0310891545808408604e001c4070440d440e2116400c00c2074440d00d80d40e0307036180a920005010049100c0008440040307a110b5a15042d4010f00c12050114903481c000b04410005002d000c0c0008039801900301583c4140081d240381e0b002d5a0001041091354500c42c01814540000388110312542001e00100c0002c0c400701c0800c944154204000402c40d00c00c80c42814001013001c601402001000c4040100071034100c860b0200c9541c4a0400740b00900094885070103d1050a0f800e01c41400c0c24056041101c10050a1792541d41d980c0340a05003540c08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 555305827 1250 555304577 555304591
    0x405010506120a110d4811070b031f0b1c0e0a081b0106030f030f1106190b03060708280203090109032316030e030a05010e06060f1503 59
    0x120310070204c102d911500a8034120100e048081089030080340c90241b900940c01c1042c0d51044801c1018000380503006102d8601900311b40a031302d050342500c004031070030246511500c446000b0060002040b06440015600a03c0c244441d4408003000c02240700142c0c00038429414403402c24003a50811500010f09100d0160000c200448ca070f8180d10415410300704800c6e402c07515081e01081c1c04913902c0120f000301c00a88000b0000b000b0090846d12840080580742c0801010003440300110300215105030301c11900c18502c40e08450003818050030300c451840f5070300f00350350030940340a610100c540303000141640182042c4c1c0f01c0410070b8640300900c07040300c006002d00c00c81c4083c4101e140d030401e1300140700851003940f000c1d00024a64000786002000e90740c014442d00d0502d40000c2103040498003580c225030300ca00014285a0b0741d0105840c044d6074042800007129814003582ca00141401419000840583d40143c180d861340d569000411901030040007455030070059810f44400740342c940100a64002c90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 555307077 1250 555305827 555305831
    0x9030319050606070f05070303030b040905070b070501110a02010605011b0305090f01031107030c020a0e010303021213051206100f3606030305130b0304030e09070306030203061608060405010506120a 87
    0x13603545581e440c2c24582c1c04112910b0307000c002d00b0018194144a0070504580441d03003030080c0140c0307488681d510f010a000f00007952000003034510070000300758007420307442d005425110744511488201034024001c0303106041c046440e0808030403080021440c40d484030742e03241e118241020016024450320340c2c0d080710b05506241c1e960b0b649050b103101800181a4141c17203070303507410100d40007441840b808556651103a036011613034000510000c2d4000c1071081d201401c41220700e49a0340a00080000e013440744c0d00841d001001000b40f41011400400d4141c4581060b90080c1c08141c0e80307042403150b2620728401c41250881c0d0b804400f03040d44908401e0f0040c800e105407480300c40310151100d40110380741503000718041071000801c19041003401c0300002c014100703c00558110301e09620054541404c1c2c0745628070501050b400074410b64080d03840038003c0e603005000c803906c5251050760141030030049900780340450030701c0000812900e002c0c0603090680358058074090074981100600c01e0000d9000d00404411a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 555308327 1250 555307077 555307087
    0xd12020a080c03300f10050d38070e01020f031803070906050307050909011d390409031b0606092f0a0318140609030319050606 56
    0x5001e040541000b0038514051561190703c4030601c2140c86424601100e0380e014000e20701c0252825003c0d440d0f020b103100824441c40c0ea13411040c10003124064206035803241c882907030b010034001110b04405030550420754070b030078410903a0540b151010040040710240d00c003800010f60348622034204202515018011101c0e2113804e807418a085421410802031410010301c081c0049141c2080014010141d603a01005281c0c200f002281e00c4011a00500d4010151100801d160001c250300c8800c104ea02001540c000c01422030005480d030414061080300140000712601d14044120901d13080001c8c6040340a000100300350520014180004059090020f000420b4003049107540c045a6450322031035000444504103e000c2c01110392103901c0e041c2d001141b040054000084515940d00c40c113900704101d84aa070028402c8002c1c107281200210038000d0211980100300d0880d2103580080c402c10705a85c61541c8000a4503600d01049074160b25007425290f220a80304020391105802604c0502171601c0c0c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 555309577 1250 555308327 555308333
    0x4020f010e12010e0a021008040512030c0f0a180f140d0804081222051e040209041a040507020105090316020f1018080105060307061412090604050d0e0d12020a 70
    0x103c0b10200138468a8100c501740800714507100b50700c000305000a0500f111030741003686595a403240580b00070780345194008041200ba09140e825a40411202d58100c1d03900c2c520074400500004016101c507070f602e501d8803004215801c080350004c0c10707240c00d05640c02a0303400800411105841c00c1c6000c1c0e5260004000104d8000c0040c880c2e528200f007940802580c4503151460303408618202440c258400a0440062120303a8481040c4000012046100b0640e813181c000060000e1081816280d44640750040032220003014803540d0062010407a0200442d9507230900503804d8640072a02501e0581041015018a900c0c10000600c0240085c03c9090340c0003521010480ba04100c05400f0046640b640c9080d103512003484807003014014660003403009040801c0802c2d5205100d000700d9080c01910b080e0040240030910540702c03c2e1241c40601c019a040c03050644d601c800081e0341c1a20741d070151105124042e8024103014100c0307840030b0078108124425460350415a0400080311007140070f206861804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 555310827 1250 555309577 555309581
    0x20d0804090c0207150302130608190c0c02011806050304080c150a050402040b041406010f1206091e050408090409051f05010f0512030a0513090207060606080f04020f010e1201 77
    0xb90b95164009107810740c2094415002d90342d60102210070140104603100e080d00d00c0021081c1190a6803d25541c10703250000d0782600d50303802d49541c0d40302916044a80c0c20380c0d90701400c0701c01c060307000b038803100c04104013014074442441060240700d0200300100041030015140800030829001010151010b40b00389015042da10b103400d842c0c2d212555181c4051006500d01446090304c000f0084400b0001c00142484100e411f25009041d281844941d081c40701c0a03600402010210080f80b20003008201d49990101c8010003011012369035004034030072501107030f2051f40705440c06260060300440c02c01700c2400802000d0000d4240484580c0512012026607884181008800c00b05d114000720b000d40c10628a600b501c00c41da030160348a000c0c4c0d0740c9404c0c004103001c002c40b0441d03986450201d6031381c1c8200c1001484001c0c41e80c44051020710002d50b580900880b5031009003900c40030b5560306056169108007280024041e00c004c1d5201440203000e00d45580500c00d1a80d8000c0050191584443c40e8601142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 555312077 1250 555310827 555310841
    0x708060f0403270303030c030906050c0c060c042907050a0b010503010c030b1320120901060905061008071214160546110106140d020d080409 62
    0x40404003020621003015009195189071001c20f25802c0302c00c03214112255101c40991002a05040e601c0345043c1e48180329420002499130810028001c5080c412101045035001c1042d0700c800c5d010b04804620400e5080e0211030494094290105c207450340340b94440d03540c4140c1c20024403c900c0c208901d1001541c240143c80c0c26600032242103403958500403e060075201600b08100416240c04480009130303646584103424001507500c006114004061500381400040c45c180010207004140c070340c04500c40d0100030340724022740700090008503503c4803054217841c410760704a030344891944c07141d01603284940703031403580000c0c1c61901c11179450324868006c048a029814004d0020f004904004001d50446156240c6d10000c2c0b800e6844e0142c031860011601d10807501e03000c21790203425694280000d51640016180c0f2006c1c2c11b50b888902c60341d2000c0d1100c99011112081035003405800158024800810a20050080e0003807400250903420000c03094411001184c03050340a000114881c0c101c0e10500c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 555313327 1250 555312077 555312091
    0x16031409160f0f060507020301060b04080f01061a030610120203010803130e01030b010b031005041104080d0206010b1902030c010f0b090c0c0d0f02100c0f0f02070305071502070806 79
    0x201c1c010300c00000d445220911078006009025401c6800c020264244900038100d9040d443d1642c0c03914000e10029025042c0b2350301060600d54082408038141402040315481e4802c03100c02001065a1f894100c2300d4908286240750640c41d040c40060740c5420304da02c200da012405850089a0415441411004c83e003081c1c01039207096001184c500300c0b4000b004404005055111540d514642c515601c1c1440c8403014021080c640c2804000f00e414200c480a401010340070080043c03004408450340ca41c0250880e06c241e238860f219a4003203c094030700201d440c0381aa80702a1206250666908440c00440c890510180440c030042055440d035180c00c3c071503402c902d2480362000c24000c07000300c01c04c40042e1025100304e00310300c0c04200c03180504c88006103514004406051078201610440001e904154400561050f514284803080c0c01d510741c451800b01302518691a4044059040311080703a503910503010042482d40120014808548001d04507082c1100f14412124401c2d1141c1d452800d2a600b5200c032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 555314577 1250 555313327 555313333
    0x1020c0409080910050319110a03090206070602160606090c0e012712060b01020303130f02060706140708010b090f12120706140106030c05091e0a0806010515090916031409 75
    0x8007a070000400c405187d40f03103240100340450759981600b00c80034407498181d07405141e82c8003540000c54480f082030380e45054110b0421034445000508a0180d9880c02a0481d401403030050003040e00081403042d41e040010a5503400c003040340300300054070107410340f04100c000c0380c0c024010440301d44031076080c05014103185003e1500d4150546426000e03070701d440c2007485c190342081c820031455902c045850700c0116001070340b00e0a5942c1328000308009100d800c0300603154038108411400c1d80038480007141c0c00f0b820103989800d0341c0e0380d85106070b290031702890b0b41c0c0c00c0d400380c0e611034070741c8880c5050100561224080b0050304c015a60211010b410b5900c039190444002d515001040c0650440f272400c40d00408060406010030305e10244001c3c014864920900d202e07000c050501014032480c20760500d02c2110241050121546a0005c560740d084240f141900c601010b508407107503201c489054800f10380c4003424011980d201c080b0b0200e0504114150002050342c3e601c0c0201104440500d80c0d03028016000207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 555315827 1250 555314577 555314581
    0x60f1d060703090f030c0303020f071a07020c061c020438030106080f0a1506090e06240c0a0803040c060806030a0c09021c06030803012301020c04090809100503 70
    0x4803800c04000901c0c4000341840c003004180401d030540030302c5038040c0d414500000c3c05012850150024010fa03c0082001c00000c034030b580801405050241d2820030120428034103640307512049a44803880750000b42c00c00824030841000039046a07007031050100134200942030070b459100540d00e080c0400441c8101b0141c810404001180407003802040f03410208010380356606220001e04600c10141c0f00c00401007004000500c444c203030340d00c21003010600250710344134141c0d03c0c0c400500780001c0f805045800ca4407500814914501030362102c2c41c16001d012040032025480581000700d0b0058004502a4040d10307800c0000a217000c0000c6118900c685107e4070101d080a000908511004045a0190b805491444045805a807400c0201c6201d40b9000d6640d055012a0f101a04100e00307490045c141000008410003114201840c145c4070030340603d50004402000e11010703103401071011030258014220111031418682c115000c0341d03005500041c5400090408500249840080b142c005040030007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 555317077 1250 555315827 555315881
    0x60f0510090e03071220010c09120533010e0f06032a0a050301150515070b06061b1c0e0a0320040608161508070c030c060f 54
    0x1001d0724244404000040c00480381d00d5030391050300130181241a4800c44040701c0b9208501b40001313405403c2002c1c070803141124115010b04041080d00b000304000d2000451004084402010f11681000081125016100d0b84144810200e200c2a50000d000003d41041c6608071240038003c00413407465404514001d07094504191018000c01c0c480c1c1c0160030366800c42d03014510a0040c2c00c500b540e0140320a044503000071440d840f0707640400d40650a08808076038501c6d94403506401c842040d0f4040c803062407040e0f940b20043c030070300000518881d0711001207081820010060400c1c00001046100300c01001c80583e4640314144c0c1c60b841d2980c00b14080c00c3c645591011f110b6500c4042507905a001034111380d6020f409820741c184150940c081d0314901c8401d656286c000100034100340b41135803014425441000d880801a0092501001ca80d10b2550401c520451015100d00a29a6031140814031039404031084c04c0d4004040c2e41c3c0c036840c1e403000c0761008894410106c044080c641c507102026440301c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 555318327 1250 555317077 555317101
    0x2a0103060f030201080f190c0c0203150601080c031003020607141219050903030909180d020304060f03051302040c0c02150426032101050306180706120603060f05 71
    0x1410016014400400c2000140d812417229038004c00400380b0200f180da900c240304072901010030566145541841000c800881d00602c0c1040c90074000c0d002d480c0044071075080f0480c04082907401c0c500141e001313030000310050051000b039a04060149842210b041d030b26000980f00d600201c2e01900c03035a500c48202070003800c04021101d410084812084d0800c00311200703040b040c03900035181c1801e1080028a085240d42c00f0b1045030030711000240700308091708081d140740040c0b0400c4010a01244682c40d400d424580c00001654211030050303a400c3c0303104a011408802500c000341894484ca245c0c405004016500c600070400260300b56903580f00d0348501d9004100490702403203603000020508000a002004d444800d0440000b40c0580c0300e10480281c3c03e04501d54031075010880c4d500d40c0d00c0361030000d0b162840702599040b84e40440803078003951500c40c40e13030540304611030710b0138039070781c030082042001c1c90203209240300c105003142c4001031480d0303680c48850075510304410814480c0e541e4810040038003164 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 555319577 1250 555318327 555318329
    0x2f120d0c030501030507090902010201020904060e010806090c0d06112109071d0708042102070e0606121609082b02150a0209130f0b030607030e070b0c2a010306 70
    0x2034602801107504d0b5031200d0740c0300c0c50b07240100b509481d00c4082e1441564002d4040301c071003000260080002582d601840b0081c03038001e0041c56100c0c080c3c0d50110b095090300182e0100001d07002804054003003025070b01ca1000f03101e0b0304604420820244010141e015080400100d016080700e00f20740c90f864801c3d0024146801500003012518002d10721804080000740015400038444c1060710090300d5030700746507401030155004107011084180444801a43c046600401c680400c86515215180c080c10441c4900895a11180c01c403654000291b4941d00c8a48a030b42410050a004100c07035110b283c1181050404e9a03542c04c42030054041003511907444541d00c0760b603e818800f42080401040705078000401c043e11000380c098003c0340340481952b801805d5940e880c441c1c0000c1091500f40c45002001d01905041d241c441c1c00f90300002540240640903e07061030a050014100b06030030b090200407a500001640c010900c9450140302d0742c24a42c03034150344000c1915800140a460020005041d01c0c0e071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 555320827 1250 555319577 555319601
    0xf0f071d0a0612080c15010803092101022109010203010b121b03010909030306052b0804030c031b0605191d1009030b0a09032f120d 58
    0x20420030000020090315030481540c06215410058980701e1011001c1c0c90315810550494001c05040010020040c00900805403c501a544d00c00d8030b55444828007042449030801d41c2d001000500b00310301d0307c0a811f484440d0101004c1c14810b4065100030300326000b00c0c41d4140b0b145081590041c058004400e203990012103e4003c2d440c6604100c00511705000b50102d16200382c0494010481c0b440a00c00020364003181008080d031a580c4d60a070040181a1030300c01500401c1c5050b80200c2c190030070b842e610f514518800d960301d1206025400c0c065020380c00307034015503e50000344030100c0012003880423400110701540020010f81120000da111041b480d40c00708d000e2200400441b1040703403500c103816400d031109061510f10703410800348030501400d000b0714059204200302104407403150040e80c2c0c20242c0b4010b0b15550000d41c0d130803228408445001c0c00242c08181104045183d00926000f403000b1507030036500815183c00941c0c0800c0ca4008140a081020480807404c560b9140091049581c0e04174 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 555322077 1250 555320827 555320833
    0xe01060e0a0218150405190905040b0609070228080c0f032502010e01110a15021804020301030f17040315050730050a0b061602010906021f1512050f0f 66
    0x302c2030100b1345941c0300703901c0f446008019944440f00c00045880d81c100003400201c0080c45903103043c3c170303006d95442e00403200c181c4160808000b054130a4400180400583c0340310340d0050503507082c04148282d50321099421112510100007442c01d481082c80030b01c5182042e90300658032038212428076a140348a401c40c04c80c000c11941c5402000d40c1e804160202e2011013801c149102e0341001641c2c9003001c04506004e0a0910798040b20054150140d000344201c000695603200c041071101c040009a110030f110203009081c1e2100d851010a00b400030384110071502500051a140d566640e881c111090032041e01d198030384c4e4104009007250014101c0c2c6202036009032048000034156444103198088009241c50035948900294220080707500100e42100001c2c81c280e25034070200c00c01e0420422042e001c0f400190038031000900b15000080840d10b000c940c0ca1342e42910944069480010001c0c1001c0d44c24803a031640740095030484560040c03414130700440243c14054103106040f071800c000010842d003907034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 555323327 1250 555322077 555322099
    0xc010215090a0f0611031515070803181f0204060914030d0f122406032703120c1e0503060112020304020f0a0e01081207080d0e01060e0a0218 62
    0x200d40c0c0d01c0e00765440002521071a0355402c00c00014145c00914a030400000002e010b0b199003440c0308000c0886003100d44801c14001c541010300c103809108001080c2c40024404201005000c01d000c601c16047c2c2822603030b8040c4008034000104040d090019030041c2c0c00507041c002035600c4207041018101d003e100543e40000302010a541d046222032a00802000c58600001184a082600451140000140702401c80304da841c075880240c0300c2481003e002c44042c0013901900a0141c00e0101d20380d01c0c04200e41041401009c1040d804c0280100d08015214262007003452003071140065103a0340c2d6540a20043d0303c1060940280c14040c0c0c5203003072010030b204010780c9030307400f40007400841c1000d280580c59031580c1c03000c6001860030604041d4085010080443c1d0340d03141840560485425404031201c90034413040c030702498420141c01030458a010040d04044c01c0194112040c00d1594400000d001a620301881c8070521007174541e244250780001b000e0100000300c2c8400034040ca41291110881 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 555324577 1250 555323327 555323341
    0xb011706130309051c05060106112802010c080d0f0504061d0606150d0c030b01020709050603150405150702010c17010b041e080109050307120809060a2007050c010215 73
    0x5101445064440d04108005002201c000320000b162a41e00104447c1107503100c0f100070304520f80c00c2c203500d0464454100301e40c030b114020001c50750390f844800c00001c2481180d9001101c407444201c0302900d840070b042000100b00701443c840c0700c4100a003010000b031541494033b403540540c1c4110042c00001100408a40c1020f1004216650054001c854110f4403640b000c880e01c3d06805065101300426180102c0c0042d500c0c0c1640010722103000c240e003610102c5484400351412108282c9001d90554000b0024480500700f8825594000e03000b10112012031403807200100419004030303040b800503511101e0b940f1156403c6000c0e0481c0040c030300c040303d49660400c180103134180580c2c46020105c80000070082c24100c83c0b021000003424040e0028080140a03051030755517030740104811140300440319194000184211280d80c040e0001002429032a03c801d00c0b1500540602c8607016010b00d010105522250400401010540c0c800c2000d00141c0c5031010029007002d00c00c001c43c0d280244482c00708804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 555325827 1250 555324577 555324587
    0x5061c0b03070f030c0614040b0909040602091f030c020c0306040807030509030a030c0c0504020933040807080d0c03023318250515070b0117061303 65
    0x20a0114090014001148500080c07401c16950b10400c041216010040305000040e04505c4c2a201c886d01c6985807507046a040c0d0607144a01e10820306010780a01c1165400d01d01a140b542c0c029018a0015007040030310400504000c01181d00440031038410007010044903014000c07100f004110340041c1c440c2100c40c2d004a504d482008000608500000404038100b5004009030f4140000240c222031318248a0324020b0300b5000401c100340e829000c2640d0004251516008441c104071020380ba803802c41202d90b030020050300841544030300702d11100600381000b044070703000b82004181ba84028002e151904030460f082140c10300080c02000340b403880c418046a00040c011086600340e80103011000c040e20b914a001075001050700c3c80070b00c220790500201c0720024200070034100c0305105603491101d8003000643c0c0c1035880007c10b46250040c2d003080005240200c01e004014001114017490008640d44001103d40d003604140618040702020404c840da08001d9a91720454504002c107003900b8589002e05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 555327077 1250 555325827 555325867
    0x1807030f0b0a0b130801020f03070e0303030103170c0c1203120105040c091a040e070f020610060905040e01090203120a0912170d0e0106030302010209100503010510080c0c250506 78
    0xc201e440c009135554801c16404902d00c010311a103402103446c1c02620034444407641c0143d510500060030000d44070004d00d00403089a040725448801503000f031307074080321280c0300c1e13082130b40d13201c00c076016170144031f0000d0711182d502d138010303c0b0940007841e07079220b040101c50f03070810041e000540610b10b00041c00b00925041002a805d5602c00303039084c0d042040c0c410f0200e40030710880d0440c0c208001d2000174041c030540c0102294652486c56000e440c00d5a41d101c04154841d4900e204040014982070010040e608099201e0000c1c0ea0080c400820780144a0300400d14010700a43c044440020002c0c10440c0b442d8804c0c1c88030090510705040108240c501c5d10b400e502349941510322007550900090f41d900700c0d8150f03171001e1401e08080009001c400d40ea8200a8001e40050107110b0190030000d0400d004588500c0489040e1000184a4003603d0446802141c41580040495001500030466004c6140c010400407001c1200103441d407a4102c90016204500100c1d9030000703014580034482c1e0024000c840400213 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 555328327 1250 555327077 555327089
    0x126010501080a1707143a030b060705030f071a090a080a090e1e100b180303040f0e01050a1d1305070b2115010815040603021807030f0b0a 61
    0x501c07184da1303040fa101610b00ca026030040c050001e0000e039080300000070582058110f0303220000c100740e05038608868000d4001e040e10741103002e0030303080407003101c0d00a601c12186410f01800d51401c1961907a06d007480c1d5404401030503034007140450354000b00413808400f42a14410402610400d0030064141030307030b44244c031400030b04800c07000c80e60a07a4644110725031002031201240c0e800c043e003046d03240512a2809801d00400000040001070b02c076038070394115041201c21403040036262454001b00c2c0074020141e403049a5040c00300300b200003007800c1d1541700c3c14058400604001d030075500d010200701c0701921551007026032035400300f184078610303035405002d039445000d031890036140415030f180190801c000c50704001c0401c0b00102c1c1c1502c480d1015001689041c15044c2520280e80f03580c83c00c440c030700324000350301c0d0300203a40301c0009280e1011400c1c4d03c1d0040035000e4404120981c50f075001407421441e2100da00081d07003825040105856040c040e020f044642d00c0010815503498001040103820540a49 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 555329577 1250 555328327 555328343
    0x603050c060a0f0e19091505010e030706180b0403080414010212070b040302010b03030a020102090a050d0b041502090a0b091c0809010c0201050c010204030f0b0a1a270126010501080a 80
    0x640c90036100e170005130f41108100c500803102c1c0b9484103403000c010b00200b07515070940f52546002149039405204042051a0b00800418246190200403540c01c40e10f03560303102100c51160030001d240c0c8102000f80025500c00e004a80c1c81d2400c1c00c060714807091080104504541c00707035128954000c24242115090b54100150040a548900301a8054040050629018400014469070940d81940600703050102100c14040c030310390311000c01c07a044110311809400c0b51641d0340420009280c00700d1810100404000150820b405480042d12500301507000c0142200c1c0010030820310701d080c1403401892540146080703803600c11500c854041c0c4c011805a01d05110340500c07800103580c000d40c265401c138400200255034035603c071710780000f44910001084510003030350700118a00103418060458400e04e0b80c4c0d040200c024442c03003005005801c40220102448ce2004400003d001070030042e07001c0d000c080c500700019074410b8222198014a0104003295034900001840149000700324a52015084003c4e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 555330827 1250 555329577 555329597
    0x22d0f012c130b2b0b271911040603020a12020126070c030e030142090f18030e1008090d180b0a02010603050c060a0f 52
    0x160303140300e2082401c1405008000300202048448140d11045540a640c101d100791407501c6494107481c25111601e03408020040401c000c600c2202c078940300c052100b4044070320344d10140c41d00c012a560a0b92030301c00c16164006602090780303010740165486145e42004000c0407220345d015580c0c54a100f0f4006007418040115410207a03120341002010b50340041c000700c0d049a440040380c00d5080704d4441240031030001e107030000031959000380c85480606604c403402145e644d4440d007121400c820f00412001d002d1480b00c03220454500740308070700410a1500e40d95120100015206424400c00112155a1902c040c0c80e0442401401495001c441c0c3d5101c000c24031a40201e07081004d060411441841800384101c03260505500c24000ba0719a0002e450f40312040b0080f032030440d14110100c0340c01c01c0c00da00409052929600c68010308a4110b6801d001c090100d4541001c26402d6001000d0b140c0141e441d60000e005004081c490803000300070440350740b4076042c14460003038540c000036070312402401071240c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 555332077 1250 555330827 555330829
    0x10051005070303050702030c0f03041a1606020304060609090807061a03030a03053c010e0103170304020d060e0f060f04030801060f170a06090e0f030316020a050d050304022d0f 77
    0x402d43d102342c01c283c81510404d012680001e1756070340140c410700740c030900106490824003c204044403410f107841045040c000300d55032149400382d0b0010300101d610680e920b00000d5842100d20540303464074406c09003941d40c0c410b9818140309903100c10803980d880b0b032043d030341d11522075400000302d1f0107030f10480c100851141c5d10f00d00030b000100d8158201000940c0c003402c516500d07440d5850b2090a0720035040b000c540c0360740c855146100e00c1e80240401002c000c02c040c0200c90340c00750800910b0f4020710040000301c036008941d03103080a071007500c0030034505907211403030003103c102c001d00c0f03c65840252818210010b190545004050145c10f100d072009104900c2d000c841c01611a1a41b2070103003201004c45441410003245200090049100e92241e00e40380c00c07000c4900700b4020400c44450144d9100560941c1c03a0008800c40b28828540d00d001584030700601080010000d003d44034039850b290b00e80d1501c03072525005220841d506440c5035502482d041c403442c0c80c1c7c54244490554110001c1d60700307e01b480d0080e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 555333327 1250 555332077 555332083
    0x1909151b05030301030804083702032d07050103140a0e070306062301031515180e1b04061d0103091e0318030206030f0604110d0510051005070303050702 67
    0xc6006403150000000100c00c0c8a2100d004000f120080390450341481640550100004411041d811031a452842510b05403d588080f100c032150008003611078039000040c00864010026509507403541b848440c00e40301d49004e21a01005003000e0909100302101c0082c030841164004000c40501030713542c00507000c50352082000c00060b56200710200b01403910f8460130080d00807410f900c40c80c10360701082000c415520901881b41b940c0f0f8083c203034882040c10004030040e0a8446010a0200124005400031441074040d018000300340c81c0c0303038440c49401d0061840107500f4005166085200003004104240d9600414072005240c000404503007150001c80124003801e6400340291040c0162446400c0340901d212920f100c0510030703103403a1150b0780c800180c141ca22041e444040c3d4001740074000030b19441c000c01c211641c8484014070008502c00000b4408e0183d4005020074889181c0e980c2c00c00c1003c420401e0300d040902400c944141001c0444507006010344500c0d1801400c041c2c0703580200303103954020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 555334577 1250 555333327 555333377
    0x1d0f1e0a320a030503060301230f071103121902091305040503070c0e060f031b0105070807080c07030b09070302060a110a0c2909030a020d1a0c190915 66
    0x101e0309440d80c0e01500d0038001d00c0340e0010b0302c1c0e0303520a504c0c10640126002c071740d100310001074a160106401c039a69500c80c40000c0c080c01425141070002e0260340510f4003409200604920306048269501c03030404144181c10181c403801c544401d184100480b2201d079482c94010709040d981c1c054081800d507282d00c0c2180c110300074118010500c010041000c585040444c004a1003180c2c290340c0d500c05d081d20f50042658400103c4050714800c084101c03e418907511450040010902a8540702e28220302c80d500ca003404d0b032101c0b448040310341015400f4003c05c5400c481050f0000100d01c0289511429a0005582740c41861000c009021a0664204007100d0030301c40a1078082d04120100480c940c0e4031070040d2241c181500580410a1280c080d012914025003600d421030400350040690f0700c829404e00024800d0140c080c1e40904440b840d0b80d80c0d03012902c5400c0d20504a00041544513100010894145407441c41081e06000710000d050080c035010b503000000780c0312540380c994200d03000c18407155609891 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 555335827 1250 555334577 555334673
    0x7020d03030902061204030201180c060311070c1d0c0702090c071e0506010501030c0c050a12050705030406180e041505100b040b030906100b030402041d0f1e0a 70
    0x80405c500011000e503030180c40c800c602030703002440702d02e16210410f03080e203000d160001c141070324096080c88558400d03404800b060034150b507103e142000a441d08510721a5903804943d060294501c411305d030002d184102c54004503480a441e040c411703150300041418034018050008940041042c500748001041c6090540410030908403510001c0e0038090385840090241c01c0c0460b061103c50140f442c032030310800301c0080d0400c0c098100c5000541d503110801d0070903d0340c0300801a041c000e20020842c144000c000411060f218200948e02070301440a00c01800d170300421244007079104000c007180c009a4512064080c3d000c000416a0318610500e082424642082d0381050010030040b0f00c032a0001c008501540d44070085400300c2e62820300fa5140d40f02103014000706118140b001c900141810340006c00c454019001c074103241c00071450142e01d010600346005015900000c01e00c00404412000c03902441c84141c06803c40342e46075118442d130700880310000754401011000d05031040c501c025000710481a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 555337077 1250 555335827 555335839
    0x60f02091009050f0a0b0304060b01030b0901080a050c1816110f101815020c150f040b09071a1305061303060605031504060b030a02060307050a1d0607020d03030902 72
    0x201c40c0100400840850007200d002d0102850322419920781000304d28101e803042c0300c83c1e520755620341d5a028013501c20050410705242e21820358001d0b65568484c80c5000e080700300e001f09408040c9040241c03421000d040b0845c00307840c0300c041201e0390721901c040e1617a04c00454501000c85401110040b80e00410708a0128442c2c0102c0c01c00700c0b038034070020030f5400c58103103402424440140015101030794480079039401041c450440e0780007500010a900a03001c4005c0d10019500b2103d035a0408510083d411a680d0844003401d000700b0040101000416800c07103500e100800d4224180307103480342d0406901c01040310040c2d01160394100101c0d15811000130f003101030019516000345201d03500100c44a030000f1609141041d43c0840c09040005056545480c058070018590303d668640f03a0060415221507034250003021400000350300d4200003035000c0e503915034070107a44021449008002c44e050314040748540007102d88944041e5039041c03d503612140c040396580b44402d650f240a40007049960b82c000c0d0414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 555338327 1250 555337077 555337099
    0x50711030703050124080d02070501080424091e02011d0a1d010302150310090e03090d0813050a0e1b1c1a09073e01020301170601080307060f0209 64
    0x401c81041e10300070203c009021756001900d0702005902c4501c80084140180c4c4034650030400c0750b100303c44c1d01c3e401a01842240700c0303c0036080883d03044203c5001504503801d0700c40ba1114200180003d10110725205d4003001841e84c0346903030008203004581941d0100303e02880c0f0300306e551a0b0f00c61903424000e101d1810403200181d1031401442c2c0c140030900c020392259000aa1002208001c80c040780d00c218002c60071038004074100420b0100504010466640500c0140310a01640d01d03000074515602e8081c6001c25103031804050f0401142446402c40790086507034520402c02c600e085081e440c0c0185680410419041408100000d0f60040c0072a8284020300d00d84c00d40f40701320301640443c10a000018801d40020800014040819016612480010307401250b0803400007081c900c0b04055840070102d03030f0303c043c4000d403000100301705030b0240c20b000d950010041043c5110841c02150030315407440603182d80e44c07405100b10303180d0144d1038019002c01d4441e4036030958a2110707030480340b000000501d080203034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 555339577 1250 555338327 555338351
    0x6101112040f030308060d03120f06080f010614100206130f020d0807060f0204050108071103160c080601290d060b1209061b0403020f04090204090503280507110307030501 75
    0x5075101c1c0c48161302190100010070028100040d00201664050311070966500c041065400104010754402e10b289507607503800729858a0500141c0c2c81c0b042c80000110703c903400c085800baa074071422808030740304014aa1403a03180e10f4020401d00e60060001641541010490603c010b0784203d041c0c0c0298806443c498140c00c200108015002d19406240100b0120108c810884224840d41c040c05010a00820000390b10505c242d030268030050340d1009607401c003541c440f0007040410745047d081f10304030303085d2070207211130402006090b005050700a40f85410245840401480c0f440500100ba031400000802c0e1281c0c41c03460f04402d0007081c01c0c403050380c2e449a0720560841c4074034040d6049441c0d03010704c00c003045210600412007007001e549420411714181c9107508006620010300030007500325440d0300300c91000d0707951886000c3c20103000340080c55680200d80558959002450380c0102c080741e8a01100508551000548110550000d89000310045583c006490b0441c0e03a48000c00175801c0030195403034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 555340827 1250 555339577 555339599
    0x10210020f070828020d09050f030f0105070917060c040b1608032404050c1603271a070f0b04021815040e1207030305071103220b030610111204 63
    0x100071545580c1d0b44c482444000c226220f01240420000007a14000c0030f00c82440c2951665604d510000d040318494907100c115107007940c41c02c80b400004514229400c00100c0e6001c00342c0b405046698014106903c1d02680c50f840c14000c40c0607641d1f4041c8080340080043c0e180a4100d0311036504004501c2c3c4030700c0c06403110841d0780c245110020001020961540d01814a4010079000e461b00c1464603040030350300b4108001002941c1010350810040c0c513070003851310048910000d0304c0c01c68580f095111078180305000300e142c1012400c050003604200440c101040d44500184c021a92104034a0302c9900c0714000200203107001d49501400d00001814088800400a400d6011602c16030f8180920315a000501da12542d0588424421110410010000a110358050b980c4034241e82001c030a5000c144c00ca00340f458004c110780303c199110000000403d4180340e00010000d2506c00c01503442e62400301c001c070b03005891a03140c06080c420485c40f41c200105c0180300e00013000d420742000380d449966030061012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 555342077 1250 555340827 555340867
    0xc010e010b150702010804061e1a100503010f031e060c032018100c0803040b01061202091804060216050a060b0f10110a0602030901020a0905040b010210020f0708 71
    0x44180000c00d00101110b508105480505030144c46010550380da940310340c40030b80340303040440f005940024924001130081c0d200b414807510203841901c407021045820702401c80d0107280e00906010040c0010404030014078808800d0320742c00782250074070302e0107040c42100003d10318800810450402d41500702450f4190f10a09000c0e100c20110000d01c51800d6002c9040c1c82942c1d80c0503003c8180142030042030821040d104110745042c9081c002400d541c2e01c6500c600d0300107580894141c15207600411595a20005c002d03258840030030114648821080040c144078550003000c0380c9500e034400090240003442d4150ba041d44d40c1030307050226460543c940241c84100c0a18221051494004401380c1c90a206a8900d4040009040b080c10184441000d80c0c1c1a4917445c16540b541c4a0707240c0f904001100e50000e117000d800148001360725074504c14030241c0208402c0e000300b4004d91030003407000c41e16a0b0004080e03007106000c510040e5154196800013510b40b1070301a0203030640740c002940074000c01c00c04071549 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 555343327 1250 555342077 555342079
    0x1608011b05030601120e0f010203040312050603060c03011707091b02070b0f1e090312120f0415020f09120609060a020c0a1104020c06010306062105060c0703050c010e010b 75
    0x400c01a200d40080d10306000c203840d000c3c0061154100801c2c468020f0744070a03941040e59044030b01c00c1c80d6a048813402e9030302c12513003100010041400c200c540441c038000c45400040c04c4018059901d064040f00f0b00c280070501ca0301c01d42008a84982107082d60501011020780420182440b01b0030080c0d03450010548221081e5005104c0d81800003501001c010540e01403080043c0440d2500d144035005112400c4150300340150940100042103113640d04204003943c2c4d100e58005140c40750211424503000d00340080c15042020342c000d04100c000307040041008400c091651005855010100100425020340300c1601d80140342d0074044045914001005449103060300100c41d1542c1e282000da5060f0b0040b144049550307480303c0320200024490040c900c5440300c02a0005080c160207100d042e18012080c0d1003982c0440d034a2205009000080d0b008041030401c1c01041c109054041d611250b4840000b03007007505090340881d55404040c421001c5400c80302e01040280411078018541c14000d01c035200d0f082d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 555344577 1250 555343327 555343361
    0x504110108070c1a162d020f0d030501030b090102030402130c11030f031501090b09040f2403380402030705120c2d090402060f070803040506060301052205160801 71
    0x1726044510400442c140c5034180c5c0041e032582c21800f03001e0912207114905110a6009080481120030410064141d041d02c0e82da40104442d4903606000d2480d0308051b10800a99004004110141c3c860741001040c4042d4500001090050741d0001c450380300765100c108845000005110000562400196026541d50002c841c0000b0b200001502c680740140f0541001482c2800f6548840c42c103903000325150410a20007103050f440c0030012102c0700e0003405903041c00340c0440340184103002c506504140f00a002d43c00c1c80503002d00d5010b0a1303003041070002c0840301d0024070400140c00c47d282400408020305019200c038001c00303540d05c6841e850b9401c46070a6401100e00b107603944c50200f0440c800400b00c000320300b5010040360080080c0a40000f00801c02c0e40c12a0f000c00c0100e001300d200e44000d1008a024800060700ca081a290850500380e01500592180c0c3c1840c05100c1c41c1000040d00003010700310101c000000b12810b140141c1003c0c114024014400400d600000b10014190000c4034006002c400c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 555345827 1250 555344577 555344611
    0x213180f120e031002180a030305120a1e0519020c1c080c03010b0c0f071502060c03060307050d0f05011a0102161404020a0306051c150504110108070c1a 67
    0x20855420350b118907540e078035a0207500e4082103d403007980107050fa200c01190140d100964000440e200506951086002130800100d64400445071191140c02c0300340c45506110307068401c800c4030410b0410034014000c00d07680d00c0129090130448500c540b4080c040072815501c3d4030380045042d4545c100130b040400f6035101c018103074810340e1207014402d1050742060000e90441c2d080c0703c0d0301042c40d0048601030881c3d108000010910748010070001d00242030f9826040e050440c40f417402801c0410146c07041c40c4081051061100c155400318000f0300340d0700151000070f403a584038209024400c1400c84090004d501e0100364919081a91001080203842a02140c04007414550300002241c00c51058000c0d04214a00c0c20280e031170141c00501042c825850f011032081d840343c00103000354105001040c0b401818501309400c1000000540c0005c0003c2c0c0410041403030641c0380c0241d0300000514017410400c50000140c030103030081c0c641032440340c2c12001602c400c50780340e2082242180162400319120b00300e444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 555347077 1250 555345827 555345863
    0xa051207031a101205031b15090706111c030b13090b1509060108010915080708030c010e030a0807030203130b0a060810151206020712020105150a0509040213180f 71
    0x4d0119900381e8410700840c40c2c40b203400f44a84441401485408003801100c206002c541058121f642c00760780c2c0040a0310340c541c5018005040c0e40341078a030440f0144c0080d11426882c5895620030300700d90b030b414207020038046001c00c00100b05420032040fa5189500d041d2000701400b0b182440e25200d00078a10702807024500c50001c00c82c001c9001c81c0d2a40c00190313000e00500505a4541101c20b01e094654864038885d07480d020507034103108407a00032100560010550002c020001d00502d4509524900614a0171440c41c0307006114607001801041415000000301d440c2d851581c1c4166401e98111810844504280d0b144502506080c03103402c400c0d2080344041001d0443d1441011f4810b4810b00341089141c0c81d0604441c1d5a00d001e00382511841c2d824480400403680a04070000d11240c00c0c2d000203014603101c0c031840b40d80f030101e0703029602480c0d03855000c0c03000740c4498101a4005230102d85a06012541c0052400074110301d43e0940d8064403202400801c10408031044021f1702c1c03060f00c10980381c1414003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 555348327 1250 555347077 555347099
    0x180f030204200315060c0307060f110f030106031a061b0d0509031f11070f1b030c0e131704030c0806100308030703060f030b09100b0a051207031a10 65
    0x58003050b401c40c00c001294500e802250349514580020381450308064581c81081d003143c020500503500281c8850a0303200c441d86d68820500411030441d12542005521034070100c290005008403024542e951100c2c0700c48030b27144003100d40d9200d00145500d6898040800c41e1400131981c0308005124440c070412103803018054016100e55000103001030032940c40010016005900c460350040c1403964510034622088040d50040c503080e4004c0b000d801c503000d610700c1c07d00c0d046a090280d844e12104140010300000f0f01c0c3c880807508549200345070041c50340b11110340b0700e11207210010084c904402c440c000010040c591010f042168018419130340e803596123801a0740c82d0001140d004000380d080c018207200040d1200051a040042c9240c0060126115214411460400d03007081e40e074190700d1001c001d070b0084204542d02410b410385009210280709100030400780125409050f21440d050000c0c240f9680341000580f000355080f0a030740c0f120070001e4100e007034268825540114018148440403032112245 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 555349577 1250 555348327 555348371
    0x30213020a081005011d0409140d08070e0303030601110f060103110307061404270204060504090f0b0d02090615042c1e100806042003010b01050f0a180f030204 70
    0x10b8450b00d0300a1b803034015a603c0180301c03e1010b0b6010344c0c3c680d011404108080940c03000c030001e807001007141501210b00a403c2040c001d05020801c030042c00325020685003c07056940002007803c0921300c0314400507041d0705080300e02c001c2900c5481204000014040c05840383da160000940980b1039803521034a00320f680d0501202d200410301c4081100b0044041400450341001c4240380c0383d05061204030b6860010381e8072540c00003000603070101d400d0200e00041d00c01c3ea0704440f0f402c1820050f20005401007056282c4500002c1d211b0294000082d0403600c81100e024402c2040c04400c41d5915182c9021211214004a011982d886240c20445d00410b500d0035003809020b0314240d11100380d480b030051009030311000b0101184203ca0340400201c000381000058080c0c0d10500101c801d541c0380900d0401d6511410042d01c2c403da0500c2400022640c00c0001c40707d1024141141c03d545614107003064420b20307400ca0000c5d02010080c20f00003201c8069003038a4064070b10854003071100c4c1140c070801c0343c110807070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 555350827 1250 555349577 555349579
    0x90506030702150c121602030c03040b030a050609061008180d08011e030b0a090609060501080303180705060405010c0c0f080f0f030a050a05090328110d030806010513030213020a081005 81
    0x84174042114011075440c91251402e445c070440740303030503e50003c1a0440c1c200380d03c0400c03000710110a004680696004495005000b43c0d142070a03032511100103901101e42d1800742040c01104800701d200007440103419811000d03070324100c503002c500d100001040801d091043d03280c081070b0f5252000811106500d1407046a4000703460305c000e9111101c929000b00440c1a04662150382d51984034005151782c0605402800080055501c03482d20310104101316007076104c940c2c41ca4100803000e111690b039400950301501c0082c60701510b01009403400741c448503025003104181d200d140c24006180c5c0341c001031041c1755101690660320000142d2203801e982e0300640720341c3c2c00810024080345030244d00c100082d009030300340201203841181c81c0e020080604807078080c03d202081403503a0080e050000031040e42d12421015035034071001c602e194030010060314020702060f0420078000742c1000a246041001c42c0655001450b10559606064801c0c0095215026002c00725031104002101c0c3d2440610304070071210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 555352077 1250 555350827 555350857
    0x110a032007031a15030f0d0e0a050d0606030215090a06050708210702010b010c0c090924020a0305010905090c190b03130c3201090506030702150c 64
    0x11000c12410100110080060318510401c003000000c22100346900074150400000b202c8581454409804602608188103009501003c01080c80b80310000300140d445032030703190040301100c07050001b4156260660080ba031015907241440c05100840c0e001d007048a100701c030503030611081a055140140110009940e10805035107080085a0281c1e00400a80c2d10401d1014a498950001c1e0552104c3e000d00005c042004801000710305e80c0c091003031030203407102403c0503411211103130b40780740640125025400b125a21100c10000304010b14420030031107610b24054070240d0003502034840003500301cac0400100080c1008000244104280f044501514141c40501440d0030b440040c072121941035164280d19124400c0c5c0051041d55250145000c0c00d55401920104000c0d030800740b42c1d9000c0c0e50031040000c50400800c0004610001d0000b0300206014041103140c0c2540c401a950343c00b003035008580080f030000400c8540e50b4082801d0071b01a8102c08105281d40b10009200b10a004105401102d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 555353327 1250 555352077 555352097
    0x161e14060d020723060a0e28050f0d0815100305090c1522061d0a0308030c0904050906091209030a0206070b070f050724140c0406110a03 60
    0x42480340040c014808650320151800000341e8482c00040c0301d00482c0c00356251540e480320103503a0240106a0410081d1101f07026000d150b0100507110034000d440202c51f041014108100030b411280b00303024154100041d94221003c0707030381958440000700000c10000f81e4040c00981411044d600d070007824007002e4000c942210413190705a0080c10043c200110601c2020030b040c001d60340d0712901d0031543d4405c0d442c00743c903a08010040400f28100d151590010098a141400704591121005e68000c6598880c040009000c40114044101c0c54002402d100c1001040000001c1024020100000d05036010080c640d103603607181d5214801910319034555040000203015030010140600801a0002c0549008207a268001821540007074400c0307e60b4001c000802230481d81124070708041894908107a40707081310541c1d601c01c08001d503440109440c540020040400b410f1984600f02e1000a1410082a401d03e040c2401c81c541280c401c00f0009034000740742540480003c642a111a549520745075440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 555354577 1250 555353327 555353329
    0x2100b010203120412090305070f050114030402010f0f0c06050f19150603020903011407110f060103020a0b0c030d05010602070512030909010b0702060f13051002030c0706031d161e14 80
    0x904880d005c01d00c20802007076408008501c003031113048010070166200410301480c044c0054041c04180004588401041c01040050f076041880e61020710a01d2a001010b440b4410040e0350303100700100050170907072804c070802880422000b45140078060442045070800c0d0f0b8440312a090360001ca591414820000b442045002d020350080c2c60700c40c10040001c6440755401c3c0ca000100301044611100050f1451262080020144444055050160064180c5606540210350400d90b5031281c0c56041000140c0c8402c814424400e59001082c00d100c14086035075a901e001355031341914041c0da8456101c844803800500400400c842a0000140032a4043c0e86404140c0c0e0441e0040e280aa8101004001140d180c0564600801000340e0495042103102e04007801d00c000c001008418200359030041040040c02d00001440f6400c80720907190200e050740300c1b4070801131824808000e90307206104111510082000d048200780544202d0724620801010003006500024901e204003c0c0403240d2040148803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 555355827 1250 555354577 555354593
    0x50714030714090406090e011a060c030418091e060c050c19060b062205180412020721051005070c031407020607080a11060903041710090302100b0102031204 69
    0x80f0b1005200003051660f40c0150350981d10902da0f2448142d42d22407a240000c285c28415040c21181584c0e01c03804c1c072400da9041aa41d00c84c1d0302450303041d1442c42c41400c003440e58039042444426440100380c0e01048004400304200c4032001012500030382000d5007204410b100302d0603140280800b40040c03803a0142d50342c03004035030319452009603646a2690000b40054555500504501020350081a0608040800c0e85c10041d42500020302c03502684440d40100500c855515800a4000d02d0300820003290a000340d19090b8a40d200500494030901c40404400c1015146420b2501640964094400d0985a081140e05c101d99140100360411407250119110720404040c01171460100780c600b0f0702e05e400043e581c2d00440c000301e0341d54100107802148503034422098822442039074000e1050341010440303291280a0f5000340f102080340080f0300e0035220420090303089500c04044042101c0103160034000d45929852110415003828120702040300c0d4400412581c5072001a03400c2c1c2c5c5030361100d69600e55 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 555357077 1250 555355827 555355837
    0x200a020603060310050f01090c03230603150112020a0f08150a020c060c0c0c040920010507150608060f0601050406081504060b032703090d05120706050714030714 71
    0x43c161013000b10b110354064242c49441d018038004038030840e0542c541044903041e0b400280d140310030907062a07121040820481e0444444044680100c443c1b5581c400100b49040c40b92005003407160858000019040440c908100001e0300a0b40c0844c8981d80703412500c0d81410481c82500060f46c4031400303580e103455075207100c0e0750031809058000d4502142000e1907850140e0a136400c001100e07000074040710409003017141c0003060000303640c1403020380b5250f103810701a01980704203800c101c8000c1e4804829680720708102c64403240d00c1400101d3748a002e0681c07000501040c0925400ca12884010490f8800300b600f85600c07504051703480500c2c0605258084405002c0034000e031403030351140e00d1242440c1c0d0340e41c011080078019200405071a440e04c01250310710b00418080c0070030800c9030035038603100780c95010040342c284680a03908000030400e10301c0c02c10b02d080070021405549042c0820903108000c100d0300300c9030060070990760355040100c0429030325410741720035608000810091060010032044240141c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 555358327 1250 555357077 555357079
    0xf0d0201170412031b12020a030b030a0b0f0112120c0606052823060915030108010204060e100206040f0302160801050a110702280f1203200a02060306 66
    0x1c0500da1585210340400301c002d550454211806109a1500c03640c5440341c1c094018060004030800000d49a02814410843c0032070080c007900040c0411341c81e0f01036080607510300742c040d0446034a4072050178081c151900c1034400700c4805131030200014018040b4118640302c150424401520058119004d445036100e580d4120b0344244c94180018190b602d2880000c032540c0041010340302c3c60800c0011030014041174101c1007026444507010403ea21800260400180065410958482c1c10500007201b03507044046503500742e000000040f8052074190017500446000e9290001da42c5c00a00400202c800151121401a400840000c4c0452038665103885402d010740180c40d692402a054a2a18105a003184030340f0b1b03441d14240044c4210b10300c80c03942c0c60b07407103803400030300300300e003075400036800719a0030b043d200c060341894880c3d01000e550554800001c146a00645444c0d59903800e0f500013801000c0b2040c3c0224140c0722003010315800c400c0200f240a607428002d0700c11a4805d0b800c000d03450700094689 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 555359577 1250 555358327 555358337
    0x6060f030910060e0a060603110d02070c08030c0d0207050301021c02071406070906110c011e09090f0903030b041e110c0f011d0d080114010e0310021b0304050f0d0201 73
    0x424403003540301d00c001a01d2003190f2411a4a0320140702d105403801a0301c072600b050316081182c040c0780107200c22b80307900b1002d80001581e10159401d00360714854071703500701290034040001d01c15000c403000514840401e4694080c1c43c0d044d0b0b81c40e000c1508034010301c82078810540001a001d079556801c0e5004214103403040c10307840b0180960014039460030f030b030407540301000c0740701c4220500c1013a40010100c0440b00c80000200180115203000070204111440c00b010004141c040d15420305014109a2000d440003d00c200110904000300e000a081c84080903004240343c002c0754005814280190054440e002c400c0303131076070034500103040b00500b100c0c500085504000d010b407000031039081c0009280040c40000114008195003895080c00d03080e1141c41034076502c5080464001c640000e0140d04540d05940d44800e24600c030300050700e40030201245c050703160040d2041c2c881d54001a9000d0480313000c2410300c014011800141065583c403139070140326400450422100070900c0c0101484c55801e2040c901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555360827 1250 555359577 555359593
    0x5010c020d03050d0c09080f0118020609011e0c170901021e01060909060617031204120507080a022b0804150902060703020a050d0807320d0e1506060f0309 68
    0x10448070171011040015140b03003000c100004041020710010410310008011800c54030b01e0460584081410003130142d003004c00c1c1c03500c06a016050083c2d04501c10001b9004c0281c00903c024150103030104100ca4540380c615500c96110a10010b80d030042c070041e00180325502c1e1a13460040302c0c200c420740b1400199210100840c2c1b902c060700940203004c0c811000070403a00c0c244400c1d0040750781b069400070300e580c0c4240161000603c0c0301d40c180d50415000b84004050003a03101081b19903118060300a40485000920355450b1030740041d05440b110750104d441d41102d100782800c450100050400540004d90000101e000701d503100d1400f000c440307250308001440c1c84580e800310748107400051050340580c0004914074180b101c184003011496100381b814105501d03001c0c001a1064410f50072015000c8400e0086088440484a00b40940d000c218030303c80d01c030f82c000140754001d4904845012028003c11085064540c0c00450907405064020441414410048004020b40c2c0004106401e54494148 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555362077 1250 555360827 555360847
    0x405010209040c0e180f01030b13020d120e091003060203151f0e0603160f020a06181103070303020705012312011e0e011503140903040314060105010c020d0305 70
    0x72407144101166141c072913400000c01c040250400c0e00304194151010280100803041400002d100c0c192540103503403544d992141010f030b104141d03a21200039081401d10180c8404d0000c40303498284107034216602c0c8989074140c1d034140f040c0008255000c9a1041061f80c09100140d225006540c0c4001201c0452496040d83c45c006408a001010700c0c03d011004ca500300d116442c1c2c040c4401c003000100381c821520f1400d19085c0e803020345000403a550300708040c0c0d400c1c80d45103d10901080035299003006051140090544605e200941d4040c0111000c1010900b100ba00f17040104400c01120740640103050010b1030000103480304003007825a44441c64009409040070b45401d40030b0001c0341d08401000041d0360400102e00c103854001c0e011001e00c00001e0310200240108a0b005906441510140c0c0c401102045400e41c00f9088800c2d400d2a0300102c0e008020084c00e001000d003003200c0c061440178050114500c4201e4541c1828003a02c1e00156100009a015040c0b4201d400e80c000c0c4249045868441400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555363327 1250 555362077 555362081
    0xd0e1c0516030b011e15050702011b0605101202030604060b061c0c0e030102070213020a0e060301080a0605130f0f0f1b15031107150b062b0c05030a05040501020904 72
    0x2e001228905038420051103540300020034524400620845421058107180c0304c06d28121a00000d40c08102c0c00140400c00c40e4860482c1002030320b40050301568854181c6001c030080e10003103513107140050382004000b0741080300802e091542a00a805070182e0f03280ea445200140c812000d0700c0e500040d08010116440c0030303459039270704208405640041c0c96000c0040007048048201c807024800c0c1c0c01440400051b9840759440b50032a05140b030016507802021000f0f80d400408c4092166011a0100001500314404107d0700300d03c2e0304c82d4004000954070420414a2845140409000701411039800c20025200410407a41c490145201a0290340c0d00e80d42e102520203070400703200e4045800101044403500321000a440841d03d03040c02d01c2514001044c4034294040c964001c1c00c181c025409036080e10809510426440d030001d0300159946003007800301043d0b21080494140407900d0720480c0700d10385019106e4405404d03200d5a0b03035441d503140d92607040040e041c0070b0000d5130710355404c2006503001d035924 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555364577 1250 555363327 555363329
    0x61c020d1412040506220b040627030b04031b140d0e12030a0c15020309030319140f2e030b010e10151107060804050d0e1c0516 56
    0x346001c20268188041c000c0c10b141d01c1010320311514000f03120034405984d0748400d03107960046c2c0b08542c0700704140c11070050544045661019803c820300040208125600600840b0703001c51920f241c405514004116801c421900d21003d01464011404100028401c4507896428010311041440c0003056403500c03410ba12010640800a901c55090484059089000c401d0400300440724421524040c010306600d0303204506030401007101880450301000000c0c4025031000d1400d4400310b440303260111850b90380c6d90058800ea0207010b1b542c1041c8607025094041c26080104040c064505034503100d11030007074078030f018011440044400004003030024540803001c00481c0c105054820032407860510407152041a044000030085030400c000a964005900700c08580280000034504c4850040413a47c0c1441403565203d68050107000089441d44000000c1c0141d0061056907004040740c0c00545000414a8425820080170103105204032074020f01c1000c003600038026200c0059154096199082071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555365827 1250 555364577 555364583
    0x2010c0609080333060405011803050a0309050306090106210303090b041101030b0102191407031a0103020109091401050108060d02090a051005030a08160303020d0c0e03061608061c020d 81
    0x80d560074544d102150011050002064040126801510f07400f2504622450180034184030112011540d00290005c0324002580c001c070036604546403a14004100034918450a1310134230605d804503481c00c106100b1f030001c8440711100c031a04060240a880083e1001040540600d40c0d40c54110010510744007201e0303c100e10441d8a4400999050005021503000034001c0381198000d810201e9807400c2c4076000c103819a00007200c40c9401e00f4031545246040d11981000384401c10008103c03c900c4070f1010064144e0f03100b40ca40700c0c006a00d510091084a4030fa40020040240e0031700104825400350b21000d0b00010050948842540c564010030900130003602c00341943c0b682e40040110751940c80800e01c001d4102140540b040c59070540310620103000d565095940c20b0000516002010300035811110000f001d03007800d02007041071010140001040502090081c014a000200f04040c410a681306055040c2c5540700d0a0316014103222000c4aa407404030010840030041d40e0160f074030f0980070200c8600c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555367077 1250 555365827 555365851
    0x61706060d0c0e04050112021302090607140601050a0b0703020c0d0201030608030a0203031909020307031205090901060f11060c0a0309050c211212060405060a1710062102010c06090803 81
    0x1500713010031504143d01c031402e07058101c000200188c2d40c100c03404d0103c0c05051409611404800001004d500ca01c2c0e030000c00c0c41d03030741030301c01400d07220701155840c100e90049031030118042e511080c081d080d104444000340160428111404246441450606070714010f150000d0156118000c2e586151300007a01000580c2c004010040782d02a0626213004142d8080c1d001d00040150f0343c00300317546400724000105180d143d202082c400500c100f0513911018001400f034845940e41d12030103084111140c2400d800150b185825400c04080080c10500503820b03e440c8901d0168140303012402400b807100e040310103010b01c0c100d6055a98440d0080c1240c040c90740351303054807803103070090b0246010707220100d141e01c206013441410802024a91035651012050300c0100305a650100042c241701c406400000b09403202d08500c148010001803404050b0403255070800c500c94441c1e1040d444081c0c28416080e03448101d100490043d403103050000183c0f4070506010840024965070001181c00488030940840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555368327 1250 555367077 555367097
    0x301020d0e011a0904080d020c0a060207030305060d03210609020a050c1c02070e040f0b0c091c0c1e0b0703051201061d040507091d150a061706060d0c 66
    0x7440a00c6804115030041164002000d400c40c0800c1130524001c0010b40303105d001040104030031035240c044035100000502600e0b0b0417403030341c6401d8009420140d410f600003890400010a40c0c01c110083c00303682a003584400015402068452002c81c110b0300100d1034042e212540003c0300242e42c0040d000e001c0507601c0d0562a48038904020340b51180b0908818400d405200680300a960007140b0722066031041c1c036880300d541d591404c0c0601004c18208004044811400420444030118400b40441440482d181e455021a410000003c1580b43c04090681200d4a0080025540101e1a510312081c5034984c0d1241558401021503250004101900410400541307040c151140001050142846043c503501d441d080b4420032034982070b1a01905e000f05e83d84d5022a10340d0b03000e00c40381c2c070086c4a40f0b40805800c2c0384804070542988800c0d02c000d010b007084c1041c6c0c95480d103440f040407001e1f5845030ba10090800246508a62050805802290408810000d02c880c52405004605001d0456160700d000c407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555369577 1250 555368327 555368351
    0x1b030c030609010b09100609090b043e1c090501090f0c0305060705030112030f11011a1305190203070e090403020105040b07020f1509031224010f0c0209070e0301020d 73
    0xd1708010540c4d08005c4048200344020f40e000a03010382030380c10a20340051112038031408a40140700c040301080035420521007142400744c1010168103c0b98000e280c4004400c10140f11603254051002e10503240450301c070701c20701048120792004131213501404c00031a2405142d207590b50380452151040c0c03007051085409005001040010b207802121034507140340b556140905101003801a00d03030050030000320240799440c01d4419402c031241c694280008202501141c0c0c2e131000d840c51050010f9000d00300868481d0303a68002480f545200e0849008528840465410510000d5000401c0401400792017183e010117074440c42c000b41d100307600c42e4000148600f05070406820b100c1d0010a0013045500c00c4120b101c0403440814410b500803541c2c8206400d584a891065056000ba0000ea2405030011004c11481c106031303e041c10018009884c6601202102c0e9004440042d41c40041c803011540c1603140c00014200f01010982c800703182d2034408641c40740c581c0040d082e071340217149003089036480d0307019403c40d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555370827 1250 555369577 555369589
    0x12040b0915061002011d0a02150901140714031b010f270c0506031510020d0503010b0702120a120e030303010302091f081212010905091b030c030609010b 67
    0x21144103801403100407100031014507035480003000c450003220282040344042d4000d400944019004450784450300c3c03041c00c0d20960310300a00308240d1141210440500c461246001101c0300070006a54140d00791184100722007003a0300c0b45104940305000e40da41500003c60a0019100100b04012174600d0380c42508926400e43c0c2107070003c001e44524120b4104001d51504204e01c0110300703d008607240504042c100202115450361150b030304107100004100c6d9071400e410b409406840f0072502101c170140c0c2c240d4226941d1b614140c2c420007080d002c01c01440a1400343c006015050f100510f0308090186075404142461941e074011961204104d07441e07581207401c41001400301d88161300039421589903400056a100002c0e002005011a08505840ea04101c100081c0502142c004440e181d840b00c01da8143e065101d1004076000245400020030300318168003400e401175841d03074020842a048090b244084c2508441c07035690620882e0550000f903101440103620568540000044244028007030040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555372077 1250 555370827 555370831
    0x180f0e060613060f12050c04090c170c1e0a030f0615140a020106080f0307050c04090503071218090212060f0d0b220602090a1502030d0b0a030812040b 66
    0x40300e080c0c2805000381050310402d49a048440c0c510340102c803c110203030140c9109525040340ca00d51402d003010001300741c2200300200304a45a4181c1000147c9010404031044000300030203050030b03030020012a407000d40700406000c101c0030742540c0b1203040542c8a82296603610410000011030303100c484d49400c0e01c005101c2c0d80c0041070402900f903103040075444014403501800d020400440070110360065668404d41c0002d0240408608a41e104041c02c410b8603900e411107441141c00b8407400101c4141410301b4010440103541c48401075050103003580c1d90114141c0340c03036182410441e81d10415200700011010050043c40c0c12000140e50302d00080300001e4440000f401a401000320cc4c071003024030f4440c45250b50708160400410200742e200c10282002070b020000c08413901612102d81d02d0103102843d80200309058040b1081d00c522a40d03020840d18a0228050b403002503002032003903c40d160300d84c0d0001d058142004100750112170700d960714012107030450465440802c0380502040104000001ca0f16 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555373327 1250 555372077 555372079
    0x4060b09010c080708070803190b010905061c0f1803020105060301050705090d1502070b07021603050615030c10030227150a030b131e09050606010f180f0e06 69
    0x2450102500d0001e403618010710b400910050002401c2400c0c0a40c91055940041d4401c0541707642c3d041012a501d82145581c074460300c00c0b40b0300450b15003258000d5a0b00401c40d0400780003d400c003540700e8080714031a9100714002c503805440758040152501e0a124010070010440d0014401080b5401c5c003c6c01c40b18000c00d15070090707240c4001d10134280d0308041901c46848044420610319105483c01848001d050071425400600201d42c0c04104501c440c443c611460176035084890b0b440c45150071240d008000c1c03002502c540c2010f00800e41002d000301d0040c40c2d501001c0c00b150901c41c528008550081d41c0c0b460b0001c0001d5000c124500d0b807811031200040000c42030341d000307070700215208000350b224150309113200c11b10302001400950f01c601a03000316a06000082401c4959014400404050800140045d5807a598003014000d03a080c01d2150040322038100d0001c040c0e5a0740c20b4015940810010b00000c2401049210b0b403d00240045c100790180c400d603c0c0d442c1e8030031715292101e0340d8014060402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555374577 1250 555373327 555373349
    0x40501261b040b120a0f141c18120b01080d05071110032c01060602010908070b1005030615030c01050a0203090409020411040303031e09050d0809160e060406 69
    0x20010420800d0040c2201102200c1c000b80000d007036800240000580d0360750015502482c0198018400c46c0da032004800d0b03004151045001918101c15030301c900d841000039100c1b0342e9080142ca4000c1c410002110301105c42822031404540f9543e2611210410b610300719442c070804401844410401d02500d803016000341881418501c0c0c036914451708900b6014214050722910040c0c8000622035040b5400c0031a46290341d0407010190401d48100c1c9202035641c5640c0d40c00c10100282f05441441000b000d2500003803180d04012559803030500c2d49070054021141785400d40d1011503a90340c140402402a00b0541084000c20288424075082c0940c6d035482c00e06001c41800011820f81e004401c5030101d180803200001e80d20f0303603440010300070070003400100c4426001180100c1095059171141441c203c004030078a880064a19258003951070050f8000c0041c0c100d100b215043c01d0203000c043d504080711105075608000c2c440304200c4109104e9009009a02c9c0e050103109041c201442584041c094100340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555375827 1250 555374577 555374593
    0x109020a08060f04080705190f060b010504120204020702030709050f22020108010e06040f1e06120f080c0f10050f06010f0f0c0c120812091603020d080904050126 71
    0x500700749070f0701c01480905641c4000456200f00b01042c03060707074016002e0015041c201c203a40e040516050400d004111881480e05000903815800341c82606d0488101c040310124070515942440041d400c841c0703089805100702140801d250707140e8010b00348140720070355020f1414682031468101000404000240d00414540e03142c0150364000b02640c1502c503c0703d01c44429440c3d100c0032400820010021030010707840c00311084e40503200d0007107215130b0300c0300d104051010603111203001c03442602444c00104101206001540011002ea000c0c0104c00640f006880c0031000b0405681c1c2405442c2e400c10a42c0b5a4410810910f010768048154000e502071800c0f10703a1007000d40b000b41650b54206415828800c2050181007080034062011000d052100305a034910308c05458040d5058200442a0240005040000701e0041c40020041d001c034510000b01c51131203185400b44165981322071020303198240b00b084400e0890304c0341d009050090a401c0300d510300c0703a050190307040c6284580b45056000e641001d49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555377077 1250 555375827 555375841
    0xa060503010b030c0a200d030f050c0a0e031009081218070618080102450907090b120a0510050d1b030507090e010b09010e0a0e1e0109020a0806 63
    0x3c1d40c0d400310002c0c0800c1d5a40200000070b6601c00c180398105081003118688014000c400890300011071031441d00c01340030102006503a4415600115a00554440288250000c940c03007400341100150000c2c5c180c402045c1c014080030b082c2ca0307070010296400700001442d001540d0201d1102d950254082c20070300e0042450548403911469584241c10400040540741034120000705003190003010500d0085540e103040c3e040c1d008807101c07144194050440780c1681d4005c0c2d0f0004000000e00491080e00400300403520348104144070402624007420421950780102c2c850f9101802086103400c00303c50f08600d4500410110240c903001410309004c90bc62120811440d05d900c800074900b45d034840c10000e07901e1408a1039001c90803c43d071014296200c0c000e00050350b842c15510084c0c10310880c9000b40b111030600824055200020321400c644000944005607412450340d00a210381706030001502d030010080d40e1140f900380303a140791860b810f955030f4100c4000c610300590b000d40180520000b4241c14500701d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555378327 1250 555377077 555377099
    0x80d0c080304020d0512120604240e090a120512010f0b07140c061303111807110c040c030b1e010c020d030c29100e0115050705060c03060a06050301 65
    0x75000a000c0c1111482c9030302041001d00803030602d00ea8102409032207d0b88400d85842c12041542d0040c010b5180980005a1082003000b000014641a28000c03207945496024204414001c2c0705440a010b4801e400e0000b0b510714000d40014603150b6201d079103130780c4010000b060103001a80b0239103d0308949102000041040403c0d100308503003007200030019898a806141c20241038000c1c0300c2d48004c1c00210500307c00e000086602c2503c0c0038140c0c01070460103102c103006d045100c0d00c2803401400301d078070009220329100d15001249660031100350b401c400c2e4100f010a0a039003120b41c0b5040800d03103a5405829074200a0f21844014140c0002d00507507071007410020305540a841c0002c1d0007800b9040e401807d05000e010145884c40d4400d0700d030701506c210000c00705c0d45000c0107800214498000c1003c140c0d01960794002c0810780342c0d03100404910fa485c0c00300e500030b2412601e69407818130000b40000c1001c6002401400d00c2a0385110f4100d40c0ca01d0440b0400032a00020341081042c04814001800811f0510b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555379577 1250 555378327 555378331
    0x4030309110109081e0a0b340801030b04050f010c050405041104050f01030b0111070306060501030b030f0607051e040801061a0a05030a090804080f0d0e10080a1505030a050106080d0c0803 82
    0x4810050101080042041c1c24843d16078009403080c20010709110101490403d0000c0890380e070810080a942c48c0c3c600850901d008900c2500001c5803440107001140d110030010760018491001c03100d2401c1c1300c4a07101e00b502c02e100641c0c3d0216001040400541c01c0501403000e9042440c9460761409080c0000507500c0740c4d034440228101642c889070f0a58590082980034448076000d021603c030141d9a00d00f0718050b0241b8094640040d081c4000d0308403d0500041e143c0c03102c6425030151a065071a03d00803601504080b00110020109000188400010000600250003c80c0010580c9418140d0034090703002d40a401104101040203010040b03940102520382003400140046003106403800c204113903000c0ca401c800c007180102c420403413112100160301884142540c0300e90ba803a42c10b10041152140300c2c00700d103002044004001a0895040e0341c00b282100204949050708161154080703460084d011404550030fa6650100784048541003188012103011441c00e070380c2010700d03a518440c040c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555380827 1250 555379577 555379603
    0x20f12031206190305060405070603050f1911040e0906010f031a1009060e0601080906070509150c0706051e090d060c0908030a03020717030906040b09010b03060403030911010908 78
    0x40040840d1080e5241d10f0000e114001100201059640b80e0600d65180c071001d4508440714843e25000088660090007054400e43c00030f41071200c00c0d40c0f0120100e0f007040301c03901090315460340d07810702e0109444c81c200a44040c01d420600313462580b402d01c0045c0e20b07054040c3c1050303ca1007618101000007400d181d10300051a44400d0107100c1684071400d01031001c03210307a0880c2000302c2c00c20380041001070400d00120b116540907690000c0d85d80310343d100d10b03840d050301b40e80440005034108901540d6051904540000c1410441d8091516001d94803035070401116070400000518006840d04030081c181401075800d55030000a03d19000612001a441e40d2943c1c400501e6562100000b80305603010b8407d0705c005140c0310003580d80d6150351000040c02540304400c01c4404000b45140342032022604130a40e8421407000e001000e131a01c031034a079944c3d00c4c100101500e465640b501c02001c8a901c080c00701c44d008034402c0d01c01044600462130720007160007c1c40e9080381000815207041008200c001808610408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555382077 1250 555380827 555380857
    0xd050a020f03160507020d03030506010e01170615040b0d020901020f07080a0312330909050714060d06080a1101080402130c0306050a170d0203160b13140a020f1203 72
    0x104100303099401380106180a51f0004801044c40141601904000d206030026a80d102d401007071480191206101402c40c000e0540043c0d0000301541864401146030030001e901e804e09007a55907424410039800013041e48041500800d40b043c25580410407040310245101c0608517075820305014960700d04411002408102440d07554440d001d000d58002420101d40c50100d5000720290745880038030f0b890f42e070750040b10b188460b01c00182c81341e82c03840351b0009684d0001c050019a45801e00b0356403e121b805a16640c410301c204411410704140b80304a00c0281208000f0384100351140c20145007440d88601100d052020003c01c005c01a81c41d01d0300f510217000c211800050451502100307c0082001d504800c0d0002048a000300d04402c68052610050300c1c90000c507030b02c0300269001242c0768019800c8071040c800048098000092407004841d920401c40052001d580340e40380ca0354213101c1d1100210103002c0c0c1152101c1019400c107284c0d4500f2071481540e032908500d03002024240d50b80725002030041419 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555383327 1250 555382077 555382111
    0x90c070f0305070204020a0e03060702010c1b021801030b01090b091e07020322030b0a06060f0509150403030e030f0c1c060902090c0319060311040e07030204020c01020d050a020f03 79
    0x5000d0b000395a0a56000b420440d1186104200605010000407400d0b10a2040800003200d2920501410480c5801076aa420607003042940d19031742003210100890b4840f505150283c0c540800d00d50150095008840030401035141155003030132210042c039018003131480e000801c840c151a483c0154a01d2408a0a03081d442c3d848280490940c05545050300550442c0c10807009400d4168104405403400f44d00ca1429684a5050850407552903200d00c8020403180b100f419440ca00900282980d105d0280507140401a04041a031507907020303800440205020910f9414641030411151010340d9a1f04010042c01c050000010243d8139551104c0581400c041a04420010260041c154440e4003401b6200a4105503e1044194004890380c1c0104001c4c0719182c05810341394020642120f4200a4002d851070380c410074080580500110005141709031a400001612184000d00b101c0c1904400143c0750000b00b0003440555202030303d040038150050101a03044a4100122a0080c86000c401c541c41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555384577 1250 555383327 555383333
    0xf11030f0405010804113705030c1302041d04060e06040c1a0d0c1707020c0d0201031d0609031c14010909030c050d0302030a1803120f020c0115060905090c070f 70
    0xe10741d0700105079040600200c650300e40850000c0c030807050305241c0c140387d510000401c03201a00300c0602e20034503500d030344101c0e001d1105042c01044001c8062003d100589815194005031240c1c010609044c0c0e48049a0000c0209008440c89034200c200352201c050b0406040c1038488800c0d004a5004030b01c0e9282c0c484542d074a807554890200d40040d03440110500111885001c0502200102da640e44a180e4081002a42e0281301081d559001c1500410620304030490f82c004400070091804a201007032109400306a041d01c0400415100701003840003161b46240c0c4030203d007a101d0b13400399070f00d205c0d5050003030b1000c80035958169241540c200c00400204110903080440b601c01100001030014000c00e07a442c91025810340045104080300c1c0c406020900711007141b410002159031001e030004580202010084d6210780014948014049025080ca43e203182d01c11b003110701c003a140c01c07144a00600e003081500e4102c0310300c40040c9800c03681d010203490201040c1200348204a0005d0020120700300c0c2d4010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555385827 1250 555384577 555384593
    0xc030604020706110318060106080403031a030f071502030901050313050a0b0109090204150305030912010e0d03020309071403070e0a150b18040c0c060b03100c0f11030f0405010804 79
    0x50b00b0782141d0f042c0800502113001414940c42a5a40010003407851000f8608580008420303040364403d60325028650344035242240109015040003204c0c1540014410940c2e408001c0b450a070b440ca24040d00c5502e140125560000c0d800d01444410340d0014031000085a8000c41940c0d40505103440314100c0a00600d0414105110030100031b117902c019034000b00744415554055040036200761010004955980c1180000c0d070203e110003000e640c4100041203143c00c1419030341040d40040000072a0401100d0182030500485410f00c000003907000c0100715527a141000f00a00600c42800007086800100c40400d0321114280217980c40d03100b00d0300109560310304135400390070b0070042c6800c00203582d41c565006107000d40c0a5606100c0c80036104d41c00751700a03d881d128075892104a0707250100c0241441d900c80c1d01070310050b0300c540d5260080c280c0c1c80f86003003614051004d82590a0b910700c40c0c0e90787c10f004017401e60410021503c0c0b2541c400c2c0014001c0350100e0301102c003071b20030900f080540e070b9a65240c8402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555387077 1250 555385827 555385837
    0xc0c09010501021f0609050c0c070e01052107050a080c0112150b070828033804020c010203100617041505061c06051506091e030a0c1203090e0f0c03060402 68
    0x406c49140108010740c07100b01034050003000c20543d00f070700e50003076440c030510307040860a01034150701c08540c4d5900c0c82141048190340c840340010500f42e8030000d680f00c1c0024601c91321a48840503030741000c2c00400e990340c1d100c004010140031180081060000e850713480e450510311401900a007600004100e001c3c0700e078000648072102c210310ba4052002c055068032000c11070203040d01c01e0100381000403100d08580203091104c071002204941c43c1c80c020a0602c1c2c01ca84000c040000ba802a030b00300094540c08000f0b0006520603401190070801c00d44c9852802095850448058240e0f1005030f403d20000414140790301520b495986001b1689445142c002680780c80d0141040082c90003c0070020200034850700720f0b5115004e02c025400681c0307038a000b440344070702c01c039041c16600075099907111000000b400c00c042550003002e012a035100f044c0b5a500052480242c02c00d2002d40c0000401c501015031004104002c0d01150140ca481810890305403d07102c80d001c1c22110f000c01d00400090443d807103a5058072 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555388327 1250 555387077 555387089
    0x60513020c0a030806031501031110020d080613380904050309130608031b0c06130504021608031807050612070c020321131401080a021e0a050c0c09010501021f06 71
    0x20947d0351b034a00e803030101002400c20040c000c4050000c0407403011300115036100e0804a9860300082640c801d4100701c0c18108019052036a6951803d084440d9468090b20502d01e0800c0034101c40440e0400349100c1c0c0780c840140f6154401c80e0f0f00f0007004002a004400e49001507010b45440311101850341590000e0a096000045244404151606543c1320300c991100000351000580300c2c101c03c03800c180401441000f00002d1500354648040080d81011760003090580031425040d01a04400d0360340d603150368001c0d101180c9120b403000c0030070f00468060155074002c00d0100c1d012071406881042e2000c260b40d00509050600003e200c900c01903407070030302114501d02c0c200794400401e030180c02d0343d480d01500b26a9004a000030f6508010a41030b076016405512071905031694491030f0341d001c0f81c2002a42c8501c0403d810380340640480810000741794050300043d9500e840b4031b901ca1805148152800303865070700c5584540681c07001005541d8011804021031031058403110b080d02c080380380340000f40000d98005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555389577 1250 555388327 555388363
    0x210c0308040515090c01030e010612030c05030c0a12110d080a05042103140c0306030a1b0f0902030114010c080d0e01090b0f06010908070e0118090203060406060513020c0a03080603 79
    0x44c903502c0400c8041c100da8003600c042107070f100e000c2407140c200d17089806040d210220052541c00424040c489603003106120b50700b100d241c0b01d0300000003802c100405400300c51940c40da40b42c0b0080c440e00302c2038103041601c00e00014440308403601c0e4010892840900034140b05035a401c0440c062065580d0b034240102c54a003a0866203080f00c6000a00800e0600c0419051100050100d108505d20300c0c00c8a00988009004155082d81ca86031040c40880c0440294118400c65000041c80010709800500802000c500141c03a5850000c00100300a59441250b04011201c0c00171000903c0c44c070305480b1040f208102c00205503190030328190040c1243d40c406003038601444100500e203415200c48038420311007079a87d620760a83d1107070741c160354088a006040300c01075074038018050295003001692844000c0400071600e1407894020906008058600703441c1d071929035406201504100413486c68189100e04114500300707052040c01d4542300513010007030801c54000041882c540e0100894841d0840814403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555390827 1250 555389577 555389581
    0x221010e010801060e0405060403030b2205100803130b0a0c02060d0b040c05123c01060206010501020a0218100503100e060a05012114030412210c0308040515 69
    0x8021140d94248507848456003459004a00662174145450259503c1801415580c079190303400e80182400040e8150041482d950300c18041e880200500c100509510000030241410740300b0040c0ca00241c4c2040044d90300070131100806004d0342c1c1100085a18140d0210b031079184035101104d201040c150082e41c882404501d414215a40c0e521039001601e0031a020007095582c10820344a500441100c1007101c07516000240015008140404204008a0421040300064801100a18030120711490000c55080051201a404000c101d01505003400100106000c7c0e03030006002c1108466020040d43e120400300d01d004d580310700c07441302030a8001d0603110505032641007080203044104a40392188101c40c00318084a0302881424140c030703401c8012034049040c1c5490780c42c6408421034100d4041c02e020450390f81105050001d40050070110010041141282c200075218142d00144c198000b5605000d54680c02d410190103a81c071a0f15007440040e680d035030b00f04941010341c1069510400303511042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555392077 1250 555390827 555390839
    0x100f0815040c180f12060911120105060315010803041e1d0907090501030c0504020307170126030c060f0a0b030703030e040e0604020112020912070f0e01140310022101 73
    0x400f800c0355849004010f103559901c55107030081c41c0c1c8500c220703540b011200040398040748480c0c201c011424012051380d41c285411002003881d064111962400603552a01444218038061002401a030340364032091185504016100742c0301d20580c41908403404000100803c15848454484003c01c0051000282c445a0058000542c40200c1d0103141d2401000c0300458025018400c20381030ba90080d070305481050825007404000d5102030000c400717000309480c00200d0028140c8616010300a084010f408151802d01c030180d5500d4118400e40c440c2d001400103034400c4030b0000b42240d0002c41c0200c015202e480c5c4140a80042100309070403a01400344150100605400c8402c500c0c4c005425581007180040c041903a43c1c8503a81564020b0005101a868055600c1d654020f402000401464100c07480c00d64100e644c82c0c003480c1e07070001c510382001040c00c00c44402846404ca00412400c08500d038820401c50003c1d80303405070039000342a030584c082040c1150040e48002c20020200c1400041204d50311a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555393327 1250 555392077 555392087
    0x14010305060711030403113007090f0902060a18030503040902040f080d0804061112090105040212060103050c01050304210809010b0301090f0b0a020c0a03030c0e100f0815040c 77
    0x4030300310089502d401180b005080f00204843c1203030b40100362030308488441e1007084505a00401c002c0d032a1a01043c901e0b140b07100811024414420980003069003a2a0002d03a2081c1d41c443c205030504140303002001c501589884080701c40092032440c090100b24a103500d00418011540c2000c1c04501c070118012907520040e0740104285e9510005107a00240c1e01c0011540d1406482000e80c0083c8014002c10000380070b0340c0241c0c1103810b00016a13400d000002c45110031070b000c12a032050f80f680d10f450500c400d600313202c0f800392904640311014106941c115110f0303030303a6465110101c80c104031000001800384440300342080f89218410fa509091135410305401080e00c1c60940b0202d03540e520740907020410f40390500c01d40c034403940d000800d4640306006e81c80b0145042030003400f10070141d8081100311583c050511000d00d0440c400e4400150005885600030000030f0705602182c0a200c1a00c031506d0100d40006918402082a04e050300a80c0d03100d1000148803800042c07110741160410807540700041d005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555394577 1250 555393327 555393331
    0x21081312060f050c0901210b040e0703150212070f1403180f011b030e0127060f0519050421170a0b090103080d02040506030709030501050601020c0609040f1401030506 73
    0x440140081d45522142124a1041650090104401c031f4503204448040005c150350001c0360040001364062800c01150a485003031510001ca070700002c1d401d00030042103039207191604d41c8464003141030401c0c0030441d010f8040090305c0c01c01840000700c9101a110b200e42c1c5060490403060403083c0c2c41c3e00f0461f005114140b101c103841801405107025604002d141481070450a090114194080041c1c0110950041c05002c0c5040320035500c92800719034403242c10008910703041105c4518081500c00d07040c100b045603c2d10700c406070403a050030180180510004030035040791401880004035074446141000b40c81001244644812111081c000c0b00d01d50030800c00180f1804409080c0059a82c96050a044840701100140e03c450f0000041c0b012580c800301074041065400401032416450b4800200340ea0402c031070000018044000600c2080000c0c000d040d00301c0800c0c00145501ca044500140c0d090180200e007600880d03031040341e039651040c550800340341c0c407004806988442d40c684c01e08913110b04d01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555395683 1106 555394577 555394601
    0x2a020a030501110c21070201030b1c0308011706040b0f270d09090b01090504020f0904090b0901180816080c190501062108131206 57
    0x10034410030a203c0b002e10140c0c1e44490300b41e4400d601d0140761110465284150913607140511000c442900c1030700c1da0908000c542080c81c07001182c00c183d0b92014400407810300245c000149504051264180c032500c0203c1d407903580b004401a0b68401060310010040c442d401c0029590f071103840103071030300440d0007000000050312521201a001c40300c02d5031184286c1000c0020b1440030f402c903100900415040c076003400b019403004000f81c044070007442902d01598002609000301c1c480f10040300c00c030b554000c104010303682040c24100e002500071120000303150318204400007081e45503049401c2c4140c0c4098801e240c08110200c0400c0315010b09403c0707a15000500c46000c02c03110501003585020310008200000301b1413070405070b094640503881322010b044c01111140c001c10329241141d0200c1d4114080301d5030740c200d41d13401d90700051041d80640090090302c0f901d40300300034441d0402010540 = true := by decide +kernel

theorem cover : BRFrame.Cov 555215827 555395683 := by
  have h0 := BRFrame.cov_init 555215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555215827 ≤ n) (h2 : n < 555395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
