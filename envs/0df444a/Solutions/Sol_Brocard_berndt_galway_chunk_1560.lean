-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:34:36.841568+00:00
-- url     : https://prove2.me/submissions/e62c00e2-b8ef-4935-b758-c600c3872402

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280395683 ≤ n < 280575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280396933 1250 280395683 280395719
    0x80303101802093f030913020301150503100e190b0f2d040f06051527011e0804030e010207080604061d07080c03070504061202040903110f010e0f031201 67
    0x18203284c618024071108881c40b00c01385a0448207034070004480c640c40c90039010151452141641c154030303645c1416401500b07076030848001c01c01d003c40030000c10f0003444994003c6019210945021100b1300d01a90444801c0e40003c41281b1040d1500c8020704060600f0422480d0000700901440350391400511398200c0380d0348901212a4001014000c02c505a41d91b00070359100c08410040825010304100422520455818000500f200f00304858a20112900585c5003c002820356445082e524440161543c0d00f0300207400140f14820030306841d1007904210114003844c000c0c0d642200440c3c65200582c0d032083c5e580508200c0b0341c40440082e0020340d039600302c00e150020710700201c016818141141c5185c1252074000302c0e900c0c3c00800f800e031594142000600001c22003154240042c6240910b41541d40d41d07000000790186895803908018140180510b0b03c40e02603110407a01000404840b0f64001c000359034980c5428080c2c0110044001e4000003a00d11140398001040400c0c4d1078185052040c0421070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280398183 1250 280396933 280396999
    0x8150402010e120303090d080105031b040908030406090c0e0114120a0203030a0503090105070306060507030323160305090a1e05101104140307060e010c030908030310180209 76
    0x1504500d4607110f2142051111a600a54a070304158104600b0700c0c05890083c020084080010446581c00099088000b460313845034040805ca41070208018085041000e440b661000041c0010000709500c04189680902e4000181d0b0b41c50781016020132000303110f4240d4142c0000c4c01f9a440e0300d403c030098645203095004941034101e890b40405e007590803502c00b50000c500003008100500d070013802465802039082c541040440c1c1000c0b809022405100300123003c2566030b0851401103800840c400001102c6000542d805180401d0f0aa1013190502e201000183c1001c001c13811142e000190540d40a03405122250106080c15070003c1004040f81c080d545441610341044070316502d48512000d002030210600d54407410b0007500c6030080d5002c0301d550b000b940041d60401c42140c4c03110240c3c41c5080c2c02d180c42daa01d0512070508031484d00c96500445054080003040c08100000f0090302003c40b0003e856810301400380c6c070881000c174028001459080b03c40700080141107850710000c903030102004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280399433 1250 280398183 280398197
    0xb010605090a050414040c06020d0f05031503060103080a1407110d0503041715070507020901170a06020c0f0601061701090902060d023108070b03070302300a02040815040201 76
    0x3c4002500781d901e400b03042010304500c0410b200600c40008405009000c45000411814040e10001000b100c0c0c0c2e20007038810041c0103c082601300ca11214605414080101291010750f10303170400900f00c0d80121000c50120f0b000c2e9948002141205042c0d07220b5a030017503811031480e9035443c01c2c8890000d900e03004035000c5c01708100200d0040d402d004d030740034050400390050200100c1070800c1d02e480c442c00f4112400f803280510004005a44407003100341580c1060708140c44010001045c1450400741000c0104200c2c0041a2100d0703078240028600c000700c2e041011540e2a9a0795482590301070340702d24040310b011902301c1c01405407100c0c0741c00c50001c44e44094009480e02c050042c201341241c01081500d0a814009030008803003000c1c203200500100d80300c0307041d0310000b03203041c031401d80da03a07500e00c40c00001243c04070000b41e003107010303038191010107507a108084510884803c0d6140d0010070900e640a40e042071001080c0003c11510a8409843d02000144801419200440300d0060b000300124100085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280400683 1250 280399433 280399439
    0x2412030903051615141c0b0a0603020c0c010e010f18180903030e0f0307030e06040506030c0307120b100302070212120706050c0903060412050c011404060f090b010605090a 75
    0x401c00c040e28a0003444032500d0342003030909403d401c0d49250b441d070860810014043c01c159120152085603e141002c051b400b20440c0d0220039800a40003003510303194403000b404000102c01d0380580003803e51009142c10360704127020100c0103680c0025038501c00c0d4000b0300100100c80d00140250547c02503104000c0000014583d96440d480c0055240c2c5e100c1d543d41500d40d16000304054150090079007900090010b8070341c2c0d1504d0200c0c81e50703074010f801e4045d0800540c2120054562508001c80c2c000c2c1c04090400e560360315007241c440c2c03803c1d8000c0d5442030000344031100142ca0013803244500d1703141160007000701108007903120088020b9042030b07a050384d0140c2d2030060405402000c000141c6072034081c2001ca130b01d6403d5410001d0031a00006e1030818049420005842c0981d80800c086900503444010b086400c2040e00e01207903039028440708081150310b0549240c0300001c450031002d2240d88101818404910850745070b50982e08420401040ca40071300d0014415240280301604110701e014041d841e070295 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280401933 1250 280400683 280400693
    0x60a14090411060a12201602180c0c1204030f2406090506010f03020309060606030702160f0311010f120b0d020a0905070e06030c04051c060507080a2412030903 70
    0x4003c4c142c0002180f07112000c04984401401042401a441c00c2000c011035848004000e8511459054404602c83e000d03201e0215940e980d0408044880841176003101d1808600c125000c0c2c0c040d0100408a101d2110b481104d80f01060440d01030740d0740524242181e4099698004841c018881520421981202a003000b55001d100c1e50b0018454400d011038541045c00c005000744500c1e030b58030f20405004004100d400e410000d907250300b01d0029202241e8a90b80d0038022410100007030528010700040340c00005006421a80c080c050700c0c080d0200c4001400e1850064445e0001d00c40d0306004506e18164600700d50b020307070340249403021000d06072040c4104542e0000305c1da1904c0f5008102d200340e03144d080c0002c169002054032401c01050300c4091640c00e280ba00ca0704580164820284a80780c15040400c04c039440d24602000940c0c0b0050511031401c00b480091320742881244d46034021071600383c007509a64820581c0701d00e800340001340d0b440b0b0340f070500801600300440c0c9403042d8203002c003008001000034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280403183 1250 280401933 280401937
    0xb03030403031403520c0f06021c06050907030203090c0d021c03110f010b031f02070b0a1d030a0e012303010b1b06010506031315060617060a1409041106 67
    0x4080159050300d21164030030280e480d142045c89140d41400001c00d00c1c2094111042404254100d4880780b690b102d14940900a03229074004034000076640b4480368080c0f03c142d0031031001c0d11003c5074142c0081e66030000480072800103c07003994143c1e010a00949290a10300d11107103c19002801c01c0ca800348005c1010840b100740c1c1c0804600040341d01c140210490070600110b942084500028089403020f4000651749200c04100184124044803003103400441d140d0440390301990102c01401189080c803070110050404c860301c45a500781c10035401d852888040300320b90078087c1540700e104101419100454452000311502ca560249c00520000c048201201943c000c0101d9400595502890341481c059005100f86040c056801280140400c1ea1210140c2c0e0b4001c81d0b0416901104645090030040310840b111601003a40c0307000701c04148158031140c542d854402d003000e03c2ca01030711081e0910540c0d8a0500c01c4030f10341d254141900c9220b2504001e0150414010012002d0b4130300000c00250603a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280404433 1250 280403183 280403251
    0x6060702060702100c021f080c04050a030b180d030203060103140108071a1201120c08030c191a0907170f0309060715060f06110f0d051c0911040b03030403031403 71
    0x1110041c807181d44a03a0007111990721442040750542082e140bc00070500000361408001c1c070301c0c44160300091070014030601c000b080c642c9050485417044000040900254070035544103000030308110704000d0304850180d00302e0490b01042d00401d03030280381010070a81e05000440c0489000010000402102c092000003800780c000f4003404101d6480c0c0e4902030200c903c2d87c1d400540e01ea003061003600c203080b102007602c4940c1c00c2c880e4031540c000f000c1840d00c50455000c20052088810180f010f004650000140b8070b410380d80020f801948030419404116541c1a08041400d235030b601c01c008a0303813103042c00f00141041d28400c640303400c1550202a40e040a842e800c2d00b201c421280103120800442d07901014012020b1200405001c861018802d4285c0300d000d007081c054288000001c2d0200704404800d03000c42800c407420740c108200030f0240f03006102c040942104620460821001103014600401121308507a411345448280160b0b650312a1381d41e400042010003820701070702080a05280b2940c0c1c00b950 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280405683 1250 280404433 280404469
    0x3040503120f040309060e0a0b0307170c0412230a150c08220318060305150303030118090f0b09030c06070e010c03050715020f070b06060702060702100c02 68
    0x40c0c01001c803008204003001460114292442018040800e4200c101ca200f541c490f450508980082c02003c1422850741e40c1c0300b044644000810000c10700c1d4403042041c000e41f61085840400c3e1140c2e40600521f000314001c6089411214500b07500041c010761f030203040a40e2014540404c0c44000c5412410b00c66070704400c0e200c194040c4456151981544500c1481c6c0c85281010f500605040c113910412500e11640039400c82c00d005141001d060180c80b03846480c5844042100f502901c0f81d00080c003030002a2282c1e00c80400e41003812a85280c01701c1030b01e050701d01000190340c0b5143c006035441c001e010201c0b0240d46038074400d16104046042d0382c5002c2d100c1d008520046176141c820420b01c0e890808028912420000d44042c640a0785e81e0050117600401d4062403e0383d1149031310300700f140c0e4000640c0801c1ca400d030b10004005c0705158800c00902132040c0a02100c012a80d03c800c2401081e100d80c90000b0340c0100e0030040d410062078034903844150a0b0407403400400c10065540030a202102410309044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280406933 1250 280405683 280405687
    0x70302030c0d17040201120e0f0a0b010b0307050a2304141207080316050708060717071d040f021c06080c1c06240605030103110d0302070b0d1103040503 67
    0x20003810108140558034000f032a0039541c5102c00048044880700c0503200904001040021801001e4507801900000042c00165005450240a01565102d6540e8100c9a9140140000500b910060160307031140a26031105e13480d21441b500101d5886481d050700382203c0710442440340c10314a101000c1c1c0007a004802024086818420420006035160000d14625610103542409000004015200007010006402500320418a4880d080c242e403500440b0007480f41400700910f0940c000001208185028802c44564440c4a012a180c41c03441d440f8210020f100d580d0b4020300d04042e48402c840d850408001810700d0740c01008401e0360b01c001508500602e40b540030900a036030302441002c24083c070480b0f600862001440711045041050302c40a881300e9500c501c0c0354408600d07501c81c0510000a0325078185020b45a01c0007404540003030100f51030101010711161200d050409080340e55030f0b00b64000345038051030a8070020450b4002c9480310380041d2211481303041f130300804028500840c81070011319 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280408183 1250 280406933 280406947
    0x6020306011215030813031e060b06041521150602071403060112080f0a0309060609050f1314070f0e070f0503150418060207030201140c1b011107030203 67
    0x400402c04800a01215494101c07010b0b002181100b8607801c40380d1042c40f55440c0c54402d4050003074020a988003030312504009003001000e0700028011420b05100d0ba1040020104410901181e4003513030080d01c161456600c000070300c07240140c0e040381425281d2010b48200c2c2c0400942d100583d011a5801500c118917a002031056035014007400300a8160f2480350414900030302e00203562010103101c0c51006d40c0c0c0c03c010241c24000301d00200d0764603042c031051550351008960001001070002210540b03107513240080c0414800030364041d65020b0003940340e14034410344070603596413600500140222158629130760758640c40c6c0c1040c403c0d6001019005843c040c0d4030325040d80c03142c8000005060710104820301c00050201d43d088020381c0e400282405201481e10103040103d001003107003c80321031032010064000300c01c004144c1c0091542d144281c0c003d000241d0310041c1c4032a07052064480083c0c14105100032010681085180c4407070341038810002c5103042c00340b002250b95600c403400950040e000003d00ea = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280409433 1250 280408183 280408187
    0xc0e06010f030510060305040c03050d050d05010b0403020109090b0103090606080c03010f1104120c050409080c0c0d030203031515040e01080706021204050904030309211403061c05030c010501030602030601 90
    0x30180081c05424180082d00d0b20f2400403660b24031030b00031103040c035a440d0049030900450780d0301100596802030032112522040d54014200d0781141c40002c00c01420300001240e1030340c00500b03640450f40d0607150003d2550500031240090980500e1310350406585003245000700301070f40140300c0148801c401406281c80b0f0001130500703407103036441d41e204100c2c103120b01e010f01c0c5c5800004030f03402c4560807400e91001082d203140080c2c04626a9000ba40c2c0030382004105810700c0b1342030b0028015985c0c100308685d04100400b0611168004060300034015800510009110010062900c52910401003a401040b034094030440c040340c201303410444007401c0020042c404010200510000750881740002d00090b48901c0c2e50401c1031286000d00340c02134419002050805000390091516640e00c800c3d0410b40d000d2188404841194000c90940004c00d0745150300c0c0e403061010202c9024020241110500000500811341540e00b5407001b100d4601c030400458110803420f00c11107000c5c41c8151409a5a81008000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280410683 1250 280409433 280409447
    0xb0112020403020f0f01120c020607031d0705062208030a030b09130201203a080606090130140c1206060d0c030f0f020918130c0e0601 59
    0x91150000e1040000344096a02c4e1001103014040865070035000c1e03140c403c0100c1d6409030704402c054071241803441c50040c072600800c400307114442c6a603040081001c60320480700f00724108030511105401499003840130342045d000070071181c604001c4500740d480c15180101e05104880d03008290303641002c28692105541800350b03100b421401c0b10291010b0901c000c2d104a070340384080f0000c2c10f110b00c424451210704110101d698101d84140141d401c038100e408261140c2c3c90301d280b5400c20710300039202d4414200c81c1600410085c01d14903903030404141c5c3e0313000501c16941d0181c8445814000208d04104a081c000c0c011420720440b0716100303030f040210041c15807045c0c0d0060011401c210322220b04200610303c0303e80940c7c2d010050300c03010510989940d800302d2241d103e14101d001003c2e051101160a03681c00d9007049151100068040004032440113403503040340280018942c0c804410030140d062622402c0c2c03942d4003c1961401e1035114004c5503152110402d460380f02041844400d010410b0359030704014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280411933 1250 280410683 280410707
    0x604020a0509090d0f1205040f0c081204140406030503220602060717060a0b031f0503070302031908040e0126010525020c06040807050a0b0c0c040902040e010501090b01 74
    0x300a00c0a0410081c0540c0313804201e829041040411801c1080307061090100852100c0600420010790500307080c13003640030301c00e07040603640b034000c0c1c0e1400500c3e94030008150710400b500a08481c00e040c00c010b1000600e02c0d01803c0e40c1c0e845919204003001040c8107000600c6083d000c03202c43d07882c1018582210100c0111588008190b4000034104420030780c1148104ca10319031070807000740440e56541c1c0003c4010142d45c001c44130a04022081041c0c1394000c1c140c109924036a080e9030720b95655104105a03461b5900d000013501034004980301c0fa4500c070407020000d08148921482c6080c140c44461524400030700340d100c2a070380c9240c920702513020040c4840907090211311100034083c6291040300c8281c640702c8030a14403201341c0060440c801ca1f500c240854504d009004082c16984c3e5900c052007660b03001d007400340c54401d1501620005201600c04101c2e60304898000c040c0c0003400d014804c00008190841c016a0040c0c0c4034000748052420a11403070b4041d041000c0001004c24841000400c0900300c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280413183 1250 280411933 280411939
    0x50c0c1b01140c15040516050a0503100c02150403030b0406050d0309141311030a0501080a03082a070b0f06010c0b0a020702040b060a0c051002030115081b0c0604020a05 74
    0x845252079a00118600c0b4040b0600e000540d121194651649404418049014010350030030601c810080d02141d100000c564007104891002c0e00c0d8800c1010750152845540d9056103c3d00400030704954a81085000300003c1c010790380d60820041480c28031010440d012400603642d17644002680c80d081c402c55010704026202002681c900d9034001d4040b10450007601c1c0100c440410f25012661640b03840344407106e4038281440304d900c180342d50b4192908103880c4822964100400400c030900000780d0b4608191301691f40c2c0800b034990450020300d10302c0041401180120745100d0040a0203101c000f0207500c0e200380c101103071911b8110714004080780040c100301d040141410b9400c0226207644640c54100ea500c00c001a0b5031001c520000e0014800249a103410010101d000c041c44c81c0c00c014240340780f13400b1300c094442e18011424442d089101c02d0080800401c0221a000c640601c1040c2c115030126101c0c500d030710b0220102c90004982e42203801480d1055000c0f004101c114103003403480100420b400c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280414433 1250 280413183 280413223
    0x40b190203090607230409020c060106030b1521011e0501021906020c0c041103070306090510030b07210b030106090e280c060c02010e0f01080601050c10050c0c 70
    0x480c0c0041c0c0f1464040d1189040100d4141c140108101002c08400c0d280a5050b210303941e95030300c02408000e5000602c0422040c0103103000014114080e010b00042a100200552480e005041c00c01440b40c1103800c24440d403c0b48080b10a0982e402c00c0350a90280c00450300d120000f14000d5490031140000390031450440d0450401407401c1001d554440c0700e900d9001801686864201c403c082c545498051000c1d40181400e10044290312090010360260b080c9aa00b8009142c45020a409030b07842074490b4004082444030800c0482c0e10080c055801254034079044410740b68860b80444d14141c61602e940c1c080355500440000c0345403d20662004028200040c0041c0c104044040c1d21000c400d6503001071440b0a1940300c60380c1015030700030301e44254807620a01601c0d450b82c600070030110320050100e002c212144d20758009450038840198080303405039103c0c501941c0380001110b041d0007115145100b881600c80a51600c005400768030322805001040b40c1d110003400243ca89004038040002c5100140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280415683 1250 280414433 280414441
    0x1e09060a11010e15010b0f0d06140108090a0209060609060705100621020a0b0c030408010c050a08061801090b030c0301090b0402030c09010803041e030b090705040e030c0a0f0f0b040b190203 83
    0x10024116044494180405841711300c07013003000080f23200d6180e900c0b46140c07424030041141840740605000c03650081e612601255a43c989840e511030714500b0280d071042c09031001801d01d1602000030f20b40840c02a1030507052866a9031914075144850300040030312900e40380705104107440c3d69500c40c000c0e03040c2042840c64104540101d4460b000e1405141d503070b8580010b000d801d40904000b141c0081c1030b56002040b140312030130402003540c0c01407500b0303200042d80c2e07801003503052502108942c01b0741c80c1112240010f074a01900c2034000c148030301c0865014082c842c00240b00703640a1080d025400d008442d00c456514051040608100485100ca442218241c0040c801c00b04004140d0302591801c2210f00e64400c40701d034035480d007081e09030701c010910040d0100308400c0c4030300826044203c960a075801d001c055100b01e02d082d200d006050703034071005512040d001d5021030303401640803039100e0051180700c41c580b580e9180c104040c3c200711400c0d03441680c180d00b8801000090301c00a0800300c0442821421410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280416933 1250 280415683 280415713
    0xf0c050306060304050705060a02100506040b06092b0f0c0e040803011509030c080c1f020a020402030a1b05030f070903030903080c0f07080d020c040203040302031e09060a11010e 78
    0x2016007014015480400000c0400404100200103003c0007808540c07100000307900250380307000c6825002d0303a0324100380103c1c40d20b09250240010b1074000504203820318440e84180080703a02014038005240c0c07003105803640c03a045014131994241d4020300010400304100c0c1001c15821841d80d1210800401540410000c1040c003021380c1d05451a440b070030256000c2c01e070000c403040301d141d81000d04403031000c0d000091b40c0f0500240543c180d282c1a12407481e80082100074ac03001d440740c1030445015801110b40200140741550085030310209604000600991940c001c005003041c0ca41c013800851000400d001c0200312030810b99034400181d1610fa50803d00b155001040c0d101103200040c101c41000c600030450110500120210261102c00c0314074283e0f0740d1510300ea4400c10790103200058054109040c04a0615008680c881c076090b800a5180c4040b803030100808620b81c0c078900300000d4084c404106070345e880e08001c00800c1c449507116191280c0420100e4210365030700c1440115580b2000460034900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280418183 1250 280416933 280416937
    0xd0b040e160b0d02070b1005031e0d050a050f0d05040b0a02031003170903061014011e0e010c0602030106020714030303130b0712090b1608070905040c0c051e010f0c05 73
    0x10700c2da10003141e11680686851006805443e10092a0228100400c03034010503411440049a00803000c0310b00740c40c0740c500343c59040c110717002201c4610303001813013908100d9010b50010003903080b061404502d032140803885141c45412064082c400207071103109000621a80441064120341000301c21031950407c4105483c0c000070510005143d6020910100381c10421002580d0040b07070040d080d500c00d4603212001c4004101c0c1d50051444070700305060702011951050705034144c042c41750200c0000c00054440c050300c0c840d9005540f14100700f150384107000041d01d140042e500038100384d00205001340c200107146000c0e54461520074020b600600402c244c4005440c001b0300200d070040c00889281c1c4078034008641c100c002c3c0f01036004c014100040310741000500c607903042c40755080e0040b50301074109000b0101c420200c1901c0d41c1e000200700c1d90003809145055880a050364203d402c0c41c280c03408403980d0790b44c1401d0018000303900040c4004200c4040713020a00501090900c0500200080d02060360050594 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280419433 1250 280418183 280418189
    0x616020c090403141c0e0f070909050708150a050115051c0204171506090702061b0424090626130501020c06040c12080307030e120d0b040e16 62
    0x25844507004034007458096135207100e041c92046405907684040c04e01007442d040c1100724400c0850f262014400c1e40c1c0901082036a81c4105440c040c0100515040c0410060900302c40d042d222402054030001e81031004100100182800703400100b802e1401c90045c2c000c952050388007215040c0b08038031045540e80c1c00b50458801c102660080100340341c524042d8802400745800001d1112203900410b0f5650704d00180600400f0000d0145010a540c0c94061118002059800c0000b5901c00e002084c03036602c03409030900c2c03c019090003403401c00399980c031902107258003062505c0d401045140310340f100c640d1200c40c6c080500340f242014601c0e03420021740c0190b504000c910030f41345061020085920f622100c1e54041c2030682140003552518030202100c1d4403a50255405c4442c070200c041d0010388940e10a42d44410f20741c03c0801c482c00d681c0c94010030740203440c5100134076055004a180100b001c8440f4400390403490810311000548152103014402110315941201e036441c0c0c000ba08400140d9071500540c015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280420683 1250 280419433 280419439
    0x512010608130c0b070203060c0708091e0604090501060206100e151201020a03021b0c03030a030c0c0f0c081e0604020f030f0a060f05160c02060307140403060e0616020c 74
    0x3030b03544110b261402ca0102003001800c0020030100068110a9540034050160080703041c0c4100ea21407407800c13615489004002410304000344132640340340c50080310103a00b000c0c510b07010180c1035508100181d000d5000740c1000f654269110018400c00d03504008455112825078034851070a8201100e00d410040010181c54941c04000001d4006480d250314184926800d04025521a40350000c00380c042d40000c20846034a00c0101c03485119508002414840c0c001e000c1c3c05180341c00300002c0124050020841030006210080c030044000a0281c540030503514020b40310070003001d0902c58154288060301c1c3c001c0307460b03c40359810349000050105410f60032070360403141e1144005504011034200f03104266500d18a000d485045018841203402217003d48076420b20400950745c0d002c0300041003c0d881c0030414009140103800c4c4006050000045030130401c0e81c2000c1c00300703200088900c921507101e60821030b145a2681688100c4280030004140c200d141c50f003003c44200c8441e000299a840c100c154944 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280421933 1250 280420683 280420697
    0xa050601170a1a0a0305011a0a0b030106050f0c0d0c05011805070e0a150906081203010819020316091a01080f0712020d0e16050a0605040b0913140403030c05120106 72
    0x14410301203d540301c1c8810005409582d2641e030b00e00340740740209840310204680c0b030040c42d01d44050b403602031341c00c009807400c4070032a50550b401d2130012602d0340c2081d04c119000480030440072200030000c000c40344e050f00c2503550b800303c0011035282c844d09551508103c0d45102812039950000660f0100d0403100750341150900d000700d50b0724103600c04044c080d01c20303414940344c1c105007012900240c543c000c070054800007021602180faa5199515041c4001d10500c1201c0c2c1000100141da42d400703d400d4000d017400201280e01c901d40692400184106036440386001c166503401030ba0a584d0001c0c0b40f0700300041e0901700040382e0b10708030000c006c840c50011b1880003000440c0407071810f1800760f03905651035222145401c00c03002071040d00e040d98448100040380c07000051002e0000d035501e04140e405080c0c032984d0341e446040a01d4500c140100342c020b48141070340b01d8400800c00030b280a043c8610600074001d011402101d06103410050304840303405208200704241080b1228211026040040c1117403040d00c1c1400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280423183 1250 280421933 280421951
    0x70903120315090b15090a12050a060516140403080f090111030c0714030106030804060503040606081606110d02030d0c0c0602030411091506030402010f1107060327050a030309020a1802030a050601170a 88
    0x602b403000c8154010103c2c0e24210034040140d0b208640c180c0c091403185c4810700c0e44407101c4026425405544402002240700b0012120040c0300100039003503108043c10040781508460781c8140c00e50304054242c20740c40d80721403010046080140c841d000040c0c0c041d402080000d080d40c840b28400c3c451806041c082c4a4000045410441c2c141d0098000b40542030980e084541e90500e8100da03040b0358429000000c5942c140c031400320f9004500500ca02c11103030021403500c8040440c080c0500b4900e40000c050000b1000000302084190000b184164896074194004901d41020040010005803020354400c25040b03041c440e07130300c2d0703041226000380e02400e10304c2c0001143c2c40c04030740f41c40800410100a00485000203442c64141e042110602c0b509030040c040c035a42021030840380030020703a001d09241e102c40c030010040b90003540207910341c900151203110324130740f500e511500000c09810304070740301035000040005900c001c2c81915080f900074603044400c4421110078008202015002c20091a0745040c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280424433 1250 280423183 280423193
    0xd02130c0e1311030a09020112060303020309040b01030e0c09180118060c08040308070c020d0819020705031209040c05160c15031406040f0b100201090b010e070903120315090b15090a12 81
    0x12760f642282da0009000060703da24000707499400c1403100c90f0185082c58520803040d806402001ca450000c03400905002d01b20404004914401408041d0008a448a8204200703003c2c00f924042d40040611880d188003646131940864551030800b0042003000c105010009600542060b04407030645407480f60305005000061441501c070200400c503880010f800b955280d140021207020300c8154081d50703581d5035904140341e141d48170146107a8405104101c0b54002e440c02c1c0e40b0a40014615141aa08201c0340c170001d2144d0340c4628100303403525410007001700120038030201c2003003641071385103014018609191420601044050700040c0f0641d250550760740c5032980c59001c414030180c01054035a407031444500180c02008d44180942d1038034800e00c00461100c0c21001002d004403001d82e2043d451900d5602c0b284108031480d040b51040503241c4a107036500303100c07404902022b08004074000403094030b41010841880d210b035512440801e81840014001d0b030726a01c40c4012290085445411400d9a140c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280425683 1250 280424433 280424447
    0x604020c190825060f020301050a050411090307030c03060e160b1602030607090906050d030503070503091504080a0e090114130f05090f060c07020f0d02130c0e1311030a090201 77
    0x3404a20316080c08410f80440702d4024202c03102401083c0400581001e00e0300c1c50180c1c442402465041400d01400308258205580701c00301c80c103020309280d03042a4181001034244a0b09501c00c3c1c9586035440c0082c01445801d107d007102c278405100041100d008004039a003842d00c628412aa40100d000c543d25a142e003030003071040380c0c9031f5004095915034904094050702505141c010401c00610f032102c0400c1e40c0c144691650300f51078040c7c6510b415039032201002c0f602d60340700512111a074060550007202281008903680d000310700c41d1001c036840c1c6818a9004210310803224495125102c1c0400411145020350a121140c2400b580c0c804049000c9511120291803005c41c0807812603c2c000421014070004145100428240c2c0c041d610720b9124507440001c1800b40b4100a94041f6000414100c1ca1600220a4850600c05003009102c0d024440310b010481e07501c102000302050baa01c090740100d150071051a2071a0791404001c0114961004921f2041e0000804014070030b035440310100150780c000d090f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280426933 1250 280425683 280425697
    0x5030403120c08100806130b1b03070c020f0409020d02040c0e120102090a060801060e130615080a0510120809040b06040b190305040209040201031a04020a030e060604020c1908 77
    0xc0030b21142c001144002e1000301c0840b614031074400c001401180d61400428010300a030002000404c1c0707043c00d6101d481c1b06d9280a040c1e0109003050320314400d01810070b003010b184241c1c6c5070303114014003840038018045241c1d84e07000c500344920301d401c1074000183c3d51142030145454060720000380520300c1d50001e40d850407260f424103604c50100920003011500c1500103003100d03031050350141811640e03008195510402030041c0c0021030458610b0310000d00300101d0141051100309008518a41d4840103030407103010b01c60007940040c0c002000c1001250b420b0007541d0300644d0040520311094a460008207002ca10520010010200020912400d03030341c64000201e003000c0108030320350322a9141b20907490f540c4044a6850800003000c00c0e011224007030300c946480366030064a0f01203d513450391300440040544c03803030328a04009a25610341d020784840c40a04a02030b0107480016019003004c3d84240342c400c0c02482244103d00400160b00307a50804030304911301000308400100d00080c28a030880b414041e0300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280428183 1250 280426933 280426967
    0x21b070e130302100e0f250e01050a06050903030d0204030305070b010509010b2709010b1804020a0f0e0a03060608030702130903020a1e0503120f0a290a08010f24140105030403 77
    0xc0b00d810042040051f1400c80324003030f090725510790345030110441210244106940000b5161003000114041d4000306201c0078000d05036464451041003100072a00240c00540028401041002c204806450004d000d0302c012215051a50300d03000810280b845510008640c4038030240301c9a5422034194034201d58000020f009124560310b80c02031034102d80140030b000401c8175408500c070382c107405d0034802c07175540380300c00d60b103040d80e00000c44001c0c0c503080d04400b038940d00440131440000109115111340300180c020b40000e140e8541d0300d0300411171110302d1200441e01080c9800c07010340c00650008bd1190b500c0d907120400712013000c1442d95050540d5544030016000d40400a0a500d9025140c2c0e1110301c0f48808940522140d03d0380b101071001c9603042006400c141c0750800d140702c0d04000ec81d412803280100109001c160ba0380700d00045096511608040030b400b81c94920b8107602800414408013400c0c010417190083c40d1610001200c825003100c20141072180010120b01403500c1a441d5051101001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280429433 1250 280428183 280428193
    0x1707080106150215040c050d03050c0111040f060806060405121207110a0b090a14030109080d060603050f040c0b0d29010f0504032103021b070e130302100e0f 69
    0x210300b0a00070007030003089000103020300204903100e40b41c11014039015680001d8803601190070241030018180c1661402e409000c0300384103100e84401d0074080c04900c081d16801041d00c40d0301d0b00302e035140161000d0b002207081c44809001c101d403a45440c4255000c0754021103680752010300e05a00581010b0540000031405030001078120240300d1800d81748144284203592415000396541052056801488200d660143c00c46008118000003034007607445202c4018000079101c1d607d81c5da4642503078419503940d581161903410811100360188196070b44070701d0908510149107443d55482d0fa12403040c0c01040c4003601c001c141e0300390320317185644940130095202c03100501c1c400d501524010000d01600704940094011503642121030310074001c0d40d0407203078084000c04585840d441182c0c4104044880007081545c00e1019a001000e001d401d10b9201c2d8070b05016012103800c000c3c4103c81001c0c0244086e00760380c03002a101d400658001001890001c0d1500c00103114666144000e041c48091601040300f0302c40c1e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280430683 1250 280429433 280429439
    0x207020f0307060c0507090c0507060b01020111071a010e0108120a1407050307020f121515031608010f11030604050a0603020603191805060408130308120415151707080106 75
    0xc10084e0103101e002d54200c60205075180c00751803d5401100120703000a2043c07021380c00040194002c00d080c400140004603400e00c030103160000903081444250303013110824106000e141c0c820305520f8003429076245103007401e60601c41455501e0504200c101c040c0c100008000038041d03c90880c00d8114841910042c0d42e51807039040c001d540741c0000c00281e1081c0626544102540b411000310380b5031500403800b42c031440d0410104403010000080c0031800c100c2a14590501507a41404a2030030510690b032070000c01070030f20b40ba0601711243d02800e500c0300e624201103407503001c1a401c00d42c3d40c030030350440700800d10340d44100600d0041e181a84c0003d4208002106120b42010803004280712010201d40030860b05011841c0140045801d00b00540aa040f0801050200760b42800900d69052100c9601c800d00d5503980c0c03464442e47c054244a030440d100c00c070034071003002106543c480440c808280144000a105040c4990010851241420400c21001801081b190038801e020050103d03a000304400c41d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280431933 1250 280430683 280430687
    0x702030d02040b04211e1e0807030915170601030e010e01050702010c1805040504140a050d3b030703150c1e120b0d0b090a0212011a040207020f030706 66
    0x15005a040303854a41080384400e0017003d02c0320400a0f084609000e01541c40381182c18a039110040a48a6890f0011200b034031400a161500c0c030741d44240b80990b9140c01c5070038018481c50765034001d0200000c0801845450b1075000e190b0b0440c0c4490082407520300c0e01c1d0303040141c0040442c0342140c03880f03508181c03c03a020204190b0002e4441c120680090190303116007901201c890403920300b10310007066210380034030060a1550246038064414040b54003800c00110141c4e04d0010440310440c0e1603444200c11802c1c8a41c081d91034a24000708945041c4840c003540b0107603110014540001441c0b400800700400a56010403002000390f80050704401c1d50300c0300012200141c0310f429559004203d0052811aa103140220078a40e02541c80c0c0e101e04d80c82d030510241c8005880030381a901c4d030094103800c0000c0440c075803901403801040d030703c0000c01400019105101002d00d011921714001d07498580ea0a4103036614064606c988041143d0040e0344138018800540c0303031182c00d10001d030117108501e40414515 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280433183 1250 280431933 280431937
    0x1404060504200618040204050909010606090b091011070504020a0201020909060a0b120a0f06060203070201020f03040f0b0309010e030a021e03090f01050706060905072601050a0b030702030d02040b 86
    0x2034050000720a100c1e00007202c00b461003140951054004104002000006126102540728448001d0003d8035050707450001512005080d100e05486941d01d40041201642201c424001010400803c9041150050016211003c1d43e81d140d01030002c04001c40ea003024061101d50090b040080c0215250580960028001d4000d41c1caa140070b0410440480c0c2c451411460711411902800c2c407207482c142c20601100d51a00d0007401c162000d035147c030107202c00b10000e4040e800107814640c1c0150b84551150000900e001c0620810f203406400800043c0641c4800d11094020342d0000010070f552034445052030b6004111807081496240004a040c05440c3da022030841c01842c0c00303880004111100140054a81c400c0841c4107074407010030041031425500417005404214054480058841d69858220068880440c4d4038000143d8800c2d150251140d007165441ca001019190102d03558148008541c800d000c5000b4020b94070004400504010720820445600d0415440207545895441394096459 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280434433 1250 280433183 280433191
    0xa0f1407060b0d080f300c0d090c090b040b04050408030a0207080903031b07080d05030609090c10021e0105090601140d06090b040606091b050a05040320040516080708060414040605 79
    0x21060240020303003800302c6c1c4409640314104400012060b141ca80c0030b0301070f41e4082c0308410143e503183d060f854042646003081c0c8004041c540c50120b0354800060030082200c80c18141c1c60f00c16850a414440451401010707640e2004400320b0040e07a070689424044010700500d241c1c141e00d4440010400600490504c0021050300f0741005c030b1703100c02d46400346d041d01d64043d100c0c1140041d00500014030545022180c0310b0704031011106481d246417201010500203418610a00702691148a9000500141d8490740b1a00803922000300b242c3d0402d0b00000d601c1d5841846407522640071101156807a564050500e00c2c840d5010908014880d0b0b203140402008004175000e0301d59a103000c80029001d503140c010000c1803003860740841c4c1e58003841c0d401552160001d02072a410400107000200015800180000300c079400e41e45d000750003400440070002a6500206032040304d2040c1031400e010a50000c00c000c2c0c2020a908200301c2d103a5a050201e0b0040c03540d0305403402404400c2d0b043c04207120b595170041d070003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280435683 1250 280434433 280434457
    0x204080601081f050c09060c06070f0e0a03080708090303070f0201081302010e15040f0605030901061a030a0203150a090b090901060b1b1606050a0f1407060b0d080f 72
    0x200d60b903200509900d0748914994488281624010481c8100d202d9008a0748440540c81e600d04085c0168040b8030ba540100342140c1c9150b01405c203104c0e03244d800101c480f16148051604d251101d0420300810304403035040c071002700799030381c080782c0041001000d1040d10181d40018048a407681b0b12801c0400d210111404240e0209072201c02141c1c510f0030624149800302d40684480b0302c5150008244120150180c80240b85000d06010215410803141a200d0081071265100c540b2130400fa0001401c4500715404070140c0d410403c4a0940c62920005a0358804140400161a640e501c920070700f5505a41d450241d0005145c00c3c04140c8000702d0707224017080002518442c2031551003210075422500e82c0d001e2011089005e0009954014442d43d071452524495400d6405481c0707035100c0380046420903044000440d502080d0811941d034000340c01c2104a0700d0b490300c0692404160507002c250300c55944064010f0341c840c1784040e02525103140300da13141e41e4000380d02c981d00c0081c40c82003241034119420030f100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280436933 1250 280435683 280435693
    0x2030a03110306060a080601111618020a0e012001110322031b03020c120606090a060e01030602070302010b0901231815030a080715050f07020a03050a0201060b0409020408 75
    0x10480705a0001ea9100d0f000c05000b440c5024030f03141041d14102e5004084604024111000314900702d0103200201c2c3c41304a0801a45e42c8030b00301760700c082c4009000d15004107510310610503450450361000d040103001f2400c1c2069040d002580b45295103516810894096942c01c0c004400c80a00082d80218450840b00f1048000c141140d40703c50311250078810301400103081c10140c04e018440c1c103801400a43e00c01d0040710740351210040416061051014003090b80e420904c20485181002a43c4070303070190100b05e0402c81d55060082f01e44000702c1c1030001070004c5601103401c3d01094002d5204941c01c0500800b25442503a40c3d00d8032403817900702880401d41e8162800703090011410141d08804642d84012240c020316070721000c02c440e03281c01000100d940b6102c1d400940380440c41040c001e22502d806201c40d5039440c441120710b1001c1c1c40010f0501e1852103495030810800c1940480c104c40150350501c0c1455075030014482c02c030702406842c1c00c455910304000a0014030340b01c0d07070340c002d008803282e05059030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280438183 1250 280436933 280436951
    0x220f0f0f0b070206151e01080601121803020d02150f100e090106050f060c030304020d08040509070528021f0f020c0109050606030a0b190603080c03030a0b03032a0102160302030a03 79
    0x2c0143c0000014030b0360040000d00031000346c0d6000f010005e5002c0c07818508140407a00c0c540d00d00301a64a0b46d0701320b1100f080d0000c1d604061540c180300c0b12172f40d40d1503400101112502c9003c0301c008000001c0100321655210000300b844241c820569100515903244143e41608201c42d0071402801d0034424181301e62600060003500381441000c0d28908070000c00514103607034071502800060480c05104650746041000089291b036100c40419000f415640c0d107050303c41d1300b4945414005614001740070110882c40e4901e40394036600013044400041d007080000b03000601c11700d10102400c40d4402d5000e48500120744000340410560000320704902a004584154075860240b5403580c03030184001d881c20180b40001107920006080360940360001c0c400005249070750351181e00c42c6400c040300003c03c03500000107204480360680640726601c142107002e9031808601d5900320b06190b852412803a108038540010b088490300c01e5054600d0100184141c84840c840c1e8034000391203a0045820402082c03402c8410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280439433 1250 280438183 280438189
    0x807020105070203090904020303071e060b1509100e092d100b07030c02100509122d0c0d0c170307050a0b09100608010203220f0f0f0b07020615 63
    0xc601800340b64028602d042c0940c8203000551800900076609440708104c000b0000303500d1035410380400c0151070b018441080d03916240040e070f004001500d01c0380c1c80b0780034200f903401c04e140c04442036030804a4404c1c1882c4880c103402d4469025080c0703c140d100b4120b03402c0000400c249085005200d0301d4000e51036410b0712a00c0d01800707880741646c0f101100c0f0941303001417110340c500000a058841c013034104800b0354122540003441e0401da804100c00006c001250301250742c2000d1036096400246034000d0308061004024444002441c111400c44070302c141000b443c98800140061440108042c0c49070f500c6041c103080c8002559407030303c140c41440300c40c1888500090400320079078075500e0b4010041c1c00340907240d486440c03e0580140095816004401c152000708145104003001818140005030720b03031501003840f541c3c4184040c802e20303090651340360303003030006403200080d1222079031120018411461505044e448650f52400c02809041d0010a02a0319038000074000e110302e5445000e5035054040a044c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280440683 1250 280439433 280439441
    0x9061407180e0f04051204181d1506061b01150e0108070b0d0209031c030b010302040b0409090f1a090601050a08030711150403030309051506090a020706020708030f0708070201 77
    0x60300000d0300b000e2000c101c1c1101d40c0d001c2c8a80041c003c0e4111500403101c03c00c0d03429580d010350700854039145109101c80c0410420b0103036100304100300f51001d2594115200d419104c00459004030490080c400004480f40d40d46001d40d6100c00781d100c002c162490b17400300018020880800e40d1401c650242000186600a000085041c4c440c0880079140c180e181c400d9120694200b15070160100e9000e100b500540e4404010b00005030b00b0211056080e14140748014046502c3d50503620304250042000b4080000140112401c440c640c9030b0015402d00b4500b00720300b400460900c0244a640181802410700c01c20241035402a00078606a41c4240d03600d81c1048120f00c40c900c6401100d800521118020400c81e20310300d860303500042c150070050001e65089182592154108a002c40d580b040494203000c406c00a00c0d0380c50400c1152240c0b1130070308400103442420024082c0d020160005401c13001c00c066074041e00c54469100c040152a424010600400e0510880b00f020004c1d040c400001e080c2441405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280441933 1250 280440683 280440689
    0xb2a0709060b03271f02042d0803190e040603050a0308010f120210030b01171009110408150702030409020304080c190b01060e011107090c110d05090d060906140718 72
    0x8018951800f041c4403005c401840440c07000001d41e802d00001401d100c0346d804107202c00c00c02141c624040900c02500212038a001c0d0000b500e96030080c81256591016902c41001e6520542003040840a51074001409402260801071440c00b403034241e403040503004a6100d040c0d45003400c40e0804240c0f10780300c0c68400d90038203c01942c404407000b8a002c485009078042018850107240911580c4810082c1c0c612007903003540c0c50100b005042c20104110b4603940b2480480d1142006c0e07480c90a0329000140d91307140143e1090f26000110440401c3c080d42c02041118018540144195142d14141c01c0c9506c5c40d4019103001c00da10300940c0c41c0301e50052a80d0800c0115158444240ba4040c2d00700181142d0010744525058140081502c4881c41c516040014034000d04821310041550382441d10024644012584510142c1d0700c0340400004d0590005c041d46d841c082c06960425440002e81070071303009010413940181c0000d01c0e0a60044183c01c19990552181c00c0b40d4507075040304140c0c2c030080445940b40744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280443183 1250 280441933 280442011
    0x150209150a09091d0a050c030f1f0e030d050106170105040510090b061213060c0810090b06071b09050c070c050d030c02030d0201060e010b2a0709060b03 67
    0x1c40c103000450f56580701449250b40500150094404c45500324640803c44006a466601c1005100c81d070f443c08000000c60406000c01a041001058000c08400081102604520b5480351100d0803404410025118103c160309814865035031b60300c1010f0320002c04050001c500050007800403c9905090003814065418170300903502e550b2500035242c000300700c040340042c3c1c00881004581210410070001c06d000c0c05000d07012050322403841c03524034101c80ac407140d2481800380aa04103c42c50352600c8656003200d841c6c1d50040360030851400000d449101d9880000e11851400466106540c030280c3c0c8101a0707912928100003c0d2240407002d00d050254000061a080c20014103201a04000c40381e003410500c24242501c0210361940084d0515140710402c0300181c1d0350f0342080140c20360f29015140100000e4280d1403500340412032102441d05da600303a07c2000b0140340c403802a0718000700311040042c01024800c02145445a450140f964415104d00000d400c00c10120801d40082d1050391355585030034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280444433 1250 280443183 280443197
    0x120114010c0609020f04020d02130608090d03020c160b0a020f0c0312070c030c0803120604020307090504090c0b0417010e12120403050c0307060903080709050f1c150209150a 76
    0x181c1e104005083c0c0920304a0704088000c800410689503800a030400f64110358016131210401c5544654038803036980b1078001c0204850030710201e03070404500c01d1404c00309880c1c00b5030346401d0380c40c520740351014480300ca01c6654107440e00003551020000240820070170300c1c2d082e1004050484039030f5950300d40013210306070326070082c110f0001c070250508018110127106059141007903580783c845060203460760340044c803250000100c50040c4040301000a034080e108680450940c245007400400f0311801d405124001e90b0381e060f040c0305100008003101d0003442001c840d681e030b664950420071600403100f55a8a125070038500e420030340c0c4101080b80b400100482d000142005c280c2181d085000c01e000d44150700b8132000b045400700e0724106000404519005600c085800d421525008218140c01000041000744540c0e003840941d803050701012203100c00f119018a03661000c80d40c8403d40005034001440d203c44500310401610664014140300f1b10100c0b50301e05001003414403c0114860910520005048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280445683 1250 280444433 280444457
    0x5060301200c1507210513021c0609050708010e0f0a06110715060609061805060a03020d1503111906030f0b09040b0109111305060702040e0a0812011401 67
    0x50310000d84001282031044032205044030b0f4a08444080035a140d4000603800301c04084a1084c0005110f007040e02030008001a00d07104d003038005403c811035002841000021000d100b007000c031110500130b00b0381140040040c190300d85000c5039118094070130b1a8065081a810206041d404252040348281c40405080c2c08155a52034200038141d284d086102c5031003d0090070080380304441060701c01071000d200055024107145000d04908125403001080100854075007848e001c04504810480b2025240b45496500504069029000e52454880c0c0301c2d203030441103055206003c1580c0105e0303004103d0407d00007225000e01c174940304c01595112800c10141d03002c1102c50f10982c00b00256000600c40068200e181c4400940e1540e802d4370141c031518503807001405000341d9846100000c4821080f081d01c0d0050100710082100070310b200c1d01d4803492000c16080199220f903004410607000d81c40607201000d08900d82000681c01207403641340c500c03003400f0001c541490f0400304980e406005846010090328 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280446933 1250 280445683 280445741
    0x609072d02070b0301060903051209030d0e0a120c0302040b04140708060310020415030f06050a0302041109031c020c0904021c151a1f0806090a0b061c05060301 70
    0x860094004520070a0b00018010450074003442c080d14156a4040790903155040c1545050342030035050b1104001007005425039640010790800b40f251a041c00340d84a8248070001e1074400c0c00d548440e11000c0c941d004a410444000b02c02019240b00f02e8041141e025680c050104035040040411002c3e04510081400c16005c1c500480d400300c001000c41324102d0400700f860050f6001607104c1d0040c1d01421880c210065003501a000d03a59010140411055140c98001582c46849200c040e016554078401100980140812a0309249010701107076407004000303003c00345110560700c6420041c003c1d102560703200d00c1c101c110640070319002020700d844509d00c00c4001d13950b020b42d8402101d091240708500d65042c0e6290103002500003a6805c0703000102c4480c0140b00841c041c069454080d041d00061840c13030503420030740c23070380e003200c0c05807501d04030f40d070b50010004003c0c50840a2103038404408646840f01590713002007042601711061041c00143c8500c0c00785820b0b24020042818000d8181c000c50400344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280448183 1250 280446933 280447007
    0x3021e040e010e190c030903030b011103030a021b010e1f02120a0c050c0604031d1f05070c0801110405040e0c01080a0c1205190c0203040b090415031208060907 70
    0x9828100181000c181303803820079088072180c14140e40420748820b180c0c0d0a154040c424100040d400f0b007840620100850a09600c030311005200582c0c0700d80c0401c0310401340c8019a03603090307031002901c0200084541590a10350795100c42701000014424021000c041c01032a00958210240c0070001c40c4d0f10f6240c0541000282801d07014081c03c101c0140122402200100074407030045010f03484002c002a10762090080103c135030441c1074042c509010104a00c4c04281c400344030b6100b9549000b80c0c4840c4549407805502c03109501218a079824101d106254081d561b00610458104070f40400100010182e050381380c8440744905030208501000064542050360040300d141501d5141503c1c0d01c6540400c001b0481f501030b201c210000f0000108810010142d104000a014440c001907007018a46600c0100c140310341e03410f4500407500c40c41a0b201c0e9000c088051000f07141c1c07100342010512003404000b0800c000c21188a03104041e000d0100340d130a03000d50301c140e440c40c3d405d0301c1c403401020300c15488100e06 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280449433 1250 280448183 280448191
    0x605010807060e060a2106060809190605090c09070801080d0c02061215060f030405010f02090a17120f0306012a060905030408030313060615080a0504060b06040603021e040e010e 78
    0x1208041b520407004e00051000c03100d10f0703515407800164a5041c4003005124140003030120450340e00c141d1124004003e2030710300c00000d07507200c0e8000c90680d0340c418200f0b0a04a110100a80100c0e0711030901030b946400041d02c0f4141e9000d4002c66000321184001103032008103245011707400250802c80c40000041c0484920f0780f284c0e03038a42a144030f80c0801d01184259000c4034448040140110501040040c20b00959603440c40c1e146042d401e05018000040280d4100c0c81040c2c10801d8801801a1803281440000c1010003402442503c038a10001030102d15401100c0181c00120310400f0314001203040d00c100d201c00c07070320304216002e8001b00d5611200113118141080d5082e00c0141b01c0000c0c090f00400085108000c411007100d40280e01d0324022003620f8041d0440208000c1000c00400a280d000386400e500020040012540d40c6580c14154010300040700304c03a40081d80064081502c40d016001002c0c0f29151408001da08030118400c8080e41c0198011030344503481c4440100004083c0954003a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280450683 1250 280449433 280449437
    0x90402060a030e0f031b060c250f080d1a04060f1a0403020307031b270f090605151201200715020a0c170703140309120d02070605010807060e060a 64
    0x1341e480207240301803441c1c100341c0c1d0490420694072403801401e4030078032026420a5074180305d1410481c0d600c440840c0841c00c11660580c01d40d0f0f00b0031460612280c1c28003c0c0002d600409110340e039803803018558018040005000d80022088004680310741410b20410080b19401c0b003140080d107090004a0348240b000700781ca800100400d02c40440540d03010b0101500462150074461114452514003030383c41d00c0d041c2d200b1143c2c0b060680b000d0100e80c4240c907289012410441c00002c01d050000c0349040104000f98000d4602c0d071819007001039640240d41c0b000072041084415482401020141600742c0b80300c405c02034420300390b2440d440041e03c094800340111501c11180c040c0070b00d04400106040b40c21050198000482484422051184061460488e90321001156141c0025600c01500980e0520781030644804004005810f5031703414819210751400c02c47c007490b41d80c8424950b510187d001140e09550b82071400000162000001665a04440c130310380341c95030840156020406190001015401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280451933 1250 280450683 280450693
    0x6030b0a17070515040303021c12020304060c0e03011503020603070311180a0605030103051e010204090204080609160303082d0903120609060d02120c030f0703050606090402060a030e 80
    0x7030a064204102506501c070103008050003443c0a04210342c0c01c0000c800c00c804400200320500101380d002c01c1f80c001d84014410442030030080c1d91400c5030305601e11404120000c3c07000c4107020810810360044000130055964102850803500105070803220840f065030016003039407004000500b4290060359201c0107a04000a8841402c5843d03109580400c2c07443d070079100f030912210701c0740c50010b0440c000340060740b0302282198110b55419a655418040d518840e003100601070640c4202501120080c0c85801c40564859907200800b5035503a106070f0f07115481c0e00803d03505410100400c2c00b03107030460350590780d605860748030031100300c80100c4419912408155a0b4850851007000002150f000e03031a0310004559841d0080315180d00c0ba040a000948200e240c0410b0100c41c0c1c0c1c609503044400c0d50100c6052801d8440c490b410352030484040c09c019098010304600c07027141d01000c10050100d078020300c00d40b10543c0d00d4800304030018a044070020340c0b1031424041b4070800ea00c2035200c021b100c10200100c1d9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280453183 1250 280451933 280451939
    0xd1407020a08070303140f090909070302100509120607020303160c050109080405040c11100b0a0905010f030b09010c0507060522080a021603050c0409030203161a07080402090106030b0a 81
    0x5041069a50882c0825901842c1c04100300344e40121907500040540450b02c0c00c2c092458116215845401820f0f4424404040880d002c00d600b8000c420085900030002c1c4002e0314180c20280c5180c21160340580b06100b80700e8100c58099000c201244240d038150b010314515130340d60501011010b8100c3d0301c0700400c03003034a0070800051070910508130b425004948a40d1120724010811095039903010fa44010000245802282c8a0f00050405100e4100d01400300e0402041000300c0c000c21125445840c003181040000204c2244454206003524011291150345903566458242a0b54101102c040018010800345011070119401103820001081d410223a0003409060781c1c0341c09108040a440880001404617400340d01003244191450703030700c0e007508035091030341d00c8444d240c40401110314041c507212244c0382c00b0980301384111451142c00c484560030004150408000210f100c80d040300d414840140800e000d60b0041d9941440740d9030003080020160f0a20a0840162102c040080d4000d40864004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280454433 1250 280453183 280453189
    0x80a1b06020a090e060102030702100f170c0c070608011202010e0a082401150c0b090309090709060e06030f1303030204091404020301060e0408180102070f06020105160801080d140702 80
    0x1084080003a0391a854210308021110b13804c0c0700d0240100c0e055500c1080010010303114141e032081401c81c0e5045c50a40d0021030380085d105001c0c1007428154030109003003080075820310b0b0409004d035443c0307102c01c980d10243c0f141e00a9030803100a01a00f9400c212140310343c40158400d1948116043c409020200d83e10780d12204a840c100361000072180c48458200048500b2061032a12070040c06080c100a18510150038054200312900c08061310340209000040d01005040003201c682e01c002510b4180039140442008112400d1402500001100030210022900e010802c1c1c80c040c0c2d0b00e60034040400c1d20745440b000b2031160318900440516800b030000194202c681c1c071516440c900224a524403500e0144101400c5076016040100c80040071002e10011401c42400d40e038110341e099910f2560201c1500c0181d183c5480f69009051000c004040032404607419004140101e22000c4100c2403080d2401c0301356842c00c0c09010301400e651000317043d00410ba101e042070700b1200460807051131403e030070b58001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280455683 1250 280454433 280454437
    0x20406150c02040f0507090302010806040e0a150c020607091403151512030406021203041e0f140a080d021809011d090102030906040b040822140a03080a1b0602 70
    0x200c04509407000c84815800c25005000e40e008061804101c20b28143e000a8540c1e403103800082d040092000001e107043d1a103a200b401c0c81200c2c48221104c020f050325062b40761004240c8456512810b22400d40c070501e0000410394082c40c9540c842d4072015041a00401c400e460b02200c0c1d035854401c5808052070a0355406c0c056010b03100710810a21600d603003001b0700ca086480c507945d2004540c800c00c402c204650340851529403212035103401d0f075960b03103076420045076028109107181c0d807800711410003204228000625043c035901c01c42e005943c1a030000c0c16035444c1e030218000504041c40402040781c44100310b0740105000801d1920b0030f01407203c2040070801241090f00520724501d9203540c08001014a00c1c1481e51003080503000758030b5454001103054031824007610013404158110003042c100b180c0070b01aa0f07513035030408600410f074000c01101d07000383c49082e07c0303806a05450303a4410341107070402e1844442070b240c006000500d03241319148126040c04411080c0c4040c031001c94031010010b429400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280456933 1250 280455683 280455719
    0x80702011e02030105190e010302010503060d080a020307030305060f0d121101110403050106150903080304030c021306090b01090501210216060506311e0606020601140d080412020406 80
    0x1d0050726036062500344606000f00300502c84482541c10382c100501c154002059054940c20711340240c585d1207400c0864104028440300900300038012803090031307050b0700001074030140f0300aa07001e00035038407400184441c826510b6030064200c0f00e86404140032414055804a1042c25850440c84040541414900310717031128001031260b5a00140c03c2091240901448020741403842425070000703076560006c1e0031050740d0f01c00200300c0800400003e051501403050a04402e4024184134080d548120800c8010805070103403110051a00d421140154400c08003113007510010f1b141c101d40050602c5403440e200091707130801522549c0030003007480140c1d030507181e005100d4480d06010546040c800200101d00d002c03000e4504120040c4031010081c030100041c9802c43c0802c14400180600c03940180c0d0b0101e11070038200303040642c14080c0c006140381d800a89a4121540010a004082e605e40300f00081d20300302e90380c081d05514082c40140118481c00301004e01080c0b0081c40020025604c1c1c03050b44417041c80318 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280458183 1250 280456933 280456991
    0x10030c051b160803030108060106120b1810170a030305090109081201090501060302071a04030c140a0203010609020f070b0c040807090605030d0c02060f0904090f12021603020307030308070201 84
    0x11002d00c601892004811014140d448040c1d42990f040c14015540c645051007002d04128100488440ca10940c0e0320551001401803c40d004124444210759500c050a440c210121940c003d0000741101d28490100f425108101c058549215591400c078050100074091229555850141c8070010340088000c001c3c182d4801c402162a614004500048840503408102030500412845c2c0000d0010000c280c40b090341c900040e903485d1920305080314214900e0380b00501c200d803c04040402a000001d440c50301c5442240203111842d1140707221002e1740944840a601ca61040c840000084c0c0e0a03585c01c1d5004210740005820700b41d0f2410704030b1a004d26075100080643c2c0e659014000d90806109001805000741007500461009074081480f9204450600100380c80c0800c00b174001d5030701d80d0085407135650400b5103031016400508086010390075084d4010054410f143c0b0900c1201203014585003141e0700200645001440c0d0344007030321031280003818481195a110703003000c01070140f15940c60403e1215 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280459433 1250 280458183 280458193
    0x8030d09031d01020601050919060b0c0c180604050601110109120f0503070c110316092301180b040227010905030102070c050d0f02030a030507110f10030c051b 70
    0x5040141c110350807540c20140c00b03890948104401d9800007080750465006841c40c1405035128548002d0510b4555a11800c49040090004006003c00c010707040c1c40043c0019180c11039001e504000c1030b007001c80d0300d000000b1070007400990a845c00c0e0f80001c0e88030340181481c040c0d5007001500c507821525665800c95006d80824103104010394007003404ca80082543c241301e455801c02c0e110140210500b80002440b100c0010b06000c120b0301c040c0965020203aa1114200d0055115604c440240c042d160840c02d00140407441c6001c580900d0115504a45c203072a001440d002c01c02e0034034009020030404c4541c02a400300000d9001d464001140b041d00c3e45000d040440c0108506d00040001c030195010611a03030040c41020003003104590010b04a80b41103c1c11a1441150300e0480c2d8809140d040c007a49c0350080c48000f900341a04800201025807145002c5003226050101300140d9441d420301c069041041e0009031000e0a0003948140e03046030320b03403c250f42400b5000c02c0790803514035400700c05107940d008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 280460683 1250 280459433 280459451
    0xb01030615140405040507120804030b0f060d060b061b01020a02060a0203060f01030b032e0c03063005010f02040503060c041505220e190b060a1808030d 67
    0x1aa120300403900741c40e0319518154620300303900c0c6078101d49820b141c030384560381c1c4101003410000c080201000810700d480c100396000c030003402c0a5040350028401501c01007100d03000102e885a084c07065078840d040c002c0c1240a55081500c51000404e48040810f400500c200194030a0303219a400c06c82813503000400240c2c0d40c424241c0c0c000d00b0b140b000380400042c127006000f480311990710540d0a03400c0c0c800070b03e0001190040b050000f45004491800e200c499186409421843e00d00940c0d02d1000e600c0c2c104062202c400b11120480c111810b074428852281101440d4003000001c1c40c1d0307039a40e07082008a00140301b80175503c401d421a600c40c1401d000c4141d002a0800003401c05100855100d141c07010243d0901d45421402c0ca50700812031005001c101c8001032540c800d8041800300f004103802600641034080d203402e140200d401054074200c60f0b0152015003854541168012140400c0c80a402c1034203102c2507240c1600e4001a01800c400382401c03100d4040748458080014018144001c42c0100e501d0380 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 280461933 1250 280460683 280460693
    0xd020f090102010e0c0609040c09090e01021b060c0304200a0f090c09080304051c050a061e0510180b0303030901090605011a070f0819081006170105040e0a0506040b0103 74
    0x1084130340c400000c0d00907146800c16545d41a0542c2c032101800e031404214204036582c1160807a049400240d1082d01d4000280c0303031188154090180c0400c6101c0a030441e84204c0c00059840800711070300c843d01c82e02040014001044404400580114101c0003405011003000140500c0400c2c0c20080102d455204100829642030144102507036603810000d4945007400301664403845070f80a80d900601c0c002c00c0d40d0740022000d1500c3c2440d01d42001c10b40b44621810701e8408050000d03110401c080000e8443d01000f005003500c40c44d4003d003030000111115505c1d050401440b0700a042ca14030082d650741440c1b100741d0320f06000451103043d402c1d00002c0d0080680c80c10508550040e089090b9660b00349140965110417441291700b440c4d00030180310065401840c0c03c1c20030780701e079a0b40e4403000c40b40e140880c5207403900034420034011400400e51040311a201c22084031494031204103a01d5401c0312000401460809900810218404000f520180480c50300c2c0d20345801e10a46003102c003c031114004200b804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 280463183 1250 280461933 280461941
    0x60c0d09090b03031905040f03050a0b010509160806120106060503060310060315020f13180c02030306030a0b130606060807030606080105090c030a15061206090e1c03020d020f09010201 81
    0x714004800b080036512440c00310707580f801a40c0c1566070101000c50130702170030340c062002d460080046c80c042c20307541500d078508a0303205d0440f400102c82c80704000b0300114040c50301140603841003030004842c02110032201c07070880c5e64042c00790103240c002d0702041c0c00300c0d8240c0303080c003448010300b0385601d031580d40e81011001d00d40342c00a5070354803d40d90352a18005000140181240c8030140c11000000b60319400e00c1c401c2c1c001107220b0701c42c1210a19203030080028500901c001c0214052030544402c000c0951a444107a841e0301c0103d03600e59042d0020f16405000424210304181c10070826008417071009500d903613440460340c4580080c00891004030420926903414001c0d0400761810f464001581d5141c4400f1590f0104d01a200c070310500400320000f00038107034076480490043c1e08106003e202c80e5903020090661204114010081410710001144025050044414800c0e03c1401005a43e003000ca0300c02111003d004c21f00304241e000c1081c4003a84a0310b0000d03240140303040864942d10500c0d038002908407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 280464433 1250 280463183 280463189
    0x7320c16080607140c01020d0906060501020118051906020d0203010e0603161a03060612040606050111010902090402040b010207080111131d06011b0b0112050f03040e070c060b060c0d09 81
    0x303510036820880000e622100b12508000c1c2c48030304c0c0d52140c4902d69600d0280c01280781110300c407450301007010240321003900084102c0f0401e070000c0000c0c5001140420f0450380b48039018100da40f00c6403686001c0300084212840490081d41d00500701002e855420003a6442a400418644030010500100e46400d00c01c10321103d069410025543d850131100c462210580106000246004000a10750752510821030b103408056010318200c5150615040000b04100e000c0c1c80c0c0011b079a0804a803c5002c1442000150360300205003804c00d41d500c1c0d082001078061802ca00381113009961001036104001d00440072050064240c1549030303400000742440074a02c6901c2011400c0c01c440c1d0b101d03644c0620107a03064210380c1c00c0c40c080c0040e4180c4c803031000074050f8000d00240f0b04144a400012841c0034101c0f404200e0303100e80c0070f580901341c000004581d44d018901480d41c2d440100380115403d02d001ea084010b271a441a400407440050241c0050550341100e42c842405400071458400d21030f5201e2000d50103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 280465683 1250 280464433 280464449
    0x140d020702120604030215070e04091a0702121903020f0c010f0b0a03020d2622060c0302100b0a03060e0105090d0206132415030b060907320c16 63
    0x5514085d01c000350759a2004548101034010f06010402a82c440d080522116601070001d02004c0030a1a200c0d000381c4070014210900c50b0108081950b2502c046152450305e914034000c00d0138109140038030390302c001480340701509240c0c1c2048181c0b03000b102c0401900c1c2d02c10341030b000043c801415001c07030801d442280b0344140c4502d041c503400b480140d558103036504840360001440880d441818101052405512500704405500824111095203100207011544014022401585179442c0029242d03c40d6054000b0090780006c50900b0001d0103e5004103500c10340189840780d001e640b41c403100111902e5514840199440d8010408165000c025048000f07049100812283c40c0408042c0302000c004800201011041841c4162422040d45011448881e505003001a001d0188428140a440744411a10000c81c200020601c0c58261000c2d032103140f20341c540440c000880c442241721901245100038419003207925000010054070041c000018440c80182410002d5503081c2031042e81035801405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 280466933 1250 280465683 280465693
    0xa03080c0d18030b0405280c090e0c13061206091b05100f200601180203090307030c060e0a030801090f021612110609010903111902060a140d02070212 66
    0xb2030014584409045980100101c103d6480d1803400c01d00345070320b0150266546415420040403110b6910740c000c0304501c100a8082030325596602c5100781c038199007403451242c0050103201114100701460304000072841c00c0000d003407500d0360b0102c150081c4002007a503100395070b100f8a0080000c180807101c1c0800044404ca00c1e110318200026101103401c060a000b0442c011500e00e640b1070040e0034503420584101d505204400e035240c0c6040c2e4600007441441000340e10070700954003042c40d610846e8040d2240c40c024503c2c08886803000d40c0c21800b01d1604031038203607807005101500b000510049544900c255581605d55140c00a40c50582d8880d0b03d068020380d10412074150401100c0640c1e0340b1043e4401111200012400320656003200f03a00051100f9008150420040c1c0c04198002088a440307a140c812007140800d00a0f0f07079401c0032901c040240c041084a9002516182016100c5018285041c1c0b042c00001c59012100d41c114811406410750045078030021464a80c0403640d4a080c2a00140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 280468183 1250 280466933 280466957
    0x40f0b09030601090f0b03030d0504030230090a0305030a081f182f030f070c02030c0d06020d090c030215120c0f04051809010b0102030c07061b020a03080c0d 69
    0x762201c1c010310600040e541d49454114149171550001c0e509003d0041c00c0d2920f50840c2501d60f400b13460100c5040300140600c0c14000c81071584180729040c0d001e225503407a44090400481110030398403600744d10703501c01d40440000000900400c0240468081d42d0b80e01400f80c142400f861b40d55050726a901901c03410f410b502030000180d54006400001d140b05004160f403510019032201000c40f0352021080c0ca04140300059105d10110300071401a0041c8a0700b46942d03540c484111202c0c201204001d605800c800840e1000340f500440204072103002e514018036151307401d6501070403210300000407551203000340410019131401e4403900740c0c070450301c00c075841c40d00022140e89001e4640090032040c10030b01c0440c4915121494405540143c031015009410f464044010095201001c0b64094171540c20051480407070351011041c0c1d180c1d089608001c24170303a403c3c120181c440e0f440f8404402c640f5018110f0580159a412000340000c43c06403584681c0e88104070400b5050104080300042070141800e088 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 280469433 1250 280468183 280468189
    0x4050c131b02010515060d1401300822091d011d031903090203010203040b04020f04141909120918020901050702040504020339120601090504020105040305070902040f0b09 75
    0x7400011030106c4041d962006401d80340c2004090300c20340d00355184900d40c004916543c10060780401c00c035449c0480300c03510041503600034505038842d40c02050448207000308640707450040c020001515407000c1000c225034640708503604541107001e118103c0041140d034503040350700070f208a0300c04c141c4a60f040d00310f045010900c1c1d65a4416140013501014406140d00c1016220368820640c85500800a4cd62410a4144048405020303107040e4030510600405d202c40780703800d2080c43c0c0769449580b54940c441e44d881c000110048011810a08951b4803031003c0400038501854049100c0300030346680d00584e040ca48603c10300508925040308252040101e500e02c0e0703130050b040c2c3d40b055504070741c0411140e803188003190414803260340e0100e001d169080c0010942040181510740303071411041140e607500300c0508000300c01c542400041e02503040b840050209000f01d800c81c40c0c3c024010304003e85041d03601e603219840d080d0168840b60801e68040341c04c0c0444403103118940001c2080c4907446040170010800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 280470683 1250 280469433 280469461
    0x70501110340020d05010c03060501031404110f0607020913030e010212092407050a02011d0604140619050d140c390f010c0306030b010e04050c131b020105 68
    0x91079841c001100c0700ba82159038424011502c01c2c0d200f0024403030b0078125007006c0e000d403409000701404681040501400103056003d0315100d0b9422650139404480c020040c003006500c40007207039810100403c00d000160b00e498000d14090b8580e92200d6030011010308008060080050829045422514030341416681c28002e4800d40f000071584401d8a52000d00d0b1040d10304001c6002a560f1500801d03540203005000ca94408858000e890341e6003008024060a207081b01c044082542c4039609210500180c6820f5411384140c0344081e115900d00a5107540d0603080b004501d0400c00020303000a4030850401060242e00d0700c03107050500255607420003841a810034018244003a0001580c800f032225407008281014000400c88840241c0001011a07800d449102c22462118650b003400b80034600f0600ca44038050480381c008103840516400c0100c9603407003100140060700c0c03512400c18406d40f181e4910710706004102e60b082e40000c50b040c0600214003a0502c1c01c81801c15039140c001002402e41d11302c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 280471933 1250 280470683 280470781
    0x1021e090a050a05100e01020312160305010b0301050a03031409090124020c10080a0b15070303060b04051f0324090b030a030905041d0105010b090a08070b040513020705011103 77
    0x1040a03940d204000100d20314001d45454ac441707001d0f410103228400d881c00d00540700c00309a070358081c0016030301d07069080e410784000c2c815150403a11074007040001c24800d900c0c41018420500d101403808000a0000e0240700080e00817034000c02d03025501015001c40c0c0301d1910240c107910300160920035003000c005810100080644030070700c52080001485a00c540e849944400c00092005104032186844a07403d41c010f81d00481c040703454402c01180d910700d1007041c2c500b2580010030701e03c0302c40940c0c001d5803490596070300e03000c0c01d0540b120700018200c01e5800c0364100c0015548030b11b604492400710382d80b0548082c0c64031140680c11501c485000300b40e100340c18000b515800d58012984103205808280d060020180124240d440d000001c58802d13500780088c1914082110b100715a01e031544411522790070f103407041200b104400c000820050424403c1d003440c203100030a00505100b055111603080d1815078013002a102c40000c200007003400c0d0078131610411070004d01c0742c80e5005c04603100f4020b101941a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 280473183 1250 280471933 280471937
    0x11150402120a02150a030e0729040b031617061807090306020313120f0f030b01110f070609060e0d0f0203030f0417071203080a0e01021e090a050a0510 66
    0x200c40c016200c40c01c1280d1031902e64043c0141d112500d103240b0f001c48642140c5004e4002900f04074103095400c800288400548038102030700c0c9000c50115400d01d40c40e03207049d40c560081501c00c1c080003031105a210061440b508500003050010340407448010840e0300c2a008025000c03051405014030b80d10303006089022180343d2224141c20743c9034440191111112a40002c00b017074000020426140311041c142e114480c410081420a1499590306940d10565000313840000388129400c10b024500c640c100d4682c460041c14080720902c070704d00c51281000950759204441d603100c00b1f8200a803d910541c004010010741c40c010028070003000001c1c080e400701a40143c05100c20079a800207541c2c05208907109262511412580c0c0d83e599058611450004404009507018502d40060070303a0101712000390250381940c13a030f0940d40d00d10550100070a0030071071030300b015035080c8801c04d10503003e110524140e28101e402503840b00b4040302040020342d51908400c1c040d00310014200013a4690481110400b03440b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 280474433 1250 280473183 280473199
    0x8042405310306061503021c0c2a0b09010213090509030d0203010f0306050106031a1c1202011409011a010c110307030609060507090f1412070602010c11150402 70
    0x400030700c2510310300c00c1c90503000d50050610010070040d19904c010f0846504c00000e00201d00b0501094040b0b0140d9803649100c0541c00b90080d509020035440552503001e2410980700040306494201242c56443c0711004a07600d04000800c144600c08444030340c0034075500c00a520786864020b990b002e503405440b840744450344603008600300c41802c1c42510106030200b4021922580d50301000007015a00d84000d9880364035190010410307a00c24080c0d020342d5203050307982c60b0305250a04140003058000c55200204503461200d44400181c07030800e0558081440c0e4004604144210b0807494100300250444489030316110008d0b802404030b8489946208090a25280305070b62410521480b43c2c02c000301c1949402040f6011040100541c404003900c0d00a800400c03590740d42d00300030b584168490281d00349405501070300300840c07007440e03091032a040400340014003414505d00100d49011280d4015a0150351200c1010544a0388284502c06040c0a10020103c0c0001802004803c0d107025001a00505038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 280475683 1250 280474433 280474477
    0x609130b0303031302180408030c03060d150b01110c0d030311040b070c0f12020f130905070e06091003120807030e03070506060f06070201171503060408042405 70
    0x52a032000303110100c007509483d602c3ca01828031540580020b08202c0c45440360102088018129649003482694000f902070310f5511240740c102069040100320580c090b0100d00f01000080245000c001c41c00340846001c540245da040014000122502c05e01c043c941c00050101240d0341c65a040c146072640500300012602880035001c03c19200325004042c8041c000a5408100300d68102c05000b204c103480c50314200035440d00042c42c40d4201d18038002c1e51041c4801141034203450702042c0e05442d0460100d0001d00952607503100d504044485c2d0002d0341c008040000c0010f1400e1032012168080c2d44900122040c508540d1035440d094071030207510003000042c000103a01d06001c0d9020300d6070b20392040704803600ca100624000360340b9031084403905d00502c0749038120b4946041800c00c0c3c07401294142c6510010240300030702c035409030364014800d03140d134020702c0c42600054609000480c0203901580c2003a0b0b81c1c905141d501f01c00c01c0da090804003407a00800104610041c5d21009440c5c00c1c82800e0f0801c100620 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 280476933 1250 280475683 280475719
    0x150d0207050a0206130609090203060105070b06030c22050106050a05030a050705120c130602030915071704060210110a0818071a0d0e0304050a0303050f121602011a0609 74
    0x2d00c03028000c0d00260009070112000c81d0a60881c011520555602a0302d5500c0d0400d0800307a0100340e0305c1a0101d00107005460004141590135a03110801600b210010b402e072070005110150000480e004460780c4190183c50060b6034000c0e00d026040d282400d5180200300000100544030092403024459900c2c2c000c15a501d119000700d0b8082100d4602d241458140982c0c1074185030b0100780001c08428051703c0020705d0a001005403100514000d0407411048010912164140d000c51400c5410148100350b100c20544841c0150002d44500d40c0100420000e01750703510100c0368401c002c101c01780024801d200b4016800400c0580c005914100c2e10028403080040350314011881e00940005900045c2002c0002c6041002d420740c452a10f0061090700ca91150341c9860740b0640c0900c81d00301d01c1080c01032020901540c01048070580c0c01c0055850540c45001d00c0302039000680700b501c4030002108054001075824080c4410286c01e403030101e0f4180001b9000036031305d480754010081c01040c84080d642e03a0700d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 280478183 1250 280476933 280476943
    0xa1d010c170909101707030b0115200102030f130f0f02010215151503090c1504090e0106030c050319020f040e0115060215010e0112020402070503070b0103050c150d020705 75
    0x16005031801a840c00c04004c04100c0e804103002d01400d03180522a00c0f20040c0c00000d40d0400c494006519913001e9007012003290248034051500300600000560440c45001105004900101103400040e02c0342015602520b50f00d030040c000c040100214142c041c04913084c2c80045030105d03800022414205010f04c01030342000b1120140d405c02450940c01c00c084500c10807000700312264100c07030090050301d0300d0448020700d000c00d44540c0c420340d21a80720300702d81d030426003140b502d4001c504011a040c5030b075840400050724000c1034156a280d4507a0000c204201d0220340c03107030103020210090071401d01420403c20a2001c14000644074940040304114291200d9003d5000382d036000000307025030000d0f510a030090903d64442d181c0180305001040d0108405205018140d900300044290180d20704511751325071012140d001e0780d00c65800c1081d800013940402c0209059449109070b4480e642c95420160b0a2041581d0940c0c0900c1400d41c4244d601c4001a00b00c4100b002030b8000142c6840003424054502 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 280479433 1250 280478183 280478197
    0x60c1602040f14070807050c0601031101051b07050a091a090403110f03190e09010308090103110301061d04021804020c070b07031205090c0d02010305091203010b0a1d010c17 76
    0x1492501c401c41590f40703291400b080c0300340c1480e15420140e0300c400c1d00498141c03213202614415900124018400030303c0300e03103c09001070700503d810b90401d1500d02a5070801d007440c482031003a80d40441c800b0001824a110391300b00034100c0f43c1c000c0000c4940c3d030080c40044801e03030b500c041c4075402881c009810140200d88800715500d4940031144410458084250341c1c2d0701102e5910030f0002c0f600b08a01e00644038030003802d0f07000f00150900c0440e1340303595540c0b401034201075000c5040c580c40f100800002c0303a811000d07500034603071350b924000c00c040e40b030145400a403240c0402e2409103004000100c0c000b091046e181c00071003030580b0010703500c2600411582c100030064021401c4400300080300000c1c5540604407018100e03100504015a03180c07007000700e40d120041000107400112456100c005580260300641d8000d12440c20789074410320500320194181d000b40c10001240f0303404a01400960303030140002850030020862000085c100c00c001906d081c0180750010070302c180344d00ca08000121000150f83d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 280480683 1250 280479433 280479461
    0x20a020709021b070f03082505060f0105100f14090d02030d0206190501031a130204050103030908010c0905060d021b070f03210c061a03070e0403080603060c160204 72
    0x2a083c0000d089a1090b8500310740040600c50b003503000ca25981e442d180b900489074030511191a050000c5d04003080b0000741e054940d030034043c900140020802c1072240300c0c42582c0700412405251f0424041000c9514010000010803075421903856045401c290600700d606d42c1c943d9441e403103400d40c00028240b000391340d00003234140c080c0b5034007290202d03000540a402100c900461081c8003100940c2c840c1110002d100140c42c0807980c603607008030248950145900300d110020480a240c100360080f4080d00c4080c0c2c0100c0c0011049001040b0444082c030441622104600e00038250510b00000504140540c08403103d805900040710303645419400703c1ca120700b85030203043d07501c419901e044005890609100560b00080351480301c1d016900600c0c00035010921a480d021146281a00d4460040800140c1c440040c51002880000d55a04020400c010300d4100010403492a16140c0100700c031002800b640e00030340c01001440000403200090340e50350040700e01a038240c010320303000050141c80d055103460a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 280481933 1250 280480683 280480687
    0x31704170706030b0319030309080904050906010602010e07230d0c09060503010b06040b0a081801060e0610090303020607030e070506070501020a110c0f09090f160f080606090a020a02070902 83
    0x20203040d02040e980c0854542d0749042000d003200c1401d050301c03000003000c0c40e0fa600c1111259a00080d000b544501449401601420700386850100030a04503070080d40c51100582c807220040214550901640c041c0020b03800c040c0104074a42009402001554100d05290007002006c00803c0d48604020111070394118001e40f40b40351b40c42240c0c10051400d4000d80d8029420038152856604104040300c0c00c5a05a19840f0710740b2481d42c404548102300036202c0403581004085c41c12a40209015403000380c02e004d010303a0054240a82000383c0150b003021042e0a0044c038050402c0829000304856500400900b408501d220104038024288009071f0041c691100740810042c040c001c05501509641e2400d496200519044c014030681d0340e06043e501075840045400c0944107414070300321080c0c001444001b06c1d4007504400c3c80440c2030240805c0c1c40411903420b50000c0244051840684009100000c090551402c0c12000b08103071032001000641c803160002451200503108120380c00003000c00a400719 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 280483183 1250 280481933 280481969
    0xf07030c02180f1005010201020a0503070507020112060b220311100509190602100614040e19030513060f0c06181b0609051215071b06020306120610031704 68
    0x1410000b560180070b414004c40700030496500500c03c85407021b003d41c036003905642d1580c10841d06944079500403410005115205902c020860103003030003a104400f4655150750b01a0540e61f00f01081e0145601900f40005003000802d1200c1c00854203040b0035100c02680c602c0000b0103a0b414031030951600d4010b000c1407403640d00008414052015510305c0d03402d0380c0f0031f524000c00708004e407500c1d8042c603814100703104220111031605c3d03400100e224141d00141e81d201d081d07424029840d1070034183c051700465800209028404040c00842d400381c0140d0603d50100c40c0d03500340050150003d00d0005184542d201540d2030600d448206201c00240e000040712a00da021500c00c3d0085541c6104a2012414072000440da601c1d00c80c01100c51003c40038010300034402000c030750b06c0300c980000c0c00203410310a02d40d190201c0303130902c501002d0701180074560160b66400c00130141311741c40303aa580107040b450b00300400b03001c600c000c002c0c041c1007100d0300008118402441440400603521442e4080d83c90411291021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 280484433 1250 280483183 280483201
    0x10903120206040b0f0403020601050f0d06020c0601050a05060403030e060f090409060f0501090603030c2303030a0e06160c1502040801020a0201050a060e061810030f031205010b0f07030c0218 84
    0x144154132070728000d032041e101c0c2c0c80c1c481c01c190300555000b0056000200144150308104444d6403562200800c55868030900307845590407680440c03240481504820014000c0d402c060300007400411040c0c0f0315a00d00391950310018140101486264404c2d4070000e540404543e00c08103481240070010000c1000d051603190420081407158900d050403070412000140c004818420314040300e4250710781c186407041d0b5503030340160b14400e1101183d440744044d040840e130010400186201d544050b000081d04d8007400c0c10580381040042111074003000b140b43d0b40e0b420940c89100b42103202c0c0c2c00f5445202014203210078401031301641e04030102e0341d1b1000c0384080c002ea0703054101c2e41c0108001a004c100c0c19840c0c010000484104070369082e000f200c442c800503201c0e4212480c1d0f5a1100340e02d0824048030351030781d07a1680c600c1841c0e0343c10b600007840003c6000322411240b040d42d0042030800ca146152405040344054980101d20b8054180301032001d1030b2055458003c0c0301d50030040441d17600c20b4a890a1032607 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 280485683 1250 280484433 280484443
    0x6090203250509060903070801050112060e0d20010b04020d06031b0317030a150608070305060a060207090207051504140f030306030c042d0209011b020904110109031202 74
    0xc103030a03540800c644903041e851900c1032891031062907a11146851000014040036a105004564051040c10b030000345900c0c00780720361806403c0b5488003e411000c40c0c201081a40c024416401c00c0c1d030482c40b074a10115402c1a401a00032188000d0b41d6840944400b507640103085003030805d5000b0707000158100b600300255015006403841030340d040c0452090740f00f48801030706c1c26020081c080105603248070101c0318010043c1d54013041074603012604008403030070f1400d0624694001804519401d0130700801a806005080d0b00c80300a03192441c10920307045000390349201d2403040c1103040707500081140070302c00148100010194071081e80851818103251250402084400c4400b02d40902c1d03000400d42d040202c00c803802014010014514004130404000040078164200d00004842c4180d584042c2441484036880c881281c500680303036440e10300050603045110034003c0d41d02507102594001a40d0b50304d8425040741e04844d0b4034071600000001a50b9882d516003014190b01a240d0340340c0c980e5031340024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 280486933 1250 280485683 280485691
    0x41a0c091206010b0f07170412350f0c030f0703030c0503100509070c06090501091101020f031c06240905041103191d070509090d05030a090609020406090203 69
    0x3109500403146045103512600b0038059901d012504125a060001c40c10700513140060140c2046100000388000303400c00c50b889684599071205090f0034103c144220310001e030160594002c40d1a00411606002c800040d00c407503140b800408000c41c491803001008003e40c0c4403c40c1c00c20890b5038404040b80104515005440c0890000e41030199101c021445201a240240300020140582074104003c016200c10014001e50402003030300c10410101d003081c05613906580c015000029121020b0038600c0515004050090555000744e50308040c031440003085900c2c220004012296941c58218400041c2c0700036030085489464801e1009008000850040b0f00303894107458005259030741d02c0502040c1d4100341c0078405108000d000150440782d040c464040001c185034000030b80f00e41518810f1445600005841500350b00120b0140710a08107405141d41080d810b50084c83c60101200c2e009229120040c88810040d84550600c1c0410186401100d46158010403d01000f030321160100001cdd04112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 280488183 1250 280486933 280486939
    0x100215100e04030f020a060c0507050d02190303021b0f06010e01050d0201140a030f0f0b01020106080604020307061805060f0904050a0b01090b0f0403051509101b08041a0c09 76
    0x800300da008024450110308440800900c01059510b03600c00356140302c030743c040e2541076014051248000841902c0313800703286406a1a642d44444160604501d4142c4100f0130b42d0035588441041c41c2a0b540343d140c0c0400440c1e0514000d0794440100c00141079644508aa0030880d10444901101001c0c0228481c0d043e5203510050f00950703030340ca80030022035200010780a4081841b008001000d40200801080e00150900f0040790009100e00964202c4540041e14409240e41e030a94141c990b90a00540c00200403240c020195401d090300042e031280040d100720070a220b8100425148694002d44810003841d00070030203178032171035a132035030305a00e030b011010f010300c030b0786c078281c0002e801e2522441042c0c014481a500c2c13848603801e001084429501459084400c2d41c0188400400118200301040100811030483c2000d0700304800d00314075008040742400306032070614240d01c280320115501038611010310b00c2c050303066403500d0410b0302a40d00321f0f092000c0107000030380402c1140071801004011048090f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 280489433 1250 280488183 280488223
    0x5060405151f06050d0b0a14030d08271203070302040e161e030209040207050c010e0603010b07120e0d0c1505040e0105040506011b03170c03010303020307201002 71
    0x300220540c034494010580718140c0400b80280a220300c60341c040e212890345010001401441000010000000ea500001c2d8000740e0600351400d900f000e01070500004864245000380f400c0c920030301030041542c86442600d6034a003c1544080c684100001a284421550110303900d04000d2401030195005002d440841c0805a02140c51400440d0340c01010b55490342d40ca40011034007843e802c64040d0f500d0312400405809010b2074150f0b076610320040113100d2090300200712205512001400d034581c010251071007000240700402c0800305e240110381659501c0080c40c07151010800d400d958440c0408002508440000d411000300305d01c021074141500c4913682000c405501d00035046a03d84194000e5800c07054200c00100010704080e04166000341050402c00740005d4076050061b0060b109610035030000e4220b070071030804144c0906600340c0041240d1490303480c43d8155180039541740b040c06c030001c0050f010344101014003018651a140340307000052102860b00f900c4103000356184201f400c9101c45580c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 280490683 1250 280489433 280489441
    0x4020901170c031e06210c060a02150609011206050a0f02040b030601080f130215071b0626010302090a1103180c041802060307050d06060c060b032a0d0506040515 71
    0x107642c1800740314103c020b00440350300043c10a081045900c1b41000410352096040301c3c1000ea80b84000341441e51031580c010059900c45402d0f101c0036034000391040e40505032210041c05019440e80101c642c45400a201190789e031640380d40f120080040702c00d50007007144082008581810010015400742800366240c118640b81e030381008290b41000d550620343d0b0100680c41c4c130010f06180c034031480c0720b814070a540707800c1007c940c5821014031140440003002d0000c6117024003140380c004d6004408032601c41d020301c090030900e41ca91000be040c180030103403107161008e000440303410342500003051541ca0190660340f6414442018111b015002c04030741c0e824001c52100b012141400d100d030302a0300c0740b0304e0f8031314105072100e400380042a84090400c00c104482000503c0e000c41003800f9240c001c1000f507030b5141180300f403400c224007200c070704804d15403003a004002d14040046410004041940180c080134031007040b030400080052034082401401070145030700304000d021300822000603894400c60b85103103941e6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 280491933 1250 280490683 280490731
    0x5070318050105031f0905090d09080304062001180501020301050a1410030c121425020601060e0301090b01082803020d0f2a030914010e04020901170c03 67
    0x4214010745001440600004580001c0c00e016089850104541052900d41b1041d1441c242c41045995482039400020300008003a44813001c0c00080680201840c141030800900820b4201124a210090301070b581070701903600d4082d400754042c0b000c07110041007044080c0c80d05134080e4100b442030610900c0915000a1484e90380b06405482601c0202075204540c078042f0150014900004900204a02204c0e166659045841031400590b10b0b05099981460800b00340c4042840750038a074151200c15209900149030005010360540342203040a0840074190408240104440c8030301601c003158a00000804040204404688915500700e5803c99403000007400f010300c111101c0240140c2c40280c1610182e0701c243c1c0c116440d92441c1c0f82658001c661152901c0701b40844080c601c40164a14125408042e0021807070310081849131001c0340004c1c0d518001038460003100da88030340266000107010107260f21a1150a8006080b03036050b05880c00c01da0718220381d607001218440452010b118032480884 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 280493183 1250 280491933 280491977
    0x102030f0717070b0109200f030f0612010903050310050109120f030909020309060a0c09080d05070611120414012007140102041404050a051e07021c050703 68
    0x180c10040003074542401942c810100e05101a8044072101d000d203d0440058100c40b0014028480450082440c0d0011240c248812118201029800b041080030000c2400400181d07644040030078a5050580e50306070100e44240510f0002503d554a0141914101034124001d507001e07000d042c0251121319140c800640301c2282da4099034101500c02d071030b5440001c204904c441203070362180c505290b00035a9401c200081e60400d4520070f406400c2081000400705d007601c05d0031410111403034600d420385d11f41801c0070b417070740c000401090400c00000789007800e20a66400c00310104450400343c03540c0d026105942502080180d400300d41046504c1844250028140200c0d400019150305000254a41c07002590069015520450300e14810380403070b1121440038800303400180b00300032242c03185c00320500030003048480c01400068094034180a200000c0ca136441c021907917608120418070707980c890b0301d000e928003074038910b84d2a00c07000002688681d09a005000e011394610a031550060102e5502c5140e50203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 280494433 1250 280493183 280493197
    0xd020a061107020a0315020712050315090c1605030c160f061706060a020a050709150f120201050a050d3b060601140d111206010914041d030324010203 66
    0x208114060a00106010760701e862000031b01035000502d41582642d5845084012040c1100032034000b0080200240c00d4071410321400d002184c500e03240303141c000b00509590140031010f80c01036012045000400800704119500d410000003212107070303200580e0242d1102130f5400ba00100d4501190000b40581c0a0382c008540100e03910344407401c5544803801c0c81400c3d00032100c07200840c824a4030300360200300103011a8000d056483c00c00728040300c95040c2100c03045220b5004070790380b04404100300100701140c0c900480c2a942440c0403580d0300110700045446000b80b69540458a2903e074032255a100130364268408a005080c1850000d4200c1a905075000000e588010540d0041000901c06612500e03440c07140007120b40140e4204a440107103c0c8c00c4400b8840c3c44440060005031807180380c0d107640d00c8280d00100918100080070b0500c000200b004480006150107a6201d650140c207030000380c6080c0031000260005c0303a440745803035040d549112003483c6003041c0300420032564462551011084402c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 280495683 1250 280494433 280494439
    0x100b0f030103020409150509010e010e0c011403150a0602070302150a0c021201020c010608031b0109020a170c1c1109010b0a181521020313081305030d020a06110702 72
    0x15a8030b141c091002901c03d00d40c0440b4080c044629007035118026114103802010824000103caa029140031030071111b2a03400c800c03a035442200c42c000c440e0b03400345481517102134641003039443e500c84c80112905401c407803a207107910482d40d55011a03203a60000d00314003160300856001c000255044000c2250348101204c0398002090405001c0150400c901895000100c01c2c3c001807800000071151421581075400410140d00005a411075042203402d440c6d0003562480020029882542d0020344071406030300c03c58942c5c01c04031840079240d130707024000940e00380005000c5800c2c0c10590b0480c0c0a00950a910450392602004034003081c904008203098140c4c1c1c005000c0074507208088409860104016040c0300d0010b10440300460b06109800c12480c41400c0c94907076044840400606140c282108071038034517103501c140100060003050740301c3c4400407a04034002e280d07501150034080382ca909854001d0368241c4585580e440d0a2640043e00220440c0241c100300b201160005543e80c6a20840c400698 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 280496933 1250 280495683 280495687
    0xe1503040303181506180c050a080702010b100c0218161202041a090a0e0c040308091212090a060e130e1c05070606080d1d010e06070506100b0f 63
    0x1000030b00a900040c0385021000034485229032030396840c018070034240c01c0c4880580c1c0394501080001c81d50200071b4504500510103001d1b100c007040307004111380180010f00c410080750705c01013100c8a000b0761010000b80000341080c0081091000c0140110a07440402c138056070154041c000c00700d082110080c09240c926040021104802d841180e410245135100300b403140d4204000982070032454030300c0c00b0300600c0c620070b00c0d1151941c80030045580c00c1c0742d0010100d120814200300c40400300004490542e940400029290420400407660030342c0312012401e00340c401d21181a08459090003c1d040b2810122000f4201e56240c4104a84268821089540000010103003a04030b4203079410070000d034040281181d01090080c003000c0d80c1d190280500101190000503d8000d0116070f000d2180a001c0d440010000c9210480d402040c003008480d030001360b0881c1100c0304038283c0c8250703031000604000170b1040c3e48440c0d0b01e04040b5160b05080e11114400e01c22102d00288088152003601c0b9800400c0011034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 280498183 1250 280496933 280496941
    0x31103040f0f150e0918240705040e0c0d0204150201060f080a0503030a0236010e01110a0f241e0501051e03010207120807020607050301050a031104021603020a030e1503 74
    0x1728081014004022403410350341044120901003141207c00507503d1100340850074800b00c051002080034003100108041080f080c03140e800c0c40c1c008030340c0040058000a41e13500c02da1072110000d000c1c2e0b1700b00c0161480210500721035a641504800c0541d8820300300500843e41e140085945ea904898008103a5001400065941070585d80600b04030028664001540030995a0304d501207032082840d810320440a104078101c13035a1120601c80d2050003801c02242400c11000c0301c3c5c2d074130500d0880081400a115074800c0c104050300c0c0640a0200d040c200110040c040d400604000e000e400031000c4a050030100c00d400180300500405040b583d0180c0080d1460b00c81d003400d5003c00305480c103000c2e0159001c020020008294455455011070541ea820703800b8185800c000742882409403502c400c00c5070900041c050391751407a0b2040d0461354456103000c4002034407000b0401074002e02820051118100100b03c09064001c10043d25841c403a6803101c1c250700c0c0300701c10064480d10310844818a444140001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 280499433 1250 280498183 280498189
    0xf160f0c020a0f120b09010204140607020a24080903180105070503120705120603120d020d1806020406020f01050c0706020c0a0b04060608010b010c020f0409031103040f0f150e 77
    0x9503260018142c1082543c440900601c500d07081d074000510100c6580012003409007407102a41c000c3c0c08003000f5450585400d4080e0803c820f00090144105400101c0c1021940c80544403001000c07040c2565200c403420300104461440c0c24004a00440c40d00800034645a001200b112541c3c0141104055640c6025004640300e8000103411502c0b0300c410040f0601e0100c0c260725481c800c854540c3c40a03594195104403003881a4003401c45800b0f9803118581100b560901c82c00e40300b070104c4203140141c50b00110780305000030b022600b081c0341c403070a80e000484043c080250010011b45010384c084802c00403548000c02d0132600f0484042d007150400b4094200044d1994004003044003500c01298100c1c01c464440a8008034140e4003126070550b2540c04020046080c014510f02c20006d00300038403081c3c802d4000c12840041e959410b44155911002201098014203501c00031803580402c42c3d03140d540360300005002021900400c1c040386003440340000c600b0800200c441983d40a0354a40c44a40d484c0424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 280500683 1250 280499433 280499447
    0x708100c02011b0c15020c01050a0f1404140102070c0311010207050a060813081c1a030c010c0b04020303072f06040b1b031b062721210f160f 62
    0x100700c41c13500101c0c203034950007105c60026140c60f524020001172281414180b010444041403070364000c8504213550f20185c07049071496540e02c1500240703550340402407070026030700a00c5550307401014120300c0c81003c4284401c050907500011020b03000c407560b030f5846a040048840f81840b9050015940200046c0100c0e80d0360050a49a44110600f5003481143c2c120810f1903c4041c1c0b090024640d130b2040301944440c1d400140318001e0781070f070103401c41c00341c4000028803245450700c0140c00442c82402180445d24104200c0741950742224800c44098203004000902d2500d41301c0700160b4a03000c3c0111100c0e440e01504031001c40b04c450395030794903000304820890f1082890720051101804140481c2c00703c40f0502d00e0300d0701c44408241c003070403144c9414440c9030124510342e03a0300481c0d1040c00d03108881c030a900060940201d020040d01d68090405455035804510403000c1028000359203210307185c0046400f49406000d200d1038101028540d482061320000c450011038050001141c1051007180fa6004603a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 280501933 1250 280500683 280500707
    0x31e040818010203190203121b070311070306110706060806070c110415060302040f15050405120703021801030b060906030d030c02030c03070c15020a0302060402100e030708100c02011b 81
    0x50700c0c101038139a050720000340317111211200503800015200c200307003004100c6654000c18503801215840007020140e1300c0c40c014500002d0034001c91844440480030b04014440086900c0b45050080c00020305001c40310790401c00040b100304d03042ca880071942501c0880e0007440b4070300c035654204068580761103400030900701002d0f0b581c0041d0740d51241c00810001c4140e000240c040340e01c000d0b03605c514054685c01c0340001a88802c1200030001d43c400211030b840700c11074040fa1402c4a084043c40080100c15003050740650009501013040d10701c0c0c00c0c002c042000864101c80c01041c0c401c8d216a00c903010b00817018401c403102c56040c0c104070000c20000c6c1c000d90094800703140030f00c112400c010064a28510319889007006440029207140200300c40f44420ba02c40102d84107034406045110b2140d50f01941d00c0c400070340f009106442c016039070402103229144c0d100d4502c00c001d0484940650300c0701c600e501c5140c10700d0506505030604980744100c1e80140960340c1e4000c8010204040040c002108030f5164401031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 280503183 1250 280501933 280501937
    0x21501051005210405031b07050f060a020f0708011b0302120a020a1106040c080d020f070608061f0306050f0604050f040c0c0f0516091a01080a0e0f0102031e04081801 73
    0x744010420081e00d0002c3c5105600c40c03001140d40301e0003000b188401c6018000900030036440440103210540740c0100310750348400c1c150b030980e0719802c50700e030709a05240200603103c5d298031a4400000c0c04103015000440c070746815048010747d100030543c0c01c0f0305911902085060680840011038440d1b4820790061120504070b203058204c0c0d20440b07861904150b810341d02034544d0452000184440d080a11540b8407610701400185802ca142c00009500c5881500c075110a0100b8400003135070584079401910800c0044105c0034101650910000d001000703940031fa103006144521000c0c2e21400c010084406540c802070000380078003104070801000c2c1008034400401c00442140600000d841c45456410540c0b051000c2c10400d00c641060410707800c42d65100004890600030303a0501d1000e9501084102c0b4420b10700760b1169901c1400f072801418000c01c01d0700c0248140e803185805031a040d405180184180c3c880c02041c100da546103d50242c000355406068000c040005c10b0f010b19200c090141c0f590818 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 280504433 1250 280503183 280503217
    0xa020d110709020406050403060f0905150405071203050a0909020915031f030c030314030f01060f09080303150301180201090b0a090801050106050d050708071b021302041203021501051005 82
    0x101100302c260703041035005002040c0041000e10810029008a4412400c11141044400417030b48071a031f510000c510280c035108402d4404038003400700900c80107001c0c2c10600d00345800f0140d03e1400801941c4401c44400c00607003001c40102d40a801030023151481e040041c29081030100c40b0040c0080c980c0003400d0101003500d01d05225510892042c0c415008500401c7c0040c8005d245050240810b02c03005000c400c1c0390300800c2000007640c820403256054901c9840c0c00215500c0f07080c015143c038107481e04a001c85100110810050b15a007890000301502c003503009012005d685070000d0051081000b000340403600020007030198100002c0501401046450201c0c135541e59140f0303550071903030203030005400288002010340010409005271a0800c1d4640340520040c900410000c0598552040014100d20400e40741000e5589691940c0c521001c0c0a100315503c90790b4402c500d00c2c100d00c8500c100c0150040c00c04000c102c5507410002812908003030306030070301c0031900c00088491b035101020040c0d15601c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 280505683 1250 280504433 280504439
    0x10209040e010b03060705040605030118020904050a0b0312070c0308031906030f1a13110f032a0d030206190e0114040c090b0f040506030114090604060f020a020d1107 73
    0x580d0140a500d01e855400000725602450305145c2003040c01030986081c40020041040b000d903000302140d044581003030080846540c60000f1002034441c40c042036a11a040c582405034003a420f0740051040002141203400c58038055a07010b0841c040c816000d440211342d12000c20220301408015640407900140c11004604075160311001c071031803a0015200c03450514440400c00503040041c9110203214031907980b541c0b902c1c03103802c0c12103840e40f10f008041180d1410350060030b844d80500d917210344030000c060b100000e03030045071500610040e80155182e481c009101f02000d043c0a9801803880c0d03050f07406007a140d650140c015480c03d080c0b04440c0c4c0b2040e0f98440203141c204081c490206400c42d0301c1c52211050030a17007040c41d65001c0c0b681180909914003e0403045669038903800d10a6148255030100e0306540b0040060300500c1c846075500c228140c1c543c20400200e5000c120b141c0314910603a0304002d0314004080307400c12402444003035000340e4004130a211a06003e90703092003402d1909011a481380361 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 280506933 1250 280505683 280505689
    0x4050a0b0a06080411060405100e2101020304021c081602030304090207030e0a05030708280203011b0f1b031b0c1401200a0206132c0a050405100e010209 67
    0x81c042d4841800a0041000d10040040c4a219105141c108071ba409051a007440001981801440880c200780110080005104c1e02c52004514500c071455100e441550001c0b00303500e010754001c07942240704401d03040190b44240203640703400c8403054121541505200784e0500c0803000001d48078081c2c1c0d140c0b105000028413503000380000d0020503c00d0b40c49255000c5101e00b802060210340e08036520036000140107200c07400000991040c01005001c191701012a0110708035075001418001a400d54240300d00d68240c004102d60421074144543d03100c4c00401440c840454101c0303200c0102589000d1010030001c0800d1161018651100380142c0ea50011071895440304442010740d030103010001c96000034503003250b0704100403074403403503007842c0401617000080d007001d84170500f03004001c2c8242004508ae03c01c90959041038406003000f91340100f00c0c0f1098485801c0c03c601204a526942c501e1040000c0d10120b89018140c040c56201005200d40c400d003000100207052103110707800c4159808c1c48000a130f0b1b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 280508183 1250 280506933 280506949
    0xb0c03070302040801150905090a050619090203030f04030c1a0412031b0b011a0304110d1506030c0e060301020a020d0e06070b010e010602010e03030702030403060218030102130e131104050a0b 84
    0x650f203144003d00380c0717045041c4094070380080c140000342e00f0ae141d030440410302c0410003a40c400a0344807030b1010b0301c03c20b0219400409002001941510011400303d50021a820052080c0c9000f005103070300841d0b4030280b01d40c10600d0f401801c50b013842d052008001500340030b00c4070041e803071181c203111079043c50b040500d581240018800fa106440700c4801089034503010000642504010f018007031541c505919003000047ca8814214082c03880707a080e41090040307482a0b41c2095183d444180043c0760759042241d20036100303003e903040c009094000b0407428a014800c860030424107030054010031101c140196150300c1200707010b68000d14100000d00c000b03031900800b98003800700301e5031881103075040c484c00030700315449030154403030546c010028070100320703000020380c1c04481d800000581d84921200c0f0003054400d00d1400c4035055800030404110303249d2043d560750140c5058000501e0a50783d100c907000c407200d61180c0003509000840381e2003040e078101500415407140c2c4603d8041400c01407900414145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 280509433 1250 280508183 280508201
    0x50901120203150a05040b010c1407030b010305070801050a0c020c010e150409060806070921020109030b15030c0f0f0405060a03020603162d030504030311040f0905130b0c03070302040801 82
    0x2e6280000008844c580410b00401620003503030200a000c04031400644076120924001d00641d01d1070300761000c10041040480301456001c00c940b05030b942d40c2d141c92940c2d2840e03402080f600d0350900002803a0582d1920903614003042c1640101192840e11303005580b402e40e80101141c00401e203405584845018000902c01428003031000074426280010003420711101405050030020b09100402c41d0451550305110b402c2c2c0d0480e00c241502d00e42c0d20043c0c2d0744e00c1c2c0301d03400200419003400400100c0303c400051811403482c20b90513142e441c1c081004000410220b402001d40c003407100c1223100158103042d408030307034007100280090b4649038070381d00050703030b541c1080301e40c00003a40c2d14655241c0702c03507481404040e848001206039401c08220688500800a44003800810595a5400102407520940111404945014010381e440b5258205100881558081c1c04c074500c2c104400304547c810440c5a0341c4242d5000410040141c4618143c01040c0d40040d002c042010303024403000c00d03c0c10080c4200102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 280510683 1250 280509433 280509451
    0x3051303080f0703121107080d140a0902030d020f061302010c02060d021e090108040b0a1d06090f12090105090a0f06080a050a0e0a110a1205010f1803020a03050901120203 75
    0x10f506151070010f05501c0c500c664114840d00f40014520b01560720f4080e40d1201e584130921544850903a101140281042940707881201c80d4881440350b0044e0503440905100c1c001e4050700c088803016001607075a0ba400c01c542c2a20b40d4048000107101e4407842901015080c41403608010310030213a0001035582c0c20000c1e0100c041580041c016503025501070000908420824040741040250000a01100c00050008d03156110390000036a860003c1c0d44100d180c0c0080500004034050f4074080b441c0e0b540b1040307442020ba4443d10342c0b0504110800035441c10061503032820b0901e032040c800d00464060300310160345600401e050402140d0400e202547c00050602607580c20350030300d046d04002054600180c09514800c3c54500403040e00c22000c40c039101d06641100c01104800c8460b004100c01c01c100d07034000400568204152030400c032064001c4504c17050000700c24041c05126480500c01501d0030a4001c0240e400701b000440002d0145002d0143d4500c1410300701c50b210350141520702a40c0c405c0b924119 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 280511933 1250 280510683 280510687
    0xe01050109062a030908060f0a0e15010b0703090e0106020d200606010e0f1c060f0501080a060c050f0f120a020a05040902030a09120c0501060b0306010c03051303080f 73
    0x259644000e141008107818030b00214882c2ca210401e000c05000000d4055090301c5281490301410301518076a001050001e0464003140391101d003000d40508290740c0c1400113410040c4519016600040a4007228181c1a08250307603440c1500034840c80e44036120803414428903100000704509241143e600800c3d85402900c10102805001482e5189071060f2070002c440c0500d181030619070014066074049401e081c200000f1000c2000030341d15100349a406544800c192902254402c82000300214a6102e0141030140200780718441064a4023401090340b07503400540d081000c5480c43c1c21079501441d450410b00e00d425400351044110350312180c1812110140041d000d0b646a480c20900303070340958021021410005a624014240d00c594428000a990040045a414001640248002c0358071104020381c0010030320014060500501d410b0b01d0552800c20300149940c05001200d115034816076500e2400ca42540d42a25160045944034400b1205618003200140301c41009011041d01d81101e10307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 280513183 1250 280511933 280511939
    0x1f050613020d110a0c0b06011701060e030f010e03180d1205030c040306060b310b09030106080a0b06031b21390409020a05040903211b02030a17070504050405010e01 72
    0x42078144042c207c18104103002200c40041d180d4030f541141510107900e003180034103140a00103031420000c8519100e4035441c00d0401d4003600c400100401c040e000301c4410041d92171038201000303407205c11410301801704402c0c0c1d0064003030203115074001c6034080c5450741c1103824103860303440f00c07011079026400078444104001911b9009038215240c030011042a405030401c01b800e003101103100302500384104a02c0700e0001c240303d5000e603020342101d0f000e42129021144400c005040c17032685030009482c010f00030300178000d1950f106141c1f221802c0303c540003d0560303000444440e0340000c0310150714000002034007601c0e00c0900100600b0302950458440c0484483e0440c840c0c5c00c41c1d40e48488003054403840703030b0b150081e80c3c001626458102c4003214800c41e00090000d07074508040e100741c450214440090460011100013405050740b14104400422040c40642c800b41d94060703aa9100d005070300e401191259581d029500c0180000c3c80c1c0c007440d1481c1c401d0415036240301180031b4540030782151604024103c018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 280514433 1250 280513183 280513193
    0x120115031406010c020909010e0613120c0305090d140307050c030f0f06011205010b030319080f1302040903030617010f0b06030106090e060609121f050613020d110a0c 73
    0x304100101a6009908008001070869225050b001b80101403400004a80f54002c3d404003200d4803c8806507442031901048200e28940c007954107c5400c01c40302da000c6881441490341c1752000758140c50300c42c039200f02c01c010402d40109647c4100c2e200500808084075041092000d000d910b03104100030810004c0f01c1c400c041c1001010f155642d4203030f01a5290b411101000503040341154925181360655903250300f002c50241030b01d258200d4040c80b0000d840d0ba02c1c40d201075441c81010401d552070f4004c035110701000f000381d1142503864400390581c8161100161409506c02000903100c0e00740000c00c10707980c65090100101000520455035950b05043c40a9101401781c400150703002c540c01450340d03040c1a030181401089000b0510500540e4000580e0303620348400301d9401140003010302c0d40d500305980340a685c804030b4851915520680049040c1c40056600646000e40c1d401001101180c0002501a000f90001d0a000d105030343c840440192041009004104e50029a5240c07035180c0346a00303003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 280515683 1250 280514433 280514441
    0x60103060806090c0d06020d06080a0507090b010c1203090b010b0d15030201080423070e01080c010207210203010f0905010902011409090601030c0e0a1512020f030408030c12011503 79
    0x1c880641004040184008010030100b00c0903004951042580e2107905241c002400b0311840381003158a0058007041486001505021051144c4225806640c540c0142d00c251100d0281013804076241d41c8140001401301c800d070020100e81850002451852900c4424202d00280e0049019400020301d801d00c0d0852070040b048800184041501d80c0c5165a0000f0704a241c0288003400c0d40226000010004a620602ca103400e800c02007181c150342e4031400b0031210040203100f0403440d4403400183c00710395400811988102c401100c104010310010900709a0700e0101000200c1e8995a298070702400d1613079078854841c0e80f502540001844004a10014010550342a05041c102009006049041d40d4030b4040703540c0308000b885c0200e40150702030340580712040e1407400b15900901925020030b921181501e0300a880c0e07002e035034410985410441400c220b00c280d129050b2040c90030030000c0c8c04504207134000c640141008440c24500030f0b201c4085914200280c200c1d00c011a1441d0300407681940c5806 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 280516933 1250 280515683 280515689
    0x12031a010513050d0f14100e0c0d060c030609050411181005060f040e04110a060c02030601030b100305030406080708072606040f091a070203070c141906030506010306 73
    0x3041407a00c038440c0c0c5140ca04010720302c20244a003d05244c0001000750540010a0440c2d122100095961248000544804140500c0108549082442c1c04c4103100003840080d07280d0050700da00a0300c041070701c51034040c0c03960311034100506443c1c200c000303500c0460788a020302c43da004203d8820b52075207500030844042030b003800c0348518004041c14080e6102d4820b0710702084800454103c2d0350b4054607030139013050b4001c61340441d030000c06c05010007041c4255955225005807040b1000500d00b0f0329a4003d8840f0a01180040e40680c0a0b06c014000107903154141a0892211010514110350f02d544851940d4025000000010312600522603040d400c1446203401801505020b40c45070280750501d107036150310503c881c0b03c070381480d0007080c659116079000449920b10b1f29018803408002d41000c1da1504400c80d903101d85090540006081c9a2004c0190344841d80e00030f01e820031031071502080c032012083c3c54042e964483e00d08040f411446d844480c02c00c0c01490592408031340352600314000b50445c2c8080c0c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 280518183 1250 280516933 280516937
    0x5010801050105091305120406030509070503061504020309010b03122508070b04150216171312150203070305060909070b04151b0b040212031e07030c12031a01 70
    0x40040c4620742c1c4210940d44c1c40041d0704100032a0b003174207041a40c6444035241c5015075120001a01080c0039605800c403d1003840a20304840751980e4400c1416910241203e204c1480226041e000ca490300c2c1030b800075500100080c00200d900304c034640009041c58911204800710a40003e442e0070484401c0c0a40e00d201c40780c4a5203000104219100c43c1040d03c074151000382076030075400005040204191089801c0c0c00d0210045403110700c42d2807400c40c2d00303140c13140590b07444c1d81d8050310034440d401d0380086a500f4907078003240d072848600d0b203000f0400d28400d03a9022210300c0c0c03044424414400d140e10282d0301c20555650b001c140340c141b20302400920107010701403007520303000101d0a001c1c1201640440381111040020308600c449100e03401c8038200d051201054001314040107100c05e00c9101032449004500031280d22450664811881d681c1e031080c1d886003038035400300e150107040c14011180607011560183c1803c1038401d489a981d6161140d4004006000c29645c11410680700007881426490b0b401c00c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 280519433 1250 280518183 280518191
    0x5060d0b130902010207050409210207090609111905070605040b0402040e151b0403020a090c091d04030f110f010e0601050d080d0902040b13061802121b191205010801 73
    0x5a00004d45031140c0b0301400f4010b41e22101d01608100c541100c1c4840611441010ac0c024496907000035160003461258074800b90030180c01240b0300380148901600e064500110628002070202c1c0c00050305030fa102c4034000d0050510580021540300d009040c840e520a2104240e10703d894410441100c44520204400e58010fa240ea08082d4000c501550010f000000d0210780b132451002040f641d12417604001c1d009041600c0001e65178403160420b180d80d07802a04c810003100d4071203400c801480c028664804a45103143d02003030100e07000f1302c00314030080308614140500703c0701400c40500d0845c00800740009a9544c3d0411040c000d8148101030150904407408204603220b5124604107008202071210f90030340c2d8007950811942c490380060f1101c18068200311038042c1c078030210f00003010a0720075400000d9091050b4221504244200c8103050703119120340c607154865400d80d1400010600308001d910b4010800303028500b410320455124072a103a039480d0102d140791500b00050310010303402400c03541c1c14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 280520683 1250 280519433 280519451
    0x7081b0312030f06011107170307120f0207030b060310020415030c020102090307170f0f0304170c01080103061805070f03231c090306060603240303020303060d0c05060d0b13 76
    0x40f40160940040342440c10041041d44201464101005540015083c1001913480c11040301c001c0083d2200ca401032084c1d16800f10072010659200688407901001078109403411300010702007544c916044200a0201c030412103110704244200e0b4001d4101003012086580b4092459901d4002d42c513200344c4d14070080d030034000c450010a660340c0701c17400751a0030030140300c140040c602d800b080008110398484003122907010700e810300203403298003c1c05000081c460b07041a0800b6920001100c8000701d1040e51400300513840c5444101c014000c103481d1080c01481408942c0c04100204400340c0030f00704544200c0c0e41c26285140254008801d0a040351121004030341c50300031071001180c5d810040c01c01c1c1c00110405e4140702005c44c2c1d203540300e070170003000c003442d0003404200d10b0750640c803601d030091017041c5032500c074261607002c3c80052005e444001c006910030400540306060540c0d0403031405120310f01130a0903030380740e070300140098000246081e11550b559151041510700307030a2155500401d60001c01500b41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 280521933 1250 280520683 280520701
    0x11109060901030906110a0906080f0a0f15030506101a1206030a050109061b02063306030a0506011b1110050706140a050903040f090e07081b031203 65
    0x5610615445004081510752260340250010001c00e64418000c00800380310a0700401e254000f0442000040e50301e07040400c444c0e00601440f4050307101e010350750001e0794807003680780c0c00b07400c884000716411a200c203800802d000e0581c1404000c0c40c41100501202d02d4442540c01c41102c0d00e81c4610744030440d041303110504036865001c440308203211151070001070355040701103490700403800e4004009601e0b14080c4030600c181c0303521900060030341e1100d00007584400c000490b40c0d004103440d02c403d01001541090b812044002c5005c0c001d00d05444030300d1054182400060060700100c1c3c1a541007074032282007143d5507070710513010140c613100e00c034841c600700e42984c0307800a04000c604450f50184402c640c1d15081c1d140a0011f172540d90b40c0c0014107101140d48403801492040054501e03000c41d500b0080811400d09001c01614141d8035a01c40015003245800c0e60035010380040c061620a500031180c0c081189102070154880c1e122030101c0020707001d00c083c000c1c149083c11804140e81c0d41d0000b8428000408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 280523183 1250 280521933 280521937
    0x90114030703062402010506010518041a10020c031009082d040b07030807020705030c01050918160905040504110111010b0a1203030501051905190806040807050c030111 74
    0x51a5005426201d07526040250010120b0750000e120091042c0c50200c4030f2880303050a1203c4945681c000c1c041512200f0055486000d203280b00002c01840c080c00c1c0509081076484181440503c1d51360f6040e00b8007a00202d00015542044000107030816003540c4590300382001000300101e4150000c22403032400d5280c0785007600a850f0700400c1100b0041040d45c000080c400d04408400b00085455600d03075490781440399941c07003100210017080300c020000d140b003030001c02d03543c0072144040c02612010010000444055005611407075100c00100700d03162075107880d00441440340c011005204280c4600400283c442c10280d44280c2c46141040c04203c001451000641c0c1c80c44000e0a21104002e50741c04198058140c5428581d04480c0d600e0b0300142000f00c03010804001d501a0300e0410080c0d88130380505c0304c0541c0b00460300d008800c0f124400c01c000c0c1003065030400c03260380e010285140952141700540c103002069605851482e0b000c2400c600b40304003441000140c1c0d0f4114000c010445c12246002c440f8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 280524433 1250 280523183 280523207
    0x1a0901060f0c05030a1e0c200102100905070614130603020f0d0f020a030b040207020303030705031e01080d1d03060a020c0f03070602030a0606080c162109090f020901 73
    0x200501c491250600641441000039440741c10780fa00c40703190b0301000303180014030b100000300302e40c0980c00b44603854040e5021002c01c1e40c02035132000001c503159025148000c48049518118807800902d01070305003152055120031445400a09510752070040020900003411400d5488850208184014000040c088100315800380c1009a01c0d4040d900d8000f610f4000c03150300d08005420700002c251048070070380c000c01000c1ca194808028034508203090004a0146820080d050381c0704101043c0c666008101440e403760010a014a8904126080618102023a0f0200880d82d005c00554100b6130740010000c1e842d0203990310340308901000b400000e40c0c2e455000e046003210980c0010504689201402003440ca088220304490b0740315501d1030260f000f035200b01e80702d41c0740d01d18100001c24824811423140f40200e103240e900c0c074201018140306510310100f5150031540f00f56224030019040008003d4050800c0c0140c9a4041d103500d0b005039982590a20322105e0140c910400544403076a81220503903820b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 280525683 1250 280524433 280524437
    0x30614130204090f020405070e010201111204020d06090c0803090f2e2c040c080c0304060b0a09060e04061a0a1701200406030608061005040513150905011a090106 71
    0xf040080c1040d0f12036260500300039402c1402c4c401003080b295085102d0305803d000a81c000c00a2080008900002e401b07040b240711580c60180000c50054a04048610305280c0121ba000925125a9903134008500995000c09801e030808102140c00d8501809500c5109000360380b043c1c1c040c0000b049408803103285140b00c0d4504640e10300ca54400034410081900074480409000c0c21400480e04001544075240f046103110340c0c00c00800210ba039119000c0a030164031225049421522030341e980d0b13005442280940342d081001048000740007521030040d40d0042c40e00e0821203100d41440e007804c10a90f036040300d1048908410001000347c83e1181d040d00c4003140c0d500c00c0da100700e50742c40e5071240380546217428a00e01200ca511000490035420500180115103840e10208125aa9800100d03250325044848420881d10031008004508180c1c10031035011140e00081881d1070915035800c0f1031034203c1d4030100f1a4585d40d038100001c02c07400744034001c010b580b00e540c1458046c588000146101905004d2002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 280526933 1250 280525683 280525691
    0x7120b070c080d0f290a091506050a0c02030319080f0601050d0908091002070512070f050103090501090606030c05100203070203030a050a02070f090f05060627060702040f0501030614130204 83
    0x41411469204002e01d01580300c15481001136446941720103e00031300b2035403041100400020f040440c1c1c0c80b9451038540b0301a0028a403a1030078030140c40c150041da0300d1b0001e00c11000882030043e94140014444c1d1400001901c2503010601c100904d958001445200044082818445260703004010360f10f07020b15440740860b00c00010314010350369000e80300000d134000110180d103a044a401061450944106a89140620448030920f59541c4031034031400200418408083c08194400d4102c089214021030000c64140a640c2e1102c08803101c551003940e684064103004d2216103800c2c0030841a910309840103600308146600044e85a1003031480807000c0c4a000a0710f000054001e2001e0300040c06c64800b1b0f01c0380751740c0d20712805010b0480944090416480c0a0002d01c0340c1c544001a40c4189071042e255030388101804600340003075100d1122460780418188405801a07945004241d07202e0b036841d401085a524626225050b01d4400d80710b4200c00294004000081881d0102e103401e0580403a03000c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 280528183 1250 280526933 280526951
    0x3050a0f1701091d010603150e030313080717161104060323070e07020604020108280f0f0207080414030102070308040b100308072a080307031202040807120b070c080d 73
    0x4d0210700720344202407000d5090071b000109010429080350b10b4070200c15024003140705070203180744c4c5a12048451ba20102d650a030440046800c3e0805007102a2007140180a401c680701c1c10064a078010100120000c5501d00e0310004020705d4005582eaa5170b0252014408c072411681d0303060001c2d000400441d4814800340240c098800e041010a00808900d9004179150401d000003d464290854040c0e01040808012441e030441013003110400c0040c125a0340e03140c5808a1000c80542184800c950901352190218070b81000c8500c002c01a80e8420940c4603550b6140c4811800c10b000d485071154400d9105010510209401c41662a8404da1220350b1410941d2110708451112510b60005030501102003000820002c0708003800640d800c0c41d40726140c3c1c9031850000364005840d140549100350700301340806000a4000c03010200c142240c5200541015291280185031083c140d02070595041620781110510840070b08440d00701805103809604a03420b501c501200340304030350001ca90160340300004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 280529433 1250 280528183 280528211
    0x90c19060e12070b0423090c04050f04060e07170901050114060d020d050c18150f09010309081207110609122b061d090703020906060c0102030403050a0f170109 70
    0x604090b02d00c2c00038268481da100c901e807001c0301c03c00000030007990186c4402c0d20168a00b042e50244240006842189401d044c4001c0c030408162110403a500152210781c04514011540181d500c5041180d0ba60803118455001110a01e50007030510780c0264136010050140044a00c09441c032160181e80b032595030300c00d2030b034079400901c22148060280b903d4803060000d240c0002c0000d0404010801580e8803080940c0c08100002c0000c0c40108142c2c402042500b910b0910700c4050320300751505040000e012003182d25140d60b60340c84210001d990b0041a0200100240c00000500740c500a10008020924000007032544d5a0011146203079020000704507450320344a2100001881d621440c1490450ba03502d10b0301c00041c2c043c6001d4490340c45c90036030b0310319015202d9210482c42507500f00c00600d14541f0396020300441300000360103281c114404000307400090009000840c01203119580d19603030340a04110062501c1040344000e4200618401e101c0c4e61500000086815144620000260580d589445c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 280530683 1250 280529433 280529443
    0x303060316260f010c05040f0512070e090c03030c1501080601060801060c1509051e03070b0619050303070c03020f060304050d030e0106080f030904050106031b050a0201020f03090c19060e12 83
    0x1000b0031960a00c0c5a005c08584c0c0a80030340111040c80c00151600307600c41d020003d60050011100e0520790041c0c2041211400311031010390460092001d840244980fa03002c2401d540c080d52130b00300be40d030007034550110104107520000d0041556401400b560350500c1c3c0018051302c010f00c564030030002031a80c02d105100c0ca840985d840521001403c00c00e000017442c019031a0140001007000e103160b051400841203d001c0300300c076007907035100d1484545955500204030401d0f0402c1e15a005402507400c0220311501c00300001c1ca1158000d201c1f84a12510350300c1004100d100403900c082c0150800e00500c8000781000079545581c81d403078100892002010040d241c018105540108158451001c0c15040080080020400500b0a0380c00b84a142c1e2121803d0b0152101d00c003091030411104400c1c05281c03485203000c2c20265109100261038034024245000003500252030f103403d2a00306840c83c85c464900050440c060852400300a05101d140c82e201030002007180da281d5000b914181c124160600082c00323 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 280531933 1250 280530683 280530703
    0x80a020a060c110d2a260a0b0f0a0e0c0907050d0b0604060518060304030215040804050d06060608090d090614090d050d02060a0e0304090c03020c010509030306031626 73
    0x1000c0001c03030749070600d203008211500c11010728405a484c2002002d00c00d40428043e10300d5120321b542d4180c03407022249540749542c1d8841c0349500503401c00701b000840700e4030618012000c01d0030800c250b081482052045a0712a500b031040783e400a00c00900329240c0070441940040307242030180d00c2d00d401001c0d400143c56540c400a900420009001c52070035001005044401660406912900401014440e0030301c010340d806005644900c040d0701510b892014a2544a842007a07054107143da9140452200c0e20100307070440c1d00d65182c12046c807c0c03540c8502c009900c14210002403803020718445001c2c1200c440790154800700b118111001020352500c400703c13250340718042e0104014903801c0c2069621010f4100451005000704000b08081c001180550040d6441c0340000d1480e00e4900406900180740c2004c117034083c150280901d8801d01800c2c03080354803803080e58003c0c56481c50300904141c1860191442041c044d001420244247d00280d403144d4001da40c4091000041610304401e94540a146a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 280533183 1250 280531933 280531939
    0xc010c1707020a180b04050c030103060c052511030604200102030c0a05030d0e1c08070318051b1516170a09140d241b0e0a080a020a060c11 61
    0x10f04000355000d2003440107004a800d0300c0c010042c500e00380c03081100741ca806555045489030148010b1010840307950190045502905256240c22a0008402c1c0301040300341809900041c6420f0350801c0c0b0824000345110500c4c12030113030140e8645a80c580702c6000400c4d003009c18042800800404903402007044178062129442221100b0794246400ea589900461920106900f007181c0780136500c10000c0c0358204041040110402d4421010040b0760002005142c0c1d001c040e12290315000241020079203052940c001c178058000038140e150600480c1840708038560048000702f92000442d03c846003a5a07850105e1005442c040311345081400c1070880c024044000800006175041c15030350003d0f21041201c0314070b0280f918070742c440020880300c4284000058075515010711343c03440e440c40c05101c0e0801308140c6140058510080303c50398071454030070b000000c040f9464026030720161a1840e403400051414a00030b14003126158045560f0b6440c0c1d12070780080c004807589100410907210194072a104000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 280534433 1250 280533183 280533199
    0x415110f100624120f0b0a06020303100b0a020a02060d020403080f13080a02090403080709030c080c040b0a0605091905100504090e06070906051c0203010807080f0c010c170702 77
    0x21800104058821001c200184000c41c0d001d040300402d03640601a0039850f070303d00a000d400e501310041c0c11700c0e8545420041d03641e000c0381815544d940703c0344040d2841e03600568032803404641003400d00c909504181c00d1540c081c080c0000207035001400c00003595041d038010791103046548500c00a4001c0e500000e00c5c041010652140d600c8050019007000851081055070440e9035000f856202d044890010b504003607803c0000b80801d000702c20301600600303c1d242141d035003581d907260814180481c2c0c019411030b070084c00b03000906203058091829806000c940464040d883d05c3d5015000b8800d460100380990614183c114019122105035001003402070701580b18028041002001340d40702c0e000e106802882d001259441520004007503105040503100d03c8202801e00c54190b03542e81102230b5005d0144c0c0222800d003101005030010f10300030084000188656428546414200309050ba544511030b40400d400e08566a4400d20010405800020ba5946246420006005445504030294000c01c00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 280535683 1250 280534433 280534453
    0xe03030403030c03140403020a1401021507030b0109050f0d0b06150f03010501090b1804020d020d0f06030b130c050603190e0a020405060a0501090302090606070b010308040f06050415110f 82
    0xf0803100c128443c400d964411030505801469560781c00b60740000f0750403400450707060003032000c440d0324204080d8050044401c103024000400703551003400c50b00c140029490b0001c03038102d540c0000760302015000464480340414190300120715002141c0320007602e14000100400e4081d00c0305201603030480c15144d4034035580d0b0289484192641d00038414107001900d000c1000404401075000e0b1107030310102d00400a001036100c2c1c20040a0340020000a83c1340d9420809194040d6640c420140d807140c200d1004225140785003000703142818010401d01e03203007801d10b00301070005000c22040c3c0c1c16500119074141e140c1c1c8802c207404040d0811140400700c41440c040c0701c5c151440c40000c61502d0306208407018882551041300f404030380407151140901042c00e0352020b2006280002d00103900800c0502207a00340f4481ea10303140242301c0c0a2703000381e41c0000000313402e015101c507109916014200b1810b295144c04c0c03134101c8d00e114008082d02d1071420020307900b58014030300c002480394804110801040790700c4184 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 280536933 1250 280535683 280535687
    0x2040506120714030403111501081c09051c170c0a0f03090905180111040807120f060221090703020f0909071e0512010c020a080d060f09140a11030112030e0303040303 73
    0x111113442c80300300c3c40b802c012050070808e8a050b090682e40d0b004080c061164404527640100401d5031b42d05001e0050f58040490151903070100117052440550301c00d02c3c9100241015120046007070300b5110917680030003405045200001700780d9056503001c1d0802a620203a41012201d10032280c1100d00b49608040038021001000a9071803d0001d14200801685a00340701c0c01855204e039125103d0250404402040703450b00e44900608110f019900507810305226640d1a0126400744484410f401d4060400f040c0041d0790b0078001e07030b04c1800f41d0010100142542c000a05240401d0b280902c1209060001415070700c2c144004030003030048d14502503030036002d2682d40012044e2801100e0150814980092800005000d0251002c00680103400e501c0000d03218820701c0e03131141642402075511502c00169001400a0340c50003411841000039160f440c001000c200c0c842c007d0002900c0504003a00460310203845001c99044443c114055083c40200d40f41c141c42410001441e1a81400f01003800030a040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 280538183 1250 280536933 280536947
    0x6050a050702070e010603150b0a0c0b070801290702030d1d01170c0a1e020c0909150c130509010b0306041b050f0f09030d0309110402040506120714030403 68
    0x9000a501030005544545049907128814480c412900c0301d031500400039280070380d010000041180028940d050340340c3c0111030b00c036404036402d4000105582c484505105041d0301207504050b40f480d142c82154581880350291590180c07034142808100c0300e00300c6404900d00201c0e2003150f4007a003995290009208060441820415454496621040c10f01d0181d840f900310040030360b072240074081032070f01c1d8011000525040b443e030003018040300024041d00c0710903404c0080320301e844590040441d0616001401281c1002902c00c00f0725601407884590154103010003a0b5004191058043c1c03211520800c900111b480d5034002d03508240350500208544468400030340c4501016a41440050158100034075001c2c6c540d19101c0c0010028070441456038488002807203001c400b922440c0c20104d104000a00b04a8645010008243e98070180410800900011103030307002c003210114103213803030040407a045e03102e403070783d01039005c44d240340010741c000e006460100071440040e03d8141c4a141501c2e02038041b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 280539433 1250 280538183 280538191
    0x108030a0f032706110903150c040f150306150519090504020c0303010302031c081503100e010c0306090203011a0906040906060c1b0b0406110c130b090901050708010e04060f0203040605 81
    0x16041c0340c0017404814003d01124005480038004080308000f40325900941d0030050101c0404107000c000000d1913084121907400a014104170003184010241400b80c100d4000303a00005002c89280d01019030b0903001000d0390301266400d074620f0644440418206d5007503ca075001642d0092002c079a01390051000001b85068920a504443c845007008080014540070383c1d6804000580440004d044001d80704028000600040d040310940009103824a05550b4078460b105043d030b6480c2c0d80800700300e506024071401041d181408500d1941006004080da14205030251240302001484442c00e4440504907401040411400c1156546070030000f0084040c2d0f041c1610a40102c00e4074900844041420000f142c042d0300c1514501840c1c0130b41652008810708030140300c7d00662800c0c80040c4c40f046c01c00500c8900f104000680241050700300010440060640d0466a262a0401540c1038021021a041d00c220500c841800e9440e894898040e10500015144550021083c0410815141c00141c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280540683 1250 280539433 280539443
    0x40302040f020408070b0d090b130201180602031b1006080a02150306011e020f070602100e0c09011205030f0a0e0f040b100f11060c0c070503060108030a0f0327 70
    0x1c01c044152541c140c1c010750082090030f811244080018521020043c1440d1064140109819581d82c980e0112002c0440380440603100b111690b4085681c800168654074564050141080e401c041c0c0082da00e014082410f041c8880310b00602003090401c00c0700d505010503442007401515202c100340c0b5221400034401b280104a100b074403c10100d01c0743d0030b4a1284c401a51485605143d074001440c84400002900c0103500490900390740c4034000b800620b018240ca80c0007041d42480b4803202c0401c072805196414540d801200c0e5112240e610070859070304480311058092b501012600745641184142c0c2404090103000007000034034190004070301d0720740700310455030b415603006001c090105075013142645540c0050703802e1a0b00320341802408200c1c0f9810840c030b0203160504980f400309191250a070355240000e8000708103440c00e52020009107019110a601904840d49811150b5907a40601d6071030798107000000303500241e2244070f0380c0841080104145180d1400d6105a441034140080f43c0050318 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280541933 1250 280540683 280540691
    0xa0b0907021f050a09061505011e0212390d090e1b0d060608040204060501090f09050a0b0409240513080304020d0206120907080c06190c020307090204030204 69
    0x4006800070031081c0641890a0b40c9007054081058031100802d8020400304043d43c0d61580c84d40414070b00e12545000301148442150440d00f05000502800303064955512400815049038820a901048401c12550310785109602d41d0036a20003590011070b0381828031a6030005c503d00b43c4c0000c0103144d2800f80f65800c58180c40942110b14011120050b45028400e131003840d1308007003034651b400a0a40d4903c0c2044101807030510410240030700c2500c3c9103600210005042c0001d010541c0f410748101c000603e02403d011851507e401d00815000c201c074032410780300075a2140040c0d81c041180d04400001c0c1d500400400c110080e034038108200c80358289441c01c02c001c0c0c0c01c0b000c00d0320802e40d208642c05404400900d00e0764100075034031084a5840180304a82141c942000000183c94101c082e0507101c45202e006290317468000000e9241c000141e1010006602507030320a41240c8607102162440c0300d02ea000c2440c000c00781002541d01c2c3c0e01b01d00c4000e4051260400000340c0c0200c0c0d80c09001900d1003120700b44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280543183 1250 280541933 280541941
    0x703020d090821070507030213150801020c060115051207080412020d120b030f03031519030f0201050904090b0a1e050402060405090712090809011b12080903070b0a0b09 74
    0x207a42c0c10b200b19158691038022034040c110b4080700c0e03000c0e00301c0520400c101c071b0320680c80358040344080c0d4000c50340c500e0103901c03420040d184408020f025005000e155000f1400c00350301c0540c080da01d01040c8501c0c0c801071034203400c80326034610400c2114141c45c5000a0100c0c80d003008003000380128001c07203003980c0b0a0103103400e60080d01d20100300e104000d041c0c1d0752429040001d1340050001440071800c903552510070bd08120781d40703071024005076110302840200722103031101040620807001e00c0120306662102402d441400040c8240c07640c01100390302840e080e51034074205000b0a008041000000d070010300c5040030800d40e40f086400c9141e0303021982421480f078800c00f00300b810582c1c80035100298030140500060141c0d00b0906406075200b52586480b4a00c9802d079100b610848200c1c82c026154500700203085c2501c0d503042024140c03406e18142e003940709003d1030740f612702c180c100501c0340c1001c008142c0003148040c0c0c410000d94031901e80041e503003240303400c02c480700b00c0081600d40200ca004108100c009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280544433 1250 280543183 280543199
    0x1c09150c0210110604120c06140a11040303080a0504080405030a11130e0a0204092f010306140616030e03030a02160e061e220902010306051c02060304080f0703020d09 73
    0x1040f25503140d940280095121903030740c0314203031482410311410441402014004a155406103e10140d4110181d01080c1410100201910500e11446210000400007040081e038809610b81e4066004200002c03a6143d92030f051a25104a5001c43d51520070b0f05030702d5081c8401144032058001c0c0c21140e500c03003801d1b024500015101d018039a040c0c190040203001d009820140c10030103c04d4803680c80c0758120070303955456920740ea140b00302c0040741200300f800309500d658141c440c0d003000d000380141c0c81304009422070000b400d07440740500c03215503401088000c104150081d115000021750060540b07455100191000703660303c0e0b8041c2d4010311115101070005402e5001e4241c9401030b600a4120084c134100d980c5204110040c0895458001924910109000c0108078001046006e130300400700e001d2040340001800d6603916002030780b040d484c41c07218007c0c0c0000e44a210290640c1918051303180c3d034603800c1144060113a0748860a002a0003c0d01c03200301f40d03020690540c0c02039541c83c1d5010341c0303480d0900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280545683 1250 280544433 280544447
    0xc060708010f06020a03030b0a030b0403020f0114010b18030a080318010501050a05030a1b0b04030b09060630070f0f0819120c140a0b0a0c050c1c09150c0210 69
    0x5070f4805a00041c0c0c4810100340b003500204c0070400c0240034401100d40d00c0d941c440707501108607015401070b046941d80744040c02c000e004810b0030003a4034050f0403565041c401104040d1107172400d50b00d5042c00021144070310340c40a0085100050b0444625600d03403900c8401800c40c00b100d040e40000c503500c2c0c02d00101d440d11f4001c403110182c4101800401c0303600400d945400d039203005103441c0c1180c5021034500017100f058a80041c00550b100380fa200107030741440c024540c9891405481c45100d0980c8803044403000b0452920140b1804041d500707900102013000792039080041c0d0750003c81d4110b140540108041350080724540c21182c9000c2240ca190074071210106103c502620001c0c5401203148800488500c94605c0d00c05c13290081d11504104510404130307500e810040c84089615481010400c00b1009941c8150750a42c811414100d18102144130b049888810030f501c03a00c8165024640804d255109010000150008903140090b003104994040d01e4074040d4081288105686120a0384191041030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280546933 1250 280545683 280545689
    0x15180703080405010c0503040819060b01030b0d03081b1b0c092802040915090e032b020f0c06010519120b0c091009030203070f0e01060305090c04020c060708010f 71
    0x3445091500f0140112a502c240d250180d030180b00610001c210309405004400c0501d00c020b600490200300c500d08101903e1071010314a050510341025800300703448440c180c015166143c07400c1d15a40c0d40b010031400403c1c90f2007407441c0c880b26002c10380e03c04100503200040080c3c888807049403180c3c60403c04000c070100d41100c1d85c0c200c582c002c0d00c0a800f84010715412100594a904000d410030fa02c1746a0300c01100e041404a0540900038401001280c840703206004141c0d202c000558a000c03024902d407401c06180c4511075003100c440c00304502d4004000e5048d900b170b080003211b00c659241d24440300e8680d2020300703006017071140c814544c4040c0d0810032402038100b1110f83d804180964140c1e0348078400c0c0d07014010007201071005c0c20001500d09981d1102c948440b80090b46458600500350700503d46840c0e02030b004515002c020440c24000340d40980c000e241142c006113004605036481114280c1401e00100e0100c5d002800811042c00410340402c42c00d2280403203540300d05480c0c0ea200c402c0c40d14015188 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280548183 1250 280546933 280546943
    0xa08090306091603080d090609210203090d0b04021203070b0403030606080403120e10021606110c032d04090c030b040b0a090b12060a020c1002030103020a150201090515180703 77
    0x743c1080010428400f5002802d010f68000500b0303245a1104d4060302d003101c608680004c0000d100c01c1800030800c5501748150420320045d428940c0c0c05010414010030954090306a201c3d05000030215694181e500300503400c4038007980d41b03031541858198440b1009441c2140403a00b404004241e01c0e105080c1c5902c030b1505a51048111b01505040ca0020b00c0f0f0340d03000142078002c996040d40784074040c0c00204515000608004e01030318542c05d1003000c0310741000115501303000800008008071400425500ca058801443d000a81d0500b0070540304e101000141c080703541800304000502d41c85640c89103219000a031030505c105a0382100304001c030340c9001d40c40f80d0b0000d0401018011550300d079002402c03905003e030072410098085520541740c181c0c21074981500c5034001030880d5111209001000b587d403002c000a5045504550000f0301420403401004440302444606103002c91003500080300f40740e0400c0070313142c1d0321960340707011815a8000c1710007281e10854051040d4107420001107e90450303407c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280549433 1250 280548183 280548223
    0x1201090803070c030e0301090c0f0503031c150914070e010f080705030606041d100b1303031b060903020c01090f141201060b0309210c1504080c0a0809030609 69
    0x15000030f44a000b40104180c08011700d408008125840920a0b5130103940070b04036040466252150300c407211100740e082180290000e11601040c25910340c1c0760900803104004c00b0902403000500300c41021010340c05095558200b4103544407591494100f503014000b0341d82d41e40000c0f221b0100640c0c1000c1c0d45228000000e40c01000202190311070405540c015100504041c549a07031042c20f40c00c100e50b400c421b5010140c3c60303030a02044800e0035110314000c1400b5100d40c1d091102d44d10420801c0c00640c880a8207003c4140400d101c030010a2201d42c02036980040b00700b00d54402814025610b0440b465043d0110b110004007150844034020740c10300f00c1d000b800100802a80200504c03021645006004000d90b4950001044440790304000d0b512801814000b4050794034a1002003d4940e03000b140307501ca01d142048944405000070800f5800042c40c0368100a42c1d84451800005500c22616191018050245814100510403000f0702580c80300300c085812988030300c150a0f0315851030200082c0c0401503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280550683 1250 280549433 280549441
    0x30105090610090b0703020708060106030504020a090b030106030b090f0d11210f070302150115050708070c0b0a0509030f010b0a0302090705120c0405120d02100f1b08061201090803 79
    0x21840c1d842c541e407010341c60400103043e07440c0da0715005500050411005608002d40c1801951000c00800e801040d9624090000c0c1c00c107900400c00c00c401500620b84500d896901e520a00e89003504040001d50380080c54501e50f15203484c40a448141e811850302c000d0043c40e08a010361803280090050f03540000019040c034001b6003810410b240302d045010800060700303020080e490005000940b9080c2d01a0b0094007103451149880400d5400c1604106e5101c0700f1410b051051035400070032703610b00c2d1382d102045d02d641d0401c07410110070102c6168001020200d0014440201e681d1040191400280035012100c100f450480e14909a8000c801034079045590410700300017500d8451021900f0180604000b8642001402c1a0880100c201e8a00000d58000a4100181c2c1801080c014000c04400e0251141034000c04000b0745074031051400750728150712804400c01c40c100c1a8049202e01010015211020031218005030038540d048851500c601b40d440342010001506000345401c40c0e034810046851503032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280551933 1250 280550683 280550689
    0xd173f130201020a08071a0c0301240c0c0b09030c09010503100209060c010e06061807081603020405030102030f070801080d0503071206030b100f0801060605030c0d0b030706030f110301050906 84
    0x4034024140e04510071580b0080100341e0791002050baa9006141c80344a10f04020344403004c05101404040c4290070810041140302c0710150b00d0290080b080007402c22540303050700d0031504500340c40d9029100185080e4001004001640140032030f035030aa0565000070990740c00c01580003024030413103416410010b506844105c0d80d82c001e05150500600103070400620128a43c2110b445ea00b513000154072940c103002c00c034074006405003100c14140e082c0407921302e80000c004040040250600900c0c1110706070b03580105002c3c2e0180c0d40a0280640219141d1500c0c10310400b580005176070348004101900d0000c81c0100000c20310a414280340e880e25440c0d030302c0b2020101c0c0e00d81e01250740762001e1b6546610100004e00c00c0780b0304a0042034214144141c03e41010558003a40820b680300400e1685002401c004e40c0d07810109036940325214140450712816940c400002800781c4103440d503818080c5040c04610246c059101708a12651310608001c0b4140341c1c550801980310038020207034040003800016110740b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280553183 1250 280551933 280551961
    0x609050f03012304032c010f050408150f0105100503010e0c07140604020f01020115050603060a030803240105070c0513060807080f1603020108060d173f 67
    0x40301400009035640015600000b10403894482d140c041c160006100c10305070320443c40c0a41d01c000c040790325403a0300f40056240c105e00140d0440c0f414070460344000740c07172540560103a4000744070301c0d0180d419883c000319500d843d28a003112810042c281040005c42c0d035082548504681c03254a4440b203107182d00308401450081c60081c41c0c1c8082c00400c01400300041d1000411424240700e0000400580c01c252040107546080c204809046a00d84240101c12065000001d030480d44191a216034070384950001c50300f03000280d04090070540c8000705003c0c00e40d00030070078908281c8014030206050a5850011506403154600c090403010b00000184400e1901d12042c0600301c1a1b803000168140e501c072042801c09040e50b10643e000d030041e040842c070355036051100340a184440b420403e2801e09550028102c006c01030300c0740303014024003420b100800001f150500700c200c0b258005291956001d40c413000e0a161603c228440d90140c0a00c41e1482c00a101001c103900464420043c405540b840308441c0300c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280554433 1250 280553183 280553209
    0x150e040b04081303021c03030b0f060301150c021819020426030c0706050d0f05090703110604081c0915080c0903031c09020a050303181905090f01031407060905 70
    0x103694210f500100580c1e5907680201142da0200711792000641e00c0c107015045078811601d13280500141100e03415180d0362141164103480f5580010445003801d500125146c0b0300d0410001e4100411255401d40c1e032155002d0303075200744403130140c080782020000b490100340d019a02c0381031300c201c45440c0c111071301c41d46a40782e0082d51031140e004c0b41e08103802004c00c20700c0c0c000c280e41302101240c0005034090780040c0d1406881308061140109000c1800d0481c010350b0360b50398521001d002c3c4044128820f03003d5982c1801c030303002460b0a40c101d400b0740d0074038241e0600304201e01d284100445c0110344001020300105a4140300751480d51100800d03550342811014040d40b05501c5d85606000822005140d041c44008114031150340501c0000d01c607e1510501c0340030441600010b110350b0040c05070001151900c071407020540b02c10345030703080114070928069040100c83e41020781d01c04010801c20241448121009040320702840741c82c008241001540c5031a481540908000101000300912142c24042c00503a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280555683 1250 280554433 280554457
    0x507050315160e10080109060f060c020d02040605091e0f0609190e011e0e030f071104020409050405030c0c0111250f1502100203010b090d0222150e040b0408 69
    0x1070f102d00d20000608400401840002190f00f203c01440795160511500000d8602c442e00b003003001c0e007000c2001d842180c0c04500248100462680d040440d11a5041a002084040d04500311801d0613205110b0745031241010404850341d9000080041350400c2c081070045101604007182c90b140c00f5201c41803032a0f0401d0b149141d23610f070460300d80541d03024840d281c01c00300c07000d01061071041440d00100c00e60f0074643c0c0355002e640c0207018500100303802070304940c1c000b0f030302445265207218250081800f0740038a07030015002518040030042445004401480e040d030000058450074101103005691118101140007000e070322003403041c0d590380112550190382c0381502c00c80c2e14055a407003000310140c446d6a044002401407202c41c15051036010407a83c0d94510b080641582990704082c5055418050380307420500c00d10110b804681592581c0c2501d80070f0440200c0740799a00500c0711040c80c082e00542d5120038024490302c2000406446290b400c0d070107543c0c00490080e00c1c0d15551104032980c5c1124000c031503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280556933 1250 280555683 280555697
    0x80313031b050f040f0e06160e0d050d0804050a06090f02010320030106030b0a26120c0c0f13111b0105040503030606030619090c08090c010207030311012007050705031516 75
    0x4095410000c0d80d110380461a24030b40c1e040c230b01c2c1c1d00040c1218096219507000301c804814004c00140d000c103a10110b1641840d040d56a40e4450511500d0100c001c103000d00741503d0401642c080c403001c2411490554000e0320284080380e00720301140701c4580000700e000824070703080c4010300100d4460381118404620003458603408540300c0c1001c040304004040c0f0b400c4100039240214080c40c0040c40011704a0444401260502103600d80c034680720110400c0b0503115202c1074905000640d03034882101d00b40800903204015003021000713948030350760094012064400f40300082100460341400ba5500c1035900c40091801e680300e19041c4102500050921a40a00b0070124007060b4040c602440780103080541021403481012140a40950405004110160000341c0741142c16600094050122541481e0550405403607015060040806545006c4100501030180000481800252041c180036074143c0d92510b42c0c034400c0583e00c0f02c0d660398658840016900098000c440083e50300c00801c0c042c2130004d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280558183 1250 280556933 280556951
    0x30d09050a06060810060b07121b05070f061b052503051504140111040918020907080604050f04021c0516090207050706020303101806170a050f0c0604170304080313031b050f040f 78
    0xe4208032441e000240c02810400dc01c0207500c6d4450b401750400003125143c3d5060f00000e888941c0c0740d1845044010456119900e80400b50b1210b2004034001c64126090720700182c85041307945086442a0b0301500e03001116a0210030318003062251028413854a20460701d40b502d0444040090180c042c0302c1c00340d02006120010150701c0e5819a0351240d503040d41d40c01c03250700d842e80c100400c40302d01810700111850b00c1c004000c01a110111854101c40f501f80c1404456001498607d00e0501022411080c100da044800107801c50300c0c0c2c001d0000c243c0304d08103482c2e2840e2181401c07070341c0b8001115503104103040000f08000712002c0d1076026210354a460008550701c0d07141d80d003500b01181880007505046c0d01504030801409000e0060405411070301001d0013040c000c4000094150040d0300440301032102c051030703100e904142001110014200901030301e45030000090051a1800f080c4400d890010b00c41c140c0b000780341420000801501c10041803441094291800c1c040227100684500b48842d540e21001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280559433 1250 280558183 280558193
    0x415060807090b030f0708070608090604020d0303021b0f070306050f060f011107031a06090a0902010e27010303180602030f270a090218010c05030d09050a06060810060b07121b 77
    0x10003510b00e0100420b199890262700a05020000b402c2e0805900010180001656014609000c0540600c4c026880d098400e80442030707a500b00349403441d00e02c00e0f2480d113009034202240480840703010b2442000076944550502c0002481120b8a42c0c2c07000a80c1c20a081079070041009230020042002103944031034880d51a031001400f00e600c03050031000e0020801c9541d14240f00390950103c041c1a09000e4101c0b158006801d401c80d024040344078248450b0030945001c41403903280d6140d4154060b60816503524103016002d8040c0c2241403060913118503000c141c160001089600e95520254258a40310701440585079102c1c0002c0c0408441424010002c2c45076122a07000c00901500c4000503a5001381160403a00340480e0a20356050002e80380e09280406c13004000d80b4a4040403003070203d809405032500906126a0540043c00386241407404900d00c000090340c030910300c3c003032482009a01d4075400e01100314000c0550042c64850102400518944195015640381030a501200060403480c0d42d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280560683 1250 280559433 280559443
    0xf12100f0b0a05030f0a021210051e01120317330103150f0308162a1706161206090e0d031806020c1002070501050415060807090b030f 59
    0xc010065803201c0d03614400c0d1601034440380040400301c00516081601c0441c0640f038112881c0064410303d5808030155a545003880700712908002d035a010485403610036004228004e101c5003049094100d080003054924010007000099609501c2da2108181040a40007040b01c2c010407181c018886142c904074031004000030a8180403028260003040c002c1400018112203801504980040c1d04050402401011007000c40540b0340020362103035107aa51410410300c0018404006200715500914603450380c48540701d841d009490215001c224640d154601c1c1020403e40b0808651a0002004070303200745250303e404092080141807559607400a103000c44210f5516a00942003291241d0300100c100c0e80c24044001e6041103800c04112055085100b14100b42140000400031a80054942c00c00744040260f0003141940780401d642e10343c1c0e20710300b9074041c04003502c0880310380d4401c05000c0019040d0780039060540725a4001049002c0c0340004180190401c03030f131101d405004140e01d4503849201442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280561933 1250 280560683 280560701
    0x3030f09012a03050705042306091513060804030e130b0a06020106090b03010203040302070e0c040506130503060601030506060d0b01090b13080d03020913050a02090904051b0603060f1210 82
    0x11a599440180700083c06a0360002c140c07000b0018200800c2c0910080250070700b0340300f984038880190004c005030100d81944500c0300c900303a00a0301c10801c1030b0f2030141d0305c0080908031803040030304040503a81c00e0240c800e40c80c1070b5002404a0322441c02d02015040a036222664851264000b00f04103411201048820085400007030040c0d4454805220500071805060b600d80d07802d034002c519510b800c1e10021340303903030749030003890290400d04012403140301807581038078080c0000074546907842d007450f81c00d410500c1c000d20400b8000d000b0440000c04a6020f13205141c819000070740402e02c2e007500c00c22070200502e61000d86c41c0c140800c00310701080710040320000d803156141c0244111507076401d02c0441881c10000c1050310301007600422800c5200d40702c0d6a20416907024180380820640c0f2000c0c1103130081d00401c0560342d009a42281003000380100000ca0200d650718208200900c0b075541003c0c415a031004480c0719030400e0950100181c2c40c18024400d0b00c002410340d050740c840c031841001d400d003501e000903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280563183 1250 280561933 280561991
    0x20d050a020316020c060703030507050d02040909110409020a09181e0b0c0a0c0305091203190906172a0a0e18091c030e12130e010803030f0901 63
    0x302c10003280540b00b0030302c1c400c1c442590009041d040c06402c0042c60912804030010101741e11840481c3c2101e0048007610301034248c00800f075448a468102d04401008014000d80d05558000055106805d041c070a4190280d0084c0c290750b0001d041648400190400f10b10102c9010001e9040c03001248680000303400b001c054000083c508411801c1800710003c1c064140400700e14100b28655126030030005c80d42c1d565905091442c0c455034000c00007030007441012410011070100094001590b400d4071400303c0c02d0402d03a10b03800c01158840008807201e84288001d1942074142a001c165551480340d444011901c1c895800850345640840108603900004142c50104908012000d040c4c5807190184000d003c180c0c45510307651404c1e0b5003017546d8910004400c10220b14107c00480e1440c0301c1d4010072507400c04442120080415800c40d01415800384c018040050460100402d012015002c054106d9000000645c10741d21b55208141801c0d00180000f0f10035903a42c420b1824500894801d0900c00b8050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280564433 1250 280563183 280563187
    0x30f180c19050f040c0c1b0321030606050307170603161e05010c030f21020f0405040506030102070b04030f050c01090c030204050a1514030304090501090501050102120a050906030a020d050a02 84
    0x403d014080c800d10441501c641d0400250340c564903032240055204640200c045108040080100a0306d03a031240c001824040340210700c0c00305510014211010854503039010400655100801c40d441d0006844040000e00c00401017280307880e01c024040d800100080c1900c0d0320303481c14109401c0490040d440013900b0f50712500e1340c0b80445403400d0729500808081c2045035481d0415a0000d0000c03140001c404284090058000345130720510703841040e1260080340865944a4000e003000301d941180c0f1400d4801c0f4181400504142818001d440900d0b6100105007529121030707409136040d08848480100300302080c807509800e48424000d90304154000e0000d0f0131041c0c11401400140d441c020b011841081c00d003a42a00e681c01e58440840850740e91581654840e059080024110308c119880750600b02e061000220b6080c6e03240d80101d0495001341c00303c1300c1000c0032043e001c0c0c9030b010303030031111001c500c0c28405841203040a100441e40002e80078401445c1c50018441c050841d00e05071a0501d4142e40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280565683 1250 280564433 280564439
    0x2b0608100b090c031e09060a180f03050306060c03040b09090112020f040c03110d05010e2809060b040c0206010e01080a110409060902031e01060b030f180c19 69
    0x2051120109905003004244050168000490105000907040800b0f03000004000b03031103070303a0410041c07000e0310281410103481d0500d00803182e0703141010380703407602214a00200d40904100058036aa01194048890b07550041e0030f480c03e9819400c010f10351034110104001518403401d0030700080015110a0788643d45490b000420302082c520140c100315240440001e1074405a552001c081c03904000483d40411303008c040540441c06020f90307005400c14000007244070900000c154108074140d503a482400c00da82d03501e0403d5071860060f00f44030420b14120303901c0b100c40921000d80151027054000c080121b402c050141c0460100c92001e0480c0c40103170081ca0050040012400003280188210401400c1c880140e44488602041007500144103590720303031110301004500d400502e00709070002e007134581c2c4c9041039100307400007205004034082c03d51030705030040b48c0e0015090a4074010300d40b06400c44140c0d074400d0301c02c240540c0701d00310f002424403034030a00d00d44a507140000194003051000b40c0b10401c502e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280566933 1250 280565683 280565699
    0x60a050601111e030d09111203091810030f230c030d05030402040e011d1204060c150917041701050609071812230708070b2b06 56
    0x8009092a410080c00710190b403141203000986161a0001c8034481c04000c09905034280f56100303a0900002590030441180c007408140700320000d4084082d95131041c0350081440a640f203110380421154800c2d0000108824a0112958990f00c203031034980c0c01440a440f9183d840b950040c3c500119404524121103026102c045101c0b0072040400c10003d106c80b21820300001c1c1c072212600b112008102c070200006080d55255003240348981020700c002c0040502201ca4240780d50305d4010f603c1c00034400c80e602151000300310421035044441d27540d180806010700740e80382401106801180d00c622612010800003090400030344c001604005801103580d18900b00c650741e01882c00c0020398034180d1406040100546481000b030358008154540030000d0100348a20350104409031b00010828082e8031085403c00c0160444202000001c0e00da450b100805120b03615a1001b5900643c000c68010900c20000d402850025020007801ca119640740b401c00086208104400740e82d50210554541c1b41c104404a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280568183 1250 280566933 280566941
    0x5040b030c0706140603060a0b030109020d030905030d0e030606040c170106030516020610090b1c0f021c02010c08090f033f03010302010f05041e0305010c0c030212032205060a 77
    0x88941321003100c40b80f61000000340c8a090050014036200d440300c0e0b294183c2d580a43c442c12111f40d006240c0280280581402030600150303025150103440f4407061011820702403060701410390707801802010560b0700c140620000c0c000c01302140c002e002119601080300812041254040c105a07903000480d4604080e40501490701d4444010954100d00244020f00c441181c05009070340c0e80400200d4140000740216081001c07040c0d44003040d100961000c000c21103010301207440180212034050b0f0300c01c0c001c1c3e001070318201c0742c103c020701080d0400401800100240c0c081c08907140000c0c00d021034180003d005c00d046c0300500c039208408460300504110070040702d55550850300c18150085000090002c8103072058030041c080607040c040381c8280c8000d9544190101e0b00600643c40d201e41e070300c650b01d103080d40805045010440700c2d5406e18241044007841280503000c1190940d008161161020035011010342c009042c40306075145040100100307044818080032143e118400909039450032100d488212 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280569433 1250 280568183 280568201
    0x30a0902031c08010311010e062b0b030d2102040303080108010c0804030f110a2127090902030c04020c0d02011b0507061d10020c0c060f120705040b030c0706 69
    0x30048100781c02c0445a8018070690640e0b5224031400c0b0f0070002c020069441e6040c0340d01c1654000b0000500d00c0700c1040b088259038162400108140b032007007400f41c81c14191041c44102c1501580041c41c0480d031544101400c040ea10710002030880d80300c10302d204000030390784150026008603000788010000103900748194603025020707103007150f490b0401340e500800803450700611204002c109903c0c903c1040c018402900025848140600012891542146040008094900890f03814060000c520680b60245d0240034140420040f00700d09103040c882c000c0c500b00f0401da815115807048003040e81c8036840144010f07070341003001b00000d2101e014020300790355078490540c0390b104010b1842201c8580100c1a20340c03941c3c0c800c0010a0440d44445410100a408101042c1910640000459107446d42c0e0003083d02881030781c10350300481d03103c105209030f62240d0f035180200c01c0000c01c0407c00441c070010450790401018a041440c2c00d95808002d03009420503070b1518055100026a0002c200f00380c0724000203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280570683 1250 280569433 280569463
    0x70201020c0d0b010302010c0809131a10140d0207080c0c090a02040b0a0305090307050a08031014060702060f1e090a09050609061002070518010f061407020f040f02030a090203 77
    0x444200d540c441002c3c0c001803100905020b011f002010800c585031060700d00c000c001400c0c549a441c500019600501071918440540d40d0441c0c691140e01d003001c0d0030200c2c40d000f5075100c0020159440d000b00500e0350029544442c01c55007480368400007038941c801040400c01c1d100c010300d900c40180d01000903420000c0c000340d00503031040001b04072241d03a02c41940c569140034103002850f50398140d001801d5200d09400101140140b00c561020083c0140c080c6020309407520002420f1512100051400c80300b000606511407000c0c003c0031b0040c50305900428244002e44202030808002010b606030010a0050f81c051020012a43c125142080c007400d000802e258031080c84641095004030b40c1c0050003500d124000d0001b004480e60f028000c00c84036008010180140702020f90074800d41302202c0003802000b00c824104440060258890300144d1a6405401c41c1359240c8102035003000010b002d408038490b040b0780c0718540c030703d944011807000d1446080f031407001083c0e16103588101800c02c8184802d070b43c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280571933 1250 280570683 280570699
    0xf12080108150c070c0801020d1407110a080c0a0b100801110a050d11091305041e02060a030207030e0d0602090a0602060118050a0b03011b09050f010f030222060203070201020c 77
    0x1d40250300036400341c2c01c0a40e100346a950313900c460400400100181d0817801791580006404d006480f5a5444580042600100c92005840f031b49001c490400902c660008154800d03002607020848800c0107002680c196011580c40f6100e594400ca01490104c031200c840e044c200008110b945828001c009034071340c00380031b0740d4900000c1d20805803071030060007107030300c0043d9491090350034a00c0203000720b913a42d50004114104455201c040040a84000c4601300c680d418420403d5405038600b0401c3c0b02c0c0180e00420860410392600421030094104c11004c2d0304000303020060403040c1d00c0b11403030441050b00403140580d80d01300c44400d11503a0642030307000c1011584900010407480b004900da0302182c030180c201c0468544c41320f1000780d018040c2c000e1016815483e20703155815100c14510002101e03003441c1c4070792501995400400030711100c542c581d0f6000c24144401410014402e50042128000509502c0c0e00107420094010710503c180d0488000b5038000120b140945d0380401032881c04400c200c555071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280573183 1250 280571933 280571953
    0x2071505030c0414040905030309010b01031104032a051c05010e06160302070309030203032b020307080a2c030d0b120a0204090503040b0c0303040b010501030203070c020f0d0f12080108 81
    0x300d02d8071892144000d031584940580c00d465072190403e00c072858208040740e841741814040385000b41214103166000c24036050007106804000d0056504491308002800d200b918130780303c03100040a0007112090135040d078843c0401c540c2c7c0c1f081200c00e4044064201980041c8262410f1801c454081109d42e150350320010401a007490190405c2007a85d00e145009030b200d0b00c0b00d02d03040d1413600440d08004e5040c0400b0491480700e60703d0301e10802c106001600c1c203224070f40000c071084040388010760710940018100400203147c20b0300b0340c200e42d6050020590032a02d40700454140c0c0c1400b9102465000c03941c2001890481030f214070700030110b151408844140c0004840c5000c141d8034494944028003035a00c0c0c503501c60138010140180c2d00100b104116090340d034aa03918000707469074400c0b0b8003281c0c03401a040000c078965100e4400d80b07100d0b0f0102d48a400b03103d0815000c02c503685c181c00284603413000600c249040050b492403a0b181d0024454008480030420140001d010264142c01041d587e600c065100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280574433 1250 280573183 280573201
    0x6031406040b0103030e0301110f0702010311030412031107050d0c060c02010614041a10050a020111040b0328021206090906131101020a0c03030e030c01050309030f031302100207150503 81
    0x2c6411254942803050068503044040781c090040b035480e407809100d01203148440340d02c0d03c0c0018801d1034800d0b68108041d40d03030007154050300d00081d80c01500c00010a1403280b0729600070380c0030341e80b03001045489a08100250755a030303191040340e0003200c0008091083ea0010490280901034001c5954002484518100b03000b82404181e0320618a01ca551101c1e664046c680b001c400140c214003000e0141555540f1051018006600c40b00443c80150b00e406003042c02c10580d8402d8500791010068003500c3c5031582c03000e14058454200103032038880e88529002201900e98402046255514159101e41d882c0c20410000c60340c0d001444142960000c808000307500320f0400c1c59018513644a0010580c0b0069080103e1822020180003070085115620210506401c17081000d41000101d007120850503001004586074082658901c1c41a4000c0c0301c000881c1d005600519440010f131400c9402e842e00e02d40000d000329112404400c0540c001c450248601c607001804c0c8044043d85e800c2891840c00c12081d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280575539 1106 280574433 280574453
    0x150504050405030406020f16050d0510390203070305070c05100c051c0e0d0f08040308030106080a0207321c260c0a050f0d0603140604 59
    0x710821f522000844410481a12100c08007103031921050141e07000484200301c0310750023190210081e0300f406110b146860010740307001d6031500440004e404e0361030449500d01045d40d21000c03821241d03150000102d60b4940d505280c540c3c4d940b80c40f418412461411904a1640540301c4c1c4111100581d01481c0101c5541c0120b00392080294245d202c0600e0003201c0c0900d402280c60b0b00d2075003c182c0b41241c516550180030700860a140b4020350341d0b65070740b80e00907001162100c10110040c020264081d4140340d01040303c074000c51a12000340c40380c0e1910000c030b00c000700c0c01d10100c102d21041c0181d031109509041400000702c524401018041d0b00d0310420703900301d00c40042c84010205c11161010742c049020806100340d0490903486200c1d00b00100c0c2c3c08281c181d81844400c004040301701100000030612752452007400550581140381000301003507039504802c010b44c044010712006c114101c003 = true := by decide +kernel

theorem cover : BRFrame.Cov 280395683 280575539 := by
  have h0 := BRFrame.cov_init 280395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280395683 ≤ n) (h2 : n < 280575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
