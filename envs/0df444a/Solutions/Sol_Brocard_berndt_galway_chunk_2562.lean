-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2562
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:40.198655+00:00
-- url     : https://prove2.me/submissions/c2b81473-9afe-49f5-b528-c26ef0b6b945

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460611510 ≤ n < 460791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460612760 1250 460611510 460611517
    0x1101060305031c0603171809040b0901110405100503180102031f2411010e0105011403062409101214100908032205060f040c12210c0c0902 61
    0x868000e0300050380f90000c4070340c01400262a00310114569040311004204c085500078101d002000c215000098016030720f44001d644610301429050800d4075004110508540415844269036039088c481400980c4989102d85c28400300c2d4201a540c1c2e485450317032a81da07049000301d4800325600000410400020b40c45141002040c0080700d0b10269441d589001c00154000150364409220a0003020b4203900c1112291114001c500002a151451055003400e440090f0070100401041104400090408010681d440407804d4410400c4528024008403a8624810300c140b0030040358001c40c590003410b143c40c00092980541c12040907a2901d8110400758910350342c050280504e00e5541882c40250084805080d8800c4505207507a0703900a2000407400c80111b0154644000450100012020042c0c107000c0d0500644070080c902c2c0c80c3c0307080a04009030b03402800320310168040e120001400403040d800c1000401405141e41103c1078402c4400c3d140c44074001d0b0400c10b001800080d0718143c1d42c000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460614010 1250 460612760 460612777
    0x240f0f1809090f1203060f1e120a02030303270d0801150e030c12010605042c0f0c011209021903050c0a0b0403080c07170601050a15020a0f03110106030503 68
    0x6000390369a091000764a9148488070283c042d040010340c807100710800001554040f4004042040c948442e401103032001070b030341d0300891114890700d1401c2154070340301030422084c80c1d24030010030790710b4025404aa10780c000500035214400440c0002d02c66081201100091192503c0c1198030b4082c06060003040c445c1b0030320031a039008203d510000020791080d81c1eaa0108903029009150218102090000801c410003144416568514020502d41d46900a841314503504540c0203210400d00f0b00140c0003c241c540c0d11804035807010b1480e480028010030301d910b400701c0074240382e034056070f030b40045001404001e41c0080d4444011802403244200e06003c14043e05c0c0200103c0b2085001030040c0004840180180204284144001c100203480724004000c81092001901d500d42ea03584940b030545010402e5480e980d0308024014041800c00320500340c002c003801420051030030000400a51031b00b290500282011404092400a01d40900781c40c10015031108000c01036a941c07400d0003601c0341c010104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460615260 1250 460614010 460614019
    0xb0708060405070206040b1b0c0c030c091603090f0609080a18050f040f0e0307050714040506090a020a0c021203041d010825151706240f0f18 62
    0x106440741803902c01c45208940f50780040c403154503030f5107800303124100041c0f08460104100d140800311520000203880c040781040c000706150590182010308003015259000d004150300c17410804498030140d500da4048a583c240094011040c1c02d04111306000540054000c07410700d4a6241048442d10080c503128146d5950001ca90807104006074204e050f512410f580441a55808805454643c2c02842c0552444500042e5000d07021001425500001c205403500c0d0841c050070441084ea805001c14000000c4504000b1460100000f4248030303000340000010a41c04140940ca05006425605d49181c00400900c220006800c03d0341c2d0b01e9005004202888a0200f203502a4044002a150590f200c00d0058000c6840014070000d8801901900701b030000d0f41854001215603691101440c00b040c5982d40303002240348000368007908400a080f0b2809010350f109802c64038070001c2411000e01c0900521250348942d04004446a030103503118510180400140f01d80c2441c0107000d000585160940c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460616510 1250 460615260 460615277
    0x20708070b04051f080c09010504091104061403010609090f1401180f0b09150d120309032a06110912070812120604050c0c010507031509180f0309120b07 67
    0x81c4c91038105140c8156a02003001400404c0c0c08000c004060715a103039040c58060b0515582c4e850040613a0400da081203d0108001780070301c0101d034405d15000b40442c4a10349a49554034205001b00b0b03407602c611600040e103564840b810100314240e001704641545208065103656181d18014160203460030440794810b10303140640c030781600280124034000c80e0042c0740380c8107699a0494083d880c1740f4500141c1e480300f10a4140e80000d87d03050181d07000124240d40020300c59145141c05400707600120003510b00b1030f06005440301e44001c000e241c1019554425804590420070700722034651401400101988604540e44c0400510000030300c01d0106c41143c0100c9840c030282540c0d2100c00d01c90049400c0c02c20390640d000514034240b940002c0c0d000b042c54900c051405520f11200c0742124026902480000d4840e4112505c000700260681c001e044900c00400003489505401c60300c848180d040100906070b2001494107140c082d416580092402c0348084041c460fa40c604005038040c100d44c0540405c0221 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460617760 1250 460616510 460616539
    0x20609100905031b160603090302060117100908090d031d0103180609050a0b0a29030d140f0a0801030614060f060304020f04020d1a0301020a1e020708070b0405 70
    0x207006540700705402038040e600c2d00d004e8890910b001c040114045036a4820b030140501c0c0e241442912078001c042c1c9980000d89242103140003420040f06038001d01d10094540c40040301b424010070040880e9068820000e070181c0c0614049003240501d00500ba0301405414142d400d02da00100c00da25003102c02c485d1901a0a00703500190308444180c1d450300d080d80380f04883ca8000400139400240c00d240141c08644140d84681d1b01e035034544404450348211140c0b41c43c1c41802e030064a00c0c3c0c44107004900b402e0307140f0105e20301c00400d5071245622050001c0010030388481c02401c0882d42101e140b02c0c240304045507144c80a17500a4050310080c40100c070890b1500046010040c454241c080c05400c00411010480707601104000c01c070b030030262099900020441d05a0002d0366a8401004a400640d00c0801c0c640380d10091400b00102c0101070b01d020382d00402020841070341c482c1104000c03030011540c800b04140401405ca140c0700c5260000c5c00b942c0b0900d0800304205541c1800361040b180e0440d40000389600c2c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460619010 1250 460617760 460617793
    0x6021e0706091502010908030a290303250f08030106020717030901030c0e0406082d0d0305091504060204050a08210d202a070608190507020609 63
    0x240708003000680079003030034084074450520307081d2054824800420704c010240c0700d8003152390080e140b04031250b0342c806000a12007124083c0010361100541c0d1038100c40d0900c0c0100751a84500c11621051007203c02880c0041d54a031983d2989031608680d4900c440035480ca0304100584c401c2c00b0707040c0940704090b00060352307480c548008080d40300342102039801c2031490760064001c0c140d160034910900228200010190b1030b00d10640c401003110600412041c910080c0b04e9a2014041e20102100c88107200c03000c10b01c1d80000390400207a095450009010750318214110309244a101c0070010502c1c04001b070000b80072141d0080c2003643c1041320380c81d199a40d2418119035a1210200c00c0c0e1940100d85125010000c080c000f42c6000c01030341c4000301e001e280c1d0880c102c0d54060a0f6030610001d00c004942e5100481c04041c11000c8441414080180418100e065030381d190aa03100740d5040003000d1001035007484009030000e4941410210038092810440c2e00603407140012640109641302c1c0d1405400b05118 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460620260 1250 460619010 460619023
    0x20301032a0b1905041806060807020a030804022b060b1005030601080a05060f1815040915240e180706050d020f0405030a0b1005190b03040203150106021e 68
    0x100400140c0c6440b041d030f1103242c0044001072144084c003a00b03100001c0c04044d142861504140b28980c0013030903e00700840686001005052941103500c5440c1c81000640c005074030680064044030081d90644018203000415070218140b810001d519442640410869411145910340100d803c0200c10245410448080c002191380c01d001984030000706004004c1c60340301d250008000340102c40d400003c80003040c0040c1258070641011208030041240c0c0b0441040e5a01c000c0c5012541801400441d88a00148641c1c003035826100e0350392026441c00354421900481c15500c11040459a034668a42c2c2c0000007078411210b1795816103e0000d810300900c400f14050098511545849003892024a1000025049080c40101c9218108400b0130507680401942000c5486040310f070f602c0e0b02c1c0072051038500c1401a40414000c0305904102c40704204a086084240c84004a985849030346500002e880c00c03035404000c005041c2c2d48000800d40035408a02c5100300001c2200d6182402035100743c00d95141d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460621510 1250 460620260 460620269
    0x101d031902040e0a1403040f17150a0923010507080601091203050f0c060106090902090603241806010e010c02100c03020319050324011706060706020301032a 69
    0x10000040c03006180c00c2e030042010011400440e822102c20383d461100790001000900090b60001c1030400403806a5200800078080464a0000d5800c90078a01c41d078841e0b0115251091414440025011405a52003110a1f98025802000c1002c0e40d5088914282c060210100c0365402d14000858150168041c0c0d4025181070307542c4a031040c80c120071010500d0810380201c081101c00c11401d1120b0401002810528540340040c5c0baa55140203005000c0080f030364810600c0c00d00600c202d0402d42e40e900d0a6a40c03080d030090049080d2074100420040d14484248210703840001c20884d40c60044100c2c00c0c561103044282c8a0306900f030003050041d9200035400320b009503c414007039042c200c00742c400c02101c1d444c144203004880c244075500500e0b21f401029000440001200402001441b04800300004e0741d0b01c40107425a1034865409000030802d40010454285560800c808a00540c03519403c079004640c004400f15125610381c5414900e400201e05109040000141c1c0881c80300e042d050041c0848 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460622760 1250 460621510 460621543
    0xc1101080f061003060b0f1201060813120c060216110d053c0c0f010305160c050c0a08060f010506030601022109040e0a14060907090218101d03 63
    0x156910401c101d4402c1c0c0d03002e05841015145d40000400201000280041040d415047c90b1101002200c0b01d106441c140d010008021480e001c1c04a0014203c08003d00190882180c05194000050075204451280c070001c1c9050301c00505104488010089101614801c001e181d807040074140810102c00320f8014090081e40000604202070441041440005000b24649c85d03003c01206c9001d0001015181219001d41c1111010328100d1070141080004001c00342410041820100010b6400840458240003031000401030b41c0d0500c1001c00451911040040158075920303214865951126001d8807074116109a880012a40d1303d02070341541c1c459041a80141b07000100c512918008082c010521402648100240026602c550240f4640241041c00620046a040c0f80000071241102c40a191ba600958140411501c001c40c1d40e5040381c00091000d6100d0000c1860a0030180d4001003003030b031161862240e0301d28680c112000038146100c0f44100c0b5164142c00050680340e10201000b035099 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460624010 1250 460622760 460622791
    0x181309331802120a03030e01090309230a1716030809010f0c06050a050610172d0a05090d02030c030706021b0604140c030c0f220203070c110108 63
    0x440425030000c0400c8848180340c0940c44078540100700c021482548003034603a0461031850f004d00d501030142d075040d14a500002c001107691510003c1c8075009174091056040454240721a525402d200980418440141104200342d80e401820406540d0845441401d0058013900103116194a034148104c941000c0d50a24250070b03540111040ea6036195000c06010748081468080740301482013505c0b921000301c00040b10f04110b8208a2021055401602000400350083d0300341c690004496421202c448801e034642201164075a080c14400d41c040404207502c41c0c10010880d10f1a0881409280702406803001481c240c1c1c1c0480e26482071801ca1002e60788100f0503036000039915402003500160000c0091409030710039190504003034055030709440c2d040d88401e06840201081c810b1000089044004042c81080030700403034464003074146464820302c00c0304450b42e007140e101c01080c00755a0408001310368030b2420900c044c241a04c1d000042d54018108021004294050a0683c0c05621106488140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460625260 1250 460624010 460624103
    0x4061b060b030f03041412100c2d1b0203070e09010f1b0809060103080f030a020904090320031c090f0b01030c0905180316020f03012d020717181309 65
    0x34058002d003076000c102c07e11a0007502c03001c404160610b40c40c41070146100c00c2c480040e000b800144a4004004014000c2f004100103a4002510908807080394642006030355030a5000c070f00629102d008940034030308140c0b00c0049503e03641c0c1e4a4a00d50056150030711642c5508075025603e4400b40801010602e08000395402e10000501866118104240140c0b13480e5410022605440d0010801c5010039501c1c1c803e41d030300b001082c159403c01c400b420001e604104c0c44103810740c00d00e0350010700c110045960707162030000c0c840c030005280788090b00502c0c50303103040d6943d140c815400a150b00c2840180d601d01030215540340c0b110304102d80ba9488800003581003007800e0740706d10a0494880001c030791221600c00f400d4800e8800380107910800100d10040a5075881c2107402c82c1d02d0300200b0604100b0903204209a0000881d50180960844914000291520b400c00d110714a0f101690352007562190842d02400300c098516084048003c1c403a80c40452482c080c85643c108150000000c000f2400303182a4411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460626510 1250 460625260 460625293
    0x7020a080a150b1f0e0906150901080a09020406081e01050112021201060905010b09150307090b0d060909060b0f04060f050d03091a120c04061b060b030f03041412 71
    0x1031100d40c010003504c0928010100e00c09109200b2102c2008100c00315140c0d08a40f40004005a01c8141a9951a480580c00c00000f05511850340c0c150b06020484003c501078000710742c0540c0f08603034080d0003002581c7d1a200310070b50350400390200d580613040d07204038510940b1060140034102c4040f00f030350070913420b020703801c0080d09420820f18400666a03650001000c94060017014000c0c59450051942c4640c107100b0b00130741e480c190107003040701102042807104031944000313010112400d040b9119228000070780600c019000c80d501440707026052100c0c0d80c00b4002c56600242d0070140c121503021401440e841400243d501c1c078418600303c950000b00400950074154070030002a403003490205101a1968094030780c0e10a52810f23488a00307804100c18130030174142c100c403c1d08096002080c600749441c1003801007203001d02d440d40190100c2009001410004c130381e0401c2d071850318001c099030f809000342c640c03039580c03600f007841901f048008242a58006040000c9416580303041ca2000d02071100c0701c0408071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460627760 1250 460626510 460626521
    0x1060306180b01030f060326190f0c0c03030203030703051f0302040f02130b0415050301080a0305091c061e06050d1e0b0403050d1a0121061a07020a080a15 68
    0x43c1895218034010b80e5040c05441200081c42c0300700c1c841d009402c0e400024924840c4584c1070802c401c001049230121007142030301c000d00c50348030914007a001642ea13004212034103900000e008182544504000c008c00d070300400a0751040181d07640410240d5541c0040a00c000c0398407a403040c15a0301389a0500141c00c2580183d03440010011015142c0b00c412000c601e00e031030085e4040c1030080f1010074107100040140c410142100e02614049055505041542d85c44084425004050050005010030309843c2d03a80c00ea034951070280d007800303101d40d010f0030f1410141907100d10349071500c8103620b10f220800c1d469201e004151440038101c820742d001166540b10b500101c51008150340824004041d0000d40a1003a4901c02c40c8a0b640b101d896064032503091041c0c40d03e031901c40307801d00c1d10030006d6150742e40d000c1c8940517003201d0a80060b00b9030003504200802484290496485c80d810340c0191401d44003201c1c020800c80e482943c209440c1a40e44054070f0b210601410010b0110903960404070b2015601d4110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460629010 1250 460627760 460627781
    0x110a0804121b0f02090601050901090b07290a0605040213090504050a0222050a0504020612041506080a0c05040c080112141603020103180302060a110426060106030618 73
    0x1110818a8810141501c0b4080c1d00031564808140c2d200011400c003988410f801c4074003030900300c1c1049442c2c00003030030a0389035000ea01c170700fa940403406030309001400003000c83c64450100c03000810340700d0085004040b20201c440361070310303070402d500000c150a00e4801c0303844d800c4d04042c3c528600b074240301b20780000e0103015106032454803842c902880942d6419140d0340d01c4034071640081008640d111405001da4030010800217407603244c101040096101e200031a060001003c2c1500c0c075541d5189000c8403c081c2d03480800c03071713903615003140030900c40300000b800c0c0001070183c000c001f03066131b0300c3d000c00c410b40d1101c00c503000c001800500100844041030b00e040100f58407c00303060700000303003c1c00810b2074410708142000e240110160304000b0b55800d4403441c2c1d440394184001294200c1561406560380c400a45550003080d56107a810703074040318517030640d80600549051040d80d0488064401200d00c0301421124080c00760500020f503480c000d2182904440c0c044080c0594411054005001040e0103101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460630260 1250 460629010 460629017
    0xa1104110409020c01020417011107020105030601170708060a090b0618010c061a1206161116170105090a1713090216110f03030910020f0a08090301110a080412 70
    0xc0482d460320140003500d42c00961400041e162031a040942810b00c050203c01c2203141d160200f440000d070324003021104859028200340380d0f65125480100d400080050b03103501e0714a80c03001840f02c4203601c00c07000b45c000d030f0048440e81e42c0b03203481745041ca046803003102046500001c1003090700c07041052440b82c0c1c000944141080c0030071103825100c1c4070940b5900070101c15800141c00d50400d20f4130f0402e60307070000741082c00010100d5240c941c0b1101c1050382204403400a00c015104802c045203001c0184860700e0b0550300002128903981c2080d50100386d511125a1b05d10750034100029644c5000151001000382c002a43c40d20410141f140783c8644ea200c0341c0c8082080420142c0801c19010500007007052000c00095050400b4081c1011000d40b01842c4100780b040d0a003c0038400c80e40c1e4000251041d1550459202035640c05032401079103803004046003041b1074010030240e042480045d601500300c0d83c9064000b804210f6407190803051910a01d10350001052440022401250303215281c030040c44410305 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460631510 1250 460630260 460630267
    0x60114060c10050a06091112060a08010c0809060106020a030f050331060b0a1818050f0307030905030d0804030503070917030c1603020a0b073e030a110411 68
    0x1503181460250041d003240140c880050141072003035846140c0046c0001142049001a142c000500030b00c2503142040742c3c00c1e44103020926036981c00d41c4003801841c002e0002c01c0f581c400400041c060032401c584500580c01a44c000090031400400c1d6032501c5581a0740342000c003042d0350030076181900090144c4602c0000542540164111100e00d00050352541058110798012480d020b02a107115021250040410000c1046003209580c01032044e000c001c1800b10302d0b204151001c801e444900360000d011849510522075110740084003c1c10414025595080f03195100d00030b041d134030422803182ea00014031860019020900ca60b0285800c80385e40d207495003500c0e0341c90034106109808007080d00902d41002a628072601000c100c10890700b9050080ca441151450300007409121140c802c4103800500003621000704000d804028840e8880e00500302440c80d10305001d4031308000b180b20381c01c2103411a000341d100705240015904107107980c0311a40003407840c030101c113100103800072019051445c503050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460632760 1250 460631510 460631527
    0x1020408070311030d030608060714070203010221010603090807031b020a0b0408012927040803040204050106020c0901061b080403060b150c030301060f0c05060f010503011d06011406 80
    0x5020240041d4043c200c140e002c103030b40302e041506103132100c4200414180303041001c2000d06008641c00703030f0220319800c282810352000e4246800c64803034100000c2d8075500c002990280380c83e0b49406554050740c81084190319130b07200c1c8170070350072034609140240c4182002d029020000b8450318480b450030740c100e4103026a0070b10310350100d0003a2051303030000c0c02c4c101808034041c807112109101c0d0010303003804014021720b1503c2c5490141141d031296040c3c90300501c1c0010040c0c40841d03400000d000d8441c2d942000415515084c00e0944c125001601c04234800c500340400007607050300c0058583d08031a030061100314181d1074032a0941d07400c2240700c25000d103407200c256281c0110f58400003400c0254010039001c158092550100008211120011250710b00c007444034200220300002035a0665140d410034800c40808141c0075640c0081003800181507108540401c180c40d5004000b890482e03105a0091000340124a03222a210700b0380901c01c00541e011900401109100814604043c44d01504061414441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460634010 1250 460632760 460632763
    0x10302131d0f061b1c020c070807030b0a0525020f10020403060501050a0608010303030b0d020d030f120216020d1707051b09010612020a090905010f0303120c08130501020408 76
    0xd0607800440c1e421000401500510a000c0c0580c007192001c0480442c042d00320f010b01080c0541607101e8090590703044144942912035044603009030814046803030069031080722aa5880703650008441511140700801c80301e10315402014010344079500c1c040307002d100034140155030510305001001144154041043d8403001803010400c004100f410140c0e0303a90840c20804191032042e8441070180729030340010011140e01031f101906603649442d0125452110200090704043c200f000654801c41540d502400c1540140304404100c116854400944c00d000428100700d005445421110b044400210001440d0903508c00c0c0c00240b02d095000444503074004981201e030000b00e0308945a030f11912004002180c4480d403c16458421605804a90704000c001020340e180f040d5a2801c2d2030300416018407190151400101400340f91000b0001903a4a5010030402080d07444264045840389001100c0d445841c00381c040c103040c154603423241e2900c8003040304c880b02441410075030303071550b0030301001c0740e115230 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460635260 1250 460634010 460634051
    0x204120f020109050604120c0b030714070f02060406170601181415070501150b03091c05070f05010204090b0301020f070b0709090e01090303050a050417131d0a0b0603040b01030213 79
    0x344c074409042c7d640580c80d00d81100c54003038005482c03115041c001c00840a80c8110403072030910003149920b1f180c8141385092140c0d0007400e00c000398070000200303011414a91140c800090740301c00700e5031103000d034a9130001580d030301c1441d892214500003116024800c2c1d40140c0c101800070340300036048009050786484482c5d4183c01420080301e240c3d45545150060312504103544009d0701c0704402203880d50411000a642d44e04c1c00c400b408a08000b680d640184180c080c40541303031081d801804c400314031407142c600700e8000e5206004150250703103440111207940c14144295000c0021030004549002855141c0c4402a0300090500d000c01c00c1d00c1d807021804c4d0300c00f030183d01e00e890403410010440d04071a203401360a64000910528401d844d000030440030a04120418088840e407080c4259225000303501c401411400c2e8109052103040340340c030320a0307100c0000070341da10510244104001c000c84410400400d4842924064110030490006202614042540c4030001881c0e010010710301d02c519010780526074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460636510 1250 460635260 460635269
    0x726071502070509310807030f113009310209030a021003021b21040305060a23045a021513090204120f020109050604 52
    0x40040c8046640401240707010b4103044032201e54910302400255201d40c00d0391150155880c0030308001449140083c50784400b0b82e0000034050ba02c000609001c0c1a516001c0000d0f00064000032649041180c00309550300c850141000b18404d41003110300d0641e00f000304c01c2c044540304508220281480d82d0707100b0007083c0b546004030800700302444112881d101e40c2c2c0380869909001d00410014140e942d021800003511039048a48510401007a0000c400034000e2029000380c000411030045002400054404812803204034080100c40641c11161403600580c400200140d10100c04681c0c61951a0000c100344c0b444903804c40035403101030111814090040d1816200d401c0c00b495143d40c3e14112801d184207014007910080300c1015044052440070030545850f9000b07804045032003a40078954205034400c90b4000304902000c00317241c0400320307141d44605c4103040562210b0f14002440e01c00c40c001d60b4111781904001952110040d00e41c10360225034900d040381000140100400c180c1d81c1c6402410191 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460637760 1250 460636510 460636529
    0x2805160818210d020a080904051530190201080c13060305090d022a0103110a031410081b011106010e070f03150308071401241403072607 60
    0x6602e0201e560401d10711408900442d0407125020000c100e40100711202c8041c02e48001070242c0e500c405010441449403801540072038000c0704c551038640b04d41081480060300c5015600060b000040031940c2e655203030000342c5d481e5440000040550701886076940d02103100800d0924051160000b50f800c050b291b04a4004070355582d060101e0380a00b004000008001400200104081c10754400140100038103190341c08014000e802e04144d2094101c20806003160043d181c0701e01d0000d00182c040d18020312044800c80309540010b80100c0c9210303848c0100d4035010301501d481e050488107850000c110f580d940e41401003807000e00302401000c00000380240b00d80b110200850070b10798001840b85240d00780d000201801c19004a4a0818281c00842100d0b40b000540340d40b80c8061811030091006409a10300ca54604002c1c0c05a6003501320481c2000c05040c001d52640c00e441e488260500c182d09000a50907520000052207811244580718440c0d07202c1c1206290b4030961640410329000c1d15800000f5503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460639010 1250 460637760 460637809
    0x13080f0c0105041209080f0a120e031005070305060603040b010302010818060a0902090108070f0b0304060605031002030a0501210609020f04060b040f080607050313030302040b2805160818 82
    0x3034950061803400a41b11900291480101d40c40b000750703441260180141407650b409102c1c40030f441c010304000a9800002c0c05541e44c0440c2c50b40301c480245021118800403d00b402c0c00554146841c0781100d1246a0024944103543d096400449010200502800c640400010070130307443c0030200445442413207a824080740b1541c00e4814400e5991043c0c0c4034521980c007840c1c0500c01e042000481b8003c2d503025403034a0740c4940c0c9508110000d408280c0c00700c0d07094002d42d030f076203a411030303060300254410303020f405080c00541da80751201d1113640c04907104104254008881180040c0143d00008800c50004000d104010190030009084441d5070b84504010540090204200840700ca4418001d2460f980a44010310304800050124030000b000308601031000e14200c01018080d0f81982c0147c00d1545001d03407102168111401003416114010b541402805480600301c1d1095088034581d0040703400c0507100340380503501c010054000d207840c80d03000c11560b803c215080d102c0802c4002081d4004004608 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460640260 1250 460639010 460639043
    0x120c0c0e040311030315040908190207060201060b0f03011e090213050102011a0f06070512030f01330e030109020405071e090608040b04061b0906020f010513080f0c010504 75
    0x1c50030000f103540d203a00306000704810170200c07964482d00c0e4401076402144051803803406000302d214240b1041c0c3c503803020316100301403a680000e2807016603885070002c00c041a1940d07010784850054100c4002e010804000501420008000401c2c0200c00903041e42d80881d10798255405913001075400c2000c40100c414200700569090086036014140b10000000061039040880c40184070340c504c0a0050f8000681c00007004010072440c01740701c040e0281c0680301d00f404c100e40780c0d810400b031081d0000c0641c0d901062203a00c041000d401460304040c40300c4110041107440039102d219100107440d0340b5561307901d10b56000d078841340610781c801ca4407030b540c402e440361840c043c040c0d981c1c810340d402c42e040009c1d04070180400340d00440c0f5280c1060708a06104116611490f00d0009801d2405100c0a10024a040200045c1c0c00440d0b01065407a0f40e000c3d540d11403091b5103002c0c22204100c400304c180c1c00300c208000010801c00d00081145000080c0160b18001040145500323440c4195030440e18021038000301034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 460641510 1250 460640260 460640267
    0x1d0106080609120403050a080918090106031a10060318350a020c0f040204170703021e030303010b0a09080304031412070f03030507090503070f08060106030e0703120c0c0e0403 77
    0x20f081805841410f08041c1152507660b55500c440f00c0c018a52800054000d00d01e50f11620f86000d88032a41044402c140341c10300425001c2c100501c022542c0005070a180080c0c0701000ba40248100e0812900c03944091901d40200e0140c5001000d004000c400d2043e00400706600840e00c08003000904c0b170180806007900f80041c0d554510212040202d0001d121011016901103800324070404100c40c0b1001e83c440c4000040d0003442294003100c00000300d161003004146002ca02407086900031a00c210500100d60300c1c1003085000d801c0b006034190000c02c010300c81a6051405170680000c980f40c03400c02c80d6290558280b80d684250811713151142ca0f00b03a800c5000030108100400500184041800c0a0741c1d6036821108480c611030040c1815291070010301100e104102c16801410300604452242d56107001105003e1800d00032650ba030f00030140081125030280c080c110703000dd0b800c801044254a1501d6150800421080960402003448044070200d071315481d90300003030002281c560225060130718014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 460642760 1250 460641510 460641523
    0x61f1209050303181623120d03050603160b07050a08030709080f0a081c0f020301120309080703030903030f02010612080c1b0a2304090f14030f0d1d0106080609 70
    0x14502c0d031311420607110259491280c210482e0111101b45604006d840f4140f80783e8881c0d20300440d08010b141048510105000510b26401052503c04000b642ca8a03024035440b10105500c0c2c1e200c1e80c4a40208002c1034000030002c180c2c2038040c00c162035420703035280ea030b503007580c0d205803000800580700c040d0a109007013007445006040c00c41d80d4018203200c1900d50b1440000c0c0150140c58043c840e8017081e011503688590050080c0f140c030324004550300e42c1c64105600e60b14101a0095000544210011429480008028040c0c2c2d8261711481032403840d40ea0201c17180d40c80c00005c48219520f031940012009981410b445950307115941c0c4c0c58403121007051040c500280d9152445408840c484116280e0700c0b800540ba0a8424005981d4070407035a043d501882e55a1240000d6045880c0112007800e21100d8618040f80d24032800b04145041c051942e0a9900d000740f040071a241710301002030100c4600541e2001c00e1000380c40d40a000034005a000f8282101d80d41c0c0e03c11140c5400c414200000c815091044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 460644010 1250 460642760 460642801
    0x519140105090f031b1f080601050702130c030c180305061f08060906010312023405090f0402030f0a0b0a18150c0906110705060c150c070303060b03061f1209050303 72
    0x4664845000340002440c00002230100c0c0e050180c00a000010342d2910020340320740400003041800076000e002001001081280140000582290307085240c140c20001402c04898000c00105400d413294072081480e0700c3c05019a90186c0c0580e41c00080f041004e01c0418441c0c1480c0c400b50007a5895030400c0ba000310308002c460310440d080b42010311507500320f20700b144100010b0050071664070703c0150f030700388451070980e00314a42c04541c2c1c104204c0c0a0416510f404e10a80c4283d05446049006e040016a114521100288510466000102c010b006540a0800203c400c030a009550502d82c4690b01d400550001120100d81c403030218101454112060078000d201c50324050705004109211182c4070f80380d6008803440b42100080503605600208140415046040403c1905007803003080380d4025840120b049020078107200c000541c1050081c11380e485500040c040304800c0c0040119480344000c901822000e0004480166600320142c0c8504615113200c2c0d801180d072030800240c0801c802111005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 460645260 1250 460644010 460644049
    0x20a0e0f0117060a0b0c0708010b040501120305070804030f050607020606190e2502070f0503160b0d060e1305070e090a0b1504090305040519140105090f031b 69
    0x244a1035990b03000d0300250001c810030041c2d80d00c0b600c503070001918002441e03000c000782c5a0045401d030381c10030001c034400b81210010402040040404810f0105684013486420403003504540c148012034042c2004181c04e0344036a191a01c0d160f1039507076070500043c0a86003558503501c04801c00c0082501044800c1d0031960845400219006c040c0c0382d01d02c60516805290030403902d140c045070b03111400c00b4200360412015001c007014866006c1c8001d60301c9540b807103095042000c200c80094a801c02140380034182c2c00e01040c03054203500b0310200307800c65840011001d1550f5034a1200044004002e04140e0098946400307460200d4540c0c00c000e40390182c0f541242d1402c5003c0300c2030100081d0001103c001ea180e01c240618815901d0714501c541c000d071615400c1c0d03001414541e4020405a106000304181c0d003040310070022030a042000b1071010b050f00d005461b040315080c1c503140303407560244000d000100c0e4000c003030040340e03506000464144107900c00e800340d803103d00d4a0707405c920f49440051804030001944 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 460646510 1250 460645260 460645279
    0xd270b0d0b0d120f05040512031306090e0604020705030913060f05092205070f180507030c0c031d06040f030605060d0f12121d07060905010801030b0717010801020a0e 73
    0x443d840c00242000342c02c1000c0c05010650452014081d130309503801010010117032807a088014000e15140d070f00015031885855202540030070345602820740b40041e110249510010740d501c0e1018480290710003034007a220b9200030b03c0740940b903a0b104030300c203c0c840d04965004500c0781c0c94003140801400701c41e000184100152001c00a0701034512503010803114100e207806c3c1220b40e1034201281060801c0d001003854809180001ca104949a12101112904408100701550342c0340011011900852020000607a0020200c0301103480b5071600e00c0d011130088900b0100000c498000b415640c010342c44200c000711544400c1003032140920423142c3c4460140c6080410320403594403c00d25500c0008010185e001c0e43c02c03400981403003204481803074041c0c0c80b0104801e1403080480b6048001001c0035040ea480343c00070100300b461140c0c02c05421640180c55540a507400c0da500c1d1923200100074100313010008019000410899001c020743c0c024480d400005aa803031072040010504842442118000d03070320301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 460647760 1250 460646510 460646513
    0x310051023030a0902030a140613050607080a180f060b010e0607120912030507020f06090a090f0f060605040602010f0203010e060f041415120601080d270b0d0b0d 71
    0x44541d2460780446031050380c0d0f80e48030794410004100140c1c010f5050720a0b00622820414220f801785140c080c9071045640c2507441016603102d1020454009150f034111001103220a0301880410303030042d00070381000c02c0c50401e2102031014451070000c2518440000544a030a0058a01c24a90711190031300c2c0c800e031320752000070100e078481c8610751380240280f8030481e910038500d10425404007c0e00703062612600074489424010300a40110380141d2203081d0001c0c481c3c0407454040115645042c1c05030510780c0c00e9141c02504030003492441c03407070aa827a490f50341e40280c0045910858002e000740b80c94140d15581045c00080c2100e52055006e0b9803a03204000501c440201c07246640e40c094004c603040310000d801080814068290202c40d21100c02020741440907600044803c400242000e07200340d02904030109100743d4500c800c1c0714910064110f07507421300100744540c490344441c211482c9514081c0401c01464015002268808100740c00040f4114041c460240600d449082e000c81c0d195011002c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 460649010 1250 460647760 460647797
    0xc090f0b03010509070f05071a152e020c0a030302210301060e0607030203070b0a0f0b0402030f040f02060415021f1505062d070b06190e07050f03100510 67
    0x3820100500c1100010211ba0a2003030b02200c01a41e4000c1126800b6180c5241801c0040000c1c1e5014401f04a500c0350080e95091102c42c03602120308681c0c0c007500441d241d81c40b560190036401882402c6002e8540d140d003658441203c1000210301c00d82c0203202d21404805100300d99040d9441442d03203203800700010004181c0c8a50003d90b42d01c1d040315420755480a51906918500c1135100080500c404442084001c55455100c610f50512030401802545c040b10300300800c13440111001c01c4009110303004035012480b964100b50100e071019080354a40ba8807502d6100b184100000403e00603130040c80f030380341500c0d2644070b82044032032a4141800400c402c5a0451241c4407030740103040c041c6502040408082c00040c0443e86000c0c1c84c903428207500c90f200101c0104581c03044c0340a980e0360000d0700200301581050208150350812000c0c0d040c1d030752030921544030880b900242c40002000003d020000150019400a60055100c08111000b00b89410305011300c0803400700c0140240928003088817013b108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 460650260 1250 460649010 460649029
    0x12091b010f120c21090501060b0a0c12111509010621030e01120e07080d11150703110406020a170f0a080402030109080406180e1e0702010f0c090f0b030105 68
    0x2102181041d2001011644c143c2c682c50040300c201140c3c2c408058a80c1076911003508a400f4400a201450321640740a5891140303112070400544001032103004500000c0c00d00800b00c10620708145815200201c1a241003020003003050f000500405101260b0824410100140982000c0e042c0320200d00f0082510004607510240521000300d64103146030b849942c51500f02c0801082c03c00c001001c0c1c0210740e0707944889001d808405d01c00d0030450490b42d4003032800013aa54030b445004050b9540c11f40c0c00b44410000281c114000d158076021000c85004480000d00041c04242d03004100d42042414003104c1c0b90200c45600354984802c11a04458042d403104494031146d05062406907a11b41e80b000c20700601d02c03a400a44100c0b80490080b8a090b400515510242140303012081c1d400d803030b0103d100423642c00340c4a403d00e054801c6224501603006859032035110805000001c0d40304601d100c90070a890007440c5020000d6200325081c4561a8121703031800203030000c080d400e070131503040c003010415480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 460651510 1250 460650260 460650287
    0xb0c1c08060f01031518060b0403020a03032a1109240f0f150a1d06040e040809040606091d060a050607081e0304021219020f0612091b010f 61
    0x402d0768448146036402500040c0e84240440c0007843c4095803140c185002c507846812410016083c803c00060510741d440545007034a03001840340508506d1070390103403840f4103041600768000c40d83c04048200003a00c4d07104424041e00410584990400c0340082190251001f4540200804661545c00d02c4c9506005c9500700024280c0c3c000e2820070313044000031a604c03000c035107295010100c1b140c040d2032442c009010341000710040d180c000055200c01c14a003500f6801080e19900401d0074402001080d52071413505400c1401801440c1c03518500601007001d403412a0403010118001d98030811405072a401940040700301000d40c0001401c1c060000340000318140703e0b43c1d2060344c1c040742910601001c0801c485209040051012a19480c0d070181507140d0800c030707012f900c52040c010703164031001004103400d501d421004c5101c0406111aa00300320844000204040d00504140180124100a06050f5000c0c2c002e440c001c2040015142c51804003c0f40002114100007408000c0f02925800c0203040c4043c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 460652760 1250 460651510 460651519
    0x1103070e060307020c0d0501060501030506030706210207020303071208101206090203030c070e0403021c020c1509030a03120e0c011b0609060603080a110318130608070b0c1c0806 78
    0x3601c400d00100c1c84c00c00300e174015aa00c001940701c0b05c010400d0541c0308804440d02a281444503594a2003016258811482030320045035803001c0d584aa0002c1401c00e80501c1e000100c014180300c001d0b00130a10b1504103800440307405c01e25005850000b13811401031540b10103420781c140002814003a0009008112080041c0142d484401400842d5000d00070b441031003000c0340450354400e0b030b640080b40103076005440540c054002c00385035a00d11410410403002c801c4198004020071000402804407511500034003000c1007000744510301c6c80740c1c0c1c20b001026800c0c1c000e5440c0d55401d92500701c4401107980313901e02d25841f03070b11040c3d040e00f0907600026403000340c1c07030003081001103181c0c94106800581400030001f4015450008040204800b0801074401742c01c99940705503602d0311038583c0c1d80e92442003d0440512082c0911421708515001c213003044121003811022407041d664400f100d01d8071031070b81c000d1b1200700c0010581903a0141d0410034210307200c03104200300c0108030045070060500035000e00501e025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 460654010 1250 460652760 460652767
    0x522290c1207060609050f0a180c060e19090e010f0c020607081b031e0603151302030f060a020408150c070605041e1124090103050702150c07061103070e06 68
    0x5000f01644490014456440300f40007900d44582c5000010604031082c221091901c00b503030440d0070040c46030001040c1c0c090344203501581050b105031072500d0840225a40a0301c80d664007610320705a20321150041c0f4002e0000f240003440405d03901d094428200c1007d40c258074100c58050844d9000640c01c3d009925401c0c000100e4645807007071200100c035181e011024480000501080b00070031518211007032250309a80d40140c84000405445007542c0180d14100b0000401250094101c840c94158052004040b62100800081c041c0c0c1001c10450703981409a5000c20100a01c1c0003e12400f5400c140da0480b00e651458000314141d80e600405001070080d503502d40c0090100301e200f82505c60144e0041d0004d2120003091b290082c0c4280c9050b041d140030743c0d00c4554078040c02d124200c40c0d007136840f50301c10260700b0603d4580c011030003000b0081c010001c40c0704d040c50844d000e050700000c0341e018003c40054a507580c40c2600740202600d250300c1440d0300403101042005865980031130400309101f0225032040c0c6c1e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 460655260 1250 460654010 460654013
    0xc0210050c070807080d080604090209010b0904021b010b150c150a0f050f0105040e030412020910150810060e031c12021308100501060f0522290c1207 66
    0x1401070b080e00f14141a10a01a0104150000180300741240860ba99402c141c1c0e0b5546d03041c042031b2040d03400003c0d0003209040050002042d001d02400140402520050a100d06010065192210b0b41002c0d4001d956549020005003000c2004c80021801d4128a41c40c01e000b9404040d5160001c40c0e104120f80260030120780f6820f01502302d5440065196024401c1c2c2c02c00c0e2107074500a000030320072035200760315000c030742403c0d0f103c08000c0d103040759107400244e10046140d07002c1c000703805802494402c410040c0f11010440c070403042c42c940b030150000e649500140c41c1010a100c0b054010f41c00c22000d201c030112111031f8694000400c8a080820010450080300a0324015110340e140c00c02c40d00450760012a01e80c0c07401a0801c41c3c40111101082195461505155101c0031a03200f80501c100041c034426524072083d014030018811007004145007842c00642c0041c0003240100c5403c852407250080d2021074524540b500008400c0c1404429603203040c0b6090b4005645020031040400e400201180e00300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 460656510 1250 460655260 460655263
    0x90b0105040909060507020d0e0a140a091d01050f0402100e03010e0d02032106090705071403071a09150105011d03060c09030f0d080a050a090f03050a0e010c0210050c 73
    0x8000b08a280e40038440d0b03008902d0801c2c040d140c125401d900610544100720300141c41840c542e00551800b5143c81c41b0a0304280d044a4040802000c40790051904000002d0b04200c6100300c0745120405602c3c1e5400300c2c16041841d0a50724007a00c0351440100030310038000561b40d0460f60307960880071820000c000030780100109014044540c41040ea90182c003000200050700032000301080e1446102c0301e010001072440401c032144054403400d401c414504002261540150b00400c2d040e4080d045101390a0400c0754a9890741c0c3c4120703000ca80c081150003241800560810740d0b1900032034940d000e0400351074040025500c00c2030501c515410040028566a40d0780d00010394410484c1c1c0180c1540d00f103140c1503140304e41d1540130b142d409000344034110145800c0c400209032050036940c65680e41c82ca549030a810180a04000f81200400c5070b902ca4071140001c0748100d11107403107403198403a00c0d291052000080c045e00f5070018281d041c05154010382c00183d031100c20124400103542020b5440701c00034060300307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 460657760 1250 460656510 460656517
    0x18020f040603390809160e010602100212070302070203150408041a0c0604110604030c12051e06060d0c05090f10090204030b04060e0f0303011d160c0b04061e05061f020601090b0105 79
    0x1400703221150100400e8200f0002c021234140c0318035400b11842642c1c040e90101c120f200e103001c4281c6651504000c110100d110b500100025070004080321064900ca55614801c1d201c00d460071180b1440010f401c210071120f9001041c02558030036101403d0655031341c8165100d690041c00108207003950700d13a154999603110142e8000d0f60b08050541704140d00c0303419440201c03504a10a545a104640785010307100d011600030000b0b100054003419185c0c540c10180b114810002e502281c180f03051b82400300301919480283e512640025035541c2050500440354144559243c010b130041d10700401051001c941c1d502d98054000d61f00500015070034403240304290816502c55003200c060700001000080840308022000b040e920b11b00b61040c0580c50f4001c4014141c03130400680c0c808902403d5640012401400c4082d0b84240501c20100d41401040503c01c1c0d0003102c41c1074104400d580304103008050804000141d1351101004000803a40180d5a0203543e50105100b140b40c09511001e0784c41c07540e4424011f0b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 460659010 1250 460657760 460657783
    0xa050402210a020f040b01020d0e0102010914010c201905030c060f1504090f02280b0d0f0614060a0905100c020306160918020f040603390809 62
    0x30445409281051261140446070050380303d03510704d402e410040d00d480e02c1084c5280718160010302c9041c0082800340c0c1c400045180ca039040d9560f0740c000d0404202820300303203414030704220f000003440d429503100a44100d00704652501e130741c65108110180303128006140412544443e04c903c091f0000d030701e0901c3c03840c030a07152061001d0040802740003c060070003202c40d004c0d1000342e2440d007020001000744421981071520140c201004048031f480075042c035000018410600010858254441080103645910982d01040c440c0d14005000c25031542c035440f98002030414120280595440c21003c4000000011400b42c451341000840e42e480c18010064140104005003035210f941020f000090588400600c069000e4000c070b000003100345004141081c1324060585440032490304151024850482e1010804491a800c00400c85100340200c081d00082c8125074002c0f0b100d0326050141d560880c48d403001c21608403103c2c10010b1006901034240c1c0d021300034910381442e8556400c4001d91820304141076 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 460660260 1250 460659010 460659049
    0xa050c070b0706050f0108010b0619050d1406010f0203030603030406200106060e10020307051c02010902130501170703030f050a05040315051b070f06050603030c061612140a050402 79
    0x102e103800c004064000e24811610312905000d00ea03a6890030a00341c4050b618410b0740601c007008070b140d01507880a44001d03122050b14082d07003462010a580c0044800d02500410810302403020002250b034070044101d418941c0e480551304509001d00407a50700c0c01a4003600342442480800f20351110700d1083c0d640d80d0303032040000074488180d079804054030f1518403628060141c83c0c00304651031503a0001088407080759001c00201107402c0f0a030054920107004a1030001103541f01c6c65480090b031b13215410450f885828100c0016103514280c1c000d84440c10010304081503801801d01003010941125442c0c2d1001003d05100d50365036a00d0500300d400d803245400080c400224003003802c818032826807240344221b051701ca910505e116507004001d5503000302c035401002d2040c010203200000d100b54214613080300b4041c003180d041c1a0126040e80c00c01c4000c0310354a034904000d080413600c0c00c3c0d00c00f459420b900c0009038100003081004460840e00e64008001c10708041e16500803400f19190003d8604610b100d180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 460661510 1250 460660260 460660267
    0x100c0512070314030702061801020c0d0e0f0a0b0703050310050d1a100b0f070203010e011d060105060301030c150c06020a11010b0402090d02010f0507050a030905031c02030a050c070b 80
    0x5940e109260003044058000400c00c094903007103000840300f00ca0003000310381c00418403a900e00c0c11a001e005921044031940355028000c1041d948001c00c0302c5864080a40c41e42880c0c045c17400c0610100b02c64014245209005080d800c1100c04540000c03150705941625190b83da035580c02081d41d00c00416a0301250701f0501f0340030f0500034400b1140c40070f40d049906c141d110640b52669641540f01c41d99a01600302e00d010200005506c44000c1d200a00a10b0702c042c0000c2520000403d400f404c486d9122907607001403001c4500c0070485c0d101409400d001d40710455600382194119240e00340c59540d00e004050361403000040e40c07044203000707840304003a00b680702d10259941c0b031581030001d1200f103a2822000a170b6090040300989481c1c14020f80d04200300c043c0094514079215001101c000c01c64030300902c01d000042007040085103061001043c0c41d0702a4560824441c0340000b03140c038181c2030789400040901c5c0c0b202da0b44156540030084035181c51040ca03009480d400200c1c8030b14201449503000780c51454001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 460662760 1250 460661510 460661533
    0x201140903060114040c11061306060b0d021b070b030f2a0a0e030106080d0e130207110f180f1f03061506020a11100306051e04050610080402100c05 65
    0x31351164080906503000c0c0810300002c02c0556401c0101d080810a42d007181c4006801c40041d0300701c8040b214051030340070030803660702c4010b03044a03489008a101c1683c1c001887c2c1000316010070861601c824041c000b0001c81c0e1800180415901019114202090304c1c0b1001c101400c0104030040581c55034102003c2000c5110050150650302c204141c201007103032030741004a289810710408003129a031102400c249540d0010844040350f0302061240d1100f000380100120840c170344081c10079941725000c2041d0460540003008a0824103041c081e10030b0a0450b220341114006040f180c1c0c010001c40c00514654850300780604e041215100b0503803d41200003030010034412240c00c8005841102c1d031507803606603195541281c95642620002d40396040d00c880c040d146041c041c40480b1800c9407860005500c5480d00c0000f030f07200d0b020880340a0401c184035040b058602d071510886070818001c640403003000a80d801c009d0f090840003040a40300d0300c4000ca5299a00e4014110311034480c0e8454140c44110740607 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 460664010 1250 460662760 460662779
    0x402030a0e060129030a020c030301062c1e0307080a150509030702010f05280c0b01050a14040504050109120f02070b03010e13020a03060c03020403020114030403080402011409030601 80
    0x9010076080203101d180000a1503864182d100c081c8151010090004200e45101079403c1d54070151034405225030030809a403c104040c4003075070181c90306580701d0100c2810200c3c40c45d00d02c6d00280c8215481e607868980e0101c50b40e03c828801c86022880421415040f0760303c00001e00781091035020400e24000c0a032032400708aa0042081488004400100304a49414442d0750380d90280f204024003090001030030f0007910307020340090510752104d50944801403400b101d41c00203101c803017040c07030000c0784000c0300c940108010550001e000d0700040d11500d15940c58180700203040b000b4400c030b19000e035a0399400309081c0003003900060551a04030300c0922a031011080c0041642c402c11442d4001406440b1010950213a400100e07070403104242003c5030b464903180d64041e602001c0410032648902d58490010004809000d016003035403003a00d0058465246000151003540c800c8150070411004100b088002500100641d4000e40c0a2a12050030701101c0c20f00c4801c0d10865088039031512800000242d05401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 460665260 1250 460664010 460664021
    0x604180f0216061d03030619051816030b031908040b031003020a12030c1e0c08011e02040e0106051303051504120c200109090f090323041a090402030a 66
    0x4940020819060740c003c0a428005255a04e000c083e001000403a949141152100600e070210350ba1072106107569100041c2c110014040311301c04c0095403410880a45030713030100b89036203000d242010700274954003400003900d8844030703d09038001c404d81d0a6207406001441c01941c001d0001001640d5070380c1000c40c1c0a41850300548422031140100c81c0c000300f54603a140b50044006503140d22041d61501e0240d89520031444030422004610403041213160100e00d6019100b0010300d41080009a500c07507403404000c0f80f01d0350a0700c2e5240180100003c0025164040b0003904441042c508261210030200f001032084400c0c0d030016003a80704042c14942d10741d40d04500e0314020b505c1404d406800314040070302901d0080c00c21401400d103004d400320840b8a00c1c2c02c0d040420762180c1c1454580c81e20740d00c510040d01150302c02c03000240b0340c648c0d81d12203004240e0004803c0d00c034200200d950005102070706070841c60a10480c0200340c0195401c20316048040604015189500070041042d51a440c00390401402480e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 460666510 1250 460665260 460665263
    0x60603150604030f02150423130c09031103070302061b0a0c03050706020105060a15080603010e0706020a05060a150b0901020309060304060f0b040209030309011b0c060807030e0303060604180f0216 86
    0x406d002c0c80754141c5c09158120f6045495854459000000c402100c000c0800040c4449403c9403504413820603a44030351160b51185650740c0c9541240318194104409141ca400800b14025032201c0d00030b0000da501d250544402011341d00040c01c0c0b2601050986051290f6031100030003000c035905012080041c041340b0030040d500702c1d81c0200160b603504002c004074421b5500c90a411130f690103030403e044900c103075101a41300324090000301b0001800a4280d00e841982e5100c0e000681085c1c81c02000c20205004c40390304200d00181c28032402140300781c00260f1079241d01c108082e003100003e040d400360f40280284c0350701d0300f402800c664581c6094200003002d8154240318840d0546040311182061074207200703440700350401400440c10304050720b00550b5050041d500102d00040d01640c0c00001810420010025290310341d10250b06040c402405819602544e00d45100c942060003000815211003003641e0407a0061110b010507281000034400042110310510144640002030040e0054229030200752541e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 460667760 1250 460666510 460666519
    0x705070f2d0501050c030c04050f03011d010e01060b090a060807020f1c120c0e10030f110406120207050a0f02180a060f08070503061b0d02030a09020f0414060603150604030f02 77
    0x45d9511170441d8180c0c8411200700c07488000c00d10040c4010b05040180061044018000043c4120780240d441d848114402c454030385a0344943c018048807a00b800b40718000c06143c5a10b60070801040c2c00240040b449000301c008101c00c100000c0e03446803081124541d886245415281c5480a411124410040000b02c000c00720381e410460f840c504001c0c0c401d0340c61440c042d65a00c089248944108110340481e240c9203001c164483c00c401007553f4003841481b07d080c5001c007089941380d02c1d00c54068000440702204490080c0706018180110342c010075050646a8030004540d21060340f1300c0000c4440942c07001c04003c004020b010024007011941c00702c400c0c1d500c9180c40b190029602e104c1d003a0307904010300075250541c020300003160b200c1004003820401c40301121882d40c10308420059050480c3c00c11501422030945034200030080d820810120000300a00f0398007800301c0c01e41d840110706040707000b91065000d480c002000074165001884140000d480007001550b03038a030390f403c1200c5441680070050340b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 460669010 1250 460667760 460667771
    0x901090e0a0b0921070b070f030603140d020d0503010b0409090201030e0d020f100917030c070816021903031d011808061e090a030507030909020a05030405010507080705070f2d0501 79
    0x10545413013510219503100c110750b200c0d581c401c04212031000040b000042499210040400022040e02e4401858102900208030720180c0500003464034445c061083d040c00020401803000c03400310800c540c01c0d035254540116211205100481c01041450b1003141140980443c3d422801d50219582d5050300507101124003405c0c0e2514032802725214008000c203034624501d401c680c0040c900f0040c2d6480710f0f50035182d40c1000b00c80e4882c644030b540a00707511142e464800e0340e035201314505502c600926264602a0f10032003402c50381c002e41080c411a4119001002c1544140c080b6807103004241e440030100141c11051580e1603a585903900790984c5d84040030808510310a410b0140d25540d07a100e10519001072404040684041d201a40b11030826020402d03034817808507840c031a0b1300050a08111a90700c166491400d42081070031903501610302f4080207048410b0061050f8000c0940c1e0a00b6044000700801106524000d0303421100c076281c99100f5030318038481421041c45d140c0849090b5010344000c0c4071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 460670260 1250 460669010 460669063
    0x519060b09040615050703030902030a021f02061006090618150c110906221401060818010905030d0b040906110310080a080a03020715090809040c030b0901090e0a0b09 73
    0x48131400245075400190042c0907510200c1d00c2600460040e6002038181e034420119030300840c0f100e00409000700d00952452200ba40b42d07941c1007054170360110302c0c0d1000d2040306051240090041105109840070003091000c03401d84141050b50010003054a2883c1701c09048804034081c010860181003550800214005003041d418951207075881901d000b09a0b1903902800b10b000c041d40c4017203284441c8015a58000a8000f607042c81009002e00040d80780c400191030121408401d1140e940106100c03a4140f000d00000100c00009586881c001110003141700340030600414014060440040c11040c1410402c1001e101c1d024002c0d4050004801ea20440b952510929540c4241c880787c024010403040200f40c03000362290780238103007885c4202c1711804146006640c2000355484c0840c182ca64803400103038142c05103000e102e03000b401c0000d41070520521509600103004100c052160301e4280da1519000e46400354280070410740d990340038040c4416400e102c507400d50703200040181c00d42c000403686039004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 460671510 1250 460670260 460670279
    0x602070906030b01091e090501093807110709020a110303070f0c060209030610050406080c0306240a0b030103110105030402211603060e0c01050c100519060b090406 72
    0x1000d42c0d812154120559103040c02900007403060b01154024080340340400a08564103003c0c01e50f00901031400800c0325091410017401e68000d01e400306210407072618442c80444d00c0c2404048150888034260b080903039800c5e03c02d9401c03080040c8508000d0149a0b004035031221300e503015104001c1c15903030b9070503854040084541c0d60321040d030380c07480400c2c036003104644176a104810040310144203103400b5050400410106e4a0060151206850f03110300000c103119a040506c1003600070840030340200141d40000002c80e031610b901821088140e89071490310301c00040703040201007016001410b150401c51ba616258500c6820a000440300665280d000403602d40c401c6c0309032170043d60000c00444034241031186401100141c59044005802016442d861465041d0300650065008140c00318000d889602c3d00c90920070080c0e4128140301041c882900e40c03540c0050131035145c2401400000302c9031a1202c84003600643c81e103507402d10070304104000c9001c04c2d02d40043c007000360342030750700f4000f040e107902105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 460672760 1250 460671510 460671521
    0x60604270803190b0607200618030f03130b0904060b042402070e0a02070f140c1206040323040e130b061005030a0f0f0f020703080705090303041a09041506020709 71
    0x1698080014400400840c0c02d5403d00c40225551101d604a44011f1201003105900441c0d092210b050361a94410300030305051042054009401d4055441c04070b010303007911991b10b03541c0190050042c003c200c8880589955014030083d0007160051612540d1342c400b00c50189a801c482d007110b01e4142441d00c075a8500010350384083d1100108042500c2d40c030400303c140203404c10b2000b44c803407940c441c00000104140c80c400c1c0c013065100c01c0140c903000c1c01c03000520000581d1900c0c000456070181c010000803a901481c1e004d6026015400800c040c52005800300c00c501598212103c3c2c00380040078400c82c02170800300b00030594800c68091041c3c1e505c08003080207d048024415000c20b04c10000215801450382c03001c103550000b101d00044001c5844100030880360001612101260f002070300d18185071300329280c0ea0380b00d0140c0c540701c0d10b81100f86012a07120300844c40340040c1c00003d13402c1103c412001c581910710006002c1e00400c1990400e80340d02c4201c06180c80741c3c4d809400751010218446099020780f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 460674010 1250 460672760 460672781
    0xf0210080708161709031305030703020a09050705070c29280203040810090b0c0403110d020d140105040c0503010204121b0b031501020c0d030206060427080319 70
    0x5460040d501c5454140910380074154040411016a08048584580c03c004d0350169240340001d6460300d00e5000c84582c0380700907401141c826486000700700016950a28414152040008042160b440b6a842621035000d1240000c100c52070480d40420980600c00e6030340864801b04901c4029030101440301200c621811104542c1c0f00201a10110544591210420244003901c1120724040e60344200a051000d1003d000303144d281c84601b64001d00075181a0103400100c01c414480c034240c44e641d05c14541044808030140524400c6407150117550300c0040d03e000c05a000443c0b10009041e5900e040d00805088804030780024180741c02141e981414400d50701a189000d18003243c02c1c0c7c00d078480b030307544d1444807240703c60410b0190004100c1c24410000380d80504040c068100e0013102a90029080007069103001c1e02603491050f20b4800700b0303400110150400030070303507001918031484503212a82d8070690b016080c03500940702a20040005290041d8482d901000c5481092080e413406242030f240c40c0c03241b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 460675260 1250 460674010 460674017
    0x6050609010e040f030909020a03020304150204120f05100f0c110c03100f110705070609140a090c0e060a090501090e0c0f03071e0c02030610031511090402070f02100807 74
    0xc0c0010b0710030b84845400d54006e040032a402c0c0c0e5580654016a07000c1100540040c1c4c000c8180420400050303051140212640300a60502d400e0003044c808401c42500c018208191101400060080a01203502090300038142401a5006a039842000d80301c1190340c40e000508901070310200041c0070405030354516006014082001404110f18003818524400085880c0d5480c02c00c00440e9444000300080c920480281107428500300c4003074a00c0c07170141e20100b103030b0b080b50b0800d600d01e41e02c0c12046420b0301d5120381d000940484600040701c01005900b4199080903000580c40200c07900091020201c0f0000d80c0c07040b0f00b242c2c50700a16800164152000091400107011162401da1041d000e10b610100a15210391002401c10741034804034004044903001c00d816200403070039402c060000035404201d031000741e55000c4c603541e1440f118905007424590695596080c4681c03452000044480b2107000030419901e40c002c0f406c282548502444080740702d04540075503ea585400b621006210709642d44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 460676510 1250 460675260 460675289
    0xe090f0705070812070c12030c050d0903050d110d0f0209090c0919030318090504030c060203060a0302060708040906081f11070f0506090c030c090c07140a0b040605060901 75
    0x606803001d400c0a2400c80e03500c0c506104c8003c00c1e00c0061016403094085a4403002c10b0806410022941414030810a0400d4242402201290f4001c42104c880030840000020526403500b021556030040b05000d6000c0e5007061780f189130080950000c0c0c00d00c034000a00400400c0c0310300b4a540308a01c81d6001e00e980141c109070000e078103400c414010309071400380649444d40d080344888420517182c2a5410841c04504100c11525441610000300c42c040c01640d0420840360030181c030098546210401c000703156680000000e501901d86034009001150301400c121b0300c0b81c480b4a024401c0c4c2d0468012040364a00d44080012111400501c0500910400c07a0414426201c10a0800502004001d0054840c1e04111600004000115070a02c0e240600c0203082d082c108001000d081c80d1010380902e1184d8032280082ca21a6900004a07030442e05102c0382c2d956906443c58a00c0041d80100310361007150260030501c900f44000145890300c1075204410410155036030b1400c00400d00000e00034083c4201003d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 460677760 1250 460676510 460676521
    0x403020d080906040f1d0f06031c030e121209070f0e060103110703020607020c0a0f060e1c0b040605060405010b090402071a16090b070503031f030f03030605010e090f 73
    0x140050a030790102400052404d5118210082d45c5161030380710540001001c02802d0703150384d81c8007405800c9151001c10f95080e060141c0001c0e907865100200b0720030b8902501c4c410300700c03501070b07440780300610450416604901144500c1c0c1410780c02442081842028000c00102004408141542940c19000d01506010b003800c43c50504054010140fa0616988040e500300c1c1100c1440944105486580180642d152154000b420507140341d04071030145903080c03000c0c81b600d00c10b132005200380c036401e03d03000d482d0485034030003c0d07410320a46a1030b04034481030740910410302c000070711158405c0740505800c1c00036403910800d00c011030b602445101000a024000984070346001c0d0020214a03000707405403080100400060603030181c042e110b824441c0340841442a04581091500e00103108055480d070a01450f03803031b000d031640300c0100200b840c8005801103805450050140d5400384d41c0000031011a06c03164034014009001074044c05001c81c1c0c15400783c0b40c031440c1064a442c4200b242e0402d03000c09843d01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 460679010 1250 460677760 460677773
    0xf0d02031c090203060a021b01060810090204140906012102030d1b2102010c05030610080c130929010c080f040302060309062205060402010f030207052d030403020d 72
    0x80d62075040740d807101001c8001d0b079010040540590601036006136190100c01d144502d41c44540c250766180c1c1d04104003003088484c0031400a2a4050444000c140203403a4070000d0010314a600c19130308100b490301e0500041400010b800c1d816920b2900a081d4401d0f00400c1c0000312918081c4c0007135040c2c1c040c00c00b06c640c5e14450704c0c0c0807181551400800c00741802ca59512050301010f849042045004440c2003140300d07909000b644051070030b030308200d465800e10402142000002c6001d8400303104505020640c3c1d1000c0404580401c2d256104c00850329465030600300180041c031024203030b8001c00b080d024804000b60300700103103200416107686d590f00c000366075541040e0b007143c484424503d4040c000040540c491000031480742c00440302401061908030001c3c1001d2004000c601c8144c0210002c5800080300058040e4000760242444005000510412000307071048040040c45409683d00c2c0e80707190801e21000300b105038603010340b0810070401c514000307540380110f05c0040d61190701c1104103004200c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 460680260 1250 460679010 460679047
    0x30103080912071a130e040501150911180a0513200a0210110c010608010e010c0503061503040609020a1403060601050f090d06090b0103030c0309080c0a06030f090c06110f0d0203 78
    0x540203c2040051b0b071360401345010b1502124181e82c03e9441303a0140401d07034822030b0a04054480c84c00100040f90f4544500800d500500040060358092620a400365548080f4020028039004007808601401c03107130400041c1c41c0c2c0e07110030120101078490311040001d481c0240c0b8945900c3c0d81c01000d00440c081d03d010003908a121004070981410016541111003e00900303020701040c80000c2440d07102c0c100c0c5036084135040702c2c40604202040c01481115500d0000510051381d2251000c0e4580e100c9040a07001065117520003517019124880001baa403540004001e414a0101d0a03241e0541d580c00c010769482c4224920b02102400c100503c41481c80d00d004203c01c642d01480e00015096050382d0f80194008080c0c0056012030303401015442059488107900c0d000d070900102400000d0b40210100d0751400c500d000f0301c428903444140107211081107134031480343d880c0c20142d01c14429a0703424002c1d0000f40300c030610142ca0301800071180c10f070310400110a00030a100c3d500551500c8d2502c0001c4030001c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 460681510 1250 460680260 460680277
    0x203040204240602060606040302010207060f0210150311030c10030e0a05060f0f0112020112050c0d0c0504150801030f08030408071202031908041106030907050402030103080912071a 80
    0x6585030b01c0601e2a06031064103241d400340c0c0082c54000c036030924001929203c0000d1000348120020801400140d9020410700c049800310f040284514600d21801c4c0c0c1031610300c0007112030071481d20090120000c0d0820b50076045031300501081009801490615441d00d1203601c03e50341115524104502ca01c3c4280e2041c2251138000e8140d9080400e01c3d502c00d400e00ca8240e601c1c0703059182c0c400600c9030500f00001500d0040c80505006c1c22102581d81c006820602c0c003a007413108003560307803000800d81c0b0f0b03c1c041100d0403900c4101d020003043c2407051028005030006c2c003a50b100100d001c4000c0d024035025000302c0741600d42104210b01030b12107a55130401e0a6100030021160304409200140010700030b1500d0b0341c3e24140d2600a0343d200e04c403843c4910000c1001c484000e0030020000203003c04180c0c1807011400d1100181c031003582c0e0b551803400c00e500e008696400503812a10001c000400d0040d4200600f4500100300c3e1140303511180c217504a5a0380d8024008c50302c030a8450303068205041a5880289080c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 460682760 1250 460681510 460681519
    0x1809100e0c0c0f160506090f120c031605040605241317010609050a110706020703020f03121501030515040b0102010b0d030804020a0504140f07020a02041e0f05070c060b040207050607210216020402030402 89
    0xc0c7c0d01a002f103824082c172440701c04180005150244401e10f0a4010300011380003d6510543d214040910000f043c080c20802c8000894001808001445c140c0c0400b030260204000001e03044410b400903500920603481601e088910740804211800118090020140c4035040614144842c075154500250320007641201540b1030096007103d001000d00140103143e0015040c400b26103010f001d075848600192526504042c58603007046410100f030000008040b07400d4400040040c030500043c2d0040c0702042042e980000943d021808140e44505628441e0341300b91210003445a0300d50a100c15a000041c00b10b1300036403508001945914000d4a050340803400b0307c100e50881e000d54011408850461142e11070400b046111700b4a01c00003405180352085440400b04440c8ca4007490041c0400b965490003401c680c1c64030280019a9526010741e0452508030040d02c0007401d003100f01610840000785041040072002d07644c803040b034046109603451649c0c11003858140b0019a42044000d500c0104100c1c0e00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 460684010 1250 460682760 460682773
    0x9030c0e07111914071a04030b0606090d030807091802090a080106030506010e070c06090b0103060b01090e071103070c06032f0a08041b0801021809100e0c0c0f160506090f12 76
    0x1c002c0901b09050a284030011030760303945c609501304402218001000785000d0a0100407101c56515080d80da4000c65070180781c03108031921904022255034006500c044e5110f0340381601c0c40308c1c200e00c80d401010b07003c1c02144c0c941d400b0381c1e030750707244e01c0c2610034911010304642c00040040112031610310900383e00c0103c0d86014009400b46583d65030407904144002d807510702d161801401041158818401c81e00b9003420401c10b01440c0c00c0c4031420300300000f0b0103181004540d4919004905040086d940800e0307000018000d901c1d02c405009000301443e000041c141c11070b50001460003030110741c86503008030344180140c0c904610444240e0309807902820441d036049065805405500220b02d000d80a0401d440015036254042d80845034409180c084051060251030b0a00c40d140d01e0f0000d5080844100401000080e669412003040c4d81c00b40904814607401022034260b00c140000c504100f2103030b4160241032105880b0740c1407003100e0080780d062a40100c6c02c010007680500e4000e041600384240320084918 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 460685260 1250 460684010 460684019
    0x30f090105041211010306090510090b010212070605072304050d020105040b0c070302151201030209070302070c030c0602062202130f020409060906052b0309030c0e0711191407 77
    0x20600301d00000e0f40c0380a00e00308046031940c6e0601441000300440d003414810750801140c2c0e00c00c100341c02c0c071a01c50019134542489419034001d000110541103101c034031945030740325400c1031805070004541240000e0356244c1d440340ca8030360006142c0760243c1c00c00c01e224101420803040c0315521707001315416814003505002c00101a0f442e10000c240d10392004014081c502e01d10f00c18000f441c080c82c001e134217091006112002440c0005001c5030704681e0111038a80c0641c4480780300790001d2040000141184020000100620846107207000444406508840703c581d22031941c440740070442c070508140300344400030001c0503180c03041c62880144a200e80008205c40030359009012a48154040518640c480300e041001c58154449d040082005075001c0504000307024120550214882803190f46601a150403410300d48944103142c0a0740d441040000440c0d2210080c401041080300c20100049500b0f40c03011618201081811024104003005008104141d551410400d00c03a82200502d03c0385140008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 460686510 1250 460685260 460685279
    0xc0909010c12150f060201020903120c0d1206080601120b130b04020105221202040b03030415230a050c060a09080d0e0102160f1506030b06090c120c0c011409030f09010504 75
    0x1001080681c0005079107103e20030030b04bc249041912030212b44013088c0103039044514041000090078100d481e0a0700d40a0f03401d12404020001c9801c110000e208034000480e100c2458900074030b05034010201d980341c540c3c1e0000d910344201440100100040043c50120300194090790151012002c541800f9864500c8680d0003a0305041c03551000c003204500300b41e00f40550426118410204206901030b501d400c0c1848004c0740f203510500510010401c49a08410310f40c403503085402c54842401907115543c0c0c00358003000300790740c100c42801040c82c010b82012034100306891084100303599001113004d04240148407014010904504d44032100c0d5001c01c40240c400001010100303000b8483c1d00c0c103610038906400d00a910b108202c11980700545004410310204d0440c1140942c094400c81d801040350340d0390140707014580152401c400c0c00e503842400b0b02019480c1d05e405041c40c01103130f000030094014072501c81c1a54640c1920400c215820802108880e003041100400c1510010304002e0302d0150b0759061070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 460687760 1250 460686510 460686539
    0x406050a110105150112092021070f12050c0907030e0a0f050f120904020d02040801021605060c07110d11030303040302010c02070906030206090d1b03050c0909010c1215 74
    0x80c110200c00c0307413808803581c1013141e100200201c06c0b0308001c586200c2c0c2d105014032080b56403e28100541c00d010740c1c0c0541e1840c0302311419103008980c45000909684a295841c000340c000d807800c00b00c1204001c2814440203210f240d005030003000510740c5111042c107029900d02d01030455801c0603101d050a00700d4034030810505546d18402d00280841c9034450600d6810280c4495610070b9681001c21050243d03c0244261500f061048070010395400015120500920031a0301034080c65001181d0b250f460383d200c005c4441001d00400554241e95540d0362003403858410854000c0c07400145460004241c00c040c3c0c101442c0a00c6240d200e5064105400020f1858100b2076003100141e441c2c50b20442e043e58180020340c018464031134140240c500b1980061000d001c0c0d030303411500507450342d00031009000780d21030502c500401014280d10b045440341009074032000c01c00d284c5805585200042080c10300144a140d165102641e01d1b9110880f94460450151254220705102c00300454000319000c00d046140d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 460689010 1250 460687760 460687771
    0x130c051002030403020f0f0d1403040f0e0a060801050c0f090d0228050f0d0201031a04050a0c020106050603100e070c1b03020405150907030b040f0e06010315050405030406050a110105 80
    0x1161258903510400001b5540740800502034081c02d860f40c0c8881c5c90701d951600c1d409900641e092a640e0f8074002e12031443c02117900c03c0640ca0384100c40000d069007001071081c01000f20301c42c14813016444003021400d840c01554020365400081108e4596070f480440a17005081d4001d050450048894000620105080d10141d400565661138008000c040c51002c41c0140020340340c1041c1e0101d0382000800c1c131030866002a050544440c862042c00c440c90b060403c420381c004008102d141041681400200440110207000d903280240101c0d80b4a81842582c3c0700b80d4123003038000002818884c1c0c8a00013400a4400000e000151545000141e40c120301c804400e0500541a00e80c14518010401510800b509220030742d4081400b000b41c40c5c651211841c0d00221504001c00c14a900d00049002003044002c0100801c0c03030801c2a03500700d000840e41c10304981c0200c0b610221800104080d100303d03030068034006d00c1e50344104400c000d5035004001808411000d400d080c044003080c0300d242400e5070340c00c444 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 460690260 1250 460689010 460689013
    0x215010603020a1220030601120c0909060618050621010605031608060f040b031e0a0308061504030210030f2313080403020d020604150207081e0303130c051002 70
    0x200c103115254009940304c904105107400b03106104076240a41078800d2200303101c0000380c0d40040011120303405030140d50302007440b12800b00f050108800d40100100501e00800200354108000001d0b01885549481e680c4105c400511a86900e04410083d00b070303201100c00303441405034201e805008480c100a49009002d59105c499403490448081c142d41d0501304010350030300030404107001d105e46440400c60090721060300d000807400c0f040000689003a0100880020608440315050102c00000c00d40b5000540700b41c44801c22a12854104a8510141140348548003014841040585040102d0100790081c600b400643c0c02c1c00d0340c11a03c00c6d50010f0840002c0203200042041003484240e45a681c402e00420714011034409540d03c000d800d225603c03002c1d00c142920181041917613990760032100104401c0004d12945400000c019403030b903125125030310030b50099030240d01c46450040c402c046007140d04400f4603e50b80d10403485075002080c0c000143c1c1ca0010084011806845419112020708031540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 460691510 1250 460690260 460690267
    0x101107120c050438030703030e040b010c0f081e0304060b0a050f0112020309030d0504140f07062c10050409050a02120403200304090c110f0c060901021501060302 71
    0x149204001c80035481103014614150442c641a40101100307140c10142114403405030603451211380c9451040813031154140120f000010400d40c020a9540120a05030780078441d044071413005481c41c00034184003400c1d40e912a4040000512003400a02d4154401078a143e83d01400300d0351070000303800482d011908142c3d20040c1403181d24140001d00018a82103c417002c20f03180401c0000e010401118a00302c5050300030002c01c8603042d00380140d070000040c1344000c0000e85018184009200400425031044d4094809207580422000c200c500070b445040e12138415200f400014001c04112031010320601486030728042c0c41e1641d07503e0700c60f00354044a60710151620300703000c4039100300d81b40a09007804051041202c0700c5288180d002c03055102c0d4042c142482c249032014480c2c15014580304503c5218000003070041602d400e41d82c4802040f00560351015510a01000b20550740d1b01c41c1141e9003c9580404070b52190b6213000c4001b0440c0000600c1507816005078044040d1540c102078001001080c0c022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 460692760 1250 460691510 460691513
    0xe0103020d030504031a04140f1b010e0d2108011d040302010e1f0b011b030f0216090203070318020d02040c11100608121602060d090f030f08091b10110712 68
    0x8200458003480300014000d80031030352710110b41c2d0300c4480070b031150100c1030540c601c2d050341e0103803c40714074002c4064a0b03118002101e207410300c4074128042d8443d100c4c2010361a034008507441106014142c600101591480d07103c4040700300404000108200c04542d02da0f0095034480750240301218442200d5010303405030310304180e00c001c103540d0040f84d401d04004698017a8440510343c61030b11502c068150078034580340100f07150103e05000c41400b002c03c1000e03000c0d00024091403a5401544141c00c0307aa0304200d0030107940898036804c003010784080d43c48880c0d4101400503140ca6031001494504904103002c68005140c0040d0a10182d400c100f520155120b204102c0c0e01400c0c0404501c2c00c20b16a80145841e140314103000503c0b44100c406402000007180c1043d00c6411350340540c1d5056000b1141c484d030303c4a02e01c0c00038070f6003449200f900c00141421000c610303000d6000440c04411a00d040d074400c1240c0d071301414800c48428207100d200400003494090200c2400600c16800540410760701d07240030344000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 460694010 1250 460692760 460692773
    0x1017190f0218090706110c060d0b10020c040506100c0b0c09040e010501030215030c1903060906080a030906080118091505010f0f060807050f0702010905100320040e0103020d030504031a04 82
    0x266801201805034441c4a01b42e02c5002144413102000112980c948400c844803542006001c003c4229421184103025a202c2c02c1c2c0004514402d42d46c03c0f201807003580d840c48140000505801000000b04450040b8240051010003001c1c1e880541e102031349040c5041080010305648010070010010b0355501c0c01401036081c80c00b00080c3c0d256031b0800091450901d10400400c1d84241e030240120007071180b62070011148641c111000030820014103016590700d90307007215110808c0d201c0840c08150b00c18400220396024402c2c55040b1450158140489540041e200e8040d00c040d1104984070019808801c12004044c41054041e114000e04030514604203148461034803000d070840000c2c010386004100e980c641c4074080f25448001141c10588440d0944010780d0000b140b604a0b51303010040e000500340300740d03040c2d1040b505140120950010181e488101d900c062265000e0003075109514401030016007042c1c0360080c18244a860820b203020f0352501c913032220320301c01120b034200861902c0520061120303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 460695260 1250 460694010 460694023
    0x2010e040c051213030503040308040609021008271902030705130c0f030509030a2f011a0612010501051303120201050403270e09010e01060b031017190f021809 70
    0x50100c1801074940c1d8a0704d001d001b03400024801020020310800150420005400c0f8440c201ea0207085c115800d42030200281044008440d403020000e0082c490004c9403898440c03110000220202034940c80c50b003510701c83c20005035000e040e070305803140d01c500080e903848640c0d1901c10608015400607442048200081c0180c90309014a42018142400d12840240220880b07690008600301050fa000d0100d00580d0000c40740c5104c2c0c5044400000034103015203040d0440d00c0e4002000c102e141c000c6101c2c40c104511801406541c2006480380c1c0d0060040794058030060110700001044480c01558030750b29040d64011803414030700140d4540c0d0034401010303000001031141d6070b203203050403001c04407104a4860182040c81503a031100c041002107080c00c0020352007006c80e015020000c0c040da039221003440c96150700544d1b0240d243d0880003c00100359080750b12a008154000b0040c0209248204e100201300c00700c024140e07416641043e6020041e914032130440004a219110a925854150f19550a044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 460696510 1250 460695260 460695271
    0x12010606020606030321070e21160b04031106090a060f080f060d034a04020a020709050c040b0307030b011707050a03110c0f07082505010c02010e040c0512 68
    0x40c814001c846c4201180b40c0c0d001e840c0d07040542c8131b080c280c0c0c8158044031800c4080b9034581e004104207030310089030a00d03036402d418085801360880313000300c070b0800107003203415400e100c0c101d0158410300042c00045d12050407422480030043c5058100b40070040000c61656181d48840003190481d404c0c1d203444c1384c02c1346555a10007450035600c071452030441301060b0a41c2030980010100141007a800100691801060741c41c0c10310b0144010404170000c40404010080c100d0003440ca00d400116a0780c1441c0c1070003110481c0da920742c040c4c020f26182c40c0ca040003900001e0210640d40e04140000308003048094060352065505907800b15500c4d01460002d4001c08030074a0f0440d101010100300310446400600f180c035031104d81e02d0002000022484070340c515010b810103009907802200710206102000107100c5040c3d90040741030380c6c0064408240c40d003245020311007030800604400c208100700e600a041c0c1490030350060401401040241e000941251f031825045d901240c030108040fa00410140c40c5e160303110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 460697760 1250 460696510 460696513
    0x1409040206040e07120203010f050405090303040f120e041b08070f05090d080909070f1814060c0f011d0c011103180d080301030528020f040f02091201060602060603 72
    0x14249500800c0c26407203180248681c404a00010451445c402d188241da100300c04034045441e541c4900d40c2d2440c0001901c1960b01c04c90410011468809000c001c4902640e448607810201d0a00c907a110000c495043d0003a00500040c0400b5a001c0c5c0c840303000c0c41c8600800003506003500d910f4200080d2030341c14058172540030404885107402615401c8401c445200808444140b41c240003850420014480c99031402c2d0403500d414144442c03590000c0021105d1103c1d034859042000300c5043e03461040b002c5102e00e02250310701c0c220b0382c4c0c41410413400a11843c3c0d1940140c0d14090826480746003500c21228441c40c3d12803000c045e00044080074051442007040074640b140d1006a040c015950740e002c1e51040340850000259046803541e10000440d0306150b002a00c251690383d6800e00c640c031403004a0307002c207e5401c1c42154030707420000c3c2c01040069980c0101700450340d078090414840104011040400c07641d500b0840071442e50380300b001501c0a01d03100c0c8008588142040b200074284800548802d000303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 460699010 1250 460697760 460697779
    0x8120c0304021809160f03061103190504022701060f0c0515091c02070509131509111c02040e010606050304120c0624060807020a02010516050d0914 65
    0x16500c0d0b4210003c00ca503542c00b100d0f8283c45501c52030b4113000d0301d4100b0407000d4910b0000080c41e01d4809803443c080768043e0000b00003850380e1101a02c100d203c100c603035a214542e18190012810004d500898204c1e002411212081e00a0354500074110842c00814003022070380001000705940c4922aa8081d03122403610302c03d904100d0351800d80c0d40241040108a851582c000030354402410002c0b80c0e00700e101c100441900700c40c0084045d45410090207500d000302000b500283c0c000820400c0c140529502100e0f0a000c0154142c2d0368009001c41041101c50179540e02400026035104e9000f000d207143e020380e480a08651b144100000c49030061703500760442e41089130030003603d900101070f658065003003a54440c2280c900d00046502041c1c2d500010400340c5003621808050204810800302c01060543c0800240d8862005640c2450106d42c3c01c00143e11a07180c010055208001804140c0c1c90350500d903442110b44e40c0c650b07041440c4082c0c00340004240100030003245d406540d001c119000c05443c140715 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 460700260 1250 460699010 460699013
    0xb030f07050c0717030d0c090603060504060501090620010509030421020d020907120218121f0902031e15070f0e01030e1f0f060f1404050403090e0408120c0304 70
    0x2150f10680c850140c203204092202c102e070810a104590307500408a10800c0004280840a080c0b0001030141000081c40d0400208060a080c4500410b41e04161603c0950b030f807800d81c0072600c00c2e4040000c43c03000501d02d14401512382c1e0034022a800f4040c10030213551118180700c08010124514805800d0340c0a4034040f40e070268441164007240560103544044407076842081c141c4100d180c8910703000a55200040514006c1c0800641d84007404049030310301400c900d500c0301160341d5032071110450742c401007004600c030a1100303603403002d00c40c0c40c0f026054903800414900c5542c084c4031480103803980f5401002140344040d10100381c095218199050044941115031030003426041c0d041d804605056a440000340000701c2003000c2814100005c03000340750841c200c4101c1c80501039040c000c5070b1540c1014030204402c00c4040c0608252a039031440c41d5056203049080002500020700150148909074402145200c031400200744114010642c0a0b620540d4807a01903040300d0007003180301600014800d100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 460701510 1250 460700260 460700263
    0xd0306051005031b070b040b160f051b0319090b030f060d1a091606030e100c030e0303010b0301080c0609010203160501180b010e07021c03020a0e09010b030f07050c 72
    0x208001c816203045901da994841c0c2040c81c019020000c02c0080d00003150800c00c000d1020300301c0784a54400c80790118291030314210b140742d400ba01c100f03000c0403401120b1900c1006100704081e01901802181103070103041e008914500350f41c01410015030045588a481c00d505400012520080c0a00b00d801171441ca4020058040c010014110520440e0920b03440d2043c8404914202d5a1689900444246080108045940c4d84640942e480207460740d01340094440d00034410380c0c5012042c48083e1142516554041004203841025031060603035072640c040c0040d60800156018080e00c03045560340354148002c00c0e141003030021140b44114401c0001c0007603668040291500b11101d5800f9130411500d5281160152801403030458143c50480032140502100892450495000303031000d40d000d80710800201d88469400c3c2c0c0d0705a00048040440019610990040294084500c6c041c001580244005005404281c0c4014014140481403150703011840303550b03903044030050600501e046159200507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 460702760 1250 460701510 460701529
    0xe060d05030403320a0201110318120a08030f0a150506040506130305010c17090601030503030708040c092c06070801050d08040b030403020102070b010f060507080d0f060e0601020d030605 82
    0x14080c101c14145800f00180c0e100714444d1461003900822524001000f0860703441209400c20781c0041c7c0100380c00644590080110342018072440288036015140700c090144003070100705400c401c1c1c4034010b0f042c008180210040c501951042203402d21500b48201d5180c1560180111075030400c5003440d00300081d0b139030041180d04072602903508540301c0280500e50141006203601c007030125420588036212050b44502d8040418105007a44813082c3c680d85402035445c802400000d21070344c02040491070b00d5000c0c81c05580d105200d90f095080c0261201c80050603105d41d81103500c2c41000030321500f81804001d8525285411400008102601e8003400c0245403080c10301c81ea50080304448681802d00589808982c09081b05016190349c906180c58002e000350700c15203054170503c0341e0078000b0900c40102000328080728001d60398503090800945851581d64011610a00d00940d85c05220300306480d54043d20b0014a84036120306418074020002a0400b10000d000c1384c101440c100040c80503660700743c4807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 460704010 1250 460702760 460702763
    0x20c090f0135070305060601030f02070c0b0f0c0d05041d06010c11030109080f0315031b06030a180311011b2001150909050c090402030307020904051002130e060d05030403 75
    0x210040310440b40e248074504141c00c111400c1900510b0400b00501c407000400c907000d1602030780c081003214006c1249004174018850002e0403466009402c1110f9040600035140d81b50768584110300d401240700742c0030701d0428941b02040214002083c00c0214020f9030500c00c903200e48007000c0007200d00d040400240f03c203a050710001c4c100500d000c114015a1801d500801c0d00d16400198150f4a050355486091b150700100c4408440c1d82900364070600600b40400c0c20058a205c413544201c0343e1500c04100080c5810040035003240c1c82e520752016080e0036019041518890084e100c140c41100700001541c00e590f036030003140000e040611080c00000307920072100e41e032145000c10403010001c0041f1800f800b500d268050818048400b880200c0e800b00f5139845424a94420300403180000d00507024046590720446019500d500140801005400c1c20070305554400e2154050743c00016400120b44200c1c1c000340c085442d9481000402d01142c00714558858200c20111780c0c0408494140c0d07500c0e45e892049010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 460705260 1250 460704010 460704059
    0x130912110c01080c0d0e0606032104060302030901110703080405010c0f0203040b030a1103190c08011208090111010f0f050916150c120c11040905030a0507030c12020c090f01 76
    0x81c0c071201340f00060b074a60134160b03c01800140c5d442ea04040c0c0d41c65040d00e18a1203401190301100030a00b805040724903262a2074040c6081501d070030805d6000703420042409907155214136260b10781082800081c2002c0e486910b0744112801e19040c400e003100c2e07400e0529400e0140301c10924410940020a50b012640034055090352541d541064101810030035019004029021052281000418505000705a640d0204000c0c40c000c3c81c80c101c61100d000c2c850500c0360440c01440f10007066400d002043d08010604104400c01040c44d2103908540c10150086080c07036036540741e150550b50b5402280d412858100080140c00076140300c0d03215480203403103010b40641e401c61030881d200c2e010f040e40c1e803003882c4c01c9480021b084a036600040d11840c084c80b801c54020183c20f10700d60003441d241c0b00f03521849030010020340c00c003010f00c0c0c0180c611f0307030101505400340006202c407400003d42100340c5501d500c203240d004c0d0018540070400c0c002c440c8000f03800d82c4044030404005224503a256118210440007051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 460706510 1250 460705260 460705277
    0x120703030204030215070302060705130317130906140117061017040321051b0d0207060603060608010501061409010e0a0e07020607020d0905010914040209130912110c01 74
    0x2a040d0000e00c500d610094008100032207000c1caa441400c080c0c001c00d4081d80a982c2140c1e04c041080f52140b240d02c1520703122401e004810300101d00303807181c41d2403080d102c01a41c52500400e01c1c8410400d42050340030303034001d9840e1442400081421130b41c2050000c2e003070034170007010061901160003140300240356a014040e96030310000396906c03402406402e00310411541c2c0d02c0342402c0c200100060410760702c000c00100d000c0b800442200242c4507051191115550000200c003030b800c0b0301451548000d10303c540e115000c1c000c00012950350f200da80300951080c0d6000511500c0c2042450a541059112006028495a141001d0380c080c4003140c42c400c409103400d840d01d4901000044800c4c000e0380203400c41e0b807204420065513a0300001d203240a090341c1d800b280d821004d410320071140e400103801400c0c0010300c10042045186107103070b0070310819040104050f040584100100d210300c005011446203481d111191501480b00644c1481000c45c1140ba0010891082d0f044c5642d0300c9141d640b20504204802 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 460707760 1250 460706510 460706513
    0x3200913060e1806160e040c180f0f080106030b16091505030a05060f0a030311030c01110301031b0f0506071704060207050108011e170114190b10021207 67
    0x6500400152550301c0700300406040c40074148075010540c62800c1c42d82c4c030481010a901c01c1d551900580400341c9a42e8002140100405000180c0b410300006801c0c400700c49001d8103a41151990000644021031101c807040c1c1c6001d010b1030f00f11400b84c0c40a0243c2c0d15200d414004903a00c010780c582e010342d4516100d0422001000c04442d07440440c4c5c015158048003600410410380e10500031401480c04050510079900c5200410025a2084091644c050318140c42000002d001c0c1c203030b152404502c201030780c1c200359904010a003500e03000c2c20a801c110070b001005100700000382c1d9014000740786542c003001c0b0b95418034042c1c0802c40c08501030184030303034000300c2d0380c404210496100d400404880d074482900c1d40d580d20310103951130b80c1c02c0c0106400b0072089000410340b5008103003490b61b060180c0c42041079952620011243c190601100391259540f41c0081e01c040e6004d204d46140078000300245400c0e9080501c659074226180c900103648680c07040081412005d500040e142d881c0c541c1c2c00d100d1690348245 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 460709010 1250 460707760 460707799
    0x51303021204080712170304080903010507030605030c12012004031203110f0903011503060b1512160207091109010801080f0d0e0d0203070b09030c0607051f0f0f0507032009 76
    0x101b0b00b00c803c103aa0008204020424988041c101d9107809038002d019a850ba000c0583c2924814010243c1551000c40300d0300c60b6285c1802e8400694801c2000010900000c3c540000024564001e0107000c940000c0c0410801c60310220f407179088011071030208058040344c504000c2900c140d0310110764001d800300ea0059107a6080d81310640700e540031028040e04994030314061000d002c2c0c0c0440648500710a84c42c1c6a0900041c07001c03644900d03040030040310b00ea0f440101c210714200325148114210705c12501e010a9288030391060440b94a000e4000648070b01c4804c000402052058100203ca90869141550010000181c5241c0300b0900e04200802c444200089002c940302d055010b5814840c448000400d0358230080203100d000010b6040d070710718400c0707181481081d01c41d101c4c0c010247d50151400140c1e00c00c44400401600048981c0030641c1c880c4013500e803007035980d2074130000f00780d036965014000f00d503030507200d000040041c5020300080d410848c2c065800f6400380c1b010350f5000794000c144a11600b0325 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 460710260 1250 460709010 460709033
    0x312071b0e01090903030209030616080105012303040c03022718031c020f07032307050d08090a0c03061e051b0702060706020a05070c050303040f0b0c0c04051303021204080712 77
    0x2030180881d911440e02c2980304210213030303c0c5515004133512030700104807544100c2070001001903040700d15418007600103803010550f000400542d50040700020200050381d4043d0101101e064660344c2c070850600c00507102100d00c10145c09440382004800350031421072008019940b800b01e0b101e050004801c8002c446c10080d05c01c85550410f4604001000802c141d0400484045078603410480c6d2080c80c59041101c013148540b04020704540d00046110b101c080c030480c44158419a15401d41d400d401e10307591412401030943d08100c030f0a9490706a00e42008083c0c2440030a13030b80305c2c2c03d03044c480c500f0091840100fa210520400003d00c00001d102000c0d521600100c800c1203921113400c40d030783c1442c0c0c040209142c00a88044030003203144031001690340307400410744041e29803404035840001d10703103d41520a43e10116216aa60252142e070700c0c0f45c0d60b100d1180c1d9100e070800c8c0e440368843c0403681c0fa009043c85411a10341038800420300080c440f4100000d000c100742c4e800072510866441c16414110785815 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 460711510 1250 460710260 460710277
    0x3030e1e1507060615020705152b0e0109150c0e03070f060f03061809020d020a090e0d0503151c1b050a053304050312071b0e010909030302 61
    0x800d0888940c41d0700101d40002c1000500400d810004d403504c505000700096410003d1000591003608207011501d0681c003003010002c01e012946103412440304842d55803603e07048407408a503003d02443c502d8400203004004000c40400e000f000f954050340d0b8ac0050546040c900125403907030310b542c2c130010700d0301641c0308055011009084404055842041145070b100318041c2c0c0000030328209451508074064010711003070710156880140f20a218041c04001444424000d03a403009001416101685803041248090041c000b00442c1c0030044c6403c1c01d241402a04030082040400c008110700344403010325442d02c0c054225529102001c00400303202c04150444006440040e00740c80755501441e800c01c814084500655141c0c1000355907804120503c00c40600e0600c041d5107807601d01e60350401c071070308640002c0800d410032800c1c43d4458011900e490f0102e04001c1000070b0001d00f41c8107000824542c506042004205500b140e420011803078000001845002c004030b0300d0f0228002050f001e501a03c1ca0b06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460712760 1250 460711510 460711519
    0x39011a011b2306090a020319050a11040204030602121005010c0b0c0c12040e011d010e270106060509090a05060616021c0b0a0501080309010504060c0f050d081b0403030e1e 75
    0x80c1000c05a0740e449101071a001c87c480e208400351501e2005103001303230101e1640c000000e000c00d80000e4440c10754900780b0981c45a842642000702100255451001d0700b1b08070301c0c07503241c881d161410200015929110341c002c9070611040c0b00102000807900d02c00c8545c8045807184c12511081c00b010514070389120b4034a400858000403801003041c4207c03580150499044000e44d0a10070342d940d0300c1240c9180d00303000300c088581d0039500158000100c82c80300100c50181040c042c02444605840908544031500070f040040d800264010b980c0c500040d0b0503410000300c4404000c1800c1003030004000f8403400140c2c1c01d540d00307111402c42c295aa54040d40003c0031002c0e020403000c6000e85030885c40d0306400c07100e601c0440c0ca0710300045510394001082d1402880103864075403925003021800c0d18a40310251046580004000f45240010b1080c8081001a0300c25211402a400e100c02e80016080d4500d29010808030305010406c0426070049400070b0031441a600c000002c0100c1c0f80303003104034201900e1540c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 460714010 1250 460712760 460712773
    0xa06020c07171c080708042a0f17030c03041e05030a030e12060103020109060c140d0c1a07080a0f0b040c110c0a050639011a011b23 58
    0x503000c04612243d090303020b0200c519404400da14255841c200c10f5444a0024185400080c002a8034a4011025414460b1a403200065140010b20551219002605603122194080040454589401049178404400307141000d0614120399928040c40c4901403c21030300c00c2000c40030078540c41c40322001c1c0401409464402c01a410b000c1d00080c4070705106401031452150704240610041170140c16281e05035104890301d03150038000c89001d801d0f4801038841e141000c048410750321040082c0c01c10010036841e21014010541800807090107001d400e00d0720700380300c0010440c1d41c81d4000c0700310360b0007000014009100707106100d1740c000502d035032041d8a400514010300096007981108075070320300c0043e00084810000c408000d029900c00603104460300048180b082400507861000201c06030310030b880b1040c0c000f10110402e80d000810b041d8905c000c5075519540a000c03101c4208120001072400e0a1544025003108807582c100d950800700540190004007010904a40160402d90b0548450084818 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 460715260 1250 460714010 460714049
    0x10c0c20120708011a0d020904081c0203040b010627050411040b0705150a0902061204021c0b0402150901050702040c11150f011409040605040201090b030a050702011406030a06020c07 80
    0x704124507018035004117030280204140340440740404681e0b40500300300310540f5070340d0390b43c41d090704056030030030a00c1100018003600c1c94035031014510850058145c60019458500c002e8000a4580c3c151401c80e4620f0045122a01c03250102c2c0b012a10191000a44094999040c81d8140220342180305c03059400030f00001030001c001001203d40703851800c800080d8503110128070464101180c000d41000082c0080da400c800e181a0050f07000d4006003440c043c0ba4044040081c0000b890a0116a251403920130f000c00d6050000c009061288480707182450581d0b07540002e041406030940080c482c82d224400481c80a100b008901c8400109000b11014030300181400400042c0803150403450b05042d400009a654824001c8101c17190301034045103c5803229244c2c6406001e0080c001c1e81032180b1064005140c00d4200f005500c50102804001043d04000400900b51080c1c00f00c400c448190400c140111940c0c00f09191050035840b4100507230b6102d001425505120b6940e000c40300b05540007130b0885 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 460716510 1250 460715260 460715263
    0xe0a06020303060a170a0803060d020901030f03080916170703150207110409080307050d0618050402030f0a0c062006010602031c11090402030403020a060f0b03010c0c20120708 77
    0x1030040f00203da20500851325400405583d0341826810510340c0e011490b0b407408910f00b00000c40d00090060180311450394640c0100d0f4281900b0b03802114041d207089580f9041c1903201040c10f401011103405400080c80c4040c103810200001d0240e00f840d02c21004d09928142c0b02005805e0003940c2c05000d41003a01001800f41c00250010801591000c4203c540001d00d032419100344030b1019880000c507811500d445000302d40031381010302c590f172800355900804900c902040c0110307a500035034000003046c945050b10505040a403115413204440e8131602c03400d000150242c28000076554a45488041c10741d01d00c0c0c0c0038000107000d00110050340030303010006c105aa80030000308030319240400c00980c1250354000d001c0c1200d0746c83c0171b194640c1c7c0041c005100280b51a4004603003040c0244121414031038607841d0401140d2640b0754001c103c43d501c20503c0c51508082c095809914031030306040000e440c00f074840200c0d55203c8813900a0340501200112a20313558001c000212800900844100e50384410505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 460717760 1250 460716510 460716517
    0x4110409200a0603020f041707090603050106090e0303090703080d060f030507081e03030c0a0e19050a05060c10020c010e120a080f01180908160503090a0803031003120e0a060203 78
    0x41c0d0185010078404100640217000715000e0381c40846800d0f242a14041128440340c0b040c50039103c0f00d01403520005a2840d1500a90010350700880002400a140500d107404440001c804440c640c1c00500400920200100300c00003142e80244c0f0859076a441940c1400c0281440d40003413540715107e41000c4103006000851b0416920384904441341c1109880414000c054800032118040d8020400a03040c0f08402c40500341545003401d0111400114600068005c815400c031040a008800010010792801d41c1c03000340102029600d0700d280c900000700954442841d1003040104a4002514028002095010381c0201091400340c1e045508030450046540d480307038800200046c46c040c00304808002c9052070318101e40034444120086440003100c0c001500c0b02070b5054411717107070510502d0f8664108a01c0f800d0524410b80103199241522030412403211010b411403280d035401030013080b8480720a210741d0001e407900f001400e4402d40140104035418000300301e0864214941d404005065038000015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 460719010 1250 460717760 460717823
    0x3020f040b0c1009020306011205100507030b040b010914150903070308270108060904030e03120a0909200d090632091b030313060203030108060a05010e04110409 71
    0x242c4101d080d03c0000802520480c2c0e0000e0344c145c025030010071604884516040300c45205d1800e5a0000384041880c02c2120411522600070036100c0201300400d10301403049003003002c0b013404e01211035400c00740710742c1358422303400300c4280140d0312001c2d080040246072043d201c94a100a0440d03010135107900d4039590700d80041500d00d069184450101c6041a0902d0303107003061890607990f40001d544e0b05010810a1000030300240c041c0304a00385100c90b0764030148580c803503230514041c1090b52006041c03402410000a0b44c020391b0094a030040b054181300e205034001000c408c02c02d6075980c5480c07200300e210000b403940c1140100200c0c507100202180d4020500365a40c0c200150720518003810700c1040040c0c00203011191084590040c2c42c00d03506050250345100080c0102601326803d2455640d110720030035202d0742080f805a40080010002c0180401140341d001514100c14442540746c080c001542d40750142000301b8030038034000390300c51589841c0d00504049800030790a4208141e0314803800d81d0320151040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460720260 1250 460719010 460719013
    0x30a1e03090801020301060c0609080c0f0607021e030702040b0a080d210513021c080708030103050607091202100507150b0f040902030318060405030a03110607030c1205040303020f040b0c 82
    0x600142d61141842942d04965050b00c0b02e042001c900d5a8500c02482c001c14100d84219050283c55600642000065a0381d00040000d0001e41000d1078068a440781030280c4220f242c0c3e54a02d090141c843c04001d0b501c1d125415a004580300c03c90348005580c403000c1c2d4105400c50f20030b51034012401c65000c1c0311122b802503000042196042141d82e900280c9400701d40b004d044c01801c21048005041140550030501040719004074850070301d40e00e00034654014081610000000300040c0180b2605204540e000035260500c42ca42c20714142e4075442c6a4041d0714042c2c07044004103400b00006000c0e100b116042544002c52138411840600d0b2803004082c200f007001d014a00480074400e00382404c0c411095004d4005000f9400c02802640d6030b10340f001405401038100005020000e00b5440400c081001e4521036250b101c401c2118040c528a4102c0c010071020800d414204901d02c01d0b60032082c440d00f407048200020a07555103504040e40a4801c01d140b0400020b80001c0003c3e4440f2100003406a9030035000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460721510 1250 460720260 460720277
    0xb300102040e071d06030c0313080405040903020a0b180601061112040314150c220e07020f1b0901030b07020a080a0f0806040b1c03030f0207030807020d0f09060509030a1e03 76
    0x45c00158003046035220300183c0d003000410756850740340d41900c1d0054410b074101440d00e03460b807010a042c1c0e9a205802c171301681c072240d0f0440803c0000610903601580e1520f090f003108903180c00c0150341e82c1062042e80244290303644800c100304414000d04030a2075107640004e40d01d82d074a2811016411011140134000d00480140e40c22440a891000740035800c1507407507605240450030700302001e140c0312075465401b22153360005018070124032790794450703011500038240d00c50300c420210742484803800d0100c9603030078190307102d50440d1741e00030308541943d810501e40065665154410380c80c0881c00040985007a4001c0361002501d43d0215080c0142c520940d00c2c400b441c1c54100900007955134a005943c1c1c8003103042d44c141603201118180b6900c1d18003a1602103840c0d41a0b85801d002c917841a070b0240c7c00258510100b01420303404101035140c1c1030403443c2c071a00180c0d100400509540e014010141000000201d080d165a000c001c04440317282c1080c1c0c1611045038a01203031180001c852411804900201d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460722760 1250 460721510 460721567
    0xb0a17100c0503060f040f060b031b0721020f061f050a0305190213051003020a0501080601021507050403080c0303070206090f0604030c330b300102040e07 68
    0x140200305540301c45854450841d1102810410f2a440c551a41d54100303644a024240d05003050007900300402403900c00d9940c03400e280070096030340387c480c228011807901c0800c00480040e816680b08a035501c0c242c0251220343c45005130803801c10a20700c1402e074461060900f803200d0032000444491b504000708a084802d00d6a440a101004070a0300c0064500c2e00720350124100c80b030070300248402c440d10081002d09000c3c00d003040c03442103e9007070300c0c40c1800042e44d0340c090045050040b03859010381801d0030300034024a0444d000075070b2051080e801d64220b0001074040b408680c014400c0d10095940700e5030340d58641c40e880900303d50b82e41007220b05078014490320340070852481d004a110415808a08040c01d002d6031680c8042c0c8401e182c4c00c208417100c544040310a20301c07c8811880b4220300c450040e14031035032400c01e003e01c3c0503201d80701c030320720320801120588600c1130b00002d08a60f109824050f004a407540c0e000103050090082d0303480b41000f040440b04208209505c101344400303c01921500328443d2402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460724010 1250 460722760 460722793
    0xf190216050a0503100c020c030a03050705060c1204020d020a05030a14070b03010305030304030807120f0207030e010504050a060c051e250303090e06040608101505030a03020c06030405010b0a17 85
    0x407407040581541026119011001403900941411206e6004507802802c5440c0402d1070511103110a50004501040c440c081150038424190095000481f4506140000203543e0300c40b000500000d208504060340d000c11502c50b40d000000900b0000c081d92100021800c01741da411415145203da1406200c1c40410f50100b02015207061301c3d000b000850a540c0c507607130141c5039514090440001e010290050720040c0407113000e000030360780d43d411002d81c4408a916001e4003c095801c405414008240820301c020789416480c45c04541041c40c10b10b1031203210342000d0303041c03001030140008001034040301c000124400040e06c0081c03030040301c8420903405141f0b488540c82e07440c40c08020b000030300e0101d0030090315070608002608400000c00000e041c6a940501e90324000c210140c0c94499904c0b8400e000d4111002041b42c401444150042d003000c00155038001d413603030b00049440303110f0a804004075044c13003400d40c04101d400c5c1e0054072030703c2c280d92142801c007081208490700e0b060a20882d55040e501fa4070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460725260 1250 460724010 460724029
    0x608240609010b0a0f090e010b0d0b090601050901030f061a0306090a0b130506060c01061e05040e060c031003150f05220b0703021201090902040b010903170f19021605 73
    0x10100ca070542130400d40841150301890751903c0c50704008414501051084000c43c01500901400184036529400000f074101599150b5010510562000d01044001e90f0040100c81003400246400104112800c10040c014002c03504040051014a0f01820207880390800950048074100c400b0007180d5107042e405410b0f11561510340380c1080880104400c1e0185079000503410200c000c098030704100003e825207007140c001b640804204458030010988000503551000007070402074030103024201040c80c0c85075a03044080c15240b501e243c0000007a5141e1949020a40510b82c4121301075850310b200c9500f14060101c07046070000381072810b030105106282035980750014120380340318500e0b044401d0321004005140200349170301385a000c121455051409400940c080d00a1260000d010422401032204540009004a05020b00400c051010506d480c0c006140310707000c6d040456451221000100c86401403055a041441c00708035500d040d00d80208601c103100018560015044c2e03910f81c1040007400307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460726510 1250 460725260 460725269
    0x13c0608010e220c1e0510111b0d12050a031d06040b060f04020a03091e0812060d060f2306060d1a09040f0311010515010c020301060824060901 63
    0xd440f40b404845450300782080314003e0780030308402c00103595100411010f51019030948044540000000d008514004010843c00d1480386002001c141071506900e650380300c440400a01e0402c44804200300b80c2d25620908960f603889503491481c000305500190190b00001108004a03041031030446032030303402e0950340c01d00e04880d1001b01690b407100c0e00e2f600c07084a405812160000400b06091031136454600041551242a5400054564040c2005030134819140c0c0c9585c1461801900c45020039401000c0d107082218072005110f01d903c0780d0340010701c0c014aa0200400c003d0511000310a03814841c2d01c56030040c0324125000308078008014100b10f11441c2141c1c0d1036403055050025165011103a0b11011202101c5500d03040c112110b2400030b041340380111400c07141d0110f5544004100760303002c181a8241030301c9000a2160b810015034021225a0500e190307070411040c240c1c403101f550340940054000301452801c0e40c12031104540c044c0d222030114902115540c1b07070f00012a09a0a18600c10350498 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460727760 1250 460726510 460726531
    0x309010e01150e060f041803090e070804140c0307030c050f03010b0616151b020f0304141507150614010804020604050405100e0903070308130506013c0608010e 70
    0x881c1003d6a4450a82e005410160041044160402c2e5501c90303128040301d02407200c0441c011030b5101c0c40d005110a9003130b0011000983c0800502c0364064011146580003948181880000e00840d0401481c01c0150007516038584190003000060203c505207281c1030300c405490703404104c0072401c249403d80d981070301e0b03c41c0c224104210b1312100013008555940028890440c50680703c00c00344000064451507421803040d4541c20010910b0550100312054462046101a60410785002c0b0f5135504081e00305140e80c010354028501d242c5000c54101141d00d4a5848405101c552103289500c50041401e40604054170880b2007007800150b00412015209a41c000c044a01d0107007440d0500018202c083c1c07101d550320581c0100487d17100c82d80b414141c400d442200c02180c4038205414020581c020141c8020281401107890030003152003c50480d065440301daa10a0700005014512001c0101d00c80c5103220300d400105034400b840043c40079241c01c4440d180e0318401c95980782d0445520410b401e8a5041c281d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460729010 1250 460727760 460727801
    0x9080309030d030c090306020f0301142416060c09030b01081204150c0212030a03060f050f0906030313060e040608031c11040b120604051501050d0e0c150309010e01 72
    0x242d034420703000004110b00e14038041000301d660341c0e20b074820f903004140680d40500700400148030039009050100784090b0100c03900f41010100814800b003c107400130200c1030480700007600b80344450300b0171049040713107074030413410007440da02818028078025803400202d421140c100000942a5400903091142c1d4680c81282841c0034545224008041c2c12040000c09021452030b804026a448661046044254001039991000e10010003411a0141e8000e441c620448842c20700c00c0e40c840440c960020002035501ca906515042c001901e503011700032060030a0700b01034902060855200950055036041600c05001c101d80790305e0141d4490180c40700e427900d07502041c1144030010105812040455620090040c0f40c15182c420043c19940030790840240044c0c0c107418082d046c00d10b84070f4a80d000451270340801d1819a042c000a2483c4100c41000d020681c41c2c010f556020030050203080900b12000f4035842802c82e81d11840d02c03194004464202140d4a04007130000c1c2c902060054480e2002d01c02c2c40e550b207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460730260 1250 460729010 460729033
    0x10507120b030309210d1706010c03050306010c15020301090e1203070c02150f1201170106080c01110f06040302011b090308030c030c1902030d181e031e0804030908030903 75
    0x40c081c0c0d01c245000e6400716200c100c074107510040c070030341d00c00918945d01c4043c01030718001c5031200694080e04231410440444c10b0400880e40c000c0aa80c0c00c00f00928082c10408003d0801441c01c820f11038410313030310b03d01c000000100c4010303550004164100f428150783c442100487d00e0740540c04102c0310750003c0303220540d45000515040b00c0c200c8a00d40721004503810068080e2071030b00a0f41148034241c844203d240c0040c0320400c080701c061a810b0340040000d0000764141480c85448998586543c2e05021440005039149401031005280e01e0003010112655031600e410000d0113440c821000460510802c01c010005512640c500401d50f034104051500c2c46d111859881c0f902d80c0b00502b40307040040140002405a0034403e01c0700000c4103950300458490100c03403031100488154000c500c0361a4071920030b580c0060110b8554180d1810720281800644800c0d040079101d02d213100910381e4803c0b051094040d10540c0200007140194040d5990302115903c40c82403540d86e1243c4000c0301d6055120078103408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460731510 1250 460730260 460730269
    0xa050103090203030d0501030605060a051f03020d02090d06090209010e160e040f050f090f1501120212030412150e0a0b151009290f0c03040f0305010507120b030309 72
    0x7200c0751002e0116441c00d0385084007181124402c0e00112401070300d80c4288501c44c13070080202001381000320780c0300c1c03003200421034101c0d44485008541070034941c0104801d0103401d40350303050b11045000600782c04504c00c41031034100c008100220040388178242010000c1160840d617145c6904c87c1445c01c1d65841500780801c0280c50040300d050a2991103501c0f055000c040d507103103020302d500608043c0329a107080d0401e02155070815030002c944008981c402c140700c0700035500d407040850448140701d2604012550350300101d18001411440c03d00548000100018103581c049041c521807402492200010700c4200b4803002a02c1c40c4003803e9841c0e601000e201c00105201059141d000900c40016200345141000410a1480031035045c80100e4040001008100c0c0340d07000b05a1400840d00c1000f1506202e207601c0310440c0a00070308154951008581489807440070021200a00400710300c0b00c416680e20300d011400380c0b5086074040d0010b81c0d001701940c07203803c0500409450344402070185042c01d06020501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460732760 1250 460731510 460731521
    0x10f020c0303010b03190c02030c061819050f070f0f0902030403120e0114011502010b09090706110c03011d190213020d06120c0e070e10050d240501030c0305060a050103 74
    0x42015130403200301b0341c01c8169521900385108100e40103580c54000b1501c030182411401400c000a01104400da00c94001c40803900c0c094407600803040c0000122030382407c610706001c40b502d52241c1d1040d9000810b41c072180050030701c2150313881c0c00d8190a081d00c0d0900e4800341d000549004011540500d10720440c0b11050700b001d00c41200d403d00000710f242141806048401082c0d0100003c0001c951010402941c280240610750742c007503403800c070181840c1000955030720042c814101040001c02d440050300d90280b1140f110020000c1c0240440e8040c0e280c008000040702d080b41495200742c2c2c111b071211060702e84204051b1078004040400718801c60103218080c2d802281d02000907540c2e0100400c544004a15407010540140c008401190410391010008030024005c541030240c924580102641c0341c0e407000c00d4810300c0345440d580358103400b4201005411105d461421900071841070382c1b0007181d040a00e804540c002d0740c081c044240184c0003034003200d6098820b250094005e55050109500a4000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460734010 1250 460732760 460732771
    0x3150301090209040606090605150406050a050d092f0a03020f01090509040f050d050412082a1515060906250b0403090905090c090417071103010f020c0303010b03 71
    0x81444400c1e82e002418a40f4100c0f01110348640e00e02c0300303010032821032080300042d00058a40701c95680859121010030302440c441e040800000185030341981d4840e20a48600424021041c0034800017807610080441c2440c85000c14041c044254200303d8081c1d03240b00045520241c59412080d00715003e2100545049009070f060041044001a07e901c0d40003005101d030b4081d8944c00c030030700e034076182c61800c003200f00012104020060000f4000c91108010a1108581c020a0305940d0302c00c501346141e240b001201d1210044001a11140c1d0100000c0f418002c0346042c60080100b03a40c41e200c0c1c82d0b860303400c1714025540001003401a8504c03030a119000744a05051030408090aa200311410040020803410490307910070380c0301c20705c010140c0182004000d45a510018005490000c90740780c0c1e20307560300c0c25442c400e8280310081010301c42c0010b0f44410100301a100b071692610642480811800744107400ea000b036103001599401d01c0f0303085c4283d58001d0f610402451850f444d20408070384a4001810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460735260 1250 460734010 460734013
    0x105070f17090145120e0f0a09090209091b01030509011113031a070c0b060d050105070207050f060306064005090609191805010507030617070605031503 67
    0x544000055100b004202411200c81d1300280344400e115104081c4d51503003010080c000004140d0700014520740450000301050f03d40740320382c2500b25002610316400c0284a6800440003080891020440d401c840400e60090b1106002500e072006140c1d528840e0700f09082c5207104140034030140758481e42000c1e4000500000104005502c550ba2004170745c0101822a044405208200208941001e01030041a044007007044a89440c0a0140c0070b01210750b00102603c00c550b0026035650f540c2c07000f1101160b000f00080286150002019640345814022079206000c00103000d00c0d20b107404d000312403003030300090211402d16885520194100c04c0b030480c04100c0303c031488071000301c14a42c055440b1520480d90580700020b841d102c107124440c20b02904841c0070300760316010051010f41403031341003407402c94407040010045d0b0380040e1000e801134100b40042c074550900c3c0901040b0356140c0c00460540304d10710b805130141c0845046659461030588281004110103100041544101085503544410082c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460736510 1250 460735260 460735271
    0x1f030b0a0f020d14100602060702062d01060504050a0e190506030a080d020315030307030e0f0a0f0f150c0312090c0b07050709060b1201120807170703020105070f170901 74
    0xb14241e040e12210350a410111840744d0070020a0390180200d04010841d50003d441c26003460b580080d1a0000204010083d44810400300503103036080400b000800483c00364140203503120000240207034081d03c101841507034501c4000c09d84008210501d4054003090141480d01c2e910401100060304005001d9681409080e41c400041403140c8024403c41019200040c1e503882d0983c840b4a403218010100d9009500901048000a0304010010035800048031449070ac0c3d0f805d07000080c11411150080319840d10b01c400009212003203002440b054400da04914031b9090300c1020101c2e42908009000380000d040c2c0101015620f1040d8030101100703000b07801610040381c0750301002c8440e9000e2601150180d0040d2800c00c0000c0e514403828000d1316030f4010040c507142e081e104000130100c060083c01c201041c8404d0440801134840212620a0381c480d42000c0c100c0081200b45d9a207070001c400a90140d400c0800240c0018850b01c2803100c0011203131104200002d005412480c0038070010841ea22139036955 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460737760 1250 460736510 460736527
    0x302010b0301290d0f03080610080c0a11160602071503090b011a1905281202090d0c060c05120301050901090f0e160513020a090e0702120f031f030b0a0f02 68
    0xb20405c0110700903290800c8a00b0b0440c2401003003010400c04804000881060165081013441220004001d51070088143c01981489505011104800601c1080041d100080c032540119100d001c40f904c030508080c095000407002d80a44d50910001007803454043c006000800008102120400d0784c03030162030900c01c0e4411028025848218524045800415804a8002a00d02d080b040b581c00800b1a400c144288401408890034600c8000b601500881c4035202034949030b0321204a140c00660040d04a5a119805050285400410380b80ca0042040c801046080503040380d04944015181c10500e030301e01522880142030724000e0807001c503254000d5451a45040012004551088030100d40c071038504010001c0c854212540105100c0c0184515004c680d04048000c08a0f0302500540780349903200d80b0101d051000024121031080400b088900c40d21000d400510b220f03000480200508000015031080b20481a1000810300031400001455a1000e5003118031280700c0c4190141c1014110b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460739010 1250 460737760 460737773
    0x702090103030c021f0807052503030c110622020f090412110606030a02090705040f03030806040b121c1101140601031404030f0c0f120207030302010b0301290d 70
    0x703901c15400604407041038402d40c90301d11101e0b481030004180c030700300301e24400902611100c001000b4405104011803803181c041411118003034440d103070700d4005507904002e250140040101c00c00c9640007c80300c000703da640100000790103020b007581e0ba15214100d4414141c01c10842000c80040f030f00304030203022200b52074884c0ca00b40e070700981c458094151441d2180c00e00410000d5000d00109695004d00c082c058581c5010a05213034590301656100c1d0782da07803034900c240d816214075480041c0d000d01c4131a0002c00e2690104056020359021102444161007500401851001064610074680c100240110524502000368038803411a400e102c030050070b2410070b43d400c42d071821051803004460601040321641c2d0500c80c0c03c0354a007156003ea806401d281d00e00410840c099230741103051103030341e403c4401403101d81c01401182581c001c03403800c00281c1c803100003074a5410610003240550b0030041300042d076140600440078504111a10b1001c103144020310100042c48461005030403c031100722483c0400c12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460740260 1250 460739010 460739029
    0x7110c0910090507110c0303250c0509040305040501140910120605041103060a0512210f03090a0308090d1d042003011403011103060d1121070b040b09011101020702 72
    0x461301c4141124281301755081c20140700c2e80009100750070410140340d08280031040c0501d031a0300e0740b000c0c054070311540c03038641ca00f042942c000580c00142c4904210402d40d02400620aa440c2030382e0304c0c07492190340110f544407800380b0032800e544455001521107840f0f201d85142480000010b401084c103d0313580d00070400b200c455440d850f4581d84000200030711401e01045d80300c001c01c010f6500112000070b83c00041d03100c0422000030301390251500500d00080b01c6890a44140111400034542c2e28204a4160f0765205660f603012008141804001030300e9460202d9000c17054405910340d00e0b4442d48a003454080442d00a607216446662050070f190080f035900d660402002d01c1c130000039629410400100d1113007680c03008541c0710b60b0501c0a58170104880d0801e49402c885d05407400c0407910b0191a10009910014080c02d800140400740585600c0040c841c10800071101819180700c662160040415803143e03000d561034041c0c1c10400c80b02a0352090f000009d80040107030005040c50300e1036002981414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460741510 1250 460740260 460740271
    0x30a030519140d0e01150b040b1c14010312210b03160306060f0f0b040e060d060f0c0f08040b040201050307200a02040f1802041113090e0607110c09100905 68
    0x40d0f641003469804c1c0424840c04408000c0c484a8011642c50321a9581051085000d002001780c03021034180d20684089041c81ca01180c12807041c0404905a00342408030390f804d100558111190000d4008824040c41460310f0010500030b00c0f0740e9100401c14800f000d0510b45554941503c40c03a020703005070594200d040c03c00f4501c40c49021a03207910b0310000c07044102c00c0342c014803040000c40100304407095880007202d00b2940fa11030a0150350750360900040703500080b034034083c104a00b008022140c4c6c00d000d03031115280b0b45168071081c1591401441c1102d4403607048900030404070340500131a015600580140d940560207103000484840d200c2c105c826a84007006510845030300c007118100c1149451300400203007650102003000542d10104010001c1d0f00f600384064000d0703556000481c00b0b50f0341081242c0c0c4c0084400d2541743c3d03c07559081d810004014406005d0000c0c000c46002c2041a446410074541e080b440c580108a00c00d0020304101540b5030207000541c1d00c0002135800a03203020140035641c0320303d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460742760 1250 460741510 460741537
    0x1d12120a08010806090601030b25021528021b070f080601170c2211030f010806010510030506040f05130b0907081b030f0118060b030a03051914 63
    0x382608000034080000c181c01c0700d80c040d0020700410081000000d0603e0440c0d03040030300d00341c40341c0311a40c0340001401e110b24000c8803400d00100c0e03406043d4000481141c102e144584012095032042e00c19099140b03078055190301082908030506000c00c06402078180091845194141102c000d03501c14900421070740400249902e00b4010040c4650911981303004000e8014110410300c0924444c0e9242c06ca2510041d00c580c0c2c5c0d0900542c043c07045440309021800310742800f000a9508580e0000d003903041241c1c00d040d00304c41c42c000400d4000001c0350042c100c8401602c16507103042c280c0400d4004c1e00c0001c1c081c641103035031540040c40c2c8003001e0284a00035501c9101500c0b12140c1400c1034803140000a081488503448060100304150000580740d400c0708100300030b5140b6514070b0300080d00345412103030325013415820020700c5042c210540c0307d4441e6a6101d038000f00110313044441816111016010080c000c01ca05100359a1140401900800d030701e030042c03400c12031b40307084010915069000902402d85c1c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460744010 1250 460742760 460742767
    0x1a0406180608010b01090323060a1a0d030e061b07030c03050d030b150f0c07170f010b09060d0203010b042a03062103050f03240d031d1212 61
    0x30000c8a2003a0030141000c640248400c0300d220300013070020340d80b91000410020b4203030f04c02c60601d81016110720940740908141c40c00d5092400009003c2c200c0e4040003400189000c0901c042c514021148442050745034540f41250741c40c50381048040d4000c102c115043d5105000010200c003024080d9001940c4510b00444059046040052410251301003800034140340c010b6031941556041018030403d804005c200d80d5503140300424007124000d205880b5102e2040d00004168100190801902c2c1c812040480e000e80d103495006900b0398a804032225000210003002c40c110303061280402c1c885900140012844440c03480202d4116407607000e01024800170746240e0301140010ba00340a030500034038902440740c10b0802c20030801c01444c83c3c070790000034500c1140400400d401001a5907c0300304020500340c682c07416480350341103018841e2615000b41c0310300707180b0107880c5041d0041c6140690159141d40c092811004150b650180300405294480c45001d20203c07011001c120114601e80030040d880d89 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460745260 1250 460744010 460744049
    0xc0c09020414060315100309151a01170a09030c0b040302060a0b0a0803090423070f02120f07060c1404060521090a15090f060207050d09050a06031a0406 67
    0x10038074410750000d01c0390700c00300240000400e05c80b140400a0a00710703207070640030128000690003000b5007600186081e1584501c2c4000300520340c0070024605520b082c00000c4040a401142c1e401e030096040c0b8183d400c601d01250904505d6805805028130a0806207a4a059070312050f00c90507080354200d0069010204000300c0a10a020f641c3c44001c05079151081d1f40d0811208545034058014064041c5542d180a110400714240e05011001040c4c0705040030340c10401d400611090098200d0005440359000301e0011300c80c0c0104444100700d040a11500f800320a17520a400340034841c609804200c00780d240310818005082c0240300404494035116a1200303450440c02444d0501e07151070b03060a64640030040781000119145040b1a03100714000c2c3e500c40d45201450090401180190000300c030581d00f6400c1020740c1e4024070340742d8010803c40c0e06903003d0348800c0b00c03010320a00074107070041100701003002070368026045100d0250b074454080c40001003c0d400301e012200750b580820714020144002d2003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460746510 1250 460745260 460745279
    0x8010c09080c010e040906091e0b09070e0114150c030904140615030a020f0d0b011121072d020a12020a05060d0212040605070e01020309090a0c0c0c090204 68
    0x1024581c0280c04000726000001e0f00740070a03e00c0440c021500e07200c40c5420010750307612003141e40e503000c1d9801801c008031000c500100d201469045039408070300c1000c00c0090000254503000c8400c0002e1161050703003070800201e00b0401e026085038000050300210000c88440f480a844071404c1c02e4000c40c1c49503507220400c426940c0f6180e4820242042ca000d00a207500d0710b01d07c29980001d0304034803030b580361136101c1080000d210380410822002804a40c0d140b9880340741d0026592400c2c00d90b105d4280301c040803142e41c1c8a2500c1c240c125012092152860001d5428101411566000d07102540c002c241d0303032500e40840781d104d0baa8070b10500782940582c0304520f005030311100542142e440e02101680c8503408541702c1c070384034040c8034403d24000c5412090b072280c40e01103407058000e005000f2400c1c1050b20381000505000c3d28005e001c1000302c00d0011040d40300200382d480c000d00051251002e83c81c0c114402004000d268014410007116a0803100032900c1400c8180081a142d20016035803031030100c591 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460747760 1250 460746510 460746527
    0x90906021207020c15030405210409060906240801031124090102160f210204140a0605011706041a03030c070f050603070c030809160b13090b03060703091a0108010c 72
    0x102d10100510600000c01d100140b82440d1000c1182c064981d04101c1c49c0345051401194802c0c501c150070002c01044114036500080102d980740900d000100800c0301c56504401c9040701050000740d00c4100401c003058202d04102181d80c00a00966500241d0345007001d00103101400c0a103000800081803041035904000b10050b000302e02d888042c1c01c905080015010b00c00e20302c60010040c0340f258529088040610464041d03980c001c0040140010680c01c208400600b150310782540d600c0c089000803e03500402c401540c4480d0701010204c141d6481040000810641c0c0c0c0e024070307014042c00c09a00c144c5040004100000c841c0000303010052030b15030788460700c403401d8100e980035a02c180b06000c034158120189203100359041c00d08522555800b075619240114800c4515849036002d00001540c01300030005003004500c0c40e214a50480e00c601e4030308203854801e030075070350964408400519114031a60144242c0351040c4800c000c80803901d040c40d240100203801911035650744001207940150001100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460749010 1250 460747760 460747789
    0x705060103170a0c030e0102240406060f15050d1527180f1515090b06181306030204090b0105030f0a0309060302090a0b0706050925090906021207020c 66
    0x241d24205041100070304c2811400c07001024006201070401c03003a802031020140c5801c001e6070071100c4403802c240c004032501d42650b0607145070f0b151082c0071072080d481c481644191107094140300d100c3c0800384011a8181e11074114040a00d65550010101500c51003000c402042e42c044005008005040310382540c101004851601d186440c06e02d56200038000740440c007054200c0d1017040301c2180c42c18030700910610f20420750300e05407074060002c442c0500b4a201c2000d4580480c001c10240154505000c0719200c0c51403130140e0b00c2d034102204503062908a03180c072403100701d04a001c29401c0c1e40380d005c03c007078446014007219101025030052007281001c210205031800c14000800c20341c001da46020f0314404050003001e00f056000203a001c3c01c0e0b15003c2d110300049c0b20042c01d80340ea90710a030030904020001500c40e0b407400d024600c0b48038601c0d4403000000202c0610f41040c0003116140068100040540c4d41040700d13a69000c3c03000048130140700090320300c510b08039000b822041451104200d81002c21484 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460750260 1250 460749010 460749053
    0x20d1112010506030709090807060e100c09080a06090507031203060e0a021e030907050603010306140c0310091521060b06180d03050708031e0601050721140705060103 73
    0x410841341d800054001c1100c03506503000031201c0040c10108600c0c1700c3e01c4c20241c1121b00f40f150049071104005100c0301010a490b42c104001420820111607038400d62085842941c0854992404144154051921544688101d03051580d80b031340c415000700118030340c101c0840d64030182007212800001005070301c1305805604600e0010f02d1685554440003080d150140c00744040002440f4902c2041585c0c00383c8030060070561a580d5a1a080c0c01601d201c0c0100c209881d00d1001159090283e1415039002e115200c5c1c140c0c944071705050101005009102c81040c00c459003c0c1c000071003100700000c8100c03110340c0d00580c00761030040d424000141c1e002014000e0007001c0410642c032009030560400d041740706044034000009000e40c142150079014034680a020700600005003d81d513030b01c0c2d8011000015011680158698541c40156494080e900707010705102e101252515010203064244010a00d29083c01001c1c801d152121100e00d40000e03030304651640c4810010301c01d00004c1900c00c1c514841450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460751510 1250 460750260 460750271
    0x71a071206180509210309010c0e0105030c071b031401061401050426030a0807020c0613030828050d06051e1c05061e09010606081303020307020d111201 67
    0x1c42a4450034201c41c4001d540503074490125070450801d000e4030300c416007121142c00712642617070310b142c109034802c5c3d80780001e640c80c2140101005000d0300003070072810016102d480c11a83d0300c074440304c2540d11004007281c0c4000b00d480640702120700c5500501c0030318016400c0704c0300f080c207000a113070844645800c4106040303160001020f4507179000c4211000d440b5103d00611b92040100080c030f0802c82c154070b0703007031042c040420b44224280c0e206402510804d160b500701c52010507040300f4030985228050840c201a10300f014280081050840140b500c4000809801195140a200e41c90104110540754002410001e1a02002c3e4104d0281d50b01800e41111459100742400e480070007041c88a02245018515051040803110f02d00d40800b420340303030004185c4010b4a0003a0208074901c41c0c4080405030390418401043c40600144030314410349406417912210380c0c4079401920f0441c4031085c012411440308010000058a075000d50801d05441529023810562a281c04c103c8503200003407202006a00d4403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460752760 1250 460751510 460751519
    0xf010b09040b010915081605070201020606040207030e03070906060201061e03170d02041e060c0f030806030a0f050c040b030a03050304020f181602010b030109020906090606071a071206 81
    0x40455810300812180007900b40034140060b1074a01c41c40d8019000074000d2490780c40e90a4100300d40510449070302d01414010501c2000c192081e0040b00d6002c1c4c0107a1140c400281603007065401005020f0080c00e0020f030a200010000e441c0c00416000b000403e0b855140400c1041d4090251602510038100e00c1103211050481c002d80205080c4805801c900004004900700400602212000206580207540e02ca46035501d07001e16031040100980c160751005000a1824410008155442c0d80704011641d10120b545086440309400741030a689401014540c00001e028a0a10303001c01d0301c201e02501d0841c0c00c0700b04100c2144c10460200380203401000903000000c1c0e014040300c1d8051740c111208001c140800c1c004c15a8586220301380c001c04017480041c450b415080342e40c09501c040e082e600904c6103200d035005143c01c1c1d6514010094200314035101081e101d24101704540d0b8000d030064096400c00c001c6440c0c107100500ba40c41800007500c40ca00500030469485a50f41c0780d01d81203040240b1079140740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460754010 1250 460752760 460752779
    0x1020d030605061608043c0308180102030409021606060b04051807020a020d0f0204051005030a02220623060a050a08060a0b0a18090b03030405060703020f1606080f01 73
    0x4510241112002081e8140e08114a42040d18080c02034100140c940d40713411100315060302c920240603840e00c0305880380c10082900d87c48030482603d501c44075040c1004480c0c0ca90f80b02c55020400d1150640c0003d000c00301d032411b40e40c0701900000040b0081ca10350f18406040070411580260041d20049104200600803601d4842c290a0b4001c04103000100300e5450550482c10010301102c02035105a0b9207410780300740721400241441c0c0358000c40d800c00c19600c6480034180b480d88240310b03040c0c06070407400009016207000030003c0d01d50b420250161502c945240c0d0040110744035500031240c810410080c140c940c40540d00003201406041d03074010720f44182050064428010302100c54104410f8800292054a402c2505c5000f4043c0705c103000c1d00d520529034007414000d201501541c820f03200400014810025005420114030301030b000e1403030035040c00e060100301d40c010f03802601944250440c150a00c441040f0546200605500c0d202035241851030082503444094070407200c001040c0c0043c0558440c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460755260 1250 460754010 460754017
    0x140901020408062e0e070e0103051009020a090504020d051b07150e03070c0b04060f14070224070605060909060f0f0a060305061f080303010e0c03190203130201020d03060506 76
    0x4000c0ca81c80c50907902c4210703055034003404c0808480f8029041400041c0a002648031030302500b00d0b51643e00040b90004011021036504035000000d200c0024420800288168001c0c0655003591510303150441d150b00105050741d02a0144c1d0000366038801c00c011114400c5500351001c9607100c3c003035a1a00400b5118401c0300f910380c8820000c401d03a50700c800d0051110400441d100281c3c0410011006941e0320a449910f0700540704d50408103c000701642c02039880b50056400b01124807100d01c1c1007201a40900c001d0800d521010130010b40d2119500c00702c0e208000290250b80d204203400700345854000140641c031800542419001d80c400000d02c0180703110261481d03484044120070290596404440380082c02c104e5002409601400c01032205402ca150004954403100f000c04c003900590342c401d4156284000d200b6903400c0b1101502040142030b9807401542c104803000300c550030f0003980e0300c56401241d006913415102130113103103822000c41d601032201311115203c0f810200312051411022511611 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460756510 1250 460755260 460755271
    0xb070510061e1509090f060602011a0d17041802040f050a080a0b090c0a0801060e090718020c1f05070305061f0c0f0b010b07151503020402070204110d14090102040806 73
    0x403d007041c00284a10038a2403a000f8203d60505020306a09440b0f800d00030300b014000e40b8019402d280c2c00017a18910183e059151560142030070f503071180581c68180c8101000d410b16012458100310005420301c85660082000b01400c5c40141e0b80c9140680018594400d544139500650019030300b0800e03520003140350021281c11400d50540c5503500f200c1c1505003150840d8656100c4078026021070301460550040040d281820141a010b07111100015911a41441400d201480901c00c01c006920030350044e00601016404486041001d5482d5060343c0d41d640ca03207982900e90382c0e4200501c10381e146c028160403001c15510f803200c440307464038009100e4199660020606c1020043c143c1001034020840c101e0302d07002201c8062550f103451101c1c50a43c00040140c03492090105405510035281c4030704c4c80401d40d4102c4040c00c00d483c550074807010350003440c81a030740039a42d15108280d102006000b014060000000000c0c0e062403128502040c40d000391014030107a1050000f030103491000200d403034100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460757760 1250 460756510 460756529
    0x806010b0406050304031205090705030c0301092a080a1101271a09330a0e010e01230913050105030a020603041e120f0e03060406050705040b070510061e 67
    0xa503101c2c1802e4416044115880c03001b140b404e0b040140c0380100ac1582c1d000d0f91022416a6210090081090300340c5140740384c080c040443c1e10844850b0b51409401c070030070680317600c4180c072801507883c0215418407025080c2510b41d4072008031070382c020f581d011030220503482c4c1c0c8284804107880d1006032003801203944c0c018891910306000b400c10040b642d441c241ca01001c0002c14400107200b43c20800c030600c034010b0480c2001e00f0903007c4078803901c4004c002501d18010705079592a011121103c011030360003884030101410310441140b49240603202c080300b0034800030031428180c0da4075580410f100c0550410140300452900c1d10006008035900030808510454040f03c0080d200d807a81d0906030307280003854000c10110980c440058003004a942098501481c0035140c2d0202c12607065802c6c1c4945010800d426410340024000500103034907070380082c0d040b08603840c02e603003040d440e1002005140d01c90901651140c1c840088280c1c003028500030344e4040c0240403440346d265110b0802c0075400012314001c55000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460759010 1250 460757760 460757767
    0x40c0b090312040308040e182e180b061e090402061902161205060f040305090d050f01050108030f0307110a02060d0504114c02060108070806010b040605 67
    0x41c1d4040000340519081503504903907840d920324040c0301a901511910b0301c0089460001600c10700800040e01100e030b58840985410680020160054182041c4820124800b00483c201802051082c1200305548a201d2603510055050004441f4401800c981c45010010800142000d14420100b141401034401d00803540b101d100064150241640704440a646a03e5441005900107400007103072000840c0c40344503507151000c100e243d5030102c101800c19802070020035610300310000b00da40d000340a40b03001e070b003002e030560001000601c19401c1511103901521001200910030300c01c060051070401c000314944070081c1d030510414000100940300b400325444040200c541c0034000f868110303238001c10f03081d0346481201180c0010036013a0740c203480710405c219484015080c00341c3c600d240d18001202c69a40c0c0109114658007203840c00e0b12400074150012008205244442c6c0c9c2c0140d101a90f8002c0c0c00316604042d009807070310545078440b11540d403104e0010801e000161080b41c3c20b958503072405a94 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460760260 1250 460759010 460759027
    0x12050606070203030310091803141c020f0c0c0a05030703031107090f020301060e09070e2205040605040201170402010f200a140c0402130b0a09090516030506030303040c0b 75
    0x880e4060141d000e50540000401c0000400c0e00340384250542d034065908000c44c685c0c80b900d0f029001d942c520000c004c94199000941d41000c2030015003c085484501080040815a1040240e811458002c540440041414403076500184a500100c0710141c0351060170510705000669500b516102c081c05101c00c048060368800b606000c00d402501b1841418454404116400802944244143d0340011440e80e1045110b15044840360f0081415654031061200c840003000a007503500140714500c0380c0c1300e1444194043c00c1e4001c040c402c0e40100c00000c0d841c60320380009030600300780490b5050035aa100e0100030050f0303003003d83c10354000c94a10b0318003080440c05070600308118940c8112030342807180a1001c4104010025803142141c0e026050300c450010031801d200c1a802151555800002c42d20018021005000e01408240f042031401c0c0098079075610300c00b8100c600c246c0702a40c9840c04802d070f4403100da0b0903006007604a039040d40110f1a5180545603014202294040d106ca4042d001942c0607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460761510 1250 460760260 460760269
    0x10020303160302090a0b1b0d0c170c06011a040801050103050604031404060c1118090a03030c051e0901170a09060b0d080304030315170604120201022110121b050907120506 75
    0x1190501b80d03030116541740342c2c103460180240d000c0440444440310460160450ac546060554440640c2c0c1c10041444d41d0034060707450584d2424001500c00040b0034003002030440003d00400d40203500541c003414040c206420000c229840892601d1107180042004105155100b06900c00f075035080800d0040c06050358002800d4000e000512000e036219910611071000741c04034440600c140300351000c000c0700075802810ba826003d055511b100040844107181e08406500c03000f0710341d5000501d030040d0360204011104440135030035201c030304c2c0c655a034144100c00c000c15841242514003085400c070103098100d42e039518003840000c1001301003646800320b101c4030340c40c401586400341401c003601c4000600396003032036642c681e002c40d03040c0c4060108018540c1300d0380c018400c0311640f07030308001e6401046865000b806a2010042c14030010400b03034090010f41c00d0300c0c010f8880000c5201e410030a928140d4601c1e0ad00050003242c10161141c1c21003428000300d5500304d1840c00078503000350408070b910b0362a800000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460762760 1250 460761510 460761547
    0x2429060409050405010e010b031603030c060f0216030e0a050d260d0209030709060e010e10080723040c120e07030f03020304050901080706020d0503130210020303160302090a0b 77
    0x51075442c2440b090000300070040d00258110500795000300807a103c070004240e6181c5500c0c40c1c401c8140e110110601c007091080500410740d6000d0080400c2050202030303100700300d0b40070907400c0401d064440d40d40820550f000340140038090b8121303225102036041c44001009000d482c1d000902180214026000702078a645213441e285c1d806070b5003039840b0f00d801003861002c0c1d07115020781072180c05454400302d102c0c002d501c02c035015142005813410700c507030920381030261000c4c020b8090707910302c000c41d10b00044c450000c00c0f00e6409040d40603042014120380d0448005007070100d1102ca84240e0501514480c6261700150104c0c548401400104402c00d0303031860b42e4141a020341002d400044070040d454241600080108211101a190307010142c0c0d84be00005d46440702e502901006802c01e42800001131b20a03009103410461240941c44c010225a002804051412850a000da080441003042c0030002c3da44070a8052001e050562805511000003603004001e402807660600020503213040003801007542c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460764010 1250 460762760 460762769
    0x8040e070c1b090605040e07030f0203031902070e0a0212072a0803100e1b0703140c0d0e01180b070516030f020f060702060a0c02030c060724290604 65
    0xc0c9042090000c003989101c1403039001d05010fa506000b8000f5843c1003030f10480d03a44040105c05000840d05603a601c800c000245102030341e152000788426050302428150801c1080709540091109038500b034048251008005c01401c0841d10501504003004900c40d07103181d22180c20b01c4c11400940c00411200b005c0c101e5161403c81201246000b042001500e00003940180084040b02026559909010806000807180c244800180f1880b000c10390b003000014001461190a1441003c1e031042042c0030150800d50501903940d0020795511070107600140f4a002480081c60005001c8104084c1c0168100c841d1158600d8a4000104842840010712045841d00311600c51046075aa482c200f46e442817804050692290030880100c1c0355515014044682250303010740401c0c14042020f6040c0c508104d8210140c0c0c150242d150100300396990036004100b0f16100b540307990030400c0701e0400035016001d40c42d504103250707180c070f0050145840c49005801e5005810715104400300b44800208489000d0380e0700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460765260 1250 460764010 460764023
    0x80604110c0f0111030402010903080f09061801030b120d051b0a0804081002030f0a020a031103091b030607140d0608010c05030a0507030506090112140d08011502030708040e070c 78
    0xe0480341d6007000b042690301004598028404a441e0241401da01e1005580007804968017800820000705000040c3c03503c100c445008504080d1b4030302c080b42c4564010903c40d500d80344030400c031140780e40e014070a888120b1400d48003607480f0b003400310085503207180b1420350b141440004105210355001e4400040113081d510010f4940c12207042c54080c107150440d0244004074050202c20b41c01d40b012074800d8034800c0120a80b05420380d01da0f100310000035400010302008140e00d034011480c914464034020b50254002038010060198524031558820302030301300d4240319420403400d01c8009648103500c00d111503688084140c0c2c0307082c5022008014410380d44a8003c075400d0046240c0515003000c00b451180919070024060382e651100220103c03082280c50b558400d030000014000d00c010070259401e84d0b403043c100c0c10403134203411020a2504022a40c40c00001c2c0c0000014411146442980450710b03015000a50074004a5136074285180228014150350800c41030000b168640b1844540110941203079 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460766510 1250 460765260 460765267
    0x61826010b041109010f180504020708092110060e060405060a0e1e060301180311070f0305010e0c010c03020a021903200405070c03050414220b19030f0308060411 71
    0x84070f00b9154201010321070100700040541c0f04103e000340c1280c1040540204517146590500c0100002500108420746410005000c5041d080c1c4401c102084020b4020b0411000301032000703a0b19203001030074520840c0d41814000204001034800c800c0c40d401110407107003c203081d903c02002c540e13403883d560712403480e29030650107000c0c44074440f15001c1c0752034000b00744104e065950041450700380c90800c0d980305400c40808924402191041581075501400e10060700e0307000340e84400d20038501c04643c02c140c426035034072070a10303c07480750401440c0075004080c00e00e01d08120705514081c2d112914050041d00490b00e11407104849101d100c09103019507441445210b0540c82c0862175540381c140f011141e4010f615090200300564081c407410301702241c2c9599804c0c645800d01d410200d00c0c0404c00c003800e8000d13100300d040d007a1104984e00c2c038043c20340c0072050018050805004129281a0b000e0301c03142100c1c1700030801c3c004901e035a0440349416070035080c00401a1078140100d0000d15042c06070303001d18075021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460767760 1250 460766510 460766531
    0x20c0a060b03010f05040510110c010207240b010903080702010e0913060c140a0e030109060c081501031104170c090a06030b090f1e0c030a060204061826010b04 70
    0x65100341c40c1a074080c1c0c000c2064001d0ba413000c0d01121420790703000c0c0c060fa029000c42550b245840c0c011000d55600881018103000140c401075082e0f0308520422544284a2540b40d2002c1304044082c0c164542101010310050f03003454000790030304400f8080900fa206000660400b564002c08400c015410045c209680c0d5150440c03120f01c0c2e03100e505808448150a02200038802849600013054000c05282e00c20f143c0704030610103607810090108050740654a400e24071001c6442889800c05180300c54903145102e14040300452043c0208141a50505285c001700032540109034050382c0a44191148001049000062080c60306040410940d44185c1d04410401e2140072600200304482c42070f50346003010f480d220512038a500741244414a2030f848868a4406610903142c101c0c0c04022402c02d0307900680841020034100b055601c0207403000b940004d1b08204060b4001c4800a044425081c00040142044125401d90906c646803200c0042da0f490030701d0518900313520600c0107600040081000d190b070b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460769010 1250 460767760 460767773
    0x20708060c030621030f0a170f0403090605031e0403120e0309040b0d02031c090909080a0815030c04020a180f170a0c0330030f0e0c01020601090b04020c0a 68
    0x40f01d09500404002d052814190303104010010001c14440c0994148000c4000743c2006402c5250040c0400c00b0805462594121000d1464052040065a010186054240030b043c000703041e4010000c11104204000c407890a0180501d01e50a51514461190722a802e007200e501c822000290440d0307251990030700300444c00000070480c548094405100070303a110783c05c0045824041001030740541001c64204641461060f00c0c5a0001250801d804103580303401d000c50450740c0c10f84003211056800507100782442d800c4641a41e00c100b003041c00040080c40c1c0f034017281d1a0240c20311020300494010070140700c2e403401040c0c10b108c0c905000d80000340305a0b035540c0c00e00a0540902c103005400c82103540c031020000300400d29802440e0410081a286880e45e40c5542c164612207107060b55001480d0718040e00d440d0b90341102c031696802613070041164242d00c0a24802c031446551500e1a9500c41c0d411a40f40740d8002c2141411181d54940005400c42e080d008640039128111103107602d40981141c80081011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460770260 1250 460769010 460769017
    0x715050c061f09090c05040c031b020a06061a180a050d0602031b0427020d0203041a0105030d1d0406030c030542252c010503010b0703020708060c 64
    0x4400c99124a10750383d00801000c4070940c1c1c00c06400d442c0203034003d00c00f07424190000103103424030313203400964003907940c96441c822260001800e006030061041c06040c48a24000c060190280c0781d26a810100d02c0c003603006047c8600f9030301680349a00d0007200401c40e981d40c85200f00404001d01124441c0e0740d1454850020750080b501c01d04c0c0c0100e00c004600510a010007a86c081d18100301213030388001b03210400c64503100407130300e0402899038003000349040d10712403400a54000d42c41803000d1810519640c20b46105000141c02090180e030000c42c6200f09a903000543c1400c10441c0303680036403c041e00c1804100030b040c4917040680110020700d80007082110010301c0e032801007000040750b188903640d8591071645012500742d038140803800c41c0220040040d50045ca80c0c10070700c0102511038030040d0000b003280c01c403c0c0c0a0366001003041c0030390010700c1345803840110320105409030030710990b901d01c000007030010700044c018902c4040001c00d450301018000c110b01c002030280042115424680419000116030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460771510 1250 460770260 460770301
    0x50105090a0305040e04080409020d0c020c01031a0f06070609050f0f030a080106141909150206130f0c0b040f0501090503010506180910050a02031509090715050c06 72
    0x618200000d40c00c00d0012801441d49035060350f6691401d85020000050f104000c1c00c20355a8030070400002807642c0d01c40c0b0040c003070000684000b0400d01100750340a401c04071a60046410301d801c01180d140800040c0640d454030300001c50707004103680d40310740102d489401040e800600301880c101b090b070140580001d9480310350320f0b010704032821400300744040c0d0b840703001d810b0f83c600100d0035400060044501892400d1500410b0401c4541000e02200c13085810102e040c1c0ca0001059902c1c005000619100034103280d590030760700040400e0304144145d45001d8410150241c10201000a01c10820070541c4014008181c0d44c0a10303070716982c407007601c10740301000c0c2e10445012440c90000003403542018081d0074415100103110020510280c07c0b0500030400c0204550841d0041c800e450341d078603d8600c94a4018034404600580fa85030104000c40d1150007010a103104801442c2000b40c14a40021030106442c20b00400140c40807100d00191000d0003030001c00d00c2c03d40626010000d0b0806160300d10007504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460772760 1250 460771510 460771513
    0x3021504031e150c031113230a030b041103100e0601060815040b040b0607031d04060e01090c020304090c080402010909020415051c020f040306050105090c07110d0b0a0905 75
    0x405034050803110300604410041c0780c0300300800d0602000368113901c800740310152402c3c0130540f03c0c48101062000e600005a49400e1500c13040d052045504401c100140c002c0f041c0003041d00360320180d0010314401140c1c4802055091003038005000c00c01b0552058541d4280542199224508810181e02a06034002042e006205140c00090f0311032055100601803565405030880783d1046c0c40620003e07003503210042e5000344c0c450001307600c81c0c0c8881000b400c030380e4001d82c4d9961000017050006040b005011260500c128100442403001c44000039803030b411030b0320300040010190a42101070342180142e134400c04202d03103000340306114503400c910f1280c440d23131007640d4844450b43c480013001304a004601541c0c00001e4482ca8455080d80a0402810741000350230668001c0b801d8440c00100380c2e8000f26070521003040104081040241e0303402524050581110480c40d5031a0507035111005005188018050b600140141d0b03516840f42000107001c00d800c904000c10515041c0054005070181400803504c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460774010 1250 460772760 460772783
    0x30906030f070206060906011b031715040e01020f2b020d020904050a0624020a120f180302090708151f091202092a0a020115062d090302150403 63
    0x40c075001c88500d07c5007005131502201c2111440b0001c0280000010403000c3c0110f032103580c2034030940208114490000190345013400b45c80041031205a6860040040c410307801442030f0759000c40c022090300c68402f408454114101c1c218106121001803560040d07a88600c0041d20102160300c980080c0022402074505106c42c2e250896260116403480c03044800122103054046180c1340c000340d054541d5603c0d407040701d40210080e219600400110381c482004102d00040c515581c036048000070041384a29000a0b800a2450700440c800e6503008045508010324600000c9440b844106542000e1034064548140c00603c00b90040326031101c0030414010400c00c0d00c0024840f06400100c9402aa0107440c030b400c10f4440317176030603003074056408226030103154001c3d1b1041160240030084e0164580c00d07800032070b481c039000500a044c01c406800510401c100c030405c1c4480030b080c002103040322174440ea8203000c54018401d8116009449508000d40c840c000c100340f4907520804030060400e0720f0184925901 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460775260 1250 460774010 460774021
    0x80712090605070506010918020a0905040c050307060509040902010309060203040f0b100b120405011b0906080a0605060a1d030d030510061707111612060b0102070f0b030405030906030f070206 84
    0x541d07006040000b0b00703d5016500507c041c900b60b8001ea614400d5000b111140c401241c0e00040409445400c4000c4107940c441c00c0005002c18203107071030020b020a9010340742c01401c0010080103072141411650189840d6031104046907ca03030300ca810219004002151a810180340840e54540c000000380c40085400e03000c40c1d4400c0b2210007080c200d403080700c240d41c580261440401c1c45041300810070b42c0c003175503102040036011107004030f0080b5245203940d800498038204280a0140b41028043c210000c0c80c1031004e1040d52a6030701140c0b005040340c1800b000c07000300d000d0b40701380c000214080c00782c16000d000c04036000c59070550407450152060314004007444e51102c404603080c40c00080010b59402e071010104040038012154000031845650903680390941c1e40c044070713030b0528642d407103012541d0f01460f000c1c5c280a4035105000300401d003407011300b00306807070f0440f086a000d840780180d01403400004007040030001e0030000c1f00d103500f50141c230b0980c50b8078000b4180040c10b1011141c2c0c00241c02040c1c0000d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460776510 1250 460775260 460775267
    0x603050606030f1902040f0f1103011e050906060706060b040906061407080f0315060f03061806060910030b0307061121030c0304030e04090525051f0c0807120906 71
    0x2803c4034007018001d213100d408000241190143d61040c0e1952251000da00348800d0080052030141d640d22143e4951502010710303d00e00400c10b0341308080604820170b0055585104203150858030441d0b0040c2c03030304402c1c20000c00402050b449100007000010f0b001641c21030f2500b2141c1190b640380c4a80350341400402030405148160500200f507000d080004d5070207449000051074000114510426413010000040b52803a413003165080d481010100401440f8a8141000501c2ca002aa00b440d210b003080404500207005e0080c0c2648105407820084144070f01c6035000d0030150301d00404849140380d440b20044d052402c21b400901d024010308500f11001c500801c0131400c1d540310301d050340d842d680c2d88820b80561034101420440401c0b07038190031603040341d40d43c0c000c5121050041001d8091140400082e941c5194001c0040441f121000010030a968a507289022901e05d8480ca220f003805c0b040b04e013107a140c1090392005041c00070109442040c080000c0c0750321400d40c280e89402441645894055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460777760 1250 460776510 460776523
    0x5120a05030909041b0308180613030809190e010515030c030105011b1b08010b030a0534030b0717062d120312160c0b0c07060603050606030f 62
    0x38205910811460b030305401e007a121507500900410641900c444c240d6030300051850a6842034485460120301c00000090510402200c0b02c1d00b1074074070b40340406850340e540180c00c042c440900500808950240140c40c0c2d148400b0651001c110980d440686480240e1701180c002e01480c2c0c0590000c00d1086468401c580c201ca001e24060b65440382103a10342001140d140343c00101084400c130f06c0b0600700d00014540c0c4501c501000d031030ba07408000c045c10f0541590841d0020f4080e039109600c0f10081401240020510030881d00103c000240b0031a5035090715005107100c42440441d600f1104400001e0108848105014005540d00c0501049840c4414005000c042d214960300c08900304a202a81c2003c00c0340e084903440d050030907060042d9500c0041c0300700f0821f064501e02600009000151403c01d910340c154802c800340c800007030a2626000041901244400007071140d0f0160010400300c186100549051039170040050040c0e50b01c0349802d07501d8483c140d0744240a48141d001c046104100800c0c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460779010 1250 460777760 460777763
    0xf070306061b02130203270102031311030309060f070302100501060801090f0b03100f182604050303030705181f12020702060d06060f0c050604030503041509030905120a 74
    0x444a0091151030b051425070703050401260721400344600c03a1000b0301c4078000703148502031400c00703c0182500d0081c0754142d1040c60b008440d880e4810020420f440d00d0f040345004025030800c182c0900d030b00d05100400d29520a49070074641c020320110342d00e41440305000040c0885c41c4a075083d640c1e40c15502c4020b0040d940c083c002d04000c2901c1100600c0354040765400140c20700b41440c004244000315401103424500c00e0040040380c95243e88182c42410898016441c040040750f6000810344501c4c1c07940140e01c01900340940a0130006e90303001061040c20801d4a000d020000c040d25964104250007605582c441561354155891442c94520107152a1624001c0c0c0102603180c0c1003180202c040440d0b83c0c0242241302035649509125440258650074054024100b000300006441400c007500a495011030038216420407035503400000c00601c01003401c0d6040303581401d2894491320b0f603260105058021100a0740c665103008582024194800740900840d2000c1d0380f10079000e50b5555140d034580814200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460780260 1250 460779010 460779017
    0xa150f091b060909090b0c030a1b090807060806100e010507171c090b060f1c2915010c02040b04050405100c1409100509150c010b060403050c13060911030f07030606 72
    0x186101c4460f8015540414100b2000030ae0325600711410302c90210200c55600000d114040900010008014040c082d119a0074000c00a2800c40001000d062800c90b100080050303205038115980d004105a9402c7c2e80d0207002002e001703c02140c1112a030b0805081c0301612454515401e5004c50300307101d900e40a80e00100d81c41040d564000034000c0104440d5145500008034603583c2a8801c85c41da07c0c0d088071031091804e00c070004003096064149548440b1580a4814460240148a00c403103079244a0b003c03003803c000d000b00885000040007401c040c2805600141410104000c116021401010620380c3c41010056100d03c45001c46008801c414038202c41c00302006107900a2900100106d0b02001c9860712754500034400340441c091060000f40050718190218805407440001c4c00791f040e1150080d1000c41c00c081c07854450301c0da02c5d82125040f9004800c0f0882c1880c680006400140142c00b111100f80018481d40706419041c0e0310440f8625104203a550114107828400d008050803100c1a50f03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460781510 1250 460780260 460780283
    0xb09011107240e010e091b040e090c03010e0d260106110607020c0d0609080c1606020705030607050a051c0c0f020c0d08090108070228020306090a150f091b06090909 72
    0x401c3c4081c0c1d050181c0f1f16816441c034241484602030840d0014809020503030482506414180401854000e0300c20159120b40d040907255446400009084140d400462400d100d280e4109182005103c00da52510240c50395807100200312140c01485a00684000000b1100d40303641c0c02c0d404a840d40300b41316441d50700060054400010494035001204031030f010b100900c2c0340440b5104102e10780404410b60900d0481d02c3c980400000b9011701034003000746800c1c1d000e801180f424480040451056000c0b0105100e4045032021503000402d51883ca4143c91101c00c100d60030b0408030141c01106200b2408005100701504802c03c5d0a00226002d030580d03200040f20b042000d510015280f125000307280c034045220f07155414911020004d030809489140fa031007a042441325006140c00c11400510210040d030007001901c0010342054030b901904841182d00052042460030349030301502103440082e10f05a00c42c240301c0340b0844800f03040380844480c0d031650540c1f2a620494003041c0c5103000c10203001080e1030b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460782760 1250 460781510 460781537
    0x81504021305062202220e0702011b080a1e020301260a030c03211406010507022b14010608190506071b2001030509070f0b09011107240e01 61
    0x4a020307032200b000c51301000d0308011030117140c00c403103480b6210305013031130417100c0340c100918108030202c80e0b000801031000b40100440da448030700d000c541404140080180c07990000b4030ba118150300c40b03011003030b841c2c0440291810754801031010b90002e020704190111030305881e4211243c1c5003503001e4451214806450009020f03102503622401c02c1e0030035000c0c02100b0288681c1d1786403090149130081380505001951000700c4141c0040342c1d42c000d0005044c1b060401c280b0b005070740d50803090014100600c0411301c070315121130729800061090b560001d04018802079013042d66401034000200340c1740b6440480706c01c0700840e80d1000e801c5071621405406130b005600403400c40d920034007111114420001d111404412295030329080040c03a10242d820b0f640036000203038480e40c0d05020b03036504070340c000000340b1001d4104008401c035003085108003152480c1c006a0901c05034020340c07200e1080c804040980301002d070390720000445e40c10840c810a1081c044801c1d8450100c5c00780c540a03005010694400c070b240801c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460784010 1250 460782760 460782799
    0x3c2d131e050907180221010803040e103501020a081608071d06070c0b0d060621021606061e060207030b06061309050a0902011101020301050d0803040c08150402130506 73
    0x4281b405849855040380da062001030100964002c1c0f1221004650f69460420300080d07500010700101041450190100403800c0c0c1c20440c1d040030300d402c004103040140d030b031461100120258000360040d5400459a50300103a0440903203842807140b5190b4201f09140c1c050201c0e034010003140c50f10003252401e9041000381003410402404a800600b10900e0200e0310b4490040c042c0d03455100c07003100c20b000107241c010507486024141c01840f85040100b100d0007000c0102c10341c00d9242404080303842d8045406868483c000301040303507040c2c005001b0400142c07034108c041e0180c6030000245d6912401350070002521440000c0079400c80b50050040005a15501c041001c141e10016240c1c2c1004220b40d000700e0082e4451045c24001c0d4001c5000044203c290320000d0310f02e0300a810f8161869106100400c0282c48102c035442107142d010010598aa499141c4240715100ea60003001891050440c2e007902d4003140803440340240d000302c1e00008420900e030700c130000303990040b50038a0f00030381d82841c0100307070580 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460785260 1250 460784010 460784017
    0x10807110708030d27120c08040e040b040302120f181f050408070b120105010f1103030415050a18020f3c2d131e0509071802 55
    0x404100350356045075280b03109807640d00103030a6820f280750b80d03a20200c4001318074151304042e179604640e100c0000c010fa071142d2104070420b20a10040c4143c503c2e20104015020b0101ca024100340e0a1018a5040a041612480780d040720110050b124032a18814010a02c2c0d00351f0703240e0481d440d4014034103000024a6082c0d19034001440790000003405019100d081482c009412485a50381c4150320b0f686031000711450320310035900c00020030714100046000c2041c014001410740d04282041840040d40c201c085840d0005803102c0300c05c1340008020311040001200c1903442a5030390326801d1010362200022001111600d00382006000324010364003005082403801d4225401000341000c041a0b00354491402d130032280356802d0031080900e011400c880c200e10280e25030f600ba003541d000700303640c102640c0d01200c61490a07440501e903041d0b044c03084a55a42c90030b4034400e030070302d900284000c2c11031034441061440c4606545480342d04ac40005403561000040d0340b0110f0752810302c440c42c031401c5680c03c0c000030361 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460786510 1250 460785260 460785287
    0xf0e06010e0105241204061803050f0c0304051009060207050604140103091103010e160e07120b03030d0e0a03090509130b1302100521060f010f0c020901180b03010605010807 76
    0x4404032998800e40c81c1000c084d005c8585803588104440c07a02e4540502101e252640a0b074503403507a0b030000d002099106d01a15002070000812655518844088a155005a40c8040da02a01c4846000c5105a00108034002c880480d0220b907800350320f400400540f40903074001c4807409540b40c0142925503100381c00058500b8042c440c000340340022080400c2c2507811113099500d441e40300c00e11444d086410042d0500040030650324610550411403002008e0040358041140c8094542808848a039001e004560414010580801461400e840c040ba2900300086080e808901c1502000940b4104442e04900c80d68041820400400c016034030342241031800361101c50003001d2940c5160060722801c0c0c03982200d400e19114641c803440c1010380181000d00c0d50580c551624040b2040c01120b4460602c1050844000d0800c1c0c5900360040004840c002c044c9900650302c086200c00015042120100c22207800f826003006000c8902504141801d07241039203d10790008100340001f80100c0e2080742c030b00020b107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460787760 1250 460786510 460786549
    0x50a0207080d150e4f0c0e04121b02030706050f0706140103050d0e090105090712050c0d060b040f060309050a050304090b0108070201050412120e030d0f0e06010e0105 73
    0x1521a000b580321386008950b02e080028141402c001074541d0304503082005220051417080800c15004115161408542154003100c0d090212500300103072a110400544065120f0750385600e000c1c02c0c0115a43ca40001e2880807070801d103a030440d121402c0b80d007020320540140090200c3c1d4a408400c071110b038803000503411042d50612850001400324000c4924104600401d42141e5045007049428010188251001d10490035843c0d071180c3c0350300e10034a044401c112000c00c515074420b4410307160982040c6031071403401e00d4941000590246507020380399080c01448100460364560030303604940c0c4114018480b507101104002c12105100f50040294a4400c400b130340c40d18002e5644542c5103400541080c0309041d05c42001405950307020004a078818801d100a0040341020345680045c0e40340c039030852082126a010500080351075810401700082c03114112030351881804900402450720700e80b07840003181014080c1d1142d0500180c0b07681a01d2200c0e4040324564a000201301c4804404070134460513 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460789010 1250 460787760 460787801
    0x20c0a0e1009090c091d0a0b0a320106050f040b03040804270b0913060506190321020c010207060c0f02060a0e0405011a0f03040c0b0f0d050a0207080d 66
    0x100301500030005094444c001c00c8021900f851444816501c00c10f04880c2546581c1c1e040e0411540d0008040c400c1e0b5800c04415041d50f2902c0e0f0031140a4103802079001d90002014126966400440c0d200c0c403c0810618400c240c1079894000c1100c1621075445540d541d100b0600c410f000b080c0442005540003440f80510524003039a4044820019802507030340b0b03c800d403214040c00c0c10b24807503009171960403104440180321460b1007c03408010301410003020f41481e98407000900f42d501d400e42140d001e440f400750410784080e47c0f071800d021820381d100b00d6541298011203000b403c403800003940250910050300070302030300e605105080350a200c01c410140c13194081c010f813943c00350f15050014501868503603143c85001d80e5110510007901c0e03040c1e014540380d1010b411241303200724514058618443c009120203650b0380b00e5081c141c02c0c0080c00d800a101c5020000f5010343c0900e0104c00a1010619002c01440290307101a0420200c2c080c080e0094150402040740d0720314401c80398080c50703610b0250000101c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460790260 1250 460789010 460789019
    0x20a17061815041a06072010020607020120070f030c0501051503010b0306091c0309080a0c060b09040b07120b03010203092b020a081b101a04020403080d0b13180b07020c0a0e10 77
    0x70540c0030038444409a00812b0601c01c1c2c01d503082c0103e000140518442c80f4403189882400f41e020710801001908221041090b541014032440c0601d00c0b842d0090001d200e10f0800d040c2c10211000000c814074401d40c60148401c1850a01050704c0e8405c614403400390101c40c0c04440e0319400100700c0b46d80e040c00c140ea1207034210300046030074010744482201e82e641c103407224007145000012100009402d910401a0744200000911a203a00585c080000d02d401403001c0c201416400282614409069055002000300b052044c80022092485108003030704900c1c03a451004218081ea0101d0f04010058119030614404617844c200180300b40ea0301c14090005c2c900031080c9050904400043c030503061620340c13001c11940c10180307034502c142c020111011441c183c6940c3d6070281c14482d5000104d00c46454840009640d99500405410102000002c0c0700501c2c91074408140500c03901c4048524800d40d07008034043c64030000b41e00101c03c50240c06440260304040b030010480714014664102c21000000204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460791366 1106 460790260 460790269
    0x31403042f0307030b0402090c0c33090c03010e0705090115050c070b04030b070c02010c020d051f1e020a17061815041a060720 56
    0x1400c440e03066075240c5090524041c081e6050040010020510501c1c0c5d0700c0c01e00c258400c40740100641d94550003009240039000200115600403000d84001c0c82d001c0304800481c00f886245c0c2c0c1303001134107002401120b030021031704600c02d03810802c900e03081c5040c24001c0244290910020300b0110f4242404100d40d60414031580c1404080c107146030741c07458090800c843d28046504e041da82c1180c0c9a025035681d6a00501c000c071340030310300d8a0004403041c0c8030f14106a151035059441e840c54107240e40812401d11460301041d40c040c000c005881c2645101840450305004000e1004917002d243c1c610407070350007c00b400c6d010041c2c1b40100b00802c070481c0d10040403207031120742601e002003680f205004100c28401642c3c600c152031011100b8480781813101d0315080700c07200c011030381800714110342c0509004c041100c210454024a09000c0900019021062402e03e08402920324407081d1003c40000c = true := by decide +kernel

theorem cover : BRFrame.Cov 460611510 460791366 := by
  have h0 := BRFrame.cov_init 460611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460611510 ≤ n) (h2 : n < 460791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
