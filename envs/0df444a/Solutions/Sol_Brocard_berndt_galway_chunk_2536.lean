-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:00:32.605759+00:00
-- url     : https://prove2.me/submissions/d4a8e2f2-bee3-442d-82c0-e9afbf017508

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455935251 ≤ n < 456115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455936501 1250 455935251 455935283
    0x1703070204142202010e190302030337050d0c0c06050a2c06041403040f120c0504020a140d11030a09021014070303020304060b030105130c060507030e0402070f 70
    0x40d200b002240c050076084a00d40010706000c41d200ea0b2141c42c168160340d2403105040c010f0070030207161000010080403100401d808001a00c0c20402440700e10a808400302c01c4000355440f1f203d08826000503009842035894104401d00d41003815a00c80386100c010204003898880001c44469040710405030650b41040c06221022045c4d80c4035082923600340d1203800d01180c0151107241e00d5000906030401e550300100001b00420090b22a51801144030f1041e00d1509941da65030750429400d6400c215034000010300e0384410012510016001400e0035501076080c001c120002030301489010504a054a0000443c040303218483c0d4801c03001c085a0410072626424001410300c010a40032004902498000c1682032441c0d01079200815018040c40040349032401e556000c80c06500f02402c12a586500d81c841c000701603a082c040c00340b0444040781c4041c00703074103541001e44030b0650301e501c40000e0100400403000800d500c40d0f4149a031000c01d80713025980310703d07038548030310424485a0003400d108812201c2d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455937751 1250 455936501 455936531
    0xd09080a0306031101030603081206011b0b063c0a0812183a0c0303020a150513031115100f06030204050618011e02070806011e1703070204 61
    0x141074138011001e2003070300ca41c0c680c015011105180005400d0030001d01c40c80c50003940713030709011780c3c42501032524011039141582e50302c5200b00d810070215504104c0f1010010345082c011410511110b071103000090446001511000701042c1e00d800384c3c0f0380040d0344501c8100345c44d00b5090000030514901100c1c25810344081180f929000007205000990021401c0d15040c50000d2403c28840501c401010112024071251890405000c4400001301e4440220a011841d8602d030000158040d4000e0b00c51403442e443c2c80a4005002c503220b0b4100c0b0720f03113000d0081c6100e4041d040460594141480003004003a02e020900d45040c0c0036245003103660540400080543c508806402c642214905411491325100700b9030a9004138020503800100500240190521001034001300000c18100716090604890b8a01902c1801054950140e84100820000030808010a50041c42d5410690320308920f440d1404005071800e11a101500100c0c050700e01a0090074000c6603801a4010010848802c0803070b030300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455939001 1250 455937751 455937761
    0x2060408070509060d020603070c060902191d04120c060e100c12110d110909090102210f060415171507020a1502030a020f030c0306040b0d03050406050d09080a03 71
    0x14038003c44010004c128141003010154104e40d80c002e001508507600d00d68210f03508030340c0d440151069612980d10b01c02689590076009240085a11804001802c0011003541640c0c17100030017101d110b50004000201d00b00291034550a5401c0c84e2995084c000c1741815000b4124a54100c2d005001d0200e1000c40d42240394003180d6015015150501d10a5040903c02e00b118600030008030610020049140c0e0442c56500400700c001181042c9403e100c001c1c404030700744400071200861241c1d400241809403000070b01d40d41641480c40c80040d001c7c4c0c07600040c0c640000c0e8010301090301450301d548680c0c0b205000445140040c22003414040118040000c005a036241840f012a1184d49a0340c041024117101151081e40180c000300020405200750714607400a40c0014036000c0b0542e8203001c13000182000f040254021084840101e0b100d0a152040100b11418040744138442c80c580b110520000b0340000613a401c4501c3c600b41142c480b0900359030340c3d01801c9400d000070328a1400080c0c7c4140c064269103c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455940251 1250 455939001 455939009
    0x40501120c0e0f01060c02060c0307031205060d020f0409020402090d1101120e03070201200a060b120705033d0504060501090204230604030c030f030f0c080a0810030206040807 77
    0x102109042d92422410284a4140e0b44902c40c8540b4100501c04a400740130320009680c4082d045901c0c000481c5074250640e001000100d00240c6004001d0180302c4003401400c1e0040c108440111201405a000a0250180c0a0120300554446603400203650b1103074191104c80c2000b902d50889035009280040c101c00c601c40209020070b41c0307011180130140f0148568907100c0200c80c015450600c8a8006540404007105c01e040381200070504825890814005611814402d200105074282c410003001300d40034503c06048600e030710010041081d03903000918920035170403401d0b54a0040d0036003007109001c0c4540340c906a10343c56070791401c0038900760741c6c1c0d0149102d80d014003801c101690f210382e8030030240c3c484d6100e070a440f8901841c4251000c2e08030140c3c801b9801c2c00424007460141c1d0307a61034140e8200d00b070b48140ca12074080c807010414036400070303110340169540d868076150051665940800601400c5507082c100517885002482d001c030b4003a4441c0145030018000c646440d602c1e0103095031607100e401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455941501 1250 455940251 455940263
    0x90112030f020303130f0606080d0909060e09030a0c060b0405040b06030d170601030c120c050913050c03010e060301020c0f0f0706050906040b090105221d100306021804050112 77
    0x39505090a00c08020ba0340582c0401d80080f03e90605e94403105a1034000040684065580e558005044c2c0c4081008000510031500e03440c04161030031074424111a100c3c0c2c010200654601c0c1002034080020040380e10751442800c00d540040c446007802002488034041e00e9401c07030300c0c00c0280818000c12051541c4240030440448985c20070011084808805110509203010031b0300e40883c190398001c0e04000082031a500d072144401488014503070580310460b0fa03080108a0000f40c811003424024112001844407040074001030500071a04400d0781310511802240303001c2d04011824640e401c0d0101e441d40192601191b44540740350405549a5403031380030880e031601c200c020000d10700b40140251425003174014043c038145460304c41c085440e070340311118050403c0810000c03030480f05440c244048074130402c00681c822141c100f0304903580d52015041060b24040b005ea04105900c80910b0b106029698001c0015845016980c00e80c0288040352400580c00b80c102000031403620031444c004400140506 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455942751 1250 455941501 455941517
    0x316030903200f090a02072004140108030a0f0912030e04060f08120307090f080303040507091a102c042417190503090907020708030703120b09011203 66
    0x65a8841e01000c07540502d8009283d0111483c1502d48111410f074041e805220251400c1c5507640d4030100504240070001040e0005070907581141040d20035006075040e40c6000030071039414104415900c2c028005210f041243e000c0788015880d104129480007030800e0384030703150b0490031031901400031502142441d0040c0e241110014500d401c019145007100c4a200103090f2074016000c00c46ca060340020422001c0c0801c00c900005e0350541131082c5801400c601000e16141e00b06480c01c80d080801660150000c18200358809106084002082030550012180c668010700302301e2055442c0c2007203620107c00c1203405040c80600c010b00c14200b890018040300c04100c1e44240315051115200c00218041c80100031034414009402000040d0351280c80c5041122529800700461700c40403c640e0400f202c0383d40012902d10007a040601500c6d80292260000d4441141044141039581c0140c40020b030800085c9d04070040c0010081d8004050a00041e00c004610741e1180e8040303011158010088000800702 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455944001 1250 455942751 455942783
    0x8040e0405010b09100b070507050901080604030206160f120e030406030c0908060c030c130b13050f030a080a0e06040807060203031905010308030402041122080d0201060b12090316030903 82
    0x1500788544900200c00759441102d01b0075403090010b400c14581100c15102c1c4007001305c2c0b55a64007034218000c041c00740081c946881c01d0728009051490240904021882d0800201d00a90b04030740e9a094030101f910b010f06241d006000450081c003810040c25905010005001c99002d80c15081444584c03503076140d00141c15a41c0310410f030b0781c10044882307000290040c400300350700d20080001040d99114082601180545419800d0041d50080341c024160711401c5c102000326040200039400d11800441c003600c8030711540e4460403024450800c004040001c0c0251190b100c1c2e40d030906076005010b520046503402c42c0c8400021f952a442550164840d00d601c00e814492010b45001c0d40b41a698405c44080c155169942804058444040001000c0f00d05100c00d650120302c40054446041e041a4002402c501c0c10800301d0610300000301140071a41021801e1121000b0b641c210f904041d048207500d0745907541c840c203050550258a0307036101c012102144180600d82e2190043c1e01382e0f03010701051443d1401e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455945251 1250 455944001 455944009
    0x20712050d0e0c03030f0a0c05010f0605040614011e170a05040615120209060d06140601030b0303071e0201090503071403100c020615010509060a090311060903070e0705040308040e0405010b 83
    0xb0700d08403203038903510420a0380c00f254400341c0644615a0780d4141230642c4141a1749650a44950910110b4059680c22040100b480d140c068a4000e120891088503130821650008003480200c800d0185082c2010b00c090703243c548a03079170035010842450750101e0142030a60900c03018010507171f001e482c003a081c00c0403003400c100c43c07142e030000301d03513101c03082280305c400c241e09014075020028001640150b2101e10180403405500941c00320360450880f58149180000c00074040b203041a1400380139030300a110300d500268030340c0c800d900c0319001201c503540d00c10070a200403103101d0b845805c52070701801403403800070f51840905144003000354201c003642c07a02e42590b0150740031a8544488900140c0c05100800e007a0400352040e00c6884106140c0b1601d40540c00d0040b400d59403090381c580001414040041051101601211125010445403a460200943c3c0060f40d01c841c1030040424101440000c110200d003e081110025a400508640c856a0300c055503584050101d1701982c1c1c6500780040c880c0d403458 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455946501 1250 455945251 455945263
    0x60408060a1a030d0f030225020907031a09181906061505070b15040c0e012006070503071206061d030d092105100b1f02060f0a020712050d0e 62
    0x18000d0000e08442c0b85815003141c88170200d000010506074200709151032074880c05601c260417040325502040c1040d4910601030110b43c001c01031010949007000c1c29840144450a100d80c044040b6005e1f24141c5031160300c044048144401109a0f10900803d24082071046400f01182c900458041100b1a941c54104407441245a1100009141081b035100010048081260040c05841d03803081102040030103e1300720361120545802007241c500036282b4542c0d00071070100c0c0141000e40c0b9007d00012110040381e0720703100546541c0c1031010210005603c14031a405600780c2e10130341c010a001550380c0d007801500c241d001e40c3c0d480c1211052800b001600d81000079115000784620758803c0a52490712010750b0034201c1c40b00181c02d090700e01c86102c2010410400031030502003a10301000a0040e84a41000741e0b030b200400803080f152281c1000341c85030540204009600811503136854120313a8401d110320000f441560001010740c0001c1c02e0301250550b1100180c03242c2502c0c2001007001c540c0381000250707108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455947751 1250 455946501 455946551
    0xb180603060c070303150e09011802030316080d0f02040306050c070b07080636091209090402040e0109030804051911190e090c010e04020c1911060408060a 68
    0x19000c0c0c0040b46000e8030000c0100456400303480e0008216400b03c0042d403903175803582e11035001c015100c818442c24030020701c5524102d0240d9500b040c2c0c00b10761a4003007901c0340603001c40c6141072050309141805100302901215a58003803203c04002250045604034000c2d080350201390b5619240900148800301b4110840302c1c0c0c580c010078541401d54803520100c8085200810440c1c01c0752000c004040c0d16040d0f1714902144a40100e5442020000d5450106020400909030382c00c03076102100080b021640a001c1b04d0441c44156106212a5168000304000e0308050400304070940c684203460041c90790101c845070003a8442c03800d40d0340741e010004000ca0a507a200704082c0c5503d03d100005100c134506550f40d040c285140081394400320750b5680b404541c409007220112115040402d1880340303580d209440513917441c3d040380e01310b04011110825136510b070f140c00200c41422001d0707802442880064100b00b90411002041c05983c0c40d20f402403180c07541010b4404044076403c186920600707000f0012140c05038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455949001 1250 455947751 455947753
    0x2070e01060806040c030b060705030c0c06041a0a1b0b1f050f0f0310022205060406090501030b040939120f030e100c05210301170f0304090b180603 65
    0x203500c402040000805c0e2901082080c145c2e0344840919640780d140c041c100d09401900035603159aa01c1280d1410030031400e8040740300d0a41003006001d03c11002c0b6007041c084042101984c2c88222000003034504500c0e90050760044800c0e0080c02d4100724041604d14801e40c07074219546c000b2010300ca4806443c0d415030040ca036000f180080d00407468200210039580c41c52000f0101c640c05c0003000d92510807a80302816501e0603121001080595224100c18040103040a0b2505464180b51a030b0007403a1005e10b0050904060722500055407590b240d40003800c0d025000a040a204914070911504000c0364142c040c0401c0c42c1d40f28070001d503c072a04400021030751a18198440481a40d5666020542c80c450460612502c101620003d0700c8240308101e40040c2c0392210041c422082c1417907403030140b4034015110108840341200c1c4840340c0c280140c0f41112581c06423680341e8280f02d80c2d614100044080016180e22021600054000c0359400070004014250340854101d15101d000e1070b6005d908450507905 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455950251 1250 455949001 455949017
    0x102010b03120d020f040b09210c044803090b010e06011806020105010306050a0209210f1c0f0c0309030b040c03020d0f0309050109050f04110903030301090c02070e0106 74
    0x180700745400103110f0b01d82c2c0e15200524110070465000180c2e046a0030910340001d010480c0800c508141c1d9400c03007002103a1071250024500c19040311794400611420341d0103603881d50180040720216014640c414540c548241000142c51203040005d4400d450316108002ca01c022505100c90182c07080c11650790f00110644100d0303080ca800c011211001a00c0a8100040146000c011104200c0314070050442c0c0d81c00030506524504049098900140031803950a104001200303860b955541c0044044505040050044006014081c100b00305280c00d10440e024441ea01d00c0d8802036507404007200700702a02d940031a0303214039004070742c0183c0604004001c244a2601803000c10700140b501c9920a22410300085980c2c0c0b80e602081c002041c0d94003c642070440c95207031508158006000354058602880c0c905151483c040010741d100d0303034108003580200d58944080e0030a81c81c20b01160b8102d4409400c90303599503510300070034000300700b044984801401100004240c0d10960405c045c12101c0740e0761000300d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455951501 1250 455950251 455950273
    0x507060f080a0b0a0b04080105150f030d0c1b03141603030f1202040b07080a0e090601021b030307170a12021216210605041b200c15180102010b03 64
    0x1040e110050b103138403201d4580c0001d00402001d00078005415014008101401e044001d00f49500e281e05c049486824901000300e695200011118900300f401d14001d00000ca55003071420601c405800e080d44003144000300801031090020a80b16a030380500201d41c1c41b00f071745c00f001c4070134052140070007800a10409030405042d44a0207040c2c0001800000043c078290791444680c0455100070412500500040390104906030040c181820b82c0c40146d50305034480c646440000e440c0c1c4605102c503900241da1400102041c1c80400c10740d8190f9070f002c881d03000b10300e10b1094600c4654000300381c140000796085004000000041c0240c1d6182d804d42400404203845864076000e00c403001000ba1000c0010411039030050300c001c0f05542d0080380c1524030010b403207401d20003848141c60b40100d035555118010407aaa0f0001d81c80303a0807014591440100300111000100020b080c010080346282e8040708000880041844500c0103094090903088201610300c1a50010b80c01c4c0c40921a1055054011014100f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455952751 1250 455951501 455951521
    0x1305090c090c2107120e120a1b1112150f0402062809080102040b030403051c020a02030a11011e0e030d110a020106050603040c090f06090e0a0507060f08 67
    0x6900100d94407003160502c14402051030000101a20403d2258104800e01c00d2890700401884030a09a0010611081c19001c11081d5113100f46014a221600000f0702441078600c2120b0464120040c900c2c030f0f92089059040464604103030b00442441101c90380f01010324031a0000303d010300031884000d402c100307654624441c002c501c0020b0041c2e812031010001d075070115001e4890524250030410445940400044000b000c020203078010b079020303030710401003400000341c0030f020340380e106616240107541e035100c0495102c680d20300011007070402400032401d40070ba99004400790004128030781c2c074801d080407000282800e80e26003030755503000b00d5603040500c006000140c000d10009443ca8003102d2804042400020480d10119800c4072000004105c0c0e090721a420f003d048010300e404c03501c1c1030950802d622a0b00720100355110700307942569181c440121034004c5802013801041721600420000a510030f0b45d548954008004880b036016188003c14850700036201d00d8400c03101550740300b4090360b03808844 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455954001 1250 455952751 455952769
    0x6061212052802010608060711060c0d0b0d030c020f06280513030b0f09011407051e030403120c081504050919030f03060e010501050a121d0c1305090c 66
    0x3600c0b00c6032080c0e08a2009600c20008881030b1040303a80001102d5140c40650380c10500b019081404000c030191010307820316000101c968000b0f02c18100d0541e508070ba4031010000345140e2b101d160b080819401001c05150700300824205070f50081d520211590002010052540300b12106005076410700410442c11ba0844d1201c20004000c03410710a01e0005510350000d070307856403035008a8810f185a002c10900c0c00c4200b80c001d1304103910700001c1c00000003085141d000004001c002c3c10030800045a120010552545116507081d507800d90682d503801c040c02c008003280cbc0318030085403c06080101038050544680d01051090351641c154082041503082044080e02c07000e088642e29218288501003004071001d00c102d9801d109445001c00c4ea0240e0328041c098800300e61200922040800041200f42d070008100c410f10303c5240b03010703100e403081e1014100050070200e20300b401d04039102d800034043c500b000aa0407000441220103d8040c00c455100e4015100f080361008890782000042961504018442c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455955251 1250 455954001 455954017
    0x80a030f0603021e030f16030305130e07032c0d05090307230a0e040203030405010804060e01090818090417160503030903090a0b130b0a09090f02070606121205 70
    0x100c0d940b81e03a078000401d88407400304149920021050021480d243c200141c050758055035000c0c1c9065600350b1141001c14104e07220280c11320200145102100107000b1003040034040030391036000a0306259100a00500000c1c03442000000310075150001d01d00401f002504040100004003208000e4000460742600560700701c9805202d94840400d2512841a2000741810042c0280c5147d40c3e041c0c081143c00c1809a100208144070740c0c1c18000540c0340801101c0580d0800c1c05e081420b91580d10300440241808040440e00d1b5113030011703140c10000007000500505107600b034050380c401030000c200640503d05560040c02ca000058481c189100d541c006019603117075660908182c4c60340b07521440e085500c100c900175202d81000900c0c2d40075141488104001c0c0011000140c00c0c0000302d4000387d50419a401090100340c40454a500700510030160b0002521546100f800301c50317429901203010f504a100f08584407420030b503000c03c07140c0003090142c0c40aa0000e4141d00c10b00706415081c0d42550100300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455956501 1250 455955251 455955281
    0xc0f040902040e0d090b1606021c1401031203111e0f0f0304200105030a0b0a0f09061d0402060d02070609020603091e0c0604140303090405240607080a03 67
    0x301810250b56903106080210202c0c402034110075240050003400c1c540140c0040e80d10360343c14014588618000030060070714551104005175600112980c1026000600d4002c0030310b64203001600c00c01217601c02d05141280e22451480000c200c21403026400c1d0340345460100759688051060b0001e000340002d608908050122070385140c030100d101c00440a9000244e2010000c000105210800200810220306001c9100ca4106c1415000300001c00c5844007401c032803ca41d0702d6114540072561140000390082c4020341e1001501c1da81c1d6040030028080c6440b5448007440480310f43d244075140111080d00c9294010010341c5011400394000c0000c0d04205402e441695a8048010041e20346c40000c0d401254030320020000010f010b50420054040b4050020b62608183c010b8601602e580055a05880000c11401e61040ca9030005ca855401840d09241e401828002800550560300f80c0358440c11400542801300a01d40d0420f20401d44110030b0014004882006400c00c01c52099010a240c641d0f218 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455957751 1250 455956501 455956511
    0x105070e06090a030c0e04110103020f12091e0a0201030b03010b010e240720010207050a09020d1e05061009050a33030b0301060e01030c060c08070c03051e0604050c0f04 74
    0x20b05d4030305030380400b90001d611040d14402840180001d400118030b80e081c0c00d1030b00b94508074541d004691a4041c0301c0054680e04a49800b05100c1c00c010320039640c84e1421050340322001c00e210101140d64415034039040c2d0209180008809203400c3c180101a140398041c0c40e41500070342408180030901080c80038040f00200c1001d0340c0c0c641d80c100f03800146125800380c081c880900d9400a001c0e6950252413003041d041d0350121b081084a03413150540a0200c5094640040c2c40d03000400c40c0c000985030414028100e20007809001d175590610382d0040740036020a4461141d4031194140c241c0711100741d40650b0390701041e8500f0800042d2040c90301004c00f411b1b81000b41d01c9910352565034032815505449000b02094071000590071a040920130140107186c8242682541e52541e254140c2c0b8960900600b02008448001d0a0500001c001190301d9640e11480800d01261380b81051521950b0450707103a000b811080e090902092800503119000d2608240505419275070142000009940500140d401580318 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455959001 1250 455957751 455957753
    0xb0316020709090320150106050f0d0207061406060c060f04030c0203161a07080f0706060f0308131a0909040c080102040f090506100f0311070b0a0b0102010506030105070e06090a03 79
    0x83c2c06407124540c8a6182d8450300f010b0100d0007034118120311440c040550004442e01e100007500b010143c1120042c1c14065610403400c00132113141c2c8190507a04130581d00009a000400100c5c0d03000303001000280d030b603c15442d11448200141c40c0300d4640c02c1e00342c0da484140402c0f0042c0c001402c1941192003801c14500303001d82030340400c1c1040d079044407502000121080030006000c20b10348211881800c1d0604e01d2612149075142a01c078024203c01c0030780c080e0045501010042294016009814804140340e000d036a01c0c50081020f034407c0361405034092144900040240081c04201074248000c403d440c2410000401c2c0f00380072400900a0345c03002a000301c00120700c13600b8402800034140c3c4200381d00269060011b075406458010700360500503550015500080c5e5406014180100c03403a10703000c2014440280f10149a0190100181c40105988103110f0803082c0c2c2e1f8065607006000303030000d03c9030395200340406003258002c803010740101301503007250303030191610600a007500c04c7c0080101140d03a0710703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455960251 1250 455959001 455959019
    0xb012102130209030f060105151c02040b1b03030705032811070201030b0603250909020406050a080a0624050c0708070608090307080421141014010b03160207 69
    0x5504000750010b9001070f0980240c10240000d804211340000185007a5160001240b600703030700c0354207983c07416070301060400840c503055030103030207110a000c0199115922150030444590101c480c0400c07210842080c1050b134100441542e05c6112580c903040c1c15039031440800c050200464120000740100810020380610310b508c00c020704c5024501c0003584a058510001d421214000400383c46100148200013021050b4035820034030604940e00401c2c1d80690711010703500c004440c1c006c408180d00225001c915030340d1180203402d0948140e80e0b000b14030b072900380850088400741c2c00b0b01c04054044c0003010144080501d1115001650351a00c1c51408029000541c240401504950800e821607401004626032041045801100e980080c602d400316980e03404800d84170350f102e060203e544043e43e601c91280c414042c283d000f900180c214200911500000d515243c10442c421841807601200040c600003400c0120f040c1e4801301001861512100a1101900c40d070180b403404600c2040d1000c40d410316 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455961501 1250 455960251 455960269
    0x180e0c090f060f06030105130902030f10020a0311070510021819080c010f0210051b0a090504050a0e1b0d051905060f040308130303020d0e0c04060603090b012102 71
    0x12250012241c07a06150040040381e0200985091103500140014000303952a0040e803040c43c081c2c5040000c2ea600d852011a080440e9400a400300b070041c08e00c200351000442e0001e140855650b5000c016019180d07032035030721500070b40c24094005c1d8400d00e0403c0d804000d40e4010801d2405402146049500d01c200003140112803107401c0c042c070b000100041090080070402000c02540034200b600e80030320840e01c020742d40c461485075030285940300c4002c40d0020818070555103054009140c059540c04150300d0151a544e0503106103402585400000741c03070440b0034440c80541c41c240c0f80c003030000881e96605590011100b15a116442250b050501000440070840852a2000004d5410714002d985c00c145040c058000c1000b202c600881c2d00700320009a0040b2400c1d072143d0b2001c0c40180d00691410228005e000d4642140820f914047c0708505c0c2d1000007580080013041100e080c09070300c1e100d80e401c40503540001c5005240308942401806400301c0c91100b021840c1022000b81c0c0702000d1500020301c181 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455962751 1250 455961501 455961511
    0x1b010b0616211b081c140f060a090f1b120b0f0d0f03020a020603011205060a110f1602090412030b10020d0e0612011403070f180e0c09 59
    0x14108054600c108907612071101c0b403003046010704040000b001180030780320b000452020aa541d150b54200020003d5400564941441c0d45034000350503400e460801340284001c00e84507501601040000380c40001c01e51780607214050242851883da403a100f05100135125803481100c3c0a42c40e40f8600d01c00d5260007071040b4920515a07100009100030b0850b0a08440e000c1c40c07803d00541c00e4001d40c00094650510091109504c4a0004040c03855800c04a00304132001900943c08400000005040717002010040d4000b4001c5045d1505074854a0b250300c00c82c0c81c2407c3d030f1a614107060080c1001400034001038100c1c8060003540c100c4196542c6d000416009045804841c0d2203056a252050281d00d4480c10440d498191038001d1080048500a5503a60310b43d01c20340208401c011000410b520340c08181d078502035444070b0409440d40c540d91206843c1c414015038034040e1043c2c50b40040c4000100c07400348111106048010100d8540c581c230f8001500303c91a6500c8a0312883d00910156181c16205501c66 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455964001 1250 455962751 455962777
    0xd02070f050607410f0d0603060e07141c021c03050d05090307170904020d0f0509011b090b0714150a06060201020f0d0203150603090a0c090608031b010b06 68
    0x8641c00e400101240d01345508a00d010381c1401c2104010110045010f80356040400032150311140c1c02442003000c4c0c451000445826410040c0000401c40300360400e8040c0303440041a01e040c561100403c11406035103d080b2a07014200d40d003600e01d00c036070310103900620b14009400800201d2042c0804040540b49560850004400145d0801280700e00c0c403507241c000380d550000d1880c00080340c40d00001100500766400c65048006070220380d990342c583c111a140303200c0c8030050013200810020000101400c445841d225400e0009003a0741100302c40c0d5650010a40340c03184030510b03060606500c030700c1d00800000c4031204c2c804400e45a0720b91041004840e0003141d4a030100c880d241101010b016107030103034401410b6a0060003d400754942d6a41560110195054016202d13034508032110307007421020701070030780107480001800321040300420000030b0380b405040072a034403c0e41c5090b00c8084440d82d21407404682c1007807211001a403030004280600c101c2080003c103050060340006007996200319034810007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455965251 1250 455964001 455964017
    0x4110c060106091221030216050a051b060f251209050402031501080903070c0f211a10031709090c090a061803200f04060602030d02070f050607 63
    0xc8a0343c050702d4000900a000050803c6851503600c41040c003c2600c0220004164050364420051003581920143d04c6448941c00c079165060901c1c1c1d0b290700102c20141c499014a400c1c442c903100c1141685881064054846490320401003200c0c92160068004881d80d1400040c0c4001480e4407142c40d175041900504903401000900703100584104a00e82c030160140340103004016050044800148a02000382850005a61466000303400c51088541c020700c410b111900100344c3d08c3c803c01580d002c1d1000089e19041c220540c14524a01a800610041241740c46809141d40703000300792001130700710450380d60b050011a180e550301c10303012020904100e20000d01060702c04080c508008841d4203c0b804140051600302c201d00490b0304002140540014025440e01754503a60043c45c0915004540101d1228031460780d40b807030f031f007000340710406154400d910080200c669460316220305000c840041c0c004600c0c1c100b107000001d010703401183d02a542212075000761130104800b0b01aa51240302107554940d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455966501 1250 455965251 455965259
    0xb0a0e0607030f080403180b21070f14040302030304150f020a050c040b040b090a0e15011a071b0b07030e10092105060901050a05011a070b0c0418140c0702150904110c0601 75
    0xb201020702c0300f400c509d500700d190600258581000303003040540b80d40e280c49200c00c6440503000c0030511a640c40207402d4400007a0001d8a411074244168064180e5078600c0404055103500301d80d02c1400240240598001803ca42c3d107610b0642d100b01c10307002010344041004969180000d500040c101c466500c2e00303860303101c1d0041c1500c083c41010501c0c100108514583c0d4100003600681c0340b00c6110b0041c81c6034001514a06100d80744804034034001f00c0280b1110001e403102c1d00c8110396001080c0860125015100e45101440c104541c1500c400c1c003541d0311254146401a0034411004a40c040c03090240c1045070200401d005000302d07032140b813441001107010f00b0075040490448405030b210114588001e0a80e8201e5041901110f064940003204a801c54407260003000080c0b04961283c144402801020201c0102c55009131081c07002d01210b040da41c0d03907040d0040300700b4824920300a50003440014241c9244001c03d01805080350302030f0000070055412034520015902600301c2c4501c5070f201e000100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455967751 1250 455966501 455966527
    0x8033c0c160518130219033503060405060a090f02040509010f03020102070b090f0d11010f0302090604050d06020d090f2006090103020c0109050303010b0a0e0607030f080403180b 78
    0x2034001c10781a43d070072601c8816400d04030582c65024001c3e20f0300e80480005034056644aa1a440000b0202040003000b2503a034540300700146009514031041c1c6ca2038040f806858040c1c801600382130308084009038915500c03401004000c20700289140d51100f00d409020990855503c80c0c649282503400c80113036200d0804c0200010800140e0101c00400109402400140d0340403442c0001c1b10a24112503455060500014221840d40e00c5602d811000e1f101601e418440c84024448a9200a8035804441c07007510404a00b0307072049600440c0c1081080104100c14185402d8121080707004a40041c20054402e5607102580c800312001d451503220385c2006010b11900c01400c0385502c2854001d00e1580072003201040003802844a0395040c1640840d900708050020b400c1501c21550100589a0320340e1244401000e98009130646170014a4880107144d032410406d08848440d605625403160000034400101c0e400d1400920403002c104040c151210010b074600c1d43c040c05000c50a02c00b0792a80070300b00c505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455969001 1250 455967751 455967793
    0x12240b040f0f0b0a05030703062102100c02030c010c051213050a090506010801030f020607060e0609010b1e061c0f0603031b03081f0302060c0d03050108033c0c 70
    0x10086112070b904200481e1405100300c559540340390500d44e450366180030301600100851307030020091019964103210800c0f10a20929545442107811401d010380d4407200322003000e00807100075016440b40143d080c856000311840c5800720702c5041180c07a09000070f004004690000300c0c21524844100c9400d018030320741481c0b1907024083c400c00030400b0b032514800081c5000011720001c1c0c445000136146d681075450f01400c035929280c004100b4480d2400c41103000b030f9118002c8540c02450751900d240c1d0fa4a80c6080540003c040c0700c008a1802017080440401440703600c01125580740d890249100e03801300307469000703150701c0c50070030340000946a242d800c0c060b01c080786412003151a1003220cd07046e00001d400914803600a0000c10300b04113000038004100c603007068a500080d6101502086520402c000000d500000c00c29075507040c4180e9a80320f59036a56809003001042c0100805400ea800003221861409c0c600c00c1180e9102c4100e01a50106103900d9108580c100a282c1040c1d84402c20041140d01c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455970251 1250 455969001 455969009
    0x1a01030c170d0c030504051e041b020307120903240c0923040b1302030417040b0d02090301060e010617070206070207030305090a170615010203070312240b040f 70
    0x1040c0c981c204030051840e1a00c401c01140c80c240046100c43d0824035210705c2c20780b8080d18001d03200300c0d400048100c100f402d4618000c0c5984c8200d04100028511503006034451825803c40e030001d5052018030358508040b50303600c996050800035002c1c0c0c00400b140c0303000d5070603407824170800000d14182d000307124160644082045032418040910070400010109404603105402c03091400d10094440d54006009002101107490b0700c844101131910007149580d004500484c4118502c40c145102c0300c00300ca406000b5441400e01d8070105000645001c0800e8000f40080d0100400026010782c40e2031000d16028420b070172200025040c7c10f040244030342480c0035960025110b00040419141c86180256a1f00450100408100010940300642d4464a00400240c10002642600032030100f0801f651000e0403269083d000c00c0c000800700727155002008441d1040d4142c0e541418004482c101480903140007160001042803000b00c812081680c201408094150074075000d50707841c50420300c05040702e11504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455971501 1250 455970251 455970269
    0x80a02060702011407110a15020a0207120b0105060313020a12050c0901030b0105060d02040b03040812010b0909040b190915060501020f03120621060403120b030718091a01030c 77
    0x1011a0038000f0b05007501d5100385c05240030748850b400107040a080c081441d4004018101003003403d2522202c0740c01501242540e9130817202c156940d800d0300400c44118940207401901c3c003000610503401c0081c001d590042401c051000425025804500c002015502c01c0c42004190105c0404018050001c43c2c4087c0b41181d41018550660301c40d90b0480320f040c4541441010b0001d03060300300d403419030140c0300100071206900d1349910b018200301400303a02c00c3c0e018485100c40c50340003084400745401074900240001e040c0d030345955600d91b41c81c10368082c042e001e089500d05050003410840c1441c0a0040390a02c128a00c514051118a420003070702c2a81d0071147c1950480028225001c0c0e001081d2020ba980303498200f03003103440d4407001c01e64906d070107111318000d035255051900760b10390300040c0640110702c42d40d507401c84108407004860858a07504140e030707410b8228200c100042d8000560b18030941104403400641504682e4682c0180d003040c0520201c0065000010000e0119200200000b0011a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455972751 1250 455971501 455971511
    0x516120f03050f1611070e01030b0108120406121d010c090e0603030a020c060307110a0f0b010e24210105061201052211040906140a0c02070306021c020403080a0206070201 75
    0xd8115001804c4108841c0c104404c038810044607140c2001000f00604000e00d15046958590924445154003400342404500c2001c0d100b00d4140303521011102203440aa580d03900440310210100b0241c051a0041850050f001c0d60543c00524213200b42449500d841e100c0d800181d02d030116a010080004002d02e2184c0c1081c0f00c14015183c021408000000089440d60707500c0d034615005403030890403000358080e5445440890410410b10011000380316000315120341c10380c2c3c2e0b107200301140180d089482e2481300b8108184600c2c400b9a104400102c504003c040322032403e20000004420030015107038100b0b584d101c01c188891400d000c1c5008400c203141c41c00034413882c0b80c21010300c1c45030501c0701e8106a152240400e98070a00a0101e09100a81401481407214091509010001e07100270f007480c5030401c3c20708020a42c41030561007210805045074001c2c241f074600c1c544982e4020b42011150381100720312030103101c5c581c410310b10042014610440034145c58040342200285820340c024800302c1568900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455974001 1250 455972751 455972761
    0x6060f0d2c100e030d050c0c070905041232180306010506040302060a091e030b070c020a060e0121060305060c0f0405040f0207050115051206160516120f03050f 70
    0x2140c2c9841001c035202e4041640a000b00c032151452180c6035290820518100601a00345507500c01030140618810480b603000c0c0e21179031010300f26003064030006d158922a025540c40580034070500b180510081b89a881c0c0203114030012800d50214001e10304200c08001060910b81c1d25a18004800d120194020a0258105804034213284a0790001a20410010841030700e424401c0c440c540c0900758441501d410103401100d061080c50340c1d1b010441e0316440344000190b0040c4a40750301c40341582c00800355400249000c00595080640c01d00b01810003d034800e0856040000f00d94149078403107a018000783c51480c1d824107604120025045019040301040f00412640342003041d2800e907181164001010340400394507600922840200030125402d080130500108036040c180c0d41200d00130340d890313024018400c603040c0d100c2c50211550f44180031400c406510252080000c1c00880d04202c034960700c00300e0b450315200c00c90400c0d800042d0000300e60081030754100d50700d8056550032004a101005031400c0c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455975251 1250 455974001 455974003
    0x1030f020909151f05090a050301021804020a2304140904080702040f0618090b0601030e070905060d0b04080a030c05040506070f030e0d1511030f0f06060f0d2c 70
    0x1e42580940c3d14400050302003540c461034010904600180d400a948135035440280964100c1c8401d41d20924040400150304d04043c0202d600750000040c00e000300d00301c80d0003000029044041c2d0344007000321142c600032169627066000030103413910108007925240340c409042c1c807003a00803c115010b200c000b800d206c00031308000c0aa820b082c0c1d0484022903e404c680c2040350060102d64016011440d030501f10710441186a4410343c00d460152608804e1a40c50400543c00d8039841307400c03103905a0040c0d43c00c0100c0041c90780070713940004000f0304280c1003104c151a040340000054601f03581044002600c22282d0b50184902d01d100c10190603d142410714040020b5501d008035003020b00344c1107012004008052003414540c03030540003f4080385c1810b41d9820425000d908243d50b03004074500e05104000e80e194520141c1e03200f1006070b00b00352880e94540c40301007510300c4c3c0500f100e90000750030b001c58004a0f607002d000d00f20055031020300181040c1d00f00802c03185595a03139490311140013900c00744210710070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455976501 1250 455975251 455975269
    0x192003030304062a0e0f0105181207030602220618171e030403020f12060103080703030b0a03060b090f040312090f020402070b10090606050d1814030901030f0209 71
    0x40c20400000d00c1491410104c180b030384520f00106110511401204041d50b004461240c9180d010389010320174190303400040d03903a8407a841c60004a00081c249501c15131078002c040c2c488c00c901c580706607641140d4035641c01040e60004c065100794400c8001d40c001107450143c103101d00030305941c507141030000c09001d10654200700c0e500411540200c80e038a03100810384e04000d440c0924440d0b0940017490130290b50760544076049800304a1142c01c46841110031072402c00402500c0b0000325028064903403a5139104011940440d030210189070f203e00e4821a07560f6269140001107010300004244240c0c0c000401071307000c0c00108084416141c400c1440042580400311f80100d0900740c0340042d140900c1d0601e040d944881350750081d44103000140a00403c46041d290a001d0b0b511400e2048074940c1382e074942e5065486600481002540c280001041c92009412030401c0c07a070303003d07149402243c003600d80f51090018015a684d407130380006031b000760a5134103118104d000d04240000714141805603000030310400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455977751 1250 455976501 455976503
    0x60a05010b0715090203100614010908030f03100e090703062304020114090409122316020105040506030f090c0102071410140c010e0d09050d0204110408192003030304 73
    0x201e0b0f80c1c0064605100719481101d00903002000c48410503030714081c4901510580c040c240318450a400621030300d5019050500980da0b41501039802c0684866030310075180c01c01081c000b1005004032001410f20010f03007100380140c007441c01500050381141400003d031610346c600442880c1c0018500603210380b1141d112500309909191030f400344000102c0e100b516014000790b940d4400c2c07819440c00c04102409805020000003525030700b01900914445041c07051004004012802d000c22402500c2140070104031b441c0d9205041c038504254030382c070102d080d6400c100e580c042c0f01106602485864002046100204202440281001401d21178071400813498408500c0c010f050301c17001a44818080c42000209240340603150342c5402c0f001e00d01c0b6018161183e0715030780c6030144401d09120148155850b20540d00f001e0804104034182c2d500707000080c513800c00001c1520805000106030810309100200340e00f401c010511320090840d08000b9144c203c0b00c0d2030b484030054143d41041d007685012064942c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455979001 1250 455977751 455977763
    0x60c030507141c03050912030f0f0a1514030735120309071409011a0c0c030d0c0b010b09030607110a1a010e090705150d090c0e0603060a05010b07 64
    0xe07030220140b00e107040940c444084070040c08649051100c0d070326610942c860a11042143c4d0190026801e0b03484920080d00d400440312800f10024a00322005240c0a400c4049204005500c1e05501c0d11919a901d86400c6000c820602141c4031840e45000c001260140c181400b0215501c03169075220120b100e54010192281101c1c400710308040d510500628208e6100f941c00150b891505034451a1209518015504403050003080c48d44a401c0000b00d1a050f25102032580844040700c0380122182c0c0c003e1211076040384039003007a03203009031014400410030401c240c484140c0320341c06240201c0042e0050704503204070f45080c801041c007a600014205d8104503c0c0c1001c00482101c1c00003e81030203554407020342908455039035030031400c0f920204541210485910f8101da510f03046840ca446040c03612a05500900c4203001d402c48040c90401407109a100701c0000a14044568448a2071312480c1e124100b00d40340750080141a08080c04215803040698400b000298101500c0c11501c2c01421005490 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455980251 1250 455979001 455979023
    0x10503071403030d020d06030201020717100e0c03070f0f1a09010309080c070b1c1b1404091a030d08090709020f0d0203180f010603020a090507030615030903020601060c030507 77
    0x1c5031400d008a4601c3c2d06a40c109650b944080041880541000d2200b06d0040c85000d42c0000c415501c8292006407440c01400351031013400c0158a0320181402940703820f80c1d0301440c90015019031302000140e004000b2481030503120352810f10b480d0020032803a13110050641850f080300050441103001c035000241c7c01d080c001203141c51070508040600412651050510941002040000301400a0300c800b241610b084100c0e48032146940f0150382040c20901000b1000a20300c3c0616401044001e151100c0062000c1c01c0c0b070780c0e9104072003e40d00100c1d100440d2000c40a2002d0341802d0501450940c9056800c002c4494205038000d0f69503a10342d4450341080c40c1d40864205101189081104c1881c000032606640300c0c00c180385c0d071444ac1c001e1003401d03c0d920700c140c811403000b085060080c182100c0e0010290a040ca01d00348800c3c0140c000102040c1c1015981e940c04501e208640760f0120000d0a250f8000541781e01614001e403402e00107070494000e00144003020400660311000316402d2640c0b00200d496 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455981501 1250 455980251 455980289
    0x20f1c0908032b0905063d150c05070b0c101103100e060d11030a0b04080a0f051e0d0e011d0c06040602030334030f1401050307 56
    0xc40189a8200000c98040059003009244031465030186480c3c0811a801c0080a07502e4940c2c2182c1c06070070f0091660f000b03540003035240c4001d8400c4048821415285010310f030a00312580134640c01c0602c080b502401e10410503c0440d032202ca41030316014007801c044017a00010b8407000e071345248500c42d0484080300016004009071007486106a0291401c10030b02c0040020351120015400c21180e1307908180c0581d100090031060240b4941c0180c201030942d03d020501078541001100816240982503c10340d28001b0008a0040301c00e44100d02400802e034a442c410100184013052841071241080f2051190304410940801101000200a940340f80e40d400e0303d54105000c2e02c45001014065464030710450107100505140c54100b000f490103171100010200704200b5980101d000300d6005a005100161903032001100c1050f20000e81c1c3d60100c0484400c10300d110f04441d82d844401c0010380c036040840d40041060150081c0b1011858180080b9810880070a6032240c49110302c001403200f101440c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455982751 1250 455981501 455981507
    0x11030619080307080a030c0306030c05040902210a1403040501090b0c2401080d02070e01030b100f06030c090e070c032703050106051009030812041a09060610020f1c 72
    0x4001010640700b6640c070f42403581001000f0350069062000071900302595504080d229100d41401c0e25880401000c00783d0400081c003004002e2100101c1e00443e4036005503003d180c00554544043d41d0a400500f0055264503214211056800002681e50300c10b00042c4010f0ba00101c452066944c911103031601c6081031208181f600c041070000000551881d00844e50300e0049000c2e05069501840032199110328151080ba0390380101d02c2501d6140d14080e0060002550a1a4498001d05614810300342280c40d6031600014145650080c0d002c2035403047d140100a400c00034200c010000100100072610b04030f035015000d0001d0391401803c2140240108251070011006090000c106100340d80555803a4a8064020681801080c0c4501620142c4036030061050903a4825681e00100132810031030036a040e484070030ba010344100c40789807007002c1c0041e01d4079400c1e5007513104020030f030010031503407c0010a10049892101c3e0900440d04500c83c0001c03665000580102c103c0c01d927080031820007444407011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455984001 1250 455982751 455982799
    0x51207030c050702130603112211040509160e040b01020607200a0c090e060603071401020732060405030c0108100e070804060c020a0f03050a02010b1f12110306 70
    0x2503205c075030100407428a0000e640001c0c02e0342d00c1071030340c05004280700c001c1181040070503404100070007081d08400c82c10080c681004540c1441c14030380c1d50800752910001058024201c1d54514030007440802c150105902030b10039600e040b025181000108407400000707440d440c00500500a21081c00fa0b800e690200340d5011480c004240c41c2900d0601c2c2e96450201404580da00c80d0b4510a81000c81c051f46002c80425014003540300100100703005854001000c42203410340c0710150545c0186d000005440c41090042810281c955040120005c40040b6042200114501c00d03405042c05010501c074584001078010402502407d00e40c00554651100307004003961600202c01407121202840380755900b04000d036000302e10420041c01141102c82c001caa0341d1116500280c03018660902080c042405440181500d490510010401403100400310726200313610b1100c010100d40001c1c2038040258800c1801011040c0102c050108141d00011404d5501010340711901c110007449452403240f00a60398 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455985251 1250 455984001 455984003
    0x2070308060f130f32040213090503030a050618220609050f0a0c060804030e0d1506060f0e03010203010b09090c0c0a050705150304020a090c020304091104030302010b01051207030c0507 81
    0x100b40000c902c2c1e80d01507030190000f00d00880e0700d441c5e010352644008010012404044a045a007a0850b660300d4080180c20b00c280d0a984c030020b43c0d606074880218909000441c40341014100c041003c2c2440e078244030494558552142602d0444418032550b802040b00110181c0042500341c0301d604500e003401c00003061403100c0100076120308000711400c25000f18036003500601404c1da2410300d41d80d6180540300d620003141d0042c0003510300802425146000e1074100c40550007203080c12a55500c84580c1c40072620030340c1080000c2a401c00300c20710301c643e019916114a1406400a60440d403524280c40c1c058090f100700944036078050b40004e401180b168094690300300581003166014426070a00c16101e1303003507001c1c0c60700440c1c9101e000c0000c40344460480c4d000381d0340a072035045040d10340070b40900101084600401140000c01002460700220f00036004a07070204000e9076511891843c0290850704091401418071a0074802c000d00b4690791000742c3d92041e26820041100107182004481b540b1802c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455986501 1250 455985251 455985289
    0x103020d0513060e1912030b0d03020f12340506010f0e06041803121113080c03010c091a070b042301152d03050f0d0302070308060f 58
    0x104100e03070120744205103505000780010440f084e02e40e4042e40d00c60101050a01041213900b80c1c2c1e0780001c0e0310807031459600b5541c0c80d00050180e4018000354894109603020303801607104e007581100351ba0080c01401c0c40030400440e0cc0e454440704485007400c02806482c1c1c0e410000040e0308490303a8401554880d102aa407100641d222076843d90012a440741141c002c1015440c400b60014182c0e080030b1245050700520300400d01400700c080c4c1d904070307104041300518080c10b81d143d011a2065a550300040c00e12440503082e41c640150901e00c04914103400c06100c0741c440e81c1007800160815810026150544c0c981c46e14450300c0000d04180038100b44280300c0c0040101c80c48100304424018041800a40c0303150402d10107071100b5407408454262400701d884500d003900c170101c1c10850300912412818001042041a008100c025140c10000352140c1c1d0003035a058000c1096000c240c1e6060083d100d0030100c80c01c045042c44801d0310010310042c40140628081e00c0345c1603140c3c11503555a83c41d5903200c3c0c0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455987751 1250 455986501 455986511
    0x60d02030106020607020f0109020d0605100b1911190314090d0f140c0a0b0a02011805010b0102060108031c0e0f0703060209130902180415060303020703021f1d0103020d 74
    0x941c0c002e69413075040f5841001402000d401c0c0040c500e060003036400654004203440581c2002c0c1c1c41e860b0040c00c01920301040c8089605001070842064005003003800c2c60b4074101e41d410004407001500440d141001020b044e0015554541c8900444070b10019240c0c151504e900056400c215800c107901c10407030455401650050408108581034130340303803c5035201d0a1f94042e1403000c6201e150765038050602d20b03a80929200024007040d2100c2c4003401c0b00310080e2001141c4200d460102d2034584000c0e020903101c5944400f201501c4c0d5804002d030500502011000358074240e0040f0320001002d002c0020341c1c00158540282c15030b80f004c02c00c10f180314500090291005c1c11b5980c40c0020080d48816111800b60340c07910461303402401203105801400e50041e2081c1c2100da0402110350311400d0040040b501d64454000c0028450590300c1071b840594031940082480a055004101d10041c209a60002100d224209441c0441d4040c01c2c04006920b40d401009070f00c0c10310070050300a80202c10100708000d10348 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455989001 1250 455987751 455987759
    0x1003080a1112190519110a02041d0712030f0c02010c241503050a0605061923060a02150403090801020f12010f06050712050409181502040f14060d020301 67
    0x702c020310681000a1003c50305070520201039070180a54030320341c40006204182d501178540074440716008407080d242600d00c18016540014100c9446580314074400d865a21040061042007101c90003400c0ca2100400205102e41d070003c121401d840725260400001c81812400c690003560129030050707100581c0802d0585103103004c0c1007a03014161412142d810100703403815006210b1040800e80e500140a805103030499201c101c00b8200150081d074120440e60361000c01c02c24039560700b030094401c8021102c11110b104c0e5410207080d14148007030b441107000700700350764002c1c0e00085d880000c84c0b1502400d207416a1681000d413040040c0d40c0c8030440c29400000d443c03080e80041002081250030140d40c640c02640c94214003c0c0c00c1c55a4019400400d0741004901d012882c9a1450890075900d403811310300c0e243d2515000d10503940c08070300f05514a50190321a10801030170007040442e40204240c01c5007841e00e01504040300881c5480341c5002e4000c00300268415840e940102e0b0b0320400254000d556035692 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455990251 1250 455989001 455989033
    0xd0b090106021c0e0a06053406060504060b19140c15090f0a1b05040c0525050309040e010f0608060106110f06070e010302190f171003080a11 62
    0x102d403c5403400c114411103481c3c0403500403c0781d1003040c8000380200d0a0035003030102c181c0740355101c03a0810700f0016261340c4040c501d80450fa000c0d00d0b91100850440b43c4145a4985082524180d401c642c0c40781703003003650a1140ca40200c1c283d9404d10030b41e401c112440700111400350380110070840e24080c504e50000b840c88980d4800148800400e800c2d0004944035a40e43c0306854650f01c441954011640102c440c200104102000c201d5240c41110200a4900d594400150843d084a5030b108007245c4046075101100c02064240e15160180c022450015801076440c039440744503541049120b181d9498089030040425440026200c0b008034003005115194506550384181c24030880c0000350b420012144d0380e141c04141c406404500200401c82034030356400641d0039596044107581015404e2055540c00301da8051200d14505254070745141050b40d00c4c10040100a80d00328008929204c5020721091480307410b80d03841140d0700084a5902e407558400111028442e81190a515200d400c002e6064100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455991501 1250 455990251 455990263
    0x9080904050103081e0306030a03200f01050a0605030102090f040c020a06090501020c12070809010327061b030e030d020304060207231506011e030e030f07061503050a03050d0b09010602 81
    0x31200c0801000f0fa00c18080d05e0425120483d00755402d90006800e03200000d010b5190100580c01100c0d0004180043c51684c6184ca6200c010703112042c3c0d1614144408008184188005882e0030303002546406034003000f00310000103200e80180544d6440c006d80c68214801d000c1040e10351352081e010310400a1a0034031a010350000c4584042a00420f480d08d42c00254020440707510759032111030030b4181070140340154020851854030707098030000b2f4809c42c0249205640f1506d000c500c41c45000500c40716a02c1c903020300d55407030015002450318144480c450002c000040d07424500c003004015a6a50390352800b480607002c0d919000305a4510f201c07040f8915150f11a0090300300c44071100301d503440c1d040094000e00085042e5641404240209000c22807400e10b2111001c0c440f4103401c0206441521506a500d1607004002d68595514081146420003841d4014000701101c0c40140005003800d503259192500d1505c00c000f01403100010300100d00d103c2c25041301d4030310480100404074540c1c2d9590b010b5200c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455992751 1250 455991501 455991517
    0x18030c030702091021050106030f030203030a0b0a05030a061505120601320f010314011d0105030706052b0207060b1f050405010f05091203040e15090a0908090405010308 74
    0x2a8500005413244d01d050021400b2140100880b03044038030100d06400b100104d4000980e199500d44402002162000030400200751007580250766071710745904407504841c100041a0b2080c106901304102c40d903000070340791240e00d401c10000901c02801892900c0c9030b0311203500c080c0d0468a4030603100d541003400329102c0d040f91021030318801c00c4441c00c0c05a5400b03204075210780050202d820000056404c2001c18801034042c10b0400107080600e011902c107400b8402d034000c15254600e2081002c6000041840344e0040000764024069030742040005007080c014034550100d01c4111b81d102c4800403c9118804000e0000420304542d5001d8a05144014010003958140210025544030075560350b850700140c0b65010b103907502403d1605120044605603501c00d19002046000d1000101960350030700748805649001000b550f549141071580138220301c0080041203031951403501c0900b140c540043e115441440d042d40010b40c8c640a261a0031103005011006130018940f07400442000324a000419030a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455994001 1250 455992751 455992759
    0x150a0c020d030908070809010e120d0e011b020907021204080105100b180121060f0801110a020d1b060c0c060b0616081303080a02010f0614090f18030c030702 69
    0x207600c0308025415078405240c0102122020020a401329040780c018002d2400145408071403e11002d000403130a140c880d05119403604580050050075810104101d05460b00f13003003000030281c440e901e82c03c1c90403404802074001c1c410b8400091142c0d100b88690040700c1c00024809441c0c0c2d0321030100c1402448111180e40d041c0c03100903c0850522458802d03142152140601c0b42040440395004680b80d401103031502d03c0300e400c900150030509100d030003032002070142c409062403101c1c60041190300752194081c1188420208000300f0601503404144004540c00c3ca00748015481040407010301c00c250507440181c2007a2800f44455203a5074480108400703a8042d072400d00c049480c000400c0380602c1039000e8819001901c122000c0080c440502410403030300300203180701403e079882c1c40c0c0c400294031210304040141d5460700c0c404d10400d6248111400780ca10100c8601c00c00710414042900d85001030700304030f4004039503130014040b940780030013610420ba0200252622140c8c440425950b0342c01c6908200e01c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455995251 1250 455994001 455994013
    0x1820070b0c0f0307140d060b07060501141005070203030d1803020705060a120b03030d18170f090405042a03060614010819020f030103351b150a0c02 65
    0x20844610203503642d01595103092032542e02c45036015648044a115418802d000c18002107407081c1c440e21480c001050940305455403480c01d4900b05044840581154600941c20100d00b442621543c8581c00105c10a040543e40c038480d60001074510300604002b088000e003020208201e0030214102e400500b84071b41c0071142065210002c02140d40500c1c69011b00107514000383c0d00ca01c40040d00400503480c0040c060f81e1a01a03940e0b040410354490001c52103d99510352860401c01c04500700e1036050300b424004190805d050f40f03070403035100d00c034120340d480c4035a8880c5c000c80c6c2403001411b00e20030a504085850f02c0e802d2a2680740c20220f4460b480142c07455440c02400044039145240d00e14003100b4140e450b803480e030f078800755824070090724100000a202d40c207010000506080c5801180a580030b80c000c245800c91010b14072a82042111040c0a080c1640a07070700b5034100740005540b00700780c001a000203884180d0399500c2c5824402400d0019400c40071091020112159201900000d850f5086d281 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455996501 1250 455995251 455995261
    0x51b093a0b13030e042d0c0f09050f06030421120b06040302030607050a02100606121a090106110c040f02090f090405031c06050303130611070506041820070b 69
    0x1c050300b42100043c001c02e4401030020460314141d0f000c0180e0300e58400308100b4039103a068410040d82c4100f94620900d03aa1500700c0d0100b40c1d0030082000d1100b0407440c000040c82d0800000c128078240aa40781c4c1d025035808404141007050f880311402c1c91500040150781c040041c50401040d408101d18074000c40f529000800080341001400c031800d45e5005002041d1a442d1010704071100d600900360f4000718002c6856942c1905440d0099031700030f150341e0390303110369501c0610008000c45030000210010144251415816a11040d03101d03070440e80203090145411160555440c00c00244014003070384a46030001c0c01a0a13051640030f403c0292044d2a009640780322102440140071003a40c025009900a2242009003000100810b1281e0040300021504aa07202d003c02c0c510381210120b06440b8018600601115500207100c0d132000b4000710042048510341700201c0c1940c8940d001d50301503071403202c621400c5280c0c950003036142036070410034994450039040c11604040d006a00125070290f04200895 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455997751 1250 455996501 455996521
    0x1701050a0f150b07110a03111005030405100f11040806180a03080408030403120e030a020111180409050109020d0318230907111c0201051b093a0b 64
    0x4000420b5084440032203908042010312542c1082d481118041d84100642c40c0c41d40f21405401c1c0114842c0008083c9012181e00300404013130014104410000117004010104500082204486415240c0024200c2c4c0c92550b203005018003852118038504000740000c3c0303000f40050110310811014044030055808080b0258891000540c00f0b4000b840003000316003c94415802540c000f44a802d002c504402800011400e4a20b40c0c404c5001503000801c8595a144d028014240c1905a49a0b0545424030100040c02d1042c000804140a2661a0180003c0090035401503d0a42e0020410000312200340f400401d403441c104040304424001e01d02c00191140d02404440a860b01602c90160109a0000340040c43c18020075110802a51584100e118042400000c64119955400a01c0c1d2484540083d0030748001600460201d400890300880e54181181924000c040890340aa581c4030f480c1080d054290b03a15001c00d8071b580c0040f0045014517620401086120f1040b5190f40e400d41d6404036074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455999001 1250 455997751 455997761
    0x9030904060f24030609050106050301030b0a0501080607111203090307140c010f120b040c030c11060c0d0509120a020721020f1002030708160b09070b0a0e06041701050a0f 75
    0x654000281c102c541076030220000e2101040004d290001c0d206a80340070210a0340c1c0280c1c0b000380072a03400001071080c42329184d507542e80078a20000521965241c0340d00d4640d1004003c10420801c40f5560505003e064203100340b031003003150065030030340340e05028840a4490f40b00d0302e401c0b01d4002d0b00119155880c1c201180408807044c050f1140010194034000a40380d80c1d1213001c080400b40c3d074403101480307241d9541c801c0364880e4005035000aa4a040d900001d0a405c40b4607101465a070310000030810002c4e101000c8405c00d100c5058041050b48607952044d1820152043c20340c4046d00c0480d100e04819030005101d0101c0d200d00001c4c0d4502001c0030788810328800b0402010303400414100341280a0309201c80340119030302c09481101e283c80a20740310000c040e0000068070081040e0b4854500600c00c000d841580c1103035000000d800000d140942050440c0f01d0398600c50b050061184403460180c0d6400c00351002803440c020200703580200060014002c0c841183c4c4250942d1510203d10313541602c6200e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456000251 1250 455999001 455999009
    0x170f0105010e0604150f03110403050a1e1208100e06010e010e03030f130302040605090603030313020a0506070501020c07171e010b0a0320010e090619080609030904060f 74
    0x400159081400441d000003480c0d0207160001e00422001070b04050011500c11080d032a940da4180c0c00300105030060648a01c0700800705031400600040c804100e0120b000030b6082c3e80492a03080b031016542d9440c0f55041d0000c0040c1109004129000500c2d4100c804188242d407000d005240c0c058450400d13224065099800ca0b0024400c0001401a0b500640000040710310060459050500e0b03417022250650000d100c6401300ca0101c9401c00c2142081d004131009840c0c1120480b10501e003100102e40c0c2c0b408001c003100d03911580010030301c00b9900c1e400c006201410000d010070303a813a050350410310301030342c049a000e202d0b5200364080000d030005000c0c0c010ba003031040c400182c08100b07229070014000c50b401c00400c0d5403c0d56502c0c0000070f25a03138100c440c0c00962184000c0840502011100c5440b102c0302d02c0f00328180000d00b80c41c42c4d51550f031000880e41c880012103849903a101582d000c64600b2006800000716442940244000100000040d0914500032141407291079150f030303164a034031010740c4a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456001501 1250 456000251 456000271
    0x1809100927080d060f1205010b03060408090105030c040305010204060512070e100c0606170a0309150801030f060b0909031e070b010e06031002340506041112150717 72
    0x8020740011800d40040c5104a0f0072000420315648400c2041060742c110b80c80200c40381e41000004041100c00e0003440c01801044024146a2401342c403000300601c51903110904100c0f0000010b840c40880d1400d450103160041c0007191916103800000d000b41e40204034044281a2400006007414414040b0801026002c2c00342040c41600080030390301c82c981d5101c1114695140c82000c16a50b0380c04e55007844040840c0001c1c1403040003800d001d84103080303036001605151410b062288210b90031100da80c4c112903002c806a403050107107081500c01800c1c03940720650b0007c000d80c14884a00c0d00000641102004c08a18046085a80110300c40900c1220802455114002c004020a5154255481d4400e40290a0301c200c0d180c0800c00c5000c076803081c0c20040840c0c07500c910081c1c50300350200c0c0c21100a14004540c82410f00b40381c07034907552902c1c001c100034009064403544c8941074544000400700701d0742d40001c4a44c010641384031182c64480444484000590040c0e900000c02d4400502500558105c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456002751 1250 456001501 456001571
    0x5040203042d0b150114040f1a070203061302120d0e060a09030b040f0c0509040816060b2106060906090f040c030f05011a01090b04060518091009 64
    0x484851003028840e21220120b1000b1510300c0407941e100320f9103209004500881c0d0701460520005070401c2025154240c0030700060206110140c076003160070050b5124290800f4191640300c20b40300c01485184802505402135006015800001030182203e1034421580e152030400c2440c806642c0c1d11640c449940000e0610880141c1c500b02407000302040306441c40c00000041e2261240d03c08100d05603800c4644120300c800c1d400030b204d603011440001c1e0000322000015030409446800907400350035030109003408a042290100070f20380e0311407600c03240d01404041002c0c0c019500c002c080944518180024003401000035010324281c000f0301d11a075001410499240ca41c83c00381c840d00310004004403101d2107100004004146840b02c0095180d1040c400811001d40c003802500c840302d40c40701d01d9130500003001d00078003027071010500741c60070350310207140c510f0b121070300c1c40d0710001ca003050070a981e90440803070414440c440412080310410f8500d5510240b1129403591007001c44040342410550350151a5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456004001 1250 456002751 456002783
    0x2009030c19090e07090e0609010f0603030f1227050105090102490e0d0c0b071107030602070c080607110606010f110f06060a060201050f0f0403020a0b070c0c0504020304 74
    0x66440888010341542c211010980c17108040e10440e62001448201507000c50b04000c00c1140c2400b6038070515107140c2050254a186540150103d2200d688001c01c0c04504200d0002c204000c5d44500405c20804118403012200f582ca522994400300e481035400c0c3d400c1000180d003d200500841d01040c0540440d03000b5a26180c204070300038520030400d079610305089130035041102c01415405180181a47c1c0c002000f01c04403010034a816880454007041c0b10b445852038000c50b18486120341d10001d142801240440030303044590400d5510f400c018591303403000c0740030000d10200803c100c1c00c1d03c01000c21a909510f039140107851054032102407040e6607011074001201c039403040550000c0740580b400d03c0110701054008050034880e10525031903d59010008000c498a0081c0e40000100030f9400204100d040c4034280c101780e070360024910301c40300c6000c0010130304061007081045556500848104d50508000e2001030030059a49006d071415400c1c0e540216180ca081e200700d0b401141e00020400d603d8040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456005251 1250 456004001 456004019
    0x3070309150606031a120a11010311070c0602150c0a120f02030a0504060606030c0903060509070b04030b060a051008240a1d090604030807122009030c19 67
    0x2140444190065120242201c00345000d003a0140c0101d40f40454003121101d200f035400e0700511545440307440d1a890301d260382807004c19400102d68004d0b65841e00240400010303800b500146d003003a43c0c003050000308001400011110b24040d60420340c00d603031101c4c0340c612107200114410390300203150391001c0040801880c01000815001da80701d51000c10505028586c3c3d0049810840e1003100301c5440e070341007000700303c420b1243d400981180e0404100003503203442d000300401c95170700004104a58400124400c0841000040700801c04a10302e95070300c41d100e24140d035030070300d06807202402020f40c803e022640c1d00d40900c601c2c4201c00241e84542c3c0355507502c080e0581d400c0e000349804007004520b00c6d41c401503482d69010703600a403920007514211000d80d8031038210301030170041000d0b001ea00000181f000103680182d0240c0c00c11058078001e8250352030751550b00d00602c2c00c02d0b02c0890050612039108524421000988280d003403c07425078a40b40f91030310900480807030034807140003000c0345102d050104040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456006501 1250 456005251 456005261
    0x81509010f1e0c030216081303120c05010b060f0d0c0327050606040b03030304020d05011e1d0d0801050111030d050901200405010207050405070507051f0e0f03030703 73
    0x8918004a0001c448805200840da40001030303448000040c01d0a080000b2280a07498040041d8901103180c0740210b400c8120880b060b1400401010f80003c0440c140365031039030648003541c0c0004080128490701503002d0300d80d40506d20101c1d1a5400c1114582203450202c00b69240c2012011010b40380590b44d6803040000c0004122039800c2c9507803880500001c0080007282c2c01c611507480c080c0c4203015903504026280420007030510780b16604046d5088120346012050ba600175130706855256000000d481d15a0250403c42c441d91034012800300080c6210800d0f03048008601551300e81d003680303504e0a60300292a03e00c542c20510214000b170004004d070354400e200030420354502d07405881c18840203c00d100103960066501c011269161011442d10001154000703004001100c4154501480c05002035160310303041c8900342c4180d941c0c900180900340500c0440d0788003580481512030074031130034902c10f001d42242e5080f11182450902d04084a080000701120500c0c080d000070342c1150380e400c44c210080c0c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456007751 1250 456006501 456006511
    0x71112010e0a0c0602010b120705012a05010f050903070203060420090a0501060206090a03021c030f1b18060c080c01091203021c090209040f05070b1803070602070815 73
    0x165a44400c030103100d20900100c402c05100340f10704801c10b45070101c02401d5580d00f0308120700c02e15450340700b210458000074083d022242c0a08141400348c0c55029441f40d031000a0b60a101c0d031f041c0d90b0540d2410080103600070030040101c4c02e020031507a101d140220740d81e4015100000d40580c4600040b80100318150340c3c10441a0703801800024030441070b404a140f00c01c1c140d8605800f17580b1350005005154046c840d80d54000701040041c146c81980b510001d54510a0b03e4040000c0040c10b400c541100d4401d402c15409400c01c48410300103050785103a40b4a04640c000002c00005038441d4040dc00580c222141d0802c5501c90343d11240242420b4550140b0399002080420b003070340d6510910000500003007001c4004261680700140c41700300c8540c8e040400521820143c503141c0c40c0200040042c3c0d50414040e0304130380c1210811040c80f8107071600c03501d80509034001c0703644050041a52060b0403000d03480807804220a6041e52a8180e9401d0241c2c0c0d149890301a4044a400a111866600300019065039000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456009001 1250 456007751 456007753
    0x405130e01142e090f020301081209150a200d02100e1f0e06070809060a1e05060a09110d060b25050709060e0703150f15050f030c031b071112 62
    0xe03503070740c1c04e0404032046110100025034012004100c0044240051800c68450380070032850140d040380040e00b0b031143d201d054103079001c0105d10728068500c25610403241c104402c0c03070070030b90342d0802c4059640c0e014a034840744018803502098081d1202640981880c20a05500500303948004012020309154580b81c40c600c19903584202c55000e44040161a010b4503c1b81caa402041c145006400c1c24980014024a0f40d1420181400da010442c020a85d040400900e00080d40c0d13100c0d2400101070004d00d80c02400030604200d4840d80c1c0314164001402240001390b001c1285540d00c032000d1400340161007a010281c510268003502030202901c20b00c140714821015030300182d0311403828000b217886c140c01c008c2c0099104001c125060b5054420032005a01c0416940001c9250404001415100d030181049080d0344a030606107290152050303c40300e14111030402e44034508000000e8803500104c680e1043c24643c545070701c0810090030105c8201c60b410103044400d540c200030a105007441c24100303490741 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456010251 1250 456009001 456009091
    0x602100f1401030b0712180308041a090105070f0905180402060f0301090209010e0303070b0105011b240c140d05060a0b190320040302150405130e0114 66
    0x40c035015464881c080c504c1020701d62181d040840b402007074400e00c10752003800f00707151820352851807a09000482455034140742c0940039640c0d41c03510569040303200d89900c0122040c0e40501030480419000184204100c1c0d490050040340960100e441000d184107841c0c00c9244072540884c100380d090166a803150001d0404c62a10700c1503211452070b40d000740e102d00d030038541c04102c404103984d00c44511170030400d0032001141403640940724082c61b0001813003600d060144403240030400c05503285d6201e0210f900164070716491181000c030407d8618152008049440c03400c00400c174054022141c103031010750058241ea0510300c0401040300240030103803140d540564118070006200c00020003d2005881c2c50900d4018000c0c040703000740170341e40e00306a02c08d20039141c0410402c2d0780f01c40c40c06031130403070380c045a0306034004209901140b06481560004c40e08540301544c14a100070b015000302d04950482c000130042c0031001142c0c0202e01c0c8042e0794101c0d40f0480e8101085504485508840c4513000c3d0840c1d10345 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456011501 1250 456010251 456010271
    0xe01090902032a04090f110901030c031104090506030d0504030c09090807061a09060619030b04090b04030f0906020d080a0f0e0d0c02030c03120924040b030f0604060602100f 76
    0x1c031100031050700104150f0002800d11400220f0300030450143c10411341444000e4000082c04100e000310885c081c1051354171001d21514138072035001014502060500665216190300d101406414101c40b05270091140400c001d941c1481241203c0803240c010b40000030f01c42c1030104a2000c0d040d12241a950508180030311408500d0038070410880444105030b04100004400503c54106001001a44240c41c00d1007015242c100300c00300848110958503000400620a00008006244040010303000d20452010402090b800c03822a2074140d002e900ca000740d150b03407038008982d2400042c000e00c0016880c2804a9041c200d00e410120300010252004100e03455502205407030308505880410001c1c60811182095003000d00110307180d2401907011303004848a04d401c3c00000d10584010a000f03920f1003160782466a514889542c0f26000800510b60307a40c7d80352602c1c2603a400c103179060703610240c2c00808240d40785800c1c070440e000c441103078014003c1c0c002400d054000400c900310390f40c0b68660711401150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456012751 1250 456011501 456011551
    0x60c071e0305010203070306180b0307090b01110118031205090c0f0d060e0d2a0b13050a0f020907030b131d190317071b060e030c0f010c0e0109090203 66
    0x5104251b15600000c4803490054080810260740160b101c0c224980080801e442e00d0102d4542d0641d0085a400308007226510012940d584044040032680c0d46400001c1480842040c00d40b00c949009956402001000300c00c0300e011501d064907908101d51041501314100e0920350b1060f50b07504001020084020b0303c070785580c4207944224100d010207401108146950795000301d44128840c01105c404810b410b240c800000440f1040b24018110003101c0000403407a101c403002820340b803980b00059841900142c90805c502414140c4101d2151074000b0004065030310030310810714420380060145108113000c44249004000d031155144810408090038088171804001c1300600d66224007103016000820306004009000303110104640d0700c000d03014404115440a405030040b5089601d04a540400e403508200800060040750b840740008207106090400c081981c480801146009029030005560100da40419426040740070600307801c418020041c00754043c550240540c1c20300d40040054896071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456014001 1250 456012751 456012757
    0x3090203150916081f090c080d0801090c0806120118050c0301050a050c04090c050712030902041a0102031b2103040c06050406050d0506042901030b060c071e03050102 73
    0x5100002912024481e4482080110400e40514240f26101e40ca042407078094032101070104940340101040100c0300c000c0c00d540d0198a240f0f40c0700c0881c075007442e075030640b503900d6410010001021071090000003810380070034001c48208829640d0b44000c03a68030681004003d020882d844041d542d038486001c103400c1c44420006d00c500340034100078401203c0d5202010f080d503c00400100303406050905004011745960103590945520340c1020402403002c003000c440c28001d502010b042e42c00c01d8a414081d42d034040d8089440c0a0003a1800d10007510190100f00540d1132103000603006a008001c09011035200d1000320208007900401d4640c415001d0010000c191464100340c07a002c4400030a1008005080401d20002c1000b401c246080c0f51034000003500a0041e0560740034419158000202c085e520b40d80150030038801d000020ba50000c01502c520001415840180d0101e4508010034101d8607041e801d43d9070308c02c80040101201402c1812299051a1000c5080c984100380000440058000c0c005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456015251 1250 456014001 456014023
    0x307030f022116081314100902040b041b0309050c030a030f09080105070c2405010f1707030b13020d080d050615090d06020c0703140715110c010305060103090203 71
    0x3502c0002200c40040004000000d0319980003c1450003c3c0d4104a80041c1d1050780501d2644810144140508044081c002c0e666006516801055454002030213558020305d961402501e082203540700e03150a00c021900401803894102e030925404c0c41c0354a1181e041600500c0c800d80940c0e18841031000070a19021800e5011000302d20384817240010700e40e00c0f0000600510040c4020701103410b01c554003030b00005440c1d001801614a05100c00c510302c000d81c1c4d08807001507030b08400300019a5601380c1240d0f80c0e82140a1002e0075000d4141d810b015550000c0c010054030b80201c0303822115100c0d10580200350f4580340c0203d810246100c0060b0219000002400b41c4040f00d50000c5541e1074030104014039550300b4003031004440e00c2406400c913591500360340710240a50041005070b07248031000050b80317041d1141d480101030302041806034010180105c1c0d000d0480e60740c1c090b0f80315030704c00b04042035a2507048800c01a9041d40800d071242c00e158881e812403600f010b410305001812040da600424144190001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456016501 1250 456015251 456015277
    0x1150314160c17040311062529011815181e1b080f0703090309080a060e010b03010e0d0e0a0b1803060106020309030304060810053307020a030204020307030f02 70
    0x1600f0001d02020300d1b10b000460f203084a105103000b07010000c45a1401012141407401c4004006030010030040a48000e00c0c100c0e6090440c000c0c08110f5942c1100f04024095020701804642c0d000b040d00c400381c0201644840f080c41d162507424105080d10754103092040b021420344da15840c00c4001c803100b03c645650500b50440002c559500250300740010019031141e04420402918200614060048074180d0070909520b00440d594030b903410304658015213038104a0288c064860f1107810052154000c1c3c01d0000890003d010030300d40c030780416089800c9281800300c02e400c42d801e13500c10710b07114150170041c980005114846280c0c807810580386940001303521000301c41d0340d122031191518081280c2da0041c0600d1000b146800896408a41c40c1d001d00d100d910140070807100840e1200802c0701c1c0250141201034a03100d01c4030062900c3c0004a010b14a500300ca841c103842801c07828005050845030341a0300985030485143c170303560902c0000d50004102d28100b60355020000c440d005540010200e12b86121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456017751 1250 456016501 456016507
    0x30603030708160302070806010f1e0302040c1206050d211803060c0314061c030c02030d050a17040b010b0a0c0c0803030a0c030e0627011401150314160c17 68
    0x444c0281c40c200c071039000402c1c0c5501c000010007008169100300c4007507030989020407d00d214040d1400041a0355500002e5205003400500d004c42c0c0c0d801440308000d0180da80302441440c3e629401d0184444003600701501d4003041048540b0a8121403a0745e0002682a103010b65240c042d0102c11240c414003900115440e54a40140820b02a0706008001c0c1c0301c0c280e00c0c502141400c055002030300408002000494681c52000f426003414016100000a0368000d400e55046400185000f440c40d0b0140100304040780c01710b5440e90705641000e42d00381c07003690300074101b1000c4c0c0d09220348a034060f0414002182082402d400e03000003e888580404000d001c0d0a00035501ca05002c03a04500fa80c114802107070030507180028482c400500014100d8005800004542c602e80101c0320301040703070700310710400292503081508070802c69900d41c407854100c5419814000c2d201380388a108030243c4002c180d0a000d14001e03000414140c0c0e00340c00051101500720304101480400554410f0040c110a01c08102101404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456019001 1250 456017751 456017753
    0x40305010c0e100f09030314040f140909031c0513081b060c0901090e04020d02061206090f04050a0314190509030d090503070303080a2a1e0c0803060303070816 70
    0x40d81c400780301d00d2014113110094112181c00100311406610019082103480b5510f41000b03104042100c02034403c2e843e40c00c800b1600c801c204208414041c1410307020f000200c00042480ca4044203030b07240c08910b03c1d1851100c907221100400601400b82c224616080140031450000700400000c1c0445030074200a20b034840342c0f404055081410051510314110403c01181e101680d22007038000958656400044040d141c900100351031107058440250842c400250300403921102022091280700b003244d206102d595460290f0540301c60580780133000d43c1c05a40d800000178000c81c2440303403204c0801c03ca00c1c02c1c21200030710400fa1402d40048400441c01c0001c1010325402c09000460011100782081e8240c146400c1c017080d5140705521001d03003008881d4000c105c01c4083e6400c0b404124034058120184480075032100821503600e01410004212003c240b1400e401140300c00300402910b903200c100d031000b0252111907440d070008041e13507854081008140e001608000c050502000303003007180140381040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456020251 1250 456019001 456019009
    0x806070e010e150c010605040207081e040b37030903030e0a030f1d1e10110c041805060a0e1203160e19093305040b0303040305010c0e 59
    0x10000c80038104092419501a140c0b074404030200320352101a5820342e5105501d400368010070032034004640c020b0000501c00d041c4450781d400b0b844d020014000c86400da40708203688440031700c83e5204011000b9010322046101640018004807030132110783c0c000c0c4212081b0704139400c00741022400200840d54401e03284042c954180b155000e9442c068006108401d400c3c0c070003805640c1c1c81401c5000b04103003038030040505802c1c0c8014501e00b6001400070340a5980040024040a0359650058014080c800342401c00702e05c03c0d0701111400d001140601005211b60041c070018145a0001940054100003404001102000329a02c01c00710210005400081c826050b400d0102210194020075418424002c41038001d0314105050361440c1004044180e951000c60303100c808440140d0400c11507400c002441e5003c03504010402c0c442e940e500070104000c075814000c21582410141e10400e2609810f01c428201035210044200006046038201540e0303076500d80c25901c5080d01500090401500501b160070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456021501 1250 456020251 456020267
    0x130f020408010612080d0b030a050a0c1d0723041a0c06180601050f0d080a0e100221030403030b090412020d03020306030606190f0609050a080307030203030f0c040b04080607 76
    0x15200c0c0415551280c1c0d100e17580c0070b004905030001e2456540d0045405941c082242406460344403050b55111075040c01d01071090102403049100942d4603040c1c5002008062481d54420580c40c0c0310780c8501c1c24400c8150101070300e40c10803110456420000843c400d41d800c2c860402000074201440d035101c10041040e820500050480c1100f825411340f0110300c4407000c60014103544050b01d51031498560200014004020300c031000c0c008280004110030160340c4a10800c407115010384808529044080b000c81e13440c01322004403400d000d0b148001511000103000219002070080c034006c12080308801c00034600c420103850859621a40f20030100115805100d040c86e4500305060850452a14401294581000230040e501c6000089540780340c6414442045028020215400e01e01c2c0d9100c20000d0019001c03400381e180704400e100303400105610000100c1d0b910a9042c1d010710308580b90b60000041201c00a0400c0d01c00e40c2c424000446c07001d1f20100a4030052605400811980c10708481c0a000c1c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456022751 1250 456021501 456021509
    0x30210020a02130e010902040504060b01030e060c0409050a0e0f070e01141305040515150a0b190807091d0402010305090a17090616050c011101020c0c010e130f0204080106 75
    0x24101c00040d20150340c0380110500301c0d81180401152484440b0311090040c000300d07000a60180c6414140414400d5660000307192400c289c804020a00e071041980e503072440300310352a0300280801c010a20620b06580c2102e9040a10b103500801e005040c1600c560810348010f02065030b544c40704104002c140e45941c42e10f401003020b890001e5a95842801040c514400c0380400da600c0d0380c441d4041003c01104011100321a2040520302d400ca08000b281c2505030020064a288261250304000c543c0d801c103c6c0840b54a010312400c801162800b0780f000382d500d51401804401480708900c2c000404103828089000103030140701d8112007600d4188005000c0319405890710406500c24011540021840041c1900503802140c0361901d891074100002da19100c0c0200c03020340c1c3c2c0b99550140041040004080d00201403d0301d8080500034800c0ba81402c074012207031108015480340035088a65405450403113500e0f100071b00b0700c0301042c8880c104042583e05c0d1a99145035691b00280400440340d0030300c1070704090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456024001 1250 456022751 456022753
    0xc1203090b04031707150501080705040b060f09040902011107090212070509090106031a060d050f0f100e07110312010501031d12090301091401020d2a030c18080703021002 75
    0x180c210348480e0403000c0e04c10070079031200314009032920510168849001c41c10604100030f025070740c0c58440c0715032031b40c40c144a010b003d00d00340312031088203160242c01ea52055807031a880d58181040881048064003c1074400d0f81404060904a03007813010500ca000050822040d02580d640e010300c42c000e01144000f0070440800400307004062040d030328681c3e441c0c1151614580072500305050070001480030302c2d6884c3c07954040400268141d05a000d608498841d07500d54080d81040d44c0c462407100d0300c1c044100c0e0048a00c0e2051103060000305000300900760041e07150316111b410030016030b02c079a280d0762212207030311f41a10501c1c00410032580d01d4021201a080b0004030704485c502003140041e80c50803060995001c242d40030440d4000c2d5202503000400140d0402a802c645290ba4041c980c000c0d4031940014500c20f082200e1803954040c10780070b040c80b992a0814017402060100021001848450382002c100100d01c0c001d0300c02000c40c41451000b1301485000b9209280c036502c1089090b000305c120407415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456025251 1250 456024001 456024007
    0x402090c271302070c031e0206030714120f090d0f050d0e0a06180b0a02030705041401110d050903150702031b07030203030703082202030c0d020406030c1203090b 71
    0x1140d81981c08030548000d441d81c0035118020080c001030600c0080340c40744000703600c0850004184000c6000090890b40601c40c05155200030141c4810391034140d2602a401410030000308441c94030503d0447c0e0070406800d034160400c4040082d20207004000e999001a080d4140140114aa0203000c410890710082c24000e203001080c0c6000340c0709015009103200c1460f5030301080080317840e05111480304a41c1c0a0410800c24030140360b8290f0503030031420183c0310394001c100010380a200794422240600324584607241071620780712810100701c0d600798242e410002104001c620300b6800704002e580c20b0041e80c8445131505029002e0510386214002913000e013100078414007200300d80200c00c5036200541d049a41c0700d1008240b010f1440e20ba082c2d40025010303c000103c07030050507030016010b801019005078079500c9912022a8100b40128070102a41c5600040610b10301032603d0304d483c01085101030004551107680b6111042c1078801903110b5803003013034590717482030030968886118005000115000d40c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456026501 1250 456025251 456025267
    0x10030609290f15010e100314090d020705040515030d09080c06070c1202122b170c1c050f1806040f030c060f0207050a060c0203070f1e0f06050402090c 66
    0x20103002900fa4240c042c49200081656440755078000d21a410190582a014845030b2009005001d582d903040441084000810500b40e004a00116121f015a008000c802e0410301000020040505000101010fa0881c4055610284648000104140c0300d403820545070151a504242001203054403034903040140f413000408840030081030302e000e03400c0031154980038804a121403501c030704410194400e143e240510b8100c000c5801c0714445401b520081144030003079042e00c1d6003105101a4040714495400604540210300c0504800003003004440d0403104461404011550705496014003420014100401035035170880c20004017810f24000c00d002e1506884080010740a0301c401020421902000400d210300c50700a8091542c00407000c5540302c0080c9020303990341a01410484080d4204030f4259004ca00210643d4015500300000d84008051541d50b604036100281a0114001c082c001020124290440640035588a1800002e040c02e141c01001541a002080c002c240d0304c003081211 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456027751 1250 456026501 456026521
    0x1506070b0a0207020f030312061c031b080f072d15020c070e0c0702010305010801020a0504170f06071d03060105060909040501061503020a08090304050a0e1003060929 73
    0x207511080d030394030050700c41c1024400075540301c0c245c84245505102c0818680c002c4041c0c40b186034011402281c900c3e20000d03c00031445032407180c015002c1c0c0890900f00707681140d503103256000c18403580f2858999140400f10280460b89800c4010180c0f0114454480220040c01d101005e000d072044030702e081c03184c10445039541141c8158042500c0540c1d50081850981000100504009450754403052122132070000b41040c01a00510816800207081000002d0a07440c1031003290692101aa1124070301810500180301610000d1000e126901c00d003440f403500b02606010803401500070795280702030300d13403124182c107400400c14034054401d4001100410042e501e880c101c44400005981003071160b0b6039414103500500c0b080d03010b00402202303c0040c80c1e0f1a60700d640280300d0000c039a240c0c4082a21103c881c00da0b40d0180307005e03c079005000314a00748404c080c10251542d10042c417100700d9003940e40340c0d65508240c521a10044a600020003031000b98050202e4811420003005034010706a80387c880c17502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456029001 1250 456027751 456027773
    0x1903060b0f0f130513020c010c030b100507150c05070314190e04020c010504030f090e06060318030c1b0406060516020f01020c03120406020105010e0103030f0e0d06090506150607 78
    0x202201c0c005a80042010015803000c02440000c0c8500d079000c170400290006581301040c0800ca6520304880900000d00a00c10751a600d000940340c0020211201001d4070a0741c014030f020394841c0050004e000c41190113004100368000d1780c0e5a1f043d194207051a0140008070010400c228510f000d1102042e2849000f125042803002d81c51300700f4515603e0340110700203104200c0503070820750801040200381504404002e11514050795055a0207940d55044885a0710075203010703603c000d0030070100b024000c4020340d8281180d0b101096901d4802d404503620700e041040c0100e501e103102820354002080c6003900c90300008010700e08003a4944009071a01c2c003031039001c150b002841100420915202c0e030340b0070802d9544607072000d002c4809000d0f008403410226001031044070300541c202800402e50303c800300740380760480b075040e1214180f18001c105d0581d050502c10850603000103c40322032a02140c030720b000300c0c500b16014001625844c140080080d00b042d00c24000680920700c10040c04000035660400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456030251 1250 456029001 456029017
    0x70f030842030f0c091b181302090604030f021f020c0a150f030903020102090d0c090507140f0703030b490803090109020d0c08100b06040603051b1903060b0f 69
    0x6017950556900c0c0440e10b1202d10b1500c12800300e41c003c200e0b200c9400780075141c040c0120007100c400011180c004640300c16031141420300c1d600240c0c02e106c01c04c001120001c0d0303142042d1000f4038811030390b400244560300318000c4000d00401a03100300618001c80c100464000c014103a01480c00c0061407171070502520000088058030105070b074074290031050510030350646015500c0100468000182801c0c0070311686028041d0381d4425140201042240740240494501045a100e410b410b200304a4a001c3d020381006800390181910344031286040d40e540c819001c0340b80f201c01640b20802c00b101079030070006003002c108201d44211032413030108140015041455903643c482042641c0e5664a20614054064080001c0d00694032018400400c50240303103a400340ca11080490340009603100c030480c1034443c490a916000301d0100002e1100a11940003580e0020300d034400c01c0ca12001c9004403075801da10030300070040c0c10202e03c0e00200d0010707803501a01000f494641806400c058142200003407038414442 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456031501 1250 456030251 456030259
    0x10927020105071a010b0903010e0102040305060f10050306040b04110a0f05151201120212060c030f0c1e1902070f350d03050c070f030842030f0c 64
    0x252000c200310780700720800c01049503101c0380c4d811542d58140d4006c5640107a54010302c60350a08095000d541014800e0743c0850b9044001840c4a48402c40310209800c2c0182c8010b150008007080450a520200000d5004071300c02c0c1644500c5183c20b05000700c02100d6950720512a07004240204a1100050b48030410b40e00116858440c0b42c6010074200254401c50b101e101250100800000344103007016084054607000741c03002440b8071074500301c4640764007040b10050013200080c030218524401030b402003548604880c85003860b048000f8021540404410300b5403909030000a45000c0010b417140780a8284007042c00284030140c00c0c00c0c08050500111b01442041850101207650700c41080e041841a14400c41c080720340c500358100b20780784c0f1a11301c41e0594002c6400d250200b01c0c45546c1904441032541c0103144000001400ea03070403622684003624031824501010300c2030118842c2c20030109000d140300d129a0014440c0303903902900d031040405040d03103c0c1e00901d00042000c1d4020881c0d9200c03c03400c0f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456032751 1250 456031501 456031507
    0x100e16050f011209050d08010e070c08090d230111090f0d06110a0201020406020c060a0c020909071e0302090604180b06060d0608010b04061a070204020d061508010927020105 76
    0x5004030380000f6005400d110860401414a06010f004181c200d524000c03969006582da03229000380b812804207844900002d00701c41035480c04500400c02828010070001d044510400d681e072030380c03051400d500320101301e100801c440c40040c0754002d2048081a000101c050b90034010700f80000b907000c29172510194094030742606250200105984000742c1841c5a14001c0c2e210170300010024001e40080c044d140151050980c540312600c0c02d80d040c0c0c0c01c2030040f0341c4c540c1c0f410700c003603400c0c0650910060719400e002d110341c0c900842c805402c031001c60b00f4418110002c0b06494070303600401000f498060b081e54051440c000113245c20120340700c0c01d2120140c10203100895030321501c0204075940b148601141d001c0740741c1880807076501c106401c41160440c0488080c04000c0d1600c0c0504400a5480101415007000b040f0400060034140c000d4004071000d0800014443d5417011814cd1100d030b00d1102c040002c2030000140400e00a0307104056009840b607040d0307130b003003040075079051545c81c098480a03041c00408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456034001 1250 456032751 456032779
    0x81b04060503030a11010f0504020f010f020715030903091e0e0403170a06140924040f06060320070206070201050702042406020f0f0c040c050d0905100e1605 69
    0x94000d9030080001400303e0f640c0b110000c400601300c140d42546444154206010141e411005002d40c3c1d02841c3c00401c0c4030068841e410055602038210b920700b00640c00780f1035000558501410307035005000560b8801081056448c40c000f440c1e145c4a422104004414500159032140b90700840030503280120200c00985c0c8440c10142c50129146901c1e40c0141c0c2d0081c20060720070703483d400c113008440c156404046060043c104120a04404a4001807407003e00004103a4403000c1d170b030090004078000b520001e400541000d0710002d5032215007000b400f094079484122030300c130704410042d0160204990441d04000140d40061650720a444000e810090041105015035480758003018449458030a4180c0c1150610408a141e40c014807412000d40079502d031820b0f50550110389a56255650005031000c0c10f00b088c02c21000302041a462010840140f0040e6030240740d1f0b2150b11010780c01900208000016240c1880580c3d494044203c0c440e0031038103800502c1c6c02401f4410040d1441121010f050b0864 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456035251 1250 456034001 456034009
    0x4090b030a050303040819020c03120a0c050624270c040504020304050115090c020601050d08090a0f050312040b0304200a2628031404060f0e0109081b 66
    0x800c48081c002d40400401c1c0b00800a900c07000302800c030840c1c0c80c03810540e44d0043c020f030b848080071052550950007001e10318004d18044401415208440e040c000c4500b209519414500042124111540182401060300c1100c480309454094001210141c0b48481800c03000c90865541d1140459130120400c041400e80e0806000d54010340300c042c10231503c918143c10028080d120001345d0011a600c3c0c21000706420103607001d00c00c480100354004040b142d103898107000200d15120b00c1912107200900c04c0300400c7e40ca0801250041c00410851000c0500f06020113013002c42e07401040d00003802c1000100000903080701560b074015001548601032001d41032058122100051980e44d011511358400f00714010710810705502818042100e51408200403901c0c0e81d280411007000c0701c92075103019001801c282c40c1c6100e0f81160710a02e040703202140303440510009900a6000100410b403c003540b002c1d41d9910241c04201740d002407900c5a00185001c4440e500c079441d9140300c1040340c1c3c1d0040240502e8036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456036501 1250 456035251 456035263
    0x10f030504052a010e0405010605090d08070830010f030b130203070f08121e0c0c130b120109030503060103020d02120405010617011401060c1407030506191104090b03 73
    0x8004036030400341550900300e0703c0099840d03000484c00301e1080d140c403400324202485050706039202c6072181031804500404010310580301d00c9086400110403c02c1c50009200c00001d050300c03404800c0000e15404064a02400000d40e90482100440e0807000400003031501e503030260120fa4000304401e030300c3e0300d8408070088040c00800000e5014400c000000031068140c41d04541128212803d59019005103041040325110300700c21000d0001e0071280c40b49000f04402e00900345139141a08540d80810001c0c041017901d08904003042404d40d40b440c410815003000008602c45500d820004c00c120115568007600900024003500d04047d80496074400c0f070b0b1280d9044482da1a0b000b00380020904c0c061905602810351030240080d00f040c80721007200405c1341406240aa000503110851281c4c0c20107402b11142006250262050142241c4080340301105006450240d400760000d41340c40c0c5000042010703544900ba8032180000d150003c886010300c40402583c064a038848004588031911400007890320b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456037751 1250 456036501 456036523
    0x1a0a061e0f0e0910060e1c0b1911030f070309050d0f0c08070c0602012003010909080f191d0d08070222060801060608240312120405010b0906010f03050405 68
    0xd100d2080c0129807030121200811903210b59100c04001c0c8881b818408030082d110382184490104407400000030702540e00a5900c82802555000b040050441610580b005501508a0f203100081804082e03021405200c1d030080090805218184036599503d9a510907045880d0800c10300c00140c480082c894500400f40c0c640102c1800d84518060815003550a031600c40d440140d0300e0300400359100d01c16002580c101d4511101c05c1d40c00e5070705e00104c0c14068060b4010844a503202001004140300715007001d4840c0252410160054210000303001d044003021841e11100da10681c2f400f9582a81c410840402c080d522500994546030107102081508060031f4002900526000c13800f00d0800300c50340058100d0fa1402b000388040760380e030f00058a0590040e5448692014801540c1c1c0050100c90b14042154a000d800c6541c0c0c2c52000b00c040445400034800d0902d120624070911090150034010000d1114007210513034082c1c10004001391258000920450a1503100e100143c144501804412210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456039001 1250 456037751 456037759
    0x1093b0d030e0d0906080103151d060702070e01120807060e030c2103191a060c010902010e060909010e0a15030b040b0f01080d0e131a0a061e0f0e 64
    0x2500020002a02914103100d90403183e10a003d02c4406561058140c80100c3d10561600346599003107403100c0c43e40003604000110026241d0624001e050005000f04400c05901c0c00500483d08050600908110541d844602d03036402c400018040e1465007508810f04035400480c440d610280c516040010388a0310280b40198000416509080040442c54042344054000001d081450324502c003800390100fa120788401c181e00300d400c400030000c260320000d0190b900000c442d030003041c41c00000d403865100c1d20205425075100c1d4144011560071a16410551504490990030000e003036021550050052017824007141c0840045200d0078400d40c004820400c0b0802c4041d46142c4a042220b41440e00340c2d1b0464001902000251401804503003450599020601414030b800000c40c04035450844103131080d6002405100d00c101035940da10a00c002000c48580780265100400c08028010040b0750103c014800200e060300d2000182c4e15105242e4801400e1600c03000c45040e10403100c0440480d10300b604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456040251 1250 456039001 456039013
    0x2010e1221030106090611070e2a091203160809150408010b0f06031b0c07080601180b06070312091a0702150108070b040b0a0201020f030a0b030601093b 67
    0x1849180c1c0d40114182c80142e100c8034000c569034042120300141e01e94500a45070031072041802601080c0030441c1c1c010700300c288610008800361806082c100300202111240c00740c001800f06944c2040710000394001090ba014504164084400e482940407144d0001d00b24640064445190360318242052031a01c0c1c0340f01d1003130b11070352100a000c0c000c21500e59943d1242c02548200706080c030706441113030722500c048014601c651041e10501c07500c0703403c101c2c1c5041d05400b0341080030602520401c00d00e4020045802c1c4100035000324a20001100e011415150060f80308000020200707821640d2001c501600751000100220141000036a03078405940c1c1180980d003600602c81c4440d40010b1249105400580f192270f00c0c0d036600c6100b41c1d920014840c501030840140401c1041d109a80f0207080ea000441c000513250903100030301d14200340d0049400b80d5010341e0f204da00030300310708080189502500c0100d008101404103c004040f0988910031800b42e140c100c07a0200045d10310201800f0342c2159188100c442e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456041501 1250 456040251 456040303
    0x50c0a0b01050a140d02013518010207121103070204020f030f012106050613110a0f020309010516031e0c0b1302090601050a0c0803040f1a0402010e12 66
    0x140c5010a1148038412400c00f0b20100320100c41149003010204001d00c0c146010320079900640b011a140341084013646d00c0181058207081c00c80d032038403802406000001036103280c07140c0740301c2041c4080c4843c451181e105200301000180c914030b900c80c50f4000303410301c007152414008505103507204002e00290054004103030700c502002d03c500a07600401116010300c4043c0e0701d51402404503d4000300140010714201c00c0c01002c18030a80c4000d0704010047c0a91440b0508010b58006990240751320f403a11280002c0c03e0010350740d001c9000c100c58807151019500e04104440002c00501402e000386518004080c43c0404150050300d48115025080c0e9000e034038131440000141013180c1191040c0c80d80b083c02000a24000d1103074015202c080c0d4003d041c9001501c4010044607613410102c5500244000f405031840820a60000766224604c602000d95228489283c502e407007406503040c2c010081801c006000050b038004020400303050080e24800c030781c0000014a180b415500003104411441d481802c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456042751 1250 456041501 456041513
    0x1a0f0909031c020301081c090605070c1502070e13021e030a150f1109030a1407080703150c030b150d0b04050a0f0c02060408090607030c02041503060b010908120a050c0a 74
    0x4d41200c020005651504a24200e8000c0c1c1d071188040b898001501c1c0101404200d010f080500310344c601402e446c010071502c90f003075080e02c03040650300703000560700c03400c003c01002400d84c03002c660203107143c00e14205e101503035804541c00700e010402603500c600e0014617107815a10300300320034a5a035030410b01c00e04281e428983c0e0440207240c4030f28030515450410389442d4014400808580c03540c00c0c054000c00c904200b40e26a500400c040f84000c2003d8003c45000143320301c001c00400d0040d5000340008224104008451000c4031058036950081c0f50909080b002c9136036aa8003503a01c04100c41d00355554a040d05159a00180012080b003076005140c64240b240841d00c6600440040403c0c2208001402d40c00300c5c103980da404100c500800c404020030050030b450502c40d01900040b0b1090800e41d00e040450f900150580702d10400440340c546507100208107000301e0380a44c0e440c3382828203020b007086060030101030300c9141c54040706a01800000391310444601c01d5003110b1000a4100540e11131803d5482c0203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456044001 1250 456042751 456042757
    0x20703030c090602210309070b07051018020904060b040f0905150108011806020f0409060314060a06060e01110f160e07050a0516050a0b0117011a0f0909031c02 70
    0x1910000d2026400450481e000003900c080c5041c1100c0c0702a402d10880c0942e4a172948002c20084040c01848000a22038417003801414155101e0006415004000412001140d02c184036551060b01424240310151325019030003030300325802c000e01041007100d03180420702070010f1608200d1440d241203002d5082c4000404c400005243c940c1c611541070341c1c2c0d00107407800d030b42c0c10b000340310824442003203080000348203035000b800c08040c807140c9c41d404d281e602c418510840d10203500c00d50f202c0075a9203400c00304101c10b003c4660302c4450a101001800e0624100800a4000005107414460380440c40d03428100100031030008091300c0700071581c4009030b440c40391103540c0e05840b400f4942c144200216140d1406901911020002551068180181040d00324020340794410f003035445004142080700825044010300c2c3c003034044601e8200000103139090b110308403036000600d8030071041c220012101e50750f180f20745018000303030856442045c0e494803408182103110310b464481c40728840c070581c401002619000303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456045251 1250 456044001 456044021
    0xe1b0415051311031303110a0b0c030907091e1803020304060315050405010824010e0a051e07020f10051003081b031303030f05120118020c0709050a05060105070f120c0602070303 78
    0x10308420b03104c0101035203032364065081005011b901e24400284102e0242c86c065a880a07412040352549941c80110310100c5004032030112080380c06190f180003a00c040d0064048900c03614651180f98161505c0081d109e014a0141104140e110315210b0441e1010306081d101a2000400802075560346448280c2d0b20328850400070f030540f2211a204c506640b640021a04031080317207200c1d541c42d41e680e0f179402c802010b005243c140d402e01041079400314440002e0016104803042d40041400c2c1126200c0c561400b008148520701d82402c020070807442c50403a5151008690703014525945654040d0310703c00b00d004810105452900c00030a400300b40d9034407400224112802502e85440840502008660790320030005c492008050a0004100d1003400060850007030486510050511703a03480d10403400c10314643d000126032034450091101ca12907502c24039820a0003420039903d001c00903603c020751507450303440c007820400000c000b101006004d0f0390314a08665210f00c04558454951a0190040c484014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456046501 1250 456045251 456045257
    0x10302031315020714030a0f14190c140d0e040905010603020d210801120219170601080607020a03020a03080603100501081506010809070e0c04090e1b0415051311031303 74
    0x800c003c0d205d0100469181804d44d69440d0780114084400b45c0384216000343d00c010402c0c04014034130201115030091208000e040e5107820501590b41480390030b1240c680307141c015640144a10792401500030320085442c40c01aa8040b85a5005003040c07401001d803680007a400013240882081080622004100740c1b200761481440580c500d100704503039840b400d01441120703000040b0130343d0141c50141100c144a04512800048064594242c0351a11010620381940da070302400051004590602c49154040b4607480240003000d601c3d140203544143c8580c001d82030000040116245403014400a401030144d040d00744001e50b03580700540da95044200c600303040211481d022400641c8a10001070040d0002e030004c003c0c080c241490000b0181d4041c1c40715081550410002070003031040d00400801d0304070040a420028040c0b0b407030180f4031141003901e52103640750400c40041858510304000555a06031001100d0080e414040c00080404135028550028041b00b00402d005c9146203407011a40301e0740d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456047751 1250 456046501 456046523
    0x20d14121906140a0302060711060a051810170712060b04030302060717150d0b160219030519030b12010c0212040312080c120f15090708060103020313150207 69
    0x2010880315981c40da2030043c0c0c0b040d0041805c001501c0c0030390282c0384081c0500d0246c0004060600099960381c031003100000030400109201d0f1400070754900e0006003183c155054051410480d078014111080c00030700240e10414000401e01d058810041c21282482002c0d080000680355281148160800e220803001417103944c0010320858441c1d0001900c2c5040c058943c1c403d40c8481e514200c000c0c0250485070341010985031804040380f00409124010540007080185803404810028104078400c0004000e1b51101e80000c1c0c00650320008a0394141d940040321006283c000c0b000320060b203070800100398400d143c0d9120855403c1c06610845802c03615070211000c081980202c181580103c2c807010308a049002012240c460086c402c0320340c0f018460b0380b81d0340b0b401040100034810400c1651482c070b0311004c800c104000c1000c4070043d103c1144040725002b0f2940b40c01d0760010a54240201000d04045c2c0202c08504810989011600c04550150303180407068440e183c04002504443c2007500c05060302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456049001 1250 456047751 456047759
    0x31006050a0906120209151902070b07060504020f03030706050109050a0e10110f0c0a0b0c030609061909020a08100f0806150a09050a02090f060307020d14121906 71
    0x240d001c035980e85071152542240c8a240c414140d6444000c60000c05100750200310031501c4d0b94400096030039401c03604084988a161440c69042e424010032040e800355800854140920200d030003e66908a0340807a0100da00c2e515440412500301e64080300e5a01840081413000801c521900014140d4194050070401036581d6034404050f15801494144103400142c0d15030711458113030b088200d0a02d8055241b61031701740600c1c1001c10316070207660710f010baa0304100701d81001c000300411a82d82001e80b00d0031700c90031810500005012540040d102034400c1c402c181c0a144807a021515920041003403039002c43d140d1038801009001c0c4801182d864401d04100c0f540030806001c810070403802d4070b0703d50009200d1790b43c13a00c1c0910410800008a181c2c00328000c180012100d540303000e0a44a1700c07078580c1c007680f2941e5202c01c0c05040c2007807130300030351140c001803040011407680012032111004035450080355600010070018401d210380b045002c0703850a620104041c10444100b80c5202c1c90f020301040250540ea = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456050251 1250 456049001 456049007
    0x80708070201110913060519060914060409020a020708010203090c0a450f0b03061003110d081306110f030a0f0f3e0c03060621060408031006 62
    0xf000c1e8414084507424400603100d1300b41140d010100c0502c44078005011629440060407011400702107803826030740d105060098940c40b4100d6002400740e071000181c000c411740002403840c0207500540300c241d6808100000d400748200708103001864190000c5543e4188204a19203c0300b0303e41805020345900100010107101d041640156040b4850117020080c0c615002c0003001540d20281c4038030710425148581d0728042e00d101c0d041d045000c25000007a003038025020300d81400070003003a00032000483c0b9802c2011078854496507a100300c0460702541560750a1505407101d0040000202c0100644040846c1c1035422400c1441c05168280403542003409a030601ca907240f00d0115103000140c5a090802ca6150140b40441040d10442c2401c050340c080010411040d0b282d0b802d91406a4108121698041e0f006a90001608a031441c050590b00c154600802da071104050843c50042c035402109a0b0a14003c0340e4503080700202c80190340300d60a150070000380541041c0c581900800341410001402c0780 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456051501 1250 456050251 456050261
    0x1e020c0f0f0d050313050f010603210207140a0e0a060f050303070519020609120d03060807060813080c03070303020c0c0405070f0804050f0f030d0c02030c100509031207080708070201 80
    0x7540d5000301000e40c41c2040031103a40e007015103104080302120b81d0703420000700103101000c039030600d100002035018610b084c49034034502d1612098081d00c081081740094107901081050075039010305442d05128801501007502712802d40c1c2308200e140488028082802c1c86500114101d4245205075450704e0f4030785080607128801d2a800038000d5200039100040380e0b0203003903c0b03420940001c020310b041002c000d0220b401020320b00c1c00c16000d40c2002c0a805007140d054403a1401810802c07008110060174440d0180250002600d11200900a20703a1442000000001c03130300c140000c8800c1c1c984400581c035002d0042d400490781c50303035140180c50b00003038941040e01c201c074490883d944c1c0f150061942c0c260292500107014000b81c07060300410300001d0400c90100304502a10558000035640d88800182003000c66000b42d04070021500100600c203100080014408900c5121000000e07164484560703603441d5200301d1461a08017401e4200300f00300c1d10780000c0c41d44d00c560030740d85640380a6030b2840d0049080399 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456052751 1250 456051501 456051523
    0x405120a051c020306091f051c0303200406120612120e04051509040314041e05030109320105010609060305060a0302091f030501151d010e0a0b041e020c0f 68
    0x1b42c071900003ca1420600f0142c509903840105051105611800401d401e601d154508030501031031380c007030603040603818450040000c8000300100403c1111748403801052180c0d04c1803200b007046600482126661a1780300320014940d1005681c41c80c0000d1400d820740240c00d90a000115401c540c144000b81403602074148601c280714840d0303a0424140c002c210070b600b8098415002c0140e405c2c45140ca0224060040c400b400c09010b03032040c3c21010050030301d614200d5800ca54005d90429040f0000240e0311580b00e40900b00d0541d1130075282350125503901440e1140c142e020410740c00c02000103092a046800c44041d1080c564080c80503640380003e21001d5001c83c44000e410403003440c001500c4100030703040070b1070055043c181c440d4035980d13985401e420f41d00704010b1604882c040c210b0030080b00e0300000700c2c10410460f00d050441c3d10343c07505419048030a801414100444d4813149521007035955584082d1895140004000110341cac45090761001390001c00b81d5410780d1198695400000c1c4000603400707884 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456054001 1250 456052751 456052759
    0x906070c0804030609151508010b0d02330f191e230c0715020607020a290a05040510060b030613020405090c0334080405120a051c020306 60
    0x1140c91070b650304000b006020001c3d201045504075030070700411180134006207045800040311129051002060850310f03447d03c42807007039221000120060300d0b07000c400f42440da40d2444000314101d44070076283d0084c140bc0d081a000002c0020f00c00b5501c0b08000180400e9103940e410344206180c001801d070b52141c86c08810540d841d8940f81c4110c0210f10a00d0340c4120b26030150319049445008103801c2c0e0a5400c40e604003161900118000d00c00c0b52400d02c035529888105100909440c10002400f1703482e104454000780000ca0b08462414000385000c8000c0764586140210418070716042c00c6d240014a01542c04403000c0c040d0000c02a41c416142c0105c0042d650351034a9a486c6840783c2c000c0114514080c104441300a4007844002010787e21018031512170701c070300c1c60707019170300e01e05282520130811440e078110799900d4551540850310548241084080c81c0b0600385003c5d00c1c4c440d82002b07480c145003003140340485240094842e44455020000e006201c0142400d00701c0c203485820040d082c0c2c041100d5035500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456055251 1250 456054001 456054007
    0x81b0c0a030314181e01150f0e0a02131715090a0308061905040203130203010204030b15030607090605071a0709050108010b040e130f050303070c0b0a14070f02070b120906070c08 78
    0x24061709165003c6a10b2403903000103640d400040452000340f030a54011000801d14090821004191110f6141c4c4020780034000c500d828100d02c0555603404580c005c8403016006c40c80500a00541001041c2c0388408e442c0c0001c266107070a900381c545e0340c54242800c40c00a03041c0c00102c0c035181445968074003580c041c1c1101300f00613401c0c801800029040184800e80441d81c0c00d120101580f800c0c070091000c1c500800350b001c001e241c03032422018002008106140260700407405c2142055100c522503054a10914007155207504508150500440090000016601c80030034442443e80005040c01112404e0b03d032445213a03603890103800b40f4011882100c5000f030100d00044ca03482d504004003202c1e240b1030110354034968440c0d200d82d80346400807240880400e00d800d0304030081c4a581d1704890b50101200c4000d01c1000c40544603881c40c000301401756420b0100340781078001d00d54020b2103a503024022000280340c0340c81c21110300e0401114151040e41c1c0313601604002c51140c0f8031514442c605a034200c010f25207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456056501 1250 456055251 456055273
    0x11b05030313050a0606060f11030906070209041515150507021507080c0619060b1603030e0a0212030702120f060c1810090306050105010c03081b0c0a03031418 70
    0x8006140b0100450300360090030391020011302a4421b40000d811943d549000e40141c900014000e1005118a21010f6000740075110255481d2030494080c0365050b12900c8098560303103020f21607c5014002001c2860400684070b100c1524099140103d07800b41302c8660248500c244c0c00d840c54411680c0203900301c4909140c18800d50140002840b0080c4104d07089031410403141007080c10302400744c4160f92502c101075414490b6000b2405030704042d1a8002e00c46240140150724484641d410150040034192160200e42c8288410b0009441c4a500904503150006001c480261039038080001240302d46140d810000c0d081c00c000451440c1070b4200c400400403a04d41030a41801030300411f401500d02e548001e402006600c502c0c0031425041d0850b1201204541985040c000b82ea405812103410086480d0307026012035400707800350380c010701d081940c3d1244400c1c1101d400d14a115620720701c107480c0f184259103800c0590540c08500603a0307404003c640c0507200c01c00388048280030606201415031107417640715 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456057751 1250 456056501 456056521
    0xd11040509120c0f06010b030f270d05071b0501090905090109120806041a030304090b0d0812040b060307052d090c04081002040501090308030907050603040809011b050303 75
    0x40d42000440c02180d0042c65030803440c40c51503002d09a124541c1d040500d01c0b110f690820072805015201011002d8214901400d01d0040008002c0004048402d6200102d14102008441114280340b8200f51400c4400c9010080e020783d2001c41c080305c6604000c810300140a200014402c142e900580d9044800d5160900110140a0280504115550b900030500000d4800c0341100c008154a4444840d13502e0a401040116240702455428045110034842110f80d0040308480a079030b002130b0001a68100440400c21080c0e82400042c5480030014a40070300d980c500082501c203d01c00c2c51005065583c0c842810b84502c000c3c1329490b003199620903509090644507025000740187c061810500700c09840000714007003003d54010b0080d100020342031003004020701200c082024400380c203500d800c0c54200001c5c119462448050310500001c4003040c0e02400a2040500502c402070034591203080500f04a6056844111003034040340c070340c2c020039420031103480b103004c01c0540203005141165030700d2900d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456059001 1250 456057751 456057761
    0x1180608010c08060f0109030c050d0302070b0301080106050a09060605040608090313090c090e04020307030f05160b0a08090d0909051017010b0a1d01090c110321060d1104 75
    0x100251112404201140309101d440c882801079902c96905080500600815110803c035a50420811400900109003a00003a80c1182e80c1a40e602c21401d049060403400d02c2041e401c80302c01440004000200080e0540060050781c008648090049542d490401e084540c03910600021910521007000300c1802603441a5029260906407450010080c001c4104802300350004510360355264440c8407000e5118400b2006030006000c050a06d050640001c1d82e1291944001442c400700310310414108078050207e40341018811003c0c1e10b5a13500c8000c48080303a0099001c81c0009034114002900c943c1000690915210340c40c0c4807414075034180300301a009054001e1014034050002e03040090410b01c100c03036200d22030018a000140200b01707542000202003031135000340c4a524410300501142c0903681e0f4514111507061500040d40706001100381d84e09441d9200c80c0d51140404030307910b00e551060080c19401010101c50380f1000340d981e1020801c0c080311642018190390030244208200e42000d602c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456060251 1250 456059001 456059039
    0x10b0f0403061407030501170615030a0c030b04170a0c06110c0a0308061816030e120a08090c04020c0c190f270516030c20070f05040905030301 63
    0x105918007500c07070319081e040c3c0e100d900801c941e00740b2540070040b00341c0d858451940900101c44c40541640281d21200343c1d5580b0180841038041e00c072004111361a5402c00c50100703965480000100c100381c1c0c0c0e04040d22012803c031020740d036a8a004e1444110340c001c0c00121080c0709415118001408225282d04004100503000f01c5184d0a04000b00503100d030082141000c02c43c0b00eaa180500d82c901502444000030b010500c002c4490042003d004403204019031035a485d028603c1c0c0000da540e13111090034a40151102c015a004900040c1800300aa00c180c00c07602c120424001c0380c9407003a101c81840304910503161030121641280c0840c4120b45400c3d081c81406094601201091640b03502e00081d0b4007205502841c82800c1c230b07098007080c0a080c02c800445501c200101048607150084890410340c2c18a00000101070350744800b880300900580d0700c044001451210101c0300300314040d2280e61038031103000d06812441c4803074002039036142a01460f0003060b4050059070440e481e180203050340b0b000c4104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456061501 1250 456060251 456060277
    0x80403020a080f0706140103020a0519090f05060103141501111005012c01031709030a061109030c030c0303370302070c2103050309030d02030f0f070503010e010b 71
    0x4070350404108048007410401000e8081c5a07520383d0a45040400c8070809910301c5260042000100301503520384208808485050b034149003035080b000540c2d904e284142d000f000c041450060180c8051020f548041c1c4250300a8030100300a000d25142280a50000c68100c8180440b40780141050f52095080068003181d4004031400061340301c80840c1554802d8001c4241c80040c5000007031820f130130840802154039a04c414034080e50454940522072010400c2040480800040701c8682d40c904002148129800200420480c0a0207400703105030343c054200580701e44100e01c0c04208620b404a500507120000034000e520380106034103108007034403041020414156039644214400350b0800182d072244161380d60700680d190440c4c60000781000580c0c0142c0c02e0300d0000c01ca07002212108a24500d162605410301985076920320401074618411203c02c12032080c00802408407800300c2c421000d01806c0701c2c00c18890581d44084084515000034800d00240c0d0214400400482840400800341915210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456062751 1250 456061501 456061513
    0x105220c18020417371e32012c2104030c0b09030a200d050601050301050705071e0201020c090f1006020c01020c01051312080703030e030301031208040302 68
    0x200443e10160304886908115001003c04928405100d03481410804800c0e0058908a1103142c0040c0a0304001d40c00030911800200d01c654607455481140d000b06502c01910840e9040c181c281c100c11222041c2c0014801e00010190800d480042c000c070f0f104422500a270400d9010081c000c3c0d0b4680f90403c03c00200e9005038428a0443e00d040c003825501c0101e62000540c5d0b031413961802030708118860388811866001800300f07040a64010900060b140d4010710010400441200d03109040b61007041c0c05a40b16001108441c00c100020400318101c034000c030b0080240e50b46517102600e240c410341c18020071b0786900218510035514680790701c0c003800d030040c8110313081f2003540e00129072050001d44034806064201d0040092800400403d0000382202c0c2c8050156a0000d5001039075420301d1061283c148280801c15910040b01d0a41001c002e15100241c2d011100b42403d044400d940003a43c25070001e8208451604400b070000300311b90403294040f0b401c150b01051024105c6e070000c0d01a0084007103000d55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456064001 1250 456062751 456062759
    0x9230c100210231e0106030603150e0c12071a070807080a02010b0d030309050c030c0604140409051005091203040804180e070305063403090201020a050105090105220c180204 76
    0x1032443c6074440e229035030110f14204114107880901c0c210592208007018100700c41030000807218070408100d624034440c04510600903a00c42c1c4d003031142d0101aa500b0014600c050141c101c0c0014079070080301c00c1d0180100714144400350810b0b0a200e074800140118008100180000b0001401006042024800000d5940b00e9200190408880d04815000a611030307103170a0503c00c050126003420f26044000780b00740c0403004049802400f80f8490803180c08101c00310503489403200e410034a4010703071110075a0100c80700402040300a00040c3c0e004486442113003415040b64000604590140c0d41000ca402d0805141c18038100a0b540380c25003e004440c0c0760303150440c06243c100301103000f0b144604003500062500d0b02e08000794684004881600e90380a080400c20303091000000c0c100d0000500d800304065445000503441c000b4641c400400940c030341401c1040417a41036001f24040c4282610b5014044a200107600404800c40c13800b0f00b001c10000010000c0100702040f51b038003c29880405801c0c590740d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456065251 1250 456064001 456064061
    0xd0314042102100507120e030c09090a0c0e04030509060703031d0c01030e0d0c0609050705090910050610080f041b0609080c0109060c120309230c100210 67
    0x145040d81030601d10400030802140740c41d00381030451610a113405420a2546d84809401003140341c1204103008a0088807009510148500403098501074012041c0b4180000c2041e65000ca210303040e40c0a01100c540030804c802007558850049070995109403c1c41c100104100039079001c00e008070180741d030b24050858108194001a4010b0b80120040d0921401500015040d269a0080c00f41240c011903071540714a0f41000c0c1005100360003035000591280d407843d080745401c400c1e4011690112441041107486d4a00141c0c0c07842440310703500d080c81240c4500050041a40166101a0203d600d80c0002031401c202e14240039031207402052290002080da21041281d4419500014001521204103014486c400c11402e16427a8013031804500c4989484070041c401c0055031070042100480c10541c18100b44a074110a80d415003081041c1065840b824503101c40600c0a010720505005002c47c0303000600e04400303004079510f231540103000a4603812030441c00070080d0301d000c806660030041c5c44026020b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456066501 1250 456065251 456065279
    0x815010e060f3703060630020c01021603030c0503060109171f0209031b0306010b0d0b0406060c020f040507080703090204060b0c010504170f091201020d050c03160e0d031404 76
    0x86101c0d220250b05603c101c0c001c1c01d54245400c0344040c4045405076480b403ca0720003100041c19141c2d202e604541d1a507d094a004c0d2080e000461442e600110b01e401001084d1555100d4042c03298404210030b40300c0d031405840e00c0c00119003090109100480c02c00c00350b08002c50b40c0198010100503901800b01d10600c45002d500041c132001c3c1100e50208912200d070032b0420410002d00782195081140e089810300081d071320601401400500400480e0080101ca01c50b00100f41c1d8280c001c10900a03141ca03140000c01c0b4900d212002da110b1405030070101c1d011b081c80d1107524010a00d0380c4e22020166103141080c1e000d0900d650040707802c941d4400700040d103420000f0241803070900080c00030bc2e860030a03040000841c601403044a103078000400244615011940894143c1007094130255655982884489c0c0207020310f0f2000c00e0001e050a041042c3c40030084000d5215202084034805500941c4e00d040301c081d031030304102c01d8010915940311000302c0c0c05002d1003a1004034150285140030f072078100d641c02c3c1007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456067751 1250 456066501 456066577
    0x3170a0e2d0601030803012310051c050f040c050915150705070311041b0207120609050f01050a1a280305070909030f0c080a27060815010e060f 63
    0x5c0003c4010b1200c008106c0010745461800e0011703000f0005d14a0001d82c0ba000844030000900000180501a80d403062030030307220003820000108118038103a02c50614540045808403030728518078070003280500d400514180034490803090085010400800e1105007d82100c032501d5030390081c0901c10004008124800245202d62455610112a401480291000c4107020f0040b001d10184648a080d8001490000c68030780c0704104916054130309003500180f010300c40c040c209005802099480a605401080c0200d10300107007048805564030102c102c10004010f0030394820341204003200301460880d11200155821310040902ca603807650b0b258603190150b403183c106180c550910f242410f800aa84c580c11602c6420000c0e421401981ca440ba01d2058408802c10b001e100d03610300c0c222264240c4c943c0103134200b103020b9110f81900d030b03000034041c168100e03000c450110062084501c0c0b54440c0f043c0410350b41014040508000103601c21b00703000c3d08107044c5403001c0340b40400080e031a0b404068000f4001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456069001 1250 456067751 456067763
    0x207080414100c0303150504090501091a010f050108151009030314030f1306091202030d050a1404080a0e0a0b1207030b0a120c0f0303170a0e2d060103 66
    0x195150448141e407080010515922666441d005210450341100040300a2641351400040c0e20151800403811107229420003500545131103003603020000d05510184405000b683d80f035140d43d40c41c42c40380c40840000d000c2c0b0f00c8540c5d28030030100300d19401424101d07000303079103c4e041800342c4045002041b081004c03000042c0016440820401c1455000484203841402401c0d0051031031030b2124513591a0400600610464011807507003900b44803040c0e00c00848540c0c800058030b155402242d00030358980206003c40041ea1401000c20148006486990b502c0316018606c007203542d8454554000039040819030b0414404180d149014030f945070380a041c0a0b00e000360b03446480f45155900391700d094000600300000d16151030000703502c9690f5480e0a1003165608a01c106050b03c89181488001015070701104c10700c0c1803941d01200301504516080306c400e00c129130b01106940c881c80500180c070340b88480603803160400d83c2d07203420580c0b80350b407140007a140c1860481007a01c520404030340350100c00d078403d50321 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456070251 1250 456069001 456069007
    0x6030c170c0306090c0924210115021b010e01050c070806010314150411181518010b030112061e0f0b0a0b220807090f050a180f050c0301020708 63
    0x10b4580f1100140d0004030901915080002180100c0c080c0d5942c040304c1d07080641c81035038560144911707100700d4051a41d44007104984a02a05c0070702c40c23207070007030048503418200d084400901602c001104104100308203c900001001d100055881c40100305143c0c3c100302c0108074100102004100400051801d54010401503255003006071200c0d05c40d5280500c2034120a848a5000f90a01d4074950880c1c1c0107007000008000c142d00142004a41080406002e8072000403c201d81c40c044822034842202501c0f0b41181c05415a0b00b03516595090003420303d045810300042c4060340c4e80007503200000b440340000140582c00400e248408250607041020116114242c80d0581412030003160200c03902610b1f440100e50900d202c030500c2b4002d0340d01d8042d00d0501e0b0071100f06c0c6010000800001414403605490b40c0c181c544807860064507401c3d8107200b5403420300d80411302000c1d0502c28040c0c0030030044044080813459564100d0320b42c1c074115050714280308403080301280703070740a100404030ba5100b0880300365 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456071501 1250 456070251 456070261
    0xa270f03031107051b12070603060302030609010509030a0806010210050405161e06050d1808030708070e0d020d02120d0e030f0a0305030f041b0b0c0115080706030c170c03 75
    0x507034107000d4040450b07000500c801e10000b0400251002c6880880e101e6405c030b0046403020865114455007440314a214010001a045415600c071b00252802034080c2c2d506686e40600305030030380e41e0541e9140c10703503030041242e8154148030341001500184148192100520685144400d8540c00c0d28151000d03040320220b19601503d07956980004c0480000b04880c8850450001184180c21b2140790144400014103030840301440d442220461010381740070803000110f0400c036846410480c1d01001046521010a03400e5005240d800591030008001d100c04500e19803c0c800c4200c00b13000120f03003056241400300034450b800d022102c80c2e491107179034070b21003070142c00c0c1014500f559495509800350000c075032900c0442d51220890341d000180207016120b9803140d03d080c3d81c8c0b0584200004500c0403004c0d0001c40d110801c1c0008004c052003d0000340b00c19080e0046602641200340319000c480c1e40422002c100040c0a40c01440071030f01d190402131550004401c14196034001150441101c010000403c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456072751 1250 456071501 456071507
    0x81308040303082a1c06030f060c080a02030103021f0203130623090a140d0c1e140a150203160c0306060b0f0403060213050d0f1e0b0a270f03 62
    0x121011800b000b07001046100c1141318140e5100d80f41404000c072070030401000c000c4100b0381100e0025680018000580c5036141082d0300180341303520603940001c03092004070790128400c0c001e40341641d80041520001500084003030140f0312020440e00c0940c0810b000d816040c0c030501c130340c0d50010509516134001c400d504040001040c440041102d1111205100b000d10980301d588859050b148a0400001c0780742c03003030000032029844240003c1c9640d000c0b06020410740c18950100c1c1d0044649454502e000b030704d0b0701c1e80400c00b5905001260700316401480030064411703000141c415030a014010380c2e02c0c0c0805c954101010b8400c036007050b2001c628443d420400c000d424403950b0b000f06072042e82035007404041a280d4865100b688805007480350045074041e00d05a1078641100100001018142c000c1400d15103100d40e81e801840640d590701440345026038411b01e0045072030410354000c1d060140d654038034590314001c08450728490814008128a000a0050401c810b0021400303568000c500301c0d40ea103070003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456074001 1250 456072751 456072781
    0x10b030f0102040305071703040f06020d080609010810050c090a120c0e0702062802041215020a0c03031d060f0103060c030614090402010c0618030e15070308130804030308 75
    0x400207070b10410040010030f0300072410100743d4400c07000031242800f00018451840c0034039044000c211100c0103001400d5600014022002c001588489c9100c2c1d8030007041200303011091140c418135800400d82d41110300c603030364440760f80140d19038407160800c00c9140119440031550380200d10074104d00b40c886000d129160f20450020a54000c03c02c401d450800030081d183c3e0b10207407900842d4004800c511201940066414550180315402107490b541d58401501003a28128000c1d1029086200e1115a03c1c0391030080ba04c201c07a0585407403402d0000c2e640c3c114000c0050304c6201240103141d010302900d03050144a00c60040130700c0700c02943c540d410b504100040395148036801e0705052400714108100c114000341403400c03040c00c60388001265a1400140c40201590b14002d141524000355501c949112202420744071340030f5030b41e2041d011500800c1c17040307403a20480030000921061004000280c0301354840c80d403004a00000c001c582c03c5c035584603201500513800c11008160f1040803c09800100241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456075251 1250 456074001 456074023
    0x509030a080906040f0b2d06010e1806060d0f09140d030b010c03080702010b040507031a0a050a0e060310020c0327100813150207060501270f0e0d02010b03 68
    0x20b842c0c41d0070182d0381c04130005c5c1405c0d40103020711012400203a10107007520700302c80205160740f840c8a02c890041901e0f2000c4404590031070108410030448a0310342000c002c0380e03482d4000d0003803051490f01c0364070401185420092500341440e417124803c200340178080c042c010019124903510000585040c110300d00702410150054101842c00201d0b6840c5c1c1e0380082c51000c0350340c05080000c02d940b1112000c0780500482001250428180000d03c4205503150f84003508194081d500d85100c04400c05c100140400548a059030003091203034240301501801e8002e581040740181120107070456003041409a800c02c031a80045a003010654150900c1455250040f84555001701080c110191000441581741c5984a80400400000207401001903111010030b4a13000204040740b0f00b07040030403001a42c0614800c640301401d280c00025020a001d9010121071241076450000064a42002d0010140d40c6141c2d41000c1c0c03982c00500650f082803010040074580e039400401c400906005051a209881107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456076501 1250 456075251 456075253
    0x3120c0c030304150612050601091a0102060c090d120815042702040b060d0e0d020c01020709020304020d060f0b1e060a180503010c0207080601080d080103080a09090509030a0809 78
    0xc94400c802001104407076020b50300420407000040c8424400000301500e4008000444006001c80140038002070301034122251084144425038584400110b40d0b26500046809a803000000c80d180d5140300c4007503e107101d07001d89001030800c11511820039540e003c0740c1030804501c5074800c3c40a1444c96041415454109641c07d2040b1500700c07800220811204901e0002c55400e070840714215507490b04120700a40c0002c200303d44404220002000030300c650004402e140c4601d90884a4490011030100c00d04103058000c2d0200070301e0302014201035840100304980c4080e4640c0141d0002703000b4490703c3d5a405091900080d6407401ca410310485a07881c103054010103410f0110b0300720300d0382d5030011504807240340d1808031298514140718511019040c0c201c06ea00d542400030301110f05034005207200c101c2d50304608035013507030b41e13120201038440910b004082e0000d2000340040c004100250300030a4861094034000180c40d5a800307080044403000d94012005401c0010704000040c1d0056089420400501c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456077751 1250 456076501 456076507
    0x3070807090e04030c02131401060e04060509071e0302040b1803010c020109021f1209060902190501080c0a1107150f090b09040b030f0105041b060320031506070503120c 74
    0x7132400781020f150001d001344540c420461810052480d5084400440304020107140301d540c41307000142880198a99007401a0b01d80b4100084602d0003121490160109454a0381840c0e14116600c030b18003901c604410505400300300c0041c066840c000244006200c072100b1940010004c070415007510f0307880a040e01168140070783e00c0050381c3c4000d5542d52a5050850a115008541714195200f280704501210b2070340c600a400c1d000e00c480d58000c0807403036200f1a40c003074000d00d181407404040c007c0d80c0252030015080c040040c54000800c00240140d030800c3c02c1c000000a0a0b078107851601165410902214401e5444621441d07081010249001c034507043c82c00115040400f002074038000e09882510075511500350039201c0d1418000c400703007860068024000c600c4c0c142481c2a03140e0300b8000791b244441c590b07003001911178424402c504084615200c040b07410005014040b00b00d400250201840014141d075410140d5941c0004000051040002e5a201d09500e0900201036000800250b40c0320010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456079001 1250 456077751 456077753
    0x120209090d020606010e03150112020f06030c07031d0603070306081b01020c2403040804050a061b030309110a03060501050411070c030605040c0e0103030509040c0905030c0f1503070807090e04 84
    0x105501380d000c00c003032070007101c5203040c0c0000070328000703500074907010460a110020516120701508400b5040c001d441c030485855032003051005a10003117809400039003041c0590f40010b441501ca00341100a600c004201e00d05420300003030301c40d45c81500d900c0c011030fa4604040004990521031824800f036107290f45440d000300c05001030341710b54003054000c0c0324506030000f41c84440d07082800d160700a072036451180c0d140c0c985441c180d900da1340309005081c031980d07481034001495071040185070012451030b000c0102c070882076601600a40010282224081407981000311540c940c910488001e50280c00041000e500d088140011203060034003c4140705001c0105801280c1344403100411a603201c540000c484e611400c1c10b115a44a9030040b0020490030030000050561150150503164000c85042105451004d01074440c150640320300c64054020b02c0d6003100c076107400d5080e09410310001d40410f03c4c20151043c005160f6000301c07405000310b160720080c00300d025807192072400034080707543c9076461a00b45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456080251 1250 456079001 456079003
    0x109060b090909010f06180f18060203040c0b130303080c092125081e100207080f040303030c110f060a0207020609040507020d12020906070f05030c07120209090d02 72
    0x140500303041c0a00b41031070210701c101009521204143c1c1c080e00040142603100c005449000e09019200d080c0300f07062508500303c0c0c01d29889000203d1010151011184105940d80000f9410041042d1090565040d0003c2c00038800001030810302e10340305000c0c03d4541140350160007540c000e042403000200610405a10352a0300000710141d890000d000300c08900da4445681c41c0c268003465400170048042e1000c1d0640031100d00803400c1c0c410b29000e4038031038514903021946016124080f41d246500c25040c148601c5100d034000d1404502600e1031a02d007022002e04140c4550142c2d00c11400280d482100b03001c8250f00c81e0020500544c42005824003941d80c1c0d17043d5941fa20050801544d00e5400103400d411941c1c1c0200711420184003030b10500103840c02e0341e00130703440340506403403200411000d401444403261607101b01c40c454100100401d0422569490f00518000356500803221440304100d140d51031403042240000400036075185284e505140d10600c07101c0b65000d030103180c007507100d90540341c070141d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456081501 1250 456080251 456080257
    0x9061806080d0c021504031505090102090102101a120d0f021c140403060c0915020c030604110d0b01090911090105100c32070b07080409050c070b0f0f0109060b 70
    0x1814600b044000f800c500000f002442038401000607104001000400c00940790901c0c10021402ca01c1003003941d0743d4440c910701340d00c25101d01c240180c0003c002440000241d07882841c01c81142048589202908404902c200300c503100c0c042196400000d540c000103034031400d6002d004400344047c21081380800d03402003412400c1030513a41031191441c609400c480d500c10984008540200381808800040380c1c000e014441c940c02000e40c0e0b4005500800843d60002881101405016008103440c0d42c69859010300310300d8442072141c1c0b020003030966001103812500d40354040c103640d20000a00c0549440e0600b03003000c0c0c0074405030060500e800100083d95030300310103001c40011420190b8011213a0f15016404011040c60248020705c051120b981c044085420080001614000c0790005900c0b8003a4000341e0056501c0100a240200020700403051103401090300503615207030380c0b41420b426030740e040f030b2404003101e008410001910030031062550402003170b401404c80e800c0c208801800c05903071200c544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456082751 1250 456081501 456081523
    0x7140d06110706020a0c0b0708191e0617160b09010e0301090c09140a060f06050c122b0504021003091406090c030616020d0c020409020a0906180608 65
    0xa9038900e481000300c1d00c4541118003155010008540e10750b0074460140c010084c0e00010303214921b4010000d115640503a8000380120300e0b1046c00b601c808858400030010304083d5041f0340032803100c003260054080c1640111000b82c4220311a0300c01c9400707030f40c684500c0c1001030702c0c500030400003242c42005507280100840705100750a103404500740660001090141010303020040ca102d0351075100041c0c40c0410342c0400040305c032810001d10b0a0f12030034104400d80308039005643c03040e02402d404102c85800354009143d1071150005455074144070003d8035401d5004010345820107061103903031512604005110000014078401e04209908103070300440c008140041280003450fa81ea01c043c42401540e01c62504082000b03802c807071151900e058101c1e00c0300d042d450740500911912001c03403400c5610b8034000c2a0403880b50300801c6407000b116411101e05060400698011360340717240030f80150b11a0140200600400200810100d14000421042450000f00040d042e854141d05121041c00415019030301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456084001 1250 456082751 456082763
    0x80f04120804081e040810020903070e0702071806050f10081501050f031302040b0108070e0d030c080318070603020405010c110312070f1b0501080a2403050c0307140d 73
    0x1540d0340d1805043c188a08046030a004240b141c2852006180d040144152410b050a5801c0848600d000f00c086e40218801c0903456040b180090046018501099901001a01c12550300341e0b9100312707a004000c1206886041ca6440362000c0c4100d00709002041c0340001c040c3c400003a810030310031000f041181c010f0b15044130341c0848148110b8581c418010b0b03075200704418807e144c1c1e0f8100544182488078102c14224010790501c28003404940c0a03540300c0c0d214036440c2e112400b100603c10100004901d01030011814060040030400204003640d01070b51254405c2d05a8112240402c00010710f0418103038000020140100702c1800142d9014205640c41c0381c2c060768500c659212440003e0601c104040140da4042c00400c080d028450842d00101d2846d001c2c9070f98800c403680088100d0704414035402401c5c0491401c4000c26400318041d4000c075a5032106810540c0300300da000d12800c00d1170030b042d841541d0075031051021921a180c14041d075001044485042d003076000418000c2001d01c840407001400c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456085251 1250 456084001 456084017
    0x302061b01061d1905060a0b0a0314090a0b101a071110090303030b100905010c052b02011406150a02240103211e090b0f0a080f0412 58
    0x440c4402d400440c00350101c00e040040b5141a009208003106007103507040c8289070001c42c00004040c040c8503c43c020400500041036460074400407800591043c11400c003090350b1684c000300b079903a0100c01d290084904001900000410f0700700705100305400b40c0b074000c040e10042d508000c1c06d00c007400703042d401c8560900903507100c903e981062103028042d94126500403151b280700b0049154444103080549119480810000400c0020322007030b141d000680c0c1c40450042c00052040d0740c010304c40c541c1d0480c8a00100c5500e4401c49000720030080c44004080005000710f600d50126039028011810408103013a814502c903e0080c0010f009006408201c0c1350104000910100040c801d000148030918000c07240d8120008002c11540782da00c00740b000b5a00c8110746031305a100912f0f00c00340714103a07243c1a60f55900011080f03054902c030690211501d014041c4001c07002500040402c0906901d0701e4040d59140c440401a00251140d08014240210140705200300310009084460b0003081100710703d00f0a503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456086501 1250 456085251 456085297
    0xa1508360307050a0501140112080301030b04081314270106081008120901110a11060903030d110706060f0e04060f02220315060b16030207030b040803010e10030206 72
    0x100714420000060040d0140ca0010030074484150860171900800d0468880e042ea41c0f03283c0c1d00c0b00c5240300c1e40d001388a0035007000101702060803000c0040d0802c2c01550160310b00b1120036000a4000d03000e61004103c1550502008541d1501d606c0312003000d032040c035244901c00718444000e405141c05010780c0d400d201074040410007251400d1a038102500031503086400101c2c1180f103000c4d9680003200040c0c00902009a81d0940700800b05200f408a0b43c05182441c44040920420245411500c482501031200303000300d0001142a0041c46400152205a59030b102503900700a000d950898000070f402030060002005114807842c4810b900c00d0b0015800a8482800f000040282c0700d0340415060141c520034500d040b1203000c0da00da00441e407140d0030140c4441c4900d00c100040d20001d100b000c10260040c84484c2a2100b00d801945446110780f0580b60006c0d22035884004800081e5400d80b04200080010b2100f68107034061580c01100407807290001c6031075580029a1fa2161307019081d05a011204001c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456087751 1250 456086501 456086503
    0x5030a120c1401060e18100f020f0f1b060c03150402130312020d09180905010e0618070506090618040b0a06030905010f020301050109230a150836 64
    0x1055540007198400b204900001d040c044d20060107810340011118010a102c9040d41d0341464450080c1d001420152070040250740080500441c150100d50702000211034a41c2c0c0700008011300c40035110070780c1d140c044000d60842c500750790040c00d1116034462018011014044019030345e0042032610a51180b0050f60040b170064000d8070810381c0400304208002c010014009561038001d00150301701d4948030000442140e08030154406c94841040d1010b8004084e5650341048500c0e600034800850100419030b0600d01d040012102651502c1d810303001108900006e00403071008240460781d66080044103000a240361061844a001c042d00804000d003183c0c903a80c201600503180180300c1440103980302d00243c09000200303c00c94145d407801d16005881d801c9032007038a041e0740d07060b51081115420805084c0d4040312480110b00c00780c4000041071199542c24180344040c00c3e81c05140d0500c1c8540740c00c007034a50000505074180d006442e100200c00141c10ba8050186041c100201c2541c04403141c10a07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456089001 1250 456087751 456087767
    0x90b1b0903011805010c1706010c03031b0801061e020303060108060d120206060301200301030b1b16110409030e091008030c0606010e030d080c030c250606060905030a12 74
    0x9a019400d00c40401a600c01e100c0c1c8110341c00d400784e8000d100100c2d03103604c1107074540c010400c5075140442000203d01207501c2640c0d4468414440e0800191190100030282006400700c00c14400003044000148000f07607004221b0010980110001050040041c4c0c020703403039000003000a410000c0801c002800b560701c1c42010300150f0303007006000e10307450350302c40d40291071300c1c02141c1c00c500a60800c01c2c42e0b20300305903e501c150902008c4500b01402d5909580d03e0000b049009000203503c043c04440e82d0329554006001041d41d510505d000180344030407071414402c080855801c5c284601e160140c0718003c640c00050341076a5560442e030a0019036503000d03071141030550704d408c00807091101007030107061700a0000300d49014210076264900038401460030103a8844030701c0c9000c4001941d00700403581e8220020007031a0410a07298401b8201160210000302100071640880130428007010034a09011302c030710402d005010031b1320b09041498241004665140c80d0004000c14040d50107101040d164890032034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456090251 1250 456089001 456089017
    0x609090c1209050610050a030203122206110709020313260d02030103020a0503120f0a020a120804060c030507020a141207050f061f030b070936090b1b 66
    0x81080c18001e05040c0d544d08411039083d0b29001414030040782c0c91500c0702a100807203a000780100410040b880c1c0f4103025810400c1c9401092030520342c81c1030001e05142c00107000d412599505001000007140702d91600c45540c4c000c0001c144104180b10f80040301800100d040e0380c1000343c0c2c0b03051100c844c0000d905021012a140364250f008260b40d240f0400c0d90300218102d07802140c0780d0220644440415464440f0300801400001c000c1120b008407107407410141c80e2000300ca0040e1002d0742c80c2c0f80c560322000e03802911031000203648138040008100d220700c01e06150100c02e2800304254139169401940e540c400c00c5002c0e01c1c00c241e1220700c007070851040180f00d150741c0c0300b03461640c0c0f00c40480c941190307960035580814541c1d008440000303000801c8801c0c032791091002041c40c1300b8018910345481c0c0171940042c1c0071500f040172224001c9008481c0d60b20700c102c04250090039240c6000150140c10300e180600ba1440040f03801d00d440780e80880c13408110070b5000785058042e14103086070805002c18a22440031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456091501 1250 456090251 456090287
    0x1a010816111f1a011b060615030507030e0105010806060d08090d0c0509010b070804050904060b030a03020c041a060d050702031303030903030e0105070b04061a06030a0b1503010609090c 81
    0x112405034a10320045100c100445400b0302c040c0c50103071a0f8405904580c0c400a0014030140c0c120100301c0031504201c8000c500a00c000642203840b0651061055114000c03280401d03140d0060181141c0d0521642000d40030050007004035504104640703403079105c00341c4440d118845070140c1c030080c0548031080b51500e0500500c8060340d2401032401e40b0803104a44201880755050030000610848182e0880c1c4180ba40551405d180c281000108069103402074000e890340fa0752960410700320344040081d170000c1f50281c0c0041c00900d500700200829542100345d18201000c0d12010300d07080c0c0c1c17520b100340d48680814620226035543c3d0410200d1942c0540000481074074410030001007855084803d00c411340e40640d645c1d4190a00c1200152500d1003060700003840b4211910024000c40e035a03500c11440340d140010784402d8400380d44005002904180d40c004881c0d641d6141d665601d0ae40040a40361214100150a0441d0324214002d010706c0070a103c0c4940040c0c640c030b00700e2801c5125914914850381c02403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456092751 1250 456091501 456091513
    0x609010203160f0c081209041503060203151c0201050327030703110d1b0b070e0d061d062208090a06050a2010150f0b0d1a01081611 58
    0x105001e00b00d608140f00a07211141a20b2000c6071441020070708050300009050304529000f80c083c1440020700410034500c0c0d90811202c00170000035504c1c00103500540340070241c100303d80090303820090a1030050b080b8139010028040500c00503608402541e42c806400c0d04c48048000e4141c080350801c8680408808040c000002c0407003c054002400c5036031080700300120748400846680c2a214a400000700340c3d24412000b2103000000d680b107070844c2d401811842c01641a40076600410f030603012000d41159595107031741902c0b0814014200c104280c2c0c0390074004203458100520520840ca101c6256040c00460f64513150f02400700a00449142050142c06004010358900c0c000381142c116480c00000030324110240c00c14554088000b01d002801c6a01130400c40ca050740301e0b00010840800100c041c2e0701542000110850a012203400402e4108a190b58511154400b481240c0c0102001ea00c4254210351402850b41d110300c800e40c2c00700b00c03200000c1003a0900701054601603060040d142a5100304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456094001 1250 456092751 456092753
    0x20d09020a060507060c022e0b040c0c1a010e0408070812070e010314010e0c0904200909010e13113c010201060315180b040c0611150402060901020316 66
    0x90002c4c80880c0c000c4a08200380344045004984825440c1350b65800e07000b81c29810002400c0000c000029030707807107100000310111050041010340700003012440c081035154414509002075000341c05602d000780e41c09000198140301410b049003801900c00782192a000c90b181d8200400300080b40c42e101100020700c4102d141046004120f0044421010f0001c0c5c00c1c0140504c0001d4401d480c42e0507141d00010f0f24449035035810482203d40c00a034011740e800360700d070380030360b080c005c0340c48070200d41a4100d100540d80e4030141fa05100907114181c0c011001e2010600401800710094151074040d07a51114610310810b0042000a1400da1600384003150048000c10500031502400207080e03041d02080304020b420a0140016822a040c80c88050000c00c1d0180c0e50500d0000740d680600d01c95096240200100079264a40804c5078004807030844101071190011f01c0542e03040300c1820848040c13880240f4070821140055185001c001d00028010900850303501c0d6642e00a04c2512108091450558229009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456095251 1250 456094001 456094007
    0xb07080405130902010c0821010815060109081c03062103020607050702090112031b05010c08010506180103150503011514030102040e040f02010302190e040f0b0f04020d09020a06 78
    0xc40c1c41510710030004002c000d40044110f02480e103082c1c0c0c05031103030010315003e0703202c145ca2640243c14852054080807030900b690302c109084203002c6e0100d140106040b04000b8062040e642002d44018144098100200310085002034114100c0039602d05451040c610707488103401820098009090300e01080d0198220000341400c107642240c00390b82222004d0b1510442641c2610400748041c0d0070104c1000107122080201c4182d6004c1c612902e001b1411030302a410182091411440071034981e511220120100c65010038500c0c00b4200407070f8010b241c0320050845516616540610505258640d152082c20709001c81d8030307500400d00a40203104002c1c00843e041007100395800f4000e0070450350a004069401c0510a880940d4068081c1d0a000d440340d440d000150801d001040b4101034003004a106802c482503041030725000c0f06d40318a0190702c0e089040005aa0300742500400162070004030341c1c4140c1d079500c104242e60341c0aa9005036600102001c80c2c001d444034400194200d4490100090120781c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456096501 1250 456095251 456095257
    0x7030f110f071106040f29161b1206050603010905030a050c01050a05041212020d06030b0f160206180a1406040b0901060f0302041112040b0702210d02130b0708 70
    0xc41403840d010f0742c0c500310701040304500450007450711000ca0440244031f03840d204049440b00c1480900c440302650080036076000303590b00500f11102640b481e029100100401004040803040c00c0e00401360400e810000700c202d00c3d4041e0100034259545800100b00181c5081d48007d100982010640350383c4c0a20f101e01400c01d50000209101961800c0c0006440c00394622a442c084e40d4002c4c06040d1402c208081101c0400284000700c3c9426400c11000710303c441d0038486d0400039482903001e450f882c80c1142d40c03801e00080051220710f0403841e84121084203a400b140c00c80d8000050f19030070140d20140d08816181c1509201e00401d0280a02000350090900040452140e8424805524583d84d40c410081c01c0e90064807540540701043e01040c401480c003900130340b05480d00d044103942003504c00040d10750030b04d0069405803566001035090200c0140e0600119a8406d0b41d4445800c0c2c0c00702650545200e44901407501c2d00181c0c0c0481c8032100a900c5c0c244000062804030007441e100c100504144600741c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456097751 1250 456096501 456096503
    0x9120d0f020706020105090307020105030603030d090c0e0a0510050111030903030c06010503010c020a05100b0f0607030f081509150a08160f060c031b050715080412080f07030f110f07 80
    0x4402c1c90030010340d03503205005451046601c00059414070381d09500545081e00081c245550600003840185070b40005d51040d5841140a54440070125151901d112001c3c0e0010b01007090803030400c4100014040b030811000201c60087ca0520185d14225100c81c0c00c500904e4003259045c04001540f0342000d60015059050303903401c034001c000c015542c00307060340d55091000000b0000e82000b0860019a209648028003115024010030744940340b4000041d03541c1d204100c22404200200400c1842c641d1040703500364040b040c0300081101100c1500010300d4540010290f12026009040181c69074a800c007154009000704401c45401ca03a858010000350324050042c07001e201c8604000141c0a40318001c0c0d010714a400d0703194040091030409141e1007011002c44240c44610800000003069010800007090152869072035110074201840c04010a2074083c5886040141000c20b000c2d903542c107045119045850350400160030b00700e021000c00078003002c20b5039944529020841c1d29101d045940101161 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456099001 1250 456097751 456097753
    0xf0606040b01052110051804050c2205090a06090c140405160c020a03020a06051b01090b13030219030801060f0305011a0c0f030706020702100207180209120d0f02 71
    0x328407050045915010b40c820881c440c0c11612146485282d0020145821810700720542d14403540342e5001c600c0c20b02c05000300d841061340407402c11041c00414481c1599240085881070f42c2034007812901c40d0484000c9683c2c3c803001c0d0307995021516a03002001804800341d440340042c0304020090501003443c00d064847e14100030246005586103207030902c9010320500d59411a54004440041300b00c49810213560102d0f080f13200302c0c0020015a998042c40402401c1594a82d5511010034a0b03080a40c030b90104520007503030621141c0c40020703021200040e4820510040e0758804050740c2401c03850b02c0c901d14100699080650b05050a160340101d0325030507140c550301c0c1c038008420801000c40440d40300b442100351200190000d03468003000c40004100100c04541102d003000c0c041c6241d80d0565014000840f4829400202c032030450414103441c13500b682840c006051264a4901000038004d10140c030080f41560020700f8003080d60310082c414038141c8a0004481062030541405895001391051fa0405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456100251 1250 456099001 456099011
    0x14041e140f130209040f021c05010c0e0d02030a0b0705121302100c0506010303050307180e040203011107050703030c060608030a1101060812070b10050603042109030206070f03110f060604 82
    0x50400511042002c255014080003815515070300d0303a61a03003240e0313281240d01c080c401c01040c080d07046171049058024050000003031312a900b0000036047d001419007490081000c1c03031304580940e0300880c80c582140c1d0055450355450f81c170444101e84610030b151610b1303182c09615060107800da03100240001801c0c0309460500742e01c2b1607210266410b04820070020503591000300140f00080c0f00710302540e044203490038840c0942e518610741901340202c980002d400040940c04100a52a0900960280c40806e08a040c07421001e42c9401340c031511035001c00f8082c0b00111440104205055125100400100054a880380c440e40c500505017940341d050064150300300304002c15070850210f40303101030500c10140303030303192050742d942c0c1d4552014010844040c4800c00c0c080000d99444940003144100d225407280d0400b065203480702540301003040500320403c94a14410300042e02e40904655080e0780044080501d1641c03450200c8105540b0384460110380605200d00705810300005442e401103c003220b013801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 456101501 1250 456100251 456100261
    0x90607030e03150c1605120403051612260f030118050906070e090a06050a0b040303090602030a09030807060e12370f030621110a14041e140f 62
    0x242002c040c1c0e200d0948513410031007210703183d12180d0303001040e5100714140c4090f5002c142084800380c2280e03205542c00d801000030308001c81c036410807003c0603003a051044070540401d5120402401c2e0a110400e100078900003c070b03102008007409030b5000d031240342c00590392136031250758a0380390b60346251301d4880903410000800c030845008101030303214400b141e0314041c00c0e4100307108020001002a00d01d00740c4039078030f440104040d02da00500c4009086821503240d503461540c54010078080e51548200e045400c240070000c591684001c6500840750017094054a603c0307039080c280c00808086003a09054800c00c4c40c5118248041c02c00f40540d4590780c00c0041640e4010f949001c00d0140c00080520032590040106854034040c01708540d040e5400e240c002181529505050b0701450901015940380d03000c035600e54100000100b002091410170f451206d01c003450310b0700e040c41e040a000805441203440d05417401c0001c0d00c24601c1d00c0c0d100c0d0b07002c800307101d0000c81740c003040000d00003915051174154070140054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 456102751 1250 456101501 456101533
    0x150408190c0206091509060f03090d0801030201140c1005070905011701030209060d0f0506010902070c0503150c0c0111030a06080c0a0e06040c0c0203030a0e011818050c090607030e03 80
    0x24a807907030003420182c600414003081082d1003044416113034504906001c030445035107075000904841001d556140d0b41c0c0e8180303801040e140003506100d01d02046840801880183da000b00010050030179250302548510380d4520b983c0c14510180d2003111860315000810031002ea100c003940040302c40c20303220aa088080c802841e1810902400065040f84001d40402c500b81400011681000d004500309444101c25a9880b4240301003070b0703c0042d034142c010a9034002e0014000b1040d0050008400070155802e21a20054008800a0074844041d03000b1449525004003074025540140441c4c00c500d40d20310303000b09030900401e214058920a44284402d0110301d08100c21402c09540f00039501d1003c1c1d58a210402c0040c04003480d5400030000c1385000c200040c0c070200301a0041251513290841c00c3c52028000400171800c0480000b4a5011000200600100603545c0e6610313a50410004c01d190343c80780302d05401c900c110307001203400440c001041820715900001c5485011811029111840442c40801d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 456104001 1250 456102751 456102767
    0x6183d090f031707020a080706080103110f030a0f0516080a06050c0c0714030106150503060916050906070c080a0302060a151503050a090206130611030a08160215040819 74
    0x1003c0c980030069200b56000000050003056200500b0700240540310040d0b03030305150042e80004085004403005004020382040004c06402c1d0554035400e201c1000b0000030703521900c85c000070780300c0194003411006006092003100482c1e20311444401c3c00b2540c480f5030b655500c41c0c4100961300316191201003804103490600312070002540074010300d1b05d80d061060b0303031100c000c595040960540d60303080c0001d00c582030501c03207030325075852a1555600d91a00070184003031380c0300c0101032017140040d1000a446494000c402d940385150196046900c4150903d000c83d401f03e0700c1d8000c0c0500e032080000c854201740d400902070740704000742030702881b004d174940110405c05d007980c1c09844a04e03201101e0980c0c01504c039500483d40481200800b280c1526107401042c0103074088100f000e95419086018002c1e150411040219050320341c004518061010a00421001d0b0103000860441c04641c42e40e02c0b030358401c11035456050035055803230702e640c00c240c500a501a4494618003810301004000405d40c140a01c1c5a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 456105251 1250 456104001 456104003
    0x110301150315020705010f0b01030e0c010f050c01180b1602150a09110a0b040609140a2c07080a05060f0108042d0b0601090506183d090f03 61
    0x200c040c80303030a69680124240041c01c4900d00150300380810408100709000e5810342c102900030020b02601c89030700040039521359001c010a2548012900c1a05980c04514401a94a1482c0254079011038000150141426540340c2e9000c4110244401c140059110355901030741c06180d03e2641101c184c0416a12101e040c2e40d02440100104006070301d8010580188603c1c5200d404406d40c56000400014000d00b07039500201145540882e007804019045007032000680740d0060310f6a0b82c2c012100008082d0f242034082d56001c1d0416070420410030600d09010b01000320807550010b00c0d41381c25800105003050071100360406504110108166041510400041010603520b021403656940c903030480c080607141a1449448810a000003141c01461450b69060f00c90340c0300d4540d6041c80d1000400c0d006080d08405d1081904001c050385030305088410702d1981c642614080700240c0e2690b203802d0110106d070769030303030316a0100f0402580f5022140c0100811600613181c51582c503445807181100d00c040741c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 456106501 1250 456105251 456105281
    0x40e100b07030c110306161409031009060b060a0c02040b100203190905030d0206040507080105390301080114180a0311070314100b01020321060a0503030a050403110301 74
    0x40744000c41c0c442c140c0301c12164065030500b02c0310b5070341002103484e0007421900c203015640103841d4008201e0340080031006400c5070005403820300c45010000780d01d801c1c95840d51014142d55201d10000c00c2410340000c030885000a05407515400300b490040c1040101d40c4040703104600c1c01c0107150b0f881c40c0240240c3c00507440e80c1d00075820109040e1000390410305080101c024400310304000969035038204a0000e031211960301900d810708091506c40d280c4591070300301c20740c0d81c2d0510040000b8080c0e9003550a00b00d000c10300e16205010310500020411b40c4014012903031f2040000000f01c0c4140d015000241070555680d905c2c0300f10b594052040d400c950664041d41c8054200c04401d0380807a01c103440c03102c01208003100351881d5540e03e95072986940042002400c440c2c20106e2a0b9219018911400c0f00780f110a0014500d0210f28403c40d2204061480c26000081030700030100d1030503201d031559100542009030403695144511880948a40c209202c111500741d1149130031354a504040c0030317807400c06860b91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 456107751 1250 456106501 456106507
    0xe120301060e030705130209010909050708130318170f0d1b02040b040c09050102060c0406142508040f06090b1b0a06050f04210f1206030b04050102040e100b 69
    0x201c080380c4001c80800c52580c14490350601080700e585090702140a019040d0006070390b09180030015111042503800b0343c085c80c3c40e00c0d040180c0984c01110081e8050040c0c940030490310118981510749617000394180c507020800000210341002450120b00c40301d10141d00322148039405600e107a40d2011020001000100070a601001121808491070f201034801000404e10011000200301100d010341e0007000010503256080003070f541c0501c41c02d504203406992903850981012005800e0f940c254903c5000a40d00040e5000c04040c10b4002c4081c0d859881004501c1c20b0301810456810380050281e030003039400304d003000680c0a008030110001c0710300c09440c2d6401c1455065203e4900789004d08028018052601c00d81c0002d0114411280f1a40e08010801030504060030031240742c41c0c019001c0450000f0019000745083e0700003040301d00118070f80c42d03d03844003803c503040c3d400070b0107031540010400100c03d404e100400c10b040d000350013030794180e4061401680d030342411108041054030034428000810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 456109001 1250 456107751 456107759
    0x6031a03100c030f050406020714031e0904060509090a11120a080d1d06010612020c0604060b061e0309120a21020910020c0306071d0603180111030108010e120301 71
    0x20b5081801404258240040d0508001080c60260340003101d040382d4050340043d004041008030100601d42a908200450034180b884814100c1c171000c0150500c041100401c855040f81d6440c2c1003070020b0500948010280d04007101c0352940c40d64690821038041c40c0003c000282c9040c02410700d503051030050002e00c401c207941d454042450748420150348042ea2200c1110340c9101014888030000004900101a19854624014460300141406006640c010040020745003000114180c020740c005600182b00b070f214400141e40e511884142002003100c0540b1600c0ca01801c001441c401c5404006540611820b05a80c100c02c2c420003501d400030800103070100c10381409140c0d929680440360000140350100c020001203500002102d0000141d12140c3c80311030506060180d04e4004d24981030200080822110004082c0c155000b245d004000100014071078140e81071001051a4a08000b0000c1c194040d041e640302e0351090058507019070030b00510b100e045400140c0030030081200c40300141140d0074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 456110251 1250 456109001 456109033
    0x30403031412041a0a0b0a181e0209043e04030c0b0c19150c03020f0301030f030801060903080913021b010b13090f0201030209060d140106031a03 64
    0x84912000150441440075482e0300d6400c030900c50240d4060b00c40c1601504a0071000400504014441101281422000009510744e1000c2c801594010711810180070300460941c00240640190b0000307121080148565610035940201840841603500340600101d030038056500504110b600ca41d0000707442030010b480403020705809005101c0c40441841c0c503035a5281c102a0702040c1d000341d41e04c5500020340e641400f02c200003003003003640c500070185078180c226103622000840d03440b00b00a8081d00d5040c000016407103541111010009410402c5d20384d61207017400340a001d0340308801c4010845981c00450740c0c5026500541c210395205401c40c0c42e040c000000e000d8402c040d9006180b03815024003c1143c404950a440c0b0414418a800025501c0c862410070404c0700c5012064104d651426400c0070200c0d840040c0102c1c1c1d50b40a0802690f1403005138085100d512401100041e181d16002c0350400700045034000714121003140c1d0b018481c1600f8880c48411000e0b0840c88035905500c801645031510f46 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 456111501 1250 456110251 456110267
    0x130b0c150f0604060b0304110105210a05010f05040b181906030605010303020d11030a0c0206040e0a0b0108060109050a051e0a060302070201030b011d0f03070b220609150c061508010e0c010305060303040303 90
    0x21850104034181e002030418800500054500b033140765203c4005002810340b16000030000e003002c07038060003101c045c2c0f4041914110156100003100c12524001122000c0c4240124000100d82e401085075a941e41850002020280411001405030014807585030380709802c408000942c03080610326011003128141e5003850a40412a0491418000041d8118018002078403900945002190240030803000405401000700914144180305805100c15219038a2038419030b001981c62201201d102200317461484042e9405903803180340000042501a81900a400b1a43c0300780c07014405a009600150b40b40c201c4d01850900c41d803c8580520081d1400c0d2040001065000e4207403a007081e00e580c02c2c60300942c0030312104900d41482c10000b2001042100b2104000d004500c1c140c05042d003025456000342000d00c0001040040c0850442c0c103015250340407500c0d1040600032000f02d642e031841c0c0c0700c0c040c000c4401940e842c0c0c019075498205550181c094940b1884006002c0c500d01411960181c49581c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 456112751 1250 456111501 456111517
    0x30901120b010e090f1b0a091e0305160602070b030c090f2806020c0315010b0c160312030b0d03120f020403021c17130b0c150f0604060b0304110105 65
    0x84940030040071901c84c2070075103000703810440e43e014051511a10003c880c007140311440724025010003c420b03c5540c4000813505813020651003c15892215810080e030045076003000e0070078041c00d4802c0c0d4540780c0000b81c010489080c0d40940c0c1e03901c1e655441019840c04215000b01040004014003207051500c100c842012140041040090005c140e503a4004001b46106d03040c0a00a1b1810911072190100000a65032001710020040c00140c02105e2201034018800c044010201190301c000c0075000f4882580c5626450701d4882d440c51752402c2c40103c12140002d4207005c203242080a035424200300b00322244d030b6a055201c10b0a041c050640382d0b0014500c108482e011503500303201c0800181c0e41c0304809002d044029408146034102e03420411100401038000d50305800c0e04024807110600c03030750700ad0012260300300300b055140c00e00c0c0d00c04142420460440c21042907046000c1040c0b41400c013044c3c9008040c02e03981004015110002e1840502c404d40b406800440880c0c0361802175071150008201613 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 456114001 1250 456112751 456112757
    0x10f0602011a060c1e030c0c1c0605060a03050f07061e080606030a0b06071406070c0b0402090a0e01020a030615090b04050402030924041a0415050403140f0714030901120b01 76
    0x1424141780364185110b8100510500d0760800140341c0001c000400c00341c0080c10301140c4034a005c059131300d15011030f5000c000c0c005000c251241c00040c00c0d41c1d182c034002002035400c641a200380080c4000303202d80f1090103014a40108030301800314684000040e1118202461644078401d82c0c0e114182008826000103096080342030311380d1000d1256448401c040d0407841d101d201011000d411103942c075070a21200500c10ad080101410b2104007155071000944c1c1c00c150140e44e003281546500c017110018094a2910604541c00000d900400c00e500d5030021049508500007042405891842207518603118480c08913200070030300040c0305524155008541000b548002ca032240c002540b00301c006440d141c0380d94180c9081000800080c403c00840f07504a4500a014203406450241d40d507800b18001102e611001a64400001d4101030007100b40c50a050014540d8580300c43d00021440c03010f50000c0c0c011100a107140c10003000c0142d0000a9070401300058603010064069494030704014040e101e000f07810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 456115107 1106 456114001 456114013
    0x1207110706050c0a0602120702211b030d060803071e1509032d02101802120703150f1a090601110f1005010f0602011a060c 54
    0xc1c0d40e040c2c1002d5450f40c03810b0000610300226408024066840098100e04468001c00720740e2140c50301340d00b15003000821610b180f010a81050b0205c210010a100751800c11655140c9426040c07110001c403810104281800c034155102688220560381001501c2c5007400380c100714540e201e0010b440170041c0d40401c0d0707031540380c07002113907a859062550b14841102050304c00d0343c5d001764105900c0a90140526800140d100701602e60300c40030054030424880c0710180b200c40c052000440402e403140c4281d0140d9409010320700803550314403c0c0074051100301000046100c0c034101e00c84c035951100040e00c1440810030f201203c0080c00c003411a80f040144000e540d40d2000e1000e0350040087c60040300081d411280d031445c0c440e000001c0383d00c42c000c0282d10441960a80c1c0000c0c101c0c1c1b802120042d045540b880264200d41d0000341001c240143c5625020341428003000604001c4003500869075 = true := by decide +kernel

theorem cover : BRFrame.Cov 455935251 456115107 := by
  have h0 := BRFrame.cov_init 455935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455935251 ≤ n) (h2 : n < 456115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
