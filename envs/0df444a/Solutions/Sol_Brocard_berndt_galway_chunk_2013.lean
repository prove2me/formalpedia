-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:17.175409+00:00
-- url     : https://prove2.me/submissions/7fd2fcc9-704c-407b-8e2e-5be3f5b855bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 361870503 ≤ n < 362050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 361871753 1250 361870503 361870507
    0x504090f020301060c0f0302070b072003010203150420070503041505090105030f060118140108060301090c15020f0105010603020c0f070f0603090804091802120604020d030c141b010e0402 82
    0x13200c8010126100400041d00d40014001e24104161081c01f10701c004058180c3c04540700c00c06410b2404401c020840f00304000e80c003050740d0458504044c0240c0f403084800c4410310500f500311905010203050002c008284880e00801c007820401c0740320000c0c2100c00d000b640215151800c0441e140009000b000c2030f1020b1010501801c82c13141e900c20700701d81e4010500041c6d901c0703d840b0711006035210318001e0f112400c0c4050230f400c0030070950025400f0000c0c0940c26a2a202940c41d03040c03e06088416001026180e03100030710b010f101c1404401800c003440b032018412650030389070485981d800c40f402a00000002600081d071400f1f0a00700300300038106000c00e2405049003a183c040c21501a51203441143e09042d241d06540c41408100e030700b0303107008016029003448240500003070100060038070f18049104407044403e003441d00e407001801034800d95000c0c01403a59880103440a503440e16071020101d400194580700380300c0c2c103141807000c80c0c4040c46541440c20303032000c084000341c940c280125459010b01c0c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 361873003 1250 361871753 361871759
    0xa020a020106081036151d0f15011409131406040b01170c090a09051203010504060b0c030f13051009060f110a080a0302040f0308033103032a0504090f020301 69
    0x1140d21700310102644040c0b007980c02840000210080d140c00a201e54001100f000c0038051000d0120340d00c4c40ca800781e5025546031039440302210a00300d0080c0122515800c0950f10303c1d0840c20100346d40c1c2c2c2c1082107490140401051350743c40d1203040880400c100c003140c101b901800100080c1115850151500c0800e08001103031000f10555181c010b001c40502c21094100840c90203080c0d544051013003608031058400500d1489070b80a00740d4400e01c640e030b001e1480c121002580b050382e4802d4603068480f04014506d0840d580210b80b00a81003014400c41009203150006640c2da10343c0040c0c1904c04403510f5040c03045103481c03005042d040c0a0b5282d6014000300107404e0034811030120300956903d602c0306c4101e03100c640049040740280282e41041c0c1c0b00c03100035038000c0140050200518414401d19102202442554001d041e80c3c140403106540696000b0a500c2c0010340260045411028240124034401b80c0c0d01180c251040314100241d0040f0704005014801e00d1454010f188001103074036400c2d861549 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 361874253 1250 361873003 361873091
    0x9092d0a03030507110d03051f030b010312030b10020c0306090106062703061107050c060f030103200603070c020922081b01050103060b03240a020a0201060810 70
    0x20200030300074100341e51000003510f01c9004140401a90b0f00f072100322000c0010420000d4003d000c25601b00c014510b0042000c8200318481c4202419690b00031999840d90740303103035903031206000e40c6192007085c151990241041e41e00c0309091185d91030516801040c401119005150510b14050504080c59041079801d100c020b030440e4043e640088440c020700c0700101e41c0c41d407201c1c00310f900740c00c02015203007000511924460104040c010240c01602500d102c000030508200341071190444240880f01c085c801000481c262020a901d4000b1400309201c40c524044005005a4000c45032000070a900c0b19007a015410321002c003550200e0003103038600d52150b031020301d0303485c401c00020020a4590300080384003120303910704618904044690024012561686040000303003401d884054040c2c800c6551602006c1c0381c22020189180084464081507141c40200740c02a52014010740305541d200c8030006110401000100710501d016000024000d100564907030032034a01c0809413154404c0c944440801003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 361875503 1250 361874253 361874263
    0x180201080f04081e07020306161103071208131502040623030a0207020604032909011b14090306040c080c06191808060a0606020f07030c150e09092d 65
    0x91113500042065103064090050b10500c50300a4140c002c03c03003406004100c0c0140d00e450f0740d00d1501c560316010030070011943e40c0d000318080034085000400a40c0c2c0300d1402000349503040403040306c80807001e41090b03e44072a1018034a940c0b00e1a59400113013041041d900c0705d0720504002000b0350b411400d0412194620040c00080c00030403010368009080011550b8180444000b181d2001c8803945440c01d5a50b038a540b0542030f20841b0328410107030000b900104c0107110790319130707070540e910101600c40403040c0455941c10640542c681201c0d080000d4001c079a010001a0701c294429160340e52110709145106040c00d1540c040140181303070a002440640f00181d44a0041404926282c601070003842d0020001c1c4426a0050340c45e802a00103101484001d0b4002c28103036112030302294480240040c071169242d50b288405003100c4c0c5844400d01401d900840000c400c17803400e14060440d686001d0000300038000c25540802c2c55489101c0324455a4900700001c00d103ca080c4401c5050000f01a800325160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 361876753 1250 361875503 361875517
    0xf0c0609240f1005031006180b030a0b0c04090204140a0605030105010903110406030804031b060e030718060503191505040b010e04051c02030c06060303030402151804180201080f0408 80
    0x1010b10000035160b003101460381d8001c100045c01ca90300019280b1030180144194050750310701e00c2050118101001943c021101d10f0361020b8010b040c1c4c40c0382510f408088404c080c107c604105020080040c043d5240e0000c0c10190078031007027401da4034403000c0030062000c80d5a0300490a00c0818001004540e03040070401d000c99401c040c90728140148980050014207041c0c000400b0524082400310600c405118400d50312001d030740c0c3c4c0d8036466403504815246581c040e07402d9681940550700c18480511540300600030100c0b01080400c8141d2a00002800c0400d486000e10700c02c00ca03034080800380a09503060508070388003d5800c00c940d08140d1181d4000800500505810050840202c0c08008080024946130300c0d0480781d003d690341020b2002512580440d002142500c00ca101090861801104072402103600800040c59a00b01d5501d1400503006080c0c24081041e10105580954899001e8140000039140d6010600001c51002401c0e5100191101860039008000c000004100204940d04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 361878003 1250 361876753 361876771
    0x504090c06080c040905130303050f190902031e0d0206010f060e12250f060801180510080a240209030a03080c090d0501060f08160303140f0c060924 65
    0x200d980f00104070320184156444000d0042c9070004108180307191001d10303000d00e442640d05205c1c80c0c66040001460a0b8151040c640440082420f00442e2826078041448640b0140c00c0e105968200d42d927079200381d11020f030b40c860250450b2000c00000d550501085000d00b182a00c50f0550604110f030051500902e04680d13030080c080c2c080c00c1900d1100400c0008011489803002c81c0042503200700c41e030344a003907070f2007a144c0c200030070880032400b00e004e01d0306107040c1d03402c04480b0080100301c078941c00301a100141c60300b15000c0c080306001c11140c4040c80364004a45c040c0d4802010520200190300c00104401041074080e841400402800c0d40e02140c1d0321409070709450842c0c800d0716400001c01441c03191020495028107500b900004106040d00068121240b1104104100d551009840d80360404617403442c00c0030b0079028051000070b018042000c1d680b8071400000f81000c01d40c02207814664418604075036940d000604101c54a40204290005044002000c8600041400c1700704401c0c1009401001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 361879253 1250 361878003 361878017
    0x204110c1f0609020d0903110109201207091b1e030c0905030f01140f011a03040503040e0705090306090d1205090a050a030f030b01081302010507031707090501090504090c06 76
    0x59004520b420140140c1128a0115660700d02c03906040e0043c8076110080300403650308029503031509018400c560303a55804c810303403004c1000051400c0c5981e0714000300b0640e0040710a40e110f0b00604080154030f0182400c91710014140604102c0d00325024030b01100c6000b0004e4105110b02c2c03407424456184c155200364100440d4454840700c00790341c0c088060300a87d8151240c0d120070b100b03010054104001001d00100c010155031206d1844130020a400d004100d4801e1401800d03500c910503a40c0115031140c020000d503402d00351181025175000e5001e40d80c0302c0008102092102c8030345011b000840e00640c200009101c89105800c0150201c4040041c02400316681c000042d00c6602c02c0c012950400e5114017a100300314a649000741407000d81d08003000020b0700e01071030808154007504a40307014000c070104e4100049215401118164008201201004603600310b8804134050307090002d00955054542c1c03107170f55080c0000107113001c0302680070744e202e0360030290080e0105a5000da41801e9a040c0d1511403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 361880503 1250 361879253 361879303
    0x109060809010f15051305010e010b0f09030115050f0916030b0a0506040905091e030f16060f02030a0e03070209040623010e01150221030a0e01060e01030204110c 71
    0x780c0100a09111a0012030800440c1c0208052003404641601d030304840d1198001070b800c550a08603034007401102c060140303100c0188042c082d40009090700c01a05080546130601e8680440d080d00c001004a80c510500180148601c2c600041c91403401c21007a102008245040e2102c2400355107904091020b06580c0c190100315a1140044400034250140400380d071660f80320104402081c00311510030450042c1c5239445400700c00328030100480e000600003035007884941c81400401c0e80c00340b003140e12400000524403001840070700072150091202c490058481c54a41008001c0d541c4d0140034000075042003004a00584d5520210b0760029000b88000802c8800c41c00c40c203c1c4511403030000740005941d24000180000d40700349503416903c0264005034000741703251042e42d039500840f04000712440b4648001400500040240d64000d1001c580420151440341200b401c41d000b680002c184104640018010740c10140140001c0540f83c0340d00ca80350042480915440700009044031500d01d01451900c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 361881753 1250 361880503 361880521
    0xb1c0b06040b220c090b0415030f0509160602070501170c070510062c041b0f0e1006080103080d02070819030c1106100519150807080604090201090608 66
    0x4840024040c0101d52003c035a0300c450a0306042d5a20709610640c1005800c0c1c828900c1400c505044a525000c1c3c24189414403031011000c100e60f041d000300309a80d590385074510034040c1c010316000ba40800e000d1b001c80241580781082110149d0070040035903006076002c000c103903800158480e0701400450365510360344401d840110380e84204a0050028850600403550015503030384404101c800132403032036010130714050419201026001114000c510703034800060200e1061418000c038031200d8072004040030b07141c8440141428070341e08031011000c0a20200b010b101c20038901c040280c00d0078180301d8950740c03441da200d0485115409040b02c0c49600441c120b0100500701c005e07506003010b08481c100da4518038102c000c0003815101c11581c0042c0e002c41502e070128002040ea540210f010014103100c1c0c0b8104408d2140184070b0b803101d1034500d8804103000841281c7e9580c03844a858907030752190482d00f4003000040c503406010701281c0c072441c0750140490044c1c0e0003030880c2c01124200e050501c4035603995240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 361883003 1250 361881753 361881761
    0x90b011202130c23040504140f0f010605030a02070c050603090a0c080f0c1509150d050a11091c020916080903040f090504081605011d010509070605030414070e0103060b1c0b0604 78
    0x8083d401c582001c070323654000752030718070124410080704041d031140e41d41d10120115003038428424803020960400100703101000c10340051508600520841003129581e81c04140c1b507034800c403400e05d0250443d400c2d07103080045440d100f200034005400100340480c03100c845951200c076103204092003480e4244c0604600004501039941e99000144441c0c241c560034000c50400e6404403141900680c5003a0010305841e800c1d00c81c6495010311410060300345107150f414800c4410117407901070b8545585c00142d070016924450702d135101c2e00c4124089800c4900c298005400640f02410024880d002130100380b001c40071001c180710881c0c00469011880e502c481c28044071603c01c124402c20035444c81d011060510030150800440746442c2e10510140b240d0001c407080c226181920400d1386500303c0c035410445180b0a00156410600502d14281086c80d41c0c2c416500d0100594020702010003008010414000303a44249240c00006407a00320b50802050024150000342c5031000700a00c031020046251ba842c4ca40c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 361884253 1250 361883003 361883009
    0x18050409052514010c150c0207081b030607080403020d050306060702060a0908060604060f032909010c02060a0908120411060c0604140d1d04090b011202130c2304 71
    0x2241c140740b441d48032490100c0642400380014040241c0c03a860303442e51081d01011201600454084d80a09201800001806201c84503a007144141c100c00300d80c2410034468100300c03d2204030041509900401031509203100104081d003800981c2c010000407d4010900940c689414a0929174954803000040c4007802081400307500401c1c0403e0103003420750004500420344065104480350703070b0746080400040e035845026481c03072014000001c00004256080300701002031801880d480c0740150071100c00e80440200c64500b41f42c2e4658180d040c8241d0144685504400301101c00e101d01041ca4441c850280300b0711000e0440e8569007400201403280c030800d12480c0007002001c1a50b10250300200a5640c103080c1c030207441045a1030100114942d0000391020080c1081e2141003103a025220328894103200c130708034980c00a44540f12400006e44104040317000c0c00c02c3e07008103620017a060040c01803402c0364501d8022038501d4000e04e10803958100c201445c1420b02e61580700396801010036404242d001d154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 361885503 1250 361884253 361884283
    0x120a2106060c12090b0a1206090507050711040207081204140604020604140a0803030a0218180105090c130905041a010608151201020d47030f0616030c1805040905 71
    0x406d40180d45a40080d400080111034070303061003069164040ca5045400680310000440d02c100320b000001800ea040418000000400040c20140305031200d285030780c0200c40e400d035610403190400c420800d050b51043c0501c0c41c038000030a80e80c50a68081810f038444c0740207041040720202824960399542011110190030844240c1e602ca04051040768040d422a400707004003084048810300260130121400c1140703400358803c40c0d04691030a03003440b4111101800400e02c44e1420020f0b03000a000b03800400c00200040903002417145030a00b8241d05100d89042500c00301d0210000401c50b0741c2c0d000c91060b030028102c6046500030004000002c0740c400d031038041d010940d4004100c429800410703500c0541108080003c4800619040e419101d40b2102d40d000c00c8400103002503020b0000450440d40003a000f00501100c0480c44100f1941e80ba0103011a901200c29600c92150b0210603232500420703120365800c2c1840030242c0d80001d4846000c006501496024994400341c030810f2150402507110350902003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 361886753 1250 361885503 361885507
    0x301030b040807060c110d0206310f03050d061215051e100501170c0a0c0303020705030c010914010b0307120503070b0717010e010e07030e120a2106060c12090b 70
    0x703510046c20740485031480106501904541d0a00d190001c00d0301d62080c48a1702a000300c1c1c20003481c82c00003506203181c803040f07842030318072140c030001d00030407000b0780c506002c0d450b02038a54282d001028240d505582084007444041080c010010f4013803105035450346411000401c0c280e568140d03045010f00b00c071024600250294007400f40c05400f01d80720600b910340aa0352041c132042e060080d03103019141500e40d04c0400c48104015450039100c1c805041c422807184c030300546801c26503207441f45541c01c421a041d60320307590fa40495040201c0d5841000c080f601d0b074402444800400000240c860710184904800b12401e6045101000010b1003202d04c03466000d16600070354288a0750080040c40512180c19903400d030f0000104442d03035a2540304dc100d46420600c9030403982c440394200d01400c0801030700d040c0c0348246074400d003900750b0b400050400c20515950b800044203d10040d180741042590722800d25034501542401040d07401b0805c0000b4640003003454900030400c1c5000c560402140e40001c041e9200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 361888003 1250 361886753 361886771
    0x90601051f032d05010510030b060301270c020d03060918060b0402160b1509100501120905010c02010b0a14030d050f0405030102120601110d1e0e2e0201110301030b04080706 76
    0x560b07801340e816208151008190700e00b41c2041582200e8803901e9140d80510300b03100402031402c0d0303000120340001c040b4603034061004400b00703141c05840c08481918050307080080c03051820381e814031596004060f50707403041c010307400400c12a044050300004007400715500e81d201c0c070b80d01c3e484a4040b6004414003c01d03801c03c4038024140310308a03010070740f26540318005030388074041c241c85c012000380d01410b4504041c07071003a80780c203006441c1c035002103a2042c46c80e62203c55500100342c0a224028580d021a0004036400d00c00c0810042c45846035040710210381140d00c216511a2400980d100200c3d055080040d50350504040240d00ca00540c1e0165a15600028002c101014603d00ca2030140300700707899030004080c0303040324183c0701c0c683d40d085c002c000388048506861a240f24800b8501011690600746448808003003c1950101190b5401e0b09404420524200700c20f041d0740a1054024648020840b1600304020030303801d403006120143c50b0090040205081c00084030840d16090340c0b050301049000e030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 361889253 1250 361888003 361888091
    0x102090307030f0b10051f1808010e0f03030903090405100b07030e0a0b0c0d031d0a0f02030d0503070c0213181a0c07021804030309020315090601051f03 67
    0x740d500f008035480c50b03a0b580426a1052450b4411094941c01405024aa403600d00c030241c0e0040c0010542c0100b1100101c2291547e003124604400780500c40b00102d107517180c1018103860a900000074907103584c400c0040040916020081d03640071103046030042051b0305d038018642e6030f0702d10b141c00108003400002109420550012044041c801003a07903840c0c08955105201982c500924078030f20312075041040030300b509600c40d5100c49a032501c1d050400001c6d80e091461079142c41c001c41000c80d0b5004c0c01058800540c541000502806030042ca025843c1d4904100000e000680e11400280100227803501250b0647c00d80d0010100310400c000d058214030401c1c10131185100d41c81c51a140b4030701240300030030001c0c52900112000c141e006052284900b00c04141981d00000040c0309904140da144040c00059906100c5c80403928031001c000c2d0080d04101c9141070034aa01030f44560b10038002d145040c40d01c222050445261020340d4100040c1c145e000f01c5a03100542076074104413144071070504400000714 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 361890503 1250 361889253 361889273
    0x21090f0d05160929030c042a091e03031b030c0b0906150109050d0305030a020f040b070b070926010b0a08010906050901050c120702030702060a050304120206010510030e010209030703 80
    0x2602120401a00003006840e29604d20002c0342299056042040d000d202400d20303801421081c0000e44808800414041c1c2040ca0400d040c0c020320002000f00104009411040c840294941e20080e00c006104d441c654000e001090912411456075075005080d00a060180c0050790446404c40f003120314503d09100484d480c0d0008850685010804800181c1103500c03501060098400240903103603d03c5464801b550540c000030042e03040700380c00300284a0401c1c00d0501900045c640c00c1342040c0c507148189841050301600601d03031002c00190040401c82c2201c07010800700c2d00f50b01030030045c0f000c0440c000a1400f50a9813030945c0d4024168140000c0d041c0c005521102c2c00d103006102c104002e848075019a400da0b01c050700c1d001c07041a024404544c1d440000d4185a03048486401203d15003001c50740410001d03000001e05402040c0c000c0204400c0c00025990f002e050985031019124542c10100016140d074001034180c8101030b81c1e090000340e020004d5048803442d4400804803180b1503520300d0035500e02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 361891753 1250 361890503 361890521
    0x9070c03110a0c03210207051908010f06030b0c12040305070807170316030e07060f0c0c09050f01050102010e100f060f0b13051c0201051e0c21090f0d051609 69
    0x11840c161440b00d014424092175404036200d5002c3d08106150008000c09210310105c03c0c9041c8444400c00100f1520900c00c10031640880440826060319505200861000081200b440c50320204004ca07001c0c039809818540c80782e03050401319220701a50411910764040e5510003406224080c1d507181244c1c6044000e0352040c8405200c615113005000e00c120140c802c003440068191b40300300c0040c4038107401104401035a428600d460341014405444008424080e42c0c0881140ca5a070000c0c000d10028184000307000d854207000074002d80340c52720300680d40c50038007418208181e40c0d0b400c0c4034028542d0301d4104000400c00c158240c0312039616181524032603481106a100d181070031020000302c07800d0801001010041c0c4c035074410464000e40e001515140e00c10009090740c03600602070400042c3c83c0d9005450b9440301e03e00102610000010300e00d0740c080d460288400040424000b00791944e4035582086070010085d07541011260852400901c1c0c0481120600942c0c2c0c60800041101d0b100c5500c08881 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 361893003 1250 361891753 361891763
    0x32603091b0109120b0601032a030f020a170603011107050606040501060806130203091c050a2a080c07090e03180607021011160b040317040509070c03110a0c03 70
    0x80c1e00c00140055030307411081d203d80d4a4981c00007440700d0120302500d48040d440401810041070210304006900c00d00940400108294000c0c002c000c5903142c0d05100b18280d00c0305c00d0600b10318043d0030003406846c50030050801002d1540700800076006860a4001c11007014010700603680f01c3c190b502e041c60f110030b812281140200d00d45800090391034855068a8040e080203800c90700c54901d00c0c00f440c1c010b540000c04801080c400c0203c507200c0070140c0760025540700f401c2d41c0c2e42c540741c100c0e84100030300d40c0b401c0d050502c8031260024400b041c0e41401c241d8050b41d00e40e0142c40c2a50350802d10038120700f411400d6020361440d51402082280f0250048010201d0050500c03042e4042800a01007010307600500101a402000880a080e5000c2c02042c00400384076048045542a51800a40c90b80f4820f0a030080120341a010808000300708a442646040340b10340c1c8030503401c1a041102117605110300602da0380030481500918414036015054002e145502d02d001d5542c001144c0c10f00c0d02142d001448200c407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 361894253 1250 361893003 361893043
    0x1110d0909110f03060d030216060503042906040c23040312030501140d0f02150c0106050301020f07320703110609011e11060109141605030103260309 66
    0x10310040b04021110403c200c0d600080c02c6417540340a00901e1600f04004405621a213200141482c0300c40c1c2e2000028551a6151940c910301031804034202407107403802400060032008000490800702d000e05902c0313001902c00085014030382e00c2c22140141c0030094100502c031100c00f070b1400041030070000c0090f2070140b43d030900405a407000440460b0424410003640c0202428000305a1070800401c420042c050026240b12003415000140c01c4100001c01d000110000030b91528449801c3c0640c0006020440c002c500303008503003030050102d1041150060510344440c003d814080b0035031401180f40c80d0420b034604000405070709031642c0d40e81540800e442d0b030b14411008a003907180c254103c038965681030350380854044086143c0140d440d40048503c01307100c55111018201c0804101280c0241101c07440443c1d1821400601d140f040d501801c2c2c00c410104d10a004040c903900081104c0c1103030780c401c050300c00701030000241a25034a1a80603540d070585000042c0034580f00005455505040f00c184040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 361895503 1250 361894253 361894271
    0x2030f030a05071502040308180306010906030b040f230309041a06270d0f1407030308150103060b0703050a020d18060c060902030601080f0c150d0b01110d0909 70
    0x203035030380500c030400740004400b008844001040501a01c400241d0001c002d41440c0e01daa540c46400e410071400c511001090b545400560f18081149600502e290b50040000c1c0e0308513140c403c14548000c0c40a000c25901351003030410000803601d200810341001c621601c2682905202603220390240e84054815410010348081040c050690f1012181d80100b84515000f90241c1c00780f501004096050380b5502c10404c20100b81d100c00318100c0340b89100e49048220101c0c24501110302c45071508030200303213920146080c80000c3d0804030090300442180415512101380d5801240030b0036407030704840504000419610b0030581c108010b00312201c11a003d903440300e0941001142c48801030304680da0100542c010400c1403600a0700c84081d100d00031000440d8079480b640129107807130300a9116412a074002d445c21044400180a52740e9594001c0301c0b40c81607904d0300c81d4190828000c80107400e0003a41c2c1c941008180da8012410405512688001c1e180c01c1740d9021805401c00070b5030301c103074903100f41000405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 361896753 1250 361895503 361895533
    0x3040c060305014704080114060d2a15110606130e010b0a14280e090f120a0905030703051203192909040f020112270203 53
    0x2e4140c07a0301034071a48004642959030b61042100f404039800b885050500d6403900040c6034104801007000e00e151545c0e8a151803105030845a0610b007a100c4003010350300b4016241c0d110250008065008400c8105181d4140110004130b0300c80c4842400c03013101d03440c001412801c1c2d0141040703000d219480c0c4243d02800e40300880d0702c82d01c2c01c964039544002c420a00d0610b000e403541c85005102001c000008402c0c2c0280301143c140100c50b04105038025410750b499050f440d12203810040280c5440100b0b80d80c0600342000c00c1c404d12540141072000580c0800181c802104008001c1c1c82000307001110004104204401030070fa220405010000b200500c0124060800080080c00c4a41c490020485c0024030044040c0d03980020303140085000b078400880001f181c0c18040c4a00707401204039540c001c0d04144842c00054240c034043c440c0900380e80810040452080c00c0d41504c61502800c06200c00380b00e2552484c01064421140382c0b0792031034011a01034070022040c4034501240700368120f1725448088944 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 361898003 1250 361896753 361896761
    0x60902040b01320405040f0f05070c0b0c0304150c080402150a080c0d020f0d06090b0906031c030e0f0f1603080a030207230a0b060a06020c011409100503040c0603 71
    0xf140710410750311540401c1c0b5100003007900f0000340d40d8984500f0703e61114001019650607880d03600c03100340c40b280904001d116a07c10503801000702e091151403560301d0b0740e80000300c402c001c03c0881000800300005080c007818440500c4686078146042050b261070080c080c0c2441016a003e0740500741d00c0b080b011541e0101c40c00c0300c03030300b04003516040d4850342d0301080c0c07114a034010308103814105d40a128801202e00303c100502040000d0046c0828114106990801100d001c0380d90340b4814094801400810f44002c0307041506e411110011074041c850313000f81500076103609040c4080d14440c410312007000c40d9000c00e01d82e0382200408240c2c0d0340a541d24044400303401c110f0001070202d18013003010442c80d501039401496603d12031340030035454504600d081910345414485494003504010710381000c01081c0070b140f652001c6c08903a4071404500780740e0020350700c0c080c440d20a41170111086490100c0d6070410292059568000c200030240c1d901d0714802800c0b90000d0b1070446001401a00205d8000e0081c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 361899253 1250 361898003 361898027
    0x3180e0105030a2319151a01030c020a3f0509011d0a090501050310090b071d09130203060c0c0a03200f03031906050604030212030f0304060902040b01 66
    0x28591030301d054680321114070503039207120660700d40b41081080401007070226202c09469004a60900c8900c0c1c06c04507200304412142da24140e29044035055200c440205107005600f0a103000214410344140c02d03803800481c803401500b182c018046403203155484041c1d42c50a50244035000094050b15500d5200490142c01e0a0300422800e20500341d01c8d500c2441c40c240da0032000c0034031000004004001c140600d2442d0804070f106a1580018451400d04001200d115000250200300001d55074899200714807004d005c4004001561384d200700078100960070890342030340042c441782d0075041402c071920340c022000004a0103400364000240f0030441180540c0d1036881c454018001060b85542d0803694102c1025801901f00440c0315141c0c0398641c00c005d03442c46194100000c5680c0d003440303060902c1202078509200700c07550030440b09015030f8443c881900c04696055401000a42d008104030741140550540b607504501e02208110501c03484d5080050114000d0b6410041000c86a00441d151035901c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361900503 1250 361899253 361899259
    0x10503060f06070302100509060f01050d0b1602100e06100e040b0406020313121718151005090403030609141501140c0d0801170c010914040f020703180e0105 69
    0x72944284a04108008241c0f040c03180c070554050502401e02d80301200d5017500c501d8040e602c00700030014034650300c000071800b4007802c40702540ba40c60196a2404034a06c014691403404042e407030705040c071078000c000c50200080126818010030b058004415130700c80c82112140c000e0302c5e02010004464104001c0f46001e59080001d9100d01d581d9a244c01c0060350010700380034580e2501028020210b500859030000380701481d69070002c2504a150400410034018ec200da1194a54144100c824000091420020084292003d60582d2640115200000c2da940310a402903285400c01081551590040c0c0c2624446a01008a2100d0042801180104a554540301410400c40f0300715580220643c80280c4030110800e450200e07203212060907c400b492440c0045400240140000c050b0200c0b5600e082c03181c0e038028440401180e0008054030503e2040c00d95418055102040c030341c80ba90480405103a00850545d41e80e0700703920b00108001058200c502100c00c0c06100032a9032604009614100d407401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361901753 1250 361900503 361900519
    0xe01030305161106030c0c01060e07020327090708010e01090c1713050f010903020f0a0231020a09030317070806060d090204060b1b010e10050a0e06150103060501050306 74
    0x10415142001081e4201a9800c0c56403940c10b10343c03507441ca402140706804d80c00800340c0b03802102c11258207480d603d030401d122101440d0104005564004143e03400d81c0d486406c801d03459030840d080114411440e0551641155403a020407014a40124456048076566584041580e03640c0d1005000c552140130700c940060107034840318000b400c141c038440742c10400341c0d180c1000414443d5616407602c007800c11450606d0351140e110710103054060000b0407841544c5806001401e6040c2d00055440d00568050380c501e054800c500f2428803100c00e606608068405000c550320512101c0140603816527100880005040d0311550300c0c107881010078030323004802a440303501f0f00d91a00000c1000380e40028500d4400a0f0340c4a80ca200075950700d01400004110407011540e441041e8500300d02d01300c000e10b00c1c400360340c0c1c10030b800f10f075140e0300000f86103c940003c000000340503102d0074480c0e80500b030b140d240d801007886003005000030300d040c036240e007003006109803000c000a903070741c1005661070300040b621a40d206a00b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361903003 1250 361901753 361901767
    0xa020307091d070305010b011412060103020a0c120306181a120a020a1202041d0703030e0612040b01050123221208120c09060304062c160e01030305 65
    0x106402c45100c4140c1c80000100c40240b044140d0b20384080e03688180c0d220380d1103455920302540c12440b00300403080458043c80c80e000360000c4580c2890320241c212810103074001800760003d4483c0d020707400d4a542c00089800d8403001c05500030003618041c018158000000c454880c03121480340305902480408102c038110070134043d0100419100050b190f50a1402103282003401641e0791062140900b100c0682401c02d0211070052004840040c15100440a50400f00c021145400070303c0c1402c5135414580402181007140108005014128050ba1000900c406100c108480310656034180c0e68280d8900d42981e000801e210f030359801c80b80d1007480c000c4003080404c00460304445855007070409001e8440d061640d603c81100c54106144042d14107000109440c03440d5840c1c0c400c525084a141800c0a092000c040000b442c1c038130000d4001008030780c0e10032100d08444a80810240c1101c4103050b0800349044012901d61a0b521010882540d404001c0317001c9801c00040c2e150b141600d8142d5155410090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361904253 1250 361903003 361903019
    0x6090506131211040609091e02030708011103011a070b15060702040f1d031317120f0304030909020f030c0d0f050a020d0509010c1407031107030f02010f08060f0f060906030f0f0106020a020307 84
    0x1612008c01e9030103014812000c542e1900034003c8002d05500200c81036038940c50705170b8400111080040040c180c010401c400b4012911364581c80e5000403d0440051510780741d07400140c1248210380c4000d40003402c02d8180010f003176139680411000521144a218100d11000c0929202c1c414034400455103a82410280031086482c0300e600b807102060f900301c40040c403a0160078205a00219403d115240f800410801019800b0b04428010442442c0a50a100c034210710404c244c000180310b840c5006001c554600588400e40025100658405d0200090304140c1c0c2404003079403003c1041c1001c241010701084101c0c8052189440f008544e030760b940061500800c45042d260b1000a00341c00300001c1300c821203440319051201c00001e62080c1d12407020412184000f41280302e42120b40f40c1401864800c11140f0340382d0703a01c01413060404840b0340303d45802003800202103000360810180c00640100c10030050910b04d41c2c400c0c0c040c05a503403008109a0780c86074100c0e41c40c000b00000a4140e0001001000010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361905503 1250 361904253 361904303
    0x406080d050f0d06090506030f0a03020d1202071428081821060f010b0306010f0f0306260c06041409071b030201060f050a0609050613121104060909 65
    0x10054040b00e2900c002c204202d402d07514a50010ba1005036502c061015a06e8104104841c044006c8045c2c4200a0075403006519440040400b10610200f41c501700604122941210300c0c00f507100414010210003d900282d075039504903030184501c2c185d0000078900010325001c61480c03550200786a4a404840000450000c00400425800618031088a50144c10720000105208032120050a0701d18003042c01d0084640c1c107038454480d100c420028446c90b41d9000c3c03c044420b00c41e42c1001589880c06040850040c07175036500807000b0004500031400c5030218000d5244500c00e00e1000c8842c00d00002c0c08101e95441188241c0e6465038211001c41c4803800c241c01d0741507102c519410603405400c10090002c556021148040700140d550724820b00808941074a0040504015242607a41030b0402d100a0200002801035611490020030a885001c810035440c0015000c0e008007044c01001500d8035868041900c00664031407410458042101d048500c1600005508100c1981404522042d025881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361906753 1250 361905503 361905517
    0x609040603020d0303050f0f160c0c0902040906140105030907060e0f04020a02010504330504171603020f010908032706070f0e100c08030a0b150403060b0406080d05 72
    0x10903240c0100202503982d0800540226010340c0703000c54a0314081c3c45511030b1a100038141d07a1100043c00903c80c20440154820f41e05041a0800300503c1031b21342000500d08209611a503200d5000140108544480c0d40002d0101c0b0281c01c04d440b610742c550001540d00b40000c032419109980f011400700106841805d00c032051500240001185181400110b4141d910003513850000d07039162010302042040c13103c425000c40c0364002c03044060102d1400c008504050781c2421410581e120b0000c40e040c84115162010111070102106540342c0e9007082092282d422170301c041c0c01500540d0070807420000c06000d00148550320003c65803855598440050b090242240216902e240703505035106511020080d0078040c031001d44410f01c0c11207928000404900a07040c1a6004080300c61102c1681c0750041c040c1c507245a402822141c40c0e9941600c03000043c80e6141c140ca5000013003206031480111104003d0040c0c82c0154001d2010124110500040e0b46443c80b6280041c1d00207404015150700c030b03001502003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361908003 1250 361906753 361906759
    0x30206070f0306030c14090f0108060705070c08011b1202120403030f020c0141070f0c081303150e0a03110304050a1401030e0f15070507020d0605090706050f0304020609 74
    0x146a132607844001d0300001d242c0002c3d040d100c41400c240b56620f00307030704030680c484a140103407041c7c0d43c141041c043c2c6540001d807101d4240080815100d0420001003000c6020b4010350008204a04562645031708040a0300b007100d002c501c40c002081c0100b9141e000f21000603a41000355141ea488555046004001d26609225a20760034400320004034400c2c022008580041d88042040802200440100d0381a440301603002180c0340c8000d113101045040103a0f84100c86042c8141e1000300305109075510250114018800b201c0060140b8842103440d0b248402d4034054290704040c042c40140003012591007010381c6450364007040e92640020f02c1080f200c4076989844040d42e040a81c2c134004143c494440d500498204d010807a5a1140c550703062142c0a803181f8a5001000a1000c000d2071a0b00c03131440400c5045980c0d1544c3c00640202d00500440b00025800344c003a03120141b090400e18000c0000b607440141c0c074050b0a0700000c905110b641507403d890501d103111407454403164208410f561084c202a030f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361909253 1250 361908003 361908011
    0x3060522080d020f0c0a0201140c0718021303061a0d0201170415151a03101502011d0d08100522110705030c060c040f0b16020402042601020304030206070f03 69
    0x105555030101808517052403000508a5580a00c0050280340340b03145404240d400070b0105509100c0700250301000c0300c9070504103095a0060b00c0d400c00280c45081d0b900958080c00c9100042009810f42c89040d42c1724070415201c0007114200100444204d6109010303001410009600c20b0a919000740a0b811601c1a100212031001000c01c1d0002c2c3c072010000b0050042c00410200301c115140c000c009000700c814140c8502d144bc01c0c00c0c11001000d0680a0180040ea40b0010319009a0003540900b10003042480f10314194032416003500d41d81c2c251601c1c650000348405011409a100003442c100503903c005200030680c0e40c0e0251707812021560a000c014040d80c46964141c0c008140100501c0c140d8085d0000c0c0d40d8a207000007480c3e1034500090554001c0e24002c010411800ba01c500e02d1009951003404880d50310b0700c01c41007400440c1e440300d0003e54490702c00038000444000c0e02c02c0000000b961085100c50310072030082c1042c202d0001301c80c01380140c1c00c10400941d195100d1000c0002c0c0c0c000070b0500007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361910503 1250 361909253 361909267
    0xc060d0b0a05102f2a130203160206160f021603030c350a0c140d09080105162307050c12011b0e0d150603060522080d02 53
    0x201d107501c1c02001c0714042054060f0300a4000403013240ca8441c1d40e26412070028129844c405107640e1035186031400d1480c03400888400d00410314042030345911030b00400013101034019000f44070096005072241c00c1e00307403c02180d1400490010403541d105848401115428201d41c2c2020b541c2d4441c01d0400c20114000c2101c0318191081c1140001c0240d40207a039000c0c640c1d2070518289801402000c5428030741007018900c070f201c1c98401c5404000081071800362a4a85906004c02d445403a1804001424083c0c1001c958100d602c00003550149800d00b0340d129880650b990702e5650880d0802d40d1514003e04800d5040a4014020f50441e103080a40209900c4000719012315980f40ea001684103d4440c1c02c100c00c6002a07103405e41140c085280c0700c000811240c09071041c107024001c00f00c00e1000074045502e113121170640d0740c10080b08040e074000d440f10b00340c00c1e0710b04401002032006002c02c440755451301e804074800d4080c0220704024144003c001d0803411400d5190840390740c20041400420503003c00c290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361911753 1250 361910503 361910509
    0x13111503010801050403110a12030c090b0a020c01020601140607080918040501050105041505060a030b030304180f0507050f03011a160501090b0705191404090e0a03110c060d0b0a05 79
    0x9600802d00e400c0006500d00313041c5002403d000c600c11101020754000d0741d190001c81c201c4064a079021002c0d040010316808200c400750fa14881c035900144001c1800701e8015059900404c0e56034007003100b41e003610500c0c0c1c0c84100540c2401c400070001508188280305007030010349003034000c00141300001d1442c603116120314031820300c0040c01c0740c0449281e51240300410803410300380200200c282011650040942c100000300e000350217440251010152201c00059064a060003214050010100b80e0328480c0d642400490241c0100c0c0c0030410118075003c00180110321803415a110700560105061642c0d180105014031000c0d407000113440014204030140710340d001695580718040c4500c0003c100d681c01e90600f41b000303410061000d0f0902030700f007191081c00d490440000294a041d42840e4861040100250106015903000032004034070b480441403080310001a400704180c0309641c0c4035228070a9442a50b2a0200c4d1100c0e030790801420b100314482009130f60440d90343e1b44405040c86201c05d03550000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361913003 1250 361911753 361911757
    0x8100b070804030c0b0403050d05040303141305101d0604060e060a12021308060601030509030301060f050c030c031c020a02060a020304141002041505091e0109091a01090509131115 79
    0x80f175411000c000070b04000f000400d005061110940e8140301e820649585c8001d490008021200d440e504000030300e04038180d0801150401030000940280c101401c04000504403800d0f9008a42c2c00c54103035a64070185280c00c00403201560055074481e55050140400c0c000705401a0303021a041c0031024941c05a064405e101038296050362203d0329260b1842d0100325818000058071036810542800d0030451216030000440781103801d00e141c500540c000020045405000c0c1c600c500050b40000200780040c030030000b02800c3c2d4043d04083c600c1d030202c108120041288250390302680541c001e0310011702040741590255500c0f44c09100404080c0e80020703001030801e0100120310f4441a030100b000d01200d5080007a03101c200d61107050441c0703441048800035089002c81a90340318000c5008116492591154400000800d48040107100c54400c2e0458040c444403608800e07800250400c00000b042d04d0f02c00301841c080c010300c0d58040301d106000e403601850792445000898009400b100700c05036200c2c00d540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361914253 1250 361913003 361913009
    0x3030a060608070e0d141510030b0609040b07030c0c02030d0807020601060c05100b180a0b010206071d01080c0c070909140102040513020307030b1e01020d08100b070804030c 76
    0xa000980315050440182100ea00079000e0810000d06135060041e43c0ca64501001c1443d8000b80c00103215072400c4e2074145410341c0e00c8044d0b07040c0800442440034140088149106481c400d0707000c40c1c0c10342e0310103050112658048a029010010340c40104500e1400f99000780c14500481ca0400c411201c1c0ea0007291503c0d0b005690b0030005900074040200d04ca6043c414503014202038540848040c00f640c403490390b603030b01c0c4000008545a84195070404d95650b000c109002c09054042c40c040352810340481001003080d500c64034094040e0304000f070703541441a010f40c8502150104d1120500489400466108000510b05542c11004004502440e0000c0280c0c070003c3c0b1b0700540105840c41246031842c0c44484001e10b021481c0c1c0140018003859440b07400403540c80340052401a02d9030b075252000c801803e499040c482c1c00c15105d02c501e203000c100014006090500a0b000c880c441c28100c00d003190281d0003200c2031841441c841d4001e0160018400c0104005801100c505017420348036180c00009800301d81c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361915503 1250 361914253 361914271
    0x2a0102011b0203130501030c02031c02070b01080709112a0c220e010b060a050d020405090c090f01080402150a05040b04090501030515060a05090c2a0709050105030c0409140303 77
    0x304200d802c00004d1110b2002515081c601071010080140d4041d56900030582801001d1030410000040c00d14a43d058402c2e00b90403120302689541e6130441e01d61a2141c40c00303106503980c101507080c0c541d81941d20807180345180300c4440b02000094071642c03e2003e0b10302c00409120740142c030a01d061740da0303a201a980390400f440d0b02c01602912200014400c0320f02183d01c964440c1d052110650441d0b4030b51003654083c40b1607040c2aa950040010507000074030446d001f00f9804001e000500c5a03c811010150000c250140c41e6440c2080860006403200031046400a50201d0a040c681d2031900008011f4036501c282414001c0c1032035102e60320540c198001d500240c411640e50001001440360820a03043d0071404005005010708141000c584410300a02031140a481d1110105600143e10822900309100c0c0b040c103421059400c0610313070b0300704d8109240000d052040800100e42c14069208950403100010000c0c0051086001840050181140140d6203a0550807003010751303800510055209401003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361916753 1250 361915503 361915507
    0x706090501060603061d07030b01021c02150a0905060601030b0411070f03081807050f1507110a090b0117040201030e0a0b0405010515131d0106060806122a0102011b0203 74
    0x402c01022a590f46d40030610300440492080881c0c1840000b0303c2d00051180f03000b1034801030080c01030345411ba11a84c10082443c50b9001a018280d002c40d1454407040031321403a00c030a4075444290030a071195140301a0007a000800400d90541c001e5000d60b100719030250012a19401360f041c441001d82010200707450400302c842028041550105c00258494042d482c61340d464040408a50741c3c402090040d140500000030307000380d0310f41d1843d030548a80464a010aa40c5034100d00d408a0214880d0f600c0d580201c840300f80105112030103000e2000ca480e0180c1d1070301481c40d92150f485900b80401ba00c00c0c0e042c5aa15824901040f0040c01b40802882c0600c0e0035141ea82031603e44a402c42d000144601071101100c2402e0516568044500c4155a02c810713011508940941c0c00c41d84240f40c00324216040c0d880c003440000d2558000120503c225800c0320482140c80341d100a0a4403a640c040802541c90589015800700c0c400080c244d808070b14041c800000c010359907041101d000311120f1840009a400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361918003 1250 361916753 361916759
    0x70e12190506011a070c030609031202030a021218030a0806060f03090f0c030307030c0b042406140406050a0614090409141b10051c050a0e15100e070203070609050106 73
    0x3012256003614644d0341070785181507007684640b10440d000d408010449600c901d080c0017894455802c0003107005004d1021581c070b003000086e110080d03111111100514010b503000803d07591480503241284403040b800b440c5003007242c080849550100800681d40000c052110345012000c1101541c03207541c0c40c2c0d0082c2038075401880d440c1d1910440411651007684100210000a6880600d10055aa1100c51a441c9480e6481c202c0100000e00002841343c01c034100b00c0040e958095001503080762041540000d000b881c1c0d400340019602103004041d080a2100c2080001c4c0d4440c2d0b040b903101f0001d1540c003c1c100030400b0002829500c02c04010348030403a5104100182c003105101183d05299400008595000d240000c24008900d0540f00ca090000104503a9041c10701c40d01e0414000405400400541c074107484003070000c1c81d28444a45447c8034440d002c010b026039101480303015000c05007884640520b04490b85041c4036009020400f103000a000d0b540019071103002e01c42481c2c0c4a0340011030310fa41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361919253 1250 361918003 361918019
    0x120f0b01120504020f1e03101b0207080606060702011209050109060b0906100305090a050114090607170402040f020403321504290c0a120203070e1219050601 69
    0x41101680300d001c0340b412040c0001070f500c1c0110311032200010713a280d40158500c2c0e00058081684011107540500401d144880b92500300e41c0140300e482c9042c900c04007c00314200007203980310010b020300030b000c1e4024000b0070b0304d51a0070360140805620525090081140717120301c6000f9680680c9003180c0c61307034403074000e241004928003902c44580b00c140c0f440b00d06403800c0c2c1d0004100c4014250300005142d910f00200d06041024850141e1441e0040c000344090108208208140c403812030b1402458050071001c03840152103031070449060390900941480c1c5031220f808000081207040401c01c1304690070080080001c4141241030030303500c1320407c0b02590490000301c41595018011056030583c00c6101e010540580800b9403036002a00109614103920f47d2160308221030940c55035a04008a00341b007004400b054410003000d01301c400303030b603806003c46410850b02d05900080d00c599020a42148019009040600707580b036000d0082c5048450900070410440030a6030180030945568018100600c0205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361920503 1250 361919253 361919267
    0x150d021e0a050f0105032701020408100f0905070b0307020a20031c020a0305090d060603080a090609181509020a03140906010609030f080405040510091d060106050901120f0b01 77
    0x1500f99500d600c0400d11100013001d80c440103054810741d64251340c4802d02c280841600c2d907884942c9038021580c454941d01c04996550340c5007402d503055814400c17580b904011324000c183c2d0065001c0c0040c01e106080c61400d41032034000510610440c1300f05c900c0d02c80072a4000d01001102444950b14401e0b54010f0400c0c18140032000304c0c042c00e03030200a900b01c040e29900060b0080016058a82151103582c4000003400000ca01c07100508018140040401800904070042680c26450b40790048196502c02c003c5c0d0741d43d1481d20031045000e1a6014000c0b0070410754110780740840181d1808403590f174848000c0c400300d03000000210000780d5079185003002a0144d1000039002120708009049543c94044024141c03590741c04004c0c1616500703d104002c11021906490281000400070701440c45c00505600e580185445905401810141c2c1c451220f03000070303200303010402200d01804250b0f0a040041c0c030541e1002c0c0c8914100320341e1141d0028036030f54a01c40c03401c444240c641c0100d1940d40c0c50000400c28 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361921753 1250 361920503 361920509
    0x1e0303190f080408091306050d0c1701090f020f1903150609020c0703061d1b091513020a090810061a0315101b050105070224150d021e0a 60
    0xb01c001c0805100228900506844119908071030b94040300342418090385c05080e0550000da04801300700e02c0a020004450184010340f080301b0340310b444442c1640701b503900343e0380314540141c030303491141116501508000e040c10b041d8903000703082040200540e012800c00040958003c0d248410542064040d0004902511004080710b110075030030310300c440c1103040c3c4852281c8402000d030303940d480052410029441c0c00f03840150b8018150f031141c1c03000c840100c95203a40c0c40101886500701000040c2042506c0c03c41c81d0702514060804035007580700844000003544107031801c40601c0503010001680030010803203015400c44000010480500c0c0c84810014007a1240140703206280c140200301c1490904000706002d9502107441a240005d1910207942c00b40815940b8048410002000028840150045405442107a00302d400c0c86d0f0045000100360681da1244090480c05440031559907440ca5443c03210a880041108001060a6002500180e030410500164030444040802c1a25008540b4401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361923003 1250 361921753 361921757
    0x109050115030c15030905070b190503040308060904060f0603061b030902060f0f31090506060d1d010c080a060605070b2205160e0a0b0a051e0303190f 66
    0xc0c1c6055503611001d4401c1d038010310290419034078803140c0c4c5510a410000b0560342010550301ca00d0340756000341402c1d034000500a440c02d20070501d02c120284c841c000312841150941c1e0340700442e4682e5800c02080b40c0d4090000ea40c829103d08400c00d00e000103103c0c0030000c40c0300350310000e01e2036a88c03080c91a201945008d00b0091524084c610005a1200070464035584a50035100755606a1b81c030b03004025000302141106a0040640030210010301340e40065180d0303421400102641d6640d00140055484c03c46030280c01400a00c0f154148407080d07007003000410208100054447c811040450071140444401000a44503000340135030b500052144501800c1c2500c1c2162070072245444620702c0f882c01501030724081d0900c518014004001240c0708034050350001c162120b0700c6404c541a062103240d030061045810380070f40440e050048900c103420052034081d0085070110b2921040bc58015000c40e0000c5511808078003002060b90b050008200311944071b610203901e483e00d031034018a00104035031540c5c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361924253 1250 361923003 361923041
    0x36051303030b0d0c0b0f19051b061911070206121e010806130317040c08010b0303090d020402090a0b07050706140c15270d0f1701031b120501090501 65
    0x301003910244800245d0b40e4000d01e89a4030030905686d00810304c101c803c422020400000100307540d552104c0140044500d0045641d115032001f00c2c072540f02d00082d29800603480301000c4ca4810045503401c07420700b1981d13448404d030030025650045880c5510180a1603040054901001120701c1181404549240f00454020180d810a40055943c20020301104040a48039400d076040501ca2504100da4015220489017241002c4c503008004165a004851440d401e10900c007405080000c10354814801c01880c0d4440b044690f000c0c00001d5001890303030b81c0c01030040302021130303004c0950780180b220306c1c440e000600100d40303800300051103403c09403510160640104004a19420000342102c4500002c2c0700f01e540f103440e804800341043d1041c40d0800495841d5021f84460800f0218030800d0b001003a80301d141105a100c5011220701c200140a012031a00c06001070001c500030805207482400e100c614034000a0b00d803024034248003c403035411100c513910741c60b0711b03001c01c2803e0080200120b00e03804900707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361925503 1250 361924253 361924279
    0x1b1b170625020a11061c050a06350304080d02070801050618060906120a0501090b0c040b0f030a23040c0501030e0a0803040512030708090c0a36051303030b 68
    0xa40300d40f80307030034094030741c203007003030584526913146001c8800e5649807611002144800d4180c0a01400c011500d40350740b5403500e070002581c02800328032882000450814101220201d81f03005105030810480d1904a02c030910001c2840d1804101518403200b1580050062925005945080d650002d04c1e0318019201581e014204035902010103030403810490340c6042545d54000850140c106a10b04501903204000e045414030038194008400a8010000192250303036040212035170b8490391007600784540080000d0b139054001a8055500103400b0340380400d045010824401403402500c0c0381e20340014800c4103200403c03400c0301819005280038241485160021803181c0d40f92000d13070002a01d400c1000000070704000d000e2040108410000141c0d83d01c0703040c104001000c01004071001c1e1058410484a4103061600428000c11034101c41c00100318858507003d903a8040c460312190041c04032600d16110381442007802403521401c24041e402c50004444d090050030345603808a02409441000004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361926753 1250 361925503 361925507
    0x20106051302070302160f031b0e0f15090403030212070201050424110c010203041703060d17090907020d030c030209090a050403050c031204030f1b1b170625 69
    0x1201c0c1500010700043c0c859110f030a0690500d130307071942d5440d01c1804d05c2c240840c0f00040303400d4078402c3e6030041d0454a0389240413220442c2d810340034018901d055038602d00044400d5044114039500580b40c1c10501c03007440c40500400c411100c01c0d501200400d40103e00204c89401c80000103620050500c001e000c0c5080c60f40301c00b000302008041d94411407000d4107640035022410342150003240c1c4008070302a40c0301c1d40c6010783d034002e40090b00e01f1101d1032000349885070032007016000d581c003c0e24014000b6a00c0611039587c5003501e44901e0a0000164003806010350503a111250944210b055402810301d65903400c00c02421a03400d00786102c20f145c4140080c103100d484465200d0f030300201c2d0170030010b0a17445600b0281c880d40944094142c1503c00055820f03151108055514001c0d4480d444a000c4c048a89400740e500801000c42540ba01c4008500f2601066550b503000d074030300d45085a5003a009071261907000446064600841c00d560184003404074991610b0f0505081600e403807243c91000b60001c40c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361928003 1250 361926753 361926769
    0x270e01051006030f0b0a03060b010e19270f050609060d080d0209060f21060103050f340c0b071701090203060301180f0201030605060a12020c030d0e160602010605 71
    0x2500e080650342c4c0b5108a02240540c80f0100200300142034411203a580e1510074090041c60280900142c1114140507032400c08409260700000c00c01007901e4110308104070300d59401e510282100d9040040c20504c504039070300d4864180407800e03081000c56140381000520140950280c00e59008100d03008030540807407800c0c81074a840505d1703420056a200300e0807000030710f03c0c00340e5a0300c1e40b036043c400a0001c0103c980200b005d0f032004c0300c4020034820381e52403000541c221a01203580c0060401d40e14006491000c410b0209805003c0003030312501c0140d02c0c0d2410700c0c035950112183d80041030031a030112007845590480c0d10f44c0f28030030b481c006012598601c0540382148040c412a0240c64004c8042012a4cc1c01e411022903e00368101010314002e032803c105d040400c44541c2a070200f03103040000719142c00e00e00f007100c61501d0f482c0c80e03908461b14485201d1009501000402c0c140c2e00050001c00c40e805d149010317800780800d642d4014154000c65115000c20001242e010800750382c5043c800304030315150040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361929253 1250 361928003 361928009
    0x30106080f0c280f031e0c0b07050109170a090509060a06081503030f0d0c0908030301121412091f2f0d110f16050f0a270e010510 57
    0x1602c10344185014036003801d4540c900208102e982600031004c15105800300b60380003142d015043e0b01045113654424003084021441003c2c02c0041880c50902000002c240140740c218440c5000264001c070584030ba110000742051441040c0e0000181c03040321a51150030382c409000200c90400e654200040062000e60f0544124028885107200150040b66124522640d00c6d001078180e0f551003160740164a101d92080341025070451408072500750542c80f40b0250000c0e1000c9400031807459003018044914218032aa0494100050444004900d60309105602041207c03401d1240c94094034030401a5407440b0408818407005485c1c1c80f085d07071503842040703801486848101c145607140c070251040c04004000b070740ca0ba02c030310030f4003841341100f90b0000300d840d52031003d64103075214422138100d800c0d260032286030740410310320440c40140854900180c1d0141d01800003003910707802c0744c1d4641c0c50b003440080300d61503a6202003030510880c80003805800381d5281c1c003103a24002c20407403505007610010300c54180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361930503 1250 361929253 361929259
    0xe101418030a050307060b01091706010303080c0d0603050a1211030301030204020a2d020709090b010b031503060108060601090f0302061c0204170606131104060f18030f02030106080f0c 81
    0x40a440803584092121508254119080c1d9545c3c00c014144500500440f034034050008103407260020300c00103481a0581110303141c4002e04407503445c0d03403000c640c02c407005400382140402c1009118504c2105202e0038000303500c5940a40f004100ca0306002a0404040a8100a116503018510b0340e041000c0708507415203904650050f140c220021003150520b40c1610801c3d1243d4a421786820303a44d10640740300c0c42100c442e40c2124801c68680d40350400781c078124800203140c21044401840500807508c003569000c841d6107510116a405140020301d02082a4000644e581081c0d083c0b01701941d0040e5220302a04082552200d89490340d800f2603090720a418110348013410049000741814015011030b00113201480c5001008800720581544130101a03c00510582503900d80341d100b4400da014048968071321102c1385003000d103007442c2980c181642c51071007401c01c150b41c103003551100b6040c2d8032900a1402002040000b525510516084a100d90421005503000c42c1041e0740e410000501d4480c030490617 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361931753 1250 361930503 361930537
    0xa03020a090506030c0706060801020c030702150d05010b1206030a02090106031e02040b121003020a0b03090f011103090d21020906071a0603150f06010c110a060e1014 73
    0x100d1040324a1070441c1c01555022400100b8000d002c0c00f20009440c07120b004e0f4000308a03459440607058202d105200035690700c1d800c2440391601500d0314410880601d11942d81207807504210540c800c08550098011610200c0e001c1282070b0752034100b01c0780a900c000c058000342910342007600091161901441a0710405844001c20307071004140d000645044038010000b5910303551554489003550304284a03203029143c1887c00114550456441da108594028100c00840790501010110030b6100800b11a001d204103040115001424070620086030800b0038032649a080150100e4240000c9d810715400b0002c2c10f8105005850b15502210100918940010f9444401c000401c0c0280030350b1703c001d080c034180780c0c0d00b00d5404811030041911030841141555005450103d40300e50805041d41d0034125520008000340480d40501001014a4000d03074002d55114601e00006411100c00e0b0068030000e07000301481c00441c1440e510000f4206500e0a01013000c00000450009900516006608044403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361933003 1250 361931753 361931767
    0x24140c030904060f06030c090509070305070c0b010e060f0613060509030703050303090102070b060604030807061d011503032c0d02010e062106092503111b0d050a050a0302 75
    0x410000c481e00800080d20510915907074103442180032040b0310440c00424140020100c0726071044404c9401e03164020646d80c0241c54004007180103050081915090101101203100450f4003164541c0c000e0010a0f0040c0003850208c003442604c5900c0c4c0403140c001c00c02448404401c1c5008a44017041d42e030030349007407502c4147c01800289403da4070b07403025215004c0002400340812040d0003c05200780900342d40e0003070381c64510900400d44100d2102421300d0307409120180006595801c681c29645804e444c6c0d00a071000c151a0724211143c024010f541c8601d01c1d07004100b003540016450040c01030a0016001042c116a20b00c12035180c1080d18034030034030380c0c288842e045a005901080010741c02800d46612102c00e070a01c800f010300031401c10880e40384400009a403516095400034421040780e05c5c00080e22100a4102c4000c048004c0080e0a00d07440700038014641441802828140400070104441c408040c0342c0d441c1084400c000c02000c1080400c8500e0009130800c0896410390f400c2c0c540140e45103a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361934253 1250 361933003 361933027
    0x603030735040f05010509010c171b0a020910080c010c06060306020f030a180305070b060d080a030b01090e04110d05010e01051e0601090311041a0402070303062414 72
    0x8041115048900786450500100000780301400c255240c150020001549420065030240640d00300e050006005a90700800505840000e08040304008082801d0044509002001811801c05039078a42c2c4060410800d6180104d40b09820081c100c64103900395007010301c0e0702c0d01c80480310007040c140071201101104115a031b9100c0c00055420000c00c644814803900303603d006034001c0d140e03022034078144000e0344600801501583c29a80d81070f141c0500d012107641c2c4094241c0e1000300340c40d500481035181240400e10010040090040d1550005202c0070824000340c500d50700c0d80c1040303040c840300100b0400004c3d50301d0458211180112003c3e000302d03459280c528054150364142440c3c0754206402c1c0400551f491031a611500d12840841150b0780e503440c01161003440c1c40c070015144180401880c0c20780c3c04c017030b844641000c8400c85078030b0b49900c41c0e00116003030340d001600c1100000c1c0e030f41c00208401c62040503480780c0e04402c5c010300210a81c0d41da90003010010304540fa044030301000600707549000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361935503 1250 361934253 361934303
    0x40615050c16090b011e1d0607061505120a0203070b030423031218060115030b0a1404060807060c1509050d0215070207030804031407030f150b040506030307 69
    0x45040101e41d003464443c040c1802503c0c0e50042c20f40490a460a0410130f03549108060a204807503039140c82c1d4074044d400c492080d01045590054112008119000108215024000c103030945580c903020401e10745070602045a03809078003e0328603003107500c1c11f00040e90042071030b01c00c4441a81e02c003074407520b0f903040c020443c001000311a15103100314800c51511241c08000b520b0325100c0341c0c52520f4a0754624080c1540d11541500d178407465040007005008001c182490001400d065240001c1c1c3d645154007c2a000300c0e0fa60410040240e08419000017880c02c0c0c0100c002810110002d8401d40b0700d088405041400405801070666008460400f8440e6035540300d9004c0607000000c81d45448045e04001e9114031b0103000c602da5030001140001c00403130001900c501140d511840c41e42c0340502d50780b599148407244003103031300c03090140420020114842e803c03000308a9000f24149070a082d0b0007403800b01268030121130580030703609050401c5056540401540c00154101c00c00307082d80320100030810300710 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361936753 1250 361935503 361935523
    0x20408060702010603050c010306061e021216060b010c03020a15090b04080a090602070501230415020304081501030b0415110f040602010b06030402030319020a050a06020a0e040615050c 81
    0x1803003600104016907605420140403a07010350280c4841802190044064564034024039021540820800c481480780d03405e10944e603600303441640c80400c580c0c1c05000c203031303401221440c0d650000f03501c10406009191040c0e580c00300302422301d040f419504d40d1300a91a6840400301410f003410050f042110103d50ba04640302407540030511403024500b030728ac44110ba0700004180400217410010100d0f109000081c0403041d5241611421082e4000c02c81c482c00b00740c2c40d6201c60703103244801e01c000100c0c640c41c15444400060141c02442d22070b400c04140e42e01e8a44001c082543d04003102004101281080320ba583e0490340000e80041c0401c4c41000312005002011041c0d0190040002c070b00018443d5040501b040c0c51059000344190160002044000d01003510003075410f8000300014100a420b084030000d2038a041d0054940d1842c031500e9050a281f4004002e45000f80c000548010082d404400b01070718040c200c40422000c4d05029156480800801440007071090000d158002084100306003084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361938003 1250 361936753 361936769
    0x4021323030604061e0b060d0b2403010e07022e24080d020604080f0c0a0f0614070f090509070215090705040c14070f150c030e0c0109080304050d060204 67
    0xc604203403404ea00202030b102e18039564040a110317120302d0b811503130094060210004141c142014003021a4500a00c000c52110303031311801d08803000900d08160030094a01a260240194896250054900300a040104803c0464100504002c155590700c215050044941d42c41c40040c058940310500042c081e110001c0c04c0c5da2902c0e182c800c068000500d070041038039034203400c0d6070b04440428026690f44038203031002000200b0601545603400d41c80c10242000002180c200c9410758410303100c616026101020588d01c03103882d0300300c075564441840303911500904c0510f403442600c015504014004030a601030b0910171100c12020850141c0b0812000d071142d2034903130303280c0e03078608000f018a65906041d10070203000314105020070364900e00810b1072054480c1e800702601d2821940e5603032040b0341d120590f81180c1a8044100540d03054280e880f40104080c550746000440341d00440455140150340101c19040211040050100c0040401030b0f13002c4810075141180800714030325100000e07015603044400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361939253 1250 361938003 361938013
    0xc0f0a05060f04030c053c03030a180c080d0e010c05060a1a0a0605090901090b13090203030f030c070c150c060509011b090303030612020904030807030b1f0e0402132303 74
    0x6409004581581f081800264403842c3d0250740a5080415507501000851640c0044c000980ca0303150b2508202410701800161040409003540c03480d4142c0210740040c0a41c0d4007415540c0c00e540c1d00008070ba044c0407001d0074151948140c50340c400340c0e212002047c25080544803040c0c1c0d4076201c880003e5100215006100c440341680b64036008109412200d650b40c8a0461b0b2800001d011600340300745105042c0c080c24400802e03000741da4100241031220000c07a00351104000e90700510a1300c1004e0742c0a140c04100350755807500c007402c22050025440e0046158203a84003400301080d50040002c040d40d5070b1096001c1840d54414482d41e0043c081200c102a005442e038020010040e4010340d03803c2540c0c801d8130100891620760014011070000710900075084030351040800e000ca8004d80c01c0c103030b2000c1c1c00e1402041e04084000171890a0482c031195044924941c10b802d10b482c1d400201998400e1029181141011340c00e2024100c40000c5104290380400214130b90000146100c5960306454405000c0768 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361940503 1250 361939253 361939273
    0xf020c0915030601091512031707050316090501021903020703020a0312020d080415050405011e1b020f0316080f0406080114030a0203070303031505150c0f0a05060f04030c05 76
    0x400c101c103000c01807290080c0c0d00003149038141e600c50484201c8144240c40150b504100d10741c604d60180c1c0c1800d030184840030422414039a900700189209204590b034480e242e0400800340082064008120070a00c090500d0034081030368001215040340000b605085051821801c090b030038a6100c0e08003941000b25400040b09010410400c070b080b604003039080704d03072980f1000009c4401c842e050710010060004400400380c0c0842a800807500140103d00000365510000c03a9582804064411050b241e03890f9450180e0008842481c03012041c11030020303140d40d911000800b500c2e0300c21401c95426125030004da41040c091010252006615244280c1e540d941c0c842201900c003640910580300c6100b80b00c400d00c1914140445c10445544d4090000c2102c00d003980d50980240000010040f81d54034402c05c0000d2650b1021040c08603500f4103c01666198500011a030401d840e400c0414202e078403c200c190f000500000d001c0b5031141c80c104031074100351610328044410003c402000791040c40340280700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361941753 1250 361940503 361940521
    0xb130203070917060606033301030c0f0e0603091c0e0a171c020f010207060b030d0903080403080d020f0307080f011712070c030803040b010603060801020f0405010f020c09 75
    0xe41c001d609944908414565601200240d0046040d03400364070340040c030206060b4105580503541140e034042e03861030b00403a41c5016004401c007118651146004483c00880296054424842d020800346841e9080420048024041e81d01070200f03203008a10005c00940d0545003409000d808030461756002c21100f80d181c0008246c42a610030540c46400c0d4079400041e502100044040e134404004085c0440d42007a000c60600d0303a801c800304009501803050842840c040c20f1000b80041e40c4180c0340011442030304414580350510004408040c04187d00e001e0001c10300b02c02c161011a94403501c4140e40e0a9035840300b0019000d418504074000c100401800460342d0094901481a141c95580d502280c0c0d941d8400c9050704d8400440c00c1c0c4680211032081c5002c22544002c1c10010700541814074115038030399403099160300482d025900c0020b6000180543d80c0d00d0700070500102040e500960614030140c80751505841584070740d0703040c011b440904000b014020310852009140080654104e0310b024404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361943003 1250 361941753 361941757
    0x19060609050c04171b040527010218090709030b070203161109090606090714090901060e0102071707360501090b1915141306030b0306060904020103050a0b1302 70
    0x25818080207144c0500742480d800240b005e01c0c0111408021070006210b405020041502400e51a082c41c2441d00918102d520f000d074003250160071200042e580c08405110303020f01100340b9800380c8644601d0040c40169a40501c04100340c0b47c100901c4005a1200e04041c2e2451060311041010034035000141001d2040f2012001140d22096580c0c1141d555a0640d55841c0c0d20200c0e00e440c0d10040c010086165284280500450540e01090300c1c0d00c0d104416000841c072903000d0b071103800000d640c0050840381ccd5905005480050066203811b030b81080342c040300d035601c0f10b1043c061291041480c0c4024414121000b034010051555108a8002201b680a105000d0300090059030b00a03420003d01480b103080c4050340780020000c640c0008055400d00c26600d1141024400440400c4a04040760031003580b114000c18615024820481d00c0629054020b000d9511007520030f4802d03005202084126100d0b01440c550090b42441e0000c0e1030766071280030300000c00c480e40030f0780c0c6c0281200c0c0501c8000d8000c4e0340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361944253 1250 361943003 361943009
    0x50c0417150f0f011509030f081e13140604052e090305070b0a020309060415080a0606050306130609091104060b030601020d18090e031e090319060609050c04 69
    0x403016a82d01c0e580a000341c009a0300c11600006031001002044c02d01e40d00d805001000e4074000d50016036a0302c6425018060740c0003500e0480340050b41e8280310129100c0301c00020000b54409045c58840c41c2000e00c04110380c4105800810102c1a4141959465007210f026100c000c02c0c8950801328040a035204002d4041095000e0700700040c00015940102c070201d08030303503000d00141580740c28640405c6250b080403110805500c418080001f46688120182000c3d2141d01c1e4074040030410464010b2580f00b01034103180445150441c00c2c80300640c4242180d6000b00291403200021600d131980e4001414164040030110b85010604030410a0989103001d0041080310f080c044107032a2080310000380701c25101380340941d0040c0c1410582c0d41c01450401c2808030860030441e0944d58a01500090324071034079400c0c3d01070300700107602c3d02454021060341442005181142d400c0c800080c010a554180210300514001d940e62200020040d40360081c03000703042451020b1050b81000000d800180c0c220f40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361945503 1250 361944253 361944283
    0x30c080901020f2b020f072d140a051b030115120f06020702090f04030f090509060114070c080a030f02011406090603010902040c0513120b060103050c0417 68
    0xa0045014540c0500a03990180c084200241c64003031070b0510141c1101c9031000030b81c1150090081a060308a403032003d032501c1d1400f03e0401e90380c1e11442c5451591035030b08024468001c0f42103c21040d0801d1000c0c808400d03076500072480000c220312001e40713519040c00414020210311840c02e20040b84044841e0044030980700350028040d1500d80580507110905078002c0f143c074101d0720a00341c0b000c1222810000110f50040c2d00040c5800419000700752075444c101c60713040350b0075416024081010750002c05085680b10500d0079505040c28800000c880c00d00240440e0304114045489420321a880000c5a264550150040e085141d42e44c0000303480d450152001d50100c0c0202064100d068018010088100b002c00ca00d18201d0780e500b010880101c0026043c81e4066507a04d800a0050325503115020f40940c8580360143c0f1469001241040c0c0038158002d418410000310724a000a010348082030342010090801003040d07a50100c2103211406540c0c0304100c40000b5928002000001040064620240d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361946753 1250 361945503 361945517
    0x10e010c030e0f340312030c0801050103200903010f06030507080c120325080a0c02120c01090e090a0b01030c091401080319180e0f0105090402130509010b0a06030c 72
    0x481d559200d942001c0444403541c1c045070300030804c03001c142d41000607203081200c10140c0754a03900c0d1604400c403844426404030381d6030718402031101c0e0460b089600400091030180300701818a10003c2c032a4003440d032180041c6c00003007030b5a850766a00790070100c2a00b60145040020720341d00c0c2413156403070f0542e2242854a000b224001c014901f0910003940c140c607500700042d880d20035130f8800b0f010070444400000d907501402e21200f000058141001f4480b00d9240d43d40c1c401e55070038a00403c0001c2445003542c0d1120b070300a408a007a5070740c00c40650000c5545845030034520783d40c0c1d080010304019070054000c01c1003456400200c10804003112030016540109010822104c04405046a0140078020030070360364001c6c4a902c0c600e0042c60324814042c140c91400d0400908519011100f50f852500b12803070780c03e49401081160410704103528010310003291500c80c9800d054021030000c03004d034840400603a44400002d80400003d400090032003501800440a041e62280c001700244a88090b0500250b0340c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361948003 1250 361946753 361946773
    0x20d020c07150302070203150919060b01020f01020c0d081305030a110c062502011403090706120506090601120b0d12030e12090111010b0303040b07120302040f050f03010e010c030e 79
    0x807034405e0300c580b1a400b0340103007040c50700e401d22000c007158001c140211354400c0200410789402d0070200300000350b01c10440400c400301464006810040340c507841e0b01c410b0707106114402003c0380005503081540e800e42010b8070152541c09031107071003224894018025100c006a103e418550013640002c400c0d0441082d00c00160700b000c200b2101348aa81c01012007800785100c03001d20040340701c40b03c0c00f101b80305040080c0348a108070b0082e07541d600119030400e0b07190088d0380100107442d040200c3c688030004107d0104941d10b414400a4090000645070b181000b09218ad5820350f02c20341c1c4d000074081e00d00280f22105020451034074502d400310003200d0f00c002908101103900c0d500d5002500c5401080400303482c0d0705103100c2c1c000441d66142000c90f01100c2e0342d2a00314241007030720280001c101410000300c0031540c0d2080e0341020071802c1101100c407410140304002c200601046241c1801c182c0304101d8242c01070030144000030740581040d40d40c0306865403030110b11b0400c50340c00d40e0044005c8800241920f40c0f00d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361949253 1250 361948003 361948007
    0x3201c03060f030b1e0603070b030c0c0109030206060312031905061212030103140f0705040c0c02040603050f1516051810030902031603021302090d0b0f040c0f030206180103020d020c0715 82
    0x5c4203695568059110f000140103454010000d154004c0745086aa402c0c81c1041c44102d0954a4000d01640035811010510100c0d0605120b90950182c5000700c03546141002c1403a4a4080000c401c0d00184c95a0f8001044040d44c5007200380d8406440802150544a4448140780e500d500030310003120b105804a80c0500f10350800700c1c0c000a0941e050018080503482c010034040036240b44a24501004001210329006036107a11518000d036000300001c0041e1461605120319291403407400c40319020007a000c010419080b020307038419000003480c1094640751008024041140d14000166000d1020045031440340d5041e03022071549802241291201d8101c03101c00c0040b0f603400d01000e90440c0088060790000c2c1c0e080d0f00100756405c0081c103c00100c4c2e0301078444400e0303450180c859a051400d080c1c10f000900413520040340c0034000d0100031401113861980000e030103100d284c41c4c6000c400c0410509090b00c2e8041e60554004448420301076548440d4031280f151540c040d4050502640035960403050024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361950503 1250 361949253 361949311
    0x907030603150b130e100e012703170a0504170f0703080c090351070905060408010603030809060402010e0607050c060703030903201c03060f030b 64
    0xc1d081504902d0058045142c030703024211000748260089803000c07401c1d0030300a503845050034010a0310f000d0032070008445120303025542e007a11184266030411418061194180450354078800039071030f802540186624007903c0408110003506c1074602002d081081e14280ba80003a8070907031040900c95030304000801c9280040c01100800e8408103400e12a140009000744007e90300b0203611000c083c24440b130300000a00e44a03e00e1601c01c00c01c48001c41c90401c0c280060980c4008003a400c840340564440c11100c80f20344941400003100031144100070800040c090039a6501510b00582050354070751721819498040e1055201c01c50004444100040000f14049407980c007441e81651941e1340d2000040c100005508664000d48043c0620b83d0040c2d266a00d0500400d5104d1094502040303152003410b02404a100040118848004840041d01d014201140c1c0c1e405500205103441100240a203045000302180d030802182268014070103c284400305c01503600c1600e11f448090018506074901c0c1c5201c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361951753 1250 361950503 361950509
    0x3180c050916230405040c05090a120816060209030f03041d15010c0c0b030109050f16080402061602030304030803011a19080c1612080108010c08150312041409070306 73
    0x1d004410310700c15400d003c0400314624a80381101800c254650700003e049900c80006400400c03c00124680d050810589840040c0048980c62208108584a0f50541e1290f4508000c119114006030b408011560781a1443c804015048941d5428040c4806e662540301d4042c100000e6100b00514118100d860106d42c811401070181d503d60056603401551251603000f0111008405010301159802c68540a103008040902d03005c2102e080c0007004d80d410ba240038040001e0700d000c0942200103150400403030b503002a81600c8003035640358151a020b811210a04000754580000940003040c841980c1c00365040c0d920b1038002d0500c0900300d54402400c0d00c00c0034050718a500c0b080001a1946018050243e845904003240350301c0c02203680c00860903540940e2003103030800000d164120308139038483c2409001d81a200d000700004030109601401a030b0000300400c03980c0c2e6040e080d00380152024041000110070800502c0e88030394940228923001c0440170202c4d4080d410b02000139005900c640078010031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361953003 1250 361951753 361951757
    0x204051005011407080408030a030c0f1e0c050c03070e06030106150804080d06170a0c060302040b0405040203060d0b040f050c0f0d0b06040b130f2307050a03180c050916 74
    0xb010b16001e143da181c0b600440c40564a9401c14040080e054100340024140c1d4941a54001040c01420304060000406403540104101c0303120496442c0240c0c00c0c40440c0421034505200e140c400e0f40d4500940303840c5260885a4040c05174110015626100420650080c3c10480003485100d0300c0312079243c024403140003080c0015030f130b2201103030100344508020040e0b1648814080303940b07601c4203241f00ca003501d40c440070880d503844088c02c17500b8440d00342281c00181000d40780a40c40d00381340041c140c2441c0100c2c01094856540000070038640d5413402620200f26901a0400209140c1424040174007807135280160b0b0f0340e00401c00d60090300d140461400080100c000c01a2000800359202d46200120041c24107410a6442d11003258a0b6102e10021445c1d03001380101040380d182c507a00c020252426280c682d86a148000c0d120307980c0c20f1011451540c403014502d081034903110591b030110701a0a8802d8000031403002104244c082c00100d400e49030a03608180c500c1c41180d110122440036000c50141c0401c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361954253 1250 361953003 361953017
    0x10e0c0f09040209161b1514100513090203100e0f030c0d032310090b010c11060307020a080c0a0b010506030f040b0c090303030f09120f0406050307031107030c020405100501 76
    0x202c0c640c00c04000c4512a22246046a5000c80c0503000d50015080f25a087e40d41080f50803000d04c00f1407136405204c1d50644a1080d900c020b00300390000782040c13003c60090511032101d0881d1240013800315440400404e4000b001c840d100402040648010402f0030300d05040c2d4011303c0003c812007080001103413450070751040106a50310002c0f0048008214941c201003510303030340d60f038065562034101c900180035480c00c01c40030702120b142840d91401c81d18214200c0e81440002100000450608184002c0350031064030f4195581e0307a00d500c100d00700003206038020580f40d030100f080700b001c510000d01d407000d544c412402c200b11662941c0403c146800708542030041c030501000000d00096044444640000b81c04514030304180b0041c00181c2103401c1214900a4582c10108008440c0c80401002000b0b242030380c41503241640031410880c440c170440c05490180300c400070101d00e61600c2a84028500701500604139217070989490010500104d08000764851400c1102080d0500300c002c0e10b8000300e82c0305841d014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361955503 1250 361954253 361954261
    0xf06050a0503120315120102031f12081917012702040b1c0e01020c0102030603010c0e0303030705180a140a0605210402121603030f05040b0426010e0c0f09040209 71
    0x8090f9507460391517a401c8440c00102000c00b6009002441c05450894124100202600f6240300342d51402d6001c1010000314130b000c600441c001034211042040b01e6005115620300c002001d44519a4031301a04820403085070002800f42d4045110404200c4000014041ca0f04051400d400b640038500441034a104101301820181c001000a00030000460742e0100e240b0254628090072600803500c0072446035000810451540780a1140080b016098180304101e160104080380d0f40b400700420040070301000041110200b140c6440300c5054020040c100181d045d01d825480c0c0345185c5040881e40146850310000c80c04034091820b036180d50494001c0301c024048402c240d02c520000140c002c0c0c0c0c1140540050020000060142c0c00c62070000343c4c02d10000607c0c0d8680103144140c801740700c1041150078070080c4080c080442c201d50840e80d28403800c582408052044036504c070500100668158038044103503000ca0310224070100a04021201c4195510f40f1905100220808070340083d800750f08030b4002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361956753 1250 361955503 361955521
    0x106080709060e0a05060a0507021212090621040309090c0915211802120d0903060b060c0a061e1a091008061510050c0703080c0a060f06050a05031203 66
    0x807a08a00000b85004c049175a03900114003150302c44100500000c60008004081d420840040d03280d404001006103c0c0030100e850400a6004204d2160b108160010700400c0c0c991403c103000324000c401041e0f840030b134203080c940540b800402d4424007005909006044101c2070040c02c0490031100c0060410145e00c03c015021919a0401e00164510400e080b80c409030045e082e102d03282c40140100d0803d90865020700421440d090280100045035108800d806005640300e010201143e0f4415004120b07910254000307941c0707000c0d01030660b039148070319400b200c00d0000719000002d001192005502c00d5000400c000803d40c1c20028000200403c070540c1039046040480d4000d40c0107601e08082c440c40c1d51944155810280d040d030302030000c48443e0408441514150001d8500000242081c85c03600290410458480d8180e100103070503400f020500c0b0240c2c900505c102c400071079000c0404c2003250103150084000745214003803103005809203100480c80d403c00081045000071507404150841e43c03600c0032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361958003 1250 361956753 361956767
    0xb0a03180210080718081006080a080724050f18070e162006090c040216021002030904022109010203190b0d0210020a021801050105070609020d0203060403020a030305010608070906 79
    0x11039810004008045000d1005000504011b0000b0101405210704013825031015100d13660000c5810b0b40001d100e01000a9544040320a03407948000103280020341e444403503905852908099680314108800c0100c00d05200403601d10800700364105651000c00108116640c01140c00b0b502000b000718004283c00209207081998410520b140445045400c45040350030300303000380c2d440007150f03102005101c003401c03090181c000e15403000d54046085c480c24402601c0c107100040b40c0a030007540c1075030016803c18402d100301e64408001610540d81d60004090f031100c4001040302e0a903003000c4100c00700359140c0c4103008a034040c0d250038040054000345014154000c1030b150590781c2d8050440840040141c45065400c00502c04c5034003e00070304040b9006002191f811420b0500b001508140140926070f0000305490030300d03421010000b0419101d10100e4040c80454001a50610130402080101980051000c64040c4a0b03075040c0041c1e6a20300c010380c0c5c80d1600303640300e802140f0300410038042c161003862 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361959253 1250 361958003 361958011
    0xc0309120b092a041802060f0309060108030906070605190e0d09090902060a180e070e04230a020f07050304171006050a0e0603010f06081e03030408040911130b0a0318021008 76
    0x5170458081584d070300180a65101e1403011000039008002c003c0c00c178030306102c02c038018401c40c80a503145c049900c0000703689200b02c0718014142540ca202182036a072088060703840c10f4a100c40704000889140250315590801005510001880003c001c200c1c0c80d1540187c401c42940503203901d04081d41200706841e0302d0b501540f0170008072041200020740d0400d00030018013403075064981100e02c40150342407106940c0d022910806026010340b5680c101c900d40f40066511900928005071110000c0760f041d1000e02c0b683c040038140d807002140203d0040c80d100f0f41c0400305040507080383c40015601c020703c42554080d01c01c0a6101c0c07071503002045403218040001d58030000040c0001440789001c3c01c2d036004c80e011380c2c210060703d51101c00003d00c0955208060000104040000c600f9440e00f07035140300c000d1146004081c5180d481d100c071103c00d1400013096811200e001c0d01e80346001078480c88140e02c0d0f50841645600060f09181d554400080c151700c803c0107080d0090001075510544046c00d0310003100241c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361960503 1250 361959253 361959281
    0x2422d04030f14030d05060916080c2d0406170103080403060b0402160b0714040317070602130303080403030f090b040b0c090a0f090e15070c0309120b092a04 69
    0x383c12007aa90000e00c0200f8034510404000a62400c144042c000e00b900028800c0b010b1418145043c82d00c80c2c0c116031103a5005144040d00703991031503c0c0d45211a840141c40340c51036050040344c9002d045180b013001074001d0315000c0d9100760603200034551444c84c01c1022310000d45480c004201c07c6c40403d1080c0c21100d1001009000949060006071205d0348542c200700c0c041d01c42c5c0e180c4005010405074080312100c03402000402060815007181c135980f481020300260800c6070540040d085041251a8055803000e01840a00021813542c0341400361203041e080310100e00091614140e00354040b0359220711a034054016040804a07501c6984035400300401234151000300c00d0174001110b160391403040744405000f0040b8115203852900340c030082a100c0c0c40188141a8004655145c400440541002d0b4084014506480c0c04074241c1820f40b684100d9030000700b4031010310306154040c003900c800018001d80343c2c0d20440e038844c0c2c13a05a1400d40503003545101080c40c13240003040045894a500040d11011100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361961753 1250 361960503 361960523
    0x12150121050408071a1014031e10020705030c0f1b090a06050301020d02071403041215090b010f031202010504050705010c02030102160516060c02422d04030f 69
    0x107520764060b17002000e540b013486041c5040030001c101945032640c6d00100380c00510005101402800262540300c47c214001c0460034090122041c18802c0020483c2c3c4444900119030399005402d02c2a20b071b60084e169100c440c410740ea5020310b880e0000444c042e0042c4441812100c018600081142c250720107024021072980f2948007290543c0c0c00e20003006001d504600060740c1d1406480c0c28180d200614500300d86680051100704100356000519481940d8080304144850400c8124900184800d11010702020350131000400d140a04d1441001640c0c002c94120881c0c08444404a0070307143c0c126030042c003a400c4140c0402041d40580306282107a40300070005030400e410340320403400b000034000050764142c0c04440030708840c00c0d0952016000e8402854403d2aa10b280d80205040c040c800b00e03803003144484440c51003824016188903200e030b5041000038000301c101440b0b1201482c3c01c00d00c0c05207902e951a0b04038005060309030700f444040c0802502c55034146455500c402c4500b4403c100103a60030310030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361963003 1250 361961753 361961767
    0x51602040e030a032a05031e0103030e130911040e0124050a1a0306091305010905160f06090306180b0103080d050c04030807022412150121050408 64
    0x618001c906904140c40000c0d901e8002050700141558080007009440050b4030b9034890001a030340070740b1030800f94907080c0301d41d4944820f00e503030510704010301e6010034481c1440008810954030480010005404a46000058404410510494108900050441c4040350b00c115150500c0d40200f601003004200000300580c8400c074a10030b00846203102703440707445c11030814842842d1000e0400d0140c20002c08074041603242c40141c0103030340301c0940814800c41400001a07038840e1a110300c9200668020000d0104a00915056135255400c001c002c4d80d00040b00c402042c1c0b80ca143c0741c1c260890314141c0d11b110b4254a9038840c0d000809031900b19240b10010740c0041c101081d6100d030140d00951040c90311540c5c070491031001804542000d4001e00d40000d04100c00c001141500302034581d50350701101c0d43c0940f2443c25100286170081401d8803c1040e502280c041c00e401c1d201c42c16603101e00c00d591407400030008941d0044500c0b00441400744001074100d10340d11b05500140c1d2102d503120f48644202c2d41341c01c00b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361964253 1250 361963003 361963009
    0x114150d0e031e04050306090111040b030402060405060705010b040b03061006082505070c1a042303011b020c0d030206010303050d0f050c0702040f0c080a09060b1e0306010e0115051602 81
    0x2043c0110b040304110300180400a9080c02c001d4141d1050520000300b1a503140d03020485594412840b58622030310340800804d0656131118104c500508000f03100982c1c5010b10303d0100d02038101284130a201da85090703554400741c180411740c0c511400c0c81200c03d0300c0080c20800c059030348980c058030007090380d481d003112002001504c210500181c140ca8940d55200c6141c0d2805407100016030b000140312200e00c5040f000108580c5060381d06aaa46e1060300c0c0804024a840c0342d4888500301c90154558240800a101090407c0d083d0600c0031140e825103103d01c042d1410b0101080025000800691200700104080b070710a1000d05105403001d007012441110000f170040c151041900c00700c184a4001035404210302d428402e90384c00c40364546050040c02c10340e05015003a190b009000300c41581e124140301c401c001d0103170311030242e410005000300e560009100748002181030f074200d40c40c081e10131880007250404042c50b070306048407200304010302100e03401c401c01c40702a0001406d07801c110704950540c40c01a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361965503 1250 361964253 361964287
    0x160b040506040212030f1204080706060315110403020f0111100c020c090a0b01020604170913020d060e0c030a021b0336010c1b0b0c060114150d0e03 65
    0xd0154000700010709083c0108402c00f60714400c424080da02c00c000281c112561030341543c61387c803215512114540c2c0c0b203007170455852040d440300030200303440d0a902004004001043c8426026060000c00c0030444200015245201c1e0b8000079601c000d03d0820010340b0340c07244030864400170000080e15924040038a064082d01d00300000e040144c1c200c0b0070f00590505001404691140035148203000c04d044a00001c0d4841c54080e202400284c0048a41545980203c048480b03071407001d080c004800c100c49070f000d002500100c0020403481d0500c01e00040c541c82038401c1314010460210614559259051134100a600190200055900c1c5144d00800e0500a001800003804e114a007994000203108245004230460954030001240018100c0384a90b442009844003c0d80900909131010316055081d90b49074503a400302405902c000351070044a600400c40a0494038003011002401c1150300801441c00500c0d071610850010600c81c5884d0300c12150040c1800c1c0b6181300c01d49203440c852540050b800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361966753 1250 361965503 361965511
    0x1c02041701020a02010b04180b04020a0f080102040503100207050607181520010e1e010f05101503050105011e0e0316140d05030703180902130e130203030f160b 70
    0x165400701d000d15440384c084c001c00c3c540740000c4808000c400d5807010311151204854034040d012070040341c0007404544030f440c080c2010306402841c0740302043c2d81340300e030305d020354058012180a401200600c0460207503078021366001d154404041c019664601c4004c41e240d2482000c0e00110f40768009000030901030101c69071100c0c0815640b000e84c184884907141292519100241c00640c0c54030212804d9000c020070070700001e0141c1d0040042070140039600b240074050b11200007036034602e000107020004030210304000c01c4444021000c1202017040c02c041d01181c10034410540400d204919080c0e0100030540408030700c0e20f40f402c000d2004030004005c0780c074000303201c480460300130040b032014001524151419025403504507068105840195251a10390040140c01000d201c1000c503030400d80d8841107244d0700507010f03240045480b42041d01d00488020b0f2284141c0b0303040e003120404960740c1d5102c58110702d00c042c1c0180007180703811180c00c0400465801600104010340822040c100003441e10f49a150003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361968003 1250 361966753 361966799
    0x90703051204062322060305060a0305120f07060c09030c06050913020714060109150e130f170a081603020705150a1e020705150f04031d270105030c061c0204 69
    0x1603041203401f03412604050000c510480300d1580c00c00005000155070710ba07000e4401e48c4142c5520405481362a14021031400400381801c0c807102c4032001d640010914200e90185002c2684180e880205446a2103200000e82d0000042c074913010b030050280e001450361a00c1042031915002c59103d000e401d100d400e03042401c2c0aa120f80003c80219070828120000d00f070034901145107410448520305d001440700c0070041410401010504c01d1103001c00000c1d041d5516000900d0b41d516110a000b4085502221a000d29040700702122030100d10078420f0320002e5038010014400301802003034162407044000c0951090359140c592003240304040014104050621201c09070b02c0355128540182040d88610503852402002d9040003607640110385003031780140d09420928143d00401d0079101e179000c40031180c180c1201d020b03081c480a481c541250200203414507811100242d888030205926421460fa10f00e07032042040c4010103e51503c0c1001c0c5c0e401805211006140c15030b50804401240710024040301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361969253 1250 361968003 361968067
    0x1080402131a030106090e1f0b030d020d03050711061f1a1305030c09130606030b070e120d0c030e0d02040e0303040c05090402060d0b011103030907030512040623 71
    0x900b0381800d010ba4030140c660301d901440030031803541580d956850300055200903d24111440c1ca48070800e0341c800c098404016059814011300800081c5d620f210b1030120000107440d080000300305501c180a00d1894402c2000900016140d55100030348d4410780c15042806079201640000d641e00c66500d811003031004000c1650b0700d52003004803d850001059208038003c0d04031140b81311241e070b1941e418542c0722100c9000c002c8000050b040c80001440b040e08002c00c1110840284055241c10030310a0400701070071600e002e0b222050f042e4140c1c80e01643c08400780451040180c900000b03000d00b0480500b040f0152032201c0c002a00d0700020141c030100b0400e0b5805400c008280000c5c4080141400040e04003611012020304003a40030640074410b40010b200000d0382c1c0d841c1140303142e01c149200b0040c20b140c842244d03224140f0144050300c0f0325240c80212054421303410050505580f000a46040740c042d52154449403022040244500c01103c01403412400b00b0044a007e424000d800e1303003400c00032038801d84 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361970503 1250 361969253 361969301
    0x40e0a05060a020306062d0403060e0d03060b0a03090317010306021207020f0d0311071a06010306060315090e10020c06070801081908160609080702040b010507050c0108040213 77
    0x1810500d01400009490f801042080b0950b00c0f00c83c1214007869030b4100d8040711103085182141e4200c026511030080389400100003092003030795000040c00c0c44529096a00d01ca180c01c405400b00d581c940316401010006004002103a4000d1380680380c1c040c0070741000c400d01202c0d49010008a4001d07003040300d18940c00b08030482d04502440e03556a20031010b0004003002645031450301e90f100d09a040c0300c4101901c07003007101c60704d01c1d07031070281c5400540c0401c40da01000ca0b401801007503440c0032124140002c0c07a018001030681d100740108071458000754124102d8900f8414624040d0054403503030405445029012070790309155100600034803504c0720243c6928204014000c015042c181d003c4d0100380d0101d094043e641d11040928510244d019600ea542e51460400480b4860a10ba101810b10ba00d0084a403041c081500c00a1030180d10846040121711400001510140074081d03014003580e1002d02c400c4840c3d4050f800f032a40050000f041d08107401c200c0544003050300c08454103100340c00e1103540d00c0c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361971753 1250 361970503 361970513
    0x1e05010501060c0f060915150303020628020a0509120c01031a090a051f09090204050f13030c02030309060d09020109050103020f1206040f0c0807110601120209060f040e0a 75
    0xd4050b1101d45411106a0315540358030b001a403201c0c1029200d6580c8980003820007c4041c1c0d010030348001c0c0182071019080101e00d81b0001d1031103110980c094015000060b12581d50211070040340e4140030700c00e04091130b03200c200c04025040180c410341400f00820211000da60740890400c0b1890041c0000e203401000c40d400182503c000b00101e00344011041c8000c030080d510b5003d2240d2081c0c03246e4000410780c1c1c0306c2a036042d0890048003007490001d9150404920780c01d507a00001c80300c50007545e0038803082e2901084002100022a424640c442a031146031300081d04c180e21100f00b0038001005c8a040180380000100580c1c4592601c5d4071050f6510700810131075811006100040400742011030900f2020720300155240700700c80d4400c0084059070b000490a6960340e1020383c01c1c0d01c0410b800c02c081c841c0c480e0064800b40702641c1e2030f40450700598148108000c0028114165451010303105040e424541c00d1012145001d4a0030341e1040403c0c8401c0000c4e219441038429558403030004045080741c501300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361973003 1250 361971753 361971761
    0x3020d0b1c11010c11120106030b010f0603050c0f25060f020901020c18150109030501050c0309100b0a050405040f0609080a030b09041a0903072a08010e06060f030a1e0501 75
    0x82d003410700c800c01ca043e00c0401c00c1c94554400404e02034607000b4185034180d074018014000c0b904001d0032555040004034011400701900002d0311440d80f03041185466200c3d80b00060301a008421451708410004210100901d051104404c03058810b980d42d01d203480d40c1c0325030564420b546280d44288c0d001c262880c071581d0411003c00c3c411815902c6080c8084a400c0000e09428000c02c05d00980c298050401001d03480381103500e00070740d0881d008000c0341c101110030340156841900d0010301c5210728100807c4c8100c1e0361040d0303204003070024a0100f54a18050030300001e441d0051041e6003140b1404034000105403140101c105092050290a64a000b0260060111713107151400c580900211410080002c3c4000d8150400d8000311902c55142d50314001c4461861058180040c1b070b007600100120244280307070324244081d030b080d501c180d6041612551a82c2c204c509101050209910410204147d03040c041c201e9950b200d005410346030584007075216540c83d07144107404902d90441d01018841440402e2103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361974253 1250 361973003 361973033
    0x1141501080f0601230711060a0c061a13060504051b0f03041415070806180a1e060b130f0f0315090c2c0702030a03020d0b1c 55
    0x54424684415000000d010000c000c0c140d84107401c2c0c460105850fa8003e0a0300c030807008200c00c004161105507030030800c09802218049a4003140c070b1a0541c100c1c0703014000d65080164503580c82c408417550342c4a0802810020110710302c07034200304044003580c0c0c0321400140d6120f490305201044043ca40b0080c0802c54000801e22085100c52195440d0120520400c880c2000d044074091512902d8a05080c01d10410154035415548030760b143c441070302c02403d800c03140b085c5d8a585070300301c0c03917a40c503010702115516182d400348040d00000001403d81c4c0081d4001c0008a0504050700380c0354524800350000c440554000a000740c3c004071b20440f06811405605000d042441c4884d8103a81c13400040000024050100900d03c041d400180a401882580065501504034400d41140755940c03070900302d2800508090320050100c0410035001609005040d0701500666000754a44001403804a0080d0060b0300301148403900c1c5c0c010f400c8240d646150340f5007800740009000070625400d141800055000354 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361975503 1250 361974253 361974271
    0xb0a031424070e0114040b03090607030b0105090603010509040c0b0d020c07080109080f0a11160303020c012c04060e0115111f09060f0524040504020a05060c070909050114 75
    0x204000d68030b0342c041d0f02c00c00c01c0c00082c24517513050007914414040720701450300083e240f400c1c04020031011141c0003034030074041c00035603d04202c060301540044980e48221b2030740315004402000100140d091042030994014000c4895208250703c4140c0070360f0b9036010100344031035590042000104060b00b0712a0f000103020790710007001404020b99846555000355524031840c1c10700419007250b1385002d0458640c0500081080d2540380e40c100390580c42c04200340c001580180300d4040340000070750059202600c2185040440341105c0c0050400900810100206540094079103e0004801e0f801c44141806000b00610078581d02494080007029801c216100e62035580c800c800d0101c0c1888a10b004400e0103c0380400894007030310900f007901c007428250610300c3c1c442d860603040110403807445007102c14008480c0c01d40b13002079a80004100c286d0350305481c0a9801074440070200704610b015001400f00d01081c00940360550740d10050441115001203040d175059446003603951071404801e00003a40210b0301c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361976753 1250 361975503 361975573
    0x609050102210a0c0812010311010e0a0b0903150f090613080a2003070b150a030302070b090a080d0e10031a150f041e090507050d0b0a0314 61
    0x42c034040400380000c041c01c00039080740003c6200b000740c8a0054645003d0304144100d6580711504a0540c03198000d12040c0d8010480c0381c107104842d032141d04015141d403002800c14441d1400c100800e001c5a0104820716810300c500601c01d21940400c0110500c211603142800f103251800c4a8802e0500300008c00110391240314100310300020b03c0c40001d403840f801c0320749000b58407180f182d0405201e4141e5601c0c64041e911010a441c02002182c50740184038020b05026000f20510030000d001c0380b65081d000080150700103060610280f0b10101c050052814014403903c000360b5140c1c411400e08061800e030500060b0320805880c0942440e82c2c0c1d5500f68205440c0420114030382071560900a5950f07518244165440c0715a80c0e94104000141c075203c03404c04014613603840d640c50261107020300e90f103850500d04084034000200403003030f84285132190085444030340c5006000b2421800034403410b440310341d012403583c1011001c00c1150201c418650170a80007020f07000d280d10040381c1c413965508480800d003004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361978003 1250 361976753 361976773
    0x909020105070308040503040e090102090f062523150f130305090a1a070302070812070311070806010303110c0f01020d110c0402031006120b0d020f03031b01060609050102 75
    0x40700044030651034241c81d1020041e125490803904500c12a40108064820042032010204040d17004141c0f0280070ac43d5080840d400c201840080d0141d060b0107602550740ca0300c842c040b902d400700c5c2148001e1003007003c01c048405000001e0003c01c07598602e0745a5a21291140c89540d00700e24507142c0040200f40190300e40d1509a500030400906c0240013000c100002c0b4aa0001e42c1b21681c12001900c640300e00049041085081d1400f00c4d00322500542c01485a8200000d1002004c82c0d044001804e4851140c50f04500e9107066805050b4074101c201a840780b000000362071762060000f180070710b10035034540c0e080d0010304148900e003c0181301150700c2074000d821000d600e80e070000380c181003c600030300b045080c180020304180c0c1844100c104143e002400007003000300c0e65605a56442c284d604a40301c2c00c440681c0c0f001050116034a0046241d0001e42d00c14045001d407070000300540c03c0080040c1281c0c9440c40e800d0f080b01e10905004050f020680d1566418043c2540003074043c0041c0400384014000c2002d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361979253 1250 361978003 361978007
    0x20d060f05010f0e060a050a120608300d020703020f060f01180e0616090306050c070203060f13080d0e0d110c04140406020702040e030705100606111b0f0a09090204050109090201 78
    0x420050184203011340001c12238a654011600c0d84d801041140040050a65903402652039141c82c60696420000c03c0b404030351040040310400c12681858800c803070802083c43d8504009500583c0182d0a501c12020b50420f4004100a264410414408000000c1d450182c640f800d40b24a0001041403600380060315605904c005207040e88408040f40d2003101203001207094a00d60b00a40016106a06000030441c080070340700001c01e4028800d508451f65695080f981514a003420b41e104140255007039268030100c2e030014094034018425540000e001544078107030f9031030b0151144210010409141c843c0c80c00100501c000c070f1403101c056405000210106044038440034004200600b815801300740304081d902ca9038000f040c8648003800f2650341c0c410704d05199648402a00b20032003901c1c107000c808207215114044a61600300303003400504801c40f0b40b6041c040428500312700140c10000d040c0024080783c0e6440802d1000b4403807030000141c04202c41c01800213403481600310320405410303c4051300050b6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361980503 1250 361979253 361979257
    0x109060f09180b06120a0609201e01020715021c0503072f0a03120f0902090103020108090f0601120b0f061503130818040b0d170a03020d060f05010f0e06 67
    0x1507031010814441395a10700000740001c0e02e16861402c0c07889240c0781700042110700c0d808a21110300a2503400c0c8000c501c5c03c09590ba00d08202c0199802003401503409845402010500084020500580321030940340d0250080c145107000110700141d014200c09a100d2000c10340c0e0074001510361501b240395140c950400b400300020703540d000310044140d00d002502800000d654408801007501078608810503801c00a0003100c12400b003804d15483c1904c44408403440c0e03c500075115501030b1034025168a150015901d5000040180c03c80d80110b010010b04900b0034003c5e1030280020342140c601d0901c0c181480c0f4120070009102e602da641d0300c00d060120a0350754260315121034606801403651ba55920084003941e5a0b1081300501481d030100b00666031010206c2500c00c500c40c151010444030303409a08200280d21440c00203044050022595050f12a035000100404440307400c0140c644099011800c04488503607102c21800303401d0550602241d030307011003000300d9040703145014050080c103400010114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361981753 1250 361980503 361980551
    0x108070206160f020307080307081806041101030b0103180b0a06230d0201021c090e090615100e031e01050702060712021602041503030f0c03020304030204180b0109060f09 75
    0x3c0050392080c0803002d0f20800c00c03206420384c40b20700941c59092900c0007420501050700c910395601812890007419074000a0014840c60300070b01c40044201c402030041d0010491152103604040d00c440d0700203400d40507d0220225144120380804807403401c98015421180740da08640707800040c08240c4086100d001d4180e08450703004817070126046505100603407406c442c0c03021207140c200311101441802908440e604040311141c0130140d5a80e541c1d00c0145072a00400c0798840001810611201c4c0c076070030030103a01d100c81085800c160071111b03e00c000080c50490b046407086049000a00c25951802c000e0140507005005c074002408681803821001e4070f80ea804070341070841d050740400c142c42c6141c84200070141c8103401070010403c001140d421b01304000c6180c007059012880014401590612407809122070a0f01503018505203411942000050f12070030440401e0781c65400c0c42c10300803d03c018280e03402001e0900c0c00007078071880c04021190008803980055802e9180404030b008659080702c0403005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361983003 1250 361981753 361981757
    0x6021014010b0d090516030c0609080d031a040e0a020f0316060309060f1b08011a090d080714160608010e010e0603100e0d23340c0302010807020616 65
    0x9070030340c2030f03074000003810081805442031184807003540e01c10410200c000c017900c1c0030385810202e5540f41d41081e599280750344124025030b40440700400c0da9a2113035000903080b181c45402e150314159140c0c009000d442000654080390b4024890380400c6140403003000c024004158060300100b8410001005081e2080c401c0c4402d05840da110102009500d5200c9038035581c04c12401c000680c00254007550710102c000a80b0081842000003240d0000b03c03103074007101416548201860281800240311611108100403030f0722010500984001410303003104803406240200042003080500d060502214040e82d10400074081c020b0700511094007500fa560341500c0c40b400804249484000100f440d000d80c181203004210701d0300c030328843d00f40e40204540502c030100399588040d0610b040305142c03021410701c0a007014500e040080700e481c9420a14645041400d440d000b40400c1e011301003ca04441318140c044400c151404003e0046682290050740c00200c94801400380740b07000038001400420721008101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361984253 1250 361983003 361983007
    0x60e03041d07140f27010206090c0a051c0807080918040b04030f020a1a09010605042708070605010306050703050901090f03180f030501020c071502060103020f0a1d0106021014010b 79
    0x28141d009001140d1038400b42100005102171003802e801e40d0390000001c1980140205408159400d80000c0e51001c000801050310100303070302c2c140802c544100012302100c0550010404c1e0030100746580064540c2c0d9000302d400d40e503641b00d81803c018543c01c544202c24101c140701e0040c0000301d5090124143c0c800d034582440c1c0c1d5441e01d88a0300340e241c071341c500c1c030b00a01e20000d404050b0025044904014010045c000c020b01500e600c136404c202c00e4a1703200300e4002030085402248510300041d040ca50303a0403030003001c11900e8080b054840a007a61802d0f0005c0e41c00544400a0044c0158113104050740300070020003c0208602c1580d41d14042c001060000d01080301c106c1d4035040585107000072000401d1200303d0b10208554070301d0200d010303401100d43c201907030240c0e00d0b00081c100c1341c40700345c120464000e90103004c091b0300756420414051084044d05420440403140403d8212141201d58106030301c4101c203208541c50000300038a00130b8a00d0902e02d4180c00c0403442405184030450a81c1500c2016840315 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361985503 1250 361984253 361984267
    0x60903030708060f0907030c0305090f060c030703020f0d2004050d0b090f0a0b0912190f050d02070602120c040506041a0706060e070905030d1407030903060e03041d0714 74
    0x913141c0030b951801c1d0b0b0b44881e1960600010603090b51207000c0070704103078509000310f98071980e0f4a84c0300e28591010203965004400010380a40c107010046901480d01c2c00c0050810341c10759030716030094111440c1c0c018019500c600c4480180c255908002c1000d079400c0603d46060b081401080b0484011a4001d02c0550f11002060540505000030000c200c280ca08451840d44c450803c840646400c1e141c441180c00360410905d0070741854002c071070000001c44032065072850328a40403156400b20010600c10080c0a118070344454809000500966010b10781c096164421100c03c1880b0f48005801c084902034100801c128a07110203050707404840c0d09410103152441005a810118814020009c0c6920314160001c80c462000c0b4003d64050080c9540b00745400e5161800e0641d102c11050142000c194003100e4a070988090b0030080000320300c02c0c40c10b2004a036407a170712030381078410b09600c0451680022a0a01001c15451400040c0c079006584072991410000400351660004490695045070006281 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361986753 1250 361985503 361985509
    0xf1611040c0c021c0206030f0a0603020303030f01150306080c0103021e030903070c08030304030903171b061801090c0618172107112403130507050306090303070806 72
    0x2802209501400520410080100061202525810032407080c0c208507400c84020840700d00f80041d01d40c1c0034048610b90707101da02145118540040c040e00045444003008401a28103001540c000c01a4816000407541010700e65040500400c4c11502010f1034040300b0040c40b480021040c199441c2802c0041c0d82d62a84498911400d070000070311242118008103000c3e14100c0003005005035070044404a07170741500c4c1e02d20326490b840180c0d805070014000390000d001007003034502c40c07241841c1800c01c041c0c034151208403a034000c58004050164250003490800141d01c2c02035503018a401705a00c02000617484d1a50380d2445450140104010080c8002420b50441080f07070a0001626140078000c0ca0341c54024411030780d42040e04440c400c0002818030381303460f0000704002c0e00c5103181d100090b1000c0307000840a1120000403610b09158036901044103881e5084510025030107034100f002e510350201c0301420190b2034200d05610039402a40190100040100c001c000d0b0798100c3c01ca8500303d802c82e1200400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361988003 1250 361986753 361986773
    0x703051306030c081b0d1517030a08150604030209070306080f0a021503061212040305070f0308070201110c0a1e0b07031e0509090702010c110d1b1e0b1801020f16 71
    0x101d030300ca070b15000000307042254200c0d00d54100d980c0c56108a98110201401946034003035066000003041e21440440c0ccc0c2032980070102c648000e009815039007026500d40010b00f038404142c0388800842ea5858080c4608907091007124034603911040100030591160340403403e2900502c0f91310301c40c40300c017001148042d80c5d80c3c440c07034003000e502c00119540c19a1901c02000c00354414070040300c40744035030b000c000b401d2203840b0f42d004200da40124100d404c09015030015a61038907441e180006c240140401303481c150b84d40321442406004600f06840c11002d44004070580400540c0009150b4842400103800003548071000300a0441c2c82c3c0c1c00d001910790f4408094bc0d603801130304072030740e032000d80d11081008441d41544148074421050f581d8820380040c9901490310b66070b0b03d400d0f5400092041e402e101381c07c0c2d00f8030055120540300c0c0550501c2d42000d011981c0e101d8020728030440303c210544040c0000900c10205980c1d0000c860b100071443c005d885842c4200741e00c18003400c048180c6400468000744984084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361989253 1250 361988003 361988017
    0x7020f03071511010509070605250c0906081002030603030403030f090302040c08250f210e030c0f0c030703020906042003010906091107020409170703051306030c081b 73
    0xd0000c00b815400003524855100c502c0038202d61800b000030b54166000101070f012102036444480ca0703c80b174030301e41054003004c0e50704481c00445821183c00010748a68130b07107401010304200014059003040d81160820b10121640e44010f0700506c1841015500881240c080340c0d894140300b10a21400c2d9416256040750358070180d441460911003094003a04404400d10412800000200107031106450031070030f6034030824040010708486c55082440f030040300c0b2032180c02c1b04a90000c280b00c20f041c106034196003405240580c0360304085248020141c0c200300da512600e030803402800c1402c0c8144c02203079440415101c040c1c0f060380300b1404680c240c0c44039804414508506030003641c0ca1003c520865106900a108a1100702c2c50b0020014410119128140600300181c0c0004d00d4a14607800304800350441d2041071303d00d03004801d40b06101107041002060124440c0d00c815490345074040d0603060307041c03007a0b00c0102414203107101001032640c02900d0941c0a1030709215402c1a44401040350380ea401002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361990503 1250 361989253 361989269
    0x7020a090207050c0a081f021605010612050c0603091c03090b070f1202070b0c0304030e1f1b111002160e0f010602070510030e1002070803090d031107020f0307 70
    0x60b440080c000301190740a00c1400c240c0fa400742d83d41d036175516184c0d80d061034a031041d0704d1b604610b420480f0409940080c020702d4800c02102c03c0d800d049440704c9003101c230150300c14643c1403510001d04042106c02e0000700c19000d800c42d00d85003540b030079025883c0c4400c4c800c15070842c940014203e030101a4000d078415400c2035003180e44400d8070f2804180180507911040d00600c041110544400e080701014001c8542c103944c05846125030761680c080201190700060720450a0200582d44100c0b5900c40f09020002082c4080b007040b006089040090030005000c001351080c0c03980c2c40250004503000c100c2170303145500191200040c00716140320803030030300d020740c200700400446205000800c0500041350358000c1e24200c5411480380d0345e07840181da40d080e49204e0030740c1081103040c0d00082c0d140203512840d0302403450b40c10780b02003144e200002012a40000340440f101c070b0b004410312003c11000c1020081ca02081d082c100300e0a01b0f0703080000c1540c00b803060000c1c8a0b00c494020404241c03400c1c0b0078038005100304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361991753 1250 361990503 361990507
    0xc051207150b060307050d050624041406040b0403080706110406021f0c020d050a110d0302030702100b0102060a020708090306040b1909080a050c1606020102090112051b07020a0902 79
    0x1880c01400e55440d40d04030741c000c507040c0700704400c0c14070782102241c0c0120059203400b0310b48000c00036054080c280042c102a4410740605031540e0510203a4250816840303000813079070341d90703050107104a1698010600c3c24003c0c1024002400201c400300110f4090f29000000b040d19030009103010f070085c0842c02041c100c2e00102160004515400048040383c09103002c88848003c0300c458811011110075028020040e8004070107100b0343c40c0128003c04801400c3d1801d48001980291114901340a008084000030750001c10098003540c1070001c02440c1d040c40308140190724110700002e40e2024040c2c1350000860340021002c041104500c1103038803c0c1d038040c040d18060310341418004030908049503c3c80c0d810910041c0d122454015101d1202d019034002d1006042c014244812182504910381c100390320320402e4620220542d10581c050000c0c51654000f5a4583d542400104081201c541c0d04021a04207000d10004004803c1c40c0c600c0050b024404548412050001808007100f42d804002403c0c40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361993003 1250 361991753 361991767
    0xc0a0b062706030d260405120304120906080f0f13050609010603062301140f09280b01050904020d151d0708040201080a200a08010906050303090d030c0512 68
    0x20409849124102c00c4003a1040c400c00d242d0159404051282803a1185a010341000106120114607540280c061003c407110150000060a016407080d03405680000940f003401d0851a80400030002130072141c075001c6042c0c00c020900024600c40600041095800301000034100300d0640c1031020b0003600041240d51034184500048d0080459001c00d4031030600f03240c082003e0f50280c800d68000101c0102e0740103042da00c0d200f111100040c1450718141e01c00c860300789802040d900c2c0c0c0c071b0b40341c080c070800790640200085000400000c0360080d1864426107003040460a200d80c1c014082d42c0090205540240e51801c00f00e804c14014401070251001f00c00300300c20007091944403c40751408140401c22030150b15228000c068841c10400c0701c1c000c2c0060300c144006a9441c9080e00401c0503404001c0c0c501d0300c200c120b0b5002c01b420f500071a0300b61000a4024004003d5071070207001e07a100820080d40a1031814824101081c02103004c4500038081c41000c085000c10400d0401c0b480b0b07200444603c0e4140c9803e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361994253 1250 361993003 361993069
    0x90c0a0c032322141008060d0209040302060f16021f020c0f1f05061516061a1c050d081e01030c031202011416030902150417030c0a0b06 60
    0x15081082011141c40c1100100b1000c0c05102c0900c4e03801001030010081040202c8111400c1ca002401c0780d8022840900900041e02c440d4181d9014501c2600030700081d2a02420900c091500107201104d501c00faa9030360040c1c5ca03004200085640420b80e54502c01700700c4150743c0b00103481165460102c600c175803548003010351400721300b01c8880f00c80003581c1d01201001c00012f030140d0b20f00f9200c40b07504c001e40301d049904510001d801040d00740c404c3c120910b84e0075096110380b0b0441d030700c460301400c0e40f2041c2d200402040c5424801c2038608001c80c0c010551141140d104e050b0303100e40c41c00c00d071000e001c80400440c205007550f0320041200c00300c04505102540e102d107824111448648012500036014a00010300d141c018083c240c00520200a6000310f0356130803a0409202114140e0a02170507920111503015840b071849034042c00303130ba900c59143d5443c03910007496a0030a00300100d188682003884054201400031884031034003500107035580202e40728240080c100c1640c103072441061500701220314884003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361995503 1250 361994253 361994287
    0x901060806010905040c0b0c0f0106060909140c3106020c121911060f0f0910020a0809040b01090e040303050f06040902060d050a060e01080c090c0a0c0323 68
    0xea02406a4115036600c00c1241d0650308162001000c001d4800d6041c04541c8000d0f020b404440c030040e00b200e0003c012a00140d0840d450703a004400040c0725440c0c24400d510083c094501080414050f00c071661a103a00e451100d80034201c946040c60003030003d610404606007120030f10507810411000201170f03441002039501d1845880c0c0784d00665402081d0019000302195900c041300c0e1300d003003403040c100c500d684032a0301c14800d10f00c040e4052001d01031004d49410800161400c60140003200da6070744501010046181e00544001c0c007190701040d1890005000c81098070340c44a4141d902040034407020380143c41a620682104070183c03044000c1000f0b06505030040d5010f4072509401c84e090340c440405120542308ca400c2e0180d0400000c005080804c1c140e1352103194440405200018a16240c140c06000034a082e4060751a962040d903486409240205e0300e2600300c1000318450b8540030f4401e002414194807220080c0501c08884042d5203044400f031039010304082c250000395511211006c03650144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361996753 1250 361995503 361995509
    0x3040f09140601080612100218041401080a0308040c05100215011502030f07051903020721020f060c0c060f0a03110702180703020d020403060e190b0a0b0315090106 72
    0x581d0900c201815090004a0603500800e07042e55401e14035904e01050200040d281c601c0c401c80f901c42c072450503506003160f101614643c8a000c0c20042c1184002d070420050705c003001510740c0308200700001086810b200003410010319605060504c00da546a0030840200c00040d4001d94000041030300c0c0721841c681c042a20b40d20000c264445843c107980740c0052101d1100300c501c044000d81d00800c0302c1c0700c20020b0440030300026442082240e5a0200c4410b4000c591002c1060840c0903900809081c002c20241c0c072110301c0380c04a2582c440b01c04000d503400203801d480c6041c03840c80c018480051600250720003841444e1040101601d415614048031800808aa0100c00c0d0f0300c001915081b07008034107900d800b00301c2d050290010030050943c1d075042c07103107041c9000203002041810340c01c000d5882c8008440c0090801036005050000e1081d100f030340300780d06001045188070010b001e50080704d000180c54507400c9412200c020000100714036035101003032624900c0e02c10307600d101d03d400c0200005024150008070179 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361998003 1250 361996753 361996769
    0x40f05010504140403050f0706200c071a03240a30051209221505010203031e0c09090f010504180809040c1209060c0e1c060b0a050303040f 61
    0x10f40c0b5202c0c0880d0b500140a640003000103404015600842c01c091001d0450345008a0002445148a24026120b814486100c0b8440c4d900403401c0341000e4001e000200040c02c0500341e001503000080320603010303840000d06038084000784045106806100b640c900620304ca000d8007002d0b80c161135581d040200ca079a80c09007100640c60107140d00c80103a03203c9060760130503402402810b5842200c442128141c201183e000d801142025210024207418000b24142507c020320000300e043d0f003185072500b4212241c0109040d54401c105006945a800c0f40c00405a080000b80c0505900c4400414426214103111260300c940f40105001201440d0381050303040303c40850303040105000d042c0040d5840065200d02a01c029410303c100c1d8050309190b0060303242a8114503010286a610b0f03400e00046a0400c00c06840710b039550701b00c007040140c00010795482110704a4840c0c80f0031000110b081000c4507402c0006100646071100c1e40b00e031351602801d100c0944801010360303031107546401c00703402040e03c1072103907041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361999253 1250 361998003 361998011
    0x11210f010920090c03060409020607060519140a0f020408010204080313050a06080c0901170c0309061b0a110304050607050d080703020f040501051605160503150108060711010b040f05010504 83
    0x85044100d030070b2074020107010b80034081c16590140a54080d4000404164000340c64046000041e50703461300800e8414071074140020f06040805802003104481d1380f44001c40361030286010b07185e900c40b0748900e0707100c2d40c00c00c00440c28580c025110b502a00440d03004209660002c6008180035001002030306102d041044100b0394a0b0340d590401000c15018411000460240710103c0c0032041c25000030207002906051500d2240c800c5115042c044a0440300d9a24050307000c014001c070a03005200707258200305082c0b4024046410071071603034018801c05c03000300d050107400c1c940c110703042d4400c0c001c1c2d03001008000e001d21f0300e609950030300603102d0104a40000009504800050419009101b662440100c420989040c18182001903070240d019501c1d10068240540740794001807000c0080954010707a48181c1d4010501c0c2506040c900701e44e4810b40d05840d42d0400041c0021840020100d501c0070071032400418480c484039210b80180b20700040c6540060a01d04070450700e00c015000039040301c1042e58104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362000503 1250 361999253 361999283
    0x3050112021e032a18150105130803030a06090c0801050f19031202061605030907030f02010c0c23030c090a0504080705031215040b010c03050315040518061311210f0109 74
    0x60344140007246d03900a004c0002c3c49801e404d5201d05c0191500c00203001180c1c41d4582c136a0f096a00c0c0d50800c99462071040c0d15801e05202d8022207008000d4910618100b0070200d5042c80002030307801241c2c52074140070702d420b040b198110942081c0301d1001950092040702d04591034040003501c2d8401201c043c040c2c42a50a0169444c900c90703400c0782d01c1070b2007a00c09011030b03a0541d6200070345500c034808203a0411a80c210190041180038600600428460f09540a400c462a030504029444021420711030f400c0b002f001c1c100c0d5140e00c43d205a0104014200060590312850540000d010314a40074083d440301007110491020801d101c1d6000c4d022090621001d01c41d00b4040009440f41c1e841e030b51b0b0029805410303400c00a8051406075821081c0203003100c0004840c040441c0c101c036011075541070b20a084408110b141c080c1402810707000162140e0000031950f040d00c40a0745031580d507c0342e40c000c40c0c81800688507107602641442d18143d211041c0d90b140c8024031000b9001c2c046507101540c0480c4540382903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362001753 1250 362000503 362000539
    0x30807020a0b0a02030403090e07020a05010606030c0c02040c090b0a050c01140124031107050a02090703020412150f06080c010e03010213120c0504020a02060703050112021e032a 78
    0x5000096000c14550b0075581d03884203820203900043c10840030300c210340b0702c04a648041200c103184580c6081e4010310400c9031600302117080d0340e043d9100c5403d0500e0481c2547c615544819a00c1507690191404121400c5007401115079041782c1c0c0c820309110201207890308560ba4404000d28140f000d0310700030303c101c807038154000041e807100388206110381101100310000164401e0140b40c1d10102d0b03007400a10303141003400864003070340001400c13a0143c201c4010401140b401c0042070750400000d1400b11308003810000501d1000e0708118015200c004020500415000907401a000c01078a01c941403225903074609445079206601800c0b680440c610304210082410140f007030340d02c0f503050000d240914a1604030507002e282041c3ca0b040d101e0305460840801c89846070700051003003200c25801080c4a20b01300a005045900680080704150405152300c2c02695541c0b08540a0010703110365031020f4030a410000e840c00c25000c3c0c54007000781c1004044102e03c2612070f030000c100001a110650150462025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362003003 1250 362001753 362001763
    0xf0c1e01060b0a0c1b0b0f0a080112110d05210307030e0d05091903060207030801050a06030e211903020a03140906130f08030c0703030b06070308040b101d0403080702 73
    0x2403800508540440c0012818480401405041c000e02c225801c1c0e8403010803060540c048107001488407c000f03503044110754810142c40c01015070428141e046038981d51401c11030344904800318440d103410b810000c14000c0c1400140c400d8003d050000440c0c81e05031601042e190811105040030070300e400103082204e0f0020507000e80e03510240c0e464a242c00c03a00d00402214880742c450700d441e03100c014103010000a240740b00500540d4080d07154802198940000c2149211058106178101401c2c224101001840040c0c1d0009c0310412000e8440b8045031600c03035401600032407101c28020074600081c10b05040e0141c0c0204402500c3d80c1d82800300030b120b00d44042c5281e0b000d95001240e940718a002502d07040303803120060000d070700c6010700e48801074140c2c0b20304003e50415100714401b071780300040b20300816405101c1e1400c1ca8805881160504c1516140645a40300062000c0d04410010b00040c0d055600d10306020068000b1003084500da60f400704082500c517404036801c401284d9004042004a800051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362004253 1250 362003003 362003017
    0x623181e090c0a091a03040605181c030908120130020d050f031201060905010c23190c09060e0903030c0a0905120606030601060f020706050f0c1e01060b 67
    0x8040e407519201c80351110780581c4607003100e03400c114200030045075565116100244841641e5601600c030304180c2010b40450348007610000c41c0f031150080c42c0707103500750205080182c0001d2200202c0402c0005c01e00344c01400d44100f00a041440000e01c0d001c14181890f1881c1c1030390082c240c4c00c03406c14003d00607281c501c1030030949a4020441030345007400601e0084902440c40c0e101e8001e41e0048500c0b440c200d407560708242d090340e01c1c2034142401480a180d0003101c0d0300050509292402c10b0006035120401e080c0c070b034040081001a00c441700803140c09020814151400e6030036142410718691401c1c800b81f0880c107030180034009410316100050a0019107100d50003405408099803464a40b441c80304010b5114061140a009064200081c07540d075243c400c0707220f074204802801c0c4910b0200101030400340140c000740140f001500e02d100710507500180780d0059806904040f0780d1204a00d14082c1c4a0081903d40140f5205210500e0a00706240c064406088001c1000744081034881c44110410301a000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362005503 1250 362004253 362004259
    0x603020304050c0418060f14040812060d0b04020d0c0503030c010212060d050c100c02060703080106171014040608100e0723040506190b030601020d020114010623181e 73
    0x9034450006c03071113540c046056400507030b2000522070312112502c2c444503421101078035600e0000c90000d05041d84002e80d00e5100f035003220740c200e4544d5950b0b00c0700d02190018101900920103503050904001e600da1a05014290050449072900f000d2002d10740031b075000b403d1804c8124030410103d4142c1c20220350420409911002901288401c082400884110700d004c500030800c0d490842c20160326080006c00320320740246d80b001069814120050003a60b004c0d0200d0ba01c100040c810801c56806001c0c581040d40c680011182c0c4050007040014080c00554000300c081d40500034a10444210b00d5112108002c000c0060380c00032540ea0019242d01140c04514030505c6032082580c240500e07051f4400c4d940020001e100365400d034050054026485196006000001e5001003401a2503804018107508400c2510090140c40807249880d01030000610070320b010700507154030000302041c080304124420315804221607181c1c03030303201c48807819442c9001e50a80200301691341017943e5001204801e6000d600a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362006753 1250 362005503 362005541
    0x10f17010e0601051908161d040e030c030c070311030607021b0619020703060f09022101090f050606040c030c0813030e0a03080426060f13020a0603020304050c04 71
    0x1011a2030600000b84454100041081041500c0c04800700705505030031240d0340c8544524011480c403da0003d2107400303c050111200e0380103d40103008546000e0504151008602e00500118481c514000c04016404d036000104a04540010000d4000c0440703001d048a103201c0d43e5081d060503181c42081d52520b00507084508103848009014800f00f804500c0580014900312010440007050003118540c500141c000300d0b810014000e0f0b9014911003240c0c202c40400c4910300c190f0002d400c5298000c443c0e0040c100841d095a501300003035110010042d0402903002602909107032142e01c507001110100d114910340001e41901c988030344186020141107844540640e183c40e00c0188091112141c2282000000b10304100943c4404868074000c45c4070700c0203180c48034101340c0c101007003108616075800741205411802e0300c0d03044d00180030398210000e0858045a510b508071420100c3e2110200039402111003040017815036410380c000e40c0301c1ca01820945680c0b00b031b00c3c0200003e03260f000b01004403883c0c070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362008003 1250 362006753 362006759
    0x605030c030a0e1603080d06090b01020d08040f0602030c03010306050a150621061e05060a080112080c030a0c020102010c110d050a0315060e0102060a0c200a0f060506010f1701 77
    0x1079600031600d101040c0c3c00c80c0c5503120103800444240c849500100c410403030120300042c040322640a41406040354000c00d1210302c80210000750f80742c1c00c805a080c20804014041010300004002100d50103030482425583c914002e02040304c654400c0c80100c40b668034001c0000c0590816101c2e04403c110420810b9041d40d15180046420701d07130030a08450b590080420f05610710f01c2502c2514020000c0c80d6154401c3d140c0700c02d001100d00038940c030590280b0030800c202c03095035a00003065070641c4c00030501d510301501641040001c40c00740c1c0c50301d40224800000c07000780350f540010a00b24100e200340e00034080c07040100411a100d10100c200d54050f640140440a0890f001e140602140401c40c0341c0018020360521944031244c14550100e8041000e4a00114403542d0612081c0e0b88643e01107414081c0040c41070380100f03803107150700313255101181803503240402ca01c6c1407101270a466000301011035880c5190900368000d110076541a80402c8a031b2180e10500b070b002e01e03500d811041d20303414003600780e0786 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362009253 1250 362008003 362008021
    0x190509070501051c060f1e032d0602030901050121020a030212012003090d0f0f0302090a0315290312090109031203090b010b09030c0d0305161b0605030c03 68
    0x340b40340d0301342c080610301541c40d00105201d030f5401001d04401041460745411400b035403031040004030b04116a0120401d1001c0307441040710395822091246c0341d0004a6003410001c0c2442c907481002801c0c18000000c0c4140c20905421950503221441e0030408150308149002940b405a041b00035004a00b84a08202602d050340c3ca90710069514800481c003c94400003c00c410350204055682d03d0001100f440803200003001102410182d0703080c05684103031507450182a22080d03803545410503030000b0340c01115407641526036004550108000301d0191117803c0c407038081c110b500c1e0555101912a211480c000c0c2110460301032085000d00070301092090301380300941691051002c030b4123000b88020000001140245414003140f42950000b422034101d02e0507813080841a8000080220300780903042d025a8042888400040f045452085a03c410300e025038681c02031000010f1511200c0a090060061100c40c08a40c5821400851680c6440d01030590f454001560f40c003101d04014400900492 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362010503 1250 362009253 362009257
    0xa060c0303092307030b090a03090314161202041410030605060f0904082116030c140310080f03030c040b0a020a0215040311031507050901210519050907050105 70
    0xc0d00900030110455070341101460444810300e5104044c2c0d100d40d4040090200f050a41e0ba000100417000e41414120b07510020403c13145400301914007186014900d589407400c0005403501c000348031a4044036991840f251010300030401050707014904090360060480c0c99242c01c1c520507040300b00d642c2d91184c21511594010b02004243c2c3d9002441480c2c0c261450359400480c038400c038821602c0c20799541c410304810b18024241000f905006403090248801440e1044003442c5607440c43c900001c050990000c00c856410304181c1d286000c2d400041401005840c45d01020143c0310030400716480f040030001201c0c0c0c6d07880101c1c0d001c204c110061005004a10080c0c4c01080045040d104454041c185034000408035007241d006596001c1d070025041040010515402d1200d400403406480c0660103603c600005090042160080050008104400d60301075a420300000c41c50401c10035440d05207124502c001c100c2510710071340f000c4c58054404504850750040d00d1007200214050029140382c100199095 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362011753 1250 362010503 362010521
    0x180b07031103070606061106040203031905070f03021614060d020c0f0102030f0f091c0318050f06040c08060112060c0c081908010605090306060f01020313080c030c0a060c0303 77
    0x7250102841c00c0d904102401c20079000d200c0c00148180784c1312004e40400c020404c01c400baa00203808000240c0e0300402510403050348002e1105250880c14011a29031080c110014817200014030050141070340007400c003008240038061844842d0301e914040d01400054008564043c108000040305c2c024960003802e100030b055801c44900343c808000072402e90300200c60541c00801030f003080104c90303401014a0794100001d500504890318a045210010400c80c2c1011380a15440b500011a42040381c00604101e81d004019540d47c040303015241c503150401540e05548511014001144400000c215141250030b614100d07810600c00d95501005003184010000600010100802c04140b03120028402011051100e089020000350083c040d030f101078121303808008081c4211841074030300165040c1c000c0b00c21904620301d1500c0c180100e1840c8244004801c800f54402800100309000058401340000110180d441c2101c00d05d05104e0708141c240314030000954089900742c003003406035014200e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362013003 1250 362011753 362011757
    0x3030c120c1606020f1009051009050313120b0603161a040b04060509120601050a0b03130512030406050106051204060f060314330f07020a02030109120f180b0703 71
    0x2240715403002c1611415640e840103015800940c0741d58040380d81844924074550501c0b80820040f00d080c0c50701c1d95100c0304076482d4241c250b035411040c4103014041041c0e81d9007031a0380342c02c41e00c1c8a40b22002e90483e4106110200c50742e038140c2e0045031251401007216049907181e0252508560320700700200c909428155800c0104060400c0045400c0b00c1040050001c0e02c01a100c0c145c1e1640581c0a01c4105400d507003404102d600714000502040c4e82d0840c3d150200c0e1214804607440b41c0b00d10f00a0150386400280003800c034400d41c0d0a201100c4065000fa40c401d502840c41000340ea81d0314001540c1a2145403903480100342ea0740300103000203841d58071900d4004100500003400d0781d2a0303a10640041c0403400704100710790084061075a11200604941c100311400d42e8451f21821101074901428036011340f4014410001d00c00107025203100304426020750f50010002c0c001c0003018240f000c00080c40d070725840c002504541e4558001401050803543d030391503040d100700009242400300c2000303070019a02141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362014253 1250 362013003 362013013
    0x10050d031206080a1110030507050412080f0a21090308060907020f150108210a050f0d05190c0804050a14030706020409020306010305010f0b030c07020f031f050603030c120c 76
    0x2800343c10400481820324810403140d5401d00c51a0208011100036103059801c1506080c108501c4c00e80c0402540c003111100301c0780d002402c03070900d0306044600800d21580c07240b08001c50420819580421000e8402c0b11313a1000d040c0c2d07504140450800d6070740a01002d00410300030b0000c0303243c0341043c0080d00d521041e940305590b40035a01103079180c10410102c0e58050607031440c1005002030603060000c2001c5440c3d10540d2043c010001001d440d01c1c1c003a110340f4605218004c2207943c4000c0d0a58100c401490090300100f0241c43d06144c0b4641e50718501c1c008282c4e1910b00003411300c080d4003804c505030156401100030003080410759034081d1a40f004207405940ea004c24801d170800039105002a0000d8081204090303124501440010101c03001680050b0700b17001a42c1c820031881c002e8504481d0003c81c1d00e1801030b40c0744a140041756008101c1103250f901403040ea108502541c1000766144089080c19006002c2529500c0805a4a00034280e205140c1d4008122280c1001c1d41040144440500078003914 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362015503 1250 362014253 362014259
    0x40b1308060403080a0501080a0203061314101e050403050313060204090207210e010c0308091e0102031f0503120702030a120c0b161b030207050402031e10050d031206 73
    0x81c1401001c2c0d0b03048010076154801d00000d80401d010b018003600c0b00d500108100449900026551030024084181912003080c41c041841171400da10300c0c0f40280c0f01c040f501e4412682082c080101070028556004900c0001c0c0c500c00814130b03000385030242c1d4150740d1302d17815501c40d011141c20425045071308541031942007100042d5402107001800b00039000d40304082e40d5203850100d0010780d81c1801c0d8980108009a00c4804032680c10500120601f9003501e44082c880d80d80140e0a843e00c20f0042000400001e410021860800150019441907603003928600c1c4071030058030580665612401615419048000b6080326004460040c00350b0318001811258042410b444d03209040a944081e80700080080c0621014020b2001070f0903000241c20312218101d0b1004203000f0400da80d074403d09000844401400c1e02814402c11140e400303403c00030011550390038210040e1220808400c4800041c40021000440c0d0400302079003802242c002509800403c005030ba4111030034201c8154001119076070399404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362016753 1250 362015503 362015519
    0x6010302130807060302040e0f070f08070207050d0f050d03063b0c03010302030d050a05090103051905071805040e12031003060c03060513020c070b0c1002030c0406030e0303040503040b13 82
    0x8600034507490710b0047c0c0c4c4d50309080d08495603400040162861850440c280801d03141d2081010a02c14014038040c00b627606c640700200e0921190354001d03035000020400e10414800b0324006003680da80310b0030882d0602d2401c0002541500d5481c4600704149440a10710f00f414142c000703001d07a02d40e4840c04109450345001140700e001043c20340c1d03004400d96011006000314201000244035940603800d1140c208280e1f008003c00341d210f01c5510034101503d4201240c150090b076400c14082c0c49a80301c00740000d00e00074100034108805003500c0d4005000b011400030b070f5410548030781c0f030070507210030050100001d9422424403690300290058003940340307609001012a056114078a000f40e615500031170280d01c1c00c401c0040b4003540000070030035035104028960910320001000c8081303400d09030354a80c440000209040c00e20103900b403080c800500000800030031100740002071003034508a450401c894203c60380c2d07045c0e9034002102d0041c26a4010401404580b00160207131113040c1040c5800c2180540310244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362018003 1250 362016753 362016763
    0x30d0b0f0f040c050d1b030c1803080a05250501060501050c0604060c0905121f0b090403080613240e04031b170c0115050306071d18040b0a150b03060103021308 70
    0x540c580412114110418547c1e141c0208c3d211612203142c500f2080340c02d000d22404038605440011300c1c03c40e0002d41d406009000303500b6152110141c049250b9103400c10303601c5138000c2440302400c4a0f42d500c0d10701c000c10320390300450645241401940081c80103036195520900100381c20140c00c000d020001000007680e80d600c4001031009010200500002d208150500406c80d10040040214900f41003009401d6181c081b04254007a402d80360200c06074a4120111b85044e03e03040d844150305040c69084030b1300d420040c0010540c0d950300c45100c080e0070358482c1c460750f80701001c0d10000d00054858001e040082402d00e80e440500d406080e00c5180c009182c2c1c1c4449040d40301c07117a04c0040765101e20007a80000c55100c2c000c00244403da026000901d49288001d042090040010340f0110318091040d0550300c81100000840c5640e140c102d109040c64108074909420496803146054200039580d00480c0307035590702ca002c454121a603541182c46903001500690000710040d40080300315071000585034000c1103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362019253 1250 362018003 362018021
    0x905071d0f030d051e0306010c0807020d0602030c0901020f0c03030910051215240a18030b01060c0516210302030c060f070e010e0a091e020309030d0b0f0f040c050d 72
    0x2140c0741e41d842e05010451040300b45c0301d000580b2803000c5c010000b03166000540341c41c0141d07102091a03910741c52840041c0e004117100700e000d01000c0c404010050b00d100030748024090724009070201e0b2240043c941181d542d80c4030305010303650140c00038030004c2d18908024002e286001d5103420440c3c20029511003d0b14000c03800c40ea00d1145c1880c1c3c080c0d00f0382600302100c2114030340032111102e400098842a01c01e40902c01c1040000c200400036056000c07000341d10003108080d42d0b110364a130446596558004000b5018140252418065a00000c1912440c40440c4048078204035081c0341440201540d54101d8000ba01c0075002e40c00204614100c0741004c1c003115101d90aa00d400b07000900b01003000420340c04c00030303904506100264100e40d10642e5070142c2441105c03041c00000c52a44005400c01d2041000800510b100394004424417290020100241820150800c1d04110061101c010490041c032a050484c2d008680b042003426903040c0350700102c01d641030a060142c50056135890040807035251075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362020503 1250 362019253 362019257
    0xa030b13060504030c0227040b0a060302030109080a03271112010507210213051e0d050c13020901080f0606041505031e0105090c090109090c0e04060905071d0f030d 72
    0x5420705c0d0441ca010300d8001d0380d00c1c051305180b4005d50b0a03107002c0390440c01c025101809090050000548218140d00080e02455000d0028000f02c090340c0b84c1005c15412041803140400d09040c41400911200c4c106800e49400d8023111118551041d115480411140050301d034000f04c03104140c100c40c1c00d00f4090180183d085030340f40d8035054424403040c40d43c01074104071805864010420854101070394201d0000b030307850403030390410b61281c0c0300c0fa03410380d541441d00c41031340060704080070100b03010011410b0300e1040404e5a00c0880000344202e044102d204590245000c901042c022600c445003a0006d05e0703001c072001c3c12a501d404d40318000040841400c07500c030000654000100003080303060402c01040c0720880081c26800754186030006009210040004040b010082a05d41460303103d0f48540300201841c40017003040400e8100d009111000440845004a05006001510f0309092248910500480c1d032124001c100034080c0e40350060440c48210f901003211a014403242d6000e0028607455000c0e9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362021753 1250 362020503 362020517
    0x314070501020f1b010608010513020f2e0f0924030603020a080a02040b0901081e0115170d02060709061b0204050f07120501030c05150c2512020a030b1306050403 71
    0x1c0f0004d0300b035030301c1070300701940a9060100b8031050307550103181100b810b81e044074202c1c1c0246400700441c0440458082c0c41030640c129075207060560364161031030031050314250b490041040f00c04c641a10190880d00c65140c01c48203446046540e00a43c0940c0180c2002920b4003188a030740d01d80000718940d650350031050b02c5070401d0660b0011072900d4071a1035044c130800e907801c46256140180044d11080c522a070344080c030200b9400030607105002c1d0b0013400107402da02c407260046903d458503501c08202c601a004568443c3c1003050246a0000070314030710504495451000007810804212011441200c0801142c0c1d000c50304040103966502600d4420f840c40b1042410a00d07120000a0100c0c0c031122107141d00381d2074000140041208006d010065410540711040c0d2044e802c0c0d0300c500c90388a070003101c0d8914058100b1f0f030200307040038441a64049900c00303c801c0d9182d40383c0303029409440c200d08000b07601c101c06540c01c1000540c025119a40622442140d200c1034001e1303150b80050301d0b400c6608900003025 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362023003 1250 362021753 362021797
    0x20f1c080a4106100c031b060b0a0b18190314010510120c0902070c091401060906020d050322050303010b070c1d190b19030c0504090314070501020f 65
    0x141d811201203140c0350790b10503029070800c0000304d64002900c2640700c0800c0240c2200c501032600070340381d0902d0341480a05600011107907041110040100b10304840c801c3c001c3e00170010f41c4a14140c1507500000002e0001000300c456107041202c10b144101910145280c000c0c0004041200759881900c280b500e8400440c1502e0043c10b20300b4201d6050b00700e074048819141c81600403d541e490404196400c8002c01a5200d81ca802d0080303907000c6560114103410300307000c08518141b10701c0440394102d80c10340e106d1480ca40c0d00c5640c10b9031910b003855010000104c0900019851000c5604420410403043c00502c44000c85521030138211740c4240c1100d81d0f1044c00040e29000c020003c510180105441c5100448240003c034210300d8000700900710007030042c0c0030a0822032115041e0b0140c00041001011024082d4000c081d0f109014500e200a0324804010000003e450400380181d82e0b11940c55622050703d80d601c0c0101944540002c141a90a99401e10103080745048000042c0010110b80302c3c1c640010360303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362024253 1250 362023003 362023091
    0xb010e03120405100c1716060903020a060b1e09040602040b1209150411060c0c100e090901050108030a0809120a03020408011505060d0b060d0f02040501020f1c080a 72
    0xc010654001002442d0461170085141c1e1103c00492104580c0030580d03c0c80e081007003242d46a14000050320b01494035043c02c08060f000144402050712400f800d000c814119820880c02d84c02d501020502980100300044861034081040d0364003c3c482c1d000141016103420260038260440e038010186118090240540003208001d942010081c01d51701803800e10380740c5d403411029221010f50364050000800c048440140038050b0054505010b04a440e45001280d0020b2040c1000c000a80c000c910120101c2c8000c04180900ca0581d91107000943c80c1c00c0c0192070480c0c1c2c540d00200205010301600040c2441c0c801040010980b920032560056100c5081040003401c548148650520b20341204208211613126072055803450b03100501c00003010700841c1c0128126200300b1410b000744910700300c501542000203901038420f0324000e90032120400091010030b561020700d5180380d45901c0101605c046075a04c960009a404215000c010400c101d4522103400807030b00580c88180284e01080c440f6078030345 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362025503 1250 362024253 362024269
    0x40506090a0f0f0e010501051f2109060e01020301060e0603090309010e011b0515070305090c010f0e0901031505071412060f03060702060a05090a03120e0102160b1e15040b010e03120405 81
    0x500d03100c0c4d127500000d40f807120160000e980c20107110345034154400491000c50083d844203c6042e0040b105000d03011840c03600500035402401800701090242c034808a03a4100241905c3c840c126210003140f0300440c80380151900403034810340c581040300c2c0d401c0180f2154144003214000c2489040200110b02c000382d64900700486c0117080c1c0040618040410146100000d00c01c0c054810a09000f01d06080401c01294401a500e4000d6049012480008204902c03564840201c4c0000181000320b51549081120704402039114002000390078030030149400c80346840550040707402001c46a0806080000c01d00f482000c541c04000740e0889405c0203854603987c0100c0b94440e01d850050200240560380181030712140003030303c502e02684c44090305520002541202c11800004c0c4445100c20310340c0c6003030156644104c0e204c603003d2691070f990102e003001c003088450203a9001e4406414088011050000030844032805030b042203000700c43c0440980301403189401e440040a0983d54650078601030004034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362026753 1250 362025503 362025529
    0x51c02040f1202100f0e0904030216080c030c04050402100311160b06010f0807140c0c040207080a09060e1806010309021003060f15090e070905060406080403030506040506090a0f0f0e01050105 84
    0x800000b000010070103601007031900380031b40120340c80001c54071242012481c05082c0e600300c039003071240c0cac807400f1641510002d03100740c186400720201c80865031000180f02c00c0e00ca00f80e03002034004030081c10303c3c149103020b90031a10446c4000e003040c6062103c400c005030a08400b400c0161010b17980718090003111350307214003030702d0003a0900c0c2060065410002c000030018000415603a600c941c000c034010001030004e0000705071100300100305549520742801c3c1f0b46e4807940b02103849000304100010010b4814007408a0072241e0400800c01c0358512440c4641c080e5124005003400d04155503182c060005a6880072083e0000c4000d070740004520b4101001c1c4007040c40c8a07009086246900c0340180403496200d903044050302c62922401c4001d0f111142c00342c800c1001600f10651081010034003040c000c0d800780c0b2640c8901e0013940c00340f025072113100031b02c01241c0042c1e441d60f4114140030001400031505400034401d0180700180080c001b0b08035189842282c074240300403202a5144c0004000519220301e039200340c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362028003 1250 362026753 362026757
    0x160b030a0b041119020102090301110a09080f0c06071109010f05031219050a090815041109070f0e01020304090e010204050f01050309030d0510170c0a0b0703051c02040f120210 77
    0x218000383da9418005000d8840501c1c07880460500012070f00e4405e405a48a003003015000b07200c1c10540141d00965604070b802c180001824450340080c103950700159a01078911940040c0008a80c64018030140354020301068031144d0740c508030326846486600c04a40244106004560b0302401c0170201420f100312810071007900d800c10710048801e0300321a00498001c04040c104569903d40f040001e40e80c1454035808180a80603185089080340c02c1401624461441605150380101d00b5a0030803000c0070041d522070000a0304150392150306409800f40d104010014011241410742c1d40c00c3e40015201000b030780000903500414100518246011401540202424203500310324040b00c140360350340901c584c01c2107000e45460214940d8808800c0c0035000c0c2400600100c0007450b13801059a6880808890074018446040300040c0d10002c9402d0329411039155650314640603140c440c5241d0740041e00362400034181e0801000600034003d0440100070700c1070710641c003280c400e01e004004103003240070000740c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362029253 1250 362028003 362028011
    0x17070801061e05090d05010e1f0510060509040c03020f0c1b04020f070b0712090302010c170c0d0e010b060c0f120306060a050c15090c03100e060711160b030a0b04 71
    0x20000c1c1e00102510351801d400d071a0380c04c3c5e50783d8909106014002c501c2d032010300d5000c3e0010791640c0c0c8247e440d0401d80009804000d102070784a00619030b03005101c0b032103441d001071001d00108065107000d0300001d08200540c5405410710400e80c0414005900420078a030583e8400c49908440c905c01070b0ba001c5000004030b804500b425510345010351a440b4074500140300c03041500c00905050300503503042d40344030fa1141040043d8100d901c1d010f40207020301100600824841c04041d500380500d0054284121080300801e41000042c3e070444c030284c1030480d8612400d548170f00c07903078805032a084051303e6485451401003c0e41d00200600c1c0f030406544268550b0090020010006180c0340c03442161108042c904c3c006542d11350749400b650034510700324045501501c00e0414042a881c002413800b080715421415100210f101044550880d00f14003042c0c5000e4011100140031240a41d007100c0c5201050b1007990440c4000301d8040c0303201d640680001c0c1c18603d0103c10b01034694854032038507405803401d4800300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362030503 1250 362029253 362029307
    0x6050c1209150a05040308030103030c0b0603010b130902120d170c13120302010b040e0106090f0525090b07060203070305341404080106241b031707080106 68
    0x10b01000c4510a400c02801800149000c075203100b01d003281c00442c4c025241540b2541c69140041c80078a000342c050700d5041c903c20100e6064a818881e464105000a08540064502030815409400f191605076400302180c000c8130700b100c07000e2240c1424a8407070794804c842c01e036204030b00308404040130380030182d1228103000115045000c81d04900030b40da10100303040e090348110300e401ca0242540c11b100603041070802c5401c0240801c150000c00582c3c0c2d00030303804d0158101c0400b42004488086441101540345507405411800e20440441901aa47c0c604041c404c0d4070344526414552050500725601c0d0f50000c20004510380c184921904454925042c00126203a1122181502c031140d15564003001211084000c00c0e000300d0b01504100341a03449503440d10f5840c17030020300804242c4580c0304007584500c0c2c68038001800400b19039520416440b801040170008411340d0840039100802c800344200410511071448c41056420312400303690795034010540c10107078000c0071110003001001035410b00c12040707 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362031753 1250 362030503 362030509
    0x6050601091d04170c0a140d0e0a030b07050c120403111f0e031006080709060504050f010b03060d0f0521031603091a010f0e150f01050903070504050106050c1209 71
    0x100f604141c201c18005100c1c421075140e910070384140f009074070b8284210101c1d00200440d00d40c1c01884164010700380c079910741d0382c28425182e62070340700c0030140d120405d004d0a10004400500c0580c000313140e840c01504003002c04206a03c0d00c06152581507007004040740030420402e400d0300001c035000054071500f80d80d180d040202c10704084035070000d006000c41804249800c0e102084541001c40046006211059540b241c00c1d458048900400452030308251001c511410316000c1d0a02a07207604142c030071944c2c030388440c8203465000031b00401d6102010118a01c08a05080110034216000341d01034288114410180d8010b00b40c000000070b0039850030f00800c0503850340002010300d252500c0c00d0119003070341c02d440e00040c103100c8121081280c4500000114640c01413035400d4054070f02c84e110890040c0c41d900003c04201c0c00c403c02c655805103602e411011594460005420940390207003ca0b4116600d40c00090140c45003604000006036020804609a501c1009109102c1c3c0c0c4059507e440e0003403081c08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362033003 1250 362031753 362031809
    0x503120a030c030e0618010513030c02060a0905040203190b030f0607030905120d1506050c0a030309240203070f05070f0206030603150c04090f02121812070605060109 73
    0x1040078550b8505540e51001e009400c15140700d1229025030300103141001c0051606e1200c82001c511943c6030000180c680100b041c0000280f5030182c40b6034100d1441c0340e08010280e03100110180410110382000516500c2ea070000e0340c0074003980d20049109c02c42c8500d00c0000c9400303040b8003900c00e60100c1c8000c54000d1000c1245900000e540c900800c00541c2c9090207440d04900a03265108404005540090302446034846c500d20301c0d140f4002c2d031461740c2c1c540040302c0780c0c046d41c150340724590005516400064040e500481155118403210008014600030820f10b0484030310302c20034000e400104200f111a88041550b03036001d2281045030400000381c6410102e0740812030001d006080c00404101d45035020044402e80c1003081040c1801c40c80d0805015820340c100348607000060382050289610b40c01345000759800c0741000a01c10303c0079540d41407100d1420782c1e100f00c0b81c091350180102601110000c0f0006100c91401010082020b05126000403d56000350f480080405a0f40f801c0150704299040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362034253 1250 362033003 362033017
    0x82a01090804030210030c080a051302061602010905011403070e1f020106210803010e0c1210080705010306031a04020a050301140f010e09250e0f0604060603020408070315091205030907050312 84
    0x840017400c1c0ea24400b01001d181e06418001e90301030008181b042034ed10b0114620a20503200307a0303658204907902c500568103c11414405140f0701000d10001c3e000a00c198000104400005c00300e160041000e5000310258242640c01c20060b5112041805009030140c681403d6a6962500c01d000d144c141e00c8003a01c0d4081800794030480c100032004035019000304403d0341c482c00042a00320300701d4240b40d040d10301001141e20500295000314000002c03a58060b01c15031088940100480c0103083d035010420580c14002881281d00000d5a0303404070341602c0074030903800704141c201403550b200c0c10708100c071203406070059103c03030300c40c2101004001c1d0102001c80c1c80504144540400d422407000c1610f00e44400c0303490341081c030054101004020000001540c25030088100740c2c2d04201c450340b128030803016845940195040b1394042401000003605900701a0108050b4001c00a03c9121590f204080211102601c1c40004c3d0b02106200540400b8003070200140000c44c020045110082000401030244030303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362035503 1250 362034253 362034271
    0xa0f060b030705040306150f122f010e0316150305090f0c01051e030403080103061b08181e030703020f030a08010e130c1e060804082a01090804030210030c08 69
    0x1130842e140d110368440040234007201c100f05a407003600c8594441161240703d00503a402440c0340702402080c110a50008002d64007001c1401001000c00015a503402000340002d801d446203184130135034051a41c8602e03000d03001d05100c222207142000b0000f02034580181400301c40340c00401e20469601000a9420f0400d6028205070381c803010304c03006507001020f60189014401c2800020441090342c02900d080c1030783e200396010003036000c0c032039554450642058049004a000030020035441800500e910143e803031580e080302c280100d117803052a030358034049895485607840031408004040c0c051041200610742c04005505184001c400203010322410312461090741d0340e0101141384080120590440c1702c1d0442e0340a0300d080d948291000d00c101a0800410b0880000080424124480d00d103a038022600b0003803240c20308080d08410448030801c0482100007007103039401c0d5000002c0a0040c1400540902105621281b43d4018060b0043c60b029040c4101803800c00d90b1a44981c2000c0c070503400103880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362036753 1250 362035503 362035511
    0x303060a1e0807320a09180203160f06020303190b010e0414010f1403030d020c0a14030d0c1b060b03030d090c09060b03091903030902090a0f060b030705040306 70
    0x40548501d420000360040149802051400300d21010071000383c41c076262504140d201100b8800441a0340d204c6202e207142d0380076550038401c0080e6000360304081e4040c0c06540b0341c080540442e5001070319000384050908103008260204009452445c000c3e0f070020503060014518519004803106120b122400740c00d0340041d039030603924000340d20482d840111001c0c058820006041e03400340311190803809101e00351407082001c1c03000c40c200306102000014040094011410400b00200b42800b940003070104203514825042020041a1600805203502d941c0e0301c0516600c0c01148142c2c4195103800260008ac0041140501c001c00c400c10044111035401c08000159239a80301e000078110b00c946810f03000d1382402c0c118448103200e02046000121000c1400400001d42e88402c04080c2c0d00084400c030006800c8a070313241800510144080310310074800d01e030014080d8501d5000450000050710780a810598890702c02c00d68002e10310941c8003822411413010309516146078010958403d50000415054403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362038003 1250 362036753 362036789
    0x60801020c0d0c0821060405060102030418180f21022d010e0f07140d0809010c0f02090a0b0414010e01050d1110021f060f03020616050a150e0303060a 66
    0x404d40989111072a141c96004d299001c202149060038801c0d00d1161103646003001050f269800001218216545e2540300070f5100c000e141c030107000300740600c0303415402e145071618030000410300c0e1000300849128501c081f24141141c00040b00c00703011441c02500b0f542c44410070002604030001c014010b14080c14450031444000c2180d1400740007203003001e500c6403243d000f4525080e180030450318181c4607540110341c01d00901e8401c11191064180000c0c080c0321b02000305841039403141c0c1511000d180a070703021030002d1032a03901040d10f4060407500c11844550360362580e10b01c3c1c40c0600580d07500d40c81000101d44c0650504403600001c0700117201d070b184211820000001000071101c0c080c030715101c00810803501c424510b80082d40301c40740081d664140d0034440f00c12401c0ca0301148211801d40d00850019000241142e003800b00503445074500480c0c0b440b0039404003002510801110082c284100b4040039032840c1a81601c2c01d444001c0000b04e03450f00f0610400c682ca441c0d5a841c00205c42c041000d41c400140c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362039253 1250 362038003 362038013
    0x12050703060209030c030a030306060e04110d0510030507090507120905060105010503060f1e01022104050d030302040e0403032004052214040501020304050c060f0a1d0d0c09060801020c0d0c 83
    0x43e502d172a072070b014016004a14185609070388031500702c0d40b40e80c640d60040340901d0208402c443e411600f40070180001d0000c0320303555071766a0056134803501001c00320707003115100c0d106c01d4680201503012195035a1944204410503034002d17010343d12603403407040510004009580300d80d1155414003909042207070101c0056000d030f41e140050801d0000240400c8c0e12000e039402c0000c0c500800c031202d54090b100c0d443c400b0400f0070000000764a4005650007540c1481d040004000700e018802c0010740c2019003d00020500c122000202c600451090f1000110b407011044150340720260041034822481d42417104202d50f40311006603005402c8051400e4003c11b00d1416540c0081c01d9615081070500010000c20041007815030041d801140500e0407200000c4210f01004140d03c00c80700480700d40030050102a03455400762044007840104001c08500010110020a40b1024202400e070f910507454001080940810310410016144203402940340000d04216903a0301d40030300d4a08010003c0109075401030003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362040503 1250 362039253 362039263
    0xd020f040204030803090c010513031212050901090203010b0a1809080d0903050a091a0d0507020106051e0f040513080706110d020703021501080706030b032b091205070306020903 78
    0x400000d10031900c0d2522400c0c18440e90f041115040c05500c00c01c00c11500944c09076042d030340030f030380d188880780c60302c60a543d102c0c105900103000e04010302030300129212240c2520701030075210700310313a5000040119141c010542518680003c2c580079004175002441144c40001904080e010000720200e030100b41c52400c02e20900ca503a0580c02c60500c0d03c00d051b010954044010594802203968051100d612400f40d120141034041e0005c1c07098008014900c50046d0642281c4d0340000580000074000ea070f030f80040307460703d54081c1458a40300d43d032188054403441c16000c24003c0120543e0100068a81490741c11205070503000c02030482d0101041c45010004170b40c0100344000c0c2c1d03203522140c4900310207000c400a0b4210300c0e4110058040c908040b100d040781c1e20b55290403162450010010545030210580040889440140e0540a6106100034902441c0c40d185004000008104100e401980e002012500143c104880c0400024543c402143c0c0c002030700710641c0d410400040c1d9031202240080e02d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362041753 1250 362040503 362040529
    0x1002070b04060c02011202030f16020c09090606100212070201051c0609050f130506070503061512091c0f08060f190923040b060a08160f170c0d02 64
    0x111000003000b044090380b110344401114401c0c0c0b220b280b5104103e0304001039002c125100040303407a02c038001880b8044c8121581c0c01130501801034804503401c8001041c0315500446162030598002e600380303c101c2c01d100d500042d90344a148080c280c3c1c0b021102000809224500010303040040203e03481e0380b18004454904207d18500c0d500300f041c01d40d14035403100030301002c542040300070700d10100140c01e19000c468403c3c0216407050140c10146e450030b100b544d45801c041c04094112210441340b45c000c01c0c001005048803003034500000c0daa880d250724407515140032204440314900d010f02d542c4501e640c01c0f81081411b0140b908100c1803c0d0364200210b480e43c0181607c15a115212070702448904070a515036405607011000240901d681055100c1191168903520f07900b0500c0700350001e40030030030800c402500b2640007000c20100d540d644031010705d08115201c800e09a80c0d412401001400764030944e01d0300030004401c9034a4880396040510fa01c41140b172440324018020500902d00710360340d180c051045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362043003 1250 362041753 362041769
    0x2090d0b0a022817010302090f100f03050a0b0115023403030f020111160611070203030f0c07060f09031103100608010603060b120703030f0309020405130b06090411100207 75
    0x44442011041c440c40040402d00e1020030508a42414134900b018020b606a94014020449644030f01644000018000340380700d461100030b00010800e0b1001d160441d0081d8000d400404402c1607505040f4a1504181c0c000e0080c20000706a070f2100603008202005070290b409030354000c1c0c0d61014440301c09494221a92910307282c100201004040d0404222036016295034000c00000a0701404403d113481015180c1c890702d9003014880f000a01c03582c002c01c120329101d607000b03403c026031580031034a160451100e040f140e010109a800341d6074000c000f000000c08503458003101c41448070070081c0509035540005404410003001480c0340d91010054016070f401e080070200081e5070f5540f2514000c00417400308442a500b85500e0109a00d058081081c0e2040014040d20701e01d40b03182e5088e41c4c00c1c00780c580c00509041c0c480c0788180141c0d4440c840c0764858185409000c1200000d860900040d0340f004101a104103a00020311000c90081151440d0006050351002c404032418401030303281c40f24503072051503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362044253 1250 362043003 362043037
    0x50f060304060615080f0a050108120702150301060c050f010902130c0c1505090c01022b1803080a1106090a11030304050a091a0d0b160e09091b030102090d0b0a02 71
    0x113000740e0301101c414031462410101c1c50703041e11307080d00c03450607110280f0440c021503005c00d5014031781142640003010010f100800c1d44a40503081a00900d25400c243e00c0301002c581442c0554060000c06c3c404d4000c0019910002c0001030026800240c2c1c98a4010000d9a0aa03a0798901503849010316180384041d0380050040d1034001000a078000a000c04803180f81c2507000d240303003203d459400018407170b1905070229034588008020711658030b42d1284504640c403c02c1340d480c0c0d0281007805420070220155000d0740c24140d03a5600c494025026607011405481250f000c041002500440482c0781e42a16503c0100813101110410000e403940c01075801240c1e009400460001c0c3c0003402d60311507411002c050519405440841e4100044618049009003d210500700001d540c07401038200004ac051003424160041c210440110b10400c030200c50542803075020b130700607501c1454400c4100c00e01e800110002d500d445059800302c2d07031810104c031004090201c082c0c0811034190701d0340c0644101c2d04600302044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362045503 1250 362044253 362044289
    0x30a0f020d0e0f010612060f0204050607060c02010b01090605031b1c0b091012080309011e0509011d03070201050d02070506040506160216170a121215050f0603040606 73
    0x4014000c0c282d42a038588a90b000140f8600c0042c044c036400c075204600700340e01481035900e4070b20141c82480c0360040c0c0b50b40d00300f20200da107a4540c00584101801085c0006a0303001c00e0302c02030b08580c1e040d0121410301030000c8003000100c0d40f0904995014034201481001c0c031940b9003104d4554011040c2c4144a9104004484032564090b40326501c40c5c101101c919419031030b5280c1c082030705480d5000e4554071103040318042e40403c070a0802140c10918100000984411003000c003c1d145100c6160044c01607182e00a1144100c3c09001d01c034174000d0a901025915001102019540d105204000381800400301d104040240c15505a5000503044425a8800d25051070700c40e803503c2049480f40d81d40c40746080264800d80c40040c0040d00c0303940302d01d510303036101e4201130201c1003000c000c00c43c118031440703804051030010741c0308180420000301640f03402c501c40f500c0000d081e041d1400402c3d010003d25451004200903555042800349007081922001c2d920380b50750030084040c10a41d00410704070300001c1044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362046753 1250 362045503 362045527
    0x12060b0c010b10020c092221031505040b040902060c0102070507090507051602190320010302270d0b1e090c03151e0f0103110603100902030a0f02 64
    0x406000300064020403440068900300156401c11019400040e13102c5194400e070750420803009a000803407401290396040400030314081c1101c1030042100d406061480c4907070b031011090040380000405040500120407041c140c4941100d16105241c03145845a46150783c94032582d1004010a4010702116600e5450741c1d2a1400717944950401c4402e807080c200002142c3c0041c0c0b190a003e0f01040d96064a000e089a0422038844210001a0b921410802c00440e03096107182c2e001e4011841070164a074080e451a44140c020072100c00740c241410f0040218202c008544000b01c3c2058400c4101c1c4070b04c901400c0701285241d410860002c0525080700705202c1e201100849119842030142007203000c03551a10f0301e00303444510341c80c02d4a0700b60f40402010000e41e0040f10300513074000002158215040d819082c17400110307800b03580e102552052000103100703000768140900800a01503072400e146041100c02c2424a003810301c01c41468580c040045034820341e25401010019480b4071081d92110441090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362048003 1250 362046753 362046757
    0x20f0c0102030c040e0f0c0d09031214060108011d040b10080d05070b060f18041509060504141501090905031201030809040b03010b060d0f02091207090c03060509070f12060b 76
    0x1417150200120350000718541c0d2208102846400c0c0c1054150070900f40d1441040035000810040301407180c4140c217030419200d42d1003a04458901d4032907014003070a000c0d00240c006001a0006d07070000b07008080c0f0907100a451000d5030b401139800b182d004c1669441401488443c90720b5080041c1710b0007071010b030301c850580c01000707000c04c1740c00b03105591200d840d9082008980e1110416039500703c0c103072030125104240780640f055030041c0200e002a01401544010700210303251610212030b401d03030390b000340428000041c0a01090040210091101120f2251404c20608052040254041e200c1d00072408012041c019540c5081942854601658407450f1080054115080160080303140a103c20a54034050082000d024800f8102d00d16140322214084058491072050110513134080205200a4680040001500d4414030207403821500701154a01036401050301c007810075043c88414070042e692002d500b508180079040c4070f2030080c801c09041d204c41401e0385480b0001403030008001604a20540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362049253 1250 362048003 362048009
    0x804061401140607050a02060c100b0925020a080a08090d1d01300606080f0105031203040204230601020d03150b03100b030c0a17070f03020f0c0102030c04 68
    0x1009102241540e03840c1149103000348500000000c92100008050400000030107915014000b580c07a20211500401c000d540404d9800c0c8007984000c0010046554074460009a01c108036411070303413800c0580c005902e660441c02c00d0164600380c0703004d00098a000300440b003007642c0c4c0f1050f143d840d13003501c400250803000b04170381e490082c1c003c1c01c0b0100d1a00303106028140240101c10240481c1d64035180044072a42c25203040a54082407500880c54030001c4240c0285565000300d40106409003440340052003580080d259848440240d00140065540441c0b0108086e240c1c01a0603166a160f00029018100c022000ea0703860b40304030074000024002d543c96070700c00c0b0800c1e0200c401c10a0703290011011a0503c014018000d22582028007a00f6100390045401081a0008050341d98603140e19090700e50090b941942c48880002d0078910050700481056020040011554418031380711030060100c04450404800b01540000c2100200b01c582c41035407074407807503100215140c0c640460f40701d5060340140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362050359 1106 362049253 362049263
    0x2030c070909030e0612040204090807060f0c02060c07051b150f0702011e050a08100807060c150b0a120507030b07080a060501030c050f07210804 64
    0x8600d0000c1e002071100041d205000e46000b5000741001c44006002c1e85082c01007500c85140112840e601c1a010780c0c0c04141c10b0380301d00e4400440d101d00c1c400102a5450104040ea1301c648a5202c0103d24825400320f42103600e81c81e0366100d040c060440020032580c070240c450083c10100c91140141094003420100d5010044003d0740c0c01c6030001002c200e4414001725806e8159a0300401d0343c0c69907855500541c142003d9190024690320510401c403080c03140f120041502070344000c001000601e0110150340d106521088010400b1340b60440949140c007110900c13000c041c14510610315481c1004140000d1540f401c94038a180a2040a0944e00e50291100010108101d0b22400f0b1142c082c6544280d17251400100c034404842d101d800050400d4901100c1c44502070b0080215002d00c9142003119868001d2480c0071104c20201c0306103440204014410913a0994109600c00e0080e0701c28 = true := by decide +kernel

theorem cover : BRFrame.Cov 361870503 362050359 := by
  have h0 := BRFrame.cov_init 361870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 361870503 ≤ n) (h2 : n < 362050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
