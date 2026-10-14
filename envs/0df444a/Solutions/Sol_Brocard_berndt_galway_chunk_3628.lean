-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3628
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:09.376076+00:00
-- url     : https://prove2.me/submissions/25c7d892-0a4a-4acc-aa95-704e51c03ce9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 652338129 ≤ n < 652517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 652339379 1250 652338129 652338173
    0x290a11070c14030601090603020310050601180806060f011e030908130305160b03040c091e0e06010510050a02070b18030a0f052e051e070203040312050a021e010b0607 73
    0xc1036201b40707445030b4400c2c0c9401500900001c00c400c1c83c520300400f0083d05a906000c41c0d10780306000300c59200001c4c03028100510207403072181030400a00c60f038001610085414401c40301c0500303803400c20640741d0003d11041c41c640414640911700384040c080c0f2070700c14080d0356001100004424040c1c002040d03502070031004d0301c0540c016038502d09a07100d070109070340007464a44103010070400c1503103540203103082c1d00542610044444100d200142281c500c080048626040381004006501e40750a00c01d1811420f410000c1c070b4071465101c025203d10311030051240d03590010482a1b00c030a00f81c0080c124245000d401c6406100c080c1c00c042043c03645a4808540b2840340100c03412241c0c82104218100c80c840100b5251001e45030b82a06026010040c803d00398480c08030420320400070102006809000d640d0069969242113040c54500408d1104a44080c81010800d411282e680003e9000c1041c2c2c60304803801d80c1801c0000d08a014024007045103600c42c00c081800b4061054001006a65200c1011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 652340629 1250 652339379 652339381
    0x203480613120305040c0f0609091104060917031912060f0501020a02010336050f07030308071d2713030c0210091809290a11070c140306 60
    0x1c1c0c24041044203400041c80315440e0402e010415000360461608584145401d200668454240107440398050340031a00041814404211541140c411100103034810780105240609084000c0e001c95440d2040c02c50102c83c40450040c2503c05009031100020108002040003c2d813820060030403481c50040c000e994a40400010b2220307010500c80d0403031744103801a004480c01c40d00154010020303c042020307809001240001a1145244400d0413905000403005411489081ca9031400c514090220820740c056501840800d8009a8a0b5403010a80c5458103400c0c582c100c01000b481040b044154004d207140596814960703000106881505400e1211041d650b0351000c0024094445100a000b103282200307448051f007045c144c1480c15070124103294029603034808414440b00d201070700c042c1000b590f0700350040400250034007001300c4452200401c2c003042d40d40300c26802224005481c5501d0b880d591070a0326402c40081013500d09568002100080040e030750300b6240c603070140380c108140c480d009000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 652341879 1250 652340629 652340641
    0x6060e01020f1e010b06070f140106060212030a020c0a0b01090c030b0604060e03030f040f03060f09030206180c09090a0303050708250306030f060e1c02034806 70
    0x107050654954004001c1600349480d03c3c3c0050300809540207400301e552114100e0304aa25507400601000d0300c2102c0e80c080c2c034403444c202410481545c1606d540964103041d000c001c0c4603400115401d400302e49600240d80c0307483d40c407200c90092181c004400d185014807040d140a1046501c0d00030304032040c040007400615040d44007281200e6030f54912540c0001d0500080c42014410405400001e50240803649440c0f1401000441600944e02a12031510740138000e10801c005405400b902400a030810710079203e0130780d030194503900300400f0040f04002110300c01c43c45a600704003a54980001400d030000c141000c03243e0756254031400c2400c0d000300e0304080200c0c000c1c62285840e140f0404120304846c3d4001542c048141c0c0d095581c0d1700e0801015200e290100110322043d000060440c03142c0c07030004001c00c402030031364240f95880420003a031490b6220301c01c40c075680210844481242040e40c00c2c100314002c80100c00c01d07082c040304c0c645071903400300c1d0303030090721010800700142d451611021140103940fa0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 652343129 1250 652341879 652341883
    0x111f0b01030e120d061a0c01060609030b07080c0d0905300a1409090106020a02030105010b09010e090405030f07030f090b1626210a02031003020607081c06060e0102 72
    0x315410620641c412a005a00c0343e01040162908a604442c04150240c0d103058541100c0c0c480104469000000540b00b071080c90709218400045c455410010302180c0356454901c1c0c100030041011042c040c40d040000c1ea0382c522001182c0c00c81054450410402d5110300b4010740e900c038549620343c0c2005854007601e0614003000303134a0014410a19036985040c134005801c0b183e094190920000d005024001041e003541c4903840b0f01d0103801c082d401840ca80350240105825510103911404c0c0c641e604004440c030a9078046201c40d00110196260000fa444520313040d45148640162400c0000e00400c0c4101019070012000e03100200707039a101544a52102081d851a1141401c1038104004814402c0d00091b01d5646a01407960030741c5584000d104143e15401c0b8580c803420542c0c00b000700e8406141400505805001d0f044440c86404505501c0c202500300030501043c0006442090040f9a0034200b200c002d04540704c040303000200c0d1708882103203004640074110900408000c50701d524050120381d480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 652344379 1250 652343129 652343141
    0x318010e0d0e03061021120e0916020d05070318090209180c07060c1107080d110601030f030c05031c02040e0f0601080f06010c05030c0304240c080a111f0b0103 70
    0x308a07900c40200e8640010851000c100705861b50384a10206030078008500c58000681050500313884040381e0442030700420050040003401554608600d20b1082c0b0010760001d5840d91700e00fa5410720641d1550310b03040c2510b9451152101981ca2401314401080c21000340c2c000c0c003401d4501b550306a844c07501030040c12043c1441180d1700c20b12030348244920400b194098010102415990900c8403200d10785c46030f4a07060600c00c1e040100c055006803510f124050307104800b809855841000b92500e541560b83c1c240042103400c0015080000301002c46040c000144200c40100130741a0181030b03615264070fa041c010390898030500300c11940c208000784410201400300b921550050b9903601050b5a4000400c912000180a01d41000010f5090300b0005e14100000c010312000000110348076460143c0000011441c00e0b10b00e000c5032113281d00640c0d099040300e005142d80d980004011703240c12900d207007104c40c7c60205c0c6a11016110b61a518040542102c0e2103d001a14015046c4100d20390a00150103442c0c6c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 652345629 1250 652344379 652344391
    0x9210e01170f100302090a15091109060a02010204050303044a0a06050d050a0b10030c06122a030c110a0b060d02060a08011805010f09020318010e0d0e0306 68
    0x2468500045105000301c002e2940185441034442500e81c40b030300441e41e03405089403c6100556180051650303060001500c03c01400c2128051006000300303400c00200f4010340300f00a00520010400401c2c441c000c3d01520082e10018089946890b9140c043d9000000fa91040d240d606102103480700d500e8030a110344441605170340402030300d14a0b103000d60300c90395000244080340301d03507a924022449950ba10058240702d401840248140d07181820301c48121000079041580b480d550003c20000180405044003c0300c0d0305041c8030010505600c038a030041c1c02c0c0c13842842d010799800700028004000401e4088103146047e6810041c0d02c580036015607507c0420656a011079101042200c0060024440d180d840900581030010b1090079501103442500103034140340101d0440300050000034a030307405045948944500030302103545410b00601c1c8603201e0780070b0750520f5074000001800030078000b50301c8190908d25000801034003095840304c1e612814900d8140c0d001400300142d00b00d8610b000180907000319 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 652346879 1250 652345629 652345667
    0xf032d0703110a09031202071e080c040207050c062107213606090501060e0a090312270c18090809010c0c080609011b020f0a0b0a09210e01 61
    0x1e0441e140c01c451006a15011ba00714410b82d14089030921407003450600b50581510703e0588075040540c69803c2c1900d056296014610600500307000c240e0015062944010545000e99035181c60585002e04204010b224880c4280b201c0a00803165444040b0114945164a03d6058500c2809001064506000d09540d805219050704210354550244074403002c0c00010200c805615240c0d0381c0d1013601c01342d41c0151280e0b5540c007410040000d44400240c1e10450501d401c114a07007c1d0369010748202e1200c5180b1500e203a5600f42501c4120402007120b08084010342c2d15404602e031842e000791286604e01500c00c0e09880c40c0b04080b407140540c054195010341c000d259034102490750004503103880b6081d0342908c00c44400e80780000d403d101030080c240601d403c1c03c000705900c0d840c01820230002c0c500403050002c42d0300031015984644004100c03a4503056010520742500c1d00d95040309809410340c400040c100140c45070041c00034080e454517004c901c102c65101d90b68504c105900550362007400600080050b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 652348129 1250 652346879 652346897
    0x16030905070504021b010501032907050304080f04080f0109060b030a03201c030902030106240c0303020f131502070303080106230408150603120f032d0703110a 70
    0x900d450b0300640301603901907484c0a40d060017410041d095450a0340280d52180c03541511502200002c517100c0415020490600040c0c104440c0080c441c0c8001840508800c4003c140c2803d11418017080360000c00c19a021600d08a6070484190f008029440c0e0072a4400d207000e000d1302072414045900c2010700d415403908030701c6500d540180f44044071071551542060044614098100c811110000d40c80071040d640060406207d01c141421141103400201c20420341c03040164280a92416848481e403540c42d1042c0c00002602d004d401900480b94505141c0b140414100401c2284c00c2545044820007030180f50050606030003a40c50b40c41500020f4005144a0018080207010f0588a4110302d8031100d0b01800e0310181c40c14040342e4216401c0006560002a880803c01401c3c15400b40c1100c4110090803d450800e400d81e105441581509044007102000203003110007001015070f001451b02c6020540049642c0e002c00b610b100480340d800200c2d207814810400070b1482c0302920000082602c6030740003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 652349379 1250 652348129 652348139
    0xb1c1506140c010b121b03121c0b0406090207110d080301060f0c0602030c0406020c100f0c0f0503120403122007020d051203010906061d090910141603090507 69
    0x8207038400d00900b10990340300c180f180025124507000e400095400400790105c010029032181c214114a0300d507034131a6111601d10b034950740c106012529a1000d0a1140d0305903890350000502900c682c03940a5031062030000300184013842034004110041c840c42042c5400500c0c0401c00005080964003d010342906000601496000300940d40401c1c203203050507100d0100036656281a684112248031860308080303020801d044d0100085101541c045452540710607c480005000031400001c0c9020401a0b5580905100950001c0a85180c04c107065a0303855a1803102002a40e80c29502180080c1c0c01d0f85013189140d80d01d213324145c4080c500000640c03881ca06018a4080d040300400740d9120202021000009004001c050a50300d030301100c0c3c54896140c039500cdc50440f50709034071a1050241040e03901c0012130f130506d00021850421070b0004010344a031f5907100c1c9080182c107811007115203002400c00d49081c4508485100f00142101c680184c1c150140031402d41d080030f1001484d680c4089001d100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 652350629 1250 652349379 652349417
    0x3080315280302010e030303040f0b13021c020f0a080303241008070906022b03020c06010e01030b01150804032a03210509030415090b1c1506 62
    0x8041001040d400500c9006201441d204112601d2072810070680c0c0010000c44d6080910b42c00a0003048001c2d44c2185803540341c1100745024084000c2c03000908400284400040d151410146074002e01201c41d0f02c80c84490b038a00809200906a00c01c03100501e0f101c00034903143e010306003622180c00256045840d2010310300569030040a170825000080d900c10300e0103490341c4d0f60442c0320039182e81c1d5922035410f101e03d004d05a4a66034020300c086410510b0200a8425132150140d90100e060030700851100500c03070110000e0040c4007080e401c5025034800000c03660303c1341c0b9045042e43e01940404d0340c01e076652034000d080f00200b07400550105100000050105e40103200c00407901d1036100321000d00702c003517021800303101d000c0c2c10048000c11140e00720984030702d000d40c15401030750980340030800240c04d2281961b6500c0c0070754820500484c1c1c800144c0340005201d940501c00034000110102c1d16100031400000c040c08a80c41d41d4140384d460200d502070700409201044c401c942d02a280c005440c00da00340108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 652351879 1250 652350629 652350661
    0x71e0504051e0c070602030f060f0f210c1915030c0f1805060310170a0c0302060a1413030516050f06090f0306010305030c0d210203040302010b0901060306140901030803 74
    0x82c064403400d0001c4401700b02580011407181790340e40c004030b0031860710108001012030020300300d50040001001402c025201c40c40e012142040d54421000035010782e02200d854025041501900410681c2000c00c44160112024007030355200c400c00c0144184c10242101100e079003100704000a20701044001101b40038010403003404840c607500b558100c1e01e13140801c0065000742c0b5102030360992491308001c006090181c1003007100204000d40215149034603503202c1010a400f01900c01c2d440011909401c502442c000910307006a043d0480d10f030040e00704c01041803101c9110545043c0142180710340c00d1054203d100c800e80c0d03070082002600701701d010240446600584100c54002510501d000030568040007001d000b144540000c40c2e0b21078412a150741000d01c0c0851400900044450f5841900b00110542c40c8407501d0a000607100da80380d0034103d001d00b007903550f6560404080800850b5555040e0001002c1c3c44103280507403c050002d100b40000c07403500b48005001c1d04001d04c04104203c082d500c0c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 652353129 1250 652351879 652351891
    0xb03030903011b0f110703021215070807091e0b03060f060c0a02011701080c042c060103120203161202210301090b0105070f0f020111071e0504051e 65
    0x164103103408003010900316142c42400e80301182229801c0768100f03500441002d182041c07031030110341c08200c02d080f2507510001800001c3c4200b03030318170a02c030542d1000c02850042003140001400981410036003d0001101691104000f5035401c40c0886d0144c034010b84e501404d003109122010345071810711110b000e504054640780d88a65040c6030445141c1d1414040c0035808000c00180c003402540c0e200252046a00e1600c0e400d118401c1740c010480d80c8000305034042901001d0310042201003070409980e59103114008103059850102c4440d044c41c8400240c001d06883c440d071081140c14415110590352409502c484801a00c1040d00810015200d01c08940c600b001d0740c01141d0000381c001c0c000891005941d00c41a0900c5d10100c0100882c0c0c11502401050210030f081c00c0b46091203139101c01c406d16081242c080d2128a80038030890031644181424440700c4a0003040d42d88203500c0e43e00c07261307000089031881115440c1030340c1e02007960724141c401c0c0c82c010304c0d05c1009900c99104104001002200003015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 652354379 1250 652353129 652353133
    0x3051506031e12071109151828090b220318030c06020607030c0c0f020616120e1207080604020108071403250309081c060510020c090c0307050d0b03 65
    0x3c88200e121054018040841c80340e1340081510305690184110600c00414120300707003840b030720f0341c0240361101c000b1655260f40a0010000d0765a401c0d02072110f0200e500c070340c001d1710041c9480c0041c4280050b8000020745201d02035100060701e407801032003800b000140c05418811031403500903000a000e0608160020070700c91980180036625281c455007201264800c1c405031700160200314000342c0c18481e0110211140c10101d50300315080d111108030001c09100217000c0c4000103060840900c07051000b841e00f50340f06403880003e0440c44002000c1039812410a03000c2c0c07040690b200a0b0b00008107103c2c1c140c44188009000c1d0303035a1030300110b60051b40030b80403606011607041103a290510910081d8891007090104070522030180041a0784143c030940c0c0c000400d0301c0c0c50300700000030310b00c42d0490348021896141a01041c4501015038005c1455600c110fa001c840d284413040c0c0c41750042495a69408212041541c5a5030104030940910003141c062000480401844040104c2c5500c001d01680380502 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 652355629 1250 652354379 652354393
    0x50303040501050a1709010e10091109060105070b09010c1206081b011205011e06020c09010b0a02152a0f0706090314030703051501030e1b0415030c03051506031e 71
    0x742008208505540309041e0340d44a020360008e5100805c00c03802c540031307010020040c402d03075516950b1103002d180c0720003072160030b080b00461000da10440075520b603d50498085822400c012503120300a08460768154003042c070b050740114800c81704c0d00c5000300301c56004009d0000c07410350312078400c480c100710021641032014064940700d080801d4031a4038041d00c80c0440d04101809944907024410b40310b5400142103501c039034000e2a0f00e03240d0909060466400c00f08a41d00c500314840140d00f00b65260041c1509000f90310f0801c89800ca0070090121807403504000b403400042140c0380c0911500c601e0b28030802c070000810041000648644c4160b11043c0203281c15050b10a41c400640d50702d43c016510b40e00001d0315402171214030250a07200007850709003403c00b0401a4101d044960f00e8091403000c440c1d442c1c078401402c8026449a41001d240c0302c1000c000840c0c580c0d220f144c080402000303400143c503a03100352400a03982c2c0401000c6d05001e218000c0080940c41c20000e41c0301c0c44451203880301e58403400340e25 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 652356879 1250 652355629 652355657
    0x30606070c1206110406020a030f110d0905040c030b01020703110310020703020c0f01020d0c0b10050a0305030d0b030601140405070e0907050405011803350d05010e0a0501050303040501050a 83
    0x4054007020380207141200c9500d40c40380c1081030503142040c0060b510071904002c204132464000909582c015410b0400f60407141c00c0b50425a401d00002e05016242d000304403410100a03400003c00e01540d00c01c4404010720048007100b10304480c030349142140981d101a406101003490000c281805400080440d20140a1914400140d80000d1b6003200544c3c02840600054900790702e5500c0100002c0c401898440200c05005060b00c5c5546005801ca101c182e001c0392914480c0c40000d400380c80054594840c1c1039030f0b460416660351106d1000c507101494079100100d0741c58080f40b154126800110903203110310350181000010f1a01901c0380d424019880c0c0c800290b0b446640409114100689580e9291481d041c00501544043d05400d1003103d00d020003400050341010120108202615101101000b24002550404940c101440034001e0100f801b4003401142d4210905941e400f5501295545400d24440140c40003805615415007040c0010b2190b07500c1103011301070341a224078000010140f02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 652358129 1250 652356879 652356893
    0x5122a0d05060306090726151f0e0604020c16090506030d02151305070f08010204031208060d020f0307180c020c030d0207060305181c021b09010b03060607 68
    0x415250104860110305551040498428180c0c00442600600320303d2030841d0049440b400b15018200070241491520454440514141c500445592048800c000641d40c03114480d040c00305e8441e120005110000e001000e009206a0100d80303190021001c13545070380d41040040c0d084400e00958134440e000903c45050500103000e0003c00d041c4000041e02d0402005060410481052600a56002c40e000343c1c0681d20b20078080ba4007a03030124140d100c2c0e855510305641050150b85c0600c44082c07410002180054040d0b0080088a120b40f4218414900c1c0706c0064030380d09822140c49500c204182111805410150f1623145c42c118024242c40100380c64070765054102814540c043c4086035280300300c0c200250100300700c149075401100100401040c10b40c00a41c1c550050241808058507600420518820004600501030707111050b00c402c0000da400c2c5a64020305008807400501ca5440c0416011990800c0c00e495800c0140a000c60340c0e0030007160b60f00a0b403002c0c2c032454021004200400100d004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 652359379 1250 652358129 652358191
    0x503030a0501030201110a0803061302121603050114060d0914011d0607020c0913060f0207050d0206060108090d030b0d080c1605041806050925031a01060512 69
    0x454000078a0b5040d4000140400001040c400181c0d000c0c40082000ca004401a603911007012a030b01000c0c5902c400010020303008030200350070f030550941c0510000020000d0300a0340840707265410070180e07076903665000c80da0b2982100e1030781000e0b040064485c5905241c01801666028170b40d0050f61a41c400011400c4403003441d401c20000301750140c1040f00840500910b0380105891000382050901c0c100003a0604a000e8840c03450a8104002c000411005412440200c24002c00031526a04242804ca85031444159010f00600800c2c000401d158080d210b1039009925a800518400c1b5102c48254020071968292a600c0810004154001001c1c00c0c014440201c503003000e08207450740054058001402034001d203104501b81342917120b0b01000e0010001d01c00e500000f010800e0345441c8216400d041c3c00c3c0590040c1096a00b0900340741c91030b17005011b4200ca02c605480d0800050070f085004040c1401c0c0250300025804100c3c000c0098101598280c0024461001c040f07030041e44100300d80c075008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652360629 1250 652359379 652359391
    0x50109030b1312050702010215061c030909020f0712080108061503070807080f12041505071e140d080606121b03010906091a100f032315030d0804110607050303 70
    0x1100040145c03c65030b060001c0401c802410070914960300705074000804040d00d13a05881d000c11234811040c0181803140480500030004240e0443d9a000d04840200c0c4540c40b0700c405803024803a802410ba51107100e080f865049030104800761003103490f1044141c2600301c0391141030742e040c8503006001ca20340c00c092103680300615240004220310420b42d600700d0b0418044061803002c1301c405100403c02c1d900c0079031050141d2407180c42c1c5a0b42e2180742e0303e010b14a0801c41001d0b100407194020010341007040c4054046a540c880c1411105001440001210003020850b6815000750342842007140280742a07110b05e030410b003198541c81c80fa0308082e0042c2c19540090b4031401e07009855003020010320600744110301d146800501d051424901c000003244080034618490780801005400c0c01e084c00b80329070700c103a180b80d24540c8083e4010034001d00ea00d10b13480e020745e0030402075031120011440a02d00001d480f0464241a2200125591140c40d1402c0340200c41010f9500103004015034030001d10184001c52003030f2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652361879 1250 652360629 652360637
    0x903032d0b130f050f0f070509010302071509060b04060b0a091a090d030206010504060e011d0604060b0408010b03060705070b0c07050a1509122a02060702040203190b0406050109030b1312 82
    0x714080034a0403174000301400c0317000180042c1c820700084079800740846002c060300b070070050795034151850140845a04144089012881d1140710020400f842c2c00c00074003002c1c02c986c28040b260325105481c110380318040101c40443c0c02c03084100304c8414031020181c442030040400030305000a000c00728600404609040b80140c215200502c45854180326a0002d031124601c54100d80d07050500540d0244580b10100071400588400544103581d60303001a00078001c80d140c3d0300d0f251560341c014140680b06086040d440f0380110380020705454030034000d445020f40c1002d0b41302d0554031107245103034240e404060260303658040d2050201c085040c84408004005c104107000807480c041e424071040480c80c418888080040780e00c81c40340d03c50b602c00d6413040c0303140840403042d10000142c40000d00e070344905100250000c0c008020040302040a000f00010034107500720074807803030a1800400c42103640902038980495843c10040c00401d0b11591503650224119804ea1240b40d229260b0308041488818100001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652363129 1250 652361879 652361881
    0x150d1505270309130b030c0307080307061103070e1005090a0b0c1b01020607111c020705011209050607200f03091306080a03230408010903032d0b130f05 67
    0x74109058007404684001c0186061049080020f801c8000f940d01c4070085580341c0812100e41e42d41032050403030310349004045071100b50b55550202d0712030700040815a0094a40b83d02030411400403412a84986503503a14240502452030800c20045000442481003010501003003000741c8402c452180505000f40c034140e1500d041500540c601600d403590211002400e400e1504640d0700000c49540107178503820a0461240400800ea02d4076480200c0148203010b01c4148070411500031070f0f035a0941d0001c4c0e81e00c00c0b1001c109091034040d07a204580040141e8010380018249610442c1d542000b5040300d207030810484e59040006240107103000310001150800108900c45241540151884400044060003181c0c80c0c08903442d10380e001590090305000c0c2c82e5825019a0b004660340060640c1960300a039222601e82e034085000304a0034508a010900d4103892403211010701e80c45004130140002c00310a1030101d402c8001c09480b0040500e600003200101000088100d405100a0300840080c00261 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652364379 1250 652363129 652363171
    0xc030903040f0810111e0a1209060203060a1d0a051801021b0c04140417071505010602060c030124020c030f06040606050f01090b180d1118150d1505 65
    0x31115510460002c00320700b0811120f59008481000006c0c00241c02d0041d2a405509400c0d90003040100261105500d003d0406c0204200340d409940115001d80e03c2018a036200c80707803058500c2c0041540320008000078000b400c050243e402440d40304802190803060000030402c11030030783c1c01c8010401010502c5040c0c01540b644100040480610112001c6c1718514002a0030340303500b1005440a0301c80364850042d030001c04000c2e42150006a4031441d80c070689040c032040c40004081c2030003964018000c1e60b01050703074064700d41d042d20705031501c45028030788003000741d1a03518014076800f01030403e60240620300b2165030390501480403604c03100000360190385460300d000c4d4225042e40c1c0145200c3c0101703100400d443d0364042503a0307055030340f80c801c002c0e42e40300d80044060068110900180c0c4c810140c09580c410000181803600c030a030000c5d202d1030b80c4000e07000d0919034411b0044807604c0d01a41029070480141c40c0c00d048145043c0d0040702c40c0401341c0340c5c1b40300100c1501c6003103e04510703134903401e400451 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652365629 1250 652364379 652364381
    0x10b090108060412080c040506030c121305060603030a1e1404090e0606060c06060121020a030218092e031a07020706050f031518040302011a0a0e0c030903040f0810 72
    0x1c2c0003d020310741802e080c40d00802046c224007031805501d025100110000344046081c03030445118030902204044149804000d002100810203000c42c0c01e402100041219410008143c030813507c110740303d80c50740d041001d1074048802e000445080801030000d0744509680320b8100100094040c80c20b010490f024046808da24100019042500500080002c00010030300030034610b8000b1302c01d2a10742509104c4480001d540d00114482d070038aa0301c005502100160076070f0050480302d5800101c105c0d095910802c000a10300101c403404442901c68900005409800300d00c542d2f00102e4941103541c154407616412540d0300c03c0c1d107044028001c100140042542c040003140d004000c02c1c50810325100a901d100d00c0d82d03001c042d2101c140f940c00c582c0e03800025911500e05c201035504102d01e079a5a440c02d403d001340039000e180c5602d100c03559004410102030800140c05400e6901c03822a0308170035155a203403909507920041c6148541e0201307110100e03800e10094080d0000b813095000925021155646044c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652366879 1250 652365629 652365653
    0x61902010e160b0a030c02100213050f010804020f0402030606161b120c051c060203070c110a120f14060405030a031d100b0f041503061b021b03010b0901080604 70
    0x208150b1a440700304000c0480d001102c0c1607900c1850701190a000c1010281e00d0b004d0701514002180e40007140301d1581901d04035203641202c90884011100704180360054a6140099030f010b500b20003400d9039511141469001503800c04130107841e003850190442c00100c2c20701402c2c0c604070307400400405060402e58401c1d11b10b0010300303141e01e4540da42c010f5a0790742046515403071283d18016040c02c20b20740c12800e501d04100e00300c00c0d00013905558034a002c880040c050500305070121204048010740c0720b01800d10319801c105548003000103c005924136181c0e041040401c4004407402c2c031490701c503500c400c3c40600c0541e00a40c803601c000c50300c411150a000d4155091b8136102e81031100442c04801202600050324041c0b04078004000a1480380440400c44140b0690501600301e82481c14901031440584c807000200c034021502040845400682200301c412241c3e10034005030700c002d03402c10105850307a541c0c10920200600002e4682c0000c004981e4004003644040340541210003000103010b10181c1034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652368129 1250 652366879 652366903
    0xa030803091b0901210f031e0207050a0306021b0a080307260105010509030f01060f0504060504090309030b1905010303170a05010533030103050c100302090901090b061902010e 77
    0x1034403503500140400d01c40700051090440040c8101c0c58010401070141d4174070346594001014503c00e0070300d414040c0610000034014000703241c5440c04100351a04c0407510031b0541d9030051040c8145440e50300c0e440f019400c20070403084440c4012179010b00c4660200840408284a050003d07184c1c0382c0070002415054041201c0001d40c03225500c24070007030f08812012815150700b402c215441d40c03003800c0030a10300030101c0b6152190307600e03041000c02e0803035a80309107008546040f142030014070b84490a01090b60020b041c010041904141d042c00001c2030b140310242d01240141c0e000203e8040c0282410a440e001e03402030300882e4410b003281510020294145510188404040c03040e0751400010500700c01500080034041e080c401010b84000c01a070030072601d4450700325040d45d00c0b0350b100e00344203440c0c0c00d440030118030984442c2c5014940314064000d070350350310000400e44802030303281040f0702d005081d15030721980e4000301c100310700561400c980e400d030618949590f0000601c0000012607604c0c000041040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652369379 1250 652368129 652368163
    0x1309021005041212021f0b0f18010905091005040807140f0c040b0103020c011109040615020613031e030f060f0509060d1b0803070516080c0910050a03080309 69
    0x1050052003000075803800f02030b07805118142c40000c801001c90404100300c0303400014900c034152024400b03c081d00400c104000c101c2d40c00b40c10100e1300c0100406254140c682500603240580104004c0310304d40d00c240d03400711980c401c0d03d60100e0a0001181111000c50302151784840102c1c0a00500045017003292115039204028903c5101995045684d503230038290740d9104580350b0740d03502c040343d100f601078600001c00d61009210540c01c40c9a5041c003074201c1e02c01980111300e00840014010302852441c0fa062807190040c00080d202c03031413000520b041c14102034084c40401200102544548201d00c8400e403055600001c100c440c070140b0f5001c0e03070055404442c0015281400344020703030380c0011a80e003100d022a0040000307586440c20700d03841e02aa5141d61003010205100107581803002c4014920a44940305880030255854020a220b4449001c0d0080ca40d0144e24030740083e080400381103800c1101ba00100c08219903d80000d84000820707041150709101c04807e020650b41e007085a0000340c110554 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652370629 1250 652369379 652369387
    0x90c03160c02060d0f060b040f0306152711120a06050a0501050a0c050114041a0105030a0804090f0b060f120a060605030402090a1e060e060904080a0e010302091309021005 75
    0x81c40ca020700f802102d4100e58480b00c10035622184e0f401b03100181403a1031640e40f980d03a1218604c03100d1156100a80303160b0b0600b981c10600c00f00d00c0c201c910580705142100d4076036000108842000452024450942a9440c0c0181c0442407142e0007602001c2c404164030f844500e002c0108070281c860590190780a031201c00c4c400e0000d6078010040e00e916580501d45440304003200e003411400f500d40c0003601c0301d848003140c040c0420b1088100f042a00b07082088050318075640e860050690f84c1409502c0075040340360901090055145640100d00c0d1020b060b48041b841c080c011000a410ba4400100040e601600080c11380100710361480e2035a004113a02c0b000c015042c034040001c0d04510000f840240b041500000040c2c0b2000f0a034050401c10300342c0f100e0b0070303241da2078000d5800081005020f1505041070400c0051903501d4040b400f00d1045910024040c1801219002518901742d41c1c038041d41070507000c4c800c5401c2034441310281080040d498401180001160050121003803110109a00b0080208 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652371879 1250 652370629 652370633
    0xf15091e1506030b1302030c0d030302030103021c0803010329090309010306140f0613120f0b0a0905250302030f1b0d0314030406020417100c0c020904110f090c03160c 73
    0x40944c0d5008480f15140c48400c0309600c0040d04001c0754400c3e00e6070002c1d5881c124014168075901841c107807882912184401c90305c404a00301001074604008040340410401840001c1904100030801100311000c2c40c44029450411181d901d01140c4000483e880858502240e41e070500032000280311001840c030154191b40085825001140e0f246401400300080420240b01159041002800c26000e8004103056030301c1c129255045001c820b50700702c114a03001c40c5503110700784100c541240e031010090071032001001642403141e4940e0445840310807070020000c050b03242840000d0010103400040c240c01e80f00b00005803203010700808220b006003044851140020f4102d0080d800441c0d902884585030f030390340d2414001034840d80c0c006039a03010204040c4100703d040041d0300000c00b038069000713110031080020201c81c4204100360181d8403528490100340410b0f0910b64428020001900d1100c862844034042541e66205480003000f0384000410000d00308140004561540304602e421010000d0139 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652373129 1250 652371879 652371893
    0x61e0513020a03020d080f1b010b01260901020405131d010b060735090306010608070e0603061201020f040305240f09010b12010b0114070f15091e150603 67
    0x10707003c02806200618020b40901146a09848070115074680182c3c0da0042480d021101c8c4140600c909800d60034088915810760180e01501d07540342c0c4401130580c0c0c541c5880f20888180381c000e04001000d540c200004225925482450b81400610060204040581d00d52900c55035868402074003030b0ba45003580e50318a45d81c0d4282110402c070380058100b84c0722110740703e10310310b118401c6188005000104200d41d281f201342c0d2025101e40d4000301e007a98202c2c0c0e60386000342e44555044032404001492400b0b09a840d20b4103d0185811640113000f450700c0c43c01c0300162500b268444032540c80e1002020071704208100c820001c400c0420b01c66400394951030a0403030a44120640030300003c074904032030070008000613000d6000e0310089c40028806485480d54150fa05c3c02400b9841c01e880c00550320300900700795401a50b0454604580c0441d0392070180071581c940403111888a480c00380b000d601c500700d070b002040b00503240b00c0000e043e503407039604001100d180400c02000c00800c0e121541c0c1c1086801c0010a0310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652374379 1250 652373129 652373149
    0x5040f0b03010b160317150112050c0f0d0212100f090207050d1b05250909110402090118030606050103230105100c0c18050108030c0d1803061e051302 66
    0x13640d8111410101c8910301550741d60403091081e440c09800008000240c2e420010104080e0000c0c0c0b2252440e211010300e00301610b504a94249202104000c0740840c02c65281c024016260101d00041c1024490f0140801d000401e0311504403400380c01c4400e01c5003010000701440100038448046103020350954076140c903906171210580a10030800361600015080d443ca40d1405c0303600500385c50040c01c0000c0c03205160b64600b4001c0800d109a03c0b40800d48034120300c242d003041c0d0b0700b040307100f003000e0a03a00401002c3d6110058142c100311701d400d0a54070750402450508003841c852580450001c1c2030100041c1219060800c118550310380c0b51203920304c030804540190558005540320b4202c1030351518180d890798103249004042020030b400014100380502d5420f40d915281120620150340d0300c8c00016502c1c00380e400c2188881d08a49800c1c0c034014090881e070102000da0907105180950b41c1c1c1c61f4801202c0e00c40340120a052030145d0010710341c80c914130500c0e900112081e10000600f00c40e40100e00d0a41c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652375629 1250 652374379 652374397
    0x80c0a0f12080f1b0d11010c0c060c110607050904110a050904052701050a110403030503010e10090606052116210c090e060402030c03060607020d060c05040f0b03010b 73
    0x1200240c9610000380c2c1d14112229500581c500c0b130b156518011166580c0c500c440741d100d000603413400461031808018021484080c41507a036000b80d0790041d031107480091030700e001a04203101d081d05130001c21802c2440302c240b0694468550301c0d10384a2640521064038a10f00b038030a50507404018070001550004161011231034183c0d00025940d5900724010541d14070b45032815a06143c0701e41e00402010305400151240d880b44500303001c2003280021040c0c081c000e901008002c00d40900c018011100340c038a816600c10000413081980c1a0340344c4801c401c845c00fa0700800c00040780094001e108080556620742d601007034030940d140b240361203804180081c3c0c10348207220400c101d10010200880c1c514201401082e0901001c0150800345a80504420000e00c914101c000c06440001ca95141c6803090340d110380403040c5100d00d16601c100030410f0a502c1540100d074440320107110b10010543e14414a84003d9031910f50075992400d0119004c2c0b00401c950000b88101410401400002d8805c000c0e900c0c454 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652376879 1250 652375629 652375643
    0x4d030114041a13060c09051c0515060f010f0201091704031b08190203070b03090607120b030304090504020d05070902040f120215071e0c06031404020d03080601050c07080c0a0f12 78
    0x18201090886d850003042e849540d000c1003100c00e0b80800504800d070110124032400480301c41a100750082550234030b0494030994041d0040607517820b1540143c031030003008001413000240384034041d0358008004c003958201c00c0343c0d9030022038140708222079042c50700183c070b012a240607000381c030345000d2540d40e134807505055002c00c3ca541003032000c6460070041c1d0409050fa02542603200e15040e10119a94103045074050b0001c0e4240340300c0d603500d02180c03042022410018002d58a014100700e0700c04003401025004036005080e400c01c410104200f880000080d0403c4200540c0d83c0c0d1400a02030b01c108195049034800c00b2400c9201d000607620b030400c1210300e0b0f1041c0103403a00c4c1c40540c05c0c45d403a038011142c410f003c03089425508804101030021400b081d903000361001c1140e0501034041c01100842114000e40258500390340301c021a004442441d88000b0500d09180351100003c902030510410340e00140c001c1d4010070440c4441d02e0a1450200a0308440c4841c0c510149850711130f9a5617a021035018040e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652378129 1250 652376879 652376891
    0xf07031a130e0a11180f041b0b0c3d1a0a080105010501030c0903110d110d050c0901050d15021303060203010e044d030114041a1306 58
    0x807164000c841c8640007402911144601c0d810003000c003195500c0310724864152140c8100c0f40626034210580100c80134120444980c0d903555600e0182d00c411760100031035104a10300095080404002428404040806410070081c030010510303200102d10021400c001103809400b69642c3ca4422240ea10000c1440120b0500c81ca0190040103003d46030140e600b1000d20a0086100001504414120754080e80d0400500f0303120402104c0980c12400005d100c045194000082440c0229a14140c580205012219a200c41e400070f0000d160843c0115100d0304042c190110a103405100140140800d07a1141180c0b54951b9655142c64140e600284c0c802d5400b240c0444407403080440c00c0701465109108640c3c1e540c460001c05080345086800301c8061b2003144e1000444000014008995015a101c17100382d0a100b400441d045a400c8a0f84804d8500a007503004155400b4081ca8100d400e83c40e03c01c602ea0305150800b80803603420b200818800d10144010702c040f0320000c4480a4929130480300000705 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652379379 1250 652378129 652378159
    0xf0612111c0b1305070f061202090f0d11220506030a110907091503050f10050112020f07060c030506090a02070f1e0b090d0f0305090601030b0405240f07031a 69
    0xb500581c4801130300303510a21034003040110804443c44c0554a85407522104459101000c20030b07885044d881070f401c00b8902000c5100750518560845070035104030200749142c040b0b2400f050065103110f01c40c04c500280803890704102c41142c803641e1381010f03040e03018050421a94803030b030f07006440c0c0056460113484410000398209109000c50070241000c141c1119840c41c059400501906e0240c0e070139051803000d180400c00c40c812144030017003240d5041e15040c1485d041b0340650300c0250444010407015900801200300024410310a1400526080c0c030001141d08008051181d00b480040510081d18410030040380815004414452042da002d0701801060b92440c000389074034801e002004040710903850501046070000704110141c44213a41e5142101800328008500f03030340041d2102610740c1c003c500140080b80000c1c01c1e1a502c540104103c0c0c011440803680710403d038501074040c908503140d000a010442103030142081d0001503070715050045904078441c864401405008203486050f45420b1005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652380629 1250 652379379 652379401
    0x1b0212041e030512031e0f0f0a0f1803020c0d0b01090203060d021003060e090129030f0d09091d0d08090f010603030804060e1603150f0612111c0b 64
    0x20b560f021041c0c0728040c83d0303103140090340e130015a00c0c0304400c000740078000036000d80c2117041d910480d0b900041e55490f440d030b01d600ca002d0b080064100e050045d150424125415010b02462440c041c80c008201c1460010b414000d09220040980034130448000b01c80b080420389240303155040d40c82c14000142c0c0d98654a0009102040c8484001e400c59004140e0100c5240c05900090446110320080507099544100c070034200c2c3c0d265038401c0d6030358500390841d844506405012002050010f4115100102c000102c0c51601407840011400983d1203442440260103900406050070720303507002d030b40002c4010000f07282c4908401c0d081038204822440011441e41041049002403101d901c02003080589a040c0140340d95070856080d00c80a0a0a0781d5000380c0800045240c0e1352240c1030003c00b50306040d541c0740e03981c1c4400c40c4c03232202013141c41e40c0407007410b10150f10604009001b1b04120950322069071601d0088095000c00040c400c40000c1000c0d50014403c40b42403181c0750b88500c0c0344c410341c0c2d16401504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652381879 1250 652380629 652380689
    0x120b041b031203110d1a210a030806030a0c031202071203080705070219121a0421030e0712020319170d02040b0f0a0822030804060e0a061b021204 64
    0x900e558241b1028100084103441c61528001050b2450313000b50000d00c0c07070b81c0030040045400c05c020b0381c448100c40020070303c9070480319003101000f4169260a0312644a1305584c040e90307001550052040f010b181c00640e01003002e1002000100b5850380e01102d5520060044400140348505200002450078111b50351820071060f00c8445002008045845103900a10840c2d6804200c4c3c1d08541030111884222034510102d1080380e120b00010b1161050401044480b14a50030910a05440b01601d42c03c1d00740c1800003a001c0d09004002c4c8414070380c0d5004040ca4010f01441c40600b0001401409010403080c148120620b5614420700d90358410b00054a07000384201e501100004001041100304880f880c8010724400c0f010380c1d60046240c6a14000460000364079541d042404100204203001900903240c690b80280203103400251110310f8050306081270500700d402c0b11031300e503191441c900c50080c8010300e4021000b0352004001c0c504010349840d04503c01d43c000c0021043d4040101c803110081c000c010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652383129 1250 652381879 652381897
    0x1009050601050c1204080c0604150c1a07020a1104150905060102070b04090903111c0e0604050405091509070605090d020d1e0b0106171f120b041b03120311 68
    0x71131501c2401d80c03003076241c0d030014003500c10203004460014550b1320704101541c007034411010022554040140c0300307841105d0fa500c02200c5000385180e00340d0528091400a5105a2158000d08040803c40c9400c0c8a0842c2c14240f00e403160780317013508503000440c010403540145c2d841035800140b0f40d00c9000041c0d1500035141d101c2500c1c007500107000f00b030950854000383d05192003505e412100c004411030250b1038640759003205110064a030044c4034818481c00440140f1403019204c0c61425486102141c16940115030090280e4800c04541100380c4441001c0c55200d018800a881100e0414600030300511800c0f80300380c800e4090041c40c030107640c0c1c0c02080e850b9180d44140c061314100003000b072148120901c3c5e0410b8600c0300b040b00c000035545024280b130414500c1c050401d002c235036480d003850800050800b062201c5210210074041010304000b80d6003460280036168070b0341c1614162030480350707005440e00c0c950120b01741508104000b80e6084051164101c86040100d2142c0b55103040001c3c902490f010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652384379 1250 652383129 652383133
    0xe0f0f22050c100201020a230702060a0f02100b1c0c0b13170c061b10050108100f0c0206010b0c03090904030c03020d02012007031403040b090f061009050601050c 71
    0x1400c400c01c04000b4030107503252410303a00c50340040740e0280d05034204c0c01001c400201107154421140501d00110030440382c11007410b02c0141c00c01a5075008124540c21420190340804d04400740200c1654041100b91040405240c00f4003450042e0800300b4500302c41c401c030102c5410300c5609040c04100b602a04100a81040076540da00e51025044241d03480c3c00d036101f01014000d94420058044101052451500c80064100ca04e0000303d4100380c1813880c0c501c1006a1107005004003e011400745000d082e000b003d406008040768680d06042100b25000d148101c0240342ca482955094990041030103811104214290b50b102e101c54021182188031f002c0300c0c59441207540003000101500b084400c0342081c000e500311004030300c1500059080f5413044000350007040c09120f22041d059240320040110314401e2502421026110030100842c0d0001d60301151500100e400f0000c010000300248014010300c500203200341e05207172051402c2580740e801109486a141e50004038581d0003030048960340070140d41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652385629 1250 652384379 652384441
    0x60904020d020d050402190311010807030902040e030d11030105130506030f0a0b070305090c01080c090a0305010204120b070813020d1e030c060e070605090607060603140304050a0e0f0f 81
    0x8040c0041c403040710200c1c487c4040c4051450121003100700e030010303a5884080f00d40041c1c60741c1d006480380c4c14020540c0c8101620381081c100142c9840c043c4017030040300b0310020360321804100d0409055520b8855207504040701880104800da4a01c4103030030038100c40341c90010702034540c83e020034188809044417880a00c16030110004100e4408401c51081074660360030052511071070601600c0340c401982090010710031001244803010910003c10f08030000601444c0d81c103940f5981c480c203980259002c070101e8a203448021007404030420b6110792082a41c40d01c44024500700d10040c40512030b804010340503141480205040000310000680c3e601350b106520300d08400d0b00e1034014602c1c80728581c11900f4606007518410701090006101c0c0c1542e00c15180c0d2410b055191050001c282c00a4170103071440d0b911044000b011811411900440b0300c03c1c4000745a440b400d04041c84400b07a4160300802290b011501008500707903800e904c09401003031122155055884144581804240c6400141c01c8258003036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652386879 1250 652385629 652385647
    0x90f02120106081c1d062a1204120212010e07091b020d09030623090309031605100c05030d09080d05060315010504150509131106030c0a1b21121a060904020d02 70
    0x13055a0b0a00c580050450b000c080703801710007623028015480b5804403c82103c1c900401454809a00d400d000703085000006c15110703210919140440030760169501943d2030074108040803502550b008180603a00007040e0f0318600030002803035a040380c407028042595890140800800000554004010041000384a820618fc41c1900d903449802e40d10710921032411300c0498082220705000407100d0091208041d120f001104ee903800451082c02c4810780010002004040e15030710403807520342c2c09001c03042e80300c181c126650421140003070720030f034420342c0034024402c07038100c6444447e81543c07000d03680032a00000300a4082e500181d40c0d017207907520141e10f001700070110081d1842c200a0a0040111090300303044a000d10440e2b00c400d41c1c170311504840030491021035601032000c00c0c03104644402c4900714082641c44030848800c400ac1001428401c060004000d1940003050001e411903103a01003114084d5546610803a251042d2554000e110115016001c0d40c3e41d5415038441c00d10a000070342d03403003840e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652388129 1250 652386879 652386937
    0x7050f031c0f14070f02160b04031a090304171c050c0c040204050303180a0b0c0307030906050c07051e15070203060106081306090f02120106081c1d06 66
    0x780560401c0e10310300280b0701c020002d9406902c00109103c40c50760600e0300d50100882d5070803a8030319035200f903224150110307401c8100c00c80c1007001040e13808007850316603040d03107441c00060401c50000e9144010701804e0002c2150084111000c0714500030504802400c01c141450500782c40b0300000e40890200204480300d560080b00030404800e1002c1510324007907148040004030b006d140260b5405500501103c1c103a440c202d054104e6903140240030034021030355100310008035031146c00300e20b00a401c0441e9000c101a00404090052700d01c2c0d0400c54240303034500c20107036612890751040502c2880c90440012048040d1400c25000043c098504583c403d02d4040c40f078525802010124000e01c038102c00020070501c11200c0342c0c043c3c142103528032484d1459441d07038006400c610300103071191045948040f005035211001d40c032003031440e0000032807164503003003819003882040d81d9a0800e0041c4d00390600c24499101c82020112640c980c011032044040c02c010440500690b004010b001e482c6a0f40e5007006281 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652389379 1250 652388129 652388167
    0x801271806060f030309030206090a0305071512060b030a09061b0302130b030403091a0f181e062d220f0b120601030906020412050f071a07050f03 64
    0x5010030b121242c3c0c0c0c2c0c6000340241c0b0481c0b0001d00050203883c02840107160801c001d00d010a001001c00003601c2c0c9a031502d40c02c1c41c400350311128808803500d514640160b048a19844903620029040080703500c0c24030044446d00c03005100c0e8494a5441000c4c0b420031440758001c5d46540018103a00f0103038403d441000e0000d500a0b40e10400e1a0380da03140000e0403a401100300c91003103a050b5203100c0b0031403408d4200020518950b0903075a8681090008500c0344040e60040d080c01d420300c4d4200400140034000f8414120740d03040c403444140303c1da12100125500d0300012100e0a00d2802a010030b4a43c0d900c0d42202460480294000341e040f000a104808641000c01d1800031802c01d005414029a100164080c0c05920312a4643e1080b0911102d40d594140d40c041070f5000c00c040c18082034100e2a940c6076400c07640300c0c0d04061114003032204d2041c284502040201e01480d0340b03000420100b41860038407070520000c010080c4100000081c0441082002c1c0030f402410f0351101c3c201ea48803560203480d20040c1b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652390629 1250 652389379 652389383
    0x30201020708010e120d02160609020f0a05030c010e1807030903081005030c0907300e190b1305070b0a0807020d080c03150a030819020a0308012718 65
    0x1c5400300109802a06104821001c01944000c0c0b20260200140030490b402000c0b040400301d0717017417000665064107034600d04400d07840340074002200041d901c10440003540101c0c0050181d40010403c0c0403981740000c0b880c0e80500c013402c0c4001c41d0600240020a032142440e80c1200c144403200511800300c1c2c0682103084d2252285d1911855965101e0061007030314414071a02e645584441106a01400c02c02c60107900280c0a290812103111800c40500104010b0652020f614070440190202c10303d66205507441042043c0c0601b070074051a0040080103130801c1d20161000e04038001040410212080d004411031388102a55503480d9101364000c0b042d042046180040f610740303030000c0d010520214080894011a40b2000182d44904000c40d600e50002080c07000100380040d82c042141e41d807a2038002c0114030524109035036182100a0042401c0d1100c6100f056500c07072004540040e40004480d070540303c1c3d50f2403140350304810760303080001144d01074040c4280350b2a00e81000380c0700d81032205210b4014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652391879 1250 652390629 652390633
    0xf19030b06040c0c03080f100915061101021606020a0201021c05041a1320030102040b03042603010626090105060f0102071520011b08010f0b0708161b03020102 70
    0x8129a03c003950b0f20704008a005001814240005d1800006280981d8115140d01c000250386a142c0c80c0c400c00b04c0d03050800e025810603003d41c080201d56803103a03144210780c60103c004c1d814200802120500d642000302c00501e666004100a002c0f10b20035416500c2465941403256180705401e810080100401d490a81c0c00140c0c10207120341c0144014580c83c015080000804400c1031151a288180175000072104891a603110b4003040d103a42c01d0020b00041c20840300a169a400e05160140460050743c0026000c0c1c8601000c0406400920090360f044500c40d00300424405102c00c0022210052400600040080c1405000c5030050541c04144900415900039550705034100040e030740c44109208001499415011007858248074291188060544044004d02c400c0c41000c3d260039690816a103413490404c4400c800c50544e40184824014102d081070b51044034209408840d5500c03c120001e03254400000f082c00c00003240651100c03441d6000f4540365900348072030100c0b070300705443e80c0b0040c2e0043c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652393129 1250 652391879 652391891
    0xf03050105070206193c0b0f0f130f05040606050f1206130f050d08191811130905031b0115151112090a080d020c0f19030b0604 56
    0x4a000003075003070180d24089a00043c005e42c040c000405080381942d5100007050203100740740070040c004000184d510841d2038101c55513201e144c404d8219404030b51210720540c0c400e4004001a2241e1618540c24a001e840701d58242d001c40d407070744000d04420007214030814901000c01c03090040da0307400760b002d0f1203084860b09010302c6003500708200c4105410003207171241c12030303000300300310b0411030a00f443c600744500d00d14221907031140c5408d402c0c884c070003480501260000c0100210346c04001486201c0d02c0440c0f10402000307039640300703045003003000040040807004462801912951540c6042c4a01c0c81010018040680e1501d4107d840380c10255401c1d80d142c510b00c1114003c0c0d1010702420754a02c1040424900440c980b039610a40c2c01c483c0e207055414450311075100c810000702031014214000c046600c0d42e58039111401805600c00c0c440d44545690f0b00b2421030401c2e040d6012442c1980428100d8960020444100c00134540000c3c50100031001160444004100030100101511404c0111010461 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652394379 1250 652393129 652393141
    0x1303080105030303100e06030c1903060507050a080406020d020c0a0f110d11040507050903160501020712151a040c03050a060e0f010b0a0207030210020a12020313210b010f03050105 79
    0x504c4c00f00340c0380c400c2e4103034070780905201c11303a00f1607001030303101038010102c4200c1c1d02c200c00420031501e0402006054011000003d0007405200c0c0100ca42241c401d1414034908400c25400038003862000d84010300581d000140d1001142c00d42d0151141e401b510001d1704c074001c00034078016904040d0000c0856100d00c0c22401000189064410f180895401009101078000000d08100040038010021414448140401e4203079440400c039455000481070315540da41400c00d03001900d01010b44e80700402c00000d0404c0c040004000383e9441501903591b00001c1450410010403501d20380007132124940061a005011042d40d505410003405412040002c0104d41d13200c0500958891007115220004180000104110242940180300014403407042d20005500d0358006400204d1f10010720b80180e11150382d52041c426a40318242c140355a030f000542c680203503446944d8000c0c05034030410384044068010f100281d100e0092a0703007443c0c0d100403410000e41c0c44003c103010641d99400b00307980540c0703060700041c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652395629 1250 652394379 652394383
    0x50708010e0601050f2d030702070e061f0909020319050a0b09060118080105040f060c0906020d1b0b0702060907061706090903272707180e130308010503 67
    0xc0206010381d20203240551780000c80545910a425061444d6640768400c4418040d111807190020300d2507034825a60f0801000082c83d00102c0d8100854441084040c0420750303480705880e24424621f5508660b5208000000341e03511400765211503140c900000820200c0c1c01c0e001c0c0c81d52501c1c00091800c0049440c0c060104048840c03101459400c035070882c01285503507001e0300c8402055008080c0d280710841d03c03200c0c460f003500c0094070210391800001d8507100811200d4003400b40240d803245400e840c541e24000000350344044c800c1c100030a01003000c00c000140b03090130800384140c51300700c00301d0305050030141c1c2d00030341c2c0d01c0048402ca21070f07000300304010071040c1c032810716039110003910302143c01d0a460b000c0402450070000b400c40c2013107120070082040c0d8000f9107034150000d241e403d03100300c841d00c10f014180000d07010102402540c0310785000660880c025041081034008000d0728041c2d9409203050307144103003641c840e0040c946a64050301003002c0750341c0000c20341d248a882a500c00c04181d07603510901d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652396879 1250 652395629 652395631
    0xc0c051608190b04080318010c030501032009150414040b040519120315080a0c06180503060a050612121c0203090c01030b06090a140301060f0305060c090d0213050708010e 75
    0x51a1009000104000c5019500590341245024401547c0302c0d004107440c40c21981f588003038070b01107500c0d90010014401e850b410b45080320395202c011082102074070009480e454009054880000fa800707800e00740c0d5107a40d8488000d0318145420119241003030b0508001400048600311424440d69a40c106d0071440000b154113010f610940c10b00c00381d0440d000690140940e40d403420313108001c030a400121841d01300310980403180900c105141c0d0509152004240070103084140910f1107070b1000c00c001944000425607407108403820300140c162207034030001d032001009138400d92841c4640c840035a03260280030300520385840c008100d5807285e02ca400e0000d080e400102e4101c034441d08076407000e08040d40207070807200030640011300c0c0324506034000c400548048550f800084800c40c1c68a207020550609204000103802c2d40c4400002170382c0b96698072680c8080c003d01d19510114003060300c040c10b0b165403c013184025802488826600c12641d103035070040004841103800140302c180001402c091164002e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652398129 1250 652396879 652396883
    0x10201090515070c0b0718090e0d0516120206011401080609070c06061a1308030c0304031b0b0403080d0518100c1403090c011202041202040c0c05160819 67
    0x24050010280440358580b040003010b450a10460814000008041d078407001e11481e400d85035140c503010388a080c2c04044244d0341090303410030b2034050310ba003000100150304046840e85d0b20b012941d8207519421f440307810301e914100800e002c90908128405540200d0800c2c180c41c5100c0005105814007030046408600030fa5800b0f8101905401041001e441035051182d150b006002c0403c895aa07510400710140180611102080003c1242d81d042950183c5c84001410703030400550424005c3c42620f52a40300701d01c00240408210b4800e0250300180c1c003035610007040000000340d2199924101404e066001007102e1841d1450702002a00304515900c444140021003802010301d01501c1410100030005401c80009000c030801018000c5110840218417900064018110700504500058460b444130b00c4c1c00b00055006220902a00e902402841c41d03142c2c0445011450071820b41003505c0300c00414002501c64000c50b86a01851020031001c2c004482e5142e003100d4400c00c0c0c5442c403201c0e1036254000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652399379 1250 652398129 652398133
    0x20313060305014211071418010b03062b050d1b0308160c24051006050f0f09090a2903032706040f0f06081e0405010f18110102010905 59
    0x11010482c24403130381419a81c0c0fa505101200d8825081c299250913415031103004156441c1e2107069150400041c84080c09000a020290a50400d18400d5043c000140918081d64034000b45900c80e10900404540280e011207030700484034428241035032104206024800070500840303a8004806240300942407240e0075035160b00c595150018110321403044d0410071410401100054008681c01da1001f8640c0e101072014420184580318640003070b2140101140c5004960003003c0102e5500001141e001c2031040c600b076540d540080d4803100c11409000307101e64111560804204c604c0c02183d0115030500c000e810398800d0040842c00103061125a0100701e42c040d0014808040a131440801c9043c016507170b84440b1091001400104031103402c2a030202e5500014040d00f00082c00311402143c0c06030200d4075200c00705147c0a00d034102d5090342e0b002c1000c1c40841c000001000d1060a501400b40500742800920185880d074101010084000e038050700c00c4080042550030700c0d03005100300ca03131540c1d011740 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652400629 1250 652399379 652399469
    0x4060905041b05070f03030615020601031505040b1602030d0614040e0d09030209091903080a0b010c2103270b010f2d030611040305011d030f090102031306030501 71
    0x19441050170f1050390100c3c02d15031543d202080002d4190008020f0307140b82d81c010082c07503140d82003440c010500e060006011a14000a00011400d4440d407940d00c0384013688020303130112142808915501c5060540e1000c0317858501e000c2002d181c0c041c030700518000d040750144032141d4155211925505113001d1740000c02e101040410050400a03440b0350700c0090041580c0c5400468222500b0580700c0781012030002c0c04850401680c00014899420030340000e1912502d112403680e5120100701d084030117107010910356080410b18510a40084d91000202900f43c0031641a041f401413a001030b130f43d82211030856110000c03400c0b1503e0b140b1403003242c0290000311180200044032004d4203170074039810046500140804408603000380210b482060300e09410541c1c840c40e60800c103003162108607901150003224040c882da1020004280c84070540c1100c806035843c004070005030b24601c2260b050380b03041d00050070000340701600340d4406812249003a011a400850040c100060f44d90000560b00c154101d1035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652401879 1250 652400629 652400633
    0xc071a0a091407260703050111030601090905090c011202090a03110111030c120703090e04110406060813020103050627070e0a0b0a120b0402030f040512070506061e0604060905041b0507 81
    0x404c0004d4205800e2094074035050712600c5050035a002446185140710340081806036659111403000300500c900c08042100d03081802ea1180c80740010100c00d4100441815004180d80056044450842c001061220826501e1418041010292503402e01081414036030304044a4080304a41d1030044030340190101d04211101e140040d00856400c3d820048103d1010481d00724240c1094099030182c5000250f403000c4d001044207448164021400300210758040c01171106040c00c8906690303909080105040c0d542c0b20200c2c01d41c1080102c9541100102c00d052201007261590b0f0368040e080701d0b80d4808550002c50306001002e4241c2c0f0070f411450404011040c02c442c403e81d01c01140070f804540206640000c1c1d000581640c10540d1003400c0758902d007040c48100001007040c5400110501500b07810101181c88007501c5030700c001d00c5203002d4900303800300c01c1d4546200d824004040e680209a0340d1103030b4030b54500034020302450248a01492030001c44900c80c00ca1001c0580d02350685a48207440c00c1e4040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652403129 1250 652401879 652401929
    0x40c0c03090e0c0c07180c0e06090d050f010c0e0f09071b060b0a0602030a020d020607090504020c210a020c090103350d0906050a02030405060c071a0a091407 69
    0x3001291032010611030340130b1014080c0100e500a0101c900c1c0380117840c030300c0002e08007210072888984c014020000c8900f81103446450a880304044100d64104969003d07003010b03402c10303d1017a40030b4095460b02c04940840ea070850040e04001c0c0080c1c1d07942d0008201c2c0000c0c044508400ea5418011600d05da401e14815510700141c02070440c8034102c04030302c008042c8007003464425150859405600085400070348941e0410008101654520090400c3d003003400380a0180000c90007034a00580d00019480d418900811925a61120714584820381004104480b243e90300700b4600078005001e000070b041d1880c5000d40c0f489060382e130411240d0213841500400c0003211105c180140100b44004a2619186203114010302038040441da0081102c802c1c0d80340c010200c490050840c603a161051050201040c1c0000e503203688010710500d82070703507000c7c541080150b008950906281d00594a020080001d01700e4000c01642482409440501c07000340e00750302d4a640303040c01081c210701c2c003a140c151041103503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652404379 1250 652403129 652403131
    0x103120c0f03050306040f1e09031b060e07121a041a040b15030307050d08100b07050717010b130b01050d050a1506020a0512070212011a040c0c03090e 66
    0x850905003a041503039500d00074079080d50807040c1d012440c0407040001d942494000c4044010021b0801c02c003e11003c0f1002c2a18070b0f4420032211800c1e41c0300003480803d070203003c4030880034000720400b032040320540c80c001d006001b044007100ca15006880d00041e0480055500c00000b9074054500c0350328843e20140c1c1628101d0007041038401c0c1c100382c240f0000000900c2034060085004028510891801c214803240a1000d4810300d4065030040006902207080401c0d42d02c25a50140f4000626486040040380703541447e03004203076480b0001640c0c3e001c210001034450100e4103041440c045c036510301344080b030132600203501051b04100400c581d0032409015910020540e40e0505200e07003810100001c90007114021141a4403176640c1d00c185010240d560781c180b20041403141f0080c018070780740743c0d10243c80ea0386d0746080780c85440011640c003045540b01500902201c040100800600300904440000c80f61900b182070301451600801030781d071038810891040041d81686600030708603c0e01d0121100f40300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652405629 1250 652404379 652404413
    0x615050d1109041e0606020d023d02070209010f052112070507030501050903281e030f0c0e03030909130f0b070905040c09090203100506031905060a050102060103 71
    0x508201560043d541d034440d40f1100481391410002c581d14100c1e01e001240c400381c01c0641558060303540600840c2d80010158000c628890503450703154208055030320001d004800d03e8802002d8003803561640e12469000d441014001c0b0341c10f403020790341d0700c2035000d43c0c003920b02529070405010200c40f0b080304492950b46880000900484d09002001d0000d036856400c801c0c01110070350800c0e041041400424050075411a00c400c014503e07080880400242d0754002800300d00c0800740b01c10714902c141d40980303001480c0d006070740ca10340c0582002200040040040c01076000e5844d2500e405034510911550940d858400044c2c001c2d842d20024404004442e00002c040300d00240c201440440044c6a40b000300b80310b03a10480b190310590030103150207080000990099805140703484884d002e9942d0051000c403c030781800740300590703d440f040980304004400f90030540d0003003400800c0c01420242918a4a00189401001c0009032030b0070041001c035418510400e801680864014070105130b2034602400b81c03135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652406879 1250 652405629 652405661
    0x60f0e060a0e03060a02071109131e0b010308310b16060216031205040503120c13060e0411070b0a2a0c03080a0b0d0308100f090506040615050d 63
    0xc4100020310303000007115240985d0350081001c0d8108010914a84c030507140856005589141c0380300d40887c032403580c040c00f40066443c0004030051041e6080220b00700394128019044075a1030b420400c41543c00704860491510300040740001100102805d07841d01c0d01030800702d651135441d1036078103045500100c4071403214504902c0e11100248092004241c545225201046408400d05020389a6250319020341017081c185020440025004030850ba1503001050781032090307484d00c10031082540281c564624042e20303074140219505401080c0c40340140c604842c28800204414880003507800b900100601d00c8441d08d02152003441d841d01b0007105154040c02c2c05190b0f034034544213080d15114251140c80822503602c0c44405044e80200042d0780106d02240605c0300c0d0f4401408140e051a0b00c003805800c110811012401c50b20744540c00000801703402121881541d1100d5400d0014903040c0c50b0540310310301c0c1100c000740c540c4540c5010345c40c0000710f44859003032100e6083d0640290003041c0b0740c1c0781c03a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652408129 1250 652406879 652406897
    0x9050c060f13090614060301140904060b060d09021f141615140112150c020c040606080114090c12040c0e0106030203040c080f100b0307120f0507060f0e060a 69
    0x26880082d0700c10014000882e0100320b4074a4814620883c5961351035441c0514000c00040c010907030f40c11000e0707440c9a401c8d124050107a440c2d0800c0b4009211043e00d455005500203401d4096205a8000c010482e000f150040072580031400301040b600f0402c01800c0c007107000021049080e0f107452015262078280d520706011003417107650350260654401c01601240903038840c41d404100c02c03141015800f4103640502020392106d5a01ea83e5080001200e0700342d5565260400003105510030f0000102c01d035000340051064548402003d0144503090003403007910700c3e01054071b40e903a107000350301c0500404042c4261413900e1013500c281005083c00410582d126006904e000070072510300c052540c020903465500584030f00b85840c0420303401240e94480100c90b84101c8080c00b8a40005c65640e6030f41e246a00001540c80402000c01d040005a51291b2281202420300d8014400c05203840b0140ca03115000752180c1c123071102e0003954490229103e18000640707042848a160408400030076111416040c1a164 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652409379 1250 652408129 652408147
    0x10507060b15070b1612020c070e16030b0f0a0e131a1501090b04051020030910020303100b0c010e1e0c040908070204020f0c030f031006020109050c060f 67
    0x11070181d00c5002003640702e00091075418420883c628a41020205000c064100c40405004010982e82058051344680c00111040c90b07400401c6211b0003801e00c1014210035182c450088511040d4021503080800d0030201c10781c10600c0c0410750f0202c203180042c840c1c05214101703180050000001001c451403040c0d850218070209a10204201c10495500d8040240b840c210304e44840ba0381c000e011a5041c01500c1405001816116080e80c05035407059031103020702d0f07210a40848000c505105000740045404840c00c22800c408002450140e40a0790348403080b25031200100c0c2c2d01d10044a40c00d0760200302c0c240038004916150010700182150800100e14150300b200000d080c9185850103415164208c807482d10500001e0006541510080754100a07031480c44d2140000e23842001c2c0003e00c616400580007043e10b081c2c800790b88003208280112607c0740700040c0740c0b105562003602c01f0012103442600c005041441406005a00d0390300c00c003d09805885001440300302e410180003800c0c0c244062000d00d80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652410629 1250 652409379 652409389
    0x60d021608070b1008060417180d0501020c150f0106030f0b090a0605010810060206011205011b050306010801120222020405041127030d140427050604020c0c010507060b 74
    0x80d4070b60080d4076800c000e0800320342445404a03998031445154100d0010400480c410020050851082000c103d51b0740803904032010f008649144650741c084d0346d0703503ca40140300c0c2c150f002c0d0500740c800780102c50301049098907082800500f00d6003100f0b1902d80e040180640c070302c46c0d0003000e007000e203e9102103182100e04000440f08201180c851080a80e5200700300015070380492601d80204442403c2070256051220094580e8014043c020391207a0114690007040800d5112500c0c00d10541e10041d200700350340c200109030b5401914114000344100e0f0020901c14951034154600e50740c010850031400c85803850301c4080945608101481690134030000034030351100d000f01e40c0086648084c40d6904e105071701b142503080000c151034204031200b0f001802e1260b100082c19a48600e09130030400820041000015003610480d00685203030010783d88a00d1800406160002c2d44403036a2900b80056a1404241300c01c82c010030001090a9001110380e0100394040c10050041900070345010810b0700c035200100d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652411879 1250 652410629 652410637
    0x4020d060b01021f1a06031909080d050702160b0a0c03030b120f0102091503060f06070f05030d0207120c0c061d180405061e0106120219030f110702060d021608 70
    0x300b900c80d21010071948412203417240e8225000c040300d8080c15400e142d04080c80d401c40100741025015502c44911040c0140c0c5015120004810070040c4800d1900920003500c0340c1c401000c1d0064070801e08008240c40d1001d07019070301c1805d00d03540c520305102c80075201140a444a01d413090b401c018511501e200b824001d000003c0981d11038030016a464064409016100200c401e6143c4c801c01c00b4000e00c202a90780314216080250101c0e815910398401303041203542d000300140028501e200000d0503440381c0c411034020f0b1088a0049020f418804468a02541c050f03085000080103c42512400e0010341e0003061403400c011046807503c4038007002440864000c1388000d0044442840394401c0104103c420010540d02441107078030618889041312445001c204180107280611260300c075032026203201c90341500d8120010100a0020000c1c902c009402024000d641125180c20018561140240d0204a13880e2070f41c0542442d1400028600b004000e40120302042a030050014442001c41c2341e19000d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652413129 1250 652411879 652411933
    0x7060806151603050717040305060412021507142514030a0503040209061305040f03020d03020906041202030708070f05090618040b04110d1a0a020304020d060b0102 72
    0x509203410503a003044044240701251600403035007009214010603041c104401501d40c036041490300c40398146000448a8603a1050103022003022400000380503001417110b021341d00800031030040001d550340072600c9203001082d0107415a0490f012a0707113680f207400034100000c0e003180f4203070400c2840c1141e181a540a15070017505000d41c5800c0e40180030200041c003021001c1d80008604c2d1441040e00a001c50100500c080c3c4104010310004d0a141c4070f003100d005044e4102102040b19107170514104500c940c001d80140c00610500304603050141c028402c46040384c2d401003d240c01d05107000001c1e00000d1074150300f207070940600300d0002100ca00410201010301810114018158149000d000782c106004040c544034810030890341031120389640324150426080200012541d965041000c14042c0780c4034150f07005034001c0000030501074503c070010004001c0e2001942ea076100c11408a0983c002a10082c2d030040002e00c1130300009406074801d000c0c580041c0103030381e2285640c5486680c4e40c0758018203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652414379 1250 652413129 652413137
    0xf060203120109020a080f0613090305120a05011412070e0906041509020d0602070204090c1509080105040b070f0e04020f090f040501030305030c180d14070b0a12020f09030706 77
    0x2004000414070848107014010070002103040400e0404000c00c0740b080600603903400c0c004c100c007013103190300c0c0c050101c3d00c0e2024110044c40704600070300c0c0084c0143d0201c400403841003001c5012440f00422402028100c036221401c506000410408000501c1456260b0300d90501c81c080e4002200a01e000b8524400c081d10005403481d4501402c000070201c03900e080c149e00d003c4c5002940d40060761800800c540003034101c007005854080c6880410014800048040c21881c00c403007002550144441d40100074040e607075a04031020b0754131900c080c207842060301c00620300621180001d0130700d4070a1007859040c08007454201c20003203080c0e0104040741d01540650100110001e40e1080d0341c00c2480324800c2c140380330303941005a90b1541e01c004003107010107032005110171000141011003000701d0344a40c000620040c10050502a146003030031040070485460301c1280100400098004142016100c003000700c0d444591201c00d00c1640c1000940c0a1038442c61b00100c180f100c85c0c0161000c2180c14060003950329 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652415629 1250 652414379 652414387
    0xa0b01050c061f0909050d0c05030d05040803100b070203030a030504020a0915060f050a021c170c030f16050d020714150702060603070311120a02130911040b03060601180f060203 78
    0x10480030803100350407000b105405c014000000400c0000e00705080e50551a0a4a90405c245070107821489042400001c0d030f8240b606110501032000b000f0f500134050500c3c2d541c1b0503aa60720b00d040207802000406945a0030600c0052101030094201c00c2c3d20070710007020043c48a45412510040f41c640d44524408100450010310103560015003031044070203141407503400c00204140c000d507500e881f0070310310204d000d82d0144482480c3c01000c26449450071440b4202c81481c0030010004a07070001c86100982c0c50620010800c0b500003070114094114490b903071146081c03640b02c9180043d40c041e0038110307940c03000031400b5011f055050200e1042e500c100c11041070981880a00240f80103800f8000c90f20a0b001540c040000802c10318100b154004241d9281d400b6403400001c150800000100285d0880c40760080d903403103050a6840580c51511599907882c150203080144002c907004544455010f80c0104007140e90703980210000c40d82d90003024010700141d40c841e80b40500d040a1544103c000d84c0c8081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652416879 1250 652415629 652415671
    0x207030f03030603020a171207021c0302030f040608060a0b0901080f040c09090803070e0a0b07150609060807030b010e01030b130501060308191d031f270201020d080f0a0b01050c06 79
    0x301a20011301d50040c1481c3c10b189c0350b41c00107407000c0781c0c202d0100b043c06250a00c0798205070080c010f41c3c41c2900c1840d40d0a4980b41d8942000c3c207100c0c1c0c2200e406211780300c0c41002013046841d000a4418405040e5140000b5a83d0005080d520510280c03043da807400c0940c8d80014110194001c24500c54480c2d03114503124146414054086501d40200c14450645010288000e9151509490001d600690700620500c012030030100101075603000ba5644504201003c2200796000521340103e034441c00180c00d007603903100d9a00209200c280802009540707044041a045880d01c1860b00c1c0882c0542d00000ea1a666552071585591103141010040c80f4500e0801d010f46412440700705510715012402d846940c42107001a46440d450101e81c0e00094485119410308821688080e0303400c09080c0c142a540383c1c0d030384c00290b1080c0c8c00f240103d0051240d024198040f03840366074103c5c012a413103d6803a103a52100c6c0f00e0b400151544045045c10040d0610030600300850411116004000b200d81e40175201c2010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652418129 1250 652416879 652416883
    0x415110d050a050403082d07050a02060711030306061b100519180308090a1b0905070c35130e09060405030a0f09090c0e040c0905010207030f03030603020a17 69
    0x920300c2d0b64203864281044040b9820218155210400a00e01da5007800d10012a10040310285a50038000d080c210400c0300141d044002403103a80d2494080710390960300c00400319a460400d11820880f80c0050011034041e0500001030202c407c94011400303164a0038980706854019202c5a45040710307225020b00924034103460340c41000c20404903042c0401120310190985c80040c040c00201040100e0300000c50b10001070103c0b54080d9445070391903045041c01032141c90301c90040d0088a280b076107041d0201e00301c5030103102e030010041e5002458040440160074004502003030088051b485064034000c041d00f03210040014440d030101d00344071441035414061604103046006098080e242c2c405000c0c840070038400000d0b00c040f041240f80c41a8454031202c42258886000e070700180030541070802c0d00444a410034500101800181e134104030495011108640c0080b00748201809600840d6040c00400c049007070050100e40603060104465030b0300e90104800c6201a446030700303440d160300b00200f116242 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652419379 1250 652418129 652418131
    0x90a1202010e0615060c0714011d09070f1407080c010605030111220e1302280308030606090312070507090b090a09141608070905010312080415110d05 66
    0x8144001c0107001c1034094810350303900f8090050700c0010703d01406080a69102411034580f0500d00080e25889541c5e1098000c101c1060800d050108424051840060424024098000c50001c08000d040e440d807000c2503584000303440540040000710700309002826680c0005101e200d00c544403a07a6241059200982100c1c0990030503486641444020007000314a0020f40d409021200286141400106010115038034603922402808400380204040040328400c0405840c3c02502d102e000044622850b51803251403c164043c0100064014004210502c3c0a10361180014007014500410880081e1620004130f01d84100c2c07030350004d14481000000c0c40070800414801106109195490000030700282004124007031880d5120300c01c0090140c0c001c0c2100103301d0690903076410343c030a41f0359510200c1300c03802803213007912449400182424191007680e0484c9d070096503001c640f401411007154600c901600a0300d0600d05044604081051031050002211590740015913840392050400c0907100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652420629 1250 652419379 652419413
    0x191101110f0a1a151c0b15100e011b230303090f010b010e0402070f060905011a06090306070f110601061809090f06050c0f030c0a1404030c0b0f040b03090a 68
    0x304500510880d004e0319000044201002c980c3c00c00324065040e400fa0f000c00b00b200000d4052003034003052220140c0d00986100c6c00502c15210001341fa5500c201c06d690043c000c401807800645030301c0359044404d801c0b1210f03584079031050700ccc1074400040740c1c5214400c0180e03a90703601c00680c00000a000c00b008c004c20807418002d8040c4004d207c110101c00010f001c0c52178110109016a1300010f508040082d1804103000d0399030f00c8181000300e08001d0418500a0100740b1800444038290142c45050785400000d880e42e2a00c001c0042c80c0030f41da403030710845010680b02460001d000c1c1034410325850030024801d01e80a09115a514034241d41e000340c10100303c1d000d5070b001000c0079203400c14940104e83c0085400554a0704202c000c5140d845454003441c20b482403c80c02002034401000f48240c2003d040d0085c1101002d55441181c03a45a08a88090b1882184001482d25075580304c10000408141c002c0d2024144402d0700c141801d5403581d201c0e03030301d9004494141340354118980349804c10407040c180345a101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652421879 1250 652420629 652420673
    0x52404050c04021b010c02010903022404140c0603040506090706090632040e0907140a142d18010b090d062d0509191101110f0a 56
    0x10916446403a126035100c06000d000300d400081003030703900d80c0c010702595440031440300070010007511140c02030013404e100c00c0440040c003a8500c0e076184809054508480c000842020743c90300c1c0c031682e0b50300b400b50051044080381e6006241c42d41030a0765440c1c0143d1301c2180a1760241140d4a0044081810203a245e0001020300c20030103820b020b811303072000e520b01854240c144013042400c0303104070001e50f4106d2424080812000060007003611441030840601552000302107a010b17949404d4160b40c898030588216410180c5403034108040b4003540400e548101c006400c0f13000702072400c4a412035000c5d000080145c081e004d524150034030700b4020030350706811303803003852044c041d5040c400c426005100d248029885850009984400c0c08000e0b072102c07840c0900703281c40c0060807059442560040d04500c000c03503003141c6850300280038400c021411041c4d1174010303c40700d1180010303075582c40015601d40349030504225140500c150003500c100040d08400983c180100011085481e0101084258031303c81d203030304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652423129 1250 652421879 652421881
    0x3150e0c071b0e0406091419060b0423070e1e120d082404020d050108071208120a1b111213030f020321073008150604030524 55
    0x300c8030b003a1041360003a5000101007203400040c03d01500581c5103507500b01d56805036130004011b9204020132821400e105d1502402090201d40c01c1104498007200401d0816407840c4083c0d450320700e40c070384030340e880700031820240c02c4081070380c001c6441d82e202d03907130031a4a204400c40d20712518582141510302d43c100380801800c0d820203100c0e004100302d40c00b80000c110403031907004580c030f1700404a07542e13490950050011500c890404a60354044e02007885080806e00a132038000c00c40e41405007131644540e400c4a68540b0b04000554960400c140003000381080f5650740b2020401090710541b15180600c59a48405840c0e000c9064241030405418400071490ba040100c545e420000e0f400b041e040703d4120f600403c440e03900e40003180c245102006546010180100e2028044440c0e20250403c203000d402d40c0007441e141c0d811039a100c641c02d801040d03981c004668403031407014854071099510400c80e0f45600c0e444000d11001c20100e8201b604204c074640c01a0000c94402020a102e426507044c0d140001c41407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652424379 1250 652423129 652423139
    0x6090e040c1e03061b0806010207060203040b090f030a0302280b24181506030103051b01090b120a0e0102031320090108031207180603150e0c071b 64
    0x5001d02611811001d1203599440c20604016094484011500720b42c0901640164500c1c2c00056500c1c0ca40340b001042c3c400001c80c569503c009241c0301a29001d400451816080c6078510419420030603449a0001e04a2080c8407130ba2814046401a00d110781c0082030340c0c803004881900288080c11031003c0c4100014164400b10b02c003405d02503040000030003a00803c5903c40001c0110901308800180c011480c0b04812081c4500101c0d068803400c0c91a600c0d4050702800b0080110a110a110142440d40504c00d80300c6010084d042640015005060014413299120f2203035480390090071703d4002110754041044001c008501506400c032042c00001c41c035614190032034040000000340d01404501c070445e10500c01c5c50f4003000032551050b004000c20003541c0d6035603045559034804040641d01501c108080307904140a49141c0002c0c803501081c3e5024542050001c0300205658140000500049800080c00701500032403103000d84140c018190b540c55003401c0c00a4240940300ca20305c6884400101004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652425629 1250 652424379 652424393
    0x513050a0b221a0d0303150b0f07050f06040b150d151d0c0102120d0b09010f060f0c12210203010e010314061501110109060614040f050603030703031508030703020706090e04 76
    0x580130b541824001040e040c0802102d00310b424030b40202c100d00000182030303128000794070082e0070500e1041007183d0700300c466240d29079140c503011b950003803c824045000c9510061000d40240780d880014100500800280e01e900c6441118650041506591659010144110f803850714040b22590002090300c000a000000d554041458801c0e904030f10200c1e810400140c00d800982c0707102c2e4010a401c02c5961503804843c0d0084c030303070b00c900c0020401c021581c40e9000e00440c0020030f403e80028103014200c7c054503058940407001e024030a0f1403042d03881003220f002118409107000c1c09900360603a250f0340c107514105c0c0415038904803142069110108000b0180c0b4260103880e5103c0080c83e01e8284041000500c07800740c03002202c0104480d00b03240b40800e02145501c0c4450f01850300301c40510900c5280c0c420301040700c009845140e05608104400404203010703400c00c051407002220440c084c0707a51400d00394115000404218010781083d14208001c2d54419400e50152606000100c000d05003540d9087c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652426879 1250 652425629 652425649
    0x4031208060102100e280f0201110a050a120e0105120a0213080609010b13020c1e03210a0f18030f030222030501050c03010513050a0b221a 61
    0x280400046400041c4107034401d1055201c1003054250901c0f1144100d2041521054040d0000a0314a4007254078583e403031030203442c002100d803c0b0183c0300e46580942c00441d141c1c120f0b0210b008451040c0c005a600040c400c0050007050b070300644c08141c5402c15001c005003240a0441ea040c100f03c0188100c0000c210000c44858110241040040ea00c0180c1952485580c0b500d038044100b0713010340d004116241c60706411800408804a50079414514544102400ca004003070403090b4560000011045107600844c2c030803000d800134070489041051075501d20300901d0350049203039080241c0c102400004107440c0509000012031740300921003003404500c61600980c520b0b0340078041011a805000c09680a503044414890703014070902e030031822984c0034400d4900c003407108645961034000024013072401b00003904e060f600010007130708201000003c9078002e0032000d4040c002c000da607226400388540e24421000950b80103607500745c02015000103000121001d86800c03900003141010380c0340c180e42e074000d019 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652428129 1250 652426879 652426913
    0xb0408060a06120804150e040c02010509070f1d1302100c05010b030705011b031806030209031509062706041101030506010806060f13080a05031b070608010b0a0201021c020a020f030403 81
    0xc0320740e10362005030481c0c035400c172547c4280d00580307040d8040da052941074000d070f03108030364060895844035920b20041e030341c0c0d2040f0f00c03c91461f204012455260b9034207406a0710f4001a40b4041e240c15101150001804103240c40b44203008550003244160411000307000f02460404201c02400ac050316000c00030344100e07002c0e240d001c030350102d0314201000c060092031000d080c44002c802107503155494060280095005e18403103031181c4103042c442034010782220440740c03040f42800003030312041c0c9400c0002c5100c81030625940c50101144895540c20700c0081140a00c1503009100d10051421082c001408a50f0041c0042d4108074000e400c10900e41c0700e03070f07086400404001c5c540d1903036018031004c03c16281189400090030380c0180c800b01001d100000001d003154002020310502c002c032050140c2e5070307614901d00c44c04001c0389141004008141300344000c0c050340300c07041c0000741c0380580345d4481002d078042c19038040300c5250b80420750014650b81000ba0400c107608a05c001c5241030308603100c903c62104c007440c003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652429379 1250 652428129 652428149
    0x250216090b090c0c1b01030f060f050307050303070c050f01050705011509051e01150c0204060321050310120c03020918010b0105040b07020f030a050d0305090d030c0c030c06060b0408060a06120804 86
    0x14000c5c184d10a50125661811842040103140d4071611610303210421440381030b12030720078140041850300d408400c4400c40c1d40e000200f494a50b2a05050000c0c4a604540c80c505010007401542d010070028010901d40c00c82c0d080441c000c15003802d41c80c0c0c04880c00039000c0701d1980c12021582840c0ca14201240d03055a602c1c0d180c41e03541c007008460488600c60b95110003504141861000003c000303260091401c2445403e851490340e0182c00300407103a07400f00300c03980301000c40242801c001303100300880c46450240c00f41041e113020b41d4403078000ca420108292009410f08084500c0e46080040a104041c0000001d00e04030f0f292a140844140c114064210003a1058000da4582042c030760741040318440c91540002035928400340340b000500100b20131a0515002c0c011b92641c921428841e2084e20000f174001e840700120200c540d241110340c46520a4111100c0744d40791800318801035031402500081007070400902d058985100c000c42034486a600655500007040d600300c1c00500b0790f505442c10748480c101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652430629 1250 652429379 652429423
    0x90a12080315130f1b030b1018170c01110f070527091515060307050a0207080303091e0115050d0501091a04030201050f250216090b090c0c 61
    0x1e8481d04022444240c03e072524020301c18441043d004050b00204a20840000d0084040150f056900b18560154898809803e42c52864042d4688201c20344502004441c0142c0f1001840c40070405111140300d0390f4003101c8000d1566a0101c1c40019000c0d24002034400324210000b0f8580d185c010f409281c0c0710740704c842192000b40d15202c0c4880c600682c0c40310241000e0624248558039049102c2100e0030007580c0c4000244904000303405109000c9014111500d980e4461030201e980350040010380301140500702d40020001810405180246000f50150070308030b030111515941c00c1780000c041d1416904041d103203020854030442007012201700f5500f00c4000e00b514500b403801014050350040c94801c1d01604118030042010105218502c01d8000f04416151440c2e451406501107038228240c5807420086001c4250048450f0344110ba51f004580240758100c41080d490700b215008000643d548041e240308a02c0d0210700c0704d8014241c0040b20f4070b0010204e240c9a00d615034080312551141c0144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652431879 1250 652430629 652430671
    0x60111030f04030309050a0b0a0801030f0f06110c0f150103030e010215040b04060605010302160602160c0b0a030c180e0717090d090b0901051207090305070803090a120803 75
    0x11089541481201074036664540d100d01d006007140d41180200d50140c451f505012030714017000301c00c440780e0401a468200d0300380e00e155501ca040f0280c0c800115400141d40c4200c00000c1c80d5406800b50180e20007100a4035198043d800307504c0c09004a2948848d40c4c0840c4c144905080e20342e5120b41569007504c2c082e460025500c006034030740121003050000d500000d00c104018002840071450059104100610440d580c1c0c000440c00da019988450495010300c1201c0310000720958018100321440311803c5401c903a0300e4403041e000f81c0320b50388102c500d005c0020300c02e010140e251095140040302070900f0080b1202c0f04214040f00c41b414000c2d000402c0c602d00208000c00c1c020400303105840c0710340451802c00d240006800313440d401250b84400102d0404800400e80c901c601c1c080d942d0050042e9512410240e41e101c0c0c0300ca070724a001d0107003028800c18080c00700c00f08000741700300c03c00b40090400840d6140040e20501c00d81803099481038100c01c60380d0028000049100e4200d903005501c007240307a80011440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652433129 1250 652431879 652431883
    0x1050a0c121e020f010b0109080c0d050133050307060f03050a0209151c290a0527070807050301140a15020c0114090904171303031d010f08060111 64
    0x74030802c0301c4480c0e520003403440280d400503000d0208101080207101500040c001922400d80318040d0490311303040790320705510328100f50341d400382d1081c0076500204000c100300c2180186d10b234440907105032101403004025005802c101c48000140070a40c014205640361060040142c2500e80c1070f00c0c101a00d61b000314460141b80d03019150300501c0103003400a000025044420a80c0c4064011075110b00552542d0b0f680c0442e600c1040c142c0ca010804405008040188100d9665030a410942e801840032030007145513103d41440740c64074602c00400200c2c003c034803104003180c3c1d0401420101000342d484104500b441d0720605032411070b000145e40c944120030390000221100060703040310199898100800f01c0c0785a00082100d81490280c840003000058002041160700c62009032a070854110404130340000c01c10f100e81c50300400a0300200b400c1c6054481c030040f05400aa02c02e40004030703e081c2140100120348090401c907282420030300c0326017903481405842a5002080b00e410304c000c1a108000311401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652434379 1250 652433129 652433147
    0x5060313110415090c030b061b0a050303070309150605130e0a050d032c070611031308030a1d01080a0506011701170c010c0c0b030601031b03140601050a0c12 69
    0xc0100700b4806828401d030241c030b03e03141c41c1c411001445e04016440c121070740a8807940440000c040e00c003c0c0b03040f031040b0014800040c0f80401554a2040e9054400425000e00180d4002c120076580803403403180c81d0910b1140442080c0303c140f190762401c8400c00256036041c0c000c0f0004202c919000c56224107491080c1c0c14140c803500043c00a00541c050801807650580c802020300c003040a0980d0300c810717003280c81512201041d10081d0b031603101e18070601201c1c0c002c4003007604a1400340d04981c54041420340d24100c2c5d0700c40340c1c07128000380d202007424101503400c0000c40408070a0685c800086035002c03400200480405850300350200e5443c800b2a800740d00ca03440741148450740c008001e00030750b500c81004103041103041d0702c00403500607410044002e6120314010611280c1200400103010f04101070906144e0010b014581032607950b1020703030111b14200020720780c0d04070551400116143c0c020f00e035184858004100d2410403200700150020b40350400140f10416030400600c5141d0780f24580150b070f45e202 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652435629 1250 652434379 652434413
    0x60114060f030a29030a0807050705130204050a12020d0b1009090c051207240c0c030501020a020606060f0f030a020d1409070911040e090a061a120705060313 69
    0x10380001000038810f40b40d001402c02c15003049070b40028583d0756280a12850740310640b0b03689600701c03100000c049098007015001c001e005000f40c810300f5a41c0c500040d8130207100c4000c0e4203170540106081015140c007492000c010010281800c205c03c3c11540010790840443c540101090b8850012529918034900c440700544001d60041003c20180c1c00e0040c02240356101d2036210b8001d10510041809000c1442400c440b000480d64041001d101c4e4880c0e0b80005000745502082421403201e400300d14130210480065025030001a618500c4940007801c05a00600590145204100c000358010011085030080340f40d040f5050780381e456607034500c00a0300c40c000041c600507050407041c80c131502000300003170b00502104003116521559441110182c07041c03000b10129440051004200031124040402d9001140c101551810340700c0d80c2c1c0344001c50744001005e000008440640c0b600600b091564091400c4a50004183c418545000a103603480018101c1c2012043c0c642d02d0410030411500d9651184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652436879 1250 652435629 652435657
    0x120703150608120a051902240a1a0f0607150e03130e06090609041b0602061506040806150109090f0f0f0e1e2103150307060206011406 59
    0x440300111030000360000b030041d0821030084000e00002c100c40d00307040300c80c0400641c5034142000040100c030752480800e240040d0541c01031030aa503110f1646484206040c80140c104481c480c10110114400c03a0519400018520441345856a441d030341d1003409240110704880c80c0d86e03110814580104944c4001030507c5046052034000b0624400201c023078a41c0e2459a0444ca850550718071b0035122074101034840c2500300d400200407808500741003100d154454042d0b40da0322801c1c80c10182102d02e600c6950b01040041e040402441002c45107050742c1500e07508100c03810f1b4189414002e001c2d0b203518001d0041c1c40c0c02031500744504441d900038000d0344014030607003404121040d070710ba01c0784010f0000002142d1140381b501001080002052081e501c400c0c40703410003004241d1000710707911945000c07106064200c0c815a04445120300c0110540e4501e4450002e6507074030303401c02e1510002c80011010096101341c00008050100d81d9001030558119107005c144100c00c102c085002c01d41611440701010299 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652438129 1250 652436879 652436903
    0x40504050307061506210b0d05061006050c2a10090303080a1406010825110601090e031207030b09011217090102100b041803080f09061005120703 64
    0x800000300103081881d0050b0001c4c821100e540442c850700348214014900400d1000c2d115901a0744034050580000c1903050001903402031440001ea00000c81d44411180350384144104500000b00c1c841140c028491070070081e0401c2119490542c642d0880e8118a0040d0108a0010305c4541c0440d00d01c103c0743d002904130011040c0c0000d0003000c1283c00d00003940812441c0020600500448c868407500c0d088491508216840d003000465000e43c0c0900340070611500d000002a1303031034080d400c4200c5000d41741c0300c03e5134228407002003d0034040140e00c06480b003482c210304001524004000c071004c5507109002c2c1242589e4810040c0d0042009021290b0020400c20010494580c0c0f0519001c0c01030142805969900462940207070b98824034050600503000056420718901c0581c1150500c0c000081000ca482c100546100307050000211080c0c0000d2040c030300b17200e542c0461000180c5c0024011001c0d0510b480d04042880c1440102e00c240c0d401003032860031000d03082c501400800040e5174083d06142003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652439379 1250 652438129 652438133
    0x915030f010806011e05091906090b0915030d11030d06030c0e060406031e0602090d05031b030702090f0901140702010b0102070509011a030c040305100914010504030801180209040504 80
    0x3184400b400b44440520403800041036650008014801ea2000f08200320006410f103400c1c004031550180941c14085948048190100e005008100c0074005144000030714050010401014020282c0341c081c10b8403806c450b0b048662070105502d1400d001c0350070030440c110392011a00e4a54850b00800c04801460043e000c030800c41c4400a40d022170309101c04030081c2d61220305c104000c40c3c801c3c0c40001c0524154070784070448001c0010480000c40d01a41c001400e2038040c10114a000d50300c0c80003120035802c00186039020003148a282180b403000400118140301e07460b404109075850140c8240348031003181c03000950340c66094100401841a8400303e9519081800010b4040d16008603014007602503a44041031790309020303210b94103d40e9024280040500c10413000340313460f400900309000b11002048048081201003180c01e0003e04054000a4a000a0700b001481e100c0055500440c0b0b03410103040c4401300340d2100c40365055401400c429099828480150303402881061611038211307041004000c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652440629 1250 652439379 652439401
    0xf1506050406060e2206210314030903040605030a0e011506080117060f070201090c150923041a0a0f09050a02340f240e0a0206091503 59
    0x104450041d40c1c10302c10141c0310003041c0c6652036156202e0b41c014000c00241130400740d9404140d044540203400020703996445d01c82c128041c0d6220540305810040c19584241015401000c880b0a03109044500b03041d03080c001c030443d44a20662048004202011022601c00281a8040800040781d0340c020844526070660000503c441c51185038049001c0b0000002d04000840010300310f00300d118003410032070341d8503608100d48950103040300085650311500c101c001142c462001c00940040401003042801c2e410008204a101d9040700d507041048803c1c510802d40c02c110034005007102110080380340703005003145002c1204200040340c0c0c4000ca42034001044045141034000b601d500d6101880310340d8550080f132040c0c1c418100b0b102081c0c0f620020783e40c04030302c039005501c00982140000416100198441913096070b90804203a8403480c070780c1c5641121050b60082030108500c0010148620609200d0309900d5509006001c0e0040c1d01c002000c2e801507540c00d4100c00d80c0700c3c40b4040c8070f8503402c0c103002c424 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652441879 1250 652440629 652440641
    0xe0603010b031b0904050f1204171506090a091509020f0303160f060204180203180d120b030a050307050c1306050a0501030c170403050c070f051302070f15 68
    0x54000c0d460002116800c0c2000301d1185200400e0b4600c0f81c45103040070702449040382d002007080d581801400e110349201c980c1409882180703403289001c00c1c0c44d2400c2c00c1f46901b060706030000c24074a41c1d001482c8000c801c0c0b00034042c1980603070704488548041d61025101d6000c0c0c85138080003030409008644038a43d40d6800e030711011446000b40c4900720040d101d40145940c0340b007000a0840c2a2103640347c584005021403070340320492441414050304217961030f4405a0300400a032440c030040340c0c0101c1048003003540b40d185142d841401000400200c004010041d0182d070000041041c9a40c98680c1115192810880e140f142c0c0d6000c42100e58550403820301580ba2900030503401d1284c1c4007035030740000351580d60050a00b039030001071100c0b007200c0ca0080190024044d00b03645000f80a1081310701020840c0609540348a0340c001c1d120565248150b00010b818162943c01003107903803e090405116640b9281d40d1a00352004005c0010b0b520546800c00810541d0000f00040000d243d14803064084035941e0003203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652443129 1250 652441879 652441891
    0x15061c050123090424020414090702031306110114010b070b01050a0315050402010c0f0b040c170309040e010608030307030605030d08010b0909041113050f0604060b070803041b0e 78
    0x7185000c050024001c0021112400d612161250101300490f4101032403444a60400f070807480f6240c0701642640a90300700f980b00310075031000b40e1104085414401c0d9099407256091000d14902510102d005580d00c20138003e0800b08092017a082c040c52100b5807080541402d0414107204c1c44da50b40105180f20360043c0011200d850102000080d1410a406448180c0c4e6000c0103100c4043c81d01051880140030040041c0e04004500c40c5c3c82002c19111980c0c40d080c54040c07540950540340c203082000001225034007411090805031194003c1c1403004c82587c511580449020490090758080140546200d030082c01700f90000105001c2417a030142e00c0481201c45c19410394045d20904c2e01d040e10300078001d104a00c107154040062a2240c503140341c11640c02407242000d501c07444104400300340c00c000201c041800881c5c0e0750b4203210040b15028092503000340c0881d4107021072410449005032600805a000b00070301c81c04004101004001c2582c2000807183c10501c0c8246940c841c2c4030a4a07080946e90 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652444379 1250 652443129 652443149
    0xc200309040b100c0327060e0117091f2309120306180405100609020d05010e01080703030f02190c090b0f09061201060801140711060403020615061c0501 67
    0x307448001e040c18042c12a03462450344071811084e00c0f0340c9064810011480c42000869450300108116091640600002c0c116a50b02e280c11010030303c0024050106240c15a1032401c01202001050074001800440c204400d0103002d00125095103204041d01801c15111101c01d8680c804024954441c02514441c0d40074800300e0301072600102d64400c80713120607194143c000006211414801441c03540b03403034029104200301c541212102c0000000c8402c1c036000542810340006015048140ca0f005581c090142140103481d154905440503607220759521005043c408140340c0e0f03d03822802403010000c5504c02000c00801a51145481180d1702d540d8018500114030b010341c04652424800300304819000040c08803440c40c0c40da001040382c8040b00b021508259034903840045840c410a001c0c80384c04c00800c420702c207083c0c1448200034080060a58042c5020382c802400c1001196000505680260001050a07521400500403c0141c880d24612000704400c42000203403510103580018120380301050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652445629 1250 652444379 652444391
    0xc08040b010905090615180106020c0406050405160f020f120d050a05190216080d0912021911010927110a090504320103020f0609060d0c20030904 64
    0x340404490054844c40000e900141c005085061194002c00710820001d0a00d80810b1204114a0002000342c02c0100181c006d000404890300303260042d040900003c480510003490454a140249039102c500a0100440b50340d6950342d850080c070405801172400400d40e07e0118289403003603400d07130228070341c8c90003541303040000356a00015110300c500520703c0b0301000c070038103440f1003011001c0d400104a00b46400e840140c0c05002031030840081038105884036001c00e0040460500c407040254442c0801d042d0b4008040c009400b840d40841c0d1599107034090700a00d203200d00c480040390a409507820118a81040300117041c0200d219542010700c0105814040c04550307e103098036082402258902c5003c58190b40040c0014601500071401c6090000c2c80300c45900c10103d400440030710b00041d05640300100c480180700790308055000c10701c10305054410342d02d400700140200e4070342e00c00c0d40100056540d94210f102d1005201d40d003686079040e011500069480219442140c60b9800454128800c501d050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652446879 1250 652445629 652445639
    0x20d060302311b0c02010203043507120305030405030403020d050c1207360501030804080d02070b0304061805030a1205152404120c0e0a0e0618100c08040b01 69
    0x3c09860106020058080074070000e409013035070080543d0f04101d0543c00203000104403403031119071190315516000d8a61400e800442d00308102c86c0207204201c05507401640e8180806000441c041460a5041ca400ca07a2075a41e070601c0f60440c021500000d5000049803c0001404000500800000021100442e000c2103242500d032303407800705108030044203015500b4070021804d8681440c640005000c404000920805070580c02c82d442600110341c01c4c00c010a0030704c420002081990801c5c0d90310b0008059880c03d00c50003900ea8000140000c22060f15192070180c0203510036a8410815071003c1181c2e00d500fa0700001814445110704d803002440e15010003d84081d01c5000b01070b910f808041c0c0a40c802810007071703640200054014160b00145410440000d10701f40f8421030342c1d56640143d031103840303103400d16003c106000e00250001d0907043c242403c6000780340300410443d4010600e281c0c409403d29106c100315040c00841d500402071036280c1103969210309d40180c1c0c0c181c412403142c55048130981e252 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652448129 1250 652446879 652446881
    0x150f0a0e07050d0201030f0e0f1005010503070b0703050c100e0f0102030c030403080603190c030b160905191a030103021c1a0411100e04150506030604020d06030231 72
    0x100c0c2102015800601c040010f4144000040c039214018500071480500c100210004d441304030f401005035620a80c0340d40020740f4103010901481e52185814080b9515001c0000c4e50fa854501400801381c030000b502104043c025811110110071310000c0d20847d022040c1c1c2074000740030180080784140600d40c2c40400b40d12062084901c59000a0101e505584440d28200d640c0900100760a804d44600d811303001089050400c1d2600c254401c1002c480c1a80c01d40c80c024a54042c06841f0992034108010740f190f0740781e00201910141c81082e200b080c03451100340e0b565006840dd603480407040b200d168011100180c06580254141c9000f0754404010303080e051021000c091810f075000c1c0c101c596803103509240c060000b0380d4a40242c040c000302c9942600002c0010900c3d400d800015010903d110b41004d0036081502912210726070004651600c14036220124442c3c0c030000704101e00c25035001840120f81b40050340b02070080c640140ca5a50781054040a02502203221080001325113151207122041d001c80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652449379 1250 652448129 652448141
    0xd110a050303040b0402040b09010902070507060c0f260705010e011a0105040b0a02120a052a030d0e0f0a0503130506040b04050111280c0509010b030610020708150f0a 73
    0x8090300440c5907540d01d03240c80326610300c09441241e0141d140d00d03818042ea90ba68111501030449107400517170714415850041d241a40c3c82d40040b042c41981c0c0342d80000700e04020708212030303650040751201e51202a0000841c0c8540c181c0d044002c0c40c80d01048100c1405815403203000482200002001451603905008030b89100c0c4804081c0050010002030103844071244c060304030b820f0540112401980d0382c011000594026242c4080001c0b00460803401c03100104030340681442501c072250142909608061341c880c42100ca0b1002556200c41221466020411500c03550501400640b040c8101c10b1030300320703102c1e8440c0e007544020385c032030150201ea00d00d04482182c046031144d00321549410716000041d540b00c1d85a2505079554080c00011150b10440001440903211030720a109014490515008d607158542c0e4103c14010086540140311503020501260f4025008440c298112810306074224502805900804418002d0038050f5031082daaa0b131046000d25000000826641d45003408a412140c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652450629 1250 652449379 652449383
    0x3180b0301150c0c03031707030507050904020c0f0f0d120e0d0e04020d1a010306061409190f0305061617040803060409061104050405100303170c0d05090d110a 70
    0x10104010081c41d18244a124035100d15801c0003005000305498200e13140380b15520580c04a00c006551541c0381c0486d010803540030442c0e0400700180d00f40b03402c0040c42401803184681c01a5400282c1ca54106020001e401c0006d041c64125507040644040b06034550701d00c600400040340b401400c1c0c21030440b2a01070241c008074140010304410907103203130450302510580d001d00d0300140d00b000041020030660181081c010444110040d0700c00c00080010101c0b00d49074000c908100d03201c12082c54201e4244211144183c04a5245d0406140c0e203403140c516059036070283c6452a400344002041000c081407a034480d400c080e901900d12040402c00f0b40743c5141110215004540c030f00300050000304c00902071a008140078000207103d6645503a00011141c01d80022645408081010425072600b0b014855100c81700c84861a8500d02e96907000e0b00741d0b048004940c9681510b84001341c80d614049041c0d074009005104244510b0a00e03540c0d40d5142c0a0070400c107c00511030b10107200108a000405140203a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652451879 1250 652450629 652450649
    0x601020703110904111009080c030a0b0408030403090b0a020c01091a071b3f020a06030515040219080f07020309120102220609151209020d06050c070318 67
    0x48900d02c03c000254900400469212610b001d18108644803103405012200e40c1e5114040d800f81000300301d51910351100c003000d210b80e0081e08464006003100c60380e150425400403007951170380c5940c40c0644078900303580c015034840440842c10212060340000c1d0000c0d040400c0c3c0300c0100c29500c070054108001c5600e1002002450100203e44c0056404026513409151001031810b000e51524a401c0c0c50b0883c0c2e0b580c5a00121003202c0034090240e0320400301c110301310000d45ca080e0f00065540403c01d80100c6100d00e0742072582d00d05c002011200144002500c03031340010700c115914580c0700009c074080d000300c00c669070001d410240028000061202d5160041400d03030010342c24030f950b41c401c010044210b01001c6d03034155003c0c441c0618038149403811600b400b1075041ca250207a400c140d4000c0103940e080e44661640c1d0f0380701d0500c0138240c0d003240c4a00e02c0d8480c00c2601041c54003189c0007040e03101c2d021180080400b40f40008201c24070340880058080244a5503da0403000f8006240b440071056500900d0303800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652453129 1250 652451879 652451903
    0x5180d030e0603060103141602150709061101140412110f03160201090314070501120b09070c1109090c180417031b04230d0507180b03120c060601020703 67
    0x2e140c10781c05154001030516000c03032000400000c0071b018800a0320001c0c0c00d03c0300070324698600f42c1c0620075045a00c110200102c1c4516003908010086c0c9101d1082c0b10034020070808001d181079083d00070603100440a20019824181468500204e0303140410f281c000403504090112004070104111300c02d615468019424543d8400700e250881ca00106d04a05020b40f2050002c00500300401c0b107580074032400d0241040b1460400058112058100c0010666180001034181d0342d0317aa9600700d801c1405441c008c1c500c24401d26256400300e0307083d001150301070b040ca000c1100b212030020307000c0e04a80301a54000c00c0340d00280c1020416401c2994000c3c01c1d9000115484681e49021003d0759001010b01301d480c41100d01240ea40a0540c0103401808060541d9102000c9240112415039184a07003034a004800e4041c3e51142600d80380c4a0040c103c004040c009a180030030010740100301c1c240e900a042c0c50401d1501045030200c0d0b44020342c0300c8440d001d00000100f0540c00131402c001181d400008804074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652454379 1250 652453129 652453157
    0xa0e0f010b03180105090c0405090a0f110d14010f0c031509020c15010303031407090e0609040c0515031504090f03080c0d0c020a02030709150b0906070b0705180d03 72
    0xd642004210f40364003665034038800c44100090091900076040000540910f10f80c03002804140c2e0801082d02200ea40b020356100009412010660b01640d005080603411200c6000010748094550780050100e4805d990714005405065000915030100400c0c100009170850380141c003510714a0758102581c00040030300b00000803068004017a0302d0b05003802e8904168901860341415082a0002e600096580440e03240444070403040982081e094140403046c0ca02d0903600015964000345114040c10086000c00d0400803071b6900000548001004440c1e840000701d01c400303082d0011100d00c07030000302009941c0303058201031103010a020380211007010745400d1601c0c16609614050001c1156642c200060811814180300d140d510801d10b40c06003c20701d030307e40101840e01185410502c2c90741d10b420010110050500390f0384007102c0662a02c162a10100d200150040c084d904000c4c12103110346e820000f00c41c0e0b0000c0140320b8400e2030251140314510b21000e00c07981401003030340103001c60395400321413075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652455629 1250 652454379 652454399
    0x708060f101d0a0f0602061f0302190b0d020901080c120601140c01061205060a0e072d1202011e0504050105090f10080a14130209070207080303090c0a0e0f01 69
    0x1410240184201060364002c0c04194a09000d03440300c40340002c1642c050101c16030502c900f581140c1e4119a0b10484c000d28103c801d00303200c0d1440000c0c8902d00085c1400c14030641100110024409049500e880364001004000654045004240080c0b5070400107195100160245d4000328030b210f40c9541142d460708019114580d1801c2c020080060a200038009907000340078072b030041d002c0c001712407803c1c5c0060702d041441c01b14068100c5552504000c12180490000502c0b14101c4620040501c5100510400b0710b074a41c2e2030700301070400b041075044007049858440340a58082e40c400e90701c40280c44207401c3c120400300c40c0f5201c6000000c000b0401042258800e030003900c00207000a01840c6400803520008000d011a00e0220002c1850b0004004a00b00e0511414440382c03000400c001e00c0b840c0c6140301a01a0344000da000b1b20611051340400c100078820080c0001a00b040812240d4900740380350b1880e6220000c6840902c6141320301004607110140b038201030b015040100402c07a45900b04101c00c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652456879 1250 652455629 652455647
    0x712060509070f090f0507050910080a090206070b0105121605210109060b090c090109032306010f0f06110303061e15030f01080c030a11180f0708060f10 67
    0x800d070740b0584002041e8620400c3d071003401070903c440001007140070350050000762500185640140320044c0032402864403040f81c0134840c03141d2450103410f0365458440c104024064684040e41000c0f0205140d03040145032030115060351030841302c0d601f40310204080c09030740300e50598281c1c600c401110010001030030080311002940c0c2e607804117600001000c42495003140c407c2d40c004c0c3c0b0341c1900c80740d5516040c00c04030055600a10805005403600004400180440d006840000d0651980b4040d03800000b0051035803a64030b407410000c0d2002543c1d52002003001d517155004d50005142003800001d1640e0241c01e400090f00148000765042d940d5010400440c490101c80d11070806240c00c40b003051507a240805000c69034500008a82c8a0500d180600b4080c0c01c16080040282c2c4110b08948e11070b0760000e0341d803200c0d681c80020082c0ca010040301040482e240e03090b110212540140c00d001165982085a030702c640c00e95501c5401d141e03070390010045545000340e2102c2c0c0001e084c101d08016548604080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652458129 1250 652456879 652456891
    0x9030f070b06010e060d0c0305010b0405030d05070f0b0408030f1003020d02100903061b03061505090d08070204050c0a0e031605060d11030106020703050d020109110405070c05060702011b0207120605 87
    0x21101080b441d0003c541103506c541200001a5a1002d040030000c1c0c00d031040f107000d0101d10010500b0503003072001199407951482c4001d418840040340c020100161000c00303075030b4190310401107101d84c10285049038281c1c00035a0005141204600000d03a042e200031080b10459400912107400c4490980038807410384210300708101004207403100032000c40c00d113014105081980d01440340c155120000c004084501e00d4016800800c51070940400c01a403103010744003c4181220141d400c3d030307000c0c50070b1040351154a400a4000e41072808101c12200e0340005014491003507110310808005072402c00d42c441444004142414000b81012b000e10300340070000d022040400503002170940100b03040c1003840d4100340e0050006078070641e41031041200500c2070004180280c0028426540b07142e0360b1200307004110800358050b0b5600c10005198070710510305201101e030040103135005400e007114024082c04030b82d01d040d44110f9070740094001c1f8510019029040300d640070920003100080f9902c841c00b52102a0030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652459379 1250 652458129 652458137
    0x180c1606180b07090501032f1c230402030a11040f0e0f01060602280c180f05010b210711030313050706030b18040203100603061409030f070b0601 64
    0x16400c01e442040c800403900034000c0e080000c01d450908001403e00d125600006d0400d802d140c1c0c40f840d440603211128590001d1030944000f0401c03080c200412501407400000d440c2c4c0815040b142002c1100d901190940c1c0d816004a015201000080050310b0001d5030001c0d0142e002070100c0e0f001c07905500207844a8140140f001c56985840380c3c1c84429a00c020501b0001600885605e449071542449403070018240350000c0e1003d095040c2190794030000c00584007051041c0ca04d1680304108902180714042d210040d03503843d8440d082d2200703200030a001e0044003000351901002260a892030400d0b0760444148914209520b410302c0903420031084042c00350420722600c103118007068003081c03020310b11881310414000303810100d90601130301d004010341c41007041c9880c00707a21280e5a214860380351860f4400e034880d46000d40b07030b07880860324007212140ca00421600c0c1000200401040e43c2180075210556510346084d03071941d403404d5440b4858044460100da20400401000505029020f98001c0c01410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 652460629 1250 652459379 652459391
    0x12060b0a0801060311180106090b0913020d0b0a091109010c0501020f040e0702010f09082a030f0c0601090501051807030209090a0b120607090623040b09180c1606 71
    0x10755400d45a16030422102d116980c0c0c5000c2c4d09041400da0512400f407070108654040d45010f101514180480c001d000031441c00007145007a45d04c9610014400401c260811907032108070002a0000b0300e02152f03882c0c4200d0342c049002078038408a00800c144254001d1205140420010040d561810481d0040384c00395000d01401d61a01c41c0034010b00700400a005490807107150100c0d000b0b003110303035051500d0352b494a0441e0a001141e103c00548002103024510082c40c5020018500c0030190048040b0107103100010b048000b1811503c044c056141c680801c840041e601c0e40c1407002614800d0051030b4020500c80e0740d034404400e080601c90740003200d0341001072030548000b004c5140f41c403040307a1342213a464803074487e01c41d40e0400e11886400d01c0c1c90301010b030000d401c00120080c2803580034820201000000c0f0b643d0400e000da4540a0001000b404c40d03e9651035540d030740c4400d1943c021030340c10352082d40700d680c20080917500c1c0307421b552050f008426510b20f488022910007003114607440c02a035000307950704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 652461879 1250 652460629 652460639
    0x30a050c011b05060f01170a11040e01020912070f060801051309150203040317010e0717060a05030703050105040516030f02100509180f060102010b1c2604090507050412060b0a 77
    0xb10456004120212042e1425030401e81f03c0c0301a1340c00c0600341c07003c650200c1406000b00d10f0f00c070400320826070204c034081a110300b01d03240c5178003a0183c14006c581c05900258030710200540040c001c2d00312540c29100c0310036180d03100c0f810b81d50f0b603070248100b0b904041c1f4a04111000d05a950080409900c02d0072030356082511090384504981003101c0407001304131840004d00041800120990060146080b940c04070b1070070140c0104440d2240c0b564058402c1458049019903449440480242c038001c0d00b202c202030303901e05055010701425034041e0703020301520040c0308054400019030b00c2074941120301408100f00c16424824074045000100041000034403502c1c01ea95541503010182c3c00c0340001c040014240081900180c89002d08a641960324000d0b10640f1900c0e04160031076160f00d20010500e0100903400c00c17101005c2d0b007190402a00c990f141c0d91440c0581194042c0007a288401700820481c1d4400400340c03400d01c2280280c04849000425071b900050468022005145e4007400030902c40d03a5030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 652463129 1250 652461879 652461883
    0x30a151202130507020c0d0203030c011a0906030c0306010b070809090c0c0c040b0d0204110d090507030506010806100e090a140f06060a051f0513030308040b06030a050c011b05 77
    0xa608050054003000088005501d041d1040c8802d841d52000300b000642071548000e9961584020114002c02c2c220200109668040c0241d40c0340050300c000034844000c10707480b41d01404c02e6500d0803601c20110038020410b03a0900185110511030080c000b80201e074284401c040c025048024101c0e0310502c00c01400c2016258030306c0c89805010280c44481d211070400b0f041034180071004081c00d000e00c3c80d00280080316919104c007100300d5a015103001a441240a0a10f2040e101e62001040c1c1c1500304010003080010024040b0304983c000c5082c2c88207662124541c0e81c66443c00d40d588401106179400a1018200f401c6410342c01540c21001c4030701a041560362440c010000701c4000350160810100220707811000d010310796000c40100c2d0780c286202c0c00d00000484002c0c104d49c125110041005107010458010303001c5a60380c101085070000c803103541703140062141074200c07012140c03039a00340041181420006051040d40d98424040c02d0000da450004503040120002c0112440f04041d408001003802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 652464379 1250 652463129 652463171
    0x190201110106120807061b05030114060f030403090302100801060c020f010e0d0b1504180b13150516030203071707020a02060c010b1c08040902070309090f09031d15030a 74
    0x89900304c6071300d030840d81c100310048408541d0382c0c8020104442c06000322903481422a8151780852048007954160000031a0b801e01482440b4062148004144030a05820000c0201200d1080b81c01201030f1130341e4842182c04d51420b100f94000b24842c1c480703036001840c0c0300315050240001850200d400c4080c0f01c0003e400003a01840a4071600c40305014045a4a403070f01c81907590050559082c00800c4c800504001795803940000940740481b00d2012a119010084c004c5c01159000800103182c640c000050b4002810140e0b030161380076180c0c0203803442d000c0c0a0700a5a20881654031707031300d80421030b0003c003c590345801001e02d0300714060447c0820060b46e5201c0607002c00c042600c000a991790030002484a5182c010300402c210304c031004290b000003545542114161110b24401517110401c92805603000009a04151b01032400c0c40501300c00c0c003959600c041c802500950750341c0100c09208010055400300040d049411400c2542103200d01c900d0b90300151381210a1510009980342204140c60382c0c0e0071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 652465629 1250 652464379 652464383
    0xa0507063905190b01090b060f03100e070512070c11191509151112090301020706090605061815121e1c080f06100e030d09090e19020111010612 63
    0x403c414000240121103210078054020a6000c209003045400019840e001e010040074002034000000340340201c0181c20000108241d1140302840e0a140e0406881504142c0c040200c502c03160001a0000e0300c0ba9039a100c41c82c0c1c00044071202e07042200140800000250300c200c101242d250000202140c46003030592688280750340f243c042a0030480704891608d11007411204102440b07241c4140810f01103511003191000c9520b06540340169404079002e4090041c0c0038002d01d183c41584011f001d0150040341c132440c0121510701c500e03607480200c54245d9109031482c0c410444107000090342c5040424010740302d208040300300c1c1c014110207801701030510481d62006c40300390040c3d50303020114031114945442440d0300c2c4c18a5015407420003510b035505a00109100d12a450300c40b800050540102004802010007030283c0e240030703d04400181c00f254003882859400361911441070708040303011032940c1c540354483c252066118415001141e41c80d0b00700f00350b02040e5680d0a4005180c0324820000c908040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 652466879 1250 652465629 652465663
    0x12030a18020a12050c0a030317180d050c0c0904080a0c020102030403060f0b0a08060c032206050108030c25030b0712020c01060e070c0b01171e0a0507063905 69
    0x420f10300e0481d0030030605402d014044d150700d44007400081c2e040510718001c4910254800a07503540d00e81c1e5644009400d10b605286405401c2981c500365034010001c09030404450112003414a10105100f502e010450b80500004024000c070740b1420700c291440140c05d401441183e05080d100d403640380c1107901c480c42e5407203420b035a2440307100e0904003c0881c0c80201524405400c5616041110001501c00145119000e0401d198411a140042090754201603044042040700d981c403100320701e0b5a0b5001c903280b40701900c20016400b19854035403440031001c081d103000c10088149540c0d1000305000001e06040180b104681b54902000000d2018203101e229080011548916041200c58901d4010741002d08000d00b007190382cbc0c00b1070021001a81198900b2090914440e44002014282118080003c80c2d003000d18045010407000002d000100300d00030819035a102e0307550401542c410144210148060705840042100d41210381d0140008071810741c5d60b08603000072036640a0401082d1b5012007051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 652468129 1250 652466879 652466909
    0x2304080613060b030a0b060f0607060c080907051c15061d1905010b030f0615040e060a09020307080a020702060409060803270105070b0402040609141812030a18020a 72
    0x21091900900b00f020400340c01070111a9860780760b00071040002442e69010700d5440e18111810b445107000c890240760881c0c000c03c8403144c2c416004040210548038180d0b184200c0c240451146070004201407003103880510000e411180d5038804981284041480800b41d5030745800045c505080079005644a40c40311640c0e500b85084000010070300811844500d05514110040c040590200100c07600061072040c2ca00e41d1359103200000302923905042050180c20400b040004da070b0000d1024803809020126024040143c80f940c3d8801203000849503a00040c0300c00000c21000f0b03c099000304621400588441e144c41d403169624130642d03201c0d501060b010350000816440190f250001e10221459021540b03814940580001304103000c0c441d8080d2141d1800300103d011035440758044801001038a00601070141c170340d800184d500e0030490340c00019401c42a5503031141480840c114080c0e0006406042c2503448082a0b0f80042528150100483d0484c1c1d0b80e907005607440800800040c000d0001070604 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 652469379 1250 652468129 652468133
    0x1b02091f0f17011506081b040f090501121109130b15130b0303040b0f090310060e0c070f0f050109050708011505041e150b0708070605162304080613 65
    0x103082201c030302040c0b00e40d14025503154000240400384048901d10f240c16600d80d21061090f03604840c010002a200c0100083c00203403082c9504003240880e803c44c2410030250380d03a0300d01e114217003c00140040c66551201241038140c41c201c4142600001c80082c8001c0f40c142c940c0d20300701c1c54041a41e0220f200041401300d00114580b030f0001034081090000c0c04d100741270442000c00d03582d00490203284861440402c01e100d6030035001054a1065030018104c4003081c00700a65000142494010103100d6402080000e010207a4542140c5469a010100701c020381309907151541e00c2c2c2400741013210700395220f05962001c40c104100c82400303801a8800000c44800c0c800410a41480f035502442c010703400c00000000d105840c000700503403050840030100340c141c2d003110801e00610035900544c8960002140742d01c24820b083c005814554452503040200c0c0d203c84140c401080c164003180c1d00055541340301a0004112481d000c200044960202c0b41002d84516046042603400c45000ca0b00c20340c142c0e0a182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 652470629 1250 652469379 652469399
    0x313031e182c150d060c0f0504030510110c0a030e0f030f030327060109020d050c0715090501061a070c0b0408030a030b03030f0d0e0d1b02091f0f 64
    0x38401d8180600764a2800b903204501d100860441d448403034a500001a5918200340029000680c010a01c02164007640b5040c4004c0c1310075100789000480b0001045981d0780a1022181603c2e00030340101460b8000b081071202038201d2184a00c203489040c0704000c1c2c8807000b0849000f429111340c64880d061071600042c402510683c8140a11079480001c00228110000c0110794201c14a02c5110b20f201d036114200e250304181c10030401e0100c0c426200001090704007640980344c100c11400c81032101b521200b0a1090724082d803c0701402e80d000d90b9440c00301682242e80401d418622887c0040b585070b40e0384020201d642c40038440f060b03809000040742c41c2004256240140509142c104080c105824007004036924010509240e05050b81d0b56108095039070108240c40120751400705a5032750f10508400a0090611640c6c0b00c1c140c4d1140d5095086c1a60103200303d400712040380e85440910340091303020007200c4580507001d030341603400300310109a039240413020304001b800300c503417151050a2034038207095 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 652471879 1250 652470629 652470677
    0xa05121b040203101202060702090c04080105060f060f07150204080f100608061602010e100c0f080f150a03142401031e03051605010e0d030209060313031e 68
    0x81e01c598810010040c1c025a01070103034095a140741a41080d0701c40328400700e541d40c400d904004e54441454810003d44c80621002442036490480080c0400d441c0e21040c840818040101c0e035502c200e017445458070205010000c2e100e041d0207a01104160071281c1e000034126881600480110340100303d010341440410000c24452003d0b455040140a00d0305140301c2e102d41b070103015104442c0d8421034035040c01c2d200750000b0101e10320f80303401d84841305d89051613240100b5040b40d4000100d607851026000e41c901480c0c80611541d0502e466a00031fa40b00e07660038404c41c4000b5915548002d0035600400411241c1400c1101b00110314010005a42c0308003180396403061a85800d4070300b025490041c400203180e00c2440062001c00205a61004024503054901d8022020780624804c0c00c1720210701403190540203070b074a0b60300c6c0005480ea8126040401c4050784900004aa00890b0030408141c5801400340e403200b05034004c2c500f8010b0010b00582150b044410503000000148444880000d9000640b11034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 652473129 1250 652471879 652471933
    0x301060b03090a060c0c080d0b33031308040305100b09040305070618120804140f070b09010905100309021806010206041202121303050115050a09020304020a0512 71
    0x40c0c1e05500c1c00b202010303035681c00c150004101940360480e0034015401003045c03100455010114644410407420448000d051081c0c3d6207101d04241c40314100e84480b0007590048080300405041ba080d003d003007101246900203401a0941d04104485001180049015001440c4510043c0001c8000c281001e4103541032107155500c02c101190611000035000400c1324a000d44c460004180c1c00003513010411201503011005d04100540a18062140d6000d40d00500c101d1281c42c001d161400c08460099a4208200e004000b9a0103c68140110700b0703031138080e0410041c14901058110380f18408911000300e8000c000010035200c035400400c40c9080c0c403950103140d241d0b00f0386161a00d02074000030340d2203401600c06003c0042a204d4198102e100b84028000c0c02d03540754002c3d642c1c0c00700d81003401c0c0e100b0240c481502e055182c03184d051442003020380b8850450b540241074050301e03410010104029480504100c0c1d000c0100c810025460310781c0e14151f8603240010015100171072301d0316810005103403034a140c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 652474379 1250 652473129 652473149
    0x9100509031e07180b04050c0720011706060d0c02160602010203061503150a06050a020c12031218100903081006050d090510021603020724121d010605030106 69
    0x1e00c00000c0010543e04941101c00e44401980c41485030340d00400d28460311703540160400041011840b01e450041c40780a108805030509800300070848540c12480b16419800202000041c0307034161a54400e49400100c0102907515200c05203400c0300880701c44110308005a00107684c0702d0b03900d401283c202001481580025851494407000068a2001c2121202c45208010010540302421189220707040c0b070026001c140320310b441d0b02c0041c1c001e420440741400188901d0100315001d040545507502d614000b54021824001d400400c000e800200800c04420104182a84850781c1300030003417001da03107010640c00903c41800d42002131030500300400080c1000032000c41000311581c0034080f079018180b20040050044174a240c00340c20044d400f109511000d00108100340d806400c81103e241c0544a5002c940036642e40e001c40d1f07202c1001c4061070400c41982803d000201c0341c042c2c0380207411a170440c10b0014412080084c14081180c40d80712400c10b1360f40d00c18040c484c0d42001d120b2000039101c140c113 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 652475629 1250 652474379 652474423
    0xe090c0a0504170c040e1f090b13021207060e040f0c08040602090604030b0a05090118110910080307050f07090e0318030325060c0503040f1103030910050903 69
    0x500746100b10310030407000308060604180880e5043c041841c200d20002c0051088030389006901742e540e4000c180d10a45c1e600710f011940b050980901c11062600e40c000c242c110301c0da480c0e03400100c1c03445e0300741070a0740c101101080c040760b81401400800c020b07001c2515818a1030400901f44000c8488191410100718907103800c0709841c41e002015154003a070300040150b41c3d189105c01280d030702c0c00b45a1008140090f20402e20442840f907400081c4120040c400800144480440060240800c200050911420190a10030a00b45000e10a610000500103062410fa0386c07a0014a560302003401602c40c0c5c3c000d40b2954100d01c0081c040305008120ba202d05104501000e00700540324425180d514005850100340310016480070b00a40784109800300c0c7d00d000d8814a110042e51203000360a0841d151481c1c40011009640150103413030285400c124405d90520681da15061707042c4002485617498481801800d04581e01d0855400c900d201035914030b501c50440c030007418540808801c1ea034100c040390107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 652476879 1250 652475629 652475647
    0x111f020604060b01320d020a020604050d05070f0602180901080d0201060906180207050c0d0c060f05031509040203070b031306110325030e07090c021b0a060c02010302190e090c 77
    0x30101c4c441796030020505100ca00c080d18010b44d098801d02c0168862580080b40c00000145c01250492141d400303401981c1c10343d58046402c680311f100310f820040c10705440414910118a0941c0070f81200607880c0d564001c18401803000440080c0241e000c440d840d4010540445003d9081c00352000a00c500b880920884c0e052030780c202540d184680c00000c0042c1d0110b81d20090080800041c412340c400034280d0020206035081850710310307519001d001d0100b45418401030450f0712030740442c8d02c55500c52114440340d50b80007003008810030700a0401e0780d05202d010000f0440c4403403000158041c40280e074401201e01254a0408243c580300e008c0c070038200c1801d10070071611099205484020a44040d0100468036015400781c3c014032101c41c414940c0d2180c1c450118810180ea400025501c40c00e0302140c8109408543c0d0700003003041d0b0096144c121400150400c01680284010743c4040e105060241c2007081c003c075245900f44442c03094400041c0741c0740000c0300e40e041180788940c000b100c0d402d003180b61017610 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 652478129 1250 652476879 652476917
    0x507030f1104111e070605010e060a060206010501080606070f020306150f06280c0804080615091e0a060b0c0c0f060f09150405061321050a111f020604060b01 69
    0x1070075044e84400c819410846a0f03d02080c200c80e4400e910803070400055031607407110228034000300ca02034050304044a010880c28000030300c1604952050b0360700c0c03e4543c0c1da0010300441e03030040d4174100d82e03a903940152400140d5003405800c0c482c041941c0d00f4407406594804000c60a05643d00e40d90180104005d551507619800a681010a512244c0c020f01301c1c600306821221b0300c43d001c00140c480c007004607003c0385418010441c68090042001e100c0c4503844541f00308951550191013004608480e000b0146003201004811075004000d144002a050b55031350a40302c1550060780002001d81140ca10b280c010303d0030522109003907000307580c1c050030204403a10003480d80c40396407140c61144182c501d04078494515041114003a010203407405031501203800c81c01c80c0789401c43c016400c441d00c40340c1c600c003031504841c440180790303603001401051907980c02d807101d90a094000e070f82c2c2a0440d18151440010325104240c00703c00c0302c11540140400c0c6031a00b8400119281000e01504100c0c004004020b0b2001c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 652479379 1250 652478129 652478137
    0x210703151a0f0c0604060203071e080a0515060706061a070803180a020d140c10020706030b1c05060a0f150603020c010e010e0a0519170c03070507030f110411 69
    0x7090810075601d03008078a1001890041d602040400e2240104000c100040c54000e58020f03402c1d91180481d9500160000c02d9055941442d40000340f824000100280c0b0f154001c241c00158458010541035900c0002c17803c01c2d48076102c141d5840f61200401c1101e045820030017990b46021040303003403e050042c3d030344040906c07000c1c0c4141242c62807061000c8240340e0038420a010558001c100140c003030b05510344811a0413031003060b0361070741c00b84000f07129807410000340c4032510b081282d01800b02181410030507030040554003a0315410180c0e4050300302c0004944100002414050b00c02442d662074000440b0302598905c00e07100d80800d0900c41d0708040001408860019104541030150712107034a00920b50040641c1d1328200015030810342c241d03018440120300700c400a4029820b80300f05040d07581440c6401564010010304113494400f40081310100c803030190449003009003e6030b2a2083c02c0d282d40f032402c1a140c00070b032121003440c00b00c2810085128541002c01005480034466000058801409406 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 652480629 1250 652479379 652479419
    0x30801080c030613140d080a0b10020606120c060a030905071403070b210103081b06130f031e0e010e10020601063e0d050301032621070315 61
    0x943d510668003000a445d095010001ca8401100c00c00c03403131010000e0400000ba64003c24503840c1003102d503c50304092480c2841c0c240540c001340320399110082400030710300f034840110009005500c3d98180d9641c03000b0080a0300c0039150f4020810745c02500305241412402c0e4840c084041014000310190b4801142c54401c803a140c402e41501c4121783c43c0e041010101a142011340b403d006000801003010345000360244040031200c18424020802004d80d07102030581c0c041e05a6410040d20200044440702000244c80c400d140c50b9065040b43d407070700800000008181d2005c07900901a41d8050b5a000c4c002800080d41181c2f0404181e0a84070040d403100018002d550801c0210800d00e286607003144510310401c00112001d20400004032480f2080300340b170b12140032845c0074100c1e40c076007038038411010b0381d040e2a003241c400300700b00c200f507160001c10601008107850301c1d150511000e0f4a181e4200c64102d4182841180c0c001c0500e8a024003c04591500410503c0c103004c0030001d000004803c9100030f5509 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 652481879 1250 652480629 652480651
    0xa050306090607081e19050705180d030203040510080a0c1b030f1b030e0405060427110406121502030115050c0c0409200603070819091e030801080c0306 67
    0x61503900e0304112901203040171824403c3e07120180500c00e8003000b03440310118103001c41000705d511409000c036081c0c0b18a018880c012060040c64075424604003080100c11340c400d004030b82c0707815501d2022900303081550005c5004914403104119050364036016903000e1080918180040c800c42c103903031401040c030312030028003000083d08850803054003481401c230015910907081c043e407081c03d1030000e04041c94071a0303145c0100e06100100b8103074181805074101c4908518a111a8800302441004c0059101a000e0f00c0091030030f01d0121054485104090181502c8071100c014000f450a0501c5c0790074640340d44c060120b204100401851360424000c0f03910381d200f460055030b102c50380c100242c642208000740c0d60b40146440008820044018205a1040a0074041042c0421590100201c03800201c4d000700c0415201000240b040351048556000040701c01d2002800d18065180d0380c4203400405005581068121780c3c003820316802c41d883c01c0c018504800101000301130f031000301e5204c0030083c202d400c205d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 652483129 1250 652481879 652481881
    0x6040318120210050a18081011161509020406260a02011d0102030c151602010c05160201110706021b060403020f0f06042403060b09031e030f180a05030609060708 71
    0x20b1b40304168900322001e4440c94841701c00d45034100c81e600c4940344030890118a207805904040f02c06080b0071741d03000c01e0203081e10044203446510b030f83c40c1c0b4080c1c100b40c0200403550381309160010f076175501c17640c0c01500c01d08000389003021012140180b00c0b03603001220419a4856648a00144c0c2d00c00820f416000504a00d280140c0040005130b1850003130201c10490340c06842c400305840041383e80c40305d01c0741d000c1c0f000c0302c2c03401e8100070003d034220f82c130088088001860422002410384030010340c00e0007440c8185001900800043c2e80d25003450983d030402001604061502014100c1141501d105c800f0101c44d45481d0503d5680096600f07030344a201d1030b0003035080e030f030300c0300b40d25a20711003910b00904164034200c90460765202c9601681280c0c42252000c00e181c882c000c150141018140d48041502500820504c01c41018485210f2030704074202c01d80d444100192031061600300c015205456095a454103100000b4042005650310341e00114000c0d48004204803070a00005241500031401d82040c65003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 652484379 1250 652483129 652483147
    0x1e0b0f1f110a050102090906090c0d0b0607050d0f02070501050405130b040e031b060c04081515030a0809041a0a170c1e040e061302040b060c0604031812021005 70
    0x601c194908001c24103000390b1540d034081c000103400516520400b11030900a6544840c01c1007010241038841c001400400d0000750305960b480e601110000748018009030900d25960f45980c5028058204080010a8000440c0c59036030108001d0b4003420090030045d06013402c1070042490220f07900c04100850361941030480035511254041d042c1c40d880305081d05d90720711106007645400c80800303181c40460320078200058480031018095800766107908000d03000092910303500741d0740403001400c600380c1d44042c058607100d20340d810040500340b50b104080503911402400c04001c02c4580e100d035408035031020410032550307954441c000d10003901c400442c00603091100e2031020340342c400e4120032585c000c0c280d6512a0500c1903481d03a40034000c42d00b15410b0010105080750305454103c1035030000141502c501c40c0100602e031582010040620241916040c003400c1c0c0304451030302c807040c0c2d025404100740302c0e5070351f54010041c003030a40506042c00d140300b010700460f404a1500040c0c50801c030200040803c40e080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 652485629 1250 652484379 652484387
    0x50721030302131d070801120210080709090c0314060a060e01053a0e070f050f04110307030b1f08010b030402040e010c1e080c030f191e0b0f1f 63
    0x405004800300081044d0360440034000300c01001e403030a8012030380b07140001035a01418880b1030703806507002d04610100210701005031202100540307404288081c81d40302283c41c29031446490954040c0d0781c1e01044c5800800411340c4400340103010180240d150f22014000d25400c50208048a203003860181d507100d0005202a55546074030340c0c0c09800700780f4900881e54086200841d2558000b0029080181c3c080c900c00030b2303680d0502840ba1000801c40d00c0820051031030440181d0001c0c0501410100364210180540300301544100d0b401c0b0301099848480a02c0345c10325404491001841c02c803a01d0070741008010182100c3e5051003060340b034050020000b802c5440303d8202241210070030009014092070300300054000c2a0050480c2811007001149590861282ea0300c1401408145046455a03c8c0d01c081801040740080880c0e110307848154003002806039034801c41c5400d80340000d07840d1600e0040f040440545114100291161109080c0c552403503540e0700914542580c1c00b21784008503050a2401c1d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 652486879 1250 652485629 652485667
    0x8161502071e06030b0118090f0f05010305060403020c061201091a04021201031b12061d0a05030a140c0607110c0a09060314070605030f09010615020a050721030302 72
    0x26610942c080e5030b0354a00d6103502d0060180d90f02d5441c1400800c580c0c0d0011a038000c00c0c52030b60901c282d0204400c110f003003110344c00508071002d900380c041038998803074001000303450003a44100ca2984c08042007209259045c0120841035104a1b80c5034038201049051101104040c0a820800b07a6100c1c9202c2216055418a1101280281c41951940d160518828101109100540e0720440451070204000060800c00040c1c0e400e59544200c0071107580c0342d880040405424000741c8410481c5243c14400041208000503881040155500c500701c8d00c008204e10056a112943c2400511039940e0b4400003003840d96100c03030603140c5425154031103c1082d1800304442a255000305042001164201d403d0300a00152409094507a08440041d50007a039030f684644103481c0059001c2c00425000005103007820380041c09540041800790b22162250b80b20080f02c040540913038841c0844c41c0c1044024400c0000400c0310300c103110f88500d8030754030f14042d505ca0307688014101540001e202000d003154107088 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 652488129 1250 652486879 652486889
    0xc09110d05070f090605090d0b040204020f1201060e03030306010f0c0c0308030a02180f06030112140615180910110d090602090102060c031b0d09050a050c0a0816150207 74
    0x9000d141042c44010389540f580c204010001a0710402c0804c0c0f03280a001180c60b1301801034255081e000a50703c0700901544090402c82c2d12035020440c0f00c0080d084c0740050032482403150803280307855140940c007078810740c000c488107130094005100700710703103681c0242002c030102c1640d00b0003207000c000c18640a005414180c000601c00d03200071051040c0c0d5102c607405015001001c3e1340b40c6e000341000b2000c10621010b0300061b56840101040140080302061286580d801d104440f40c60088046010080c203150742110111000c3c4407036500c0244624010b240a10840702c0740440c2c2c680da0038103841036a202c82081c860544042d45a24204c0d0744004c44604070b0705008480796003005424800e14210001c1d5100c08101401440343c036000c0382806c60000100c1c1d000780c0007a22601d0302e81c42e28048158a540101180d012090780d20245400403600501225000390711a0f405000702002910406c80d140c00342e50404c43d89940002c03006101c5212030b210130300c180c5081d084500450342c01d00004910340140c42e002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 652489379 1250 652488129 652488131
    0xf05011503051f090b0606130f06020a110f131107060617011401081b04061d0f010f1406030a06080a050319050a0e1e0d0f020f09040c09110d 62
    0x1001050100106403080c5040400d08000240d072007050404041d200a40300c05804031045d80042402c501e009402003074090940315842c1809551000c0c5d0300110031080d401980960010000081040040d0000e221140700840d04080104c500780e002c1000440381301201d0400175070b1a0003041d4440015810f6500d40f40c0d01c03200500c00385407201120040382c091112005000d600305004804483c5840c0800b41c142c401c604014001c45c2c04203091062202c2810550720340040c0c0d145404a0410141001c8104c103400f840d90084c0729090200d40d40d102042c050b030010b440e2414401e001e012481c141e82c11251440402c840d07a94894a0f03140510b001002140e00080980c0706071a080d100300308001c00500601c40b08202030f89540d140060055585100d260682000602301c1e0300074101c40d24140700c8540c0d05000b080754940c0f1a0000c82c002c40d0f0145c0401d01c041d600fa143d007203010004c5150001106981d10015620800a404c0039540ca1145000a005103000319444100e0306041c0d103100e02c20341c0c41b4130540c003c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 652490629 1250 652489379 652489421
    0x803090a153c170a0c0c03081b0f070507060f020a0303150f081c0c02011e0e060301121407030c120f02030a06020910080c0d020a021f0e16030f0f0501 66
    0x280281066000a00b84203540d0034803c001101d0050b50f10a5480c00103807a140c002e1061507590b8101c829400c0102243d4449108810302e08088520f01c000d071084d5004d08510b079503980c1c000d0820600c9d0280583c810300400105640a1040582c04224078a403580d05080100d5045141d603240c5000002030b4108a900c1c3c0140e07240003900d014002000c0d007000348106c5050b40c03104240d0351701f11403030050504040c1c00724100c401400c4850341e0100c03200700101c0041c900100311000e0303d00041e031070768800c0e80460006540d070306241040c0701c02c1c0b01480807010040310081114900d1a510300c50364042a1081c0941020036a600714184030a0002c40140aa401010307240164040e24240380250414060700d030064442c0030391000c8250203080241c1c01441240160b50500001020050286d0b01c541c2d01e55045000300c0811503c1d801d000e0384844422800c194001c1030b80c1c100000344500c0c00704800c0c80c603500c030721420000b003001c02d2080c0b2020b00300c00e41090b8030100d542a9130a016000d003921500700708a5080e805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 652491879 1250 652490629 652490747
    0xb120a030e0a091a060a0203090301140108010f02030f070311040b040e010e01090c0819110d060602010b0904030507260c0a030305090313050420040803090a15 70
    0x1100340054107000301c0380507062684403050b40c8100e034141008150706114000c550340640c40c0520182c40c641040348101e03031400c1c9501c0082400d445580709000003040e84440144000e600c03c0c002d102c0f0107000f0301402c50451800124204a200016051030b043c566106002104080080200c078043d011030f003543d0341d8450369003200d400000001d105070440360f4480b0340045807581c3c050180c154416125500c0c45010b4803110244c1ca01103d90000c044809940c07841c0341c107159000e15001d0b2109802000d0700041803460440c019003500d55807400144208108010000002d402c0b1041d0380126401c0302a4225041202600c6014803000f0925104410000310708508e0040c000540b40c42020b20036581070190781c44180c1039680d0390060700140381c0303103281c068018003460170b01d80c0c07014440200700b021010040c04105065202a03000c6c0c1c1151b04e46400002c5e1107400c42c10000c003032000401c00c44c00d0500c14280c020000818800c42942010080303140442691551807410b03034160001c02e5000c2107841c0440c002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 652493129 1250 652491879 652491887
    0x2070807081f09020f0f030309100804120f080a1e020f221805040206190504150e1e040e160f0b031621050112021c080d0b120a03 57
    0x307075044011101d00b200104626a105000c0c07400025400780c8004070421041c0c003003001070000e42d415070781c06120a001000603035442440000301c4040c0c5884465240c00c0134100904080c1c0c074a6144018043c943c002000466070001200c2d90205070180b00098030500c000195401400b8501c015050b2070000c1401040e9144903001011a00566503203440000c0d0700741d140c1424405588a043e04042510030030820411241d000a98060300c024800c6142405044031001030450380c03080b40c8006100454103204441e0090f40c1c030303202d0620300d0400701010200403001a05a01e480c489a52350110303021044001520707030ba00701c1002c001807041603803508194128850810305152080101c140f202d0b00001481c4040c1c0000c90303006640d8143e580d1140030003607000381c2d002070600111742d1801c4002030701c840036020248180d83c081c0035030800e0000d50403080d004110b1920018408590008280d011501c002805072040300c0c020301c0d10340c00124031898a880050b84107042200c902c0b80701d01460445108042e40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 652494379 1250 652493129 652493143
    0x30305040e090d020619180606080d0203092b020a090c032a050309071a030a050609060a050909030708030142050706110a110c01030905070b0306010207080708 70
    0x29070100e09409a0b00c042006580d80030404650015801880124502103c034030000409034040d20300c046240c00b20495004000c266030706e02038a4a0b0b41d142d00a004160040c86003027010001da20085040c801d4000004480034480c1c2041115112001c1c8010001d6034200c0c20420b0070358008294210480c2c1d1100170a0180852564003400a4a0010b0300d1040031600d56401d100c1d4a1160480740005401650559440e4030161a82d642c0340320f90040000d601320f42c01d85031040070500d651a5626820002101400e035000074280900c200110800c00c0329903210f2500d6502180c2046907400c0d584e458240303025045100e03410f03000c0c1c134418000002040c800d048131407880149d4a4011400c50445126071200d20341e56181c803100290740882442040b200b4030800103480d205001310000107684c08030525030301e4a0341c840f103100b5002ca0b59108004134403020900c4555540c50080c2005c1c00003032110781c0c41ca40c40b203074103006e100304019001c030102e201c07a4420003000f00030b060340351708452800e6190101580c4e941a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 652495629 1250 652494379 652494389
    0x1031e06110d0b0111010c090e1b07030f0e04020a0e10090b070c1a0702090718050619081018180c0806160201140a0c030f0f0b0103060b04050609060c0703020a03030504 74
    0x401444001d00383d001407185002003200c0b83d0f91551823504000c0d130800700d03030409000040284138050039800603680c03040c01030205503c6a21240e541500706400a00070156028034180700c0e07481800342400345030300698201c800f00002c5400220307807032845009548480440d0080700f096000840e48004000d501072125042d11350304105100340700c4101030b210b211032090301c034001c1d04603600e60085a61140107000402d10009030400181641d611003011401c190001d883d000c0d00311a1030040744103200d800c890f03d03940103001c07a0707501c07a441c42c1010001d15000d600d4a00c444541c071369801600c201030100c04681800b20394400102c0d0006503071904601d6945c3d40c140d45c11005404800c11480c181030051281c3d820000c10f075041c445181e60392524541c010228489120181a214640340b82040c0ea144141d02c42400001e20000394507084100040890b11a50450b800a0f01c042000b031055540300c0013990480e13502100e50550703828032405076606002181c2e0000750001c0d07010401004264000f40070b481551 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 652496879 1250 652495629 652495637
    0x320240606030417030414150103061d0304060c0204090204050c0403030f050901120b18090304150905130b150304030905090a14150301110d020a0908030301031e06110d0b01 76
    0x2032248400c0080512041e20000c0c1000d001e160f2010007852440003456019004803441e032411000e00c4000c03410305076440a0355880c0251903005000304041446141501c0d0400740711401c01d0401c0d0060b9658a01c10b5010709002d00c41e80f8501402199210b130003058a10b90301030010b10180c100015586400e811500040300030880980500301000d2041060b58401c0b40140d540811182e030082588004100c0036440b80e0b0031401f0700480d1692000d10b1401940108482d40081da07a4501d818020441c501545001d07030104021018100540e03038900103030300c4030308292000028048601c1c000207403040c0201c0f420300700c0c4c0a0703000c41044240354000801808442c000e54003240240d403140b07030300002c4482e41001c001c070b210b00c99808989260b0301101e44910152015000042c01d0742000034401040c0c0003001e400c0b035941e40028490701d1941c0e00112600c0203264401c011070455040da65140741e401c0245104004d101824203008092000a8020801c580d00460010765654207258010001d0844c0d03203d901c0c041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 652498129 1250 652496879 652496881
    0x20a0f050708070f080909090706090807120803090c03070306050403020105010608041a0405030d1a1003090317040201030209040c0507030305010e1612090203071d01080705010507032024 82
    0x40d004008550929500405052034080e6650301c181c0351082c10b0030140c031001d1050041805940324a00c80e940074604240080c04014035000c00100444019000150355030030801d000c00480fa00f6200a418165024208680302d54484d106207140c0005900c1c01d5925100354000041402501d0740100d000d80d0190317009101b0f50703803103020076650107105540090102d012142c182903c0c0f20601c0318503401911070402c0c1c070b16040b038a0444a0954040100d01c030300250500701d0984d241e280001016260940c541401c1c03207411540d4501910144104440c000c80c1e00310140018210383c406e40c111005080e00070402c12486102810040082c0c10940d01100407a2500c000407404040403940c151054150380080d8040e01011141180c46140b460749040840751112440d1006070b4050012174040c1030f281d40420013024613400d1007884010103900481182e00140c4003404a40d074010100e07141560035042440c0e1042c40320140a03e844904250094a8040d01c082e01c7c20482c00741c4580f840f082e0340c0c684c0d01e04031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 652499379 1250 652498129 652498157
    0x30f02010e01090206180a0b190306081b150c060a050108010e0f0c060f0405030712022706090c07171804020f09280602160630060810020a 61
    0x2210403412010303505c40d1060244060030070305081c5140300c000015200c0c006a0380d40d098040c1c80b541046941c0c458429035140b01c4150340c1d5161041c0e000401030b60b8028041903114407075450701ca04141000f540101c1c14080d00b004420641800c540c2c0c2d060080003190b086261107101070300141000c2c012203880b5420180000306c150000101841c1111011010f0101401348800b00505540b03c17030680e004040d001d02001034160380074019a4000d002054a421072281c882c410048a0f40c5400d0007039442803644500018500a0300104a03403100d4151481c80705034803a02441111401040402400386651100070707072050241c2406030202082c15141450741c86407003003c010581c06928440c02e00103005004126040c60210b80c0002e47c0101c61f801800c10700d034100d81c1032103502d08d2900844056440180311022030400034000b13100070221072600c050024400300344145c0d10b44a800c20224891401c03a2180c01400655200d0f0b001801030b10200c2d4900000c4503d900c02070b41042160101084495040b81c0f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 652500629 1250 652499379 652499381
    0x120403140a2027011e30051b03060a0614040209041b020a110a030203150c0c0d09051e09040f1a0c03100510050f03150d030f02010e01 59
    0x41d190b841024158004403a04940100c2080d01c0740c0583e00800402e1140c0300e07400180307240b030500e907180761410002c0c3d810041d01e50140b84c1c04160071300050000003410060b400d401030124031030700519000d5040d02c0c10066020325a0b030720369140240c890302030382d041c20306003602550800e0416203066040e640c050352001410343c2150150300c140c0000c501c881c042141c0c0b510705a40140004a00103000060200302141807c21040c5445005409a841807801c40b0601004038040c041c119412030700b540d520b40c2164082900d070b400038225603242c80c0c25140801d2400520505407011a0720a10480fa110030169400505605503841003600541010030a6941c40340f040040c50021440684002e846848950b00d0041150004805031090b280215032403006080c0c20342d2040c011004102c0ba2600d030304011074080c414241ca50301091182c149203050b4a08180c10074140c440003032080f11082d40303d54640e200810383c21042a03000740e1251a54841d102019008450fa80e42e45206034000c200a0503040c55080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 652501879 1250 652500629 652500643
    0xd1e0c050c0a021c170a030e0102041d0709030236011a0f13060804050d110d18080106030303090b07030c021c020f0106090f0c0203070209061002030c12040314 70
    0x640e00c2e00900e65071000750501404042040c0c400d02c60074400c10039640ca8015090007207522411140c0d20000b40003203250b80c180144890801103000861800c2d107030105011614039014030441c842c004040000740c9060042100000a5030050075180ca8009c0c0204800000c105854800705180030103540c148070500c0030101c2605880030b6060700c0c8491416a0403505040d0003140c0d0402c4a000104010700d40c07500746100e210010540c0c5d8071801d1040c2002c6c030700182880740502da110100a80740a030600e102d04001003175448400c0b1400e0001e507071035212000b0407a40b402e40d00240a60b60a0080002c01c041c2e041d4054000640102c11141340d80e10785402c120281c1d1058180c0c0c1006038010180810344254041295010b030106004030740c0c003400c28800150035211154810903031f241e81d400c1c144099034181c5c05803145840315407000d1031800304d02d0381c005081d03008064006401041e808840100302e40c000c01c1211054000c62048850403000103000d079290f0b900034041194148032021010b0400100041c8034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 652503129 1250 652501879 652501897
    0x60c0506010509040f060f05060a0602010207410c091018050703140405160902090109090207050a0b040c050f01030504050a062d090b0903030601091202060d1e0c05 72
    0xc0c0415034039000403c0f0441030040c10503a2448804007419001840d644268a02600000000b18862a0642c1000b1000710107a104105590040103510700080b0b11624510b101c01401c6078140104640110102030061007003008240d0f541c40c3c8880310440140010070956205049910180603551032013051800c4940e1700c03407102c207040d16421001400c400364004503030080d590310b00042d80504134071203d10500c0e0107407002e5403640c00021900301d080000001c641d0151814070360641c506010310700000c04045c0d091143d00d45071030780440c0c83c40412106102d55001e50707070800340030b441509003410400c00140f0580300d203520913540400e44202c0b0b94040c3c000e03548100c1e005800387c14070300003503282c4601030400350200b07100840c409920809101044540d04aaa07681c046000662010311710303111f4250074003d400060740b6442481008000d03030303100d28400180e62403035400040c00d1515202290b5a400756a0702c4400f4079040603032a5500304112507105042c1d459800043c04003625440059415204050b66 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 652504379 1250 652503129 652503133
    0x4030303060503011b2c1005090f04230408070804080706020709090305070b090708010f020c1014010b0d060906060c020913200319081308120712032013060c05 70
    0x40050b14641c6c00a000d131500300031b2601e4008049000001a620318104601000030480c00300c0d01c0b19143c2440ca01181c50300700d05075020400030310f0501c2c1d151134403288100480d01c4040706000180030481008103860407168001000780d2907c0e12414525107898140c0540ba0043c4291180002c00b0110350040d80e862a030151a81403410485440302010040010103400b200d1140301c2001401c80000d12900419440400c001620350089182c51410401841c2c40c0780f040604040b60b50240a41e1801001d045441030701e0392a64a400024001c07003e807450740e00030f0300c0561a1640004200742c20407100e01507244212031255413035441d2a02d00700e0350580c0d00c1010b0000303104502916600c41d8018614401c0803030080445151906c1506010b98103120024100c80c04217010030340c0d03101d0141700780903070000c0c0c171a100146c50b0807803034180300240d50b00800700b002e066001c07606c14110f8114040c2d405022040a0700088000c0d1022002d01800f040c0d00003513102c1c2c48840d24450000f4580d20510110780e0440d40302c1c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 652505629 1250 652504379 652504397
    0x1091202070b0d1119031a090609160c060504030c0303050c12010311060421170309120a0908030a020d2703020d0303140f0106080106080606090915030304030303060503011b 76
    0x104000007080c01a4900c00004c00800c07004504882d030b10500b104150090398045041d403410543c2c0080700c1c1c4075031845401080c0a03010f0000e01d036514080c080c1d0025000800d492003a11102080fa40d003201d1703200280c071182c613000c284403d050b440880003000380d0298a0034440c1ea217854050381100d2190000d5a01d0752a0f41c04010700005002042c056030b20341d0018410f60a042c1c59403611515040c035481c0901104035010f4143d420011052041c034007055101c0880c81c15882c2041015460b103e8180403501101c0d0002442c1290901400b403050103403018800b101e440703010b240f201950380e0307032030310301e0000851410a40c20130f890460361020403403845107040c220040c0c0e10b50740c00d0100b40350f8a001c04500380354452003203001c81146090070340e125508100303034030701d640d45005030240144006800107010000304c0300400c201a203401b8225459a00e003551000b0f0b89580b281e251814151709100c01a0341804001000424154140c01000a0744c008030020064210b02d190380c4441d4140e03a8a146000c41ca00303503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 652506879 1250 652505629 652505647
    0x161202010c06060915031b030201120209030a0c060807030509011a060717031303081005060315180702240402180702030c010204240905220e060901091202070b 70
    0x200d00c2185080c403415003c50f4168843e001181a12107422409012908030a010014803011007000051403a42c60948001c060460700020318011560400100e029000504844030303480c2040320b0585a03800801241855480d81002084241306542080000c1d04000108281810601c6113800000d1a10000c05404200320140005071b000442c058402048040c0002c0018203601b0007103200e00520302c1d86480ca04103a14000d8805800035160700180d4655002c1072081d52a01000c4942080200782c240140000c2030000861a1003166032078480c0c6083c02061060741c40e00042c004614194043d1550000c00c940e20416102c6582250013035408002410452007030111050000c0c0c1111441c0706503494990f9041925081e42d0285d4017600c10b01245c0402869480134140030040e9032340b524034015207801c0c5014005031800c58480100300c150300742c500420621708113503400704103118500c200b81c900c0d40c5000b2407403034001c1400c2e1400b80d038645007140034000d40a101242030b005541f1400d482c241000300b40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 652508129 1250 652506879 652506887
    0x4050a0e190501020412050c010206090d090506250b0105120a020f0906010c050a0f300e01020c090a0605030f1606140909040507090e0c06042c04030e010216120201 72
    0x8000070b4550355420000825504410300d1554482c6001d03200401080c038400c000281303003c42c010040d900a03003290656580c4254040070840c1140c008546142d01c4420742010384031400070a0b0803060180191841140420031041e21090403110115a001001003116806c0e40e12a428030b07800035800302e01c04c2150281c9103071115403180c000006140038074a2030300702d5071402e10b4011582d1040c1c40758a80c4811442c00c0104003103420700d800d4143c00d0000d400c5500796041524083c00c00030088140540d00c82c1d9a9600d904c200000841c414000f4812007190500c5003000009184d20b020f00d5019010f40240c44660362030008400031003030340100c1000e022626004003203a030080c0042003022401c80400a4140c11741c0c80344a00e0b40124040c02c05009094a420942c10032100b4191403034003190000c0409050725955901940d040710100c40c0300707448040210507044860300082c021541e200e8100300600040c07642c0180c800004540a07000c0f00c03041c0ca4444900c89e12003625200d403101e102600c1d80160015486 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 652509379 1250 652508129 652508173
    0x421150b0112180213022214011d060d09050106090510030605060a0e2e0b0a05090402130303020d0806012a051f09030e0612010e1302060f0904050a0e 66
    0x1c02141201c1800c681c0058174101c1140c20b20701c6240c1d0040307140c4294180c45055185440d03000090450203510380360800096492030700265050010084220160b00d6500001803000c400c02802c044d945e5291071b1840e002850710380001d44ad0340d071a00c103000c03403c00380394451140548919501400e8040ca15500c04e00500703802000c1f250403600c1c0c61800541b4820103071009019003c4000fa500d0922040750081c81800310500d01d020b541030000404000c0240a00d040780d42c00182480d209a85090107000304019110340e03540030780c00b124400000400d0550200702880540700f550b843c2040c5440d600e00450381a5650440d01e074031204109646104080b442800701035041c0320700290f44200031040030a0700400300720790502000a403035914203010158004140400003900316205401c1a07141c1c0713041c081960050058100103200c0d1008203c41003281d0788410f4106500404940e9112058150300c3c2003a0410300410f40200d0030301c4045400003506008004001d4840d00c0240b07130200c1d4030352002000b559 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 652510629 1250 652509379 652509401
    0x90b060f1b1b030d02010b10121d07080d03050606121906030809032503030c020d05060a020915090102120a03060e010f15020a1e03050421150b0112 65
    0x48007204044006018800e541d00d1401c110340000100320840249070400e03440d40890811649042c494440c0b903643d114010003030040ea898408824202200084000c044a11980554460310300e0344001c1504002010070584241c1c9041d00c0024030070b41c0301a002c3e10741c01c0c0c600380d5124809000b000350f414600442c450344101900c0001c3c081002546802c811140e4681041d01c8030100061655031b281410440d803010400401c0d0328180e07841d02964840c550b0500d03404000c0030050880c41c1c0d581550307601040620502e0f00700702170300c1a81c1080f641410081d4024841240200d041ea181e28074924a4042038a074580c01c181c02a158201c0d8000903c4100d90082141300207255403584d011510085000481d4007801c20b16546c244080c2c14011007120740000e001410045510903015400042e15031901003844071949035445d103d84e42e13240b80c03c0e02c590085400141c1401c01e00882031220b164105054a08039008846001103003e004036010191500c20172828007041d418655800085603940c07104074508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 652511879 1250 652510629 652510657
    0x170616031e0b0103050c0405010c20091014090103030206070806031002040306020301231011010b040905010c0801060f090509040206130b041a130303050c010f1503030306090b060f 79
    0xc4440c0000580c21488540d001e0704560b92080c203100305503094030640d608900d54100050a0901c0c02c40002c10b203410189000b1700003000c5611408404807061100000c5032401002160145404c0d030601e08960b4403072142c03060704c6039010041c0c0c40c1410b000c1d0449041e29010f9028009981d1919016103100f04c0240c042500741c421483c01c1018546280302810285206080150392545130181c400c890071100030083c21500c1d10007462860950361804030309141604d608086440048000145004094030310000e90003504141103e01003150644c0f0404801c2c125886070b43c11030f600e5420864501c00c1c8900d42001088500c5410f0200380f03011076074990302920050a00380780545101d68500001c50650101102076808503040c004c0c0400300c2e070750811000c0d4089032541442201a290304098490f84000380a1050000c0c42d1405040e0030742100302e61214106c0e05000411210030004c40e038a00d203210680c0060329102022070180d505004848010070010250750400e00c003002c010746e00358008074842c01c0780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 652513129 1250 652511879 652511891
    0xc0d2a0507050a121d100e24030118140405030d150504020d050f0c07020a030b0c070f0c0501020c0306010806070503070c060c050418020901020d1115090a03020717061603 75
    0xc540c8902102c40c03802176510724456040b4251820301d80024003000c6449881c441040d107034001d07031200c5007407440d140441e2041d40c1001c54149a6234483c00481e82118864000000441c09000e5245451446a43d44008200004802242403030b941e4090390001c10542007088000a116400e1300102d0385242001d074000507031903840e40028200d07401400310940c1181c84000308074075001c075044411b41c0f05211031000da00c2c001941d070010714000c9040c00024402840c5202050080c1005000d031003420340d201c10b544100c40031a08040500b24941e2040c02d0062041404100f4070342070101c2c9550403144d0304001890141c0391a03205035550342000b0040000c125501c075a02001c606203000b89000e00c2441e498803559030381003100b0600700c05090601c4041c094010070508015903070014000c200790410303241800e0340606803c4102d040840500c0004d9844180c041840785400e4041740c0c0c0c3c0462071084c1c00302c941c50356681c90100c10b070042011418006401220001e910600c0410203504418240d1900043c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 652514379 1250 652513129 652513133
    0x20306010801051314040c0501140c1f1811100309020a03060b040209031501150804030f180b040602060118050f070806010c060c0f03272004050c0d2a0507050a 70
    0x81780049406590010300100c0400c400e5801c40030005000800000c2e0710700d400f43c1d201e8215a2000b20050610802c2c010240c260725058140d4001c800e078090b21040e05442c45da450401c1d0a171000c001c0007603841054446540010107000307104285540b90701410b045195441c0d615520010594064815002502004a442d10381d130b0501010110035180140864554145207112074003124144011050100d410300f40008a0f4100760744801c0b003441c516120a201500111401d4400000d5226101c411004240403508139008641e4034140c5550303560181c1a92203a140150980e402034400100072840343c0f0115407006d1190340a1940280c0c10b0410301848115540d5050885103498105030004500310208101c041d4180580508001c0030075600c4030040581e00600000743d82014000d1076403540541640003540c89000e80201340c100180304121514280428004551001a03090b5180340342c4a04500442c03407290340c074070000e0b442d050004082c41100720160b40035445204290340c244200210100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 652515629 1250 652514379 652514411
    0xc02010626010204240809060705070b04050f03031501030e07141003150e15030607091413020f041707030f03030209062b060f08101517031801030203060108010513 72
    0x30b51180340c170001c0c5003c50800c08010109200a010399803280c0013082400300e4294081d044d1080280c0040030000700d0380b00e903c0e105107001c1d481da403000710602002c01000219101c0d14450701c0d81800c00c0c2c0b01031203000e1036982d4950316012140616a0040c0d4421950141401c0c5180700503002c591074200055006010912070841e005541d112120308182c0904124003084603074031140300d00e0010b070020310450500d043c014040d1802401f6211811408805508650780e90000c040c800d0540d442d011562070038074134450050f48d0f2190241c1100015100040141d2a00000310001265004103801e580070b00c865804601a40c420182190b0041c0d0500140300b812062200020b5880d100302c0c10314030081c0d56003d0f43c000ba140140d00841031442600410031103038074045262051100f8000380001c0d19054904200c11801a540141e2020007141e504211300c200c0000090040d1005400b1400008580074011030992008a44c840d00117800e06004000e9824507105100301030012501c00728044071201ca4400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 652516879 1250 652515629 652515659
    0xc06021c0f0b030606100c0804080a0b06010203030f0a090c09050f01050a0503030a0c02040c03060812041d130f0c120809130603081602030c10030f0c02010626010204 73
    0x9100920485a905a40907104018800a608000748850030301d6030300294480c1d6005154602808008161100d00f5110b20180c610081c2d006c91599111612030503900c3c0e0b20720000b801240e000000e070010503081c2d030000050720701c200100850111155995041c0e80c0140400880481d0060380c1c040000c030f4482c809005840c402c41d04101ca99403107625000800610042d81e61140b400b03134004112200348558450040b02c80f00380c0588020680c50f0715800103d000b800c07244e1022a403409800181011000c2e000010421500d120803940304200500c0c2044003020025038506500c00c80b40070b4400002014403000e1001c0900604071038808540d0394403050450001c00d103040340c9410000400d800f140ca840703a0700710406181520208105d03404c40d690f45400344600342d4840140c40c2c065075114210354081007001e00b180c10203006402801d40b9404007802420503041c141080e64104100c000140b1306c144584812960680c20410405407580c00e035407448480b10894080390754080001040c141a02c407802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 652517985 1106 652516879 652516897
    0xe0a080a06050615130608060f010e121c0203250b0c18100e090f04080f0705030904020a090513020703090e06010c061103100506070c090c0c0602 64
    0x56001c0c070400a9031410080002000384185c4109000ca8046421a407241074081d250f1008002c03044581c4c0300c0c540d00251a801441085103881000030741a44003070401c1e100c6400c80544c2552017403030303811003000150340005102001c01007248820009040000e044400e02c1c0040e40c1d8030544940c0140c4082603414000c01c1018401008084a9516140041c0a100400c4120501a02154410000034841e540000024540c0c81c5140303072051117182d01101c4c0e9845d004020380010044c1c0c02c010015100d074132052019440035202c40c802405800b1064456604040c034240c208041141050703070400c1541e006221510010340c120075a00b007a0b07070b1002d036000140e40c4c403600100c075130107000d03072003c3d1442d070a00040400c11207100e0019401801c8400d804190151100c003440101d116071a002040403410a1042000710040e43c40400b00413858541542010f046448030300c180d030824004 = true := by decide +kernel

theorem cover : BRFrame.Cov 652338129 652517985 := by
  have h0 := BRFrame.cov_init 652338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 652338129 ≤ n) (h2 : n < 652517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
