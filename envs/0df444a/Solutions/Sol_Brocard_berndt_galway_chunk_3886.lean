-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3886
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:57:40.559975+00:00
-- url     : https://prove2.me/submissions/96b50541-961c-4e48-9aee-04484d25a929

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698741007 ≤ n < 698920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698742257 1250 698741007 698741039
    0xd09030b130827100f081b070501020d020712140301060309080c0d0c0203060a09050606060705011407030c080a0c080609060102010f0f05090c03030301081b1504030f1203060810110c07 81
    0x140c4000c4da00c040100c3d0126460700d141c0d60301d4008036511744049210454260f500603040585004000e042040300c0e607a1900366440301e40b01c4002140c003c1840420301c0410b03a40e05d102140036080040b10758840c00c40500484c001442540c040c155034010030010722403a40304072900da400100503141e200801045c058402150b52900364084d01c15100000e905007400e108500c12280c00400400491b41d4200820403213500403c803c45265480e051003550b442c880e900c5242c00b03071025443c0070a5504500300020010200204500b0b1580d040402104809402c5180a03800c6a003c0d01c2801300c0c0d964200050f405030012100c0940200c1c502600c0e0220301a076503002d18043e0280c801500c2d1005502410980d9a0001380214100c0d0f41010010703001d44413175126040384555024001d0315014124030300c0381072182c000d60300c1070382c51010301e0650604200e601c10046d100302d00107043c100861410480350030380c4c0d0008091800b80065440005814284c01801680c0010444104a8200c0d41d00c404d02035550501c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698743507 1250 698742257 698742259
    0x20a0602013303110f1008010608160c06020d0b031236060a1710142d010201020d0603050a290412110f010501080d09030b130827 57
    0x98058681c600701210074080e8a65162000c40242d96070941d2509507444244510040d4440751955603c040340d00c64010509141140c1c0d02c400074950325011001d400080000c1041490901207041d1926032900030000040c049d40103130780140c850420062080c0200b449100d81c5a01d4070540001c6107140072520024034a403400000719801582171a1820f501c8a07080d003400040f01c0c401c5180d02401410a00d010f04201c865038501003401c01c5c103200b90480314082c162031354601081c44c50024007070801d121821911030f00040e5101070170894003620350712421810181112068809002d8244580c1c403d4055640c0501000070801c20141c3e6803a0951342c6803441c800440346104101540200b100d0a1480f0440300007007408800d909603220b984101d02111180009410300030416000c0700311042c1044500c404a10340c1d80000781c194103117115246407042c0e6541e00d000708070301184180009200070248940100321001c1140c3c41101a10b0b04522900540d64a800890040c54441014510030200c500340e03900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698744757 1250 698743507 698743541
    0x4090c0f0602011103060f06070c09021204030924030203090f0f0304050406050118090f02040b12040303050105030321070c2405070905100e040b040c090305071e0608060d020a060201 80
    0x22071300c40d0403c1c2400115682903100103499250105402c1141c01440220301c62100080c1c04d07501c2d81407050807030300708860307840c910b001d01303000c1008040e00a601040580501032031102d000b10000a488400c02e000184002015004804104440410030480b000000e140e42529038001e1036036030a0b079482c0c00a05c0f840f0310650500d500002c41e5401001d41c480c409100b04c0c0400240d504140d02000a0310040c1040e8965076800c01001911550304000380c0080b400d0303000481554107280c200101502c006130000c2c1d209030020040003003010801030425a81d041056881c4642d541c0d806410b8450000414000d4020a201e000b85420400004521a600641c1d03d1b0300308810384510008585040c0140101031b0441c03c100b1500b040380c4c2c041c00e145d40d401e040003000482c408003076102080907981d9a08428010640089060007008000d0103d0320280c0b620a80400c02e400c115500d0010034070079807240406000403000803941a0712100321000c48141c000c0c0009190300d641e079030003e0081000c044078801e80e40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698746007 1250 698744757 698744771
    0x111030f0f0606040603020f04030206030c0309070807150315030b0705120a09120c0f02040608011406092a0c060c0d0c090302010e010e0a050d030c0b0c04030507031104090c0f060201 80
    0xc1c030500051800395034060071043c1068100b0006a00035400002d074032908080038440080107940700c60045201d110703c14941903c80c01c103200c41928003807841e0401c03029504007450038003041c0b04041605241800c28a000314a4007600c04052716000704603000605403010340000c105503a6080350040580d100c01d0600c070b88040d0307140c0030a40c00322486100014000300d500e03804040a584103100074082d0307034051462040319102c0d680c0094112201c580c004089039458207a00c15030a0824031095610030340030780d44031290b031508215500c05a5200302c05d0750b0380c0c4c084c074548041e444000101602c803c000c1071000c5031308508101384984c0e406e8010b00317948012a070030060102031180c8075050303003000ca07270f8181c43e00d00107041d0010040d5111001c1e104995000342c112040010300da500c460580998600948640f10216011b00307110b017074008018501941c0003003c0000300b001900000703466040b81e4002c540405041d40c0c540000300a82503209001c1c021424644012034081c0b884c0b01c0103002c64440b500204002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698747257 1250 698746007 698746021
    0x1060201021908060604230d06151a0304140307200f030a030f0503060118030b06010201050f1b0912160608010f0f09020304060204080327040e0a02210111030f 70
    0x20f40461300c0e55000b03002400204180070700303241c4a24001c40b6507940381c4445d0141101051441c892034106170354071922501c202407403114400c0c1c40030262500c0401c400c945001000070f4040b074880500003d200c00921b104aa61103042400bd07203281d20342c031022200c2c680c0b40b17010502445007040c81c0315034402d00e210702055006150000c0c1000760240d160326042c03051240c1c00020303501c5800041c6458140300c0b00e000d104c0840c090941000c0301440c07142e90801c02a06140b400242110802000320761001000800c2c0a04d011048552400642a405605954141c1e03000031400e5901d901203542c0080c03094081000c10320f0346041080c03080d14940ea5400e54660790358080080c007501503100381c80d18283e14600c1400481016002181e020707001d800d0251409079145c09003451031340f00c3c10144041d040c2c9070002503002e1000303044146c4078207411602800076980340501c043d250006964001d00c10150084200074046400d1200b04180141310001c000000c035107070b0b817240b9a40c4112004541c00040600003550707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698748507 1250 698747257 698747267
    0xf0338150906130f06080a0303090c050103061d070203040f08030a0e04110904090f0f08030a0b0f0f061608030106050703030b03010212010e0426070201110a1226010602010219 77
    0x86414010f2024040c3d68407260801d004103212031401802c00d88400d00861102410006016014030950300020303902103d0509001d03000e03854010340d040500701041000700100f556100c5440c2ca19500340550305031242901603180d031085e54042c4030700c5040303c5400140460044064441030071261164050390070014104000c079030582c0c0d603030312103207506100c416142c2c01e003503000d510010b120704000581c440e840d458190000d115070348202e550020020420201c040c43e40200c400350380c5e00b5030309021002c100e400014403a9000d001c84600401010031060000960301c0c801071040394000ca01c490352540c5414000b0020360144030103601290501101171b409090510845e91206a0404200542c0e400d04940d0703103c2c14000f410986080d0101c441542d4550b41d030148000030501052000b950301d800e00d200142501c0c100003459489501f081000320013048503004880c01c06d40d0f0a1400c1c10000f00d0528400443c4540098440724480c444400481e410350154010304030008070466054604170303600400c0b42c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698749757 1250 698748507 698748511
    0x2010210050408040b130801110306180708040b150d0305181e090c0d0213030c050409050c0603090a060e0a110a03080f0a0323011a040f03381509 64
    0x20021082000300149070172903001c0c0c143c0505a2048441d0284d50b41400b50030350b562402041c04441c000018410580b80c1100c900880265840070b8011502e44442c000e89042801000a00417840280c0011582c1c1448094410306a00c000e00f00d80003101541402407042c3c0010380c0d014044621145102c41c01c1c039100303142d10b00703202c0d141804002e2100c40c18280087c2c00009820079070038003010300401e84806006d00251402c00a030400000c8428954105400b501025901807809a07103411803400128001040024002500f40c60480c2d036610340011503480c140b03403005c020b44403916004080e0400c0e540070440a0425008010205000052000b002046a541d1200a00482c2c04112143c6440c010b480a860102100c3c100007514120f541201000e00d03403044a5100c2d40ac58039401031105420054030307046c1d0340e40030b010840e050505150880c3c84403001400007a052610100d030100e40142880000308207441e098140c844a0002c070441401c401c00183e6251280c0031a031160010142080d5500c0740c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698751007 1250 698749757 698749763
    0x406050a0209151e04080109020301360519051005011508070c0204200702030d030608070b0304020a08121b0d09030213140c0a03050f0403140a050c1603020102100504 73
    0x1043c02800440f060001d80e000311150302511091400c0241448031240290004042d03c8001142003e0988101401c59105c0400400c485e00546594140b5040301e0414000c0502c110081d00007203091814103504d0102004120b80e94401d041d108041000000b0406501e5000f58010600079070741c8450315001d46220745110100090840c5000482892050404141c2d007030020b08001021301f000c6043e40720f5856205c03203288034000c00080040440c2010048810b911009103000c00c0b03aa0f040000140c1c85440500c00c02e400c080700440894155a5150300d484024480d0404460340d160200210341c5082c4c110a249402d2f5800c41144000305402c003003001e808029595440b0400702d0b04660030810b00c00c007000ca0f0103980701d0751081c4601410124520a41c083c80304202d12903104c005682c0018151000104010b0644002005000010b500410890342c4000e0081d01c003a01e411007400b04885070b010703407985409540f10f102070301d4007503a2200c40713800c066a000b82d083d00d000303c00310322000c01a502c060701c0017 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698752257 1250 698751007 698751019
    0xc01141303050319060b180a0332100509150103050c060a02010209090f0109060b070b07030509191a0c030f04031805090f0901200304121b0b0406050a0209 68
    0x100c400203200c0d000556202455182000000c0012624007013102d160b074008103003000c1c0010303001011010200304103c051204032a202c10340c03420b580c0d4072100b1543c15842c48241c1008000070b110103207c1d4240811445403164200c4840b00041075510002c0c01c81581c0f07040e4540140320980e009180e041645a041c3c0703800400800286100320f0500a1950241e00b000c804c6540c203000d440981d94812801a0260700c00200a80655050103501001c07103000c5e0344031f0241101c04104800001d4100e000b682da1045031420300150356510170a038039040c41038804050340079800700304001081201000038022182c001d00c00074980399550046c000000c0c40b0a4480401048602c000035000134407550083c0315400704001c4008840f03070b0b40c0c0c0220302601d40940e100002e0000d01020403a016000340b00f44281606944c0d640c04403104a04c02c40300c0c107444051310140c0500444450445c0d054060034090b00c0b81a03210105c66001c4400d81008201006e0584080385c105041c4004250001e00b24029143d00c0040200f00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698753507 1250 698752257 698752291
    0x90316140c090c1b0a2001140c010b03010605011b0b06060915030f0a0501120b06130c0905031b06030117010204170d09080606010e04021e030c130506250303060306110c0114 76
    0x501603041c1b16030030058100150301d9540c802041d41c00020f4103074000802e00100303091010000701801d4501a0300028100030340d070060418204042c1e920300c0f090355089032a2103130a03180c440102d030951144e109900d80110113140d0b00186454500c005600c50351070050316585644555030f0b81c0e425a0700030701c5206900b2800000440c0407607403444900d034000400a00c505103c2000720a140d040d41c076601c5241c00804c550180407c0181803c0c80117a0310041400310100343e2603040c0340040d030389000c180504114184102d08401c441203095040b00c0240c8052629071300c0026800001d1039031100c1050b980c1c00040c600000c0001c01305d50001d00d40e0701a9a0503194450f0740501c150611000390060707421410b000050402b2006a288070030300541c000c200309442280d9500e290201c40601d40d12030340c070040c092001001f902c54080c1841400c40c5814aa0f229100302001d843d00301140507001716080644810301c0c00c100c07118040007403802010304403502c400a000003000f03002c4d8115400000c440004c01820b000c0300b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698754757 1250 698753507 698753543
    0x240f0c0c06111f0c12060b0a05070f080301151d0307060e0303070b04050a030809060f040f02130c050d3b0718050a05090316140c090c1b0a 61
    0x10007040002c030032070304940e860100500301d01861000700340c02c001e11a58946040d00507561019030b000f818000c0c03102c148840d626014140e0300324858480d110042000224101007002a1142c03402e54035900700407a01c0d100d5849041052a160070041a41c001c11165406503064010001e03003504041802000b1f408001d01e0b026095610301d0841200c242c0c1800100402d80025244054982c02940268000c0c000b5000c546009808218003500000d043d0b4080000c000c1c0d51102480b0050780180d2001e000700400100d44041590b480c07101520107111810110082003c0c0d50000240c21000c00030001170001581060020754003c14120a4a480e01c01280c08209046603c004070b2545084080440784411781d200f65026500302c100c0d035210500c985940c240a40048580641a000741200000d075180400110000050000e080c074000c001d080d03030301e81c0c5078801d0005100d107601d024006800180d00f0702e4a5102d104041d44032103e6000d08070909640c3e10210300c80011240181944403840030302c5000284 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698756007 1250 698754757 698754767
    0xb0702070e1f180b03010e1e0312070e01090801051603150e040602032205010c030f0b0603161407050309130b1302070606030609390b0c07240f0c0c06 66
    0x494000c4803d901c408040e40d99840034407500c0c0140802ca80a4008030180b40040702d00030040da50f5100403580280318003000c0b401d6410000b0303040030481c10859484185000103880310f50305641311200c2540307050304100d0100540b8107500c000360010768003046904040751041c40d4400c51070003240b04a42044e00003400040305540216040900040c2c600c2c0420034404440104a448000840d826515505090782254242c0030b061017241c04540b0030300040303100101194940c00000c00300f9104824580b240c0f41d01c180a15040c240d64018480b03500c0d965522030800691740d43c01081200e00800c03051464170000421403207000080c00005001748006689088a040a90040324041c0c640b00d69841e000800140d0300d1151901c06481010703150008614003200c801c0c140b180760a80c41c14500740781d070040c0407048081c0d102010f4400000036103448010045000e0300c1c0100c03e42041c008905425640d0064016852415120780700302e80c2e4250026070701c844121983c066258001b415020510020301c0494010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698757257 1250 698756007 698756039
    0x15170919020f1207090506060a051210090c020c03061806040f150504150b0907080a090c0b07060501030c150c0809012105070207060e0307030210020a0b0702070e1f 72
    0x6194000003402d40000940024400080e02d140ba0310144040004602e036000f002d5020300d0403503c0b2801c220807500060503a1180c00c560481c0000c20394005564005441d040300c000d020181000c02c040104034a02a65450044881522a01c680e5000441004400b4118043c80150b503000d040340340c51b26035440352503010a1f003046a0101e9149003181c0450b09510800b4819130003218804181a0824455011960301510007400f42c01710b0030070000c020f40c014040640100170340b400010b491519080a01004455030490180c2000010300c0d00c060040e1074200b0f038103807070081984998081e83d42010b11182400c500098000c50000314006c07010a03d00b0000d88100345040c1008100c20701202d04074041c070441c2c4261100d069a03107a01307021025504010480140c5068205901440e01040001c0d50b6400c142c03100034030070301d4502000e01c0308030f10074440540d04590100b480c11450078104c6c80a9100c50040c041c00140346000c030001080362822210003001c07440301c0219081c0703142c201001c41140c107402d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698758507 1250 698757257 698757259
    0xc03020616060e06041104020310060e040b04090609110a0e2410020109060509030a171314070e0c030402061e0405061605151b0c100203011517091902 66
    0x601c1d207a000800c002d4003804149402400140c00c652a00b0701d4011200c52440a1082c01517106004014009001222850985005045c40031100d026480002e003c1c00d90390082070303003140c01e00c90301c02d00700082a0856420948180d01075880081c0090500c0b000c0141c81c41140802d072211000310b0340c008441c04000b07160040460f6100355848440c03002c25201c45040c4039120043c3c1d540c20005090120074403881d5040703000c00015501c1c084141000501070319150242443c10301c2d0100100c2c0004404400644a20360b01501c2030700c1e506500480310340c50b081544903540604a4120001d0300c1c0c00080401c0341e00c6981d00400450600c0103000040b03c006402031805002c6000400001c542d0340c5d07a0b01c020b01500c5900b085e0300b64009415140c9a81410401500300011035400c00c180408542c2481c400f14800da00080c01584640140c07034011300d80b584050499811602c00000800c0110483d51114200b903210384817404a4161041ea00242c0c1c507080342d0305441038009859031103507140713020145460340d80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698759757 1250 698758507 698758537
    0x20906070204060b030a0507091208160f03200109021507020a05130c0909021e03040f02040504060203010501033b0705060c1e030a0e0409230c01110304030c030206 72
    0xc9a010034210350440d049500210808000c03c40b4044032405090703808484c914014040a2030000e204182000f842c10080086034007140c1141c1c00b042c80e100440804d60814680c010468103401c0c044c00388846080d41844480c1d00440514004405010300700c00307180e0140c01d6440755001c503490440c1d6608880d00413a40b21000c07940000b140d83d5000d284034030564400500141c4000d03500c1c0d02601001d01d650003849628014441c00f105100b04266110407481c81000c0c180d0b45e55228600303003079044101e18000303501c00e107810b0501c8188091f0b81d0180d41030311402c2c0c81c10003d0340c4203202d08010055185041c45500c21000343d441c00260b1400e81c1c0d9452140c0800102e4111586400009017181c000c0e0032041001d604c1500c43c0309007010840302460400d500070001e50301e0012081e400030300c154000c1104a0240761240a07400c200841c03441c80001040d9800f05806407003d90240c5151100e607400580350014820101c3c0304207a41c0040b044908683d0300c010400c041078034590070300805410013444464008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698761007 1250 698759757 698759767
    0x8030a1d040e010f230601081902041508010b070f080903030702030a080a0f0906050703030b120d030e0610050915030a1a0f0703020715050603120a03021308060613020906 75
    0x24a4500521052682c440300101c0d04580c0340381d4a07400c41da10b03040c95014481c0100c10010044c0804412a03401010a00c2d000c4000e68481032540d42140d12079044000c4a440083d0001d03180c0d40704c43c0c0020009100d55211081641d0340c07510444c1c140241103002c0c044a0102c614200040c00c514014101c114019040e80d05001c21500000c2c14070b81c0740a0150359100001840e0b000c13403076115848510a00c002d0a01e40005801c0c450010700c0c40c041c0840090503d66142c4046045613a9060301c105182040d500702d0700f035044100c0c0010040c5c031031100080c20034810a0049800140c0d10b401c0c89003a12005400350105603078461100c5c2011000d480b0540c0c0601800b0740000100e40403214694001d042c0310744030003c2c8d00b05120001c0a00f84d0003846032003018418040d400004848503080b1100e400d5541e004185503c074500007a080100c011014081075400083c000d03410307a09a009044500240030380984000e81e100c0303125842d0802101d61661041d0f1514500303428001550180030182e00c083c052a00341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698762257 1250 698761007 698761009
    0x120b040f090c05150703120902041b0201140601020c010215040c0b070507080c04110a0f11101d070b030c0703030207020603040309080d020d0207051014040e090f010608030a1d 77
    0xa0341e014000380c0300d012449105004a0030140c0c840483c1e50021110305182120070b48004000510b40703101d142603a600c3d0340a0300300350350369600030300181e0b00c0340100250030229450703001c1d000703140c0d4031841e031128446c0e140000c045d5030012803030300320448040e0040d119259040c1702020040c0f40041c802c44d15800d000394046411a401d0000d002c405105100400a0608010025181c6003066540700d00c07490801d40000700c629208800c2e980c482c0d029082c84c1c0c1c0c1c849083c25054860440e0800360007268400c80b64075507038402603500f002c0344024a0380100b089c40c01280102c10344511150007804024481000418401c8500000500d82c0d94000d03c1c0041c280100e80c1e001075003079801560281c0000d0003107541442205018044140c142d1004c5c002049012100c3c50043d440c1d14032403145070b1244521000c00002d40707000d036103c00a940200e000141d07603251541000000340d42c054600c3c0360700f480b42d50301000c0304c03400511480c025580304900860410843c0c90302110f260403200e5088a05800d0391001d0381207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698763507 1250 698762257 698762261
    0x21f05040b0729060f1e04090510061a030f2208040e0a0e120c12030108010e1e1b0f040f0f110f0d1d060702030a140901120b040f 57
    0x2440d2040c81118507041d041103c04001015540c00801c00220400c14010300f80d407011000b2840001c2540c51140b548040141140e41c07480350020250000d09244c110800c2200c00b14010100b444020400c00643d51500c140030441000040910b11420b02000407910031038606044030303400f51030502244046c00340e550303200120003c610821159124003007800d01c40842050001540031510410800c586000001240e642c0d50781d4000410001c400061200e440c520240020010f040b60300da10150390b541d542d2402c40c024000740380200101d000b850720a45407420040359800100480e2002031001407a6846481003502c20b42c42a242c0c000d00380010801103403940e010b10740074003240820000e01c092659001c0825106604603081c0300d84801c120941c0138100d0a415100440b8000200080300310310381c0c1d402c109507001101c201c0400e1040b0b90400000940c00002060600702540d6040c0c82c2c40c0c5501d480300c11a000b0010480d010404944070082c101280340e00c14a50b0110080c00490400c40245041007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698764757 1250 698763507 698763517
    0xd09060e030a030606020721030806010302040914061807172206020c070b0a141303050109050d02010e190803040f060c020d0e090702070513020403061406010e0a03021f05040b 77
    0x804c0c0c50712000c00c01e050b01480100b0043c100d00742c110307150300e0007070702c00c8001441c01d48402001d2040d4030b40030411130392095050390f01900a00000300401031803240f402803182c1080350828440c8111400c0500c48a646080b41ca0040c42140c03508040700b0f4046101e10f5940344020644030042800c1c0c018084611100d914800f61640200401640c43c0750040005050000940181000400400c06481000d034002c3c0a002840041c0e4001511414036004c01c880c401880c1d40058080e60800903081e0601c8400300c2d18601844441e002003003102e0780600040d84441000000e401104224400301000c540148011540b203481425243d40c96100c50f501c150440c0c1000c0c500a0040c0e000301555600c0903000398244802d807504941c3c0440510388158000d581d1811800b81600a26200d0711840701055982c05480107540d0003182403081e1018000c1401c08200c0490b0342a000814000c005200c48c2040c421003010b4940140c5203070460340c500345190030b0717080c154242c7c24100801040005041005200500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698766007 1250 698764757 698764777
    0x5030c040c083909010e0906060f0c0703020604080127020d1707121805040509060a0c0c0b0903070b0604020c070e0c07020415050a060f090612090803040b01090f020a050d09060e03 79
    0x1c0e04c1d107034002c000400001030903031100d001d0390900042c4556640c0ea0016210703041d04c031400e07595450440c003000c141000c8555200941101e004240452110340c10f420803802d06400440700c040c05030304080300340c00c0200b11240c041e41007130b00c0d03041071801700e42812107940c1c18500c0426110700e440961342d01c208600303030340100040015611440c00101220784041d402c0c002d00c4c045906012a06140380d40940360b0502618910402d9612425008440d00030030091052076003055450342545000c4140c2d035180e43c804601181c000c0161000140945002c0c8207a8141e041c00d20001e11a071703070401c81c23000480322029003175401c043c1e000c1c007400380141c0d03407400b0b00308403c4640c01c6015105441c0c14184141050075801820601041135050603443c0d030300400510807515180360610740003003041340c058001c15400e180901f56950000411080c81180d0100504031000004100700c0710f10707000d200f02c00302e0050342c02400005104108903c1e001e070072500302442c0315004840c0003400b1800342e000d25146074800301d008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698767257 1250 698766007 698766121
    0x12090c0512070609050d08091912060501080d110c09070e040e01020702040b0f09070c15060602160807061b020a0b120f07020106060801091505040f0605030c040c08 72
    0x3e200403640103004000400c0c050f90b12000164241c1d5500304a030241c524154040ea40252505840c0303203000d58920001d040f102e40114440000b8108900a08800d020f82000c510071103c018002e10310a00e840030300e400c1448041d002504030401000400303400038008404001003d1a040e2241da01c3d4441e244e01d61000300001030f07580501b8411b00c0b0907a900380042d584640190700c0304800946600c812154000e50358a0552013800d15407500ea28800c401c54103507a9500c1c5081c202180303580c0c0009031000369800c9600c1911003140c1e01c076083c2c0e95601c041e004040014818100201a108000042030080741c03009202c00f080c55102e0a5080040e000104041c21f41040b240c203020002c0e108016181d000503e510003031001901b0070001400e081c00600c62106071959400103090200c01c8030b0120f0b8060708000303000b48001c0d00c00c8544031003d01154020349100c1e0213001c034a4580d41c606480380300c03442040f90b10340321036503900d4002e01e028103883c10140041648060212032100c10000700118190000705550f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698768507 1250 698767257 698767259
    0x60b0d0c030b090c0703120e0a11030c04050103150c091703040e0114150702010c0218100e100b0a0c060c05120105041812020c1f020c06030712090c051207 68
    0x24141c0301c0b40710015000f0116035060003102c4541c00c013110021905810310507180031000301840010650140000e00a0090140c0300e000c000850500c503032010800c07011282040008400c00c011180c0a10008110403645605103024a080d50041d8080c5000c50408502e4555282d008101c03030b444100c4103034004e8000103001d0241c4820071010501510501107003000c1a8003642c04142801c21040c461048100082258011607102d001180301d408d50180c1015442c1002c04148400e2240541e580162001c55081c0483c02c10700c684c06003881a80901100c0c900c0625041c00c81840d0381c00f507110300003040304000620021460394000d641152401c2c1da42d0701d540300c8541e9052102480c042c2c200d17522403420304010101c105150a08440a56088030780c0342d5610000d104103910741601d024665821002890210400607605411000c001c2c0054017515a4207507440d0400a00307101c22512080840c4000c0c000081202d82580700305c40c0c0d648a40000d161268039000003d01044000e1a03400c01680407600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698769757 1250 698768507 698768531
    0xe0909060601090f030b01060305040807081911010b0315062704031704081b03040f0b0c0f070602071503060504020d0911060f090f0612071101140f0103030305070201060b0d 76
    0x80341c14021324800030107072421421aa207009203001c040c81f8030820141c42300041028020204102c55030994410416a41c80c00300c80f058062070881525081c01003041400c490f04460418043c00340f840b04020094944441c00601e000c80220001e0400e44d00b011103600ca011424400b41514a807610a04200081625040c64003c0200700035404c80c08102d50028240030000340d852041c1c03213801c0c4440c0070040b0015480c0540e41d2441c0903a60164161003c5813100003080c800039001044c82c0c0ea4800c00b668014880400c801d41e5817400d034450b0704010381c000c000400103a449180100c0c1003280c1450302154850342d850028041c3c0c2c00c102000100580d58a0581c1c08000e011360b111542c02c4009d4030964100103c00c030b10510b05010341c4450700d00071107882100c440160798100880c1d001d1004004c8003105418114001005082010441c0d0012740ca010801d05d258011882000e100e1030780384a5100711a801c40d91304401a01e0041d11240c290341d2070b18cc001c100903c6000140002100b8070700d00003000c5044207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698771007 1250 698769757 698769767
    0x41104150314010c141c020f0a030f090209010b0c0f06160f0e090106050c01090803310f030509031f0c020d03020f18030a140c0406050415090c0e0909060601 69
    0x40040032031603141a550b14181d503040b0304117400d18a0f011005a485601e02d10510500220b1807401c4d400300c91001803520f07410b0440c500607140304419503504210b24950248540c2c11a80e0020000c1e42c000c030303190010800000b041c001000030440318802d0350016981411300ca4030b0300c10103445550340e807000003c46551040d4403180d09201c0000310b2405080194948001c515002e00600520041100000b0070102d42c0b0400d4011004141d4000000c968901c2e002040200b01a610399140c00b035520961230065004100d02080d0b840990080c0c1540c0c120000c6642c00d07641d65015034480c540601030f1981d203040d00032855103020003c2004420100c0c402c00c0030600241800c01051002c03080c503105100d605903e400301c43c1074a0002c2030340200180000d1034000001d19001501900616112100c0480201c10303c0c0494040894181501c042c41b5083d00c1d54100300564841000c8a01d82c030326501d0341040310250350703080210007800310308001041d40ca96601240c82c122085440b42d11a40c000020300000d541d210b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698772257 1250 698771007 698771033
    0x11704110f040506011d06130f03110907021203060406050303070b0703150609050603040606050a0303030c170f0f150d0b01030218060d03030b21061902030910050411041503 76
    0x211410401c915044001038000301341840c0703646e0402464800602c5a440d4035013140e07100040052030007041652819860113204090101b101c1001a405084055003000300030507009503100c0e0040c1c010070f45000f5449825800003084203a01a8546a0020ba04d480034001000d10501444842c2c4041c58005005025161240064840c95452220070070101e54004061015030300d080300c9843e9070740c41c0d50a00402600303550708001d5010b450580000101034040d44145100e0b1200c1d11541c2030942c60706000c1624100845004540310584000a0900d205d8240d480d035200d581141c030022880940c0f4081007412220980840d1005158801031065250400030522034056200e160b102910300b1801140b0b072030030b110000500b07068440c86c2002e1180d4800072442c0e00710401089400d8441c000da007a2a60324002641c210101c0324011002e00489417060080b60700c1030310742000501d0b01403c0845030500500004105458038517a4098070300704e682c0caa0090090042d14000203200050840c10641f90b15001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698773507 1250 698772257 698772259
    0xf1620040e12070209190c1206080d080112060603061e060e0402061b010605061c0b01020c0109060f020a06060b0307081501080402041a040e0708160b04050f011704110f 74
    0x104503440180040c02804540e0f885a050300e82d24103988510a6180d5903043d600c1c51100003074140b01445400e5540007044208041c40030100303208143c0d443c2c0c803003030315100b00c01030100004011900601043e0300741500603440c02d1081c4400640729940340c60b031204848500909548507900c000044422480314060300018108481201d0002c2c145070340050050301c942c1d0440c030303149040100c4003503d0010a600410017010040e00300d540e104580b5082d011001800221201e40b6450304124001d41d510004021345503c0041c1c44861840b03081c0917059994081e400407813403c40c03040025280000300580200801005010b940071b4030303402d0840700940150b100501040b181c520840003400141e0f486016242c101d501941d001608540c1e12175031030420701004c55600d4000f410314412441620f00094654111040e00c010b41784075002000c0c0290090f249072051f000d402c0303420701c03007032016151603c20000b6107981410200c10000e4004008290110115016183c59500042e503648504052440c842e040304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698774757 1250 698773507 698773513
    0x140c040c03150611030715020a12050411240c0304060e1c110d0501090507030c1703120c0c070b03060406090902090a050a0209033f0f1620040e 63
    0x8011400041070980381c0f00704010044404040080240c0c24001c49040740d401203444800c0590080c013a00c0a0750000e145080090042040020402001d02c40c903401198030412000300344107610f0070059066120030492118142d0301c0d64010b1104440d0005081202e490710143d619949000750160040b608003891038022080100200000b44110710441e0040f580400c0e441c94030500c01b07002c00c5407070000210041c41340d86064102c0041c4200060030a040b40d1182c821204041e886000b9030b00c1c00606601c100d440c0e680140b201d1141c5105074184544d001000c044240d00381104070124504e00200c9602082d60003034000280409401c16000e108090840d41c0d40a00010280f50b0100e490885e00810b1502c140e5500c1000c03400d031078980d40448610990040031221076502002c00480f10300d414141045800042d409081c00c02d1302050303030040e14030f20075190541c10100f10444840036030b4000704800148085002d0920001008020341c032110081c0e0703003500c64a00d204c500500c01212810760440c0d580da8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698776007 1250 698774757 698774771
    0x712090b0405070b0c1f0f09110307050a051e0d02030a0f0302061b0409050603070e1905010e220c0504150e0702150601030b010c0507060206040201080c121302030a140c040c03 77
    0x40c00603ea842c1030407900c81b13a42c000749141d00004020510f590201132075908200008003031180f00c0c160b40b004601d044090710041540c400400c410400e0302e12a40390400f000b0b0341c00c0108a07008880032651680090010b001840403640000d05090a1000440d040ca00d1100e51509250b8100881603000920ba10540700008800e01e204244c7d000c1c0707110300c81c94203444400050f600d490502c0001e0051080710304100c107506084032030055240d548034024207500d00e0a400090048405040940541d40c030510345400403150f000d0940c64520140e905980010680900081c252030740c4c0310780c00c0c0d0a601034401460550501040c0580884007800e0003046520507000074020b891032143c070303541081c002d0900190300c040941c016a1000c4250074040c0aa008200000030b0803030700070900300d1040d0b1003640d805007959140c2000c50302600640b41c4084c6694010000541d4121280105404071030005048552403034096480307032000c1c446079209103560b0b00315103d441c03da405c0c80e0041c01c0039001c003824103026078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698777257 1250 698776007 698776027
    0x714061b1603030e01060b0915161101092103030b0108040506010b1b070e0a0b12060f28060311040e0c06130e131a1e0712090b0405070b 60
    0x190140c0c166488800c1c076880041000c0501983c4079038050801e150090045940e01d104890302c0341c004e140f5041c021000e80c1620954004200c1c11201c1001c030110103081d018078961980d41d20030250499043c140026000c0101d080003030741c1c80d4081c08261840ca804080d00c41c601c1c00405550320810094148030303040d401d100004a02180c1281504e4142c0c00325034a0701d000149207030143e100d26981c80d000b4041c80c04082045080010f4007441000303542d805000d540c46078002e0180e12030180d4803000c203d810141c045018a07044054103900f121807102001c09004007800d007020803440b80000c00405a684107020001c000c00d070b20b011682c01200f1201086040f45041c00140c0780d000c0c800701c8070721a04000030100d003040c0303c06695001810100c1d952507460b141240d2180c00d25581c0b0001036841074000c0030481c0504446a56103131049007150001960f40d40c481c001d07034810500c0900190b0500200680d1300c9030020305442100a00b9000e458400c18505090802d1070400d07000342c100e20010141003001c2046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698778507 1250 698777257 698777311
    0xc0b031e0403090f06080f060904030518030a061a090601140a0c021f0504060e1009050402212d041115040f0f0504180b0712020d02071406 61
    0x16221105100c68620740c0c03107180480380e00742d031a04071340da500400660204807154040c030403512401081c55000364549800003041914032084400400041d810415038100380352803458000c902c60080e041f01d01c100b810b45e45260581c3c0818032070061020304142d000b5107510700065025000082800c0050b14402d0050040c8142d11481d49200244103058400c0005c6440d2a40d03007100c0d98114a040c80300c1c0c0c4886000043c40341e80b0900c25440060485003095081c3c0c60800d10503e841c00503602c4104400345041e00340400f039000f000c4003d000c0501000b49a003010380d050b0030107126803100c0c3c560144040c80040030382c0e80c0d25203000d920101007080390204000074407655508801c000c0b003110840342c0d000866400324881d10464202c40814980a0070001c0c828103107200f400700b0f44604503402d000e01c1120340064400080004005003401d2901c0005c00c1e003e43c010310800c54805c0f16040003502d4612080340c82d0301030764465007040350051100c900c1c10403150410300075250044261850601803200d546071101c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698779757 1250 698778507 698778541
    0x6010806041104032001022514120f0f1002045a0803031504020a0509030307111c050c090705120906070201110a080c0f13120c0b03 58
    0x300071a07550308458000200e00d400d0f80c00450388120388060001c030080100c80c0560301c684005000d48202e00490508030078110400d0700e910540411104042d1500c002501e08246890381c0e1500000080d00c60072425005003d040442d8400900802c481d02c60303405180d01d0045120b64a90581e0f205207c10700401c000c0308407030240c1d000924100c80400158000b03111104403800600c0801d410000c42980301031505406090045e0240c10094008980c4c3d01044c640ba0302c0126455202c0f10742107420740700e09180950103003a181c04030346002800c0c84271050110b131840d40b08540c191070030014003020000d10b2800022607162036156418510040c5c41c10b1790341d140e44501e02d401c420f01c1084d504000884541c400c00569016400c0c05210102a04007081003548900c4161403501c0154200407071b50742042d20310021a03040581da503644041c40c2c1d941d2909408a40c1002c1140603643c03070200070704514104100e001c1800391180d030032000784070030080c6045100a40e13150f1007054410014800c03c02d8000105803544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698781007 1250 698779757 698779759
    0xf0903080304061410120210021906050109050f150111160b1b070302010203040306050a11030a020d0b04061505070f05010c05041806030206030703230c1b0708121b1e0c0906010806 79
    0x9510a40702c0030185d040032210100e2140d1420030040c01d034180a0590010341c100c1c0e4ec100b90400032900c03035003c5401010412554407000f400c2c51280783c40b595125003a04150b075280e20050f2440250f003420702d064048407a5204040c2c3c0b03100410010b104030902c558604074061844014100302d49590700103512400f07148005801c950b500c0b000294000c145400c00049100081b42c0c0503030b0381c07410408240c000d4103d00f14842466103052004030031400c0c644203000c141d80700c0e45915038000302801022613156101b20401c50f8180410301c10407001803001d01500565a080c0c1d01c5503034a581c24114514038a00600d050b801100381021b2082004d41c51300b1044079048441440e0100d000c490101d048402440545440160b5044820800007100c6503403020b00000c2c00d50403a103000101c8020700c016a2803049000f4a046a04a0107040c910f01207564010300c0040c3c0222842580c900c08680c2203801c000b407528401c008401c4103400800c20a500384140318088404840106580c100407000902080c0010107035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698782257 1250 698781007 698781019
    0x506090d150207060906090521160203010e16030b0901090809060711131e0204080c19091107140d020c0420070c05120a050309010f09030803040614101202 68
    0x65030000c59681c040300c4959030048000d0104170f445141800040c040f00c031040d81e441c0102c070615010501c06c1e40c60400c00d840050f4109040c4500102440d0101c91041003ca03855982c418040d0ba01210074800c01c540b04251003580c03412180755040ca5060300708002c207480501c1c1d2400d40c00780f0018402505980611109070b504644402041c5080c06000e035280041d80d81c40148420b011201941d0f640015160f070450810f03006681003140301c2007040e8016402206000c0d0000c082110359802e0410308400c100040d81c0503224499582e8256400b03d8a24501c10036040c1000911030b4103100004488030a1100844000d00d44180020300007511040408881c504c0b40761a8002c002b80803071003618020141c1c103103900c2c00d6550601391038801b402c500a8420a4065403240c1079007025003c000c2155288250040c010b18a004c802e00011170342802c000302d00c0300500004010120100e401c04c0d001e1442a882200f00041c198000c04041e00d07001001084400d05441040050044001c4409000c440744d0307040d200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698783507 1250 698782257 698782283
    0x703020d1b05010222080a02031c030212070504140108061c0309090c03020c1b1507021c050c09011e090e01020d180c08060402061902010e010507030903090506090d 72
    0x6025140400707400740c42c0b580045452a401d40a02c01084000d182d0248840300c0b80b80e03100401615801e2108000e58980c010503d0701c5103145034100c194000c00d84501e030062800030341000201284000740c03019070000d100802d003070008210064101c2d44036202401d000c0c0241c07601a00007512252070909081848035618049801c242c00b5220340310191284541c10310140c000200014006d4010070b403450ad00f4801c0802e08540c40c0790105000500020103000b040301c0004044203892039034400d1804030b81141e00c3e40d04150b034080c0d08003501503413a48a9406001c20345111002c111030300320b06802100400c0c94845008404034460070042046903552800810590041d9004034028050280b03220301c141d00709001c10088e003029a403155201c9100e064034440e0561100f0015a9407a01190b00a40044003000965801800e2040a141a145074400400d014400c00070450948009640340b00110341c6904450b400c042c0c0120003240600703002d5850324100f02096000425004030f007103011f0465515001c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698784757 1250 698783507 698783537
    0x4170c04140a09390b040e0106080403090b0301181401060e1c061d1e0c040207150c110d03051e10080d0807030b0904050a1e0b04081e0703020d 63
    0xa551300d06484031510042d41c416508601c003101c5031001010300c4543e8060004100c001d40e241c190307001d440c0c4645121203ea03003001003d4403046009030017039062200d1034500046080205c80214060005502e03820603003000f50341f40006031400d11407003461075402c0d00014404141c0c0114441105201150008074046009a50079040e000d06500a0451810007041c0e42900b407899a40b5082c15419104540d040242c404c04032942c01c6400c084940f05401c4110806124500b030f07000b030140c8034000d010703004c080040b00e15100216000406403d0104045003013865865609214200c40c045007420107110071b1601d00c40f56800400b08454034542c0f5240a1301141d0861500b94401c0041c2c800b0301c080b1440003142d40340c06010240120b40103000a82002049000d5007031149420340100d61000040c0842d1540e9030f0340c95803140a00f002c01d510034001c1d80c03042c00424420029540a60300a15106903902854000d0410822942408006144040089030002503002907074a5407030045203004044090001c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698786007 1250 698784757 698784773
    0xc06050c0909010e06010e06070b01030b040311030c010b03010b040209060d0e0a0812040606050d051903021006030804090b0406031e0c05091f060e130b040e0304170c04140a09 77
    0x95009900b24140c140007082c002c0c60300c10b1840c05110240c1302e07403405007410070802005210700d5100800011031000104009107400b620260030a1003400c1c171003450a108500107240d5084400507d5071691580100501e17820284a2641c0c41d2200f620158540720500d400305d60349100e01d002a6191642d81d404101c140c1c80144100b0803500c0d4041c0b545940d41c2c4914008640080c01510140e230b000e40b4050f0009128a0700b5000d02c05c0b4643c0c4000981700c406103592400b10100316198041e000e40c020100d0401440c94203201b894051842384001e591558208034185084800310079a05025520f000e4061000c5a12900b205042014002000c90420f0171440e00d80c0340c2c610644c0c455a0413414030402d016660013044002e07800251241440c000d01c1f6a98482201d12001e2001c5007500444149c100700c4450000d500300b584400030181c00400c45610659000c2c2c91a4455444901804884100c4a008400c24091070701142c000b01c90920003c460f02c2e4000344150405881c20110030764500300103040100746 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698787257 1250 698786007 698786017
    0x906140609030c03030408160503030a0c060c1e05070c0e012105070519031103070b030c07060b0927120f03090a0c0e011703070b0609060a09021c0e0c010c06050c 71
    0x134050b2500c680d13454560544e10f88050152106418800d1800703d014140001543e030140950b940307803001c414407900c400c00281801902d1104000c604c80140d07a854410403403400d540d407596695959207010504200600820315040904070000444c0100103110b45240d900805d0811003c1c20010415140780032480c0404030307803045400c078201e100041d000d800343c0901402180c2c0503c00c501c800340482c03c101034440700c4500807002c11100510100300c19920b00800b030841e5500c151000180103140100082c0042000c85500c11602ca22040c80070914080748a02c4100e5140c0e00020080c3e03800300098103100e800f6a038440181d5035030200c0040c034044410010a05003582160701c043d4031700c1c0c40d007040c10b4110000b40216682c60b03241d95079500c1c0070175001003121903603500119403075941e4880700200800c04402810640d4401e14012010035407207010b10003001c060310350380808070b6031102021201003560590010039200b5044a880b030701140e6000380540030442c0d40700c5030014599540121040580c000c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698788507 1250 698787257 698787259
    0x17040209070903050105070203030735152214070801151e0906020d0903020114090420031e0112170c070e0108210d2a020a0201090906140609030c 64
    0xc24040c8071140390040003e5005842030303683c405126000003013320796001850560b182400c00e000d80300940700c000c813484a0b004460f4050b071f00304000d0780e0800036040c4507a80d8a00c2c3e072041031808107924110828480c80c25024010728488031645880800501020703014852403440031001000b010045200f103e204119104105011241140c001402003045c040c0d405010701503c140204440e6950140d4411411070354140d50718403900c050107075051601c1d000301002c290020380365821030515131001001240100480e4240a4aa04e0400e0b410003110701030421724a1100c1c9900018490004651004078900c3d800070010900e00d10b500002d001140701b1034035208030038042c00c0b00c0030a0400c081c4864604031450003040f40c8480307506d0403044031200101403800c0c0c03402e1401c12841c4e200c00803a800c403005940c0e5100c01405a800c00f1440c05001c800b01d11100401030b0440e802d40000c660300516114041c20310002c00f000424144803e8040000b2048a1148208404070311220155002c0154030102c0794 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698789757 1250 698788507 698788511
    0x50a0c031203050f010b07060b03070807120b070c110d110603010b0c0114070504151404030f0b0f04050c0f060903011a010f030b01050d0b18160f170402090709030501 73
    0x552420041c51001e11414120006402d0501103038042c502d07180c100c0d0590301c0b424480c501d803900c44d44d104001000c100c1c1c2a82c0d0580604000080d0102040c1f001500070122510080682d03a0503260801e19000010501c0c0203000544000201041ca0880c5030740c0c0140d002e9440c0c3c01e00a41909040050403451002c880d8400d400100104e003a41044001e88140c14140d802031106c8800c1d591a1010310508039609800901c0600c0308000084920907041d00d1801d003420703c49800074103900700c0d504681c000c0c1c00a44140d400d0420b0b52040218002d80306034442a58154800c0ca41040d9030768980340d5010721103403440b5031040309981245641d03060440e0f240f010000c0003002030403140d980c2105010780240f0f01c2c9020400300e00f6100d078143c0c028042d50100035416941c442c41c04800c0ea0108009080c10a20142c100c44c103101c40d03800d0700e2801c1c003c0c940103810450b1201001d0b100004004c00102c0c13015620b0003080354100d0207040300c0040c550120740040d81251140c203071395a0a5021105030300507601c0503040758 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698791007 1250 698789757 698789759
    0x110120070b0c1e0c151606140c0721120f0e010501152109140705030d03180b040609020a03060e0610082d240105040c050f0304050a0c 59
    0x994034900900307031016002c0a07204801079806802c90b90668860000400da000300760f048086141c0f082c0f250702c1c0090b03900c04550502c841c000100c55440c582d0842141d001b41d49030044005a8840e0755100c0d408410300c5516441c0c4842a41e86180c0d4045426400d41000d148051040c00d0600030315500d0440341d0002c204000c03030402d00e04260040c2214a0701c40750b09520701000429007205c101030240ea151550348903050f144000c003211240b03016031241c0d035013109607440c4004c10004540c2c191480b00b801e60072000b06a1941400109410101d104941505140c60722481490030005070135558409904503e0002c4907039110f040503001f03460a003000075031082141d5070210403c02154001000b0307048640445403140c0c1c803d81020340015542c014541250301a818100241c40d5a964104c40380d00144000603074003940c8101c0a00e85040e4405005600c1d1401c1c41c0035a903c9494842c440c01400121800d1100c0080f519014045100e48c08210313003020300000028062210070881590b54039030104d4040011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698792257 1250 698791007 698791019
    0x7150b10050d1a010f0e011b03081006020705010e12071a04080d0f0c02091005030601090c030e01020405090103081602061209060603070f0b3117060411012007 70
    0x2951104581d1020103142c0074118003560490030752202c90800c1a1240044c4401000090f41c0d011a0400746d01e04002200c2d68050207510b00e1103000f030090b8440d4642d10311508048d440a142000c041e0000811581300c004104800d070b0f0f122040328070b111070590f0600c51844000d04d14906120854201c4e1100d402440000401d802c0800300138812281d041c810384964500c01003049940480c020354500c0041c92240b20300025261004000340c01c82440103181ea02c548e41c0d4001b003401c0c070509130b00101d0701641e13448040019a81500440000f4030041000314941414180003421020041c00043c14252020036882e4200076269861809a07800070040c90b00c4020003080c4a04c200011949101741f401a40081843c50500144150a88110b030203020001410040f0411143e00300d075070484005080d035046c0d600b89501ca8006109050700c00e000c01c1012a0514014401c030b03803000e0800d1065540b0000420003c90f620340c00785000740c042460010641522003103010a1003076084510102401000400504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698793507 1250 698792257 698792267
    0x705070b0432010e10170a1b0801030c061821170c100b0d0605150f030303010b040504051b19080c0a02030f0c2503051c0507150b10 58
    0x1090940d5145641c00c2c212440e2407203400c10301c85928902241820030381115030302d4410315403041982c0c2840d180d00c11084901c002815203505407010590940d40b00d0080b80e0f81c1510219040c800c281c241803400c401e51456440302003c503e9803082e0010030031400d032000c070810120380c0f04e20000c000581094402400095403403281104500f41240c540188020040072100003000b943d0942c520b400140c95200c0ca0044504090864240b1a43d0b0003801e40381c284000521030b1142900031400194490441000582484041045c0040c440d10036881800108125082c80b4115402d0b201d00740c40214240d103400c40000304440c20901324156100d0007003041d04803401c1049800303c3d83c1c10680d6a8521030784030300300c0c07242641c03040c0c60841c40181c04c1001030790741d60002d11008004405c1d50404842401841c0034682c4022600314140c0d01e4500e40c84041002441820003a164044081034120703141c2e0640c90001403d50311803d00001e14100392440c0342e0081030010380c8095804d44010741402c182190b0100d0042c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698794757 1250 698793507 698793539
    0x30601090608190305120a06050409050c040b010302030613090201090b030f0610030b010c021504050a080a14060105011b03030e030d0b13090f1403160f050607030e030a03020705070b04 81
    0x2c1c41c4100c000000c84000c40200000f1001d4058480c64075001140401c3c09060400400c4404240c0d21b81c08001801d0310b86100f80003c0b103000e00080c121080d661000c01058070342d04540541098018021301c07010791b99114210000c0650381c00700154002240c4010791340b08845074050400200044200411300780090440d41c07242d941141c0543c0348010f4102c06074100c581c0c1c0358bc4c49000078003011040005003090404082c0c0c440301c0b4503000742042c1d600c0340000c0300e02c2d9a54104880940004030008208424101690a50000400600810b44c1400c0c0002e00100d501c1e000704110200d480d102c00d05040c065441103020381c49010980744e64207410b54010340a024460210b0380605000d41e14010341403c184140e1642c1c6a000240300e6035074055440302440040c0d1280030310300310301007000280054150040d0f00c078200f034405e890114042949081003030810384028199000e040c202802c6118004001c02124201e02007414010307110281418540d10700070b460723001590741d510005000f050ba9004048010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698796007 1250 698794757 698794769
    0x151d041515090b090c251b060f0302070203100f0f090b060117090714011202070528050a02060c01020d05010f080607172403031c0606050c0a060c0306050306010906 72
    0x40824035140b404d001900301d0407100041050010302c40800c1d04481209960301c0c3c0c1420b039103981d203406003607240d031410030300030b07500510542e11510401c1010a4004044800140c80c80c00d08500b06801a00426140d060200c401d1000340c0e03030741c480110100d2503076124051440c50b00c007040101c00410b14000ba0b0701c000076a041400300700040821640d000310740003250300c0741c0003a40240c0780b01f5150031440d940501441003c0b50500502d00c0401c101c58800d48050101c85024000803d8102002e2130440d030341c40d14026441c00e080c41e804c00c01d0400301c0d00c00181044d002d036040e00e0031550b4994004229009010300801c103002c040c00e00000203200031302248a03c3c01c2c1ca038408160303481c58680350403d03200b5018409403400410500c40004000c804005608402ca4210101920b202094180023a05613484166141c1588001284003003109110340f0a460181005060441c900a600301c602aa038050510000f0910358031445418805440b0b40c020100a1070044c2c12102956114003485d00500b40e507003d44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698797257 1250 698796007 698796011
    0x7122402220506160f020f10170a090f0201120b0a0e0f130507030b07052802070b090f040b190305030703020f010b060a08042112151d04151509 63
    0x102d02d9140840440714902e28031003071142c07840c083d40d031815a01005040c081c1d9110303440c90030b500c03030f035490708214110070a90550340c000d010304070540c1f10b5001d900040c083c00310707040c9031002e00030000c1d0160b18400005602428854110001d0000741ca000d4960051800d40040340340000003401e03802c0d251558000c0320880090444d41c0e4910f460080d0b105c500b6100030b0160740c892542007020400d00c16805400040c21303c1c2081c0350100003d1940042c03040c0307111203040e80c1e0320741100031340d1a42c1c10311018000e440a49074480ca0b08901e040003450142c41c55551511940c0d44403200345c030340d980740e11503003070903030f0115118007401c0b5902d040090300c3e0382049c40280c0c0980111698600130070b006106170f501983c0020070b05400c214140c86c04032440c80c8024003c4907030065001d2600119640360744909085559641d0b400a0780c0150030360903042e0380e0000c07841d2101007401d1006200e00d482c4400344160030958200e11585a1750b80f030420709003080c2d044150742c980030729103032290b0a00004002c2c0030741503032140501 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698798507 1250 698797257 698797259
    0xd02031e0c16170c04090c050d0813060804030e0301200d020904091b0e091504050316050d03060b0306030303040204020c1f15080a0b0411040915020711030712240222 73
    0xa00c41903543c5030318020301034090303203205208c2c83c60b182d80500c4c400e60107024203a05018504407041c50040780ca41161010403044400c2104251380b2030509522100180c0092005201c402d15013a1001c5100c0e1251451800c0400d1301180c603556941650765a42d0014020300816009003844981d000c1c91122410905004001c0402c031040c100c40c035103016030b0380140102040b200c4610b003224000f00103001255540000c0011400121425078643d038081d0241001d400e43d055841c4000e0101d4290360b00c140410f120034010498079543c048203903903003d43c050302c1c0540e4444104085a040c00c03600b040c003003d078050004140c0c0080003150b2020b645c0e09264194030a0750f030349610015a6405c40d00e107000788581d40307030400900000d40901c009540700002600126002d80e041d40c0741310f41d401c45d0140045005601003034407020301c40051030130f04211a0071b03005000218204044220000e411942c00b41a4181d10320010381c50703094654004d410060f600e0421522400d0790120b40c0741419008149618102190380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698799757 1250 698798507 698798509
    0x150b011d011209080d0b060705060c03191d0d020a02031207052103040201022415060d020c030909160504030803040c0506041409010e0c180d061b020d02031e0c16170c 73
    0x808c442000b90840024041c9541c2e1008400050703000038461768599864003229030030141240100080043d008130b00c80c040d568401d0b9a6460400a802d103d070456001301103040141c0c0f00841c40c0c1c070918071003a001b140d82302900e0500a00d010340302845c601d4092150643c2031319003400c05001c0c1d4000e9100341d085d00d13220907c1c2c4164900308004014003036019070003000491a040005041b40c8240740000c1c050600706109018140c040307070003448a40030b050300005840d880b585001d040803075005038a42803d0101000240c4010880d001b80d010003414400b0010105003441200c0711070b00001c08000341342c135985d1030b00e512050040300c0e080c1d40c00c18022203900300040360500261098a01ca45101004d60303080c4030342c462045154070181d540841d04406c1506a00c400314030075005410001c0c0700101810aa801c14800c028641100401204210f42080c48181a002c01207440b034030180f080d0403903039900d9802840c01e030342c140303481d100058105501d046d200190340c003030350746c0f82d2071040c0c0c00d01c1e0994403507001c1c5c0b0f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698801007 1250 698799757 698799769
    0xf05100501150806040902030601231f0f030204080613051c0e0d0206120a0e0f0105090a0201030b040e0a0c060216030f080a1209050307150b011d011209080d0b 70
    0x2008072185407802404402c8098802d4500a034481030080001c1041851303500802d06194081c0c000041d2800e42c105d503010041104405a50085815200040400030245200b124940f140080e0800c000c40c6020819089200384c0564026008020646180d410000e6412028107403454003115075019000c603805101e80b001c5d810b005012003030340710b22124075841401c10031206620841241e000c4010b2203412006802c0e8040188a00035004000130314011000304145440707074a06115107568100001c2011241d000b161004800b0760a080225400a060000030050020f600426a00e0300c00d5810180c140124450100c048406a0702629110304107581c041d00401c2440c000076103039881d00308400001070403640040100088510f4080781072100021254140e45000c081907aa603800032407014180716003e200c8000d0714205441c100701400020001909045664801d00b0020151018828081c2d024100928540003460002c000e00304051624520035000040712203100c601d000c0c500483c0781480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698802257 1250 698801007 698801009
    0x11060124050c15060d0b16090f060507060b120627010b0120150c210f0a0b04060816170a080304080f0f19030f0203010f030b0a0b06070f05100501 64
    0x784014180300d03c01d4400043c01400d0181c031041e041032800c4d81d0407020400c01820240a00c200c14025050f4000e14800100740b040c591300047d8158880c1c0008208543e042421101420f502807000b20b9111401c40020740788030a110596116409110100080341001c101c50045c1400020824101c050600900500301d40c0e04010507030216480380c00e0300703840c0400070f801ca100c4100072004072106002c0c00300610a52100c1a90308044122020900c101d6070100c1c0c40010203100840d610702c150074900341d4010441044042d000340000c1d942c0d0941c51125807110381001c0c000d4000b080c21105230705803130101d000116126105541400a046118020340f070070201e90705480c1908001014259201c0c0c0d02c6030007240c1c2c0000c1405100020400c104620408000702070304001615080c1c100310b6101103e03002c0c042d6152017800024062040005201c01340740d01e128542a40c1d0841840103180d9a003031001001811020341103684444082900001c10074004400e0081c642700b4025078000c4015802c0c01001d448003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698803507 1250 698802257 698802277
    0x809070f0e0c04030204062c07050403020607020f030106120512070b04200a09020c1015090b031203040c0609060f021b0619020303060f06090a0303080402011106012405 74
    0x100c00040107500e40340161503401035007500100e45042da4030340c002801c03107050703500900000204001244a03010068440450051340c2030841c01d942c907029000802e68400d600009208090101e201029902e400c1410a09220050002c0240c03985408050000000122040362540710301090710400c0241002510243d82d4024060250354846a170780079010b4030700400c90454078110800b5880c0542d10100c03a00018030303003044016900d00302500c80c5403d101c442c400d402103013414519515404003034000e49000300c7e03400000000b0f0100e10030000a060001c0d0030ba94821a01c3c011040c8010b1124100c90300d0112401034499042017680c07402d0039106145480c0c00d400141e040b07240150749440071507505898003007001704280d144c01c00c1c201861100740b0201d40401d0040e840030040110b2030829025402008108984180c105800340340050004003060000404000345013000c101164055034004140850560a8505c250f84428909600c90441c0060507010444603034070b56030031805078046a6807029 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698804757 1250 698803507 698803529
    0xa17390111030a110a0b0a021206091006080c040b03091b030607091202010c21020c0609031c09030f030c030e01050f093c030d0206090d080405160303030b01080907 72
    0x46005131861290815013100e0343c00390303004940c00903096604540c401d50307803c0310058850b03290015040402d2001030003e40140740c083e0034007116000c032615a10032a815454156070b159648005850b286c0101d5212110414010040c450602000b10342c0c001203e060030114440160040101079075607800741c4000c000700f0340030030041c07003030301c0440c441c14483c030b801810001d074501740c01c0e5540312104544840c030030700c510303c20201c1d15000d603810f000c070030700441080341c00078100440c130300c0080c1d21090003d40e014102d26004200b002250b014903100c0d802540c00c00b102101000342410007902c00c3d10070500440020380340391020020f941c010001c0c0c1d20040c2c00340c0011403d1100c00c034140240b5103541172450002821b0304140f94090317501e0f425105c40250060301102144851202494502890202e10100b0b40d08080104001e03d1000a1180c058120074940b041c002e858174140241413540305402200c0012201c100841410342507040685d0b0401300781d0761074140da510b04840b9500d90f0031030f00494030504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698806007 1250 698804757 698804767
    0x5010912051501031104050c0901050906030411030d020a06060905010308160f021507061a181f0f24050a05090a0801020309070512010603020a1739011103 68
    0x22915031900446034400c10031107400b069548203684820800364800c450008000600054a00f094080c16807c0002103100600b030034807440000e001c038001d0803641ca0103004040005400d000400b030504445400140c25a0200c505243c0000e403035560002c0d0660b015410004009000391ba98030802c2c1c12030341c0000c0428203148030b50b4030100d110494038900380c3d4683c503400d40c520050780d11075010b501c41800b804109943d0349194500b6074207941c002800c03058440e101f82445041c603240d0000000713070640c0000892215555006004c00c10b10034040d009004824602008582c28000104001c2030356800400340d02072210032140ae0101c003160020078000900c00340070220b601802503000c2d00c0d0061004214844054440c90194220381044401d05081d51100e4800c006030b082c050800c6034009900b070300a01010b070a40d00496000d038464454801d0142003401e8a9a1000302840010411484000410006041080800c580018012042e94516407940114206600070003442c560b2010001c0518103007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698807257 1250 698806007 698806019
    0xc0207080f0607031d0714180408090603252a170c03210708070c1115091315120c0e07021603080301060e0f1e0321041e050109 56
    0x80c104001104000300540617440102510038042403000c2c20f425910041000030390000c01040520416620b000b219180b070a100105104d0800c40b41c03d0807080d11100d5a0b40c6407040d006804107011000611142c050721640c00c405940003410880c86c81e14000c5001d606502c03481c03150141112a080204401c4640a02c030b0341450807100907001ca44c01e00001e41e81000d4441301c25080c0c111400d0701c1e10500035110020000701e01d0304881c2607a040b0050317240a503c00841d540d10343c421007680c0b00d141c0d4030504201103007080510340d0104650f851040070b04149040104100c060010f070510000480c2101c0c245403002c02c1e4405502d00d08500c0c00d0b0050a99003103e0700d02078007074141500c00f8080d40c0845c0213012460458050311240500194491610680e41b907241c018020800c030307103000301d40744104240c6640880590380c007002d4860060f0740c400700515201c00800001d241006e054030394264480011180d0741d895060718040d0040307400e480085416031307105200f000c1c0354840c01d000351030108103002014404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698808507 1250 698807257 698807261
    0x1505030105010f0e03010e120c010e010605210c06160b15031527070e01060302040e010e0a0603021e042301061103040306021b010b01020a2003030d020d0c0207080f060703 75
    0x7100c84045e0000503850410b06641e0f0500011141c2513600910003e030311000c0b807000b40f20718a0514003010080103551b08140018403400300c007a460303003001c09494412418041c010302481086a1006121383da54128602c00c00c81100b0001c50151005035003180003840c075881c0340c0000c4100764002009045401110000c0094138034000e03080b124120003003522408403a90446031380001030400000dd0030180c5c9400a1000c082e14160050410940184130400c800041c400c00303603040d0341d2540c0c0500c00c1660b680324194001d26180e80b02940c880300b40300000041060b4507008448000b003c0d05d00303000d041c51a0a402c0e81030800550b00748107000841340104815480703101d1000310490140241ca10b0031341d881d11543c0c1030360000311555100408440c60344030300c1070302403142c440420001e0014161001c401e840d401c0385800401d02004005440a82e8a09556028401c82c1c40764514110115248c0b000300184500900c0c0c103e01c084054428003a02041030b9500041401c03803c026000103012541c0c81850480c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698809757 1250 698808507 698808527
    0x90607030c0b0702011401060e06030f0703020702030d0e0a0e0c0304020f22050f06032b050403052a0307031101140c0105130201031a060706090203030408030f041505030105010f 78
    0x20422041c6200a4005500c1c840000d000d8040342d0b00100d40b008402401c0c510340311040c0d0040702881780314041c210003503d0b80c5044d00d50020740504954643e80c3c1707040d0306801a21030900000e515000d410603202200d078000d001c480313a0010558040300000d4407480785d00d0a094040e500040ba1a01c01d00010f4014a01030503840840003015104202003061604070304039500e1440c07411510142c075002000040342c1c0610b80e00d030340814100c00900400500010100c5d521000d80e02280c411407040001890071401002101c0086038400d0454032245132007110007000d2036000c240100d105007580c24940d89440d0004500d000c0e40d8020382d0195030301685100540c1c6900312101c2c1d280f0716900c01e000d42c0300390b8602803240500c04d00c000c075196180c0010500c00141250301e404807a408101128a04c80c105846003401d80b0002c5903c0308002600d0f204500009245008681c1714911500c00011280d0398482c3e07420151003203c050f110b0340c908014001c10140c949003c24011640000c0440048841107031040b14588 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698811007 1250 698809757 698809763
    0x200a0204110f0c10110702090a0c05090d06060806100609180b0a080c0f2b020604090e03041e060e06130b0c0d09091814030d05040c05010e04060b090607 67
    0x1d4500300d03100c10b42c00b066420540540c0d90310340100c403816220300101d01541800c440b107882e90318600500da40c0080e408030401303808210048d0340c8400c4112034074020000c071000f4060091442a001c4510f01c0c000002c0c1c081c50142c00c0c0e0502503100804c658800c4810442c06a0300241c880c84540ca081c400024840754044071541e1400b40c807048209030030f8171403440340400313000c41c000540900343d00e810510014009010225016521030004401d10034080c001d40c54420314030814003a01c0c2c61141c000100c0502440e000414050b140225090180100100a0040740e1451581000300b00613401d82d81900d8031184030315408a00e20304c0c00e0b030ba441e00d4814010301c8290708190280e1142038581c404003006810400820b0241e6100000c9096190342041003440100b8400c001804650a100d140e0400050841001400c88030100c1c803022030f080050050325040070811504200603d4103060500c0a06e01c140314143c041108480c030056541001d001d01420b031070320920040d180806080a10046501403a016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698812257 1250 698811007 698811041
    0x5030c030a0b0d2901050f010c030203121303020d0305070801150302070501090507090e070f030f020a080d0509040608060603120a0e031e0c090403020a020d02042a200a0204 76
    0x20b22a955294500b000079030284904c908000d00041414050070181200e4420380c004140c01003201d555249030b2007446d0303002864811402011460140c0c594096000b104000c00c1034003082004045041c45000d2400e4042d0342140c620040c602015800c4400584070300e400034900c41e006020103000c5004440300300b20585401458050152229421030308000c00441c0e59070030946003008880024003035030b030040e0611070103440b56500e000c40701c82c0038103428403000b8141d181105542c010755070346464440080001c40141c4e04100c900440c01003a43c2d000c0046944140e140c02c80202e80b0a80000e034061040308090010001d810700b42102200d10303003101200030104504000404040d8505001190a20300c1b800c600001ca0303094420030605140c00702944600402c0414100001320307074000307002c94400e60180c07014800c1142c180003141c0508000301c410f0810344000304440e040c1414a48400a00b00c120341d990f0301c00c6003042c0d03020b202c0e440e21000117000d184c0d204551007400351829a01c0569001e16820f00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698813507 1250 698812257 698812271
    0x2191103190c1a010501090906080c09040317091c03020403050a0311120a11010606051e0c0c0a0611010b01080129160c0f060905090a09260406170705030c030a 70
    0xf4030000c5104894041e600c50b10715030010005560030002d4040034194101d4180300d61400e110909650f1903240d0740c1d45100705944030209050500030401003180c107890f4040c5800301c0c074091130001e07903e0103105800314901b8000c41c40740195030b20034426282920340c804041d00c20f82046850445201d400d101034441c41e80503030b40400d44899501e9001341070002c504c0e11482c0344106205100c60031070f40740703a00c48414003070104010700030300b008080c40349002203807131881d02d480d506002180385c030301590401442e4000401c0030380801d00541007004400540c0d006802805100510401103403941428030a44095211441c218503c08000340265015091240005400d000388104403146d4107000c0f0300142c1e2629a00c1c3d405221094603001c1180c042c000c1030610b0120a881e2201240078241c000304070300c400b00e42e5201e4501c10031002070703102d008019040b0280e0318002c038200e850400983c0107119400128404912494407a9076201c0443e206000c1615250700f143e41e04902c512165000808900e2003a9640302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698814757 1250 698813507 698813513
    0x3010e01061508011505120a0b090c0702040e0a0c091d0d17010e010e04030318050d1d030106181d060901020d0b01031a0118031502191103190c 63
    0x11481c0001c1164044031000107603441e10207007500f107060300146640303205900e8012500360004101c0780044005582c0c0714013565a00800001441b2881c61a41c2c044038400a0045d00030500026100c2c00380210741c100910f8000b40411591416100402000c8130b13500c1000b040050b006600c000c002005245042c18024070054078281008054401038010400324001c00d01403100020070f0901410030882c0b16846035052075a0102e884100070300040c101034480503805401006440c08800c0e480e8008100c80400022880280c235a540e200c00e244410060f061091040c3d203014050902141c619800031a94a01a09810000381c10380078907001c2081e001a884108240003080428400c25042c0001629904660710b00307001d4801c40c101144c1018140840c8031928050459262004282400d0440c0c0d001d41b40401e400401c13901c0c2c0d1003c0c0c4840c402000348164201141c004012408c0c51075003d1440c4e03603600c14140c800c81c21004220f22258410300550b006813590420682c82020035040810307455a42c0d039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698816007 1250 698814757 698814761
    0x70f11030309150708090c0d033c031503080d060b030109020705010b010306030302300c0f0c0301020f071103150c181f05031f0f030b0109151403010e01 67
    0x74032000003650040d0501410b06840440701a084485842c0c17040841c00c03c01c0010ba42d4000300541180300701c11849900c410903024400803003501e030410a011041180b54034100101c0c0e40031100581c81010544040c451182c440c0c440c4081c0003c1c00580c12020f075085484187d156000018803c850030381d00d15011030301b07441c07807000345000306604140965070b4040c030310b0180e0039944040800f0341411309081007840040d401042e450918402060030304a80780e01e00c03985e4882102d402030408048000020910111640400c03050380700c44400302260a00c140d071400740f6080384035100700030180e04418071010001801d07030040410800e00c001c0c1190321181c6031211402c000c0005803a4802d0500c8001110b5081540340d40005c400d130142201c103400d03250262032181c50352a1012924404001c000000661008030400c6800e01281c0c001d050400a2500d0f08040c00406110340401d4400e03880a40000460054a0249410715140154029480d070310305800d982c81801911003017030341552948003d41c1606024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698817257 1250 698816007 698816011
    0x4140426161a130311010c050301030809280e0f0105060f0a05070b071e03090b16031508010204082107030c020f040e10060b130e060a0e040c0f0603090b070f110303 72
    0xc3c07140c0c0b04507000616000e0443c00f5402c015060b164102800e0720032050b040402d4904403504050701d80c1e51062042e0004008400400740340e00c1000715449510589254489480145d0310340400901641d04e904245400781042445081ea00480800201c1d0707100342003e01030403181c925401c0c40c3d403c120f074682c1d4040a0540c2213680e007000030ba4020655031203043d4842e4100301141e241c2820840719500f03485882c0318120003080d8100070851610210255846030b4014488100201d1031064840d854030b490300c1c00f0f94424450301035140b00304800c19450081701901e5810a083e552145840e11145a03029148407444080903607100e002c400060b4002c0d00e440c0a11201c10a41c507000c0c04070003140584410072070340d441e0888200794505005100d10704071640310840a861604503031f890f8503554017001030b14840c159008601d80c1e0300b8820520080240b01051002607503032014200c20266110142181101c100a41c007034500d20f914404508120f0041c2e010b03050041503480e104140d40350300940f092440e801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698818507 1250 698817257 698817271
    0x90312060b180a051f022a13020702090708090703020406030b04050624040515060a0c060c020c0f0904082101090b0d0209071206080d09090c050f040902030603030904140426161a 78
    0x1201201b02828a41140c0c1c8c6043d0f000b261004500784841d54011440d070000003400b0206000040e0042244280d08000316001141d005206120f25600e074a000c5001c543d05079011a032a116a4010900700f0308003445090603d191b12107011480400c2800300000707005c003c0c1034070b08074920845c81060142c072180b0003000d481540d81c864103051030b0103241000850314104101e200315000030102220703030340e610380c4004010003040315001c07215200c43c102040603101c0d5049200601c154564852115038001401c036040314640d442c00c0045650303182c2030200d0b075444004000d620020303a00010b01d1b840d0003105840c00441c52400002104d503110364195180544c03030b419105c081000034004004014140c0161040202140340040c05c0404242da040740780d010328080ca20742e0715004400904030381c50070007e44010400040060029688480c0900d035902c1040e11309817031108030000c001d0712021034070000e404844451328149140c41d9000020076162004158110350b400c044680301007561200d9019140100c0c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698819757 1250 698818507 698818573
    0xb070b0c0a0c1a2e0909050f0a0311070602010203012d0e0903040e0114030a0f03021204170d1d040c0507061d0f01110d090312060b180a051f02 63
    0x10300c0c5542c10782a52045030714091104440303803401c4450544c000b10204503881c024020641000c240380050038912017240e201d0040c4514150310003410740c02041d1070070410402082d40e000c1c60300ca5404034240d10090003049041c08410740a003840b011f00481b4841050107101801641c240ca8080d00c1e981c0345d40c2518001d40950002c141403001c140c1d01d02a0070700414007a40d05504200d4200c001c00d8541400d5080981204000c5a0a4040c18024000c44140e80769011420742e64a8640c0d954401c0c0440008140c0c40500c100d16005000030b009224401729064244070b00c41c56100307180108000b0701521a0300f00100701c1c0c280404400a0030a000f404100c03201044400c05203043c41510340d00d03001d000000e14401c1c4c0c0c1003079010401c03030000c14111038881d1000304000c00c2500d660305007601d664040400e8990064600940010304803c1000507006240c881e92000c0143c10040e401c202c0000824055141d001c822144e4810141340000c4140d080320f403150040d50320f45645514810800790382c2c0601101300700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 698821007 1250 698819757 698819761
    0xa06050306041a1305100e10030b0901020a0c170d09080403050c010c200a050607061b03111222290c0319060b070812010b070b0c0a0c1a 60
    0x101c0c01e40038100507540e002d03c200e4052108036001407284801c0001d801141540d0f1404100d09580760b1600c5406403460703c0c20881f460030301c0e46030103032400c0c2c0c284829540ca02101000c15102141802220182d0300340350b4610726562095101c03001e480c1c6240c4445141c44c0b030f082003c1100314047e4001c601d0000d005071080c0c1e4940340f0350306107503081c20075102e281c03070412005401100015071440004030074440414200c501040d841000710700c0300019508582d80c4940c0124582c010060030360040b1100f0074141000c80755000c0c40d05800c0e8190303541c5070591310300300c18248516003140301c00f003d1003640081d114204242c2c10134004001101041401d609440c0f110198003101141d4078000321780c4495421540c1c41d09000d190018071503e190001500e0038040d90084120140940400d42202001e00076001020355581e0307240c50204aa50f0090a142c00e1101450000080744003140b001c5d1900c140d00840340031030990703403080281c4442d40001e5407001405680868800441e580a09940d03009040c0c81041801d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 698822257 1250 698821007 698821009
    0x7051e030f0309030607050d06030b01180e1204052b080a0e01020c0a03031d03070b0901080105030a1a0a140a022205010e1c120302030103020a06050301030507030215090a06050306 79
    0x1c4424034501c04400d5004210fa00704a490000b6910340c800d000389840c646030000d01c11060050903940e80301400c0090644000b1030340d1042000d0414810101d52000c1101c25070400f1000d86034030680b15501c84c0c20006220412540c10a003c403103c582d42c50140380c141d020800350018403504a0011300303a41c41000418442160380d00140c0e940c0d002d9109000410516564600052460360680402070820882c03402e5813120780340381c1b4054240200000c0640360b01d070741c0350361403030116402011181d8001240500002554200452800c401c103802180840c2c4010100365012041d02020b440f044003242e56188207240740111149543c024980c500f8056a0303542081040c50f0107149a42d500240ea034404001040711b40c0e00400949000c8106481c2c3c210441003c800c07565480780c6442c00a85004400912822a41d50580c0258140c034806c0310480300e49600c80d007088030140003d00000b445948681014400752030300104200311400c2c107030206d92601100d400810120304980e400318001c11408130a000c25 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 698823507 1250 698822257 698822263
    0x10f0501140a0f0b030c1617180603010305060711102307032319090b160c050303070e13140a06050402070b1503030903060c1914090f0307051e03 64
    0x2800f904462181c1035050a003030040a1002070564030300d400b0009050348100b03400603250102d0b0368015410030b0f0000004103003d0010f901404000340f42803840c04900419152903019a13060340c0d042001850140c1c1c5045c0f09071a003217101c1440034002d106410304c040840c0840c0c020080740400c007802c0b440074004100c051031502c0c000070380360b8428141814141244800c420300c3c505200c10707001c030108401e500c0d13a084282121101044100c45c481c1092042c0303061240c02c0c0c440728011541480d01180d0310540303040c100c4240048000043c0039800400c08608070921450410f030980d070b8000e080303c0c0c6000c46c540c045011198481c0b001c1c04214144030400050803250321a5200a2505440940c90141a542d41042c0803d004082094080650310103d0f0580c87c20000c0e206581c0d00501114001e0811108448a47d040440900907038400b0040100c0e286105500345d450414100300550b0812078140104080301c4400001c05405110344680064030f82d031020030b0300e103040400803891a01355000000b8103007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 698824757 1250 698823507 698823509
    0x50d0311010b100c1b0f0e040b06090c030123040f0509010606050c0c130609050906150f100e030a06180507050406050f0d061b030b010f110c12010f0501140a 69
    0x84207000f240049074507035030401000540190710001e410814014040a00304085040d00046010399440c1c1c1c0115205095202042c003e5000301094861503a4080030003a150b038084401541a003401e100410004c140c0f040070020b025680040300781e0308802800490b041303600b001c020f01d00c0c03580c4402c188001d4031020700c2040b01a0110385046440d1040340541d96a9861203006114040c18480f030131045943d440340d1042c00606081c01c418043d42c14407108407a41e030384081d20154070101300e220185c5e001d4900b600e40031002e144068004128074031a1281610703010740c0711062030780502591400c0d40000d20548100c0190300202940c03900c1040a03410204e1608030541c00c814052032030031605110300c0ea00c1d071800b103020107001c071600443c07203031689040d00141a4410926100b80f002941600e171454041c1c1112011203020303606c0c4840700c000300350102c6090520061800d61a0400250100282171030f0340319024038040750b000418028940f01149003100c00c01d9206400d030405c501c44640240c075022803200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 698826007 1250 698824757 698824759
    0xf0a0e0a211403391f0e0a260316030f140a0606090506071703060307080105070801092906030705130b130b0c0c061803031606060801091515050d0311010b 68
    0xe15191644d11860740c2c684860034207196500620081005c0711050b0740015400c400e020f42561005119445c00c9482c40584a1492007441d01014985078112030752406da074407400d10008101c0e04204407140640c000d0020740c07490030105464842449140d02c0d58075415001e5a118200011564a006002412407a080d003181c0d108400410040e404560602101c0360300d014290500d550329200c0400007445e00035664000031540d4282004c0010080d08203580c14100c40340c140082c400030001c4210108075290a1096590075240c55160084604104024660003001c40c20210b04d0310344601c3c40401018220b41c4035a414050000d08140b015003039041c4800104000d8904030b0810550502a5454803440700e002401401b0100f065070320940e110340074148070100542545d60f0764882090710141a400c9d82400d890041c240b10001441c01814801e40e001690400047e0040b0002503070300b01c024180f03074014115200f04005011a0301c1e40d80c14110100b29100f40c0300e0880d11000c4486643c00e5800b100901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 698827257 1250 698826007 698826097
    0x1090b090d140f1c140901021906060b0c01051906081c02070902030118110a0221281b0b0a0c11030f0a0e0a211403 51
    0xd1a45620125078140c070b40c03050300c15000745800d12119140c2115079010312001d1255001142442000192240002146585210280500c1051500c0c1d42c401c6040e1140168001001001130110302d9280350b03119885080d0208000d41e035002d20304926044455500d003035035901c40c240040a40700d43ca50300c00c1c1c40003040d8144005032800345190740741c0c2c508420568440e8001c402900c1051303c00d20120380540002141152296140e88140e480760030349020300c03103001e450826043c200701310020075195401d08590003000c2c00c49044030300042c481070149417181c1c81b400034854004840300b6001580d070070b03a04403441c0040c640300c400300007403000c01c200c0130780c05024990341185030202e02e96508850740a4a021004900d100ba0010200d8501d8203041400c00e11b400089588450b10500328001e01c1004e0103a070b1562160003152042104401b00c40c071a4000d202e56070b112000420008860b0301d0f06440c01000744d80384c0c0c400070b0781c8114115400f080c1054080711240b0082d4100720b0140e40c0c034a101030048505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 698828507 1250 698827257 698827267
    0x190221100e0c03070509060a1d0a0806060d020112181e0804031e170306151201090c11032a0f0c120c1305220c0603020715090c0501090b 60
    0x71030002040c080c22180103500c00100240d01c0e90f00480441c0c10041d000b61031030b07a4444c0c2c01c40005103421030760401c41c1d030348803480c42d070072075461414018280c20756501174040d00041c0c07113007810000a00c1044004078107002448a025150385d420748644500700500414440c216240c1c2e1a1540e00181489814074506004008d2040403801000682d41941d6000b0080341d1400d00d00b800c4084404e00a4400801c00e4044001106031201740f50041e6028030b40545649507241422404c14000c1d000c1c0846030440903920400403c580c1e21300ba08401042c0300e460800906080c41c5046590855200c0300103a00c14102c05442c0000044250000040190f601400b0f001c11101c07028425890385024121248140303082101e0042115040c440003c1d8a40300800403c00b00b0160050200a000102c40000c40106c4c244034015024001d20030761b010030307603001480f5107a030360070600b044e0001d400103d010303214586018407185280e560780c803e41c3d00150103100101240e078601000103001c14820380044141900600c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 698829757 1250 698828507 698828519
    0x14060c03040315020c030705100e19020d0602040b0f07020109090b030303070c06020906220905040804061215060e03060601180e0a020903150702060907060f03020319022110 76
    0x1e03182600d501008006901103070750998000390161040b10340480c000018080108030740001d0072091108420014060144441d0080c3c4c0c855001c181c50000b002d0b08160b50340d0040c030309072401c80e03802c901c01c6c00300500b025212008088180c01031003c000c980d030340001c0d0600640d80c011b00100e008000c001420320004404001180d242e00000c1e0000c410300c606c1110388002c201464068402c21740b805801c0648a1400e5010380380c2c01d0b5268490b009112922103004120410300f401aa481581c0001d0006d1606140520456101d0420304461880950341c114004244009903427400c0100b0190b5100341d91050b200b0201420010003521030b07414400c040314100c102d10304900840c403c40e13010319040e40d010b0f620722403088040e21440d0002a41802003c03179100c10a248561a0350041d0803e1b0708a81e040d0b5102029180e0340c1c4101d024000c0841d0200d80d41050301c912907002180d00941c4003a409151441d010082c2d03007030784c01405150403040400040200300100d0300c003585034000c00c0284106640341c9018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 698831007 1250 698829757 698829763
    0x60c0f0a05101b0c0303060302060a020106090e01061419081902090a140a0b044101050913030e120303070e0d020f040207050a08130e070503040302060a0c020c041514060c 75
    0x40340f0103100800d5a980c0034140294000401150050700840c1e40d0542e02c1d000a0090603203000d41c4d882c4502d010310702000070350144128426624510340b00524110840208000c0d030400882002d41411125400301c1c80f41c5007440300005522100003035000c0c4d02401d104001c0d400800401c1542c02501d07140c2200401c8603003540d0741d9003049410303000040715103010000c03c01034801812401400000060f1051945100c490107262000c1321210704109003800a0100c40c5503c401e1044950040c0c01c0300114a00c1c220303094600c041d2611908202c20225072400120300811a44000707440603803c08810080c400380c210203413110320203088580c6910030203243d001510f243c480c0c803481400b40e1741c04107032300c01000300400200100ca90444640c50f00c40030007110032154080ca81c00390310103008a103000301d0081801402602c1c000e0b94580c0240890d41d403032032820001402010080d02c114406c0894811664803540f05000300e000049018101460a03c0c64841c01003450f00700301c6004060400c45817031660404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 698832257 1250 698831007 698831051
    0x9111c030e030a0503030c0309070b0f0f1309230912040927060e0c04061206050606090411040302030705060c1c1e05070c270b060c0f0a0510 62
    0x40c180040301d5040d03080800d103002581c4000804611002003030000841c0c850002d144550503140032100402c0e2a007410003824062030801f5221f060007030190810506181020348501c0d0f00c05440d51481540c2c8108010594008035001404100610020004900e817503a4040e4084014802051564440c1c052100700b4801c41c0318030110607607202410f4030074a000404886804d0f1000592101808150030074500808107601007020341e10644142e1203070b9082030f02a07802151000280850b001c510380c0c423507401912008218641c440d60070031032040c4c80d83d00c1d48200b118805040610341e45490952050520302603454000c80e00c1010240501414600c0020302c078006070b0090031304c412042e100c054085c2d80d40074030b6a038010038200040c0c50007080168020041d240c4680145040f580c11903660884484c40d00721404511000400c0b46960001daa04a03004000045005007560349820b801d00689401e00364000d10326205900071200d61800d00004000c2c008031071209100403c500840c03070315400301c08444 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 698833507 1250 698832257 698832263
    0x5040605100807090b0a0f0e1006030c0e120a080d06050301060506041410170403120f0615030e07030b04060501170f150c090a0306050702012a0302130b0a0309111c 72
    0xe80400d071170380e031300d500c403c09005040c0d03144800d01103034542486040b07120084400034545101d4450000b1030a02c00c0c042c11071611059140c0030301c441b02c01414408200108009811207108100c000320008084100815030507200000014000c1c0c1400105800d40e40541e1000380f0a00083c403090114020072441d038400010100e4442640d03104081c02507845034290780603091482c0c007a0b801c100505401507035048007280031117010800317840b04c5119482100c03a01d014030b540c00031064000d00138050296204400000c80101100c0079a95240d0300c500101408407401c071181915a4010042400c4040360084265181c401a0a4000b186081d99a5880d103500c024045100c440340030803500c14040c1c0449030708101c0980301241c0309449041a80c050b0806031483c100541c030304000c1100000388040e21400c001d0030792600b1010096483d000b10003039040400d1104402c0c0652100180301440c203001801c121809890200f0040c1d0303a802d0001888038107d4602e40510b0445a1602884292410b9400300a40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 698834757 1250 698833507 698833511
    0xf0c060a08100e0108031206190501080702010b12031e0a05070b270a170a05120604021303061a0d0803130503090d0506160906020d050711130504060510080709 70
    0x1d40c4003200088040540c3c400711031108075100102e100134001c0000c1c0100310f06640100816250307941413112603c00b18100d204e4984008034280581d42c8540303885908a03090340300100324095003100194020b5803800985155034800600c5081c0c18076210901642d542c1c14000d214242060118058000d2290981c010712203041c200008400429500004241000c1103503401e0252840300541e5680d0340000720250303040c060b10030540030f0b0542070f0821070700102001e903501801c004030b003450035081103801380040e5801078090204507084140d0360b001400660090b000440e0410003080b1324001d9103d1002694003038810800890302107a00d100c101c1c0d801c80480e00140326060401e0906a0a41c003403800c4035540209511034820912000003003c50040f521802080600701c040c090548400301140700c3c040241e0440040c007030005001300c0161121078000d03101c803000081c90000103110117112a0721070000580c0c0d0402e0009000030b512500358084809011065080d003441200c1d07907190b180384146d01c1c41726 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 698836007 1250 698834757 698834761
    0x80a06061e121103040f02031225060902060a090f150e0607240204050405060405040b011215050406020a11010902030c06072108090f0c150a030905060702030c0f0c060a08 75
    0x2c8940d500400410811580075500c0b801c051602204480002c5400e03442485061042400c5180720000c40386650b890203003c0542c000c209180982e000220182519003641d035200c40c00150700d560008103a044001c1e035500144070b04000d04280c01c03200540006402c507031020441d011483c0c1001c0d084640c204110b03090354555155280c0301d401101c0614901803405003000c1034038030300c2400e0b40141c03050760402c440600a42e80d80720184030868108440152012985400400c2307481c2d2148107042c91f4601950030340340390142400c001c5081d68003c3d10102c0d925a130000b20740e00c0350f50744500601c0134200d5075002800030a03801d4000a60703e03002e040c1440d1081000280c041c0401c8914050114190741c080700668520303c00440103800741c2c070700320340207103c900400012b48100800480d550b60300d6080200b00c144120040d1701d000b25240c10180081050654400e00d02004c1442002020300c5085540c0c000c43d80c5410300e50341c060811152250321242544000030880c15662044180c800d450a140f07031410081d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 698837257 1250 698836007 698836037
    0x30318010f110418050c0f070201021002030718080313140a0512060717010317090d02041b020d050c03040b0708120a09032c0103050603010f0c080a06061e 68
    0x400c41d014a20a51a180041c10907007662400050710407100c41101076580780c41c2a000950594000322041469441e00300b15003120860104007500000e4018811a400c0c00510780d1140c04076030060b179918010414540303002c10440d40fa038410030f0260010708003a60404200a80018007400107002c1c10021217000107001c0002e07112501c500005103002000320950808005802d611500d0568800001640c00e6010305041b10442d1071041c122548405000d000341c3c41610301000c13940141c2c640546c17100c0100d00100150790303140200d08100c0a0104100c8007019040e03006807404c110308451409103c0140025403900b0008010b0704c013181e031419000c9650344030f540f07400b842c0b40c40b0380c0d00080491021402070140702182035000c500d02170700c01d482d217112011020b14040201d4451100c2800c21100e842d454030590b52081e0070187d0006000743c0081211006400c4880c01c1c1c940800c06000000d00e4401003100b400801c0c001e6200910403404c061400e000102c034458a5004040b11a1003800501214000d03070b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 698838507 1250 698837257 698837261
    0x190803030a2720010309030512040203010204090f02030907060305061c050a0b09100c05070f12030b0411070204050a0b01080103290106050a0e0a14120109050607020616090803031801 80
    0x71600c0380c4000c0e0100c07150030720b801a00004400948071007100308000b1007030740394081e105501b04c0d10b170941c581e9414005803405041034110f000700304a80554090000165007403050040c40d500720302c03006002da02c07407411856052811440c1e81c00001054104400d2002039240e280b800c0c0e103410030083c06070b0580100341c02c04501d04802124010b0002000408228584a0101e81d891620380c00080c1070100e030759441011512401107507000b07000410080600c0002132440070003059443c0b007a050203d200d144000004086501140a868010100256010841c070782442031540c054a0440100300c20b42c4040d0000b4551181408003d103001005e00106190300c00e1300b003a420b01c100011054501c19070310f5107070007041034201c100040c0c0402c2c40d0400000140c649000742c070050310700071403134510f5025011080180070004094512a25540d455243c0701098083c80f01910401280c3c000345094209000310324201e8114094503030030004074090a024441012003100d03044440d500f000c212a040302e031038081c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 698839757 1250 698838507 698838551
    0x1090203120a02160503072318060a0501170109110d02130e090a0b060f120304030807030905030d0806040b0a15020d11010b2803080d0209190803030a 66
    0x585480362a40d240c0071511410014124110076500391030b4a4443d00900c209448828012141d160301302807001d0240001c1103052012520100800c0c16041d407078040481c1c10250100e01e0b44680e0b00d400001c100c03150134442d00c004020482882c20201c00800f40380400c444081c1130185111590311401070100e00001c0c035050702d40d501d80b035240855941290507400070745403840b4440e049030701600c500090701410011039502c20703440d045121001283c0d1480104100e0345601c010040e4403000c10118050000e1040010300040e61040701020b956100505000e420103040d0360090b403081d1700155031620225480200c80e0f401c107200b03a5003c00c04451307a00002d402d07080300d5009401c940b4805103070640900c3c0e0000d0351704035000f0391f0384031464110030301803030740303003a0307620a0202d0784c00c400d88150b41504400140d405c41030320955440001d01c12a107a81d101c40c11980b00300d450704082e07a0041841c90052902c45000d0030403103000e2450301045880c164465444e40002003040c4101030307485182d89486000041000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 698841007 1250 698839757 698839759
    0xb09131e03021906110c0705031e15192d09021c020103060b0d290a180207050d020607020d02070f030b10030210020109051b1507142a0906011e02010902 67
    0x240c4824510042c00c1d075640c114400c5900c03e1203502d12542a04071014122100040c1d020080c2c140d03606010101e41e410b81000e8001075003807091315080c4071f4034485c500c151a20034145500034480c1c80410700d0001071880c0d4dc2d040c00750150380350502d201c00503510000102000a000b120801d14008030f0f0005a005003031551240c806000002003a10310488164064004481410200040c8100e0344690b000c164030000c2d045500107403032140900640c00251101c801e98074010101502c1e0007a05d649203810840f13507038401409a44280305100400d0340500c1006c03000c40c203920081114901e0040c4940d4a8116488040c00070300b00480405c070580980100a405190054004040c0441c03028009000b4001c001c02900c00f8040c0d02ea021242601d0003c031321415103401019070503040c508250001486c0e00081c030488000e414880703a4541d80d00306100c8500010190362090440c030b010b000c044400005108286c80c49103040404000c03c0d0b03078000203030a03002480b0510000040c038440000f0b82c010300d005030313001e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 698842257 1250 698841007 698841041
    0x18030415033207050d110a0921150b03010207020a0e100f0305210c15240a142d0a0806011d0402040b09131e03021906 52
    0x11503036541d019048940c14880700c200301c40c201064441c00710388861103040c00b000540c40030b001103000300e48190050005200191000035082e5500041784440b030b0300c9402000003040d000d040401020454088400c070702012502440c060300c145941c0ea82d0003843d1240741c48005551030844100c00e403001d6054640196011341464035250b00d07005103180c1c01c01d040b07980300c05c8403152080c08107002c040e00c41c481d801c895010307008006030350715a01c030041203410b0328840300d0034004203100c541c45040c800c01018015a0030940c040d900d80c20090401480540071419220a000d6140c044e10820784a0040f2241145c45030003450401564410002c1c20201103180710020b9143d5010311792050861100d8030303400402045540c00800c5d41c1d240c9072117403298024451000b4a00c0910815070291071800c0ca065482031004000003422070310703c400100240c100380d030300b148072407400b040c0c080800c48580c1c11140903101e6000184031540060760025924501c50328080e4112240070500c008000d02e03500300340120201c00c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 698843507 1250 698842257 698842289
    0x1009030f1a0f0a060503030a020304150c120518120c010c02030f100204050301060e040302060103032d0c05060f150d060b0a170d031406040504050c10110c0603010509180304 76
    0x1d010b6a03400540d001e0710658548000010700c2d03d000001c5586089080d009141000e01d85009041900403c1c2c034124107008507040110001030b0800e418400001003a01e80c141c64503d0b910303040d441305100b200c0b964056034160b0400c044002c00003c808040300b80074070744506e0748000751020a0405015204140d060f220704030a0034414180c680240050394002e4000b008615903548aa0540107003d80c0c001e0b015820420050012a01c01d02c940c0240c440c20142e1f2a8030007100500354054441810415400109020040d4040040a00c0402d400c4022840c48100a09011400002407800399446e64822054000e48004006264120003003015000701006486070355486914a24050140c41d90007500802101383d1005020b407084003181c01c0041c801d5203195490000f44801080083c00581b02ea01c01e00c80142681d980c0d40c0c03c3c0101c1b03002076039505e54440c038050510500e00001d6000061060742c00b400140140c3d26030301c40003a40320381c05456000e40b0401c100d035020f0951040d90040700b4102c1c0d407590 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 698844757 1250 698843507 698843521
    0x9010e04060602280308010b070303020708031608151003020d1812110312010b090d060c1220032212020303190b030a020609010318120306051009030f1a 67
    0x50740c804812407900c441800040f500c00144d003071411143c001004612504014440c2a0b900c13405061094031030b00780145131068035103d00c0425041110006100b800107502c00a02030380c00003200f070b040350801001d041242c0a00d00042da440b00221948020540d004c2008580302400d44c101c442e0703000c5400d14403034a00c3d07103608001c01010161404070012076800706050140340780c0003044800042d801d2404501c140d0800410001d10f600c001707140e9a01c02c88001040c000701e030403881114981d174034a480307051031304058100d80c10950b4000d181146c20300c212041c05442c10345d800021690720880d50140b228804000302c510300c041c0000c00401030402511080c02c42d04c1250000003c601501c882d0701ca8402c090030b0034503a0420780b20b100301c3e62500341d0020b0345d4900050428402405480805041c0400c01c070070041764049200074070b41025620700b86404400c01e41d0f02d805200b80c4000d04026102c1200d02403459001400d0000c0324400140444a502a4a410f1107480708240c4000404041c180c4020b061800c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 698846007 1250 698844757 698844763
    0x30705060903040e0121060e010506040b030307050709050901020c0d05090906040504020f151c0204031b240504180e0d180b0904060306090b090613110609010e04060602 74
    0x502210140300d424007180e0100000800e0350100c50740c6401300016a070070440d034400c6420111110802101e40020008000b50540c06050042c1540400005031881d00c40100310696810b00729150083e0001c01c0380b4408a01c0101c1c0b040251040c40b500032482e41c450190450092181c0300044503140900802c03220200c0d4004020000084100c501419a489801c00c000894100b03550082d80311003020140e42050412594040040d4942d14809040c21050540142d01042011030811400c2c0d000405108200744050802611b12208461148690905038880341880480e0403840342c0c040c4c10820000910f20403000c8801410626490303400510040900e03002500380e80800360b5440c040c003054207024521030700c1400741d440c04100e94070b04514074080844006034000c084468110742c4803040400410b50a0107220407403413058120070001c0c508105180d04101026250182c208003c04820020030300358a81090a00000c0320f80d540d854460f400141e40c044003c0e0b46080d00141040b40009880d6008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 698847257 1250 698846007 698846017
    0xc0507091b210e0a170307054303030f14191b09090f05070e0103091707080a0f0e10050a0309141e031201030f052517031204020103050c070b0903 64
    0x14901d0707452820010643c060940401c0b20007d0005000740000705503c60850384154400e00100380f82405070b40c010a03805200170001c12131114598012403558105903142c400e449060000da5000c011040c041e001b0303030300111006040c41107400d0041c0c00c0a01c102d0250383c840e02c4a02180d40385060403801412015003414150310071685203a03e001c0000300e21048a000f010320a404560303801c501c03200c1c2c0100540c0149034000c010b03501d040c0501000c40980c00e405e0021702d84180107201450f169001c1030001004454242041d0080040f02e23142c100041d03c80004070540307844242015a01c9100c0c10300c040b0000c058140b00a04034840300b55800c8554040860070b064080d0000519200b01440d000c1c030103544e0302c00d0101421628205c100104081010348400c103004500c0b810a40e002500e221218980c0754020141d00d2150015000b82040302206c000b4a55048a070191b01a41c00c00c00c2200070301e110500c1c0200301a040c19200c40000e506981c44000701c2b034200798001100312207400c0121a45940c6c0d040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 698848507 1250 698847257 698847263
    0xf060102100e0109030f08060a03260706091101180b03071b030903050105010f06171305060f06090709121410060f08010507050322030302090603070c0507091b210e0a 73
    0x154490b0441a944203039141d48c413030b41c00603100d101090329641d1a00c0181643d480b46400c0341e8486504010180c1141f802001000e000381030128400c41e041c00d040c0783e0110710300d8031281407104456080c916282901007501c01c80e80d0304011551030340c0e40d900094502004101c0800c000e8001c003203102042641184000c0e09070390041d8001c201c40d03a210b03814404040c00f02d02890340410030114005842131001406168440480414492000c17426942d55162901c00e032002c100d0070070400304000707640c10306100099000f0344918002c1800c41c80e145150f40002c44400c0042c100401e001c1d040c002d0f216080008116604209070b0401c412940d8042c0e00880c0c1540d409400220f500700408940c000e0705c42e00c2924000c0044e103500c0103540f111049103011005890504409264003170201840c1da588150185d841880d290312048007038045803420508049003600304011461500e2650b092051401620005000031418401c0980c006000039a00030035004114464aa00b022a002d403030f6800803c05400c1244 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 698849757 1250 698848507 698848517
    0x5010807080453040506131e1a090f0415180905010608010b221103041a160f1103091504051309030c08180d05010e0f060f0f060102100e010903 63
    0x40c081083c0501428840000a41440900c01444503141140080c0380e020510001c041e042d42d520341100c0028040d84100b0040c030b146001040116815031410581001030031031285d890030141c0800074050b00304003882c0d10b02481e070b030381103518044e18080d405e180604003911f03240b040c28103541d001001a080307180003100c1650030103000243d95001400341c859004801800300f20b45100204c0351600340e01d040141500603585070441c180c1100b42407802140142e002d002c007030301c0040301c0c1445090310000c05460b85010361a10581d010303880c0c2d4422404040c030203152500107401151842c1085c610301070010040d9020703070400c1c0c000b118440075000400441e101961480c0354060050030810484044040240c041034002d680c0400146d001001042203121001c00c030395510310104c010601c4906110b0044460303a5688000f1030301a00200403144100302000014082407800b0784c55aa510103010308a20503182c1c48102040c52a0b00920000c002640207800400c07401c20314400305030203402c0c0100160040380c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 698851007 1250 698849757 698849873
    0x100e011e0b240406300204051e090c03090a0203030d0504020f03150130110114040513090317090a020a05010f0f0c06020d0c030b0405060a050108070804 67
    0x11100340724040d181000744802c40c2082d29210007075507040c200f1800481804a010200c0110311020340803a1071a107481080142c58900b44014040c28415016583c00d952400f40003140752641d03580a141e500811071031031a500d03500d809580c649407040c208030007580342c000443d40c10718003a080d0f40000d201d61700850383c0c8001080c29009060700d42310500340c0f88856491483c014000100d80100c820641150071001402d81146c1038141d2400203d04401207815458240000c81701c2d607880010b6144070060301c241585001d01e05000a106403201a591000050310b9003846002c2c54025856624464040039428840d403501102c85912811491012441016203d42c04500c5500c10021030b09a0041a111424002c0c01c0000070b4403c00003100c402c50300d00e6000c01c25540c030044a030280000101c1c0d9501d011500780c03812030800081d541d0051441e1b0041c161410100100e83c0d001e0301c115001000350504080b580c07114100440d41c034890303200c40c00800050080e6204103070850302009501042112030305582c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 698852257 1250 698851007 698851039
    0xd121b060f0c0323040c03140d1d3102030103050303071134030503040605091c0506070f050c01050103080301060f17011a130e090f0d02100e011e0b 65
    0x44081c3c201c0f000e4101d6042e441c5000d00201084a20703009405001000d44043c0c0c7c0b60f0750308130068902c49512030030390090529203894903007118a007406051814800c903882c400c450007240d00ba0166032403040c0c0c49000000700943c0301c9802001806045844103040d5642d42c0c683c2040350781c81e80151513000000d07103485103440189002080300165600700c0000151400d044642000d1402c4055039841c0e41080e04000020004008100a000800198072899191843c000030820341d010b004012050380040000110001440450002d50089075030600b411403885e15101142d213401100300a03200c540c600350010060142c0341014604035002c4d940d80421900d0740c0b80088071841c0e003224554040303000920040c0b01c0c10340754090b480c0d0668145c211590074400140503c008209040d40030380401442d0505102e0421018030007040006071004c001d0014000c98000207580f5207950725140100d9590307440f80386c04698207410404c20000810000581b44506e14807000041c158694824402d0b400300554101c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 698853507 1250 698852257 698852261
    0xe0a09090b010807050a030204020306060c15070f02061b0a12061d0604020c0d0806030c04051e0c040602070e0a060806090d0e0a050a0b0702010c05070303020a060c08060d121b060f0c03 81
    0x5455001c6d040d00a01c1d440c503402d0101030f420152041e5403004007440407002d10300301001038400342074000c044c01d0810708007604003030501c000c003030000e0045400110070403086c1c030200640080031810104400e43c0d110180c0004964095010400880342070030100b001500703401d18150007120200365501e0078602e8407420100302c102c0c41803140600c00c40d04000d101d01440c0b40241c1d41c40c1e50252014054a030750100650004040f80c40844500780000040c440c407200c004070303440d5038075800078403d241c00340b40a0410300084c0da03408c001c2c82042c00c100103900004500b417640b40c000b02c0042005600301d130301a00b00010490346401c0311420f22800140035914803d040d1a018664504031603001d03049000080c10503201d024031b03a00002059040c003003984030700c03400204100421030056000c2e0b0701808000301a440c046003621403a01c520010004002c09101035982c5000200d0728460344007200f844081010082500d000a07110010340000071401810802c1c040c09400144d0381c0c29440008100203038181d101901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 698854757 1250 698853507 698853509
    0x607030c0e0411041a0d0b0f03030d05070c12050c1c09090f060807030b1b07110f030f0115030c0f0602030a140c070902220302031207030e0a09090b010807 68
    0x86507603803100601c2c146a0300c004044411407004900e8103861300807038848180040604a0900d00000d4110b42540d298070852000b00804c0b1180031500303a2020020f03503240034200000540e50b40d5640451000ea01800410f400780e43e00c80030116125501c0d0320040c20310b800065043c0c19a00501e0f01d10400300c3c0c5941641680710020751540010507060070f030f03804c005040c1c100404001340d581351070114841400b00246401035104601e240384a10340b1a000e590b4141d01d80401400a45050001c04009110200800b200083c02d5600c06805a50741d40000e16200c3c1e060001c40b900d51800c82c404a448404241c07031404d886c051851021055030703c0a4500500c0c4452107040010380040c045111191f10648000b481c401c4403003070650500b80e24440b02402d01e05164404201d0907070018000c100d1200025844064408000050f84403c1c903503004280c56000381c0c03400c3d00d10703600c0006000042502450a010b1031004c040d01c82d00066842d800302400400311801c050303801180310400040c060a0015401e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 698856007 1250 698854757 698854781
    0x150c1c1e0b03150906150406080a0b09071406271201050702070506031009020f190c020a050603070f0f17010b0901021204180b04060803070c0e07020307020919090803010b0a02060703 80
    0x5d90394002ca100c0c000050303401540d502a48400d00000c04020402804c0002c5011713003e500118288101080c6c6055101e521a01c000100d82c2c0b11150b40e580d07818241c86401071042c02c0903849040c05144124283c00203096035034881c0c10804941403036401507001606c21442c54089600e5144c84800300050f5000c119100c0d040c0002814081c042c540d101d8000d04011050000100d0410501a010800381c001080104001440a41c09078056142c100302d070303200403c03058654030300c0c506010b5401054170080c1d8951500703219410144100c4144186514281c952882015240550f15034000c502c050b0b01c01d048190042c414985005903404a00c0708590440f00300e180b04190007c210300d107020144c400364140036406546c2ea0030010f0310312020320040c10b80500c54036610f6070b810700b00340d10800c441c8005001c80c01198424808400140ca400550681020010800c4250140421140006805400d00003001e904d804000005c030342e4400760203080c02c22110703002d41e542c41d40c503200200d00f11810701c2d20746 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 698857257 1250 698856007 698856013
    0xf0f22110d12030506010221090108060111010905030702030f010507020d0e0a1805061905010e09060607080703050c1c050301051228020102150c1c1e0b031509 70
    0x40064108004800c030494060210a640780181c0c0725085020000c500020229460310100405982c0c10310084d80e000940f0600c1d4034050144000c400da9074014030041c42d05000245c0003203202070703004070300340220010908001c0c030881c22207140117610703038000710401c0303000c2d210f0002c40240303950301801483d1040ca03142e4024024446541022a040852890500c1e04044941c2e00810641c048140c2d8007441c0507500004a42428080b00303004c55007003c541c9580c200004c2c90010700031a1303441020f45c00004000ca441f40c0c00d546540c0c00140d058410703c04d0082040800040142c101500b120241148003070244c2039808c006070180c8030800184100411900203401040140070500d044426164140300c00c0c01200c2d603000e075552400444000c120315041c107a00d0035010716001c66a04202640140304004e001030340505140d915032815010300b00001400c1c012481001c1041030f01a440600c1070007004030748200803004c406080000384100d800b02c0b0700174000c50540d40c001ca103010702c2650140301d610b001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 698858507 1250 698857257 698857321
    0x1090902030d0c06090c12050c0306040c090f060e0423070b030604050406182a0b160f0f0f1101030b0d140c0303040b131703040920030f0f 61
    0x110340c1c0000d5080304a40f1240ea80b10343e50040349008901401804894030390380d1a47c0040e06090346000c0381e0074483c1d480b81d8401c90170000041c804d020200d049078007201021510150030074240004d001a5007051905200800c10001801402c04440322030f800300c00306040048151000301c40d103410139800b0b50100408100080303030450605502c00c980c01801200001414a4060183e002d58250203100392896101010301c1422900580101c126400b040b20444c0c01c2c25240c002d0304284c0b0b003d582c040705d1301c07400806000e80c1840040d03c41000220342c0000880c006280070b1800d01544184110240d03104005050365804650182c86070820700e1200410246c6040c21990790104480d01c4100c000c6070034000c032080101d81d40c408002800281c401c00401039110788039141036a84d003210755030100e044540c01c5101c641038003d02000b1a800e40b4a80c25010541240c60804800c4000f01010904440743c000000c10600c403400407649805042100403000c00f40d00c03208500351038564a121909514112424 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 698859757 1250 698858507 698858533
    0x309060702040f0e07140406030b0c09240a021c08131b0b07060506090c2d18040c08102105060c04030512120c0c010b1c0b0109090203 59
    0x160150074802000032840c5a800c10303450341502c01810700405076500c0a40c0500c440300000300f550103580320551381003040341e10715241d00f03101000141c403200100d14005070190b03062b1100d000707012401842204650621820000701007050380701740c40d901d0050043c2d440d40c580d40c280381201c107802c28456a40340c01803031300d80305600c1525002d416030448400c030400d01f04c2c10400445030701001c010501d1452568131486181008003c2d154001c240510070101602009019441602038070f103000025000488041c0384440c0a031101914100f10611040340401e04280c020030a00140c0c01501007601c003444101c104a10070354010000f658501201e0702885014400403505400136509210301c00c00144045a458980c58103003201680c40c240340e0680050305009000301080342c0d10444c42c040394085c1c0340101c802d100f00d2614801820000407c0320002c2c2c80d0303e54480c02d42180001080003061a072401d4240c5d210b0f8034842c80c0c5c1c5402210300c0e2001200024040115115449641d0b4001e00603009894141ca = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 698861007 1250 698859757 698859769
    0x140f061e09060f1e0909161a091f180b0d09020118060504030b0f010e0601031d060901050108010e0c0a03082a0303040b0610022e050f1008070303020309 67
    0x2400b142e0009001c2e01c1811466440c0340c8203910040800a1101c5a04400d10602095030401001c510403980180f0740c0000a054514410048440400c0c010450480c4002030020a100310301c4903070f81c0684a101c0301c1000c0d08596501c40e480c5440d0351504c108410000c0c0150348207088038403a8071b40081041c08440340d00301e0b20381c0003c5562441450000c80e0420f01e6481841c1c0c254180c0c000309d00195021600b4810800f240803400d4100720507080d00d00c0c0a40c034183d1045000d8500428486c101760300c401103c00386800313082041c54212080019203501c0c0c601002014002e210910822600f50b080441072126510b020400c00f001d20809000c4440260858503040450780c4200e48141815074a8030300c2288201195025030010140d00000e1580c03401c040c180a2101c100180c9200c0c0724400240d10004e070340da0005000641036a0301980c0c501151000a0040381070650b40e0703000729200c2d0a142c10400700d608210000c620504101e9003400402c1d0301d480d20281c1d40e54441c040100580e02c1044400590300d422 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 698862257 1250 698861007 698861011
    0x91e0c0309200a0b032d090a0213020705030c0a05010f0c08041716150c080c070b07030e100b0a0803030c030714191205330d06140f061e09 61
    0x350400f038806a0350180280c550f8421507100f56504425070303d014100d420701c00216034080d1070000c01e83c51410314510480d05c4011030440207200e07988040c48142785071660b0301a0303070110f9001070075262214404d07040170307465619440040361154138117013820b0041c031840d00c60801d403610382ea03541e503070184d440f03a07a8940e108441403603032a1410707024400c0340c0b4035944801c0399074922841011a03120364802660700e8003c0d200c84041c0041445000000c009071281d0107016240e8003500014078403101d0315540c0c401d43c0100604500f41c2068001d00707041c05021500c036003100201150a071110a0300700d89d0380200d580c403400b068a900c05019400c0000c500d6291140c107079214200b800d03610351440c1000c0346800c2d400032000800e802010403000401900c152a0038418140c0c003108100380c546013890a0842540704000f00050341e0020340e07041400c501c1c640c071040440840c81d5840031007004070040e0101148940301044440002c1034164800040e880d05000620400a12912500c10002a40882000305071400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 698863507 1250 698862257 698862259
    0xd021201290f0d060b0c160605250203010f1a0402030c2d030711060a1127090c071e0f02040902131e0608010908040603090309091e0c030920 62
    0x10030b00c585019815180b14000003000394100c03246d991000900c03001d082500201c40303141c4843e41d1100030055240c00c68211202101d842072407070481c4070711807504004604001c10194040d807a142c00c1d82c8041505620140e02c1005d0341c4212110b10f0104410801070707100442e0600c000c00000e00c10080e10007501030340d00050440b00740d007170906401d496072035061980088a000000541c01d00f203000e43d42d001803001c0d40c0c001741150700c24001d07800c0518804845101d14915512420544070075503d0080702012401d406080040c03c0a4042c00c0581c0d0003030203a08402007e40d151011100c07600b1940e0f0410007401041507000d241c1401050340c90302080024140c0b0ba200b41c0e08440e1940300b403d4011903030320031b00034a0b50b16014443d201d44440103103801240c0c12034103c05a207030b140c5001e543c0450840383c1540c085401178500410074010b6441c01b12001c201c40c0e800358100b40e00f0015280c040420078801032401c009420010407c0f490355007021015a43c8040001c0d0034554902c00b944500400078014685901c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 698864757 1250 698863507 698863537
    0x6051905040b0a0902072d050703020105030a0605040f0204060806010518090a090204090f030905061201031e02060c01020913290325030b0a150905060f04020d02120129 74
    0x5520000340f020783e030281c18102ca610007401c168100c0300c080d5807440e82c0c060440810385c2500c407c19a03580b075500d0f200e6000203410300a0200c00100d44503041c0c0c1004000e808003901c18054116106001001380d00301c0c1c00f803440410b94200c00556a94498402c1d101c81100443d9040701800309182070210990020301380061007515010048050303140c50003000b5606201d110030169602440c20014249142c03a00200e1260104104030702c1c1003400100d409040d250000303455001c41c107401100c52022480b10030b000390001c201042445841d0410360103004644001d8402c40701101464042d082220b15020514150640c2d4142d15000145143c5101944070ba000e0215421103026110214120b0b460404806050304441824410005203246154010301031403800c0c00503880c0d00c42c0030005140381d130207908080303942c4a00041d090f54074048400c039048800340085564846c03c0f200d9038080d521040300d141303140d2070310800015000740350401d46c002070f80c2c1c2d445006050211035450300e04e9580b01c02040100ca031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 698866007 1250 698864757 698864759
    0x3071b060b040c0e0a05011b02010818062502060103080d020a02160902040303020c0303130509102c060a031e0602040905010f08060703150e0705070515010906051905040b0a 76
    0x51624402d1585009503a203501205815200801082d8011900807034100116402150b44004002a08230412542400c001c1c4860751007100303034030408500c00041c003424450a001c3c019000e42c42c80415186c0900c0c1d0700081003100300000d040ea6140300078403000b04107000c02c210640e04000c05501a0140140e144151150001c01100c000b00c6a10720760000d070415a80003c040081503010020512040015006581030107250480b854883c2114441c0500454401000a0405503601c940ca4060a0701119440e4921202d501c9c0190011030300407800c25030b5000c18003107031103450036440001c203c1e54001031140c030000c1000f804004280d0712807003c03100a90240f10214040c4041d014441c0641110346090049919014600b0b14107480a064081410710308582c0e166208030341060b450684d100144480301c2a1a005002c88951150160103401801040c1451010200003003245040340c54a20302404000d0b1a44104209a403103417041d22403480c11010104541c4c1003940100718501c1004005159071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 698867257 1250 698866007 698866009
    0x9150f04110915010908010605150a1403090624031b010509031506031603080909190e06012603041401034503050706051906030c031703071b060b 64
    0x340c1020b590210812402c8040b03c0040e5134000c000c00d0060040c40001e020207464900031687d0540540b000c0c0e10340c00d0740000c01c00f0340b603400f945080c41c00f06c4101c107a031581c80c500580410349408095500300000b09100202910b4840c0d0140c80002010000300a80145015002a1000281a00d8090707050000610900203103a400340b0400c420301d071044032001041d2401004143c100740e00c000c1c1c25812950840014004a0403100c00c2e10425001a21407040701d0b1100994440c901240313858140c0180d0038100e00b25080c1402052680c12a00c0c8035008404d422a400b188940e9910421030441030b030392040c40104020304a00421b4500001e06040c0060040245008680c4604190420b881d2854941180e050038510692100c004030180030302e02601da00c001d6900501c40e1050302000b4101c25100c0b0049081c80f0340703241c89442099402c00c8100303c0f0b191b070b9107041d0602d21030b00e202c155540c00e0400c0c43e03501801284422203100d140190f0750340b40c00f00b03501c0800290101200d01c0a0384c0744d680c2d0785540c00321 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 698868507 1250 698867257 698867269
    0x150f23090727060501230903101803030f0c0f031a03030307110606100813140d091404050f0c0a03110a0504140a030510230c030f09150f0411 62
    0x5009140d4015590b41100c415101503401980c0928100005411150034000c40100c050801407000c04a203030360b90b11aa80000d19001c00e0001c1c0c000c00510b0100244031008a03403155161607446510144003540d11900080704864160b42e009021070308400d2001d4566211741d0001c0360076140c820313111407032900e0b80010030310b95041202c00b0004941c40096003140d4003020001a80c0c0010708039940310850803924001011144003615010060f608079050070100000209032204140102085448690035004001c1c44000701e442029001981c01a90302414201405868460401d12001124607143c0c1c44030140a54840c902680c00c140eaa92429048101c2c000c0c000d2030240345d945d944507140c0d8240f10b0091005804010b40b9845035154801c1000040d6001c200c400d500e405210700014080c400c41c0e00c0d02011607000218132020050a01048400f242d014041c600441440c42c01c0304882d42c0c2c0e03913003240d1381341d07601c1c1142c00c11001a8030000e218042002c0b11564040c0c4152404180c2c405000c1c08142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 698869757 1250 698868507 698868539
    0x3131502070c1703032703210105040605040e06040f08071b060e0103050702101a0406090f0605030d020604120504080a03201f150e04150f230907 64
    0x503211107004001c10650b0802494294100c3c00b00025600d581402008200d000c1009001d440800105200c8000f4002041c026074095054500301071b140e80003000100711014900740a15403095150601c0402e980c00c062054901e0340b54240000c0a80f61502c0d05e0300302d61a980c002d03040310605c800308004400a641220854840308450100001740c030308060b0068005e510103c54241014036280400500c991300040000e02c80c030212000140d000b0414001100ea82d456204842e0072600300003000525445a81c00800b80080c2c80104000280d00c80c001c240e1154203003000305e03006900c8040490042055004070f4800040603050003464550384240c0c0c0e50078403e00714419000301c1c2c41500c902e1345900d0006014100c960380e06016106518030f00320311651840c28880a9050951f48000c00112000941c0f1404c010344a041c10710129032a06160050b09c49589540800b1002d06209240c10001580d00820880c659041d907200d50480c800d040800403600001c2c08500310b44500940017803140088a1090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 698871007 1250 698869757 698869763
    0x222060f03030e33280210050c040f06120c051612030204090e01020304020f0301060f06180317030412030207020604050f130e030a02061506030402091504021602030d02070b0313150207 81
    0x54032240c0c88201008014903020068488500c001721a188181d8042178182101d590b001c2c00007610389400d0315803101c500450b004118450302ca0b030000b003055604410004110340040c07206200ca0314450000315090700601c0004a00104040345a20010f84480d03443c086209680c031700103041c00e41d261000c509688110300314019a960000500041d428400c1b12180c0402064000303020107840c05000c4d4091882d68840d00040007200442c0c40b032007207011030001000315001900101e4094900c04070041a51050b10102d402640304411118914001d000ba1500250000d089a09051400052002da40c86002a09030301c5100101400c207101503038400e00c404043d0160003142c80c1d204841001e45018005460f26a8040903d40c80702c3c2956544400c9070b40c041c2d41585c07407000584aa80e0001d21b0800c9495071a0741c0075002141d0141440c4925481e4581180203c08a92145402d950166190001405494803403c0c1c2000014045002c400e40407504510448603000e400d03560f05141000ca80181c8422 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 698872257 1250 698871007 698871109
    0x7020102091914010311030c0a170a0606020d0f08060d0201020a050a030e01090807080a060b2403160f021b1c0b150306160c0309030222060f03030e 65
    0x1030083c090407a242d0208030300c00307003020850034290f2260380100e800b0040600c018034100003203028000b0310801006920081803e04a941414550305820107002c05010b40c0d4018465035000c0900c0d24450344030404240c0c80790709c8283c40b50300e1740c5081c031400b8504107509034151f21034625402d00007842086080c440d54001d0b41d1b00038041d080a0300041c000100341c0d10220956100c414244591100071600010aaa01c0080090303071240c80c0000c101c01c0d100c0000c0c0c489100c1d0a075100103a0941c4460011442000d01300c9c0103036040e40c01410161008100d44100f500141c0c030421060079a00003660000f00003900041c05072005102900c6a407080c100a00c0301150280308190500448201c1d922005070304240c11800303402d00e860040740b000703560441c442c500f804016450a680e0245405010904042c40e00503101c025400c98890328461061109500c3d8094a8a0080c00251160b0707007034904c806595040d5207010007400380d80c040110b40c400c00300030408038038212400c900d000010015503544d11b88502c240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 698873507 1250 698872257 698872259
    0x60408091e1003050f0a1a1009050a090c020d03271b0b0904141b0319020c0a0c080105010b040b0c2805010e03030f0609040c08060c0c0f0304050a030b070201020919 72
    0x43e013400050043e0014009a080ca2054400d01c040ca003001ca07071f14181a540900d003100c41031b004a0308041240d22050b009402040d0100c0c2c0c3d251280c101c41d040fa02c80b034003201c0c009000014218100c0710401c071160081e808055259254900481c0d0050320b041c040d14600d000300110f08a4508054100e510180d05450000340811160600340503e00b2418400c0c05c940d0b24515010f0582041b0b1030440010343c62000001000030741040b0468040b0060010000003152600b00f264074440d034034200080c0c15142d40741d008000162194050050034141d90f89444103904003480d0242d10b0409400c114440c410501500000380c00a40c82d4500210403c1d64844c41c00c01c1c1510141402821181040c04400ea6a0800c00400520080301401641c02060941d20104569100d09002410350f000d500220310328003603041442018081600501900040792080d42c29101c061340c840b95482c0f00350300c29035070807010264080000c20b031554001640824640000b40c030b804032040c00141141040d0076240c05002e092a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 698874757 1250 698873507 698873521
    0x612030d0608060a0203010b0915040807030602121602030d02090406050d1a160e2b0c1d041e1a0717010603050415180c081509060408091e100305 64
    0x3416800008604d002c52555041080b40149441942600c3c3d008501ca9a9200c0c0e05904440484004003162400d641c02c5039220b01c0c00e0000b03544051120b25070b0b01c89000100c3d000840304404030f811440560025442d00c0884600701c03019420110381035511980d5040009600d84130745020307600440c0701d10303031000b6040c00b03c98818042c4e44025081107a011680f00e00d07a00490303088103001042c01021111380c00c0034898802c403d0450390301d82000101e070040d042125000c20001800b00c4041d50f0800d00004240b038440d102501024200311405465003000320040600c2660070062200610b000360032501303050b4405000d20b400c0c1c800c10fa030a01b0010707112010f20a180000300c101c1a000d04843c1c80c0610050800380c48410041040f040c0354038800d5079404181080d039403001d01d10180c03154440703840c003900c40d5215480b94071002902080c611000744000092a139800102d0380504c40c99101682508095500e030030300c041203d8400201c00b001401e0380c0010701c00c0e5143c03600034543d2a503d980100b140e1601d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 698876007 1250 698874757 698874763
    0x12040b15030616080f04170f0712090302010905120304170106030f1b150e1002070909060209030d030209010c06020c031b010203070207170a150b1503071403060d08030612030d0608 79
    0x7031990345c403120f0990034800000d00a842544854885144d03241c1c80e2003c000d0645c0b103504c50507000801c80303951030480780034080d0005410300c1101d00076224000825030318400d0101170044444100c2047e0400c000a00000042d041886105c080c404000110f0039201c5d81d684000460a900a651202c01202e14406820b804646480030b0002040d2031007014008d4103020300004086603030b00744502030300c3d54804c0d081403007084854014012040c06008940f43c5082510095005101c41d600078000d917031080c8540d034064000c803407074020182d440011440541d10380c03000a4010b92100055070004010241d000411405200c850160444c00160707241040301c0d019140042036802140004400484450000e201241d6030548640000e01c5041c40c410300b141e07240050031028942940301d141c04040100b92521000a1881400c00ea101c1209108016041e00c005003c00c64606a00010a240c8600010a07417005150002e034042d024071139107100510f80c14110741000c2c00413400c45031b4842041049103820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 698877257 1250 698876007 698876011
    0xe010b0d1802011e2a0201021e0a080703030212010905160206011406160210170a110f0a1709101a1c08040b0d0510080312040b1503061608 61
    0x1c0041107080045039001030114071040c002039001c080e094140c00310741402024817030f40580c1d0040e200d241d02c8501c129180c0900c1a0458140e0046c0f02e5280420401c4680100e00e80312061b00e500103000d0b040d03c5a94017145c65104541c200c00b096000d016103400081c1101401380603189000000c04c2c0c500d845180080b400300803616080c115407200004010140b9032291007807004c5403c0c1c40c0e40c3d90303d0040303a0001d9072401c0c07004402500500f012491000c5e880d44203c64003100002c0f00b41034803e6880d2030160605844046c500c940c41e0305810850400404242c500800c5590042d00381441d00b044500c410640e0810110f070701030066007105a110303141c900c041c07090741e00120f010540a0060b040d00750119a070309084424004101518100c0780c005c1c80100c20664009088032100c150f0340c3d01441e610030018203820307511b034080d0004171500824150804130580303482c030006907141d050642d03070390701c40c80307601203000e0000040e450f14004a920991401d200e1144202a0006c400c41c0795941d03500c0080c051000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 698878507 1250 698877257 698877281
    0x303070309092f1206100f0309111002010c020c18010504020937060c050312280203061c0203060f04110a09090b0a020c0706180e010b0d 60
    0x10449000000d4026020300196010000e0024080c030f01900d80c141d03552030344203008032800c80f088030345110146084014071919070f18098582c0151140d405102620a44480ca140400d6181e920528040c2c469486008054002e0100440201c02500820b86590200e000b02d40140d460700a4810703246e8040040403010b40c026508075618441c1e41800303e40001d81805061f11854000501010a44d929080701060143c42801490600042c00820019800341c9111f00704c0d480e00c4030000550640500f0440201540140145143c14410462141c070070100030070f07400c0480c086101c4004180d03032041980d0341405011000507501e080c048108032075800c2259090520001d545405801138501241c001e421011048000174151240c2ca4414924960740c05903542007004090001001104c5401c01854030740901c0c0c0307080786900c45180e4030050340716403002100d075588a200200a5640710365003103a1009659400c56005c6501c5148840b0f50700f070203a01441e5602c40204040d04541c085214030b4001030701d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 698879757 1250 698878507 698878513
    0x60e0a1a040309170a020d0c0305030a1707090311190b03011205250b0c0a020d1a0a150618050d0615060203090f010c14010e0607030c0503011d0402031e010605010e03 73
    0x103081e6058903600c1017078800c000d0142101201150400500601050185900006880c0c0300c84086030001c241c10002c00c401d45d071032a00c81002c14505405051100207503908000c0d409503c41200040c40091180050307100000c981c005400900c035000440134601812117a201050302d600d4034188623140440702c807034460081c000c00c6003814031491524580030440300011b45517611907089003c03040c03c18003665808dd400001c02d840c0307141002845840100c4080c01c410b440c840b03a4031560540c41c1200c0718005003010411a60300c00f0701c002e0f0302a081d14003102d0a41c801070b00007c2c5d203070000f2a045450400003101c00b1900c5103404600c2104480c04517000d022548021402c080030000059002c144a109850602c20406200010f00c207209018051000c1800b0090041c101c42184041d500e9008507640d00000c0d01e0104c211031110b1050341100e040f0f54024005455001402c6502c0d1100d0f81d0240003203074148242001c1c00305090419000c001150301c030030000030b20545410300140c000700030251068401c0e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 698881007 1250 698879757 698879789
    0x90a03060b1311030624040906090f020703090513092010050a021b04020c010207030f030b01090e01230d0b06011403071b030e060d05100e010b07060e0a1a040309 71
    0x10500007a130394042070407155074610b146091b040703045c1d00d420000b080d04100c000003000f080550039038002504640c06254104840320002140504034081c00300001d002036491403081156260190300c45000d240000400900c8450b140d07210440c0c0d4200000c000034121207100744001600d001c564952501480742400e44c94844003501c000c0d140d400201c140b0f80301030090010141c854444d541908d8080c42c4d10f0008650b01c401c1070401600e40850045000002403c040c4000c0095209503002002c9500070324200882c0c3c2d0920b0100ca00c00d00701f031034180e04c2e161050080044a5916480f02e40c011381e000d0a9100f45500b400000184815484100800d022030100240004503034080d8690140400401a200c038010261404891104685c800298410310106030091100f10b1580484d01800c1e0701e005444080750764904128183308240310f5020004001d104803404510160004049440c44400751007140c1d2507546e511020022121041004200c110204010141c014403080b01800204100c44600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 698882257 1250 698881007 698881031
    0x30201290a061b121b0317010b160f0f020411041502030a20100509340608131208160905030706050f0418090302070603050103020f040b0303090a03060b13 68
    0x100c02126402000515003640e6031940314440d59202c0b0402e1110707000748661754410700303009010000d001c9501011038407810001580e0b002203012125031a0102600e400341030543c0c2c072001b550303032041c0109445898a50700c818005070385900c6003011b598900900c07a901c990500f12200d000041181103001550320400c80172140715041140b8140041c1b4001d40110502843d00c0068146583c009108070510b08200922940040c0482d00b05195503448492075444d060390030804c0f10320f0038080f0901d040d0710703015403084c4030f02d0b4030902e00c0380e920080d0340304450014491590b481c04c107189214442e1001802001c14060700d42c2501518460021207485c1110216082c10300091f00d81c0c00030710545040c0080002d41c0e00f58920800c0c281c41c01001210602c011108850307108401414a10a003100107004004010902d41d010f03100311360503290060030304401801d4407400c0c0002021030806c02c9505100a01038910301d0359a2800034000ba61083c03102040c00d01070241400040d00b0507076410b002250a015080c034007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 698883507 1250 698882257 698882297
    0x3211014040b04050c0a0f180e22030203030121050d030b031905010c021e06070f170403090f090e151807030f0302060c04061b030201290a06 62
    0x80d280034861800311040e501001a0090001c001080c1d0424208810001c003400e40f40060200d081140c1c54111f03ca05840400f04e5214230078041c1652840d0803114103021107801c4289460b40f000074480304081c49011030310501c105501803c3c00f240141d20000050000451600e014040c0c107120740d844500c0c000c440d94429850300306440300c4070101030b50b5080386030b1507503020082d0210001d40c00700c071881301c0720950800078040c01c1505401ca025104800d140d9622200e026032022a114003c0068000398983c02800c4603c0c030f08003420001001a1050a011007202180c01140141c1c441c4d21070405c1e0918000701081841c502d540450310040c604a0842420840401ca402241048001d51202c07991340e080703154000580d0141500c1c15228070180841003200d004628120640660210b07100c035600c983d1001d01c50301c128021000003079031903040301c6c4542d8544040d02e8031041c800d00001c280d4000034020f2500c1900340046c6078140c90388500810041c0c1c1402810040a0701c2c40340307404620a071121b00c504103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 698884757 1250 698883507 698883509
    0x907050d020619030f0204080a1106030c0d0908040f061101060b0c0703110d050102191103130312030e0124120201090506160f1a0603280c0b0c032110 66
    0x6103d05600702441d021482640540b0140c1803440d0110340383c0ea15080c007250350300400d00c1c04440c040c0f520680a01e07146402c0c400c1c4c81c03084001c0303c0030f545407452100144001d40220017040314140000c1c000414450b0210fa110701c05403080355582005410001c0d1000d003910316660118200020030000e0b40b0100b24042002c0701503a42006048506071072110110b91483c07136501001c0d040d544042503003040740429181e0006140c10a41c0c1e0212041e04241c41c941d100d2203000550300c1040600c00e01000000c82562010301420458100000c5040c2989071160030740c2d40e160041103c5000400001c0188039241e4400c070003804d01004000c80100f115130018120800f140541403180c20042030091b4103d15004000349c02d80d0b441403c050115101c1e103010640440c04584440c845500c01000645501b0009005003c4030760f094882842d41c0a001d600321b103909054481038881109990303020494038003020080c01c1d82d8404200859480c880000f01d0807140d8080b11900e00019240800d0000c420307640c4000350 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 698886007 1250 698884757 698884777
    0x30411191703040b1803060f01210807060606080612010501030b012d03120801050306150603090f060108031b0d020a032604060501090501060c03021b0301150e0907050d0206 76
    0x54a001c180109980340d0700555000d4050144001041c4810303a03100c0c510754070a5603003901204c6036600d0f00c00003200c50240034000d48907501d07910208000004640c0c08038241c01070007110020724100260310f03140e00791145070308032902046444007400311038103088040c1040c403200c60000f0070140d4150b40d1034070036541040c030413000c46c98017080c488424a0042c501110b1030541ea110300c0d100071952450050030903c0e101c140800071801e0a0000242400c02280940c4181080449405a41561003c000d41354002506031400d41c452051488800c9404009103400b030000d260086858006600303515090460004081c2e009400400a40308d4480d000034000c8007060f4503040450000c04d4406090b049808081e1000c148031135444180410300c80651b0000f0f0680742c1810085c025aa243c40d801c1e0f80d461030800c401001039221058100154440e0b407034140103150018008075281c28204408a0b503800e15400101c0f841c5c0d101828840c40d02020003002c0c008100c03d5030381042c100d0454001558900500c8510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 698887257 1250 698886007 698886029
    0x6091d04110303160b010f1403032a0d05030103060c0c0302151e07081e130303020c0c0d0812060102160b0a020c1e011706060301150302070506070503041119 69
    0x1612082e5810b00c2070300c44110000d22104020403050070183c2c080403080c0b05402e14000c41490229a80022240c56400441c1c09002545001d80d0458455441c059505c07040c11501c3c1e501c4e1659081754402e00c4000d0805002e41c2e2003d86a5055080020807294140b644409100c0b0401102c000680c01107880c0300c48408843d140c445680d078100005446946c4a40c030740484801060801c0040ca8001c444240902c00c2c5861007442035040416040d5607600954202c080c1541508000e070001744a0780042103802100c0d410740d41110040d1700400c4c141201160101e60b4504041061051202d003000c0440e480542403004060501d441f04466090307001c030b8021050004000515101c0007030081040c0c0520050241c043c1d0b958a40c160103051072000c81403101800940c141550b07081050700204400d0007000c1c000d0001d0b1850346070005501007603850680c400141602808000003240d8140a09403180c01180c8802e035807481c013803514986864448802c40d1055030420503010120301c4440220007503400c0c860328 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 698888507 1250 698887257 698887283
    0x311060c0705151c090b1303050409020a090e04030305040218070c030e1c0b06030136031202030103110a05010503090a02060d1e0e0c03030304150f0209061306091d04 73
    0xa841e040b03102c4d145514141400b0065542e001074a07552140505070300801d0f09502c02e844002410a2040d10704030042c0009200340810300c1081c40c00c1e40200113041d801e00784034660b6039850078246411241150103070301003036030345c003c0209508005140780c010b8480307148603aa0398984480c010344480303220440501040020f284810640c2ca0340001c40c2030103117400c1004c000f25603040c80c000c610450100d60140c000c0d400c21045640310369440c0200308041485681e10240080b6108000e0068a0102d805408000d00403016640408243c80250701a600030b4402c5030200503000140210307011075901450402c00100f0400a6002c1701240311941c150f41258034956407580054080c0261100144482d0b00d2500c09003a000e41c500d9035808070b20f03c1c091203001d44020030343c00410103807230740001c44002d0035144c0700e903041c80030945250f070061a08150a900060804005c1408590503401031000d2182589244905020700707074115a202008100130080240c0c4213880c09062424040e02600080615181041d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 698889757 1250 698888507 698888539
    0xc031b02120a0b250c0b040501060e0907050103110405100e040e0102120603010b0319030827010903080c040609030b061804031d0a05150d1d070311060c0705 69
    0x580d01001c2121000c0300c58403201400e24850740c00060701d1110360011120b201c40e41d24452150400c9000d1082d8907944400c030616103506240c90402002200c0b19543c8060118040c00c1c2413202d14083d2401c0b200811b105800d010024045400c401e00d00241890144010402503951344801c800d12190351418100c50070101000c134010740400c0e498241c20394004100701706885180100c03140b04070002ca0003800a08008001e00d600d03400c1c0004844245009600c03484c022900a81d0000d40000410781d404c0c508250f41d1403104807003a290b00150351f081e516000c000c0e0616900c03d5041e0740142e5041b50035481c0c5490030304003400220f95844000e241442d02000070f4002c0d0380d4640704068040c2c5540744000d040c035041c07500902c00d02c14400e511121b8032140383c07104480e0402442c00340a885001d80340b03006030000071085030400d40010004040c82ca27190a50000c4627005110782c0400203007540c3c020030f4098118508001c000480d200c0c43c501640040c8104846207000092400407202c00355140c40d49070030005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 698891007 1250 698889757 698889769
    0x30105060c10060b1201050402163e01030e0f0607030908040e0a0203040c060507030210050430171015020325020a05031f0b06091207050102010c0c031b02 68
    0x71404050a4600700d000a40760100800401c00e44001007100140daa881f03404110490141d84c5558500500881d208000034400c81d90030020750101440000c2d2081ca080800070303442c0303a89032000c1c689134a1040300d20201d5805001d07110101c005e48001c0d0014045001200742d6489004040c4c104040d00da0215000f40141c00086a0250004040c0c1d0340e541e2130183d20b000041e50054400310b85c90b5103590b1000404520443c182d41c405a45680a81107100044840700d002d0600500180c81150341c040c6c4903c9071a440d04015501d2042e45c0c0c0350441895006076002e0324a2401a41d81040282c4000801200740051aa1142501c0c207008048040b9400100b0484c9035001c1c04d8020041e403020820203200a8849040d032000181c400c032402c008103600e0340300b40364450072503603130085581c50140492001c051140c6c0201101d100041d0019092801c110000382040301e44010f205140d0b0000f4074144402e59080c05680c217900c9031414034459041301982c0040c000c001011101050900e003d2505085648003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 698892257 1250 698891007 698891023
    0x105030604061a0703020d02030a0f03050a11030702010e2107020436120c021f02010216080c0d0e090c0307210213171506060d24050a0b030105060c 65
    0x42c8250f452800444080a2060340c00000185c001d8031512141a0030644000101d03403903515a40e40c0d05074034540c8000f064015200142003155041d45424420740c140c40103501451145070140d0021030149141141c0c24103050115000c40407010040140b0706e50070110100300d07100258183d400181c582c4481c040c407a07450b110384002d02d4030075145154890341e078980318900b542d80701c0c0034412089600750801c0040d61501d201d0b002c000d41018410002c422503d0700e080d0801c1b8807040e18000940307050341010b01040240c2c03094000f11001100411500e8260030200300100800300b1030300b00310100ba882000061001d40b0010300911145a00000280441d80f0851259008500214081e103038030560211800180d04280a82d0040340c652800009070801c40d580d040f103112024401074000244d05492008031030100401450700314070100288a030b842c082d031081840306a81094454031002c48501c0010601c6010340c40a40700f5502141c06004505003141180c2c1164002c030340180d41d51082c070080b181441c00d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 698893507 1250 698892257 698892269
    0x203070b130c080703060e060f01050d060e070b0d05010e010501020c0d110613090b030d0e0f06070b010801050405071e151803031d040e06040308071701031a0708060906010503060406 80
    0x4140000c07140b0000954801383c82c89440288a18020207454607611312041740d9209c07031801ca11313004010380d0400c0c100c0c0d800c100d8015880030171607400c86101586011880d41c400d02d580314000500884004131842554094020700138800c00d44d500d030400003540e075004d902000c3c0c0314201e0040924100f040c4d0042441c0d45580c0a0072080c0c89005003845e9a21040d4144106c51049003004c0020000340b0300812a01035660254891001c150140760a008402c2c1000c040b00f070b00030314108070410104020f082042c5c000c041c1000007082502c0c0502d407481c245a12944400c0c441d01d0305980c00346150811007207035401d0f00c80e18180c525070781080c00411902d1b5482140454141610000040f013072550100006680c0526641507030384008000c4107000841d0000079426566401820200300020300c41c560791500044503191040b00e460707070212b10307890030038003a441200d00c15080b02004010700f00c4040040d50200041c1000b1140e45413001c040b032050382e001044241000b000100052603a5515440395001e040c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 698894757 1250 698893507 698893523
    0x5010306020310060309170f040909050a061104140603060402120a0b0f0a06052502060f0a170c070b040503190e09090304260a1203090b160203070b13 66
    0x19490030850000d51003600d1408642d6070701c81010038007a003e80501000182d10000c444118008821081800e0300481c0001200d0482000000303582c1c012801940341c02802034000c0d0440f10300c44c2c03503d4000c650008035914a1a803061104220703100c8905840f141c202d00c15111143c1d2690303034100090003445401c955180c55010b00c024405400900e9112500d800003d465070402020305404005058005d4403d03080094000c2042c00c0403000003004041050300b40707000e094400c3c1d991b41e000400c60b0b0000416004644c1d4003017900ea203c19031042e1481d003000581c01011000e03003080103416060340701d044400740004995801040c2040380400451300c001503062a104030804016000800b14420409190b118014100214a2100001c803c4800f1540c0c0c40c85040000324078000b4035604080040c0c0880c0040c0190b20030075011540801201c0f00c45a081e035400208a6000d1500b14041c6102403d546800008681c0d50340742990000100c0361100d07003040c11a5040d94131000f165001084054000700260 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 698896007 1250 698894757 698894759
    0x3010f060f090b010c0b0f15120a1e08030403020312010920030702070f080d2a030804030203070813080d09030309140d0609050c090a291305070f0e040e0709021c0501 73
    0x401e40d00c007424050202c4201d60044152014100b01004003103009c0907895400c4291104006030610001c000e0400708000d00b000b100420b500d948100c0c0d0421203040e400342c1c10001c0c0c6020300600898115000d404041010845451024944861100010010401000f000011500e050f000704030070b200070246403090030301c0c480c2c40340d08030b0340c5802c0218200004a1903428102443c2050f0310030f420103070702403804401804807140e00c007150b080602900c190f0542c001080b02d400400c02410080484504682e85440f403070740380941c554681840414440104010114240000307940844200c0032540c030b805412048440c0600000c000510a410003844903140401803010450040f0704403802600440c0c410540717581d0016a1420b44d070403001050601c2d4424001150013240046101d0010600a00b100d05400c400c4e03004101150740550300c1c000411607540036034240c107620000340c0b49100c5064400303001c03641840f90b0f000d627038036220b000741d01c2e110ba000f14020700d03100c0600040c212001a40f83c0180055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 698897257 1250 698896007 698896021
    0x20c060c0d0c0e13020304020d0f03090f060203030412110c0d06090218040503070b0a0f180b090703030909020a0201110a080a0b060304150b010203090d1103010f060f090b010c0b 78
    0x1e612240740d10070440e041c102106003240c040d41d4030b074114090280c281012650068000700c02540002e00480e4441e0f800c14079080400c2c505c0b0842c442551094603842511810800c0900310790201c2d82c84842194030820070040041c0307455100108981090402c022100e02c08890369080680d0103801c142c1041c580f01c0d0030014042540c200c4005503000b0f4488540c007207600d03200c02e030341524116070161156104000c0c0a00203040c40b410103511800e081c030001070220350202c050741613887d03541112500d0030745186240d091020341c0c103480d80c2081e1a000182042d5185a40290060420380314550b011940800c130888998000e4012103c444600300702c1d141d80d44192140074100c00801c0c0c0f10402e001e441c00c04140760908003041103078011608a1440c0b045032261039246005407143d4611941140003e00c110142030704d0b00c0c051010918881c0c03200d0710b02c18002100f45400c50702d1120890202e10f044c0201000800700024860302520b03541080400c1c1d6803000f00c010b035807030720f41d0f40b50045c003c070302da03800f00544 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 698898507 1250 698897257 698897281
    0x2010c33051006090b030c04050a030b04032705120c03070305070e070c0b0a0b152d04120212011e050103110114220b070605091908030a050901020c06 66
    0x140800361a040007652588000315003000800d0040101180c181c00d000e1001c840b030388000c0d40d880801036111616094544000c80d10039001540210f4683d0004c205101c105500a40c0580340d104004400d643d081c200802e500c1204000c034801c50340200c0070840d00400503e0180000c41032104080e0031640412ba4a1030550b541e40300c144640000d409aa10204100350f200380c48400c00150084507100c09604d860071034600400d900c0050710341c00390142200070400924031000c0d101070140f2140c0001c00400c44409407445004044a00964200400c01407040e0780310f003005946055010b861060f00c141480c4400c80c01054010b00c10300500d4200440e1522991035a00243e0580340f007683e4203849480c5a00066030311460340070110b5400e0500348284441080c001207107074400c10740700403d998050fa071070400700d065502150099030080c4d2608100aa840c1040055805113034a80508100603c2e9a48030b0b004c607400045c1c01100b1003910382c4046640840250103035140321940c1d505941290a0003c50545 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698899757 1250 698898507 698898593
    0x170c0d1e090f1b080703080307050c01060b04080c011106010e0c1201090606090602030c21130308030103020a1706010501051305040507090305010f1104120c0f090e060a0605010c02010c 81
    0x40964103418141a45036428001e0300844600c04c0c000c0c00e00500f995181082a00000c01200401506005001d01c180090041c1c0000f07013001c40742d0a641e80c0c00c00b04110704210007012401c1c180000100c43c3d05141100142503811291140203c80c5143c40b00030b5103011038814204240c540505a60022845044952040080383d4090b114050907503907072401070ba100d001e10040400d59401c0b5540f00e80207a54950380c40102429011540d9181c003511001045807041c6030741090b140c1d24800700041c011403c0040c040400350003404103056600c0b00d56105580e4460381401800d04000010844030242e11261503c44064000108140402c8c506540300504d607030301e03612056038550b0138820100858100351095149007000441101d00d0241403140042c0302c001d10800c12600180b846d00c2c0000d00303c145103804406090311034000320703503814888200c0d0324200010303040d0200a8070708030003000b8a03a000103000d801e41c0c2d820b080c1100300741c0d001d040c14500403440c010b04600b452107041084402c03101c4055110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698901007 1250 698899757 698899763
    0x290108010501030e032208010e010209030c030f100209010c120c06050a02130b070c0f18061a1b0f12071b0f182406170c0d1e090f 57
    0x9209a80ea04011019200298202800c0e03410403c03101349445080c0744020038200e964a04114104e0380d0385034450840c6d407050070302d540596000c0707850f0003240303810300c405900b841045000700701e084c143d401d60948a001c0e14003002c0b62a0340c00203440b101640500c1204c240c85801003010701424800c200041c0440c0c40070b000c116100c0f0f1030580062900301e5684213a03682030040441c00d1b841c40d418040c091072580d00c414020340d0000c03010680011503410034070f19003010f80840c5091828843d16181090143c2c1c449422212030760a030b40300c0d4440803804802c1521201c1405540c85003440c00d21a02150a0100b00a43c1800300c1c0038a403d148600039040300100407041c4500610785082c0d40c894100c417030900c120b00581d14180f010450411966408a80020620201e4031000940d61803080c6407169404020f03110400102d1861030800511740c05c2020959504009007910307045207041070818000d031040320360f4001a2a03590390181c82000044082a500f0003c61f1000c0001c4d4440f428500c000c008050303022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698902257 1250 698901007 698901017
    0x50f10050a120618051e012106050403180e1b0723011d010504020a151e020d0809030313031209021801050f0a080d030902041b08010602100903021b042901 68
    0x852840d0f8000036200903502070304980ca001c0c07a401c25200e02142078000305440c5404820030322300c5003c0340d001e01c12240554484d80741d80010240c03a190244245805078880b010703c004d05d404000d60680700d1100010104081400c8076a44c200a203003240340c0c1d81c2090314110f11b948045d80c0c1e03100c4650307056001e485984803a501c0701001080000c031080c203944044a0081d0011240d82e0100701e583c410700710194030054141841d000c54a104180448401c036010708100c0107a00c112440840e80f1342080c565600b2100401c050752440c0b030100810181021203ca00900704140e01800c1001d0000310740c40980342690040c005220390035205c00e1025081002e0140b684641c1f14422f817030b03070745140040c20310007103680c0d00c0c02a1841143c220780c10350007080d10b0001a1780058030b581c02c0d60b046015550403800c41d514182c8a80650b54103105000349071400341c64501c40d005141003480e20200e500014000540c98041c00e03043c1182c8144004a0054440e4126594043c1c0450000300d8441e856030381c120044a400b0390311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698903507 1250 698902257 698902261
    0x100302100c0609232b030204051008160503010303080708270309040b040506010206130507050607141c051e19091e060e060a03090b090c0a050f10050a12061805 70
    0x30304e92220b40700780b80c24041c3c080303005484c80181d040003010b0544800c1401c00500b00b40d5241e004c02c01c0130716600303400d1000a503103c00700040b02c94901c4e044000040c9a2501d281507604503074000d400c3c1a4003070075840a004021000521101840298820b016840c480c002e03810707414420f10b156a038000030f845901c91804d1001504140c180b074800c0c01e224410590042815480d00310b54040302c400b10643c1a0b8090088200c00305e000d803a200018001280b0906040d80c80703180c41042c050521642014074031076a13100c00d02c40020280e011094460355115242c00c41d254008006922000d40724400c4880c000200f2403040c001ca032074000714440100c4051140082e021b922000388840700400c0340c0502008290050012000c0f800c00c080641100903060800052280054030341a0042d50110303200b0b103550703003f01d007088101e0078003c0907000244400c1d10014a941c00000004482e03a084101407010040d01060041845105155482511001d900104403007921404a402402c0085035852489400d00340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698904757 1250 698903507 698903573
    0xc1f1a030109051c020304080a0b1f03020a0b0f09091e09070509010308300a0b06180402032a180f0307140307091407080c03100302100c0609 62
    0x3115040ba40c4a00600032409048808822803a0920520000c51000340800719450b2010054480310501a610601c201e1600143d03c113411032440d400000741480140042005071140340609064500c1d401c8280d4450346440c86a2550f40240c0914990048022041c000325912414103550804013207802d00841e41c1e5501c00f110b540b501c15202e49500315401d1801080824900c40c060700ca08c20b0030140f20780c41c240888240301207240914140c28440c01500090110900c510721600340d045109481d000e040c20400841c5140025481c00c0150140f0380001c0040c014a0283c1c002d640050540c41070810000102081c01c041d0750001c0000a03c01c89051800041078900805c140040103030040003040c0580c10441101a140c2c8500d080c550584500000030600150b58002c00341c0d4039550702c0c03601c13682e460203140003001c90001400d4241040b001300180400461040c4810f42600d0301610b030b1254210a210302100c01800004000d400c0c145083c03402c10420942000c490183c00002c60300840040d0307816 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698906007 1250 698904757 698904761
    0x90b060a0602060c03100801021c0e0a030504030b150d03020307120c02091323010f0c0c2f04020f03090c10171f18050a0207080304080c1f1a0301 64
    0x1004a00c05680080d0005482c0c0070500011742e0b1080401618011103591840420b00713981041c0410000c1400c0e5080c08441061a03218808003000c00c40014100e0034950744014004d8030490002900d03c0c1843e00000300c5075900d0b248a441281d84c050808d40320f56002d41802922608102400c8aa030915441204402e51090440c50280da400405071b100948960341c6410b40c04100b04070860701140c1e480d680400b010904076403e4000e2540100100303003d078800494030111440c0096860500800640301c3c40891405c0450707510504500d40b11601d041000e08410f40086d520082055010340001291441101e07035002070340c010039a05040766141045038007017000c040080074444000a600d2800d10b450011091203040e0070882d0225904900c0c0441c1c000b80300d511049400100000c00080e60002036580c141c46141c1d40312a01140c11410b20403665509a640d202c0588060292100810394030303000b50041c0300202d402401c204d03201071603006141c03002d406020700c100344030700982950220f40c4c2ca0741418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698907257 1250 698906007 698906009
    0x3050121024207020a0e1504060602030405090c19120204230306070c03020d2a03020109120309020a060c02060d0501030c14010c08030126060408090901051c0809040f0f090b060a 78
    0x1005c0701c1c0d6250401203203007a01c610041c4169030050b102c41c901324843e203541c41400e02600c0c165019558440c1010140b020b04000035040c0302e19400104115a040311030f040945e4409502440c05624902c1c1080311030f400b83c0126002031129032440340c94514048400b507080c0d04100416030956150790380740310091300e402114007400b4001d83c0105101c0e1115621844981d55044400a4030850382048510056651050040308402507903403144104240040441c454000305d43c00d250500c14403d460717012690712919807044409000300d6042400442d5254025180080c1110701c04100300d43c0d40b800c003144078a81c903224580c4001d0b142008158154420000c4014194025914529592034500c0726030000a1040c00c004041f20850100034102c0c0c81441a14040c6002e52211078a0711031940c10400440d0061340810311500781d902407074140400c1040d10401d5290065103081c1c99402c0b1320040b03030140504074042c212a9181030001070f29501c2076030010f0f100c00c0c0510f1210100359903080a02281c0703001d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698908507 1250 698907257 698907259
    0x2c06040e013f080c15090a0c0f140907030b03010510061412040f0201030603050f010b0109050906091b0c15090105061c06090609300305012102420702 66
    0xb522511030040b5000c58010310999001c241111000391020032140e40c407010544407070f40c0a8119168807024840d500c0b0403030000d0081c50030b902d000c50340791107408402c0300c1303482501c58011302101c3c0004140c01d0281c0d12400010700c016000340101c1c50496032012850506018440115040116200c0d074425a90300361f81030107a16222144041e12242ca03288102c00c40c02100f01e0400d512418088001901404203030001000c1900120300780f107139130300050010b0b10300f03810a50086002d001008150f030b880341e0001c0c0d00030b000c90403a000200440c00380d81c112440b130045020f54500c00d0003d01100c03994103140080c41180200e000300035640b2080708004c107908104c0d002e20407600070400d4003004220300340e21014456118030700000e40e800007030b501c04031110348804000315200000000a40c0000c0c607003469a0154615150030802c660401e40c89040024005110010002c1460503180c11501d6182001003449502407200c10080070300510b402040080d8950780e035946484c6040c05642404032804d445541e58 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698909757 1250 698908507 698908619
    0x30706031a04110f040b030a050f0705070312060b0318100203131b090f0905010e0114150f0603090309010908030a050307080a0f0504080315012c06040e01 68
    0x101c00402016215072495080300302c1d41041101c000c000c1c1500144002d04445061a45910300302003610121800140b1000d5814005000c01107100c0d40007049810103a07241c1040300c82c000c84121590018612038106e000c0f4a4000030034094041100e002580d01c038400d800031510204990f88522090340030540d5410701114407134441d10f00080b982400c0d180b07201680e0344442c900a0341c41c140c4800781c1f015203801c510016601c80401c014441c0c207008100100b0b1003c0001c1c410f80761102690710104000130501c0c0e0781040c8071549190259241801400b82c14002411305031a810315800036502d941c0f00030480c601061038504d001420540100a0b569555001c0d11503904541c0c80080070798840c00010901120b040d642c9144d07038100321041c0318440c0180c1c0101d12590300d070b1820110725401e04ca800c140130340c1840b840300c210020b410784900f840d02620a0302d14540c0c208444080c0460030f113003e0341d00545640c0c0c0c400800455001d9200d6a0300a40000c4803248035884840d1441e1044104414962116008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698911007 1250 698909757 698909801
    0x7200d39080705120703050d060605120f0c0706050c0909010e07080106051c140103060501060309150e1504200108160c050309190311040c0507060e0118080903070603 73
    0x110150701814a0b10701810607031311148101038031610a03a1250104802007000031036854441c041502c101030203401d01b4242280303014026642145a0940204184203038149400044c43d460102c400b502c90143d070040d010300050504888100d41030308460f6a05000c0c10105000252020359084c002d8000d4205131141090342c1d092030401ca51a50103c0164014024603071507a03c2020b07142c0c0301c0c0b040075507040703941030416504614200c4c0c1941c0045c1d1003041010b00700078003070011845241ca0310114200c81d1134000f80440d91728111500300014420504450480007040000b444160148000c800110281180154422400550701400d041d5a1106040441e041c1c4544580c094a41200e8460103181280c0c10500100002030b00d43d810280c101c611400011010820014645034009503d00101c500340800c0c29a0303038004102d8050b101e4041d2000d03031106001e06144400303501080494000754400e13031900241e42400c02c2c45a002002180c0244a0044002640307840f0348101c02d030204a020001d040340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698912257 1250 698911007 698911013
    0xc0d0206061f17010305031c0501060e060c0c180406111602122506080a0e0a0b040c0b040f05010806010206060102210c03031006090e040b07200d39 65
    0x1102e204400400d020180b040c5032003940c8960001070007148584025076481c0d42d50f00d541e661051300950b100e0001803c040060146680007000c4150484090301d10644900140810702c0c5010f0300d08142d103030080351602c40c000c052004040003030322841c05040e00b401012907031201c8006504c542c440e080340428070a40081c006140003c000500010200c0484847c0390381ca0001d0311b18051040003042c4024030900c07041140310381144443d64401e001040c2048282c151b4030031161215142100100b540c80c80c0d100140c10000005c0000014100208000380c5903a1980c01c840c440c100103010b4a8041880c180009d6469031001a11500c121010380c041c0c2015040010200100d5800b8041c00c881210300740046103519804001442c811521030701d00001d00d616150740a806049203401c84060070b06d00404110208440f19990754001c00103240c4410300303403440108104060001d24140059005170030001030f009502506031843c00401d40c1d000710300c2c2021010010000318443d81a09030780c0c0060034200000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698913507 1250 698912257 698912299
    0x8091207032904140307140f0706020a0b04080a02031b0705040501090504020f011223070807020303010803030601081003060e0c04060b04030302100506010e09040308071d0310150f03080c0d020606 86
    0x2c113043c40c10880b400c0000c1c035940d1640305010140301071a0307a4803c00900043d481c1c00c02270b05004151500203400f00c3c0c60b091305c400c1c002070801030000d032400c01c0c0042d0070210306108004aa00d4141c0321141440c1962304004800d48400c01c6200d4036102c2c504103400407580c1c40c2d2501c41c07603000381d42c000c12520501d6041e100640c1e08950480f4040e08542d1394000060b03c0c50044103024406058100c0100300e0b601c0c03c010b011b0070740348001e4a0b050856000f400180514400002120b0f000182400e25907080c0e0740390900704000740819000102031608007019842502c0300083c034500f440204039018406643c1320000f208440c0603904c4041e006070f0104d80400c1300b406c65a44610b40201041c5840c2d500500d204002c1400e8100c2594101e0000d01030000308401c099201140c5900620349144811600004100196840c103110710401c907150382c0e40e01811540303500540508002c01140d9a94480c4650701e06002940c0e070000e9108060707601401c518607405c1480031441e81d104540007408405203020f84c10300100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698914757 1250 698913507 698913533
    0x506040b18030a12060b040e0604140702071202030309041a01090621020322030804210c030806040e120a0e04050708070503180a060c1704020f0d08091207032904 71
    0x40e982d1780315408164101c00300d000380090258608071002a007025001e01c0b040715001426074074503040c4501440b61681d80454034100b240c030794080b030411925035800000d046201300144a9885407a02024150100c2440141044458240c0714000701c0750b9914011b988065148140350850346451401c3d14035900d06030b000d03642110380c1000200a11010410029181d0b8000b0010340109100e103042100f0462500d400e50300349402c4030382c1491030302035510018010300481c01c00241440400c40024416498a52100141d45150012603410844859900c3c215a12200c600c10002703000404400c01401c050007464040c0201e540d44c0a015552644210303003540028007006000c030444a41c1081e0b9150401c9034500c0d0038060840021b075030040036009015110035501c204c0a40060000304009a5960740d04400c02c450161303682e501c0d881551030004120b2003218403841d401021907014403112000001c1c4a020369110348045840a00d50105030b6a00408035020b468002083d0400075000505840400b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698916007 1250 698914757 698914787
    0xd0c02010b030109050a0c091a04020318011a0a0f0f050607020a0f0618080a05060604050901020d1b081f0b090a08010c030905060c0408031b0c0a030506040b18030a 72
    0x1590094074000a801e44182d000180c80c5035016004000500c000040c500d4010301640f00c0801500c4002c45648464003492030f962403180740d01100240c0041000b03982c104a004d0800000c010b00300c10440507100014004201c2800342c814113070f0205059400b2100001510b502c81c90403a595441c0408200c495070100d24203e80005d081000003c0c00b000c550100b13400b41400303846a4030015a0718030195020034059112403080c0e803210321814085900441c20540210044c0c1d00426540e83e001d90007800ba04c01c1c4034207240c10307500c0d15004110b8805c01140101480c1c1065403140056281c1204508000841910300c041040082400300207810414005180b10781018043c4040e090395000040e0031a1118006c080c0402c2e155040c0c1802c01c002031000a80c00300e28150340600307150502c040607507680600719035040c0b021242c000b010205181000190f110501c006c1c008220309403a4585648c69074000c1d00c0440c0d044400c1400714200041403038004000c80003410046040c00c1c16642d0407a0740c00b600c58101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698917257 1250 698916007 698916011
    0x90206120618070e040f110a0e150a110c0a0e01060c030210021b0c060a020a03080a09020306042901050609130b0a170c030a030806130e100902040e0f030d0c0201 71
    0x1642d0038000900040c810a070302d844200e81d035590351040c00705a80104004030035803450000b0400c071604000060710725203c12441d0004101c040c607008a1030703180055481001020002ca4002546a80241e1960b2002c20031015100341458000900400200b1030241c00d01c1012035a0060044610407400420742c54001e204a907000304141200c00e040386d2040c001302d401e41d00316400b00c4103840400c104810388484192582454402c03014402501c0f40881c3ca0000c08000080b03000c03880e03a035290b41008080340d800505558103070500b440c11140314122681c003c01c03403034090f80030309080001000b01241251000340005141a10b40010801520300c62a14440c0069643c0502c0c10307152511403150001e440907541d00c82c2c6100507820503518000c5050240340c0719901100c04440000d5000c4800341c2c0025056071824100100182c100c0003902444007021860320981d65540d81c242c801d41c000c890058003e031006c10210041e00640c6880301000c080c40d5034103520404c507035040c9041540c0b01c108a20694400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698918507 1250 698917257 698917279
    0xe09061b0f0301030c032102030306040c09031a0612010c0504050906042a1706150f0c030328230703090c08030316020303070c0b28060e0a0902061206 66
    0x40381070707a00280c00985000055410600c20812002e01c490420044260040b04202d00060b0095481c0f10040c15030303000304d480b10440c6c40d0550052151801440e03000b101a03601e6411541e003141d00381c2e0203c55203840f4548940e8040511070040c0f00e0100b04403150b580b0946041e0800d0240000700002400e000e03045540ca0303482170414014050a00e20314865040e07544010007180d00000e00340c1071010b0344816500040c2c0284407083d92018440e88072034030040802521081180d20200e1240a10b1811048c84d020010410040d090022030803818000b03d4083d45107068107803045101201ea24812a002c01c04a00215403103c412104010f54000414540802c00001c0b41d600d18103000415400100660b1000c400e10504900070383c0d034211036030901c1c401142940b4043c00010138020b9007071400750002c1e100c50702181086410665a0003e02c1442100251804402401d01d0041c191485000001c03841000460b03e103c400380100b00205800420003424814246940302c1007010140c4940da02c80702c10f0768 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698919757 1250 698918507 698918527
    0x30403020628020f12090108060918071403100209010215060a2c180703140c0907050a0201060801020901050d2c030a09080c060706051902130f0e09061b 67
    0x1002e061001c00e03a601074100107003010700e40740c901806502040145030003131021110300e07607000018079488082181d110019445071a0007201c480109400d0429900403a840030942000c400d050b03d042c96000d0b000c03200240c0c60124168100c3c041d01011a0060700000300c13a030194011b40354115003000c0700a00308080c040d80c83c20400340d82d044c0c904036084001c4840718140e181d5080c0498155026103200500101ca0b8046401742d61a20100d0200401d400d01414080150305420081700a1042028001200ea810302910180c03241e0020202c000c015802e045001c2030248060003a695402e4042c2c40d02410800b400840c07401500c1c40c2c1c030000050341401c3c030f8a8100c0070414500c03861072000e4440690341d12140e860000301440340170b80058503aa4404400c1c40d1082e1140c9c4c080385c4845421070b80000b125110f4900000340da840d5500c030b4042885c00031030b45640c01015003840c02c0840d01c0e81400038000994452215041d2a0221111032040e0000c80000b500b001c2c5143d441c40450400035411450080190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698920863 1106 698919757 698919817
    0x9100314010212010e010e09010c09091107050105010603090b070905060f0309010e101505011103040303030902060d1a0a08010b0a03033e01050c0703020304030206 72
    0xe040c00c0d91002941a102d0072950080030744815651038403ca030081c2000c1c011000c6c01e505e860301041c0545030501c54500464581c0c1c4914071650b10304462540240098112152101e20400c459800240c0030701c2000c0c06002e42c0d40700000c0f003085506200748540d80c001e1412041c04190385041c000359a840e01a03540d00460708016554035540c43c0030950161521425800891040591869455911760000c00401041c0c040101c41e042d0350fa4011150843d19501c0020190070070030080c0007203842900704512190018180c13524140741016100c08640600041c05503811600b40310707882074584a1300b850005c1003100c009010744050500020020074041c03100406102d01c01508090420300d8450000d41c1010551030040f01d4407030201c070103030300080340c61200c81c0651a0500089840f0001c00580c1c5005030140c0c0154109030942d070911100b0303030104c00f0308204070140e9281702205001c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 698741007 698920863 := by
  have h0 := BRFrame.cov_init 698741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698741007 ≤ n) (h2 : n < 698920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
