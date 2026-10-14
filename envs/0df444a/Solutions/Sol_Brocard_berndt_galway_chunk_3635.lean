-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3635
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:14:47.528977+00:00
-- url     : https://prove2.me/submissions/c2bba0ef-ed93-4215-8e06-f015d236d644

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653597122 ≤ n < 653776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653598372 1250 653597122 653597129
    0x5031e12090c090108030724021c0c1701080a08090a0305030a0503100608100e090c040509010923060601051c051603270f060e0a050c0108150f040b030f0304 69
    0xc2c030400303802c1000c00c01c4401060744070201e190410042c1d500498110f091515800d0f2401c1d1501111341c04012101000f80310f00c1a0b01560314420341d19901c1900c00a0b04080400c0b1125551a426501c41c4002c80254500070311038581c080e844110050700082c4000083c003c80c4070b00070907120009640e51205403c650080da00c103c0020800001c203d1200400d4070b000c40a0001c51426801c0f034500005a0940302c2e0160003070b044070405160009084003003c1002e405403c20250050081d420040030310ba000e041200c0f0103c6e00700d03880541580c03805030660030000000c00c0480080100b6125140190341ca50300000b03100310041203800e04510000c52a00800303001d01040c02059013500030b8840001c085a00810401904e94025070b0410a800c3c0a20008030903113800054091000301c5c0f9103450307002000d0031014502107000e01c865190601c030b03001c200b1410040c400c2e200e50b6555640e512030501090544584250710200d1180c031086c09080c81c0d40300f90202c40c070240403180114036044402d45903400961 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653599622 1250 653598372 653598391
    0x90c05100215010f0602150a0f091407061e0c0215040315271b3602042102150309010c09050f06030f040f060c0507030e09010305031e12 60
    0x98074030320620070202c0b0090042c150300908140150030090020f444a2050b10f400c100540190302040c103200c0c02d84c0c0031040d0000141003c1248607441d02c1c03e0114405807401c01200b5026103c00018114064462100759a058046e0a03405d40c41d015415100e0a1500742c040e038101c90b40c4028210491858802040a1805141605181c0641c00381c00410ba94801c6a074417081401f4590098031901c400c844110040e5209001110f440d51003941c16400c1141544505c00c0c101403491400040441b00c510361402c0d03c0704c12901050301000d081100c090b485503104803811134401036401a0020580c80f000c0d08a00c1c40203049540780d440440c80a5031581040e15058000c0e595103078a49902c5070002947c40081c14203644410724904484002a420b000003440c60740269008030020b0300300152a00c969252941c0a2000c00400031040402007036504500f00460118203001107515081c606500c526040b030394850000c0d4a09260a14026500c2c0f030101d00c40c0078050018030494004e8183d8213501c03845110b110f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653600872 1250 653599622 653599633
    0x7140a0e07050c1e0c010e060a030209030a020406031a0c1603030e010b03070e0106110f06060103051902070305031b090a14010c020315040c1514070804122004060b0d090c051002 78
    0x14640217003400030030350395241440140e061124070384e2101001e65407100c1182c01c0044e00c1c0c4d0200380204e420014140c20086d8007910304000882000241c1d182c0125509100010305102d0fa55421901c825119409442e0b0404030765800b0100081e02c01d80056244100400010a442d40d010011031300c1d10070581c203c0350740c00000c20014410b0300d501001c501c08010b0000001c0807001408a2081d8450b10043d03c0d00e8100754568001415030f80310011100c0e00610480401c558a40f6142402421130304162410035140d04002d1501106d40030b00010b450a0600050a040005192042c0c01510702005034090341813020403400e05001d680c0910001803660b011107d00c1c4164645032802000141e2190443c46104d04621420030070700d9400032810707000045000340c5030b5a440b030f43e060500260085501a80d443c05510b0f440000300000088519094003c61030300b200903c600c0000c03c020b03982140502c2020701020702429800340c80d1900a034001901442900f01038540f940c000c250081d0303200c0e00000159000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653602122 1250 653600872 653600923
    0x20c042c0a051c0801050418080a050d0b06070209130618060605040e0721020a1503021e03070e0d0c08120703020c19120512041707140a0e07050c 64
    0x40c40043ca2018504031a005014200c80e0b01900400041c022540104c0d0750f45140302c3c00540350f144480700e0302e4002c0100d41c1c581c494220000c0c0b0790f6004681000c415414400c0043c2d580c02c1074815900020b034014481085136544031100c40003841803000590b04a80c035a014640c513010030525501416005032030102d042801c100a00050324003001e610f008070381c4100380801124451081c0c185050300c1d00c1c05186284040c500015848100c1c40d00030000d07058241d66040da0094055009204482402284509000e240e091913841c81c002210040c012400a28202c0c18a10b4007a04014045114079071403503403076894015641c03070700141700e0a04a1580000400409154040003c0c42d1203400480300d8800d0400e0b144001d1010f41074610441c0f40c50626000303000208101030040b0f000542140aa02c1e40340ca40d00d100d000315001040131180ea03036010b1404082103448542148c0600000041c1400c2e504a01c2c125200040c030b8401403011082020034801c035030400f0024440c0f1140f00c202e03500c031528003482 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653603372 1250 653602122 653602133
    0x6060905040b060702030d14070605070c03081605190c15020306090a110702040209030c0301050c04180b0603150117010306020d0c08161101140117060603030406020c042c0a 76
    0x1102400750f40300324818040b81005035000180c40c1c4e070381e404910b0701082e066849081840c60b0f000c0c40078000c007220700342801c01c00780760348c041040e148150203545c440f601a15000314411004001012010000745c04004461180700e1002c4500d1205802d4a45188070440c06e4840549001c80b40c00003060160f0000306020582c680038141c95004200604100080d103100040f800d643e1041940090041c0d80108460792255000d0115408506014000740501c0ca000d00c070800107544030740160001190541c0780c41500070102e1042c07000103030000c1c264030324503192449800455010300d48010b0402111102000200c80d100300514020362203010003607241c10725501d09000743e8940b00800010011808200000c2c3c181031280f0404a1145040003048c2c02008403200c0d001d4580380d5105088441f03a00b00020380000044000f0021101044c00d03148107445110415031240702d2846030000592103580c2e40d2000745800d512403c2c0300025010705201c004032b1031425454014041c6903101c450b4004174502014050f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653604622 1250 653603372 653603381
    0x309031b033d060e0921070f08030406020f131a161704051509040b0117190209130914032a010908070803011d04080a03021303060606090504 62
    0x2e000140721500360103451030200c05400900c2d94020074403003907008103400110b610500280c90128030a0344140741501045581d003508aa850790341c0e50840c6459070703030503045805482d03c80764440841d40c01c5003a00d0302c8041c0d513900060415074850760708014111031040e4990040042c05000000c21000c1450f0402c070360502c2c807100700d40442d0700c1403c111540c540d50041d0900354a41d64040f104c0c0700351203c4841e48040b24041c0f500710f03980013050313000e00200025225019000d00700d8105c40a119501b40540111003500706004480c4607071400501180041d4004a02511026003a030801030800e195800042c101030b080c0b034254076a59035a00420002d00c420b50407003165089400008510307010b0454450004000d4014400c3c115011100d082c4007420829040380c0324068020f4200341e121150b40c11b000b103103984203100707040d00050303603400505030324410107207240c4200d0300000d8007802c010040206401942c411211a90040112140400025814400c0f038000e8036440c1d460f100c2290a003014042243c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653605872 1250 653604622 653604643
    0xe040507050a0e0c030a0e010c031d031206010c030e09130b150906130212010b031914061c1a010f0b0304050c01030b0d0803040602070c0b03041505090309031b03 71
    0x740b0b64000107101400b03d102d82140c1009491403101c1da03075540e800d02c4d100100314601841602e03500b44110f0711209603058200c4001c12070458400c51001c009845a99540c0c400c48a0710071598040800043c580e42c0109102c0c00c5160003401c1080c45c0503540c000140c2201c00c200c0c0d003920801102040d82c0306010201d05269809945003407580c1011100b5400140e482a0040034107120301070311940684840040e030107540000d2038480b401201541c481e50300720816002111108480040c844846110724a04d0180140c0c24040280d080314940304c0c117060200680c0c040a1610240548241c1c8000240c0700b030361840c0d0080e004044411440d41804150156944a5031180d4a680418800d003c00302c4c802141d0000c1c095024240090b02419240c04030f0170101d40890b000d8400c140200070070090140540080030150300c038182180103107450b440c5451081c00183c4010f48407410724500c0d060801c03007540c00319422440d488126410300500c04002460214541205543c1c92014400859a42020020420382 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653607122 1250 653605872 653605879
    0x40b0a0e01050315090c071401020403120c0b010302010e0406210b01060201060305120c0717030a09050a2303010e010e07081b01050703050a050912010c081005030d0c060e070e04050705 81
    0x960400003072003c1200e2110300b2907071265002c3c17004a0061007401c000c0318001d5a000388a0340a0801c1102214002e4010384010b503890003100103021540c41c407501c0082e188561010b034800071360742143c004491960f4074980507034101c0d44c1c030b03503010074500c0300e01d403030341d091803844400041c7d240d90b1618003401442c0e4181d100c641568100300080c00094400f14642031140c4100382016255911200000c0ca8505e51750321540301164001040a004800403004281034030468a030710419660300c5c81801540e182038400c12900c00c1520902840d44910300030460500d240081c00401d01c8413080c090b1a0031a1000b90084200741d00400f010044008240464401410042075a402c580200c000103030851003103140c014100140003c51100150080d8242c07882031001a0a1440280d1003048480c001c0034603d40f40c501082c1c18800003200140d040001d0000d40308003802400013140c03d000141d40002100c0403c0382ca103502c0d0300548407441d00c2041800024040401400268101400c0050504a00d504003a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653608372 1250 653607122 653607127
    0x30705060d1d01051603020d0b0904080a03140f04120e09014e050f07180506041515020c1903020a14091305030705060106050c01061d010623040b0a0e0105 68
    0x380f40c900486143c45d103114604015030780703000090781c51300101484030f803e41d4002c3c1200c05101c00d03c880f00001e41a00364071500c08100c0702c400b406001e10704030001c5454031001000c8100180004804800c260613b2410b8100044000d4100f00055503c180c260000e04540141c04041c0c40c201e5807205420040f1158282203950440019042d0514480ca40e082c1e039250780e011a181300d040100421450401c42c402d80c042d40e44840d00d401540d0641e04078041c80080560421000c81e04616061041d03888207912000b07592159441c00c60702d5507007c1c0d0181e03000800d500400200504603215404e4682200000010355a1464150b104004c1c3c47c0c8526000b1601f0324111b005105044c0e1100603c2030340043c0350301c0038010740444500d4010f01d14415071500030044c0c051400006201c0c0e0704030001d094042c044500038030086455407440116040548a02260703101601c2c010400380380140d4420804404d81d0742e600c808801d505a0010860340310344d1202600b0340d000100154001c1d440020344220340800d180075403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653609622 1250 653608372 653608381
    0x10b01090e011a1b0109030302030a060e10090c0314090c1203040609120804030f0b010509092103062806090605030c19020f07092c07060c02030705060d1d0105 70
    0x82030801c0c03568142c18000043c00043c0300c103034503007100030b10790b051130003032010078918a0014041d40098412000d002c2c201480407401d8803000ca00d282c410340300c80c1200400249891400d034058000c4c904014181944c4820006107100306032841446856074200400040705c42c1400d110507088100507000340b5400501c0107010055200d02028121041203d112503000710324140200544129400280244401000c160420403601e60550403650200e480d004141d0360803150ba52100c24102c28011041094076503252220102c030003958111074046c1c0302054000c82e48110441c000100725a825a1010b0351034104801079001805102070701c903500c2d03c1c0b400c600b40301c1382c4442540103d00707560028107400309480e0000c038420001c5400c10303400d1004480203150707a4802c04005160740540d80b05039050509801068501c3d21030318043d44c0b03244400410710b56182c81c408455464003820101c1c1e160041c004001000c1c0d4800000c2e00d403d000651000406107500940708103c00c40b052005000d80e4100360401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653610872 1250 653609622 653609639
    0xd0c030209220f0302240402040605031b0910050d0f260f031302090c1b0109050d1404090c0815040902010f03020d140907031b030f020f061902010b01090e01 69
    0x11071095038007078603202c000a101e10b000c5c0d04044900d4816200081c107882d16180119407403241900840c02030341d0802a5030f88420030f0588515424540c203070120358608048039541800740a4a901c1942012100045500c500c0001c0d20305980000603541c40038900700c01c80c1403056007076903c80b062442c56034400040168046e210003c3c010141090b8441c500400006d1450b0b032041140320300c00c0ea009000e090303181b17850070502e000380d085043c84241d804040c2c40440813141d41480f42456039a0400010680c81c21610070494201c44403450b20000c0400601c400511580c640c0102c1450340825200c0a0080c0ba00540001d11900300c124003900c140d040601c10700150340c010011102c000214500941d0380c4603504840c0d009841180c46445a82a0f464100840d202000c00d43d402a6032013050380c0071781140c01244001510308180000b82251900c0e41c8a04d0042c80d00da52162030041e801307000c240c101014841c841a19490306918400541d4407001a850320350303486103d240141c140112076490381e50510142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653612122 1250 653610872 653610931
    0x20412150605090f0703020c01051906121a0402130e010209010f020d080a020a09030c0801050601080c0c0c130f02070309030203072c0901020c1204050405060913030309110d0c030209 80
    0x501c0d80403410802280e4486e102e50100e401c0181e00710300921060030301d0300c3c075400b5030782c64881c070400403518100d000700c1e40102e001409810039802142803c0e50300b011141d0002c2240018004980c4144621800c0f13114a4141c003230042d0030b80c3d554000580350740c00300c0000340180303844000c1c010440d00000c01300d0440923005104e0503005210302100581302c40b440350090303a8420303142c0c0015160380560300b40007800c0c0f4015000988602d42c283d80e640c5082c0c41354404031400d8011444000c8103900510030030307021424003450000d1a00002d1201042d0306032843d10300750499101320400d400141c6405802d20a42c02c2c200240c030010499982241036003c5d4000d4000007146008000005000822000c2030362240250142d51b00321400c1c105464802068201501c425482031140314041d41c00d043c00076500c1d18150605a104100d20301d07150b41d1101c265a8128000c120b11001143c1d50100381c4903201c802d407610710419030352520459000040d141540100054901c00902c07a44260524030b50b0110035040f05e03c2c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653613372 1250 653612122 653612131
    0x2090c03150d03270b04081606050c03040b1e120a14131b03050115080106050a05090705031008010c020705130b0d150f051612050601050a12060902041215060509 71
    0x104a2011340302d40c807002003540096440503055000103e0f000c81c42c0d60002c17a40e01d00155540e0000c0a0807550b8170019a014002ca003c0c42030240c005000801c0000c1310307003004081100f101c0d150b000080003503094290158210060038070419285404020240712648a034038411460b002d41601c071403402540719002c10410f05d500900c0c96145100440c081898030001c3d501442d80007009001803000070200742a0b508080c4600d0100d0341c24144001040e06000040c01e040d0748000e8110b44580d43e41c080d083da03151740042c0049121416426002441d0344c0280b089e04c8181002e40d0280ca0722500c0c0c00b04100f40d8044400016420500c0c0c401481400d40d6810f00c00040aa0b1040810400448404400c0003d05508004c04a210b040004000c0c90090381c030307018000c184072a120b601c8e0040082c2980d0048030011074180f800b0580420a0700d9000f4000e031007003001c111680d50085551900c072000d541c140d8005034004501200d04020311410455520003801403404c6000082180030310703007800a04196030182 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653614622 1250 653613372 653613407
    0x2010c02282402120f01060c0b0606070f080c010f110a03052d01030209090a03080c0c010f0609090b01080a05030307050307050c0a1b170601090f060302090c03150d03 73
    0x1821030030000598588a45100ba0320300c05404a01840141006980402000c4040481003000556a45001c44802d0b058070095a10121988100c1e6202e005030311025192a50068080c081803002407041c0b880c0004142c49051107585941c5090512429210224440f0640c1414072a84510305c80044041c5c2d9a01c2000c0d00c3c4c00701c3c0301d07150b070422000c282c1ca111015040c1c0407240700c0e84000f00e41210074224122442510003400030390302c5003191a2541801600140082ca919021421944030030010b00303452590880005010320700c008280b41240c56541c0803101d925114a031807000e0282451540740140f070410050010300c075941d600c03235807244401090b003014410080301240c1e04510070029161211850400c441401c00c0e41c0c05e00004074015180c00120002c20a10089680c0d049a07051107001c00444c40105501d0b4240b42e0450094925000140e030317680c4e0f442000001582d50314902a0044000f040043e541341070010516880020181c0c1e240e0080809105800c00a540200b901514041a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653615872 1250 653614622 653614693
    0x6060e0f2409091e0a0b060306101b050106050f0d08030121060c0e030c040606020d1101090c15030b010e010905010c11090718050904110909010e1b0102010c02 70
    0xc1c0030740c074240141122280c0012196041241142400c442c0004a280a0109103103d036a1003280000346d401020407190494001c4c00414880d003030800156032804a1401e01e21145c001d4080107018102c10300400307039260307034455100f0055400c060414550380340003583d01a0b036103409519049010300c81803290806000420340c0e01c89500b00d51181545020f640181d052014502050008050184014009200b4058a61664060300d028403d440803a02c854014010620043c001920a403525010b51a241d540700c0c606a40025a10882c10010b0901010340c4000554040c0009084482508445052000b8581500d245a0300604203c045807024603142540c3c00c1d8a1818004c1074503200c5070f09030007800f040280300341c440d0446203070820000300e8000e4003036543d0388004110b1050310944000d4040e407000015116113041005445a01c84015400460368100b09044607142c0703080c480306104601000340c410404c035a4280503541c5116800e100500c2d1000000056101d4506284007a6807440701c3c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653617122 1250 653615872 653615929
    0x6060108010e071b3f03020903030d050406061a04030b0f040f0507180b060424110d0503010603110a0905040c2a06110403050a0209070c0b040606060e0f 67
    0x940750800000855000b444070030202c13440e00001548104802199100428880c101402060101c04001a5171344c12125201407003a00e00354000d5004690680d01070108103c4a44070b81800d00440e40694881d0f280001d8492901c070414512072114180c100045404200030000f15040f210070701d8000540025940e45074849240080d0340d000b610703400400c00e020304070f4001003840203031a0300c2d003140c00b030444144a00c0848d041000203504c254001d80301455000c46c001400020081c403207501c002380504005161071071144c421450710403d68654000100c0010044c010603905000e003008940040714182d0510351000c0000e84404a40e0245c14055651803d1104507175104096001000500e613150300740216840500b10b47c0703480c0c091020350b0504e04082c4c005400310304840440d0202c0360407030050444030302d01e9400c2100300c0d0740140c540e03410000807100b00380101c0e0714444824016841000e000800c140303490320103098000119446403180c0100080c0d60910b8a850212039620592600658020001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653618372 1250 653617122 653617127
    0x110627010e1206100605160605070e0603040f11040504030c0312060b0a0332010e190515030d080108030a0c0c090c020307060f020f090909071509051206060108010e07 73
    0x45030328001d68007503071050094415a40202e040d43c0204a15013000581d103403070781c4007510f0510a41c5030311804c240d0b10b84100c10210304140c0c0042d404c04060f1a20881e09a04000018001d41041d641601e582d2000e1414000f08007400c4813240c50b100060718244801d14068402400820b1a1b84014080c1710224042d41c10b1407900350310082c050708035246120b4607041083c0b002002410640e140c0e01c411078400003449410282050012803418240d922050140c0c206601242215030107040f20540034869030b03a080c00e620403030060314440c2c1805400b05142c00701000c2003500d009801550742042c46107100040c8540300000c800c840c481031050401e50b6030221140351a444461701a80070004151510038000840743e408002060030758056030082c098001d0b5028100d040788100c4485100c0641d0030001c85020342000550070781d1200241040e110759684d03843c0c003804900ca00c0c0c00e003100014140e4a0502851822650040c0a0550040144114642072001030828034043c02401c0301c410b92040007400c00d51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653619622 1250 653618372 653618387
    0x610030e0a08130614030103052109031f2004140f100504030b180d030c0c1203020408011119110a1e06062408091501030b0411062701 59
    0x81e8402e00680da500f15050796280210881d0003100300040d0301d00312080190200380140c1e03050fa5000805041440c0d101d500e00c0e4200b44c17a4080c071190491080c05509900c0e50709000d1240b4900040d8201c2446882484d13031a000c68070305681e00d5100380e40c02c0c14100701c40c0154400f903c0c140e684491440c59018200400035056100d4001c805d80c0c090403a030305482904e50b000000c2d0044910500100c1c60176221018180500b0881d6002100741e0307480103518800240c402c0d00310002e81052800e003550746a0403501d0301c68108035100a8040403036000102040348150910403514030201944403281807807480b1982c207410f0455401010701b0840211b5200d040060140000307529180c0c00f401340c030350410b80c000c02c5202003824001c054400074500000020780014004d141c2c00b40c5a110054030f403040d52400c40036290620082d0242001e849440e4050003208030450f15640a1030094281400078901490070800407088490300d217004030401e200c00d4a1041001010060001680f64132807090f0405400407900da0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653620872 1250 653619622 653619643
    0xd02070c03080415021504121101020d0515060403020105040506090619080906010608040b0f0406060f14100207050114090d0b0a0207060b030c0a0e0c07060608030307090e0610030e 79
    0x162a0315000040015040003001100d014900008500341000c4050362285060054146202e00711030026000444000c4198411031a5050182c1c0d2040d0440341070f0f08a030031000000c02c0d05aa140c0902c40a21100e900c918540d9104a840d1481c1c5030641e40003c085001c1c5215080c002d1360041526840c03503407010151480504e800051210b07071100b13250010304000080d94464003500810b0008624603104142a5200e190800e83c1c15000b41c80390404200c0c10a0024002d9a400c2d81c1c0b014041031aa5800e1925801019181900344010003003d08014010884048110941d0b000c1c82007040b05e41d070068840c04002e10b001241d161034082603000700e10801e8007010014245200003040140220066006d040000e01071142044400381c208241035450282c0140180d02201c042010010080d940b101c1d264030a0307001640324100300c0c5507030390b650540c2e1054018010640000c020000259404203c81c0c00500d01c48070015807905003000410402200041d44104041c0c8844076800b00280400240301c61 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653622122 1250 653620872 653620883
    0x1f0902130b130b13030b090714090717070f0305091606110a063e0306060a090b0a23160303020c2a01020c010206090c0d172101050102011e020d0207 65
    0x5481c4c0740c1003409880040d6020884010049501246030032000060900c107440380c0803a80b080c241c504c20b04020901d000103020000f0000c010405107555420740702102d00440d5141c0318400c4401c180700c00a02680c81c0100a408681d1014250421100d900d4000c00100c038187c0c10000240360780c595025051519134003028240030300344140021944103440740701c24204070354149070a0341120035000c8491402d602030000c00100092004c18074600d0640010102c0c0d00c1a802c2c41c100f5251f44028604103600209441e0010940e44003a441809400c0600710000c19092500c4914100145c40030010005860501408066010500d000c0b00c42040100c903c83c0704995100d60000f02c2c41481e202c50141014a010340113000301c00c50702600e07500018402e1700540e26170b000340901c210141c00303010301085541015079000f050584094032210301d0400a0550690f4103014400c0f45000c80305240c07082e02e069000504680c5815680c1e170900394402c44200035214094405651140140d9840021303018002d0090170 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653623372 1250 653622122 653622127
    0x3040f05060106020d030c0e030d12021e18010c08030112060e06162624150406030501171509010b15120c1204030f0302121f0902130b130b 61
    0x10040d4000505400c0c142c1c1701c0e81d041c41075442d008000c407008000074441c550561700c9042c0c0341442500a00c40000b41015205005080204038124403443c0500c00801c60b005420020706403198040070303034141d9000002800d085111800940e10840316200511600d04c69801094541c810055207400440e1147d07030b9182140c50760b0808980402c07499000303543e00c41c0030a03101c00c2c14080108055060407210341910102d01da01d50f85050346039010308140d81c055407031800084210b41080e070b030b120401a12800e03200001074513079081c24030240881e03c040e00708012900807101d00740201c0d2000180080c204040c10324022040c3c0700d05625074050003003030408a912004e2480f9170038103a130210f0041c001d500e540c806014541d8640b103200b030100e48507900300031088005050028000c2802403e07080010b03e2540303070061400b21606400210010103030380c0c8050603106000204031200403182100040c08400c1000c601c1c24401d070b010040d04000030f228114070044082070b40c1000e540c027800a0b400a007201c2850a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653624622 1250 653623372 653623379
    0xa110a120e03070801062d1e080607080f2e090f0f0e0a0f0807060207080c1b09280f021207090b040e15100504170a0c060503040f050601 60
    0x810074800c0301d070803034041d22501d0302c00140c80e0414024082141c0d070103002464055402c4041c00303031480303542005803214001c400000036040700076100c03918056031000c0141c18590038410000d0500704064910000c000307608080c4070301d1502000020f5006000010444110001c042103c4050901c4030620303840303245500c1c00020140b8094018007200c44549004100300d004101d4800c0489441403103241096211519210029144080c0100064050807260303050038410798076901641d200c1031044030003010216031501c200e44200400c003c85141c00d007030600b042045501144070307504001d105990b0000c5808602110206441c90a1000a1001e506015012800a0030800383d400340780310000461403a8001096075202e030700e0000950781d4090368140780c60324050440b4003d04010703249140c1c8040c0c800000f0140d079940c1e0305813012100d0680301d4070340b900d18100303000c00059200c221444c445d0700180c480d040002d16880214090324800d0038220388076159414040b60341c50750040001c080e4400c1c2c00021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653625872 1250 653624622 653624627
    0x105040b070f150e0c0102061009110c0712111c02040b150f03090c060a14091309050a0308060f0916030b0d05060105030613050c0d2f13020c030a110a12 67
    0x1085807134200012220650101001203070b403400200c41c812400700000d0000e01501200e82c204080d52942c0d1000750b800d00c040c81540c0350600559a1011000c520161030070402c010000000078006030040381c10304003042e41109105202e141024000740706681d540028822585c1d0700e4500e1141a00300220036854000218600360254030a841c3c101032072265041c464102c0ca811030807100c0d090303110b90b11488070074106040c4420700c0e00449040f503032050454624843c0c08005200344400700340a00014110074000d800e0150060340c001d0700d00c9004488084c180700072030b1030300c40781c80f500001c2e541c514030507142da5040101c3c0100502c6820030344c800042c6101c841408400074110b8181d0300114107548142c1c880b0070148511a544402c020030b26002404030003282d25007824101172035406001c0e002c6680c00c43d02c0300380c008201003881c8000001003000f0b20b40000d08007540003000482100c041145070070000009681d8900842e4041403c01ca08025894420901800000ca035141d1061007003164050b0234801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653627122 1250 653625872 653625881
    0x7060c03020c191b03061515021e150412030c0905150c030708040b030f0601020d0c0f02030705150408010b030a080403020d1403072306010f0513020f0313050d0207050105040b070f15 80
    0x10701c20440480c000214001160007404040c1c3c04041c2c0043c481d41c08901c1d801c801d00c0302000341d03400460040c41418100746101100d11803017503101d00380010070000c01d5a008ec0072251513078244c104000041105010a8640c1310301090494007a036905603d4501a194403440c3d0301ca0f0340d1000b480c500011a00268465289014500403000c100484801c1e0781c8480049030340d00002c580b42c6000400301e201e100041601142460921800602a282515125404035400e200051011601510000f42c100302d528000e03c603100c201c503030480180007204e9064490025034015400082c2c81640030300c2e4210308004a0200c607220b135140c2c12003a0707600c480700d5092490400192905811001907408810880220003064460503a5014203035001c2903070409050015500e060135684c0d1640b0303400c0102480c890b50301c0001c0c511500c0309a60040e03900005103407060414840084800940d03010540a024580c2c2040590f4141c40001070044e459555904000d61841090080581188206100c7c88a210b105400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653628372 1250 653627122 653627141
    0x7090903032a0503060405060609041a03120c0a0b060307031a011511071701021b06100605030f0c0d0b060a0314010b07170325020307060c03020c191b0306 68
    0x540645104601d641034415403440c0030b42400150381003001075954542588066080000940103034108444c11000c07800304c0c3c3c0458462403448944d5400c48d080c0d403808101148162081c540f1581c00d00c41148403195983d03003035a80040a041300d10001a1007600e041000200031a0403074235803090501d0011500c0b590307200030301800e09003003440321680c07985601402d60000e501d00b0842c000e00071503142000409c00c000131a022060b465400700718450001e502e000d030300414880305c1d00c0035103180c5c1003400d40c0e0740c50610158058014440148100240742610403805503220141c61111a562404040140b00810165494a9000c2c1001c15039107507040c1d0503400f20052a1072a05992081e903228000e83c03501340100c3c44000e0070901c410301800625600030b009903420110520582e100101c1c9040700007114040000170b000180d10100303c4e0814428a401054800d02d03e074181145010203031000e90361a000e4940c00c2c0d0b40080d05002c0028104a00400400740a202d600c0e4410300803a00e9250a0015004a00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653629622 1250 653628372 653628401
    0x9050316060606050a050a0e150c0610090c050403300e01030f060506090607021903031101050f070e060913050703020403020307080c010804140304051f18150c050709090303 76
    0x220210342180101d08030f900105c03d540f01c0ca401c08550300400c440c142e070031040003600529028140000c142100d805030403110001c030060034207032408621590700700f25150300030460310b410308610320f8015402c41d00311003d4a400c081e0f401410300b080080d200c45843c60741c060603c8000f1b002c18131180349600c0915401c4910003684c0912045080300b40300e006448883c000c66520240270481e0080c98540b140003422028400b500d25141c0381680030861441d14101c1d031041c2c001c1000101800300080080c4a00307a0b02c13050500c181c4400e42403000005240c03030f40000b01680a0000024100c40039a185070038101c0c10201c2d40b106008900e4000402006504503220883c024801c0324000304400c0004602c510407a401a92211525611a1500f00015803404860f80c9903001c20031000c52943c403036820840c5900e2403031141d8040c80301d08107001006030701004c1c01d02040300300c080421710201c0303403410030b00c01007000e50314103914500800d040160905009601c920f1a4a1400391904109501034106080b42d41a08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653630872 1250 653629622 653629631
    0x702010c020d05010e24070c08180f03030c01090507120b0c0f070609241a060307091706040b06040504050c010e01031d0f0609030c0c041d1518030711040506040905031606 75
    0x1821f00f9182494640d4000381200700900c11a40c07180c10003100151b540340d00034102da5080101002103411079001c003040c0d0800d40d440d03142d5003060220420000340100705036002c0481c0004192150303250b544000d00340b02c4618000003140d20101512800350b503111900b15200700402c0e541490241c2044c201a50f0075110882903040204400c1e60354825900800e02408800b0184283c500070010180d200411407024815800c00c040703200c01003d0640d620795030a120091001c1c1c207050400901c1c055000f0480b138819410401080005100442d0f1b0f5003001d43c003030034034042100107800187d0241c42251001f904108400c2c038825144240041c00c2e28000c4285c03025603080e51a041038254a910072000203160a50000d0250b11060030640d101c00040c6100b1801504900c062140c210b0034601c0405c00d001180c4082c03000e02c880c40388103031131022034111140010f601e05a20303a40c40b800c074008000c005038412951580002c131951a1a00300301d000c658400c050b241da400039000c0900320301c1c100750000e8440f03e140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653632122 1250 653630872 653630881
    0x70503010e0a0b0f1816080c040e0318060415020a021203190809010207061121090705060309010b041d0c1806130f020a0306050112020702010c020d05010e24 69
    0x494080c0b09241c02500141090365035074039103d45441c01070f260343c4c400b6603a0307034080080480c00c3c06010300c240940c540c002e105501c0c0c000114542642100514440c07444c002004404110000031180c03040800b010f142902e034000030016056000d01d62010035143c80e14450440038030f43c04940808054400c4601c01c118038000174007240d403405002105c2c442d910840d4034a01b90741d4026484146d00c252200005841c2c078140ba560542580c101031504014090013140c2007142460300304504036500a290030003030652404a441076a100c00d039100f404d000d190008046010000300390444101c10901404c10b1000069040082c0620003007002d81c0e10450181c01240760a9180100070460a042c0381142d200c2e1544944040024281d40c20300006402ca03500c4c62070102c0c0b002c590010300004200764500040041c0f5100000d0074400940d5080000144100700007170060b0b82001944c00841c1d01a036241902c0a45894480d004104084200b48680319405c070f032241c02c800d03d410643d000745940c1c1d0045415102c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653633372 1250 653632122 653632151
    0x30c070b040302030312040f0501090c05010806090c03011809050f1614091902070204050712141006030b011211030a0612050a03030e0c0a08060f0f1005010c020607021207050301 78
    0xc0c0c0c040203506401c1004400200c420840b06c103504240203085201080c4201d03682c00e400c680b40744030112604908070700100301a46e04032800d01c3d40310109a650a00b50302e02480d81c403c05220502a5a040300c040c1032004410480c1580000d070069800411a824220065502035650b0106c0a9141c2c81c090084004250441c0ca604c0c0809000c0c3d001c4c143c052280c0380c6800f01121540007480c4645e1030b650902041c0050b0703a480c05290301502c1151201d40300b001028111200359000050603d0321144100c0c24024580390301d0144c0c8080301d10030310740020550303e448012200704038802400140c2c942810140d003500c01d08000214007030760310310804101040e610360360107104003020240904690414500003020a000c2d8201001c5030132880d046d186011241c038001805c1c0b460b140c10100d01d642c800010088120200e80707941d41c004980042401d000e1a01101d600303410700c01c0d409218100108001c841782103444260646980c0c0394010a011020303482002070554404552140034807130b42c2000d444486422 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653634622 1250 653633372 653633377
    0xb0306040e0a050c090601121b02010b03030403170703200f010c080402061b0321060405060d120302070809040603051c05090a0902070c050402030f090f030415030c03060b0c030c070b 80
    0x55111002d862141c0c141c80412243d024010700d1039040c42300700001240071030b015100e01642040c10380081080c040310a0b070002c3c03c5600924060b4000d610400c82400071403854400301c0100c0458680301c1d6510314180c9011500700b2142c00300c1104002d01701903103101841e0301042958101980320000c12a92042c03070b00880340700005690107900049c041110b07094110801701c0781c8001200000449141000d56211229071250b82d074800d410f0b4183c40d4041c0a002d140c10301905030444030072a1803100b85001501ea0035880e0381031158100905d98001202c0c2c0030452a0000e440b40f82100074000c005a035502e0400640f42c4100d00641750109421141084003980240d0603141025009088010304030b0402200c82c0003580701890a44070088110000603281d6120300085200b4440c1403040e800c076007066000e451a22003001500382882c1c0080c0014000c2e0b00c0040c0d00f000740401d00740b44c007080350703405100240d0003002c181e00502031700140060b80003543c010001c020b1103030340d0b5550200c0d501969200690917030350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653635872 1250 653634622 653634643
    0x8060912040909050f0706032a050901200d050406021c1202090315010902090a0b04061d040e0d02071d090309240d0f05010e0f0718050a0b0306040e 65
    0x40100740400d000b4240c00750700092075071384504100c82110104400007880c1070255403201e00080c1c0c40e01c04813020303030203003201d44a61b80c5003003032480c440e4031070041c0050301c18000e2220050400044000143c408107280701c110710259549016900c0e903c4030b0090082082e400742c01034802502c04d80e0f012010000d2181d40002000086980c2d002c00e0010b80c4070110042d610009040798035114204411516048200da03550081080c0a001070359506480203004c0703070246030b9102924156081c00f042083d03030b41014595013040705512203c1003511514000500804801c11010710510030a01a1001e994000a0700e10a50355205404004040c480000c4908000211852541e640003403207200d040e4241a40d1003841c0c88180c0002138048149011039400c15040700740515940b985500c52011046441d11403039000d040c403c942000e40e0304e0230301d4070100ea24a000d40700c1001c000c1100305860700f03001c401c80c590b0b01401c0300911107040e8503501c1002400359041598510301c070341c0c40d0180b40f0141000000302c02d00d50b0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653637122 1250 653635872 653635903
    0x30126030c150a0f0f0209030c011106042904110307150507062d091703040b160e0d03090302031c0c0602090103060b0c010f05101802030a2301080609 66
    0x8401240c400401c2518007401d00343c0500d07100d100040a01c8568025980600224000181c40e9418041007501d0300030244200b5041c03244481200700c005401003955980103800480101c0c0101840034280f48010300c40c801070321980c00440500c0100100306012054500d412012034500640f03610702103c54000d500c5800001c26020000e840024050390890004008041c003070240c1c00c0e0981b122408034030200391012000b03641d160010410010008611302c05d590304992000d05524083d03452800400c0003800081d1400390b40c48401982511901010b00344400142c0f4000389000035103030181104089000407031180c0240002c80262241c0007007d2948050070342d481d0800d006082d140d40000f50301941001d81095101d003400324248116100034490400354000000f40c060414103a18100c84000c1d100710071070380c0c4810080010200c20446824003540200c2c0040e600d4603500d14050080c4141c49904005040118035000c45c2c02403040d280e41219109416544642d5610102c261124607043c801441c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653638372 1250 653637122 653637133
    0x5100c0b09030d0501080f100203100506090a0801020d092009041b051503071704030207061803021c1a071e020a1406012c0129030126030c 61
    0x8100d594810301e4000300c6a0782035070301d00081c0c20455020394000360468021540410040c4070380c15420009110500019081182103081c0325102802e040d045205d0188a15800315080c82141e03200350085c1d00034a400c00c02150b4482c0c14080a1700038280c441c9054582500c14070000b0382c0544406281010224003c14800e09552183c0d40d140c07048e00b8506500e0700c0c2500c101e10109032601c44c10700c0700190783c4200740303940c1e04c0b0300c1c12507002001d03139200308480801c0c0d004202c14840029000245c0303005440d203a0506d040303da01283d1b03145081c0401ea41c0b0281d07001c446004004d002500710a02d519000b03004041900084400400310b1080c207109513008800546c01400c400c03002d40078156005088603161060360542c07091611201404a604410007405802c460010442140e0754401302d02c9070307041290101c88036a580c3d034004000c04014461100d0010805007001d41c2c036200101c4440fa255a021099034895845a1290031108038003140b04081482d08180901d10440002c10780f502c1458040080c02c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653639622 1250 653638372 653638397
    0x70618030b1807031a01240834090b0f0702040507050d2307090503100f18111e0d030e060c030c010504050601090603120804021f020c0a0510 62
    0x2140d40000601e41e03028800000c200302e45601060202a000303500541590110000410310480d6415045c0d0205101e9081508803292091070554a50303004802e904104201b035545c2c0600c1812130500107401e00489030142ca91909900d40c10000c034003031400741c0c4c0d903030b48807188c50fa202040c05100d032607170f07104402c141400341720014038103500596404210741c6070a0382444001c1c55a041035440c191100c5040b1140307041c100d441998840d1126034403c400c0c0c5407000b0014501004a070b16080541406a2020f4440820800b41c0740d13160400f000104548a8444109500b0b051440503d045085c82d2031048102c07203803003400e542c42d88211075207110b03000740795460107022954107031080c0101e107080d07641054040c000e00da042e18052020f8030250401000104451806181460421005800c130303003c8076240550520100340144007003103a01c007540c00c3c00d00303480d1105e0000401d030b140521502000c0c4011140807102455001c04c0c1e00304550703c25164024026250401c100c4440700c0340d0f403481c1c0040c070070001c6034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 653640872 1250 653639622 653639633
    0xa050a02090a12030c060227040204120b06030a0b07020f0106080a020a050d05011508070806010b0f07032d120c021b04020a0c0204150608070518150c0615010207061803 74
    0x10f4909031103418a103407a00b00e65a01c420070707a0005842010b012008403186040c0e600031000141f000101103404610301810300f91401d03800c0b0010701c00500380034050800640740303840c03c008150783c03140c01523901c01443c41e02d043d00954503040984e403c880e6500740700000582c80d00010350005800c0d402845420705504200501040b0440060151103640d03d030401e800007050032400040140480c0300180c0302c01810b0180362407410506031f21016410300b0402c0003880101848050300d103101e80c1072510002c0d110309030456109059200c41c01401e0307844a00c80c1d0b00038290700104803518003c9d584000303001d191200710b0241c0e120f0441807101e81c1d4028945060312080d203420740c000c000a035228284001d0122044e00800c0842d00401220850705110741800d0104c00c0e04081100c0e803118407490140e05e000001c0d48002c03c40124540c0440c0900262200007038605100302c01d40e025014508121517261801400401d1112700351420725000d4066002e000c0352041c8038405402c682074000c000c0300120b501d1683d91 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 653642122 1250 653640872 653640899
    0x916060e041a0405010906050f2e050c030f1e0304200a030c181103011d070c02100c12051312030306031a01051c02011205070302040503150a050a02090a 67
    0x14250b5030100c0c0745221100e40c1d500e1090750301800717481c0000903859003080c0611a0f661425284248520400d01d409114284000510451007851408941c200751100905440c0c42c0109250300240b8000441c410030b903401040040c040c40081c0317085135400055904003c3e690b92000380c401401203810f2011041c1c042c2d0035440e1541c000480a4050003100b6925100d40c0595001d54209030b9040031f10300040400101c06005690034081e019078414a9035140c810562189054204e24041c400e4014001621007070140c071b003244060790040d041c4003440d0300c0d40d80010400310680908450b185c00860304850b900d44a402651030308a040510200c442741007140301d0382d90f542e1408c4210308164030b030030011001032054555030001085c942289502da506040400814803c40f140b4104a948405015030150303902c100402c0280341308000004050b183c0120440c040d01c41d54002607014410030074940c46200c031902546205114071041040288c071000c0a03042a4488d03041003075844191b1f580d080c01041d610307480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 653643372 1250 653642122 653642141
    0x605040b070209151302040f0b091e010210020705010207060501090506010507061a0a0303181a03060d03110610240f12061d190603031d0607060609050916060e04 71
    0x1c4c4000184000d00c0001c0381d66101c196220001c0c0d4020034108884642c51800c50b02409a410741c90382000c0c0c01101080c841c04044003042000d4140b40314826650b4024441440d031031141050640d9a003449041c84c90203544030b200304a510300d180c880005081c149520925014000507914031340b40c5109900c03518047d000c040340d640c421400e088411501550fa0080540c000e40c4a510381c3c02c000f101490440126560a62001c40d03154070021103038100d2826203040b039074040d03002c0340c01c4c2000070783d103050480e12000c00000402842c0704d40000d100701380c04030700c1300003007247c0f4000c8000550035103c1d010948402d0001001001040c01045800007142c0107800f85070005040c21f6000401c2c6644040d0b80c55048480068800c502d00d61405101e80d00c00c0a9454005030461145c080c1b01c1b4600c0c1d654010701800681c482510325058000040000750f5411089400560308840d05100c41c9440f10700c42030090105803200700062060380d444011055030700511300d0444c1c4441c2c80e000c0d41c0c4000761050102811582e00b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 653644622 1250 653643372 653643391
    0x5090a090201090b0c071d0f010b0c1e031c0b030303010e070c0b04060b2706010e04090f06020a180f0e0403030b03060403020609061f090b03120a11070605040b070209 73
    0x414140040c00203001884c950390010b011282c07034001d061f19800610350b414051584082e042141c082c00c1c2007609130445040c069119520840c07428124100010504180b00d049a54052111140d0f40040070703007903801e80b40d07160710303800124495a8011103480c08200343c0c16400c10702c010004d140c1004400c0350b10cc859414601559001680d0f00241500d04a0f41120f2403aa070b5400002e203420403601822003400b9284210120b4800d00d0000003244600800140c10000d1482a9041e9070f1901d800c54004254820b0403107082c60500e20f002006500302c4041c0400003051488000d80216443c15032200710703402e40302d84078241400d156802040440023082502850740781c081c90145602d0403c000e52241e8040c3e4094581400c00300e00250a00384040c004141000542110311240c241518003c800c50314803440c0083c40c490580013082c20500ca640c59641020000304111250a82104119405604003000c2d5800c090715654159054052406020894031060129030f0060402d0742c2c03501e40095403070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 653645872 1250 653644622 653644637
    0x109050c0f0a0b0d090308070e0117060f031605030c0f06071e120806191406070c03120807020c22090c081c0e040c021f0b09010308090906010905090a090201 69
    0x65000f15415401040b11091481d42d8510190505912202040d0001c28078501803140800900008001402405e42e000c1300c001e5240c00b0403290b54030011032410a290140c02c2c2c82c84c030b11001080c0f800400091090303a010307005d41906815640340c008080c1c002d550b00104440c0c03c00d40700e5254003a01c0155545207203c1c99124503000c1001c40d004000407610300409075150321440c60194248890045c40c80000168110503003c2480780c403401c034500441104003920b4a42c0c490500f400c08082ca5a040d500c047d00b004141140000072a511140c820b21902c4c07280c0031201d800c0b280c04240640f814440140c203440c040043e40d41c446494554100f0141d0034051411617028a80341c015290a1038926081e000b00800302c1c4114841a54001b030185114400442d8104401000380c00080d4640031030f0304512000c030300050324089000c4a103501460721114050180c89103580c407440c080380d081d4411034070184a40b400b42c002580d0780d0702c84c03600042a00e1f009050800c468076258101d00160100ca81c040b818400c07907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 653647122 1250 653645872 653645879
    0x15030b06070606061d031002180d0b070207170d08190c050a0e0f060f07021f09031505101e09050a02030a11070807150603120903140109050c0f0a 64
    0x100000740004900541d00010a2441c1c070344080c1841d6001c001458a01c03070b89043c068141e90f40412a0596042511401341e036401c0d24143d00d5000005071b00c03c5a0344500000d070b0300003d1000300007d00b0b115200075001c5403030701505c0c0c5ca010901606560041c125a41c0044014420f00e0301c00e4641c19000007050071030510010341c01030700c070040d030f080301d658000000c6000c2110841c03141d021020103140702e4241c5040042c1c951031808105584601003108000140c0090080119211b10000c182140704502c4c10488140701c500c00100780900034441900c4091001d1074801c04445148034050140c04860700d4115424600b42c141c081c108030781c155107030000010680000d060380720b03401880d00c61640440010707038915040003400b0032201400c14208000c0c1040c4070b2680020304000854811b80d41004c001441401004070110240c0800c3d00000c091100c0c0e181000401c0d50040842e00035030384250300c17081c024400803090030700304c070840d840151141e4040e80c4278018a04081c03007084d04c0c07104081d0031149480d84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 653648372 1250 653647122 653647129
    0x6100603151710060605090d080306010c15050a05070801060206060d02060426010e030f03180703141c02120909090309090103030504060908010c14031018060e0c07020a15030b 77
    0x10b07a408488042d4009400c403542c96503482c810600504014204503007440720705d001107952294070001c000d140c030350000702282c4d15a001d0704240c15402d038400c00e061543d50300c01e04c00c40b026200a682800c00c260602e80072130501401055680c2c1038030800d82c0101030903503500f0208145040444410f0b070b0070080811000c40c1840302450002d5050030325116251b041090310140b18211010742070035211b01c0c0c2051003541e01501ea00004c580e0003a14000400811040c3c0401302420918141c2c802885401d10301a450400702020581d8006840307142a10255445508002d0780c80307103043e0000355442d5004229046551070141c0000d50007402c10b50880c0d08008100c1c001c00d40c7c112082e0820380c00702d68003113170811485501c01c07806009059140300a01c003990690ba409011020310520400d06d0420100019a0780d10354110028014908900c800c03074255070030b0307a11200511660241e4041c40b08071384001602824280c0407a00340750ba0207080007500700d26220380e489102280c0b41c200c40c01c06480d80203803946641d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 653649622 1250 653648372 653648399
    0x20d210203041b0603200a090605211e1303080a02070f1a0103021f0926071e0f050d0201110708120a030e01051e19021902010e0610060315 61
    0x4c0e140e1800100400c5042c4041980003020107184146074080048400c441d40c0709445404460f4142040c075143c000e18800d40007002c4040c14207a80e1008510304101180c0606408070800300d00c0250309003800e48440301606407140350254080c022070784100100b01035241d240d008186140c001c03908031807000404d64481e4040b500200b01d20020f6034010300103209515280d80041d085d07040501140041c5a04008040d040e100948030f4807240000c2c0c03001c103030303410300001285052104621090319507240d15180c0784142d107580300d060322418201507040861000c01c3c481101f41035803002030103242e07a005554011191003080203e0035074140281e5400041039102049024000c8c0c548110440c1c8a00343d41c038004003100c0550a15001584c100000c0c801d00113008000c00c01c211210b01c890a4a590f55800607594088200c175149a03028400141c81c0c202c2c40703010b0074400400c00168005d2140c4041254070a40e2510b0a0301c0401082c221880200009406039000c07001902265900c0e8200c142c0c1c4e80031081219 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 653650872 1250 653649622 653649629
    0x10c02120f13030f03170f070e0d0506100f06020a200a0e07050c150411010c110a03050f06010e040c14040617011a01080106091a0c0a030c03020d210203041b 69
    0x1025004c400030503401000f800c18042d801079100400e07240081d0700384000300000d00138905111840c81e028240740c40b504010120590400100d03511420840c2c80e03c03007500024815400c0b42ca110440104006102048103610590001c60020700151610314036440d00300c2d82c040465200e0040c1d40000762020a40303400a100e101c15444158488201c0c1c1d043e1030a0200305600c00f91400141c604000005a6112086204030300a10b400900d03d901ca261001c00d20224081c2c50358041c000a400008001d40001c09111a529601c190750f480d1340e039071030101010681514004c11619980c0720a0001c0c030390195018100440c0100702052842c1d80f640c64096041c43d80c030542d04565140c1c1c82c40c04050640f11a0f4406984080ca8442d040398901b21005140001d10f0107410244080407141002d892000401e860103c50300c0c1d02610716030000c03440c0c042c08004484008501600440f0b00d00c15100703004000d5545100010843c418680b545155030000035400108110740046d88410171001d00c692039080d02014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 653652122 1250 653650872 653650883
    0x230a02040518011d010f09020d060504180204202506090602070605090604020108060d0201111e0709020408030d0504060f09061a09061e03100203091e010c02120f1303 73
    0x229418404c1070303d48083c00201449114040310010050300c46e0041c0c81c0e00440d81580790042c4c0720612160410080c0c02240d20841c0e00c242031420221100201b29141020302c1c3c03007180c0400040210403982001c00004149c1d42d2154a0b0901186c0d000801c0080184482c220300360300d00100307486540e28601100c1041c441507420a03400b0a8582c108081c1c2c4c410503421403214001048a40b82c80c2d03000810000d001001280079108035400030f421640030302c10140003403c003c0140c400b86110805400e650480007002c4100c41c1c81500000200c201300340c42160103548080d0091441c00603a11554130203000301810865130ba030782e66114580e11005912610150310710400c2d010480c5240080c0344d40004801051740c1d8850f00b0340c0e00522900ea13541103043e202201135010f102c020060301c0000281405404441c08100350300010400800c2e06011038500166000c80007000b0800071b01800d054200c614000c1c2041c00744e41b0181411074084c0c4140d02402401c0d40c6640c0c1c0d1031908840c603d0b150205442903204030390 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 653653372 1250 653652122 653652169
    0x40f0c080607030f0c03200d09080c030304020120030d39080108071404180f1103120304030203032e0e010f0b0f0a0c020f060c0f0f01230a020405 64
    0x14400003c1c012210045c18a1909100070440010f0041c81201807058850100300d00003a02c00c08440c50740c00461440342c20045a5896094451505481c1c1d07008036400c034001118540720480c0801506891400d501840c4010340c240a10456464003c1412080c0008060400048011b464604484461b140a0500c4900e02c03820441c40000c0e06807141170300840030a0300280c8003405a880c00381303040b50301c0c003408550100b008034034051103800107001028007404a05050740c0b003405000c440f14411072088420381c2112103006810240300a0760005840040068200f0030100700302d0000c1411242010059252840c00c1c100c07103240e03103028004c3c981e006600c4808010300400c0031a600c1800d001c005c05110070100c1c80d1a030f000c1d446002e24400c600b0b4000501c11196440c00a54648000200f04ac0001a004555445003104c2c00c5558901c1c20005074a28071889902015144042c010710b155104080b03031000f401200050780d07414052000b401c40460b140e081c013000032940e0311b01c0d9603a0880d45618500f1035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 653654622 1250 653653372 653653391
    0x11040f0b0712022e1b0903050601050301090308070f0207180905120304170a020106050613141207050d11030102031e0c0a080408030402010e13020405010323040f0c08060703 76
    0x1160309042910081d0740200402c100000c2c40e80780041041644088010045056401307000300804441112800c1d42641c290284209600004524281d030300034802c452250b070741d40b03040500340e40c0c03104d00c02400180c0352800300300329501a030001200030207140103a500076900e50345591034010f008098450410341321000c074030034404188584030402e8955800e1615514003521442020303040039203201c42e0003100140d8001141c1c03007940101c005e42001044140e581c24404041702102c120b07800780038040c040d840891540751030000750715020440100050a0514900380401c07518258054090f20400008696105165002e10003988511401501c01c44036000c4800e030040d6030308000741800007002042007291005600315540d690700980c400004d81d5660303242d2004072a440b118082440e0045020900d080c60000d4640280050302e0007a6400c00686118400840546900084c0301c05031440b4a00480c000c030340101502c803881401000d00d5031402d40d4034551240342c01c2c0e0031501c91001079a51251038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 653655872 1250 653654622 653654633
    0x2091201020310060804062d0b04060302030303062106090a0c08150604020a2a0302160b03150f13061401050f070f0201030b090112030905150307230c01060906090504080d11040f0b07 80
    0x710780049064ad001c0210a081d58003080e0760380f02c007074000741c8100046c40605130081003a410355001c160604083e14803a0812200103541c0d41d144100494080080010102c1c141600181140503074848000d6694540c403002c041c08025400244100100190410080c000002562015408040500c00710441074558200241040341034070700c2640328501544100024030701c850540b504061494002a9005170984c00508844141c00e400c2e0b4006030f6080202040002c1c42d03010500701c03100b5554412984c2c03840d0004554a1260314440e0625440500c40a0041880032800c4240a8810f04000480c80c2c240300000302e03041d03400d83c404002c940300886081c2c10540e10501500043c007095880c02e95454941201c08034500004101c08200328140c0d41c1c80d4800552050403000c40d000c01c0fa140c507521303510f1030380d0240644514011042046c0c02c100000800456900c580d621503600300100c94148100780e81150060280300c0b40c1c2c0e605554080c00041150042c04050200405a0b5524142d50321401c3c5801d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 653657122 1250 653655872 653655881
    0x3050309160803071b17030a1d010909051f0b07110414010e0613060807061b080906070809090a0209030d0c021509010507060c0302091201020310060804062d 69
    0x103041c0e0a00100408102c1c1440000c2a90000356002169030b203600900d0171865030b060110785c840c82103890450750081070f5401c040000d104005040c3d40e1120162880c0b8011440b07150305d5142103001801c0150100080041584001d80185001072505140304400a80c00a01da45076084880c20203000982071003080703c40030840c0d07403004c42a40c0038000c0e8520810b403119a40014401d01c001070040130000343e840c1c0d43c1c0700c0c40c4555061030900304000740e0341c5807c0401e60704d01940c0280004201c002c1e004030840d1001b4082401103690050220340382c1031000080c46020381000c00101e44021007400100443e685002560380320317104e00c550050300c0380340e008101882d10b554042440140110b84000c2400750b21044041d0b54524820300c215030f41c1741042e40048a0f076100e200c6000e80b1700c62820403003068003075040e002490500c504840700882d5040705042d16080340b1082d12894810006000100031150081ca02c0c5c942c011300a60001600150449008080d48240f58a5400c3c00d160004581600c842600c138 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 653658372 1250 653657122 653657143
    0x804050a1a1614120408012d0b030a0c0e042f01030c05070204090b0403020d02120405010819090c03032a02040f1b0e032b12110703050309 61
    0x4000480500c800c03200d8644181c5180305490018201d56409000343c11034440d096892240c21969400f082c80c4c0c80d41d0f6a60890701030790a465080035601c03000c2806101d00050750100e0301180c0a0010500d0611500804000501c1c4c0d405009903000f440101308001c1e4440700529001261300780d0351500f4030b80350040d0104072460034000b503101c0c0400b0380303080d0a030400628565420308001a040400480554850041020096205081c00a04030400c219001e8503400340b4426000c075010011340240598490040d003101f506041030038401081590f1040c1e1241c3c0d00003441030034001c1032500d50000c1106490488c10255940411903c08104040d405003c0d01d00c88000652020300c2c1c4940c2c040d040c04038203070820000e8456030b100c8007819502003155000c0c0420312500b075482411802c010350b0144c034082c40c14926911038041e000406c81c422003110364505061003205100d90680e0f0000c1e0003a218209003060520340e56968903c06540b03100345a0007803070140d010f901c0c0c440d200c6c503003450b10901d003800d2041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 653659622 1250 653658372 653658389
    0x5011503032604200a05040923010902030604060b0d0b07030c021b180c0903010915110405090c03090a0519150603050a2405011508070905030d1211070804050a 70
    0x702004045003403883c03525803080c4c8154981074213403d03400c009090003101c1d0300000c0d88149002d0b01c0e00100040e0000703d002d2013941c0480c9642805211581c00d088550001c8041e4041c1c004030001030028040358070404410708010322900c4170703041586441d20b214000b00c5408000c41c0d507650403908507903010481031102e01048580c111a48510390003003401d400e00300451455850815001c00c1031440350400f940c0d40e0000240c002c0189a0203402d2000034498411305007204149461041485604000d04460a86101401840c000d171a10910307040150701c003d140070040d00404e3b003c4400110180545e0354280007040015425001030300341452880134000c0c10500300c078035102c001c000140011440c490020b8120743d5101a030441c14500c001045d0780d1400100841d0714180000c5648542100700c2d88103100607a45006281d62003410696014138035000345903060340002942c0441920800082e04103a424407404503540c20f401c444a02140c101d40300c116138803a004a0140400d040068a00303000b8507174035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 653660872 1250 653659622 653659697
    0x200117060a090e0c040c03020717030c030103080702120a0507080f010515060c150406020301030c0b3f091c080124090810060e0c180405040501150303 66
    0x358002400d060480c410195034688441100340c802c201030007003500300100503100788034481c5405030040013035000d08011aa006202d5500c54a061034242c00d8a20680002c400c41e0703c0d5900390345481c241500151000ca034041400c0a0000110209004002034607100340000c10030340f801c00b0350b114200b01c014071482116a1421003003210300000312411031021001910301b69138a00601c01f185091018009045550140c40c83c00c0c07104018180e401581202d0103508002e032440d442e11601800b600c54100e031001c2003400c00d0740180404100011585141080c0d641c41e401501480c2401c00d00e0200845d0110a035402850204201202d945002a10801d071072030101d00640c14040d85111214401240c1c0e0100403900d41c000c041240102210409820494200c400001c0391081040142c8414051010b18110030301c04100b9001890040e01c005026902000c8080d100580501001701401042a54151749410b048103460117400401c038040c6000350748040400c0004200740103007030300c5c40c0c00c1813800c2101e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 653662122 1250 653660872 653660881
    0x40c090c020703020f010e030d0e0405060d05030915040f031406060303040602070315090804180b010807120f060b160507300c09020f0403020f0906150d09200117 71
    0x460b0301820380c0e40c100e0742d55840f0585400100d646842010390349825128414040c1d680f02e410194040038a80300315000e000c2642d60109000d605102208010016031090208419500c1d043e0008103002100050050901765101960b80c5400d810354002d03504c4251409054440e850203100b280e1f031241e03060300190b24041c90850020340d00c01440c400501400d212011b010b202008030f0b0003039480a90030414150f26662180900c41548204412061845140030102c0c2199400781c900c00d4841c030001d0b02c48054118114080e0006403c10500907140303540c0c0e81c132012a0040c0c00101404d0a42c18856166907140c0c03441c40d0844c075150b0140c01c4034010502e410342542040d150740f041c0c18200544030002c20a50b000030301d45201580c155400c040c4080c0d001207640501d18154030068002c91b4000c50365400104140c0081c8003142c80309071403131034200d03007030794030b15490980603500420302d0b000d016a0000c0c1480e102e4451485224000420044042075108482c40941c1c2c03200b0762820402c490200914030b401e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 653663372 1250 653662122 653662127
    0x140a083a0b21061b0d09030905011707090620370203190809090103030509010909050108030f160c06090e010501030e060f060109050a1e12050705060d0609020c0105040c090c 76
    0xb4020149010700c0810081050100e5400301175030107861940300140003072990383c600509110b000e40501800500d101041401c110120369a40d80a00d00603100d1560160074907408444056022a8031900d00c140c40303031002004241000200d4011806041070004c445c41d207508040c031802c041415104041e07002d00d800300503940115006c0b13a174089180010103445010720304220035010b4518410b80c011800d400000074150000d000303000701d035800d984403905244c4802c00c900c12a4400c2c000d00c0c00c940d2041c0310900c00741d203d450050400c41340031200c41030100c40759a2a1050100710f42c00c0000015164034081000031842031000d400741200b400d0610500391403181d01962038500600f10042480c40b000400c44c164003542c001c0019201c080d00750104241c403403446c405100b140043e800c00c1011030300c0b000076480b9490a00c0c0a412036100d8050054246024200003490304014101110207983c0c00c400541040180b00030408440c000c40082600d1400e0b09004403480610390000341c09a0502148901259 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 653664622 1250 653663372 653663383
    0x131d1e070e2107060e0a03170a180b040303030f020f0a0e0f03011107021c0201140d060509130c050102120d0e0703050d050304140a083a0b21 62
    0x1103520309181c80c02090740004107600a064000c00c00000b01d000d10407004140418090160303600c50b118015548103c00601000006520021b000510034565400341545840c1c010400c480c00361621718107171071000031103006011041c0d100c9007078088001403c00401d03070140143c00885401e0b0030308500b400341098034a41648079201c0200c0c01c10a4104501c042d17070f9600140d1010030310001c0e000308a8010b010565100b207510035100dc0c2c1c4983d05050002c100000c0001c121140b45d039042e95a0484e40354000303c00c41c580c1c1c00400301644071544035080032405440b0b403507000e44105600003004002200604200400d0081608010b046402c80000440d0b02507004040f503c0c04500c10301c0008010040340c442c18101755081d0401041e0380181c0c0411459598010059809a07015032200108a002548125529201d29900400000041c8107106110300708149204a10640e0184d004404500e0258940380c0c800c50a400c0c2d001d265944c5000e4590b0412011503004185800040064900c003200d449a81d80c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 653665872 1250 653664622 653664631
    0x1061202032403160605040e0f04050c01080a022b0c17060f0a080307031809023906180f0c1f0c0615060314060112050903131d1e 57
    0xc1124580ba9801900c080046034400140b84a02007044c0343c4803440200141d015203d49024022401c000c114a07003120318a40c3d0040383d00c04000c2034158240001920813400046c000c02c44141c0c2400302da01030302c0e81d001b0318400380982c180450880d040c480c7c007400100c46401d882a0204500d0300006004800041d500d5030f0881c00440b500c15102c0154070001e03090349019002a03150740804256201050780002d070450000d180c10301460f881d2a00c6070442400ca0091000c5240c040c6010341001c00180f401d1404000400103c082001c261074a40951510304a010b036002d0300140780c0816606100c103c1480344160140c0040040c2c019400c050000440545148000d038168010b00e10305409a20b00071100410020782c040010301204210070109044500341d841911b000c00c0c101602806001c0c400c1d400d103881284161a1030f200740700ca59107084003d0100a0100c6918801086440c0780300004481d20f8000707000d0300c251030b9400c240050010b070304407401030710031881610711262081c40c21503990909a0312 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 653667122 1250 653665872 653665921
    0x14010c0c0308090a1407050406060c03050706020708090303031503060a1a090a060512010902090a1811040b04110306040e030406080f0703180305070507060815040b030102070204060e0106120203 85
    0x1948404a00c1c5081081030180100340c4081d103241104009400f06e940001c40384200c80c00c0001d039a4400e01079588503001c0c0402400074508200c058001740066002e004164024030b40b040c14241800c0200e46558815101d56100410744240014030707103820000d803a842100540140016104400030505906402e480d19101c0d1450200240b0707400000e510400042c038008003084140380f0441101402010007040990103a0105030014107130000c113010345d05480006104005d500f51803500c840c0071580907000c1e80c2c0e52141d190090301640796a41d004242d0310845046c0c41d2503607410000204000c590b5040c901c130724190418081042800d8002d401c0581c01624001d5601c11503548600440041980c182000155850507480a05040e800406003050900c1002141c0d911901e80380705880340c0c2c1d41140c090140d000782010b88070681c103090f000721882103030107000581000110750016082c0d45864014040682c800d000411410354403d15521111071018021071031030a0403100e00041030a21041c180c1c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 653668372 1250 653667122 653667137
    0x102030711190e04060c081302040218040c0924080c0a020106050307090e010518030d020c0304092a0e09150303090a080d18050a06030b0604091814010c0c03 69
    0x7026119141e2400401c15049100d0390300e02e071600991501d904081d2025140b01d86040e1121200c0d5026403000d9005807408000c004140107941d00308030180d40181e1030b10f012011034444039516a103035405900800d10a94407840c039901d08000344906640c1400304007130860103005050801c1a80c000c07246a0304424051015684c82d40640380a0340500916481150140f04020002640c1c500fa030784100f8020080d00024480c17500c49022002241d004080840d400b074004201321000031800d0760003007030a00b640d00b080d61304040ea100081d4080711080000c2c4140c1c02c4d4494427405401c45220300010000b0541d080c002c000403a50400310f240d1110040240c41c1c141e4000c203145041c0e0781e04105981491000500038034246480c0d02c0a940c0b6841d04a40000c0812001c004108070301c0d50840e95142510030140c05200c10502d0494100c0c007400c13003051410f0f00302c00100000b060000150049540591a200c0d24102070820751a01100c100c190401025039645070034461724000340e02c46ca1100415405160004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 653669622 1250 653668372 653668403
    0x72c0603090a0503030112020f040b0f01110c031204060f080c04030b0403200c03281506050a031a01090203012102030f030706090b0105090705160305040306092f01020307 75
    0xd151900816001c1e00071300c00840000754100003403080c2090144291032005610181009100c103880c410001c455210105210700c0711154400c0c5515084141d041e4100d038070144c0600086410114000812840402c000800340946504941e0b0f03180340c04200e25040d000382ca0080c8013002d040c0214007008018402c60317804502413500c00d24080c801125480ca8800340303002e8104003140d891804601d2076000c0d011f84450882c1c00d2401d081c49240c900c4001031146850303c0140c1e1501c5406500d5880050004d65030007000c04d10b07843d5241d81001840c8140d6403140c135640721401c11515884141d01c000707007807401040140201e22a20b80f01100a0720705280d241c2034040c1602c0064105170600c4a01145d6210100300501409a542c000c0b42d07550380161081c0b419a6264004d11481600840b55400031550400ca0708120100700c6111004060203031400504241e10f9a480c00161050000241c500280c00b804003a85000b1004000c2c0380c0c0000b0300d5440084401180020303440740540800541420310207232104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 653670872 1250 653669622 653669641
    0x1a0a0b1204030f02070e01170624060304020415080a061404021c030309021f080901050403050909150d0b09061302030c040b1507030207080d030e0c09180d08072c0603 73
    0xb40914052190341c07580c4404c0180c84032208c3c424424001c1c8a01d001007408009110300038006c00d06070340000c000c040103802c10300445920150040b070f0016507800700143e441c031140383c542c8081c15202004e0003446100d4281002901e80e00c00b590001100c1c0c04042c00016515042001001d0000b101d02032195442d90600394001c001040002e50045460038001a005650110f00407200070941c0700c005540d1215600242201c0003160020046041000380880305c0c504403a14a6005002d040c407100b0042c4000c002c9001070b580f080003159240988020322135583c0d13003030144590054441c0740c00c6d0300c90030741038000035a0703001072008081c021541c0e804401419140c080c22078030780a0102034219650301c82850000c1d580c40fa43e00c01e0401d02c0c010301c4c2240141a03c280600c0f58004005d070000c00045400a00b0070000c80d0b400380085250414000000c0302c03584007071184000c6884c55444822640c40c190602070302c0405251700b0a040c3c0344150052081e07081459002102100d001d0311704a40342d91b103600d8407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 653672122 1250 653670872 653670883
    0x20a030f05091005090415120605040828030b0d03090b0a03090611090a0b0301120b1810090209130b010b090f0a0b180d0308060d151a0a0b1204030f02 66
    0x2076604400c0803c10b20f02da013504400103110040096070b080040c01c0c845183c01c00c820049005061010b030034803807a8004565240c01030307508140036012440c0380081100d01060b40f05603403054a44055510b89030708051079094450414204000c0d03640c20180c450661780104500340350b00406c401e514021403d000c105200380c0c41905016800034040101d0300a91407032110380e03003241001d58032440d40d40c0800f044486200d020b5034104d40380b001480c620451180e84c1c6081050004040031030100c031100d036000c01540d0802902e014a07050f41c90015040d4420300500c012007800511498070f4500c09216800001c820151040c1103c1e0515035842d00c030164000010940c101e00300480d94000f850800c0440e031110200001c000110b0500b41d0b190702025681e0600c0f00560040d0300150200f22002c0001d2000e04111880d2022940329145241000c10454099001c603842c001d0794817920b03042541c00b03039a9800c1070900400a4000b0004040c10311100d99a201c4c28810014401010030107003000d1054000c1c000c010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 653673372 1250 653672122 653672137
    0x10605030a0e12160b0601052802150f070f030c0c02240c250f03060b040605031606120501210309181a09060604170c090708040b0115020a030f05 64
    0x1050b500c0d886942c0c104c040e000000c80039034003a002100072840039030140080350b107070700c030050700c06543d502000b100c1180e9400d144140e50198007400103800070510401c16401d101c0c0b20603080b00c84140c02c140000501d166081e00c1014249071611440700f00f19904140c5501d403240d4104c071140004403058101140c840c041509403080000d010507482c03200180030491110269030403d2a1484407480702c5040c109074128402c8000d001002d510504c08100d6a810244580c1c01c06040401ea181d82e0f04086464011018600c04a1240460040c000242c0c08061040c0906200c1010311465041103250000c06408003000704806180c002458209401078107010300408900c21508035101d080546500a402884a141428501d500101da21880d000b007843e4000c01d07010300a13605003410100322482c19015251071030b20303901c51070150b001d159441c040e85034401e02d026038903050301703080914081503411010703005804400c40300200f101015a0001e82240c146406203060303050b048424509407918440c40c0c0303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 653674622 1250 653673372 653673403
    0xd0209060a030606230a0327030e0307060c0b0610020a0605090a0b1810020f040512071703040305060f070e030a120f020705010203030c0f041823010605030a0e 70
    0x18001541c203805030320074000c48410b51078070380c4050150705010f00c10040420042010140c1401a58081407003a071140c6040c91021404110b4684801780118807441300e07600440c00108a611164541d04007488810020107240c200f586900300b065840c9840c80d08010701c100c3c003407035611006c10300081c0300700144c82256405c200208558280351007600c0d140c903002d2500341c88046c00d04000c905000d810b80421801104004054140b039822008020061b5018401c80d28042409202c0840d203039940c0ca4155402580e407a0007012254a44580750200010f10700103000250001e1000b04003180c40814503070ba011155008140540d40d1b03000055600c20500985c0e80d815128085440f410004401c00401c1e0403003441c0c03a0a074100f5140030302203a541c070041c018070f401a042030020818846218010740190003000031580d08281c2c8540c000c9855416040e4001035080e11603142c0d86280c01109485009590900c4048580b5030600c403020f0114880546400c203500d9407444000d461801c00c0c481c0c49203005064 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 653675872 1250 653674622 653674627
    0x2a11060d0902040516052208120d050601021204030b04020604090504080a080f0105010914060d0c0c1103010b0d020d0609050d0c06060909030c171204030c1101020a020a05060d020906 80
    0x40c20404020064414101c0c003492415001c0342000075121840c20b0150b02650702c0c14644172194200c1202e0303030388805c65001012102c4401040714201485a01280b0801c824210380b92440c1d40c40c60f409a400140c0b819040d9009810414404c40c6040d00700c074150ba03046900103140c0d40719440030a420b841107a20092078249003800744000c100320100100240c02895032542050b8442100c402d49140302842800e0110361300d41020081031581d840d515601560080c051814500d1ba040004195144440b0070400510006001810408031480c2c0b80050001034008100301000300000c940c1c2d40340b824038060700c2500d07410f82c0da4013040117903001409800d90000645040c86800c980c0036203d050383d400704864880c1000000f00318070350b1600c10540125016a100007007110745440f0040c00311000600c07060b100108100795810415807505050003280b00b60384001c140301160800440e88041026041d04640094146c0c1000d0f070780b08500d581c2510812280c559680d06913915140c000c4c41001e51464011602 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 653677122 1250 653675872 653675887
    0x507171603080106030f1103060d15020712110f0d0c111306050a050405060901060c030528031d07090b0103020d0908090907020a050a03051b0f0f0106062a1106 70
    0x402c81150403505141c1341403282c059802580b5094804080c9000c1c180c80080c030000b022450121a0304590b90b010b405888442c4082a1005090381d0011030b00b034413114183c0d1002c03c29158000c01080103100c031980600741d200e80b150310035625429260204410001c0940540090040b92803c103441070348028034005e4038882d400881800f500047c400c15100c2c0c01c4e40540025142801e0003000c0c8070700001450844103a0800030199144d41d8840001c3e020003000703200080080714042d086817030881c0d131b540f0051080d03601c04c0001003e442c0e0452600e10011010701d601031030f210340010910103a0305060340100300f003204040128020b005030b004081d07030039080c6498070007845000310040c4003580082d0b40d03502d02603440d500182e07075440d85402d008100303600c40800d03000464800c0c0e0141107120400c005101c0c0c02c4407840c542074601030260b1144112030300b00b20032504a08000344144c00080600b42403c00180780030740c4a503465406200040340003c03440c0d4106408020005400205203200149025110420b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 653678372 1250 653677122 653677127
    0x6020f0a030807051228021305130212190b0109031a091606030b100f05180307030b1806010e06060403020607140d050a02010f0b090c09130f0c090b0a0507171603 71
    0x9864100389903180c228140c012111818008c45580106040104c4822071070074090082045d80c04d02c1d1400010750900c90340a4844004401c0382c001c8082c11148018006645100d50455004036074103410310290481c10400200c800c4c00c190042178684c0c0714034440399104507109040840001040080088080c4041200c17900340d4840c111510302a600f24544100504080c1c60300001c00c400314010980502c04d80d90800d0014140c00360000b0701034251090346035642d40d2203400d402e003550480d01c680c085021021060310200705a500404482da03030130070740341003100200d0034a20885c00064001c1c1e1000030018244031142c50a070026000250407035840401800c00227150380c000c2c200e560b00550a02d40c8480340d018a5000304016910b0042c182011a01d500c812003503584e000d00c6003a5080b05400c101182850424840e103002c12980c0900440c004001050040111702c07540c1081034910000e011000050707174400150f868155028401d001e8880d2240d02202d258012060380c2c40305420078000c40f408255 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 653679622 1250 653678372 653678401
    0x2090103090b070f080610170403030204053d12020c570d05010f06060504140324091207030512060d170901030b0a0b09090106020f0a0308070512 64
    0x71300968907441141c0340c0200b085001c00c90007000c0d1002842e42d01d200c44540c00b62000454100e03201c1e041c0186415030341c00104140b850103a0317505100d0300419101700d00c07d8003100c400080200f5400070843c1850519000138200c030b003280075401e5013550b012072071081803102048002811400c1240f8ae0b5030341c00d4076038900e0304229a110f0002a80b1000d84242014400182910f80e03608081c02c20301c44c40c20b650780b00621010718503000b002d440964950902c50b00551349c500c038039009081d0a54900e0354582c2000b042443c403801503611107011381d000c0122104010300d248401600c42840c92030f5214603466041c0030500e8000c203039403c1894440c001400c0405c150300b040c010050490328103050b094581d07402003048010b80122002a006140d502c103070b1084c0425400040800d410141000201c00503440c02240400007580c0142d00c095500090a042c245000c03000103005194620090140b1f1602048283d00d89140000040a07c5500c40c0400c0b5076a0094041e03504020054201c0d284619010a242e42c030300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 653680872 1250 653679622 653679647
    0x3081803120d0c0801240c08180a05060a02030d0e0f0712021309051c180f05040f0504330e1e0304080706140d02120906012702090103090b07 62
    0x941c500301d5105425030003500b440e4102d580c0000611b00c240a00003441d000040380300b0400041100d403460784000139548602a20804140c0d02141c08400c03241014003254001d641c00c00f5104002c2881b07035580642c0d0000c00c440e1014062403020030010209500240782991141c410f958900622401090f415009641038907c51300071940300038560303062203002084030400d500240080d0040b00e00c0c0d40d582418040401c070320b9031403890990313400c90700c401010a00000c0d41e0481e640700c08682d202003200e440c05000e07a9442210080d0200001e003019034071a610489200e100c20b4442c800740400550140144441030510003101009028441c03200910305e0302c82400030340c0744c420400c52840c0001804c100205460990380c00da0010700d66642022015920850110107074032021340c0c00c128480345104580040d2400110001501c0207a01f018009030b4202141608500b41c0d200c814500e07282038030b400c0c19510812050040005a0b22040f06004801810f160b0384003800c0726448000b4040d100b0391009100340c0d03e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 653682122 1250 653680872 653680897
    0xf060c021f020319020307020a0b1e1008060619031a091608100209190806160e01171e04080c010b09090a02010e01020a050706080106120e070308180312 67
    0x3101c420104140c200e02084ea481008590402444860f400f1356600440e00064280100c2e110345405581c1c030780184104407000c2214080041d09031040450714100c00c0c0e00034030354548103210300342803680c840d0340d401004044920588040d40d6110361202c2204500300555000101a2440e4005090401500b903040d10f0061042c459621b4032410410210465800e655201024103207115203800104080d401240c0d455500001d10448014010b42905401e401082450042c100d00c0c50f01c031403040c25038125100c0c1841889196880704500744c2c0d00200c0e540040401d410200d08640724500002c103440c0c1d9000c25400441c20040a2000f400343c00e070060801c140e1500020f100d0110600e0502aa01d103068907188629030000f91003600543c0944010301980d1418030448000007001e480e0145000e0a0398403080c0840d004d840144681c6620040400d525804424144609250140c03040d07658883c82c44050080c6202042c4010001c1c030708801d0180704035000b011607808410014499100750701640c2c00141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 653683372 1250 653682122 653682163
    0x20a03051503191103010b040203160908060c040306201303020f03010c0504231003050108060c040b070615230405100e0705030903070212010b030609030f040b070f060c02 75
    0x103240000f060030300034943e900c902d98001d9095850461a646519810798955203c0da8244e2954842d84080d61140003901d220b00503c216054001c0c15400058212040d03c1d0040020448074101c0201110216940890700081008102140351604540c82c0040041d404000584801c100782224103074050324002c680070501650317484209400c90b040e4000c0100800e6080c0400c0007030207140c1c030b80d894500340c800c0c0513055080e80b1000042d00b104c2d85030380c00c0c83c0444d55440c01800004410003031282d00c0702e807500102c0d24007400c01e000800c0500801e4802046c060302c0f80280801817180c00c0050340200a117034191400001c9c520701c1301c40b0140007031804a0181e46401b001940e240c0141c2e4800c8229124006901c8490301d94100440711a400106440c4c803902c400c000410040c0c850708500090501020300029090392500300701818128082c1101e5420f600605c406856400008225000c03943c0c0b07585503a550f4506460144850080302402424480ca0a0300e8800b910f500880c2c01600340d200c5e1820b245 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 653684622 1250 653683372 653683411
    0xf05160807020d0c03050903070506030103031701150516031727060403050a0c060b091017060402030d030905150f1b13060c080712021f05040f0f020112020a0305 71
    0x2ea65440f49811071001070708454030780001c0780c024001419918000740c00e841a0b26150b1020981b9079100307030300403400505100307e090304080200038641d016007000395031403211442c0d03100d00a10b107000d038200d00f1048560f110b0300182014041c95000502c80002c03000da045510302110003080c040440741180d54215009409481840c2e002b185251199030725844043c00c02720b12140440b40d82070800c03021903040b60399500100b01a540d1510750342c491923918032240c0b446800c0038054198030251150b529502d51158051000580d004511940c2010301c170700c0c0005069500f030070540d142c007481000c001450051001031041140b40045001d03c40e81c0a00d049440c10030744908000d0309482074103a89400c02642c0c0c801031050900c11191200d08074002d41000c2c0c00c00c51542c9030707a1480403a410303070480545e20079131a0300000d5000089488402000c41c074100700503e481d4072010550b52018500808000c0e40085400071a030180d500a9182e03c0e004204646842c12184c0103801401c095584035000f17060b500012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 653685872 1250 653684622 653684627
    0x60609031e100b1507140102070f030e06030403090e130204090f0318121104060b0d091e21050c06010303020606010813080d0509120c0322031a0a0f05160807 69
    0xc80907848068041c443c4d102060b80b0110042d00072800c1241c988a04480c582c0c20b8101c24001703401030030b024902d100c5040c0b81e2890050040c01c80c80c4902400303041c017801000302090308040c083c42120019103a110843c0c0e030718584032a0101c031841c0001c0d441031510031644144480080c60303c40e1181f280d103400c16551401c0001005081071446151030903580d800c400700c005903001c0071410400c4009000800c1c429250103508007a9000000c2c0e0004280d9640c1d000014803404009000ca0145036141000080145403241815034840204000310070748038840c0892881c0c466001c4074503c60703406064a0b031a58480c46d00075143c00c81900d8040c0040c1d5045c0104606200c1d8614486003103078011001464451003010000140c00001e084282034011804241c1388140300000800c0300c02503410280da5100c90002c02c0c5c4882440080320000f0414280b1810b00005507048841a6002c581c4034544d80166140e50090001d01107441048400d00d0600702030100b0444960084e410490f110380362402542e550300000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 653687122 1250 653685872 653685881
    0x40b033a09050904030c0203120d0510060806060f070c050a03080406020d02060f070309050705120c090115171306060308091804030e1002030c0d09030c080a020a060503060609031e10 80
    0x29a9809183d08001c240003d00540b05207402e03030320140a072060304220020440c400d270420384803850130300e440b1000c1040070030f488100d58000c0c1859040c0a200341c00d00102280503805210500b00c807000001540302c00744020321900da0000d080c010aa0010542c4a103840c8010750014840c85000d032290301e4880402c0f60006c1010b900c50b4072403260820a81d92081021806060380b180c094070580980c03000450180c0301d0b41031482d68154040000d1460f40340c01c3c01408032411050340310f841109003240a0700b90582d448107084414800c440e0311b20840b5166080e80240c50003003042e0050542d403400000004001381d40010305140c0c20100d403213224403008031004c1520020110340090000d424245514410b00d03084210259884003481140d0601314640c0c1040d04d002400032800c0082034014804104000305540705001400c018009030554035855800700d0400312013809440b051110200020344103444940940301c2060005003207c40c007243c00c160a03008502015220f10740c42c029140d40c0c0c140300305540074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 653688372 1250 653687122 653687129
    0xa05070507150e21010906051b090d031809140a0c05120a1806140603070605130b03040311150f090d050913140103050d09090506030c040b033a09 64
    0x441c4072900d00c0b0f00c0c00300160340c11a119054000485112031810380002440703402c0105101f0000000d00e03041002910304007625030071200c0030f9510100078110f1152115070b100c0c0529681424001140344980d134100c009107056400414000f40380c0140392512141e55001ca42c003814128000f084602c02c40001200d261094583d141c0441030503a0100b2448009540700c180081100803049040711000d540d10403d496015000500c4501038005105140c941032100c44021b2043c1d0500740e16049155583c583d012586100360031100401000040a260103514003001085040054440110f00103600394041802966000040130405002440903d80018160f0200900b034407010b003030900b0b01c404c00c2010fa118001280345140c07501d41060011011544c0c060107144500c1c0a80004c01003100020014642580304442c441d0409003400026100030030030120684068a000c0740f0f004812010915010a050f500018a43c400710654402800100d440d5a0003000d90050a4007000801044408011074003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 653689622 1250 653688372 653688377
    0x504032304060801140d110102100e031309140114011e0206102907081603020601080d08131401091209061103120718080105010324140106050a0e060a0507050715 71
    0x42c6d0074001c180c0c0e08600700c2448805204a5424200c10004e8805640008240e60b5690f840800d0070b1a0f4480e16198520241406d10010011320304240d000d10070b828018800c2461406422842048503407140d405120b06030f00e4442a101988080400207544440845081c14010310603440403c00520480781c40e149652012001c0c2a40400302c00840c0c5241d0162038121001c40d41004202c10964606d9080004217010380c000d08060340c5028030389130910710142008070030005442d0810044010240c80300b06a180c0061020743c6a200c4054014014401c0b03840241ca444408420b8450840c0d0141043c0281c0c1c04a955160010030480642a62402090303101034010000000080c01144226240061140e9030448001195502c004180c00c41d41c080c2c0042daa000132809003603014080c1541c0c85002c1c0550120108207005401614605082060283d58200100055250301182c41060000c1094000400301d5a03660283d41c0c01502d01e5000100440701d6004060300001c45406c1c099010702c001c1e0698 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 653690872 1250 653689622 653689639
    0xb0301180209160f110c100807021b03100f0902130e070503011103372c0a080a020c0a08160819080a031811030c0a050f04050403230406080114 63
    0x13550644400c0000245141144941000901c0c3c5568241d010b200c505101e89501d03800381010391313000342805045084000c0b44074100890b4030064400044129903609504000074102d84c941101c8000380900701c40182d0f00440e281c00c41c01d6a00260b500444031101003008551f8516540c10070b150a81c0e481400c40c4240c01428400640f81080c0240304d03141c58402048030b8090f101040912010710b80102d01080780307d56607221030031380c0c0200300c141108204031074550300245910384000d2142c0d243c4440e803004216007004030318181c465000b0000c0f0134010100a00c95080c0c84d40740c0461355034400703240400e1700a203094188001a001c40221b6544400c064100d03070724002644030385510f000d40e03002da03050301c0c101980c2d01076a00d815685210456009441200d031107a18800c1d42041500e001200e9034610320411502c10100841d955559603030681d40780640c2d0100d0940d6407800d0076100c1703005149411804810410b81c505012103100004c0c820f0b0b481c1c0f0b0701c030180c040c2d0702d51004600c66082c8800e42500002d01c1d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 653692122 1250 653690872 653690897
    0x10902010206010e10031202010e010513050606040f0e1509010513032a060609050402131104051903080f0c071a1210080102040b0915031314010b030118020916 70
    0x804c420036621403403a5191150466903039480c0d034610340e071034184040144d55454160f001d00d502805620342088002010031010001601d40e16150b44001c0e29031807150b03542d4002c034200308115400104403400c00100761030a00d01e4058080310400340c210356106003035180c80005040592606c840ba04402d8041d41c800c0948c0350000c40b0410301c5104a0902c2d000300d5003800c0380c04001840c50040d000504003180c804500c1d420540705005016220b0f1030220511f6092800c60a200603c1600b5142110340854800ca590700101c0f090b40500d100c560006807044000194580c07400004000404c0910400381c200c0390302d03550396400031000d41031410380c600b42d0140c01c11206255110605509802c010056580440d40e5511202507007280e0290780480312092020900c1400c0b840e1040342440880d20780711209141d4603000c54190240200705a0062950780031258a0210381e009500100011030041d008100b2010300120082400070081701c128410311307045001449804541201d564800040e807205118a1036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 653693372 1250 653692122 653692139
    0x8160c0e011d04030e030a0309140a080d050f0c010606090509010b03190e01181103010c1d0607050a0c030303140c0c0a0305091c0f05011d1c090909120206060301090201020601 77
    0x14042e00a4042142c281030a02c803a44d028130042001c540300341ca5141d02140303092b041410402d01d611042d441154002010042e0103400300b410000b4070b81c10b04d01a80d031a407900030058954060050200c185602c4c00c280803c1c040d810031301030300a5030011104600c0b580e903580c44e495600c0c401202c6602480c03003800d145a036008100d030401c061b40da0843c8004140e2400300d4400004a01400d03000750f4803603010fa5081d4a942c1403e2040b08198011881e00090540c50800f10280490300c0d540c805004002c0060319006008ac180001179404d948a8180c030486035407810024054000382101410183c501d5010030a01c0607607000300d50915103c00040c1294503c0350300c0640c0c1c20340294030442c0d0090300014040c071841c0f140da002000d81510400000c0c1e882c01150a050342112a4544141505021808039203200741c800106046054074040c04400040c0440d4801c961549150340075103445800c1c60030301d80030011a8905001c580d0070981c201d600507520141013600307a034072040300030b40580c000e14014405204c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 653694622 1250 653693372 653693429
    0x90402010c02030118060c0f080414010603080a050406020c0108070f0e12100911010216031407180b03060a0b130209030c060a0206070e030a080406030f060308160c0e01 74
    0x140141000c204035500d0b40c000c03078291140800485210804030700780e0003c1014510607000c060041d45041d10310b0700c10401e4040d01613034000e40050a0890300500c50310258109400c45c0010315480b541305520741501c0741d4080c0668106004200142c02030020007109944582e1005125150f242e5420240c150403080588140301081ca1480d00180c00b21107082811404100030020030405000000b1541420b0901410007240c01c40028115008515601951b0220610301c0c8160b03908a50080654450741101500d01aa10b52054010480140c00e0300181085580040f561000c10b0f8180d40d45030390784103400c07001c0b0359080e010240e0000d49488604517207441d03903001d080d6001d0081c00300c480200030070000030283e4008110b86001a8440f6040207134460740f10b0180511500180e000b48459821640c0340c0349113020703c0c00782c0300030140d850680021050311508070740d00464000180703d68030002003121040003100010705690202c6034580001d803170300b0090300050484840e011a5844220000320707040511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 653695872 1250 653694622 653694631
    0x1502120301060806150c150108150f0a090c0b0d0c0807081303030902030a0b011a030402010c030c02041b1101060e060609150d05090303040210111e031b060901060503031809 76
    0x300c1000c5c0040118260007084040c0301d0b08001c5c0034141c2458240500a40140c1203410303a074026062240c00203045504c42c640210040c0d405440c81d985d40d6135842c0091905440c003034680d050340c150008400352490010480c03180a01001c0c4400601e0b00c906a5001406440c5400000e115600085140400f00f00e01d200d07e41c824500400d410b55990000303450300510050580e420f0390588010400004510000344001da8107508203404c61900b5000602508048613000d0103020881c0300300c104559a55214801e00c1c0c0c58511603c80c1c1203000c402c010000140203a04008662a20b00701140802c810f41445100300c8005101502e080070312400c2c80030b10840070307a000501c600103014490100016018452041e07031501c008584070b1500340104008070480e41e00c80b0b400d0060aa03085c0c3d02074074010a2100c03100d03013049a540701080d1004070aa1962040c003000406201721585010a4040d0108410b402216120001d0022039255000c054a900c210072401c4a031403240e006a20f00380c14000e401c0381d4032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 653697122 1250 653695872 653695879
    0x80906010b032d09010c08070e090417070302010b0301060f18020c010e06040615090203041e0201090512030408070506030115030e0c10020c10050c0304051e10091502120301060806 79
    0x8202e801503010b01c2e80c11216200005180c41410825424001d1251040341b40c1306107000101820108009030030301d0804001c9a018502d0480081c1c02d000d07501d856410100c0c406c52500c2e5a071589410020300908810583c03900c203500b0041d0003d6446000c4118000342c41c400413051106020100340c100c025402018103003004d5485101d45490f4500600c102c1c0d20a600685012034100d88003412088085880c0d0000c401c118818030a0001180030b25120301c140742046c0200700ca651510380010703500c0c0c04035580401e07802b03407928500944400b00400900200d549a600300da51b40d03603c900804c040350109001e0400010101ca8107181e595200b500080f0880c40e250080c0c5466074950380110780d000001d032580c20050391004540c0a030b9410306011211002e003051030300324144219521103503160701c01e0703204a0380300f940a00d80e41d203400d10a042d448411003d004041350031490000030054840c000302d11920500c520034007840e0001d14004580c911601c90071364041da107961b00340038003a80c090501800d071681 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 653698372 1250 653697122 653697151
    0x30b09010513090f0215030708090d0f112e05060f010f230417060601030608031b070e1008060108060c12070509030a080d0606020c06030c0306181312080906010b03 72
    0xd81c48051454240c803920740c1c080c947da840d0007070000c0c18a07000a000c0d444d0690202801d08460795015104060000325460142042c80c401c0359000c0ca0004483d00810003c1d425014800340034aa4041d4000daa0400132010f00465460408100c409620205064085000d600a103401140b00f02c06a65000c441007000031141a14542007501542050300580b044a031010034202c41100308200d600da100c0e0091a0500c003003801c200b6503685a00911010324240c24003000308649208040c0034100c0900080c2031300340c0c010301d032078490710b054050701e8862125180138820001c501503402058cc10f10451100201030300e8991501e280c0044030340002c00ea074040140501c0940c10f903035002c3c04039031402405029025180c00161000d0380488003035612034030540d4882d07540c8111a8440c0c1c01686c3d40404107010103500c030740d02e000c081000c2c403102506403210381c001e810030005030305000310b00d08080a00444e0b0301d0600d82c42c404010348a4440503680410303507512220040241d00100700c01182e008030a1800c0b0340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 653699622 1250 653698372 653698403
    0x20c03040e0907091406010806190504110408030d0212010602070e19020f21070509090f0a09021305191a10020c1309051006030c1202040209060f030403030b0901051309 74
    0x1044400751800302030000d800074103000c02903078808c201031342140003160a0050040315056098885090388903282c05541c44821051031804010144c60080c0b91000c19644e403a810001c451009500c21020702c050303004000300100e0aa440010380c42c0580303010800408258032000700c1400031061700100c092080e5020491040c101e0540c170040d1441c106544650044032026022099107810000c200c541004018808901d66a80e0b0f01010742c1c1240c1100400100d030b403a114042c1c400f9015040b0040c0d0403a00c245ca80c0e028020b49a8089889004000c42103030351401c1c00061041a21010584100300c0c00c5001102c030b400b032900c40684114004280125100c074040e46000c500f000f108d00c5184038256944001e08410700c001402036040c21010140200101c074110303540e14620b0011340c01840001c107481c1005804548542c3e044038402e4400600c075030344604d2450dc001d8040e50040740d0440c004ad04011940b4518280500f18505030303480100f000a5000d02c0600030300041820600c10398020b00c0242c040e2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 653700872 1250 653699622 653699639
    0x30903031b090a0e090601050105180409060e07030308071d060f21010b0406090e101211060301090b040f0b0a0b0702010504090609050714040f05150c1618020c03040e0907 75
    0xd0002c22006144c9019071826034085c03401c0c43d00591010341401001c00c210204c0c01414a4640c5204604070b1b0700003010289420000b0040c01030300201d1b00b6910450304d012003803542105690b407013081281d0340c4d020708441c82c40403030201182070454950811400c1c011820b030400350314054201c0100385024070404100310001c10000c044d00ba4400311501d20000340038860f596001c50f075100504603031811282d56080030500c078500c1126600c01d9508400300c000d0b6030000c0100340c8100c8415054010405a280c0d61540030f80402800d0000c1260f10892800c0600d010300905802074842c107050044c2010f40140c60811207410f81e51101c0320403810810108008550340703140e0701c20100501281140002d035880d10542c00340040d0380d540c44030045041c05000400c1190b004017502d80c140c0e041980e00080d10080030010200300d0080c00501003e038060b20103200d4019a40c0261031044401e0111a425100b00c181c03a007004a10465603502c000ba0002c10042c801100080c3d15183c224660104503800c40d6a6003a40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 653702122 1250 653700872 653700889
    0xb030c121005040b0d17033304140402030a08130302060706021908040804030f020f060d0507020c0a0803091009030515060f09092e09030c0b0903030903031b09 70
    0x10800c000300c010414000c50810b48202100130703005551560071400355446154045203d0f40da0380e40d800c0c0f00000010480314a0b1108120040d01c004040040d1081805000b403c0030f41754242c0718012071030000e040c01c0e40310644002c10b0140d5009400b40c0b488013256144c10729541c0c40701c0d5403134003150b090000000040c3c0b640401040e449000741401a03d801d0307030b00c0300d07d6054418441c030001004107020a10000c90040d800b1901141c5d440005907007110b1040c4081080546080e10441e8030401c042605509060550000b500c00d80f102d50030b60b050500c0ca0383c104582000c5d035002d844402c0e4424840b040b014200b400c110710b807040d0103041c1100001d03174a50700c99140402ca107203008906003808051002c94204000314042c804011140c0087d549450600641c0e25048050b00e41d01c44010040380c90301a43c16000b0030101d68210342c1c2c092160078440e04000d0860644124202c5081100f080000c60a41c004819240504c00700c4010b5481e5403508101038080e14015a01c8900d8070100300055400340d0781b0440d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 653703372 1250 653702122 653702131
    0xf06010e130905210a0e030a0c03122703022205070519090303050702090714161505010f03150608010c0306080f07031221091407080f070b030c12 64
    0x8042040661483e055007010b150341c2403101c450103290f00010010000109445448005192203501161100c0001e40b50101c9003a014009000300d270f0002c41070000460601c10601070341e407210359416801002072481442c00c5104005001401d160078001807500014024003180210000240200f41c80700c00402c840080c0e0350540817070000070f14802da541d01c060902031501c02174101000c134a440c684010b440d91081c804001d11030500500095440703801024815141881c0d60f03120f40e00c801c4c01d241000f0718800b000c2c209484901c00a50b480000b0075072405450b041e100c4806140004614503500d117804030070f0b441c074080b00749503c9220205a8401c01d10801c1e0810b802c40c3e0340819000d250040036400c09a8403801e00c50f04e901701d05170610114000d045070b5003004841c2d1511400500e030212101c5030b40321601e4080b8203902d05100e0300710103101c12080d00440c0d50320018152200c2a59402480340d13900180a1112141e4000d400304010440c0d101e4042c42d404003900c45100d00c0d1011685000011990484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 653704622 1250 653703372 653703409
    0xb1009050918010905190b0709050d32060703060b090a0501050a2d090501032d0213030605011a070309050d02181e0a06050105030c070609020a09050610030903080f06010e 75
    0x6d000030203200d0030494980c3c00402c18100241040e0600020880d80282000c0107091202e40d0340d020905480c1c503540605014035014080c00d50941c00d5002a0b844501c1a030f0040300080c1840d03004203041a001d4201e0346614402011003e40b249070600644440e00702034030103018070904d03003005803044258009c103807612841c4c1e010034181c42100038000381001c00fa075002241054036250070300c1c52420303c58501109001c58080003040f000400423040740644180070710581020780b060000010403080f900041e060b15564403604403800d40000720300090780590000030b40041d00d007000c204640c1c00c0082112410a0001e440350440d1080000c0045003040306880c1c1442c40031021101c8210121554000ca8000034011000d000300b40c5424002811400080c1c1550340c81c01000500d94104100d0b5030103640c4040c1d010704052615030303a80342a00c0c0104001c07a842401110181007081206200b44601803026905031502210354507542c4240840c1c0390003c000d02d0611001070300707985c1587d9403107254285401c0d015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 653705872 1250 653704622 653704663
    0xd1b17461202101127101107150807180506030403051c2016140307030f030207030807030b040f020f130801090b06190504020d0b1009050918010905 65
    0x340c4024500350f0f9003100700c0b03561480c000b8501c081c1c040180482e01301d40301900c10528000c4083c0d80096040102012240d48144120079140005400c41c0d0b42c01002d10920f01501d405590701e280500d100c41c810901d40e0001a12500041c90641c01040001500321a003403234441025240c0d80491141c0e441030b9801da000c10340100e452011000e000d80412074069929200f0305c00c0f280c181b0051669842e54040d0700c2814540465000c1c80b40c0315080e0104e8120390002c1c2d8112a01480403e4a40c0307940c4401001e80024100e142100480742c064001c0350700c1290f040c0c0d2030500c0744da61800c0c11070041200c4c1c03410fa5440342c1c8410510b00e000507a4009008080400c0503034540d203035506800c03005200c10681c0880800d0341020b454901203022a13086a0340110140c0c0d21100300d10a0720340e501c008068a0308000e601074804144000c03614415031140200042c1030303440f2001c4100d2284103440106440c0f2440d0b5010303001c00000b0307044001c2d1a0598120303004520010400000540d43d69090072170415681c0e0a01004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 653707122 1250 653705872 653705903
    0x10207080706060e0a1109041a1804020112020f040e041b03030818010912080709030507060207061709060403050c0a02040f020c060f04050c09060d1b1746 68
    0x2196040d500b142505c04200030101c1c201c03055491030b005200b001d510541d5205120324162005154001c3d544400510100c6024555607807584120001d031410b03030000b0840c040481c0504102d10840d40d8192005603c641401d144c089500e1004030000e004940e0344080a0007006202010545032025510a48881c441443d120a00d40b04807503411602810741da04014060f40401d040141101e4402e800b407903c45a2a6203100d010b68079092a03501c000c1c00c9200d151400100242d02150060680340c5560300c0c02c0350941120940c0c25000c0041d141c000441c6c0000000c41d00003402000100b124404900c180d8180220a07000541192f0341c412072881400e40003d0400c2c01c02c0030034400c10b5840742440c419948142002e4480a82c0c50000400c42401030782c0060110340140c0d00e1945400d0701660148001c95220098040186c1458080c0300784006e801c0114403001041d00040781108901520800700c90b940318000302041b049445120459600c42d51500782001742582510001d01000e002d0801300030030f40c61 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 653708372 1250 653707122 653707139
    0x316140a030905090604090f020607081e041406030702190c0f08010608010f0212010603020c030f1b06060102071a180907180605030103021e01140313020315101701020708070606 78
    0x10040405e881180b41c2070640d80005c6245a03101c0340c0f2501980e19130f0711480b040c80e1180403403140a1002d04015030b410900d0b61042030850080003078800441c8c4801c0c1070b20212080c010140400d40b8044003581000142000f6406900b2603204a64003a0b01d40d00c4115a958800790101c080c6034002d0702099450380710500c58880d0901880e4103e2150700811443c3c2180b61100c0f0320b1f02c20041c052002056000500441c6400007001901c40445c400c6006654419140038440710740651011094400d007e142c000070550f43c00446c00004440b0700000051100ea4a0810741d075441d4841c00003803c094442031803400703064440a00c0288103034010340300e015054880d00554018000f030f590224081100c10001840181c80b030390340d111104038805003a036001040640050315900210290038005480110400c00c1e44d001c0b041d4000d900ca80281c040d034510002c00e035800b001d4005c00300c40b0b89106d1002400c0c20444c1011425010707980c0b090b0080014201030700b90751134040c640e2114109855aa440301014000780c613 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 653709622 1250 653708372 653708389
    0x9080316110d080c03090c0406061d1207150c170301081c0203040501030e01140705030105040b01050306030c1011160e070201090f080f09040f02030106030605010c050316140a030905 80
    0xc4118010a40b03a4441c000080041c4801800825903c0c0f000c0301041d2889010003035506101401001030140e2902d4400080005440d070401027000c200c42d4030855561305210a42001c0b100c00c0382d01801e801410040e842c000030310141002d00805c5410284000400c9c0c40905882c1c0395281484d0541d500d5141120b4645030948072600182a03c005110307058034903400008541c1102e90138240070a003151103031011801001e0f01005910341080e2070302040025517005004505a5008036002c20001c00400d004469500003102c041d50164044490f0305000d15011480240482d101d250044040bd0541c00141c01c02c2c00d00700821190b000f030201c0501070744600810940c0e2001891008201441c000e0300c1e08540a103000d400500b44640002c1e4030340041e00c88400f02c0f0080e40d8043d0040c4181003104990f18025402485144000f0b49801c002040a40c802c01c007030812660490000d50400031500d144408095022008031440b400b8070103d165848002d01003103080d280207454500342917203008241300424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653710872 1250 653709622 653709647
    0x5030703031119080403050c0d0806040c03111204020f12010e0d080c03070324030309090507020d08180106030f0305180f0d0b0604020c0a051b0a0b07020f0409080316 73
    0x101e000f4051410405424004005181e020f40341409040c2c595081c02d85040c440c00c1401006409258081e40a59800c40480360081d00d00790381c1041b600c80e40000c118108d444460342c420306c1d00010007880000f890b032122510b80081c00201610101c0720038000155800ea90031003064101d944407818968a03c409001d0140c0000d40c600340300c0f0952400d264404080d00c001420b01040c186d4035686540000c10500000007807140c8054422a44ca890b8100a4450041c601c03900025a040000017160a031000c00e46440c1e2900c55118094030382c40c1d02c00384100e4010540101c0010359070700c110000200300c083c1d0780d0a416a010380c503820b6680c00401e0450300301205180c81c8501409034100c0700d0003141c956220000e0200e41010b01c4481607212100007174043c0c860700500008602c0364044070014000081b5601d80484024013640e001c540300d00f070074404040018440c41511007024885038007d41840b4010020100b0018030000c1c1c4c0b40301581c4d590165420540b1000c008100a20414031040d40081d80211071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 653712122 1250 653710872 653710901
    0x90706030e0309010e190503060903040905100f0623070f05011a0102190201020a0b0a14010603090c0303080c090d0803060307120203070924080c0a15020c040c1b0503070303 76
    0x30f120a10380082d0100b200a681036004611a42c9241c030080401b0307244070302030320700141544c1d02410030b134001ba50750390450701a41c21703420b00d0400400c0603684a16502c070200c03032000c0720705100b061030300d1416500702c0c003a01000c45041440c002444151929640100041c43c4541100841522a410480e0844a540441c0e00302c4107048940d411240e038000031004c06004200c07002c44003500e1140f0040381484000a002040d801c081c000307021800c0d0003034000c41140c400070440010107a90340d61045055500c1142d01425031100044144042846902c1a81d4000c20b5440e0941c5002e840c0d501042d103c00c00303813a0648141c20301005024052509208120080c0340311010700012440b2a00069158150f5100300c420b07641d1345865030584180a102e6580442121a000b056010b0303403868100d4072030340d9941e0654818141210041192200030503809840d0039264004c059003140c00091100501107190b610080c8142e407216071b00c4011080707504118181c841c0003d151590402c1ca0041c00703a98500171800d81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 653713372 1250 653712122 653712127
    0xa0501141e0601020a0816080309010c03051b0405131103040f020907170604020a0c120302093d05131710090203030a0c0813151101060620070e090706030e03 69
    0x410f030703800522514019040000595113510142004e54006040c1d840288403e01c0481042881e031410743c00042020303c140c60600c2103960341101c41e10005031050002910b920144414090ba0a1518885190040002d400222540e0401301088140c104640c2195040040e449803400c505000320141d4001015040001c441002400e001d401050010641c50203580c1c00304005603c41d12031b480e003454a64000300324000a0341c3c0d40c00020003944c002c102c4140110340c1c8005100041c1c03804071480910080901c500d480110000058070401c1800d030900c0e00420005200345003404d00d62003141401098005801031360541b11070019420000081d442172005c0303140440c2940543c03404011559421000d1802c20b106410354a000c05071805440c1c2c1c02040b29403075100200c0d00342c00c40c0d8044001c4444641314548020101c1118500361002d03400f0341e90024100129102d0210100b0401c4240080200d003907441080e101d070404d103107440c0101d504401c43c3d03100480404c01c250b00b610402d4100f8127080003851 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 653714622 1250 653713372 653713381
    0x1e1302031b0a050f0310061e0503060105011205040f1205180306041119030b01230f01052706070309230102030703051c0903261e090a0501141e 63
    0xc0200080c2c1c8290f900a0b01d8000c0d450580c4d56017844101102015148100004c6850300c081c2d444948400c0e402c0308455103141c1003c240f910300081c0583c100c0e00c0594814902e035813804c4d450350250a0103001101c48200d04c007121000158884a1440898580e54805441d003107040c20609455680510060203500b245052102258421200e0036402d502922600e0500780884010f0315a2010781c2c3c03000d44400054800800c00341000c044204415142507505040c0c041c0a4040004101c10010110301180781040303c0042c4c0c8082400c1000120945054001c1920303210340481d41540c0011012030005403051710520200e024030f6000803102000c0b1600d508411802c01c0081d6491041030000307030910002081500400607810b504802114580702c00340300e40f078032900d0040c0c08402000f44100410004903121003150148980c00d512440d0b00d0038080d270050b103030f01e01b5101d0103500142022003e40140070303d84000c030b482401810314001c8104a60006403425070f8071441d02010210514201d10789800500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 653715872 1250 653714622 653714629
    0x140c1914040501050c0f01020d0f0e0c0901090e010f0504060207140312070815030318030d05120103080d0b060a020a170705030306120f0a0804090f060303020a03081e1302031b 77
    0x5606540b03003130070420b544481400b900307442c007180da04024080303600000f0269503151031504242002d80725203806200c0b201c100014261201c0c4541c112a401064400040001130181d410581c2030325040070002842080e4070300c204003030758012142625040d400242503000c000b0000fa004160b41d451001550814000003281c01000708003801d08800c01040300c010805401c04041c0d0250b41c03c50082c00c480d55240302403400c80c0400c0c0190307803c80c8030340520070074924074500441c01c44d20400c0ba40441e00c040c5a00350390b141c12503608038210341441540d03102a1a20a621820001d0034064065002001503058525010320081c0d090301c4510707100a0140201e0000a0001050740c1e0401001c070741451031188140b500341c0c075020001d071140e0014444c1e1084c00301840405001001921840e4100b4000c1d04c074284516420b6611911004005070311589612010070b21500036941c21907441100c3c50000c80646a02c403424500075281740d01041000d080c01001c600c2c08000b41480d503d015010200c2140608002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 653717122 1250 653715872 653715877
    0xa031b14030a2703020f16050d0f15060b030919020108070c170301180608070303080f0709050402030a0506041a10050a110303090c0a17030a030f140c1914 68
    0x80b0b1a150700d9048400418618441d164560310101d100740b40b01d401c0905001395280b003a402e0652240c001c0c038144c118040011500c9200340c0318094034000303c0c5e4506030348410480d44030060984203845000c035a42c40307101050094100802d0020740031034807801c000d0a92410029030304c2d000614407100200c42e030010b0740c00c20a174642c01001c6081c031100d001c165081445401c013015600c1c01c049003001001251039046c03112003031744203240218100849038032001d0b410b60342c689130300002c6c020560302e0700050500320800c0d000c0c4d0381c0b1034a0351070b215034250341d5600440c083c1c0c2c00c00d540c1c03804400d031500200520f40c02c061003105503c3c0c0c080360400d9405060707000070414485c85004140c0400030005201640d090244803000003003403207041140e40c1c0749000ea601d0f03070b103941e58500c5880c030070342400350001992070f00e05000903500200c01d400b65140113064041540100101010506d07910f44074207240f4039021700c1051042c03003022040c0d40c0070380c3d4452a0301006040100401c003403051041c3c0c800e03211980c601000c10b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 653718372 1250 653717122 653717131
    0x9080703021e130f150b0c0715020f0106080102180423060126010e100e01060507021f120b101403090307020907051314010e01030f110a031b1403 64
    0xc1003011100400040390b88a80072a800002140c02c4c0200d03100619030b02da20020040045840000c4442d441d101ca290307052069040d411440d600501080c0b101520344088000400c4ca40c0c0100c0b1021540c900189081d101a03502c0f0802595000c650501d0030700c048100194240e80848042001c0300c48042280c40249915400036a8803281e0b000080340c0364000c402c450f0042e0b6480000c0c0c203201130200c1d000c12a9240c04d00454600d004a24085144168002944010755400400c00d0200e6802c10750100c503150000581039a101811743c11291005849500c085c080c01402c1d5100501e1400c50300200e03042d5406070a02c00d0060040c4030b240300c0b07440c0c0e2010160710340050b40c40d603a41e62600c64814540c40d6006000c0080e40c0102100103105840750800b0040852014945a04c0700d1144e84e01500c80104100d2901180800c054006044045d0300c65803041020182d640d10004803002e000008084a4020032041030109a0321409884007003590340040ca4038007040d107401002c40a4510070751485000141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653719622 1250 653718372 653718409
    0x30b060f180f0a03060902040e0a02060412020102030409020c03124209090714032806140112060e07061b1a0f06011704050d0f11100b010908070302 65
    0x21a404035980340c95030406000350041070600300f00c3d16414610b00503c0c1c16081240b042e49029078104807803c0100320b80782c000d6001403215003414604807040d110803030944c800b01e045000410011400c5c1c085807014000314600b4000654441010010388802a41e0242081c40200c124052040c18005e003d96201c0e03039150180a00200525072190003030020328104c11550f40a00910104000701070b0000d80c0c82d0031290102900614180030390300741501d070114044403180145803480a040c0c201c1c940c00844141038841c201c002103904040e958400d07034400a80207103103c000000203113424040381d4050740c040d02d04407501501d401881c000c0040d017031003032600e45008270890300001001030000014a221410701c0d00c035245c25861500c040d039a06000001c8807900c1c003241c1c4a01740041019042d02510740b00b039601400505009070580416544280802d03c80010018000c0743e500358030000380b089030000e042414002c161000b0358000075002c8078081d00314207003992040900f000540d42c0c4555207410f440005e03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653720872 1250 653719622 653719657
    0x8030301091104031217150d06050601050c0706090f0608100e06061201030501060e0c0903120d23040204200d021606140a0c020a0201021203130212060403030b060f 72
    0x580301c0e560500481d4006000c5d00104800b4241c482d0300185a17204240c0307050443d02540d95000e400b141212034007801c0d1a004140c40b0764410010304641e000a402c00f005042040c1003450300c0195a28095164000c0000103000d1801006038511a80420001c7c00c4142861007092404c1514040d10000317510500100141c44c0d40820081c0d03c41d141101e444121030100c1070450b60712403c01178041c1c846842160041c0c03403200c000802185603001924209400140507000030321000c042c1c0781c1c0c580c10906034480099560013020701c21b001752070610951b42013012000d1300146018010001202c0c0100300c1c01415030304005040080742100c0c000c440003a000307110010b860700d4801c980440c221280c0000100714510340a01141d45010300c0340104c0c410420b898040c003c41100f03035012070b15103140c032600030302607801500e00b2000650844051070340711101b20010000a842c9400103020b51645414212841d00f145043c4402d15600d8018000401d80a0b00c1c2c5600d4020748010741c1109205941e11400d800c0c154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653722122 1250 653720872 653720891
    0x1060e1627080d03020301050f151c02090604080105091e0d05030a02130e040c0f05100c02030a05030f0a030f05100902070507080f070801053106180b0604150803030109 74
    0x108140702421100d401c0301c030980500e00d0050000d42c42030117642d2050080202c0c014a81c900800304012401c1c808503e80d05000040e19900541c09141c20184040f03a020b0140d00580e8a89101620003010440008203003410103100c0181021280d948158003485004405085101c0004070f07406920254a0300c15078a56070310049100901421100c02d031440c1c013506c1c0002e03000704021010b07802180140d2005004595035011000110018852203401002846608000307038068060201028000b505841900c20142c3d030305030a640c090104d0b2580c20201144a4154503410701c50307001100c900c40702c10011410301580800c0d000100744507040c4c0b0a40c0004d5101c08200c1e0174403800f0020442ea40c104d40c1109184120729072210740701c0c01a4046503207800c0005a141c03a9000385148115007524960b89030b420300040031100c444c0000400c3c2d9a541d00d0703580f0380ca01d11400020b01050203004040526039400c1500810058810700f02180e0704003417000009110540020040744d044581480000945800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653723372 1250 653722122 653722187
    0x50715061a251101020d020d1d030c0603040804031407031e0203011b0f170c07120c08120a181104050a1413050c10050a03050402180901060e16 63
    0x580001c2040c41d400d80c800410040c8194808042c24001d07000c1d44c410110400c1b0403a9640901415500040d621100007041140e60094040300303202c0140c1501c0d0965100404158150300548007110b90420004080081c054081c0041c8824422400a490441c0c55070700c8142001d41803140024ec1001610107035001c65a0075403080e8090340b0040e121040000030401c010f008103410401c1d440c0401e24403400354a000d0071064000384100e2285504906255094031200507042c1004454014000c08071612404202204044c007040c3c509044045080c0c07410090344030a44400405e01c00c2400c0b09000c2c10030001d0010028200c04030381c01d503000201d0b40d8409248034060004621040700303016002d000e000c0c5c0021003201d52040704c0d01031000c44e0300f0031042c0b400303000c0340c50001c069040000c0c07014481d010b02544650045500503000500d10f84064203142020703030905d0410766190000f070b07544070400c02c04603540740308140d8013580036503403c5c800280c0c4060180110301003075101d08540c0100001c420081f00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653724622 1250 653723372 653723407
    0x711040213180e0c0102010e1b01020f060a06050102070f06020a02011d0a03050102031e07020304060c0303060506030a0f0c0e0a0311040e0f061005030a081c0f0c050715061a 76
    0x3050024180040340324a0b4060052a002e0440b03000c90050200d142d04c1c550050180180b6000d00034014000b40d02d0641d0f010120310480d4403400c1c11400fa070704a00d0458031003041000c0c020304000130001611792a1000180c640181680301107650400c20708108207254010510850b03482d02820301c41c0d842a00040c80c3d9500039584a0526400065007038080140001503014502c01d141030813481031181c20040c041c139483c00080398003d0041c0c1c4100814040ea43c42403029040c124428140412955180c1300040c6043c2c0040301c882941e03640c0e641c081d10000b0106c0c024417103203141301d0609802c5910420040340701a01c960001500b0300c2d24000404c42c02ea100e6600c669943c071444001e030303078031032001c0e00307103a03466540640c1c9510500245440110f55482c4c0421541c43d00303540180403602d00b9402c000f40d02007101c1042c060307050aa40e12480307800100076500030500c20340c03070a558156850351540780c4034040403024540e180c0880d1911806025030503200903012101808100602d840f402c02050498500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653725872 1250 653724622 653724629
    0x4090c0915020a02040e0f0703030c0f02040606081e090c060f04091404020a140d060c0e030d2105150904050a060222090e06040204050709090608210711040213 70
    0x3411280503021101c2da000c244046402e108850600102c000b4045465440703545450521198014072003c00c00240280d07651a40e1511070190b85100d00100c2e000075003110002c0c1d1258020582403c104007890050349ca080c1e4005c0e500354000061400c0400a166407181e158000e42d0084000040740b1070f6102441041d030f0002c090100060190582e008140112010700340e6017240601050140444c4241d00f0310b9003040340140180617a10041c41c41c1c2c8410010f4950840700d8018001d10701a0440799440911148a501810f07840700b02c010500c000b11002c030848070701c0000b1009880d0406010f0002c0c00308411450003082280d1040d640d440b2420326a0804402a00044c643c03480001c400800d60b09410001d01030400f45031504184640d1400c0c07000541c1c0c404042c41055403c010009401403410350702c03940d0040042d180c001042920f50887c00304880f40c9401c05584d82c0c0c010b090541c0c4014009a11003183d8003190101c60902c40716076103d207200f8011221052140d84c0101e0001d1141c000620610001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653727122 1250 653725872 653725889
    0x3080310090203090c040c082a0705030307181703091212040f1a0304080d0c111603050106080703030c060b1c060203060a090203010f030825031e0306060504090c09 72
    0x180c0c180303500c1545e0f0742c10403a040d041c01542058200407480d80507201e124400c401c1d01c1642c20340d5010b117400035003402e00240f0480700a44018030403000450740c1000510b22800140d141c000304088107521101000c0c800b64015802480c2d0080010094400841a690741c0501540c104c04019039000a035401c000f8038941e00d4426141c04500050b01c440f202d40b060b412241caa420082800d02c1c1140c815503c0d110844d4007800300c0074208040c541c100400d91001050b4915454000b000c4800900c03034a08110344414100c1c600e180d080801d005000d0203100c0c0e0802401c841000344141c5155a90140c01402c0c0e035100a402180c1c3c0c3d0703014000341c0d29850081d81c81505c200341d042a2142c10761034060001c0d0000e071400744c09911712002c0400c00e0101c5100710786c184e5000a15400d84145540e070fa4141030b80c8a01c4c02c050a1100c0c440a0140e286000c241e0a5070719031094071500e2040c005000302c1040b03400d070840700303a04040c2018010454282c00c401100d0031358001030302c007140004810314103403592001030b405202d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653728372 1250 653727122 653727127
    0x102161719020604172502040605040203100317090d0201080a0e070906080d0320090315010f050915010f0e3f01020f0f0a171e0619030803100902 64
    0x190b40c003094052040d80b040f1800e424a42c074030a803020407801003081b40c03011070544115183d103031403000c0f050310360151000f8008960750341c0305c00124050b40c0090f0303070061540425840c18010010b04002c0300c1d5a80503e03030002401c1050201c00288140c0003d00040d060002400100d5580c0449070031126036080080b08a4001e159211854030003005030b80f10708200e60140c9490040000e102e40201c201420a01c40d406014012000500a1550280301c0642e8588502c1030040305400c8424075aa000b85980a03c007603000389048144420080001c084101010401520450303030b80c0c2064a14000b8580c900d07081001418013000f10320032070101c80319580c85210f2540d200e07440c0d10381480700713205012a6640d285444c00083c0754140c240d00491200c2d0841210030b01055603650010f401800134030640d46080400b0894030400d03410040343c1540c0903210840302e102440440444513030069001032042d01e51200227040096142e103252100d001c02844c010000020901c0c020080480d0006032640d42000c55 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653729622 1250 653728372 653728417
    0x30d050606040b04180e0607120507030e070305010b0325180b0607060e0c0d150b150a020708061e0f040312020a091404022b110d05150301021617 64
    0x803104180c543c0c0f0881c4107030406c88103414500c0041001030159040e501c1d9280446c80841a031005401c1c010a0308003095640c0013190701160081203030f01d00a41c01390000181068400e4149130a0080903180301c0c46889164410040d0810364089402c102c038121540805d010840d100b800c80036040080081e540100c0108030307001842034640c03101c210100d104046071a02c44880c400c0c0444070301c001c20080e0807070100070904000d0344a82c1d04142c81d2039000508407203100018011001a5821143c000001a448180140007414080242c00d4004032000408401e8200384007111480600080c8502d103103034039620110342010700460311041044000c403c02c1d5126021300070018800d02c0344c4e10441e4140c030221108140300381024422189482d40c84600c00e9482c2c0a80c643c00e1a0703046091031419a4140d54607000c0000c00c0300c28001d80b541c00381d004004602424468103540c40540003080107842a4410041e1113070700e4840600c01090154030071800314813019082c484681500a50b55800140f00d18030103a034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653730872 1250 653729622 653729639
    0xc02040b13051509010b340f030306050301050c040506070c030819030f0c0203031602150109052509140d050102040602010e0f010902010905121c08190509030d050606040b04 76
    0xd603c210400c4000e0001e01c1000300c02c10000741401e21501d80445810408031103a80d46c415100e11840d4515484c0079014540004002c01548038038405549000c41d401e02c00c0b0030164036000340001010f0880003807086046c032403120130217131083d442a24031075140082d201d4200810003240000554200824649131252081c1b1410007040200850300040e140c12800d08041805106503184080750340c1c001e6065a0b1541d11401010300c0c40c80c9102d05500c603000d4550f049484441c2c03001c2c040d102a03100442c850826002006d1868011203142c4000c04140c614003003020344c0000c052045540c0c1e4176042c0d1003102c4150115000d86503010004e00194000500810981c2e0150040c1c1c2202082e0b5040390780711800300c2c00f03241c200c45500708000e000480d48907040055183c101100d0503a8251041950f51801219a001c0c8000450001c40000310302a5801c0201c0d81c403024090740c1680d0001003040c4682d107401c0001688a02c6003410701559165150080740039512240705680c0984407850006903140d4a90501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653732122 1250 653730872 653730881
    0x100c03020406030c0c080712120e0a02011b0203060403031104210309062606210604050d090e010e10030506040506040c0b09032d1f061e060c02040b13 66
    0x2d2501007400d28024601c802e215503080580203410108040c1014615520f0704988080940020108814600d103c80301402034441c0c25a04110705008020a5005100140202e18454a58107600d01840c0c00040903890118a10303a1040d03251400213943e589200d1071340d18501a5821602400d6805e51a030100c0301c091030000a00e06010f5110101010f035036000403100b0444001c4003951001c2c134004032541710903403280d407190404401040784d02d154041e4403290003200c02d40808240203038072413000d01040c004c050112291099880ca004480141480c258804140d030611602c210356010400007007100c0e00310710800d000b566118003542c00500309801d0640e943c80c010f03141928410703d0304100203003c1c2a1201182e514040140c06032482041c02120440c0b11020903a462256000711f0300074076402c000c14000b03445000d0444035860003182c9800e0240c0120f0ba2240c012002c002030600d0031501e1150081c5900d41101c4281c640307581444660720125000e4980b11032103076040f800050606084a009811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653733372 1250 653732122 653732129
    0x10e0f0f010605093705040501020d140c07030806180f090106060216030b130c0f3f080d1407030b0a05011b020d320a031e02100c030204 60
    0x28000c440d00da03c10041e811006a40c100d07402d075002000d8030a82d12207040101174241455804500d1160031400700d5094510481e8210b415950010b00d88810006910074028a00030304044008a8500310f007003184a4843e160010b018018194002400d0743c1e548800e5112121612600c3c22540c14001000c2c0d22900040d203041c4229401c0c201c0202d119032001515651144408152480c02461a01c55154100c0c01520001800200d400b401d00845d501d031041000500c03200b200a040d1601d03000f40b100742c075a0280010480002006405100041b140458101034403151081d40a05500d47ca0007000c44d00c110b03401c80c44840d040401c518081d0310115056489071586403020b11440c40c0c1d2004210714031256010b000e002c87c8140203540300702200131140d820103e20142504104980c562a240344400ba101d00c05e0500c4400c81c81c0042e100c640c0030300b0030007401c09940c00a1114509580e0003074081003060784480c8901102224190480d84200319455003100039080810403d522114024065401b500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653734622 1250 653733372 653733403
    0x51b120a0216140603161e0807020c010c08030f0c1201030309031103240a020c010204080604020406080f0c090c210402091602060a09030915110c0f01051b010e0f 71
    0x340002140f030a03034243c02e002a07034010241071540c2c1c0e4109107030218035000703442038003081603000707a40c0d40a200d5200d01050b419495120700d03445180001d4000e240c03604c0f171034109041110416022000031400e00030303290800594401104a0b50303031426410594020b010915035030216680001041c150042d001c601a41d002d0052944180c400c0c009043e510120260751104602042345c0110b41002c0e6141c40503004282c0110140c908010812441c0c00d81c0c01c07941140303607190400c0050000310315103446080b00800e55417000e84180c5501011171a01c80c1d1420382c003503001c1c1c101034000528100008046407983e00390801100078140b4612908a203c94044404170300842c0d4400204149030190413191400160b264014000c40d0385d4003540c00c1c080c20080ca404c40c107002c1505000314035984842e5841c084103102d030341d900449000c501015440c2401d07859105000380f4103c80584040d0760b00100716400908441a2100b513140200c6056005140f1050103140710b01604402e0030b0a0540820740907504003916 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653735872 1250 653734622 653734663
    0x2203020126060906030304050406080304210309090506060d050a0902131a0d0f12020334031110020315010206010f05010c0b0403140703030204090507090303051b120a02 74
    0x76414010100440c1025460311600c48000480901d00312402c81d501560203011b80382881d6441000ca01a907036039401c03207541c540002c034090004503115540c840c8030200d0681d000c0200c0300182c070302414107070150084104032929070300001c800b42c075078400f22085010901010825450819800001065100002c91082d6011000e48400c24035034020191508035020700e243e0801509030810402000be08400c0710f40c2509144680d0104444d1140107115030900d402443e51104003000000500c488502d480f03c00820405040100e03030a03601d03000690a40c18100005c100030310004039894104480c0380c8030181c500000c200b1000500700e4411610343e010a03000c0700c440380d80300e0500d00ea080c41d43e0300401d40001c1491003084040f84030702051503045402820100300d002039551200f1880e900c211000c1d008280c0005040160030014401c4550000d178030f1030001112400c40c1e4000304203110f04007500c3c003281480d08040c0d0640109004c01c0300406101c941087d070302d00c21180301a40b40c0e4440c009600c1a102d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653737122 1250 653735872 653735897
    0x414011a2b0e0610030b060f0d0506130201080702010203010305060a02090d05100609060920071e0f021002160b0903150f0a0e07060507030c03030b030303040606170a0f080f22030201 80
    0x54486401940e52080c0000899607c1806000301007000c003500c9036118503000305000104500b0312416024190315080080c0e010014000540001c0d00508124116841000100080ba001040140c0c0010680f01c0259440c181500002c015208441d005400c80c0600c2d0f5415640c840c075035101c2e00c2103801100782405a10b5540d0000e4003242d0380c500d05420f406a02030303002030340303006090018158548903091801d42e620415140038003901306020b00312201c100c44140142035180904071240700004c140b009090400a0403600480c280300c0c0c2c4141d03003a00001048456007a83c1c10301042c0c03019a800450101d00d072420301c0d0703502107004095404416082c5401d44400c0601400301307180d41959600d455180c41d1440380e0b41c0c1103a0303050480070280c040517503c28000015036410310086004078024000030940740c0c01c0000304502481c80b155500c4403071740115800d0001407000388074640115080555151214102e4142c6143c0d03100f040600d007100c1000c0046807a82d154170324000c1c81a02d0007039a07485c0c1c4c480765 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653738372 1250 653737122 653737141
    0x180609180f0714220b0a0b07052413030827030304110a0f03081608030412030e0f0d0507110a03030c030f170606130911090414011a2b0e06 61
    0x610440c01400d11284d007603154101d04550002c502c1148060060b1440725960840c4100d140c11081c3c00b203440f508060703841c0340010380c08280b444511103848860030742170414000c9100c04030078200000f801d000005001827000401b0182200d02006883d40c01c43e503007072004000c15200e500071182250031460b03404440c525420040303882020348003c00341041e0350f10308507101c200301904000714004214000c002c0110009105070017460290b8441d500280c031540c000302e805000e0310011569449158010080e00c9421880045d0000c4851305506200e90b440703c190a01c50f6095030001c05041c0c100710800300c0041056880640d40e00070034025926456a21106101111008080f00004840d8082c107000b242c013900e030040c0140b09201d02c00437403802e00c99440202d0000d540e0140740c1c01230320031000316003041d0b1401d040c0103203010303500d00b2411501c50303605100103090104140a03080d4001c5074042660451302024004485241d0b1541c8040000e00310b0015144000c0c01341c405408413180107440c08650710301d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653739622 1250 653738372 653738389
    0xe06040f150602070b183102090405090d050315060702030f06041704060203070215090915040f090b0a0e19061b02030702010905011103040f03050c0f180609180f0714 73
    0xc48091b11800c200000d0000c1080600448017032904400c2e45d4107070004003c0000360110306103002008007503140d500400c200412160002d0044100350042030b45800c03800d40c0403040320f031b001450114607110200420f011500c540143c42c2c00941511501088084240c00052068400d510071100112002200300081c0818092442410050390041c09800700503d4052030300c0140e0300f1010400c0b0f0601c440540022200c420903a0503074000075442d41d440c00c01e03040c01d0281251035003221006010090300da40e83c0e401300c0e580c010880b480c020360390710a0545501050010000d10192922030024411070740c28524000d10310010004150b0a0740303100c4960035030000c01034956964050311161034040c600001901ca1544400d40b031003140c00108400316a683d085000d20380030714005c0c401098024100b00a0102c03400e00e00b07041134410441801c80c0c4440c0c6441031001540500700f40c0714403d80e9100c10a042c0420002040b07072621601900c001604000c2000504c1d40440b1150240881100210011710008c003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653740872 1250 653739622 653739637
    0x80d050907120809010c05100e0c0d02030606040e0a0f080a020d0c020d0311030f0a1106010f180207020105250605011a0a0e1302130914100e06040f150602070b 70
    0xb0440c8440b1a0042403001019200401d418181256142400d9a681e0f0400c03a000040160055603810220b010746010864210844070940704180a1720181c1c00080e80c81c075004220b148515201c83c0c40c100f0222081c003100b10708a6101d205604041c10f9807420400c4d9410510a000042c0b080c0200d10088078482c2c04111722181d00a400c44180e000750361012240c00480140c80380c00d9200810804d0090083c0c4001000200056134607520005a45940c0505013501a40308005501c2da405090000212050b07001b03402c074000303c50042e0340d00e82e20b10060f40d80740070741e010320030388413801038003a1f26039030303045554411068401c0c441000030360780b9a94030920b01c81e500e0568415040040c42074140031405140805501080100324164145024000302d059030f100e07620403029400407135001c0004440354002c154044500403d8202680f400b1040c00c1000c0c5114402d101040e02d44901141c100e07102c41c0e200e0101024041c00c24446007002580c001c1c0d134040742d0300c40c0070011b1061020000345210513105881c400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653742122 1250 653740872 653740889
    0xd14040b09010c0e0f0a030b10051e0f1306082d010501060f0c03030e03030c070c061409101b0b0610031e051e04050c0109051806010807050c0109080d050907 69
    0x1c00d014106004540c0c4d03100c00d20340c2e005002004003101082c4000c0300345215009c0c50000c40d40d06d608210030b200c1d01c07104603081d2212071546c2403548503065649640e032a480d41c40c04d80301c40500f10100e80f806005001c1c180d000481d140600007040361102c1020040015201c002400b80b0020960b10021600701e130024031900c4005000c04001c0300d030262044c900c0e034107014068980401d0f0302a01003502c074110340c01500d507a0428400000c42d001040741c04070443c0d004000600f4940208440017121007010b11401a600e40f10b6100108052200f41c020b19240100b07410102c101c020552040c640041c01e201c080e130b4038510405c9124900e002d00c1e8881d02458440041050075800e00145d044c950802602d00a000c038050f488401e10740b000402c4000c004144264050001003044e10740000c00034090800c0d46d00281e000344004060180c60404100716190407180030318011070240c2d2000340840d21402503e20901300b0b5400d00780c003035050203d4600506481044560100320980f184003500e9030300c41313003442000782 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653743372 1250 653742122 653742137
    0x60f0709210c140d14010b0612040c050117010905180f0d02060a06061704050f10060905070804050a0b0903040f0b0702102f120415180605090f0301020d14040b09010c 73
    0x85c9181817285800c0303520780008121603010100140c103503040b00d2045c090400c501c50811017400340303000140c0e000b01820b0a00c5040058000e1201c4400c070014002d580310030b0b4490000c40c0f004207400024800d08130700784050f2802e01c11492320554648810a05050051007400d0220b10002c042c0e00c030b000c1c01c82e05c40f900d034001d80068071704079201498401002620039000381c400c441d1013006c1c248a52141c40880d8071000070300c00d06000601044403005880380080103908020040000d000046900e682030300410300b9445991004252803942c8550f8100c5902c00d901e4040016554002d03102030105170388225003000004009032011540f4003119502681c080407115048101c00c0480303a0500c1d0090498010380e2406038100582d4410f591041d0301401b964411031844a001c1035020080017089081029004401072a01a0050082c081c50203428451050f980c4034861540e405d5044804c0101003034000e1111a18144903003100c4a000c65060750030a416000203462404184910b0005802507200e094 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653744622 1250 653743372 653743399
    0x1080a0b130b0f0603100e010815041e050f01020a080a02030405070512030409090818030105040803070e06041e06020d02030c0601030f030302070c08010615050705060f0709210c14 79
    0x6001008009a0003400c00b071804a502d4540100075403240d200c018901071001c1c50081e07c01c2044074144c0c84201d181d040382c680c0320311404810074001c1c1c10513003220592a003c7c1101500100003010030500510302c0c400c21400b14a40003040d005443d03040c00c291104103080d542d0710721001c20f9200480c0c00405c0c5802010052040d407809106503200400140200c90400351540300080440d5a003210035111044045043c0216507080f202100309000103070020300460074141d031580c01c0760001030003050500080780824042e03034413248152001130140c0030805000c900020310110503840399006030001405151250103006000104482c001c0c02220020145e50b0702e55141c41940700e120f40c3c02203041513001c1004901240d041161a80540501d02c0006109881d2031419801c0340c0324004c1d00b20500c60240004004035101080055006207030520801c4e1130395030344008869071440c0390051224408045940078980501640b80d40d001c62141e00240300d15a117031014880034081450301d140e40060b203c2d0058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653745872 1250 653744622 653744659
    0xf060317030c0412031706010f0c020402091c0c0f05090c03070e0111010c02070503240103080901030b09070201140c4308070c0e01030506180c0a0308030601080a0b 72
    0x840c2e1000440c6005424107072101403060344054656000e8000070307101d007405c541d010403842c4001d420041c24201070303901005a04018000308000c000180c400c1e9404100c5464580358412031000018031282c4c0c04602100c2482c3c64022900240100001d81c50400000304540c180a4041c1d0302a030a9102543c0c155611450112001090300000c541041a114078180040c002409868402681d64028001d039a042806261030820716403140c014014074030b1070044100000010260540740c02810f00d5559414000c0160040c180816401c0d400c0381d20f5404214225506520140302060035004c0e0030b01079120030850464a02403901184080c2c1400f80003134a4440c0c410011040e82851030313240302148092084510407484180c1070989000b13100103101800c05c00d02c078101d08058122892180000e50443d02d410790707164001480080d11701c1081d04040c01c101c001b00500c113180e2100402000001b912031911078036a400c02e86926000c95903001c04540102c0c018015105808409850115590459075a2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653747122 1250 653745872 653745877
    0xc290a09110a03030c03031103070504060e060f030f15030d1704170c0708240105151e190207060e01050f12090f1015050618040e060a0f060317 63
    0x403101c00c81c40c50580e00c0142c07030b040030361001940603881c4e000ca40d08580c140502a503452082405001c01d0400400180903017010907102501c0c00c80c508141c202c0741e081c0224909200362800b155000102004000542c40181c450750303c078107101420b50070144284028142d440841109030710108203150200e9541e2140c0126440e8802e0088074040c2c1c0b000b0b5484000c540e02e0744a00d04001442d04011000d001c8850104460720808105003800044a050405407000f010f006016244c8160035034132129000351002d8041d079803040c01e441418000e071040d1040342d58059014020800210000c0d2191201281c00032441c081100c1a41d2280002c07000320b0741c0110f459034054900c0c1d241c0f5070001e00011407105418174100d4801d401c85001000d00c070025080c414606414800541d03c0a0b0400304070300f09140c100c3d869842190010b0701c007983c40c3c181c010400160841e1075403016400ca4682040701d0020a00010107a0003880c1a00b010444215242c1c181010750350b090002500c020b03520312080c214004034100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653748372 1250 653747122 653747141
    0x1030c0513050403090b180d0309060e0f03032a0f0d0305010608102d0f031b06021518061005040506041104050f040e0d0e100302030105010804140f0d0c290a 69
    0x41c01120000010102030b2307005419000140b020300c0510819401c54440e40d80c130321080350320305a50283e13034000a5803072040c080806044402416040e08808103607141d030550919030070a8422160120564030f0351901034030715400000781401c0000812900031008903020360303401d0340003d07500c5003080040d0400558a0710381d00000d4640e1480041c50111070000c0c00d015044105491412618505100305109260015920024481c1004000094002403085d9000f40905448102941c6140c0c0c140c84811040d010895280180410444a10b40c8042c102069030422281004140ca5800a01084918010580f8100c4900304024400340c0b806c4480c0aca00b0b55001040440c1c00a00d8103855400c0c800c51100c8980454039a0517031411a01e429008410040c0851604509541c50040000d02c813000280003d40785904440040c000600c0030301c0411070140a9a0403580c020240c0107005000660b501416141da811104c11b142c6000500048011960074201449003075071070f290101401003c4450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653749622 1250 653748372 653748397
    0x5030703081504110304050c030309010c06180c24030b0f010305060d0816051b0f0f01020a12091d010b040e180a080d0e0f120d06090501030c0513050403090b 69
    0x80b860a240d0315030203600c038200d01518550342c03241800e1800c1403400740784400c074034403035082444207203000d036072020222071076581009000c0303600c85608040a00b500c0c2490805071110180f00d202186114405080d61208201408030a905040c2410204c040340c40f5100c0c40c55001d089102916800d6100790803c541010300241406000c22242e51400c016a11503580c51906194400700c03101400018001d4900c0b04d4003c5050380f0b01209041d00003103818059018081c03148031484103c10090b40f08029010311141d200e40d02c11031442000502038030b518550f00c5110680c3d030040c0c140400390b042c90017206041f1910707140e0701410070b82840818008900300a040d4080a015401c0201d4001c900b004400c41d030380e000d0f419481c0d8412202448000755400c06800041c507a006604205281c0c03000a8000c60b8410044000c68507480700c058400c0140446034009106181414004410310400c404d0210884004456010324035180001540668404450140102d032164200308603201c5084028280e90341100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653750872 1250 653749622 653749651
    0x30c201b0f130c14070803540106150804080d0c03060f0e06010c0602090d0615090e12091e03031611121e07030b0f0411040501030503070308 62
    0x42102d140d542441caa6095848010110407543c00403d802040c0d0611031001d840c050103611030702d07128440034003607542c1e840410b181d0f4020390354515501041d106800c0500700c04540980090070600f07a080c034540030070a0340f01490000320081442400200e8507400343c0c581c40c0b825140400d4450b403100038002c1d52441410020761002203014800c580c8e0700c2c01d05480c0040e100c7d003402c543d0a03040031680c2007102811103060521403243c1e04041c102d141590700400150750740341400c1c0411079885581000402c0340713040041c00314590000580f80b1054034501e40040090002c0c442c00c070b41e031740e414801c4003410b910000c01004846080c040410303121643c4c1082501068090031000c24915840b81c220322141c100100c00f401c007084083d10840071640c0040302c4411213099503038005600c03620b045e15100781e14070080c07000d68480b0406100c100c0043d500411400f10920303100030401c411000480e812034a0301c2c0c0e410000c1c0032914103481024180d941000082d8141030141d5001d0f204c0c0301001e0088903515258 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653752122 1250 653750872 653750899
    0x20a05030601030c080c06090102030d050a23010302090a06061d01020a080309030901030b01020d0e040f0e060f0a050109051003020d0507080609010603020307290d020c030a030c201b 80
    0x8001c1c85000754843e0b07004040051402d0081400c0a04003002213203d07207000c2040c100d00c2d80e070000507900e9424688100180648844000c40028000a948403402d0b040d00e08034504c02d407080154040c1243d000381c400d0301103540e038201810102c42c01401071001190749200c0090900c042003500d001501d6041c01242d00c170546540328445243c1040316580c40c00d52000415a00b156814020948600000e00081280c0b07121104083e020b40c1c500e040c0c9600884d40c0c0c1c1503040c00044107400c55181c0505290588210382440f000d0240c0501040341e281035400c0c1010300000c2c40c4001c5d031213440c1c850392110304101007030390450742004046100c801003991144600d440104040703505000041c0118a070100000321f2034514814113062120340d60045560326541800c500300c03400b81e00c00f00500f0044055049070750300b83c5420b031a40203000e9041440c0340d500c000700c2d909a0680d01580040400100c0340c5400d2045000c103520710341394050812000420740c001c40d08040150300545c805a030400c01c000c10348043d00f8031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653753372 1250 653752122 653752129
    0x5060c160515061003051009150b0f1215130b0301090c0f1d060f10020a050d090905060904030c060b120a0b01170d140a0c060203040605241c020a05 65
    0x4072040440396244946041c49000d01d40404095152013450400b4001c07464801400b90f407151007403003050300003600c0300316054502c07000c5180d041c09029005507007a00d4911801c0c80c0a115042400c858400c41e800c94041050404c0b010300210a00744000d01186003071040031000c101400102e82c4442e00356427142c00183c00504805035030000b0f03001c540000c41046203060300c410b0500082c140b07012542481d01d801c1c40030b1501c5400c0311a2500d4010703102c1a00d50140d0340d0702249090b070301040207000c9004241302d5002c002e0b400740c80001190120a414445070700c0390004c1120090065030024045000354800d9800030301950031040c0686001040c2280140c5607801860820a21410484040103204014001c4a440c0f4480801a500600040c050710340400009011222007451661075240c0c082641d603100340c030440354960030f50352102096440342040d107003000152006483e1461800306a603018101c0902400030312400c0c010040040d200b8400c600c1000c0d245400c184401d0360880050724011540c1d0700c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653754622 1250 653753372 653753383
    0xa050403050f1507030b0a0b090a0b03010603090312050f1803040518040219060207030f08042303010c020318060d02070506040f03140703080403050c0a14010903020606090405060c1605 81
    0x141200d003d0710b083c0d0001001a03e04400c000c02040901d86041040c100d540c403904484800e0700c4806910b142e8071001c3c40c0c0054410b0401d03511503410940300000109070603525030828403409200740c803000d54038650440c11209842d0119180b210350140040081d00785400b0402a030740c103101100940380b41688032800b0640d0703400842c1e40545503a0b2405d0a1100b1420f180450002604601d030042e01042e0030300000a4031110a4030015008181d04c0c3c100c0014002c400d403c807401816a4400301e442e0741980702041a4289001641a109501c1c16818810b0580040201c0e03811104128580401c3c5c0e0500303041013460b4203c044242001507082c001c0780002042046100c0c092401041004100c40745441d0003031072b8440c0d002000c1e00c0d00780244004000650444a2180c0081e817504101e61550203074441a0324250101401034168241300c810004c071010f06501046090b8002e600380c5d040c81d40c030b81e401d0203c2c83c44241d0380182a0307801440052007148041025180d40a6001240c90144601c0d440780342c90031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653755872 1250 653754622 653754643
    0x1101081005060f2d0f0d0b1807020d021b01140409142a160f020d0602040f090203040507031412043515060d1403040905070219080a05040305 62
    0x40f10014604281041c0400082020303112803807001881c02d01a8180e41043c0508010f11044040c0810218042c08840c5c024a8000c035000e444040017031081d1100e00e01106090310901c025024000d00c0030030540c804200584d0380c0d08608540b10304a8107090044032515010a0581540b42d000c0c4008208001c8a00541079100e4129000c0602403c0c418112490404a200da204209142d0040c041401388038078141c41140320502601c1c5442221410459401811140d009620550181d0b441d02000455805401612500d05050740d501e5100c2604508030710054801808075442082c080001402819840340c1c020b0052098580c1030745801c80c07000041d089900110022b0004460146040005074000612001c03106400e12100002c403070310984403e60041c803640742e81c0d11000005e41c075444801c038003210382c5d130f1060140c90326070791040c01c032a101c1d001805031189103805c0c580400d50041c800640258006501c0d00410703044000c569410380d50340c0c2300301006e03003c0c02828000040845c0c014858003041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653757122 1250 653755872 653755897
    0x72001020c0304080d11250305010920030f1005041e1203050c07020108160306120303020c0606180c03060a05060d1a0603090a06090237080a110108100506 68
    0x29030741008249030402040111510401c886c40803411208080060640d907010600a8210540039581030912240300480d00040d089600f402510303010072450400c440905400c4040c80d58528005804240d00d8090300380c1c0b101c68550060f00064900810341c1d0005400900ca0303008000001d84122a0080820716203500361049130220001d0984144c140c011150302a181c0080541342c48416400644070540c043d0221141044107a091880e042c003a40c410b001821030503e03a0800045185030090103544852040c3c8228040c0401144050901c00130190040c1c0c0262500126503981000c0d4644681000700b110340e000181813800500c0d0340b030b850001d110801c2c4403180447d0000641721030b5103441e001d64881d10302454003042004400e0741c0c08640c3c00c14282d842400483c80440c1ea00000d50030b14120480d1018041c80d200040d48807404030a003c908100410f0007900440303030303103816007500e989034007101401d0113000c041d6a0000d0762040e100d80381c1c0211450166520365840d00040b0b0519040943e401c0b50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653758372 1250 653757122 653757127
    0xb04091b0303080906061c06060f140a0b120c030403030b0d0f0b130201050405010e0d02090a09030807050a1704051509060a0b06180609010507080c0a17030f072001020c03 75
    0x1410b0f88691100e0380aa1000001e104508042c0003086400607441d00009040740301804213000c00c03525401420041c005d0744010040c0607100c0d6090300250800807411840354190311000a140e42c0c44a00740c4034041d40018059116171f480410507442c0b0340c0003c100f10304260ba10240c4810325501c100c5c0c070042040c0200301c841c180304035600d080b20000d84007520039480b403401e52440c400140ea1240464080c0d030000c0c03170700d219507100381d02c08299040700c507030740095008050718104070b400c6442d58460803045020f039540901d1504d42316030980d028071507507061030005001c828541d40ca03215110b50140d08148241d0880740ca99912001c002c880d0300c001e443d5800b01e60000b0b0140315440c5c0c154040c1e81201d010441d142c0d49040b01c00d0401c10020220051800d001c0d035008545a2442ea020304160b814040c0c1000019a4410340e000c41d0700e881d002000021140d400e06a903220100d0007402d000d0b00e2040b81403452044107038958500c155001502c044042c14100207108004002c4c11080c0054404030981c0c000458 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653759622 1250 653758372 653758379
    0xd02070c0b12070f030e1c020106120f0201030b100e04020708070204020c060912040b030f10081207030f3e0a0f0b0a0212071b0b240316090b04091b 65
    0x2412032140b44c040314105420f04074000c51009011500240e08080142580b403038500845059000d00000d42c44541d03c4102d00003100107004004883e003036243d100b40c2e010843d000946040000c000d221002450015110034081042c80c00c2580c014000300d8000d4900701c3c00c04020f540054241da101410502903908098144030300100300300100a950014090200d0406082040306001408000c26000c00c0342c80040c0400c1002c8261402c03507010701110f505982d10a0481c10400c00c03541e100003c11000207045441c00c8800501c10442d09038803500140e10056005050340d000304450740700000014005010008031404007904002110140780704900300c088000c2c407405d00445c1003c1c01000c00c884a4010048140040c10701545c03140e000e00681401c0e4a0b08101000300c201e11004800000c10807031200040c0703e0303480d010000e098440021800d00704002c1d8107400c18035440740400b0400d00c2c03810340d8500091140350b0b19608848542c0714003910002d8041680c0d1a8050512043c0261620b8110424000d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653760872 1250 653759622 653759627
    0x9020f1e210705120a090206190e0607030f1d040614030105060d08030414030f043312020904020c011d100e1c110105090102031e0402060d02070c0b1207 67
    0x111026a01022980758030744404007400340e20074a41048400e1008800085030620b40390722060050750042c203d00d440e420822002c84e60180149062000304064103070b8140c0b6841c040088488842e4542d881170302d144c2d0954820350303040c3d0960142001122282c4200f4020b40c54074400d440041c081c26010440426201080c0b5003141c2d8050491400381402480e00c02c0880c020008407500603070301440c08640100701c4007030729085005001003801880e10000d00040d141ca20f43e4441d0811004120813008030317080328444208000d212841040105802414604961034554087c01c1030840c0600098070384101d142ca002d0031562080422200ba40c01031100c9111100200507460035018684020007110090011881c0d607607490200915050b244580c2d2641382906c9040c0b85402600003e0003407000d82010041d07113010b500304841c01d10301804507521103a01c14002c5901c041c0200d80140109150402d246084400781d031005000f5200c20300088400152120207000a00087c03c100c0c01114013804d003070340b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653762122 1250 653760872 653760907
    0x721030606030e06012405040308120a0c180303120e0307050703030806120604260304050d270504180506010306020904110405030c10122307110709020f1e 68
    0x80c41403c3c1c0c0828010304c00401070245010925101e2000a4031b450440d040c111640c2c0f0907600001d140100115003100c5140e07014081d58003d20b03065000340300100c66407004030368a4481c503820055880801e9000c0021174080c1d56501c1c01d6103158140442c1c00000b0b00007592541e40a0201201c440c1e120440410500d54490006504400e0403030b0408400290104020340d50480074002a000c1c060158101c03c0914005103d482c0b00740d2900940f50302d902c0d1508000b500e0301096000300000c034243c178020081407400c1900c1510480c540100042c00982408107200080c02110049031141c40200110b001140c0d0800c0001e00131441100056522103a03241130105841d0515000c2d8103480091100303000aa50204e01d039085401d058820f0716600c1c80740da00032240d1000640120405c01d00e440a1004451002181020141050008074403681c071000811240d281c0c400c20784400a40152501340441c0581e038008001d402c07592000a030600940c80200c44d00d0421201910190403400622020740b00403400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653763372 1250 653762122 653762141
    0x1101050105010905060a0806041409030c060a050601021e150c0a02010c0c020a09050a09170a0311040501020712060608070b03070f0c0b0606090a2411071406072103060603 75
    0x244031981616000100310140110f8002d07005210b0801f0004000f92140d5020750b1601d41038500340d04407410501841078503a4040102014103002e03c000144035121140101409080107900070103105070400074180040c901d05620344c800b4001c201440f031032501c04101050044403444a02a6180c0c00c804020382143d0611051100744504505603c016a6030398103c00c00711240307400003064990b0340340d080c00020550810001c09180440d410500300d864140b01415091203152400c000d0200c00c0b07200712425014520070f40d03006034400320091140040311511131004500c00d08d0041070300c41e16618010b08285d5540c0200151140101c100643c00b40d015825144001a608109100a0690b04c0300b000810005004a0094000003034554207600c2e0004004010710190f4103400031150064400d10307600c601c204610000800349110b62402c0c0d080410500d040b2503400c01e03080340c080054002e102079900180000da41c11064000c101001d402c0036941464045456038002900700d04042010302210400079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653764622 1250 653763372 653763377
    0xd06060f0903020901032310020919030807030309020102030f04031208280c11070b120c0c03090405060a1707061d06090f1203070f050d030e100515030706110105010501 74
    0x800400144e101d603404c2605490700120340c25070744642c070005c0b281c200c0041200075826203d10482c4500389101d60740a8046a54111460650311101031340429581144d400050081c4100700035030702c002070107940904d04480c4180140e07030401f80c00001c81d00168020754002d031945152181e9900071180d00c031a030290303c8490014132055140030480030801d0018500c416840b880d541d05c0b034880310180661540400200040d04484520362030700b2100340b95030410f4071141d01c030b030320008007084600c0d04010644500c4120314004604008a03030041001924020341210f4002880d51b50114001e40c0d88910f5111030b01081005160283c9010b00c0203041083c4450b44551600e01303689803029a07910344c0100c81c1c620808aa540302001210400189609003036120000c42d480001655020442904926140316002e4019100400d030800c000740c0507100300c56446160b903000030f86c20a00440441d0311150308082150143c1035511141d40102e4a4140e0365009600810f8145410039103500b400d001c1c03103015160a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653765872 1250 653764622 653764637
    0x706110a0203180102030c0d021005060a18050601030b120a05060705090d080306030138030102090109090528090506010518070804060f020a0903050607020d1d0a08030d06060f 77
    0x40c90020745900483c40308488541805600c0700c041e038420030581d02c4809181003500e04051290b040a9607030340c40400f0750080300c5c2c1010001201c070302c1c048203060f0445041d18401e4007031000d030600007070050000070088ac0c185035841d0300e00c02254440b500c1c0c8071140107220300201130044850510500c0e1a400030040c80801c1001c0002d04101d480381800309000c4c6a2003885a9180e440303640010703024201200aa86040b184c0c00589814800c1403000c1c2060751900d01030700c0f00300040010905090b480381a800c42d0209802d00d40407c00f071010b650006030301107400c80d418200f000210141c60700b00d03182d8400f400ca8440c0c842c584a0103100003403001a0041404481c5041071a80004c006a0b040c540201310000303020424000074140036441e00001e5040b00007480c02c540e1003100c0c0202901d41001c40c0000d55040c40344000158200e800081c144014001640702c010207a40d0704414201030203034290515401040311040080e2040b01080603000d21803944d04007094090610000034005541940303403a080200c078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653767122 1250 653765872 653765887
    0x30f0a08091608120c010207080a03090209010603050114091801150501110c28080601030f031106090709020a05251a010b030a02160b0708010e091b0f031e03070611 72
    0x303000e6941307806018400f521420030040c464024014440040c00c01d0200003400c401c807641c140d00c20141c0303600c222046100341c1d0301c0703540403070442d6000d001d107a030390031656102e0104a00d0310750304443c0e100f44101c481401400e40706006509561844c4482901c20100403824040d941e004494680c000e2107074401030120008813000101c5a202140c032041c0710316125580001451031009000d0054843d403411100c440d40d40b0314010103808000407054000a58982c01c1351106400404c165000717500c200001d152660804181e840258898140c80060107410851000c0d48446c280c03801d075841d008000c80c06020403040c102041544451107081c40154060401800101c41c0381c0103407034010312071480c0182c0710020140c030166965640c6001030702202c110402c1140580d4020541c1d41641c034000b18614a81d11003860403651134105400480d170114404085025506090211000d405c0d1b0042c1190740391031440240c00f0000640c0381048000e5000042d50b0b005000960140c1381d000304002840504d001030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653768372 1250 653767122 653767139
    0x50106110c06160309051f0206100302010c02010f2a02031209130f0f020d0902040e0105070c031d0d080d0c020d140304060b04110a0801080307170c030f0a080916 71
    0x180036004001c120300b0501c40343c1450b200c0e40401010b040060800c0303030311050300541d0301444141104000300610500c00026001000310301c500b003c40c1c1e4103071903050851f07885600548000050080070010018a81c0c10445c3d0f4041e4024101941d0400700080355400c4c5050040c10304000070100d440c03244480800c140c1c0c032a0b0300c440400d2005880c690500265440b146d0548001800030702c000d601d161400442c50b2028488550f100080c1079108560421017020521442c03801e0300e104441c0140440c000100d11400300e80100e0b00045140e02c0e040d00c01c110860f51a001608030408404c00f52503007403000c114450141994401c5000310340c81800140126401240014000130107224001c02004010001c5020090141c004000780d40c00140306120340c4054200d181e143d500035403800360001e41c843c000051607400100031141c8141d04070348021441d100f624181e02c1c0035070004819402030700c42005442c0d408070003000603164801181e45d483c0e40740c2c241a5000d80c5014000b035029003900400810800c5005d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653769622 1250 653768372 653768377
    0xa080417070c09381903051510030836010206070e03012406020f06090706030911090408031014060a03020306010c21080a0b01020703150b12060115020316171903050106110c06 77
    0x40e09050655074a2700e5010680c1c2c481540300801c00440031a8a80104e22001c00c940e103e0700134860000200a040c0c40b5000303018590354101800341c0c0012000c40d40481c400e50b10302c8641075000d400400d0081040b41039603c4030203259201c22041c030030b0000034071140d50306120785911603808500502d414104407103d540c0303640581c484c02090503941c90303050b8100003203494800003810f0300620000640c6060b050981c071a900440385415503030f8514102084030103201900c040b0b41c90000d000d890800b0412001078000394009491541409250703406100025091858040284074881038055000115403010b0020b0001410f0460f00500b8201c04642c5a40e0001d03d441c120b0360400e216400031444000d030100180114104550442d0711005c4801c42503400082c880e040310044140c82c81d01d841c071450300301d0b180c0c0540303c0c0015010302c200f49200003050000482824009140901615000c081c450303400d6844034194164001c0390300c0b0401000300d250400c0407103080485800240c07a4131903504000882c2d07031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653770872 1250 653769622 653769643
    0x206150d080c010b1c03170a090203120d0f090503070201080a020f0c01020418051e07021c02150906100b130b0a080417070c0938190305 60
    0x81401684501030340c0d515440141894018001c80d9441880303040c010b002e071204c1084d450081d5000d80040361040e019070b103544035064156540d43c0c05039480d01c3d8103041c1010050046410191140c1450001d6501400540010441e6072003880d0740350550400901036989140a0940940c40c00031200007207940442241e298940c2460101e0195440446040003405900c41e00c002c0000b0100e14450840710560062090f60040c04000311070302e4101004030113441c4101c600c0401181c2c0008005400c45000403da604004a030068031848041c1e03085c10b242c0e80c180040058010b0f84140351404001444140868214802602034007040c81d104920010b500c01c07511410131144000500002c1580d14801c05401400030010040e03a1603180035401081e00f60241d400b51078031808948105020300302c2c2004c49a58079800050b0840c0d807881d25212100900c00c808009503070b100880071040d508a000c1d90403042c0d9401e403a416060017545034003030000700d0b448001141412403030500e00744042480015100300c034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653772122 1250 653770872 653770891
    0x30909060f01180b0403061103060d021003020f161a04020f0d1103060103050d02250b03070516080c010c0203030f040624030305041404140c1602060712030c0507030206 74
    0x118100d070040b5104200c03108903110341c050310700300407802480e12402841141d02988003849844505942030b0340380c0c032007a1806076104424030300d02e00050030594170b401030445003400c00508121a400d007a01250780100010742d486170141030024104048103400d03010a01a0081c0685c13103281c2540031552407036440308440d10543e00d160075041040390440c6d003d000804060192121560750f407401a90f105c800f5113141000d80a82c10200d400c9208041500c0903500220303480c490b510b4600307903841030954809010035042081c208040b0f03080c1c0c0803440046101c60703c50507400d40d95814a40b40c0358215880742c4120011074100708240548201a0781d10315811a80004d0000386039690100e00d041400b1121201a1110091400010605410801030811201003c24102d0600c1d140c008020403617580030740208075940c2c0304010408000c0301001401e21030301100001c0e040110b5540000c3d00e190054101142c8804081d040c088100c0d41c18012007025480b2424001e0500d41d46a4001e9150341e0000c100c420b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653773372 1250 653772122 653772139
    0x9061d0c1203090a120c15020604081b010213060909060b07110103021908040506060a0501120510080f070801060603050f070807030908031519060504091109100c110303090906 77
    0x4503010520803602410f000803d01d80311150348011410403a6031000b429070320b020075050005419480300005102d240d5566000e0403543d03a8586da00151900b081a20f818064245c07894103070000000d00c020191901d5141f40c610700760b45050401400f8229a82017285110705041d07003044054031100c2590761003980101201501049040101e000340120800c0c1c840d000028403440f10b01a4101603400c1c051030180c4240d80003030f560340003800a00c40d058841e003400540c0003118a002c0c80b115071321150f04140604102d0741415541c500351450001242580c44182e040788100f00084042403160500602650a040c881445d0428952080000c018a40f00c140701211000030141c85c400c0c1d001d0318040751320030b040071307160300b004003200500c594000032490194036080d141c4800c1c05400044c00080b103136155903641c500340c201110180580344289591500d0030050046d00c407e40c0d2043c0b5110078040071603540b00791100321400e00780003055150500c04d020707400400c01c40a00d512650040c50340700c0010f59100c0d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653774622 1250 653773372 653773399
    0x102040f0902281e021902010324090c020601050409031b151406090a050c0415140304061b031112060f031506040b0a05030a110a080d0309061d0c 64
    0x1c00100d003190040703003441c02041000440d107804c26000683d07603010441c213400c0f0b8241e600080c3c2c0e5a02e00807055044007800d410040c4010340c400c0c3c000314081204400d003100e21003000d040841e091541c54001c1c0403c10386903201d608046604228442c010001110284106803050f10050007502c0424910400d0400d591411424000c405d1021900801c3c90001001030615101480c241000152441e6100711880c3d008a00600010b025103805212250549843e0518090604c0ca10b0b0b1300e500089400d20150f4080c0003031000b01007000c6d41c0b2507800341034046044102082102e4041500041503010b1614081601c074a00901c04243d0328410800307880350000c2d07101c9000103180c00301c80400380c980c1880364400c0c1900600d0081d006a00600060b60140186d14001081000c2030301d5a006c3c144e0180e2184243c030b4085068905039140c16a40601440c4a268440b10883c0c1860390b005440d10102c0e84881b03400080140c80d10600604074210410340c40d807071071413000c96910340a082c2c402607c140c44084250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653775872 1250 653774622 653774647
    0x60606070f08043605040b010902090f040510050405070906090605091f0c050c0f0f0d060b090a0b270a0f0e07030c0f0e0709030f030203390102040f0902 67
    0xb10040c0c02a404025001d401a101d100314528011880c400350100c11810f90f513078104540034040c01268400020280f6a0a018030325000350008201d00b0b51240c2d100c0841c2c1d815860390310881d0b0041c030440d0402c0d03103043e017080240401d45001801c44410003460071400c005440e4405070b888261800f51030b00c5075032550080009641b002070503031046d0741141d0000d0384090254101c080400700c11301c9101924007200c0c4070300030001c08494038a0031542080c00300c0c0300800b851909000381081c1034410a800071300042d15402055900400311001c1400c40d50368003102080c0c0c9005c50b41d00c20906954094448038800c0c000c2c0004040101034111105541c60f5980311404803403980280d40e28000c05011a20025628181100c58840c2031080b0342190407000300120b80002000c01192044441ea228105800d2650303a03655958121130506a045001c140b02442c0d00341811804603d4160507008550304142c240340c6504d011620b00094003206a10400007004080e600c40c24100031504c0042c00140c4a419000c40c0c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653776978 1106 653775872 653775877
    0x22090303060f0f05090408040308030c13082a030a060e010c080903070209061509060a1d0a0f06142a10021201032a0312020f060606070f08 61
    0x900c0b00341042801650028403603901f103450710381d0740d0311038141580060300c90300d640c10800200c0700e021414800f0703081c025115400c0580810203403a8070410b40b81e4041041d00d56407120007111101a640c0074000b10f200c09802507001e105582450341d80320700902c41c0c1c0c1003540100b2015000708181c01d10000581d003030a5805090080c10352654410402c800d0101b0980d0010741408102c901515220000500070420154540d8031a82c014642a1001544c4041030f450003101d603004c04000e80104030144104680742400c0074580c0300141c0304044150b02c103007030075200d01e1681c1c0b50b48200c1c80c55101d907072485955600d20940750085446880384099210302c8003c0141d000a04c00180045650308602e6509009007003a0504840076040078804480b034254002e50790b4000d8614031024468050241c44011304004001d06460720301000000c81038003038150302500c0310b40c43d42c1c2d1000800000408 = true := by decide +kernel

theorem cover : BRFrame.Cov 653597122 653776978 := by
  have h0 := BRFrame.cov_init 653597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653597122 ≤ n) (h2 : n < 653776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
