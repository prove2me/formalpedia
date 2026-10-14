-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2855
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:56:22.14816+00:00
-- url     : https://prove2.me/submissions/bbc2aa22-ea3c-4c45-a1f7-38bcfe65fd47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 513309352 ≤ n < 513489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 513310602 1250 513309352 513309383
    0x71e03030b040609021e03040c030507170d030911010302070507050a170f191e050111030105030c03070f09200a020c09071115090f010606090602010c02070b0a030203040c03 76
    0x50340800c507400412035007004800d45a07540d90080b4081c00c3c0340313811540a144400418096041c0c00b0750361241c030801c5140003141c1c49580307150408080d40e100004041002c2c003110124001070020503460702540c942001019550303141d41400000380c071401c905169000890809118051203180050710303001c3c0c06030340019610440d4500340c031120381c0295240d0180820f4040906404100c000c2c0700c140c0042202c441103a5a100c811207208450802030b007000c0c07107000a00000d08280a42103c0c044200c40032030300c0c3d6140ca4285804c0c05a1003003254402d400c854000d002c50801c1e0b01e5039109841c1e0314400000c441800301c1c17400040d000c1c040c00c2041d0b800f40110780421030036400244000344010588040c0031f680c60740c1c041610007469800301d80806402c1844034990440ca0390b2038565001c8104412984018882412182107500c150421400900a94401c0c4600d5409000b1582003d0300751000704040c602c0c00708900c0941c05600010020941c000000c41c003404024070380103018640000300d000c1c2e141c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 513311852 1250 513310602 513310607
    0xd02090d031101150509061002071a0304110d03081501020106050307091a06040b03040f1a1311011103090f060702060c070509010b040e07080901020c01150f14011202071e03 76
    0x1030b08404552198242a01c11503902c0c0ca400c9010100e60029150340d055464450030001d103080d0a00b42082148950140000c014080380c64406440c20948401680c030304260030584032211700e2150090058a0003154140025403012803140d0044881c030040d0f01e4605020f00403809481720703502160340742c400c4100208201000354000343c9034140041d00020269041d4080c01141e0056124000d08071005000040104020301c21305100d07144941d840082020344020045075901050391076018051740a2a0101000b2420b80039101880090801c1c240e80280604225130b40d00c210415030703005100000f00591280c50300815655101e500801440e00c4a144d10314090380c81046110f0b140c818195500000f03013166004044034242c1ea420400c1440c3c0755100001681e0b11540640340b80c0c46594200000c2603600c400380b040c2035401010203030301143e10307103050401d00c5400304e560004003803410b0303e02c1b031002c1ca41e810100d00c8010019004025032900c8281c20040392034071100c24040690081171078020100741e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 513313102 1250 513311852 513311867
    0x30b01022d060703050103050304030f0c030b190f0b032508030a051804090f290114040b0a0e01170a05030a08090f0d0203031306060b070605041202160306020d02090d03 74
    0x1200740c000c81ea00303540c460800320306468081c40007600c241c01c200800e00114040e100450a1107010f2468244010741d40d680c1c00b440341c1c038203c41caa00a100034000120545e10140035401b6144866101488101040000640c40d0200c070400490440c0c860400702c100c0100b0a90100000c1074020103a81c0c0780c00054102803c1036020454400511000800c038413528a0584038404017160414041c3c40ca500d100e98841491a100c040c203070f60055510036400d50207070b18000e081400b80c03000c00d21011407801070302c0c02c0c00300b501e1b214a80d40c0e20400c14050140318401e900c0c4080c0c0c1c1101c00c400c3d0810440c00710148085d04000b01042c010b881d034080054110045900024601c2c0241c1d5404100e4030480b1460505c642c9828902961074016001040802c401c59402c00d5080c29160045200040440d65514400001e0b880481c0850301181c545080009020700005944007040944c005030042c002c0c0c01400701036900b0280401054240e0209089103841c1c00d5a0680b072055001819401c00c0e02c4d0a81009060003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 513314352 1250 513313102 513313183
    0x2040f02130f080f03030406020a020124050102010612120806180a0506090a0c0905100212030a060e06030633030118141912050c0304030c03020406050103050c0703030b0102 76
    0x41c031105100080c82c000019200a50340c040c4d401450850321380d42d9a00e0301079400500e003403045649803151812500c4030f00c0841507140c0d001c42072000e0850f282000181c00c0d02d02c00e5004040050407040c1000100b040040400c441040c0c620389407100d0381c0c0f0900000d0300f02c4002036035410300621540c00c2010b444403982c40a400b5600898407003000e9901c2c1454801510000084100020a004000c01c00703418040b070000b000d090180182c41012194002c80902e6410464080c8103454075034600b000641c2d507104489812503800c0e00900380350310740b1003500c0c42500c0001d0584207400104546224840e8800041c10000f410028000d020294000c4003200031618132550903601c1c2200b40601d40851b420008040003d0711344202d40c0040182242c907514414600040b80e141440000c004100345082c0c1400140b019500c0780f40040b01035421801444116400350300000d043c50b10345014000300c00b1a5905407000da95043ca40072613105c0f40c42c5e004074207010020541c0406c1c13038411094109040c803044c10712202c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 513315602 1250 513314352 513314369
    0xa1b020d0b1e060409021309020109090e1006090902060a050a05070f0317060a060c0b060d170d2004090f09080a021b03060c1603090b190305150f0d02040f0213 70
    0x560710b0f860304003c00c81e00200c40c0254440c22004209503c502c4a4011054840c01410054525999101c2ca0401d0320f000d1070300c0f072085800080c4004103441d40703446000d001d040c1d43d071810000e100440d40400d1030b9228010190050000108030080d81da031140b8100c0302c0d05d03984102c00b100b5980c1035150282400d441082c040c818150b00d103000030004c2c00c242d030140f0212807280e6220700c04400980c858042031100070b003405070090240d1100300c01180d21050400d85140c550700c281039580680e0714841049960707403250b030046100302c40d004c1403443c120303034094405480302c40d800080c401e00d0145042008004500d00108000c0d80412285842c980100740c1c440004290032400700d0208603502090740b01c120844000102d00d005000a60030040078420680c6081d100f0b00741f202020b606c0e6084081d079601b1004100f8030351000000c0e2041c405505008454105c03d0282105c2000040d000002e0015042ca1201501400e0203108a8080d07560313030341042001e06203481c0c04640d5001250300c0c01c1820209409034015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 513316852 1250 513315602 513315661
    0x122a1c0207150f09080d09020f3303010305070e0a0207020d0b0712060b0304061e090b0601090e060a0b130b0f040306050c0307050f1810020609010606050a1b020d0b 72
    0x603a140901407480021752101c003161038071041d040360100508488500303a0b006107501c0aa4500da4813420301440c841040e200302d00380307204602da401500340203500c442c8988001c010300041000810015443d01583d80d440a600b01603911410b030078000b40140d5001035404a2041c1461040c00103c44055002d2012a0b0340d100c0d003e010308440b24241da51a100d02c05584e5130400008000c581e403035002541e8200f2601441032084d02d10390002d000d90300590400c1d0345400d04207090200720342c0c100e618100108042c06c8a0074080c689607000880101c1c3c20b2144002518000981003510445690400c0103000c0070070146403209400611040071340c115003c221f5001e86040080751383e0103046015a0310031f807c00e50780c0914000714001000100d4200103204400c44001010580ba00d6031400078181c100065036004001c940303084a000e82c25612994064030038444108603001207140d0005414020966494084280d00340b2071011850034035400002918907406101400700c0300d014000b80350110005104c6204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 513318102 1250 513316852 513316871
    0x70f0507021009140303040e040b06010c0b07020f0114090a1401021c0e010b03011503150204030c0e100501080108190c0806092b0905090702100f02122a1c020715 71
    0x6940b031040740107003c1e03240348200c0082d00041280c100141d1028041c5401305a420469484000ec0354090722800d0158002403520010810709209078840243c54602810682c141100c0560710364a81000207800185450000c119600e02501140c0441e10f0102c0303c002c14040e0402401c0040c82d0714001c3c3c0a80307500341803605006180c14007034084560301e15004803e0044c510703134940b2901e407012054024055000d00002010800f95a200320081c020b01070060304520b03000c1c20102d101e01c00740d0050341c1031080000050010b410002401c610a090707890820360f28400314188000051203591240120340b08030f00400604000c04244020040c80c1500c0030420108507110a080224000484c0400034454103010029840c040759040c1d0020402e0054441c0c040c1c501d6542d205407489035550700c1045800003804401e00c5c0c48000c51079480300d40509126284030826614840369482c562403c60055400306804e0009045494a215144c01c0300008640e10b600620386034041100109000c01101e282003d0758 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 513319352 1250 513318102 513318109
    0x1418130201033e190f020a020d030305220c050f12010e0307050d0206070e13150b043002040203100b070510050105030f281a010f060f0206070f050702100914 69
    0x15843c08038408007082039030606040171034002c2800e0003081700714820301c1040e0005d0b84500500b604403a00030350340455113281001d1403542c0402e0382410781d402103294080c0480810f400e40090810b44504603080500b5400c4480010300c884500410001c042d482e202170b000c1121000030040940a1140d4240c4400b1221420141e0316190100d0b40003000c0388403c1101c6516207031481d200d100c5404034a90008038200018480503003910b0541290b40741810001d0309201c10506240c0245007030555940000e0740403008000c2d01420507540c0002030281390040b0109100003000d03441f0701d015045060515031a02000d0900c1130755020a0061558502e282200118980c140850280380321031040000700501d10b42500707802c01d01a02004071000b510b6440c090080004d005c082c907c136200c240c84000310110b50600301580741c41000d03035001d00103001600308040c210300d030003080f03030b07a8000e0741400d103107034503d00303907a41658940b0803000e00950103000030003054a801e400101c40c60030b4aa21480c0d001c0b0301c441d500b050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 513320602 1250 513319352 513319357
    0xd0c020105060a0e0112060603081b010b060f160c03050d0503040b060904020108040212101a04050703140415061d0403020f060c070b2e1418130201033e 67
    0x2500c0e44c4003201c00051000100840990300a03038414000000d04076920740b240c0b40250482003513006004229029400042024041c00c1801042120b0740d601c1c1001c05c44000381c9521440d2a0184000201940301e41407090f4401303008002e42d004815240303000d0503103600500650080303404640c480f0301d0300082183d81c14002c0000c2d11503a81a1664052501d541c0c0030040320450301c1191039040e1107440210b500e4803c0c40d004000e62a662001c150500384a0305003048155007004011004051805450481000d8051800740e00650846032041d45807501900b4480a00407e41000f403e4005102240c40c07511041c15406c5d10030340c041e500f6201070b50214050b0b25180c40b0191400d40d19140300780b21300000700f10b144807003a82203031401200d14451280c204840304200100d0702030407602c1c0840e2404001c0141040201200c104046510004905003c2c07080e0002d0500070f0701040d11025910218021a40654070447c016072054445846480a882c020034403001d944080d2080314250058040c2d440603000113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 513321852 1250 513320602 513320609
    0x180f080303010315051e3301080c031003080c070e040f050c03070608071812030309030908011104092315040b01030209030705010e0105160302060709080a0c03120e060d0c020105060a 80
    0xf01b071886002c40d50000080c0440207000b170310703c00510000601c3c3e0380f2a641011190309840410804000310120300140940d072006245003606103007042004410001000c540301070f2540016078503255042c01502910704102c98100034200c40864082c001400b545038103a0550f284550304540360f4421a109064440080e0700c5a0f00100341c0c0301c004100c0c400d0003640d00641140903c910960030541e92442200c0c540c0100c02c040e40880e550f86001c405055002024a02901e4000000c0c0194000210381440700e104034441d00c1c9111b562602d00b2440e6260850500c10100d035082980d03030311030a003101e040701000203951a1500c5245030503038502c0a94000c2c000d8a40b903581c0140900065881c10005444074002e1030010f82c1081010070007a400400e1030110351543c030f03010b54002d000ba40741034500a00140400c1d004030841c0d40c001e52601c1e001400f8031a680c01904d44c1319902d04c1018102d40001d4a5440c203010500758008004550070110100603481b8100c4c490081d8020b01c000d0300c4170070502608030006d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 513323102 1250 513321852 513321871
    0x2040f12030903060203090a060908210405060403121d100e010624030204031704031b030203060a0c0306150507020a060905060a0f020a060f09022d01180f08030301031505 75
    0x40003003002c504030703174086c541c082d114500f5a0440708131a0350701012190b50030307800c882d0010042900004c1c8004e50400741c01c00483c442c0710f46880d082c9501e0300c80e03492000403c01020407440d00c80d20750a81c0403503084240c402c0d255030611f010102443d46526113440000c07068002092402c00340800d0031505020705e0084900c01c00800c1284040c00304a403403800e40c06201041810b80070440080011102c01000219032103c0111a48a508520705a01450011000d1780280d40140c1c00602c003680c0d000c103546420840000c0e00092032504201c040e006880f4a9008110900c160050b0040d50b581190003085414801c6a0000c85c0300e85441065a03001961f000d0300d07410110500c00040001c0c000c5000703042c031380c1c01401101c800310741c0c554030041542c0101c4070b0000e4143d201e030103090442c205410320b5100d290040101c4581804400c2d4100700341c03401e51079000c0c10824103420030307014161004a0300000d40107666540000c07545a4010700c1d41d0b58021306c402c42e81101442c400c0c0f2155191071052602402c01c2c072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 513324352 1250 513323102 513323117
    0x61509030316030f112811030304120c08060402010e0d020f032523101b060c120c020d031104090203040501020a080903042913080f0f0703020f010c0c0306060902040f1203 75
    0x10b0100c45400d06d82001e0071603c0302424114145a5134040015000403c4070700707424030981c15685401a141e8045610280c4980e100109006c010b0b07803c0000c0001c108000c0d200d0600f17204140c00000d80d00c02100c0702068050180c045480583e04102041a110070030042030501c1c425038409040c91110000403130091a40c40c4011402e0003882d00a06804072a1464545a0fa103c200d03098080700038641001c04441c80d95850343c1131b01415801030326180c10280700c00d5003001400d12800002e922250354651100815a1b034840340300324503025000303490182c424004215124585881c01d64001c1d8400503124003c15411000546090000021182524292998081810400071307910411010000c96000000410f0018584500d11005884001c082002c002d261043d90103100c20704010440403980b0b501c4e0480c070401e1015803240d94080da1140c13400c0ca0140301900722401c01ea04440d1850700700070040b50500c030b80013500d80c0941d0064001d456005e0700c3c1d810300c965a40280b10540880101c01404103060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 513325602 1250 513324352 513324403
    0x21110a050c040c120e0d030b06120103150608030c010905300a03090609060b1e1e01050c03030420012604020301020c010906021803010203061509030316030f11 70
    0x80c2e0001007801d079040c204507002c0c0b040e0110350010f171540e0141e0001d50740c0c010340003601c405905000e22000c11030103981251400c0c0c0300f044404442c2d8414080034090764011b001d0b04480441c0c42d80804018000c0a00366074076074500000303850107080990000c1d1124810405600c00340c6041c2e00c030407110032840200e84080003000c41c46120070b640201d070401003416540c0030400003048607405044600c5100308400280035000740101300109095a03048540100f80c170702e11002c285c8071100b400844402d040614049024502d004840500ca021151a400d01000c803d000c10481080f074001011003401c180fa40c2d0100c1d1080c01147d00440c03e003030509402c6145003640104580c0f151176550044e0001d0005460100c440c140503081d0f607115001110b000f680010142e1180e0750b0b4005d115040f1808030000d615508100000504000c030014005602e1400040c840640e41c0c0c0801c1190032119004070900880446410064400c86108081d0001714590001804080401188440440c500ba20040754036922 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 513326852 1250 513325602 513325609
    0x30f040204110319140105010f11030f2a010b06190c05030f0a02010501210209070309230c0d051908040e0f041208070c0b06060721110a050c 62
    0x161050341c0090355504118141e01200006500c00d150b030920818041d0000700c442000c0301c926a1044c5030150103400140143c1e03a1080da85c03802d044007840c0c40c290181003e070707000e4190303c00c0c100481307410100000c0e806118103095070300c01260401d1000101c3d0749020040301c40d007a2060302400c6035000d081046403845045031400e80034102181c0c1c0c40c001d59101c0e03d903568545140d01c0000c4407900340c0cc010908400351642400783c00c0c0940f1040c0090b450109044d800303a030400c181e824000380715030342c414001406c3c180700364810304a040d0030015012500e14404d21a0926916106969016004950b520001404c1014200d89142d600200411460120b40202d07a4044d034102e0f0100c849450070000004e082d140181c01358007800c1d403d001a000d0342818074140c080050710400050a200c0f01100302b10030035402c601d103101d00541005c54403409566202c0000c03d0f912031048000c1c9414480031301007603146207484110f80d81c000aa15078020403941c00c0b03400e6558175555800209117034407d03204190a8207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 513328102 1250 513326852 513326881
    0x61212020102090301050702060621060703110f040f210f0b090a05010e060108070501090e15120a030f030e0309150d150b030f070516020f1c0305040f0603060501020303 74
    0x61610006003040300030740009007540c100341d0340000140e00140c00d200561902c5584941c2c0c03c2003000042100315000c10700203440c0d0348014180004d05540309004202860060115506403624141d1280d60b10380b69101e0151410b402d0040002c0e101512811b8016209015028108250046d240b0020008595a500b481c810020a8003919000f0302441c840042d40034000c0181d050f0206c0041d05c005d40c18441e0981ca042c4269000504100356018104003120302d815040c0d4100100005c0d45804a54030000310f00f061120041076210f40c8146407448007450703404035042c60520b0450ba000d103ca58134812040d6030381d00482c8256903000300e00008144590070b00000409211282e20008505124841c1f01032050040075484483c8120f40081040341d040700d4156081c0d401a400e0501c04c3c18944080d8041206094a4200034000c00d0014902083e0f5500c010741c6881022450008042d00c022610780101250040d11a0f044000107144020800e01c0c080d006100640c3d00603402035042d66201c000c000c8042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 513329352 1250 513328102 513328133
    0x8010b09010c0605060f040f1a0f060d0b01091d090706140d0902130e0703060b0103051005060a020a05030a0201020d0f061505031b070f1112060a0c020309190314010612 74
    0x42c41852090040e501c031f90085680341707400840000341030313481d12807000800201c030140135104500004402c0c0c0995110700544074210f540ca0070010310702c4000c000507a02482a42c01c05006d0302a000b202c0b11600c1411802c0d9032140100d1025118215030f10702c1c0c16642c0107900f0290744980322041c41045803104042c0d0083c000c0398001070810f080e018270078010904a48045110642a8000d101c051090203124000d11352030100a03c1d00f08400e15000d0b943d4522505140106031045600203102c00d03a0a00c01c10620040070382003c00e8a907908a03203d4042d000b0b5000c940603003801402d14402c04c80c0c4252a110b28421039003928224032000c284407108031203651000348000b4083d90054040c914035050080a8409a841000e211301102040c0c2041400c0c05522a80c03540300340c1440800c04401c03000030604542011b0300c45004612812002820790031405841c01d03090300301c001c1080c03e01e215007451500c02d0880e4000c0550000c1d65098007502e0f03003030351441d000b0203084400da04403110000300d108803010281c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 513330602 1250 513329352 513329359
    0x11030d0f110a020303011d060a060f02031215030c0a150302030606040b070302060609180c060a02010609090f0c0602070f140402071b090b030714060c0f0a0b0708010b09010c060506 79
    0x2070034020603180d00c1541205002500503480400180180841c2000c8190140c1403604101410b2400c480019442c2400307009010402c0012a98158424020000c0d0b1300e40d8075a24021031518584000400721b515405400700e4440d01c01c0785101c000908005020f1800d8a140c0c50f401224480040c4041d0b02035030000e40301d0b035000032081000151008440003c1c080403446580604541e00700142080701c0303104094120b10141090103d0001c1201000a048414140a5540c1d50315408400e0301640144510750148001e02c0c02c00032101c003080414a40190041c1c410800c02c05115120407040341d0704d04480c0503038207800000710414060200030030120800c02c2d400400c051318080705039440d020010160141340403040300c0d108041c48800254040c4080c020b40039030080c207145192990121200006000e441c1c051000081c10340e82d11001071041180003403407036049912120741442c05215550f0221100d81c0080c21034000811200000d004540a03000c0581d60b854960b5070f41c8c0c481340001c0c040078020550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 513331852 1250 513330602 513330611
    0x1050f031008060115210f0f0605041a0102060f131401050603010f0c09030204090f0203071d0703110a0302210901060504050604050c030f04060906020d1b11030d0f 72
    0x244048248000d510407803110070414945031402c54041c1c5828030682040c120b01d2603400341141d83c941c1c0650041141c0780d8070000c000c0030110a40c0034038010001c0d40b103400401da050140781540510b00342c100c07004445d401d441c10005050440c0003a00d0344207001c000140141c0020340490001614040c40f00e400101c1704d00407200c1c0e036041341e8814080010011144203a03944407009c00a071442e0a100d50620f04142c1c62040c04080304500d401042025240802840f4075039403114542802800314402c0c59555000d001c46110036141c2003c048183e10040840011030040f41c005402e40d0710a0080248030107480742400c0c10804402400d0f401b035000801a140b04844420f00580d05001001070180180c82032000061140e041c0000c0c40240c4000801d41d60065080c04203000c2d441128104807a40b010304001c000d00d030340d1518501500070744524a4090181400850301b01c00d01e03002c6e0360040f03010500107524840d0304c1c106200c3c03d48800f92407004070800c5d03400c28443c0c0d03808403940b40c000e1003000a44410006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 513333102 1250 513331852 513331867
    0x20c0a24111605010f0807020d0f1403011e170c0d151410242303070e0f0306090a06050601020c06030901022d040b0706140405060403030f0e030304060b0105 69
    0x14a402081e0400c0c840c00c40d42e9820802c110350300700c0030851555010307103040070843c035281c1c102a58604200000030100280c00440d1a9102d210b000000c03c182e440f418a20342d02d507514044c0c031500810240e2207489402e4042400034455640030b8620a18140f503101400c4d00050000c200600c40d1341001d0141c0f01c00550001100702c00020348190541c0c0b4030300400e481d2003800e2410000001010359006158003200c14284428400d42c5032021100303813a1b880c54903010110045003000c0101c1e4041d0100003000038080300b401030703803508101580030352041079401c8003010001d0030825540380700560788800c558121202060209220341c0013a98042c4040c0101c3d0401048070001c40c01a60040b582040303240d502181c00c481103480f40030005050800f1803e401e82441e0000f0070560030744a5441074141980000070304004024858000c000f602c3c4100c01960102d1820b4180300786c50321003c036800c83c006031034100074026030a0148030b405238001e6000025400c559582c2e50394002407805d4091617050000611144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 513334352 1250 513333102 513333137
    0xf05060a0e0c0918180609010e0a0206030727050f0405070f230705010b040c030501080718060509012601050c07021e2d09011a280e01020c0a24 63
    0x11405045c940706000500c1410107541420000090000c1149905168441650074000200074a54a4049540d10740ea51101d4006442c0207404c04420100c244804200c11580d498034130a142c200d400546150200d989140c04000440d00708455404c0400c10421100403414403030080c80304190f4850b0303000c03610350790303201c00190046c2c11103802112030f03a45030010400141868042c80005011a0905000a5040c5540241c8400660040741d181c03c2c4410580750b41d8000c15044000181000f81c403960351541c442402050121103984503007100f00303440c0d4403c01165014410b0921551810b003070a4180103490b0300b00940180b85406598030b480d02e961044a85075221251482c104154000e040f0b070f031504000e941506903101003001785c80b40520740010460b103030001c4602d003c14041c030224147d40d50007918038002480030225107102540094480350ba40e8035044403009805007001d03006c0b5072040d44503e00b0048140382c07502480203903040003c10300305d5003081012609a510300601b05401c5811064410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 513335602 1250 513334352 513334399
    0x507270302120d0306080a02010f1b0b010303051909060906050703020f10020909071d0d06140702030c15060d110d0f0b01060f0201051510170a0f05060a0e0c09 70
    0x560035411124203d00050381501c1071100410f10740010f014100c00341c0e00041c1a0031071030441c83d014480304407141c0203103d001d03c88002a032540100c82c0c0300a940c40c0d0400802c00d402040310134002d0744041c3c0c0744400c21030144903100b0403078645a0f1911601400c20b0003c8499800031001182036108054601000400900c002004029400d03401a1660929020069000300241009007071000c0c06140c0e144160251046280c803072402c0d40c903020000300610707210340100b4400b00c03803107400402882842506a800b00080c58184088811581c00d10020503007403240a409076043da0340005200c40d00307000200f07c9500321000203002011010800200e03141c0d144003c882071801c8540c21461801801030a400c1a01031050000a1000704818a4116120106014914005c81c40750301f0107003604d40704a00c45c294041c2c52546485440b4654104002d100c0090300182c2d01042201d41001e0010303140e410b005003202c0407a9001c100c44507403611a41d5044401d60302c0b05107415009094013030b6821200303450004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 513336852 1250 513335602 513335629
    0x11160809060705190c061106010e043f02010e37080406120203040b24040c120501170601090b01031b050a090509060d0308060414180d030507270302 65
    0x1e260401300f003860880303005401d0f500b01400384600da8960b032415000020f03503e810f4907004901c00500ba1568201009440384050407440170801103a00c4500e420551039860281030101070300c0050800003400c0690a035210384111000301e030b000b0b0400301d00342e00c0d150a03402c12104000c0007801490081724040075150043c04019101210005010005c26512500c0320340903070301401d030443c158102070395400040c1d00c000e00f421000034005208110301c0a00c0d407507c487c142100170400c101c00c0d00303008009000110100b200800340c6240500008100c088202d00352103240c2402c0240034243c3c01c01d21000c0c0206111500207042650b03030030364000c96080e000c000c0354242600361a50b603105c0e443d036080140a541203400c06400748a041c801d01041d80c03183d100c0316510650505010f03030b8540d1200042001032010f011172001a6503440e040c0000b40303070681b060290000040050f07400c541d0300c3c0102a4151807050310407600080000507401c030000740da945604801d101ba001c3d222000d46da0398001440012a508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 513338102 1250 513336852 513336883
    0x25060c021e0405040503041e0b0301030f021504060e03060907061707110304060c140d0f0c02010c0b0109140f041104051509040c05131505010c0c0305030a030207020411160809060705 80
    0x5e4180070300d1540c1c101c402c50301c502d20041c2d403c02341d01302650000c5500040c413004110a100181d00303400c550b41d81018005010400c000d40b0740700e50f03551a000700081c070707508082406801500301003a420300e03000c100b41058440310f84030311007210040005d03170300980402054541004580c00508040c040180000d000803c125500d49642e0a0941040791301b803d5503070600e208030352001c60003a009a8200c0d000c0000c0a001d17042c00300c0700c00c0c95400181c0304501100401030850340c1280000c141080694801520080406100c03055079851000b80711a900042d5030240c060003603901252114a0260032942e0301225074113100700c1240078200410001e00e4284e5003111645420303070041c4880e003400750780d14000c2c481c004410b101454000151389014040c0d4042d15041180314840c5800384140b00d28040d000396804011640d5651540d18008c0c000c3d00700d01012882142400d01e03452a07002800c2c1030342e5544a04102d042180e2110b5620000580d01400106030400c8050001002040301817282c41b101d40840c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 513339352 1250 513338102 513338107
    0x302030a0306050117041209120501060311030a150207022d09070c020a0e06040213030506070e0607021807020c120c0a1d0708151225060c021e0405040503 68
    0x4000c081c0549040741c202604200700c9508241e0004013003400c09410a401c40c91201b4210303140c240482e020482da030401c48149044403058005c218055001c40202ca000e01d600c1d18070b1000760710806403101007407600680b00320b1518400c000c0380040d42e401494a0351000b803402d0b5040d072034110480048074034003454042e5400401064281400c165039503561180040c039064500003d40d03400900800c1090081400340007070000003c006480f43d5049500c180b84418020440c0d80c1d8a00d002507654404554070400150038844001e03450400000b5030380155801010b00c10380c22020b03a803201ca40c000081404046104203d020515038642c5944224a0f100e01c00c040c0c410f0324000001e000800805030302030f00c0d4003440f01c40c10740c81c03074246160110340281e054581400075849144000c8500c032250303210742d64004620b2092210f00740c00007641d131060300c0c00e041c01624181c8039500d40f40000403080c4603160206d0b00d040c08050041c030b84141490031485800002600344802c0074041401c60f20210b40881716070380300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 513340602 1250 513339352 513339367
    0x140a12080906090f0a060f090b0c0301033c0c1a0904060b07050a02150f28110705060a09170102041809050c090403050d1a0a05040e030f16050604030203 67
    0xb40030103540310303650b0801014140303007054142c0d0703a60390344030030203000240e80d1030280c0608091307900108562500004555100e060244103070ba8103a2080c4401c4401810415505018640c1d0800c2ca030b80c8440c81d012202d1141040340041c0c1e2020240c80700440c0c00c8942c2c00740c00301d055059001f04007c00440303184003540ba00801f41c180000c175074003a0040308420b030013480790308009000081c220b4200355050710f00c0000710011038503000307050142c4640e03150003c00c085220401b020014100100784800100000d54030324102000362072010360b804d441c21317198101304800c8c40542011001080348500c1c2d442e11144031940c0c0c40c02d814401d0000040e08205035000681004500e052012030810700940d0242006002142d030303540d0741c2e2070f182810101d0203510381c03000003018180034400361005104620020700030031b03c27041c0243d5401d15046101a02c1180b9060001c40e4504061298000044212008500e40490703c4e9222000d0b4000e000501039034125068086c0c00180b0511515025510036002992100c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 513341852 1250 513340602 513340621
    0x306080c010207030834150506180a05060307030218100506040b0a03180b040c08161404020c010b030a0308060f0f0f12010219020c031b010804140a1208 67
    0x881400a04560103143d0038404141000e0848403107040d49107083c519510b410405101400d03032000c905440045600d84801844041440d50031054a10541040942d079104108888250401d00340017071101803100103180d19100b684951b411600050494080e250340c1c0c1d000450506440c0900341c1e800c410041070081e101c0c00c00c0303c800060107003152050300701814030103914400d0142c1d1800c1c1e010180c0b0343c10728617004103461540281c2250400d0503805185041d0603d8a410129481203070454490395540c180031500c85c13607580341591020304078840c2142e218410080650000b01c90001a95a514080e013200ea40030825104003500c2912514000c2c0340c0942000981d4500e49201030244002d40c0c0055425070315550f107813030022021221601c0070046401018024000c0d0518144800400049a008250000350188184400300d044400c2d00115400c26200d0091407543c0c0e50100e401003003c54002020251f040316903808410032100c140c8000e07107607000070209500950340820001004e0280481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 513343102 1250 513341852 513341863
    0x2070b0601030e10091106040b070309050906101413061706100801060c11090a0e0f01060f06050a02010f1a010314070806060723060717011203050a02030903070303030608 75
    0x1042401c08101502d0400c00d1241c40b481c0e4120b0942d400c0c3d80c5ca140030000c011100f50701490408001d40303c02c2e100da40702d078401d282a40c01201c0c2a0f0101d81c429074005418134214442c2ca1180303001070000090543d5891040d070f40c0c1a140404804020002e10040e2841c1c00e0400c2141c0040006a80f0b0303c10071003082403403100c003041c00f4000354004c11841c050821307815003010701c0604407080c0b0f00e403106a0700620b0030861800b00f100d08495600c100b100c41070104140031604096001c0340801d041c2d540414007074a200703088036814824043d03450446d03030042044c280160084c0074941703400e000100307120441e00700c0c7c00101ca0700c0100b4107900807580d070488089540c3c0752181d04103034100854026120708007441c0150508400500e9644991300000d44841003000500404002030700400b0004942d03118042d5150f20f41c0000c9600100107107022801c10b420034180742c0414121000f210b000c1c0458906905d0403541544258052010f512007000040042d844c1004940c000314000d58001030b42900f025401420720 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 513344352 1250 513343102 513343111
    0xd0503220602070e07110a05101e09050a0602070212010f1e02120a0f141003170a08041104062112030b0a0510090503060a02031504090f060504060e030703020102070b 73
    0x5500064051000441c82d0004c15000b80d06030400780f141c8000c140000e0300c0c000b86218002c00e580104ea4150403825940d412000b0307601410340080b65030110052240c0c0440300d5440010703017141e1042209001080c1c0a900814a40340043c0400c0189115180400d0a540e401480c2c070410030350701c0307600605814588a80b5034807227440300815858103404043c01603c0080c040c00c13600c441d59842910040d035030310651007c51040c0342908060075525200c0680320300442c46100c195195498401800003440c0400102c410f891016199031141c0d0f21140c460020500ea0b042c1d0f02504581c0d0740e280402e41d01840c010b4043c40d03a400344110400306900f072410440401070744000070241070502680d1046a6192a40c0005850050380c48004144100100710340050310340e40082e416004078418441c0018440c0c00640c85951100c83c07000d0041c1420092000700c0d280c00c031001e0080c251000c2d401c8001840c0340c100c950858000c400203c0c0d01c00740000310f141982d02000d001c0700580c1d070000e803100820401c58004e0743c3c072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 513345602 1250 513344352 513344357
    0x2c0c03011803121505030a03020f011d0d030b0d061122080a080702130c08010906050d020a03030503130611090a0e010503190512040f05090f240d05032206 68
    0x10407a0395802070044421074283d001003e46840b07a400e02da14003020180000d2800404030741c40d070300d102c0c200a5102c11288444080329401e050704540404a09000d01000c0d06030200104244400150120010b0100c0b008482c0c6c400c658031a00c01c0401d210340201072004880c240318566038548100d40f0244080880e00d0250350301001101000040c030040741440d6015000005150380c1d0342c0320b100081c030350b64201820000e031500d80407a03a1a00d983c03005501d410385074092410080140c642c0f0801002480010000350b005003061800e01c0082e2042d40550b400902009054903010400d948903016214044c500310003004c0049241056486c0c5090b001b00102200c6088604950500001c25220102e11440900450a40e002d01040001c01c1100c030100f0a00c40070300503292511030289603407144161007914030910915001c500c80700250040640150480144d5240704100682c83c545813176035170f080140e4001c1d045075650380490418802003840340c0300346058003e4400700c440c00c207c01e0055a00050304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 513346852 1250 513345602 513345641
    0x30d2d05010b041215090c0302180903040605071b03081e030c040605070c08160501030e0c09061215011409091c121b1d030f102c0c0301 60
    0x3000800c2048030207035813440c90300c504150382030304102400c03030080d4149200745031078040c841c02848030380c101c0e1f0ba056901c00c803070f43c0814000d904892010400d007512800003507041013008008586c0039034001c0800510440d1000c03000c0e0b20104500c10b0108140e4000e4501c0800003e081c01c28950044480e0704102d0306d07507096411801c3c0003c02c0d032510300942c060310043c044001180d2061045208404000381904022101c1e507540009801d02003030264411180403a0404a9491180c5004131744e50f00c8450001d060020716903a10410841101009049010240a840d404103056000c4c41810350103401491010600c8240031002d01a008400800b8000c6582000380c10820003500c2050000c070406003407a00c03001240104a8a070020280018180381a2025400b030070445600040c0f14003146040031542c450304030003901416101c011000f8500040d404c03520300342d5072080d034590100400d0b240c52441c6c0319841c00003151144046c1d484c2400341c80b140d84603010b040501c3c942401484142840d04502e2700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 513348102 1250 513346852 513346859
    0x708150406140402090109120303020409140708040213110c1e060105010206010905060415030506040c2306030405070527070c08070803060f0316030314040305060106050c030d2d0501 80
    0x100a90b02503801ca44220340010700c0344c140c0da200b025001c000d4071101040e10104203040c5400f60007944680b08151a6600780803041d1010300b10940903030f00c15800c80c0c9135403080d540c030359007000b83c4400149440c10079183d8443c541d5480000c0600038102080c50f95006200c007110340312004000400040718400c241c1d100c80e005210590340480d5550442c1c2c001c98000c50503849617800a0080c1c090700011300c410341921070313000062140c00a503e034000c0e4004d070703407802c000760b16001c100ba8152a005252540c18420941c00041801c0010066030702501400603190301a40301c2c40043d43d4100e80e0a1041c94142d2444c2d00082810f0100751001d40001c6241451205c1100075500c1c070105026464018201e08004030001e440d580390b40c0d501f604220001015110101031000c01c42c50310100500043d00040c031f40c2c50709122086c03142403c0703c003076070340010090400c0da2800000b200c15074858210b01d5031a0006205101d01000705024440e05001d00904132680d00c0306244203210541c0d048201e42e0780c000e05000041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 513349352 1250 513348102 513348119
    0xe070e100512151003031710060516060e061902040e0610020f0106230603061c020d170a030e030726040b04120201081b0a031509050708150406 63
    0x50881e0419030701c501c05401c4441a00d800c024440d40340d4907202e0324500401c002d1100310003403e800d4034425200e41b03100403040462000c031110200c070f40680e490801b810a110850003003002d00011600001d4072200e0118a42d918019503c40548004041c0e00010500c5450f4414858000300703a0a104000c5040070f1a0060484c04500e01404d07460040700d50f152800481442404500412400310000780589039903800c046200b00000c148501a807140e210620b4014a03042084031b00809006010b090700c0c010030010203500080c441c0c001c90b0700c400c11035482000500c401141c510001040c59101e0b885001d80b100c0642a00c5080c4d040b1241a0410422500003030001e0414008201804481346412420000302400d14400c9800220155901007400070304140465100b5110364401c0c0d907801d00701d407911409400401c0c058007104c1049102400f19540e114803d602c03603004061445a1541080c0d0b0301c400e201c045680584002c40060f00090130400c1c0901d420b039001c09212003d5a042010900d40103d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 513350602 1250 513349352 513349381
    0xb0108060102031806280f020f0705090117010207020909010509010b091306050405210403060e01061a0d021605010e0f0c01090303030f111912050402100f12020406030e070e 76
    0xb130340c46402d022500020081d035020310304401202100301d545040001c5a4054551105865400014032a80c00701d610f030044080340e440101c810140c07041125900f001d4140c0d40204034003145442640d03090040d4000750b0340d08100b4501901c000c1000240904107085407e003900c03081d01259000e0300c052024032001c400345500002856420250004403030300ca916015003010018042c0744050303600d03224140e0708c6040e02001807080302c0c0b25910800540c4c10105016003a545640728018562030041c03440003071402c00c28004d001400c2c41a03801441e2a1400c2c0100941000300342081c0d0340d41e0b654140c5541c01d10b00800034120038032010300c010a42050f0b8000001d108503040d00005040640300c01606400040c250040c144480e594441c043d2a0a249100754210010700380640740015070981010051b035060f8030a10b401280c0280150886420840c0c1c00c0d0b68500340312100200700031000c4055485d05034944050005030440d42d0780032034003018880c11b45203080c03240d070000d4a80c41942c03028480c901550142c2c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 513351852 1250 513350602 513350647
    0xb0403110d09030f030c0b100e1b04120f08030a1b0c05030f0a110d03020a0f030b1807050904060305010b0f0105090315100e01080d0809011a1c02130b010806010203 72
    0x1011109002c1314a421220000c4200000303028440d81000e01141d980c00701d80c40b03002e445800750304030711607900c400c000c0070440c2c87c0d141180340f581020001408a2000ca100741000b02d4007404445005800c40d170b603480001e43c011178464500300e0740c500340032050a1018424201030503007443c1212400c0e0b2580c42e810745078850071041041d04031001903e0414240a501500a0515050300b500e5034101c1160014019500c8120401d000650274807050301920700034030078815217680c0a48441d0485180c07801921107030b00302030450410b00005020f00c0100d0b03500c502400d8042c0d84a0000450030014802c20b2040507180d010000303044c40000d104585098034001a03034101c1080040300c103809900c0e140342840c0419050303000201e8640144c0b0021444550004082c1840c2540b0307560350aa03652841583c0d8200c600d580e550000d5034020b440100964548004000d280341c0034032080c126500c4056001610700c0201940700450704d511000d10411940e0000e400980c040002e001540c03901c5429401c480d0411800d14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 513353102 1250 513351852 513351863
    0x507021506040608010207061a0108040b01063608060112020d0204090f050f0c15070b0414070816030b0a020c030328050405010e0c030115260601030b0403110d0903 72
    0xc00140c40355a42d070081c5004141d000c000310360307401e90b50501802030110071103403089103400c120185000d548200001c1f4455a0071000000032a420a001101c50304c40c101c1d0301c620081c01c400c400c081414a1004001404031500c454032001e6880d155409090100503400480030300b22039010000580c0b50b071740c070b10112250304480024a2a100b403416061b00215001c01030203d00c2030082150003038600054100c100b80040b20f0000f003800903429000c415118080000300440d8141d000326001940945002d1084a20f20017a91040c90f12105d41600d070501800b8285400a00070b0303000c009100455102c542c000d025140f05606d05800707103034419500d00c4003600200003450b8036030685070615242c04101c448000c90800c1032041d4141420500d01070f10603222801c8031381c090700004910500e014458288039841e0680c1a81d100c0f894107101c100003030340c2218144411400c401c49002c0c03c207410300581313028500c900b641c003203242090704008004e0204828040081e40c0442000f00c1035075001480030045981c0f10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 513354352 1250 513353102 513353143
    0xc060c15112a03040f0e10050d06020a0c2a050907020309120c040213080606010305040c06180902030103120210020901050729160f0804120804022209060609050702 72
    0x105944002c0905008104240e010204020940080c1c03e8034079070480300c40302c1841400c0c1d00d50f021520703003540d4503101c0c240d40a8215044000080c01c5500585400030a50406201054850300c401c4440c40c40307100d4490413030f079000c1c0d0b1503100098880b40302c401501307081d2171440701440c1c8140040e41e40d2060541c07891050301d4500310b02d46c2c501c4040006204000c0090010341d02c0350b001c403851240c1d0035054040d450841c0101400107089505c40d124280c41141c11a040344038903480d24209881e0000385401c081490360031241c000c501c210007800150b0017180300c0d25540b901c0e86030010b402424503a41c00c600c03c01580c01080829560b030707400400e4440312a0020030115142028820f6486887c1c0140c0300c816403d1000001c2290301d408140300e41c051180e00b0b46440e0070340104514100c2301440c04580c0140495404054106024410144a54010f20140007640b120000c10300038092018451030f1144c181f626204c80c41c04003c00350046e24010100c24205008500b403003203005e52140404031f40300700c09500b00f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 513355602 1250 513354352 513354397
    0x507110705030a0b09031e31051002010207050a081e04030b0f131a0601090603092d0b0901090c0515090409080d09030801050406080601030b010e130c060c1511 70
    0x2401110000d048503c22859a110225100c2c00d141d04210324506a0300c60008c42200881e1031446140182586a11052081c604050801c41d000d40c194008a00b15036080c000900058400c20903142d0b46409441d000d51a01404500307224045002d8290b1503404009100420001d00c0d000c0c14960010f40011101d18107a40300907486441010000d409000307100010710314551002201a0035014510a03a0341c0400552295000e405a6044020050140d20320682031003141c9040c541d0001855100201c00f084a1400c1e210b83d22090b20644160003140d64810719142000180c0030b003880180720640740000006000c43c03c9000c9401010b092901841d02c9105040030052010700311034010104403070810801d1124100141754020074001c840c0290b142076400f04400c880041d60314101c170f174021034224603070303080410301280414050034a00c0201400928080011107611a00002d804503644500c141032040c208400d00f0142d070014156041e1130b240d180c0c5d00d114042c100b1102c1c04001e40304c01031151402d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 513356852 1250 513355602 513355621
    0x3030c0201181a06060903030706050a0b060c101a10030504031413090f09080301030f0f020604060305040203061008060c0c070f090c0f020102130522050a0507110705030a0b 76
    0x1c0080c128158140d00000b98001c02904000d015486120409490015a508000d1144520981e91910307071541c01803102e08001140ca4200d2507000560a4012035201800700105010b9082010510308a030448100350424040303078403501d01401510002c0700d200150300c0020882240021290100301615070b00002c081c54019030840500040100c0d40c40e170741d144240e4003110260510301440200a0030310001c50803204d0f1500882c0174a5030050760a51840c0d1079651a840050015041186e82200104100001d40c0d01c10014000400564402142d140f0b88ce104042c14504028102202c407410020180301c03030100040c0d0315501220045000343d9070302d0840c0e0100e00c0c00c1186d41c4810780a0000000c081071480f00340d0840f41c4c1e4011607407100d5203030300d00004082c1d0907805440305249020310410010486803509682202001a00076521004400e03005111010f0fa0422651031111a40307881c10320181c40e07441058001c4005481000e400010708100000c1d4a856204502034550002c0c2c102145240301e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 513358102 1250 513356852 513356861
    0xd02031b060118090809180a0b0a0b030c0a0c06020732100b0d051c080906070e13020403020409260f030f071814130b010206070c06061806050901050f0d03030c0201 72
    0x24401049020018412016200c0e0b207c1d04070380380d14402c2d040c07811600d071900b4152440800d94007885842c900f180d03140d41d085200381d0000041c40b4108460201d0300c1c00402c41310320003814001c2c05113045060034040507041c840e01c00740301c580c0c440c3c80038480404542040d0002c9008104900407a401240114030040020040c030001040a0b0044c0991441e1001d0741c6424104070034001040d071103495007079440010f80c0f510ba18007141c9000104108401d00c1050b85015002c9010324810940c0040c01c054403030f0081007c8900c4c00d0740c202c5407024203c071050700f007040e000700380c481e03090034a0085481c00e2201601d8400601001e0003103241c4190b441c0110341d1840c0502d6485e040d41410941204045680301c0d07902e0546a498281e850040007828600125080140101100000e040e002080c2e20341703400c1011942c106510400303440c941c0ea00e28010814640e80d10100a10300b81042c1d002c58114203060801c2111007040e0700451103506405610410741d12602d10210000c0d416080020b600052940c9c10703030251 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 513359352 1250 513358102 513358117
    0xf0f06041d0f060103090803070e1c03030e1c090506130302040e07151707080402040905010c0216080303091f060302031e060a0b1f03020c0d02031b0601180908 70
    0x34041211001003203100034442500c100d0b940404031085444070b10056003260070400300544000070400024520b0741c040c02070a060040c3c0549500100e10320754803d50010207108000301c0003c3d0702d03113043c44e0340280c00f04552400c909924a00415400318024090701804003881001e00821000c6160201e41400b503006100868015200380214171000c0040394030b0322454000e10300040b10349c50045003042d00c070303442ca07100c600032a803c00d040036200c0c1e1000b6610603900a100b00e900503194904600010000c1c00b0b4882498902e80080c503141011a001c1062840c858110440c20b070702c140200040c403c0c0010302c1c44d104410603546404001021480350001d4240da800281d0148200c4a608200c3e0000b0003a000c0f142c0a0074050300d42e161607c140c04015101d1130754045e1303031100d0340d031081502c00c0742542544402102c07a4240140350002d5406a1810500300ea10b598000d46c0010408420415580c2d1a10000318001c0024051a604201810448021007110b034040c4503174403241d00c420004150203c9199 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513360602 1250 513359352 513359369
    0xc020708070806060108180703080304060b1f091205100c120c050301030606080d0804061a091006080c03190f02040503010906270b061c0b011805150f0f0604 69
    0x7501d07111004280c0c0c83c0010f40342180011060070002e4403d1003d42c58140c0f0594503d4041c049030307803a68817814188d0b00081c0041e50b00b580d840b090720040741d4075038201e01c00401a170b0102c10703c8015803620241070301030305900c1400b0701d00150074680c000030307030101e620308103040003650000799401166411100c2860b441d0380340030300714a0140c01c442e01c181c0042c003035412a88240400d02c4096115031340076844040600c402804140703000003040016000340c2281d0a480401208030f041144c0d0785c07000850402d019039910f02c03682d03030080080c030020303900812003580020b076404868a14102009000000f0010201100c000d0b9602c1841442510482d01180d000b071034010024091300c003031410244000c100d01038425051107008141c40340e180f03080108800d01c0d90340241000e8030302c0d56040c041c494035010446440d440803500145200014640c000d0940c080c0c1017078506601212403007181d02040319000703014a0544005008504403c4e510320300308804000c0140ca144001d62658004201c0074029030300816103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513361852 1250 513360602 513360613
    0x41704060503060f040b060a030f0b041d010c020a0b0f0406060e1609080d09031b03050303010b0a0e0102070b030604090302010e101a0f06160f080f070204230a0c020708 74
    0x40c92540000518020790b012070b8040350340c2d00f0507020881101c034003d5400340c20074000d100e0500641d0007940701d4100760780c04440100b44094060009000c0b06c440c0d280c880c46514800607241c550f4a42440341c00b0908000e4001411904038035101c09440000060028039a0303440000014200545a00f000008120061406000c0d04010389102c0120700940c0c0440c0001d61907600000702c41c0c100003050325080390561140403005007907031070b51180e041c88040c201031201c14003180080040c02c2000114000c001c41e034002a10b409980c00700070403c11355080400d0440d40541c20510404000c1000c4a03009101241c0004184580e441c0c10fa02408003400500c403240a102820720f1403582a4000100e080b4004540d001591751201c20020595000400541c01c00c0040c064a11421124014005100d0003125410740c24000b075902d00e00c0c0d9a1143ca20031058110104806045007071900407260710703032a03180070103202c0c0780b0120300601a041c004050300303075640c0c40e900c2c5031448500900903040a00301c4041a44c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513363102 1250 513361852 513361859
    0xf02121c030605030607020109111309081801080a230601031b020606011215050423040303140a090209070e0f130204061106040314030402011b0b04020108160203030f041704 76
    0x80c01800c083c81528081d0080400080388640f041c41075081346a4440c00081080300d0b040180201249410442000160f1710002c0c40040b552080180203001007003003001422076451800101b42c00c80103401040064182030300042c1440401c040c001107100003410401c05642c6160040b00980403a900d8804000314665154810960206006202d40001e0301c0318450b0354a681501021038220480a1000740c08551050080380340642025010303042c01044120b4206500000611410b81035808030b002c00e40c0d54081d6011558882c04035607001080c008100040c40c2c49401060003090300804000420400a11032407069580d020328103401040600058027621b00007a005001350300c03038000d1102241d0b03503640d508a078840004c0c050340720740e40c16505d0000d1000e60058014844e00090300c12814808091a0030381494881c4541c403461034060802c412a50810f400090200403000d000d5061940c0514080f00034650000b0499030449a00ca8800b070095441d4100500e039141e2440c4450b04c0c0300d50028001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513364352 1250 513363102 513363107
    0x10509151902160f0308070218010f0f0b090d020d06020f070b0402030601050910060302280215160903110f0301020f1b0a15020310050433030f02121c 66
    0x1510074406034080b10260a14020700984a021038401c240c070084512105000158401c8042e25181388042c1c0640b01049040500601402c400d070411400c00325010404c00114500850310310040101c1150140703444000c0f0003107845003550b0040a03004856004810041001560440c0c162440150a140d140c4841d880d00312142c0c40142d4003030380f181c13040c207002090030318001d6855401598209441c0d00c0e018075151040d00a0342041b044a9400f4540b40300b07130700160441c080241680009540500040b6090402001620801811490103144404001d10034190001c0b80041504c0e003085682c6104004c02002540e1000c00301c918540550004c240612080840b6000c0c0c103100e01904a114050b0f00c2c0a1080c40d556088c8050181000c946d900c00a03d2200f8158011a046918650034498045e10707100450169241802c1c10060f445c1d856072480e051041090f03050150b00e003040c450351030305841d51310b414099440c0010702920030001280e201298800c1045022017403403800042c141c9a61120300b02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513365602 1250 513364352 513364387
    0x501051501080a020909041b120c0815060f01030e10060e040c081212130b100603060f05030a1b090e070e010510021e030d0f0f15080c01050915 63
    0x1400b2520328804688035a11500950307443d0000a8008109a07136541c4a0309203124450408141c00700008802180107503088009070090343c0101515190945000109460011500450304e880c0c040d02c4248241680c2c4c0940c10912148246001b046264203042424101501600c0700d0901501d80840060003008045d03010744514010442410150b665600040e10703510207201da841c0c025010040c0c614905010382c0c0c81c541200e00e207075945540e40341c2540e0b80ca4034244250b42c094056504a2410412560701d4000d28001d0100c001e54000c000b864400820758400c41e4060007404079140901600b4a006194442002050400010300020a58050990302c540c0c850003100d00801c00b50340042000c1c02c1c500c0c2c0410700390344247d000f0320031400110808038501409204484050104215450041596000d601018417240e0000100c002120455400300c075043d01c40c1c42100020a0300c2084002004681110004c0083c246541e07504440000514460b0445c01d50360054240400e44c80301d0820740149 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513366852 1250 513365602 513365641
    0x30313080d0f18030b0415050702060402040b0f060f2508070b0601050f09040506031f020c0705010804030c1421130b1602010e040212091f020f0a0813050105 69
    0xa0710422810110030403a21500010403e890110740081c080000800040650340e00901075030200709454145003e010917200300341c1d031150041c0e0020040c00b003545001d10a072040c0351011074412804140250105404d4025145021032850780403900038030020003c5c1c3c804c5400100da05043d1486026407403c41e62603000440156041d125030b100090780f81d402a1b00b00c075150ba80e42e109660034105d0a204000c06000010031700c5c0e0b05070164800c407046050b58131210704603041004001684401c1000c101c1803420402c2d62145041003000c000b0311002c030760814440408603800400008808090291a500c0c1c1f07403c51104101c141403507816011040352280181541b021110b01502c10640e42e4011344901d0700842c00340a82c401d400c2c2c3d40210056010b040a03403156000600007504100d00640300041d1000110740d200c00304e411a00c005480b440807903400c4008610009011418403c054034880c025002e40100101441003442c045103003001c001d0050940300d40e110300240810b01d444a901c899040141d403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513368102 1250 513366852 513366857
    0x31209080f07050a14010210060f03110603130308100f15121119180f0314010c02190503090409050c0a0b18010521042d03090311030313080d 62
    0x840c020760040041182002c5820081c056035001781030101124105180342c44690540c400c43d851100c00645030b0003120000c000949840507507500d14140315912290003000144204001c008005c400342c0051080d151194051800010703d659007451442c0541e0b09400c20300700c3d07144004c0d00140168100442c0c1101030501e54444e018080b2404103042602c86160007210070340c009203d0011031481800c4102c3e0f100030185801c581114001d07041c0b00503640c59820443c0381008816042c000d1200200103040404906002000b0901e15050001e4407001d092500c0418451044002e0302403240400540e1607210004000304005009403900710340c2c5090300c039030b12402015100d80004181c8002000d44032551081201d22055a50301e100450b540d521003041d8020112600c070390788420007103440e4101d00c110b114560006414020811480c0b0782e4082160605a1100019a40000030f0f44180c030201141d0340645208018200440020301354055921040707150420100c0000f40310300001480c1070f2428054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513369352 1250 513368102 513368113
    0x509010c1d01081801270204111c0903030e0609010e0c010c08030f090a0f08031b0405030c0906130e1f0e06071b0215070b09010c1b02030703120908 65
    0x290000100c850708251240410002e00000b60003600d68000071800000d95000018265120501c0c044074502c034100e503020f0301c0f5a203200b060840c1820300c1201a8200603400060410114842c000d582000c1c030000a012140c0b110b500d04101402900802205040c0720305488007458000c007550f00134038094581c42200d00c03840405591950052510405807900724240a2455075464a1404124400782c0080d0040c4100550320300440e4543c0c4006021510844d04640d5030700b40544d50b111442004141c0b241c900e0f00c1008100b04554001802d21290803050350809030361703542c6000107101c8803000317058003d180d810004001c0509501141d04018041d4180032036910101c014200021201c4803010b41c5481d0344280b01007201030340a0000a00c01e84451507402c00504082c0e404510340c05903c2c0711f005000d07000800c96400308408000c0c501d80c4061130724000c110580800f40c00400e28000c9040a01c030b09020041d41c101951400d000c8007000d5a04141c64003a540e20281e402005042d07540300362903039070041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513370602 1250 513369352 513369377
    0x1140a140f16050c16080703030f03060b07030c02030a020a0909020102061e06011407020d030503060102190302030f130306050c0c1006050a060f05360f21100509010c 73
    0x5194220b000340a078040219407108030071000c1c2c4903544003003003100700b41c1301d41c0c44050169100c0b6a844409892a04017030f010151440c6400b500780c89203003420006040c03d1100500103c90401c00703a45203e03826162070314501402d400424140054414080d4125803035690108989400790403864a05100380d088031031a90f10b00c07188180c171003c0070b4080c419100408000c0342e0550310841c035030068030140740b40c010b103000083c2d40000c591030700030002180880c80103c01c0104d1582c044c082001660141030044400401c1a64001d499200e060100c0c41520000701d4a5801000c4131202d51001c1d541c08001004242014545484c3e20380104100d040c007486001180154080035014000445201030904291b035810014180c0d000c00841c403480b400c202051051181d042c0303000e80003110701240c0c0143c90303a05c8030022a6a04840e030303011846501a0380c1410080501c0e49800500074030018461107140c0c0b10340d41c01c00c00c06007440981110500b10908040602002e0f0360103511040084419403191402003d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513371852 1250 513370602 513370621
    0x1c0b042903060c07020f0a0e0405100c020c0901090f0e011109041113090506060702100e010906030221150907081509062101020409060303122d0c0201140a14 69
    0xb02142c1918080300c00788841801401c005030101a06c01c0000c10b14040d003621011000041c031411641078403d503100303c1800711205103d12a0880840061001d05520582c1300c0128603114018451803440e40c1d5240040400440568002c5450000c00402400b40c0c417804d1640183c1a006000e4003440b540ca41000319064603401381c00c41e2146032a29401c3d038505850400854014000100780d9500248200140b034016070780c11041450f20045074a80c5407480000d60001030a810303440d04548103141c8100190350404510b4158111406030144e03c000706540c0d2100c008000810700700c1c415802c64920400e000c1c84682000009120380101c0c0d44090107400c0d11000c006c08040c0a4400b150028800081640c2980c00300310715000042003a00094603240c1d0310308000c822a45280c1c01a000603540f031501602d005e41600405298481d1190045000740c1c1c0d2401094066075807001c040348041d0348a80c00390340c4600030740080c00e810303101507811481481d12480740d9001e00301c4031121428149070003000990241 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513373102 1250 513371852 513371863
    0x50103050d0513120501110318070902211f03050312060103060609091802030304060306060e040e07060819050c0702010f0930051002090a0e040203031c0b042903 71
    0x5040c1207901c004a444e0400c105404694180f060318103548134540890203005040046006a004200040c1c941070388030706c80c0e414401290007010f0510700400800e80c85a4030b8403501c0c18504a028140038080e240e403100220005002d8851220a415444c4001705011000c0064403200c0d000c00f540b009140d5410004504031030035030007540c0c0401c507108c3d014400040140c3c000c400008040c80346650440c91900080c1c079542142c0d11190006c0d8442c9010301c410f50348544400b050000c1510207000c0c05040c420a04d4407540356020728010001d0390b00c0003e48181044000181c0302c00940da0410450900300f0100300240d0007450b01f0390100f40318500d90350741e45200c0c150903000c036003610661010780c040c1e14843d4038048030801034034448110084031035404514144003111543c8600c400059594042c481401011440c42d0f0250741c8606c08035042102603100401161403840c10014940036000401c0305c02401054520140780d0032a242c2100c2c0b6021a40600c030010040a0074903986180c0100a802c16940d003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513374352 1250 513373102 513373117
    0x3615040803040b070e091503160e0702010609110a03020705030d02040603061706041208090705120705040e0d0203070201050337050c0c030708090301020f071b1a03161110050103050d05 81
    0x29404005550200151403050900d01e008098520426034000b01c12127009607500903151019111091007251034092007404024031382444180705901150188511901650481078203054000452000b04242071048401500114108648075a101d480003402480d00e0702610942d5604201c000c003203c0d00015140344120350000014180f03441c65841116199070290154a151245040200c1e4560300c0c1c91000000c1c80554005080c032034504010081900c107049200110b94102082c0000502d80c040119000c060702820269526250300001c003100c5500301c0c5c00501e80e05d00000030310000c0010f00c08450000000c6c440184500d4813150b10144852160000f10005d6034010802200069114000f51a0068006000506080c0c4540540c0003d0340451401c4a0249204001c90540005070300180d000c3c0030702c40001c02113075624050410083c0300240c11012160001508000350130300c140504611010401c0035074219260070503520001d01000c1c0001c41305c6000d100c036110308480c800d20503100d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513375602 1250 513374352 513374359
    0x1801030c082401050d021b1002360d0602030405060c04120f0602070c15090605040612020c01150929030613030e030115030b3615040803040b070e 64
    0x18401014014007034a00c240b41000e041c00000d1244011540443c40984895806080c01900600b200c0ba0900e080c008000c0d8000d110600c107220b0100104601001c101d4501801c40c2c96801381d06160107142001080d800c038299102030a28001170030402d998002c0e6000758410001c0710026140c040c090003030750140e40138400c80c041614034008046102e8864032101c1c03d014100c010b01e4246981c56410490a05030408a0340c0e040d41c0c40205e1910303900144440042c2124a095800e00b41030020003003d0084e0381c012008200c0c0c01007000003c038802988802044088540d190707820a85d0f0381a548082c007800e400c041c14074000504450041a06118045051900100500b010703a481c001c0001c00d143c0c902070140c0810040710a0072800d900d0034400d90044074241c2e105101c0e90f502d03501d08403920038001008031489010f40c032031032880d00c1c20500c3d4040100140d0f03003241c80110030340ba90782c40c600506521102801070080041c0402e10065100950055000e0150a04c4a40e2010300035280c030384540c00b0300da80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513376852 1250 513375602 513375631
    0x50d0903052d0106080c1c030e0f01030f06030507050a08010501050312070c030605010b2703071511100605040b061c15054b040504030302040b1801030c08 68
    0x20100751007031481402c07019010030400d1004044142403c40340650040382c00e5610a400c07407541850103484095151421042100700300115540c000c1980222041040c003e07000301c03440f24881d0707020790411902010076850411030190f603801d102c0c1d900c6001c0c1c4181070082c1100100400c0700e500602550b4140e410203030007840f10024556040d50641d0200030140c841d400d669101100182c09070186500070300010100a840d200d00e000481c40702800d0031807000d0f1901c2c20003181e0046d500d02150440c102e444640312549a030b10a580309589100f0400600c0c2c02c54020f1280c0e25011040d158040000d441050303400b00480d4040c8002c1c4001c40c46001407001180000340058074004945402100c00c2984600d02202c5c2160b0782c80104054240810388024030165000d800804d01046111280782d0301022840c0c4101c0b090102050031900705032000c1c081c01540c4410028040c94043e4046074003c0501c2d0080e00c0d0f480140003a0802407440e43d201c014006820401424191407241507102d000c4c2c40140d0700d525 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513378102 1250 513376852 513376873
    0x41a19140f06010e0d022b0b04170a0f0e01050c1e10020708040b031f0e071101062d1a070516050f040e071a070201140a0903140109050118050d090305 66
    0x2104459006080c0d0345c880b0304203480c0b402c1703884a11200750914230600c1140864201440c20400c0000d59402c04e0340d85030014441d00e040c0c03030341c0034454050042d0582400304810b078410004941c030344544203160607948542e140b80702003021012241c903200c0d545201503602104141d01603509903c68580c0c044c0541c1010706c0180440c500c680b0083d90044100c4000000c91510200d6500001185030b100050f20050082000f080c5a04003010b44040450b1600030003a40d4104201580c1005050301003180c0700c0080840d0380340c0b080103800403d014046c1800d2100b012080b0302103105265002d500215070901480804004002d000c0f010401030310f40c0204000301b541c081000780f1008110410821943e0310940000003000000340302e100640d01c0c0046243e0343e03a101c0c00e000240c220419410380002c4d481080018424495108030001c00f520b5000d102c2d41917041541036461301509035032201070401d510300215071032500028100140140d1042064810b40c044503003041c0c1d0003940c10721015096810120959 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513379352 1250 513378102 513378109
    0x30318060a0e0919050604110d090203010902042a0f0c0213020d2405010504120204090302160902130e070f03020a03060e01090f050906041a19140f06010e0d02 70
    0x10041c5142500d400045401203034000f40d254481581c1003154041c6070034110394540614015241d00200a45080c400030142e50024211403240d40e0303418400d1580c4101e010215982034002640701c50b00203105006801c1c41c005458030418490700030480c2c0039000d000e186091409442070740750700040c035220b114104209030240b1030f0604071600122070143d403c003c03450786001103100b01c02c1c174a1860292540c1c07003c0035200c8144c92690903042075051040a000070030186014103003a0300000d60554011841a100385026803500c9079181d82080c218903074403404070b405103803540507150b00c04200344070f220520b0b40d412000000e4002510703040c000030072488424072154001d400800c158042490005038070350f510000d00481950a03042411426100d03d041070062865008003900125064003130811810103a8800300d4050424000004a03046440003030316807040740310410680030140354203000001c046c900800381c0d601c00725280311654142a0105155510800140040f001c02601c0015541000d8081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513380602 1250 513379352 513379357
    0x21903080f191a0a0f0e0c0c010905030304061401052704030207090204030302071e0506071b0504020f03041a0907030602090409052e020310050d0f06151403031806 72
    0x4210010081031a48588461a00c6089102441c0403603032000c0d5841502002404c00c1d82c0c0d03005103040981d4000030302c15011035100a641104c1c240108a50364840003074200c0c094106010054100d000c08030400080c0a815008184020310681c00b200203680c031a402c01200b0043d00205c0b1060b01c6c10700d003000c02100301360100c851304035001e40107c40342c6c15910202c410681e03211740c01c11001070b00007050812104000b820391302040c240c008105000303242003a02007002e40c09184005005204c0040c3e159100b03a45010001d805800301034001d540d100e00e03d2408580d80d60042e034085421304104500d2410000100800794080e02450002c0d0542510b0b54503050040e4014808866002e641c904044000480802c0340b40ca03c071240e0048041792580b91401c000c5070280c003840d0010301500420400120103044800e03c4140c801c22202c50442100360f040c90b29600108003c001e00c001d15003d07820b041c1a00d00003200c401c40300c01410007a01d0001543c14151030b03001e19031808800314203502c1828072a1500c0b202 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513381852 1250 513380602 513380611
    0xb030406060503061801110306010f122306030c0a0501020606010e03011823060613020304050102211504111603020f011b030b0d020a06032403050607021903080f 71
    0x4581e07251114002424004c0a6401d0a02c04004400c05000d141c002e000d441161596103031020308520b40100007030910a0701301c022000300004280d500303d10069640c01400500d804044801c0c223890365100307058896000b512068841c2c03096049003800b61805102250581708180d0251029481d0000107444110151852503455501c4002c1070f60200c1d030b06010b06004034014540000c150700200149015a4141480740309607402500c01c000702c548030344080203141442c0c268010395a030b8803824014020300900a000350f5030440c0e818200c0c80075410a42c070500035140e40303000f00d034524500400c11003250b8045244410801c1d0600002d0010200c02d942c441c415070107030064418000640c040182118044445102507050b002400c0f84415494413a12400391004c0c0d800d204403c0440e00040e80c007240f0ba10500c4101030700c03111640720070001c0320142240d0306000286a0071240d205e2400d00c2e1500c604491000041c8240340b144908130005181101c00260035446444140d103079614038160f4800d0050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513383102 1250 513381852 513381863
    0x1911070203010539031f08030d0603060e0a020918010207080a0306030611120414010e121905160618020a080c0a08010c140d1104060f09080a0c0b0304 66
    0x8200503880078015188a46150f400d0440c002d400225041c294200d842803d084180c0f100440d0300c4051000c2c0700312608503803120f4000c407a4002c81d09502d040707221a6008841a8000420036500d90344880e0029410f40788103100a0084801140d4966500c03007000d10040c3d80041d41c00301050950a1000940d013000c900d00001600c0d2172260b032554009540441c034024002540d8440400c02d00c000ca00c80e1140040401900c14584140c200144600d11400340c80900940c072407403c034400e400700135400b001da0b1400c3e0300e0035600c2e1110f08400003c031907040340000c0f117180c00540d241c03103480c00e21801c02c641d4024403a806079481481c99480d800c0c020441e85207800d41001001800c500566159031882c4000e1910000502e00c407c0307100d090200011842e840341c00710742c0c1044070b44c20015801c030b0740d254000c01c00600350703648544820900b04064000c80302c89814048002030f001c5501544031003d046032411a455140a40d40d9070303212a5a81c080d10301000d0b00000d0120401e0000d04200030003190400e001c1c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513384352 1250 513383102 513383107
    0xc040908092706010e010f0e18090102120105150a11070504110d0f090201020c0411042d0b040605030705071b090b0112090c050918120714061911 64
    0x10225401c4500504034864800c0e00034003100b990521801d403641e00040038a408583d004140c40041d042c0701c03010564909004c1d00440c6d220a81d01ca2520b4522000010580c5400c1c500300740310801e0003980140180d41c0d0304c0118400104183c103250181c1d8010385151410203280c082401c200310b80c21140c1050652060048030070014a6a58600400251070f0381c219a007681d5071001d40c00c8000b00d80840b464022000d080c001d0010140c2c0c0c0115500b0780c0d200080d0340106640040858041480c802c07030304282d0030030301407049850900640703010300032002e600b5070b6a840605842d88010000d5006500c101c000281c0d0410014228601c600013610a030b030b204000380b0404110704510f0460b0814541c000840c2c05950b8812041c0541c1d01c42d43c402510b0304d20910030080c1003003948507501003000a0290310300030418076020a842d4074402c005034126110507400d4421000200800103910380c000c2c1c0049d1008004a0600c1700d03220008aa0300d8040c0403074846480c450402400e07208064820740e4204003a91006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513385602 1250 513384352 513384367
    0xf18030809150a0b0103182a0801020f030a05010605070804060f090b0a1d010e0d02041a12070f1a0901080c040801020703080a061203021b130c2607020c040908 70
    0x40e90503090140381501c0001c610f80400130001005c948900c800c000d14641d0400c10b00020039800003940e215841c1c211080c4044000388100d40014055540c0070540d59880024a2014007007050040d5015400003401400540d0b81c03049d080707642d40070700c180180100303104100800109005002c001071540c0c1174280601059070303419900140703820031051907000c0b4800158072941c41c2018121203000c00002d081202000324050003258501d44201002400307139039512204214104130340f036070b611041d400925800140344220501510791502d0310850306880d1031180c6c049448812100022054010300c10741d18101840d072401100c2d840b40c041c24220314641e0403c00454184404c0c002044424065141c3c03601501384558401c2c11074281d5801f0084828120042c2c0340000d6021401d004940c0491020100121003140029180b20100b02d08540152401c0f00c5074040359004929003150a1000300e14040c0b450202c50592458a8200d903081c006070849140030754286840d030b00880c43c2074020032219050090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513386852 1250 513385602 513385633
    0xc12020111160c05131b0f020d1409040219030e12030406180c09020a12270614010f03061a011e090914011e0b030402090606090306010b09040f18030809 67
    0x30003c80385c458582d00e03550a11120030501c03502c850501c41d50320344049981d243d0700000b522144070fa2015020000c1003035541154010035402d507140000d00030704c11942e4041c5041c075a4101c03080c444618002c00c4c1400c060a0300d000010030f0304401100720030003031840c40e650380d0f40d1040201040c12040d09007250b8903100001089a422801c80900341c0c2490050f6101080200500300807407071005150081c0c2030050500e0b4a002960165500c82440c0d1002d0300d00c2c88042c6814009080602d410740e0300841101e00000f00c0d0005407002c0c1c01205c0c000c000400031503c000c0e8103401421582980c05001ca011501c49951f1a003031841030f007080140d140ba005e028036440d03000c140c060701c1d843d21008036607445510050010306042c0f0500300c01c1212004c005101d20b0b1402c21420340034000248040d12860a01001801d6070311813a0869807040c1700101501c00d25030310351000841c150002c125141c080d43c07404084802c500d501d80b05131141104020802d03810440980d80846481a0084c2150310074050000860721044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513388102 1250 513386852 513386869
    0x80d050d05040f23120f043302011a06070b0f07050c160509010806070f050f07080d050406050604060b0405060703021903080603010510060e0d0309050d030c12020111160c05 76
    0x2040164040035560182d144c0f940b070101c4c00710501120003001c1245104520b034110440f400c03265200c0c41910b00c146200d204611044007052880b035504e4140e08448a416410351045580c40d41c0b414014080c0c403010390034403059003c0e10368010614000c8401290f1214030300d60700e140d400742403460424601a041d20041e41000185980303501584000f1500344001e24003040d1403405406070100501083c548a000101541c8011402200741b010015070503014469030002c8440203a0405403032652101408802c00080c17400712000e03510146001c0100385186801d0082c981118500d0741082d0400e410b260030401180d01800c41141984516a008140c600421079a0111180aa1181252460b0540600d03007035500042403442521040d040a11090703030003501d140c00b8068140c454001d003141c01c0c40d0030342e0030f1072054005681c4100d4094010041543c4917072807207816403040380911140f442c002016401d9030503140c2c00c440420014400c48a005a29000c08180180900b511021890791000880e2001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513389352 1250 513388102 513388133
    0x5011206150b040801021206030c1804020f101d060c0c04150905070504141f0509031002031314030a09210f440a09090c030b0109080d050d05040f 64
    0x165004036901c19039a0341f070b5920952060080e40588041c54411001880e001c004851802e815017a0f00e020909644400c0310403445000c0281c00394410f101020005044481000c1d00c0c00501460004003101e181800019504200004c9004140e0030f400c0302c0c104000361292403030046185814038000074100c1c440d4050303d40210390b9911800c0d074843c1001900c80e8030b025140c020714010404038445610700c2c20300c4295200405503d207440c586603410300c00041d041075032900314100c883d0700200070302c01d03008600005206001d10076028041007508980d1003130b4030380c00f80781c1c10100410071010301040008103500004000f1221041c07004c8407a669070b50760030384e103000f05074042d600d005d40081407403003181e03003214444620403445007510340c40366030703250200c54000450f25844c1140c1d202180c0d280c005400766070488058019150140910403146c01c00038018031607850414005003407200000b82e03012022030848182c11503566400d141c22014490300c805014041e0044401014441c240b1021600a40060410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513390602 1250 513389352 513389369
    0x30309021507020906100c15062603090d050f030c0c012a0809010e0406080a03180b03010320190e101815120b0702060a05011206150b04 60
    0x25155640140003229190802000410108000c1000542e54245080e40c1c085001c98501040403c5181c04644c000c00804008151000b40004400a50034680042081e5504441e440d6580c2441c03030013100080c00010720b4007400390010403042d0503d052503200c0b403c00301c0c000d0007100c0c1e0501400103690726640c080c0d503022f400c03500f0418510710207613401554441e6500000c0440424a10b00c50404aa04035040740000c010400c0020810156400b9103959543e100c0002d00810a80c0c3d40d030108607480d100442c8040b80040e144240c1c50701c0546042004100703030354140c0300050941e82590f82e1284d400d92244111070b41e42407080b02039803140d61504206959a4003501d000c6030003601d00100f4414512000d01148140d4285020610641e480710b803084810b0f04140c80d004c11032034125030850203654042c0d0001c03070025402e010594240000884601d004031401d600321522541c4960036102111000e0245042c0c29280074508008944136820020314071840006110703413240c0d00d418141b5507a11980c1306825 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513391852 1250 513390602 513390611
    0xb0a030c08010603021801080402190303030b03120c070b0f040315020c011b0e040b0d122006040209070507170412020319020a17030403050111040e070f050406111204030303 76
    0x3125603000508500521a5080a5041ca284003010295100c3c0003040b05040042000000d4259901c51240f0703024035805002e071003442a200c1c240100948002c0307540c40c0c0a4410460000020356002e0111012240e5820250000505002c2008226800240c410307540c4601400080040f8800c1c000301100f459003594010b0352903201310100307425543c4265480c00d21500c40b0b04050034468000360450b5a42c0d40c01c890000704140c0030400034901043e00e410152040c2d1145030460380d42c80d000f10182c1541000c4a55441c3e010140c0c1520326940d4604850003500310005101055496020358090301c1100d1089580d0f21000d0302030001c5810380c1c0c1155010780203141e00c0d40040c0e03055007000e005e8036000c91216002605200700a4020400eaa900c52051400e444941054001003403424070550300510b50100c000c3c000844441c240c1d5415811a002e400406200c42000c211203c0c043d810350090048152601818949040c10035a0707150942c04003200c16004484d8011241480f80c0d00800280d446614000b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513393102 1250 513391852 513391871
    0x307030506131e09020114030406060e0a0b010504030b0402010c1a1e06031207080c0a0b1005030616050306191805070903030c060231140d020604140a0b0a03 69
    0x300b2107581ca440300b1101490040f0a040d03542c8424054915040a9440482c0140003440100e4280c40492402d940c034107000f005200800c0680c1d0001d004494891a2900ca25203d003065070088801007080240402c50807c4200002043d11001952003401410010103500c01c5c1e4841c2c621a1030410b05c0945401d10301c02c100305100307409102014460010352484401850a40e011a550782c3e401c882491341c022001c10844100b0221500b1110500aa038082d54042c0900345400080142d0a64105059105810300032035241400180c80d441131884440e000800001c008068400d82d01c0941110b8210540344800e02140e42484890001002c45c5e007964941c08043c504580d00315000a08800b0410510f40000c03c0440d41c4034404100c007a070044001179540d0101038800c003510b035980c0000546199070b5001440700d141813590801c100d130122078648005070342d43d00801c244400c40d9007000b58441c806110500c002c00103e2001070000c0c0c1c0c040e020200f5152100c40b00340c00c40d002160300c40c001035268061903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513394352 1250 513393102 513393109
    0x160305090d1416030b01030b040606080d080a06090902090f060616050c030f010903051b1504031d010306120b06030307140d1103031312030f06090e07050604050d030c050f030307030506 81
    0x140b28603407500404540303d030a541e5015000c480c107103c040c0c001201b050104003488401e0b031002004104080031900e001070101e00c0505440d000f1207807903100c81d15045000031046454003031076400c9540102885996659020045507a18000d09583e0308401d040c003181d01c440d05030420300c0388024001c000804441c0f054500705032810048151419940e4103218400001903085015201d00510202803414882d5440280625140f5030401c0a07040c3c2e28110140000d054001150044c1d00412200c803442001d8104015025a4282c0c854107904c80100d240140c041181441016000a0014160703840c00c0c105440d082d401c0540309070300c482241c00c10701c480034513140c0081001c00e9200c0c24502541c01c41c90002c0c40c00b1030503860701e00c01a0042c0220500c0e030b03040a109501407812150b4012080118540301c612480c0201034030680a00c041c4640b50002c1840e1a20009640071504000d00941c0d200750b440d41c0480d025405040308562902c10318107500c403028001c1c405103104402c00e03640040d01e8135160081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513395602 1250 513394352 513394363
    0xc0c06020c09160801060c0323030702011b020d0c02010203090301051e0f0114011b0c06020105070f0908100209030a06050a0903090e0f0103060e0c0d0501022a03160305090d14 77
    0xc9074075103265a4540f043e80195001d030440e0405d0811410781ca000c0d00b420b41d001c11211500d6803416240b00d01590441e402c0ca4090740c0a0b05969008000142c1001500c2d0380f01180001003a0140c0c0c412080745104074413400c0440303400d91042c81030741d00b0180107401090940d241912000c2001c1401d1040100406030840350070b07403040c85032500e40900c0d40340c1547c55600617518100c8504222000001151503107203050300020031130b070103a900c54000b030b51148024000d10041c2c1c3c80c07034005180c1003203611200b44110404819030300d9107005401640a80d050040095001204481e054010f199039200400c4151140c1c5100c0d199440300465107442c1d900e4020702441c2a6041032850b510840244010104586425810750382e2280000074502c8049000c075140c8003500d10b095504c030341c1035410380041110640144c0100060400f14138080195162a4813404000d40d82c1c50b40a07500600100c3d90a609500811218134042c2c20104d141c1240032010400302c038050708040d41c5808000e51030788100b0310200071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513396852 1250 513395602 513395611
    0x210302190807150e0303070c0605070e06030a0f06050d0614060a0e18010615090302180402010c08130f0b031b0f1e0c0601031202070815070c030c0c06020c09 69
    0xc0406410155076411040d40078815000d40b048010010062884281d64010784c0e801e02508101c980b68505600c00811407d28070740100c60180c10200401c82d0b407401280341d03008440c8000d0506046540e007489501c000c20740030381104065900c5d503c00259549596030107092403170240e5004201018041400000240050507082c01604415000c1180c0301c650313206070360460300525101c4844d0300c18403032a5000d00980d80010030301e0f0b000b0301c0c44603a200da0041d1102c03044070700c01c1d2042d24004a90608078810244111000307804606582000d4002520780c20042404500d40003903031091359101c0d0300c0d0b010200e110341c1103000714940020034003c40e1149040400c03c00c0d00c80942061400a91000140113401682290307850300b4180c007030fa444100d45440559000102c07040807503505603524241101d0100000c40d136500580105000840d0001c000f1401006156045054000700d40f14540d04480c66500b409042d030400c0340d00d482e10700004540d02c80341d41c01014107900410040c4244402c10108040250 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513398102 1250 513396852 513396883
    0x60b040f1d0402190b0d0f060e310512070b060409200d080c0c1005030c0301061d030a0302030414010e1302091201060b0304060b060310030206090307210302 69
    0xa0a030701901408260301d90340590305a0303142000c0b03030360701d41c24000d0241140c202e80c060080215914554504a074400408802c115205004942c0e0b103080c89021480140e0390648a0402d0b040200c1e0010f403030b01c88400036031044a034041c2d00b44540340c98050600000c10300e103e200031000074900e018400440c04441c0c005600303c4041202800315a03e0007a401074043c004030408070202c980880701d030780700c400706a90942c01c042026070f980508581d150322420020071403485580200c001030501441041501d100b0b65920204030700d16400c00380f05488200c00d4281c4007040101041000c0d036683c50600100b4451403083d001140c8550070300f1040c90341c400c0d58101d80b6040003c3e0003c034540d01e0740c0e190120035031000c0303808005030b5a65103030b408111560700b110101c102e07541c00c05400085850004e8011840b8034090759003005140c1d0746108000321440240d8003d098240b08103010300c05490048000c110310078004044460311a0f40b4a0360203281d51903445028000541507050405154040c40403501d103201c0c54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513399352 1250 513398102 513398129
    0x1a07111002070e0a0f110a020f03040b030604110705010218010813050624031603030f171810060306140106051e0307090b0f0a17060307170a06060b040f 67
    0x203080081d5103503081c1c8243d00d0380380240780100d04c0303001159001c00036046204c00180250b080495010f00e90b5481125035000611a0071800d04003d80c001c01a00d050790f030908262807840d22400c2c1040040c3c0701c6428091000d510401241c4000780d0244001e0615242002121903a441c4800000d0103884005055034039401f1206c10580c002840400c016610039540d00f480c50b2200c8240c00d50241074583c020802c0d030148600300000c1c03181c0b1000700500d01180c0c440d07519100c01d84911801180d91100200d030407007500400302c001c140c130000c204800c40c15102c0240c044441c0c1c402925032280c15103415600554400e60f44039000d40c4180750009045014124a0800d42d180036440880700880d1101d0360f00428100c1c0c8084041004d0130b104081d003800a0440c03818060700d50200c0d00d924481ca074807088902010910100f07480f0b1000103070310100d41c4245401030142c0303400780c81c014179083c40d001c00c1c0c064008540640000900004c00c10711800018210b0900e1079070b00c0ea401d10500200c4000c0136000fa41081010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513400602 1250 513399352 513399379
    0xc05060301050310090f0813090b0303090a0e090c15040f120b0f0c040e1501120b010f052808010513140c09010c3e0f04050c041a0711 59
    0x280c16115030041807400101c520840c14101b034645210750f40206580c030b0004500700007402c461558030950350640e004109080d05c1700308059aa02c100c84050b500b00d010f882c010004941e419140e182d0081d41c01e03007600d01d00005031000903064018000503038130180300810b0510010380044684809094207072070350300c207802007511685602c0400400c0105040350000004e0024900c00050301c0040101ca0740f203820509000e0705002c3e0040c0d0142d411400210995960704001800d40543c00760f4400c1a158599014144181102c455010042851601680c0340e0405018500008414250001e0340e4900806506060803c04034000c021226100c0c02d0502d0385d0704502c2c0b032000d00c000780c114103a01000b642c0e07040300c90016a090035440201034605040d00d10100c0e4403160340700f665400d00e0b031031803401d042c100002c01500da020952000282d030400b010f2510b900e46401d05511194006c5902008242410750304d002803000810f08072000c0b85051004207c02c1c080249900710407070314040480740030f100c0515 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513401852 1250 513400602 513400609
    0xe250b0304022e020a060c0819151d010618140d031403040605090c010c0309261911040506010e040504060b0d03020c0a0906080604060b060d0501120c0506030105 71
    0x4050006403140008118400080c04001c9080c0e124411903444114483c01004010b51598000901a00c005042000d140101d038420360045200d04035140b400545002c21003600720041c03920070115014080440e17004140c0a48443d407601400c0750569900f5050b6040400040080c400c4817620026408a100d0070f100d810031900c04ca604c1c00c0e00030f54543d11100542d080403900c070304581820b80080c080001c180410710145410103442804200100c41a185085c8d0045544009860001d070004401460a105256410f4400c0c1e00300ba135508403030300d80b01c89280c0100e0b090404000300401505c2440103e01c0c00c0068030714030045c01d0981203d0420036803901c2e2002a01411664600c148583d80c4c0d0400141000102d0f4003200da0752030003404d40300c0c80405034030300a503035540c000b0b10251090394940c3d00041e94004e0b9004079816542920080e0a1649032036489101400b1a030311182d600c10003e001c0748980b14002d120341c1d03000f0254110380b4584503400d030034901c1000445810140c0500700c01c00050081d81c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513403102 1250 513401852 513401857
    0xc0506030601051803120d0509070b09030d03050910020a0f0237031101020c07090b0307211a10061b2006040e01080d120e150702030d0e250b 62
    0x809a400d83d401c1d44d04000c001900300030740b42c0c0b900c90384490013040440300c024840d4410780c85008000c0840c0d00f600d480320710b0081140586403143d54141e0001017032243d030700d00c00c5c2c00054200380e404085a088040c00410070069800461400700028800981941c2745503040059400a0500102c00d0b1000340400f10b900303009010800145242e1036181444600305480346c04a804010360760700c0219120b01041c01c0d100e840d4511841281c6c000c9087c02805005490040340e20002c4442021164180c0350700500104c070a40030f0380d482a1071412000b400400e07142d440c401c040e8401e02c220548a01c1d400c0c07c0c05070140c540b08800b0518124200040040700008207800c10303e0b98200c00c4403100c0c60030101c001d80060207901ca40d8104081c0d0a8440c40000b462480c00100240d0079110f035120f4a9061401e1200c00c0100c0e054040b840c012544040c4041c240e10810307102e640d80206007441a00e00d00705240305104196050030503010295400b030072209682c0d150706034254408401786080389480328138000d9030418a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513404352 1250 513403102 513403117
    0xf0a0809030d050a0c11030a06090803060f010327030c0c0f0e0a0507090501030f0b0d08040512030309030f0a03090b0411100f050403080a030209180f1503192d0c050603060105 77
    0x50034078005480360341e02304a860452544a1401d01c5840781e145010030a68000b5141207000d04100c2100c2041c07036001e1300400d10f40c01002c3c900c0d840414525072841c0c140b4404068140d0502109180000115500544100250041e80301403402c040c83c000c10305500302001032500034900d181c00c0500801c181d01410760000c581092802080380f2081440c140000c08140c100954000c800f4401d1108001c0362070301900440d801260f82c43e807640d5407840c0d019101c0c801291801565041004650254000f0002a20740ca81d00c1e440c00151141c2c040e0b660b001c414500b80c82c103031401000159008060728000d551105104540d1800600f1291400d00140060055000060081101040854446100741d041e9000610000c0c22455202c40241118808000c00d5030641c4003256008001000384000c04400340d92a6400350040a80c042407041c00542940c0c803400444001d281a91482c030069840449085040c0d51649805d03118101440d04940b4940e00b640711500422090081040b10381c4c029050300c550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513405602 1250 513404352 513404363
    0x14190f02040e0f0a0308090c010e060706020d0605153f0a11120106030f0203010e010b1804110a030f090203070509181902010f08190e0f0a0809030d050a0c 68
    0x5012402c200181080c02d0341c4900740c400d02c180310341c03c002c0c90307400300d0900d004404040039a40034940000044800302d561014181c1c0040080140304001581d5034014035403030109510000e00540ca0340001070000e5031003030a42012060200c0d040524a010100f140101c080d0b589401c542058034100100c00204503001081c86c803040400000c03925103058000c0410b0722400614075946a05011114681400a01854001a00d003106002012007503100b01c0b81070b60170021500e00660301c0c1c441013140b50790000b13035000d2105260501040386600e40d40120303549064001201e07515228007110040460b2107400484042c981041152000768a000ca1041d0684074213031502c010355a11500400c00701d0450605400152140341440500b00c0c3ca400700480b0140c0c400d030394900860b030b020001160150310580303010400c00700c130101c0b010314140b030b6510001b403150207042a50303408200559228100342059a0644425900250041540c40c017840b2180c401009410041c0c103002007080700034003045048000074203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513406852 1250 513405602 513405611
    0x106030207111c0c06020105040309050f01031506200304050d0303020f070506041211030315060901120f0905070510050d1a090a09030206070224060d0b010314190f0204 74
    0x24490032012030b40b07000382c02800e4015104450b90743c108010781c0000007581c802492140101d901441030282d01e000703680590300c1403501ca041004110a032844581c1003814140d0b200c0c1a0100714006010380720041c416034030380218042d16006040ac1021100d451402d1540082106200a56030900960180c607018540161501c0b2603610038840e81c450b1800c00f4000b44582c000308800c1008102c0c00c01160314059544507960400889050f582c0d0106480e0401d10f50b01c0d0303070340300b1401c0c0c1010005070410b814140741503005200b00d01003a00885045043e596580c0351a0500001402420400500100002c1c0c40c0c60010200f036183c010b0030b90080ca024801100e403102c0075412024580800c2043c003010040000003941031407501d00e00100541582103015014001c00280c255002141a8000c0c00c3c0c86621040c20b002d21303c80a51256034024510b035440060b000c003020100c0c5151105501843c41104505400070703ca4016a1806440869002c114802d448030000026500d07040305280030b505460114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513408102 1250 513406852 513406867
    0x4030206031308130806040611070b070f090b040e04140a03050307051303060501080f06010621091401020f07060b0303040b040e07030609051317190516051b18060901060302 76
    0x403c1c9200c0d1111a035105070101e100440c2555020520601991140da03080012081184070000340c0e01035048007a0000c5011400180017501868807101500c41038505200c010351101d40002068000707410442d010301c690000c01040004107101d01000c86810401805540c400e1341c0d005059200042000080100c045a045022004040c40d18041c0d68000000c1c0641d41e15140781c2c3c0ea540043d200c19165a1058a00000386507000700ea20401181c0701c16512842a05007c25107005800d05400072a20304100360a80f407154402840904460f020b0482c6c0346940710a1418201c00303883e1041444d0380f01e80c000b0403081103001381a0044078101d80304030b4118030082e42e940c5000e40041140e070740107040700c600306400c02240c0056195003582c2076100d001803110850050144807804e000d00e10050100c01c2403440d844406901890180c526120b294440040c2c0c04965a203e609003550301c3c0490525209551441e440d40c03070100005c6646250400140a0300d1801e000002c0e10200c040c403410050560006401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513409352 1250 513408102 513408113
    0xa120c15060825120803150d1101050f04031208070f030515040f140c130b041401081015050a03060618030b0702010b1206100519030b060111100b04060b040302060313 73
    0x80b0043c81c0403520602281e041c0e0a280e2490f81c421280c1c2e01c82059480c0487c00185040c840500005410107002036244060344010341701c0754040c1c1000005140306120010020300e00812000f14403c1035620b00900c2e080800c0c025042d03a52030140c0100b45400c1030b00f01f00141821100c80b003480c3d00221000f11300d003c0b40c81d00c0a0024001d202c40d204170031584074108521041d01030000e26814080c00202194142c0d14a101c0700b0034061801102103940f007860401e803181d80300780c626641203540802010ba51658903d0781d50703913014110f100349004c10008150320b5069a054400c200082c10340e420400790000c000802200c074211107010041178089003001203011107100754404040136401800034662040d200010595510003100c40520610100d20040754a00300800c04101039886e008012000710306581d266505224024201e5042000e0300d5000701458074208055021410f0841000038103840c06010300090f11116081850b035800100000c01c01a11080122540700c00c100d10365484014982c40c21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513410602 1250 513409352 513409423
    0x1506060c06221a15041a090907150c02040605040603050a060c02120a020a02040b03070e0406110906030a0b040e0d17130615180908040501030e0a120c150608 69
    0x16003040f04000884082050000340e160150724144070180c10104013030b00b00310070750394803444800181d40c00c440032080c039050030081950480d940d9402d44403150707120b0300c690142c80702d480b18182c001090b01c0c0c0e440301503040500c21344c00a44000e83c3c05002c02401c40d1076284c0c5d14088400b009010b0f554407855266840d1080c007140c0f8404426404282e61040c11241c001c0d030f143c0b04848141d10031490032440b0350651070006102802c0751000f003107079041681c1e540c807208014141c05000c03560600013084840007641c0c500340110700c60030495030002030280c0008144012030700d0394000051264000d540c0c00d580b45800208071014640440300e41103240e5114115464034081405004000c14107000c880c07201901e10042c1013040e124a4913280c442a440f07034842c0c0095841c2e551000d010110100810310603544250400503515238030100b12039800301c1a5448800407281d400f0440d000500d4401c5500410600304448114107404923000c3c0050b5003841c00c0551904c0b0402c500c101500060307a8243c2028650510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513411852 1250 513410602 513410671
    0x1002070524040305221e030507083405040507080f070f080612010e0613031206031101051602090108030a020f150a0c09120309170a0c1a0c01020304051506060c06 71
    0x116006071b1031500800d03070703481149400700325450b0017414804201c1910000f0018103000d01c01100041c000c41c40060b024000550700c01400480350f0544020809032194000c4900511055484a10f1460200741031000c2c0c2c50003825060030000409800420301d07070b0080c11590042011600f01118030b908140c0749004141c0c85e00d2540141c0900300070810440d22400c15010218002e40b102540d4000d0f1800110032200540030060400314028100c10940d441000580b00e202d008030b030001e503d4100b68001520180c2c007644044c2c0076074400540484900d90511907102d003170044a00401813624072480c07030070082c100280a0b90700555684c04180d4150b01c01c105410084c1041040103441c44024200201612042e028a140a03064401c84c41c00040d00011441441074210042c0360520f41030041000000c5284c410701130b05a50f0501c00c94202c0c80c07080c0300941c00f03284214000c0002c803001d16245000d154005000380c1c461002800501880407000c41c0f0503a014100154100e540b40c1e0451088251765440d0300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513413102 1250 513411852 513411869
    0xa030f27120515010b030c030a060e1501030f06050a0b0f040e0f1e04020d1203110406090f050603010510120f020318070b03011a0c100207052404030522 67
    0x140000320384440c40301e03180c0c0c0d182c01181940c0c0e9030700d11010001842c0500b0b219280f8541d80800c0021510740844014540003010101d010079220380c0c2d003014424601050316a40b00d841c0034602d0030500c0d0b60300751081c0320320170728403000170f110305850800040d922440d02d10412000040010b544201c1050610454014004c0340c072040d50320b400c0a5001c1e0f00540d004075102c20040b018078000740103000c3c8002d845407203103900070f014040c039544550740e949440c20000b11401c02c3c1a01d0303990304001c641640c400f41020303100c40d9483c81402c5251006800b4a101a5030100b40658001c00050210b5101d00030203040401d011b003010901c04502e11345c500004c145070a05901c0c80ca1010040c4188101e4003021030304010b80403800c0361503182d00ca8403000c0305c91100b0b108140a22054980100300b1043c801c2c00340c441d601454080da07007030300c0c60074070084180e070300c400001c69036504110402e21000340b80c55090080304203c542c0b0a0494545a60f01500134415490080c00b5240f41419040c4202c289090170b401401421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513414352 1250 513413102 513413177
    0x705060117060f0f0a0f0e0708150f061807020a0614190c0207140102120d140c040305150c070c0305071409160e150c060403030c020a030f 61
    0x20120403004110700d6100c4107041c002e50001c41c0c0e601040680320390040d403484540c400107031110b40d00d0500500820202c003c07140d071141c0c3c911241207800e001030b100170040d0101038203080010a8000040300c4004104050074918042808030726119120840c0c00003011020205681e10745034810713403615803c441c008080a0034083d11001d0b9620b51094140200c010580c440929140240800d0945100741007110040e03020420400c588a030082501c081604103005940c1028000d4a4903401603024025402e074081e118aa10400b0410711851950300a040c4a461410079085603a42d940f03030310b00481000b000d8014400030965003040e5a0031100c030740794000760900001e0383c1c924200e915408180f141b8468185565018401d9042180e203a910448900d03010094410b001d01040c1d54815030b200d0569001800c030030040c120098118010721500d05c0440c0204600e15052500030144d0350540918011074000311141c60019821134500400b14441741070103041058900b0b10b0302402107840b0f444040808030b030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513415602 1250 513414352 513414359
    0x26010e0c010807030902010c170702061308070501050f03011503020c19030f030b13050c0715091104090b060f040b060f041a04030203070e040201030902091f0608061005070807050601 80
    0x2489680c000c0280c0b00e1020a036208001602210161403020380401e000400b0240042d5401c105c600f0881140c000b00341c188081c2d034020074007940080050443c5688444001e11a11404012010090109190940c40d00c0c40c01440d5044900042c0310311525072101060000b5003d000ba01695519407510f41201e460f502c802034405401c2c0c03a102020f0f004071b914400d2500310284240110340da14900a4541c0d0150002e4034070303607402800c000b03000380d5030701d50148485800180340300c9010151130450040440c8000369800c00d9000000c150380300340d04c11483d10034001d0008000140d0340707610500880380c50a0501000001c1000340c09194251a4443c0300020205195181c1c14054819902c0e420120050340e60b04517000c1556114500020b54142d00210040243e448100b5956a21070310602d004a083d5003a0750118084000542d0134000600400c0c4484402d08020110070000b40043d00d0080d4107030410201141c2021000200b0400704000002c0f800c0900032900211403c0c560311004459003582d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513416852 1250 513415602 513415631
    0x101212030c0503100506030903160804090506040c0e091003060c05040e010906121b081b19050109140a0b0409050103051203070509010e030c15030702010e06102601 72
    0x18112120004245040c00c1000e825204000b5079100b080542c00d603400700c90078881000090f410003040e41d0f01502c400c101c81040c0f41b17019011444110300ca00caa840c0c07601d040100705002e4a1004288a01540ca0500d0408105501041e0700560441c10307101203141d61a180600751020700c95800240403203060000481c1040e6216000700b0440300d14440501d61a40c0340c100007810b0310701034860a2240e01240a440c40810100350710751f0038071043c0303c0e402d090040d5103900c00d038289410366004541414a91140402c0ca040400301405000001c0d11503100c05410400045c0400702107002d01c640071030b0348600c0c0d013134030381c4504002c400900604540107485543d1030004d03d001c0c000900049030f60340200c008003420100c076101940e024152079215641040042c400443d0301e40456003250340d15115240b42c1c00380d5611104150300500a0b02c2d48070556a242440c00a42510500940c61800750312410411541174103603400f89042e5822000d800c4001c0120400c3c0c400e004000700714000d0994a0440410210403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513418102 1250 513416852 513416873
    0x2c0409141e07060c1214040f0303020106090b01050313080c0a050a0f020a0e070e0907050904050403080a05090c06090603060103060e010e0108062211060f04170c030d171012 76
    0xa007404071a8000c0c0c841a088801070141c1400400c0c4118004c1d0050303c6500440e4031407030403120004a5030030a40e4030600c0720706450303540c0d000f680941d5651000384a10b034064050201420420300b41a032450414402504506818010161400d5000300300c41080940501042c40d9458002d8100d812844803400c0455080500350030481c41200061800105001d4402000303200e40310985860007031181c1e00d420303c41148002000d403004c01c0404c114005899030340d48501e40c062800b81c5d03240800c515008006008580020341b026250368002801307000c20350b544c070f000c0301d0b10340300c09503021171b100d071540c60040c3d003c0c003044d81140f0510701214002003603110744006024100c60b40c040498040e40c40c0d030b4010722040194105904d42c2d4241e511030030000b081c01d0781c1400003041c401400888c43c1c00e00000e40100180c0154205881001c3c80f55541c02c030844d400c01041d2080503007107000e0700c244102d00a01030181580200650043c103ea03d00003080041c220a02a0080001c082d4255038203c0514003440941b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513419352 1250 513418102 513418153
    0x2120c011506140313030c020a0803130503071802090406090504080a0e0103060608011e150f030b040516110a061a130504050c01230a0903032c040914 66
    0x411880100207a1507200c1c910f5081451201d4031000e156460740d2641d60030340b280010f416402e010f100802e000c0140c61f0b00401000a04403900510b44803000c88851241d0a00f0720b0344100e12a40c031014092007041d140c0d0403442c3c050405000c1c0103955021071404100030b000c0c994403409000e4a00f00800050000b400000d00c2038548660f10942a11143c0340103500b04c6030710340180000100000b0040c0100a010b0f80b08408544092441d038801b1030b80c50444403c04500c3d11103c9000441c0d4190001c90644c240c05880488081280c05100700d2800007004026640c5401c014820000407101c8000c0e0100309100f5180c456421500c240030b810360007200784d200740c0c48040026009039001c140d1403a10706080e00c1114041e07039021024041c000c1000004403002012070a02c0a080c0c80030080b14001c511410006003a0a552a140e20700210b07d5420301400c86920150319501c1d000044101204200c41aa01294001021100001d040d4020305000800180b94507001c5018403500085403403140b07603044945400d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513420602 1250 513419352 513419381
    0xf21060e0a03091d0105041d0703060c020d02011a010507031809091502070b010303030b0a05041d071d06010f121802030606101418100306081513030c0302120c01 71
    0x1182d50380e14544c0001d40c03c004014a00030b640c0030051005250541002090540c3c0ba010521b00305004d440c06c03800c01403142e00841c0c00340d03920300d116005a1b0301401207801d0104180001c04c600c100e401039208a40c0f5480c462a41001000a0004100f5000d200808245140740490500703894903a00e2a20092154000c1a1050001030b088410003680a000721404554041c910b00d015034039580d8250b018240038007900c0e80c8101005000700d10f5803079a01c5100c188699031192042100041e01c005402d294603034000440300071200401c42d81968000803a150840800e01c0e0a16520740f18030422107a101c0300c2945400100e080000080420340e28140b10300070389008400361621516403804102c1500ca24551321400318100c00904403182030081c000d030142c643e03032038100e804004140000400e100840c6202c440400d41c0c1d40418040c8800070043c00040302700013200700506042c64000b50a80ea50780440003802c201c400c0310f04c0d008143c82408490740b40c0c900880310703640316004030301e0f04e0b03020b4003048481540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513421852 1250 513420602 513420617
    0x20f120328140711130209130912020606101101020f0a0c0302010b01030b0117040f05030408100b010f050301360207052a12150f0601180f21060e0a03 66
    0x100c01120040f500c182d68000340076003c8402503c1400342c0b403004481c441c0680380c1c0c03c2c03000c55915140e0303400c0006a04011703a400641d10009140040141e05071b00039000856009000f00007050721101c1422500b9101da082855003078044082c043c2c0a4410452809a80c440218030380070320a410403461031286102c0d4009104003d83c4100450495511100c120b0024803030750302d80c69806844180e11030b00325004000b50044c000c0c550300d649145501644c000829544031304030340c03400050700344109003c124003482c1400c1d540c040440020300701d002c10f0140b2a50405803020310550710315554500745074000c1044102640c03000742801440250007800b800d403200d00500361a150007282020045552270b807074110380a10a50307001c0c240b10307000da80c03111040c140b40b00d40c1d80004030a10540c00d85038030851641d03070941014500300c400144000200300e00f02d00c0c820410352080c002d8403400c0c05241c0076a079139010800002800601c626001205c40790b80a407581d440c10b485000013400100b07184c213a86009458001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513423102 1250 513421852 513421877
    0x7020307060822080d0b040207050d05030711030a020309090919050c0114030c071e050304091d2b0207030804030b010e060d050c01030b0d0212011b020109020f120328 73
    0x1080b40c071503010003041134008010341d6044034043d03481a403c281e00940014280340d865034a940ca4001920f440c2c5003c14808000c02c100d1581c070110565601041c04040c0d400c00e041c0078406580d90082d00341d0315200c0d0380c0740000920501c1041003051426001c0c1400c0c207580c0c40f11800d081c0e44074400551a01c0c0080c00300100764a030a6200802c60380511104106c5e98540041502d940708807584045003400941d41c82028100418006c00c081d00141174608000919001c01008140070960300365080100354000c803090301c50f0300001021052043c10102440e00007040d103030400f00e08110494000501c21580402d0200a1200c900031440c180c0d45000d03d104001e4451004101e05405d45040c000c000742c1c014044203203954441c0d0048034445c00003906c00c1c0341c443c45079400102001c1c0e4103c480700c0e06039500d03880c01a030b80440d00925040004d140c00208011481900482c030044401c80807203000c3d42d032012038070111240810895081c00001c00603e02c0d1309124208550601116858040004001c0d1001c1e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513424352 1250 513423102 513423151
    0x605060f01020d02070e06010507150b1305070c030c110406030f060e12071b091e050f190908120702060906011d04060b0112060b12011208120408070203070608 70
    0x308a03d0800d400500d14189000028100c50000400040c108541440000e00088108494070810903500101144040421b814054004914018507074128202014015840c5d00403901000c510b400d031801c0705070b4480c02c1c18040c42180d808486250404d141c010000180f01c408000105014421201030043c2c118164a06544141056001542c26010000c8400040d51401400c0074042d0004051f00c40c19640c4200000f1100b8441c80c0a046850036600d03141c004016219a07030748211107178407aaa41d07080903111aa140e2001c4445a03185580d140702500c244903019054489030314070007425211a16011500946030002503801e071003184540c10001c03411000320b4030700300c1100e45000300c407090a030b841d80c45800182648052759410310080b9180140c4800131400f618000c0d01440c5540c070756039921403406101c000310581c010012402c00000117000036003800c0403a403c040344810b02140540f00d50429511520070294025894403ca07180003e9580d08803142510445208030b000c0d00501507034800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513425602 1250 513424352 513424363
    0x200c04050606040b091201090605101706090304051e090a060f12020603040201030209040902090703021b01060807090c1b050d080105060c15091002040f05030c060f04050d02040f090605060f0102 85
    0x109080000e085c06510380750300701b06203499481001c500000c01e0700000c1752118002c5031015510009000d80c1c001c07050040603480d1440702402c0110700d0041117180351108415489000e14042ca80c0300b8000d5035030040036451640708000c0002d0b001480000142415030030700740204114030819407000c00c079180c00184a50a030400e6808260094080ca156903540d0340118020b40c84240181e9100356603003403503400350711140011442600310b9140141d41313400f1013800f106180c00d214001221340c0e061801c1030161020201e4200202c0320b0445001c514800c45000640e01c060821a003001e007401c007503049005102c000901340b00d290165403240980390340c8440a00200b0300c03550201000b5030b808004c02c01c010071907010155074003c0d860340540300b4180c60790a0010580e80a607000f184040c0c04910700f03111501c0c2c148810345211504944035407401242c0d51102000d40118891a8401c400c03c82240c003d640380c54200c158220a158400c201150300307413500000070f00081d41c6140c0200100212400a5400043e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513426852 1250 513425602 513425609
    0x1308031b070303080a1521110d02011e140705010b0418020f0d03110307060e01052d0c07021807030b0109051309170406200d0f0807200c0405060604 65
    0xc0b0030413030390b071030140e06006040b88000d500c95185510000156540111101a0381d545421035080742407015810008511160300703400500c00c0340b0000705000142c0c1c00460141841d40c19825007603110036200c101340d840401101210081d000c0024001040000651003010042c0701120200311070091880d006001c5070008000941019041b85000034510b41006409500e61007441c100340c4c0d80700920505415a00f0114045442075211b07901c08100110038090243d200710500140c0191203203816044044008000a0316038001381b000110781c1024840c8100c130b01c0355400bd07282c945400c1140e0444103c6050032640b0700c00080c60b01c04071a4066201e5900e0104441000b40f41640c480d414114036401007921031011240309510000364a0494800b030041c20040c2102e480c2c002c40c0c003039000d90983c01503281e415258241c1d0011410741e440d09400c07100c034091296851401a5090340c0d45072007030780c48280c0320b0250b16040104a68000e4140e2002400f642d204078207950510041d00c404050103e14082c901 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513428102 1250 513426852 513426857
    0x1050906011a1b10020d050c0c0606010518060a08010305010b09040222090204110a0f0c0b040f080705010f02030106020c01020a0b0105011b0b090c36070201021308031b070303 77
    0x140d503220400420041c1260749000101c6a05002141d194185855032403511312514a0f008103011403000c83c1031080d181c0c0418030184542c5803000314940d5544174007005054074140300000c00c0c6c081c281078500320211100b100280c0066a140441d16025041600900c000c580540c01c0c03005d100c800382040540c00e0b00a40d4042e120028280080b140c91880c0e1130350b14801c80b402c5550f02418405691503016001c040720114141c140d607000f90110091200e09030503140014818208107a80005031018807032039102d42c2100c00c451100b103851034151540c0c401d82e500070b8269820b041c0c1c0e002d00702d2090340c0118101e403100e40803901c081c00c0e41c1005a071249100480a0b000403c1040100802d500580ca0704002d21300d0310450030410318035680c40f070014660980b079440d4940e00c0344201e20101d05080d0038130004407803880c08c22242e291281c0004824550700e07181d681c07404031448000c43d540324001d405076540403890a1030107804e60345501c0d103507035070b038000301d16825801000c2c04d55581d0509002c2203003000d036034055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513429352 1250 513428102 513428129
    0x1a09010902150c030f1314030d0e060f040b030f01091a0d0b0601200109060c05040b070201030e0f0f0f070f080709020c0304050a090c0806040c09090f0b090115020105090601 76
    0x410b503180d60781d0050040b1003040c0c08104000b60010311100010020241220150404281042c46809100000094160080e4024400880e0303407034000e01017100c10703401214000c2d82c59071152500e440c54052070380008030481e80442809400240010310a060710304200307081201c6850b00c0741c0300242e182001140350300014503e5941003c500044050b40c0c1c0704406042c009580c0940b0f030040003140780c1c058240c1580d42d559460400030000e440c042c040460030070b40340050503c1e040040d01e1300c2522032088024145139276442c100c084c40340240300c00014030f0a040c6c15100114a16094036440e1100c4104440d9980101c000109024108005410036240c412006240c004d08118100000b54800d1031508124031040c07000042e0740c0e4542d82d142000d0a124400030590380d1b09500c028002d008054070301d41c402c904001140c01c0b007560041541044450091020540e00c50302c451010081c000800c2c000d40140c6403100100d01e000f00340e01074a0100340607a0081007a6511401119107500003030140710b0301c90303594 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513430602 1250 513429352 513429379
    0x3010f0c0e0f0d0b0f0103030e0d0201051c11030a0b0301110f03010e072705090702010b06091314091509010509211309050a06290c030d091a09010902 66
    0x42c078003203080001030624990341500340c0328109038440407200d41c02080345100051041540c4000e47c400c0029058654244928140d40060060b016485031144106500c942c3d9580701c07071103034201010012183d00d50580c0d90070484005030250404100e103034001d40c2024402241d560010040364001000c5c40c40c000c1c203590070040142c0d24130078050421000c020190061740c00c03c41c402c440c514009040a20340120782880d24092140302840200098150b914164152143ea2500e004486490740d040352605941c4804c0b000003001000c084201256007404d04017001248407000078100d04030b0540303096243c3c86580b0032903007600f41d5504558028450300910300d000740007200001102a4a1401014031382441e01c11b07180402581000c1d4004011142c541381440855402c610811020301030090a500d1655580c49001c015245443c4144001190004121034201014003d403444814088001d00c8400766500340038202c150308000c140034100104012400b2002c051040049850f80500501c988105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513431852 1250 513430602 513430609
    0x17071e0b13090c0801030c05090709090c11030c0c010206180a080a11010203040507051903030e0616020307060305040c0b07030e091f0602071e0602030409020d020d020403060b03010f0c0e 82
    0xc881d00340e0307190400500800c00410501070308450b41c1082e42c501e08030b589541007000c614801a84000e000740c061405000805030301248080643e40300d1040030030300070035080003101c80540c0032600300400c1c040811074450320312010a1035030722045e0982c00c0301c3d801d486001480700c02c1d010720903503d4108d41c4034061030400200d00f00003400d1030503032901b482c003a0564100ca5aa00f0f9a20071a402c035419001000c041c400340c038002c854044086c5130f04e0300507414a0306503517024240d82c400411980c402c91011525103450469000001c1c40140d0182c16a044a566050003038050030080d60b003290410040308001c28411840c10a4501c066019940c91128080d00303c10b029090b5000382c411030300d6020f18072001d881041040c415000802150740184040e41c900580b01c0190b440b0394900c1c0309901c903180001c001841d80002540c080c2c4110001c0180d49030320482c0150000d101d151041107001d800490000144142035008603503014003074009000c181c00300820603048800c2070500d00082200d040c91340140b4103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513433102 1250 513431852 513431857
    0x80708030405031509011811010215061309050f0f06070e0f0603010303051c051602010e010c0206040b10092c070524090a03060c11010e1c1817071e0b 66
    0x44070503000056410311250811140e1340040c7e001e0301c200d050344108501c29641006042c000a050319170700102130424a000640c0c0680a08046501c00d0b150300f040f02c1400018459030742e600d0218400c55121148014442d5154071086503100c0c0440d04450380701929003080091b19201e1a0020304180c916800e55406486503006950740b920b0300301d039100c41c1d106490702520a09000e031880b900c4000751a0361081009080d902080a840d9440c4d0400551507030054001565940056002882101955600e9103a482801156010a400d00d007008100c0302c609003820004a401e80c281100349184e10110090f8036a901101d1107007a0300b0600103880000004c0b0004421205002480446460000c0180020b414000c00b41c04c10b846d140e41c0c0e10180710480783c00440c1303030060944d004000e001d106089600242c8607107040e0504400340d06104030139019144584041445492a48000c115454507060101c44400c05001e52002b40d11032040049419541c410614000c01d10148903c94039a042103100c400750b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513434352 1250 513433102 513433111
    0x40b0304030311090a030c050310020405060306041e0c091401021f020a0c02061c0b0a080601060f0309061d1e03090f1c0303090b0a02090609280806010807080304050315 74
    0x1800305101c84641131355030118020046d40110035914140e402c1c0800c05042007000007521892501c100410082901c0760720a50754008411a00000c1052000d13a80e078609804100c00c010300c95140003aa03003001a040a0080262101c0030b070203c02007110b5900685c0e584c0449864410044a1000400c001d4501030b0020f03d000c505524041c200e180e03555001c07070140d801443c0da203421000b003007996241c80546442007500340e0300c08517a440281c0d03103401034082e2150b1041c0070380c0e010403080072a81c0254038000d0b00308044207139102d1740401800160007030601d04140c40040600c00c5014901045010610305000c60b040041c0040180d494500c065040103603d90001082c2038020b00ca82e81185016a00b807851802c0c8180a520003140c0c814151800c880501e0009040c41c41d02881440510140e80720f08054071101c2030180c80004004181d138900322440143c6125492500214aa02068007007001c1283d40c100d5800d0412900c03000d8490301d000d0f40328011400307003582651190801138504035a0b0620a03400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513435602 1250 513434352 513434381
    0x3050405030a03030b090c12010918080d050f0c04080c0d140708030a03111201030204202b05040305160611160b070c0c140102033c040b03040303 64
    0x910355510007107402c088000c002070300481e1707580843c403d2504000300d40542c07040751a08020b10b0003014a08590300c000c01801051034007036540c15140854031840345000f0304c1580241d0556280e09451140c600903010031a50140b00542c00000303d1071044000e0180c47c181d8030088080e0240c8400c01050215003a91010191003040082c1c3c0585000c000c107000c00009450b115001d960785c0c0e40040005415100f192404490284040102c04480060f414039541503983c110f5011540382402a001044104400b503c00f03103411002030170300715002c0140b049007401e013428819444e48440030185142101c0f0b04440c090040f4030304102d07802d000c441c0b030104018181d105100026002070020b01030340054000b04ca011440c9140100040706100320b040303036a540046076207425060203820b682d482041312001e10800c41c0c8110503041b4000d15a00900649108100c1031802d4803c1c018240d0310320a19414003603015081c012143c071a41c180c3e118a20495081e506624205451616250390840040400e003908001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513436852 1250 513435602 513435607
    0xf0304350a0c0803100819080301060309060e060723070209130f0c151121090301090b0a02040e0c03090a03081005120706120e1207020118090c031a0d0f0305 69
    0x402c0240a107015040031217140d980282400c400b40e19081002c1c0790403085030400d1711f01e0400568400101e078151102458046081095807400c2d02c05041107402d25402405241c2c10050a60b62100101007104c1100d244040c0071510271441c2c3c180c500c02c40c90003070f4212448000246c000310301c0c41c14040d0b840d40b140078400440314550300c3d10101240c2c0360b00b042184030704a00c030228405511000c09080d12445001811705048a9200245058441c0403000e059141c08143d819060343d080d0b00c4841d003280c21032a416028504002003000075405402550001036400010940c030f070030140c06484c4690305c03040c010108044542c43c26135600400034648110141e1411003c40c2544884c0c568a62181c50713100141003081c20403038050a031181002e1400c400c1d03450040030418449001800b1000511040c80c100da68918600040354030350001d5540829071140b0701070009440c10135520240d91105550350821618858003000c0c502440c004581c103034448a8041400c01180040308084070180c0309050961 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513438102 1250 513436852 513436877
    0xf0304060b01210209010e0a0503190c150e1011031b120a111506060a212306040506180a0905010e010e01050114090705130504020f0304350a 62
    0x1070030007003003508103ea80d4001c519101c165030400d50114510400302e40c1d5440b01801d10001c03c0d0365080b00d8000f043c01e045e00100310800c0c030890341c682d540035003041c40d440c0c40703801980507001d80b902110840b1a03018241260b03203d030400744203101001c4000c00301409140f85c19002c202035a1107111b016440001c0e8007070200001d015085c1d4a0007007400072140c0c0c40c0c0128100b070805009040860701d1010a684100307042c02c1100e151307202022612180a07a0901030115144070414641120b1841141c0343c0b56490400088034090b1201c0d03410984000f4000c031030310240d8666040c44150f0f903007503592981001260f4a12800d054607500025400700c0810700c000740d810903a0b2507c5095900030b400b01c280036551401003030600b4400b805901d0143c000400307202c070019129408101c03100002400c042c104000030441200c0100d402c112040209401401991581c812200c40c1695070300684045414404000c1440081ca05000c65a04000720b00c5a200c0001401000c50952540c00455000100802c502590 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513439352 1250 513438102 513438137
    0x1a041220010213031103010c02030a0c05030403050f06090d03110a0c11031519180209180609030d06081b0108091204031208090a080403061a030f0c0301060b0f0304060b01 75
    0x28000c10740020b0014064074510305000903503104c1017110313901036410142410142a00042210021809468070480700c5142d0b06040d400c500032500010130702c1c09600c83c26040f42000194103405880302c8400d45d17414184103001070b030807200c01c2d190201f003a007000c0c00a891058000d40c1c1c055583c4d40030340c02c07800300c0e0307070359240000d00b03260310241c80303980c5d00c0d1591041c00b4000708098a0510b03000882401000740006c1801c009c0003e601c0444000d1084a01c000094003c2c980c4500080703441c02c6030300c11a41942010301440341c60b80c005005070410b42e450200c00064000c4005158888030103020620742c0e0741811100111002440140034100a1083d026100c9200b02803800820080d030054022100000701d130000248000005488185c803540700c0c201e181d0102e07403190111780c11079500840010303001300b28061041000039034203109039160040380c0d00e200d10000c001c01d002070702c00c808a0080100d140c441e414403030940100c02100c00801400e00026000441c80c1c1d100400554050500001085440140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513440602 1250 513439352 513439357
    0x81c030e0319110106080709051503070e0a1415040c05130f09060501020a03080c07030c08030f06010915020d14040504020a020d080604050606160f050115031a0412200102 75
    0x1011002e8503009154090b0303070019241140901d00b800a2200034907140c15580c0d01c03101d03400b403015019035400106039054802d01a2400c4410b0140a64107a155070f011500c7c0d00b0310701140d011250708d00306a4080800c0f040c0301207042c8034414454401421908a0050100401100d06a1070901200300000101c1a000c0344044c401015401040c0607944d0603d120386099072000e520041c15503020a01010000b47c12144550380600d810b40855210001e6050446201c408ca40c0c014008007000014407102c4480d4040030742c0304076420380b0750900d0182d40748804507080a040d05d1020040c1c000360540c0080c03920600401403050b042c0c402c810700309038031000058100c0c1c1c1f0a0b1104d00140e4080388041c0d00e60b41d0440319565024230b00b110100700a00e45000403411500c584036401820a800f00711910411140c00c04014885800c00002c11603942e88080012400c88207010a592001d21189020080752071180c1c1103102c0d41c3e20140398141c0820181c03041c0c6a400d1408491b070f5200102442142640400340b01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513441852 1250 513440602 513440617
    0x30a240b04110d0f06060806010f0905270f0c0906210109140c0403020a0b0903160b0a0905032410030609060b150a021c03060e0903040e0709081c030e03 67
    0xb03065884000c5501d240840d40340c0740013200040d0070014200305664010407110fa002c04203007080001c03000c014500303c58070b6146800655106a071b80204aa0039800d5890b60221440e07210b11441d140d0722404440c00c19680110303a90307802c050301044111118100710001e4040842c2c000c2d40c0f10560002c011040b00c030108243c00c580c01d090380ea503400d600c3c080c904250700c0e82c10450480034903180a0841c0c021800d2140540241c0c0c444050002c2e202c0740c0c80e2010803c0400701081da40c512409103841c1d0501504583c02500b800e400503200c1a0041001d2401066450700311994403510360208414140c0f8526600b00100000f14000040f080000810410b000310f1500c140308240014441200a0400143e1181c078500c450342100180185075906400280070480803000c3c0e1803034400640071070300403806040d080d0049114a003400d81403000108002014105035549100004269a1114021142c00c0018442d0a00075131048007101d00e8155407a54100d4404ca5030701d004514802c68409180c5036902004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513443102 1250 513441852 513441881
    0xb24070203061f051f08070e04020309070e010501050418050411060a110d08040201050a081f120b0705131208090604080615030304180f020904140f06030a240b04 71
    0xa09500c3c08071100c0b01d00718050041100c3d40d504a6104400842540410240000c14041c00b000031465540c02181011078624004005640d02e28060341055100c032618460f1443c02c4009400104d803d6003e20182e909031855403442500c5100202e82d00b2001d40340142c800c4ea25200189150300cc19180d103001403516603010345075005800404483c462030420741c00000002c12030810280001170383d0210840c0c1180009180001050302c40c030f441c200003c0c3c10f003045180105240100081c1c403002c480780c2032914502031410a04140c0c1e03190000d45041c070444400135000c5009150910003070b908182c002460314000c8251a05200501010031600e6009400c2081c01c0e90041c0c00b0000c1d060502c0d510000200000d80144d400c1625095910f00b555118024081c6070ba600d03099103101e10255941a10101d4034020020b000d1b0440e43d81840e1500c403c1694100c604030f8294002903003a040c001001c01005a1061032a07914448008080c45009401490006c105d0340b18418440319903140e004820703d809030784 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513444352 1250 513443102 513443131
    0x110a140310020f130e192306031501170118050a0b0c041214010f090309061112130f06050703020303060913020901240e100c081b01090606090b2407020306 68
    0x362039100d0f80d80c410b00c80c406e078020f090580d51007100d125a0002c181e01110051403402c152107035000607081950b06943c2405402508000103131640c0d0510461005121520082002d01520000240d4591701f00c58003404079440480300320002809100002c3c1d004a085886c981007d4580c910503010001c1c400c1c0603607065240c2034814161070028410921040c0c8450030130407003512203039405046101503100b42c1041c0401060322051542e010300c0900e466400c0300c0d902640d02c2040c240e8686001c01c041c000c6100e096404540031034010f0182e012240c00b42c0d01a0011411655810700700301c80140300421060f92540c5180340c0e00c00503118849000e0180102d405400513268079048011501d030045d00c81d100c10803c10320140500c0343c86600c482002c4010900c0c0111110341c140c141805984141d4028104012aa0482c1c2a14140640c021001139119142c188009942d8140000c16148462104c50b0302c0f07842c13024442079108070356100e940e000752080c04003818030019400290514804a1742c600d07040d0f212 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513445602 1250 513444352 513444361
    0xb0c0c010903210b010c1b050613090c02062505041706220809120a020603010312120606050d0b120312040b01090501030c030f0303060909110a140310020f130e 70
    0x103036888a04810f182000340c000380d000000e19881c14a000940904405242410180e6034841c071340002d030030041d04170341d921417000380601168501481909011781c03908403001803c41c4080f0b111401000001e601c0c106d003a066100e00f031000085c18007501705010041000042810700c0c408200070840c902c1026140b80e140c90300020003010384405269625070b81c0880008005605201929120074081d1080303d00d000c4003038a4039182040036280694002c001000000401880442e6200302d0903156070390709008054515001c0a0721268090720003c10018000911481d065a01188021030000c09000d40100e52103501400e40d8032818034505902d4a00e0b040000384800340762245c0c01813400c0101000b1030340c074549448c40440442d000060680d03c000701c0d01c4092600c02c0d0400b00181a19000801440e5258500f22201810406006001e9107140400080b450080b14003052070300c0b4050003401d110301a8507807010007903200301c0704000170384410700c084100c40050150f84009882c00d44c0030950035080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513446852 1250 513445602 513445637
    0x60e01060f2a170909091b030606090f04020d12120e07050127080303010f030302010b030a0209160302040305060705032202100e0f0405040b06010906090f030b0c0c010903 75
    0x3003086036220341c20041e1400c0080c0c0803481491403040d50000070f41e0442030000704031000c0314801e6000d8280e000864100740a0740b00d40116401c2440300303180b0203045c0120302c0d038000d06803144401c4403225880014000020251102c2d84611a48a4030013030005120080c281c1d568040c0401e0000611b000505113203034803105010902c00e21403010b54990082026614003c002485c084a4032502c03040458503440b02d0320005214081c58002d030100b001030701e0f120f6840e88000403904e9454801940150300f04465006541804104105000d8010300520015030300c00308010705003581348003182d0400d03600300b1000022820500c1020f0240d0450350300c8030354a06111090701c0203614600d13180b4219690402a0400681d5410800c40304103401e42040f0150406500010f28444075003152207401904043c100710130400c1700107a00c0d1160400b6214a501c80d510b031603045850413104d000310301c240031002c1003c1c400b09400000c52a44094027066152803c0f1441c2d81c030a0039100c4041040b000f003410380d100b80e500301c074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513448102 1250 513446852 513446867
    0x6150307170f0109061e060f0207090221130b010303110c06030f0907080313140604150e040e07060504090207141912031e09380a061215060e01060f 65
    0x21b00001c0040244161280014404101d01c13841c0c0c1440300c0c480441511b18024407805008100c0314508540390010354023241c0d040302400170040300c00d0040500056110100b154038038015a00031401440582c21a0b409070381000384880000682d1040c0070ba240496943c0400a40c0b003040303050407003802400c080e0507841c50403d4035002510700b07070424401c10240c0f1480d0000c84080350145a01c4083e40c2a040380414102e03c5075030000015003120342020110305030403075121030a40b030003610f00f00a0801c124602c1c50b10307065680201c20020b04104010030144030581c0140001a004561340c100c03c04042c40f00300c0c9452030b0001b04078078000510314400c041c4040d810440e400c803c414101400201381c240b101c1c000400d0000050003690f603a0303080f034109118030304204007408404003030b0010414200c026003580050007612118a41c500c100001082901c9074000c0104a131882c02000c0c110030b015649000100421402c1c4200d0b455075040700003442005020f502d03008165035140e5421071421114020300c00e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513449352 1250 513448102 513448109
    0x30c050f060c15070e0a1706090c10030b040b10090611031602091003060c09180c05040b0d0f1d06090c0609060f1303050f060f06150307170f010906 65
    0x460701480246005040400c440441c00001407098800b036650407416113007003035044140c0b6005000400085058034a07080c103140b10940501c101c0b00a03580f00b4551036070711f00b41c0003030464016540d0700c90819414002d03000703111081c0c0010004200c1c00c92103404241782e0540e0032862000111458020001150000400754581d4000001b03145444070040b0410105500c6c004000d001c0d004000c002204441c0180a5901030f56000f20180140c045d10100106003c5032405071308803d010b4648092000340040c441c041c202225078440c5c03420309151105140103500300c8140e8501541e181d0045440d0710805201b441c50405980207006401e44425104515120008114603415400100b03440c03015919402950785800d0100d42c0103554004130402a48103008038502c110880c02d5440c1c01000304000803581c3c0a10b00d00c8034007100c030b003030b0b4820310103415080064401d182c1000c01050940410021b0500940c0e101c8000c1c2407400c02c1a070800208503082104544003c0b82040100041c48200103d020f100000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513450602 1250 513449352 513449359
    0x902010f0801140f0f030f0d0e0307030b0609070215100303090e0402150903030d15030219120303021e1b10140f0601030b061606060603110910020102090a030c050f 72
    0x720b6040c2844410b41048018100340300d032041c61401030445e5a590800e03600d8140240c00d8034128411040904ea40790000c0c035081000c905003444000203400c00268030002c0f00c1d0810900f119903202d100901c1503070030011708082c0843c080c2c001c0c0c1c42c92604548075040d00441c48001540c0b0610b10310b003030042c81d80200d5008000c3c0c814100d424407002d6038074070070380d11400c241030521160382d482a00d0000f8518440c244480f1b4100d41807a446400514a83ca203001c200c0e4001d564a0041111002c0d4a0b240d02d100b42c081d12107002ca1528000c00030034400d0303000c0d0080399014089030044440d07104140865800518081114043c1c0c0400405e072103d09005460f10401c0342c02007402100700b0030511000e44c0c40000e05060705c540c010400201c5070303031180d0401800850082d00321399036650f199400d51780b8913017041000c0d2065400c0007000107125200e0b200b03c3c0c000340701c5c4240c0181040d000c0001c10015402030010a42199000e2100c04030f582c1d5000d501c1e000540c4164040003200740307440280540310703007070800d40c611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513451852 1250 513450602 513450617
    0x1b0c0d080108060a1e1a1207030b130201020d050a140309010b130209010512220b0901060501090e0a150e07020c0102070506070804120302150c091801060f03020f0405030f010902010f 80
    0x17801461100521014598044041410004440416080d9604007081a03124120780c103903100010000c40d120040d81e000328481c0c51695500e01103241d07005030341d20b0002d0041e03012003500040300c0e10841c050030b1240784503d04851200440340c170b40f04441e041903036400c0a503590703031602c0a501e1800d001e803d4003000c01c0c107005500b0311060394000790941c09420207104d20038803050002914000030518804c00c1010101407681b08040c603090005080508503880e00c419807034140d000c521903025001400071207008007481440d40c1c0c4c0b50f06081004c2d015105046a100e090003d022514004d0300e50020300c034842e294020309034028031100081c500541d69000a018000810121011071500422201560740c601203060804982e89003c070302d00020900c10341c0c4444004003c4c48034890007140101080d8104a80c0d02c13080a001c0f8440c18122a17003885038102161801446d00d091074000d4003e02112820b10790840e0500d039441000c0303402d246c0c040e440a565139645504540440d80c00024020004d0050b1600c3c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513453102 1250 513451852 513451871
    0x1d01020a050d0c15141e160e030a173007030b03070801020a0905040605040c080609090f10020301060f18090207060908070b04120f081b0c0d080108060a 67
    0xd459510b5a082038080001003143d400501062070a001c00c44403082c14100050031150080391a02a0203a80208404c0c0390740b5050401c0f070041c2d8000600841803940540b07a003200360842941e00c0b440c15016203403d805095080004a070300394020408201c0f04100d4155242c02ca00600401204040f00d0f002c21a0444041030840c03501b000400c50b400080ea00300003815407170304800280346c40100e40c000036056000088006145500140d0329080718000d0300c1c00d200b5580c90344100001c1e101c08130209400911200b0000d10703035142c07401140c0d800001e05403d40c0c03075800e00542024180840922004012500000100a00c40c0d0108519095000600c1c1c00c0219018014458854012134401d000c40c03180c012400c1e00900003a0362000c1c0200364845419a905d6480d45099039800c00115010f981d1500314943c0c81c441180500c068864010071940c0b80c1200ba0755040c51414090640240c1d03003101c4800b40050000d2941c100161901405c0c81d440d0010039600d03100c8401e00d0503c1c021b00d0b03d004641040b0411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513454352 1250 513453102 513453113
    0x60612012703020a08180a09050108100f020d1113080106050d0605070912050c0405010608100b13090207030c1b12080a020f19200607082104031d01020a 67
    0x80c4044041d07006000d2081c02641401c9190403400703a005818005c001400c54002401c12180303900201c400d8443c01c080235070719540c940446800344500d45550b0008032907108005480d03842803002101c203242c01410030b201c24200000710b0303280d03402c01800182d001030740744204d26400511100030101c080080c040780d0f007040c01050145d1540d41008003000e40350404601c01501400082e009451a034085201c81031107402d03c039a50700d86070385880b401a89410008110544038032962031203180b100d52315800d603618024101c001c55204207441e28035000041d401141c000c866000502055010780c3d00c6044c5122030b814010611200c01400ca0107001c1c0c046400c000c00640007131340c0895940c1001c0381c103450f88401d01007070b81803240c000490042c3d40254090303035141c0c0f200d0304150480c281c0034664901003022155445041030180340341440e8001024011880001c9074a00240340320f00340c100c1c001034145171b0030900b4105600269411004925043d9000c1600c2100c1c488642031f00e034091005000803072298690 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513455602 1250 513454352 513454391
    0xc05040303140c060f070807090b0f070c0305011104050a090e10020703170412030e0102030103081213060f05070e010c0f170702060304051c0903050c091b030906061201 74
    0x141805289010302c000b19981e9400c2c3c030405120b0500341c444074900001240307a010001c81d03541010450351004907a0592081d41c100b81a5141e1001e000d14000001000403182d8100e504221030103241ca400c0400011028000e40591100e01e410304ca88650601c8100f090510440d0802042e191410f407128044800c0000c801b004e5120b103040c0165140600c1c241100c800303510b844031125900c940f40910081180119400705508a103035010070881c60140203581c20f1344000e02c0080e001241c280182c8034110800285d25402014480c81400364950540d03a050641d820b15485280d0b056442080001c003e4002c0507200c0900001d10303101601042c02c0c0e5070f91700d1002c20840f0146c010030003003001c020028001381c1102e01550b001495a07859141c02c1c07410366591018041180154550100c030500c28900403485501901d80c040054401c4111390414856a010000d00081c40c48011440e40b500149949000f1070141e20703140c001c4c142e24907201d0180010f441c1c0c11441640d003a071401c2c3c203844100e07201c60203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513456852 1250 513455602 513455609
    0x4030509130c0c03030c0f02100c03020c07061e05030601120e0118230a021003020a03060b040b0706051b1206030a050f0609060c030420180109020414040c0504 70
    0x8105465200c40c4010414a203012940403000c1e500d45040000c901d40c010280d400340c80e01c42c0d0307401d005208014a00b01e0b1080c1c00c540601015034444c202141c10001c01e600045070070000e600c0d0040c1030079500c41240346844440e6004a02240e41000e00101e41c0260041483c1a41d04904010b441c6041190000744414055956401541d03a501d03e40c500410003034224950109003140142000401410b080c246008520f00030030b0954585d400010190f05c000c1501d245894004000d10042500200e003500a50b2000b07000d13000705951f40c1e4000ca07152461801a0000d45040d2858546841310380c9804001c070341c4090500424900c1d80f00180b40c03010b0410f000c0b100700146002d07810900703450b00400300345400d0705035030010100e0041d41610041200d002440c14400c0c01180b04880c140c0d1600e1404680f03600c0300b40c0e0050040158850303045900102007181149400e03025000110380b525000325050010310a0b08072030704c9076400007002c010a411340e01c1d1070030f04071104941c00c2202ca0607810700174010384240c0c40f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513458102 1250 513456852 513456857
    0x611010b13020a020703020a061107090e060609070c0c1d071404060e130e01021c0216110112092301020f03012705010f0e0708060901061b0503160203240403 69
    0xb83c0c0c000c0040c070a0100b40001c2d42c0c017410110901c2d4840740060403188180c2240301281c403622100040c4407140d4050b0f8144040204080c0909444040900c405807100030034038020711105896920005883e244564010200c98165111075040241c0900e408034000d0701c01c10400a4281e02c820690407018100e50485986040040e441d20040c401305064061003010044501d10f810440c03000c4410640041c11031345048540043d4047e0380d14044001c034010324201b818098032102d0400c000030403003e801d83c48000c05041100203038003904541c03419030b110380d90200c1e600140e041c03049840b14a40241c280d101031116000354140180f1041c10400350105108003e07480d80c0d0003012000c1c2c401c500409044482c039440c0c1c14007266840b030710b800480440c58030604d4511101c5000181503988110002c600424000741929405d9181c41070071503401056441c404809c1030150044c4001600c10001040814105c20360281002401e004041c1051444c0c0d040003105801d88003444469440e0040d02caa0260341030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513459352 1250 513458102 513458107
    0xd1a101d0402030a0603060c18140a080a050d020c030d0507062f0702100306080d030b0f04021b0f0106080d0c11060301080105040212010b010203040b070f020306040c0611010b1302 79
    0x42900c0038900c02441806904944000107008004106800040c1580d014100a00980000e000204c0b82c041c4500e0040c4100300303210034140916800c5640c0700502c03a50040c030048810303455a00072404c084509204907482e510143e0885200b980600020030070000441c06411145480c20020788640f06200f4010900c5a440c03000300791001c81810045105881603110040a000c1254903803480d902c2a4010792241d01104803100085101e8080c010907281d40402629009a002406401401d8910f00706544002c5800820b1825125440940540c00842c0395400d0a411510801410490f401e9601c8130944d041c001d06001c0e6440c00079004564a070145071880f50b00c3d4190800c0a502c00c0902d4600c0c2c2e0046001000007030320b40c0c0540020780554000ca88002181590380d81c46401c80342c032000c030603003d60000c0c48204038080400000c1e000c940c1c0110fa416644100e0f50f40024200001150215220301071000e00703006280d0710030300c0b9142d5a41c10700c00810a80480c2c00000d6074034907004074840ca607203400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 513460602 1250 513459352 513459377
    0x305030a110a0207060206011e120609080d0b010e03030c2a0a0603020c061f120218070809280f050313090507110a0812040206041205030d1a10 63
    0x101d92041a084458950315502e8102d00a4025180d40326482010018800d00d130020035500c24442207400300010700300781c020750580b80415082c11110040016681c95542ea20050040307981d02d40102100f26540d600064003004040c009840146181e60860096000348440182003800146c050611084100d6611442d0714030010302c9020800c0c03034980340d040480040005101601a000303408140345410a5403415030302d040a00701044000e0301103030b003c0300100d4000c001320741e5001c1d810f0309100e00150500d4100e030000141900406000d4030a180021090300400100b64010300c1010502456266910140f140301079801029074403016001d0309001c003010b48481040310410882e40c0c40f90305c0c040000009591001030b03000421086a108001c60480c505600c024100410a0f8111303d80c001c005034180540840000c6c1c420350024000c81c4c00c008200004502030760800c1c03081d01c150388150004c0d5900c03092041460107443c80411400903070b000360358910507180c0c0c500b1f2030a2130100755842d02c61f210f940c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 513461852 1250 513460602 513460621
    0x5060616020619030f1833060305100b090c09040c03020706090b070e06040305030f090d02060f0322020d03030903030638040e010b0a14160c0504020c0a030503 70
    0x2d904400c0c101001243c42888810b5003542050b048012428400c0007031074920640203003146102180107003030120382e20051400c0a0403d01d040350740e04900c41140402d042405202e4101c50030398009031032550042070700355a41c065a011306800303250f040e21403805e030f820301080c90f0541e4003441180c280314503140d0103646601442503060720700c034036080401484805190b040c94100400c1c00d82c0d001c800607404000c00c6401d41040300440c0d003241c4d4040c0095103800300d103000c8413040d40c2050340710a50000c1c4010b07141015a1310103014040004e824248a42c0e03a0509032103204040700020442d06449241c05802030150391346200090710503425007001314483d882860110028101d54001200384000c80f20290544466201c2c8081c5440d0342e280b000303088103a0310340242c1490045115191070490107400610200070034902030425110a0705000040c4d007440700d040e03485600a03214021520000b01c080300d00348108241c1d40802410140d40c11858842c052002c5030311908842405818050000080382c038001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513463102 1250 513461852 513461857
    0x71208040503071a06010807051c09080d0e07081603020901030201030f0905010204060203120f040c032402120618010305120f09030604030201050609070314042a0602031903050606160206 82
    0xa40c0050b82c1d001a41d4904004c1889540503960350b03001440742c100243d41540242d00312030245c5040380c050010f40115800140140594036021580321000340f040154450b01800340f02407280c0460007030464503052115a0f4a01f00d00030310010050701d85000c0400150300c0708140c072415a602880c01203200a80015004050100703c1c8008240d580300250004e450741d4040007501c10b20904981654a175205c0404003400c804040d10054002000d8001c2003000030300c0b856080e032246090001086410748c0403c070003070403600070b0702031040100070104c1086110320349102c04040850703068800080550468844071341d11000385a00e08500100000c01d03990707400e455015103001010040c1250520710306072900a0281500366a1a405114000086804c95000c1d00a00e950016926623400096071140c40b500e42c11000805481e0960840641c0c000b00b40344050340a201810040c6c00555031548601c0d691869841440741c1881050f140609001d41a99180c0032204440280150059002110300000c3c80c1172 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 513464352 1250 513463102 513463117
    0x70819030e1605041103010e011202011407120f050a09060302031008010216060b092a0c15060306010b1e0a0e060304150501120f0308152d0105071208040503 69
    0x28450803404a00c80707003640e6066803c0d51816102070004180000805400d1700080c0506402414480010b00104040300101d01c401801407600c042c1c28103601c01c0141566100b840309039180c8400c400d030441826000840c1d01c44414081c6052498541da1160052400805019010030503030004081081e401d10b00100c20040c0800c08000c554500d202070006070b4840c55a401201c200d4101101c406540ca0b044402034407502c0c079600117401c000115880011595881a031014034410280001c136420102005547c00c07010303401d40ba24240c0c2c1040707001c240c900f00c01640042d001c403008101c0d030550b408550301410350340340c907005025032181c0c0e05160075a0b00380800b044468021700007000f00402e0184020b000200d4100100041125903200c02010f20750020750840540800c420050030000030f4490320006500c841d0600c0c0c01148000c0100000d0600f101b26045c01d04400c5406441d4003103025018039030561101c017401d00302c0c50000c0e00d544840e03003813520703000e54014850044001020b2090030b10845086 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 513465602 1250 513464352 513464381
    0x703080f060a320103152106060e060102011505100503091e0a0614010501050702060c0a05030408100b0a060e0d0c0b210f060108010909050a120503180307081903 71
    0x100480d036558107400500f80c80c0180751000f06502296a00d50182c403c03240e072040e24400c69402582042101100d91400c106d0340480c0394002405080820340d01d10900016000201d5084011304026000a0170b40f104400400100e24044d4020400341d40c445803522000c9160b41041d6460340d403003032056410308a0380c002500c008444a2120380c0400700104180d242c040c8034010412103032107070090480d10b55609015090120318100822005840e0810103402d948030074008a90902c04e05503141400c1d80c209600072a01a0302002c144135282c030310307400749102d0080b080e940e07a0440ca00d800030050412040c4190140100008078015050115480701c3d0800380900703400195440300e80b0310407442c3c010308102e42c2c181400c1d54031000c01d18080411a40c00e000b2041655004616400d003011100141092001207480e4400c0101200008007104c00840701d1180c2516605c1d00c1c2e250588002003056400382c80140181c1040014800140036041a00c3c0e001c540e0800d102040c0400540c1600105100f8820408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 513466852 1250 513465602 513465629
    0x90a030303090c09061d091e0d1704020a09113123060a1b0b04120c170313020622170c06090f06040906080d050703080f060a 55
    0x9168140d00b150500341d1103070392900e404956072801101143c2860042a14803022009060300305076003000201c1d08113480300c00f640e01810300428212940c0103190081005e40c0c100100f41f02c4800c4e08401074201001c580c81a819252a050380000c444001501880d59050355480a82891454141c2651919581c0c0e410383ea600d1000041a64074130302002e001004000c09020000c69801800c400507083d1140781492a0030060a407010003078243c10032443c45080042500c226121a41d19550f00380403240243e4804249003854100744460b41c08030704140050000c01300b00400002d444a2040710b80d03a0f40101040d4481d285d410000c031b454250b0b070304065400b400109160204404080e51907001c0c84c0f1003515126540c2c0d031804120302448255490988a400c0380d401c240c02030401e0001071104c1e50008207000d91084c0e18000080f115003040c3c105046080d503400d000c2c42603000801c40340503510840e042850809066980003041008018180300c04018542c000c240107894944201c40604910840c440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 513468102 1250 513466852 513466859
    0x6060d0602040b160203060c1216050d060f03062a030b0a180b040606020c0604031b05090103080c0f01061a0c330105060702150c0f011419060f0614090a 67
    0x4e58084200300140d00c00e003d8072004c1101c49010804583c4212460046e10300d0607030740e010700e00d17204030703924030052050004c01c010a00c3d0303c00852040ca0003801d0031f42820f003000340c21803d0110865898a00d0b11424281025000089001e0843d074019550350790325000c00c1c0c0d1a04800860b0a046241d0700c00364005048003907000605042e50451405090251003c12186503200b0040383c0d904144200180c11450820060001c941d81018980d200414901c181c51450364441c0495881d00003640165003140e00803ca40791000800d1010a4155000340002c1c007000742000301c4034209091a030314228031000001000ca44807407090145c036481a0309208800039035a010710320405000e410000c00180200c0c1d100001c501868610255140d15070003500040c108008844032007141d0b840000d20035503030301c100c00301d030b51301c001d000d0041c044890f50540030091182000c0160301c542c024900800c8900d581021010721040c0780c032038048400c0342c19904c2c1800c0304400c40d0101102074868403103055080f625a00021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 513469352 1250 513468102 513468127
    0x2040e01060801230603010b16050601031202070803091e180a05090c120c0108040f05030c0a0606060503040210050d0609090c1a0307120903090b130906060309030206060d0602040b 79
    0x5904071130400711004c0740029946103c0341044c02c091300c002c0d0721003020320042c0300000140020304002c1c0080304100312070b01031503165189490b000364012151841c821113803851040d41030020310010945c0b100290700f8080103030000f0315a6451044142c2085101c080040051f56810f0b040440d403e44154008810703050646140c405810300703c3d0f504041d40b080c10484e1400d0309120300c05034500c0c0940c0010704282510a4011907002d80058016120001030420040204030140002d040702103d4600070309020810f80317884001c1c1c5510343d00a40500ca000c3c000c020250b00c90314910800c0748160301e480c41d610b200e842490741c01041680c01455070fa900e000342d030004024140c6800000d540f1400d07604240c01e0200c2e1410310380f0348411698500000d8520040078481500da40200b00e0252090400b00b01207038484444001641000c1c81401400c100b49100b04050900c9118082c0501030500c3e05101d0f00419480203560b460018120901960400011509008696058401411401cac01850b5500c2640005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 513470602 1250 513469352 513469367
    0xd05070c0614220504180305160203010e030d23010e040311030c07030507090b0a0b1606021207020105251d04060b220e0f15040905010606031e0e071802040e0106 71
    0x4c0a0165203029034003600121003046040342680e01d99a8240380000032414184003401c058800c907010b40d05ca407003070301345d0720310a0000d0404000901800101000c1321003800a60000840d1101c2c100048003005000503661015269401034240c10880b001d40940314100785075100703103030944a082c0207070000032041210104a40e821a01b610405118000260041008035a079a105400080c1000c00419071310b845820760040100e4020390005003048414040103017005011a00240141d540303000300084500150300c0c50403030810600e08103d04080609002d01a10300101b05500400320b144038a00d010b03612904244040c0c030b050003c2d00c1e02c0318a1070709a03020500c0b040950544452400d0004201007078104002d510070f850310400c2030016103410080c40380088003680003640060301d5982440114400b40074401c0104401d07075000808905480340d500007060b604400c90f00c03da0914903082c41900780041e1080954060643c130411740c118612420f0003e00c104d501c0b807610506c43c00000102560010f06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 513471852 1250 513470602 513470609
    0xc03010615120b0f0d03021903210506130b150f0703110115090b03031b0705131e0c0519080f0105040b0109030321020f0702030d05070c061422 63
    0xa82c00d168248507010442990741c948141c07900f2040c0701008041c5483c014540c0807215010f40146c41c10590140044050a0304800041d004503c1856031441e46c0181c0407800e483da203580721020022810709000045640395410181461340791222001449a941c0c8440046000d0603d5103941d51000b070031550b071449400c220015004036159071038491040e0018040e50320b040a203801d003980802c0c02d0140e480c00911403950f400f40c244c802440401000d008250981d00c01000400c02000b826241c0010080a1560711000f81051f0b400c09580016103104001e50a0000c5036210000c95848002d04003200c150181c3c02513140c494000300c800340396440c4c001c1920b49c064401e0407001880c507a2141d00744401e641525000c03600003610240100f0109201d0301060289982000204500e02242e141c408166003204180354848400001d040301140b03410492100c50010b5401c215041c06502c4d00c5080700105184290018440003044846282170480c0c01c0f00c036030b205098044600d488088141c0c002107500c601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 513473102 1250 513471852 513471857
    0x5011101020d0906240e0f0c27040e03041d04050c100804060b0108010b030a0c09090212090115180504051c180503010219030e0c03031207120501050904060e0c03010615 74
    0x1185016034002c0c041c040c003914110b0298286c0c03911110040400c0110040c0307401400300e81130149001c5240804c00d1313046150915804484c11100050030002255205030100c10342c1c0e03008100800605091006100e1525400c61030701c0c19a0741c3d5403c1c0b081c100503000d0701c032603031003034070440c3c50318015030840380d12809035004540030091201203200640b1011420b000301010600240005454001030b90805148241d0610303040c0e59055440e07118000341d800000124501242d60020000d844109106401c0740c1551100c6443e6698900442d02d0207814062580340900f64980c80001c09100040081012010458140e05201424090003c100c41050500c11500e17041086000a0510f014002d943e00311a443d102410f03442c2c0010070a400a0001c0512501d4a001d40200340b07095507028009450010f5100c090401d641c90169801400d80c541031140d40303191860400140840d48800c4001c0342e0040e88542d0001d40030740d90411052520070080e4056034150f0074048003040620ba02c1d8040a450140b94 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 513474352 1250 513473102 513473141
    0x50d0c080103030c152c010506150406050d110d0209030d110606010c0507051905030f010c09050915120f0c0301020c250e0a050105100201050402090105011101020d0906 74
    0x11900321881402840060b0010f15102c6040001c20410148001c401c03041c0100020801440c83c203000c181d950405480340740521012000040000c20f000d1940d2142040b151001a9800c4214243c1140038038001c0d90704010002c580518000c0035580700d0305920030820086038071680e0944015010350306c900d404a01a004003070201a02a005400303416a2022860243c4521755484004441c0da18500400f501d851041c2d4900207000d4503100080e000c142c00185550940034180000c3c50714054912034032480b1a81b4000d040b08107598010340460a407030b01141e03811f965445016020a0301038100000d00c0d40003140a03414480d1510000c0c1040800c41a032040e5903003030400b417041500303c0c01089841c5145070410309511220404800700242508a0a0035107000303103460b03803104040107600b211a031468969441c0103014500d010800d030040d040c1184001d010500d03055000c1101c0442c184607260502c2151005183d504c2801c0d01554000b0240d030b6070402500d000e40c18684080d002c1c1ca074013040c44110300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 513475602 1250 513474352 513474371
    0x903090f0f010c021306030212010516050a120506041d0105010501080117030d0509011e090b0f1e07020304080a03020a0c09090b0103030503060f100f0f1e032a050d 72
    0x2408044120300d016110f64412440c00d800344516011408482c0070601da40d00408001aa00c4041054100d404100001020300e041044401c03828003841d83d06040c0320f41805401c40d030550011000c0e1011481c0300000c6030544419022501903e803a002160010048030010002c2c01015482030341206d6090f600c400c55a40d840c10f07103145200b030031641c800c100d030810400b0403000c0c0c03140d80045411034100300000512045800c1c0c001001ca200404000100d81c60f0160b190a001c0700e58495a00800341c1e074140383d841c0c10300c1411902401201e10f1100308281404c0c0025041078004c2c02607500902c0e4140a940f0001441d2070300944642824030110755002000101040203040c611030144015480302e4401c4883c0d0031a101038510390001080a135203c401c014908030305858200c0c01c0b40e03034039203d51105004000854405030404400c65010410424245d14162207807203009284080d100003400d001913420301802c2c5030940052049020101030314050301d80010643c2c0900101049030952a00300080b141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 513476852 1250 513475602 513475609
    0xf2a0a03021c050904090c0509190c03021206010c0317090c01030f0902030c1e03070303120c0c030e06090a030602120907170d050c030d06030b06030f01050c0a0c03090801050903090f 80
    0x710002c500000f41c05020f0340c070b2a410f041d8415420140105c04441d417240e50b40b00001c2a0104c1110320040704041d0071101480054a0300a182d091511420158240b0804510b00064098000c092504005642c0701b29814140950f81d8142c10000700035846d960b616003516030556a0f04100c4400b80040e01e001746c1c1400703604640c0b18801420340d0040140188001000801c414841803000600c011805200001c12a5804004a00042d84a40c0f203400400071100c0003c021203940e001700b5408e10811803200800250301c0900c0304044501194050745030b80b19031000c00c1140d0000d8200500e014070010b8240740d560a0028440d10071080b01c030460314540c0d221200b10801411441d007420b026172168200b0440d0500440141c070501e840c0a00b1070b0708102c1204000c4c02950025170054645141d08020711030300d41400e00c846100007540e040248a64200400c488101e403003106074034420030010605403010584109440380040042100901050810500306a2680c0c03102c034ad554820120118019450b05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 513478102 1250 513476852 513476893
    0x100815010b1207050409241d04080a0c060204120b0105060a1b0305091903110a1a0c0f161509150c050304120303050a061205030f2a0a0302 61
    0x1551620482c2c14290b65408030a410700d0054032060500005000c08900b840040c402d01c400e09090404c0300c01112441051502d80c101690031101c601a102000743d0300212078010926046030344420401d40e1000c1480c001c90f03540c0c1440400400c4180001000102100107500c0200018040c20301c1c81441e99031041000942c0c4200c00c001000700300c014128910f010720000c19164045d0003814086c0ca072552410014041908031a030900704000712100a205220b910040411810303400c1d2840c140c4e407400e020030004050b000c51040d20f0208000184810075803405d02900b0750340230aa50880c1e00c075013403003a00180011194000d4499045c5103115032600c481c891042c150807980300ca603c0020182c8940f80454003240344400070b4410f44402c110004600d0010003140126900950700003c150801200d80d0f03040e500f130340d0700c83c0507124003444c02c0101281000c41220000d00306d181c0040d030b517206a00e4000d064050700b0b4030010045a41d0507400414048003003200290148642d09407410720030105507592809 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 513479352 1250 513478102 513478109
    0x1060c0506070311040512030a03060f1a07080702210d02060402090f090a0b070207080c04020403020a180b03030706090203010b030601060915021903020a0c230904061410081501 78
    0x1648008003081c0c4040c040e600804c9210340340c0f0300080c501501d4101054454130001d8400055600009078031841035850701c241c2e00074114001401186610b4042801902002c20b130219006030000a1685d00700084101240c00059025010f049504c94400707030004005841d030b607203030784a0182d4541c0682a500c080f500b207110300d03401000602c0c10b88405c850b4184880000b0a1003015100c0d150b03201c0049403410842c240b150105070b0040c05414144203009040680000285019034014401840107a0742d100114094450100e00350a10060013209180a000c80d2400300740c140c080010b9200a10203ea013002c581d06000b0703002032155010f0203041c113a50304002d106050000d6810802407001c40070302c400c4225902001d104440202c00204542a80791000801c1100503901c07003c0203004000c07055038100b006043c051855004405844200d445203848400c020344075826403400101082181d50240010a000300c070058454907003481d01c1c082d000028041e258080c0300b00a01281e40011401c0250b050707 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 513480602 1250 513479352 513479363
    0xe011406030a050c07050a140c010908060c091f02010b0f090402030c09060301140c0909100803070807030c0f1407082803031103041203110903190312110301080601060c 74
    0x7107a03a03041e00c0c1d10052002804c5014215020403141012650400080c0d0700c540c044e4040d911248419015185000c441c00046814000c903450b04011040020031842e038060400840b0641c2c5400401c005951a04501e00d44003841e003004886241481d415802059031841c181d450fa5034417034540003042085030044074025490347c420141c115003814401080d40d000b040240c0041699582d802d803032400c42c1c2e0308440c00c0c1e90790304011808070345525082e01110303041017801e04004412810a0f000301d0300c82c030a0700f00c05401000300041c4001010b00c94441c0b490002d8000055030422444d86c42e00e845d010500c6241c80c07801c2e104d6494081a440804204030510714108080300c08040303103400c1c0a08100f40c0f400816400e00d40d550f024040a404040b00461180384a41d0401e0b140d8401ca0b18040cac101c900316000711501c080c0502540806480c0000e0f551a694103040d22421010000d02d000c6031442c9a01040a0170203080200b5400c410410b04003460580d45010166280743c0c3e00c1e1142252404100c480c040d10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 513481852 1250 513480602 513480607
    0x50a0e030a030c140a0e031501150e180106030b03121c05060402071a041a0601090504020d060b0d0c080c0f03010b0f0c010c0c03020114010e0a150302040c0206010e011406 75
    0x1001e8000d80c002085082d603800c215001a101030308240d6a07030007038007082d008500049844405031406024014144d0780702800c2c418603505010810411085e010400750038400340c050710840740c0d42c4401405816165100040e8425030b15414024050705550b0f2400303002e4402c0710b01007034410031007405444612507611003036202c1d440b039208840081c1001a0105412030f41c200007074030106615044880200382c05044016081c1401e180083d0580f0426095080b402009001d00580744e80c0600c200c0708550f0202c1d07016032079803604440300004288590106141c0d8000161688080c0105d41022107081000e8035840142c1d074418411551030700c50925081001003040006102041002c4040c25500c01e45030782042c140038000810034215100401c220020407180d0814404242e42400b41c1031143d441148088940e5240505190143d20003416220396940c0b529040c6050581c081d03c482c0040d0b80042041c0b150b01074103217019480e26400e008409181c4a108004190701d882140724122006000e0007891 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 513483102 1250 513481852 513481867
    0xc050f041b14071a0402120102040b030705071103010911010f23211905070c0302100b0439050304050c0105160821010501020f031902070b0d06050301050a0e03 70
    0x882c8034549580c00112040c0501040021640c4401c003c3c0005401c0c0c007410390070b8201401005111981e01040c60407aa0040001780401e00c0c100d41982c2c1c0082190500c0d58449215150420803641c081620303940662900f03207084244026403088001c1c2100a07260800d08504c468001c403415940d1054809190020400003503082080b20024030300d00005039004011a1000c0e201c444c0043e5040e600314080c880c2c0c04042e40c0030500300b4803501e07410021600305207079003e000c0d940103034690600c1011501302d20b80c0d40207035100300e48a075000341e074003000401e030580008108a0811400d40240240007001d624028555021003030048040700e0155801500a0510074038003001100c5950294007010b4145803105100350005462401034510007034584040d0b681f4800b41000401c8131081648040d0441d40a461034501155012045506440a03520b040072246044001a460482e01387d210b540d060f40001034241c850f8100f03a01400507140110000d01c19510b8844071603080c2c480c80e100c18a040e0f0810031001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 513484352 1250 513483102 513483107
    0x10201140118060b040b090a090209090402010e1c061a090402090c071a010305010e010b1e0423191107020a060e040b03010204060512010e090a0b0a020f070c050f041b 73
    0x81d0340c0840702d032202041890b100e508041660b0840d030f101070400b072008585401c039494019400c101800c4404011420032000200117406080c01510103414003505138242c0f81c035602c070381c56a05998030604006204502492078041d0040c01c44020340b10400d04052205031047c9462707400c09000b26001000c04596450301071040300540d005003022500421007602184c0504001c60b20f05000358050300001074080d182180c5182555007a25071076118170f0310204030080d01c9080c1134138802003540076507001806200080700d6030b058482c0b54861605010305001040244542000d41500f542c80944043c8400003e0702c540010901840344002e5000c1c00801086c40168401c03420441c0d80b00c002000420805d9030540130a003264015080302c400180b00042580c0501c0303500040c036006110240000100d880c0245140b500c450013400700a0a08030000d0210f507400c2e03896019222010b4561700455a07540051809404031000c0307100e040d000302034560400d07441d4602441402e0721164500d103450100002c88804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 513485602 1250 513484352 513484379
    0x5040b120706080c07050d110105180706050f040b0313140106030f120201140f0a0e07030c05060f120901061805060d02011b0f0803090118030e0409020d0b0f0f060102011401 76
    0x141c800600b014000da00106e0010030416041e15000c1d210558140a440c5003903003954802084a040c800d840340d0343c0007400000049800487c0c82901d005900c51100a060044603c55a48515a10301000c010b004080a107040442d103560f200d0f05043d462021382c0000e082c2625601c0c80060000c0d215083d01e0404110001031001d95000c0341c1c0b00024240780700840c29010a4026110303103210914090402680041a03c1001c0a80c10550020050b107499566a891540128044c0900031280400d68030020700c1c0340345c181d90546401101c80403c5242402010b40204502d10a070808040c440b05c00700303c0143c05200d028010310000e40003c40510388c0b5001519091841308841078490460840c2801055001c5100441c0c0c5105008a035980c0c105070040e5401c0d40e80384000c207880c0c00c400f54580d400098024101c0d40c05c01300140d030045015002130001070b81069150202420140704007041014114880c2c90852081002000303903161030710740d18012401c850f00c0070350400ca500601f80040c402800790410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 513486852 1250 513485602 513485611
    0xd090306020306220902010216050a05130b0915030105060604061205060111030d0203010e01140303270a082a060a1b0204181e1707030e04060f05040b12070608 70
    0x1814070202d2040c20301c503181c03103c00403120509550390759401c08548e07060100501b40981250207505042c1080002150058103104142c8606604144e004036005503400500b20202d000b04013004a1420031507544e40c140c502c1c50b00ca4800c3d440c1c200080d00c185004410b0b1000d440142d9076242014402c402c441e0000c0201800003414005161040444041c0030001002c08410100c0c01580341d526010501180c1c00c410303007110786034415154500821b40c42c00415904081151b103444070140c500e25582c0820341e40390051141d0000071202002c17030003810006d84907041040068030700b80039031000c0041d44601d610b51100c1030350100c8200a4485410310840d80500b04e040b003250311903060003a95000604607404070444481001000c92240f06110b5207441c5280c440080340d044000d980000c4c6e179070701c420750105244034020354804074035007003498483e0040c0711040c41c029004119240c0c4a802241081c103040c450984500d0611400c24502d0800b4606600035452410081c0403c0741440d1095520440007017 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 513488102 1250 513486852 513486859
    0x60b0315011d0316090e060601050304081e0316080901091101030c02100e0a05210403020d0f05010e060115090f030605180703060501050103050a14011509030c080606120d090306020306 81
    0x92803400c0b595404d000f002514542e03048191406850304c06140c0c1900c08a07002e011061300880c04020050340c0080440c0d5206500c0380c001d0750382d000000c040382510704480100d6541c4070000700420208903100b0b140e002e8402810703250580942d0ba002803090036903100017801402001140c0420069502a41108001403c01d005481500042c591094100e03850700c5022110355002c0d664200c14031009000e045680500010500c0c0205035420b113101c4144100c1c4030003030081c0041c120310014842028803802c00c1c554020001c3c452514052180360365400d003030141041c480c2460380c1e00c80035180140c2402017101d40001c00a10000d1035900c5a40080500800648588204440c1c20490600a101020284d48154030024242d414400010100d1b440102407604c01807070302103a28528140c2da4050382c11558428900050750000ca003040f20b055a040d84003c2501c0100403020921910224044d485040e050701c0d02d20750080c0d12804580d0b03807203100e005500403c0c0d0302442400881c0303154000390380c89500139 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 513489208 1106 513488102 513488147
    0x3070620160f0609050a03020607080606121911040608041a132004091a0c0a0807030e1c0c03080c09060412060b2101060b031501 57
    0x815001e002c0c034410070318050400019400001c00164080150354960306540340c040d64a6600f65650b80200b1844000a051424030806582e041d2070320780f0f065030698907428248100240da8558000c002c944405a030f854030728403100140010041640d8980c0f8501d400c5c1083c2c150b803050784050000c81c80b0440180082c0781c0301922941c11003600080354220401a424020707078450b50307018041e03800a041210160a1040c8100c1c00303403e41c01d07281101507583c1c0e038044158078148034107000c02010900d444040382c689482980300c41d010200180071581303817001c01c00545101213680311b040000910700703800b040c0030907a1200c0d40c00c3d048020310f81c4880c00e141111000a1140c000da008041d03a131521008888240021a0800e01d40c800300988030410582601640c01468108103858a000350b0030030000013003d10040c0f0889110341c400c20345001c04001e805004450026482c085081000c092 = true := by decide +kernel

theorem cover : BRFrame.Cov 513309352 513489208 := by
  have h0 := BRFrame.cov_init 513309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 513309352 ≤ n) (h2 : n < 513489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
