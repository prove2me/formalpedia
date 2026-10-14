-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:38:51.803613+00:00
-- url     : https://prove2.me/submissions/df08f5f7-9443-4928-b818-6925522d3dfe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433812949 ≤ n < 433992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433814199 1250 433812949 433812971
    0x7260d14061e04050405011d07030c060206011a130b1603081b04031e081818041106130512010902011b0c0303050f130f080f0c0f100203070507030f0204 67
    0x8001118074030031000c4034090805592050101130900600308841035901c404001494444600b24005003000c0c05004000151a50809560030945544800c0a41d0055030060006a0071406444420240b03c44034959409000c4d5103807505030304541c80341d48005004250b04030340035119480040c2140c081e0340d42c0109519182407200000a0700303514840091001c2000f00001941009041d503405403050890426440303070b840e100c5403644501000c00c41140322020071015481c1401a154020780c607058600660720b0180d0f0703211b22280e0041d040714410300c00031940c040600f0752050004060140540040010b280c040326440c060b00c50720004901003800c444140e0401030001468120b03884d042203600710341e103155841c1070365158000318184031041020089110112000000c15004007400741861240d280f500c0e4415003050551000b80c4c2054000c041301c410590780b0904014070045048a2000d200c02c503c2506a14620648400130468051340500100340030340118a0b46803d4000d0714280a181990 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433815449 1250 433814199 433814209
    0x20904060606110106050d0212070909110120060a050c1315020708030c0309060a030209030f06040308060d03020606120a150c0e04020901081503070801020f0325020307260d1406 78
    0x900031b0a41040f012807000380903150114440a200e000301c1d094600355502c1e40c68150584003035110580307215403039621030344c200c1d45e11402d0085226101e0419040c4e81c0d000c110100d4440002401e880121502c50011030800c0d403200044682e1844041340310001503a9541d4003050b10031842125030094040d90034005000311001c01258102d41000000d54903041d442000c04c2041d0b040240d0311420141d00307005a1406403001c12001000c550203100418440c90240360040c04240c0091500b8000d0040301008400260000361b0241c011000b00c41484d402d48252600501d000341c000c2c006404d100700208610080b04c2e0540c8040001c5460f60783e50100d1511540a110691240035541800201c2c2140014140e074940914078100540003010740c0c0311955200340060990b040340b1a920034040001043c40b200743c114100e00072400840c64806282c424039520081d40364050302c4e4005e06030707404600101c00e150010303070326075a01030a45001058690428201c014000e164102c50721380ca107450030002c00c640d03140c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433816699 1250 433815449 433815461
    0xc01090605100b07060f0b1c0203010b0a0f030f021c0b07230a031821080a0b09010b0a020f120405010f02070f060e010306030204020a180906060815010c0209040606061101 75
    0x40383d180e24503290481c0c2d035640040440200b020318041c2c2e1403201060a655894181c20f03901c03803400203071107044010b004041c2100d200a042e0f0f449008480c00030880d880ea0fa401d8075040300d8001c88115454280c500104951003880d9524000b50061002290200b205522800e805005207966000c1c001da02c6c00c039594000a4480c1608140030014403510010754401d41001140100e04541c0c030a81c0c0d0225030b5031038a401d5440c00702e11400c8032000300c14208030350301003100c07076102402d420140700d0100d070800401d02c1c181040c0900140034400140e602c032014020443c1c0d4903050050001c549681010320180b0705903411030f008082c0094120069140740d181700054074415030382d100d2070749444145400420f440d840c1d02d082c2070505050700e810380040940d40c0d5101900d240c1115465480d044142003441136000d08154000700c401d075180c501c0500c0b02c26484031055610101d84040520100e10040040c0c41b105601d90000f5842a810001c100c10010300350880c100b1141c0c69190713843c0c4151200b03402801d80b00c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433817949 1250 433816699 433816709
    0x80c011d01050603030d0e0c120c03010f06030b060108040f051209040506090f150a0e190b06070302150c0f0d090c080706020c0411120108010605010807080106080a0905030f0c0109060510 82
    0x40207010841d1940c815901c0007c0c0580c1c40030895800e2140000410600800644200d010b5000b019148450342401e000310f9000581030102080b5640c21995030301178501000e000305d8108030b88800010200510300840401554002048038500f4207025180d5681d98001300d000d81c021400e01c008290b07141006151680219500003690300f043d9a0089000701a21440c5a103651200043c20001204c1e848003400780d01a00c03000c031446640703440300c0041c5026601a0681d20740154030400004000ca5030120340c07021203409050300742100b62501d1200b07003040c0c00340f40d02084441a0029207104403501ea50f10694010784035017416550f0035900c00c55245c44071050320a00300944c0205103070b90420b1400ba8441c0190b0742d030a0070614103005c0050b88006c0111000d03007044000b695150024081c940c0c002c58030320b601005a28201000d9810554028a03500300a003107036005035202e070034090030090140160360801e03c036005aa500e50540032003090207801610303001d40703800d443c02000c1384141204404d11016a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433819199 1250 433817949 433817953
    0x306030d1b020d081902060603070b1e030601021005010b0327150a09170703020f0d050904020a03090b0c1c05010509040201180315060e13020a060f0309080c011d01050603 75
    0x28a40070b128182840c210200e4401404021890800150a8000c1c400c84031780e074010100b518007081030500c0c250141e0400011040c003482140a10700060005081d0504000e02c001e44030340b90708005034640410081c0100c04a4100030004c00e0409009001c2c2d4820f80b400c040ccd2100400400058601e4000340c280c40401d59082100b0481541071090091500000781481c0000c600075291030b50302140d1010118440c1d40c480004030302c400d1550400c6007602d451120000740c5569210800003504500c10f00705503500842d00801d195404c280281e000c400110b0704a035002d6491b1030f0106444126502c08010244c1054104d0143d0752610031500c01d0703e041c0d450140498025440e540c00550300f0342e140a24031003944444540100000740702d2028200c030301c0c40c1c42c00302141250400920721011840100b003001200001d01032035006da502c54200c4070440b002810490541a0740c0c90044001c0d10140402401c038010024041041420550001c0d005000303075000c401031200103600e1907098600030380c2c0309903041d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 433820449 1250 433819199 433819247
    0x6020306011808072102120309090a020405100e03100c0207080f0105010305060a0245010e01024b0d020703080d0203060a17011a0d0b0a020f04080a080306030d 70
    0x8605c0c1000e40c5d41c01e031341c070042d0748146400e080d60000340d0740300030798403841180d8102041c4107075075050034441603410900c00781c0c003035041030b080801050b001802d000a80007001015045510551010b120804040c20740c0c84052083d006a5039019541c1d00c550b1047d07891760b01c110040840c281c0340c107203d1507042c0c1c3da000024008548402ea4030748003030b4220041130300c1014843c0310b00c0b4050300080c440400700130003000d0b20403010b6500c40c844400782c0c0d58a507803403605110519001010701c0c0c4c1d01050b400303641c01610300702c18103078911205170380b03031218039032100c0e0b0110300b61b1395862849002c50883c460f2000ca1002d04a514008400101303e03112905484014041c0340207100b1090300c00701c1600519030240300a09060b90165031090640c5079501c11440860459568461503041152007656244411100361425032500401d6a075040f00c03a100284500032080d40410348201e94005007046a00034400d0704111141c080d62810308080b5580240d40441c07191240f0200b0740d6800e0301030551555059401f0b840d02c444 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 433821699 1250 433820449 433820459
    0x150311090f0307170a032c04050702010b0d0b0105211b04110d020712050a020a06020c0c03061e0a050c0405120c060f04030b060603090a0f030210090602030601180807 73
    0xa801401841c1d941e040c0129038002c074104603c085411008000140200303000b14090030082c003000b03900000504070079448020052140e00d08090701001440640e00000c003030707850042c01c0340140508800160b001d1026000c020a0005001710107058a00844020303000440840411001d2054011210101c2e0800300b14904000b2040c91241078103040640041902181001403002c1c9511940c1c042c64407036404140981402400c11451031051fa25050040c50000d0480c1c0c00380d42c88045000040c503030b0342c00044041490a0500440e05800c0f00942202c4040c140030201c0114003072900410050759070103200085844030280a8580a064445074503071600d0b00700400d01603000c903800441403081c89451003695054480e41d008042d20100030800c01c1d1076604600e071080e00100d010b01501e00c1144c050042c8840c020300450021115503012681200d07402240c41c2c203070b04105400f21640c100a2400f0b00b038400384030284c2c0045104810980e0340e01892aa1002580c500703440034000c111480e0300c080f40c1404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 433822949 1250 433821699 433821709
    0x4020901030206220f09150305060105040e03090a0305010c0f03140f1807090c11071a1b0607030209010f05070c0e0903160804050a0509011508070302090d050715031109 74
    0x2503000007040c4031503604020152203902e10a5140d204000c40c94103817004024007101131060007070840040b102c58888170f10315118281d6500741030040320f1060717650701a00030311350008100311950400007501d0070303100507135030b0800c14024001030a403000030440d200001200350b0b00c41d00c0340380c44110100000c0100c5494400940e401080014035003040714402400c0030101070020002e5800821400c1000309a1940f8800024090700070790001040c06d5118801c00e1045c05040c0040d040a20740d003011442e10344445200c003210000c40c001c0c3c110407500030300c41030142d000d90640092201c00001c0c0c032038500d1080406400c490ba03100704103014196124002c0b06005400f44904074507085020b44c000c403401c100c40f100b0441b40003880d0b4082103880020010f401c00450802d0028040180740c04c81e0300000707961400c0e0b8501000001240ba80c0c0801102c0000941d015001c3d0b410798401c1000a03040030b00754072081c0f400a03034425090140004c001903019071060386921a0103800362400064011070705001e55101840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 433824199 1250 433822949 433822957
    0x16080a03020d1b09060f021f20040504051e0f0702070b040e010f060306030309140d2405090d0e010c0c15080f01120f080d090803010b0403140604020901030206 70
    0x20080540030016002e82e80100e000d4031a581c2d018448400740c42800d40c00240101100707500038000e201a0498011580307401240d5001c2c0e50341c100c48000314280055a5050003802e10b6030501003803c00092044050140d10710180080c3d9809031410841c039211107041e403442103c03800e10062149600300010700883c041452260300010304e801111400d0740c8540c0d40440541041e002211300301c4002004122406c00340048800400301400c0803c5114110f8900420042490003552030a010b0754014035503d03210401c1e108007540d0040c0304407107840c0c007401c56102a40ca4164a00c990581080c0106070610808918012641000d031034000b56035480300e005454a000c021300540d18a410341400090307003000980702585212250341d90750102d00d0460851902180c1c1030300008003140010070440002080d00305010a60798000c4121030b162181d09071490094001010014003800c000f000020710040200003a005603481a00403502c283c0410b680e01e540c665044074041d41c8403040c60010005402c00300020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 433825449 1250 433824199 433824217
    0xc02010b0d0311010b060328050702060402060a0e1903120906091403070302040912080f19020318010c0207080d0e0d030302031f08070314010218040b0a03050a1109010b1608 76
    0x3244505d800c1c00050440d41044035000d580741504d81c40c005147c8514030104d02074900d11007080050f410400310085d070350300004000a000d410000b070300a0350f4a01a685060380e07018001c01903002030703e581d4180e0b07102c01b00340c2c80111072140119141414090017180c00302e00b505c170a5580d4079541e600d8039a081c41a10101c5c00d1042d05030080910110140e00d070380c0100030716a0b02402000914a4801c00b00800d0440e009103140201e40145c002e100c6a64025a02b9a8042480da240980c503502c1c1c41105540400141c103403824958600700029901c40e40200c2c2003003c40e078001c000c0c0d5041d603070303042c4041d00c9040080348160b600003c00c404000000340254080c5400410b60480920809180310840d00c190401e03400503c401d030300c040d00c1003040107a0406040d0034221100d00940c209031560040d5045a240e6542e5280324a4941c040e400403904c41c124a0001503820804403a025856401c285c0032403100550200d02a41d4080700100d00401c0c0c482c2107072501011140c0340002d12500ea202c0f00310640080c842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 433826699 1250 433825449 433825451
    0x901090b180f04021215030c09010b1801031b09030510020703020a0204090602040e010f0905150607020d170403080d0b06070305030a180b07020645070b120405010c02010b0d031101 79
    0x65034480c1c00b051519445440046c000e101c600744e0360350415217008062041d19120f03a2181006000b01c280010603100d540224920030f4550120800050300500111600a21140c0381d40440c461309a91200d2036008407030254081d141803d00741c10503501a440345440160250f408007070048014106603100c00703e207074003450006007000d848010034900c101080e031086590661124041c40803110501c41d85412407107d9034041d14680f0740d000451818041c2400103845a2030141603c014007800310303082180d0880d1030084550f10358580c0360030310103500041c0f00c0d0148103250400700d0a540c14580700315140c45425032200b500755541d46a03032802400100350401100d0341080140320001ba4a07104c5240651000d4015000718030300041407030034081e41900c114a9401102030144a03018116030811412220b08a00145403101115000e140035a0f56000800c40c401c00160b042d0300805441c81c40740605d02c140000e01680c82c04840c102c0c00d03541907481059026810785d0200001a010343c0c564081b503091000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 433827949 1250 433826699 433826707
    0xc120806030c122b08010f03031d03071a04060230031506070602030a0b040b0907030209152b020703051614060a0b040f0207080706110403170901090b180f0402 70
    0x103682c00c40d192400c84c0700d0038800d03400150700380300b504016198090300300200c81104030340c550744008203804055041211680700f40c042040301a1010b0000c00c000d468054119a928003400c3c000c0c0c545d0382d100c0c2c402d0000502400300e95014000441e40d803001c10061804101801c09010b920004050b803000c0c140f0095000030400d00700d143e8988902a20a44d801040016201e140c00b410031800c0d60a0703d40300c54132552420180303489039030341ea10900350410325074640162110203680c0407801103580041002c049000c007060440884504003a4044c207125201d080c5035440401c074120703c0907802020801800300d1003e124a02550140d02c08484955001e10b21140050f0384034070807207081000c160350710040b0b03c1d1a540c034481a420076000d54004402d4841c01185031015a0701c0c0e10043d4003407414001e01c555110058694205501401da902840d00240c00440c000c1800c814214181d000101d101d0100e03101c88030019100b038010003540e41c0291480c07001800d501c0014104039030301510508280d88150300b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 433829199 1250 433827949 433827973
    0xf13080f030d0b030c030d030c05070b01090b010f0807021c0e04050a0507020705010e06070f02120d02030d0b0a120f0c09151805090a060203040c030f030c120806030c12 74
    0x10300404020220091503803032410340158402d4a070100c40540c069402450a03415640f00000d07002e44042d0607180c00503400d91040c40480d13182c0703e54032000d04071000c4d1800118040d000c96002d044410026225030b02c00c44202482959803041c01c076102005070700480100c0054a1450302e00500b540c03610f00e0100c1c1c107a40d0440000e4101c50044c1c6041c03041d40e50f07510403c0fa44a03010000000580780c00d0030804100c81017140010340b540310303500f40103091b9030142c0d03000b408646503040381b0004202204103594040c8401d0340001c0d503a801c01c1010105c2c482c100390000f03002c2e041200c64031003aa0a0180c41078040c0c91366448110740c200055804491142250400141825882c860840c84000010100c4000391400c4040d0f4400f04100410f0120f02e403415050100c0390714006110708600350321802c0940c0369612400c01c1001c481c1e01d0350001d40400c201e40c0e10041019440785000000612030b0f014860001c020b204200e40b8546c0480e04540c26038800d007101c29642c60405500d040700340b501c60464541061403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 433830449 1250 433829199 433829203
    0x40f0f0204110a020105060f0303040f140d05070816091404030c050c0a080a0b0c0f0301051201060807030305030106170411060702030a0c1707080c0609100c0b040308100e04080f1308 80
    0xb00f18040050359250309000c41403070310b41061065100c00310300030350034a41481e940c80c82d404070320b10401c070813000c01c6507010595444101041e050550040199500c01d96a1504561035130700890b0039001c1040d080001044503001841802d081401d044a420071b169030701e2380d064841e048889020b484611403405500015903039012200090000c071005040b40701c0c0f4030311707080864071405481854041010301003001c4800a40f402d80781110022070b0560040300ca5168210700504540e04500601c2c02035807404800d05400000441c1252a940c0d41d10200c1d00d0005092170b401c0c2401ea030020f042129442d08007802d4030300440030780b9445000a0599a08020f1076564000c0310015a201ca41c041c8481c801d00304400d0801c0c0700100051803d0306c060140c01290070000341c0340344607043c00c25205020460720491054828100c810940d517000e82d09058034205410302510300c403021030320218019407494001c511201480e0f000e0340125440540300c1c2c03c1003100301444111341c21511901c000e4401020000030b040e030302 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 433831699 1250 433830449 433830457
    0xb04180606051003090203062208030408040e0c1801030b010e03030c06070201241229091006030201120209040207080403210c0809150c0f03090315040f0f020411 71
    0x4500000907040d450038007802001843c0c0e5200d20145884c1c81c40080141c0c8011a00306c0d40201c200e03240c992086015043c0006c0380d20b5001018021001c080200300070019064014801d0710300d84030f1140b000d503440007840b199922070104502d440c2141c950440c0b60550180e00302e104c4c0702105043c60b41400c08800c1c04a4655040011112840e0b80801c060146881d020711404c100e841c0c2d951400c443d141c48200380a2841d2400307206000031640d40d2030714071091040141c4000f020103a000c0e1407004040804a282c3d0340a1415219200d0b83e000d024070740e031400303c01c80c07154504030b0340d041e1904d4500064600452000303420200f50319410607000c001c0c0c00c00050014009001442c8503442000442c009420042d42d525600d81000090081722220000840d803004281d9103c80006c9403c4003a810508508200501520741d5070a070b144100300b281c3e503a0780808000f50078111416811503041c44003020815136000c9080e02c0280c07403060bc2c02c001d0f01c0440d060202100340c0e18009040841d442404400d0100e80340c1c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 433832949 1250 433831699 433831703
    0x41406010b090310150504290d020303030c0309031333020c01030510080609031819121103010c020d022b0f090e0408190908030d0209120d09060f050c100b0418 70
    0x2500744100e01c0219405823400118150607204030580013959408255a440081d1000b040780c0c5000c800651001001c00031248a0100209016030040c0c1e03d1074040500c2c2d02e02d030ba50b40560702e0700401c002c41d10110b110312404005441da0051000500340c00041d8000c4c803014240700340411142001207064081040803d008010542c000c5641d112190302140030301c0c1030181458403606400760742d4849403031500100d40958032041041c81c0a00800e1030070b100b2400c1000003c64155003401c0c030240c2c00603004160840001010740940e072402c007842c0b8a486207006058500401030b00e010580c028007500c50400ca130207120181c18850000350f200d011040c12003d04450450303e07102d00041902c04180d1010558442071518240340101d58145842a5103d014142d141c030340707040e0f010a402189030ba801070700100c100711882c00da58804840034802800081c45000341008900c0450710f14012078440c000f29070415011801800390140382c801d48001404076100000c0d44241c80360820b40d180498030421000541c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 433834199 1250 433832949 433832981
    0x90905150c0a0f050705151f230105040e0103142b09050d050c01080c040504050c090907140a0c08190e011b0819090b03041406010b090310150504 64
    0x990b00c0400a110141c50319802041060a00c101c50001d10001070300c001e4200c40e201c0b04515952100c0f1119440031001140303c1c1042d000710780018403851850a0303450f0340301042c010741d802080c1d00001500c1c00c0c820761081a00d80b50241340100081003450211070141d40c14a410b07034510303603480e02048602c00c8800000c2500040f1703102c8403450440d00925142c0040c881510b06a40c04003040c1c4459844401c5e410300281400071210003e60003290400072207014100042c4100040d040000741031645070010140d0a015580e24008100418001e541890100804103a401e150001800d004c4410847c04c2504450509043c8040600314070409202c09a0840b56034462a0b510480c0000400c20380d56025410b006450603040c07880440c0309141102d010719060801008540c60054040703c1321b035035541c441151008040f09010421208815459011078000d044038910b0b6203880d5101045c0c401e00507000e074194010f421100d0009000c0d04000300900405142800302076803074001c203007550586e407202c0100d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 433835449 1250 433834199 433834207
    0x305070506150f09090303151f18080307020a061d09190501060906020c0103091401060b0705010605010e13090204090506090109060e07050d1502041d010e06030610090905150c 77
    0x2d0504000701680d03a00f08444a545070309001c1401034582c800500115081c100300f40c800603480e110400a0b490f403241c104161090b40c00c180c2e034024800c07154403144082507103003031800048012000061307401680d00241412522441c00606903500b0142a0200159a004401240c0e89030785d15207165124a4440e60f181c0b010f544016080811104160000024400c0c144000d01c030169000075815140842800c0004801143d810a46d020845013003418a1a6090040100f0100016809802c0d800d02c650000d000300c1e0703162001507946081d08150541c0102d1148a50712016486070030181b040c90005d400061400c0342500e8450802c20201c440350a1030b91905014010800c6034030800c51020907000207040e0072030414002901104501c10040c2c80807484d06d411842c041402e0b81110003c1400c1d085003c540100c0f118189000142442008250342d080400500d45c0d09011078660b102d41c1610080040c01410005200002e000001c4140c0d2a80701d003050014215120083c15030041d02c2d04039460741c40d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 433836699 1250 433835449 433835491
    0x7030915020a390305070501050a0624050901050711030f06070f09030f080a050c0102190e06032503021c0e0706050a0f0806042d050106051c090305070506 68
    0x2040080020000c03004401009524662000040c04240f40040d000c004002615a050880b8030340200c0c00090005e519203401d0000f0244035278800400c444e038480081c009080b0170100c46120100006d00341000c11401c20a1420940c860300c024880a8031400d00000366880c0500460b10300030300141d6121156107c40e00707000c5025040038140382035002c50700d0301540190550351445012052501c00411001010944401c950301a80545440e10021802191038180c406d0b105001613100c041848003060a07001805264108141124800c1c072841c1d580c500004808080203882241903140d420401d6401d020100884080c180110f0040b4007910000c61107120003140c4134141005944000288403080210b901c005030070540150180d02c050070300900b1a6203603400f103006401140001c145260315524901e20710b04074130b8003084907990034103002c21060b82c9076202039540703204203054409480c1103030350f040c001004036400038000b4901c689030245c184001561490b140c0f030701c25170f0b002c15406129200000c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 433837949 1250 433836699 433836707
    0x2d06180604151b0b010909140f210f12130b090607080c0c0c0d020609041e0c020f061f03080703081504050c090603040c0906030507240518030c060c0d12060608060907030915020a 78
    0x102b0750000d0501d5850310002541c85801c2d0b01c0380c448107148202d50000092941c0880240c08603465410910407819898110303d0191074038021144807000c614014003203122040e0090980d4a00017541c5c008200080c0c0340820400740e00310402e0101da2000702007021200c0c60311540641041c004819a00118520003d0080e174280ca2840e030580f41154003040c9800c81031341000038110b0300007500000d14454480824121004d0042d10f0300082c2134200c001070003108140e84010118451006003400070842d80f1103100704416900103032120007900e070b002e01c4815186c0c0340c14802140c01500c20420200c207103682c0c482c070b101590000e034010b58640c0c02c806010090030304005500900d85006408003000c0c0004c40801401c0c0e4001c800c00303003066a14222410225880420403032050910003089503480b070490a50031540d5110500201c4001280b80c215203a60740c9803802040141ca125488501d000c0e9508400e0280c4840010418401c00d51143d900c030703001c0303165009480c03100414218096036810010401138 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 433839199 1250 433837949 433837993
    0x35070204060914040803100b0301031103010e0106050307090f02040e090a0506010b090a0905090a02090a0c17130b06031009050604022d06180604151b0b010909140f 72
    0x7440903410488000440791210301d403164490380c1700740800e490b5141c5d8603c5100381e000c00c1d04100d0038110000004018400ca18a52250b080c070201c0c000e0000300c1c0300241c15802c0e18202c0c460150140c0c000401130006180940150071114408540182419601d41341c03140302080a444145142c0c100710403403030511a00b402140d01408055240e540780400131030101e020103c841c4a40112543e944020805400c3c080c0f10520f00c0796001031014030141070140c840720080007030f100c12801003a5140c051418802d40c001c0c50034400c41059281c1c01e00b2403030644829a413000001c0100741e040c0a642d002c0007a015084c8a408804d42c046d000608542c9094030510a090007440e20141440000d500c125081030003042085640c0d80f4190b803040d8440c040054844002d03056220b20692001c008a000b040d5969042d0013102824641c1c0c0d1148140076010a804051204461014050800e108014030403103800f6002803080174840e08a03070108411450500d418103044412140113600410703a020144c82d0610740038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 433840449 1250 433839199 433839209
    0xb060315010b0307120b060a0305090714010c02040f0e030c0a030306060c080915090a1701111603110304230f0102010e1b0604170d1d0901033507020406 67
    0xc201541801005005400700401c0501001540d80050414002c0307a00308950140d4050b0070a903c5801600c005406030408890504941c803814000241c40b903543c41d5503e00c24041a11141d130b15000720b0b02484081c241c0340070f04042207601d5140c2110684c0e01000246200030300300c4060480640d0500d00181a14a960311007010400341102480103c0c0b07840d8100d0390103980440300d044410208903000e411a00480803070b10342c480010f480c001042c031a03542000c40c080010701d00820001c00f030010060094000d9000c1c4107480c0395064550340c002030107040f0303046604460104403828141d07903c00000c480032901c2484000329050650f219600d080220446a40301c8090000384049004920019903a04000c2c0d8018010361140203c400d55481c0e0b641141c01401c1c0c0307603078000c203c5072050250704da880680001c03030000074a0501c1142030400400c0d060f000518002000d0301d1081e465030316416001a45131005c070342261a17400401c40c0c3c9440743d1400c51000b01426145a4844a00380100001c94201e9446 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 433841699 1250 433840449 433840483
    0x807050f0c0603010902030415020a1d03010603080f0f0712031a0109060503150d020402040306060302030d0302040503071403150108010b01120e06010605031e040309031e050601061b0506040b0603 86
    0x250201e9549070303400c0d01d05540b46020016165030b29030508240041c001000724842c24400107090100d1503111040b034807880f070080c8000f0904100d17941071508945591101800c0d81e078050051500c0300410100402c15829512100c038101181c0d40c80e03050000d0041000400840d0781e03034001041803840c84214024103403090a1103d0028600304000e085440000e00c030b01ca0418890101d00030b90f40d1410319191807e600074000315140d0b501e07840c054008003041d0209138840c0c42064180d1040c2c91003402200c0558a014010702000c0f07181c00040307880e1040803c1c04076450f010320300380d0303060120800c0c03050360017000104000b2941d48440c500140000210004a429460800a440002c0e410004156045684510b0059541d03598140d0540001c180c010b00444010107640620007815441030f0444142ca0003641c000c1c00300f00003810811240105194020000c9e00302200400801e405002880c1c4035982c074848958200410f55903150929004403000c460780180e0000340000390074200241d1079000c0d44888 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 433842949 1250 433841699 433841713
    0xc1406090d0f031103040f0c08070f0e07051204061514010c11010912060501060914030a17090301020715050702190b0604020d0c1d0f1c0f080301030807050f 69
    0x1200c25160100110070405100d03042d400102036a02ca0b82c010030349101050390b895102d0400307240140c81501054410780d40b017040c0c510041441500032400800311802a1183c03840d4501e414000540c220000b003500c41400018800b4410113524160b90038840c51140d000014030b0906400400118407694201c2220180b98410a94803640c201d8944116681c206001001c03281d640c82c0120780300002500b02e003040c03070b400300c040300208586600264103850054489001d45030b1501c440c01c0107040701b1070a4642c5076204114090101d120119003200e00d0001018292400001901003802e9a2120300212240320030300d10f020240c4141403103140c0d006606071019014150464102c505401e401601c0500910b410001007841943e0340e43c115a01d1079256001881400e0254201a103405111400302800221844000742030386040285e10002c0d5100812100610582c000e0222144440100840300b013042c00d01e0001c003181410340690300070351250f5461607441c4258505a410800c104d0240b00641e03010790 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 433844199 1250 433842949 433842961
    0x20406050921120c1902060f0a120615020c061617132301210911091003150b01020c010509040f050c1306020f0a03050a09090c0c1406 59
    0x1600301e4042040484007000c0c0814003a94400c581508082d8a22051040c1450b2001c00b4030b601010f0224882c0301010344e00e5026100420784040030030040c000303500403410064802da0b84103000241c0301d0313201c040c6001681011108029401c50f101d41d00f0409400e100c4400b0b0101c02c81d4104010580100c0c241e0350035042280107406085180325045d0001c0032503140d01c030300002014079441500c0360640600111088035588205c2060103101000b09004d032000c003000c8205581d402a8400c4d07001031441d0041c5e024180d80c40c0c1d1410001d010003141160100d0f01401c030100780ba621805030318020714510840392040e614520340349800042817440e0b510014180042c040701c42ea00410344420b40780b02030803e107a803066101c00141c005c1810901d070f5041a807520303041c0040c400d0703000c018192118070f5240003a0840e4842c10160f07640c10034407066a50320b038404403025001074070a401500f580012400e2951005894800440558000880b150009040100d404080c4004508441030a4481202911306800e242c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 433845449 1250 433844199 433844207
    0x80403031e1d0a1509020d06110a09080102070308180f120d0b030a03020705100507050604030206270c0609030a1e0302190807020909030c0a050604020a05040606122307170a020406 79
    0x1400c05038001940d105c840d030302592640400031414903031119080041640c0d83c88404a603800115900001980d0704001150b10300b4144215034240741c0507159051699100140079915036070b41018401030307001d40c422642070030104010a484407100f04c12200d440f002c10301048002c80c0d00c8600f090703101c0c1d03010141c0c840109801140242c1a1141683e0401ca054100001a20240700f03c490041c1a8499002000b0505a011810b1401440440300320aa150078500000354a1840303560103405942140003038131264640580140402d482c09030a544408609860b0012a0280c0e0166941a040300010708010168144201410041352001c10040c07200e41d030301d440080307010700a4000c0c0508841390125114000c02c0060310107410140e0f08807442298286403503920b403802034034124042c0e030083c01c0c04211440c19024a00130740d0603550780c240d040c5907841c12150280c00c41a40c0700d802807031220300d60100e0340c0f07010842c10302c131301c2d6261114003004c40f10120442c61000300802001c1000c1c41808240005944 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 433846699 1250 433845449 433845473
    0x30507111224090304050a0902090105130602011a1e0d2123070c140301090212070e06040b0303190507020a061e02010b090105040e15010f0305120306060a080403031e1d0a 75
    0x2d8018014ac8800046006841a00c0b54014603d1262034040000400300e50540042d09403a00c0e10f09040d5840307420b141404208002115000c07038003042554800810b0601c111685070840c02000780d203046100086420713107441c240701c81c6040051103440b40307528244040030107020000d808030301452902c9030949450b51034505a0081401100c010026034a4541d42500300d000416001043e401030303071208043da10340e1307078520703200301140d8064500c0040c04034507040c4a071912500001c0c003c0d6207821494103855110a80d804401030910806100381c42c0903840381c0000c80d000e0a9580c80e94243e6400381017408000946e1480901d0440e0b04141c050a066110f0340384607811240300783c0307001c40c40a503640d4001d802e119507100d180e00305d00c40d140b0001a01e00c007400041e104880c01803090703410249000381d41e03e6941c03000700c171a01d800170707410404903034411f104401c0c155001c0e00914002400158508030380e1002201d0703041e0100f010303440b01380001c0c3c0c038000a1540200b13030103243c008018503070a5a5600c0340d0012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 433847949 1250 433846699 433846709
    0xa09060c0c1518060e040c0c0b060907090e0a200c15060a09050a020d1116080904020904020705010911040902090a0903090806070c0b0f0103030507111224090304050a 73
    0x40e02603900c4426001d43c0f040300090802d030800344185500c07000300034000790315284118816402d2a9080b202c8502a8209400103078004c4804c200c5a5261030074491403240180c41c6808014543c10000380f520840c55106009000c0140c002c2040b860310100c402c240c0c88070945080c40c10004101509407040c0005d030358225804140d007038500582d6660001401d4503070301d0780b00d0500039040c0300070001000c0282d40284803400414108111090a03111941103c1c010401800c010320200b1b2211004148a0005000c0d40c0d00e0060002d072820780c01002107021303a00150380498a5030f450300220310401c410507014088500c005d407010400a240d0360005540b040001d004507410a585058410505109034041805409054122802c50812020007450701c0510030054641120700400301d03403816003109065040781c4d05540c580b82021803944850f0a402e0390303134002c5a03000400115066510300c0c140140301c1750110811170780132400189065600c400c400100315075000d800c100070502c0203507100e4102d43c00781c607 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 433849199 1250 433847949 433847969
    0xf08130e13150b19080d450602060f06030102030c040608060301090f03080702060106180504020a090305010f0b12010e0303070c061e020c011b09060302090a17030a09060c0c 76
    0x1d0300c9016002c01041c061180342d40101110003e0000c3c01102070602040303800b800102d0300d020550040407204111150f07264030300c80311600140c44040c0c1d410000c6907290700784408008020307038a0301c00001c81420300b5480100540c200c08100800d0f64151281c0c2a07000e141600298650b1074441142c2c0b0991042c3d008010500c02528040390f500d4409512241200b9403240754180900b4260401505c2d042003111110300521900c000410a03901c83e012031070010305845540c03049207040c0f40400010350000182682000f2f45404d0020209400f40689828050340100000f02d0408900a12800982038a45100d281e81041c100f00c01d601c000100301d030350188a52404401e40301307a616102c2d0103015030031440d00180c851541c04040e0300f10303030b80e005040d5140004001c01449180040514850b1282c40c918000f00707039007100c1040f1050090b0010092880000d1441c10041e840301003240002048a040300c0b0315620100304102c03d180c0004040c4060550390408850b1542e8a61303d0b8685d11a03a130040715018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 433850449 1250 433849199 433849223
    0x30912030908040803030a02122202010c080d0f0e0c03030903030d05040f0b070215150a0501050f04050603040c09060602160312200a03020106060e03030d05070c0f08130e13 76
    0xc0b10121040d540904200c4080c4c0b99207080c59040340b000703900102424003040344000085007901a9003550100041d0302181c821030300b46000c0c3c00560b810b03040f85405580c81802001000740400d0903100360042c01030312a20002d03080f00201641c07407802d980d005ea000d0081c0d00800030301106980000c1903c2c0c9080001001003610b98552400b40f10389800d0907001031003024120148000302e40c020070740b04601401a40495446d9990b4210111a55800f0800c0c03904003010f10001d001d0703940702c0e41c024104601c11006103480c4c2a0b454021440a034012681651400740da04800e00c5900d01c140180e10040032180300418041c1140390184c00d5041071484020320100d041041c05c240b00340224009403000b81c9441d0401042e0010003652a2220804903049006502c3d0420208603e07010300c818809200d00940190304254030b594a590003410040d01c181d040c440004400c20015000d217400f984214803c2c1503d0f519901c02c0d001c2c146901d4102c0e0441c1183d07501c1d1908000c2c86800d00380059014a8203c002c01d802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 433851699 1250 433850449 433850453
    0x2043306020c13020f0f0a081303050d0b01051306080405014706040e090d030509030f03061926030307120f0b060301090905100b010f0c031214090d0309120309 70
    0x80c4a0400100c00034900031910008104048014104410442d08c50301d9441da10f070030050300002c00717031800100410810301400007242e00d960b02c40c5240e544181440351a00090714044914920760360302c0b590000b03c4c00b200704000c1007404c3c0295a84413034140b03c11074030705041d60706150038108610111111144805032905002101074481c0d0354010016200a503180c1d00c80075070329030500701110f02c034646100301c89160300c4241c480d1240ca482903000002850038008002580e03a980c1d400070700095070142142032090560340304c80030a540204900b054040115007194811306403c4075250301d02c070f620b0304107004000113241c01000c981c0d1241d100000000e60720160070146c20003000001c40b0103800c9100400040f0300300032a540a00507150051080340c001c21440102902603072000d040e960b0000d440c2d0210080030358002c01700754035014803900300301003221491100a02116043c1100c1446880c03800240403000c03005100754401d82c1020b00c0c00744282c0c8400c0c1c90710040c201188000c402016507400720301d41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 433852949 1250 433851699 433851701
    0x32d010e0a0312020d050f010302010e0901030c140f0402030a05070207080606010210020c0f06070f020f06060a0e091c090501140a020d05090a0f080703060b22050a0902043306020c13 80
    0x11940e010400c10006d505100c442d1451034002400228049040031000040b24034040ea8034904036a401032012010b281000d884d80410486615403980014200d1072202c4559140d0000e10f2143e4150301d00020980741034840245003e0752613120308443d800602c00c2c44410390780030034044581000c000e40035a90721242c8200c00d01d0081100f42c9008a80101001e000d14141d00c00603600749100e05a0880d070f0381190145409864003400d6075016800350381d0610803c401c0c5400064103500403154400d0321840c0c030a00c403201003011110785d0307494000303608468148500c1d07820421014154034010161420103250050182d500c600700d40301c07181400f8020810b6035650b55001101d002419002062614960740c401c81e040d51741e000d0780400c0ba6110304050003034065040940d1a00050400c07884100c5030408a64224401405c001c0c3c040c0845584440d2140702584403400345500c06106200580d200390441e0344521301c0b002c100c40c10b080045441c440c040000ca540000c043c112844c044511301d608400440180d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 433854199 1250 433852949 433852957
    0x309030919170705100504080303060d111305040b0f0402010c14212113060b0d2001030f1814031e120108030a1715032d010e0a031202 59
    0x1840485100b00004410301207911021100281c0354000281410307541079a15005a00400c0040c1d0b00520004049207000d1581d400184d0090221030314450340500456050310303a2030305e81e0b04201d0b12203040c0004c00c0003850810740e10400c410040c11140c142540020140e41d0385040181180c8240455625291010301001041070080d0190f16007094914980120301d421454000c0181d08201000584060f510341c081e920404012080c000040e01c00c0d516400104010710140e03410406035000a0009048c041c1c1ca5a4410b03402c045018041100b000010b041d500c10368401038206040010b240700b000c248880145043d5880014806060b000340c2149255004000740000a01034051045540305051401856150307a1031100e00c807283c0e280d104030384da40d1081d440714400042d00d9a4030b100000065120254110710031040c8043c02d06041c2002910341020000084440c0326910451840854050300c28400031060200070f105480000003216150203c908024080c000c5115400140c07004c5a4121 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 433855449 1250 433854199 433854209
    0xb09070e0a0f1805070312090b030a0e0615061903090605180601060e030d1407050f03042d0506070f060603060c090602061902131205010207020f060309030919 70
    0x14203151601411032006442c00c2010310144a280010480b55201a540c0700c4020a40103002400c41c0b61444e559000c589154001180401c04280d20110325400035000640c0144180c280100d503190442e820300d4181740300a440c0c845130740011764081801ba1100360584040e10b40704030701e9001c5076802c24029400340080318002400c891070308040000100c03800102e10710000307001c000c688240c0c0c5c0b242c000365441080c40800741c3d03040d4850049441400d2060194480031488042c4080c03d003c19507440300d207000c40744c4641e0002c5410126060020502804a01e504900403941c1035101c2144000841c200380000d0048500589001032008244403003c242b200c0b900368402e1003000755a94a040460090a0742c109603c00200c00300b0000030854400505140a0346460f01e00d01511010010850300a520002034401b88000000000610502501c04400001e00860001d80da03003400d0300c1000081000b41c0003552062805109106a4400002c00d0752043c44054801000802d00c00c1e031400750329100340d402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 433856699 1250 433855449 433855469
    0x120c03060b1c0501080a03050315040e0d031a06180402091503040c05040c0f02060f04021f0203090f100504090f09240e01061d180613050d0503010e01030b0907 70
    0x140703a00c0312160498a2120442d260020010b40e621510055218059a040580003610038008250300d20f080307603494013116000070000114001100d0740c0c5030424429501200c0404e035120701084e0321f83c1d101c52b10010010412182d25240915805003003c000308610300c0d243c00390354085200c2005890b000d900c186030301d415244e13660316031501e4a003500d940840c9020b003c0c001c90502018110250152440c3d481000040d005442c055840b0401c2101d2600001c0099030b001c3c48200d901c47c56002001400c404818050340a1690b540000007070062349084520503070b0155000c3d110180010794001d0640d03041d28200310340401c800c400c140c0420003030208014003600451070005440308404031000721003902001c11105101c070b86102c04080307080300c52a00c950010384103403c00f00341d41e04500d020401d60000302d081c00c804c0b5944800d00964904181103075900102402d420814040c0f2004002492621841e4234100d4550b6040001000d07003010188401060b40005402180c0c9440c01813051a0140c140b01c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 433857949 1250 433856699 433856707
    0xb19060305160501090b0405100905060f09040501080307210302071b1805060f0105070f0803270601030c0512100e060114060c03040b2107020c0108070807120c03060b 73
    0x10525290344014000d06004240b41400242950080845000f111040010703203080c80c1c0340c0740a0100141000031240104140c00d0b01c040780c141d0380d08025154150410007000c0d00d40f0036403014030044074010307003114126601c10b200344000141140c030309001000c41050b288080c49a425010340c040e004003080140900402903221054504401d81201191200941d45911203651003200e01103c030b0946d01f8503040001d42811460550041000703012162141c40b15580707860a03920b81081c10740055a0115100f0141301c014151549001c096404c1079400802078030b9254916596a20001901d10949015900c46101055081c0c424000f6100e00c8844000070f104005541000c1500d51509009004442c1e034918844801400d05001ba118104c0e06440103500d0a810300e070410710701e608020403117124001142e108030f00c5440c01c2c10405011341d24a400800312641540c0014042c040020422030030003020300200a08950301000d1420322200d500c200103105030b500721085015082c2a048140c2c9050001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 433859199 1250 433857949 433857953
    0x70e030718050f0a0209100e0d08040b04030605180307110a0b180306070201060819060615020c180708060f12030406210b012a0b150901090b0d0b190603 67
    0x40c020b18410841080980c0050340d6801d4298100d010f403400d5650415603001107070031028040c601e8148080340080c14030300e032550342d641e815800307a00036003044101d8400403900700b0412406000d0190820b90461520703162000300030300d041d40d03030103100b001a110085001400c845030b1034804100000d0901056580c1c0d64480003030601ca401a500c4096900a2240c20006200c892041c414041030354a01c0000d017068042d000c020b1807000220b0303d41950965520100003481d0540002c45240d40c807648c0c1c018080315030000701040000d901c50340701ca80007000c41c50100b05842d03030321002155000c08100d070002d5000301d00102180d5036403100c8a030008644800507001c00c01c5070b00000b40c2586d10380720316402200340d1a04941c40301a03804408800c0c0c0410f2001030280149100c44c1c8400480e40c420a005442c105240c0c0c4820310408002e58558010300c40c684480501400d20200c8035004d410340c020103000345800140404c50700d0ae601c44000e425203074280c02080420b51398100700403845024a00c1840101d40741c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 433860449 1250 433859199 433859201
    0x324010504170d09150215090c120a0308060418080a03091b05030609030424050d0207150b0901030b07050d0f14060102070f1802070f05010906020408100501030506070e030718 77
    0x40d0b82402d01181600000017502030b41220042c4520800b60302902440c4120b140d0f402c5242800b0b400d060311405510203141040d26040c212103402c80c07156004021225007424050044040605500d00590619140c01d170603a05031841c0d0018503500c100038540c1c1d0000900200c00405c902000140040d12012a0440030f00c044001c2d40c0c19100110140c0d4050307161008000c1d03482c8614440c5419201c480708607800058614a8901c038180703250b0030324601c1c1214001141d401c0380e2020400f2500e01694103603003240305400d4814651540f1094403c020301d54119100c0100d5800010002010004005a0101d5461094001c4802e1041c4408144a4600c82800c3d1402d0b088048a12500520442e2030020704100880700c05030480b2000c5035061007107154040e402c0040c1d4052182074a1042c08852a040001c0e001d1240da800c40380503510060319242866141070138062010b050000c154241001071000c42c8002c5180d5400074640d081404c920100c020120742401ca465010401808184031003181003419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 433861699 1250 433860449 433860463
    0x41202012f06060418020904020d031205090d09090e1f060306091a240f120613061505012703050f1f09030e04091106070c0911032401050417 62
    0x401c0301c090060f541760580d00c103030310221400069445418000858098180088031076165070085c40d103c0c00c01c2024517441c000351441940e030040700f84d10110200c0c400c6a44905a034000d840c4400062000003490380c000740e519141060842c0d454069051000342d40041076100360000c60780b150080c80380780d004c0d040c281300c0000e0b0008114001c180d8400007940141051403000b80e002c01c5c01c80001c1c03e9040e602c00344a46036428103a996042928001c504002c0c04007000082d12071500c8034000d00000788189888415600803000926603481d0400b014072060780c01100b9500d1207150741c03a000c58000103415191002254039800a05140500c4010500d01103011409100f01030210200340100f40d9103c168504940b800c0070042c0005000c501804580d2903da0400811903016002c504e480c40c05010005801c0e43c00080708032081e07100d1481c03c01906502d4001d82d2914241800d855056152082100401461000049100003d40c00c4408000d038002c2d0140d50140c20524506012000344800040c0d50b058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 433862949 1250 433861699 433861711
    0x20a0204050a020415051c14072705120102040e040302030a091505030708190507051314091315050c040503060f0c190c0f26041202012f06 61
    0x205060001c0c0e0840064000c580171610060f000418000c031002c011180c80d0810704442e40a40c140c1c40112a20025038096140e0103030744030b8101c15a43c14480405080700007900001056580a510400003c6541c0701d078010840340c081d10807000c5556800c4500d03009209a801101c0340018100900c4181741d800005890000d409844445025480d808003800014048500c1030014904000290880b441826041e4100d41107140010811104050101c21f68008840d190002800882c40541d210451032881d03005007080c42c071115040080d2001b18400c42c0d0b0080c5141c01840d074180c1917108110341309504a00700041903c1c100602d003811020000c9941c094481e5034030034070980002c540030b14000040305000d007854a210516007082a1010404002c01c6030044c4284900207000d8030109503103407002d13070006100e51050241c01d010441407940000456120103200740042c08140250044d0900401c0c200303809080c02203004642c60050340c0b130640200020030356260300010003c0c2080001900b140921 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 433864199 1250 433862949 433862951
    0x80304050d090b040806040609140601061211130b13150e0a05010f120e030903011a01080709060c0b190c0306080708031309020738010e060904150b030a03020a0204 72
    0x250780c459801d83c05004d10702400d407141c0c02440102d80011a43e0b44140e280500ca402d85842ca05401701c092818503000340c0c07041000c291703503401c0404e07185894030602000f02410041503080c0100b10106544050007030040c14070441c00007a020180c100035481741c01c001c1100f10121995081c119400800441119518601501c0140800b26007903010707070040e0304400400d40d120054496850921f03005000311414000f41400104000e03201030700c0a008100c0c0b5032002c01141e410002c1118001828020000c00842c02c02080305000d01010b80c1c005410343d4825049801003140b038a80200081c07820002c810401c02662070002c00d00850303900741d0441c008884040e0182c0e010181c1e1420119260b11960f6401141200313515014002b02c40c5540c082c000080c000c0c0e5038002111195100e200d100003a601090000e90b07008a030060001c1c1e440310940d805002111241900d500b410008180c0b000d40161004088a124250800c0101e4250740402417480004007140c02500107410044e44880f03500b20305034000c2d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 433865449 1250 433864199 433864217
    0x2030c220e151f120305120402010e0d0f02090901052a120103050a05070e100b1602100917030702010804020d02040905031c060e070f0c06020d05010e1501021506120a080304050d 78
    0x2083c0113a086001c5501a00c03110b00c0d08206102c0c6014034000280100c1c140480c00e2400c0165480b020325207000140b048022018440c228010007502c130350014030312503160b81004204004200121000d41e2510700803807031034480c680f00b504000c00302c0c018480306450507035128000000b4054000354a044842c040c0064401c115141d0f17811140980c011100c0700c8200358050410844403020798020546402c1c103109040c44071850f41e0002d035407107074102c0144c400100c001c00309216458074000100f0340018100b00461030b0416650010305031b4000100088c1c400c0c00044003d5080d521070350815002c8a074004107a9503180290003100c241c01803507030000b810641c0781040202d4040c000341d40007401034500781c507400e800c1001d50000322191511280f084410f15002d000c0c0c4c0400059a01520f07020304242400001c00d4940a03d6000310360000d8003400c1c0c11544a14581c00c2c0001203100c0084c0c01120a48581e911494013101d0360740380c83c1420710020b145a030b00000300700070b0140108145050508690b503103011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 433866699 1250 433865449 433865459
    0x120c030b04060b0612040b0a3b0d020f0f0706090302010c020d21020c010c0503040e091207030504030b06030316110d050a05012f0a1b120c02030c220e151f 68
    0x102c1d4074039209454a504220f031030300c029050b0300c101c2da84400700c420010300b00d0a40702710340c5906041031020315401680c400b00ca210040d000900071180345420901c01088800d18000f00200040c046100c0681807107003d2003c0d40654451000d00200280c000e102140d061401402036002d002c0c04866001c014050b150404501d503100d12007815260341c201004504107420301c03403041c0c1100409450345215228694080384080d031544080c3c80300d01e000342c4580e5141c82c07440c20000d400140c0109514807940080142903607014845070b8413404190001c1d1010214900b800c0818102117200c01c0c003900b01d103d5000801c040110540003084191404040d000030f101d00500f45500c060403503444a030346640c0500014081610490b0416001240300c00c00c031010507510b4490280e81208942404000b03000d04001c5000e50808106a040b0340d0415110880a02e0400031904950307100703011410942d90f129450015a45410440d60340080786100303141029003402040001c102402c070b003418005003030500340010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 433867949 1250 433866699 433866701
    0xf1204061503030c0b0702010204032907081611102d05010518070e0d0f0302070806070c0602090402210a1a010c030819020d021201120c030b04060b0612040b0a 70
    0xc0b241d0585031580140e07415601c00002c0300000301ba034400c40d0340c2480004003040d1841c8201071600440e0111144d640c444003888020b408000b09000c05001d201401d000e050707610700005c00c202c82520700d070004c0d403202000e0110b0304100703000e445160751a041c03d050300142940030003827810f000180d080c00c4402d85d00340e5040d0807ea41017446081d50240208405140e01040181c9080c2e211449142c00f1134074288040c0003810040d10301a0035504041c5c0e00018404068040000384040c041c2c3c1c1c00202240e00d030134000248a000d00d000d00421403078001c0394540c15910381c0c0c0c05880107910004841d441480d00c10044441d103040458104280d60309022502c0110000319107140140c4070180d44101c641407503918251040007000c0c060751b000540344140882818094806002c12016882d809aa07550201a01c0c414000c410b81203190b1000b40d41105800060a010851088a5000d51080c0380c07941c40b030038400000d014200f612508450000b51340511070720562096071050380325020011980c1c4400384844 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 433869199 1250 433867949 433867991
    0x11403010803130f080606060309011503060b21031902010605030706020d0f08010e060915100f0e0105040506030f221b0e09060a05220b041a040503090f060f120406 72
    0x170006400400115601e820210011030340130840000101c0e44620048050901c46403a50099420700c1c0e0714050b50406d45401d10708070f80802400c0f0300a100f20404000740c00d489104103c41c5107402c5503c070001c010610700030b400400c020070005003511003081d035a90001e9200c0c40c610451500140107980c2d6012201d003d902141c0c161110040292900e60b0380c0d00c20b201c0c6407035001e8454800c0b03602c800c003011507a581d880765108521303806545e203646650000d48054907070308550030400c0c10b001c0d040c0f0041c007642c0c0392038055a6005074441c800443d1030f04c40f1001841481520703805d0002c0e80024921a2040c040d1602884000d0703c1140d0410310440c4d6210035100d1004010b64819100350003503808595050081d0b0042034200e1130402c00396016640f0350012031818104054103c0340e401614082005002c60100140451032850b00141c1c0d981c074050369056142c2c8101e42c4c00911034011020340c984240c80d62816951000441c00c005a5240c83c81c1e00c440e85070a10171101121800d00b4410011482a1017071444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 433870449 1250 433869199 433869209
    0x18040209160c021c080307030b0a0803040b030a05130804080304061808031222060b100c030804030305090a080c010f051f0302040209150f030403020c0301141302011403010803130f 79
    0x40c400d80c0c2d950030442d10341c01c1d8a4424185050404034400403400407001140141c1c0182ca0008814102000f4011400348580c0410010341044c041084541c5e813a10440354428440400003540e6911916507401d036002000006d08000004034010990400000041c81610640c0c3c46400c0e10900006500b42d502d200c9001f8290150818000c805004144065803900103030700c58007640f041e4040f419000088000c140c0c0c151404d03902ea800c0c4111909105c2040003e070040c500d405242c060b45a14043e140301c0c800303400101016511000174520314014005070f1010342d0b11145a40c0e65441e1050080d010300080700562549a140001007501c41c11201e907091910060000e0203000b05242d502040003c0d006403d00c1e94205025040b001c8481ea03507040203104e801304140d80951641450b0800074a08840b103080c15001e41e00d803120030541c0341c0000300e2503a4410010b40310009601054401210000807856a22019440102c0041120354020020b41083d40b4000c60b41d01e81540d41c1c00d03084034800128851 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 433871699 1250 433870449 433870457
    0xd020f2b0e070323010e0d090306060905010f03121b080c060f090d030c090f0b0717090604030605040809090403092d050418080d020a0306080307022107051804020916 73
    0xc060084d082042c0741c501028004800001c000e0b0a1460310740c280000c1400040014007407a05c24400c0103281d10404018000350384082080758186815038400041500010b0300500c40d0f140010b1600c1d00c949529154a030311002541c083d10450f00d03026085030000c40d4488682c1c0140c000040741401b8510701288180c0e156030003020312101841040d8010311696100704104031005001003a240c12041020b4020002882076a070340310020b040c01d0510100c491504503556000f0001614a550340d142aa0700f40e0b074010900003660f4445142040b458458644001c0d0082e624900b004103042d0022084012550040e4000101021030650480d90950302d403641c20b04e92194071010b001504050b400003510001154400c022981907032240c2481703030001c80748107000070f030000f42c80b9400f9a49070040300003d000302d02c0114103090490b03001503c010290030080104801e5402c1c082104202000030500918010381807112015990b4541d81040c4e0303046909a000303070300b400007003001c003940c0c5840c002a2909a5036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 433872949 1250 433871699 433871723
    0xd0302031801090228051c05060f01080709020a0504170601080106080a0804170a0c08010f0605121506130e010207060c0e03060c03041718040606030c050d020f2b0e0703 74
    0x250030040c20700103408603030121740c0700c4012500d5103440f0000a211003c0e410403184003030301841c042d80b80c58401840d0380300c0440014010400007000140c0b42e401e13030b9540880940c031030944070340441f940d00641c2e1280301401e900c507803142c0c0c000f00c0c045040d5060300c40e000300070700c80301d900c2d403501c02c0e40c4014041c4010440a410030080015100c0c0810418043e41e0800c00e0781c0043c400740d203030100d181c3c1e000c0c1c000740207a175940c0c9415143c00480b44215401014151501c075424500f0041c45902c03084031461201881c0c080700005543c5664940c2e1308e01801200520030411184102d00c414000d4000040071a4079030305c1d08070945d0003e405a455448500c8000b002000705a858883c40d001f584c00180084807a8809160b51314014080700d070241c15054541000e18200b1200d503400c0200781d640c02d601600034107140020204815500c44110390190003030030781c09aa200040c0030705800034072549695200c803c104a105040703c00c5680320007801584101010702c98584522055615249240f100a01c0c0300300c030030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 433874199 1250 433872949 433872979
    0x60106080613110405061908010608040b0411030a02060c030706060b18060c0319080f07081006110a05060a060513050c03060d0503070b25050f03061c050d03020318010902 75
    0xe0403030f80d00c0d8420340090301e04080d520004039070f00b43c00403014420303000703110071040394a160703c12011401014903140441c41e0b0309040e21000550000500060b101407a00d8240b8030042e10b040041d00a0310b94094440b80c1c0d51400d100c1c0c1d0a850760804141100d22a082c00c20004942504c00c0c16a0300070024400c1014291a81c4400c0089580c8a10040d031044d0105000f00c0b948001e0400c03003412003104e5074942c0340140c03a040a803045a000d005100b48240502042031000a038000355120302628458100344401560381c021081c54840070250040c0725110702000c00042c489160402411200c05a0390185010098083e100c190750040350a80300341003080c4006034030f500d0320400046407a8007400039a468540305445150f07000b4803c482001c00400545860258000120b1001c0c0c4118050b103021401c2c460301c4085030302c25201c094034491082031b115a01101c246449a0501c8516a000d003c032612840020406000780d0000c0b5420707a00b42032110369038490741c4010301a01003525030041001500b42404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 433875449 1250 433874199 433874201
    0x8010506220f030f060e0114010501030b01050d020f0a080c0a120902060c011803020d0207081b03070b04080a03033606060807080c030d0201090b0a1a06160302060106080613 76
    0x5004401d150000e6035000a1200c65220410700910301400c61405103001c141015401c0d90b280a00c180e1150703160001201c02c0050015102e415100300746130209003d68024012105409940d0424940a00c006945550941e640c0014030f210310b500d0300c540c8155580c1103045401405082e0840b0041003d00030f003c11860038540c8810105880140141d0030302c900394403080d00b16a1800048115403024042150034142c042015000b02c1c2c1182c401400c11500301140c41c0d45400c8401c043d0048902d0009a010240d80c0a06c003050282104101c0903888665801d2095965102c0b01000c1d00441e143c1400c05070701d40800100c2d80e049020800b01c103050210100048081000c09010940f61030344e840070081000c400922155004210f245d00400064060204040c2004480f444100a683c034001911000412062500d039210101080004082c040910110f01e02000c00201aa000d400001c0501c844000c10b41c0d6801d80034040d0b42220001d80e00c9134826105520142e81141d80032a030900302001400b2b40d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 433876699 1250 433875449 433875487
    0x3030703050a050403060603050604200a0512010209060a021f0615050304030e040e070513091703180601060503041209080c060a1806050c2a0103020a0e2e08010506 72
    0x40b601e0030718a80707940c984581c021142160812150782d00004280810b01805121030101c4003241c0890403a00340300b000004241880030b01c40c0721300402500c249525032000a5040c2c03035003540041c1c00180c0e070300c000000003910303100c1801904840c895a06c003648065000d034440c2405654010200c0e2401d1542e40d81b003034071075800003803044041004010813111180c50700d010f8011001d0104004020160034481045556202c00d8601003169140150600211700c1c0242d1501010481c03000d05075403030300c40e91a2180800c14098027098284a907500010700c80368403000031403145004050700311030030520940403211303a072192207860410340c80804503c12074980000100170100260602201c80c25a01150052a009640c040000f0910110300315000034002c0c0040200180101c8220510a02151081080500c0003a216040590224a403d499405000e461080d42c20060040100c40b00d0fa070648281940112007140180030100400321540b400b03003110343e0603190005d1110341003154150202e120120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 433877949 1250 433876699 433876717
    0x60c0503180f1513080c030706141b0304050f011b1202011401080304170d050a0509040f020d052505031f05090709090b010503070c14010f02180312090303070305 71
    0x70300e0b6441032095544600380040e8088121500a0303c07021020300340301c9030200641c403604072a0481c900c8000c842e1342c041004000e89445042807071845821000020803401030700c2e0301c83c01000d403800905440c0c02001010b0800c40b18129130070110700c4084c0d001180e8925820410301500810346001400054040da4550b10002c454800020400000c3c0b016690b101807c0e8040c2203907400002e03040c00040c801107051140300d800c100c000c0c00c200c2c08400d0024410b104480400c1d082080204d1034500540c1c0d140c1009a50f14854a01551524020314030000100401e44640d80d404841c5e5680c80341512424202c850341040743e48a80381150f9800303444a50107880043c0c00102e840340c202000c219a40c40c8040c031070080c050ba5580858060805a00c8012104110402418040d082c800c1117106540b26105d0081142d000c2e0060040c15094001d42d0701401c036250102401c18000724050000003004008401e1110302201203c1420185034500d00d0540306102401b5050f4004010100100c0c1c090300007020741c0c80d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 433879199 1250 433877949 433877959
    0x521030d0c021204030b06090a1b140d050c1c0510030807052803020d1d0d03020109051902040b0402070807030507031107090c020d0206062107030b150901060c050318 73
    0x501030030300443c0903402600121000031001d410720030981040b07402070340d205440341004c00c101c410701c00ea100c900700c8405414404101e81da00e012203540d288001620400101c1c600c083c0100c0c10284a103d11941084030808061110051403034242c4480d806841d000d800180381c2c00c090345040d515800803c0d0310800d01a165882001000c2003100c50141c12052421800125003d40680303914000f41031480c081d20080812100c00d2201100058822407070b1030018044620580c072840c1e503c0c05901424400c04040c10600901e084110307904142403501001c0c41c400c90b1304001010200040100b24000c030000030b8142103040c002c280c0000c0c080d00040403510f0007800d000c0364800e44c1c0706040d0b20701215500841c05450701c50420b10800303a01007108109450b62800580300394030b80780e0302252220146241da44125003040f000c0259081003441020040c5070008510a540d1031f0056402c401614001076050041e16007000002d0920302c640d1300388180c1603010001c1c600d031815079600d0000b202100c0d046903603c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 433880449 1250 433879199 433879213
    0x70e06030a200a0201020c0f0f061503010f050c09010e010809190804030b150405010509060312130504060b040e1003170d0b040911100c030212130506070c0521030d0c02 74
    0x403000c10000792652043d150f00250340c0d2007004902d1410004540304103201c5501107401d505c08010081a03c03540201c0e92001400c0d0f01d28850002400340001c61020071a561030041442010706840c0c0081403190801c0e00d8420080c00c180340112001401100c001c501038100c1a035140e030603e0040080006680a102510f0515440303071920300303801d0000d49604503005c1c4225169107190401c0e010316401480100c454500310f10741100866158210401072001c1e20b6030001d80d0b840303489841c12651000e040c001c1e10030810580c66107044003482c0d10078010ba00d00c1500810005000341e02130302c2d0303003400c0d00c0d801a4600000d11088800d1095074101e0600c0b075901d26191240300d4216100c6110340c02002d8012800805459064404e200c441501140e1180030080059030002c0440e8000039650714190300740312201c3e41c40003004000c40c44450980c003c02da05c00c1c0300055800601800741035a46c20748900311a03016042c2c1c20060310030800c058200c4144990703003092010b0221f5880c982c0c02850441a140150380007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 433881699 1250 433880449 433880501
    0x1209052b0c051008011d0f0a0b03030c151905060d140c04090602070b18120d111b0606100c030302030601020109081c0b04020310120f020301090317070e06030a 70
    0x25880202440d030000d071a0300010001d4a4105001141c0c0c0c512010049030b142c113000217171f0004504001c00041700261074600000701c0c1d440c1002110700700070ad1a01038805466298040c1c0c40842010b4422105001c1405240c1080007074070f00c101c50088800038800741086560b962244145021340102d845140074107003414020b600c0c0c0d40540440903105407401039985075545410040080c0150500303403075040c0c01030a000c0b440c2002a140700544943d0303043c651508205201d1401820740a25501402d00c0041741003010104082c000c050007805510540d2103c1d90340390240591b0b075105884040003c0c9032590203002281c003940c01181c0201040c0f00103d0305190381c0d1244503440e844100c0c51203003e00884418842c000040c414614224001c607000d40c90340c14200b0301d130741441c401401001c0b803500800c0141d03000c00c1511100f100c0125401b9000348030305012410040c015035140002c1c54000c1180d2030020386041d20662050041c814010141d03400e40d00c680200d80010a0800d01c1c0c604d4545000b801640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 433882949 1250 433881699 433881709
    0x121e0115050f0a09050102100504080405060c010207020a080604030206011202090708090c150904060905010e061002100e010203070e030309090403080903070503070f12090e06150f071209052b0c05 86
    0x6403e401d4641608880c6400c00080c07520380707418648031040c0d2a14060100140e1948112401ca8800311000b507103850003410068020301c1001c00c000e40c00300b090640014495004510300c1c1c070541c001c2d002d907600c1c2c0e07982c0d103115070b904481908002d60180c401d03400903e15900400205421018100480700c01c40074600200d890007038200004607201e8008104428035291600649001d884660070920041d40341031080b01d10444040c0c00d1341d10850070412203812040c0f081007030f40704402040c9418080e00c1095080d5600035401a5000000206840800501d5040c00001c031141034002a24070b805c2e80d07445450445001001402d1705c6141d0200f000184003045d010400340c0b0320680100c031150258006880d05d209224100c1e0030402c1409407010741001030981c4004200d5029905542c0704900300c0c10001c003420070303100b5400b80480104010034550103001cac811042a02d455050717201c8010303207900e4038100b0070002292003103564804d5500c01c51000303900002d075a41d07025510036824a440d040d12000004c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 433884199 1250 433882949 433882957
    0x5071101051e0a2919120c05010903150b0301110f1c0504034802040b15070303230906071e050313150f02121e0115050f 53
    0x10240044200c4881c010981c20b49902c1c1c01000482e410070000034045410011070000b9008418484810301e0b1546603034848031148104031614080454180c0d031100c0080800040950702a00c903140000004074065019820280c1500c1d002480721640002100203074001c0c0c806041c8561f011f5488221780c00306110b0207800b6003107100300d0034022501c0f00e000e44840c4090b810440135808402d4140307028000441c0e04001150001c2c5004484111440e5032042400b1501400440c2d400d40304404080c46d00035961145404410107100f01c40078040c3c498000204488005058070140c920f840070040040001e01a500c03456003550f4110008141c40d0218207080030b1002c040714804c40b6900441c04224445a10019082c101c0440b9003401c406283d445d2801030031408020300d0482140c4800c08000b06011006d401110708040c1c0311414001c001c000d00e440006034203d40038800a480701d282c0070900c1d001000961803d042c02e103207400440ca80c80c00d108610f424050702503440501100b080b4160000120200070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 433885449 1250 433884199 433884211
    0x4020a03020913060528050603010f03030807020d05040b0703030b13150e0403090e09030c0106030507050102010b06030906160c0f060603110618060310051e01090f0608010303030507110105 83
    0x16241c107040010f200d41a140c00304081d04480c9030401c140640c2e504c9101095280c440e1014402122800c1c900e02c81c4c07075070011780000b94042404400064076100d1109640152442030380e170100d10340c4480f44140c2c0d07111420032420020910600c0184140a007003c05011072900925010924070060408100594800c0580014150700c40a42c00c03c00d801c087c006800a0a8090000c07100d440c00e920300505c42c089c14059501c001c80300b640483c0100608006490000c00707280000c101e0141ea078a4102c3eaa882c1c0c0303200d641d002d5401c00d031016002d8030b4080305507072103500e490002c1c061903a83e8200e4038203031070040d06180c814415503140d9580031548400342d0300011442184006074560441c20540507002000300e8261191204005540c078007110340101d08007640e01601c2c202e449854106580406030510707000306070051460001c09140711034146030401d145000b80c0300e0f1094540c44541403042982c443c021100442c80d4240108002403090f40000d07402074152400000c9071a08101203400c1d00c1c020f03904 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433886699 1250 433885449 433885451
    0x70f09141f050a14120d02100b040902030d1d030313150203040b0c0307201c0c052d0109060207030f030c060c0807080601112d030c100c0201060b03040204020904060504020a03 77
    0x858071550410701712a42001884000401c0c0300d24402000039640c0d60507c101ca0021a121020740e00c5079212504824011540181a80c590240c0c0764001011000740e800704440c41910180c070380ca4642408000c48142014100340c18001c0f40c14500040c035420401c10740482103120800c000185801030740c1c05040a44d40b484041d40c0c0d107001c0742c1841224030a01b81c0c2c020b0f0445030200000340984e03440f00103294a80e654110b040c0031003907103414281c0f00100300d5844a904001e80b20b00551800e001300562113001d405480402e01c1804168004683d22042e5000300c402680c8010300a01c04261145d11807440c40f8480e03d040c070b00031f0500e5030350f980a0b10003540702100428161030070b00141c0340d0000c5065600800c2031030a1204403034154a05540c0d0b12150f8600c0c24070080b40a07880c40100c01d01301070421120244011a956281025501940d484003802440c5880d8a0100070f10002031040c040c00003103624402c1c00c0745c00c54556808103c001d60041d00440d40c0300b41c4e9031100207195292400a001001c0e12618 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 433887949 1250 433886699 433886729
    0x61506042601110d060509310510021e0702010903080d1e060312030e06071b0507060807020f0d1d060904051914090303010b0708070f05070f09141f050a 67
    0x44150175114039070400c91280304507508020807407114022005400c4141d0041c5e000360341800c1019030a0607500407025125015040020144181c9a0020700c01e0f203511100c03000c41e0b002c40191244980c011400000e001560040042000c03951580292850000c40c5000007a500c084404112040003410502c0c103d480e1030714010020f00110b480c14400300700c081e050a100d0000740e0500c19444050043c481c0b81808030140c0340b00c1c00c403070640c5007619145900c001140c80c410b44401000c0d0080d8411103929005100c0c0703206940308a0004150200c43c0c204130b4880b180110714101d00400010b8650314a0764100d0070600c600800b0f50390398081c4034010a03121031003181e0688500c0409080da02d1214090320107484203c00e100e03c3e0840002120304542d80201103603103c150343e19246205104801018281c038403800300c02c5041c00701c0411010200c0303e00501c030b454425034030f4004600307460000d03101103c100100d01c00211104100c4000203418000b5120110800d0703110000a02d040c00150410942d4041081d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 433889199 1250 433887949 433887967
    0xe100b0d0b09120d0f060b07050a03050a0201020405091306060b130918020603040b01090b030307020a1a040e0a0606030b0f0f0904031103040b1b150103030e03011b1106150604260111 80
    0x101c00c8a007d052901c580340d191040d1910361303070780d00c0103002c00003400c1260000d00341c0e2005100303605860150200402c85030305ca0030291151000c00300f807802d0946803940740c0300f4001015110b68080310f803081140035035101e600d482e200c035083c0200761040c0034042d0280c034070100c480180c2d9040b000310b00c02c5210310a410711039414010900211003264072843d009500410000307015a0740d0309540700859144021160311044068004000e501450780281032641541c01072121481d4143c0021055840b280e80402210001d4803c10145103c42c840481c0c000601e9038184419040c030f04c296641c00740c0030742888400d03c000784500601e160300c83c2e8001d4000d440007003000e071050184800c01700e030300c0c0070070030b00500142480ca42410200d98041c13100505102d408114003919840070341080220100801d0200c12400e0000d4019140c4400c82400101600600b00003807040e4074040c03004441403c0160901d4206401c1034048548484406140304804200b0701540701503a800340034004081c03400381c0100391521011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 433890449 1250 433889199 433889201
    0x1f0507030c2303090106080d02061902130e04020f03070807050f0315010e04030c020d122c0409060207050f21030603030f0702040207060507030e100b0d0b09120d0f 72
    0xc007002104020440c01402014840e070302000008481d4240050ba8030b882c1c600010b4010301c034507480200d040c000c811f490041560082126441004030408901c030740c05800c483d800c200e00c160304071035014145000c400d06c41e10a44204195100b840a09000301440040c80020b00e4046958440d02c96a8801350080c00281000346080404500a0b0010200e100641181800201d01405103950760200c1c840000c0605118031400d4005a40242082104c1602400e111403004010358415000c40d0780d08281c11505c40039024032000750282000101000300000c800c00010304a410419102d054007441001c0204006000e14a001400700e001480c400782c400e0322040c40c03c01199205540e0320300034010804262400700484017615589801580e03151030510001d002070103028409400d4602d0917082050558056210540c160341d000c0c01c6480c1e481c070550220050740e060070f41885d00008085001000103030200314140d0071001a5040ea030300c10707044940d03a028036003001d1603900440d03464400c044030300c4c41c403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 433891699 1250 433890449 433890461
    0x8160212010204051c150e190606090e19060b2115090601440a060e01020a020a081e0703050304021e0603040b040302010b0406080c0f0402070201170601021f050703 72
    0x2504018070406070446e03c1b8911001401d40e22040d8090b1202c0800039001014007a10085211030703041b03d1041182418600000e01c281c0c020703070a03140e241c51550801004006403204c9080c0390320240306505461680c907000038001a500300c64005141c0040d040114a40c0202d040c4078452440091030340c811349403a10640124080c00900f0311b50880e10050000401c4a4900c1690807628101c611030180d940c0320a0b640011401a00c0304084080900204181c030040790341c0b540075000381003d105405000c0071a500b00d2050301d1245c409070b441320a400300000c10000c0944103940d038202422140c0d0f4100c4c01490350550083c0703012000910000100030031494107181026445245200441e0505074480c0404c0203480302800c00f80c00700141200080401d4402d403c5034040c90380262044c4410341d501c0c11340940d03512a03c0704003442014040224005401c09100740c945003601652200c0001880c0c10301100e11441c0503122a0440c050020780640001459030900c0e25000303c01c9001850b440c00000c001c0480710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 433892949 1250 433891699 433891729
    0x6083d0905220c0608310201080603010509070501030504060603171e1e07020a0320010201290d050c06030c0705010c03200d0e06070507121b0816021201020405 70
    0x102c094001000c200b02c4902c4405444443c1003800f13058641800e403091035104042040140042910341d6072000d6011621024a10702c03e88031500913807110010142606d034215020352041d40702040030032496110783c1003540c0240c05039600180d8641c80340c030b41108144110070b6a4075176060000704d440800045600e044140012aa40181801c0440441108000100005180f9240c0202d0048150368884803440c000350760140c0c02c00c2c90f4044006c054452040f5021096016500c3c0c1100b50108000c0001114000150b45800a08100c00c501c20026500005d15040d0303120b21503c00100d402c0e1b183d000c01980189031200001780c945000c3d16007142507401c408180c0c81014141420040c01d000c0c00201009449602e051082d22001c0c03901008000f46043c100c904480c1c40792a0910001d560060300170007060740201c2e2010a001090703030007512051005104a1110410801c0c110041541c0703074041c1c40c5100c2e012241d001c80749030a40010788034050340030241805950000d800c118901d088a5281301d00c403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 433894199 1250 433892949 433893001
    0x2303250f0206010306020306060d0f06080f010b090103030f111f0b01050703080c160f06021306090b1207030f05101410050f0304020f06120105090106083d0905 70
    0xc1100000035100c007410b00c0001c08494001c00030644560303402e000d482c45011040702c10812951036256981c040c00389031064800e9801455502c2d000c40384103006020b8113600103800c880c035030f9103556000c5801c4480045035900b0270150500800310200148526041c940503c4500700200b06003800032011102c10444c5c00703045c00b40400c0000002900040103d9000c0c0e22085c2203070322840c580c6406220500095401070104000f901c0403000c1049a40c041c203014491a0145a2000c0d00c0f03c03401e8401c13000500400c0e1f48071380c00b030001a8860310201c8085a02ca0304610300840d81411249100054070b0042e01d00c032401007012042801410304003041d40341a044102e402c1210740840381006040ea2240031915860100000001402d54841c4d152204c0d180801070059640c4407015000714088020a0049074852410b42c00001a203070f1007040010b0098160002072a48250402d1000030241c541e15500c604540010b581102204841c0e003d40000b403071494008076941c606052100d189406001c1c10342d00e14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 433895449 1250 433894199 433894217
    0x1120c0e07180e010e010e1e0603030904020408070e0109060e0103060905010204120503070203010c02011b0c020613030320120a08130c0f0905011e17100516020606040b010f230325 79
    0x22348640320110401811800c0c5e84200c41d02c8a10100303080d881035040031a04035000040001c1c006900090780001c0ba515005a40d94590720b651003141954164400c09a400c8600d0005001040417680120080c0348628001403406654008400d1481440101518107400220325401075040030b02034180b0708800b81c8001c0001c0322000d0200b54000b41195401d00401c0090000c6000b19190031040b240c01d20340308042105810743d01d14005040132013502480402810170f0300218110480001c0a501c0301c4400801a401d00c40440070803641004000c0400030300009030200000030810390102040546110000000e55600302005030f07042d40c0c41a8010310340030120703a024a44040703482c400c1c0070669061501040c800051284c4d01440c1c6400703a10100f40451802040c4640122010003541901180741c00351001030783c60303030100400c913101d10803850b001c01c162060702031986101d08504c458034034151403140c1c2092000740100255410071200e50000181c1c0f40707c8500401c0d090328200d0b02085691402c4074034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 433896699 1250 433895449 433895461
    0x11107030c14011709010501170303010f031509121101290103020c1c020703020414240103111309061215113001120c0e07180e010e010e 60
    0x101da006114500c2030904000d41d004190b8071910072030a41850007500c504290030000001d42c000c1000307108900d4010190804c007421004040300384c0b07048680d0801d01e140a10300d1500c80200a0141d40c0302100003554410b01000001c10101ca082e0703011195607240604400740016442c05c44401e0741c00075444a0042c025000341800d0500c198084480c02c0c6030140c1c0310902200524900b2500f444660100e8403220121001c0d03640c005100c40440e8002c031024000c0706841c1880e5140010300750f03400321350301c008d0800c0903000400754009002901d20615000481c0b059501c1e940301a9042055008088901e0b01d4003000895070500030706025100b018807031507d840480e42c600d0104080285182c1c80251141d0404000f103007148142c40c85480c9030020507500c400b210341150344130b004841081089025400020849043c41c4030403a03106030f8030542c440449810310b040c032101948000c00c0d041c10400340e03048a000003d03440c0d2103c0020100451131326442d506240c00c581c01c03510140c0146206009100070880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 433897949 1250 433896699 433896713
    0x801120c05042a0503040b010b09010f0c05190305030a0608010b06030f070309020603131a07210f090807120513060c031e120b0a050105070b15031b01110703 69
    0x81224070841d030008004040c030111501688401c1101c46842100c3c100c40100b0301d4000c0002c510651003500207690716a260985030006000d6402014000f42c1d12a5500800714050196650300c50f000384120303005000c40d004100d110b0714280c1f000320009000442400342d4811180030b400050071005009014000481c4042151800002c0003400c44400c0103020500342c50103a0f004007115500901001d540c0d250604c41910b800e58204021100800243c0c1030507030f1a08000317442c9001d44040d540b01200822542d20144118240c80c040700c0f40603581c1c21600c03201203a0f0f8416000f400384100702032071300e910b0541410788014890107110030a000c403c2107880c0030a5043c0000c40191100c9080402c103040380390030304491064440360b842c103101d5409400910b503642c014502d5000030200c1c3c0c000f80b200746540c500b480070394801d42c45485d02080060007580300040d0704501300d1382e220213900301141148007041c00103894910f41308440400b01c80c900345030030079a50380a819103004581d80c100511419186a6800e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 433899199 1250 433897949 433897973
    0xa0204031506142403040b0423070501050d1407020a150603021c03051b0c03070501020a0b180313060305040b0604230a09020402070c0503190c09020f070501020316080112 75
    0x1e101e82c0120000c0c00080d0029249600000004d2040c0c0e42c407031920340340058038407109403403d42e0f61080d2403820910980300c00c044060400802d0010301260307854400192000c0d00040e20208820351901d09403820740c245203640b00e00c40c3e000c0394002e101150b82c60801e2040024003006501d1481d041c0901400961245545050082000389600b039903c07205003801c42d4203000c8c540c200e840c034a014512811003140002041d40c0030700d0b4100e040d00c0e0301c0ca13035400069960701160b0030010320000c51200040c0d02c082080d00440041d29210080c0c910341045640f4035030000040f40c0064021996074421f020a11540346012640400d060b1000c000d01c1c07000b1000c0c0c803a62002c00c00b244090344d032181c1c000380110300c05400c82220710341d000d4801d64552382d003442d01e074410641c2806164028070400d5008011004002103402c0543d41180d0702030441030504400d00003960096110130381d0510100109400a54240300a51140841c0036181100d0729144c0e0004199107810307031000200d4924030343c40c40c1c0820340c1d030b03d00c070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433900449 1250 433899199 433899239
    0x30703060b12070c150207060506040b180c070302120a0c030201050708070c06270b010512061306090804180b01090b0a1202030a0e1608010b19120c0e0a0204031506 72
    0x102410415038580320710fa00542c05c100315005400400c41030204005600501c0c0982c0049030241303c060303030f0744080c0008a800540008170000b003130b1001c60380c00e0030300c2402008480c0c0644191a105d035014000d441c42680000c049900103110010840103155080c8203940d0020820b00d8100034a0501c000024890200660064100381e0b41d01e580124480078440031002c00c101000034250383c0c41c07031800c0c4081d652909200c5c8600441c03120f81245801503020981074401d0342d0701d5080300440042c5e503d50390000c0c040110b0849501c5820032020990b500711303488401c6103203108900461407043c25000100302c1642075015403000ca806000044075039400c203c500c41801101d510050700c0e0b2b0784034501c200280146419600c040d004505010a8103210308400d10103450f640c4000344400c1c1460828444c0031410f80c0d8450045001020041c080c045082c02003594003402955900d00c1a6254252690358038401d48011b654142d002404108000b100086440b000c0c012880c00c00206142c2140030728041007003004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433901699 1250 433900449 433900457
    0xa0b180601030f061e1403060f22050303180c0a03210c12030608070e1e15030d0e1002070f0b03061c1115130e090106080111030703060b1207 62
    0x42c440c9000b6998802c1004000b10024074001d1203c030021451700303100c540542910100d450103428442c0c24005000b41c000c070135140c10702c01c659907001c0d00104100400010b10a03542c181c0803034240030800400c051401000310b0b00e01c0d00ca22402c10614585082480080c540c042c8819080401c007047c1d540c4403d0500d030943c4856142502448801140c40201e0401c00511000ca8080855442e0f40d2580c0000e0641c0c690704221000386443c1c01a04c1018a0119030310480450782070281d0380e501300c00301d455130780001091540d02e29048444000a04001d0030384040c01c0022840c480c20310040c6002c588074003285e542800549000c506000f450451021140140030502ea000808290941c076900300c00b216203250300c82c0f1848081c0301d81c9006115540700b1800d02d4487ca105281003c40e22641c035084900b99150f00c008080040e184c01401080a0f50041c0701305e01a541e11342d00091401028001e80c0c65080241a150b96a0f1400714405021038109811081c55550103000c510b150b4105420095080320302414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433902949 1250 433901699 433901711
    0x40b040c0e0108101d0405012d02070c050d121e08010e0c09030601080f06061f080c0c0f03071406040b0c0c1606030b040c1b170702090702060a0b18060103 68
    0x700000881348240e00c6800000e00801245094464500a507401244a5402404078a44088078021409000c40720312810350b90700030403640581182d50003002c0039071050302414200c56a940004040c02a151415160802584207038190642d004048101d10040c003545c0d072036845000b000c000c10780b0308140141f190701172070000420310135142c2d0300980f154411f00030112400c03036840c1c40c500350716000c1c40c0807500844d11481d800300700c091a1401400318801c0e2103000d088108004030034101d40f42440034027001c0d009081017240e8030241400b8813842074120340d081d00656480d003280c030708406281103541d03450015030400d1041c84009008171380741c16005030071002041d4640710000300060501494044000400101100c0050315641603041200803070400c49080260310300e204402c4d65a0604804078080c10b50040015800281c440140d0340019408480e505e0309110b040d40c003140030300d11705440784000741e030002c2d0800c805480c0d03e002d013155a020a8852802e000d06402d07500d54514005401d59047c552249 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433904199 1250 433902949 433902961
    0xa1403090f03032a16030e040f02041203080112054317013b190219050a06050a020307060501140411030606040311150a0e040b040c0e0108 61
    0x115401c54031a11069a5690402c12901c0300e251300034002d088070480542c4805140120001d007070360031840d0000700a02010039990742c1200d16280d00321400758000c0d0b480d801241603990710b1010348098030940703580751551603042c2400f0700b003403405034403900d0707140507c05403040001e00100b562074407203010260512000b400000c0000d004149007144000f2001d0902c0500d0142100004007812a0000202c0800300c880040c5500e0a954043d0070703946841d00500800700042200344240c1c090100c1c0d450303d0780401403000d856a800c0100321070b40301003280c241070719000c1585400c203411110b14042402e04c1095a2422011851040c124400c0c3c0e8280000403400200c03c030f00a000321051160b200310100321540c0c4076141c603503a001210300c503140582e14112032080582c691801b00d07070092400522040c1001d28558840ea241c150001e0450340021031001c04030060242038015000c109100e490383d00e501642c90042c0030460302c0404045205a040441c2c038150240c01c90401802240c0030b10780030041c0d950761 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433905449 1250 433904199 433904203
    0x80712020a0b030f06010908010911010810231002160b0304110310060305060c070c0509060a0807060809010c0509061821010f05150114030a0f0603080a02010c050a140309 75
    0xaa2155401c00000010084415124113659100c0c68090301d40013080754440c64034500300c502c2d188000700942e42d1031203170616660041300c042d070740b0205600c1c158000540b10041580108860030098680301c000070030340740706440c040061111050242c802000818a041013044400e400c0381b107500e0220600002180c03e01c035039824071145802002c2e046903940b5409024500c010509440166180c5c016a0089100710650300103c0342010b4001d0202a8218241803c10a0741c20f0003074000c2d5030040c4100c2c1c0010b41da99003071000744000c3c507040d22039044a01d032072520242560014180381041060030046074407a9a1364005852044c00c03003a404012200b0300c6d4001c04c980c070b800031101e030f031000080f82e408681007441500403480c10100d202d81807007261540d00780c1d250003000340c40300c3c68081000c1103803c0c104d2071070f070f04003466100b44040ca01294401070783d0111011503189400a0310791440c00a5821501902401500140000c074031b00715240c0550010020081e0014034005000d200000010403418442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433906699 1250 433905449 433905469
    0x50a1a03070809030f16050705190e090f06070c05070503030a050d0c0e09010801060f0807050d02010516020a030305040314060f16120c21020f0304030807021f06090b060408071202 79
    0x25245d255079901c00c607070380c4403124030281c00440e12845245c1010545050000498919148030032100315264209800c407003203407c0040c01e280407446445190000341b0001c124080c0110b045031508680d80f103440c2071040c10300c10940c0210f406517004100103180c041e403086c03c8079400b0001900c00550025119011a400807070541041d0303100c60701d00008681410194818021a08141910340c0c10315601c00800b510f8003030612455900121400003200554040c10040c03002c81404000340c1d00041550b80041c0612500303070419000070360080b505200b000488802c4a942d2186e001c002e0100e440c0000c0100000c86004183c03c1045a41740d00c60789100c0d004885690680600b91010b02c000c110041005141d51801c1800080480c08243c44a102c00094401c0303c40004410f0708851550b940d03614117440c0c0c2c45c0e000d41510114803400e44408881c91032151078a41c4d00c07211600c08074200b0b15001c4e003003040d41c075030300303802486000d040004001400c800101c0104841d940d201184c0d00003864000a002200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433907949 1250 433906699 433906717
    0x30a0b130603050d030c090810090f0c0308040603140603120a02030c06190c0c0f0813080d0f180b0702040c020c030d03060905070302090913060b04090606050a1a0307080903 76
    0x10614074007104000010a41c910b1211392690104541d1052210448021001c0d03c9864010341080c980480c81040c3c83c0c1004d11000d010309003c00070804950f444010700e0a141d481524032a02c086400e001d4181c0c14020500050706030340c501c5095007400000281c4a0300202c1d2209220000060f050100e00e0003802940c094802c01000c0e13407044d20f02450f80c9030190150100f546107441c5410031b403a520a0107480b00000c40340d0032034207446181c410781e40c0b00c45040d4081c03e00111040d030000000291680c080201401a844541d110850840d204070060403107190302d200c419841840c1c40c4c0500c00741070018265241d01350100c40101b69904400307805d03403c0081c8003907442d4060242c1c1801c01501f80d05900007034201c801903a010065591001e404408a000701c801d0300d98000000e02c08510400d941e00b01c88024140204000070b918041ca000050449042c0c8c682104c0d41600c03500c0030400c0e031a0441c1e07038070001c1080791161144420041e60b49a0244002444182801540340100b075421600708143c6180d04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433909199 1250 433907949 433907951
    0x51005040812091623040203040c0b1e07110a140105091c060603050601080d090b37090311090403021507030b03030a030617070f141305040f0b0a0b06030a0b13 70
    0x351a0065500d1904500d40c9501855400304214a504d04291023100e10403a0852a40d103a0941003403100c2000b50b00c48a00004002001240b2203401002c290080200900c6050001e02042514050000840180e8481d041040d084c604440c0166082421034080090441c0d290101d01110f00d510221100071300e102800841c9014804420000b000030114140c4980030115152038488120455010740180034040d45020240503c44001041100702c802c00c0e6881004207407000e5a810002542c40c1d000020000016102a000c00c144055a43c1c643c413112010303207460025144ca42c501950b102d442d0301c100401400d02c0d00018035614440e41c4201e03060540202078070768408004000030007410560140740484846500d1003518058006a001c1c220345d60826950300203031400702e410703058007880b01c111500b141015140c00c0c6158074621425204034030030f2040001000c042d040101582c600140840b00301494078803d240740750755900a40c0c0d889080f400d004030343c0c0100c9030040b840c90303040e801c00010740e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433910449 1250 433909199 433909243
    0x60403050706210501061b021f020601150c0210080c0d0f0f0f0506030d0305070302160f030f1716050f0a0c1412030a0e01020f1605100504081209 64
    0x116482030201010f02503181018030b54442056004040312000e208100c080707181d0b0600d144070300c041c00310b44501c068002021030341503918002802000e2900b5046410058202c417006100002d0400003401001d03400e0714014010080c1c41d4080b40c500d1240018003000d200603140003402a15840c801c80740c0f50f04004000b440f55104242d00c5200bd000000072454901c0e08010f05081e02c048144a0355108d85002401460410300070b601c01d400418018203000b040640800540d08501e421000301107417207108444904030304010b0b080c01054007005100c20002c004451072019115030f61000c110f90054030b451310b01d48600003000343c142c81a1180400c0300f030b440180840c0c03090080f82c000c01c4e2107454a001e200410f01801120390080c1d202e99a01c58000a02d5000b40040340c0d0181487d07000c071a080c5c105000040c43d06a20042144041c0c0100c45200300e8501981c503420100101400300c403070601c882c80f40034090390406035200203460140541007403c4014003000140302017000c112503015400c0b100c0b509410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433911699 1250 433910449 433910459
    0xd1b02010209012a0b100f0f0801060e0c2205100c021305061c0203010b030604080a0e010309110d0f141612050303070f02030c010f05091b0f040b0604030507 69
    0x20b9040204001d02040b00080c4003242e003500a8005100c030903015800e100c210b5600d40d180801494060604015020803603004150b040c0301000800c05401064181e0501914200905007510099005003c541c007019091000c0c0c03031070f0407080c0da0841184000c00c1d501c85074400c64088629a8a501c51a8441040302e10200c1c826008512103141500a40e110710014401000130780c01e560007940c20f2038002d01000015640490055408100548000c0000c1384450038000040d10b01041500c1c1514144c000088480c0c0042e0020303000d403000002800d00340805419600c55441c01442400c25a001b90ba281043c2000c004400070003454480c0d1020b0b40340701c0000c003444110303074030350900e02d04202d41480840045040c00381a00102c4c174607540320004500d15994400c0c1201c9040250b04040c0540c84203214144512000380a0f078080460030301800151486c02103411f40c41c00540340380341200110300b00708065003910341c14040c0c1c2000c1070a40d4080341f00a00e40e0f0101d8850302c200d60029200340125030012131 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433912949 1250 433911699 433911701
    0x4031218020f01110d21060602010b0306070906080106112b0e031f0e0712080304020f01110703081602060706050402040c170604110d0911090a0e070b0d1b0201 70
    0x1295600039a0310b614402040001135610409031041d0207196480348800310030080c030403c11401514480c00c2c4510403164500c41607810748955400c010050303511006220103506003000321f41d900000a2501104107032510300041d00140f018003c90b01001807042c1c0d1900c05050800181d00b0f803024250642c0c1c1001180c199049001e5441c41d01d600005400c3c502603c114078000a820070b0541010380c0c2c28481000e40d04603000102414404820180a60000091740810500032045c6050040e50310395601c2c942841000785014001d0101814016101c19401108100066510903290f01c41540d596403802d05003c0d41c2164010b400c0203510001c00180070741000003640050b40500c2c801d95003400f1501052400b0317a01e0030070106588140080b21000508a45015000a0300e42d2100245084c507104406440d101924503408040d00e160325200e403011803900745019142d912940ca182d040044542c88079010307489080520403141d88001c085070051a2501940c451001d81116a003a204031665208000c2c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433914199 1250 433912949 433912991
    0xf070509030613030801081f02072604081005070f0305060114040303120e0a0203030a03020a0905150a020c09090a03030515120607110c0108040807150617060604180b040312 76
    0x40009070317800000256410300040703840d0443e040030455103c5103558040391000350010351054650303203061600180c036030310307458016a1003440303030b80c18155204e0030203100c02d02e003440701c01d4074404051034a01084407441d4090380034400c024442c5004a0113498010041b44e0406080c17412616200c1e0003d000001c041d00701c1081c2e00d15180da5441030149649681c0c1c943d0300c914000c0806509034104102c030391a545d01ca42c0c006d189089060038204e899903101c03401f25130441c107407826800e0001c0b00020441f12a5404000196135a082101d1f1403d41c0d14012100588901d0204002420b150302c50000c21030303006511034919441000034003c8041801d22210f4035030740784d0082c0d5a10002c285810071300c1c1d45200000ca5880c0d442101a100d0043d540c4955507120742a07807041c131302662a4916062402000c818034003940c401048905a600e40309041d03240c1c080d0401102802c16403040b0300d0003601007220000200307442d003060740003600b030081581c0b00c7c102030703174500c00200030709091616080109110300420030280c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433915449 1250 433914199 433914203
    0x13080c0111041502190c1707080106090c08060406141504080a060203071e02120a0c0204090c0501032307050a020f060a0603120c05070506090402040302040e0d080f0f0f070509030613 80
    0x128181701c41c6a442c4030402109001c050415414928240001e80d080d1200d00410052107040303940e410b903160759031401c480b0f150708620200c588503000d40121581c8485202d030020021030301000054904048840c2e05400140c125000c0e104410042d409002d5104c240c3c6c004102210903201ca510191500ca002544111092000714061000c011042d41034800840560819500204010381d90b0781c1d00000d4541200c0e00c04420480308900a80041c0c03618001d00249030301c0f561455580340c5c100310000d0f041e1030303940ca2605030712000c403201410300c1c5480c03040a030303048800703410301035075501e02d4110481c1814903100540609114a4081c064150816803020301101c1c0a0700a17a00c0c2c0d00350412040303440d890341c205d010b00b09074080031082c000d0340361040040032000d1004000500c3e0640c5da50110702640c00034001c4000e91b030085011075000700e4210030308950042c04600201000d262400c0c0c80600d00c0c03000707404c4c01045144007000a051070b008038204c07203183d10014119009860b0100041046d90501502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433916699 1250 433915449 433915453
    0x7150201142a0a0f0804230d0f050f09040b010203040512030a02010f0b03060f2d06040b1002210d0e0c100207060219020621011a0313080c0111041502 66
    0xc026a241441001e032011012144d9411000d8042e2001c200c07406103001d042550f824500480540880000b050815042a00100030f0704071585a500050701d410030780c106e40001d0201c01c120094940002904980307122004a400048420701c01004034038500981e040103400402c07050301c040c08900000058645109503a00900c0b030301d80700d803891009540141441a42503400328000c2036003154440400307a4802d040d03210b03158240c0b00d4843c4104e0f00031044445500100c902c5410b1094a040038007641c89001402e5a20070b40e00f0070005002580d461004d01500c81030921034049540c150901d6040361120780d4168000d004a0840a40d15515281d44204240c4250f844000c003008031400840c0c007600301d540c190080c00350049454503440940c1e140081c01c981c0482d0070442c403032410704c071002c0480784407282c00e10080042d0304103190680100c1c03116607250814003041c800c0181d40c0c00a0201a046c181d03100301c00346e84442c0001e03215070240042c031140001c448408100400c00381c004d4814031481c1d0440c1e40c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433917949 1250 433916699 433916761
    0x3010f0e220209071211040905090f1c020703050d0e0906090f070f02010b030f010c2019020d0c03290c1204080c0601060203040512060601020715020114 67
    0x10070381c001821181400140c0d800220a4080903282032000d01e540140e890600d12004403540c954501203c8814180304048407000c201030196552078420a5481a000f03c02001d0f1200f0705240c003582d0f02c1204600018000f00c0144a003051803088c010940110b5002c022994403010048018180c2c2c1c9074000e03200d000c2c2092800045070351074103c030224099900a0b41c0300310740741c0304c000046500c01742c40440d01040d0341d25071502d2407540c0c8040005045071080c12000203040861002c0003400c0d0118500d0003001ca6100e500c9030b4100c22804640849014207403a0820350005a510110340380710074650300a0642902001c0c00410700064800b02900d6018050000c407404015401900280b0307402c0e600003401203401d114401c1c103c6d040784212030b0001e000b040060309055800281502d004400d800510050700080f40401c01420628042c125407102400903007001d00d002c0000039503030b0015100f0b04100010318052121b440d4001c5d405038000b00d0242410800515254203540907824034890540a00c1074200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433919199 1250 433917949 433917961
    0x602010f050f1018150806010602011d15040c0509070f090603090503040510030603020901090903020d0507020f1504080f16080304051804020604120b0f070228060e0303010f0e 77
    0x42c02c0b070b5110745100702c11610b42a0902d2569600d0400d40c203440b290059484055810002c110b410100060070740d00000c6c0b156604004000782036030100d180c000320b40300d551141c03030150007004284884030740d4040f070309c00d40e0070354541c1000e42400030698420383d008805c403402c1c060040ea02003c0000c841c0c640d601c400385c11542c0d8410450031510321000103005500188001c0c0b2003490300079080f01504a0034a00803422589940014081d0f490030ba001145071542d64040e13038101034050050503031001207800e00c41d04011040d000300344008013000c43c2510403980b400c0016001101c09069502500d0b01c0740c01c4408003d901d0480f2a038a00a040100f0031154901400007584007000049506548000d0484800f101e01070f20400e40314000a402264841810302010480d41d1401070301c800543c0c010621100f060170712034554040f10354007a146c1800c40d08000300b80c0161301030040c0004503c1c84424515410040d55003004001003800c1178211030507000c00000011041054820f801c00d4409d0011083c0c401d031116 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433920449 1250 433919199 433919221
    0x5040f0f0c08100314010219050c16050a051c1506030c0509010602030f36120a08180307030f080c060702010b01020a0201210f0e0d0c02030a14070f0602010f05 70
    0x803584076030000f0120741c080c00080d55403202c0203040c1315003e00241c01c0800b5003100c40010f041400303510b8002040800c480030000700800001c4229040e00403206132030345c2054042004024540101801030103910354510441e0060052119403d403c43c902c591032408001c0c03800082d103054030003520070902c101400700c1c4919000388214101d500070780045161010032060b00081d070704144860703944408404494414003484540754026402c0ca1148842000010b030100240b80540b641c010a00303034010640e0800040c0c04000310f5100ba100440585e03100002040081c0c503044040d0001000c070035894010f1000c0120580160030803080c4801510400e603100345089080341d04550100b4010303806010132a001d940684030381001640b192155201001e4104611000e83c0c0e90110040c1c903156030384a068084000030302503003800210a240c14414074003150000382d607640f54541c000d0048148140340359241d68041000c0001404000d131200b071090340d00c96005e8000c1c03012810024005061500040d251a25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433921699 1250 433920449 433920451
    0x60212040303030c0207030b0c03010f080319200f010218010c0f110a031b03020a050301060803041715041b0e06130c140409090203010b01090303091a0405040f0f0c08 73
    0x940080981081e29584044000e40311007500c11003540110580880803c04d015040c520030b060b5101903c0c0d480d49006d010031005402035001115a41060010310040d0440485803c0988094604071009404d120460fa54801a40042d507088c2d200d9119a111050702c1074002e010301401c89480d40e03d04bc80d10200540700c0c51003441c001003100d00018030010000e400c111034030b1800c0c400034016801c030795103941d1072019080c4a09240d00c040400d0460070003c602d480302400c40035000175802401180e1900801c0ca07a40d0080e80100c0300c040e14801154815a00104000083c0c468580740c111040d0500c2c1c207000d254800104c200c10800440c01c03c0c08a040040b0355042409690301401c80781e401c00c54420340200501d000c0c08200100070484071180e03c4100e0b044007801c0602501d5000251080c0c0910405013101c00c03984050b41844003494003080401d0f00544500c08490300608240000584403284485510603600070590140c035061750501d40455507400340721410b00748030007084880024101a0385080c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433922949 1250 433921699 433921723
    0x15070516060c12050a180603050402150c0c09090f01110d050a2007030e031c080114010c080d060909060218030a05061305070e1e0c0708090103270b010f0602 69
    0x10206100f424224032400c014a010340349803034194449200c0034081d050003401c0364080d400094a58042c003055280001a9141440410001c1e5190040444a060704e40c1c10058009101d001340500003540d84500b030165001890b14200204540308109016800c55041032103910301c814a0000001c000021600c501c0b026282a1032a0b0103400c1540e0b2543c40540e80042400c404005482c6241d5a5644041000103000240003402008181b15080020316140050b8402c030040191104440b1051b604480c04000e60380e0040d002c141d85e1304a2602500280c072243d0300001c8818544014502803100c2c581c017400c90201002d000a603e10240020103660320302000019040360011030108a2034036492803608050303031080064075003166071801200344400040781c03072041c0c4174406185c4141495803010080d6011010080030f038106030b0070380c03a071030007a0045030700c89418036580701d080004440306128260200c0c1c1401c2c040d00720b541c00f20b103080080303000c003885a15080c4040260104a040c00401d078480811 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433924199 1250 433922949 433922963
    0x1c020408070b0a120516030c0e0a03080307200615060a120f06080f060603010605090f13030509030d120506060f07060b06041203090614040303051815070516060c 71
    0x9050080b140c40a621030040c8006202e06007502c0d1072094040d000b1540320383e120401c4260b265180c40c42c0036064030034a089110400c00c507a07070f040705160741350040c42040c2c81d00b001c0380e20f0f16552101d20070354444133541024801c042d1400001c040a20f400101c1e07610401001c1c00d008400502e10040c0403140c0982c00c8103201040e141c0c01c90030802200c0368004032800407100004a1000d9891112a05010019036094903d400850030003034141424011400101816141c40303140d0310f8807420000d580794020b0801c2c0072051110141e031090500c01c030107441003504020b003034552442c9100070161071504101408c45005050000241d040d180250550745032003151240ea91400034140c1e00c031030003032920101155025106210101d50111815000000c0700d1007625048806805d0001c060b094040000544a100b84100b03c1400040c1d0301c80241c9041c0c07420307414400244030b2104002083e0a4008140a002007030121703d101c01c1c070200241c115a1103440c00010141691101421170b620080350602030118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433925449 1250 433924199 433924213
    0xc03030a0903020c0a124b17030405010f020c0309120a051f0b0402031611070806130b0c040f1e1814061008070c02010203040306060b1c020408 63
    0x82080368000c10000e5120344103940c03c1d03640c84400668a00c4498211940b40d84c0c1c110228004c108002644d40c00c460503e24140c06c28483d52540d8031050f8041c60b9102c0d0202440d0304001000d100c1d480b0211921036800500c080318030080d5441d003150794000711400d444940c00c01150f5205801a44221005881000301542c0f4048049051200a64841c041c450f01f51280076900c9011840c28450034108a40c200d10000c0740114049003801526690159280b1951040051051603540d502000040c0060340c1440e0781c0c05c2c000142c546061100652000e6194041c5008214481c5002c0d4018001c17a80f2a82d10408a42c4a031b0310f608110b07000701e000d1a880100d4180e4140828002d840c4049000040f84844c0d00c0790f251104141400d00a400408618507515590710a40c441c07120210103a001c0c3c0300303407007030400c43c0c0c00782174010314100c8081c101e0410320206c050200203691081c800c5901450308030806100c815a510100d001583c480e0002090364982800c2c45c211880180c000c86007200d01240042c590 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433926699 1250 433925449 433925461
    0x604050a060e150109080102040e01050102210a0804050307020d1110030b0f04021c0f1415090622020c0c120d05070611190f0909060e0c0703021e06040c0b0c0303 71
    0x32180300b0303000e2903050110745d41c800203c01909000510142c04031046002c40381d494200068078140c92200d030600c848143c0c10b401401c1034006416550100c40501d0103540300d450342c0c1882400c510a02034040e401188040d000350034000f258000d08a0f2680035907115880501d0b20404604442544424660100d5446801841c0c0d00c1c294003c0e01440345142c98403a203030004217843c00102e034a4610301610a9413991095107030010780000040e031241c512514001c410a0b42c1c1c1c0001e2280320003c20082c414860030480700d03a104446040c122504401540c119642d400402d0502d076120340b880340d124400d07851060103410003440800d100d86094400c2d100c2d20b0501da5150707203000242c0341c1003502004465043c041c0984c008002d04510f01507980f070761a6022201020100204484190340160000c42e0070000f00708014101200c820707501980d031248250322980c46140c102e0404494070030804080208c11444803420102180081c003940c85103400c0031402d59100c0c0c4089290103546030114090700f01f0310026903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433927949 1250 433926699 433926721
    0x80121020102211207090302030d030621080906130e0c2503170a1d0111040e09030f041508011d040f050c1201060e090f0a02151905030604050a060e 65
    0x40708640b99003c0c241800d5124081e0403081900b16207160000f10154010800e40c10244001014444680741c10b00038541003201c966400ca0b40c5007070b203680d41802c2031806818049400c0903214000c0c0300074001036803189481c2840303428050f58050618046a03940225010080c1c1108490180c840400380003110f940500080213404400c190a400303004203501000c0c1d00070f080ca510b0a03c200e5104c1000140c255200a8840044c0312071076013407a09070f143c02600c51b4508240000d8408541200300c1004065550000701030942c000c0282d6265980d6020602284003060402c00a074030b00300300c0d51085260381e62169032280c9042d4556505444002031400b0801043e0a0070714414200d00132400c071b8046031301e03410109807001620303004c0f907040303942d00d03041400542c00e040609504030251000a04130301040c003108540750f01c0c0d00440248510b03100170074460440b04032400c0d141d11854100d251407080e20685070241c0907601c00c0300c52621841c83c15000031a560080d1150100303650070741821b40255650000320381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433929199 1250 433927949 433927993
    0x102121c0501030b04030806040903080610140c011415010c11030309031c0201180206340501050a060501170c03090309330309120a0c0b07080121020102 67
    0x480300825644200400041801814021403181e05140041d141508005040860240c00c1c20f01c65820480300f0070100c1d0f842012903800c01e00440380c0c050007959890003038034141071450a440c00744201103404103c0308019808541c102e030b0791282d102c21681d120080316440c02c40b03540d0304038040340340715130600d0100360400d4034034103624005002c80740b42081c00c40c0040d02d401c410710f040c09003207083c1021a440c00360307080c010711245051461003070400c0e040c2507001600fa8020b10852400c0c1c40c0c0d115120300d00743d142c40d001015004400b10800e00e03110495040c00c45c003800741195144480c600f4510001055445400d001003684035600640303410762555409154194000341800d06541f10505c0060b42c03039031fa0034422003010034800360a100200c5249040c6103a0340300440390005454002c0c01045110003001c01d500710106241526a40e6074000c8030429111840c900034060162140e102c10016030581164459043ea503070103142c0019561018040d03802d00403040070003401a0003040325102c41140b403407200313 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433930449 1250 433929199 433929217
    0x10f3807020a033903030806060a0c0b0406060305060f01050f011d040e0309090c0f18060f03010603051f060504121103030f1c05010f0315110a0c0c080a02010212 71
    0x9000310340e96915252864542491118801304420708406070380d0591a07401d081c1c03503003c03160b018a0b903895503e014000030001001107004500c00104c2d080d490f84240c4401c020b80e079200301b140307031903050900b089001031085000c00c640300c0c880c5102083c45840d00003082030480788018070002c48401d83e0401140c044051428031000341c00c1640c0d10319425650350090254805007031008607251040d000c20824a51030180a080b98501c01b0869404105000d804894120400012901003a651030010903241e2040c101c40ba014464080000714010760300d50003031402041000320540c0e01d09660714074104585024400c1e003012410800c07080049025462500050602449148a44011140119007140c0c0141019410900c00241d03201003508030b80180c3c190349000c500100400d40c10120a40d01c1050140070140c0001a41c0143d0042120140c10401e03c1e5000d4000c41c0d501c40c444a40003078100c04160004507603060000b04d005c02c2180d4005502445190140c0c018070030f80c0e021030f00503080c42e445003c03c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433931699 1250 433930449 433930459
    0x60f0a0306180b01090b0a08040206070512180f121e120a11061806280c081509040c05060a1206080309130c08070503150306010f380702 60
    0x80001d031510715070b00310032003000311000100b2a666000c00060400d142a042800c07039200c28000c40758070355804006140c3c0705074190f8481d5900c0c0003908045103001c00940300d081e494880041d0307401030207944864100103560180e8ad069941480f400c10007024543c10f1210080540c007590881c0520000e00c01d031004d014400d0819100b550307284523880c0000d64043c0c41c0c08800703d44001d040b0141124208049640550030080c00180d14444843d0315480d0680a80401d820b00c0224407001d82205c2400c080300c075159005070702049201803101d0702038421401198107401580c64600722443c2c90410441c41072240d40e2007448050701030304080407c50a9084294030604124079512411801070300d51040c08041e00540000315244d040d0503080050101030650107804150800f848c1c4903002d41c02c1208113420020324185140c9036070b82d0104000651500480765689441071800000c0c01d52a10072403207041d9100004850b0702c5035100c450b0008001806880e180c00842c4401c600d10a92283c80c0151500b1440101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433932949 1250 433931699 433931711
    0x2103070c050f0106080f12091504050402030f0f0604110304060e16082104030203100c120c050301091505031c03091203020a1d03070e04150e0f0c030705060f0a03 71
    0x903001e19029001e82c0702205a0740d0340c10700340070005041000e200000d2410004143c264890f404050890040440c5240113000e041c020303010b07000c001000d40d8041c001c080d004540f01e1030324450450b400c460689044c1da51103006000315a860600e8040c2c1c0d401101c6859615103580c40d40d0359003400520141440e0501c0340a1401403040e0800019004001442e4001c000c03c10000040c0c0c054801008401e1280200c1c0b03810002040103803030205200701041060480055150041107042c0e42205407559000074081c03900491144c080c0d00040510f0507154042000c0040c401d8074413402c01c0819603405603a50651140c4ca2003c00e42c0e10f1a07441141e141031600d404a4010601d07501e80c0c58407820918840d021175000314042a0441d4403400d000e4101d04113547c2c24140c038840c00d01298540005001ea10a1484000c0c0000c050280e04813603c0c6200c01c440004101480031101003a88540140c0f458034524003c000e04a80303075240c002086015180c00030615880d100350400604602e40c440036048043c103803241 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433934199 1250 433932949 433932953
    0x90c07140307031d010f0e030a020406090905060109090b19090501020310031b060e0111070e010b040f091406040207060e010c0e03280f05070f06031d2103070c 70
    0x11561803010a009401035850b803540b441c01034094898030a07110f010482015040046a80c8007600c8800ca00003824020300181083c4046410140c101c1b0001c0d40080c1031510016a911003540528429030181090300c0441e621121524140d4a9002c1d014182644c2d0001144040754045203501902c00b4070500040c1030001646c4490a80c0c00888103008051903040080050041d05224160b00500094080c00e074141000c04c040d00b000c82c1c0010740d0f81000609040b40126041c1007205a020700002446054113694079031001c82c0da5030080c02840d0a4558045002a03058058041c0d08804415812026110b581700801e120082d00301c0c10007540c28580b10750740700108190030b00c54101e0002c115511558250001428103240001d0f402c134288240c0e200b070700d1200e0001e001800c0c210300541d01c10126642440a4208146044030300e400250f0707070a0030030348005402500356100003441400300d0400304003400358040d090389070000b042e07504510015600320302071185c404c000190740c08081424400c1c8140c0d125 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433935449 1250 433934199 433934213
    0xf030a203010051603051f1e0b1206040e03070b0402220218010e010c050c090a0e0303191503030819020c030c030c070f032301021611010e060414090c07 67
    0xb130f2802c2c0e00c902220070132208115414011268408100304511b000c0b61000d502101d01c5512a21580c00181c0d4008900c2d440b00d501204102c0003800015882a100e078542d6030301550410342a03030054826468146a00400c200100075914507541020320115203681c0c0d502445565010707103160003813909940900d00c1c0c41000510142504024680000810700d0015002500c162210700740181400017500c03030b400003c0e1002030080701ca00c6003950280c1c41c50701d400005a000d00300e100350740c5940d80170200400400200c0c3da2990200c1c5c4509910900031101840907621055103a800054002154040050a44582050f081480a07101301d001031800050000190664103c4014018103800000e202403052504019031005030042028050b4034900d50b50b507180c10120b0303502e401703090080702c281c918543ea903080d41901d400c60042140c1d40340d0586146002d110032000da048890200d000c070901c0c1d01c81c6092050548003a10429101d101008156008010300824000c0c04c0700211b07007040204900003540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433936699 1250 433935449 433935451
    0x180702010f1a18011a1605010c0c1a1e070c06020c0d11030901021906090b0c030109140c040603020f070602130e0901091a060f030a20301005 62
    0x3070350100e440003201d01042146000f0007050142c10748070904010700c0200140d5025403165a20464045e907148281814203c0c084441000a400d65103404040014960003050810700248103170704810302180440c07500041500d060300c025038900018000044191411520b260308000c2314180320300c10310403660301e00003070341d0003604507003550780003104a8480160414080407600f506000a14203141d000c20000703542c2c1c60700d12200c0e554008005611400c0c4001540b081c0c051a4000004100324681805803801550080c0b0801c6131241c602080013941a00d580c040d5401240c008202c0ba10f0300d454403004801a402010200340d40c1001005524005151480242008920880e40010441c54408113003880c2c1d100418240c1c00341d0511849900150000e0900b0220303104047c194072003900c400c0c000c5105503045a6449800d44602d4004205120003107443e01490109400a0079140c01359074180031744401482480300c2d5542d00d0311002419201004140c001c80072460040342c00c40118440607038140c0b40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433937949 1250 433936699 433936721
    0x9180f08090418050c010819110a0e010203030403020606240d050108010605190e0c19030b090106140720060310031214160606050310020c010515180702010f 69
    0x88006a07408840c2450f0003501020208003000b0a4041100c3c0c440355158100e1842c2107040001c80030005040041980c194180c80c4d6052904000035401c070006031180e984400e0300600820b0580d0500140b540c0300100f201d104035450350240000d52035000500813001202e039040c0200d000400c10641009501c9000f8180c0381d1000341c00030400754501070704682107460035004140140000c10f030f80100480c0e84110001142c0d0804d0b44d40d001596a04998041e0380100180d1522100243c00d024060590680048070307040021030360130b09641d03603400090f214008000215641d00e001030000c603000c1641c800842001d8440311202c910065015000946503610407204844540c06010041c4240049041c40c409820183c0c1804010014690000000c60252041501e100d20500c1c550200304001500850002d0034040e04607491490b201c506c001c0650402c0d54107001c19840e140c0003d2807000788001156001d00e001d00400c2c01b101c040954807808042c028030080c1550f4a42c0d04a504121251007031380c43d0070b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433939199 1250 433937949 433937963
    0x204180b120109052d0303130302070f0909111c03030209040b03160306050c0a05160f0b0c0702120a03350c0a110a030e0607060906020d1401150909180f 67
    0x309a06a419500482a0b020740d00e100840100192242d04001b086941202c402c054900000c026480c3c102d1500d40b40c5e410282950385a428005951407107500030407141c500c1a9041c0c142040b000b030510640380018030604141740c000710f50481c0800e020f54028241c20401810205503196100c0100e840c1015112100b0400c41c5400020400d21000e0300c1003540101d0b10b0103105242600b2a000203040c0e0089011040c0d507030740100c820400300031840d00003528041e800321304185903160100c42c10955402600d0164000c05824400f00b8070204046044017900c0d81c036849140d10400304070030742c0d041c446109600b04d224800c2e20029042c4040d0340484140b0801900d911150344040c2c8490041c9211207054030505a03a0240ca110300010750400790500801d807007911030f5920380c109030800c4005171904800140400740300103180680c00440f50402015009403500c000b5441c2d90700d00304041c02e000700c00441800107809107414000c18000b9004003481c07141381e1000410b0345445446614170b203518514111514 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433940449 1250 433939199 433939213
    0x3010308120705031303080901090501110c010b0a05130b0a0305012918010905070320131208460807090f03060b0102030f1201030b0a0204180b12010905 67
    0x4118041200c41d0b1241c1603191040c25414480480802c03403038400da000301030240240008200303042c00d600650b01150044021f006100600451201c95404103003041095400c0014a982c64109800380a0031650041d1920042c2000f51224038018041d8030782280e840710301d040340040400c0e0309000c0c20070030b8a0040d1300d007442c60080f00f4004100d200b08444c018002c0102d4651550a40c00c60418181194540180440c083da0b80c0743d030032002005150b4030701c4800c2143c02e041ea1080380326000a404a1b107081d1508003029604d424400b1500e40d0000002040c2850400039030920192094805d64010f54120340c400c0000f811000d0507000c2108415001c89581440d0003030041660301501e1a030b0000040d0500500345400e0040c96002d82c0c005000c00f90074540c071034140649030f074820002c60f0750040c050700c1880e4880070301b1480c0d1300d004c030401c0c4419104400e440c000b144c2c41c14428401c40e022540313810141d1002151040e500340c003921004c0c40f01a8099242c03c0c482c000c2c00e00a0261520765403191001d4408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433941699 1250 433940449 433940467
    0x3030b0d11041518091e05031308010204150c0305040306110d0c0f020a0206070c1a0d15060906080907031403091f05071b150809011a091501120203010308 68
    0x864030a040071a8030f808004030204056980120101070341d40c01003401107a1464242404040b4400310b2044107100902011042c05000002c07000d4805804c0b01d0001c84403190ba5050018207030b000e03600980c4240c8611002c5030090f0303806682000e0401d8440c2c2841c41c1059038945030202201c0c5903040d02c1d003840d040003800ca4000011441100104007042c1044400300c444075000030b40e80e85c00340ca0f0080c0199800076550040c0400d8a0b01c4100611804d1802000c010b00010100c040d500522007d0a040d410120f0303e001c1d040c40d003081c0400f5689540d0360200901e1618204843c0403001407e1944180201d4001202144501c01c441c01079580c3d0b41e000b15900c400350002e2003405020344010303254a84403103400c000880d038800d00329034034680c001080b404000c805001850300c0c0c120700d40c01000c9550000300300d044220307000703542c6034810385603c0020440c040c8031120243c0044203011080380d00100c810000b0b0f10a41a0f03050240ea8060103140002c01e01364540c0300390080380c3c02030300155543d04011500c02c60f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433942949 1250 433941699 433941701
    0x6090516120e06012c07030b0a0801060305030a0804031106010b040807081617030408061e0903032e12060203060f0a0b07030806060c1e191a0403030b0d1104 69
    0x107444500c4404005820440c42001e0301c82e401070085200e403c003803144d0028004e0107240c1000c0c8000d00c2d1006804142000c040160050505141e201c1c0108000b8a0004d00e5400600c140801ca9030007001441c81c2100e040d000b01e032a40030090040341030200181c00811115004c0200340d000e0181181499a40e6040803000c44c42c080485d807003094240d10500c5500c0da07a0010b807542c0001c4488602c5d5003088107405100d45815400390b0b0308420414810705040124030340c2c1c008004400071000401d4a40b054454021040d00c0b03110899403081340801e0840d9a488141e0340e1031941d482c0d02c1041c42c1d1410100d0b1541191a80140da07030340c060b035405401106008044c5854400709200034811184c5500c1c4034940010003019004201000d428000140001816500c0b502c6c101c49a001c034960994085512096810196040c2d01041003c03907c1540e4890040100c00e6880726041600042162031090102d1140e49606200510440400d41c0b110440c0c0f000d516100c1d6104801441b52511165003000750741400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433944199 1250 433942949 433942967
    0xf0603010f020c07030f020f27010f030809090a0e030c030c070902160602090103021b100c1119050a0f0309141f031503080d0207020f0904020a061206090516 69
    0x3041d018410006034290010000748042129484036280000b18881d000041c5070880755044a5001081c15014510b04540c0c4e203144000e41c0c94101c650078150b40c0303c40c0c4040107400c0e24007004091100070440a88140341c41c40c6a1544021320708000f2881100450070a4115001005189003035440032a003407500c58001d01c0038001509010f40c00f1428400400c0781c07848940e1403903a010b0700050f40041c038042143d02c02c0c3c0440d440d80e4600400c0a044042860303803035540d880c03901440345040f072030840c50400f1035224103a8100f07219032000c0144a940021901c4034003a00c02e129044556109105003840010000c8803168209802307500d49045c59450240780c5241c0401c0b80c2d164620600c140804001304601401e0040c400c0c0c2c00380d2a002400054500c0035142c0f41c25039800140c000f000218460514000980051070424401c2d80c8551920082e90f00780400d120003038600039030001c1640c00070712809104942e480f8655134070102c04074000750742d00c40000883da4251090b420040041030000e5806811412754 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433945449 1250 433944199 433944221
    0x318050619020106120f080304050c0603070e09091f2c010203100f0f06270902041a0403020315060d06060602070311010c0b070e030a05011506090e0f16050d050f060301 74
    0xc421030174500d80d50754164444111b0b0003003a2210100200c0c0900404210a106101004d4040c5949050100000d00400c4120b44081d201c1c0040c81d0000c0d0320380c0c0700495031046900d07100129600c0326080021040103440103070b03e40c2140b191018000d05408214051181d103500310b000c00180d03130f03080c00044c030143c1210301c2d0095003008917100381c00c1041d915403101d07480c101d810501e860801c00c610780300c0e07c254032000003401e4005c00440c18408500304c1c0140d4001c008485240000c034600c4024900101c009000c0c41c80041d51507008017041340e01110f803280ca1958010b00c0241400064001541c0e148103c2d20143c10000060b4801c00b410700401085d161103c2c1641001d0074402c00180c040d545040001360010007210800901100303a43c0d250301c0030011400d03810381c80b030000c2c40601081210803420079030911813200003030341060380080c0000702860311601400280505201594400d41954943c211003031a410030402c08012500010100b8419280a03004071340d04403034a810203004040c20f44408c0e02070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433946699 1250 433945449 433945469
    0x2091c0c0602070b070816021f030c020703051c050702090405100c0e0d110a05060a210b01050301090b19031406090c0f0f060f030709032a030318050619020106 70
    0x20302103041c280045d5418180e01004265035500004903500302d11000c8907000b90008000304604036028a40204008070950a0390104404841c040c01240d481c202403001038001d81180c0c51207449106001480380c504216401d0061500c04141e01081d28603004480555054010050102d44007130b540c000d080d0345054a103485c4807660309100010f1184400c4480041490004020700c0c0e40c140c8815400e500203041c01004036031140d583c00000341c507070740303100c000250300080030400d00b4051103180c03007282c2d103101c0b060b5200c500316801c20420500508502079446e40c0800700c15584500000d1044001e4003841c0300301d154a18512106001515011014040305030a070060340a40c01e8980f143c0315125045241191008000c00540c40440d100d4402e640305001000700c00001c11001d03540015007001100c1c03280b20f2040c07081c000c100c0d846400d0201c401d0743c49445100305200b003001c8cd104440c4101094141c0b44002403440e40d6a00203003007079000200f1443c0031140b048511594035028400d08000340740940c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433947949 1250 433946699 433946713
    0x307020d2303010b07030c17120105090705030126071715090c100e04090303050402011202130b0a2105060f03060906070311040906080304030b0c0c10020a0302091c0c0602 75
    0x4140c4601d40014007a0a101c020040380d0700d014540b0410500c3d5410b41c0106194504100801c80c045990b402881406205004d0f0300c000101420641320b07a5105680c19500c40e810f50742001250100c1000341065081d101009100440724a0018410800208001019400584003215259080c10079881c1101201c0700c0000c10491100c1c0702080d5210040d60844d0b202040070a960307419503644810f00550fa41251030030080c90205501503000b140958002d0301d801c10b0b40540020848140e114070f112201c203903c0641420450b14001c14050710341c00c3d0640c01c1c0062200c102d00c4500c1690180721441248550700d030800d0002e28206800b5040c420ba5003a0060000d0b403030503c00150741e8000250000c7c0805603111107100c2100e02c8001600c000e44120201840b04960345c800e9160b49800600041c2c6645c02e60802141614808008a5170900f070341401828400d00c8440c200b000a410040201007495000c0104010681c1e5914100c03240d04c04480165145150a080c42d0982400c5070b003150f4290340c0215 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433949199 1250 433947949 433948007
    0x9050f06070512090f0d2609010905010e0a050c0906120f010501090f0216020603150a0f06030c1b1202072105010c0e010503011202040605040e0105060429040f0e030307020d 76
    0x300e481001201542460b03000c0c1085010a0520515541f0b5200351900c3c1607824000301a07010b41181d03030000d005e0b100a000010b05d0180154503400e0804000341141c1c46a1101c44590800c000180d500010041036841d0f03046102005a051601c81201c003496130355200c0041c003008210b4400e6141440c20840704500300f4601ca41501580c40403602c01a1107071602000103070242c03c0001c11100b01c1c40010b8960800380d69246c40c403207c0003401e4000c88000c03d0511310b01e0619a8030030f602c948400140a0403d4968040304e440d09c00440b80307041d44440c21801802008140d2543c402e82d800003003130740c2c02c004a0000071182030050844149441030000c00101e80720301d4103243c0c1d010301075030b06480220300c5144840d17890780700040041999074003c6403c14201000d1404001066101e10b02c9407800351000d00802d24041565034501000b0440c40020744100013030700342d42e42050342c0811403455105100180080b0441c0c1c0305459074004843c000d00503840940c401c0303000c56103d40d4103e104100208001c184040354 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433950449 1250 433949199 433949203
    0x18010207023f030f030613090b040b0105240c1c090e060607050c15070204092d021c03051b1f1803050706180c150516020409050f06070512090f 63
    0x74001c04e00641000700124aa9540d9820054000d038850311040000f04150310301000d014000326000d0342c4e50107042d0b0000490b810540320001c110090300410b42e96540784000c1545c0071781c000030a2450355100c0c400440100a5500899105d280b0b040e89681015070f180c1001c5a43c0001d004000324060346081c040d40f0700142c00000d62182041040303603002a4401c014952810074000e41901a521a003000003080500c004000c821444500e0032600880603800c004a91b04003060303000c4001d421054610409801d050480d1100441500c42c0c80c142e4030300045006504424128050700c0c030300d150400c000d42500d1120f429607540d0107200c0410f0904c8000807505244101e0b00c0200b0b0084d00b440b10002e40001003003240c1e03001181c0100360140b900011030140c00e24401301001da0281044103030541c64a452542e0150041d9264403003100104114909607130300340800740c16201c0c000c071007510800b4803441c403001d018807906200d03080990360603450b01085103a0038800440a8204140c640025541d40219040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433951699 1250 433950449 433950457
    0x73e040e06012601020f030613091109070c0b0c030915010e07211508160f1403011103090105060f1c061e060306020424050318010207023f03 62
    0x1400c079581103601a030400c420388007a8050041100f9500c0000d40940414884c0c0145000c0d9209841040d0600551303404a802c036611007c2c06025200c00c601400003d1401088a1f1f900c807809180c800100d80e1590381d00c07441c4100640d82c1e000d440c3c0001c410010002030411141002e039445038511405549071100c04542810040c022404220312608110b4402d000c010080001e941c440e20104245406c0350211103141c1868024148103024544581030320a2020340980c003078030351150b10303502c07034501e03050f500540c511801010580654030f034450440f000b605030000c2e5114105000000c00c0030b15105040140d100851105240314002c004194070103184041d03203024103540c0c02900001d00719124200220391011304a1803c0700325003003170404020000d20742c02030422110312141c0c121f001000041d070b80303648000196030000020810300c00221030105141b05621080b042000040c03070800140c0124800030350305054840034581d6008002d260281144401c5d050b08140742c1104006e000210015889201e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433952949 1250 433951699 433951709
    0x7081510060c060b09040b0f09030c0d0302300403030b2d01020c030d020313080303151009030c061d0405070813140a0f12030204030503090402073e040e0601 69
    0x8030341c0b05200104000c42c1c0c01001054001401000c0900d068541100d03144d0044aa604410740c001c03000c142c40d00000000e81d0703215001b25010300b004a04500c4110000d4105415000005000b450f00481d04001c14040803280c1c00c10705d601e248076240c5805c001d42a1410030304000c0c010a030014185000c203040580503141014000a103a629002c1e160040f440c140144086a80c180940c002502e561500000141041031084814079011651031007907a0710780c0001c841c1404000c181034009100381c5051003462081509908003001195100d490301231301001c498110354003064262510400d90000444846d000c0402200c09101d0b518040000918441d0090503c110046031081008200444d01c49188640e045880807942041420b00706540c10010000301501d0360200c24200c0804503100c1c0c0212801d40790044000d6203170005140a01000f54084002030309e0004440700120350b10302c0d41d0300204028004210b0041640f1101003030000d0b00400350b102c10f0b40304a20302080760304111004181541164 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433954199 1250 433952949 433952957
    0x3018150c0305070c0b090f030601030203060c0310170115050409052a030f010c08010f03030503010e22051006290c0a0b070f02070e061e061b0708151006 67
    0x80c9103460151550300071680b004000349100c05001c5081c24498002d0300c1c81e540101c801281c44074101c0103241c2c60300c40078000a07405030082c40006000301043c00080d034000720445c010081d04e0342c3e5207405000301c451541041c03246035151a400c20700103c030301e80e280020f814201e40810601d8406e0340c8907551150300700741e801d07031101866074a1907e8a1411542ca9101c1c5406416a040171026070311090080151210076000b1800840010407918a2021004103807649a2106481c40c1d09114503c01072000c018006040403031030458802c0c5070801c44400d000d0f124880d81c020a02148440007441c00d0310099040302117441048000c51500c441c1c071154010f03208800010440e0b031804429405802d0400c0d09102800c0312814005000310760b0b601c60f0518100786500c0d802d45003010b881307412403080c191050710310540c04010250707000d900803490503a02c0140800141b000380380001e8545482c88823034020859003203d8100e408100071030310341400030180340d0b4a00c2c5074000c1289000108031480484d030f402804100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433955449 1250 433954199 433954217
    0x5010f031b080c04120303090b090a05070902090d12020a031e020c0d08090d0b090714010509010e0a270510050a031b031a1510020303010909301815 65
    0x20021400c00c4030301030304200784581c0c400c111700d05019024095060046443c03829120018208031404212480610f03881005051480d02e0915010041d4000ca808150300c100c01120010014440315414009048150003070600c02c41e8504000d400a811100342d030b14020008034103103d183e540030500043d107074011181d15900c080e942c28401d200703025401f01e00b0b8020100c60b0007482402801ca2100e48900054412100002d4441d510000e0046141c9845400308501744017400d801c1d0f014100c075030320400d40542141003184c1c8d21121321140003c1c030f40358480b80c0c0014041c0d00d401030b4003500402d507010306c0c5c2d000110002c918103008540100c41c2d40c8030190004614904006282000100e0700c001150011425000790400c40d6600002242c151500c50701c1e111141d5980c00c0c5820845040340c15081c650300514110380c603121498024190020b41140c194103407d01c0030740e4240412001c4d84c00950b45040c0c0003414452030704090a0010210b4081a4200500e001049190154182c3e0955039141307150407169 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433956699 1250 433955449 433955461
    0x40518120a020f102c07181418070e0c0a0c05120307030f060501230d1112010501021204030c1809060c020a02130e0c0d21030605010f031b08 62
    0x4024120344091140c1c041c40c0300510113901e0310381100d440c0780e50090005240f104042c030310850742800c10503c038404c1d41007083d0422030154290101020310103980300110740c04031080e030382c1e0140003012100d03040361b0a240c100d1480030480802802000d0a00307000c00d0300003820140c04040c201d0241c1000b0740104500c0110070010084c0501000209000a84c9504c1d12818068000f034050054a0744803002ea0349803942c005920f40c0302c3c034400c000d1110318030444000a0340106900c20540c0c014030b16424115100d00c0f1044a800190000341224401410024419410180024100035002c002c0e004c80c04403c0c00305002140b40ca5800348204d42a05050b13020300c210141051000e81a44000030f480240780c40e03c030040c0b8903008102880e0301442100c070300c04000000d00383c00c4202d0301840300c9400307184d10003070624206051100c81c11701005c0c000c1b03080e01e10700102c0b14800582242a0460f060020fa1610002c00081d604281074840001d000e040901c4a14028504c000c0303501e80b0103e03108100001e00c00461a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433957949 1250 433956699 433956703
    0x6070602090a1202010f030b060307110f07030309030209010801270309120b04060506060310050103110d020c16060c0b0a091a0709260304060f0e03070303030b040518120a02 76
    0x1031072041c0984400080355a42034240c2d06200185010780c0072405220b03124203074034442d10440c5040c0600410090540e1213018044620350403030240182c03d881400b10791400c200041150000551083d529006843e0451061164540d41030740f181500340c0c10401243c01060340c0300c8220401c002d0f00000944c00031403c4c202192026802d0b400029030132040000361080c064075182b07052240340205000e105030340b165014061544022500580b201020000c184071a602c04c0d0003a0070003e0900146d507080888200141049070302c0380503012020b600c2140c98124035494204224010310544c100780c140d071480b58030b0b0800300c80801807003c4511a580c11140c4108040034030301c0a4079881d412020388852526600140690301240149100e81c00010703044a1518003102c0d03a0b1104040f420051400d00740703003140560b03a16028050741c006100009184217070780e4500700400001540203a40104800c40690188402c4a6025000d4550005021102500204001501c00f90044481c0c00345030340300c1c031040c000c078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433959199 1250 433957949 433957957
    0x130507030b070c1a01030b1b090423070e0609040c1709010203010609080f120903030403080f03040c1d06090601110618240106050d060b032a0a02070506070602 70
    0x101803809410900c80070950249103030a6070742c440d5004c2c6820510800c442c9422110903c4001c0c0503140040001c0c6c030030000d0b1183d142ca030103510010241080b25440c00103046e6464241000110301c0d140304100504000202e02c0c40d085001800d02c4a0201d211901060b268440c00300c809000341e49601c600c20f08144074920000c1c07d070100014101c55401c00c10880c85c00f0f540213100b020001940d100340071400d09800700e0003182101c5180e00420150310948800c001c150010aa800ea040c0018000000031802c02402440c080c0070070001c3c10b587e886c01c2e107001c000c14003094022400d01a0207010b00000e84181c00100e41d0400012125010240c3d2107500482e800080741d02d5041e01402005e040c01501d40c00075034100400342a02050324258102e90140c1e002480960310301d10800700705000104120b40c090303c0140f603041c0c62248003254a64454000900c154805d0300d201a04000941c01d854090410803001004128003110a6203006102c240c025641c100601a59218402c0040c11204011540c1c0c125 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433960449 1250 433959199 433959203
    0x905040c030e010c0e030307061d0703150f050601020c010c020a0b162a031419030503060909031c0b06090307030302030309060f10060c02240c071d13050703 69
    0x5210300c800d86440200075190a103030400b4290308281807515141e0107030f01d10f8010001c0c0070317000351300b0202c00d0b03100d01020700340360055030b80c3c807040ca9900c074801c2c02001d0100344080c5000c0d1300504001d00154158804968a410070041d02925180030311009a0323010629600c8088d00b4a001c4001401070700009894a5481d8000c040700c0e440015402010107408118802a50284180c44d04c44084039518425243e09101441c0f95151707030260500004000035841c1c803010318200200c1d49003941650704804414080c1d0030a0340450804810004c40780342000d24140d00036051800345003407510200f1240003121440200d074030556110800200035840c1d1605556600d50010b086850302552420081c2d207039803042d1400c8146000c4c01002800c01c2403407a48072402015144180c542c46032401388100e42c80843c0520072a4080041ea01140c0c440340c1c04845420003041c51800e5079601d200c10422541350920303940c006d8100340201a40c6070094000010340c0b56000072641800030740c5180501d0518184401da401c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433961699 1250 433960449 433960451
    0x105042316080d0e030a0b060d03030615090302100903080441010f030608030306011b02040f0b010e0301140c0f04180f050a0207210c050f0c010f230a090504 69
    0x40050096000510000d50007503545032161300300c0982c01419102d62000c940070313044840d00d00c0400c4003818260203000d91203010b17183c0000c040d9110060035030488444e080304030018503c10f4040c42940b40070b1059002c030358480e04110003203500e103580710f01c2c1d18040c520505007200c0c8100c0d00c04c402c0c075a00380c0c50040b0074071408851984050400d82103209506c80c442e940c60010704559114000b05000f84114001d07a18030740c000b0340c00c642d90303100111184411422410310041c07e20004500507110380c00703049600450a040494480480d40c00140f0359207400e83c195109a0500614a0b150a100c1d0006034001d540016510382d101048554a06640b2a50340003012100d40c0110030801d60045900c0342d94020700001050103241c481404075800c2e802810707000b030502c849a0401d014038040601800d50890b94174100082d80c84000e850b594101740f11058180195001902251925a84040101c00301100c80c1071051a0603081040c2001e203030000080000e82030400950000060701607070180000f0600100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433962949 1250 433961699 433961743
    0x9090b061e120f0c1207090207020a120f020909031c3305091005060d0b01030e07030303050f0f01060c080f0708160507140f010305060a05120d090801050423 69
    0x10304a940d440d11048801800d00906060202500e030810403a40710302051750090403118200001d242c020743c41403004982c0060301100000708400722103a510303201ea01540d41004071020350b0050200000d001014a04103401c10450284c10381c80ca4140322042c44032440703001503005c0c3c01c80100d0380003036080d140c49060405140303203103d410300e011400c10054503c291500c581c1a111082e40c42e25038840d6014065018800b440510700d0029142e00c40c4482c0d0005240110340c008021403201d041c031441d40c00a5000030788410410068134201b400c02504048084014592580b42c98001080481c101100521925002901400702c101d84415200265000b017901641c8401e1041c01b407440115400044a0a01070b071400040c50920070b1061880c1c608003d003c03001c09880c16401100104802000c890303000540c0c440120301911455a4000450516002000b001c280e04030302a00112145e441403006078180820030000860800d9484008030740c4d640c1940c010b22038643c0180c204440320910010752940c0d49 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433964199 1250 433962949 433962979
    0x309030406020d051903150b0c010b03011505060415021614120f030301090f060b0403060203010e0c04060c030509010e090408030a1103091b060c06100f09090b061e 72
    0x120041040318078507002c0743d040a0020a05403030030300902016049140048410421050080d000420081000752590104d141c9550000f1340039009050b449865139500e801110b40f5050921901485081380c1c5a841f481e1071509000841e24400c0d4010082860628412044042c1c02002003d23000810800d4080c01e10780ca1301c43d610100030101d03080c0c500c5410b4140c1d401c80c1c41040807407148001c1152801562a40e801c0649000203001c0d5803461b07030020f0b99a4500001d450f199503010300081c0d4450b110150340c4c1d52401d00361145e440340281014403101d500300002c2040275048040da4803c15410304220341c441441c00c0059039100d2624500b160450341c41400c0004100d8602d00852080003901020044d40724602d010012500003110001e645d030b48246510740070310036281c0550703c600c10004d001c640380104040c0d6044c2000e40555818592165a060a1180040030a00c4001428120000b00300e526001c0d00c0d002d6080f000609804c0c054a00e50350301d15000540007a000200410150500700044281 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433965449 1250 433964199 433964203
    0x703170a05060114090f1908010608030a1e080a0507031407020a030210020a02060c0c0109080c1c050309030703110106080106180b03060601201e0a050d0207050117060301060305030309 81
    0xb01c42c101e0004100e0300034074114a0844054460409010b0300c2c0b41859454001072001c024000800f0703d846040040001806100900802e8080d0000602440d102c507a980005070800a02c528a074651703640091041000c503601106a943c44001036901150036203601c0c00550040c644401211455034040d4100800e188e00040d42c9864144a03900b103400007281981c2900490207581c140c04010780123900400d0368045010050800009840e00014079000517940303400c44c0ea072104058800c0381e00902096084100c002c40f00f90b4084115040081c91840c00004c0300303850f442442002810301c0b02c512412040180250b1094018055910003000425200d01205112111f1a0300d548415420460300148a04000c13070828040d00040e12000d6070440354020004901c24680c80c5410307030303100d200d80500004510b4075580e1204018036002c2e040b2070302c1c141411800c00d0803100000c0d06551000d1070811299a20400714000751305148180704164449a00180c0074207410351003e0305510004c814000d002e500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433966699 1250 433965449 433965451
    0x905010b090a06050a2702041d0c071a10090c0c140a17033c07031b0e12010207081b06040305162402040914040c0b0703170a05 56
    0x81125241c0d11652418040810b4500750300505403c80c3d0750b0034003040b640070114011916002d112424819020b6140d94000403600705520070a00000102005001110950180c91b00100c284982a103441c00c41e842d001040c030b00c0d6441151702903065400280b010144501d4842c09021401014071100d80401030061850800110607103d05010403d081c100a20004a90f4051a4801c60444000c21051a52071494100400303504550000c440034400c00301c2c40128508110500328070310300c40d076458682c0c42484144014442d2091600d0300340000f12101038110f07501007018403460481c2c140d100030f00c04120f43c3c0c1040100395011b90b00200e00c18003001a1003015007804604440300080e03003c24805072964842c0281c0d03001e40800d10030007070090b101a503000b031039a00303a010719005080a89058084013076660008103000350310ba4082010302c1402218041c9c8060000c00d000890300d181408d440c1d01801c1344103485100b02400d8006801001c143c050070101410880000c1e107103c5518011000c5009000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433967949 1250 433966699 433966721
    0x170a0f2607030507180509011202010c1b030b0705030405060103080a050f04080f28030503100b07060c1b0308010b1305061308010f05072f010207060b0405130203060a0b04020d090501 80
    0x5007917800d040c043c8614420700e5085030b40040502d07105900c0d180100d8081c621002e400e80c1004843c490200200d10b14840306003030340780503080c286035081c0345050810746604013400d1034003000340400032300010400000321030b81581c0c0c0104845a6a5184500c155418460303100401c161410104000948020118285081100800598030111a92090b00000512180a005400c0001e01c10310021911860103950720546c0e4043c9028140d4684044c0c003004e8010540840300c03142c0312000030008640c000b1030300051a00140c0c41c0e9145d09516a00a0b26a80050003007204260b4003160012000c43e403a1400c40003000007034806941c69040c0c1100c8610410280182c0c060b5608204400c0d41d01c07210382c410f071442807856548005a014403180d40340017a007180c8219a40c5c882d22071840c0d044003402840144481762107401c00252909410b0240000e4401c000c00d10507001802c0501c41c4007684021446a5016803040c1000503400c50600c00540240224020154135074034020940c010081d0551001d0b610310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433969199 1250 433967949 433967957
    0x1d0105010503150103050d03090201180b1c05070c03081504050f04050f120720060315031c0f2039011e0c0b09010504170a0f2607030507 60
    0xf800c4070300d18041000d02803100400d5030b0b0201100b4030700c05120b07502511801d0301c1454200c201d1682c1c00720814600d1031542210207007002c00643c1e0240315144514642007030741d00c3d0406212514010350040c01c10041030030060107210101001410710148100446040da0009000300442c0c00e01142c0b0a00b03980080728101c0c4c0e00d20401201e101c02c100c00045c84a4440003182c10140b03055555540c4401c081030a80c54038641e140460004445580c44401a510139641c01c4031554280624000b09031034011070b403a081e5041024140c810020944c400c42c00301e4180c00300d0078810100306421807001d083c0c806040c2c08005a020303800e5410701d01803e1007120503104080d00841c01ea10402c40002c0b040f0b02c12000c2105002c140308000d0b040c039440301c0780110354241c2307940d04001e6000620b5441c0c50041d208102c9485000340d42d10350030001000803800241c0e52000c4020509404e00c0310480b4050301c42800d80410380c0c18072611414503417140c0800b0091150802d4000300105075030a00b8400034000e4403054400901103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433970449 1250 433969199 433969213
    0x103061701091e021f0302131503060e010b090105030612010212040309060f0903020910080f030c0d051804051302040c0306050f0f01020a0b0711030406020313051804060c031d0105010503 82
    0xd409010030b0300103d50000d00c031000900503410003160481104a1040034160240040c6801c0000400ca140c000c0914140c03403042074140e480028206d4070f03550499030342035083c0340c010302c9100410f40070b407207880d00d080c00d2855a85e00d1b4000044c0c0c26240100c409143e0398000502d10140300068009940503920079111680040d88505040c3d13441401c46078268000f5433050410009031034030700d842030b40000b00c503540340c41c1c62038a6548060400310501c42c00101980002040da540040030844000d43c2800e51414070300b0101807a89940440d03d101c140c86218035111408502d56491100c2584030040d40240304103d841c003c4100034001d05050300c512031040200080074142e03401d05035a07000782c0070416406050f481c80d2964a03880000c0015051400300710302d45813a04480c6c5010402080a8070041e00203544544a40c0e9a090007206503802c400c1c014070811030b00f80a0041101002500594009000b10b000000081c08500820303d403203e11000e541804607242c0456419802a4141e64094042d2100307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433971699 1250 433970449 433970483
    0x30605040b01080415021b031e0301121403040e13060507081306240305070e01080102041203030b0427020a080c030607212307030902011d010306170109 67
    0x12118071540490110344142c0020707001598000c641410794000540c01810030100b803043d0081c401c1ea400261880f548006846402d0340010261140389a256040251070746d030501719103480c0d01c40704420040620a85ca610300c150320740c051003510080d0451a526a220b80390132408110035120107030090714014901400b09424520800354144540510401c1d203518101ca50381d002c0040210f4010074401e02007601409a0b05a201d101d000015030040f001081030505110040d059a030381a48a0441070703104100802107690004400f90700250103040000361142002e000c100a0821240c000108080d41c2420b0004045245000e00c8007034026035940c001c407a100c40d8501d0341c460f0f2007082c15526520800c0021121445009840c81740c00380144c80d0034150340800c4c002c0c2c040d00d2500c22550b0b00010101200c0c0b0751800d03800003203070340310742c05c0c0c0380034094120960006010700414007401054424407003501456a4020f800072001032001d104480c8400d106094014020115840f040b0b68003545604514a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433972949 1250 433971699 433971701
    0x32214040e0601050607060f0507080907061b0303020f0d09051c0503010b07020d020307080102030702010219180306020307030b060f03010603060e162d09050f060403080f03181c03060504 82
    0x40075400c01c1c0c0c01001075900f894100141ca802a15040b14407a8071120000192107160143c5802105d160f190305080d030412407000b5040a26a821010801071b0f00c0000040c0903881459050707000d07425060040c3d59202060101c0c103103100f00391012071407034105003a1800700400052a40303400020440d46c50864003c0a9040328944401e110b5040701c81030901030341c03000d443c084502000c160300c0101205e038000d548500300c0d402ea03002102c00102603580825078041800101058a121540b1803500594111400c108003000001c07a000191405601000041c40c0c1400b0f0f9102c0041c44c0c10060000ba11000c2e03503900074825910034000c442c002400c1400c0050200071150720140103c044440a400c0e10709900300803155000400c540c1d400c001c1c90480700d15242c0e14600c900d801c003411180ea41d07020140c10101806020107540700e00e1401288100400c0000c1180001910351504020380440c2e034941f500070101440c07040c00d00034280140a03a00715800749200100020201c80e103140c80c2404165550b00802c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433974199 1250 433972949 433972961
    0xb0d141b0a0306020a090f0f1d042301180f0c0e01050d03111f0c030c110a031b120f0206060a0509010608040f080301060c150603121103221404 63
    0x9508600301d00418800688150042c01e00203003149011017000d42d54180004409000e03600116846011710810300019285d601d02c4a9540d08558021416041c81c0d5680701081c83d8009001441b80b500d50021152903000703410081c5203375603503898500c0048142c2415150038130050070884281142800005440c0c0a10070381324101d54000b4100c0399800b00c02c8d20152181c0100140303030304044c019040b1160002244c80c1d0404039602d40e01e0800142d007840701102a085404d002d08103c2030200645185507801300004491151a80c9403408400303441420054028865182c8001491120040d407000300581c2e000b00a9003003100b9580c00c80b07503562944c01c18018910380318002c082d0000344000042c4132003070188402c1d540041c441d0034820740001090710748450070380007038001e100007a00112401090000540e0320106e4210010700804c0311920310ba60354280f01401d6a2600c06000510f01c003d261001e051059401801200c00191b156211800c8541040300050240001c000200440c0c1700160800c0d216007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433975449 1250 433974199 433974253
    0x14010c180e01080d0c0303020f03010b071401050105240702040f021201140307060f11010f021908090a0b0c0d02030108070f1d010b0c010b0d06150b0a0914040b0d14 72
    0x183c9040d07195104c04403400800e103402542456020402c503c0c4624402c030085009200d141c41a9840d41680d190a001003122030502000c540e050000600482da1a6410403441e4074150390f006a0b4440300e41c83d000b0540c050b115002e507001e03180110b602c40c1d8020310f400400c84c142d003044071403055a807030305c0c240b00c124080011819016030024005014450080c150b56860159509000c100c0d000008020340c01d46a81010440130150045171089402c64090541d2a040d04142015101441c08400d0301e580d864001d940036000c84240780c0440d9280c000d01044032004024a0015940c942c3c503480c0a55131641984101400348444050020303003a03c0c4029445501946c050351804649d01c4e041400e4081e4224241d081c86d19580c8228040395592035171104e900e590310603107000c0740c0c0000804954400701c0b141d40c0a0f04c201c4404000680c80a64050070340350648504403036084000e14201e010400034503100c20b5130754101040c0a0181c0c1409003040e8800e641c180c12400b158040d140d4640c100318001010700c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433976699 1250 433975449 433975453
    0x6240423100c03080a0e0625031a1504030b0406090b0f040206070b0711010608070906060e03030f0a09030204021605060703060503570d021c14010c180e0108 69
    0x100300006842060450b820105c80c0001150a0201d80102800c20200361003c003040c4842400d0100e880c0d010002000b200d51640c00c0801542d540b8140c0100b2581d221041180b0a4030800b0100e904484140143c4020350380001028910345428a014001000002c00981d200d14005000480d03940d5001c950710300c80d9074080c00403401c003481a80c442800c3c0394060030080c00d02200311615071403001d0034840d84006084c3d4038002e000071440e001810044440d6500000204410444811100d807400811903c511440c0c4528594600002400311040900c0c1e40000350701500010341c0070001050f800c8840b0703005008000b591401e8483c40410f404642251044a4264001060581a415580b0300c94454400364080b440c40701c0022a000000e040d141041c00800103481c5c40c21035491001d80068030380703140000c0e01c40c0c1e49008100c3c0c001808890b000200b551852031002040420002c0240304ae12940c401c14000b80a2405588d1024000c4a1899007c0096031246400007505081c08000f05040301c1c0a000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433977949 1250 433976699 433976717
    0x1103010203070e2e120e030a020715020309150909100e0601030e0102090901060c260313050a120503011e0311040c0207031208010603110a080624042310 67
    0x4148034146601182d401080135000c0500894107454054080070000c141e5112241c1c42d039100c0081045450a40c8403aaa82d40305000d1882070035000546072094904004a1802d10f82c019034049145126044a490300003002e0a001070800010401070310000720203c45492695440c0380300040c07a9003451180008602250020500a5010b40d00c0b01c00403c0c00100003610f001c0400002c50a1b15400380d000500085240d9043c405006201031684542c9a0030b1b52946e03d0b506948584a48034000038280110302c8081c1c0c4256070400904005800d0310702d900c20585210414101805840c0f60002d10601c601c070141c0302c0e40d005e6040f00310707000c40b029650b0081e1000446503041e014003000b0504c0e440b040041d40308030000800803403074a21044152305070507034440c50703950304040c0001c0c00d490100c45c01840300d2409000760081180c202456036400310050701c4018104401d007810b206819076524000d90581d20018010030384040034004006a0303840d40c900352a006130300c042030003a4000c0510030840010142c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433979199 1250 433977949 433977977
    0x3140a0f03021c0513062007060b011b1110030b01090306090201030b0a08010e0d0503010302011e02071a0304020f03150a0908040510020c0f1f12110301030f110301020307 75
    0x40d02814400a031100e449400e210898400c0d800c864081d1100280d5040310000c21040042c1c40c051038002c0f400c902d1442d2014a224540787d14503000d0030030010002074030307940d40741c1d040c0e440342e0811a0000300000180c0e80c4517101c1c0c103015441c0441032040d103014400700100075034041e001f070280c1003110700184c0d500d406161850301d82100902c05060100d04140e144e0413088041d60b19402482c0c098a804000088c821585110b040e00c3c055504000c04148082031004101503030b08101042990410342e070031890b051030b08407002c034185039007138101011601c9010b81c02d280002c0036a000d988240d100b40c4130b000800740709104050f904c03800c2c0f10071071200c40071180001781c2009480c0c00c181c0d40144903080c454105500c1d40001260003a040c40d40e0401684070001e14480ea242c0010902910301040e100c0e201d0640740f000306c2d0081702560907034030741c103220640c00c10324425000c1d40d21400b600582008090340341d584919080d000204502c10942d01102c0c2c1c40c0000d81c42e8601031080300d003d0402a00c9101d0990032072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433980449 1250 433979199 433979201
    0x602030a02090613060e010c08040902030a0e060901090201201f0b061206091305030f0a18060216060203090901150c0609061e06050906041503050a0f03140a0f03 71
    0xa10488090341c007400405250386465010304600580800c0344440c003410001c004140011880420303041001d221803c40108400001b19000d0310100e0002607030f00d5813510a4030002d003017030040b005010f01ca18010000380400c19881b00982c3d038401d0b680c00b001c40e40c4e400c50762130140301c044480c50f0703080e00b01842c0d011042d02c4007040c014103680c00e40c50219440b018000041ca040d00f0071514295680c29500c2084483d1410010042d0321058001d0102001f024646071141d41e4050f05070741e941c0e6140d0004103040c956000e081594010320f80f9481d42d5402035107a4500135201c0c100c3c003c104400c3c000c0703428042003150000c82510481e0401600c0c02d04168030f004d10300841e210000010800b4400040070702d401041c00d030300400800c0c0f4041c60011560450310310303078480740034400004590b80c00d03d00398082c0410b41d2603152150300103404031804514520413054501030080c081e03000030306510400c0700e44402c0001d02c00071364104a0280c0c882c01002c881c0360342d030004544a001d20a00024080a010708641d90003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433981699 1250 433980449 433980451
    0x70b09030d0c0f080a030605040c0201090b160507020303040b0c0609030711090402040e0d090f08150a050a0213090e0601121a07030e070b0705160b0712050d051e1b07060203 76
    0x340003030300c083c2160b5282c0d02c025600121508000a4541c06d041c805404c00d800344031041d03207162000300040ca0361611401c140010240080f01034081d41d004d98600c051280055a12a80d0000c043d01c3d80c855a900c0c04005592161030f59a000b4015880001c07082c984c040140c601d0345401515100c00759040c2c40401031030401c010800c0364459070b2901e95940710001001550700c00300494071401e5500d420405288940016503100b010301c0c0c0c0c000100100180000b401054001c600c004010405451f001e404802900034013150301612542070030005083e042d5a0054002d090008040e01c21030f907210862203050580c66440640800c20102360014041010f0000a9100400d40b4000819107415549242072041c50f80c0815a151404690b54040c0701044c010800c8040280700f00c5680585800080001ca00410310054400410000d07941c03045030250040b42c08040c00e8140c100010b103016000c1d00c50b811403070f0911468042d5950005429401c8003e0120044942c05241c1c0d4104030030b40d980c80b030203580 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433982949 1250 433981699 433981703
    0xa2109020d0f02150304030201090212060702030a081003020303071a0f0610110a0512070b010b090913050f240601080114040902010c08070c0602061506070209040f170c070b09030d0c 80
    0x45910b4044003004c000000f940c0114429800412201514010020340d82800c3e4145a030b41c0d0000024003046640004c11102040d2060500c119a0340e5155910186c0c031506d41e202a4144c00009a042c1c10040141d07a00319040d03520740f5030410a52106200001e241030b0440c1d0b5182c100520121013801b07103000302607142c0840303000c00444600201ea5640d04d42000b40c01d5901c07044400010983d0800c100d1014469400b42c60114641401c048076440011b0b25244041d180c41c9200301c0c1500b03402d043c8181800302c1c50014040c5e030304071113103103507007512540821034a804007000c900403031408200290302c2041c00c00e04a032102d020402807010700008001c020000000200d042c41440000b074000507500b08043c24080c1d008100c1c07140c90a25000c2c010f81012030091010490100350f00c0764000640d07481c010385005d15010703140d0703940b07994481c503004204500c20701c4094200303003106e240b80000310001c5008280c1e12102c07506907001140d130380345030040301e0013081e004c1c1d80e0540091018504030f5201e600700181c128 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433984199 1250 433982949 433982959
    0xf061202030c1b0d0e1e06210c03010f0b13030809210303040b060307080604060903030b03010e0c0f06040302091801060b1b0601120305071b0b0a2109020d0f02 70
    0x241e504040c102400350620f2680a1030704040403031500740e600800c010603022000d4855480305c0d0148811072400c81701c2255a5841280b0100340d0101490703c042c03058804013201c12141e5883e0030144103c98058100348558540c0060700e8030003144640118050b80e901580c1c2034601824035007143e64401240d00109a519000010003c0c07034061500c0c40c1504102d401000e502031039507400e09080c03100c40e058000b0106e40c02035200010030850f000b40014110f41c400e41240000030818101d14040b00030f4004610215070660034102d02c1208510b000c58a40c1d1342400407035040c4c180c21486001d0180c0c40c0114800650700244e60b100158490100e0751001004e103950000004855442c0c1744a0462038101926285441c040c0300040b2080450401182d40074200d945001d68200a0701e03600104a48503418009003181c180c511046840110822104003524641200c15200d4181010081508028800801d10408495903200007142c0c14810320900d1600549842c1d4100701c1e40c1c81d00501c82c840312908a03000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433985449 1250 433984199 433984207
    0x90907030e030703170c1c09020604030b0f0f01080105280204030c0308071a0c27060408030d05100f0605160803160e150901030b010e1203030f010f061202030c 70
    0x640c002d000a14925110f5207407500a8079802c07248035101c0d440100080012403003001a114100c814800c0707014140f04624020031495018408075049000302c2e0f00c000c20b050014410f201c255520b400c195132250000b02410080e41c2e9031050700300e00780d030304c2518000c00010380d40c0c144100150101d41400c1030814180d40245ca07160307481d070f03404c10701032040d40c0145c4410030046186000c0001c80400254220304900010318141030141074000f00c3c3c4550401401d40170342a006000c90f031145600200b0503041c00400282e20790b03681e4001c0703c3c0ca03588042c40200c105480e05000489084000e241c8200352191601045c168505141069078a54401030b070b92008138000b05403441c006078a0100035485034900d14003c4810070583d1034042d090407103210354580704242500049064804900c00d481012800b4607000c03890a24500040e11604120000950482c0740d4030101404004000300a6001c0e18501044201980c1da400301032000c0d902c28060080011a004c6440c401100b994001d19008080d034080c0d1468 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433986699 1250 433985449 433985471
    0x62202041103070509010f0302070c090203060409060504060c230306060a09091806050c071106030c0403080d0603110a12080d0b0310060918020a050d290f010504060b09090703 77
    0x580e0b0022206000010f000003017a00d89540c2c0205580c0919609040960511200360f4074002411164003441007a55800700000d906903840b5000003444541014007006142014186800908075075100000403a1101032071043c141c040c00d006021001010500d0780c20341d1035800c00c0040c183d04c13604004040102801d00400c80f403440d48120311195004124600c0780d440d081c0b90803025601d00900054800b14180034800200c3d9485da000c407600701086901560300d646003094841d0600490b040908803c202152011210420303a10440540b405a154582200c0c6440204030341d14103039000301c136804562480154000740c00080030380008400306901048941c00e04000c20702c1c0c030301c0101c00403001903255942008a4851445111000407050042e041300c05115000300e01180043c0c0305150081c0c00d03905040041c02044943c03115503c1440b500d84201d0340e0040030b040e107800010f86500d04a545441d00000e40c40c40d042c458001181e0422051a0034003100108008500d00010658000e058880701e000318 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433987949 1250 433986699 433986731
    0x1c0602092404091103012102031c08150a0810020306030703081c0506060a0237140d020c010c060b01180b1e12040215090301060f0501020f06220204 65
    0x1a424900d45040741c44915101ca00400c0d01e4103a444845001d40170401840a840c5618a003051142d511361010900f807050310201c1d18003c2c5007210142820802c40040c05a03a5021810a000f07145203400492842d42007002c004404400c0d2080422640c0f00f004010941c0250b50044d5620650007002d9030040f960f80d81303403000281e1040744201004848103e802d51100000e00c00c09410440680e05d513820924a8103000e980d4a40404080c0000602d841040a800151a1111b465020b0000851001c02c400749000c2c01d0920302c00c2010307503841c010b4803181c2203014400a40c140c20088142d41d0000ba41c00282c94910040411840441c100402525a840d201003511640d0005107080c854041d40e900f8a002e20781c03802d81d107010380804010001c100401e09809800308041c0c015404a60105007101c1c5a504501688500e503070154055080103400501c00741400e050400711103082e0280c5190030310508901e030700d46804540d504c80e004542c1034246503011810b010b030600310b8030142000804a1960000c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433989199 1250 433987949 433987999
    0x60e01050108191d0607030b0306070c060204050a060e010f0201051e06060c0d0207080d02060606180a030c1805150d12121401210312020d0b0409031d1c060209 70
    0x55021145030521144261300b0045540e001300c4600d0100080d40345c07800001c0d03c5500242c802000c1040414544080c098907038111402080000c7c8060040c2d40c3e51075001d450b00301070451503400325001f02181082c0c2030041c0030780d51180c0c2c0080c0c0c01600c00010080c41c0c1c2244000500902e403c000203121003120303128204154600802c176a0020080d2600d486486071500304c05061a8007150840402d0056903180c04023521282d8a902e02c00492044d0f1600108661180c01c5c1d1000c0e010706040e05002401c180e41d44040b1040c1002d11100740700c0c5039a4040403048a03403440144a41000181c40e5540201e04042c0520101501034540070b4002903021810780103689070141780399940d07803503000104045484900080c45150001400c103803841c807580c802031700d442c441c4d0400304a50b0342c0016050050401a911000c07042d03600410400141e03195040003048030a511161080c18903d07590704003d9440c22014450900c900001802c00144003980d452011f50010030b0b5803904801441204040962009601 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433990449 1250 433989199 433989221
    0x903150501051c0b0c0c0f0601090504030801050d02061903020405040e0f0c010c02060d0e031905091914010c02040b06120f0705162a06020102040305070801060e0105010819 76
    0x104165050804019040d03034400030600d110f000501e07101000848000003990712440c44020311341c40d003600b005140c0c244991a080000540290700012540d02055403019000d1030080d0345481141c0c2c3c8402c1840300c1c3e401d00400180d405a424405003402e804d00302003826126900e49009420b0558443c04103040d01c4070340d149044550020304074102591000c014000b07c03a902407034000301c1e1100e541c02255180c071500801c04641525280c1144c800002041120300030842000c106140d0400c2d01c40041c1075420a000039445100b0440c002c410036400ca601220070742d18162031552000300c05c400103540c01e19003003e0490300941c03508040e203003640c0c038003000d02040700040d44107841d039180c456450020840000c000300e040c80340c2403083c010a0840507007440c20442d4840242588d5041000005580f660302141c0801c3c040240e80b4003007030503941900a0320840c1d02c18030880d41407503201c220b400d007a80d05501a0441c1c607072240f0f00400041d840313041c1c0315400c502d04501d8511481d041014140c2a1101c1001f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433991699 1250 433990449 433990451
    0x14071505010602030a030e010c05041a071a181606050a0c06060e160903150e0a0606150e120c0f01050f030c070201081f03030509010513030b04021807091203090315 72
    0x2c13a10742501528102d03401070380007000106502740001c0d01d140a28040c5110440078400c803520710403440c04c122468250041c459540c102c26000c04000303c0e00085400f0400c00703e00c81c285800d03504c8000f61000610040000000e445410325800f1034a64200807000d904001590500d6004900c0a1181201424428001a0b0f40d0316214003111160301d0300003014010405d00341c03000c0021980b060864111a004400040b03443d00205507054030f41008000040c3c000d0345000c100180b44081e6072181c0d203400326070340c44000700c41a2840402c400d850080d008a051354103c040b2014003481e00c0d10b80d605070300c03c0505005050000e000401081ea400c00c480705180c241c0000740c490107540e0400d6001d41c6c01504100130300450308000c1d8501c44a07400742d1000509002002c1000e056603130049042d24050f041702c0d0001411030f40e80f820040d500080994085c2d000d081c11401d44800208510f00d803030300c55442c40e202c298000349080b900c5c040316600c1540c19420880001404800901c0c07001c1780d020000780d4250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433992805 1106 433991699 433991707
    0x103060b030a0b0f06210601090b031006140c1902062b0c020a2103020d060923010f0501050309150403020303040606060f1407150501060203 62
    0xc0e110140c0030040020102455000a40c8020100c8050129038030742001c1c01121301c100b0320746020912600c00c1c0c840107001405041c0c0c2d0480c0061401c118615500c1c0c0440d400c5800c00c1d22202401d18120008100c0503a00001e010220901500b1582c44c0118100815a07580904101040468010150390081d5134442d1705965604904c00180c0c1001044001507003c60b00300004200360003403a086c585010300d4800078251941540c0001c0c0c040c0d103240c40d40a00d490200c0300315441c2c000c26808104c1100080c0203030141c2d10041440003004034294446000c0e110780c0050740311307a9005540785400100840c4d10150b10700c500300c079400c0c2030445d41d03620740000da28205105d50303800c034810300c9003a400e0004143c1e00000551103640a07160421449440e034504484602150308506d000440a03106c10400b00102401040d603c3d03c5008081c0249001003c1201699802d9200b0000b58002007 = true := by decide +kernel

theorem cover : BRFrame.Cov 433812949 433992805 := by
  have h0 := BRFrame.cov_init 433812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433812949 ≤ n) (h2 : n < 433992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
