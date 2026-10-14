-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:53.265073+00:00
-- url     : https://prove2.me/submissions/35227326-0c59-434f-b424-1e5725e0d275

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542446043 ≤ n < 542625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542447293 1250 542446043 542446049
    0x9131b0510170a0e10021e030702150a02090306060f0a090c02030904060801020307090b070227060f12120c010b030715021203010b0702060c070e0a02130f0305030a18 73
    0x110140c0d400011806040c0758a142050300b000e40da00d07400504048030034070803c0380380380f4410010601d504250180320003d6115948100350416032160100032034007080001c520a00d11940a000d458080c4010002c8800d8068203000c045401804070042c141c03400035025070b0100c4210f460341c0c81d00c6081404154000e03201d400134450b0381e0610012240558002008000000d030649040100359603d4400c0f43c200c0c0000d9070080001202d0020400108801c00007074046e090001300039081d44c58079440f003500c803100329113032400018098000704415442c20a0780b01002d80400d0f10401c6401c00604074994940d80c0d5980d0909040f080802d9180940009503c2031804400280440710a5911186890701c10614003042c40018450b0000380d80101401d1016a8102c80d07403000e007103017403020075420801540c104a40080c214454500009076032a0201c030405d021700107001e030050b95801001d80d504521030702070704017014803181c070001017001a600208403142e8414a1905001e8070230081c40c21610400703154 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542448543 1250 542447293 542447299
    0x1203050a0b1e152710080f0a290f10050301090c09080a030905090a060608040204020c0a0c0308090f030705280b07054c0603061803020c09131b05 64
    0x1140c95100d40c52044080001c404121030402c44440501c400c010003040040305210000b080000455000d02420302c0380ca400803496080030507090422200e100c0d02c0a000301c68001c0210190019022718240942c0140c040300080c1c82111704907038041c0010306144018825004210b40c0c3c0c0078500c12051007078130f003a8007604e011415144400950b0400400e080824081c042c0306050036404981400c4c494840d6804484064403440c03002d60316074003040029041a103086205000340c1a50700f000810705c20315800918410088182c844180d102801601100c0914040c082e600c1000c00b446030b41c5c0e4091144880303699070710003442060281502d03d40301554592020400007004103035181001030103e071204804009421b03035503954882040170003898090000d4600d4603288112800000070340301c2c0b4648958540701c040490138a903250385140c219032074042c421041520a80803182015418490388081c1c0c1d2040f15807080702c0c24120403880701d4108686004241e11480428030341c80e80f480c4540e01d80100303001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542449793 1250 542448543 542448547
    0x1d0409080705010501140d03020604080f040308030907081e0a020d050102091503071b02090a0e0304051c0c0902041d09120a030b10020f0307060e03090d1203050a0b1e15 74
    0x140c50443d011308000c0c000e80f01101c160701512460f90400195094509406500038200343e2106d4554034501c0d80409481e459601c0100808400b0400030340c01035014408140040c10780303038a01080b107801c04e030740f08445d45107120074200e03840000d07000041c0c00402583c04a84074080c003c1c592500500a20074540c4564216100b00700c042c2401712158061442019240c44a0000c041114079180000b8407240b0f00a40c01880a40420260600c61b4001071810200c003040b00d01e01502d99000644490708070320000c9040d00307411407a5007005202c00031940109000c043c19414142010440c845541c910015040780c20b600c0d000041c0b144030304010f0035402010303c0d48190350b02c400c040300050180400c901e101d40a40b59208240491a10000d17502e44074402c0760b0040d44c01e21100703235108006010368000380c440510052100e54466500c0b40c0184614030300c66042c6901e18502c0000207000d8a000504e6141c1c400d00e442a294540c2c1c0300e5100000c100f203a01c610b2001e0740d1088074001030800c040d2000040302e0303440c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542451043 1250 542449793 542449807
    0x1103030406140912150f1b030103061e0e1027120201020d0212010801051608060f030c0a0909050f060403090e191d070b09030706140d29101d040908 65
    0x320b03950503002c3c03a440160604695581e24682285000441f40c3c5c40d0144070420041001c21120351101031034107074941010880e14600c2d000182641d580c814110581d070420901c0c40c5804034240b08103420b8200c4500c0795401405028481e003610b816110029144200400b41d071a1403c2c400e504562203220380000c11516240c2041000c80203030301c00d000702c6d01c00350f1a08000c034060715600008400d8100ca569504040c5603510410300c044240384800440d01071107400701d4100656590400c200c06405181000500541c1030700300f071850825541c0590702c00d50058011712001c25071110400043d90305840122a00e6240e0045994403219602481c0c1841c03803422100c42a4146040c443d600c007505408103d0b09041c8d1194007003150380c410304000701e074950321a220400460b13000b541668a801d01d0700c12030508103ca00496081034a01c2420350356200301d6045c1e402c101070704500c0c4d011900094161500c403200d01048078060140c1c03c140902045050a07103201c0d0010342c1d1160012040d055201d0041d0f619100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542452293 1250 542451043 542451073
    0x1d06070e03121903060602031e09040f050f060a0e04030210020304081b100b040c0801090b04061e05030d080115081005041d100b0d030305060312161103030406140912 73
    0x280f101500700180c14400009405480002a40d0501032000e12220f15210f080c400320b051603229900040d0096114440007065003040d10816125220410000700940b80c45010840383d00f004e074001c90809804e603c24000403076800511070b441e0906400d001a81e940300e6040c4044280070b4011211040380400c6540030000c0000f0801d104103420340705003801501d00c200c2c1088162030010040300002030801e001005085015040800000406080001c1c1991128070022590f40310709141c80100480c401e003040203040400140c4805080d9161000881d410f040c0408000b07218206800204030001c2e01040300c880c02580102d0090400034010407600d011090101e08119a10740e4a417502e02901c1070102d110501c0d4065800505401001014129aa564181c008090207000190140b00b8403410402000c7d00400410350555112101200192949001c42d82c918296800c1070003a082804100601c42d0002c0d10001e54240141e141511096440301154289080c06040c150b503100e001c1f034201501c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542453543 1250 542452293 542452327
    0x302070209070e18131e0b0c0403200d0305091807030e010609050136020f09040e0f0d0318062d060501020a030e010314090f011d06070e0312 62
    0xb602a50721345000c102d91400340c000e2120071079a00300402500300360600007031007500350315084650004000b02c202c1b001da11000154002101c50104403800020300b442032140d1051028120301005c0d003616031106e42040843e0070030700125002818444081000c08890703547c541020780022902c4940e010919010301d00034050500034010340565481c244020400100500507141a82d54034964120000041c03081d4540d0445103044000e00c21030700c0303060035022112500040100400c80c05025072512035107030402088071030700104000c256010450500c080c400c0070540c0b4541c1c5019040010308100c2a950f43d40802c21600d0317004101c10b04e0450446503807016400510410040c5039a4850390b42d68a02401d811150300d801854003580c80b000901000038840d450b0b0842d042c4040c074000c2240740c202280101450429295982580c00400d411401d5076424411a0518005441aa1301825149040329129034000c1c1c801e01c02c101d82d0031040e149d1510b040083c0da07400c0301d03c81c240d26550380c07050010220030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542454793 1250 542453543 542453567
    0xc03020904060f241a030f1e040f120c0209010902030c0409050906150109030f060c090503010f05090d0c02092205060a090c0b0a02150a1104090203150907050f0a030207020907 77
    0x2a850000d00410b902d40801c00081700d40300c01505142c9542c403501d00b20014010010810a500040701c0c190346a9111003070b5001e0300841c0b19914021000e000c4c1e20b00399108908441e683d00401c4101200f201c0982d862100b00c90445042d80300c0141d8030f031078030465240188070780d07080390851500309014061002c01c001549840b50020100e840344c04039807003004485a076840d12010b0400302072942036501141c0103034011152003042e07081c0b80f04015500c201003400d403092005100c0040359030748100702c24150180a814001c26440c1340083c02c0b0480f036070000e4030f0020050420442c5080c00351800c62010070324076129080720340041c101c4500e458042c40002c0603007046035007220007072000e41c1c4c001820b07028a401d540c1c4918054002c1c1104c0c1e09514124244040300a00301c00304240c8541e09114940b007050300407c090840c02c403016a1340d20300a880c2040c82a20101d9840c00b0340c102d1402c02041680c0001950703c21600710344125904c5404400440c00390040a5010354002000e0701400030071350300310501d0422 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542456043 1250 542454793 542454851
    0xa140106051c0209070f0210020a031503030f0905030d0917011d031b030310090902311b05030103031b0203100501030308090105070e06090102030d0e0a030215040c03020904060f 78
    0x4c25030342c0e42c1046400d44284001c0030050b920200c0480c4490400e50081d020142d0503190000e00c01c10f81c90951012100303240d105a001c5403005604000c4180c2c04070080d4042c000c241c00501d500d805182004020180c50b10503035080c50021100001240801e4001c0c4a50442d50344c40b610620946100403a1070368481041a031445140c441c3d014900d15000c0241c91080000318100c0003500e20301340c084005041040812640031959412180091035010f44641409401110303405119034401c104804031042c1b99005c88200351040500680190f00c10203d0b41501d9051400351500122141010001490354400139818090f682c0b0500001185501090490380079a445000da600d40e1036410f404c07100140c80020000d0100d152280041c01e0132001480300d034506204691500712602c1c0950111010f03090b034650107401000c0d1581c14594108030300c00140c17580d080f081c0c18030b042c1039860480540071480007d0003400c0400c00101404401d5103c815001d01d100000d208200405203604521001a02d501c4e003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542457293 1250 542456043 542456059
    0x1302040b04081f090809060705190b090f1c0f120e03070204050f090d0f0c050717060c0309060601180e0a051b0f04031e021203070203011d0a140106051c02 68
    0x3200d0343c40340a454400ca800000c0186807a0b02d501c14401c0c56480a0b000f0344040c803e4803120426000d4042c810011940512030500c07041c20412501810700101131034907165540011086000081100c1800d246240319040151140300c5202e01514020611600c2e500981e01d04914562400b10102c020100e1b00c3c4219010005030340c90110071100c0e00f03400d4680480781d9000e014891500d5000342c900c902c80c4030042c20589403114241c2e0300c041c0751001c00c1e085100345810a41c0c014680c080204411500039118180140c00c501c3e1070041e00340d0301e8034020416030400003841407280703083d0b941c0d440650180510b4030a40c1a130f440c4c11207104000c0e10707041ea05080d80b145844a0090000750b1402510720700d060260341d0074a001d1440c0c407a903003800541e40d80314a00341c241440701c0c07005030744103810402e82c60a95405942c071200140109800c503400c020a10a003100740c051014416140403030074150441e40b04000104461180d01709174014407854202580045031640f098000d1444000c02d451a28800c80d4050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542458543 1250 542457293 542457343
    0xa0804030506060d054c0c020a02010c0611070602040602060603060a0e0c09060a0f12060b040c0c0b09121305130c05090928050405010e0a020303091302040b0408 71
    0x280e081000406009a04000501e0024490200c3c5074510945450241d2406c01d0086d20584054080700500c125039906185144a400c4154043c1d80440e9116002415940c00280c001803d00c1e090340d02d005103002e64800c4015802c0c008081600e1090350801e004645998480794042e50b6000705581e514400d210302230008010107814007900c44079a403810003070560040f038002440061007000d04000e42c007101c0c030a0042544101600c00b00300400c00036400394036980b8541402821030b90344490040c00b860810015058841d0451403035041c0c16800744c01e04061b03541d20769001d400d017030003c4072038058104002000000444d0880c05081540c4040f1501224481702440c05d2007241c00c00e0044601155051002080c18500900e0040d0311582c820b0071002c072428010014000008103075005140242c0ea0424002030002c2486002c2d90308201000502c50030006e6000650342e805452146449482100c808ad80b0621b21078040d0f03001010740c1070161f41c40e03503161420b982d1201c00c0e051988016030500304000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542459793 1250 542458543 542458549
    0xc02010809121b0708030c01061818080702041404030f0e0603040c0e04020a0e0a0606090b090a05120c040509070501231903060305030d0b09091b0913050a080403050606 74
    0xb484500c0388071640c0c0380c403020041100d248048104446041e0180040005040c0403d0000f0401d0441c0c640000600031705090984500444640c02081d94a192030718500000d403441d482045040e800c0104542c9400d0741d440000c01030b09440c096001c10b4401b110a00081640082d01c240c8425015120394140d441c20a041c00824002190042c1507150103480410105c0c03000c0c19210382140c005456141c82c1c0ba02c4403541e000f1607000780c42503d605a40c444041090907440003400003d00070520446160064000020303512441c1805158800d500c0b03010150280c410422882c451500050024400c0340b61030340d2402c0e141d000503c515408210310758551030240301480d03a000054400c04003214140308207d000709c0c1c2041e1444c020041072565500010010503c10000390200c44617122001c1889980038040c006170382d5010b0b010418035440f444413811110182e502151074040b003526003480d29500c91043c0c007070116500801a00b9402038500e402c090100e00c5001340143e901030b0b4200d60a41c1c0b00c00042c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 542461043 1250 542459793 542459803
    0x703090804151e0909150302031c050421050c010203120708040201020102040f09050a14012d051804030207080c010c02190e10080c15191205070c02010809 68
    0x40c101030007000140700701d0105020070030280040c0d00d0034490b03e0b42044051040d00b880c0d05681d5000ca61032410810812070140500c1444110490500b4544c500d180d0100340d5400c003030040d000d0b1317041400340d9103240c0c64840e0003074034001c02e00503030441d13440c21072180f007007084d4014104250f849000b0044942da0359400002110740104225035440e001d82e8444100320703003a100180089045540030000080d05a00b403551b0503025140f10640001c80b0b0400360284801c039035004460000c405003100040051824540000e01d4003403040c18100d18841080090100d03000e05600138030303071120000880443c420344002529226501c01e4080b1180c00e6207400c6126920301030040c0c1240001c000c02c01010042c104030810360b9624040e1211004110707141e144a040300071085446c1026600903000400070080704102103a4144c8054960509849020862008900c11940400d06072040d1640c50080c1611604404100140001081081e800c091100400a050b11039090380051440030106100d0b00740898 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 542462293 1250 542461043 542461061
    0x301030c0b0c0312010303030c1106010308090613030819091403032a06010b0913060b03010306020f0408060c0d1d060a0c0903020306090f0105070906021b0f0618090703 74
    0xd8a01803051030040740700056801826103860a01003440188458a80954003078041e42c4291404a49012035101c0240052001c502c0002240d205c80e004001050490045070303414a02541e19542d62a0a11a0722810a00c1503100402001002070441c0301d81401c0c0004050181301c0385d6a041d0941d82d80d161040903111100246d99168004001030071004442804044a40034072050140c921040340c441281030641c2680000944000018000078625284c0c04600340611484810080c090818a20001c1404140001015184d002070321030405081542514011701482c011526580b50104203140d840d017000d00080c00450400c000014a940690f0440e4108003010f0020f129558600080d40041d0200d040d441090103061017010026884c14440c0e18460b410380c40040800701d80548402d421101d0003840e200802c609620140b220941c04542d0807260f4100c45095082d04442e000040c82c107803501402c3c0b80d806140052054003034054100740580c008402c441019240d42e4034103040d0b0544c1d040803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 542463543 1250 542462293 542462303
    0x3c010f0806070c060b03030703030c021002160f0c030c1512020307050a2001020714060912040306050714160611032208092728020c0a05010f020a14030103 68
    0x1d00040e082481007081c0700c1e8484c02004007080c814440300109003945c0c840c00c402d50000b61640001490150104400d01c0c500d403440d01c2c1140303030641c86001504420b503400801411780f40b0000d040024400001d00c84005035400c080b074030620603501c422403900504012440c2022490000d086180b0b20598030039a40f141c03015458103403810f44d50100885a40750100341e40c0703403003801714003031039046100c01d1010f450840c1c864102c1d100c2d81091402c1072498803100a08281c0694041007181000700a11010b641c2201c0d4800c0d0b0118803501e4540c4296140101035141699981c800f0888100c0744101028400949004807801c004143c00c1241da4000351000b1a101007964000d0320741041402d00ca4448403d51500420703066050566100001d0b100040650990403030040521018001010300800c080e0082062a00d00c20441e5a0b1003807841c9020700d02d60f41c1500329601007250404181c050242d04101a03110b8020404020924150002500544c40f00000610301c1008841c00c01306035000c03a41a26000303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 542464793 1250 542463543 542463553
    0x905010f0605130806070f03110301031a0a02160804090e06011a0a050c06040c080d0503010501020c010e0301090209042f0d060c1823030a0b0f3c010f08 67
    0x41e01a00d490707020b0501c03c54080704500000031665414801280210300303554403a12804101c0c9001402d5402c1c040040c0c1d44040104010030018180c0c0d4060000100300940f06480f40c3e03540c14a04009010ba04512980070b10907491800410031450000c005842c2541000c00886e14007088683d40caa801340100e4a5a0981904002c0c5242c0c0020140602d200e071407038140d19180c84001e03006c0c140041a1811150344c404600e043c41160000d0200240c0d0311034900d03096080d1340c5030400007035641c0000c00021b4180012a180b90416032000e41003803041c903402400e03510b4103003072500e440704a40c007080e04c65042e03c82000807504061004030039400e05a03800104030042c0c9a100b500d0341c100800c0384607805020f101940b0026401c401074541c2c2d0380002c011000300c00c03000d403ca10b804003102c8440000814401d42101400c0e500060340e0079030142d000940341044141c070f9502d0300040080c5114402c1c0002e500e48242c0040d21f20340941035014285090b00304004d0400d079a0303980390110f40300f501e40107560094200d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 542466043 1250 542464793 542464799
    0x311011803141801080901021b0f010b060f0d05040206090d0506070e0d0215130e0406060905060a030218060604090e03040323030307050309210304111c030e060f1b070905010f 77
    0x200301c0c0102c0e0486e070060001460040007029200c0030440c00111742c3c41c19004001d1001c400c040070320403912400000e4880c00e1804030403140303015480c8100105480c0c141c2d6544085800d6407034040030f07640b0410010b0481c2c11f2240306801d1180d0303500c9040711010000f880c6240d20f00d50b503091a81c0038144003680548050488144468400c402d034000b5041280011940b81c7c00042c42080c4e520000e0040d40a40e600007041c900f024080f0040d02d40090140e40201c980400400043e00e80301c1c0300501c2e16012030f203440c003152155000500f40380b0481d844600030301d0030500c50020500000c001001102e108143c42c26010746a00c09440f800e411102e1a00c020750401d10009207000e02810046500c0040102541c01c9100c11b10300f03032030b01120301e00c0c030840e03450b01d02004100400914400c044d040100466081c41d082c8852030491010710700040000381000201404a4055103411040d13540b6500c8594a240d1204560641c192400c181070391200914030403041c00041d00c8415100d6541640ca030754103448c50f400d003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 542467293 1250 542466043 542466047
    0xd14060f1809100c0504080f0102040b160309080d090f14030a080a0e0303030a0f2004050d030201090204060e04050717030d0b011b140708070e01120311011803141801 73
    0x4005210340c519016607181c1c8040c0000911580590f02403503114a42c0341d42c1803001e124649040e10789082444c2c1c1c070400060002cce602c0d8400f5191411040d00c0c13102d04403c80d5260480d4601740e10b0340300c01224801c5080c40424241c001c02803030706994040b012143c03a076640d41c0e60064484118011180c0580102e070009001c00d141c00024030340d801e01414140e0400d80641c010920711742c030449114003800c0c2e0780c0b0a03042032842c0b03a000701c240802402e40d00c122403030007912011806100324800c030352040c0c500d10000c5080500039041050341580060042004e0343d40c884e02410300c10400c40701102c550180c4c04001c10030381220034091003281517880003103003490100c80840005220f03541140707042c041c0e16442012840134a541c50b42c0380c0d501c030b005019800900340040a00e0300d211a049040e03203030083d61040c4610882d1a443c43e045442c04001402e041c6c40030b06050381c0b2444045560610b135400c01410b00d4200fa0300c41d000c07040140c440d5480d0508040e540006100c14014410400d5030b500d0a054000101c2d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 542468543 1250 542467293 542467339
    0x115050d0f080f0a18080a03021515031e0c01081905280e010b0d03080f0a090c060e010e010302070203061303030e03070615051807050703090b0d14060f 67
    0x50b204a0700646400c0f01c400b800609600800310040c006003680103a621004181055480180080c10040605034040d503006500c034424912408181c81c4076170001220b1030140203c400411001a060314090415100c0200f400109082ca2600f03510a40100318000d5100b10345062084054400344201e06908001d4140a004042e1950101600010040c0001c1d2400600f40e5511281103200090304418500340d1400e54105030320b1244038003801140880825004003400c2d912020381d080c400103039526045000003c040c8005c01400010980c2c402003a40350300983c034860052001d8a036500b040900800440682c81810f50094041d08418045000105001172007001e5a10170b050105080c10801d00306883c5800c84203040d42c40a8170352134032240740d600722080c0c50050300b000d84140c040f02c20940130051030243c3c090442020460b000596000349480343d405d95000d000160400c560302d007101c4c0da45101418444040040c2003d00c000402c0fa1480c15800070b0104000c00303440c0c0250300c410007441134131170 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 542469793 1250 542468543 542468573
    0x6070f0c02031f0b130506060702190b0f04030b01120c0303050c072102040b0405042a0e01032001090303080105063f3603070b01090e0115050d 63
    0x144100e0000c00e5441e0710081800900c040c0340f00000a00c00850000c10040c18141c10380e0b0001c55140805012141d16900c0483d0389064050b0340c0d8802c42d181c15401d10100c0d004907400f4170105400811180b00700c0d11008010800c907805025070100076602e40100007058605503800900c00740c1d41c66010800203000e00041c0030160041703010703907410603541d1080150908041a0326443d40d103080c05804118a07191040039859401601d08024514040d600c14000d03410003d2020b46107816101030400307109120304080060308003102800c0c1956500d1802d00300d000d072038160b00886040d084009413520351141d80090200c0781c15a8503003040340d181400b84038059000d074804110003d103401480a51b001c003520611038140ba54140029003014501404111303003c058100100c078a02042101d01c841d0030040640450207021440031042184851164a9440381100c02041540c6080000401c0703102988940c00014824000307103c004025007450250036003500600d54883c41400c91903011400040c0c0b01c400d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 542471043 1250 542469793 542469799
    0x90c030a030f02010b09180114060a0504050c0f0a08062b120c08070c03030f11060c030c31050103020f030c030c040506181c0f0209150d050307120206070f0c02 70
    0x50f20f190100300c18000071140c100c80341c140f0342500c7c0340d444030921074150240242c007030804c001d007844030004401d00098803035188a1a241d0020400002c00c4508582041080e52030081c0d50780c2554201404a000407241d4600c568440b46e1309148040103403000c80360111401c010100c042c1965039400700701c804078501c00020084080040c100146044004245481c00340d20000101da182d460300805142424038881c04003c0d1043e8601440107000491980000c0401e0145480741d90b0021034200c2801041800000c8a041091440e40800072420320401e61250303070303000b01809440303e0040d4140d11410048004c0d1090820000304d40d03c1110024507000a00140302e02c4c54503584100107101600709000c5e410341740a0411130000945840820045840d4907007004480c084059100d880d002904018041e020f000e000340003803600300d9400503510781040004c0c1001c42100040c18001e540c0d8100340300c1165240e5111814004680c00000c10707500c00d8080e651940551400f801741103568410000c0300b2a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 542472293 1250 542471043 542471051
    0xc080d1508030a030207150b1c060b0d060227060405120a0c0b19020a030909050a060503030d06050f04090210051b01020f0d0c031b141201030f0308090c030a030f0201 73
    0x50340c403605200034079a203c2c0641d005611203c95061400c10f0072800c000fa030408916011030054070b62180081f60180115403a081c030800c000d9420401d01804884005c0b6034041c0032940810200503e070745c054040800c8055040342e4031402c500f024aa0003001d001c0040d4042e03800c1c801001503140c0788183c90041c0d81014180c40c3d1810403035940f20796008550f04101110342c00810a00c00a40080c486403201c3e00d0244001c10b40d48507541c80250140465000d9881030071b031a10f001031790f4a1501c1c0c100c070005000190071a651034104803400c10060403203010300e82c03245e1030103500310485203000d01407410625001030403103a0020b035110301910303141e01804100d040e5030510058000c1041080c03010700001d000700f005d00c1d9a10014000118104d43c1050481401d1511b8021450303a81280703254400c080400c42c0c10011402c00b440308510442d4000d5058040380130908900110030084034800e1510494466258401e0701d44500d596142c2b20b030070f41210a50903510144409000c6485600398036040c55080c00002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 542473543 1250 542472293 542472299
    0x120010e030a021e030918061f02010204050a0504051504020c1c021b0102011a0f03100501030f0b060a06050a052104050d120e060a0b0109080322060c080d15 69
    0xd0440d0041c2c580403001d40c002e54403000d00e01d140251212074601c00900039600c6c1102d20000180341000c0765103002150384100d800a00c0c941c0302c10a846030011455802c55030b5017080200001c2c00f079800740c0501801044609030026042c1028001c407402407041d541085030111521003031000075044211003400522864590042d803640c070290000c1413150a6024100481c426100032884540035078081d811a0b240860003821003015440da07480c00442250405002030451002034500b128500d50720061500e40000081044105a04c5408082c40303600c01e038200342e54180802200d40b240f442203001140040040c0300101c1d100c0c000500c000d814010802c444034120300b60036002c1940840e801c6441c0e511009600c0031450b0003408200d01841003030300511105110f03035211034a824000d014034001503103580110702240c0c01007403000080c080000469071034092480081c01d40e80c0303c224800240503a5010b02041d03e520800e0300d0b408843c0c000314103501c0c00001d0b41001c0001c10380480d00d0610315074040404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 542474793 1250 542473543 542473571
    0x8070303021c050604110f0306040e0c041d0705010f0f030b0a0317120619030305090d050d05071a06090c0318060711060a0c0c12020325030f02010b012001 68
    0xc0c0807880b18030038001072a2800310700b80811503d842046860f181400c1c01030184540000e070031203034001c40690b008698070006400381442d00d5130b4940701c607070700c9800e01e000480035115400b88032000400100071600b11390390360390054581c1c03c02c1000c0c0c20700042640c100a0b81c80c0c1e02a40000b00c0c480030181c03015441903a20344402040d00c10b200c49560f20101c002480c881c14500d0440c582d5001001151410981403100e48401e00c1041144130007000d008020a0800c00c61391100d20041510380c220007500c144085501005040b0b1741b0403002104c4444645101c4403080c000c0000d2240300710005000d42d6070503140e09121406039000109580540c2000c84401c41c17903c030703041c0b00303039400b03814280c503190404100602640c1c20488028848465549460101d02d00140e0040c0202c502e90303040306541243c456902822400e40c0304034888903007040404020072802c0e0381412540c400c414025510000b0000710101e04030b003640c801805690004400d61201265120401030141c0e007245000c0000400e07286050b58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 542476043 1250 542474793 542474827
    0x7061b03020d0615270812070b0615030109090204020c060f040b0106180506030402061b06180a0507050108041b0b03100e071d180f1e0c030a20072303160807030302 72
    0x144410002c80030920004201c0c50840031500f200c0b0454040398428bc1a82d004007003404140300b041c000740d450320000c9096490b42d6040302c041680380410f40c0c00f0380c0b4145150005225068400b11241c515100c00056403a120b508108111011006c24101c85441d25040054540020b00240e034020420081c03910b1900440480d00ca40d030079010094003c40c541804858820200004040a0354100c02d000800194010a03503105a850900f0040c4a40d210350401c6507101d50101c0091502d940311020100e114540c8030081e40c42801e80940a04805456000003100c400d81950028003103850300310f50048203800821000d0081d040039103028540100d21100508038142511035288419400060203001d03044501202405800c0300c0c280219800c0c004104003a510009280845003070b1381d695585000d899010b80e542000800d00ca100e034442ea05030624401d1924500f0158071140202036007803210300004405da441c0c58034009150b45801c80c0e2615004407030341c03000404a08040e0b0030412515079071440382c0f07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 542477293 1250 542476043 542476063
    0x1e151c0506040507140f0a030213080a0605130b061002030c1603060b090105010c080f370810030201050325051b031e07061b03020d06152708 62
    0x202180a0800c503091004070340e0050141c10800c50030070f4080ea502480c00048900b00d80a411209507034071a92031084000b4052100d260b03955a13005100002d1f0424009030f11540b0f94052902003000c4c0d1944043c2070902400c071000100344044d410002034040c6000841c020f416081401920b00d0882024107030340c02e140c01200024402030030040180b080c00704a07c1617005043c4161009180780d4104000685180804080207100c9000001c80030f80ca0341410301a501050b078481801109250854600fa0903840c468440b03d40f200c50038403000242c40d210355803141c050000500003144007411900111115070004201c0c01c52164100e2680d1001496500c1300c2132040d02a5603540d40781c51000d616421070400f201582c0e00d9507401844240c00054a5400310814021242985590f070500d41c50140c2c013a00a00244401070f07401884210ba0380703501030f00100800c0c810054200051615040342c0b80c1c0d060517504c420300000f84920300e090151151104286413100c2c01840104240307a1382e144191030088100c13 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 542478543 1250 542477293 542477347
    0xb13030c21080a0207050c1302120411011211160503070209090703030f030501260f0a03030209030c0114070f0212060106170901230c2101060e1e15 65
    0x40d541200d007944a4000340e00300502e42d07000d5107442c5e82911500c1c2d880000fa40c0c151b120720780c13400010344040810307411240c41d03440800840e141850581410780d40001c040d0000b5010400a0300d6001901805106240710380c0d511010f118100b40469100310400284140d084849102c10809800503a0b83e00407520720a0342008001c0c40e0203030540c9002000030f20780103298010b040c10070005000c5074440094910040340d903d9421159a80c02581907854100b910744030260a00039130102205140e499002003814050a600321051102c006004450b0040501200c110b85042448042e00040035040141c080900040c04050304180000100d03041a50a0b408880801c030f01d844082c8403506144441a4003443e040001c0003084002101005607070f4001900c0d600324801c400c002500c1040800546a013440c0e480301d00d680c54007451150a0340c1c000280508030108103429103030305580c0f41c6102140034519440c100c40c800e401c00e00040c030840701c080a20540380250f082c000444000700703039841ca28400b6140c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 542479793 1250 542478543 542478593
    0x15040f020c06011e0806060f0d1b05011d03060609041703010603050a0507090302030618120a09080105010e010b2212050c010806120318040605150703020d05070b13030c 74
    0x20503280c1c01c404d030b800103655000400030034041011703110205482e5803000040e980f6599031407080300041d98900584d880100490700b840c0107030300b411413505801c40640d8400c0e22410b03c10701c9d03034440881d40b50b00c0540407958140d000400207000b03401c00c190040d410034440c0e0740501e090070400d100f00e60240c100360000300001ea41c501c10081c00140d9800380c0f0350403200a045c0500c3e90750841c1c021a80303400c8001c0c18650444401c8003c201c05440420010300e405d01c0e01c0030ba6540300c040303465004010240780c5c403a005042d0f08040001c51040b40040c5294125000f5030406840d01d0301e603403014104900040d1039230b1005003c00c14000392512106030180d45491182c000b900306204003400150424034080c0c10300e070044490381101507041310008200c990a141700a00007010440c4000024042c0581c2d411141c0c011014001d1290f0402242d0042c08015210760241d0346424a1504100d905000e085c1020303200d81078440114000e1094200d1011185000b8035042000d401c10740c40b0001c0c0c0240211200b0290a14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 542481043 1250 542479793 542479799
    0xb01023702190e0a180c0608040201020a05070609080609160314120301030c08060f010312031d07121a04150506190e01050a05061c050612060708060103050c090915040f020c0601 78
    0x80e0740300b9036102c1e0b645c10700c0c0030903554415102d0000c61880360084605000c0f0304000f08056a00800007002c41c0e80d405005ca641070380d00c4040050501c80300d440350310f80354820080071a50094021800b4003855424604078940c581c81d58503000704124070070b00584258085c034100030001ca02480700460285003d4007010540e1440d207814103150030b50042243c10700c50380d10801400050640991001c0d172602924001c143e1400340c0d0000070038205007440702d0362144107031007001440078038582a00054a000d03d14020001c0040b0102901e0514100d07001021442800b004202c21100d9501c4541c1242010340b2105194452440c0c1c40001c02e03d582240081c0e91108004100c245030042c2c8490280c5000da9005081034100c00070f01c07214100d400800c131003103500c541c0000d629803100c07100060380801180031121503081c0142c001e4009003051301c01038002810000011100c8402800701c803400300700070304840c800c2c1c0d8500840c0281502403020042c0d02c10f482d085444401c082c00d0000d46034140d01035000e0002945 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 542482293 1250 542481043 542481061
    0xa03050d0e0f060a09050127140a1a070602070606170c04060b0f0d0e0319080406110c15150310140105010903080d0203150405010602010b01023702190e 67
    0x44520340c0f0540d020841219080c2c2d000410078201c0c0c1c0c3c00e0030001e4922000e0311810314421000c1e404c40400d8400b100c0e000407080500400040484c00a0360310401c0c42e0344a00c103484005840d0007282000b00ca007042090001503066009260f4680642c000280c80340e02c81080c8003403c80314424206495000e142000e030285007034403e200080040c118060310b001610700a07050140150074422185030750b240010039810710144210303201417000859468020b8030a41e4041c0c43c0c81c2c403d9405440b000d16041080f0403c128244c111424261024010003c5510301944519042c800030b25603441c05031200d4032840303130f500d0030080b030312050802d81c0c40419610590440a444203105078400703810403008250402c0410610000c80704940b071007183c0960307a6682c4605400110121840c01a003240ca0800001102581035001e698849426801d69807860150050008062080440c90303003607950b200801c0500d80c0340c0c07040400a032840900b04013150b0100030b02410060001d54400d070000d41c008020000900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 542483543 1250 542482293 542482309
    0x617010c0201020405030705060c03090d080d0c020d0507080a09080304120b06030a0309060c030302130e06030d030c050409150902070506070f03112703060108010b0f010306031a060a03050d0e 84
    0x41c8000c42c04c0900c0d10001a6580160b481128050796002649500407030061080b611011800360911035105014034003110b130f0350310405114500d43d2802a034240c12500c013040f081c607440c0c2146d40311400c15080b510ba1544a60001c9892024011610000601c0c48002c0c0003400090000b0701740c0300c0803ca00340c00c182c0c03080f02000b02240e110350014003000001135000980308003034136001e203040d400e074070001c3c81e00390300038441d0000b1419004548600082c100d5a039146c2c5074844e120a405494141092109c2a4250380c050a00766010840c144800d21187e20150b100d0403107506c2d480202d1503140d0361040b0b01c40c00c9a100d04400d840c03d8101c04108842d407604403500c00001c480d0380c0f5007007015a0b602c8100580902520390540384400083d944454048162009144d00c200e0050507201c495941e000000c0c001c00301c0318280d070b0140301c80e40d40b528550760091251908894118061000d200107045003a45107007401014590721081945000c401f08508001c8003142c503460b0780f200000001c1e00001c0040310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 542484793 1250 542483543 542483561
    0x6010801020c01060602160303030c02030f1305040f0c0c0b070c1703010305060601050415051c0c0f030b0105090a090c030908130501080f01180b010203160f0b06062a070306061701 79
    0x954043c540c7c05143c3c104803119072044a800d0306d00081d07504840e00040b4214480d41c0c00c0e4420300900072641c200c03400c140c00364420851700101e600b004040c549495a0007900d840480f80f00c04a11012500c102140f4001c0009502c08890710309241341c2e140998500048100c09a11a4250362010005100700803040140a400c03803c03d0815500b860315209540104001507100b0310108200882c0010310900c065807048030200140c40280007440b010301d001006580383c500f03001c00007403d008010704036501802c00c58184c00d9004d0f00f00c0c51b8150528240c50054115010301608050f0348400030b4012540c03140143c0000f100c003106201d245131034074000415444001c2c0c014000400394400401032001c00711603241a82c1812003010810412000040c0d007540100d00c2c001402040021500c01003202025643c00740390b206514121950700d501f800c1c030201d809414001c06950b0b0b4140d5030003030304d1703500c817411004000c6503002120500c6071241c1e144026144168001c419001001210401f2007000780112041703 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 542486043 1250 542484793 542484797
    0x50d0803090c0102010e030d2d0e12030709060c050307080c06041505150d051519060f030b0c0d06090204060c050d08040221100c05130801060b040b0906070506010801020c010606 78
    0x4140340f0000a07100c0c8102004002c1013640c030404180c0303085049208081d00501290000c050301c1e8401c012708080d103880200ca01c0030b0b0048001107080d4401300825680228090342e1011fa815050a2007602d288050328015a40c44c80203004450000d880c11000305070480345440907080d282841d20f400652229648018581c0340d0078841003101e40c180a50707441c095007408585513546848203090007070030801d5003048661100c0d198030070410551503403005da44c00500014010451550383e03001e40c1381d07125850b00006000559138004900403c2070400500b01e00100c0c15000074210b0303035030130595040b80d105600201c04100300700341c0b2001340201400840148030b03503402c1c80303d901d280c01e9000580e20343c480e0345c1180c4c0c070160070b06038801808020044030107103400d0b05a0400036a0503000f0050116003141510301a0f02d1401c40d000700d8036207010700612080759411060213084c1401d01d6109807940d0040603447d0b8100700248240310105404014250003000ca4800050b40c52401f18011829582d403a003021007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 542487293 1250 542486043 542486051
    0x30801060f080c0f090409080301080c0a26101a09060f150a031d0f0d0c110603070516110f06040605030a020706021e0d0f11071b050d0803090c010201 66
    0x501c403078000d07401643c06298924643d40d0f4960580900e001c2e8010749034201e80261810f500e6104216200c001541a50340100031246200425001c0002101c4c142c0038803480122103440000c00d010300c1c00c6072117070f80103000e80035221000703140303035000080300c0164049154007016001403811038200030001c80d41000d000e59607580010040008984401481205900c2e03000c2e000821001203846507001040d07041c9201101c41000e440b051000f80e490f5002002c41c107030341c0605044e604045000d2034240080c55888290925011080d8040140d01e420080661090180030003c901120844805a400c2c051203010f900c644020f00c0700a211103604080c0c02103004100401c818040640c000d01566071012018034096a19010391818030041c0c003900f903218003540035460900310078000c07400c0030304141c01425004010304070003a038110056804202000d02440020840c0c900450b1090100c3c50400302c44244040302c840d6130707401080b000440340506413000c12010080c002e40c0b40b42844000c07600c0a007403000b88 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 542488543 1250 542487293 542487317
    0x9010c03050c19111002130807050102030c0d0c021504090531060906060806181203150f03070f0803040303031d072108070b071e0e010c0303151203080106 68
    0x500f81c100c403180502c42444409a0325190800c96921180c028240554852141c140800d00290003401400042c1c0602400400d441d440001a1034100009000400c1990111007095031b010f0010030342a41c0211031a201081d400400c44010001055076403000100e5140450b413181491040c0c22500714801c0d00c44e222147c1341412107a84020b00c40d00003c0000f0540e10a140550040203198440d0307540b4040c0000b00301c24071103103842c900001e54502040d40c0840446e4181b41e407071403000b120183d10140701c5900101042c1400c0c00f000e0340840015040326659a00c8001c100091100f81c2e00880c040d600c005400d00406078140684083c09150141c0e00030301070b064640c465101c0042c1d0190602d40000d201c0380c07000310202e0000110075242c10411403036441c1c5203424400403900c811200080407451746010701c009000000d090311811040c036558440d0054207400119400f0f098250309804050700c0e410600421f030b1401140394010b001d140c10040520b90705140180280005a11000501591041c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 542489793 1250 542488543 542488567
    0xd060b030a121116060e1201061509063207021f2d14130f050a0e090d050c0102120c03010302010f080903071b080607030609051321020a0b09010c03050c 67
    0x70130585240f03062080e03004200c000425407405811611200320760a001000600164111608072030300816501d20f030240340c83c1d02c019210482d11000c64540403040c00610110103141c3c0e1591010500c40c0c1090f98a802e1003070f000150300c40000c403500640e0000c640e101d1804180c0251000040140103122800100c00c0c15011004c10508003103024248441c45101002060504040314518845d550280e2400c540381d07410000d42e0703005230080b0750080c5030f0f00f007020408051456003d0f1059010034001c0042a107000c0c82190340c0d80100100b41442c1d9028801d580340d080451075058881c03100c008800380c8a6165000041c105000c08098000380310f002814800490b03004401c803010300d50444203c41006024418116040c1400e50080750030340540402d0101081d0b060308003508540f448030050110b5102c510044c2020703001404002c0a06a900c81907032496000c0321f00c0c100030a0300600585138000c6c02c0f80c954204024086603c600185d560740521400250188074140d08114110b00b16818200d0745140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 542491043 1250 542489793 542489833
    0x904120201050109140a15080f010506040c0c050c0f1c0f051e15040203121615060501020726070303051b0d05040308031b0f09180c0304020d060b030a1211 68
    0x103104a06440705a8180b000c5444449207008000788230440c2c0c5182c950b440594020101913030440d2140d0300708070705070303510760f21418400c040a50020003400500c900030081003440401c041c0e00300d4200c02440c0d039020f0410800b1280c1c0c0740d0580551080c4803880d02c24500301e4100350010b5000c00d1341140400d0102c40640d00000c07030362503101e07045103540516100c5000181ca4801d100208070301c01c2000140c40350f001030b4500e811140d541c1c8100040102450003031581001e462550007a140181d1083c070040120300706242181c80720b0041a1044440160450203442c1400e03282d8206030046100000c82003101076401c0b410081442820010b4440103081d10001415071080740f00291020f1808170100d6035041e070101540444000c8a8120f07542c80c20000d0001d2560b8000d003089a11a07030b1001e4400e6802c2d27911400040c42011501445491a9920b6081241000e0b0100091b0341103079441d071503000c2c551001c006041406000340c122054030321a0031001000004909902300c16904403a070702030824916180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 542492293 1250 542491043 542491051
    0xd0e0a0b0415020c0d030f0e01090e07030207060e030705030a0909050108030409092321090d143927090f03030c12010b0c07060e0d02090412020105010914 68
    0x8007000c0c48096000081303140481c950a6a54071a484082c100c0805820109418103001e032500c584115000d48401518045414410030309140c10500000e090544aa401881d001d44182030004061954101c000e10790381103510119220351001800d1185213400106010003404000300034411907040c214015182c2c0554440c0f0318bc15074070b4010b003e0810103018942c0041c1d071000008582040021025a03a40e400d603e0f6010010220002104600c911440d084032527001000d00840414061035581c0b00800c0b40714000d00100c0d014201a12000114160791040b0504148800300107200c0307590f01001034110030202083c4a44c4111001c14078075070b210081405012400c610760240f80d564200c0c0107003001c0014030164400d010010030040d07002510409089084081c042c081d002d03a8a0b141d0400b501c0c419145900303c0d80d8000c001c04c0200030b100b08800f012a83c809003940d880c02c0301c25408141801c20580d0119002034000403040c24103582480f4403070040c04160400d014403050984807005114006e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 542493543 1250 542492293 542492309
    0xc0504050c13090507140703120c020a050606060d090b0f0a0b010c0b1b04090c031a0901260c0409031106160e092e031e03082206020c0d0e0a0b04 64
    0x1c0002505c25001d82c049200303081003c010a6541c440d21314000789048000340c0c4c00c1140718030741400821690b20004007400c146501000500080d00c48608010164200ea6448a00642c6482c40783d80040c6060b0160f80c0180c5d90b1054900c01030421402d000143c0d540d0340740d40c50402601d06d09010102d2081d50000707800030058011310ba258105682825180d12071500402d03940c1d8145842800d6807a415440100300141c154080c1040041d90b4040102c101000e1103040074503e150b6680c42140c605c0e85210800650040301110100070741c1c0d10104042c0c422502c13080e0041205040200b1000805100700365125a07061304111520440747c4001d0190200340e0210750040b220341000900740c1c0d081480303141660f00d00c038049806c1185001040d000c4600540001c855070441e00d10003401100004040b40000c603415201c3c469660785203c240c0f0105000c020a0061400c0c07032240302e002040c201d10081c4192440c00b8042e20034009403260107410600340f222254056040c16400f04028201581076805070f80150b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 542494793 1250 542493543 542493551
    0x11724060f2205010812190e031b0102061f060e030304050a030b19050106050d0b0418050d18030807020927031c0902030607030b0d0f0c0504050c1309 66
    0x12010540141011941a4002d034801c1c402c800c00341c0341c841c2009080301a030581440f8a0707807900c02207a140c001c0c106c0f408026200034440461a411303801010201c0000c0c0389441c403031980b04440001d01e40340316201e0514000816101c0005103580c18040d07140d010030f101e0b0080c0500c4440b403014070b40111243c481d1004204104540c01002c0da4140210b40007024001c00700b0904984038104450020001c3d01d942c0750076140112000000da14502425040303c00c161603207802c000c03c010902c001b800180c0e42440c1c2c003907640c80070f1180c10300d40d40001070503180c0241c00901c004000207001400038a0b807004400c62841e080722007000016244001c8401403641992030008540301e254412650b1001d03201c440c04802c40b280580100000000040c11503803d1603562907200c0020084c03440220307050608080d4050700608000b0380d60034004e070004010a04054170395400c2e0340454076034129240a09400715041214801c0401a52509003d5150080c3d0810701803490102c556160480850a40c8540602d90303031a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 542496043 1250 542494793 542494801
    0x501120c0e0123120a0b010801060c0609021206150307080a0222020405130b0306012112050f0d0b03010c05270f0406030f0c0906080712050f0f06011724 67
    0x780343d460351040040741d05955150a810704014031080d50444880040d140741c00035078031241d889054810704030303180307621840751103102c5440d01d00c054135032458241c0e0001f84c0d401c1d200d0000e00781001400c2c0304084400d40c10703817410000c100f0036042c50015441081e081d40680c1012000d07a803a06070814180c06810032041d100013000c249200039024a41c0040d6202079032050004d0b15003080d40107481888821419101c080c1c1e02c0324106d41c0328500700c040c03224503040200043d000250321501d401100708028107295080c01080c0703513014004d07442030021110380c98407010b81a40c0f50501b4000c4490307215050414a00b0001e045a02c10b02250245070f820380740780c001c03242c52502520344c81d50f881d80c0c071030018000303000d80340e22400e0410100300c140d001101c0002d980c20700018604694842d040955915030b002d011036600e0258403120b01c1c1007103a4160360601a50010000c010310400c482c02946980070081c2c1019890040361716458206505140c1440e0000040d440f0b240c49007203000e096040103c68819001c1e03e0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 542497293 1250 542496043 542496077
    0xa0605030a06050a080604060f1406010c1505010609050a0e011a0a11101a0405010503120d020d09060b031209030312041a04150c020c06071106071b0501120c0e01 71
    0x42c550f400315070403000001005c614040003003009481203000790400d00c09078946914950454182600c4010740102c0880031448962051804004543c001c504004240c0180b0114404840081c1e00c003070080780e80383c0c01c10051828814605402044018804e06a5625050404a034500e141410303440482001880300c0f100c41c01040c011304031100d554203c1d0031003000c5190786001004242d18182c01c60a00c1860403a441c541401034a06985014000c0c042c40c6c0400c440c0f80700c20b40c00040081000315001c1c030456620340018414026014050140070886880d10814141881840038406002c2c8008020049850310700000300c030300f581e4620080401030307640c505001186800f061700700c03280c03c000c042c20300090090301d4407014003040d00c000081000400a140580c0c0d501c800100e1160841014044000810404130a030074032294040e00e80d0346440e145a6038031411046c0d5a0000c4d503040d4220105000559015001d002c05a04a00c400c004081481e4409400c0c1401326400d2410400703000c002e200015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 542498543 1250 542497293 542497301
    0x31015080f0c090108210c010e0619050c03100b03070e0d060c0906170a050c041e080615030a022b03091502120f0a020a08030a090c050f0a0605030a 65
    0x800c0300015110044408509241c075a060040e40354402e02618001242a00d004075039070410701800b05540b409a4841400000d680c1c210100a070015561391141d00b102c994284111441010b5590300d800328100d290103400103c803009800129424414410030610112102466003a210903805082d02d96450450480307000c800d40c601503070410080794a14040180303503005a8011030158451507000c0d600d4040c222200307502600400703040b1001e540800c2e20030596074051904451044a807030724064498880c1d82c42c1c4403c1094a00c03801c0d150031400c03c240718040c8031030b5070050406190f01e07140d140c1050009603540d903081e00183c401e011040508103245801580e08822081800342e244d2000c5190030b024100008610a6010b5040441d03101a0282d2010455a05c0551018091420807090f00c071601e5942d04200d003107c0c00c2d0312940c0f144201081c00c1c00e018504c03501c84c0d084082441551b5140c40b01e00303004507902c000e0141950154054180e0b40369005042601d619240040e1641d550880b144090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 542499793 1250 542498543 542498549
    0xc060b0411120a0c03051902070c1e14010203040f060806010c1506050901081c0c0321020a020f010b092419060f08090703150905060a0b0a0801020405031015 69
    0x40000620042e55400829594412605918200704100760343d44140d0690b20210b40010030010100c0056021064503400391803d68025640c00100e151950300c01c0c9260100002e142001840c04442000304803091100b00f400d0382d100303101460a107842e0008404048001d40540d1042c0300c408030001d0056403049555142c450b8108080704d035410b0b06400c42d4001413205024881c0642c0c094000858200000511002c05103880400d45070f106181c0442211100c014a1046040150340c1d20b01e07018001e038a59203410040720000d001a96440240c07006441c00d0151003030300c0c3c0c40b641401ea0340411a0345024605600c05028415611000d6400803541007108440528542c09083c0c0c108882c81456205140400d482c1252103070410703180c0d801d00c187c030452001c0380e81c0c01c101e60000009000140312580400c0e446852203d000c965100280c5d219410400f044900217081980c0d10f81007555441c20240c840d00509940008518007428030340403030f07241c140c5000801211512641c410011000061f400001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 542501043 1250 542499793 542499821
    0x15031e06060519091d06060c0d0206060406060e0d0b0a15172b1d030312091c05030a05060607080c06190501061b03091508040501060f05010c060b04 65
    0x1203a074580c1c0d0064881d4019081001800da100754029079814002c20800f402d641c0102000e254009040c281d0490001c0014103d5801800038010714003c60002c2107101c1c20000d640c3c01230442860010180021a18140d0181d8100b08045501900b00e80b66a006a050039820403c241500e68820b50b00c14042d10511006d100202c0f202c12000034070f18020314501c09101201005d645541403080a5401e1a20201041d104a030000030449101207000704018144580300f040e421031050407020002c1d040d508458100c80e14111403804100d0803100a00200400c6a005442e80103501c032a541c0050250200814200d4610364500204013075036107880076504103a40c0b10300d04950701e070281d500194440e2800d03900c41e201032281284203491140f0a0140381d0680754540c0c3c9503803450324864114100f84107804416030501c00c0e4030b00701282c2c4800010710a080300c881c60700e4810b024141454550b003164032507444080d0b030740c1140200388401e03070b8031014600c851078100b0300c040b44090103140013900804050894100c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 542502293 1250 542501043 542501051
    0xf0818070b031905100603050403180b12160e01030504080c0706050a030501050d0b0a0f0f06060c11030f06010302061b0d0309050c030606030606062107081f15031e 72
    0xe21a140400118822841e1043d19041075500640150545905480c03500c15000d032a00d092008a02c03942c80994442d00914003003c02c140409414242e074111904440c891142c005030400103007070000074045d048444591605240041500700030a0110f58003001c0d81050344aa020905200490050b5170109080d9400d990a40d9030300c1d8006401a44085200d501190504000089910f807602c004c00f441030304100a0011030340c1d6005c9000040502c8660715070790396503808621507040894031030480580650784510100c1b8604c0d04100281040c00301c88148294444503034029640004500281100e50590f60f064523503503d0801ea00c0701040c42001400213200703030070b8070810059058000c01e0319513011710107669918203000f043c10b403615012640150981c0c0180042405410018020f003030040c8011951900c6145040c10021030160503280100060760407814440e10120390310311000c0b081c1c441c0d040c0a128614000414080b14400c0d0184c0060540d100940d00b01500480240101416400c40c200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 542503543 1250 542502293 542502299
    0xd0c09110d020c0303010f080a0f0b0702010e0a060f150803040b1b01020a021501080313170705040f021b0303090c06030403030f05041209081219090803070c050f0607030f081807 78
    0x355881d0024480c1d03640301401f01c40c0004a0320b902103840c0c403102e60041c0381d007503100a441d01d500c89420001341c40c51007190b5981c5107030f04035403000340011002248500c00102e055198035100d0419119944800c142c0184174840411503050000111070450300402c01c00d0703495401d80c4c4500b0041e1000d1003240149540001f503040034142d80403800624440320040c1d01e0303890382d0f200d001c142d940340a481500722a04800354824040008100c64041018001c8802c031100507485034041019503030b0202101004035008502e0325200071115a00c40f0f00038032850010f505618202c61115078a24202c1e0340d150207981e0010114003894401d0b042031074001d07116681403019041502d089242d9111301c00d10980002c10080b8003082c6458041803220311035460800d401d00700341c06201203d0324450041090402e010300c11400240c4441c00303101805059000b6840008220b161809200c4200082004944a6030b0f081201c03000190308600c44240c981d0b424031b070800e03045e552000b21414030070135030038482421705c40c410f000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 542504793 1250 542503543 542503567
    0x3041406091903020a12030e01080c0d0204090b130b011403040f0204020f12061e01051605010c0807031109060703050306030a05010f0911040e0705060d110403080403030e0d0c09110d02 81
    0x20b4030840303109803100d1344240c1d0384a4440f00210f901c03440040c0080d00031070405c00251710071107546e60841c0307803902c11503d80002d0200c001c04030b900c47e80c84200340c251107a980c00507500d070042c5804559042100e0510105041a0008100b05030702d050048001d940840400c05000940c85103400380303a0b02401c02c5580b201d191503041e070981c0085a540383e01c8110400003808500b407060a2400f04040c201d514200204400010b45842d0080c034103811210f2401502c600c0031940034059002e05090740e80b2840020b0038044401419a01300610340d41002d42c0c1000071032115112034040fa614542c151520715100e0300c0e0b86001a0601c001d2803409001c96003032200c440b09034512030344002111845101001024030010040c0b000f501d00118400580f604000e00c2001381c0d050002c0204100842820002071030501014615480e4029820035030307041c540030609100309a0408192245420211501107040605541d810304044184c081c4e00390030b079112070030184842082c4080c1c0764a9049050b065440726140c48407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 542506043 1250 542504793 542504839
    0x71d0c2203051b060901030209041b09030212010501080705040902130606051308060108070e130b010b03010f0e130206090d080d0e0c0108090a0f02181303030e030c0304140609 77
    0x19030b028020804003810100e020940780340b03ea000980110b0070111030030010750003034000e081e146800c96120700f01c2801c50b1100604a6110010b2500c4000d501c41c15401030158103180d001c003100941e0300d44401030004600c00100e8008942c0c5c121030200e803002d440e1001c141c0144049c1c1040d002641083da0200b1030b01c1e007140c0906000300824000002250391048655920b031020302c109c80503500100340130b1000205590400d9032042c4a4111303803108071150750300c0101c200400d03070041c0403d0b100403005014212a500d1100010010100200e240382848450000421100c50303000b482064001030303101c4e00d511a081c0040300140c1082d1680c0d10f0340000c3d010003020b0180411604110300400c580e81c0000e40c018008240070300c80c4040185003040c12a9104a142010484241d9002803200c048034102e10100c15809d1007039010518205902d9441d140203411384512a240b07420301c0c2c005000302e01410b4400030a803000c4980001400701d50080c881e0210700302d88903826a07a0b410030110121505000300c0042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 542507293 1250 542506043 542506049
    0xa0503010903120b04150b030c07021206041104020c0d0e0a0b040e0412170c0f040512030705010606080c0909040809040e0d020607020a0206041e0e190608071d0c22 72
    0xc041c804c030001002004115500d00d501c00705111910303001404012110b802950f80044241c000d18908880382d0002424845003494061650784494104000c11480080d0722128060544055042c04140c251550320340b00c21100400030003550600ca14029680c2d803c2c004020180780401030396130b036240e2072841507038001110b064425003014080f141200348034240074202d00c001648807590075180e950314407109034400310154010243c01e02011407144c0d980030b400c00d201c0014800650f5500d04502c5d0003429900c1c903a00c0041031010000420020113103800480d207200008503021003007903582d80b40c540800e00500002c1c42d0054500035980d501c40e41c000804003401d650075001c541142d5a1358100701d81d6500d100400a400240030711040203041515206200002c0b074010b118401c2c161901e060141d039203012542042e6503207a0303000b079024070b20081c86018007404a00e8060100340d4100036442d00e0392150100c08000303c42600740024003c8003020181c0c0c190030100680c044c0648400e5586082c0155240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 542508543 1250 542507293 542507327
    0xf0b0f0a0815042c03070302120d09020603010e010915080c0f0607050f030423010e0105090d24230609041a09150c2812021b0105130302100b0a0503010903 68
    0x8500c09590070340081901d400707e5060b4001d00f844105540e102c62650002e00200c0101a00c40c0c10640050703a03680090350292000c0c205e09449585461503c400b62500e8901e5100c10f43c52031602440f400d83c0104444001d01d406603408440c02d00e421010410620510b40007401c1f41c007070300020303040341030000c8001d00454480c6445142c1040022882c46998414114a80d01044503286900e80550056014000200c002840300c94603802075207507020240e104581440da4201804000d401180f428420008001288405007401c041d4404440c0c1000e0009040c40780304010000001d001c00141e0050a5003400307460b01c0d05061810500c001c10f070b42e00c403401c0c00503850741d443c4400a54101d031003c0c2590101c2804214170301400e9010b8030b85d0004000607800801c10071000002c40603503100c0b01e00081c0000010703000085641907144d000d8500711000640300c5403400b6044d0514401195002810301c6e4281440d0000159026405000500c03484040e03000c103405501b00507003142070503003101c6491601ca1880c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 542509793 1250 542508543 542508611
    0x20111040807030b0a1b09060908031204140a0f03030902010e040b0d060c0207050319051605010c080f0702040f0506010305091204032307030803010f0b0f0a081504 72
    0x4445056168040c50095094590101e6020000b0450b5080065000003101d02c000405007030341200394142c0b00d0040086800328030100000c0021075401500784005180c01c20185d420140002c1112100000c054805030000c409110900c0e2030740d00a114214055501c282d504c407154200e89005406010401b500b6408a9000d44800f200b038105402151000d000003042620b0840041c1c0ea0f40006002d6841d101045101d22a000b0810f0f0310104100c013060742e942c3c00c40707020840d824500685480104600c2c04a0801000c0040042c0c0c1d03004181c4103115607020350016100c1c010200004e00da07004404c8060341c094144032881440103803990000717001c0e01081e0790901c200e981c2c000c2416aa01410a03100c209040100010008a9010301d10541410483c08946003d0401c1d45900c030301d0b01c5000c0c0c0040c2e5600c2d5001004105961102c6184401415019046410408a020b2071f000300d0051040c104103010012000400c07072100c81c40f00780303178070100100100151002d03080542070100007042080400724403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 542511043 1250 542509793 542509811
    0x807171504200603070516030908010c09050a0b0a05090d080904060b03180f0303070f020133080d0e01050d0f0e031e090d0615090515150c0a0816020a080a02010201 72
    0xf00b070301100c0c8103035460b0310340c10318001107a1100c228803195800b0943c100b00c1071404c041007400c8280580c54a01005540740c055080c106010041070844941c003082e6130000410000e05402c6c1c000007a64565501150078024015541c18050514410490550382c068a41107001c40d080881601840c0285404aa00000c1020414a9984d00d5602ca000000642e10a000061f07003d8800c1101c1c48810043e40300106540300b0140c11503034600000301070320036126a2041b1b00c000c00e00789081003800804c4d07194014807001d02c0f400d81c058801640042003038100640040c41c10343c2100c1c103402c2014841d620410410103c00c5013940c85c0d031030390001d07422000074a05043c918020300803a81d007a94030f40300004bc4280981c0c450355030b414005280440343c0c000501d1013541d001408003000d210782e900c00c0002e5a9840040c2e00400104110500100a940c000340028000b86031240c40009900310200d034007506d40c90351303480e000454030115442040000d502084515001c9011341300402d88805c2c0c1c038400e0b002403041ca00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 542512293 1250 542511043 542511049
    0x3080f0a030e06240f090103080a0e1c0615121a0105010c08040b0d2004050109050109121202030910020705030c04060315091a2509080717150420 64
    0x3401e6400c1503204035004c0407018210400b0080d101c1e68a4010000c01100c019400400c4072a00240e009a840c1c01001c10210340c0e407a00700b42001c50070602181c2c41101d1202002241c11410240310b40905010381d9100c2c41546d038040900602c0c083e00c01c1d03070381e20040c2d480d03d858142c4041d074500f4034510722183c0d00400001d5030350003101040d0b1200d83c0034114504190401c0a08602da40080190220b910780b07840141c442c40580c25201800300407000c0e4090f503614180400036125124030703440b0314100043c110082003905501c40641c20303032030b0f8001c4000401d039110315012840c40c040c1501c06075006014840320300c180c940004110f01180d600303034255820380c0c501e401004100c81c032a07c8040e104090080103401a0100307036000e40161881166000184252019500555030703007222030284e0348170010224001404d08488940000307000c1c1c03400d14061070505884645440051040741c100c5503846a414661203001d100544042e103a040c000030142c500b41c00c0042201c4104182c04003070a50329100030b20729007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 542513543 1250 542512293 542512303
    0x3030606090807090f02070b071701051503160207030821010e0411091308030126060411010c05030c0604050319020c0d020114070b1515030f0601050c030403080f0a030e 74
    0x600482c001d40843c0d85014415809010b1220820442c280c0c01c0104c640007d82002509004203001d81d542c8001d15200103c20001c0b10040e0401e500c5621000500b070303024046007080b40d03400349145641d6802a040d1500591518002c3c0e00300406190f0045405800c2481c0d03490641124040e181d0107104903680c3d5038500510ba101520003400103440c40c0c6044aa50270248100307078014114021801c0002107544412a00d50001c0e08a06105400c40c030864a110003c44214461503800300003403e0b8a041a503180203002d00e40c0c22216061116101601060143c184242c88801c03145400b940c00d14906464001e88a500c110b20b601103209014144c0004c1d03920014164100b81c10180640260300340c2900107441c40c12a280007880804000c0080100140c011745003240107200100c0954551030500c810000385d146622252800d0103c01d00400819000710b90301150071010a003040e030ba8a80802c207103507007584941d030005440010001001188061403800902c0719086980d010840b0f8400308034070503154 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 542514793 1250 542513543 542513549
    0x1804061e0b0a03023001020702010305150a03060b060f0c030307020f07150305180d080403030b0f06030a110705060112021906050d0b12070801020d0e01090c0909050a1e0303060609 79
    0x2c4000c4007014030041c100a106210b440e02044541c0d00340b182d140322842c8102000c9401d0400d00d035008150801107503014000c140d0410074070038903645211189400709000e88290712014100640742e0b4a074034000e40700c1c40304480c01060400030190351780040d0141c013a40c3c1c0c3c1c030588031400144504108807218900206040c400c0d1400e580029402513610300c811405400080d00b07401110103d815402d001440400a40040c956030361600081b0b403a140c24060700312401e0780130183c042c2101820b00d4a00f680c0702c5040340d0b404162084002006020f040360541d1a01600d50020440d201d103000200b5161200c811000d803042c422a240306c0342e08011072540c03a00d80405d03c5850041070b0144021505100260028001078401a181d14080c10340b0500746480c059955000f449203960000b83c1d5040320203075000e541c402c0c03105503000344141b510a0b9135036400c0e0460f0348100280c1607030b0b0320314075401c1020600102200d0780d080500706981e0f0540405070481581404802c0340400e00d0803200240a0f800744000c1c80407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 542516043 1250 542514793 542514799
    0x1308070902041d15060d0504060518070b03100909050601080f0307030903062004090b031b0907050d0905070b180306040302191401020d0501031703100b07021804061e0b 74
    0x49100e00001d090b03010030013520b450440014140101030a84444002d0503502603080000b10306401c040c1403460840d1009840c0c0d041c0c0065000d01e80c11010800940b0208407241c901e005a600e9507138001c10108181107400910949050111100a0203030004d1118140c68003031341580ca8599007184844d94902c01c101005022640c508410008102590310000308403407540b26441242c0c80c00464222070780e0140e00001a1550b540d125000301d030400704101005c104085150040802c1c2103c0041d42095004002d5806c004000409101c1d041003500b00ca0407a030b601c4021290380c541c030307000f42103081d812007003a00540440c01c5242040515000034600d0040d0b4240d00504540202201d46031840204131105803002200d802030302910040c24070040c5464084150700090035411460704000c0e2108000312500002e07030a2044c401a810000041012603e2008000b84e4891a234800b089082d11002200b251500c034400401080c041036400600f95511000317610601400c104004904a4084410b482c1e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 542517293 1250 542516043 542516069
    0x30e27090a0f061805011b03140105060f0901050d09030215070516030e040207020a08060906280518030703030c031104060c08090f030d180605030106020c1003020d02130807090204 79
    0x214810f03a100c0564034013601000c0005604e180c55090a46094181d9800d600c1c0030030655080440d4584a841043c50081000b40203551400000401328095111050050900040c8034615680544104c60a5000041d000d10007200a801c000e52038002d2000408086408100015a05803042084842c031070810301101c00102d1003514100d540342030040b0300310b0300158200020300140ea45c0c0c81c0c034a802805484003c0c052880c00c07002190074803901a02c20b103100c2c46a024251001c4614203c03900c2441c444443c00200d07980d80002048461104422a1b0003901000903182c2c141a80744e0850082403009da1018803181102c1035820910740b049100c1c550005103407081100000725000010200b41ca0f0007003080003250882d4000034140013225040c0008694904110140a03084861a400410081c140907045600d0020065180c1d40064801d47c819682107020500c01d900a034107803110054030940454840d0740d884030704040001e4500483c030442c4200e0400040406c0b8a0088509031180f010f4105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 542518543 1250 542517293 542517323
    0x2d01031a01031e0c050402040305031312080a2f030309010b031f0b131401080d090f06180849081302060708091c050613030e27090a 58
    0x214040c4900f08200c0e0540b215400003d801c2d9582e002800c0918015806503541e03110628030400c0b41a060b40c40080300c60614003140b030106003e4416607014074083d04040307913811000340e00384100030409071154038078030000c10101905a000002441c07280b60700c50000c2043c800c2e68010940d0700c101e01070a0800c0c0f00c9110506080003451600000c03041c0001401303082c04106007100c081c003035610805141c1c203444a40c1c0c1c010400d032a001c200c44507501d4414100441c5c1142040101000b0b42110701840080c000c0040100303089200d41445c10000344030b01c2c416982d105299a40a420304034081040366a0f11001e0020110780079815590120007510f050300c514209101d40f50b0544242100420b000032680b0b40307041a8000d603c40340000c02c04d0a104100040e9200c00c00c1003080b2003507a902003081455580003101800060000904c290015a422034652006200c0d01d0300320b0b0044081c1d5511a04009944182103000c0150014100e00c0703603e07000b202c000b5903a000d000541d2004450700160550607046a61 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 542519793 1250 542518543 542518583
    0x61a03060a020904090638090402060c030903150618091005060102151611030327071d040203121603050912031626030a052d01031a0103 60
    0x810b10040080c001140c040040c4e00c0d0042262080e8000000c50407d03086400e40c9160000c0f500a00f130300c4081e421403180100c40022030709842c2c000b031000b80a03030340c0007a03614160541041a40d415a000038100c5100e2521038102c80340c1c0000690b54540121020064100b40008000343c440c4644003400c0204040001f2a180304d0103020060529410b5008011000095a0000c240e10b48100c221101c6449003090546004140410b114500d841c40c1d0814814000400070600c40d03290010020400e034a86c01450f11203050400e12030394400980051012082901004036a140e175100d10300840c15501c00c0c0385d00c0001e48050703200f908e01c0e02d90300001504c0400c00207401600540030000019102940a8104144041c43c643c0200d202120101d8081601d80400840180141d800540c10841404580e51038450860301c0c00054298080716032107900180380e400c14161200106001408444141c1695039410341d100d0f0420b01003601c910f01d8040c614052001c0074050786049030340c440c0340b02074411140004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 542521043 1250 542519793 542519797
    0x2030a120512070305090606011e0806061903060e090106030f03080a0225060c021f0b04090f150608060601050a030207061e0b030106151e0e090c07061a03060a02 71
    0x2940501c40144200307403603240c03442d652501c00c0c81c481e140001d103420903011042c40c04a004001038100a0b40481c200301c1002100300d00b020280e03031420211805d84030040041c20601074010407250030512141c80340c030741c280d00d07400c18400c50b0001441441107803210041176091320700a00014100340d9406509100181c800c4a0703081e0311a45440c4018208103085c00c402201d40e401110b4018191038620111003800250320403404110701030700082208001c0004440d400314030350b14500c9405660349083d1142610745403c80f210b5941d0201c85003542d03003001e141c1408180510781c0c1081c8107a1620f0008946480001102e50007050140c441e41c1c10000444011006940b00038000c6030ba0b961074150803d20107283d0f20001c10740b00107120011825003240c405041c00c403101e80c1e006045203244c0c00c0c403592106803c4440c1116441c0220004010003803116010b46004941c20b42e526000714403a8104251002c04001829213a4480c08040c48040c4603010032030b18913200c103440c140d0305070008004120b0003106070340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 542522293 1250 542521043 542521073
    0xc09050a08120c1513110103050f0105060f090607030f18030b010b0304060e060103050309030f062208070512030a061d07030c0306030f050319021c031112102102030a 73
    0x2101d0312400280c403101e2070004103030fa010740c00c4007820592070108036001c0030514840202307107010041490206d52071310901c141842090701607007000600422201c0104102c91040c0d501408803552080ea5140080c42d0420f8180190002411414100c00441c560000d0000707c1e90045150320303060b424402c0901d03860f80050000c6a40640d581d100041c11003040c0440350096000d03e004e19202c00303203481458244903015000745104d402c80d00400407401510004207540b1139040494030518117181c50300d41d255120340d9001400324411030310090058405400114032a101c40d002c04c0c0a401e951b000007110003916060403039141d081e00310004180b40d2180d8492900b100c2d83d850007080700396403074442c1c82c2031207091a0190b809400005025190b4540c06030326441d200c1a0f8030040c0908803800e84094140e80343c100025080640b1280c035800040311a1081d20f44c01e43c500f1440304810f080452910711503524610407462681c0309440d0400d55041c40c05030708204d03260064003030090044240e036171840b002717030381c034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 542523543 1250 542522293 542522317
    0xe370e060d030c0803060a1d0a05090d1707050708180a09291903060e1507121a09071709010216080904020f07050f011a1f11100c09050a0812 62
    0x150001a0600c0024440100c40323488440e100e01410032068240c19588018460b001d82e601c03448101c429240d001403070050058070714191803000d0310340384002c440f5845001c0010341805c6009c104c1120000010189900c1c15208a03048800c283d0b072858014199141c0c1c00d5404048594040d800d003030036041905540300c035a0b005044040c440b41ca080d403018a4407960f0015a144c82c1c0d11104c41c586c44030204240c0582441025400005240c4980020103248410118804141d1200f082069132901d15a81154030f41c0c005041c80c0440c500350000400842d20107408004898100c40481c1d0402c03010701c01c030b0300071002d00700000c1543e14180d250410b80b0340c8040e0026403ca0380c00c02280011205ca14040e01e2110f1099014207440b0081c40011070a5801720000c03901000c0c031400051030b042e650b051805040d104a5100c000003100d652100342e40e006940c0340c2c444c4a0707000d0b003510007480da40242d0083c2c0410300750b070321048a0540c6070b03810b00a41503582d011385403990380b20307010640901c10403801403c8004014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 542524793 1250 542523543 542523559
    0x5030d08191d070e010503120406050a2d0f030507020304120c09020f0310230d05011e0c0215063f01090303060e06010e370e060d030c080306 62
    0x48890b400302a804542d00d40b016000044240143c510f6114141c1c010881100202494150350f201076440340700b14031844050180c001403045043c4c2c05400801400800d002440b08406449101112520f036180d5a40300020400800c00914600038440d0600500c840c1d402541803d042a1314240b4415000078262132004e203c00d0b0015822005000408091400c900001d859080462001940e00c07000c1e00000e030120040000d002004090300c50b0f04a240400300e035400d41d80c09240c00c12500403e4600c41c00180f40715074030780745640d103840f54100312100c001c25400c495449440070302048280b201a100c2c00d0f070007400c4099076443e000c000c00205c0a0004101c050708440b03001c102d11011541c00c000c450514513510b841c84442031513050700c030b003030300400c9c42000f030407003d1034000c1c0020500000840c51034030032203050080140100c244403c0384080713009001656041c8401071002c0441054a109080000e49800005013180c14802c44040c0d1003030b4941c0f14116112182e0b40c1d0200715810040c04680c00c0065 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 542526043 1250 542524793 542524811
    0x1052101020c0309010e03060f070c140f010b19080606090703020c0f0715090b030f070219061d070302030307060b040b0a270e12030a150806090705030d0819 69
    0x800c0c8001c20046440100842e940c60b508400900707101700b0000d4240c802d80020303041001c4281099061940030100e03140c80e211500d035600d410421500744040c440c0843c46081e401e015000b00561080d5503000c1c0c01c843c0341c0011000a0000381b80b07844240140040c41c8c011901050088c1000c122080d08004603050140c200203501c00d0303151524055000425059004880802c01201c51000c000d0460707255190108040d4207040201c0c480788000340c14103007a249144005040c5170301c2400702c0000030794141003080c000806410500301510301030140d102c40003010b161740c0c1202c450000704c0c00b00701c9174054091408e1020a07140d8000504000c1044c42d0415100d2800751030076518070310148050302203c94030745002d070360002c5040744070022090440c8000b440c0c0300710400c05107000103006240e50041950a6940c4d62a8207581000d049140005070030700c0225000070070503480120740c040c800d142d80c50842d01c200d0f03a80c2041543d91a0040d40440c08030b9900d80204d00c001d50f0007000416494000f9501145402d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 542527293 1250 542526043 542526109
    0x3070504050c0a032403240f090212030405090414150703050106030506040b0105090613180c020d03090c03060941010b090705071e050615010c0b0105 66
    0x31902c861000740005000251aa0035200d10004016660014101d13000c00350f04100d1307031124501018141c40c4038841402a516225420b0325100760440c14244111000a00800d02501c20003000302c3c481c16660b28000050100082920116440101769041903101c54945400d02400140070380350324050010034881304201c4806c858003030680c03030707400190341e40c540100101107a80150045103c0d03030030f000748401c0507039000301a200e8844048481c1d9658401d0381002c034580b401180c0c03007200810003201104d544145294003903545c0710411303003c1d1003512442040803401c9400698009103210410641400404da01e54043e1150a01c50140f41d604a0071a440c0803000d540030307004000010301800d40400741c0340518904901ca5403401002446492002d070000340143c20f00030401010480040342e01c1003030150f00d2140e501d8103220411590807099041c1801601ca8404403200a85000118241e15aa5200c0d12200e89075581017800382440340d080c081005140c460f041080b200398940c2e034010b1030100d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 542528543 1250 542527293 542527301
    0x30f040e190e0d0e0915010807020106090f1410030c0308130302040213031b0f170a0f05010b0a060804021c02063016090b0a05040b0726090307060e03070504 69
    0x102c1d480145a0446085402844035943c00c0802d070041054400b4443d0010244031425014603003400c02140a40d583c0404034010003e0340d03c208056400c0c81d80c0700030380440952001100a200c0e2030b0301d2078190398003100e089203d000c40c0b0000704002e003004020000f01d501c00020b0b10141d50a00c4101c008a90303a80c00081c2a40c00205420541048000c0104200314410b021a0142c03180b034107018075040c0c500784440b0340010315841074a098074403080c1d4003410180244111450168002d14210441d011402e1440c002c0403001e049901403450b910021601038002c003819407190b076000f09041100c1329040281e21201c072079440100e801c05024002d402c85c445080b0003003c1a1248140c101c0030203509050303031080600000e03001030b551069080000d07002076445155113007911014202c0c41da41380001071040b1060300ca80e9001c1c2056913004035202d002c20a0464140108801c0303015416a02ca140d070f0b40340d9906229098045030b25a00080080110a0003014503880400004066911040c0d850000c82c05423 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 542529793 1250 542528543 542528561
    0xe010b1c05150306060406121e05030a09030b070206060f040c02011103090c090112020907080709081605030607090b090d0204140c090910061407020d1220030f040e19 73
    0x10b000e1285407102c0c101004401d9000b8000c5600340800391800d0030420780545000409408283c18100c0d071804501c442a000305120f40c000d04995580d540306030010011a1381d404102c40c540f0700e2401162403184001503080c061703000100a225030307400340c1c41000010101c9a512505554032800110640d802403406540309000e0314001e040c4440341c040c1000500c0405801aa1800900c0d070300103000b50311a00780c02540100c40f402c0020480c1c403909400e0b44c01000941c010300d094481c07925000718060945040a0480740300ba0200d59460700d81c01c200f924500058003c105c2421020b110825403484c00780c0510000368006080050481050181010018422100f20540904c001a074161600346004443da21a4051740028550743c282103009240e0003415003107140400b000320b079030825940c0c0d4052901c107056000c4429809202d0b00c10000c0e0418261040442142030b000c0040b60030481d02000300c581071344104441c10719040c1841c5012070100c070040e001408012906103003035a11074051280c8002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 542531043 1250 542529793 542529811
    0x108060c0d0911030d030e121c1d060403090f06051620060408070e180607050307050d1a030c04021206090702010e0d120516050d0b01110d05070210090e010b1c05 71
    0x30020b000103a14940110f055980c240d10300c0c02c0207081010f01d8460a0085078404030000440c00301c0312b00300e401030700d2942c8074602242800340030184010150840d40c00e004545030034801c48022981c5640513181d40c0a050f140c101901c4100342e4000002d4080911802586049000801c40005580104215811980116815502408040c0a4410380350411980b0020144807418801c00f900c0040d92604405000041840030100205201600540945e060800400e5040101c0a043d030004806080b480c40514001d000f11546180e86003050f00807180c4054032000e1880594a8040901503454801402e000c110b55980300c00030950801402401e10828441e0b560051420341e40f000c050803900003401058641d112001c10005035904442910302085503110001160000d0100503a400c107040424511280980d60480590503048409072a0241c0241c03200002c074203400c182554074070f029000320865a004100100002b200d5040101212030100c540303404a04400700b4050705442090300c074004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 542532293 1250 542531043 542531051
    0x807080105042102030a0503070512090604030f030e0a110321030a0609090b0406180c080d080c03040302060609040302010f020d06060f1e1b0b0c0a02060108060c0d0911030d03 77
    0x4203000c460f64444200203a4588001500b454000c1d010350303284a0002c24505000001c0001131060307028a0590f19511800c41489000e45403141071756465440440e07007140424100580c461006220740324680c8070841090080c858a2082e0b1a0a10890749403105103034144201000a95407482c481c850081c054144824035440b81040500700060302e030319421a4461610f00110180441c035400013094101d40c00140019071042c9a248080c428103801501030840c002e0b90000050b0840006648148039407955584242a1a0044c004c5098841076030064016881a0040b80389882c141440c1c5400900c039000009901e2804c0c0030f1a01030342c00507111070901660b0345508003c0366810255500e64002c00d85004480309562a001451102180c03503070008000344078240e2845040d040111488d03107900700f10300300c0301460710141800f06988100c40d0038006002c1c1000009400000180c410b018003104221036080c01c101c00c820100405582d4420f80d0b81008000311400b182e2014018010500340d1603070045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 542533543 1250 542532293 542532301
    0x6040e0c030d08240306040b222012103204020906030114070e06070606090204140904050316020a030204090b060a08070506090f01020c060a030506040b0405070c060504020a0807080105 81
    0x4c6003550400e00c40000310618100d814055030380480c0c140c1e806039001c0c49404241d01c904a2007100301c103680003c1090364080003111810300c0b8076843da60381982c05030380483c0641040742003030116202d000c4140c4c0320150f100c40f00495004601c0c0d00198000c0d020320618004203401c1d070051101403154800100d40e0288c030b100074441582891120540c0c460000d400a004088265100183c0180014044010010a01d240c480c42c1c1e5102c1c000c5509490300302c40144109501c61280c0741c025406031003029844101082a50490f04140c11701e00d129076001000346081034081c078843c00c1b1030143c40104903031101090b800840117030740728451800564014a03141ca00e80c54150203020f1503091541005403598402070041199640750011130b202c68500351003411500101c040103034903090003440f440e9400000031456152096040c2d0261703124000881e800d00a00c1e03440c2042c4070850744203407500e40010f48030760311446c00303c0c1b400d42219070000c1c8080c085600032075442c1102428094250041d440994548040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 542534793 1250 542533543 542533561
    0x2150a0c0215060d1b36090305030403180f03240204270617030c0c01050711062208030c060a0b0906091f03031205070c080306040e0c030d08 62
    0x402d214086902c805002401c110000079040d40c11954001d000426146141c0e03011070340e400e0000f0042c807030103040701d5040b0407081d900f441022000005202c46e91100c107103d2900c54140c0505084250541c840318559101c5440846121540100451000c8042040040c900300910440707002940904542607a080380400110020740042030700850b114014003090080f09280e1080c4210040d011b542e00b030081031690144030107444150701c4582c840f100b0a0764102e00c284007000900354800714a007624407070217404005496500514101904218a050243d04076013031440c0189100c0c104a0904030041404410b4061520140c2d00310300e04540010849840a00e0708125140d003219881c03005200c0d0700c414002203049441d000307104610400b2070f680421441c2002048104400c0182c80821004507124100030b001581c3c8907140310038031b40c9003000090b0f2582c03145043d4180c1c541c0c415172462a58503900304002c043c05010380012802c0c0500e058400c060340c3c0401950503903c050b81c0703480d0312611700500307c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 542536043 1250 542534793 542534803
    0x6030f0b150f130b0103090609030309050706050406050d0c030219050d06120b04121815080106050306090106030e01021201171e0607032c0714040905030d02090102150a0c02 76
    0x3624011264120354103007503038846a08031690801550000303104110b444c0128054890260f015041c7c0c0c2c40c154040e014141e0540100406600070001c6a002d6aa00c00080300d041c8a94030814000650070711440b0001000c68202032181d034590310b03000d42020070148000c5682da070003e007800041540002e842086a55070300442006243c0303d215030540a80301e80b00c4201e000d5009200a040b0070300420030700001405180029504109824007040c00ba8585542503010030401d481400405d1542000181091203481141d10403140a40621902d0f4a0036001707a01405800c00140030a54082c804080300526075400103000300300c003076040c011911010b4842d074142880c3c406030200614a000024660900c00070310140c0000d50ba20300020513501c60301142d203602c140312648441a08002c0b010032012240058441e041d40e0086401298081c042020041118802940106aa00248014240141603a02400c200201070064503200e0400c42c541140c1070800316582a5016076401444041550400c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 542537293 1250 542536043 542536081
    0x200d06050f0402041d061207090b0315060d021909240504090c1404091703060907021c080a0e031c0f090206040308131a0a2304030b07020106030f0b 65
    0x101180f0f00307405e04011899000d96440d400300c2540da88008a00a03884003443c1d09000c1440e082502d401d140c0320180390000d0704080ca16103200e846200c500140242111311107600442000342400c000c0c07040c0c0e0b03003444504040b00501e5044003503849000039103c104d5000d01d4011512111074404180128803506228142d56005180580c0c5030051000014440c200003105a0b0168010600c82844140000d0042d0101001c014013480d0b8841e400381001e000e80000c3c500880048030315a90560310060304a0352400044122115440350760030a0300303c079001c1e101494000d1944200880d2200818014910b10352111220015070401c80c850b0030002030b1588680d01030310510590510035504940c0008942e40218000940380c0d0300001000741c503890303113a80004010400107100c0c500c118126109034105800c40700b52580802d4086001c44020150301140d03001c10b1903410401800d20f42952114401b0040052030308041d90358802020000c039801040c41071949100e0055100e151404c2400303040900410341d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 542538543 1250 542537293 542537299
    0xd12050903040e040602070f060903030b042903070e130b0702030a0504090f0b04051018090221070e04050a110f011205060616082d0904200d06050f 65
    0x9028849040c50100440d4100d4480310350f524811340300e90820400911801c44010288902e110340c0000300705482c0c020341510b50003074808020305c0c2c0701ca0b801d12050f074101c0542d400008404a8201b002810300c40442c42c407a840280c22940e40e603480303003484410000182c820751181d0f41c80c90f2440080007000004a81d00ca191317840550b0070b0000210001d8203e010f02d00a05003850384845800c80618a6036200c8009018000c00c107000034141101082070000b4180241914016081c03082c1c2c403071544601584140715400b030804a6a125214404032a0040b2040c002e101802480000a05da2491800c20350140e030266025095039489031500340c4191758035408440c018100340b01c50082c0360381c020740b480e0b190300802440440d040d90f501001451a210f541d9284649070780800f4680d0a0103c3c00e03010301000c01e207a80104a810480058500e0a007045c0366480902c400100110001c44c2850340046980e42d21400b03111540c095400644045600300e06684200d11790f841b40104898584501c0d0b05060b02415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542539793 1250 542538543 542538551
    0x80a05030d230f04170a180605040b090f0604032a0914131401060f0f0905240105120a05041110022e060f0f141c02010c02060a020d12 59
    0x15600e100395928002d0002d5024502c010009040c8131500004102030507688107261b94031001c0ba00d01030709206502d011410030084c141c401244640c06501250117454103000628102000e640c20403064090b644100c1d50032520a0000000103400364600e10501051203200c3c020a09041d09420b000c0101540100d881c282001800a0b815210306a520b07003109460410410510040c144407030341c1010705400c88155841c00c0300028640c40342c440d0280c00e4604880c00c61401e580d0341e100d4a025102d090b103a80c0300384600c2604404807860b0f8102441141401810500d04288903a501061015006c551140e65251100100700030030160302c107030070300300031007211209180404908002c1d928035026a600075a1001102c6030911884c10722030300e0600d004242c1c42401202d4075840e15088640c0b50f40300e6a5000b025454000c907140d8030790035002e0003005d009800070810007914640940e801840c0c04c4280c2c184402840000056203405000b086c1e0306600e50014032201c0200c40b002850481100140e903551494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542541043 1250 542539793 542539841
    0x1c020c0303180715030203150a080c15130b07030903051b1201060825030b04030c1e02060f03061809061501111c11061005040c0f080705030a06080a05030d 68
    0x412000184011303051a0050720395032441d061151440b0380034a41c80d030091000b40005518000040d4a9042c0c0b04207031840d80704da08800c00e82404074040d03001c0b0210315940035001030203000c1401010f019064000e1400580040e9640c0700c02d4200501031514080540003852500d5031400c00741c0c0c00121030900200200440c0d03140c061210f80301d0a0780d81c1e00f030314406003003264000c1400c070b5002a000a1b540000001c041c030b05081c0342c0603040e480821011a240403184141e1001d41c0d24282024580c40e40250045103071480d54088158a80e2004140d10741c03090100001d185584210440340c4e10031817010004040500381140e00e65100c00340306e60120704011004003040585400440c090055030094861180c0780a41d090050b82d502c030502c03080c40c0007440303184104503100310703405508000c885003078400304040d0f8135203442210043c0205400001195151001c2044984264015a8086610900018155190504a400c1103074420060702c50340d00205045841c0032062203403045002e01c00ca690540818 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542542293 1250 542541043 542541059
    0x20307050f190f092a08060f0312030702010606021912140711150a1b0c05090907060e0d050d0f020102160614070302070519030315080f0601081609021c020c03031807 73
    0x1c5c22120810800c8918400700715603845210403001060b0008064581913402d00c2d54401050b041140c0420042d0b0910000180d80c50000c03400380300ca101038118032401e64141d42c0318034001c6484132616004000002c195040428241406000003a21424000c0d1014101d0030030411001c03564403442066a104200c0c021020b900b001480e04000300040d030307005111246040c4041c19403600d074030039500a6495800c001020401203480b07000d07901540c40710300e003030410349042c049003003c03008000f00154060500d41c40e41c940602d044039412201417001500c0c1c10141c10102c9203180311500f0840d40140c5800800344401641240c1c83d0b8041e400b45001c6007841d28a8880c00e659600c01050401510980e08003081454402d1f00596a1803200c030030302c140c0704c964a0742940d070780d068113040300540da000b42c0c000484c1c4e5180100c3c15281c1070070b8041c41038420b581401d00340c400950040645050f6031101d0b9612600950321400074006004025014503220701d009480001c2d107020a071800c140c580c00052090110035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542543543 1250 542542293 542542361
    0x40b04061b120b0d020411120106020a020f0108040f05250e0702071a040f0e0114040915110d050c0406090b070b0f0a0e16060318020307050f190f09 65
    0x450000400f00d072000a00001c40c0548202810107501b2504007103402d4542261a00140240281041034003042d0ba40c85008a85079044410000c0d40101c40c0c082079038042d132060240e65080703405058800c00b40c00d66a502d007441d041500c44540010503d5020b104018440304020350000c1c449800c10515a240880c0002d449132814000da034110154034042800304544402584c000e48048050035144540780c520015840100348034402140070011a182090f041c2801110841944030268649804100010901611000505100740700051107040c040da11640662409045003c920350343da941085001469120150408007181104000c29000281c189a107240d2000d81c1c0c0e80c1d00c5a6544420790100c01501c801c185c02c4000780304068404403211f000040000407501103032800c010060810f10503660494034404082e5240d003218070104601d08151a00c82c441175002440c94031a681c1503040e000b2111056080107214005002c82030220142502ca55205d880102502086401441c841c1003911 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542544793 1250 542543543 542543567
    0x90c032313031809090c150c08090d0f0c030308100303120c0e0415090c0c0b060f04110c0d021014060f030106090c081f030c121a040b04061b 62
    0x5a070601003240e0506101d401c00400726074980318805081c90707480c5a0b51000e4446000140d461807440c00001421143c1d1400101c1001015180c10b10b1855039a202d0a02d1070700f090080d0368100403258447d20005114005c00b00085200d50816901c190441c2001402603c00a00b05501e140800c081880440d811070402c030560710820f1342c085419030090008440c80380c00c1150700e80e009070900c80d0300c11240060580309800d1f14101c1e40304010040880d1000c5a000004900161203d42654081452400c0030110380c3c6002c0c802410108400309601c01e07040c4954810003198482d500003418000740700350b06011a00c00d034284003205200c40040071049600a05018240c40d115a68800e90060952029049200100110542003200642040000d80091000c4071460b1a16030300744141c2d024580740c4540e42c41a81e03001000c202c1c12604110000d02d0541d49004151064070607004500100100d00365003900c143d21402c1c180101e41002d14100043c0c44071500c581403400660150798003c3d952083c00c05c008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542546043 1250 542544793 542544811
    0x123010927020102011d0d020c0402090616050102040e130303050705070213050601021606050a030b040c051606020c060a0b040e060f1306140c0c15060d0f1b090c0323 73
    0x740e0395103480141d006010b90084030b20440c00049030030441c0748010513025840c5041d42c0a4920355440c1c03404200c120306c00c620b60b1940c01041800111644191401900c4000c0d02ca50001490b007500c80c401401a200300300d500038034424954010030200b582c1070084ea034100041c0d080290810906a000800c8841600f80f85420540c1c0c820011722541c3c800c00400e042e602d5902c0c0300d034110300d484013401400b07036000750140780120b030401210341e025041c02c1c4102a03845e40d03e561014249504100a0b04031040281c00c01d0303410030b80034820000054818420345001710601d01001496141c0c1006020a40d5107070a640c80035074000b04104060100c1400b4a1070f802450f250300c100002d801d510b0014000d20301e030400c0c4181407240d601001004030300e54009102007160f50341280c0118482002c3d41001c4142141c403190000c103400c443c0400200c1d2600f050750614840c0482e030f003c161211a0307555212003103078005008251200c4400090b40c2d0180f044403000b500c0e4000ba0840e0101130500d140d5450f10281c07038140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542547293 1250 542546043 542546111
    0x20109090b181008012a05030907180609180b15030f0a2d080405060f07080a200a020612041115030708150f130b0301230109 55
    0xaa6100b04802c0c03040348458105184034100440c25031803075841c83c0101d540940c41c01c4182210300506050840300000d54003111100a94859000c45190300098209050340c0300e804400f044500b01c0d01c0030403481d54800040041c3c028a0480f03c4800d98010024807210348840f206101c0106d10700605007513003d105510b0f0b00d04084050804245030000c5c1c002142e419000d0068003d04104d01c502041d09002280d03030030001480e4185031b4400368040c0b08100182200810001000b25081c00e0000c1c1078500123600c10f59003400e6032921108820703404802d40c180040e501044d048001d11703214820344080035522000f02050030742c682c040740a6215090703c21101b0b54180300007030104141082c003064040c0c0017074000301c0c0341624242c4518041c0c0003640c1d0800825040b40004400f1601480144040700c0001c2a4803c4403d01c8003e204000b034800303492110003515055a0541c5e0b440074007883d134074200290494800f800c00303010403900c200b40c1a001040000e040c000f1509148100710411514000402c60f165 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542548543 1250 542547293 542547311
    0x301080a0632010512190f0213050f1f0b071b050604060801090e011401120203100e0708100501050108010e091011070308090109030212250809100c02010909 69
    0x102c65018000d0100340d0096000c45128460016540c103030482c0d4040d11248031300c40e03001c0521070b1076070303802101b0104030420b034410600811042424a15124005031100d0b0607200080c450000741c0e4070440d94046442c55540c00d01c84138451249580b00f00c604010000300b0a141070407800c018078415440041c00d07c02e81458000001c00300d0213000401400d0090400c0e9896903189400b078080b100900c02c030040a4900a112002c0c0e010600444d4144102d00301e803180b40b41c1c20801c1004d02a648800c0990701486682007848013071403948076484148403401c0084c11a01c3c80d200c02213161680c48140b00145d1403c01c8010401c90340c2040c402810b6441300141c200307050b40c5502030b0a2404407504881c80000f42403c1c1607c644600680041c00c500e40030356252042030345c424a4107421303107281000c020010b81c8814a01c1d003d250810000d01355051100c0c5d00100006130403002d44072410071884082d00c4480002030010b50621785890700d050380c00c2181c00d00038010401e07900086e00128186c803c0100e6075880b21282 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542549793 1250 542548543 542548571
    0x20010206240d050a0c060e03030403021c06050a05100503070e072a0f030305090102120105040c02070e09030901020d0206070c0f0f02060d2f03040212070e010611010f020301080a06 79
    0x10301c5061602401e20034881d50a400d1056aa9416902c1540c950b501503001013030340c1d8071800728190038801c060011441c1c1461942405142c00e800100c0b400040707249141da10014480d4040c6900500c0050400309090a0401498100340e0709680068840c3c0d110b04010800785040f204044d03840b0005080c007504044074046d441120101103915000312244100700c1c10100101d0401010026002c0c0d50100702941e15103e40314202c0c45291000468091000010010707440c1c142c0140c40c00808510548518603695481c0e2a0b0070642950410116080801d45020550303041240e0450101c0500c01006541061f28014101100c0c07614050828044002010188424000b400d002d0581c007406066640c2820380141c07001304418240c480300203a2441c40c00069001e04101c104081004050f17240c55502e481e4200a5550010b401502c00b5000310f440004482010b061018000c20f0962a07041013004021038403801c4695507003441807c180305000502041000003290300d4030759400800000d00b03215100c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542551043 1250 542549793 542549851
    0xa0c14030a21090909051f02090607080304060b0d030c03050d021216090e0108120d180f0501050a14010b070c09050108010c02070503150f0a0b1c20010206 68
    0x90244460b9000c92501c007000b000410b03221070203e075205161a81c4a480c50400d580038142d024009034480b1540b503000c4494040c45c10038041c42ca450043c076201408000c144d42d604030320000d44242d500482001b0502c8441c0c002d0a0403008201c401c840041c078965800303020060990009070411501140c8800007800950440728018280024402245400b50b42905400302004c03040001a8141c000050359883c07030056541038a0468001d0202c00640121444640d0803501843c0314003500c1c0c1e080c0800050428000303d11060066411004254550034201c0c00d4581c0900228580c51500f6001c101e59080e288813079055841505c2c241e580c2c0e00a81c03c1c1280c030a181a0001d022003840c02d400040c103190305600140b075a001c07a400f5205000da42e01d041607102e41c03804d030342c42d5103100c07050780014183c0c00210210b680c0203100501c001000b102c03d00101e00e1010151a10b00d02050750b01d0b60340024407050034004035040c40701602c0412a0801c1da40001d45401020b019051105c030240d0070301212243c0121 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542552293 1250 542551043 542551063
    0x30804060b0d122d0e1801030b06210705060703020a12050c070918080f0415050d05010504020a17180f030d0e0303011a03040206041d0610020a0c1403 66
    0x961250791041c3d0410107000b0307030326120340b03004503609000121840c1c0b080003100102c00103c0e0785149420380e070001c00b940d00010100d4815071014208071140021140c0c1c08031107001c0c42c05400c1e901c406140141c00e0003505240405034101e803181d4070142145040002a50400392107055410075181c0390207181c00d80c40c082144e41c000300f000c0c4011070b070f650030702d54004003400c00d0001ca20129181c05984200c0c1c0d40440350f04103090100543c1011620000c5400d200041c01400d121840103890b0a030703258902800f09201120450004a000802007650701450240c030f03014040c02c0310214034003e01c804001c0c1c100001460041d426445810008000442030b00c0c6154008240106603450700e10b002c52410303100c0c2c0c0400080403006292441243d84c5203000800d0700e050341c100842150310140034480c8611346410080040b0b900003010440031915903400d001c0080349086064507040740e81050b0301082540310310668107801319400840d0500201c0e40410850b01283d8864500701c2e1110341207404a42000e00081e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542553543 1250 542552293 542552299
    0x6020a0e03070e0621060f060907030207050c09130b09070f14062205030123090601050d030c110409051b01031a150409020a110105010b0307090608250306030201030b0402090d030804060b 82
    0xb401f08905a00040640e9203d1030084a90004564604c0401c1d0101e001d4031101802651140b4a03e51131828840b9005d60000800c0d4003158030420300350707510080024102c5511090341c002e110104000a42e02081348041c0c0150850117103041316560100f01e19000d840040510b0100c042c420310070302c1c8079010024001d800094020f0042015412800040c280303c460fa1280c4014600c0000b245044045203c038141e41e00100151075031085928200c1d00070940b54001d40d40d8645608180442d60b07502c0c8500380c0c010344160060180317102c10500342e40416018506c0c039414941021b91a0b02c441843d1403c41c81e01c070004841300041d1061124200409000355040561078070300c002254044e40b5003000300d60a50154000081c0310f141e03290344044030745000644001001c1344030310b2400d12000380694000f40e8411000665200700081c11520f940090315072070382e1000461345e01c420034415941d1601421007085810707207041d07140c161000003003480c8180451001c3c0411100e5008141004074517080754190303010003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542554793 1250 542553543 542553553
    0xf060510020d080901090807030503180a123c0e0d0615120317090a05062a03130311070b0301090218040b0112050c070c0306020a0e03070e0621 63
    0x140c00040e40e5540d182849401281c0144000f8108401c140100c030b601d945d00603165400d14126a800b80c4560300b0103031000c0c50301194000c50035002c4d0f400300441c00f1f8150245883c403500504070342d800b1704501254400003028441c2d20b54400c01c5801640412444985255000c00d810740e442c0c00c080b40c1b5004510381040e4030160080e03a400610050303802200480c07000059903400103645442d81c3c8460040300200030041140e11000d01c412a0b100c0c68526482191740c0d0a96004004070340d03940d03082c4602101c3c1c0c01030291040c045040780300d14640f80c0c28110f4145004191442c02c012903c54511001e5240003001c005038006103202c0c400c030601060000304901000d00d9241e586400312400650030843e2a120400100b6007403042c1c0d4a843d00071210720f210b06840700d5a8000030b24284002034903004222060301c0700200030000026491120381402140100c030f00680302c46c50311b280100079094507025944658001042400807684540340190071030400c54030440002000883c0c0c80c00706141d080c503c0014060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542556043 1250 542554793 542554819
    0x70506090703050c010f021f090506040f1506080c1005040e130302061003020d120e0d0803010f2412060b0d091703010f030b04020f031606180b09040f0605 68
    0x20010341c0303006880c0710f44143d0720f035040031500466a80024815400041c0c1c40700008041810700080c2c0ca0000c412011400f0650b00e170551161850b001d01550102e0703d80700070551070003c1c071820001001d5a0880c0c0b80003440007a180c401d00c40d56a03501c0303684a92180c62400560003400340a04103c400070810000143e070300340b070a5000003a001c01040030981c054020f150000d080204810800815207600414040b000445512070b1040c65010310f80700014001d40d41013004c45d80c1d40d0f040707400344500d00c500d0b84a80d4030740c1003401e0207001d48803580c45035080624154174855034071180346003521600d000e8505400e08011516942000c1d14466201c41c12120780010400b20f03d4003e6006104581c1c02001c0580c0b106005203001d01c1284024894a0701c05d008a9000f0f10001e01c0510203c0d0300103000801c511400c41c03016000a007030080b00b9070803030383e40c14840004010035030b0030541d60102360035441c100344200e92601d00244590300c1104821407189650b0f0350b51040c0850181c0c4441e003e0b1102428000020b50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542557293 1250 542556043 542556061
    0x62e0509040b01060f140f0706140c0c102c01090b010f1d010b090f030a0c0b0c1209010906030507020a062d1505010f0507080a02010228021c0203070506 67
    0xba080c010400010004110b0ba8079507400390410860908103c56020315004541c05503059036005079078110ba1280d00d684d41d02d82c040084112050198100e003100d555a10700c4101000d1900e0380003403400c1451410440c0c4458941c1481c200b030100702c0300102c000c4c0d4020038440401c0e4018190500d0007071859005000115149800010420a88800f030400007132180540d03542100400b424480d503400d1500070002079003141000303080480f1001c009001c803140b1000544c1ca105103030030290801c600280010a080d485d5a030708100b24a0a4002c90100038a0011b00000003400c48503540200018552981c010034000c40c8208001061113800c03800070000c0320116201107200800c0c240c1803151400f0aa1104103541140f84182c40b4880d60f1400560109450200152014103004e0242d00a101007401818082000b170001048060460750005035281d1011000d00040c1702580150380000c01b003094402c00594000442200080100d14800800500041d00300c1c81c40c4160340780180240240c0042c005414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542558543 1250 542557293 542557313
    0x6050f0415091101110304090905030c010605060f0f03190c0201050f10050a0e06010203190507020310020f03060420070606050a0e0c030114010c060207080901030b03062e050904 78
    0x24418501c0800700c111041d0100240e03500081c001d4a032042024101c545580290710460b810000c0105880c1426500c4010390121081c3c940181da44e82c00000b5480b10481c028400c000c06050f088942905240801e004260503004d502035541001e60004007040091244441c0420100c5c62400d042c000c0745855080280a09000c0e103140c0c41c01d66038580412800300001c50b0b80c43c20b0301c6001d0302000d501071a2108910700c0c1000a40389074190b010401c280011490310769a843c000f21119299144d441c002813042c1440c201a0121a8001034410b0060030003c0900c0300403240c00c228120b80104501d440c6920122090340402014006501d00080907820000700d034105604540003190808d0100c3d40e101400c100e0307034904a1f071080002070204014071a03030b0300c24809a0300c1c040c410701d000740c04050603941e40c0c0300302d9011b00f1007615404000300c0d811280d03607454059007002c02d00c1a005070089003008141d003465413041c15036103036100c0025684000c2440d1191007540c02440024484000c900303213420311a903a6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542559793 1250 542558543 542558551
    0xf040504151409030706020306182d06060702060306040f2c0607200319122a0c0206090303030c0417010501061e02160806150108040809190306050f 65
    0x79604028681d109103050072410352103400204080c0d40f801c102c5948403c003e600041c90107602104030a8171901c1500d41c0f4480e00e10405980440300d04002c4504940940b09021500c6c1a0040e40c0c5581002410744410007642c452030b906503210768403a2074041c0064040c05503201c1d04034001b850f29032501c580410b40500200840072010035020001810b141c2c1c6511401d040f41c12801181d640c0b50082c4c080c1000600810600c0a582d068900300022844421200841c50042d00c00240d54a90358a5010520f48948a48000c00401640b03500506540e00110b60b021106a00b0511803080d0b481c50564640c3c03c2182d0603043c0040a895a82c5400058585150840c0c000c1c100c04210301c580303170a140c9005100d014180c07189900c40101d03414000888004030720b91031800e84210702a0808669a0000b90103800d0040c00303021001e07200c540350405210f0740c2c26120a044a0401c9511014000403840440484101d03402c140c070280a1000c071804045441c07019070f0b02c001e020314034103003c0000f4030024248040c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542561043 1250 542559793 542559833
    0x307030e011a1c08160305040b0a031b050a170c041d1501080c07080a11030c06070807020d090b0a02010204050a060305040c332616110d0309020f040504 67
    0x3541c05801000340300c5103401c3c04010b03c050420000041c4c0c49402401d8104402d100b0716115142c1a01c60303000141c140c00c560201d0009c680c0b91400c0c548070001e0200305001c5201c0c030b4030b01a8140541242c004120301045d0307010108414a0502188202540c60708407400707801d1039401e06c03040021420000e11019800c48110400003030340d20704101e6540c072032030000b4000c902c074015450401d8030648a0011170740c0115001420300904400000e40b0003000c2c0054007901b5551006052240340032200549010002000c040454005071108441c00b41c108104c102910f640054894440e090301005030f0081c410354101c541e000700d00510005400b40d040d00810700c0380e44a1300c04890480c0e520050320400303110780d0f0403010100030184400c07001c81c840d0b422541a410304600c0c002c000410391700801e0000f00a0404640c00c0034074640104481e50072005c40c40766441d5101e240951580f501131100b151200044140c3d40c040544845403030081d555034000384408074000030020052030800d4039220004205441e06091 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542562293 1250 542561043 542561059
    0x10f270f15050a020d08060105070b010b09010305071407110f06030906010f0902040b04090f0906051617071e020a060606050306100806031009170c0c0a080604020f060307030e011a 79
    0x4185102e40c00f0381c0d0603c2100c0d0001e200d40705003d041503e0304107000707004504101003403021001181e00c05025034001e028141f092540d5100c494001000c4d04c00040030001030200003010101c80030b207080102c404d04e582181412080d2400d24000545a0781c40500065010401009204403180017141940c12510740701d0310f40719040d5903070b045003050f03001c1c070b11500608180521040048107241c0e003010410f650f11200002c0e025610f0340c0c850040361029590700c1d60aa6000388034614041d00a81101800c07141e04501701e00926108400815135192265407562140c0301c1d9071100c1069000300400f8102a378070540a221580e281c600003070052b0412121144165845107516803101d02512241c0d024101c01340c060110006030000032800740645040444081d0101c044059180c070311440589208044031018081d80180003082140068517038021108941040c400c0c0300040e5584032100c02e074400c082d5038482c1c0303c0e55288800d0b00100700c14801a400765081048100914200408402a10000300c070492 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542563543 1250 542562293 542562329
    0x13060e010e1510180b030a0f0311010b0a081e0a0f03080403090e041a06030a05071e0b0c0c1519020d020f0c010801140d1208040204050f06010f270f 65
    0x91403803d95403143c0c1ca0307003440458906010310495000500b4100000e07080340c01c1d000c0550344402d091428000243c0004030140d4041300d02d4a021302a00010391004c1303e1004045040884c42c0352503002c1d0341e2000c61b4081c81d200d00b1150283d03081c800585019001030110042642e03509020340803040c01c070b404800040482501145942035902c1807030096130014019401c403800350201958044000d010a6803510641100d0f00c002a003c00078003014041800b4401c10100349c5643c0c0c00324140507908016060a401c1c040b8030b04505001627072101640d011544c01ea40307101c80714036460b564400c0f080b00840c4040b500c8400301c0e01d2600000c0d02086080c0e65400c46045402c24005680c42e5100810420b00083d181d038010028444d0360002d098070140010030544510700300c0e50703c55111802d851030440c0420140c40400c01945414410a42d010001019070075043c1382c1840002c145000049003a020300241c1244100b9000b02c0c0701826070940b030741351b01c0b0036100c03500e80b105d800c0f151130305104103905248020009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542564793 1250 542563543 542563561
    0x6030c03140d0c050a142d010506240a09050607110f0307080d0c0510020a201c110f03041404060f0b070201210510030303150b0313060e010e15 63
    0x40d0629500100a0081c4189a98600d1554842c506c0c19803403074880d2101002001a48183d22100d505581c80440d180d1080c00d0109402d60380000c103014416040c8010041c56020f030024503100c1d0a080035002c43c0d0325107036403034180c0304400241c105c16040075011a64504121103c2164602c107102120b1340c51004801c8410540d943d05d140c00b4104550b0056008540a9401110461034003032144040d103605d891140d20040882e0840d400c1d410005071030305135049203540b5501c50395071545220382c040c02102d401e1000000d810924148040d0810020548100e1fa11206000c1c44080001d1102600e1386c442d501c80e0064403031850032030a58411460008001034080d45900400100d0321047c64050600728190015910f0390003481e50fa070f40b0150942e4550112290610030b0358071851200c406090110f0035801e000b0221140036613144100301c0204000d008d01d4040d1002c0d01c2e481010322007a01e0a2010380d142400c0502000003140c0415800e06140c4048002c011030303540340c0e1810a00c0580c07240e81d140060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542566043 1250 542564793 542564807
    0x50609060d080901030c0e0d11120303101a0c011a18012306071202101b02071703071502040806060d1205070c0513050108070504060308090402070606030c03140d 71
    0x91018a0800008641d54000c3e0002c850120044c10041f0581ca4a1008620601f041071400c84580020040a030018a841c0400d01325078130b0360383c00035030851030150001b070b050814a0203071360740012007c0c0e4072051000620084905c0c8426800c0280600b81d42c246c0c99018100341181d0061083d01c641c04400c020900d0218894100d522004c80c0d84a11840c090381030703446038011407280f6000002008614041076412450251046040e8002d0402e82035a40c09507048540071402d018001c000b1072280b0080c6c0c0c1c2d00044041c183d8440d4413140051020720b00e00307540b0318400c0c02c0c8020b0031090300790740044804c0038030390141c03013112149010f0360b680340d07034640400454000d107440080c41c0a42407a1003100c814490000741444510071504901490740300e100090109808003900c1020603214801444214010301c1305100418065405211090666485d4001070140e585041c4c092036010440c1d5050001035080036004580103094201000c1d12800c1003046501614111071651090b000d20380c20140c85040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542567293 1250 542566043 542566069
    0x2040c09060e01020114190612080c010c0c122007080c040b061201060302071b0e070e040b010e063115050708040b030709090e010911030703170f07051005060906 71
    0x3d8000703616900e001c0030083d908081030601f203155944000c042000e86202c66898180740c001e01d13049454451200000e400d440c148603d09040110310080c0c0000580c10300d030f6850031400036040003001d4110800622940b0120005040010f03c6040c1000900b54001f1032008003040054030203120b03040c65030040c4402c620548400340e071142c0002c0010060140720b540600700e003510403020807401120654001c4034040034ac0e00090007450001d018000303415000303007002641440960b018801e0307005c10740018102041d2043c910740070303800009000020710700c20702403500401c0c05424015190440c449c810544201079024003412030303402c2501150300c14000c5040e920000da109400d0f80ca0581002d1400c401e9400140c080e030b0a101540a01061241050117502001c0512100014140c4890f040c6910035410100125011340c00134602031000c1a090025911503061241c0c80e00d540302d00000706001c080c4200407011381103000b0481c05100c1b281c55030308a94000c1000f180d2501c110344810040182c1616249 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542568543 1250 542567293 542567321
    0xe09010e07020c1002010b030a0308010509090c0108181005130b100e13140d1d04020c030909070c1208070306170c120a2111030304051009020a0302040c09060e010201 73
    0x10070810243c6014031400ca252a268170000c9140c03640600070a28008940c0002c40104442e00010702490600c140941d602050410081c0505403041001a002c0ba07005401d8001c0b18244842c80d40c4503070303000c00c40000044030280d020407003864112a10704440c0c6071804201d0f0800300800c0415400c0003550746083c252140a0003442c0c16071100c003a08403147c50488d80c11505404000311480f0003103824440300100e001b03e520754611001800004a58030b00c144000c1b00d11645c410722015051a200109440314890191031080b140d1311350500907900c0f40c080d544014440e0790810b26000c100c960100d0f5280c001c00d070307580f002d0100c0d41d12840c0d20741d10060030f101002410342c40f180e50380c1c503185055405008045034081c11384141e083d0700c2e03c40c000b41c48225459a01910b29078002c3c0ba0790958044050020140e292000d54103504240e540c69032920031401100ca001502c86486038213641e40d83c1400c1c0c00440d4010010001e0745901c04002d4003c5805d0303c0b40f50042035551054001550040c020400c50240b60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542569793 1250 542568543 542568553
    0x204080c0d031d04090b070306050415140904110d050309130522030e0312040302030d0206060604090b04110a08040b15130203220b0405061308030f0403030e07060e09010e0702 77
    0x107540c1d00000540f511a90b07552054858000d0310101d000c0e0710f90a405807203160f80214071a801c00303050006441080864414401310143c0130884403000020340c0940b0041202c0200c099121402c0c9079910590f00c2101c030f90301c40141a1500d08106000008113a43c0718242c4071401040c0d80300104030101d60080f01c45075451542c500c421450344128641854034940b0a00305100700131220b40110307280180c6050010068140050103100358078013042039541d401002e100403e15450107102080d014000c5108814245031650b0480000c0d9a4a81100b410142c1c01c0b80f4850715210b580c07000500e03210303040d182a101d030070310301000c940c1c0d1240b082d407a161001c1d00a080c01d003449036040030500082d84000c080c00c081c12142d06c0889151010b4007902c800b4140503150505240c00c2900f081802c10602500001d640444075040c2c6000844050540e80d0040c0c281204071410303511818154007030800311032110400c0c016484086507180c2c018099442c0d448040d08d2001d4a41e80381e60640d500b5000543c0d070040540c0c4a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542571043 1250 542569793 542569817
    0x25080102271f050c0a06150303091a090111010b130605130e06160c051207120302030106020a110607150c0f11030409051e040b060f030307030f030510180204080c0d03 73
    0x8100502490509408642519081e92120007c8990080c1280e01d00c13003000c1010414075500c0070030031000d1b20355045510050782d54560010f2040c42988940d43c10300c4180b41c1400700b901f500703600907480c0480c040c0041042c80380c1d0701c1050000b000e86006080c0700341e082c0800200324011034032134281ea040d200d00c0200125101c0c003203165900c42031112403204100e50b03a500d54001580034007132001036042a400403070700c1c0c0c01589403545007485410350f10001c0510505c01000040e03400141d40c05001e41116500c8003d02070000411990700c26440041e100384881d03440d000e81e61115902860040303000d6558074580740e08503c1e0403250201c984040c41c01d268020321060200c0042d503441260804213400c0310282d81c0c11040ea64843e599001c036001d641c035580b41020081c01e410010340500e0340700400c502a610706001d0303a90241100f0010f11107a020180e9071000110061548440d00026001220304a902c0e1a20002c002c40039500500614059008191180c240303418040c00a0400c0c4d03034942c0b43c210885403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542572293 1250 542571043 542571047
    0x504030f030b040207062313050a082107110d091a090301061701020703301d0312010819020603010b0a0c0812100501020d0225080102271f 61
    0xb001096a6070040d42004603400040540c80b50121944100c0c051100c0c9140035500343c0c443e000020043c540405601280d0000a2400316090a80c1c41e48902c01e186c4503030a0780c445008121114001d01207034080700c401e111606800c0144100d1019241017268a640d07203449045030566100e01c0351604402c030001c0340e04c00d01000c03c0f010f86021140507000107402a600c44a0000d0000b004000c1c00e03403654005400c0051507030181e03039840d82040d050114224040720f010001e81d0420460000300401d9500c00a00d14084c040c081c8003e0200d03032000440c0d40743d50150290403140b0000707204140d401c0c480c0001c1c078060b5003822400e004907540c000303000300d045a00e051040c400d60303032142c0d28003001c01c403060458200188100011300711a042c1010015a54135110000c4440d040540d00200e0655000c0c191038248141d002415011203038624118260803e10015a0b80f80d105503904200203550000c0f90a0f064460f651910400c03070030342ca20401c3d002908142c14880c010b81ca202d020410345030840c40302000c4034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542573543 1250 542572293 542572301
    0x90b010e0f030111070f0b0105010c02010804080d1e0606030f0614121014090f0105090606040903120608030a1b0b04200904060623030d0f020a0b01081c030504030f03 73
    0x21074003800116484000d00c00750403040c3e010340f0f41219182900400071082c0721101d11400e02601c403c1c00d003111801c8050300043d14100d4000d0005003404070000768505c1032882d54100c2503000c40c0c080441442190320310101d40141100303002d242d002914160074100b02c1c0c425800307468212140d21001e0746141c6644014808806c1908012501314450400303802c1107100d2510401c42c86400c8405070680e1400c02012003410031401ca5401c0300542e050000380301035448007160040c2c01010464000503103c0d91458241c8000340d00e5000c1240745450144001100d04002c0020400c01c03405a1342c8504504940300440280300003088050445a451070000e4001950f0383d00743c5140303841c10103c0c00d200001c8400000c80d1610200c0c2c0c01c0b511030780c0380c5104000c000b02c6400c20204012550006e0b0341ca1050080203e584c40c008620748604001c230440c0d030850b18500078044010200e400a0308280c856850b0700016a03585031541d4040200d03030040b1900032071288079100e20390240d42c2c103690744403003122201c0084000d8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542574793 1250 542573543 542573569
    0x30e030f041d0901050709090b0d060f09030801080f070e0a020d0e0708061e0f0403031d010e0c010512150604050604031b090e060406050405070302091906090b010e 72
    0x15100030003002404100440c007601c0280051000c000c8000d54070301c1c2007091510040c203010141d0381000203110a40783c001074280c0136141c005200140059070f660001d1001150980c020b00036510313103203030700302180202c0e00400c01d020b010b40c4401c036059036030740c41c550f941d060130001c4d48105030007107101804400d50311104039801200035100075040881d800201001c0301d00e4070314000c40f170360322030101000258401d0010039401402190280010656a404681350300c400400c981c18400c10900040d040500076413040d035400200c800600004d0881ca14081c2c02007401c204040102e00c55078600202d1988200200c44038546604005582902c5e8104c000c0c0141400d0707000154442800d1002059944494010344000c501800030100076009008104c1d00b218155080700c0d10582c10048085440700c80042c00383d80141c0d21010000d5203035514100030342491242d0300001d50003840101800103004a0a294110b080c02a000c100a92039a5840301c400320381001c00d003140070503039030009100b4038588402000c45c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542576043 1250 542574793 542574821
    0x5070f0b060316151d0307050d060f0e03030108150c0a110703060c09051504060507020d0c080109110405060d030801050f0a0b040623041805130506010303020f0c041b03 74
    0xf000c04840c99001c1c0c1080c181d04040100c25601c1005040a648180503030743e80c5688502c010360411210300804d480750424041c0d03900408a0715520340030400b90b680003041900c0302030700412440c1000d40b01241c890388207200b03c40c1d842c801c14010b8104500d40b00d40c042d0054200c002800d251082103207054820303c00b0059408050701400c0c00000202d1447d001e01a00e1b10029a80e040c241418001082310f00000c9014070b20142c10103000900005402c0301c00c56080c2c1c0c1d01100c14420300d10861806c004020781e540c010300b000394200082c0c01d00f00b151070b0300c134010b0003402143d06020a075180302c1440304031035403550080d002400c01070042019042840303400c80d0b41040a80000005c980301c0c050100340f0340c0550302010008811212580210305240800003204088070b00d11450689491888000103c40d0804040090b50711008103101c0044003c503040d41c00c0d400030648000d5a941c3c01d010752212500581c0812900602400424902e080d00c50617880d010b2540080c680c58900b14001c4008180c0400a245 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542577293 1250 542576043 542576053
    0x1e060d05071b0602040f080703020d390608071b020f060702121e0304030803011a210a0605060f120606040305070e09010c050412031d0a06180605070f0b0603 69
    0xc0302d2040c01500c40064007441c800b42c0c1c0c2e03a150083c80710035101194090207e641001105000507503c0141d0602a80d400942c0114900040c0107000c40c80d80c65403103d040303200042140e801c01940800e500300304903810f607142c0d49902e030b44081c01643c810341032034600c80d040c000c419011001494030036500651000050b001c14203094007640407032070284052070144602c1d03005a1b9420300111681100c4032030140d5078405541810b1540e560084280018020a8042040c44510544002141083e108060403c0d0307211004440b002d032003200420010344501e11900d00340000032405041003801c69614581190f00740d460b0920b0214805228203003c0c124aa10076410840040840c004001c00d00c050503107261075600a04003182081d003102c90b406146e0050110a202c1000f48905074461202c006401d41010129003812100700c00c030000c50b50a10503030102c04904c01041c960382c8010083d9915521298011180391205001d4909000e224802441c2c1d41840615400144e14a18519000900942224 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542578543 1250 542577293 542577317
    0x100611030901140f0c1c1106040f02060928060207060f590109060809072105070f0806042004020d0b01081b270607030207051e060d0507 60
    0x241083d17121030404a120f51240100000300d5401032100300680d155420411940c101d00d040c550784440c401000901000c8010540006540f40c0004030348803640024204211090906a110507582039101c0d40c8094800184000c1501800020101c3c19521241c44424042d40040c100711aa030341c540c5c00c84c0080700b4142c2e440e0400590b8800c03501103612000f002c0c0607850401000402c004003044141c0304000988106405001e0341c01801400643c0c646281c03005460b901e00c440c0c40e03e84070305030344004c61010004036000342d41c1c82c0740303000f65000d40d102d039040c3c80040c0c3d5038a100d0903200a640c09028681d4000c24040b5000400002103e13030041c888151428030910103100140c200c0c0c2100c418460080d0310795500c1c1e00d856038010052584030a5101521a070310208002005440c005c55880c81402200d0f08000e01c0e8207484030810511901d40104602d40c0c491692500075140d941c076209260140031841c809000942d6400000745c0000e2014016509003046020f405000c0c0002402034000e01601c9441d103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542579793 1250 542578543 542578567
    0x2309030106031b0e0a06180507110703050f07050a030c050d240510120c03030807051218060c0307080403051308011409120702030c060d1103040302010510061103090114 74
    0x1c20486141d00070080d43d020718001a084500307100400201c42c2c940b61010600890b610824034a10912614500040342d548008054400340035150b2114502c0c0b1070b00400004121000528010b80c4202200f0b5419141c2c4c0c450a01040140c140001001c1e80c0c200e03c03043c0500d04124101c3c021040c00365a8881c52880032191040c6801c0c4042c6d80c2c1c1115903258401c00070a2417090200f44000d001b071192070318000c5102c3d20356900072480d0340801800c00c0390072800304003414400d00c15103034140842d52000c04a4144844840e583e11104001860140a40d000007805500304c2000c3e00e119685a03125501c3d0783e070b11541c0031110743c1e03c9045d070010308180150010500710303801d10645440c14035160000790142000c0b8929440d0452a0b0348507071500004000010042c0c0f00450780080001d01550540d40305c15003002d04001030803076141c2c03e00010350084208028140d0540000c0d0281b0038140b80d45020799200da20883e0107108001c55144181e004000300700981d44180c0c0c2d440c0300c0760236282160703041403800005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542581043 1250 542579793 542579813
    0x121b1a0313110a060f0e12030315010905040f050a05130c1406040b0f03090c06090d030302031503010e0615090402010503040201120b0a08031e040f0e090f150103050d230903010603 79
    0x2400614952540c4d4500c540111171a06d0100382162040445809100090b56a20005002600e803004081d50724020703900400e01c0d00d000e0710004105000103504540d07440c0040c0011100300709040d0526001ca90340a010b40380244050b40c0040300381401c9420100c034000c14207452911250480380c00c10001480e4101513019214000806000554038100303902d80300e05e806c00085420f0b10071001000078413016551213501c007850580c1070502503120740d2000070301000c021031040746035015424842c41c824066800f045051040b0f140e0054600c03842c400006009205204840080c04a041003000c200558020031019003a80e403d010041444c2d80e030031000c95410109988001020380c004a02d9042c801c82608622060b10450040a800c040c80c3c00041c0ba0302c0d0140740724070020440710300d01182140310284003000061b514801220241041c3d4020744440100900c8150345501510b1592034030325100f51641000d40000d4a024400001074450f903e0440c0e02170b010750390f03066507a841e0000005042d410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542582293 1250 542581043 542581049
    0x301020301030606260c1203070c0b0919061b1b030c17010b060409090f06020307051206031902101b0501020d060e091c09121b1a0313110a 61
    0x1c0c0440c642e844c2980c011300443c5000b20841500b00c841c14178030414540000d8008800310121442010f50040d04242421445020b0002d44041c015040c00305698031000020b141e88003040d9030b2100424030903118003261403845d01900d800100c40d014103020140d60012000030762401001816075415110041032810600e56000710f40900c5075080800698107075001c40208100e81c140240711442051000ad03800b07104a014401a41d691000c60005100ca6525881c22041c1e1015046540c2c0c203000310080c1c40c40d04031640282e081c20944000802d00d0501040c00c0c425030000d0000f030403c00185908100c1750180410242c4200031440c1c0ba4020650803541610304060f02034000142c1e90a560004401580e80c16000300d203040750030800f40913030040c001506c1c3d0075460298203802c0107a58101001c40d840b5a459100d09060021840b445041c052918040c2c0302c01d440ca00031907001f4a07030300c0b41c0b5403101c0b030501e1002c001385e400c042c0300103403410800f0050180e2991003480391002511f40301d0001a403492441d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542583543 1250 542582293 542582303
    0x903090e1006030e0c09011a0403140102220303080a0b030f0106090b030c10080c130e07180f3218010e090613030e010e120a0309091505100e030102030103 68
    0x4641080060303054414110304c00100e50103000c1c0040000f0218241e17003010b1044d02c0d040ca01501403d44c8014100d01178902665000b0782d01184ca034440715019000c0d412040e05440d41d41c0310414018030400000c0f50b1072084039416207640105d0399411021000802d100303619283c05001d142c4001d101c51000784521b40c040c1002401c0000c0c040b803404241440c160110341e1480c0110f484004c014240c0341c03c0200f542e031050340d51640070343d101032251840c9000501079014054216080c0c0c28040807035048002500c2220011100c0f6524990b6030311011808000c83c800d6a903c1b21400c502c0130f40390702d01e42c0c4545001140c0500130710091094680810040e40000c401401c00152103001441090514501325402c1001032000380f0640c03c0a00101d42c0360210010001c09003c48840c1d180c203d41d010340942000305400602c0000700403500c80015440b002e80f40700440c00142c3c240c1020400408610800d403081803142e8480144a0601e400d02c20300c0403500c41d0990510010050f06e403403c0d41c007400158040c511074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542584793 1250 542583543 542583571
    0x1305090109021206090f040b090325151506110a02100e1206010311040506040b0d150e030c10090f0f150b0301020a17060114070515010b040305100903090e 68
    0x40c3c001c0c0c080c42e0805021035204480c20000c3c0644030402c0702e1565000380d08261400c849071501200c03540f1f140310b0004181c143c503400101d0b82c151040c50810141c10a40a9803a203551003e008452608481c0e1050118039141014001030041ca03224515590451008504403048441c1e03540004041d46030441e82e4100180d4080c0c20f00c041814015500200d69040dc00140010f505545c0c510520f01c0610702801d000e00c3d5070783d0000740141e44540200310031a4000d04203904540007414414110480d40f0a441c58071070810260600e00e4000104981090306a0005014208826101c00e006070010100507034910702c0f024440e60105104040910320035101300010f800510354814841c0a4074075041560341f00c0d902c10b010801005400055002801444042c209200c7d07441200594100050307030b881c4c4403580c201007041d01c03c002d800225581c0801800140c11201daa8640d44032101e03106a003c02080c3c2e4004940c49440e40c1019009602d40301c2c031030304140b078146480710310b001f4481c0d008030340690b250956 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542586043 1250 542584793 542584807
    0x6030b0a0e070f0303080a050604060905090a141b090c09100c0209060a030f12110a05163512160b0106050c2a181807150302130509010902 61
    0x70400038180186101a0359008581c9140c50192031900c0c020b04100c115031715200003600c1507a51798072503000381c150820100011f0030900c0340740f81d40c0d10354801c04131890301491203050f29205002402d03040e9241455500d1910342558001d006988202400040000c40300307001e04003031960303411014000b070000c550700d8a000c400c06004004074002c0207440700780900901402840403401d0710a2202c00ea6800102d880c100b540100d004803485407003240c5028032070054007241c81c20084045440780404800000301c220903034980545124024440b40301c0003034424031441507040901c900c0d1414102c80120416640c810b9120400c00450351702101400e01ea000000e5202c0c000c00025403a050f000d000075241240c10032034841d0320a81d45004e4104026070210003030b00310003072404415070306000c61040940911407149843e420707002590015140d501441c614141d120f80f20010000d80c81040b6a2051041c3d00c280034000310590017540858250b0200d001f4807103001c05e01c0e03200d501c04a8002d00980d040184d8a510b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542587293 1250 542586043 542586071
    0x120204110c071e091b0e0a03170403050105090d0822020604091e0c050a03020c10020708030103021e03280c0e24030a120c05012a05090109170106030b0a 67
    0x140d0300134508a03490000944070326050700e43c0d208007403143c0b130414500707180c15074002451021403035100030010050b20240d69640c0c04000007500849114074024815911086400c81e00c42d421403401038000f90b129400224101c4900d110030b0106e4001e0f40b041c0d18010a20b40219810340d0064100000f6561140360490340c6956068403e03000c2407801c581088015401d0b04020080d101c1c0010085c101a00440d840900368401d020306612007000450840d99070809252406294109101c103911483d040c407442043d08004025036501c4045c020302070401c90701c5c1d200040c0305402d9441d000e00c048050808403007000928081201010700b5a48058240c00e1526815a1903001c1071740e5500708a00381c0c507440e10503842e20f00181d50b61544e07500501603604429029021a2000310140015001d0343c20003c040320211003c1915004212009225100b20803403410103445500c942072030907000800d011030400c151000c60a000d04129907131380000c42d9290ba251102d016007001a121082010307070f1201d00401d004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542588543 1250 542587293 542587349
    0xd0902090711120f09030a11010e15030129030406050a0c020a030c06020c0f03040e073b03010b030109050708160602120a02030d06060806041401120204110c07 70
    0x1031481c1c0b605225006a60344840d4a5507003100105241c1c5001140c2010030030400340c00d440d03a10070043e0403102c0304020390925054408031032005c1c1e404190644030120741c0d0f00b800b415180180106014071031440e4600b51a00d0b050122031008c05144101641d0024031890f00d840066000e58090b1101040f2410041c051908a8000340030501c151360000300c180001a07003020650a030f1541040c80140c454650880550804148910024081c0800613011840c3c10301c3c8141d0b18050811075441005220880188a89080e01d0344243c0803442440c4441c0b4014448645207030b1500600a4000300d00000e5640220f03080d03480d911000c44003900080814442d0328000c102c0406a600c1c03401002c60201d18014010352aa0765013503040c440307607000141503400180200300b02d03129805171a0301080300c1c0d03942e400014a28a8181c13885072082c1d00340b40050b6103010303084040a05a90901800b40400041c0d80d0800000704465404151441014001c1d040280317818420a0f00401d0450f640103413003205512041c03800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542589793 1250 542588543 542588551
    0xf0615090c0c030c05150403210c0c351804050412110a0b0403081501030605030d0e012a0201120504050a020d080721020706053109020d090209 63
    0x400e10701041d10201651021404114a0301424080040d89440c2400ca0410050854080c0c61030108400c1c44101070b0302604542d0b49800284c035250101000040031001d0711001864400010111403001012801c0310340d40c207141d0b40c0021591003042079280d075555010b01034000640080e01c0c0218034003104e580200c40039000e10f00304880c10803e9141c582d4039400340d45824040d030002c00801c8080307d9081c03c010065802d00d0303504202d810b441440c140c80d006043d91011181c400f07503550801c0f1601c0c003a500074058031065503002000f5000750700e2100c60440b82d4000f400000b81c10030100004036000030000740034040c1d10440300018410b0000003030002400e1624824504d142c0346182000700b00210b2400704441a40039411910744000201c0750511662a00070840c0192840d5000000004010a800441c181c4084180c00f95409960ba0f400701751500e005141103114441003e02041c3c054404030081132204962030300040c03000c1e80c2c590a00c003080340c01464601100d02c2c1e0301c0840c0c8040d441c0c0010070a0340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542591043 1250 542589793 542589809
    0x306040209011214030f13150c06020c10060306090627030302030a02120f07080a090507090e031303080a090f0b16030306050d080d1b1b030306030f0615 67
    0x11428a80d0210380329200c148900c1d00d40e2202040e15400300a80f08107480607012001c012652a025043c02c8441540d200003400c8900c0d950781d05001030000c5510300362070032502d440d844024900f800d60320741780041d510500b210034050040d4101d0070034030300b00d500c1144051801220300050101c0750740b07030440482c1d9900c810030b01c940e80e0248103200703001c840c030140580c12607041c6000340e10b0341c5078001e40030064015400300541c03540010081184200c00e5103901c9100e4142540c804800352074612140d000c0b603003440005890340c1c2003900300f800008126000009809050002c807032070003940c5402c100c50b00080d84c004881e04000041c0f0340345100e034001d58403009010350050b040304151800682c4043c520595800300c49801c2e8081d403160505000e07034480401810094403c0540c11800d1034021807a500510050481516001c4c3c3d4009418841c6480c1c2c407204916111103034003507118020101c6812071040304908050b11800b0100025034030100800f8103a120740300104031160b44001d40040e01159421032a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542592293 1250 542591043 542591053
    0x120201090818030a0602120f0606031303030b0f0301060305030a110123151003090b0a02090109060c0606030c0e06100810090f15060f0807080105010906081504092003 73
    0x4086600c05040380c2034580d4030502d6000c0103041c4000320741450030441c409002144003048600804480c1030b411885980d210081c06040d994420400940b400250380b041c1100520f4444100081d0195003c64480500200001c5289090b500020709450950300200c03015080460780100f41601301020240745425074009101e000002400d54a050003038481d81e501030030410b03020072400003030007000001d40340d40038000c0d50480b44c0118010707000d070200400445801c004031000624001003807090b01c40d0088160b4034040c4551a20b28102d85200f1901000d85015643d40070004c0094140c407036513070040184401c92102443c2290801002500780091a428810480d0400842c1c0228400344029580425000038007041030382c1d810401088106410641c0d15103192000c40d00b04d8020502012ba82d0096481304030540c1c5040040303465602c28440d1602191520205000e0107020306c060a41c8425565801184880220000380030b854050b8401d403086015103000c1482c0b1180f0362200b00c00080c040c1c00500d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542593543 1250 542592293 542592311
    0x302091303020604032a050607090905060d0b090f030d0b310c0309080408030706292e08010e011527030f0803060901061d12011104080a120201 63
    0x1035120580100000c0402112010f8460500500c92606ca0001c28008111811003c545040c9035100030580701c010114000c80b400041ca00058020107100380d01c041c00400b441003050b41d60520452026150000e0780c02011a0402c0300081000544000b000002000c140e03011120180f001c00c0310b0181c54600c043c0101e0b0301d9028030690948030310070300380720003200081c070386681400807001040050300c02400f40400007800a0041c1c4008050003040c2e0003107000b080302d0400308111240107030075a000c00c170085114121140c01032401100c00420009003000c962000040158003141e69041c050f000c4d00030520034401070020a64801c011030150060075051844441c1c12003000d0942c45944070952070300110149039050704004c80710b010000f143d0040c01000d02400905d010101c40c1c1045030514090345007100001429803080d00040da4444403201c148800200d09001d0000201e50140020425034941c0c40c1c561600b200c9000500003010030b90003801c00010140380800c0c1c09502c0803240d4007160706000c40c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542594793 1250 542593543 542593547
    0xa020604030e060906070b06031b150a120c050d0509010507020a170c070f03212007031203020702011124190516080906010f1403070302030109030203040302091303 72
    0x4180c005805041000c0b02954a00000301c1c544207840c50143c0041010030340314200946260751502503c002c03000c0c1d406100301d01e4650303002c40c50020707049035210000c00064072258810800421416900d860445a9042580760b0407040e50b07840381c0d041001850005003034405065500c41c1c01e800401580c001e112505040320000d40d100c80398040940001c54117038800d440640d131030044030008440081a03c41e02c540d04c0c611a81ca1868034071066030b0311803203000c81c140b4481d203542041c0e02408190b00c600a4040d81170f80c403031710181c02803c1c0c541d081d480303036010100204055a40340d560608099030701681c0c1d06800d2000402500b8100200000c1e17600512610031101c070003041503400600c1480c2801259501c3c172200041c50703262076840070001071421301404050140311140f440721411580386e03031106e81c9400f0461642d8a400340308040d612000e0700e4050126691070200c026107420000d003103d4840c1c0c0ca940009003180c0401c18101d0269000113070801c03c500386021580c0d80800c2030344e0f211800382c05607100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542596043 1250 542594793 542594803
    0xb010c050c04020f090a150216060801150c0f050d03110304080304080c1e07150f1d03120d0501050f100f0c0303110d05040606050406030c0b07230303010311060a02 72
    0xc0381e40b240340c0102c2c0c0503115210f9181a1500010b008100e0f0a00715038030031540080b030980300501c0d4018000d0600d2070341c0c0b68444508020440d03066503143e8007960320305204040502e651070051302c1000001080c80c80480c0d28050004200340c051809010000c04441000e401c4850321403240750702100a05c10000407030070b58000e403030f8000e0304840f032645d60300d00161111381010408070351500b2001c1c000a8005d1942c01c0007600c94103651000f403503c0c2d403007490540c058078040750903050300c400500d1034484030498464441d6070501e03000e006070844485800b031b8050544660001c109403a40e0310369540c0104941d241c92202010410800d590143c00011007540041991001107500b00500c003000c00740608240c840d500c9031b07194110710102180c80e03400040e1307031002030103059406584540c00c058011078a8645480b6400882e5800010a09814900905d81c3c2c11034000e0786041d910360314041c440405a40762039500644210001000e15034a604515081141003401c0385170178007030442840042442a00069 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542597293 1250 542596043 542596063
    0x105070204091b0e01030215191211180414060d0f0512030a0504110301051e0411090702031b070f170f03130305120901051b0304091407030b010c05 65
    0x1030101e8070030101c0c1403a07000e0343d40c03071040102101c00030907000030880c10380010b260691b4402c440c0081ca103500030030909030900805000000c7c02900300f40d01f140c524014000e240800041d03c00c08603481998014079201c0b40c0000004101c0c0c16003031035082e5024585403280b0b500003e080c002150361410481c0c04101112903800008048400c584080d0090000800c03102105981c0483c0d020703aa4500b0030a400c1c007900d4299000c86083d450900c0c00d111301d28040c020184a41040c0e0700700385045040c2426200c03002e1001d8002e403001000800340031180d80710000a1340c89526603400941e525503110030542c40e02f010316403004081d5041180203004500e0090500811aa201e80e42c40e504040c42c50001810010a60881d032128070000a0103402075002c041d1180032213000e0425205540c0d1585800001031141d4411180040c4040004010203210541c0e07005031440301404603130906403030709e411808840545030611030940000c4104104568940103042c1036103000c0c40c0840a0f034405940341c65840b035000f0303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542598543 1250 542597293 542597299
    0x9050f061e07060b0301051003061d2d010e060f151003090302010f0f05160306150f02190c0e0a020a2a0206030a090303180f0b1905070906110c01050702 67
    0x2c40d02e050015035000680743c01d0008008010324107218540465007807447c0b00032515241041040d00060078250300705c040300341142015102c280d003584a0240e2040b80032920300b54a0380408448020b4080034407400100742e042000921580c01e00003000480000020180f460240d440c964011705501c0300b072075002c200382080c10086403149084c42d043c0e01604400d034901d49843d1900103c80c801c545203420050040341c81c221103c10040344038000b10f00b6508240542e841303015484c14103801e001d119108044d03c9842910544e554628403e900d00940000342e8816141c1001c03442c000d0203141002e018258202c80107043c00c5150411180000e03041ea0f020404a000481d081e03170105503410f0b1101054020706034014609540e901d8400407450043c4494003043c0c00080c41c2507a0780403610030845a4210003500070406074000152660340140c50785004000c1011031803406200070001c0003034060700c0c0c0290020307100c2080290400310003c010440d401254115648403034072000313191741c1240448400d50340603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542599793 1250 542598543 542598547
    0xe07060f0f090902270d080919150512070918110c0d03020c161a07030203040521010b0f101404030807031218020f1e0a0609050f061e 59
    0x300d007003070754145840d90002c416a4000200c00d004801c43d0340b1404442c42d0b40d8030228400035000401d11094002242d0000d2010000304000140e520344000a02d44400003002d4486101c0e8403020116404c00300c0c00c22940101f000481d44240b950070317408a203a4420601d140c14412039140c000c80e0140070490020102401d641c805070100d100c0b500004a0380c49480c0541290700000c803000d0020000d60000d10b440000740600e9181e442c046124140c001c0444001c01070400501066090150b40f55001000031419844104400200c81d2034480380c1b070150455408124480005a10038107003590100308050b48980c50344248200640e8072144e5100324180d840c076241c003035414811031142c20351065810150440307201003101010540e20010f604640004200d043c00300341030420cd100c0d181c54400000170340c0145800b0840000b0f04210125281030101110021042142c40300899003501031900488002038208006114a013020000c4c0c0b1886d10098030618079051038440a106012141c40c0d8040f460f42c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542601043 1250 542599793 542599817
    0x30a1b080d051e010f080f060c030403140702090f0603162402010b0306040503041502010203040807030f0219060c140c0a02040506010521071d01170c04030c03050708010e07060f 78
    0x101c1c104803141441d01015000702075856150315407400f41a0b10070386c82c80c0c0c82455143c00c482840030510601030062203078a1421a1110b0343c041e00c0c0b680600344c540940d01c3c014040c8001590b00d440ca420b01800c9000300700000c5081207802d15040c00d03018818130001011038036042104412100c5024125090811240c03a5840341143c128090714800d0212035041c407400342804107105004c0014402c0341d028107800102400803039000e07803d074001183c0180c2001010300c90341012a0080b0a0488030031160f1054074244c01030a10240381c036002c2c410b000e44079103540d0242005500d0300701015199403060b0507041800c002501562903902c2030049070080c000c5850300046000759006405560383c0b0f240400402d41c44040d03071038040c42910403c4030020002080510000110340d11500d1510300e540040c1e442c0084d503c07241a6030501d03480701a02030030f00c1d00d001300300010100d801954440050740c0720314080c182041c6000c82d024250b0305e15410b004102c0d00004004c2180581100c03112514040505043c030050907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542602293 1250 542601043 542601061
    0xc1203070203060f06240406080403030b10020c120c1e030102090d050606010e09070c0b060a0902070309050a27390809120901270602030a1b080d05 65
    0x59000e00a42601c1080144008a00030303910852080c44140c40d6003c01000e260f04550100104452040ca040c804100c203100103449850255842400b0342800705403521010040380340e11201d203c42c800141c00c521036540c12481c0c401c4125203140141401800b818503460700049240643d40d12081c2181601c00000e03603a51800c5d0191114118000c004d0419070380c2c87d061860311000119101c0380041d4040f04105124901910300038080d4100795640b25075000704d95109016008090070165000c5100b460000b454203550004180e06e034407030b90b035048000340340c2424042540c1a58100b40d110340241c0701d81490f0414842403100c072262810f140070801c100b0304001c86144005507004920b00030841001d0890140541085040700c5945544403d015510100a20345078552041c00302c01d102410440c5081a40c0b00d135028280041400c100402c650b121920307444040b0109030300030005a0000306840c8006504010b58200c11003407500301490f0087c1c01e64440b00944602132403200c107150303100d003c940002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542603543 1250 542602293 542602297
    0x60b03061c210503100506030408180406180c0806060427060b1303050d020a03050a03090309180506090a0908040521070b190302130b0708070b1501030c030c020c1203 73
    0xc026400e90042c0c1e41403410040c1980d00480360a500098001e10000c1c1170708003601101d01c180c0d0449915410200d22151141080c1103c4800c40e5005480e000041a0101c105051000941d245200041e0f07004001c040a09518402060725124240601080120440c1d4440a00c27048116042454150804d400380c0c070000c0c20280c00c8042c000e80d010078003280d003404001c0400b040d64041e400b103400410301480308907580c29507080020001078041c803100111078040e030060071400e403080c206070880e039444200c2102c03c903d104910443d0b49072198180041030805588a6030031400c3c0703160500c6007514640b2682020301c290b101e02030080206280d20305c07000a40f030300300d51924059981aa40800e564200c004402d07040350350a031001c0e0707035a82401c04905001b8402c95803501c444190040d4182c0ca000200e2503036030407148064551031030421040340020344070702c4002c0c031941054882d012290b502900040484d009551a04145880c04810400c6140c0008050400c08000c4402401c42c540d50f41c040350942c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542604793 1250 542603543 542603573
    0x1806130204020c030415020c1516170408060a06170601080d0e060f0703110d03090b0a0207050f06070201050f163906020702190b0706090c05090f060301060b03061c 72
    0xc590b80d100c1b1011507640c041203085a026084804043c5964000038945151040103030340d4000e15070416110000440d00c400401d9414030309207500c2d003441c6d5220b04141c1800011602c18034025914002031001c441041c0410540c000389500a041395030511503029030f280e8013441034600b40505010070782203e0307555200300e910300166074cc0d00345e40b0b07083c003854060a00c12440c181007202e4040c49410190340d520a00c02d101c0328681010703002940b9210003142100075480f01805403011f0007200403030498075a042003c18003c00b801d600000e101d140000714980441e4001d04068a0f02c1c4208900c0c040259103c1010395403c2c40a4607600d00e584080030120600550350142400c55050b098a1001130100c00d40c05000343e5402590503d0390780d0710400040500d901240540c0d403d644c0c0903c1103034007042c519800000e455200e545d0b0452000e4481001420b03422044541c0751500303141501300499070a003802990000e04d01c000e411800c5051110000b85e41032140058104440c03821f440035010b01c0711400c1d600034a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542606043 1250 542604793 542604809
    0x8121e0706091a0405010f05060d0311011104030f0302060106020c01091403070e1e010f0602150c130b0304031b0b010b07030507151506050c0a02010509030c10081806130204020c0304 80
    0x1151031142c00d09000e41d03c00c40d0151503c0d441c001040c40255100d000706841498000c2641e0900401075a0965010002e10101c2d18150750314006800b0700b004020080c0040e60140d079844540801500e4000e25003039050304100d00710b400261350850b03a40d0300954458103861009543c808092074003808a45808482d60100c0e00d1449040c00348011004505941c461103280103015990780d81c1c82e8116007203805510321403400107a00c003103541c0c0d240e10000c120702c580126050391503910b060140c032510312520300b5503080b02a006c44000107000400d600000c0e0540301403000c000c0300c021440c054541c440c0c421814464000e9260300095080100341c0300b0001c80d0109130f8010041e03400b0311207240900004048887d0125076203201c031a0049034003030148054034101e101d04401400c000707a52303034011285034001400558041c4036030b01030170001e550740001c14840030100b0b584d909481d29104a078080c084e55250302e42c00590b004041030014402003081c962000c20b0b01610050ba0b1400c0d542c0115203188504e6001400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542607293 1250 542606043 542606063
    0x2150306061c0b03011505090115110703151406030607080613060801050708011a09040f021b0607030b0d08040909020109030203061501034209060f08121e070609 71
    0x4400c0c031143c1c8100022081070300200203240094110148410490082d02d5201c5000b100402805480032821703030704c200c141d180400c204490a1034140c83c1407041d41040796040b852100f0203031080750901ca062500d203046c211170700040c10100f002c40d486080141c9810104010000002c1a03601e13241242c20303400b0441c41081004039074072900e540c0202001d80d442c00001d4950000050002503444400704010340c0780c40c080d41780901240406c0000c001074030000b10456000e2105511001d0038000c58950800303184040c00640c60040b00080440300c28041c43c9120740c040001c480701080070310041d507084d0307086100000384854050006842016095000072b50510410082011084480508120f503060a0b00c0030710086003035044100c1c1c0c1c51116034003000c510403401100d42c03e038004c9080b1641c9034a100d541481e4400e842e91182c41c292143c0d0f41001051810108033000450010441d00f548010b4079200c190401c5621441e4041c0788035012101e101e01c1e40c02084800a000c19039002c0d06025a04c140c00e16 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542608543 1250 542607293 542607337
    0x20f0a03140613020112150e0a0c0305090d021002090402070602030727150c03030603060c020313050406120b09010b03010504030e03100c09051011010203090f10090215030606 77
    0x84a810036003003104940b0700400c404a00b4003001900c114500715416101c41007090101d00c2e102000f008103491015814800380c800151040c0082d00c5180a003008000220303901041807400740c01c0d00c0c806020444164010308424106690108410600c42d0b04e03160b0150f44c40b0040000100a1b0007884806841c0c540f000003482100d54100c00201c22805244940707008403140182a075112080130300c00c0046101c4026200d102180c490746040490a00c031b82070004801d52a6140c240c100c3c3c1e4014a0500560300015100761b16a40c0c00514000820080754180115420b01e410040c2c2105194001010315402001041040f130081d04007500360003001e002000545001e040084c61548103440c118020700650b0403150148006003c1d0251b1070482d81c641180303c503c2c08051182c0301441c0b464010801040042401003000280000c500500360300c0300070096250304410040c01c0c855041c00d810925481c080103503006840b00c9189a280d00c0341d07501c84a0301c0b6a41c05000c07400c3d51007201c0706100d103a008030400e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542609793 1250 542608543 542608553
    0x605060d020a1706180a14070e010207080109051b0303070f030e01030501090c090e180a0c030201031401270b040c030608071d0c0702011e0c060c03022104020f0a03 72
    0x1501e019000750340c40c80e42c3c21060404101c2240400c1e68503e030400c401c00782100f60748040d000d03000d8100040c5400055440301e41d20202c40c0300340f001e803488000603064540342c1c03500390380c1002040050800180200074041543d0794a503a01c0c074507203842803610a45460750700203541e418000d46d51a03903000341100e803030210fa901e00104014113200303003180401d14100011900c21540e2080b0000d0189580b40e4100c0c1d1401c2400d081c100a100400010b488282c0c1010b80088600c24420a104288130b07650032100c9500354070000d001e0300e41140c070101c50308550f03400400201c6040642186603030b0b0740406040c2442070b40b00044018090840c4015041414080502640d99240c0d02c031204981d440403d8840c025254000d88600c2d10500174a00e842e5001c000100d050340880c500207080c0a03105050080041d030b0410106206100510614000310304007040840a11a5034000e00c1400d24440c501149080c20228040412940404480b61140546000103023103450b65a0014112a002003008022560b0780c601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542611043 1250 542609793 542609797
    0x1170a0e0d030603030c06110d0204060c15050f010b0a021c02031b060912030a0204091e060602060f04150f02041e0f05090105120106050d0803040201020c0d021e040605060d02 77
    0x10405108041150041c24031030310030481030b280c0c56941e00c10301480d03d460740307005084c0d44078030302200380e608019001290000e0310040c00213141a4a5044084d41542007405481400000d8426070508060421985610301604907054460ba850320589491142d1400c1b442c02c041030070401e59a141101d00c0300005078001000c0c290308141d6a00c4164915503004107907803500000d65602e20994002d008031400c000c0d208001c0c6600505000b80141802d0b6102118000e4a603a81210140810a20b404480c1c881c01ea0103108083c0909000400c518100440c0c020307201e40e0b000b040501182803191000c9410404c2d41c010100c100c00c03a910554580c0d46842c1026003051010800b90382202c03210744000344840c1440864012248000c25244143e0300c0c28040c8000c0c00c21001070301e0000d55035600045a02e0307640240e442440360094030851786a1810340300180c81c3c0405500500d00c01c0b03200c42007a20069035202d14052000613000d00768065500c0d4031300814040c04403904881ea11403004103801d5a441541c1e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542612293 1250 542611043 542611061
    0x80d020c0304030b25020714030a050601090204030b0c0c070b030c1b1006140904020105090a03051207021017040303020c0f121305010503150405071b060e0d051303020d0201170a 78
    0x68071000746808241000c11048140301c00e00d0247c4c00203041000035016880c80c1c00450400902540d4542c5a00e907075940c01c1440c243c0001c426264046400e1060001c3d00194a9001c512806080d141c01c404107a00c1c6d5407804a44103411103920004001820280030300c043d40c2c01d0036107010740c54108a1291509907144c0c400d101505004c0781c9000d100140c000b480d540c0d100e010346000f6000c4040c0c1e03101d58004403110303402040e10980150705036000200152040001e6000702c00080f4080d52507400703910400001c8100800b4000800030381c900744541039100c2c0107406820030b0b418100107030313615002c08100c1d0420005943d651072a02072840724000c2c40a04400a160807040c200d0071710f010725103960064481c0e010603650400c4035540d801d0031b8141400c003179201c00d4004120742021800d59070880001c030b0156003920022200a40c5610600c440194104008032403c102405d000b0308044007540a007017880c1103032001902c5400c00c07290100569000d60701400851082010084640ca08000d040001d4601e0038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542613543 1250 542612293 542612311
    0x501060312032f12010f0504060509091510080712050c090f01060302030901140a0209100f0e060d060b19080601020303011a0c250f0b03060d080d020c0304030b 70
    0x310008210318868496141c0c3c148240042c001c601c12005600703100c5030748050042416034070421502d012004501101e5008105070200c10316014100300512055401c1755100601591105050040b0143c0c007103441c07819209014001041d90340c40b8101015400c20742c1d400704144c0d001d2440c01086050705104141a0f2a004034100c81c808245030301404601c0508075803c07140a4501e40043c0400b40c401d400840e0410702c85400414840044414001d018200380c6010182903800244e0601038207140700e01c540508070030305201d112605c3d5031402503d1207100226651282c000041e001c500710310164085005400400c1100303860303000c0744541d1208105054609804100c000d40021007a61000048074165481401500004c2ca503038021009036401214000a00703001b81100000030240341c079443c0c803081e030f46c80da000110249802c0344070030420a45e4000c9002e00d402001000a551a00008818a40d9204003403940d134224a5500400034001c200e50000b5074000010300005020040d104c0034082d40d181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542614793 1250 542613543 542613563
    0x31b050103051003020d0210121d0105090d0206060d06181b0e0105130c0e0d0804060912171c060803120108010510060e0102030f0c03040f080d02060604050604090501050405010603 79
    0xb6450703c4912080303100003940407005480d0240182000310400c44485901c1c106003840020092114042e1410174840040020014107003540b501002d005d06500054800041c0011a540180007522040004c0c15503014442c0c00c4a42000c201d020b9118402c402c000c03494028500f8141c1c5003072080503c2100742000d05801000d8013149040d0800b521a040741c40092601c0c000310300030b40341c21000c2c0c900b078800b500a1110361040343c0801e072a0804c0f0300800c20310484096603501d0502e40c024210182940250380c8280401701d02c40c0c0000d079242003071051f22240c42c00b85901c0d0780503803c88544c0b0f080d081860340000c1d030821000117160035001014100b00411441421b50785e0b80c0380c0e040b503401c8980031900a0103014401104200d000d01400c03014241440610603a45001604500b0000541c07018190703100a5000180400c0505403030151500a08119806070024000c101d000a544010140029128680c1c40f000300780c50f9503455000d060101d80c0030000303116074902800c00303c1c000c05c0184815a58586a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542616043 1250 542614793 542614801
    0x60603060d1412030108240c1c020f0d0e070603060602031215130207020102060601030908090f06041508040c0f0b040b0a09090c031406010e03070b03040206070206032503020f0406030213031b05010305 88
    0x4010505823041284010b4141000004945034090802051501035100e03820004c40d58101c182900a009004d102c54020a800404245840c5800700980c822001c25280400078058982d02004070f81c00410544003400300360310391000c414201d010a54030254007503442c2c031000c0943e02c1e084d006420700a000347c013a104c0c02c0e5610b034015000c0d14850302004198460800508000b07181504407a0507104010b0f16050410781ca27040c0d45210304202c006040701144c6501e04200c10410780008500c050103040070b5910a0720301e03008940040e40214000d81c8a82d0b800852079400c4144205450001440703050001d00c105c0c0840701001d0000c00c001800048001984000200c2550080720790301c42d820005002080040e140c18585240c03900050022a8882400c212080161786d4a030065801401c00c400700b8059034150000314840c204500300c0c80e01c00d16006011210703104038680c003924116441070030b0140c0e0751203038000c0703601180645030001010009000f41d08031007100c80120070300640b03400b83c904000c00d4903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542617293 1250 542616043 542616103
    0x2030a03110c1c090b120121050618060907080c0120060709180c14090a032a06031104030308072f0712020d02010e191d060603060d1412030108 63
    0x45146c00540440b0601c0c0d0040100d0400d240080c0c0c02c1403210900315036800c00c999100c81c1051425900c0e5007030000d400802d48240c0b5018000c6542000d0010020518586061031146c1c0720100d8800f00c1d414410100c007880511629541500440741c0176106544280c608050050418050350050110a00003000c1560f04241c1c54070031100211040c0e2146500f444580c2c081c4840d551010302c000d40c00030060fa00c00800200484c2905502d100700342d0354000a618001180e11071044039911a50402d800d000003402403105140444054a40501c0c00d02056507490714240c4507860300360004d035460244038034641000030410418995207201102a1880c0719070300c0030300c820000d00000029602020a1030740d940190301511041510300b40140000002c680f11100b00c0100030000d900601d406607030754106002c00485050601d520035011101c503821402c000c004921141c000700c0008000605459403070180c900c040090601041141d41415940d40c0c49522468a0312091860f201c410000c0c0d244035414a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542618543 1250 542617293 542617297
    0x20040b071e0312020f0d0f020a02250b09010905030a060f0c090605040e0a09020d0b09070608281128050c0d030b060717130b03060102030a03110c1c090b 67
    0x6900765503010762452034065460002d502c04038010710380c0001001004c06925087c021001154914440103880b1900760202034242000e40204804088400c9440a48a00f503240003006031a0380399000c076143c0580c440103840c4119550455603041c0b0500c41903400308a4260403103981c41802200a001c1007902034001d503444142805960082181840240700c641c00e4441d015901c0007214201240c83e45540d00030611440100f8800c0c0c0b820040c401c1003081001c030410440300100014030b840b031100d2519101d400c030204040c0d40b811021007100d6200d96580d41a942000c24a69a0420440d58030122243c2d208074101020000c0341c0007000400c00406241d0207102510b40c910402005803009500d03580089000b0803c04502e194055001d00601011400d041003d0302071040341000c46555110214204c038111507035510110b10081c5c100100406a613000c03094400038038103810702003100c02203070100900d039002d03250154010b485407260050541c800d41102d60b5074415103445041c52661180c0b4180468 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542619793 1250 542618543 542618603
    0x100e0c09180f0606011713080a081506070c14030703062301082b121406190510050904091a22030906080702100e01061404060806060420040b07 63
    0x4902e580c0c0011b2444d0202c540e1103035001c0f0108610740703140e01d21655100c2803904151403110008040c0b80810044030201e003281c1c0a140d0045440d2400d0816503990740b0074200e00d0303000318a14054500d4600c601c1da03c0c20480311000e158041003c1c0044d050082c03a402c44001d040309000c0e207440c400c4000084010012074240351100615119440c031407120748600c440c0711068840301c410012450b0000e06980d0350383c403c08a40500c450803035102c81c280403080256040c1d00342d100500c5e003040d1040c1001655184002000f88040a0810315110109130f400100103081c1c101d405014120b901a8403200b0002014119100d0507000c0c2100b0700415002440c00f106040204c0002d01146070b005081c410326003d56a101c1c1d00c800350f0f20481340d00c02801030070003003926041036140310b882c0c0d190350080c44076610310019448038000598080010301d01c1c020910350748810242410f405580d032103d00c11828115003005003251600040715645d25580c071134400c00d0b0f5520040003910700000e403840c0c404940114056900706 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542621043 1250 542619793 542619797
    0x110a0e01210305120c0301060915170c09041803020717120f090d030c1101020f100209010309021905091321030b1521010602100e0c09180f060601 64
    0x815412250328200c040d05403403040c2d082c0103003071040d124a00c811841662007034a4041150380c89525110740030b099480a900b1880403045807111842803c0d41c0712503e2201850303040e000305401d0702c545803070034400e10400d20070a0b0003d06041e039030311660000c0c0440c0300020380300c2d6080301c6510350386520f602810301e0b10b902042c0f03042d04074804c68180179040e48060308520007c03a44c00d503e008907020002e40e0050802c101100407031100c1880400b8000760b262181e03071900302030020705600c842024080352181a08001c00103519400f03e00360045902c250f001440c081d074080e100ca0785803225688040040b00c020712981d807050303546200044100300c800c802d0050669109203a0f1a9003146420619541820440483c04140e030f90010221aa03842032a0f071a28800d0021880703948011025010301c00d03078001c66110170724291060042010035400500707020718144000000640440700d0000c14202105000c1859000c03030030742c1c2030003200e20301d00700b84940242e43d050803a110304550841507074480b1070446250340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542622293 1250 542621043 542621069
    0x152106060f0309080426061609061805030105040b0a050c1602100e0301060b09010210020310050d080403080a1e0e01050d090f12020c011d211504110a0e01 68
    0x18906020360059083c2a00c298400c500745600d42d018560b8031030441443c440b90407070541058036000c2040c0101a0412460f000c4144640d04030f401c0a00f20000510682d01002400c07001112101c81c01170306a0040c11005000f40194141800c0c80c4005e014151401420717a843c02e40801c030030019440072108010b5900d2401300c8108915020080140003c039000b07010303c280c030601d2070480d5030f00b0301c10100034022034044241c0300c0c1001400246002d140d140520b408610400510000b08032508404044a41c11505800202c034149004511030090b0f030300041040e0004520075504540240c846600380110003c0a094110803101c11944140100c5c00103000ca2020000344511455681005ca15035025184010150b49107940784050442c00c100340b240140c010001e40400d560b400f01c041d43e003500418000340c1100000c000012600e120380300ca80301485241000724071180b441845500c02c49000c9164007603840c030780303030400c3e0614081c0c110040e48110740341640818240f9030402200e060381c2c1000b607250 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542623543 1250 542622293 542622317
    0x10f060f02160609060e0f03120a1b0c050906100906050906070c0b03100509040b0a0504020d0f0b01080f0f060a2d0b030607030b0d02100915210606 65
    0x5141800d031410000118041c21005a010004207004000140714035076607100010f1070544000c00c2029945201840381c1e240d00c691043c2c6a6000034142d101003d20103065581d901c120109803080942901e400e1507011410381f904051002580f0008103d403000d807000c0c003503950b071136042100b649170201590021404885003402401d01c54000b030120f09002800031860041c0360f48070550411801d9002581914000041241d9540610310500060900f901e4412207410240c2e1480000d01000345034102c4155a03000140a565803815840000c6d86c0160040300c00313254034202006020401d0080151034440d0b004200300c0310000203007000140786c503040544119100d56144a014014480c0b000040c004580c1c943e000c42c9007803180c91a1a810700781c1c00005d20224800038141410310040540303050618003038020314551141c80b107018070301d0340c1211200f050411a21081d02c0c07804490708030070151400503200718111600094041d0965a05001080f00401d00d00501d03001e807800350048800264040d4401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542624793 1250 542623543 542623547
    0x12020306070f050904021c06061803080f1209010f450b070206090d08040206070605060312030a140105032e061e051003050705040b07020d1505060a0e010f06 69
    0x8015910b10916145142c481c1c01c60000c2e003031f600320980708840c507411040754550007140b61084000808241c10000b149610000800311034103061300c00680140c80010b140110000c8130710448007113605080d40c0f06281c0c200307056182d00a0207110340e06400b2038503022610b641900d44004240642c042008802d8007888980c0a4800c1240c035008a5280c2d0782c01c61856500140e0f414405512559881d030040045203801004d00d46081096041402440b00503000d200240c1c450400315101a50003440200d510b403070300d80c0402e00e009010824800ba01c039010060006400031074000880800f41c5074500f80042c0d80714410942c4076042042d020f00ca43c1c6000c858064120740c01d82507070a00011011002034425690b010030460451105002d0124048041003400507107041a01e902c100151803034200907620340b03120041c00e544514002d03c1e441c40d40c082440d00856aa010762688003940c0700300c01802040422100c40701622042d240c941c810090b43c4d01c04580c860300c1c2c801d010304032210304010808051030f0a0007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542625899 1106 542624793 542624807
    0x16020d031e0518070e01140a05030c0d0221030d0608011404140109020402041404110c06040b100803400e130212161202030607 56
    0x341503030600d10807080103100280c2000091151140c0d990070010300f481c03034400c01e0a440b5261000c200c0401030700e1000e040b10700c4000c0c0510500c03208020070480c0219401169056441520003030400e1819035107040c0502d0001d017125050014150f650710b00100d880b0f18072455075000240c03c0c0c0300c01d0f1700f5110791030040903010000c06c014011211210910103000d000581011704000690345105c2082d441449821390040c002c40d911a510841040140c0040b0400c500c200c2c90480c240c41901a880e04039000c45003000090b10072a03071640c0d9140b00b40d44014100d03400c5e1a90301ea07000300d2084820402440c1c0c03020f2203140034141c140207000b03d90005c1003008132501c01940c03c400c3c070310006c8a10340ca00d00940340e10345d00c419065643c01c00e403141c208907440c00207984203110010300300c103070b80003c2122030f1000468111003101c151507074001103103407010310760080d0076038060300c0069100c5102d00c81c = true := by decide +kernel

theorem cover : BRFrame.Cov 542446043 542625899 := by
  have h0 := BRFrame.cov_init 542446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542446043 ≤ n) (h2 : n < 542625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
