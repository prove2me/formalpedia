-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:25.689982+00:00
-- url     : https://prove2.me/submissions/81eb7de3-12fa-4e9e-8676-f652714a3d2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441366906 ≤ n < 441546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441368156 1250 441366906 441366911
    0x709090f02040807080303010608010e070912050f060916061101181a071e0f020c060d0b0f0306010e012102040f0606031a06040512100911010807090e04060903020307020310 76
    0x18001503103160001540c0000c9031750704104010f10209902c40c00480c1900c40c00c2900d000161201901100c042d1a46da201c0390421101c981c0003402c11001055101180c0320550440d006504ca2410143d1540003014041d10b88038031301101004107502402c00a64040e42e00000041e0b81580030204c0394070410310000484100c80f81d80040c01844c00203031500c0c0e4005206142800701d0348100d03110780d0b030032200510380c600c1404a4131070900c003540d20070015a10604000f5002d59161801800042c01802180c0c45551156810850011480c100002c84504841d8003c1541d289a441d18403a0b034041802c50340c26040030310700f180780680980c813503024019803c2405200042d01900c0c0000050440303524640b01d5201030b14085140000d41c0e122402c0c5e13810390720122a4101d603903040c0b207015480c0c014890301035800c550403d000305c4140700c001c8084811021086e20f032040702d41e0312060119400c403103900039840c0c28921000032034080340f020350018505601c21f00441713142c0220340e00000d1412010400c491220354 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441369406 1250 441368156 441368159
    0x40303020a080a02031e0c0d14010f080111160f080f0901091202100302030a02090310050a05070903030c08090105040803130f092c19030c0b071b0303050709090f0204 73
    0x10351280403160b01c246200001c6095080a8003590104884520740c2403e050600011847da010030500310740b8140d440000c100702d091140c0500e040400024864441c95500c00500014442c0d030601071001185800ca10503844c2c014000d06080322180564002d42c0c107004103905820004040e580107121040602e00000d49a800e0030000514000c12a0021080201c01080c4d5000684442140070314403d000c0c20096102e82d00c2d05881000bd02a564002e585403007400031009040d48a0740c480c902076150924140803590710742e071080d6100e840c644001400180c0e510341d58070124454138080c11640c10b05142a601e001d95841900386190010103e8415251100070100030300000450802c000b400001401c0c0505101100c50611058002ca0081c0c02408000d114000b00348051280f02d164961890461048130054100200700c161040801c540d05008038000c41d050a000c0c41201c01003505074004015144a20b179030032000390801804072001d00110700c030003084584060080ea6074240800d00c0068442c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441370656 1250 441369406 441369427
    0x3030c0a050705012c0118090603061404080307120f090308090618031b010e0303040302280c091a09183007050a060603060509010f05221a04030302 65
    0xc03040e80424184904440c5d40c41d41140060b80c5c0d9500102e18082d5544100341c9100142e403ca4000264854265924600416000c101d81d01c402c2c15a8050801000080c0e00c040200221000a03a0045e1241009100180b01184207403445c1b40341111a00b0080b45c07a600300003030001528010721048022988060400602d06010060f031035000d0408003940b198049581d030b5454a9200d1503603841400c00c0c0c8490388007039503d800d4001141e406255021aa80d030b11342803c1c000e40700d01e03160744402c4041c8068a030503824000c40d52003c8038007940001200501c1850803100c5401050f4450fa03071655844c0141e050a000d40d14112910720441020805110303072086140f0b828240003c1c1c2240100c0703110200465403c8807001c01005d04059001519182d03140031904001c0c0c0747c0102848001c1c0f00c00c2c01d00070702008100c25500031500941c8110003d000480c02011407038195030040fa4025007580120036600400c0011910256000d4026a0b22220008140c0a0800d000d08100c1d82500440d40005912405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441371906 1250 441370656 441370663
    0x50307020d060f0b0d0c14011806030b091015030207020d020a06261e090709020a0c0204060e06030c010e19120c080f0c01032a1101060902070f020d05010204030203030c0a05 76
    0x41e5502290050001101946c9640540c0014003c1e40f9850b03c030110800000d07401071200600f43d440742c80180c1c0442d0b82d42c00b00100070b05604500180291414070100d038034403070080302c00340c155000000d003030f00d0a54652204a000f0f400400040e64001c031411003075030158490b4140d40f00980b28903a950f2071240c10700480b070031514440705c0c05da19645284a04000500e0310201d011308142e40d02c5080c22416841e10b8055614040b9240c12664105100040c10f044603034004030002d032040d100ba0360520003282d449043e01002002190019019048030100b0b1015602c240091402c1d0107000f004404007603440c0d40f0f1400c0250058105c08000d008aa81240500605038215001801039000a1500254014010303894030103140145040c1030711006000802141c201707410012420002c041d0010480b0042c000301012030311207a035000c0c4e5107085008203450103240211440d4030341184414104440507800c1c44240c20740300105583c01d540c00e00c00400140d4051005000748a11200102016907541c01c00c5401d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441373156 1250 441371906 441371921
    0xc16121404050604030f03020a02030d0f083103050d0903030504110d0519050a0212030901110102040b0702010c02030f030304080301030b01060201180206070201030608030408030a0908060c070b04050307020d060f 93
    0x22400144020005030303443d0801c440540390703c07941021466070186016490511312200007585405410070302c0030b490341c1c00020100c041140e5900c2c3d07076550b12094402490345000407003d0410141720703401c0501c1c0d009020194503035680f1030b19219180c000d400008204442d41003a08900203030301c50341401305005034040610040d082c01c0300e210320002e8695440540e19481340c0c901c038681d001004d090500b485410700c41c1e8034042d40c01a00250b001e056117602e0070303200d6208011290100f200c001d454040640b051003594103407130450000910340030480c0c005495000d0f1101080341e01d8400c00f64291140f650500c0614010b510403801d0a44030350451502d070a040b401600f00c2e80c04c581c9001c1c00c40040c400d240100103600d0350161101c0b541c45c0c4841c00101c0c0a04641d400010051000007400641e2240000051061905079503c4407110798950035607070784071641030300c911100060910040380130a40302800240c11510910481e071034025142c0c042101d01200d560145ca044d03545004c00315449410f40120304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441374406 1250 441373156 441373187
    0x8040201030e1c0906090f06171306090f051e1209061b0c03151902030a0b0d2a0302090703020a091502160e07090e09070b03090f15010e07080c1612 65
    0x681a044c0301d802044400c02d0402035143e840303410702140a09e148010031003017032b0382c02050900892076542007041d071180030004102c605100d01000c408041e5079110b6070b0043e40620340c029044061000a03400c640c0c0d00124070321903003c038080004c00301c0e82034914120364030100c0a10240c81e0341c1c18000c0400d0708100241d0307072a04c84d040c403100410072a0300180c8400c5034039810b200c10041e1a0b4540002000061001020841e0000d11030101041401114161111410648440001513500005600709001240d202c029080034100001c203840c00c0c002c2d0081c01c40c008451801c071490716550040300b14090b040840c0324001d0307008590034140c000600d80c512409048410180c90039400d0801c00244030390100d02c0784501d1407508501141c1250400c0c4030900042004000080c0c8905000342055140d92401507848035070f104441d007031b509011030005560704a0700c260304080c2443c0c3d506c0030305503036214004000000c800340030408030f00c1400e100109602101d00850009449101c90380f00605044442c6e107486 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441375656 1250 441374406 441374429
    0xd14090d0f05040f0905071e170a0b0d08070204150b0d0f0e100b040b0d0c1d090d050307020a0f031d0a0f05040e01060e011d0f0708040201030e1c090609 67
    0xb80414003805130b40ca821100082400500780d0b580c0c01045404a050710b04003040b404003c3c110490391584207450001004495031001095268003001c1e10888455007401c942107154140000082810180507003035080c0058000304e030030042102840c442492300d822006040002140500028510f4800c054600e0500001040304078902c000f2195100400360f4103010789922050200d605860f1600061090440600707040060880d40c9803240d4105024000c58605060210101482d41844940740c0d0240c0d00b01d0303001c0c140b13400204500310b1f056800240701b40c0170352140e81442c100182400446103502400f0340e03180311450319030364408410380200c110b010340316003000c0f481803009414a283c0c61040712012a00010f29902500701140941415031040644c8100d6000001300042001180c0700ca1058001030b01c40541e40c0c003011004100c206440d0354001801c0744001900550082c1c0c058860164680211031405c000281c20712a11a040e000c5000040d03c00041000283e40106898016101c1860b90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441376906 1250 441375656 441375659
    0x20703020601092304140703170c0111030103030c0813051503070e0d150213080a0c0303091a0d09030e030a05101a0303250f05030a0e010302120604020d14090d0f0504 73
    0x140e004e80c0c00e02920140c041c5030304c40480d0412120401480d801103074000046d215018a000742860150000003205c80154244407081640d4019134040324141c95140d1a4000b560b015500c81c0c500c0790304505035841051558140210b0076554102e42600c0e4440e507214056500d1400100040c041660140110701035949410554005424001072620004114000503214110b101d5008407402099000800324040d2410300c1050004006480080c0c3e8000e03180e20b2010fa96801600c2c2441c3d4010b81821002141402404401360322500301100903800303898444d51200ea0000040d0034001c0c8544122180d600528807900c0b0350300c0900a0765603150301c05a0807405d403065040400d8403842003181111400d1000e00c800b200340c140d04200454030a400c0b04001228855038501140d0f207a004140510200c2c00382d03a40e2030b5545d0312138001c5074003140c440f810030300c41c9882c4c1405000107034000d12106c1c601140c43d01c01002d590581007070fa0300e120b01d41280081c120401000e170082c0000410b82845010440d04200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441378156 1250 441376906 441376961
    0x30d020d0807051201080f06160504030809010c051f0b0a0303020a12110a150f06050607060b040b1801050f06070c1e090903020c120d090302040b040e0102070302060109 74
    0x140d0315040006424000c5142d9541241121184070310051030800307120200c00812011070014041080144500c03c844032500ca43c07408282d414036080c1e0303560001c0c00804c018070001300c140005d0142c442040c1081c00d0a8480341c1c6d1800c0c180b03c60102810f0000c25680400400810036004185001c00c06490303400400d401c5882c000d486c0c04c05464060b1440440b10f803030324182da225810841c42071140400b0349a43c00c8003460001008000700c034420300c62504100c2e440081c0c04031403003020112003005003801d2404a0b00e0f684c480181059503011503100740d4400d10344a95840e810700d10206000a84244903031981054200008000c5115186008020038000f880000303400340201c40c02d655400c02c2c4c4001c140c1c401c2c03000e2004443c45400c012451740c01d00c0d01113001c1640000380940c2031a0100c1c1d50005002d012031020350b031002d00c0e5801c4000100f01d242c0402c05418198000403e10101a0012036030350092038015007681c0c400707030b81100182d00201c01008170990511940300b2003c0801000414556501d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441379406 1250 441378156 441378163
    0x60901021b06070c06050a080601210e010b12030406110a2f030d0c050d45140315090a03051602040518070b040812090604080102070b1005030d02 64
    0x203407072041c103228410440300340e59184000e0307405031030380030303c141034010b854407001092900840d050030003168507000403483c1d540c02200d41c1241104c1c1c03042c0780388020100051443c0a444600c28941d440e541e101241d98407a26020401c16480c0f4080c4000c0d9501c40c908040105544407104441e030140d00460120303800200550911855071511202e100d04026500340300e188011040184548d0502c1442e0b444a03450350494192842c50380503c050b50048040c40703006881011031510040040d803d00b500034411a0040b100c09500c0c450400301c41d1b14075160002c0c90400004e41a006240d16282c2124021a179103802c12a41c006202c980704da444d20f82c2019806155102c0007100000c0c140b240105240201104d03144550600c540c004006005d13504050701c84140c2039007246001010760050040104921300b440b0110303401c40c1e044a000304019522480003080380d81213962401d600070420480090141001d002504c90300b8064400604a418513000d41d0b000c0b5001584018081d0300800c00150f2140d0300072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441380656 1250 441379406 441379423
    0x9012f0d141e130f0f0905071e020f060108061006052104031218030306090903020a120e030f0313060f02030a0c080408010e061605030609130201020a080d051506090102 74
    0x1c10b040d1590040d4140782c030b00c060181c80081c000c541040903000034248484110103044541086090366029210b05a540c19580708485000102d481101408500d0412698030040d00351a807040d983c0d0101c0ca4442c09003000c8003a40050314540c09441030064116084507160001c0100703007000c0b80b80c00c03802c6255125074408080742600341d014100002d41490700400c55180d42080154040021006262140c2d5030581c00316400e9000914011001c203c2c021207102d00d081954258004081c4040c01c4d035a0064240300d09038090040114404103200c103601d042102c030000301644005503440750040c80000c40c020680340d1100c0108164904400c5d542a00401100c4001080d445e0819044940d0300745188903202d180d11000300d540ca018000b20b0841c20214085000d912a045006114452402c0496050100380c40040d8400d0050001c134184440c0d20300e59030a030600c1030040d40c6083c00f241e01c0c0c11300d20390840c4050210f4941c0342d501304480520495106540c4000c00c580301d40c20144103c0000359030300d060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441381906 1250 441380656 441380677
    0x20112020310050607121d011205040206090405070906020f07180203060d080a030903021002070812041b030b010e06090114040b0303070c090209120102040305100209012f0d14 77
    0x70200d1001c6a90340e6100014000281c030490b40c44000f4502141e015090040e4a000900c2c42c56180c40c0b22103074211030034104203059550300400c25444000c0c00080c980a03100b00c0c0d000400b0040a003440e00d440c020b0500c07e1155803a050382003441c152019040690160038100039411500c800d1100c185411300003142100c15038001600c03550740d84045000101c1106c80502205400309000b061142c6c5500b1104c1e204d4441d909035001e103a884d9902c08141c1c06840c100412050051005042c802c0200e4070055016010b40c0303920040b06181c00c0b29401c0900e00750000e40e60701c010032005001000000344140d0704800140c41c0541298582454001c8403110241c01604c00d41c1c07600f2145040e039504105544c1d0705030700001504105961454140003d5203d009541d005464001244220341010701c20398048a41080103004101c1c0b80343d1400000394002c002550520247c036240b000038524120244201c0d440c06151180c002ca0b46070102e40c0342031710151908041002d10110603800660700019901c07900030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441383156 1250 441381906 441381911
    0x6030f05120a202b11061006050f040e011203030c17070f020a15050a050615070204020d0908030a06060809071a07050f03123c0c09031504050d020604020112 69
    0x84042542c2e0510000d5805250801c00300c04202c080e1190410042103130003115110180440384640c10386031540411141030103c100c1c0c2c11020070030580203900418130380c98520b9440c4c0c941a114241d000c6c00c801c081c2c1180c02160500440030017016014840c4007060400d600f4001d18182601c9444d10b400703000100300f00b00b0402c140e0f01c0780680b580200449070300b0315488030414400700c1550050500130b0400f2a080b540903410100881c03291300340703030f1440c42c5c031000e40c02c842d24a0a83c06400b03110182d0300c5924141400c42c2d0314525000482e0148014601911700b032040071400c00e24168004080030009807541505803c03140f010403051420301081c0010520640260341c554445050440c10615100e2a048081c040050100a15183d01072440d00c107141407041105420181e5681d14921003040d4410216400400d0000200007a001d0400d03500148041040c0d1070b000d504404030342828035421054078604203010a200030400148561140041e103403004184516103a0002841c2c01c40b11020340c0031199 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441384406 1250 441383156 441383207
    0x1031a0916030e0f01020304050616090b1c180203010f110d091a090f1603081c1b050901090b070c0308032e0302120609030d0e010f06030f05120a 64
    0x18040e4118407688550070094901d134103004410140030f5403045074125002d0040703a00041c1081d10740200242d50390308941d6100581424000b103501c5d80d500030040709248503414000503188106a004100d4102080c0c104c0b200280900c1c0b0526094901e60460302c8a114200855072400c0381816080d05e489601c0c190020450710680d042172150f0040441c3e41d00c082131910740c100131415000090020114088400711811280c0b0f40c0800c003010059400010004501080129a00c0504006582014008041c0064000c200740944000d0058521081012400101c0c910b4500d681055a200084c09254180d601e807819030303941e08488800f580401400c954010000c00d400340d403450800102140b240c4c0250a01c6501c1104040140b4101d1104078480c241c814030300c1d40c03840c0d0007250700748c000c20702d1400442c00c002040c0d590780050419030511081c150343e1503000c004a030004d8080c4000441c000c1030312180007034050924a0415007400507143e40710b0404c12000c02c445034010102c11442c03020460080d03070310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441385656 1250 441384406 441384451
    0x901050d060902040f060f0e0a03300e040614090403030203041e0503030103060e031602060c0a0507240f08070c020f0315180a02030703061a0910030201031a09 70
    0x1030800e034201c107100380c3c404980400c1c2141c2042102095402540700c10140d84800101160f00c002c00700e40546e082000300b0f40400000306600c0c3c00c82c1c000b594422501c1d038036418414940d8a110103034450000080c0f100c0d982d0544508143c810f80d40549404145103901c0c0072500042070710b0810191008041560010004083c04807228204480c03504181c1607220b00d2015051440d0303260400e0209440c000c3c42c1c00480d11080300004100c51943c401d22825881d080c240d902000040c1e04222004041402a915003d0000300c00744a11406807003141a000c4000d0a1301041c0707048011841d0409040c0311120300a8110746800501c0540d010001c2d141080314036240f031001c15200d424001c0455051720070004c0340c08201003d01001da2140c3c0e500790003100907030507802c0c00c507a1f1502d40c80c0020350035811220701400441c003d82c00852610301c4202290200070300e52408a99400300454038042d004a40010078801c5690600494034050035542002510124581c00030300c2c855005454801a0b130040c0183c41e040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441386906 1250 441385656 441385661
    0x60b0a050417070b1b070e1e0601021213030c05090405030d09030903020a090c0e0301050114090c16080304171e0d0609060f05040b030f061906030209250206040302030901050d 77
    0x20b0414004d5050300e5542c2c2c01407495100038001701c00860390048080114004c0007400301c0c9442a0112072413102d0070050100f0040303d40c100074060604500401d03404540f001302c008000c1944004001400e4021840c5042c0300402c4a0a41c1005200d030080d6428400410070020544221104003080082d90200380d00d4141c9110406500c002d40100c840040051101d0382c0703030704c924802c0702c041d12840314200300c40e010182210300c24001c9035a4010b1811081d03e071404c101110f5503004042900c071501d0302085500030a0711581e0150100c0da0000000308200810800c81e034001c1d142c480c0d910441e81024581c01002c11b41c01c2c0841c0600c81f0380300c804160020741d40070302d420600080201c240301304485921550b200034400c186009940c081c5003800ca9080050400280081e05a20080090452a00c84104000c00c901d0242e03100c03c80b180d15250f0110160b540c20359624060a80c03000a507225075082808010080344007803545040d9004001004003094000c0200c4108031024608542d0710001c5001c0c5000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441388156 1250 441386906 441386909
    0x303070815041b02100606080718080f030417160b03061f0e0a0509100603050c07120215010905130b190203190b0a060e0f210709060b0a05041707 64
    0x10b101e82012641c3e01001c003005645003848040d41e083d200e149500340c01c000c040d600144900c80c000382880c4000794906208d501480c41040c00d41d601d03429015503030003016181039943c128000f681c0e040020200400e140e032411458442080340007030002c809840b100c1000340b444502c42c0719915000000000c3d00d507960301d111003030541d102c90f03101d04c1a640c03403050050000e5656060303503005004001e0041958540f0f41c45240c821460605140800c40c1410801c401826016184081c0c03c442440b900d40041c4404403141e0382081d07a0380c020041050343c0205c0c1c22401c001a400078224070307c1c0609010b00340d1113842c90b18189507048848440141c88d9000c0c100b80b9000050b600d00c1c1964404030902c40340c50340b090344800780d40640c94030a2100d141d80c0c004000b8034211501c102000b160484072121400c9c10f080c0f0004030080b500500e100b1001c11518030a1040c1d40f5006019452034000c200140584001c5109110141460f152001d0400003d40c101800d81d1241d03010341c0000f1101815000e01d042d070108207410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441389406 1250 441388156 441388159
    0x180b030a0c1704030201140117120901050708040e07080a050712150801060305030306190f060f020309060403060e060a0209010c0320120406080a020a1e0e09090c030c040e0303070815 80
    0xb540303072a0400a00801000c400c040054904100024129402a0140503a05540e4010f0898900c6110540c6401c2d44110055418403500303226180201e1303075a00240006000e2450001ca4a14100200a092050003000480042c0c5400e05005030503901ca40c0910a0010581c80060b03206480c610000d02d041e00c55000348110742c2000404010003201002440c0a0042550916580308860101036800c0020f4081c560001c6500042085094440c01c4500590303078590058034a080c00200100e00c66a00c1a001030382e00984882021214007000c05c10700b0381c040c600e0203045044c40c01c9800000c00e4551250f401904001021354586500c44031041d003142c40071108001c840d1400c00d820080c2da900d400902c41c0d040410010320008825000070f0003103809441190380d80414080038041d002442203d40da0b000010041084a010b407aa16045c9c14540103541ca80300a11243c2d0724181010f1030201c008070024001c034100f1148694010000090340d03040402e608240d81c2c0d5544001190307645600001209 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441390656 1250 441389406 441389447
    0x7020d120509040b0a051f0c0b1006020f010e030318010b0a030b04020907030b0f0103021b070807090e1f05090319080a0617060a0e0c12070501180b030a0c 68
    0x403000d141c010009148940060303800740310101c008020480c3c4106a885425008a4021004880610b6008411020042da81890040c5442c191541e0030309050440d0486501520f00341c060002540420a9800e03001c0540000d00001041e003d02030740324040a4128414405900c110700c662030029004503a001c000030f0a0800c040b6a2401c01d903603422401d0750180d0040d10303140c000c2010303188280a14800c01e800036000308140050303c2c0045000794090981c1503140c10b0240050580c0d070109210400040c41c035a0010aa801c1c149140c810441d451040c4114065010a40e1301505c41484508550104105031000139070f41d8032810f405003184510700c500c5080901800d122000c0356040a001401105c2140e0200300f01c54946410481d040059007010050b030b400b40740060714a03010354000070031000000c1d041e2051070030341d0000310b0b8100241c0801000250000c40040c0008e59200c206041030172184004c8842c1c49142400d2820907110192015110316181c01040e004580204160040403100b503d20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441391906 1250 441390656 441390683
    0x105101505090316030204180506070507230d08070201020406081801060e0103060203100e040803041407151e03050c07060902010c02090103050c010809030f270a03030f0801092007020d 81
    0x181860004c982c00200d1285252032405403002c428580800c10040d030003002400036494100b01501d0f50342150008440c000c26000540300b110b05d04602040080a000703000380b0082c0b0071041c0c050310700d8000405000031680b042c0f0007045140d80c04004190000ac08242c80d115806003036180b28050f049c2504080a140d401000020421505900031845a080c40b500c028900740c581c84c058051003401e80b00501240300c1440410081103690b003001c1118030030201180d104a9540e0026200d0802800224001c6007242c2d4009070140188441028418111b00e410800d40c40d00c03000c0c01c001402001c00117000165141005411a400b4942c00c05159400900071402036a5038684165503018101007240040c0030b03080400c00e2028004141c0d04451108065581091034550344031103c007408450400100d4074031144003001ea1a0000d2000156000f55a024480d504003030020700a61010781c0000c95061500480f001c0310400d8500e109440c201e03104070280d41c1d12207800000d2030034034580406003154590005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441393156 1250 441391906 441391933
    0x32403030521240a0608010902130f08010b030c040c020a0f140105011205100c121e050403030608120406080703020d0b10080105010215040f060527070e0901051015050903 75
    0x143c1c00185041c1d8541510030018000a03c801c1d41202d202d418081070f4094014002c4c00116005044070002d110403401d4081c1e0b80c1c0d50300c1c0c1241030b1103034004c00c004e941d00c030980d5090341000d21440c910a1000e81d01446000000f1200958a514010300907105d414400b441d6010089004480010011140024811540c540054581030b925801045a040c4909561a0808803041c0218118403450703864503003c218030301000f0720140c04001001102d0701c070041c241034145501449100c1c0541d0180c0d40c00100b4908001e981441c1c04101c1c030341000841c206000030031040e5444242694010313100d207405604e0b85000f00000000d08403d94003507502180011104095030b61081995040ba0000da088401a0b0036103140c02d07074145c1e0156005810500e8007170000c0c010a100703400054009504034044000c03d0119101c0c14440c09a245500d80641c05c140020018604c00301d041c20b400549134002006203040c41701c20150b582401d84104007000410040001031140540b0940b20071000160075507480401012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441394406 1250 441393156 441393181
    0x5150715061e0806090703023102130b0715021b0a05060405010c110a0b04081204080a0905010503090c190807081e03130303080a0f020c0d032403030521 67
    0x1820100a000e0455000404010000c1c4c4903000e062501e001c1e045c940e096409200309a075942541d11680080da0f14000481030301240003034040c5161940050310764a04010300c2aa850b00c2d6405210300f40c60500080d0085071150b501d070500000204401039450524079400c0d04000031034003624416005651920003480000302d400e5104602c2000200081004020165044084060172060a51019074130900090381c100301c050b0061b000d40090341c2010615000460009001c0b41c0850303140602151004000390055900b00c0900b109003416800c524200b60f03907641d20340005420510800c141c0c20070081d6484011080c0010b400e018007915030403615071401030b68a000d00e800791030040099000380341000c030000c010380d011440280c61149050b403868904482040700905284e4000341e8400d911080d00380144010190024080054002d180b000ca101900f1240c9810400741a0001d409645011410401d420000d4943c107041c180c2d19100384c1b1407050394540030761006108042c01e9500303029a101f01c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441395656 1250 441394406 441394439
    0xa08100f08030c2b0305040804050a150e030c0d080d1e0204030b011409041401150609060f0c0b0105060c010e0a050a0b07050711090a02090405010608100f0515071506 73
    0xc1c101d80181d00c5680c08103000412100008046543c44c019061015119400050f009400b070440c640c2030035103d9000408254495024410300b500307607035021503a0707034010f80e603121000801c03000352242a052a000c103500100c5000000c190342d0000a00d068001c1003907000e21001039401c0b4403030400b40240785644000350300c5800151039451030200001946021440e84ea14460304c05090b4030f5103501c0340c0e178641d12400103071121725482e9500c1d0b4990502a40384040f2200090409a55400625292080140c03104641003102c00070030006c803440d503002c50880410541190015218184d551200340e17121801000640083c00050040380310360300522000140480b0041c0c094075400080c5c0d12001d400b92010321030b1070001001c031858910074440624002108a42c443c465040240c0b42c03030182c2c0001012501c1c260442004980d0040600c04036080742c607008005410080c3d04001c4a078140b070300047c2c3d03840070701d41c00041a0100081010030860b041e924080000d41100b800d0003041d84400d00c0c0c0030114400e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441396906 1250 441395656 441395677
    0xd09050307050a080c01080714070f060e1914160306380f010504080a0c090e01090201051204080415080703180201080708040501020f0c1006120201050a08100f0803 72
    0x1c40c01c010a40d441c15901d00c1c0d04840201000705a4640380c0e40c015290407400800500c02d01500124120a03146514010840a44030f809101140c0986241c058201c0d40112161200d50f03000b9035003c620720600c0c5112815461b0441140300502500c420364a2500004e68200e044608001d02c0c004200b00b01034001034020790100b9003180c0ba103800f1070440714910503085807945548500400c5807180381010450b48031500d6041c50220300d01600e50302040c1c0b070906441c800b11500c6c00c041600b00004200b62203980c1c01000c06400a101f020010780008145001c1c00c40600001c0310840c0200e002c100c00c19003107030001c0080303416826920600070b0018060b101c2c12a6101c001c68107220706050348031108114142102da0503180c0c0c00e01d64803000c0f42200c41c03d4000300211131544d400c020382c040041e084005002c420707241d00300602144011841c3d80e4103031390747c9034402c90003d41d40030340c10801030303030002d06440044100707140c040f5641d5100c440d0510340749401d42c030040f4994500384012840c11004401411503104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441398156 1250 441396906 441396913
    0xe070801050c031e1509090f12040f03170403050106082119050a030f0203010f031104020f09060a0e040f0903170709050f040e010c050c070f0e011a0c0d090503 70
    0x2c030001c0e0b004180c44103d92041c0503248040b8145001140040c045030801026120364a054800c50080303907016034181e5806489078000c0240f00e00aa004000910500c107804d002c2901f07062805885501c0100765000040813070003661680c103001383e9001c050790b004541104c001d0009554407101c82c1c0d102c00000c4a0091588080c04c8184400c000100480d03c1a07a00b205901c0703803080000c003080b1035039000402d4240c2050349030081c10285124900240d400ba180400a515000d803440c6003400d074a0000800442c001c90041c8500401b010a803400e4860760702c0d00b9606960f455820a04c11034540368203a441942c0309d4038102c03020000c004240c0c041c40c3c0984c465110100354610309204201e00c0041115a400040e00c081e1040c082400e0104592303200c140050804580c040ca05007169094032008260800010310108019031042c100304041c00042007880104541346080490a01700c0041c140200c8015911005100c10080d080380100c584581130b6000390380c607075240e1100003000f0280c548034441c400d00c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441399406 1250 441398156 441398161
    0x60303180302060702010804061e02130501020f060f130506011401110a020f060d02070803040f2a03020108070c060c0905130b090615040e0c030603061006020a030c0c090e07080105 79
    0x1400d4142010760760014a0907040c80040e0740110381da980001d10407242e00d03403540032281c000c1c0e08080d1007155544502c40701588500c0e0301d1540c8181c03040d02d54001c034115808200c030380710001000300e4619009121a84000303255510440e0038816610074080007040e5100d20f0000103100601d14203501008a02660740c1803e04145a40303041c0d880300e8528003e076100581c442021840d2908200910f240740d42d00c407016060120a407542112600200c0741a21400f40c21800d407070410002000d45081000c40c144401d9a64550410b804e50b404040e02000381442003038000300311300c41d01418052003104d078408030911540070600c2e0010441030f6948581030058070b11040b0b642208086004e4007205410203000481d8960340c10040100c51901d2001c6444640000c0102040c0344984c40b55882c440d007111944c0f9680c0b4100403050510f0004010000400f98612101c00d100403a4041001c200080c5c052070700c41d50000305400c0100300145998811008589460b002d0281c0500208805044500701402007100b070f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441400656 1250 441399406 441399437
    0x50c060304030807030b0f040c020604060605040203040b011403031207020a0203070501300209091003030809030a1403090c0306100801050108010c051603091a0904050601020d0f120e0709060303 85
    0x501040d1070007404603145000140d00c00748a580314820035200200551300401e8040e021508840c1d16140410060300b01404000501c81640100802810199021803861030143c03203203843e4803018020a00c0103404203800308102d075420010395039054900407000041c0d0400003000381d55004c000e82c04074001d000d105000a515801102c0b03544d200c0640e40035000c483c001203c00840030060701342102240030740c02d21440c1c42c01e40352205002c0c410302d101d0f2070801d40c1e83d0450601400c2d00f030009105c10195400cc01c060442c05900c5060108402d00c89081591203840b0304690760300b07084400c0c0c403203500343c8150f1041000141c9000b054100b200e110400800c00c030b98135232003e40e090302d00240d11303100410f404000d96003000c10030382c3d04850740034040d141420b841c5071100c00c0c2c41604103070344000212041c008140c04405140034800e41d42c0219007400208401183c0c1100039000c0c00b40d00f080c80d4144075802c0049a6091142e03001003034464130180589600c00e407940c84181c0106503900041c0c0c0083e01641450421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441401906 1250 441400656 441400669
    0x20c01050a020106182f1e0c060c0a140403020a0b070311121c0e0712020117070804120509220e060408070308060109140415050d0606140a1802090d02030d0507050c 72
    0x701b10542424901035024658004044641c003081102c84800c001c8000c0c004d5040c082640248408c0c8405035482d10304200040ca440c65645c1d554001050030002080141d44001410003165a10164192220417074202500c2300407614042144c5030145140c000161004d00c80141010750115943c90300c181000040902181c060796840b42042c0d010700c1040c081d40d54009074079040c1520500d442e0880c00c00303c1c100301e404040140c80c0309003c908500d0500041012924604107202820700d08242000c1740c007000110710100020560b0f0401101161550006e242500b07c561041112000c686c89401d00b8581405281e0000030300380c00084d542008106990b04c03c147d443c08641c4c10407140380341e1600407420000203200a0350181c018402811001590740c441c401c440c09983d0203201c000131030b9460400031b003440c2d007110360000384610481d40080c020f203100d40304282a00c004c0e411005840e10100c5010034180c0419010217903262052180350b01c0f111b030344840144180c910840544980046110a1019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441403156 1250 441401906 441401981
    0xc02010824040504060207020d0302010618020a0807030e0f0307080d05130b1b0714030702130e10090f0606170132060102010915091a0601020c01050a02010618 70
    0x541c12111100d010a0703160640146070468044ca400506c1c204680d40022942e403a405000c50150751503030300800c24003650804820340110902c03420b51804a04050003000c1032001010b071010f0583c0c402800d40e8040003040122078030350310f10040700e5440700181040f40f90345e0803c407110160f06042000050700c2001a000e0f61449030f5102c004800b05440b050040a2038404045080304a14024001d40d804a409582081e000082040145984840c940103101103484d402038108241400c2c4052250f10100014082654000740030300002c00300640c0c50515414442c4c400098201e50410b0000720300311040088005088030240001c0240544840481c40450601010f003c0c0c00c8918011250000c250402442d501c000144000191007860760340381614201e450040c40d841c5543c5054810030031807036800c60a5510043c1500030128a88203000039903c5002803441c034100300000c40c107000d10a0013504040058005c40c0f560b03d03611401011440b00400910380c130308582201c80343c20702c82c000000746903405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441404406 1250 441403156 441403201
    0xf0d1a0a06050d0e1501080609061005010e012007170105090d08040203191203060501030605100c03051207120b041503060507050706091101020c0102033105060a0c020108 75
    0x31101458000107890540001c0000c40d42c03107032108000c0a02d0075050240d0002291444810240303541004103c0d0318001c070043c8811500d912003414084141960a001c0048400c246412100000003000407540310040d2050441e042d11008413051300305402085031826134907400d464185005074058843d00381c0300b060752030072065005089120000d6124185160740640007034101c500208008124942860344a00152210b8006c0030024002e150b02d4001c00d8028102460103000042c140b1000030031029070b148009050040082c1028105805481610f035000c03000b4005e40c115103400b64002c0c100a0305070300403001a500c0d0205040c6285402c1c41850345040d0702140800d041800c40c0c0c1e4031030003001c3c05042d0b0130034003406103c1200090018000e41e001c09110311190946940004006407404902d01403d6041d0742050243c514000200c848041d18075500208080340b0f00004400d0303a103001d429030070180d0884000100c00301001d40248000c41080e1003030743c07040415a03403480388484088403c620032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441405656 1250 441404406 441404419
    0xc06180f15031d01060311060f0d02031e040b01050a0e0f2a0f090909060609130204110a021b01020705150f0d150303030b0306070f03091103030f0d1a 66
    0x1803010307524414804200501504000450008040300b49001d11003403900111180e440349401d00c03c01083c1d094003109801c0682c1c00324100030b0a04482510b41c040c42c042400d1443d404000103000026a6030100710f41e0b078800040c2920b9040034101070420540c2406075a00a1808040c00a02d410f91501d510348940b042102081850301c4101014880142c860245104410015000c403140f01c0c11200603c01c2940c1044980d0fa5010300344103120b00030b40010004132280e003201c001c0010302e03101d40c0400c691100115009034000d03451403001400910000d0b510a14601022541c500240d4000503554070300c1e0075491480506444060049a940f1400d00a032500111211001c03080c4941d004050400403010304c5606040650108940d42211100c3c01d03003601700184404c0410a154162182022a800aa01505051400e00c41c05491142058070311010543d40d140580180700c0800018048264010142ca42d694038004110700307950048083e80704040e2404906800388411002000030ba5000a04003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441406906 1250 441405656 441405659
    0x61a10080a142502070e01060309050c0303030603060c2206030902090a0507051603020c0d0503071b0f03020f03030d090602041e05100e060409182d0204020307050d090c06180f 77
    0x20715103c082d41c500502c2c20b51241e9000883e201400080031030203450340390703400110000c2e80d061192400e80040c4410340660810006d1040c40d450110310035500c04450706016541c0e0110300c0310030b004a004a05075012181c140840420020360540140c0d48045c003c8803081096103e0501e00012168140c60050128408000404089200c10b00380d40b04207000e40141c48051039007a01045000740045e60481e410303000080c485040004031035000e214050440441101e180c180003040300030070340c2030102920600f0700c03804944282c1d03010001c4581d80e202446051186002c14580680071b03402a001c0c1d241501407407890208251140708000d011150014a04140107031400c2c0c6c19101080910160781e00040b040001040314055406801000f40382d8400c0746040d03002509000c980f1005a140410b0f0104090120740030305141da1910b5802503030125401a6643c44900381074845224140485041a04092084050107005000c5408544885d150080c20409100d00d403581c0d82c0c0b541c0142d10f00402c3c1d0010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441408156 1250 441406906 441406951
    0x108070f2a03030e0601060804030509121905010501050102012a030e150a05010e040809040b1c050313060e0d0620180f011b061a10080a14 61
    0x4410140c91107040c09804800505140010407000c100d4240c04294010303116010958140300c2d40c10b001500002800055040c442c000740044405000502005000301e0b95820683e5140c2000690440e04005c0707490200c01c002e48400d00d02c0c0a480c040c1c41c1c9518110000a040d4018090700750f0a8000c03000d12641b40d2040c884809805201078542e42c201550f800450040b180100818003000011b000d500704603240250700324050324016003007021100002c3c000c0c000000c0e880025141500c10403a404211802c0000100309801c08510302604101460b0f01c0c4401408400b10041c4102299070345141d109540b41c0005813210035020006a4000002e50b0f038034000700d9003c1d4400d03141c40d4550707606040100c0c0401d142035a2074100207451512409608200307005480c1c8a000c000d41c010702801c01590a034040042460700804150001e032030b254079900d1704103001105900d1103000c13540081c041000780080c4100102041b0045950340203462805140035542404200028440c07842121590003003910b110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441409406 1250 441408156 441408167
    0x10b03120706051905070c05060a090b0105040207051005010612060b0a0816020709090c061824020f0a03030e06150303030109111b241603090302240106110c010807 72
    0x510380501311103c0e41100c0d400c100540074690190756555a180c0400d170050a1403400c1c480090f259881d560320306084100004c410402041c115942102c00589944440c24802c1c00c04215040706c81d401d0b4949400451203a40000c914250801005420841c2c2c0d61038030700d424618412110b5940c0031500d000000340021401e003844200302c00304c510690315615580d644210660300070210443c2c072505125010321a8a500000039541d002c0c6480d07001c1c41c182d2620f5810311250394030b0300e400d45519400000002d0680d008206e00c00e100300740d110884080b1182400d0050007042c049a0121103400782c1400314211600c4c0300c0344455408402030140d8910303403a00c2c282c0e4000b090b070006a188100c0d000d018203001e960800700403440903104407014007030902511048001c0d8071180c6070049174009490b0f0a000f140486c410031050340c10414203000a041d80c02c3e00701a80341920031b074a111004000361001030303c0700c4c003214803c41c1201c075591200281c00020696854807014601ea202e400076003000d002400d07681c85078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441410656 1250 441409406 441409411
    0x60503090a02310915090215030603071a1e0c07060c061404060e0c030d050414060405030318010212210c09150705060601081317190201050405010b0312070605 70
    0x1030107140f00046102000102c41c140020800c41c01580ca10030304040c0f0006400030b100e544030320102000f10052039400104280145034400c103007180e000c400034550741ca007040240c0c003401da03903240071500440520862902d5071050b40001c0d140c15400e40106c2e1100707204400d45d59200c02c00f00240520320304060040300c10803901e480594042e503c0e0841042e0150683e020a4000c40c02820042901d102c111111807038091a1141c940c0640d001111859032079034032000355002d03030b02c1000021030142c2c0d80c5000501d00b8081c50f048145d05000008416801d03916820101028000130303000c0e01d507062200c1c1c0a054040c040d40010b030038a145d80c8407842201a400002c11030340304204a020504008840e0302140140b0030808901031441000070351602486010080c2c10750080c000d182801d0b0710f1521540074000000d00c030314024110385a100c40000030380000800d54100c80e003040c0e0640c0c408400820020701820064800b5580b40d40382060041003400c1c0400c800c8040c002c008080c0e440e00c012551484010700c1d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441411906 1250 441410656 441410689
    0xf19020c010e1506010219150608030c07151205060a2d050108011211010908010c09290a0809011103161101050438070e0109090606020a0b04050a02030a0b10060503090a02 75
    0x88e0315040c1b0b0160b0301c03929028002442c010b680b50311000310003524011468102d007561020300c0940c5504d03103a00c00e07024040c41c0c02c10b40003c00c00d503c0b40c0020400c001056044450b00c2c01030007000e46209030049100119841c40c0c0381380100e07031558840054600503c02c0c0210b01d50402545c840b500403c0c00620000040700040c0340c202c18103580d4140c11800c6030b21451441000403000481001009040c1c410101c8140d40c90600c10011002c419508001d03204506003a002d1004080014181d14029801501c0400270104201daa902d85004020700d850b05840d612004180404491030000d8014802c1c588101e900c01c40920000030b40a000c0c0a1a0300d030741d00b250850040103840303954403200468400e80520203640f80e243c40300c0c0105001500b03e401d650802e040c224540807080148030340c00103168407403507000350041c111500e5a00300030f414007590080180d050300c00c0c0c240f81d004200c0c2200301a44625003c3c410086096110079044406e4401a600008182c0c0301070b1651015140c64424180c11071203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441413156 1250 441411906 441411923
    0x1b0b030408031e0c0a030b0103061212180305063324070803010504200415050d020a09051c11060903150a0504031706090f19020c010e1506010219 64
    0x3c08003122400300c50300719903042d01a0000b04042c0e250700c0d00340c010178407107040c2401c086c02042d0424000d03064072000c104015200c0f200c2030005001c802e0084908440c1b00380b18405015010b0b4407414170950b04c076825580c402e08190f0b0414100a01400b915000c03021003907041c000824514128100014030003200c8c4080b041c0003d076402029850080d1000301801d40c800c00e1311710744130b614100030003049950030344071501d00369204008600c207843c94030100c80507035803001030403030308480322490491b450301541d8510041548000707041400c007a01b02ca07041040729011141d02280e0b1030f8407603a52280c0004020005c1075605d5141000510340b0f4400040e202c0c0303200150896254907000941d00e0b124240644580d020240e4503030500c428986d001c00501a03152190400701124146038010402c8150700829202d04450300d040410060b10761101390910710350742d180055490b107072070501d00e44c000c103860a48030106100d0840d80421408813a80c0e07143c80b500f4160060041c007004c500f080c41c42c5100e4800300710b540c0c02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441414406 1250 441413156 441413191
    0x609050c06070c14150a0f0e0d031205060609060409050c0d02190f0206270a0803070f030b102001020c0106180e0f070603090312181b0b03040803 64
    0x803610000350280c0750241400d1100b0619104840b130703515007594005401009521041c036030084010084034081c00c02450010101210324200311580c0840d0143c1590145c421081c8806240d0b0041e6201c0701420a003100300031a8071150300f040440d1160b028002d4002c5c40500c41008084215030080e5400a030002889240200310880c14040f82d0004111660300012003030300149455014204656184e5140020f02c2a4100f2102031890200405840001e401d40c00020f0024048144007a00080c1d901c2000c66440b0300745510042c1c1480380e480c00e080006440d00c0341c0e40c07025241203900d4606024103500c4410041400003000050400c10145580256400308081040080e003485908011b02c504048000205942d01c404800d4441610882215900c240140d0a4500b40030403070008889140c24001401402883e0588003c8604140007819034580740d102001506001040300b82688140301000b610030040201151042d86409103d251400a01c0094000342150004680095040d403c00344140e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441415656 1250 441414406 441414409
    0xc031404050303040c0b120f1305060f070210021206150f07051005070305160f1206091b0f020c190b0304110406140d0204050a0605030601080a1101030501060c0609050c 74
    0x101400d86040300c540e0310010401043c0007400c2e45a1001d004401c0001e86000950100e061000c5c2d0302406104594600c0707004105213003040024211105d911005903031543c6814004010500c80c06c0303a190740036010780d1483c400302c4049842122a00c490f01c80c80566580c5840040c081c00450402d04070151080400000f50500b4484002d4a0164070070320040c15003130303111800c400580b50041d142105050400c0c09009800c4981c080500c0980e410b482d00500d40c012801c8100e0b0554000300d96020014600342003c0f49100340380e0404000000b0030001c044400d08080000c491480854a0800050300840c0311354107145094200d24502040c851020b0014035240e02c0700110031380c000d58003200c95400400e100b201900b0207019403c014180084810740a501407000b040c5403026002000703200300e40d600c0006542c800b1a90081c0d0140c030000e801c50780c181da100c919547d60380040c480f09a5074042100b40314511503110340038050503607956607910b602d150019620306001d001c60420803a0f443c040d81401c440113 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441416906 1250 441415656 441415691
    0x302060c09030c0a080607121415060d1d060c0a0801140a09110a18060c061d060c04080106150c02010c02010c05240c120402101403010b030405010c210c03 68
    0x17504800014129908207607402400c89101c08681110103410300c480da200400803159440e500c050201a100c1c2e04540c1200043c0951042c5203920840130329110404010010749202141c2e0748440d98102c0d82c2035180e2032580b44030b82c0648001400000d94030f4006200f0a20000342179a004207001e000880710540702c003d81015905c3d40d1020010100740441c00b501c076241d10500c040c101e900c0000b0340e901c0c210308103417008201c072402000c082c049c02e8840c1600e6802c680440300315100c8440070015602c090400c090411182e502610942045608002000c01c0c40c02c00488010100b240b65100d580c05042c081d8015120501000d2080c3e040c00300b41050300003c6a030034425050060032001800b03c049540c010328109183d0080c0c0940c240a105100326440381903420421a00281c04540403800500e01c0003084401030842c54075002d10784404000001d9550300035002d14043d80c4200003c0c0b0004e1010402140d032210b02402190109549020404c1c1e517030f80907800400340d80c0483c0740200b0040c600d00c950501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441418156 1250 441416906 441416909
    0xd1a0103110f150406050a09031509140303070e09070324060906050f090409080f16061410030b07030e160306050c0708090f1f020c03060606070302060c09030c0a 71
    0x5803600c0000032007001c1c1c540703402c2904141c0c00c12a62200c1a001e04a102c0049020300e000c0c010a010b400600b8085880c042d24108005543c4030201808051039404028080c0002c4041280c1c0e480c81e2910740c0710140b8011054a124200c25918606031380b0302c6000f0401d19000c00780c03200c401e25070340d0244000d900038218164070502c00c80c029080038052900f00b000309040b1440c0d2109041081c1408442c804248400444043e890100d4021031581e0759810b10011030321500c00840c082090004140c122031380c0000c9080c080301d006600c2040024180e0444c0012040300b100c0341c4403050b40358202400010200f01d402a001140c0b442c2c00100026901012803401c840443c80907202c00d6124420020007009000351035003d0340c811045800c0522a50700c45055010b4041c040344144ac500d801c40016859031058444429a05201912060030000e00039489030b55500c203490103409040006409030070040c084802c50740e45680102039035070b1130010541090b001549100e600d40034040c00d03512b140d9a003401e0f031700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441419406 1250 441418156 441418163
    0x30c0b160912080405090c0c0d0306030303151d0a0f06080309040f0608030d0f02070b0f160201051909020a08060720010902060711010c060f020a02060903070f020d1a0103 75
    0x21610aa0000e001d840c001450b4030042070016202c500700006900720b4151411240256400b400c04e0302c0d4500180e0150140c24500d0256216810305103036104d40c15006041164060b44040007200340e16801151440007034043e00203c02c220307401355114100a21030340c40d0300500c218400605803500c445d804058030000c3d40211203ea001180ca05d07176510b007a2240781003002d0800000c02c889441c29403030f203071240240745203095502ea07140e10b019400585501140c102c3c940c800c2c60700207170f850002c07515101c591060310446840c080200030844611300521555000daa104042c54144140164110000c1c068581049800408000d0300150006040202900a0b005070301c4441c44903000404d0310103c000c0d850916000341e8103150440000d42c980d841112919a0003003440504401540c0050f6200c1c60000c034000c1c50240362402d0300c108010181d000d45401c4450350f0a0701c8264403a000e10b90350b00c2c00361001c01f800a03425000f4500041c580060f0b501c001d11300c01c040045031512541400711740d09d07000768010ba = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441420656 1250 441419406 441419431
    0x20f040306150312050309150f0103050c0a030209060609030c132a080c030c1e22030b060402070f0602120f0106050a120c0507152304120804030c0b 65
    0x5004210160084002c030030380281c0700b141e009241d44c803502e043c1c01420324000180500000419400002406200c80030182480b400c0c0c03890030543c14035529606c2c240b2003a1028090320200300520f180410384a0116500149a070080e502d8880400040e580301000041c1e1501c40d89192003000c0e00d514404503a900c1c20540005000c03030f00d5a90006003502e001d4541c0c80e0804070200780c5034046810000a40d0006420403c1c640c032540d03908001c4c070044c403c20b00092001084401d1216a0810a50060119842d0500049041481826180c03450500e0380002040707081c0c00c80c0050880c1c20705a014080c654010b06c49084190640d8513100b040384d0150751401d280c9030030b04040002145a000c45203004150328a00a482c0001c0c501300144101c5441c0000c40b01340ea00d5500790800148a2400e40701d4154000c207036080911602e43c0d00300020441040d11030300a02090118860341c594040f0710314440e980069505403a803014001c21604404001c10803000d00c03034070f43c3c03410000c9203200220341c0c400d11401c01c18 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441421906 1250 441420656 441420659
    0x260f0a15060f26011d010305070b03040807050f0f010e07230d080a1817060a0e0721170c191e0b0604110a020a0b0903072a08010b010903020d020f04020f04 68
    0x1486885c0310b08035085c402ca5074610300100005640011480d04449403d01515201c0c0c580d0715003000b0911070f605001e0541e10a00941d030300300400204810481d10564402080780d14030700000e554541d81a4441d6040d03044158010f00d188400e80c0030344c000c1d000740041c40c54620311060b96071516960404403d400018112825101c0c1c3c800d103140c46030b006081201e090131405591980700c40c1d40c1e1517004100c541410b8a44540001200c0c08003c03007030250100c0c002264000d000044126903100c48044123a030b808401e01080c000741143c18003160390711110000642170b10903201e410200c840400d0310b02114600a45140e03460340070180361340c042d20f10f40703d05105440e90030318000304816200c901d400201c035080c00b0030010a549400252900380640d218a0441036603072034030300f407600758025000040c00c03c121040317002603040f40d51f40c075040ca103000f60311a41c400107894120450803911880c98090100e4000300d4140302514000312410349480c4001c0860350703041e14800214043e60400c4420151074400070a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441423156 1250 441421906 441421919
    0x4050f01021c1104030c1215110d05010e0402030601050d080f0403080409150f09090302120a0e01080121150b0409050c01170f041101260f0a15060f2601 67
    0x446201e0705020f05014200380c01c58843c80803090942c800c40f00940040c06000082040e40003189011000c00b6000300402c0c0302600b202000c035400860520002441c250001c6501e410702241c9074003030343d00074005054a0b801c0c07009100f08001c990751305079412003051108070417202040005001962251085030744071890054190180d5035007020152206c40745900038094221144400c2080f145502c801145156040c00d0680c10300d0882d00a0759040000000c884110a4001d0300c0101001030a0b030f07922040e680d0700e8952136141c0081d4010307848603d102e0340380d0340301045501c800b1544240e80007400013021480c9000140444e641c000003240c2c141c22001c0447c541c0d68100f0b1424600c1c08011b00482628680b580a12034201c00060008050858190031004682d101300141d04024120b000c13000105800b0001103081c0c180d04540d40150501603000040c0102c00c140100e00724444034406d90031550341041c909942c0c0c1244050420104454403009000c24041318840021111460324013602a505009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441424406 1250 441423156 441423161
    0x80c01050408070b160c0201030b01090803040e100b0f0711211c050412151103010801060503010b120606010f120f1a010f0c06090201030603120815090105010c030804050f01021c 78
    0x1000b41d03400c940c0c8404506910340d0000007061b0015030920b00042c00202110050360b142d030490b000301d885403101080c040b6090881c55090b5008030070762020f003511160b80b8803415045124010090565500c1401814002400102000ea00450040400000800c0c030700c40b07210a010f003a4a00680341d4003041c40e80c10641d0f640c8040280680aa190031403419041c003140c0e4590808400c8003c042c0505216655203140c03aa1303103c1e01200b4a103402032980c03540d4941c041070291146008041c071a51374a0070900b070a00c0c0140301c1035000c0800c10051300865842c2c5c4010341d403000046441c0e500340685a02c05210b04403e502ca600d9401c583e2001c00281030700c00116024511203041216410301218225103611140c0286a0185c40759101a001c2501400741c40120050162640001d01e121103821703c440360b00303403c45240d0b8412200148490440744041c2c0c00c10140542c20700c1880d005c01c0d601d00c54a00400d124044140d4001d0290040307807900c1e00c01000700c508a912405e0f100041c4031078180303401c0c2c0b0403140f230 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441425656 1250 441424406 441424411
    0x60d0c0206071d010903031206081606021203240409120c0314030f0c13031b0806062b02030102160b07080106080907050d03110105040303020a091e03030c080c01050408070b 76
    0x50b100c0f255025000c80040d00d044c8a074007000d030a010170603142c000541425000a0081c06054096031f84c540080e400f108044001d5021b0781016014541802030042d8901c400d49120300244041003a1241901080305c09030403101a00682043c1c441c1160f01c0440d03c0140e04811261003652842901c07440c03810000c4ca08500d20028020240b020418082e041c4c40054030140c0180035000301c250b54901618a01e50a10300c0f6038030040080b0848400182221200901c0b10b08641c0800f094a01d0342c2c0c0e44d541040300c018401c001643d10650440224044880c1089189035064409400140f400d4007145012091800c440310894159210104006180d50f20040980c010f000f1814421b90038202000d100b500c41c070090080300c1c028021040160141803007840502c50956041d00204900d041604004001e90300c44244d21004c2848450700003250301060782c8030ba0820b400d000781d802d02c160450b83d003245c02514075071042c0d0705ccd15810700c90301e400744030280f02c4c01e0f0150340b00f052a07566984240c500284240d000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441426906 1250 441425656 441425687
    0x50601060914040605030606011116241107031203060e012c0906040f020a0b0327031809040602040b030108030c0d08090d0e04061e05041a010507060209060d0c020607 73
    0x348041000716460001e6501e40240003403e106c1d0040b1b00080b2b066140109a41044000446524000030b0075401c90050407406105d1907403160560a210314140d448580b0040c0041d900d038884a410404a04000e24029145906d03140104006a84590300e0a4415003a004071526442d80c00381104503030707021060000d80844035004e41c180f41c03500c10240c5465420040c0f010704201d06040741a8110740d40c1c000034401034990310840a499040c40742c1c40d00c140098541d088644007803104110703034040e840081510300c40c000c10040e844d41410640107018203442c016200b1140305400703110200b9030f008054069030181c00031400864550b8a800b40052504003c40320f10001c0c4480e4a00b444043e10010500420b00421801c1000d40384d11404040f5000f8802c9a0204003c9a120f100000039000008582021200100c600307010090707001184a0880b19207201040c0490130811071940040c0c40e5030041c045c20f0200502503801d2003a000080c00954900c08c001c580140c0080d0200002d040e00004400c030003124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441428156 1250 441426906 441426911
    0x8010c080f010b0d02121906140d03050f0d090b10050a03110f0d050f0a142404080910050702120a08030a11160c08060702060606090d02040905060106091404 69
    0x80014081d044408180a290040c0600254650140402d6011560f101c0101c041e500c0041c64a2039a0380794158100312482802807c02c000050200e16401d0941c0b40850b000348603041c1c00e00c442e41c040c0c1e42c0c0e034000743e102750074040e00380450040d0000038410030514600410082c40130f45032a00080c46e42511070780045208607a004030038004500401c412011024060725814641d984400008001030301001c00100340d846005039841003a200801d060591a20903000075003c03880d803001580d1103002180c0c0c1c201d0040c06284240420819204206401c24042c2281c02e01d0301490300c0c003080351014000010070118000081c11011821f040b0540f982c41d018a0015000c0100e4560ba052510702c8080c02303505405403031320a042d50400c1040101c9115890300f51803031004c0d011b1481e100c841c0319040d200768055030184600183e0524000b16000d48034a00040c4a0751420700000200800c05211a6081c0c0c2c100e961560f01000054082110b540070705400d0312418016441c14402c00701c0c0e02c3d10039801a00950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441429406 1250 441428156 441428161
    0x71203020f0706090201030b130c021b03030d050c1b0601140105070c0506030a020405060c070915240507051f0605030c0303070b090a0b07030509100612031119030908010c08 76
    0xe003007650042d075440440400c044050b400102c1c0a441c01d4420582c0c454642e15154038286825405201c0100b010707000d42d00040784074001c40c01802c410841d1260190000c002580001403aa484560b1240c2c048411500b808922004124030113896040c55041c1d40c00f00005001c01c01d03211144240000003407800382d00e0112917540c0c0c004d202d2a203108450240c40003001040c00d0b030740c4540540380502000360044e40c403040342043c0b0300e41e2a0414800d02000c9407038201242807580c20010840c4c140e40130070a903c0800040c0c0324110358102e030a140c0c0d640400109020000000b03d0500495400490502c00400c82c0c80f40d001e0110308907502d40c0d0200e840b03a400064281c0041e1401300070f8454141e040940340510342d8a000000c0d09101e00c00030001d01c949440401c000d4019007552049000d802e0740c41c212038480400f00c200e0300c102d50b114020042902c242007400e00c00030303220f0211032444185d2002600c1040751074807008203000301c40707520841c00301c0c504641c280402802403041a19a01e00340c5494a41c030b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441430656 1250 441429406 441429427
    0x1050601080f04081e040b16020415050603070e01030f0507020114070801210203120a0228020105070222060f0501020f0c10110304030c0303050408010510030b0604020a03140c07120302 81
    0x71705c603110192503001000c508014201c020541514010001c001400342da071414410401c03000e40f01c2c1c0804a2145141074134840c619803200315401c2c2a240041e1009155840d1100700340ea107510150b22440c100340d00d5120702c040641c1e86002e100e01401883c0c00100301564150803484525000800d6002000040d1004003c51460840a0001160000041114017041b4000b0034104800144c2031460600001041c1160070f0340010811003080c841c23075480030b404005020f0481c054001d484c005c0d00141007031000b0b07809071030310421901c000c0b1241e072591400002c000720700c0c2c400e40d01139a0007091150102c40c410401c1d56014005080144c8000c00a0031010b144100069002407480000c0000c101c0300c4500203040c40d9007041103030065134110b90310f032610a41c0c0c0d24001f0102c0e8094000c0035065400c7c05e0104500040f00b0072003100b5694024042880c0c2e960310340c14040290030581c00074040546078010f404a203052481240d005516041030141d41c0e020768107041407411b0442c0c82c4201050f20400c13011800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441431906 1250 441430656 441430673
    0x903120c05090f030f0102032a0c0c06160c0b1e070b01030807030909021207090e0906010e06032a01031d0a0f0602091002070608150d060c051b01050601080f04 70
    0x2007200d84140190410700420300c1d01088805c1c3e5640d5600c00428842ca5040300d0f550112001c4409061101d026010f000802150040e4607200c04542d000998400702440c02401401066102d1200034814002944400d07880383d120340d100002e61600018210391042d80400c0f4004201454250b8a1034112603a8402a083d801444081c003980ea0104201007054403442c0f04000800c0ca000c0117540f20b040c40e03a0b4002c2500020b42c6c03514041094a0710026591a0758800c080c882c00842d80075100c00da00e495186000000c000300b00d80d51600583e10030400020012071501e03481d000b44405400102144400541285d598414007000d203082d5803242c5100e180b000600d07100d0154843c042d0407100c1d54a00e412000707030056824041c0e01c5440075220301c113059400144141156819920345500d0744920700d0a41301d143d0750a0801d0381005078241e0350008184141c226054000703003031030800c1c038004001e071050000810303148078950965141e40900800d076074000c000a8100f0080800c59000e030620741c2e03501c4403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441433156 1250 441431906 441431917
    0x190e04090f0501291215090c010806040614040f060b0c03121008100e0106031e02040c030e10020c070506040b041d0606070f020f0a060f08010905070f080c0405130903120c05 76
    0x3c6082805417501000c1d0f42030085403403250164020001c142400c02519441d9425801c0e810b0005510600055007454180591421944c00d42e035044080b065840900000c0d00c031504d9944411070315014009184420b80005044c2150900040c5855180f0303031540703081d00880034007002c014100f08481803106e0900070030300045605c59100d00180110000c504107002d00300d60b610142287c80900340f09002400150030002000748221000c00c103032000311001380c003103074004070400d1039991120080c0920504503500412604600004503910903a959000a00703560150b045051400e80c082000c1007040c001d044440701052080345411054504040410391038000c43c40c01602c59801c040b201d00943d110040d1100020328050a001000380d21110040d01e8841042805030014410500014185106120b8180980840e9590881650300c840c02210015000f0f4451003403510700700030010f2113694440102e41c0580c4000c0d0080340340344890a0190400c104046504070641c02d161103400040d60003001c5a9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441434406 1250 441433156 441433159
    0x10e01120f050a050402090604090b0105190b040b0c1b0f061c0e0c1215010302010c140a060c080606070215030c0903060406060f08030f190e04090f050129 68
    0x3a0504414034480c001d0001c685010024a2600303092015000840e04541d10440c001e907002c00c1280c44040a00c0b084814140024110307002d1600103100038608003008005615a03840c00c243e1280d11a503000c803580c1c0c0715510080f4241000112202c0d40c010a000d090170200d98461007100784031824001c07410b16882c1c406501d200300000150242101e103001040036854500400822030540c049840e2944c40c200156030394410014440d43d80c0c100b9400056604c141803c1200140d100d0b40b03990b006440201c420203045400d000340f5031081c000503c0404c201c00c6005c1c040d00d404681504007031400f4046903c00303000035026480c1000000090303100c0118900f803d0744800002d55407a611400c92a60a020303504101e585070085000740001c0c0091070b08042e059507041d0103002c1c1640c0d65841c00964034412002d640001810611108035002c82c28a04044c140c651810510b45003840c1200040c2180d612190403140200409508400c0c44004d201d0344804030380761504444d004000988002521011707001e480e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441435656 1250 441434406 441434417
    0x309091015021f05250e010e03010b0f090703020903060c04150923040e01060609090e03030601120f1121010b0406170903041d0108120f07030809071a1c0b010e01 71
    0x9821202e4038260444041c0e40c0d2106076010a1015100501c003110100d11300b4005161140c6d20f23070b1030b40b80610030b83c000030000030008000402e42200b80608100d0040c03803402415420300803004291820b1140d148039940f096841c030f039124181400700088101500b079402c20000714010500105403081c0700240865100140103007402d42d40301c002805026408250b0340d965007002d0000800a4200c1c542070262070700c60a0600001503c50240b03582e900044031242c3c00901010407085c40c554455000800c0804030207408074500b196258220400d0340074101d041c00c1001c0b00030a07204000d2558000601401e06a048a0300c4c0a28090700100a16800c41000541103000d4011481d00007003002110000c01001002c1001401c109080003840842441505094081c07440310020b10980c2200310744d005030a10076140d00b13000e081d031401c070b40c103000c000e004550611a1403004501c1c068840c04d00220945525a443e40d551030141c3c102400c029034440c2d00001b142000106070b40caa82011860301c82c0c40302881e14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441436906 1250 441435656 441435661
    0x100e1c3906080105120115060513080318010804050f0304120204050702060412110708010e0a05190f0f051f0209120309062d040609060f0806030715020309091015021f05 74
    0xc1d031b0040210440c3c01d4806954003a00094294228025103594440e8182c80701000fa60350f48415103e20070021010809590049000d10540c050ba01d6250424050380498008146651039145141d106800c98a0035918403d0b0070011072405024460f8040d4503403010700b495044c260b80f161004c81340030701c0402c18400d07420040303a81e64004202c4080100400da009201030105195032a480315402d9005894601480181c0092904201c60340c1510641c840c061450314002520f81034440a60f02804585501980d0300c00060316103402311041201c0b07841c000041c1c1e03824000d41001003a404a1818404540040c005c01c0342503030b144002d8802c8506488460341c0095031500302c9082c0f019107403902103404040071401041840e8001c80700305c29035203940c1320026031601d40c0381c00b03030381c450012030300254182d000d003105102c0700c0c00607845150f40c880c103401241c0c24108803400160001c1e4040311681c0788484801d000300130f59207582d8428005d1000c94009080c000c108903c1111030040c0070740c40c01032442e480750007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441438156 1250 441436906 441436939
    0x30f11030f060106112e1118040f0f0213211a042112050c1603111906021309020a05040303080912030406020315100e1c3906080105 58
    0x8840c3c0700c0440040f4808103059151b60241c1c07910070040b0307000d810a280610804100240d8011200d80b03580003526101d000300707020b0800c8003030501c0554a00100d40c956800c2203015100340054024035814041d410003180c14065111081416440c240304004a5002c507034001c2080184541301c8060103411615541c0d5840c24081410200030303130101c00500050304d4150206030300c4000e1041844001c802030095480c1e00301500028000d0562b200b04c000003030740780070f030000b401031400d80310100c45202506d4880b070000b2004400c04050a505603500c0303400140d445020001128030307001074a1a00c6046040c4101c5000c028014011800020280600c45000c102d200340d082013084200b034440c1c6840d95481c50140f034a14081c1d08140c0d0845000c4046003031820700d03860400030040e00b610b032503603070f07a1503050702d40040118004025141c3c10000d82d0240e801804a801c900b90740e92802512024491450750188542803640c0f030b039002e07003005540e00c0103061090300c0c0d0102016045850484031030450000108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441439406 1250 441438156 441438163
    0x20c0306161d09011d011d0112060e0d05040f0f0f12080c120d150612110903030f0309070e0c0304020607062306100309050c1c0606030f11030f06010611 67
    0x50801e0f400f032011800064407801544002d48444052456515181d07aa44008071143c4040e007082d8144d0301c0c0c1403006026506e40d190005400b07e0055101145207072a00b032400742042e03a4840cc440c0081d600003024000c020425844800802d0030f440d20a81c09807400c2c0c22001c92200d01e000b40c1c956130340102095030a01c603889042d5002d0300702440988140305600c03018858503500101c81810000d0900d4612110340050514003421548203840d9404080d80d40b001c046d00070080986400b0002e04d05005510301600d08001a00012030010080c030b0780c4e800c081c02e10901c1e01c06164003400c0c0f034030041c80810400709203000c01d4030380007641940c41980380e24862828001901101003070001c8a6084004005100d90301c40030f0602543d4140c42d24003043c0800641201900c501210180c29944158030307800c3c03641844020505942241911800001981d507595010347d00d00d544241d980c003078070b03806003400c0c01011500c400c04220100c00404403003040018168440e401449200148000101e1410700c0702c0050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441440656 1250 441439406 441439457
    0x13020a090e0a05010f122d0803011206051320040605060304060b040606030212160504030803010b0a0311190f112a01230d09060f090201020c030616 65
    0xc60780d0800314a48406420b00804092007100e8210f41d1000002550b0414100102074440e08071158460520075007003101e941800d0500e0070304620200c041c1410101d510345020f18042c05035007100752292141410800d00743c40c001f9000f08071000040007060300086440c20031140c3d844402e4820410b0181500004009040e9980595045100042088204030140d8040011050708072020441141c50700001c60483c02000c002045d048461004240140c00c0250780c000c2e0010700b454864907150f01ca6503404600d070020781c08001109404641420070130f4041c010318071005000c00250b810a0901205800d00c05c00d05a024411302001102c2003500d5032141140f06015403034881101c4000d034016162014514a51480542c0c2c00802a042c0a00d5807080300e107464405541200b03c040100da05466045660003c2c2c0d01c0200a49d8800b0801c0000300e06006203003840540003000200030134540006070805451112146c0700390042010030410070340e00007840303c0400c082e280600e131140c000444200d400888 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441441906 1250 441440656 441440669
    0x203090907020a0b0a110405123315130e0a060c020f07090506090403050a020c0414090d08040c120c0902040e100b0f16260c070b040513020a09 63
    0x95000700240d40c1d4000401c504807600c51140c090361580c0f002c060404441c03140540f6818001d040004024500c2c00c4000e4076141d07903c40e0190380b01040703107a62048542c1d43c00b0f14a2015014500041c001099900005551080e28402d29000c600c100c00c001920720161208146109a0b64884440000304e04000041001754032010821500f22800000395450000c0312300c4003842c0c8580340002c500c0000d64040c407806540041c3c021a001e468560301550150480c035030030411485074092410176550389008900d000b41441030500303010305145c0711150030072103802002c000340081a0117001c001548071065904803000c1c0010102d22040c540784c54500d060311540180315441c004074000c140800c1441300c45000310490f03403010304510b980d441854001c2c0a0901940f8550005200c60304180c055280b0540c03a42c0e00c149107000110345560f08002181810008405042e000814200581c950030040e05019000c05840c844c03e1504c0c0a00149440c55120007410f001c0380c000c152600c0da24028002200509076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441443156 1250 441441906 441441919
    0x41109070201020d0b0102010b0a0306091b030b16030207020d060e15010b0309060108070b120403090b120403020d0c0b060d021504180605060301060507030e1908010b1008010b0a030c020309 83
    0xa098000a020790020302e412003e281c40d110b142d4545c0e600500c2041c40c0800040d1401200c42d00d135440d01c0c80103010a08054a5410b140c40c091840b0051040c0c200e0050f510031081d03d0014203010032000802d03142c04008009040c41000039101503075514001400c07855000d203001c5655803103120a03e003007000100c510010f2030980780002c6100c100b141e001d1840340740c104044607210780e41c401c81159a0071942c81102c40c00c880c208441400a032102540c90b03032080c00703400d011200740c0d40d503840c0c080140e100b4500c4d0520401888203000402d54144003080d0609820702e41344081c00306035100c009200070040d03c00c0d88248001d41404085480e42034094807404141c2100540342d13075941d00038501d180407502a54481915003040031032549008000d981c180c0c0c40a42d034642c18003000f42c0d82592920340e80910250b0211035803801c400c041d810030080710080d00307800c40003251078101c41e801d10000d400340c000c1e090b0502c540c0c4801404040c41d00c03800d840c401302c0c05150100c0c0e039035034041d001c1e41588030305400180c00c01c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441444406 1250 441443156 441443161
    0x2102090f09070b1204140a03120b1504090b040b040e0c1e0301050906010303021515060903160807061806051c020d06170d0315060e01110d0c050601210803041109 71
    0x280304c103c8040c0b140713016001d0b0b6042c00598840307140e1204034807407000300403900103014065a000158040d500c1d0500180601d407081141400130200b68000707503c40040e0301d0f21001007001d542000e000d4070340300100984083c042c010700d0345000e646078003111900c40e018600883c3e010140c89a660b92148096030007074002c004a007840342d01c6503210718090000b075001d84224a0280b0180b0342c2020582c0c416800035440103015103900040002070b91001c03078901e6051048405100d5040d07041c400300030003442c0c103100400c1801e2410f03002600340d004403000c8da1090981c584081005e150000f044800c8020343e01c000500c0111103c01c154001d0003030b05203010500780751510104612852a0212080d41c02601c22107801c60041d82049083d222008601000c900d4010400c201c4c1c0c40c060080407007081c405042c0284420007015209107481e10501e5020005001ca1450200341302c402c2c4943d1380035109146045440701041444c103224544610001004480700000003420310411100035003405a00800010850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441445656 1250 441444406 441444427
    0x18020f090406120b0903030c0a0f0e0a060305090f03160813090c0c20030a02060a021002310b120411120f06160206010e1503070308042102090f09070b 66
    0x262030340d0004440b0805254086640505c0002c1520300c41c030f10a0107000c2c42e01c52041030131140301c1041c1aaa4007032180c8090142490703600e03040e150b409400380b40e600081c24606601814a4200036403a5524150000c00001d1100c0b00110408441c0c2ca40284407660784103c0316080325a00c075a01d07441b19100382d00e041c1030004410b91141d4001809800340d120800e001202028041c04c4034200100b0a0341980072241000044c01c240001d8100c0301d1190040e41c000d2400302070b05034180c1e0b020703030031042c03012001200401c0c0a03143c00c0320b0817410315032441000c00c0f42420126004d0b11442041e40c034819510096000070b042007001c0c075415880c07442c05881d007460b0b408603800241c0e80381c00e181c403010824010000041c6144c4c00c035520b0030070141010390080c60f0310f034600714000e0700700c20740034240031030203090341d00c840d511502c08012000007107105103c129076a501d0111038050802604501c01130500100100c000035a40340148560041c411440c8550181c856661461405078950301480d1200004115074500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441446906 1250 441445656 441445679
    0x606161a0c0c0c040906021903150602030301152f06150301110a05090307030b0f010e1b09060c070f14040608030301081f0b03030403151518020f090406 67
    0x10340d64446640c0551591520a0350340d00681102000941c402100c2403040e00e4513070804880e850160780010725080d800f051055042401242541c0802d40704d81c07111029070181c0c01c84500405440c40a0350030b550412001151362000904800c080003803400b0000d02e0700d809100b4001074040e02c0090031102006250f0990744500301150f0017541c402403950b100d8403509060281c2c080840c070006910f860103d1001054415810800d015038040c85800d0000c40000c0201c0c850600800805814074007941c90001e080b010740304011b140042048440350001c4c94001e0075130540d9001c0d1000c40b9440e44880c081e03407100d45040481d6209030b18061030104006804003441819410400081d01d060044546540c000c9903644002e2040d04265401a03400d034581e1f200c410007601c1d00c411546c40205940074035000081c6560002d03007056030740d040165a080c00c80316040c81200c1c0885011901030900a14201e195070800006880b0105019000200d1000324481c2c030049480020000b40304208858680e03040701c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441448156 1250 441446906 441446933
    0xa0c080610090e07090509070c03020c0d0303090b04030c17071110032d0b1206060603090a0c060e0901090b210c1c02010e03030f03010311040902060307030c140403020a0e060616 78
    0xb4507c4800850200c0344103900c4681d41e0f541640090a00040040500040082c10782c4194201551404400b001503807410840703000741d00a40d40c1c4841d80c106420301020749041076526860550040240d000000c07001d1b01228a2184215000324003104c5a1200340d02030f02074280211807c5415100d9900c01000305c0c00300040207004504100711100359002403240602e0858000d01c16940030800007a072034a0b101e0000c59004c40711005592241140f540d8840042c0000d03003208001c560090744001c10340c00c1000c2d0682c01440d4031181070000418210200c3c0d1080c80840203240014101c3c02c0f071682203982004014240000680a000c030b0850610500a01c1d100650041340050310040286c01d841c40c2c00415550140088440c0700e00d1a461a42c44980220201141c80d400c10780b10307041c0340c01598503807001e03501c0380002d81c501103000c0740b0786003006010b10022010380590160600c01400580c07104061001a1004940c50304003c0d01ca00000800d10b009500c00401a1110301d0782d01820409414142070703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441449406 1250 441448156 441448159
    0x308040302100c080c0901020106031a0103060510060e0405061f0c02090906010509180703061109030d021b121603080a0e030a0f1101090b130e0a0c080610090e070905 73
    0x50354a503084501c0c0e026641c4600f600000184100702044c410b6401d1802000d01340c80500000402517a00e9440b412600d134403103003c00e203644c031007030042042c480e560182c00e40c04108119102d1a55003082c002600c010224a030080c019640c070302c0014060f441700382c0c016084070800d0f200150b80c6107085c40004e10400c42640700700c1c061164079000c280c0c02c0c0800112203040c1c590041a1800659034110144c00c0d800480081f84040d1280c464000b0100d0f0040c41119498181d2250795607039180e4400915207409648510303101150f01840320800c800030f81d001d141c0b810040454a078565140c1e03640e0715038a0052a00e14121600e00c10302d0f00041001030100090120070b00da03403640551183c414040640343c028075113010744980b20030500040024000b44001e0542c8505040059080da29600c000c081d54011155280790b60180c201d0900620080340310300c2d84c2c008250350051001c031140d808000c140c00030161146000e200c0762882e601402e8041e010002c060401e09104c03460740d10b00008020710400703991103020f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441450656 1250 441449406 441449413
    0x80f010207060f0603020904030c0602070b160f090e060d0c0504050a0b090906090607111606112a0f010c050a1a0c030403090b030c040902071a070c0f020f01110a0308040302 76
    0x70003c1d1228020942180d800402682e610382e201c0d20240e850348403445c41101c1e010b07401c0018034002030a1220312806901c03558002d41380d11303d1300710028100214404c00358080c44050f210401c03101e04c00c80d5003a41d0101040e60410074109140c5440000145290803050340241403d080040c040710391744c055411980c080b1360400b00d9499008440b074441e4002d88002002c0d412070b000080b04e2a0060140003031a4034280304640e0940c80c1c485e940d120a1140c0d0700090006071060a4100381e1150400c50089070781303090301c503442403400c010100074620b480700e54520340100c0f090800841686c0c00f40c011045650b030000c0981d050329280f49456213101400040c0080100005004103015000c07000c1906d04c80d5600d92034909089080001c0304990b500024442040c0c2c242c10440070400f9800303400030b04802480380c201c1302003080645904204480c40202500e0800ca409059000132800b1010401c501c1c68040e6034100300401000012124007009055081003441107090240c1056400700344a44034600035800d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441451906 1250 441450656 441450671
    0x503040810060b0a1b080408010510080607090b0301050d02030a0506070302070c0e041113060b1611040506010207170703020d120206090102180919090515011a04060f09080f01020706 80
    0x1a200d0a00130700520074001204074044104640046401c1c04403a40036031000c50510b6a03805400c0d007911811100e07090792942c1000f08108042d410450b80343c01500c0c9041c10062a82015226480e40c001440380900c0380708038403135110942d2810b00c1704540c900d4004040d20340b54501100c2c0940691b1010800304e81e0350b4081240003034030240c04a9500d0255910119202000d0900010003451419080e481314207607503240000501c8003c0e5100a0801d00a6a184203a60300b1407070400303000c4c01c40400521401a41000c0c10401503030b13030205800d0b090320b008010480d82d1003990000546000300030303000250840e140e40014014088400310b03080750250150b003100c41981d5600a00ca0a078001d050201d021542c581a9207441407902d9010a9400168240b1811040c0400443c001c00da40d01854182c4050300400d17164184c01c1118420365000d0803520101580e1081284510071082c860303449084108640103400c07282161142e0b80c180014400d0808a1703080d4600b18030550b0003540416030441e1020701c2c1281 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441453156 1250 441451906 441451919
    0x2120103050c100f05030910021902010b0a03110603040321020c0f070e0c091305071e09050d030e06090a030305181503010603021b01020307020106140103091709010903050304081006 80
    0x140360604100f80e5590404840340c209003940d960f000513082103114000c40d150030b40349607500c2c8058188032210601c0c0c1080b80604d60006800c6880c0c42011390700540d0196030038000304d00507920250081c003007515015580c0d03441e410300b11008410601e040000c5158916280069107080d005401003610507400c1c1c494420070601855501c007824440c006004c0b00079000a8401a110b001070003c2200141408803414098a841001c4880844e180c00100e83c1080d883c1031500d4951051081d04102d60600c400c003d030803c000145400740029000b4200311200181c07500a440b128151409110080c0170848640c3d12450094440c4c4c102200e070b81c0e84e40d161102000d041d03141400c40c80342c2c904466000285141d00f4040207c0107540030780e0255501c0501c0c8c143e40c2030315247c03d2008503c0360616a00000e146070500740141180c074400800d0604160801c900382020440000c101c2039100c1d081e0f2800c80d990100d0300016140384000d9031000d0094000482c0c0043c102d003000c524424242480310f02006800e0303e40d00e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441454406 1250 441453156 441453169
    0x3030606020d27051504080c0105030f1f0332030f0405040e010603080414010807050903030a0c02220608010c17040f06140114010216061704021302120103050c 70
    0xe40160000349184016003d0000d00707020b4050a8000c1c1d0b0001040c5510b60700421100170344d102c0d61030544100080d080200820030700200c1543d050903e41245181006210300c5040e02003d410400d00e112841d0880d54540d00c52240d00c00250f6225200300c80707003040d01c0c1c5021010701c1b1140704441001d00302d5903144003001011046407010900741c45002d003002d0404081c040105022428a000c0390769980b0040041030b034500140008108039192625035003102d10005100d06070141c020340500500b8851484155004000d030342d81070000b464031882400b83c500015072a200c03649041030040110808182c0d00c29443d81242d420b4903c44002449440b280390300c100e400d865000b00a8040d200940041000560341d54408042c05004000100700c209038007654144161080c2c2c0b103c02d008811303140910240d40c06004600c8086240390804000342d2a250340030f8411281c1510346050054070100190466445006000d40400008011916141c003c04148143d1201f80825900c510404003188a02c0c507000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441455656 1250 441454406 441454423
    0x1e0b150414130c090b030d08100e041b090506010e0f0f061908010f0828060204060e01020c0a0e01180207080408010507121a04050703020903150109111603080402010c050f0a0303060602 81
    0x140080c0303c442c94841d422030380004003a02041454403802d00000395060a060400d00850060508600300f8110000d600d10cc100c40e0341c8030140050404040040c01ea030442c07400801a801a070b450314500101c00c1c0060a0844c0b0301c2215980581b01040b807000403140102c0704140c0001130345401483da40c80f42e00740c036030180542c030540e44030341c1c0488000c0300c6400c82405070391003045171032103c5d1075005065942d483c01c0e600b194109000160124003110713076075070b410805160005020b0307034441642810555030844071101401259241c0007000183e01d10030f8020341c111a00c042c2c1140c00076845945506901c0d0190400350354810028030420318070f5044003407905c240070700c41102c54640303400c2d840314400340b2003e00f600500c1e25050684c24021014651010b1100111001c07106540000070341c1081000000c448070519040f0300060113001a0800408200d1401884c07600f6013003039049a40c0e1480101c0398408040c80007401406202820b600c07101000070f082c41294482d0301c0c00c8c40034940301c0c1012a43c6d10310b039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441456906 1250 441455656 441455659
    0x6070909060905061e120a050d14031006050f0d05010f050a0b0a0816140c070602010e0a08030105040b061606060603110313020d061b0206041e0b150414130c090b 71
    0x40ea0505c205071711001054000c0010240800261800070390003a400c04c1d920000568180d000850082e48803a8051030302252000701d1040310782581080d484c0012904054060a028004000fa207000ea840301003003a0707422180d01d094248047d61b15504051007900031881002d006000221020840c000e1190540f5018101036681001c04e03659140201c14240e1a100382c001448505030b88020103000001c02400f415060300024540e85250440003030844400c203403d10306640110400d0400900040100ca0446600b00c60208000c00f1510020f0511310408100240307640e102e07a1034400304289504010304403400c1d0344007044a0360404108469510080b550030b13850b8515a0202c00041c40c040003401421802000009403041d4210321179a10384140740c54540c05079204000b04000c2005011001c251040f004545010000c616551541000c0c0081c2c0340180c030f200c1d020303034141c8240c4031640f2100314003e14010034070b84c0d418120f4030013000d1915410152810b98070150007044900d140d004203964030b8030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441458156 1250 441456906 441456919
    0x30607090e040b040804051201091209080a06020c0c03030c10110315041a2812050c0d08160f020f04050f0c161a070f0e060405040c110607090906090506 67
    0x690740e460109900c0001c008560303191041c800425151111442c10000c8c400f1540006020348643c14404000d07000da007210000c01100300c40034819001f000c1080da0741a5801440507807504441010f0b02d0600f0303141c03d14144c040c40007084400320028001418040f00c0503e0307400700711020b0346400051301803000300e0380b40100340300d50741d400b0309181040c2d4004988210b14000c1140c0b0004421b00044400b401c00400e00034040c0d00007a501c0120800034082401800c140c94807a00c031000a54600d80c480c8030fa038a86501c20707101700b1581c03021300070b109081b1210884a940c221280d01c1031b074a080001e00c200c0f640d00343c0c0106801010724019080030700c035080c050340c1c02c0b1200704186da548200b4035165074072113006004c0e0b00f540341c140756000402c186d59980300701045d2104a60b292610700c00042452011811003c1001950441e04503140c0315401214240c0f1003d6801240701c0f00501015119420f03001044c0059100c0c0c0001c000e801c0790b101150700103a030198941807200660341c0c1483c02c150b03081039609542c0700303a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441459406 1250 441458156 441458161
    0x160f0812340c150b030f060402090a0e03130612060504151a0f03040b06011116060c031e03091104060518060a0302130506010201060905270c040207030905030607090e 73
    0x6403140030140050241d1800c1030b00406180d8440740c055405803c1c032000e99440302c014054514080c440d4000c0d084200f00101524605034000030542000901440341d1580d5800e419102e00b2800d00866616610540c48100d4540d5100c0c00105080c0500341c40e110618608000030075a40382034020110725041a0408170006810000440c4101540d1450f4107000c0004100181020303c024014512540c040c1900c3d803242d140880001d00180425140c8000a0700f01002c80403405921081e11005d840315032400e42e034008910303c2c064134040300d4021405d0f140c07401014080b0206500d500310040c1c9070320800314101d00c40a144280010307211180905503201441d410510507101c4204499548564000c000155403503880e004541c0c4244000700340f960003510b03001080507a50f02400392600070300303070810f0400961034001c03000c8000c1940b42c0d40c0e04000c582e841074120f1600508200d03010b1404801001150303500158500500140d00510031103000380502c50015040c1801b4001c20000c95859406851726036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 441460656 1250 441459406 441459481
    0x411030312061c03021c090504060311030106090203100e1504060839040e0114070207090b030a0b060603040f0c06050703031d0606010c050f070902090f0f01020c06160f0812 76
    0x7901b048403410006da621001445591328011030000314012000b028002c56810103050070f5a1858111040080c01042807100900c82d40aa0400b11504008951040e44620308090709082956524641c05030914001117420800402c8031810038030440048084020100102c44910705012161046a4881c007402c282a05042d0004500012600000645900e032298002c9080005840140041e40402d0b0f05000704802c0b0304c0b85c0e0041079011030050014003015568082c04100c02040f1038050140480400c04000c2c0c10f0f011903a40c940d200d04030003216515050000d02e1504212802c0e00041e0400700504088000c800701c00f43c0401ea072401030965555948019034046011050480c2c0d82c0c8540b03040a41c0302d80080c07080601410045c100903a0702c0300181c00704030204640d029414030480100c855100300c0c0e80c0000380f000201c10183c6410b903e60804003101c06200d0b140300d0028102908181c030354400c0040000c003d01501c041606481020303110b0910961030703d6072000c80c40e40160420141079405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 441461906 1250 441460656 441460693
    0x10140907200a0f050f120408031e1201090c0314130210110607232b0b03190209100b0306090a022512030b01080f0411030312061c0302 59
    0x160980c1c0822550014000d607150a40700045040035110354000210b940078070076003880883e029051040000c0d00b844d09001c280d0343c49105d000b440000e0694844121003544241a0594850f1444824944107a42e500c03891500038002e20560b0380d00080c508008007120014140030701d40602c641d94940b032104c49690b42405182c900b01c0c000c00080c44121102c0e02c0c00082c040046910420075079172894203034102810b0104c006289a030307001c00d85150034044089d141d2030f50010744806142101010100e20300c8013082d40000d03c0c064101c50f070035020340a001246107c0925020041074803d42d103558071a0b45504001000d80200d000d03c1d49a0141080030561500d1300d08056500111030700303401458104450036040348401c4101041d1140029005488140064140d10215800007810305200020314003000030080e18008126418a50402001c0760601207580032090640ba00503080320b07a1501e82e07400008004e801281d000d07100e600101c1683d0703409124200f51442003036160b00240308400080203403048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 441463156 1250 441461906 441461957
    0x90711100506030a0803040309150f0e13020c030a0305150d0506010303052101060c0515060a05061806040f08010507020d141e0d09170301080705060d02040302060310140907 76
    0x10f051052130f4040300400c904100541c01386200791036151815152000708004403010200c80c3c1c007032200903241c07000c0d88c070f4010b0b003409001c60040762017400f04150b140a1600901a2550500a521004c10849051a055800180921400070602e12a039085000b006200c0144010040031500314400400000c2d000da4003032700220b1402064028036a007444c404a02500b0241c0c0401c0010304a8440c0c00c09020003806884484002c21710300c0d00c0c00340740c00c0010130001078940c0705060180c0310004010b83e4420801c000414006d000a241e1035441d692602c1c0200304000f240103032130495181402144a207800010350241e4264107881d5140324401100304041c880c1c000ca403601442c5041e64412000c0702c0d412000030302c7e040542420000b12010642013101100c0940b10900714040d0003040140700c5000001105000c40340200c0383c2aa0760140b5800002c0030b070046510007904150080144014040c4410300441aa510780701e90442c0c0031444020080310002c1981c0040c04510402a4100d0f9400718040000c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 441464406 1250 441463156 441463159
    0x1410060f0609140d1e05030307030b12010506031902060d020301090e100b0d020402030c120c0322020f062101090204051201022820100e0d0503010e10080d030506090711100506 77
    0x114108050b00c1d203e0662340704030b588100081c1d580c00b03403800500e48000700c07250301820b00c0003c004900e0600301099545505c0344030601d0800c03414601904565460381116016100608159141c0d40d640104a01505603181c6540d41402110024a10464544113040403a04c0003003007402440d1740e0780c0030704c0025400a020b03845003400802c04d8607200300c00c05070220f0044a0b15800030340c0c1ea1030312903010140c8141d20140039060350200409180560b603400340b00440030a04540040e910f40380301111009081041c80704e007086030401c000000e6100000ea01510440c1d005944000115401c98011402c03407140c030b12103100420303580a41400455505030080d69100e03660400304139074330352010300c0b8102c6647c040704001c0503400014041c6c0c42800a00684000e199824018600c1c400d6150028105000500030250308503100030000d0542a4003030180700080c081c2e5400c0d10406c00d940c2e00000c1c040e00044811b1401040c0c030b45c0c00b00d51064400d1403030701d6007401c500029010f0f00803100710201c042c12001e410305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 441465656 1250 441464406 441464453
    0x90f030405221503060b06040e0f13020a0b2d03040f0203121804110405030a0602070203071d0702010605091003420e01090f1410060f0609140d 63
    0x3804007481c0f01c0c805500b07052010f040b05461075450000709649120079543c1c0036580030b000030403040500e80070168114192911100603a0b6171007a41118030031030080c000e944052582000940c007900d400c000c00d541400100c4c800c07960400c0c0101010005215865040380310402c100140106044c2d0b0004c41025100800b9500c12880c13400c944441c40c0c128151030001014182d580c50814a068400c490703140c20700070306450901e4039180010361a4900842d0250820780c0005403001155001c0c403180c005003100c05080058940341c0001d10b0f166070381c1150020090340c40c00001040034940802500e224912503103030042c40ca421030343c54039882c6032114a004000e224410780892001c03200c1010304030710300d400c081000d04060400b003120191001d03a032507010740341d142129075004501d003400780c1d2207005d80010501d601e0b09040000d5074603000c003038448420068901400442d2404d034248040048844d0b07a940c5040b0a9120550050f50240365406254401d525800d043c0c001a0000078010700b20203400c04a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 441466906 1250 441465656 441465709
    0x15040b010e18010f021b0601030c0501140f0403060903030507030603020907050d0e01020c16060c03050d0207081905030603070e010f0e0c0c010e06010f06110d0e031002041508090f030405 82
    0x42d0035511051200030b14542c01143d0f2003c0040071100c020400006c2d94014451945162180400349220340034590420103054080e03040720701c42070100d801d4400c01181e0340f07648559a0800b1001000e010000702c0c002420000420001c520034010101501d40043c04074031107840d80c000a54103644041d520082030f80d152100a0071224081c4042c2c80c419200700050459045920f020442c5401281c0041044c06086c00c0d40e000400d6112041d40e1b081c1c0800075005035200400c1c240300c4620302502030006400030140310510100d0398007101030b5000e00300075402c980c1040e4a6041c0b03884a01024092884101500e403010800b52504103042a00124282c81003441d081c4102042400e5a206008010659100900400c0030380f40300c0c2c100034010b105c5860100303c2078028008446e1602034a0f402481080780314503075220700f0303030f018060701c11440080d0a0441d580d5584440140c201031017110034038046540e0ba80003070860036000c03a80c50f100901c4c1c1c4001d10f2416092400b08007220060303145104204985101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 441468156 1250 441466906 441466951
    0x6080a020a090e101802040516020a12090b070309030b090a0b0402130b03030301030b16030603020f130b0a030b040203010b010e011b170a030b12010204060e0f040b060f04060215040b010e 82
    0x40d100c5c2540034070700c41101c0f4201d01d005000c02d4540c0a004001103210a2446c0c0b04099404030b00c400f12160310690308028155001c100b10b51101a40c2c2041144076400190801059080901e044c100c80c803411003da1981d950209040c2c4604a1181c054040c1d00110001801481c18001016801d800e10341c00050004210000c07920f03581098004481901003001480f02c900721442d002d102c101045d00d070922100f800d550114100c00241c1c034000e40654901d190b0340070320301032640040b15242800343c41003204039500c0c00c20464400301035905a01951901125800c103511540e5000d0309110103861300d10004c90310300b00c00b140700c805844060714941c00485070103c0e45120407000303000034603195402181201c007100402100c640b03400d000702c159a104001c10081d85400c000b5406141100700d9070541c07a8840000070401038803088181c02d50115000a20040c101006d8002c2c2c01569120f0b8201c0302d944113000110b0030048070a5030040c142243c803800400258404d0101d165010101e101c0034002c1c480381c0350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 441469406 1250 441468156 441468161
    0x70f05070806040803071101062403060e090c0420040e040f12050a17010305060c130b120f0f04110f270114040543020c0406080a020a090e10 62
    0x80302101d0940c130000601084135441200030640494a10017000b0301403412143c0d803900d0510801403013404504c9036a0b481028000d80c02480100b00d041400703c4a8945035080507215001d5170035140c402c529054869010800b000442d01d14500d1341081c45143c90304000c547c0761440740c010800c0369034844000505d000101e180c018009464010345507180c9078614401c01400071000c003183c61030103014110041011840010308190400079001706982d031440d07062000008400503800c040c2002c0c00018400e01d68894101721148614220380b41c070100c0d5121058083c6040d5000d0760051728005141124494600c0c000300625401038000385030060449480260301642c800a591888080c5c0c4014010000340701d041d4680001c08904550401251a0038207403210310a10f00c2001603915444140e01e03185850034102404028800d80c2e088204407001c0900c000d41d0707840056000d50049007405000505181d0002d5440c0030703150300604800d050f40c1420380c803038001d1001092400c0248184803017801d4440742ca2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 441470656 1250 441469406 441469411
    0x50c030403080d09060f09050a060e0705180403020d0807021225050a0203070602030c1c0903080d02180411120c0d0903030603020301050c041215142a0c03070f05070806 74
    0xf40c1000c81c0c005614107180f0b04444920102d19000c3d410000a000001c001140c40b8007107541c00100002c1e82c4180d10302040c0f920815420803034202500000b440f1a041c031440e0228230540c420b03030803a040f03d41546021190100159440f20141c1d01110042c1141200600a0501084a0000f0b01d100b150807103030f03110415280107020343d59504040d40310402d5040a01881001e003140380011860441c000c40890781e68080380131090f03200108030b8000e240061040e0840c10045402c03524044d10744c06103508487c000d40c01421841e40441c04450542502e0038540560380c254201501244e040c405c0100401001d010000c000440e420000c01190908a609104084555000b5600010a5400c1d441410f00b10307200581819502c9000b40810043c2000003001d03003501c158403890004003200d03106200b40181450341c2c20b500211480000300304400d580c6060341c045120000680140361f91080180f03c0702485111a00f402d00d400812007500070407481111240e10320321030011100c80c66580c2c400c01d070070710009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 441471906 1250 441470656 441470677
    0x51503340513080313030b06040e060c0c16050a06050a0c0203250b09100c050a0c090e10060b0a0509030c0d0f020a0b0901020d0e040f140117011803050c03040308 71
    0x328040109402c504490005401980010740c0340510341002950043da0905c0010601301004002a0300c7d9103c0c2d0b007241c0c4048100108490303c2c1c1c10041010000da030040c040c020030b2442108407801601007141803940031607001800d00080d142c100401280e19600c480032500038444903000c03640c0143c42c1003005004103904241025082000300f80d0a200500301c5a00c4810031000a02083c8007a54807280c400250210034144101d03070200c1031400c581400500140584010104030001404906030341200d0b0b8501024015604640c400b84000801c480060007000a01d0000703000e20007034070340264001c08000c070000b81122270b044c12000c00100d00d00b0281c0c00071505014201d48080c1141400074041020306086180603040600090000f0764030540561078004009124801c1c10094480d94008900c40d000c0d59000c0c00003066100c8461074040e400e210701d08400344d5404414042e8041881450300c8902d030040120030f881c620341c81c00c075019040210403500d1408100400400140b4001c01001002d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 441473156 1250 441471906 441471917
    0x10080123040e1510141e0a0e090303060f0103090b0121050f031909030b0a0504320d0c021804081c060f0b03010b030402011805041e0605150334 63
    0x8040480000b090b00075030203002c1c40458800040802e994200c182650550302c00c4040246c1400795001480c400c40702c0d4000324004964200303000e400c21000c00114411641619905000b600003401101200c038050000b031321400192006110a0070b004940f801403c10800c4441c2880c0303001d85941c1d007826403d10100700b00351f10000700c06d040c02410364003000011480e07082000d01680b454a44246820004250102d1030350b45000140810075044541c0c03803064102c2e00e426105410404030388213491000100b02c82c0340c1c0b05403e46100310f41c1c86040020421680a480320300c410070019000895075a001c3d00441e400202130180442146140502d0603407000a40404503100d881c115400310a03007200c0d00202500101040140850782c40082240c1d0826030a03c1c0a1081d40034401203c1048081e0340c00059105091001d0301410700c0031400130000d01242c0080c01c00215031b40d80100300f1021041815603261110500000358082c0081c103903330303404034014400c000c81703070100d91000e001404c4640759842c045030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 441474406 1250 441473156 441473161
    0x42f030d0903021206061f02010f060806040312050c04030803040206120f0411010309170d0605060a02011a030307020d030f09030611041d0709050d0305130e0610080123040e15 77
    0x250002410981001000140070719041c448041004402122948160414203003540040980700350702ca24800300c2b1b200c800b0448c803510380d0f40454444d001503c0c1039000640c04014035500f41c02600c6800d000b6100401c0c1c9504e01891655050040d820040040e81d10002c28080c0140d690500701800b40308680b4026150890301d007a2400121804055481c42c1c1010310305808040000d42080300040b00c0c850b004000b42d1a0003000c15180e001e058181c00068105030302203132503d85230350150004400225024074581c0300321042028155240103942020b540421444a19000700e07000b4400d400030070095150841005440e511041c0503103d0100450760040000501000b0103c0c0303a104420282521011012003410f2810300148080154001c09100702c50b988120b008040c0940102ea0301c1402c0f400020310500da4402c4204000c0300101c9141d40155852800100d81c1e5100d00085416140041011201d072100d908440d100c1c00c040700c0d1900e80082d5038141302d260150041040801c00c08003001100d4551 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 441475656 1250 441474406 441474409
    0x40801090b0a020a080a0506030a0f0305091c021509060f0c1f0c0801211e060c0804050a060906020d02181903020a090c051c1a0108042f030d090302 65
    0x4802842c10035250300c1849800c8226174400c1142d500244011808103961300e400000034145050f00500030a90341508000804150f048805003012045c00c850800b60100e40a140ea007204503408002035001d03454005003103204042001815080c07202904070b07400c0208003610242594031030311001031150701c40000b803800b82441d0312400400f00980321060040300c8880d46d0103080194180500e03840c480d10ba850040d01d983c1040d104035549034000318103075010f10240360081c0e00c0350009070f42603034110b04084101c0c154502440209005070b5004006040c0e08400c1d4841030001c004855045030071a0b000c124801a204260003e001f2001c3c842c10142080c2410004000f0b01c501c4521480403103880502040000d46d0300c101101c1c046500010300810001c4550318100c40d140f00c1d480161078041a26824000030030a9944100301382c0340580000b4006a070144015900c01d6030032100109104c409031501c454031032420300704c1401c2880000c02c03101d610b030300344c00060f0601000e20030300e100154443c030b002c1003075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 441476906 1250 441475656 441475673
    0x409050a1b020601050f0d050a02090a1506030509120403050d0507031e03050a1b021207020613060c05070801060f06230a0e0405130b070804030c020d0b0106030507090602190c090204080109 83
    0x20b082d0840e841e0747d0b105139035941c56494540b003240103031040300010005400d6201c41c0d00700c0e45d01110038504c096906a01e030440a402490199680e51940c480e110100d000c40c4100000ca4054071f80080041100031200601182c05602c1010100c00300010804904000460103172200c04481250718041068075000c55268100c5e81203011100c1e682c1c945001d904540b0713030086840401c00c00100e0b1a07030341d14803250021400710700c102c80700d180810483c00d5000840076403141d448640c0714400e009880b845550b8010b03103426035100e40903108550064072800c10003580140c1201c40020092001e8031480d40d00c6407064211904a080b1020102d03c4110121960340b8292141603400b0207480b8803d0b112200e607403146103030218001c06480a01a00ca00840d051502440c10001e00b16801041c0ca54802524074007024286428811400031030300f8103003c07030081c5010b03c032084181e480c140d000340052620951200011141c0070340030782e6032005008000c16400b02c980010009814440008a447c45581c07418451 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 441478156 1250 441476906 441476929
    0x141912090513330b0702061207170f061008061207060e0f0409080a0503060607060504200907020a1b09090501021824030a0e25050a0503030409050a1b02060105 70
    0x40403d002c1c40da040d0600e60020b102820343c0c4000c1c2e2040e4079195140b021900900c950040550309a03030300d00070443d101d030b4081d02e81c0c0d00344e03001da05050940b5241d84110080e4014282c5910f40e0160505030312021443c0708005107940032900901c249034004d034420f45a0300301a083d81200300000c00443c811400c0b81020307c502d41c0d400000307030381c01c002100e0a51101d0101c1c0c051006000c003003000000c04120942c2d58bc06c1130354001500002c080120342003915003003080083c1850142c0c1780300b118004070f843d103141c141c104074814003407030300500b031224410742d40c220703081d015040302c3c4055803031152000c19650300920460508a10031000144d0312600c800000b4402180700004a00c90f141040c680e11803e96400d14100300442c0c14403605449480b00c4400c900030b01a203250300186403240b24104a030341405158040421600441f0340003422b0344503030903c000800140100d580650040004001d030800c82c3e4491030344820f001400050850050400001c1c0440c80c410140c01a40448010b1265241c544c62640 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 441479406 1250 441478156 441478211
    0xd03201b010c0b0109110c10270b0a1d0d050c06010b0f04061b0f06020d0b120a03120603050d08090712150f150b07141912090513 57
    0x140360032041c2d442c5125020140605d212003500e40c803000410118210548107460400416100d82d040c4044542008108064510f600305041401e040d2134a4580c441038030190717420910189095403101c200744050400102c5110f07003031400701c2036580250818046c58510ba040c51381c2e4190750b845c9610b40076251140c1a0008002094104070601289050108480c01c54a040c28404c0344004c0c6a068120304010415001c3c14212901c17280c00200100fa41c0282480c4903606002c000c100c80c000240704c01490f42c1441d014240d482490781d000880e014144070401c0041141010916503240c0e516281000f0725040288040b0f41c486050100704202408004003600007050005a07000d2a42c6402081858800900755441d41d2007800c41400e2440341c01501e60b6408854211401e13071b5890815061a074031014003030b5a030b8503d0700416401caa9022a122041308406520380f0035851640d220f4030b201004150041003401200e1030700080a8030340540c0e14280e1480d14500244011040070782034003400f02d031203014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 441480656 1250 441479406 441479417
    0x4081b0f03061801020706020d0902030d0306030201090b07051006080d1d060301120302010e0109051e0a0206030a0c0c0f0c030c080303070f110102091e0301060501050c0c0d03201b01 80
    0x40280c1e840000d4402c2d480408410301916443c00b1840d501d0091260704030241c0440d000181c02c40c030031020b42e00031000707161017681100d1910101980131070480c0d0b02400000e001a810700010015a2070743c001502250f40500b055849041050003e0400c403403130356101c44801d0700000040456260044a54140b0113001c5001814000200300001c12901c414051043c81c860003a501d0424103200b540310138003840d40c4e00003c114802c01400c03c6903848460f000403c0c981000140040c901401c0494058152640907052500715128425a030015002c80c1012008000100c0c1074107012172100841551300a000c0c9a2000700d0506605101110300503540008545910420601c4412980040c00701121526890241c070f658500c0e8070704501a21400000d158002040404420000160f008018007038030114002c1104c1980c4600560b40c0b0b0041c0005000244c00400d030401c501d040c1007407200d0009200380790501c0c03105204d41407504543d60451003002c0301d90005221380e007411081b02c4901d845410900f4078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 441481906 1250 441480656 441480679
    0x61d03070c03081308010515030f0304060c0618080f2d090405040c17070f060207080a080304021c0b0403080f06030318150406180b040609092004081b 66
    0x7004122241803000900546002074103d000c2c064204903c005001c00000038841800c1c110308a9131842d580040300c134481c0c0500a8403161059001044070100e0f036058540d444c0340045038640d6001800b20b00c54522524100c0f0612000081518000301041c40b84020500d0b10f404142c11504103207800480224195085000803603155000e14017600c020100448001c6003650711450030303500f1000d183e44801d4000e044103650000400010440c1c4090f9a100c4d51460750700303555003208a0740c90340d03103100703042c2250011801c000200d40e0040042d503206002404100d80301021504481c040050408241d906120380800e1204242d803010314103030004008081c0d0b207920b08040d00000c0c0c0701c2c40745081074200c98500d1a13000809840310542d541948000c01549501c1d43c0d0ba0710b0019240004110400400700f200c0030000c501c241d2001c0a035415a98280c0d55088243d01307005240c00246214240f181100207a05c203000504461100208003408031304011b490450390103580d0b100020502210301d84074500500700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 441483156 1250 441481906 441481913
    0x60f03061a0d091e060b03060606091512070302070303050a05011412070b1b061305070311040b040614011805060304060506180403020c0f04090b270109061d0307 71
    0x1003116401030780284850780d842c8500350300c40042480d41001480d00000900c40d2400b14540040030b804240a141300340310b0b0f000400105922a5811164254000c0041c0005c2020f801d010445101e404078906500e0b1902114840300c2c807062000715448000240c002034500100360f45401044e41003645c42205008170f50404a00549500800c10201d0040c4084e61880c00103c004001d4107004000a0009594032000c00298000b00380103502c0d0304040340309040c04141c01c16600d1035420385c401c1e040700190070010b06551b5203040358100154002d500c6138840095160b0b07a6075a03c101030040104034005603280d07401038005051058280801c2e0803400c213000c010081a202e0404890f0b1060380954002850358824001642d0048190042100242002c00b080109500022400c080310307012110702480007052410401a0340c900c1e07100501102c406004640c540d040c40164901c4001450881c1c8a5803804484440c21501d200c0c0c03040d40d5040d240c00d00301100807140c081803e1202c00c1d8a015524040031620b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 441484406 1250 441483156 441483179
    0x40b16050a0c060b0612180c0307181a1c061802030c100504032901090e0d0c170d1a1203030c03040f0f06020901020c010f090b03040501060b0f0301060f0306 69
    0x403009031143d80c4445040116075100021100d5030341d0102840c0d545401c20a0480071101c2d010f10481d086d510030700c0e0750103030383c0e20b070004408048480c13404214524a241407410809030110344615510000402845641070b9110248040000741c0d401c5c202c80c02201c0e43c2002e10545a00708043c07600421004540800f42c1c4011424100c41e00d4240c41080d0749030b540580c112194800d034ad02c041c02c400050100b444000c0072480c1c11a0310000284040700c016600c83d01a08115070b0640081c2c1c0c01c582c81240007006460049600201d5240207080746d2500040c030181401c00c81d1700100890083e65601c801c082070319108205003450464007038030308606541c00c030003006640380b001400380d82c10ac44001c00014100045400480d0505502400300610850780f0300d0110044d41010701da960150040f44926492544982131140c20072001d0b42d103030b500b45450196050116030024105480c155251500440c0c01503015000301003c451080b03c2070750f00d6141100041032503e498001804250501404021089000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 441485656 1250 441484406 441484427
    0x40303140919110303070f03020601080304120b0624040801540b0105040f0b1003020705030f1207020f01020a08150d02040e010605040e03070b040b0c12040b16050a 72
    0xc0046905250150a10365110b400c040307607559061000180c806d04000120000c1d4031021302c80d408461a60340c9850103107071030b40214024048402c0c03010700c08902040b07815011a0300007001401003100121554880356800710007080d650b151200c00a001c00c0100d600344609903840d951031103d0b245803c0380d10309041158010040c0d0007520142081680560a10741c00311000e40648010740300601e21451902d404038a00074407800d4403540c680041024081e945009512113040c00500e5251207160000003a4000d4000c40c00582e0741c2d110520441c0031a092030401008501c0440002001620b4081c0e002450724013441091080d03640140021522240c00540441d0010342200103107101c2d1042001080341d1102031640a54000c6c01d01400000320b00040d0311001c196002500c0c1031207441c003100080e954030311030104c0081c40703030101d400098046041c401d00c40350400103c81c0c1c0c0743d1610003901c00c00800150203a4043d070701d20340180c0c01d1080b404ca00c10b1500b407410300c040c10034605025422030040d00b01da021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 441486906 1250 441485656 441485683
    0x5010b0316201e0109020d080a05040e0408040509060d15181a090c0d030215040c0519060327170409020406020307060606020f0d050c150a050403031409 67
    0x22001d000344441c05410402c203000700000002e103520100c0d0381c80c10740d1010708a081c10f9410280c8921000090010b004a60069401601009040c002075032001c2c643d0740400308a00802c0820300c00450068080c0c070800340102d02403014592101d003840104484c03280058040c038401d0014008000c00100010810140c80c12143c80029880d45038034202c01d4a40c40c401c038000c2c2503111032080801c1110074032030114011107070b4104803040601e0070fa052180a20701480f015025a004001e07800c0380b0316a400407150304c00c0c070a1410b02d580320f9840b004181c03465682c1d0045403048214100c140300f40c80d4036114804640001c4800845005800c0c50300c1c9802010728030014210162001880a0260002c0708440080044103000c42d0f890741e071100025101d42210000312100c07414540c0000300540700060750800c299494000d01342d5000030541c180c1d6140d0141e080078145009644d0090008034042d03103101e00c160411030300482c80d46424940142100d040200044a0210000c00d110711a0340024507829000c00c2c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 441488156 1250 441486906 441486931
    0x6051201062d09090b090d050c070e0a0906021303030807080114010e0d0b1503120a1403072d080915010519080d0f0801090c140702041401060306050a0905010b03 71
    0x1100c14034030031400d0b9a50001c036a0241012444000c12900900042c0304040380306c146d4904a00d0000101c1d0302d882181c440b120640d20a00051000306c011100c040e42150707101c000011180410394400302607130880b10720080c58201c517600400905800c0103032258001356520342202a5810310020701ca4101c001c85101e410005032803441503460f100da2074002d41c3d031034019008410364644a849211070106040300c5c580030707005810060070042d80680c00c4e204207103110f0703c41c047c201c03a07a107510241c03c0e0001401e40d8100003602490300310700055418040c10044404480d0104420f10b1103002c0e001450140415056030b100b9036100200c1d0b01104881415030b031084454803050703d4503201d00500d0314081e4002c800355000f1212024800c03500515001543c251135120959560307038401c00c000c112103a0b00784460110301041c1e41a00f4108a01c0001d060b01031008000095402c0e681c1d20008072100700745c0101010a503100c4090002e49041b42d01c075030040510030300c140a690f0404980100601001c0c100300c16800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 441489406 1250 441488156 441488219
    0x20a0f0501021215031218040b0a1508060a1712090a1e0603110c060105090703110a031d0c0a0b2d030609010f0b0a0c080c010c030605120106 62
    0x250030740440710b59103414044940b06003061034915048030381c030107013a0307100344201900e480c00560170f03106136000c0c00e54114111140500180600001e00b85900e5195400300c60441e0102d16040c2880300c3c20315802c07113a680e2001d5854020306010344105681c100c000e4002414190400b030345400600e4100c41418449903648600512011510900d0b1a4024489100082c00c0010428640c0d6141d48100d03502698184289060366031031110922400b00100700e5078100300300501c01c42c207040c22101e03048080f51400080d00c80c2c2e803948990094005606140c0001c1e01c42103295420752141c0106031302c09448001800325040e040c400107079002198854480101d0f0045188a401d4003142140340142000f1420b114041c0d200f2740300455241e00440e1081d105d5104480040740701d200304c0e2040ca0503506060034103403a0a004600503590440070002c210368000d0308111406007800c081c060070104a01603100030030621305144c100407110000d050700c20002d070701d880010445c0303090a03400b0400010301000c042c00d569 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 441490656 1250 441489406 441489413
    0x803041101080108101a060a11010c0305040557090c120603120309030706140c03070e2803140c0a03200301090c05120705060a030221040501140f010501020a0f 70
    0x320a2a012a68418004600342e14040d4022701041301c505140e900801920b400c94105170201c842c02e40d0701411729407003080403101e0f964009a410f5613070340514180c2d4101d01b001c3da25070302e07103070040c00c204091503000c051814401520351601e415404004689084142c0b805600814070f90140c0716241c55506000c1c0081070441e01e050003c180d600d0904024580c2e03a24005050300c6d80c076070020108440c0c1034640216072003c00b502240c590700411440b45e05030b180d601d490404840d02840045880d40c000680e191b50048104100d0120a291440c80900c0504c28618200703820b045000307a14081c403a40240403888420b40d40d5900385000e4a0f802000a0848071440c080f4034507540b40c040701c5a8041d80781100d18414403d02c0c03a8500101c4800711429000442250548c03522480340d48540f68200d40c0c00c0c088110024000d40262900441201440c0c4252101101303101e101502660203a41c07d0f59101c004c000c8c1251091481503122803600c051182c01e500d400c0000355a0904080c1c040d01851003440c051040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 441491906 1250 441490656 441490691
    0x5090f0d18050d060501170304030507180b09010806010501020c0117011e080106080a3005090301270c060f050d02030a0f1509051012020915060304080304110108010810 74
    0x20789409040303c4070b503280514244009003420b00800c14512003240c80c480f00070500000725416a5403000180c61180d1603c90b44400304007160a2813072810351264121003841e01c40b003001d40e000b403501e44000c05003945402c0002e410038240316600d50400404030745811100f00c28071101d50440d000e01032120000044600401c0001440c2d401c00382e029400d11500081450b0300003031941e0560b00a4111040b80000840c006510085110407440d056140300720000c0c0c000d001c1c0c0040d14000f032000d03001041ca4a00c040c15509220520300880d403940c1e007910300e0601800401061007001d403007541080601c000c80e4103400303001c5e0b025400c510311126800000044075155140c0003c3c003081c40d010024024800421910386003030945006081180b460b01001a500d181c05030342c54003c480c0c0803003450500383c515030207000c0e075044020300c14075442c0d4421801440c551a884c00440c4654054480c20340c69040910b401e090500f100c401c0c681c1000f03100030040c0850540072500250218580c0c7c0c0004074001552020200c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 441493156 1250 441491906 441491909
    0xf030a05061503100c0219050f0a0b011d09030706020c071d0901050903191d0607080c010501050f1e030a0b0702030a09050a2715090f05090f0d18 64
    0x20301400090000582560004a0b490403048054420850b400c640800c00c4658201101340140d20085d00540045009585002c05900a400381c41700464449441c0e450416034040403507200300840010001092406a1b01c820b800030303400250b419003084da00c5075680780143c5101616069000402d1038403000c041184d080200581180030000711031b54001446103820480d030035071440d4203003400a50100408030464000d010b40f6880c1d10400c4841600c00c484401000c5002c04003440992101c5000e075480300b014140c034071300c01c6aa483d074442425030500c0c2541d1060340700c507004883c45042c030780c0b09a503145190303030404414005201000311ba04001a1401081e4500601101d441d1418007110300c1e03002c0021702801c408e40c1c44100c1181d075a02e00b8081054001c2c86146240c94604985402481c800e51540313881d500407110200e1a4407041544000310052940031480f015600c038600c4034100c2d454000c00c3d5004924001a00720135242020329a04c403690459060200300c1c4400e0403010310901c0e62500b10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 441494406 1250 441493156 441493163
    0x9010501181503020a0806090402011e14040f081c090b214b07090b040f05041103060d06020d0e03120a0501150504090b0f030a0302010603030f110703020f030a 70
    0x40010902c2c00c000b4009500444807440050503100000e4160b09000700d82c180140e5041c3e443c000e40c031001c00c050300b1900c41004040c6d41005110b04001142207402c5001c0c001901881524402c1d0900c0c0007505440c0645040c82c868044111010080c810383c0c000e0825400c5881c007500d01a81c1c1e1094681c0c0321070448130300c29511782890130903013801840d2001140d00e011243c03c21071101141d40c0c07060070210303480e50b812000c0031240a03c1a64000520001c40320f2582051480c01e040d80c6285e2980301002c05034025801c1090002a0600c081005203014001d80e080601e9802d03501e031031420404003048460308103000151203580c00181c460001c0c1c00e42c0d84505444210402545d4a0ba904107000410b28503040d111240c0e9241050004100a0906032030550404959100c0a207400d14150444014090b2140f10a910486600d6210310644090081030140d40c466800025102d0035413a018001d241500584010452851030504074010005640c1c0c00392501166042c05d421131b0800007078941054088000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 441495656 1250 441494406 441494429
    0xd05060406030510050f010f0b0414010e030d1e140706090813140f15070312062402160b1b0109060612111f1803050304060f0201060b090901050118 65
    0x200c0d5a100c0a80c0b01714052184184400c466981c5c643e030030f650b46200c502495120900401040051101803100203868901c107041251200e081040020b0170904036052107004604143d2a600c081000300c42110b00240481c1003003054141e94110503451401824001040c0c82c2d40d80230b0800034415030030103031251401c00f018a103080e15284c122a4402c2035885441e1405601b2060442d11b240c6002094800c2200558a256040c152a600c0c00c0b06c44151815291214940d01c81011a0912007025542c10a800e1110582c00c0076400e040004c0c5000c031910440d90810340340050510403a0b0f600401c90b2564542413200c0b0380d41c0c007a664500b41c0102060080140818645100012281540c0d002d030040d140c001d03491402c01010100510035050f1040c0981444030100040c0845898052410032040881942c81c4001140d00d07603031910701e140d0241c0c01200c0480c165201c1c006010342d09002d0300028080d2001c0907401e03c402d903000316407401010b018850610506100c018038104031043c2c4540100290302c002d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 441496906 1250 441495656 441495673
    0x311010c021e0c060306090a1820030706020616031103150312122206050411031905070314030d0c05040609051909020901180f0503061b0d050604060305 67
    0xa50745441c11030707032035886403030003002d0290381140420f1108501202504051039581c400040000c40c0d0401014012460386e80d0360306110004000c8100c00c60700c0d200f0304c40d2900c001c0d8036042c0c1300004107068a8841c07090b0702005040c4960381d404500940c1002295054006894040a098015008e000284d010444c8040304000070681808100d000704170058081e41d642084590580c0840d21400c80c030b214140d542613000c0307041421040001c050b180302c50345409654254665803101a42e60a4a058940e00b441f525031289602d000c0c8100003480410115030003d0085a42e9141d40b140300506c0090865040140c0225803408140210f45255660800070482030000700c10180c480d40141c000e43d00000d40501d404182c81c10001d0340802e102c0e841c06000c82d42103140514250195101c42c0100381081030b4009020081c1e8200d40456016085010245c04401d04103001d00d450244002c16000103002075206808040800f5011606030a0241ea008280e55035400c000c10040c1c0520743c4010050b202d181c96 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 441498156 1250 441496906 441496931
    0x4050c0d1b030c0f020c06090d02060a0e03010f060302130513020a060c050c040203041a0a020d09050a1205160b040305040509040813140307060c0609080c0604060f05070f0804031101 80
    0x145010007141510100b00300074100710121002c4420050b0080540d001e10000c1e000c031700c0e041c0f001d000a410f000b403980d04da40740d40c0d9004c200540c00c070302c0104010406e000250456440d0078000c030b403c03104096404122440c61500000d656160480140c040c007035860000c0707030b0030103202c079210850700d5006805e00b8021a1340d40c900a014030030300c0c0e1003681c007806241686c3c0351518060007240e0007603422034420000c141c107102c95404407035000740c01d03100519420004500d0ba01e0040c000e04104da4000d102900d514002c03420000071315901032141500300403017008a082140c0b0004000701300070b50480a580040d5a0314503054038103210f15045a98450301100801003000421401000c1e901e41710b41c1e10440c2c0369a01c40117021404602c0540c0340d0700d5007007010180a050302c0b920310b626881e80201808619040f4503110b5910944c450304048889030003200800091203101e004210300c0190802c010805840e09007002010105120044801c0001c103a01150034140320b4125140c016814100800544203c0e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 441499406 1250 441498156 441498191
    0x32d020322080307030b0f0d03050d06080d0f0816170c0903011104141009090b130e01060608010605040e070f031d071806030510050601020a05062d04020f04050c0d 72
    0x1381e89800081c104039a202190a000c880351402da517015081494a01169605450b181c104803480924103542c0d5400003008081040103036202d41d250b403070302d0100f4500d200d00144000d800a0001917030b103008101c8404003907400b05440a10001e40d003074000043d03d815080646510078504025403542c20480001700301c4001c90000c00441e1680084100030840040c280410104114400e402049042c4020031003003e0903080305250000c001c000c2d40d14030000b44048021144258600d40013a99506000e22603250819035143c003400840c1001d40c20305141208411172200020110820450a40030001107540240c001380c2d40e0780007502088082d143c0e100c004581d201c240780320701d0b20251602c0610b1011001d042c8074130b0094076040400340c034041e40115120401b820024250314118410403008501040c010312260f40164030030302d84400d5400c0c1d6100c0d25075007003840154418a1114540500006a0307410798012003000d01039402160a55995001c00018024554262000c42c10061641c59840c00d41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 441500656 1250 441499406 441499411
    0x2070f080f1b0a030804060515060d05010f06080907140a03020d120909020f0d0b01020313030308010608070e0603070c0303060b040905040210050405010f080a0609020f0307032d0203220803 83
    0x350315090310740b81e003010955a401c1c1c140d03c040d021a4034100800c2c00700b030042d040958016440820700c10380b84071440c0402e0491b4407804991409503912030043c080c2c904c2c0c400101c00108118074000500c6e0404001d101d480d8809071213401d070700301150f1a515405446600b04d0310003c6800030a080030710380842c202100303c8041081c504000170005400440c0810031031080d519650b10040d085d5050158248520001344084040a41544004c4c00405510312a1200840c040c5202c3e95a4070411f525142019040810240c480c50604c5012805207100342c460780203076a841500ba00e0041e0001e01d2034102600240440d03041000c0340000044c0c0491003134480d4124038051031080d02c1828240c00524021101806540121400a0242d074110003400c3e00c07529036241c02030034003800010316540d202003503000c85e0301a62410003008000b004100c000d580500c108200101484034090035200341401d80c072414000b030000c1100c541c2e800300c08036440755201081c000480e01d030384e21401c009a4180c14a5407064004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 441501906 1250 441500656 441500677
    0x6050a030f051006061205130501020c0708010e0d0c030807110f030c070b030103020a030f031404030b15090106090b281713021c14060f060a0b090a030602070f080f 72
    0x24040c040e0f001c4a210f120300d00480703425590740762065942070400e002500c0050481c062140208413501c001c0344c030a1000300b45c070b140d2180080c5800c500c2c0010b000d0079200380502d81407164100d4004521110f820240f0720001ca9407500c1d210a00f543e501e50191601850700d0480b210302c0c031458880d07000104e8000000c0c035114520004a0310410768421004825100900001350000301c413850401c001082d050444042320700c00e0500400702079200450300c8042d00715500c140c5010303210b1400c1c41404074110768130f030540e03030000d8600f8206503042007005018415280714444012000280580b001d01e00094030621150800c2e5905103142001e0200402960b00880b50907445107400c030100e02521b03085144010301641c050414207030000c2c3c855403100c3c1c210300d41c142a540100d00365884e034482c00c818402c043c4a81240c074038590141c1088414040e1041ca01c1c1c00000c00c0c00741c1007100c90324958503c0488000c80e90b0201015a45010764900046405404200180300c8600861541022140d05000e1f100300b070308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 441503156 1250 441501906 441501913
    0x105010f030921091d16030e33010518010608060d17030f06012102070819020a030305070e0306010e04081306020d0f170402090c130608060315040b0f040606050a030f05 74
    0x5c040400e02c409080a41d80400300040281c024080c0c41e0194100b00d100f4030b0b01c1030648018511400f0103070301990748081c2d90003560b095611500035030a003224030b140c09420140c540c40c0c00d0041034104041d4040301070052034240205c4000180c2c40f541d52040d4415010743c00708030b4064464102d242607100360010341d04003203d050302c8800070704594890b101c189a000290001d034880c1c1ea9507036050038025440f9900648400004021400d10803080c190408402c0c403c0b9401420300f10240c0c03d0040445102030401001c01000c501e6070249590002181d505440355403100c038071161031b90301d032410b03951281d110048030070a0014000503c0035004500c03424000d4007a207035507000f6120024221040c0d00c0d010aa845850032520101e0050700704081d030941d00010442e19a86407146401641421000a40c00580054155410400c41d42014005c01010007071100c0e0701126030809507648290401e005112420014210700010117001c01c40e0040030082c0005081110041c1e22410605c0c60203190b40401e40b035612 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 441504406 1250 441503156 441503189
    0xc0504022107020f030f1c140403080c0301080d112d06010902030f15010909020d060f09141306020918010303030e15060d05012009180105010f03092109 67
    0x10f001280103250040700001540c503201ea000452a22500311803d1002c1000c00c24129882d44052031207000ca5440184440c1201d0345041d140042c08010002c0174890004400e20040052000000e800d580761511820074020014002400b03528003440b40c9079404840744d031040000000f102060b400640500b03240f058038080da8980a03188182d11040d20405141090074000452400724051701ca00b05100500d82505543e984000000c2030303800c500302c10302020343d03100810800c20741d030f5543c40c000520362260240b10031603c2000c1860200c40c01090b900303481c07a00403101410045036a040710010311005004330392f004556009190701c0d0400340001c070082441c00c000e58801c02030000e080d0740d042a03541e004119964030f81080c481024488402124290740300e04804049006d002c1000c100e65030920b4805840707410402c00c11441d0b030038045205200d17188902c010300c030ba070b40d010407100a00f01c01402e0100744841e95142062030342c6040c00460010f121910002c01b9600c0e0f00001a0b003c0b608103401c6607600c074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 441505656 1250 441504406 441504421
    0x210f0703050708040204090816051b010e0d020f12010f0605121605060a02070902190905060c06041b0306140403021c081f05151207080103030c06090c05040221 70
    0x15182030b80c0c1d510225001c0c9000400602d400d03081003141b144100840343c1000050145540008146802103070940c02c400389030450301e1800009a6007046003460505c1405400e400820700348030440b00017030700030500c440c03c0c1c4005840d01800750b41d211002c84020414480c02429550007050a4000e10b8403d2412001c6140c1d0040f00003154800b0b5010721840b030078070621300403c1101035400019078a003540543d4900240040c039510190144020201581110780b008440007030a00c040c540099224a4003806001c1c00700b030001503001d600c15800002e03110032040c1c0d0106c05442508030f43c0700030400d40c1804180700380401c500c070040740150311907000c494508681c4980c000c080ca02c070504080001c1c0903080000d601550a01030044030280851114408a0702d4402091181820500758001510006440ca4144101c1001d4a5102d01d0900d46040e00d5415990020b01840c403415024200325100c8100740b080c4040c60044200829004008554500b40b0103071070709440c041e4411180c0401038040004104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 441506906 1250 441505656 441505661
    0x1c0606020d030e031b0f0a0303090b011203021507170702010b090c0f07080906040305070f0810060b0d0b1929030f0c030a091b030605130507050f010302210f0703 71
    0x1110745040c003960401201d400464001c010500d40311151b4031855016803964101400200752490082d640811301c680f00b030404403d032407010b81c49036404107040c84800d008681d002c140d445190f80c0d12500e01c441515a02412501003c60194104590340c0b028184185160154051150f1070002c1e65402815507513142250082c0c09002d00540c6004001c10141c000220464001e0252100c002c00903401c281e12510b8030380c60040e45801c4480b0403802c01106001c40c4200f08442c202e10240104240200c604020b00050540640d0081d18030207600c40c1c8880d8865039420803a80d00314140c02c50700c0e09045542d15904980301720514441d0494101e14001d402c10844c0040442e8818103000c102900342d516528101d60b6103500007404500032960780e803e104002000144001c2d036012a0950700e075592400c6043c480201c0324060708a004400b150152240040c001288400c11200c04407815190024200f0040e4040e20a0310500c0c4815900202e920844071401d29172280141607000c40c1900a903100c0c4d00a908 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 441508156 1250 441506906 441506921
    0x120604090209060d0228180b0d030e01120f051006020303040f0f0807060513030e030c03060a0c0509130c082d0a022712120706111c0606020d03 63
    0x10080b01c03160000740a4141004290031141c80604503001d1000fa07001403902d030880045c1c00c00001c0c8451902004070704000c0141c40d000f8605c1c040200300c0300410078002200100503510040a105038120b140d001603001c1c0c07000e8452440d030100c0500010210107100f4008000458490009050700800851079500c0081603074400e03a8040c0243c140100c00340c5658840240000007141d5002e03080100c1000903805004183c0151145000c550070b80140340f40290085140b00207680c021b91111440d4055958000341082d088080030800241e028800501155140300d1168015027101c40710360144c0e4404095849041000d00c039507500b100365241c2d5100f4044107080c1c45001c050000441c100119a0143d40c0502c94011228040040c0381405602d540c0131500800f61013003180c0c2c00600301d181c6c40f90500380701d40c1c900001410003422031b000e180b0721941c5843c05803405c05800703030759541d00c42001b01c0c81c1002201e00100c602c5030074500b100851075400c1c3c05006240251401800381070a0307842400d00074001e890 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 441509406 1250 441508156 441508159
    0x9060f080c091c0f021806130c02010605030d0c0c15140a02012d0507020106270e030c0303090d05030105010e0f01120f15050d0515041103121206040902 67
    0x581503140d5031001d200765007129416035403022403200050050442c0010011900d4482c0480c41c513600140c1c01001401da5031202030140c0c0034045030410065a46000c0d42c1d40e00400c41d500c00056010700b442007203005248a03088543c15114000714028413a802c80d0300d0b00e500301d114042003812541c03101206900d000490f0011400b05400b000c00941d000110005400030f07416520001a1014007404442414000c07a20441c038084440714004107444024060554464030b1070009004852820610500140c0701d00420300503c0030b4009003402c034003000c1c1c10407828540d00302c0c21680c40303120440003103481c0c1e4005e50300000c25200d240c19601d8540c0c0a81c0a40e03040380c4050311100500700b01c08041c440710107850141c85040004103009170383c00b08200d02c6040d82880340304900044607252130360365046226245d00003610031401c141c108000510001460308540055030780e1101c150701c903072901d0301d4510700f10341d0034030303410301485803480401b900f480080c08803c404134887c0f0506446c0d82c8140000c4601c244c0e8017030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 441510656 1250 441509406 441509417
    0x60c1e020d0b040f0506190b030c10030e0705090708070810060e0904110d03022112060d02150f030f0f0709030b18151f15080417070501090309060f 65
    0xd401040900880c20f6102c0e01903006442116140e07500e50341810005ca41c0c001d0010085124401c8110039440394000c0c43e40190000c10284119800180c0002c0c5a54108002c041c0c41e000d1810401c00123001b45001004040c01060a030f0424560161086900300c40e03603800910448001841c170014070070810103c400d60349510444511200c00c0c032081e4a4018015201071541076410355042c0c035010310802069000398042c0512044a059082c45103c402200620414062120000da9a403405507541c200104458003001c102d0035102146041c0740008210310400404100c884149070790310f004500c00e040c04001940641d84654000766450030564161000869500c024400169103aa80d150085038009644c0c5a031540480100d24011002244907103d207580c0c0144550100c0c414482101d00f60f004605080302406c002544412444401441080080c2200442c0034080480d440640d4441c406d060030f0b54520301802c215000e404500c0046001492201002620510a05125a0481c3d60355201d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 441511906 1250 441510656 441510679
    0x20c0616032d0203070e1909230c07020103063309140f0f030709020d0b0303030118050a0207140307120e0607020415151e020d08010905130c060c1e02 66
    0x16030000e4000900d6030b010f016006c14034005e103685000304041008886140c02c00c03100e003415030b80c206030340e4450203080c62108051000340c1d01d1030203100100e0303204031300954554a40d8187d0004901030f00503075000e5095064120140b400c510f101ca1004004180b030380c8181c400c03a041802c1c0840d90600309125024407113440c100b1001003490b0040255907480030003040240f01c000800002820311000e0b506c009056540007402080882e0361b400390200888080300074606541c0340c010f400d205000803102010784140c0d43c4000600e44102e59042d68035564018082e1340c0520000e0749402d0baa82c0c8150f0080d55040907580708121682c2c0701c0c0610f00445075020304040e04001c010f5003480b01421a00c103441166004411010a0380c4042d115003504003042503070f540c6280000c01c074000340d002401414107000c541003401c0e807008458100303c6c02d50445002042c00180d44d0740e13410000302c078480d548000130306910f00c03180f0024116038810851054140241c4030410f01c0e08200d40c501d134103010300c80b0002307420640c024030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 441513156 1250 441511906 441511991
    0x3071103060105100c0f14010e01060f1d070513030305091e0a09110c010e01140114010207030320070b030a140103020a0b0901260f0a02031018020c061603 68
    0x7001c082c01481003080210b08141b85c1c0c0c411100001245c00d800550b035480c980c62042d108240200b00081c106001c804103070900780110415000c095070840c60103180c8400115111512030f004840a0020b40e01f202002a80c0b2403a00030115806507900510075000305401c0d00c103e40c080100c00107600d1000b80302188051408102c0e0000e80b004200b22403540005000da017039854000e0003411a4140d41800001c1c2002e5201c901c3d441004060b008448241003040000c03585036000580304003a241c041c01c094004d880c034940c00d0104c00a20001e0b6107100d004200c00000c0c1c50314040302941c0180402c250500c40030002428408200070248000396000005240401403031494800600d0f02d00018504401901d110760044620340d00390b441507441c5412401304000065224807840c4d0f8000707402d50419469801d0281036000007081601602850040c0000001c8114502d603044804918030b0600761030261601600c0000b4880151120202080c00d03c0350302d044405041c00d0080c041d50740c12500d0400c0312a0102d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 441514406 1250 441513156 441513167
    0x4060809032a03040f14090f040f0201030b0409021807030e0a0309150215040804050a0b090d12050c1006140f0603040305180a03051e03041a0f070b090307110306010510 74
    0x800c1242c5010820001c21640201c40d0b0742d40180a000800800950406082c0410708a0041042d42601c00324024040010100043c2d0740b80c10f0b40902c1d000ca0442c024800180040c48081d4009511400302042804210556090607214460b07940f020000c29407010881030700c3c1c8148030401000141d100405000c1384c0560344291201d201a44100e6440103248a5580382d180c8056805445a50000c07404100c2ea1502c2043c030301c0545a1001d5403030802401401141c245000d01c140100618002c9a1003401144154241d440f2101002d0445134140c100301404401001203000302c442c400c540c9400139030301c0d0602000c404030f240e2010380b000303145035540d860844007504040d46007070949805901c0740f40305036943c50743c4801031070280000e01b080510180640c0200584100c218002d50414001007000a046803d840c420080076100d03596101408a07102440c1d00c50607030f009040c0400081031000c004000030192000920070384580b0309402c40e1004050369240248100b981c0025180d03155114203200d103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 441515656 1250 441514406 441514477
    0xf0c020309060f09032a01020313050d03032c01050903040b0a05130504060b09012003031b090303040617010602060405030a0c0f0501051609050910050409050f06010b0406080903 78
    0x903015804d084c075000002e400c0c01842c00500540d0398011140b150100c00852854504140034001036280000c2c105d01503800399143e00c2072034414500c038800d402c00c1c18081d81048484204e030101081d100705082d8001003141c13042d152401403561a04000482c03a40d800021034090701c1c014510541003400c650070440d81d80d4440900307080044a601e00020f000d450b107006d94405001010101e91f101c100c00800104420100340c00034001201e6501d01c19505100403080302e410099101041c281c2c0364501c42e80040741d20136107040d10b0301448002030000f0038a034400501138121280c2c5000d44220703680c0340c0c0c0884c1c0c0c40d0403da0380a0001d0b00100144551503000358026103120b803140200d0340341c01c41c482d00c44908440c41203400260100200e90b01d141d815511100c1513002e04421201e0403580d0400c582c60b8000c0401d41c1c010300d40a83c0e40c0e11402d2040c400200021014800c0c400100c070090360b15600742c1c42864001d441140046040e03540402c40c1510044241d800900482d5500401070b8074400c1c5c00f03010610032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 441516906 1250 441515656 441515677
    0xa050702070f03050304060305070e0a0e092407031803080703050709080312010501081024180305010e1603030f0c08040b0406020601080d030b100e0a09020403060f0f0c02030906 78
    0x51200002e070000302e24a0b000001c6008401030751701c4d00c0c685070024003540c00003010f002c201315114908550035510781c1e854505403a4094008601d42e84d40c460300519100c0c01490501c2c040c880110030041c10820815080e01c070b0092035500740001c01418201e2040f0100252000700403c050200140e080c0c1d01c268405035001000c5e14003419015038454055007181c2c4000807982e800002c000040c417403540c020320020340116035080380041d007518092000c0c10300500d080e410303450a00c0724034000d85520301c512100d810040d81241e45503642031b642c3c50005d00900a56482074114043e141054001070700c207180301c1007229011f0711582111409480115901000d116089803c40700901000c108203041c04003034009803c2580080c4841d5060a0840e850714440c00d60070800c142c1030408d015026124108120000d801c281402000410f80c071000074504d0300b079a0040440144045000004c0c811075030000901743d141020100441207a500003041540c035080d10750300241c4d02c1003004c3c500030b040c410b0081c92140ba4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 441518156 1250 441516906 441516913
    0x60e0603150d02060a1e140f09030102042705070c1106090d1e0314030106020705060f0412061d07031e08070614101e0b18041103090c06120a050702 65
    0x10240d00041450b041414004009246980b02c0301d0110909880d50180d140b090802141d540308240c0140294425200010323101c2d2404104507020303071025015100a40417844480d9001b070038076a80100c00c81680c80014001600300408604100d0059040041081c0c0001104035411418401d100c1282d0040040c140c200c1040c034071200c046041c11286031001d0028445070380f407009003402c00610045c0305403141280c188042004110403900094031a040780d00a0740d0a9850340313007036150080c0390b00507035105420801c1c03202184400c001486d8130507402811050b1000700c11200c0f09103c150764043c5808020300324070f040812024003c0350140301c00d601030300c03500100b0718003111545c0c0e1700155812029180c3e044940d05042c080c009001c0070120300075122501e070605403514462100944907015200d14002c9000004e80410100812441846600c5000d0811302100000e0f000a0700c0c582e00445040603e4051810000c0e510b140610454941072030311040603a168030b070031222500402019248400754030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 441519406 1250 441518156 441518179
    0x30301170613030f2a050c1305060603060d0804080109030915020109110415031e060c0f08040201080601170f04110f0a050613051c150b06030a0c050f0d0e0106060e060315 75
    0x1c0d00f2031000a140f186c4013810b55040303180140041011002e038041009402c00c0100921a140d00040d40c0e80214110345010300c2c5003070350030503258500c0b0381c1d00f00240039400d084510040c16000902d08040340c0c0c8040903580c200c22000d81c00c80c02c840c0050340080c0640d140042d42e010714580f581007500e02c1026002c0c000c51a554030b54400e02c140160501410400c240354001c2c206100d402c0c403032543c08000038285140841100c46000706182c1d0004c1009041c0000480880c109912400c00c404a03079200418504407410320b00d80e8011404001c4030101e0741100001020f00e00d60800c1600c24000b104064010b807881070906080201640102e0f40600055940403400585603031000700362440d5031005400c40b0a1020141040380c1405808000c54440505052913400c00da04d039a41241e031311282c508000110000f21a00840350b91040c0001e401002002080481c0001c40c0c950100030140c490200802c001545e4001c103983d41082e001946611010a000142c040344c40c4009049140100800500304031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 441520656 1250 441519406 441519467
    0x10f0308070b0a0f0903020c0a05060c100c020a020a0303030902090a0c020304060305040f0b010b070b1005130c030e010e0c03250506070611030703020304060c081504020c0f030301170613030f 84
    0x101c40410f400c2d00180e00800b85603c40b82000c8642e500a07090941c0c0503864201c80da24099070303480c0050034dc1170480365180c0080c48941e1091000c405070540c01030805070b03003035030300d05008002d41003c801c103034858041c2d8804145110a0380c42481d4014049401a6040500d4024198010100204141c81d40044840014009050700d0601030203010218040d41d116685418107051000d4020f0414004c1150400240a1036443c1e900070180c1420a0001080c20010303010110090a1035030803000e0958240804286180700116680d0039940040d0200c40c00c0e118011188014a44040b000101d45049240c052001341080b400a04549004000c0485c400d9011054810240e104880340000658044240007c0004c00e000c0c0804d5805946040900e60a2158040b108414000500c0744250343c0060b541c030380c0a5003840b402c0360340d04100d025030b500d96954040b0880d06120550140300240a600c0008030720f1074290302901c0182c2e4059079291020741d0b01d080195801010000c10780004280220180b180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 441521906 1250 441520656 441520661
    0x12180503030d061a0708040504020d0f0603060b10170408070302070f0923040302060109020306040908030103060c0f021204030807170309010605040b06040e04110607050f0c09010f0308070b0a0f 85
    0x3245041800103811440e004c0d030301c10940ca409800b4500080104007071008100050f00b51000d440e0708440040c0e441d001c00034000c0060030031947d0400980d003001c00000a00c40c50303501900c4280c4080c0c4008030580880e000c120ac185260f0301c1640b070301c080a14003041c00301700c29101906485100e8011641029100e00a070700252480d07600c10f205107500c804625540e295001e41e04048100d40c05045091360420342d4002e0f450300c0b03050107011200e0303074040005005555140c01441e00c06400003003803aa80e5841e802d200010703081c000c000c40040b50b81040c04a60044c0b00081d4240700201042e1020b0815086a80d4224254807864003074541496600b040421000000011401400e0310b030000500103103480b00f4081590740001c4411b210300801d200030030281015101150348035a004021001c14060b1130001452030040c280060060f11902c1d0900000000c002000b06480c407044484d5160b41c0c0e602d00000c0c1c01c1c030030036020041290409200840001e01d641e40416040304010700e0214800b101010040e08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 441523156 1250 441521906 441521917
    0x1119030807170d23240312070807021819050604270311060601050405060f160c17030f0703110c1c030305060406050319080405061908131218050303 65
    0x80c03e50351448485840d90b52041c1e62414400c89450750380c41c0e49400040c030000b40c084001650340042c601d041ca130900f99814080c0114004204075529103503c100d05000c45a0742050000328010f05050b54480c150110300e10030707144280d200c0b88506100302100b40c8400d0143c0406001550031640350b10014040781c000b040c0c84120508005840388180d40d89040083c4080c01005000c400d0303401c04001d0112a076840411202075030340581c0c00560790052203132018568868034814491980542c5481b80400505196282c100c0e448000d450440d64054000e50382c4034421800301c9000c00c03000b0008807000a0140c0f10801e603a00060b4181e41c40084984041003021603200700400604410300249400c041c1c06105150b006102514100500c0e4246400b02e581c6884810b55041401d409176132440801885c030f0304442c09000045c1c209500e408084c10010464600074005a000c0b035401c4d0300049094400400070160150000600901d10b04401001c2d54201005d03106005512095500401d5540b800c100810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 441524406 1250 441523156 441523177
    0xa3003030506031b1005090a03060c0503060102210703141605030a030e0111030723190809030703120b12030f19140f0a120f09111903080717 62
    0x29062500d081050f0500c0036505031008904040410303136210b502d482d080701103208031504242e03554041c0d40c2c00240340a040e40d440203182d2814681000301507503010000d50702560007a000c803241910380e80e044840007c10080304181c080810710000000c00c1c407618280107024a440d0703695107041d2150b0070f1041d0a000b10141500c0c1c95000051080c0c0b4658984074031030020300c40768020000304400403107140c841e10001d8403040c00c200322001e10b103006981e29841e05003840d07030030b004148c2e41f0080b00c4500807094090b030050300086410800010080ca40c088201c0d600f95a00d5902c0854916080a140f002080c860001d07603040b02001d6003940c0c7e9194204028442400f58401c1141c0300d0a42c000d0049118130702501c4001088aa01140118000c0c2a81500c0750f42800030041900c0d403038034090880b080c00450100303803481810003164005000c02c951002c50054011046111038059900902407015000e180c0041012841c007000c00c0800c2c07001c805409054450800101c03051a40b50750b102c0b003500f058032000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 441525656 1250 441524406 441524411
    0x9011415040503030c150610090510200703030807051204021e2d01020c03190f0210030f1d0a060b0d0b040804060206060d03120507091a0a020105060d020a300303 71
    0x80102941c01b502e81540038100b00d5072400f41d507003989401043c0b03551034801e59000c0c000076040c0351007940c01554064281014040420340d409254280140d444010380303c1078002c501e038000401c280a106038125880403e904004210640b42c540c20b22003110204480e11031040e0440b0990141e03a5a0800d0315180c45003810300070841024103400c04010100c04420003070565101d036843c5212918007003118200898501000c0c00311240604200300405a0440001c0d4058507038001038982e1030f01948003451001c42200c0410055485152408103541c4504180805501c42140100003420035001034000c0c801c064275868515000e40d86888100c1c3c0113644c12600c2034000315090094503410000140d2103001200c02d6913548010303407006080311000c1d444083d0303030507100c000040c00b85014441c9400202410b19007501500c00780c0005e13504a4004441400042d402d00020440c5440c05400101e00c0540080400d00e0311460501803038110b01c5800d6440750901c40d10761041402c02001d141212240307000780c901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 441526906 1250 441525656 441525673
    0x30a050607020f01110a2f06071e0905031f15090b0306130f0b25030c090806040503030c0a02120a090e0105040e120307033809011415040503030c 64
    0x3c80382922074071070140c00c8003002800540c200f05c0e0321680c82601c210b282d1010109802c0c852503811421004501610709a22601003030001c01984042002488900312041d5242d10052440c104c0703c0030080d100c3c00d5030640c882c00c0400031b52424204a85031708500d07030b040020181401790341100554002d078000690795940c0c044e071041905051080390350101130b08010114081385943c400c401e0041100d0050f00e0360000c4400100e4040640050300b49202d440890303002d4405551030002d0160038500e101d1400124013050001e1182000070f030079401180d121000d9421643c4400780d41c00144c000041c1c10085101d59954091000e08031070050030b010000782c1d2144469400e050b0b1901620703c040e41f040340180d18100c009180f02c500440e403e6880280071800302d999032210b0604501070200b1101d07507001c1980c0755541000352980382030011100d280104140c840e400c07083c410050340303510900c1100d0304010081000d14841c034003400206c0c0d001c0041d600050506440b2008680303590001d07072000d101c6600c240032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 441528156 1250 441526906 441526933
    0x50a0209010f0e0103110f130603150c0804060f0b06070807030215040312050c2505010c050a05030f060d0c0303050d1a0d02040b0414091507021603020d02030a05060702 74
    0x5950701601400540e400792601d8080346001450b014400940165003211401296039180a41c401c90094001c0084032101d01e0600c1d5800145124072080f1200c003c1801e04201030074281c040c60302d400c80f45485554880d511901c80304040e1070300c3c204071520740d6950008000c80c1e54943c2c0140c850b460142401c2a02d4415130310780a4500040d806000d801e0a10708001c20000990014a08201c2d000c5484080f555450300340078003c46024103001025007400280c9848040c80324503410201c0b00e07000c0e8009002a13a1600000e64291045100c08000190100001400c0c851580076070340c2c101030050302441660141c1d46130386e0080746940d0021030004a001400a041010f680501081e04201481e0782c50381c034101600080fa08074000f80700a00a64071984030440c540d4035039010034140c070014850b2078114a05541d00c10780360440e640c51252218801c8010821462000590549041403412907690352800c5808101400c044940e080741d149c8569066900005c90500c400c034014a8250000d1001d0b41e040344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 441529406 1250 441528156 441528169
    0xc0f12121f12050c090703020c07090c200c06030c0903060714030106110a050a14060c030f0a2c0115050607050c040e03040e0403081009020a090614090a03050a02 71
    0x1030a8001c28400d41c11024409103800820718201c902100b1014400942c03032038500c0c1420440c0801503404102c0c5410480300c1030701600280494914134051741c40b032544442c003000440703d41038009000214080240b17146403030131541c3d0000001d51441100c0b00480340c00700003885a03000301c400240402e000b0030038034401e080402c2425042001824004003090364140c04800314001442040100610071004056459090000c102601c1e0404141c8000c203c40d8104601c021003000d120310100d20456000440c0d208968050340c1c05005500320010040d154200407901078049220088680340380880c901034410b07001d1119401d254442d41c00404c007519100351480c03001c5a998451402110200510000a403020402d48081030040340c0025124000552952071400707950003000c5440303000c800788800d243d04442d0061190b0b40c0042249a03090b00c0314074003000ea0140c03446500219240b800c003405142d0190030240c3d40c1c0c55102c0815800d00340751100043d40e5000c242e200f91000d42203004140c003542011f8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 441530656 1250 441529406 441529411
    0xb060d06030807330f090c0902033106020706061806080607022407020a0b0c030a15140f01110d0c02100309240204171e070503030f0c0f1212 62
    0x340101044002d40071101821001c045050580b1741d01d12109412503203580c01a0b140503000a443c040c02a160a0303950b0095000f40c554101c01d01700b002c9407903500c15044561490301070042c0302402c0c03e00d009659803006900f1040040358240e48400700800c4031407080d4078007001004910404180b5620305032216080940140418086402120a40c2e11510f0900340b046081c01030440090403d5031400340c200e0070040609070041201204401340909205824065401181454400c020441120f8a0506480c1c07061207242000c502100e601c546a190403041d81c10300e0601810318000404444142a061002d0000100041806c2ca252401542070101155601000c103080c02c1090410307548500308600001e007441c101034154500d00891030f65440c0c0587e030042c6003440d001c0166180c20a0760320786501040262000146a0160000016400183c19011a07101501540c90b009458285003000c0c0d02c581e152904610400341c24030941e0341c0403c80b846541c03064058842c9c58503280c5024400c4040301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 441531906 1250 441530656 441530693
    0x1603110322060b09041406011e0312020a080f070b0a0603081c0b030114060111060408030115050903060103230703020a0603050603010b0a0f260705040b060d06030807 73
    0xd0042004212108050015048002185002403555403a204001e404440801500041254103020411400b4000301180003044070a94001d42e817101e05150100000101d641c40030301a02504201043c542d41c410010104c5601c10356102e1604c507240c038507490740910140c50384003c0000d140801e002d1009600d5401c2000c0c0d400c03c2c08441d10316207480c102e900801151f401410f001345010211103600d0b901003010b248c8054000c0c840e91481c4850b205190310b0440c0c00354040348004e451148141c5d004641b02d8422680480340c50704507403c0841040c1c404041f5941e000500c10100a013401507038041202c03900071440b0322001d543c010a5501103030400800f8641740d421540c08803009100580ea010a0403040d210340e0326001580b5902c01c00040d0242152401d401e800000122012403d600c4d02d4881009443c521750800104904502680c60700c0d1000c00f035aa21140c2102c94184028605508000e41c01d0800511090404d4030030100c9008aa080303078011070301399100040c44410050b02100c5003000040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 441533156 1250 441531906 441531941
    0x150d14060103241b0318060f09022817100203010b0d0605010903050a02040902041d07091a0f060f041a04030201020c0f030604060509031c0506030c0306060105070f050c06031603 78
    0x1c0e044c540c049507006141285080c141c490b05c088100b42d1500010840c403d0708030f001032050b082d91000360001001d43c130030140d001e4261112540618203e5440700181ea41200d01c1c40d00640e4600908003015440307481d15000140240d0044e544200d400b40007640c0070f41104e00d88155240340410051046a0b40390380410b06000e075402041020070008200300c5a1303141c0590300410040245d100180c001c203498052284898a00300d944407a0b4000081c051003561020b40007041410740e0550f4041ca18203c0c151a154407400d004061440c41c00c05101510311600000ba1890400303403518580c00322180c0320407155101c50008101041550703410000300d1034080c0180c0b59081da140300e820109842c0c500080c0040c2c841c6881d00c001c90724140080007164a2100c501340080310031080062048003811b000e9460a1180c41030500c1c00120b441d0200300a4040c0905031150b614010143c0e0307800e00c10110b243c0050b105402581e88400c0d0645540d070095205082c504038005c41d518550402604540415400035809038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 441534406 1250 441533156 441533171
    0x705010212091504030e060409230f2238010603050f070806120d031e060627080d0e030607030509100b0a03051002040f0e150d1406010324 61
    0x19907180016040f581610f000071b4129148000b0030440c3c416584100e50329481c100800c0b0311042810440b007048441c1e1001d00c04030b074480b11b00880ba011707810f841c22409224425a5001012141c002e0400034a104901107000c9003a0500411801c0c08080210600748003034442c8a00b002c1c5281c03140f503025010a01f810889414101c0320100c0d1014001e011000303115010740404ca1a43d503410051000f03010b000c0031544140080e550050142011000ca00e428402088141c4604001802800207903051907171044103030a040c0c64403d065402140030901400c0c01810003080036003041c004156054003907240c2c80c1c81081194141441e005008000800f00f524100c10300141050226401030b046010400c0802e400c0d0b9544006091f42c20319a10042240c40f488c4686140c091464010b80101d07140390710901071440d80c0c0c401d128142c3c3c0c000c8a88010310700041717005602303518100b8040c1880a00881c0380540c0c0c100c501500500d0440203800c1910041c0c03a038420904032401c407801710802101102810701c28070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 441535656 1250 441534406 441534433
    0x14070302070e130f08040f05030309060f090121020304110607030906052a0c1504060e0405101203020f0c0d08030103060e160f1802030f061203040b070501021209 71
    0x90016020301000c0d092003a003c00d144140409a207540c3c1038014603010421201da141503c4294031500c103940e50240800c100260a01c0d0100684051100140805180003110940503c25a00c0200748505010000d0320b5001c41c00c0b5071a440311100a0126801a40ca082904041014104004c030062144ca41003281c03200103540401e10300101c0b580ca003441521f410441502c00c4151342000100402c203000030402032070254000584080d50b4038180c40c04604949182c15440c07151140e406030b50003040d13003a05081140d00301644800e44c01151a032800041686551400c804170403082016401a48005c0081c51440814861450b41982c212005a003406441d9602545030005100c00740c0103694441c50f00281c4002030200390920ad01c0200c492000a841d0007251404c5200344c051040000c400400c140f60f8a2054402c49009158155480c1e03030380c0c0c3d03442040002158841d08249400e000600c0001224102c150140c5019072013100096183c0d140701035042480c141c000c0c040c05281d4017005104824 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 441536906 1250 441535656 441535663
    0x21603021008090f150402150403051e07090e010c031a010e0d050a06060f17010b1f020a0b1017070b031611030f12151309060605060301080a0314070302 67
    0x404001d42001c0d145980c6480c3c1c1241405103000e00301c58280607010104602c3d140c07400b503c6102da4401c031444072440301c4500b00210240070b83c0c00014032035031010f0711501c0c1c003940c3e260900c9801d4801c1021154050340f203242000c252031445010003c9a916003c038083d165070075004140500458485e00740d1030031042030009001301c1d480303800c180c090700013443c0031024442c040c45030080c01900000300780102581c0e0194824039007030503c1420b451500b1460314654a91042c080c0e6003812400038004400030300304140301c0140d6884500b2840543c8180036150002400388524203204445c400488800c003032401851442c500441cac0f564a00b02d40000c0c9007840b04100755809e40b5040700417000c0100342e01c0820030058541c0c2d10304c40040c2145100103d51841c07500105030081105850101885049440300714030106080544843c0c1544450011003d05c030380c040e1544442d007154017520000c03801075030b00c401080940d0b100780c200012680241d40880285600042c1e68900c400c141d4158503d0030003070740c50007901c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 441538156 1250 441536906 441536929
    0x16141c020d020109030e04150e040b160201020a0c02130e06010e1603060305030414060d0f0f0c1d041a060d0e0706050403240f1407180506180d0f030203070302160302 73
    0x400c66954034001c456024010020010340343d51a5100c4040c14180bd080094010441b503640c251022a1083c1160500c1802076030ba003180c807500d9944050784241e0801c44025042c00032040c105540c1c0c091020b008034200300c044c2c02048400040221800c02c0c600c0d0100404003001c101040c582000d01c10030000b00000100c404403007003950208040038030350000941921901e410300d912282045070801488200c1d41c010000e0700c9000604109454032844e055400940c0d0740007040d8050b0b01c12609150318245600002c4000304480381d0804400b082500142507508000081c490440d42c420405815841c204210320181c805403c15074107091079650342003c1c05a5000c0043c1c40541c8030f0305012000300080c3c214075404002d4404c00e000709103aa10361000b00c90307012101c400006907542e95000d0000055180c1e48151000a40740c14500403d1110045241c00c2c5080c1c1c454000341641004404984151100b018051190340650b540300d04030304000b031510825517031050500d6446c4004200607a1450b10984 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 441539406 1250 441538156 441538159
    0x310060e1e19060302120105150411030a05090106090c090e0a02090303070321020d020c12180103240b030f06040b0109030228120302010509030c0316141c020d020109030e 75
    0x1004545082d0b5002400f5140d200a4022904e002c00600540040d04170902c0b92007401103214800380c480d01040103540214a17042d203006d1080000c00c070000b0a680040c0e5100d81ea0364004a1415912410320b4101e41e1070840c40c50004080034010b002c0c00001d099100e40000005c2015401d1400000000742c0703e100e1410b0083c280a89280c5c1c891019085c0d100d820080c03100c10004544030300280303c0b0600a584641c3d0151520302070f03d0340342c1c4801104801680d50305240303020034040301000540154018040914090a442174401500c440316000b07400c2c40d40944805030700c17a030b1241891400140ca40402406040c4100e0801d000d2201c5642d020450380b0407260125130034010400c100041d40c800172000b0034058030301c0c24847c4011856411035003c030940d89200354001c200980d50f101078141c49008004241c0306a810402900d001582203801c0d49052901035076035843d00c0d01c030040003a4540044140c5468031100c80c0480d0b806212303014803421114004600086c04100c2c120382e0000c160ba03120702c0f50507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441540656 1250 441539406 441539431
    0x81f0c081f030501060902041d1006230a050702030607080103020d0b070e0a030c050a14280e0a05040605010e091f021608030402040c050408060c180310060e1e 70
    0x440000101107003950046403c030000b0046162a00c0000029600602940d82c02d04440d841350a030001004428a2040f408041107002544c00c00ca01200e2808200200b00381c2c0090700c0540da0800890040245401082c9071182a0b55000b544141410280010209020b000c2c0236401000541c60b40c10f072454441d0741c442c0b9811303819526080c003038400b0012840704541060789804d01004000c0f00b04075040a0710000c99803130b8140c581c0c400f074000c5800c0941030000d400c4146204c28014118242102c42c0648012503100c81481e40c54040c400c03045030040311141c40140d01c802c00e02080c40030746c1c8a2103014000720070802c4990b107483d01b031440d52b41540c5801032180b0764841c1207280380302e45554150761115145a1803000c8100d62810900d5045d041039609912940c80c007045400d0782da00960448081740c6440010b002c0c40d945500741d400254010602013091914024400b114507074092040c0002e24450310000605641040300780100c1c100d005000a81041c0c54031100911840701c214029404030310303000f20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441541906 1250 441540656 441540691
    0x1240504030305070c15020c12030f180307150815040207050606010e031603140d080709060c06090209010b0c120a02072106051015030605010507030e01030e030301081f0c08 76
    0x40d1000d8020703034001b00911b01880400c108495001c03604221007442110f4034420346040d4401181c40c2d00c51522210840c0a0821407079001d1103c054106803407030341c000c1c00ea58045940e0850f450120b41030890100001d02c8090412544880180301400014801c1e10210300f4550a81c0d10b450b0366480c0500040d0502c0300207111214540d0b01000110038201210400848042e5a89405d0082052164115207107000313803e01c901f1024816a88184a0401030f42c1700300040c1d02e001000d5030303485284034082d035045440d0800040903884d0444054028045a00302a0303880401040850030000444c0320011401401c0110b0306042d40d000880c9400c2d034054410061201d08183e0a44074a10b109003401000c0a085c1020030903001400c400c18411180111f04c80411800840b804808468041c018240847d00038000d15010921031103003450444010304000a40814860019145401c01d901003001036102496031000f107084904e1001400ca8492420311803000f2100c005031811b0801018a4162118034a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441543156 1250 441541906 441541913
    0x1f091404200301062714010314070e070905040506030625031b0503060a06020606010f1d0d2a050d0206070201120c0e01080112150203070e06040b030124050403030507 73
    0x4001ca00d920000b0000c2048564a50701050012804100d160042520b01da4940d10a1814059045444080d4070b1040044c0c0c00c0d41c2e21610a248483c0366080c29209982000c10100055000749009070982c0c1c98084250380f40c901000152080201424000d403c01c000b400706c00c0101031954034403801c00e50711012803010f00c0c1c02c00310002c042030074003284040069010291420b801c50005e50040c1010740e9680e000d40d459a50580c1e869030f00f61100c50010707010981d6800c903039100b09625600c940e46502ea42250002160019201100c10602512510482680d540040310b695420000452000640c0403140b4030700380001d0b49181e003808002e030050800091410031a840756200719000d00d9903030741c108104c9000420040405141d09c3c00c490100e1403070030003c2001c030100300c0b07007042e069402800b1091103401242242c000e03400261000302405002d090500b030344d41e1140041d001420350f0f40c0f402d68884d80340c03840302103602c000c0d9184a803020480003418440158072408550550f505824410f50360f01030b528 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441544406 1250 441543156 441543203
    0xb1204140f030f1206010239090702010e01060504060305121819050102070e0c0304032109083403031503080f03070e19050d0206121f091404 62
    0x1002070854003001802035030300c010700000b0b44010301d181100c042c80c3e503407600e00591f03a6140202000109074074050007540c9a0901d2062013505c40c2c2807001c8114030202c140d000c200c02a800f40d03007010160b511010500c5580c0c009106501c000d1104442c00c2c4121407454945507190703003407010703904d16911001035410803130305542410000384280a820240e0000348108185039a0220f03001c2c40c0d006000b804400610203554400ca035019810510f030591954a0b66074065440480b0700e41c4110b4030000c8d03c1841d903225040c80c4241480c0501400302e82c0d03a039625a940c0c3c009840c40c0c400100881003010fa004182c484200c101c140c030b00950500b400243c40c03900c800f840700d05129070303400203200781800100c0c8486118174102a500a50342a1a6261409080410007516034540445070484d038424100400682c602100c10f080000c2c00a03001516208000d01550f000040803030306191b044416103483c20050540c445803100502403850700f0032000c141032141003500c0030301602c0a81480b0505080e403c0d01408030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441545656 1250 441544406 441544423
    0x30201031a10020703060507090b0412050703051609140720030708040b2d0d020a030f050a0603051509030301060305090f07061d181605040801060b090405010b120414 73
    0x50103025030010a001c004d58444890008031942c50801e00803420450003122084181c46000c4030181c180f1341841400b0b2500d000f007060584080c4510038001000c10402c1c02000d002d00602040444134600b0111030806403014010300c01e0001180c0000c0114003640a0580c058400b00d10704143ca46450b691500b6185005941010700701c03910003d40003070381c10001d000402c20040c2d583da52003030480812404c5414001c0564101e01c0501080103901106d251a600034426482241000903032599001500c1085440c2110401480c5a4440c010300c10320000b00324051103240544100152440c0001c0c0c03031900c034001031180c1420b0544803800b150220b042440f80c10f0582c0a141c0440e20b6065032407600a1141d011a1030528900c04e911000d4034040c02c05101d4142048110600d010320b0f80ca0f03043e0b2601400c154001020200702c0240b01c08241e1800a0045100422a042229031a00f640c4c004000440b84182d011a103100c60800480c0c001f140c1ca01c00071940a900640c6911018a40e00602418401c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441546762 1106 441545656 441545659
    0x181407110c042003130b0108060c0a0f170a0b01080a110702090402040b0a0e01060201050f040f030e040f2c030703080c0702040b040e011a0a0f030201031a 68
    0x150041e4101c489070000388510060306080c521020b40041d14007880c030240c07111a4005011b40d15422078050814040a0304090820031401d40180c400d0b403021105000ca52554660070307900500c00b240c9400c4660f04000c0013443d040811800924621025030301103091900429a01011840303403070414511050003d20388542502085a003c000801c120303031107910b4074200d110030b85a44407100020030422521026035418502d001c0c0c00d50794020705c0441a00072400030480400d1401c0030344900302c3c0d050f081c5801040540000702d0302070407441901c5e200705070914a9007618a581102d5150041c01201c600305915001a102c440c0c60f4410a4000340000b4281c1003c240501409001049581d200400029005100d031012405582c0e4036600741000d65503030345000001544138042c0c0108100f0850300f0300c06090600105c1d40003a100c6000103810199507075103181454103540ca400349040380 = true := by decide +kernel

theorem cover : BRFrame.Cov 441366906 441546762 := by
  have h0 := BRFrame.cov_init 441366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441366906 ≤ n) (h2 : n < 441546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
