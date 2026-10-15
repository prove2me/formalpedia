-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:03.413317+00:00
-- url     : https://prove2.me/submissions/de1ba43a-642b-4d66-818d-0d5eda38c25e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996762589 ≤ n < 996942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996763839 1250 996762589 996762593
    0x50d1202040b1210170a05060a0b01050a0c03031e1a040e0a02093403060501050702060a0c020120011a120c01081e011d130b0a0f09050706030e1e0c0d 66
    0x62144c0c02606090900ca038450b01c9071001d15075a03041e444400c44a82c0248030101341e00714101c0c090700707220304016120f49060400810040b03d00b0101108203408150b22180c0d1000148520492136a181c1c0400e80301003000001c5644010160049031401405186094002400000c0110310b1181c881e6044502c2403454943c0940840e82445444007885a005000c15901c081440032000c0c108800032074906100950b903600c0151203501403001c0103500060100310310700c42c40788a009044006031050610069920a00c0307207501013450903170000600c581d90307280e5102c0c0801401002444840040301c6200316185128592900c4000d80302c070060511a683c0c021504504510300c0d24240812000006280340d030b5195410000d42e00d00b059400c00354112040840c07118202c02110001694001c00042080e4448101c290000c044042481c02020794421140c400924203101d003c0052215541c00320360b1000700040c003424248500018118031444001c1c0b080e1024001c0b40b0880c801e8800c45061903601c540f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996765089 1250 996763839 996763861
    0xa05060d0b0a060f0207060f0e040518060a0608011503021f02030d1104030b090d0f120e01060f0303080106110703060c11030310031203060f140a05030a050d1202040b12 74
    0x200e400a603010103012800f08007150321030544407421442c1c4e03084980881da15001a2485252070000e5400603200c003944d040d40e03007480d4100c6500081d11850700e0320ba0b000c01c40d110b5414004c0a4900440083c0c03280c80c01c001800d000d002d0080464981c80320422018603603400144004101c0d41c1c601e4080741d0743c50000c00042d0090040d034181c0d920307500c0c05120304400304800031402e030300c5408112101060750300403900354480015206a1100c1d2902c8a01c80d05420b804c040d94080c0204400c02280c54444483c000c003c0d00030302408000700182c1e00300c54401825807030f000e0030488050300f061303040200240347e4099200d0000742c0401200c0d001280002c482240d010200e4050314509091f40c0c0911001007800b18410010f009401120b01884140c04000b801c8d4004400b540c405118604140c030000c0001e2140070a030303020302d8440c104020300c1107030700984c1c4101190500c42c0c0d041080d80c540d00f04001000a840d004029011005000f07a0110301c0c0c50704146801041e030203400d403140041600440085c84840e28 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996766339 1250 996765089 996765101
    0x3010315020f0f041509060203181903050703060b0114070b09030708071211030c0a1e05061807090b0109030602160501020d0b190608011502100507090519050a05060d 73
    0x1c0d0040342c80d60340341c19503c90681c5901611820007400014501c01c18054440e61440e41924441d60143d45004030a00000c51880f107442100c66225014010161140050640e010700452150010381549480c5007084d00c00c5a402c40e807032710705108800c44681095000300701290070080d841624083d00746c0f645aa80f61450242c0307040184a8480040d001041c080030074208940180148c0d100c120010004034103c0c1c5034080e0280c82c2c000c0307503c958440c00c00600030381c058403041c0820070040d082c0c0024544819242c03c105503128120b072601b0543c0d45680038001d200e004042c0c00d03203c9042c00701c4820a0002004418540300260403c4d902140480705459800040b0075619000b800a640700d0901c0042c4000504c030305c01c002c500c20f40d07810b10258620760419140c00100d5480d0344402c503450b0300e0034660780802c20301206d0140131401203034803813500f641080c45002d0045030582d0f0b40340714175030170700060024218451203209011412030800700b020780c1e61a060320050380c006643e010713100c00742c0000c10300140c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996767589 1250 996766339 996766357
    0x625050d050709080d0c0816020d08070c050907050903030d0b030f0d030b0a05180703021e03150a06020f07150207050301140f0612120702060d0c020606041b050301031502 75
    0x2080c0018841c0d80c0780d01144031420780304c059003034454410803028103441c3d54040c1c0c10700420a01050040740c1c0110704022400000d640041e00302000d00c95299140000b961144508803605a1001002d102b241414184240d1007080c90a11038036160080300026900d0140d6080c1c101901e403074651041280e1800c0c095a4980304541003119412141d03118080e01a11035814000c0c010060418005140c3c9000c0d40051440c0440f8035001c4c0481d01c03400c100f20080c1d40400410845002c4441880d4504000d1a00442c0320b0003544000040c41408d400401c004150140e00c01c03011548000584562000e02081c044210f85041c0d00b540d20715000420180d00f030840640c0410f0381940703003400d18250685814000742c458000d580204030135550b68001c1000f48481c003c0201c980760310142c240c040a882a00080002c01d0009080900b002c10200000041e181e14500410050304504140042070610b13001e2200310100f0040b1100101d031210303100410900051001510505a0b0b500f0304102c14060b03412103441803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996768839 1250 996767589 996767591
    0x310120b0402060a090e0a050f0924060102070e2809150b0a150302190311030703020f040306060b071b06140706140f07090609060503010909151d0105090625050d 71
    0x2c0fa00181010052100302c2c1e80c0300327030820460001400b085004c00c5032103c2c7c070003100d51040d8130b02ca024210302100300c009010710306500c00c0c4d00c1c0c08650b004101b588988a0140080042ca001e00c80743e1041446d00024840b80503030a041c12001000a25091560071320038907451b000240410840703001854064203680005841d04d001d4811155050f4503400800400c62607a03c2c035030f440400d01b0380890483c1c80c00030311290781d1081070010a118903c00c0d0001e12400c4580d000c020704040e240c1c0c442c8801c81d507040d8025024060009500420010071444d0609200c1440560f43d00840c41c04070041c0c088440404242e46003900050b0480800007154800360b0241c042050402c910b1904001c14000c907d016124400480c10025001418030321a02c10710b0103136001d40d0784007801c603480c0c00740c0c08010340b500605c02c58100c1c5200c0b03210301000c0442e1241c405400650322000b103c034191290407600b1120050003000030780d00b241c02084440724226a0078004a10101091640107100d0b0900f201c1d03602a00491050f55 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996770089 1250 996768839 996768841
    0x150c050304020f040209180a0e1204030201050f0d15090606171b0f070c0f08100204061b05011b09060e1206010323061f08010c02062206110310120b0402060a090e 71
    0x1001140d84440b00000b4007030101d0356100703580550ac0103240100c2c440240064401c1101c5082444510040c01c02480d203000040f40c40d00d42c1002000052880c2d40041c01815501e00301005440d40c40b1116140d5070106111042c0c0a040845812110341100c521a80c00d002c8006003880d204207008040712805070b04554626074864850101700315404d03051007460320364801d0004150800d040781c400c031400c0b10820388070001c811026804022010340d843d8000d840d29560f8050520508030740c0a0303c0c0102c1403c96550b09851400c10b040a0407900f640d4a100e170160840a401003d010f20016046041d0390300038034510035400740c0e9401850346540e1900340280a004000904c00407148504440003803e028400c00030065858101c074500f21940c0495032401a40160045180b800c0100180d201440d60034042c0c0342542c0a03629020305450080c0e44241e52440b00204111819940f004844040c21540401c500388035803649540141490140c0701a1084200040c08003001d03004000480c0208078951041c911 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996771339 1250 996770089 996770101
    0x705071e0f0b1b160509220515090f06040b1005030f0703060507050325020f1609140f070503060f04051608011e061416150c050304020f04020918 64
    0x1583c1c00c203185642041c0141c105a04000c040440c2604421007140c84503081e42c0e181c201080f01c0000b001d0300c0c00c3c002c1803030001d01282010004002100d407902420041c040300824200e82c03450f0340002000c0c1c036140d0b0001c1345c0010400d8000f0540030b80007608070184440035241c0080701624194194480da5140c403810070415540030300450100d08890040c1e40400c11903490200503121484222903141c03000f40c682c80d02c400aa440b000810100746c0052044038040100b00c400180740c1901400e10f1071640a00c40c4080200c0b581a000d00130034000240418005030500241084003403201400d0b80b814800c0110001e00540c99000000d41e1035540240288681c2c10500e03850403100050a03c3d40740040c0e07000c00041407480001c1c00303080c1035030012030100c1092071802d04103e4418000b01c001c2070b4440000c102d00e04194580000300e41c526801500c01c1261405010900c1040302ca0100328003060200500810002d07030355070b000802081c102a40c0c0941d0314820b180002e030480010816400d151040d007018010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996772589 1250 996771339 996771359
    0x109050a0501060f05150705010b0306182b08070c06180308090a05031602040902090c0c16081c0c060603030809101107020105090109032907050705071e0f 68
    0x30540118020030241c0c1d04e030050680c0707203140b901480380c02ca01061074085ca200d000700000c18440c3c1c0108000950709080c07100090a0039815158854284412a40ca480b00c010a00c04010452203803a51182a0840d040e60305c80d0030a41c10307403a507080c0000103000400349030049a1441605a00c00010040780f44d800802881e40c012000043d030000310403000003080000001a10419250000011418400f002401c030800c0a0414400c0785c001c1e440784004001626004242070040024003612a150b003c50503856181c801d00c00d01e44444c04d0801282040b0f41d8802288160300890038880c103100340d0088403c03d0b00c21061041740102143d01d012400418994060032150040e90322100350f41800e0b002c2d041c071406403a1110032803241100b082260100640c0600f004001c01b034810705202d580e4035a40c1d00c90780306020600313183c03030148800c001054148074a00c16070240d014100b0304140c7c1c207215050701c40550b11042402904415070140020207462128400048010020822801c0079252a085140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996773839 1250 996772589 996772603
    0x6181912030201021e0903070504110c1203090f150103080a0c080d05040c06090605090f0d0b0403020604030e2b150e0106141c121202030a050601090e10030305090f03010905 76
    0x21706050790020382d0540010112007201c4031640000d000384201410101000000c041d80c6002254504081114804c502e20501c001416503401c44821600c0703151090070300e400d1800d103920805407a000840c480c180300400e002d86505694201d582507442c2c8607401d0b803d5481b01d072111005800c4c03240100e004518445a90881441107208108503126555501c8068902503414000c480110300140400d00c000d0420000c82611b40780c005102e80f01c214001c6e11074629074002920305600580001007004185604802c280401c00426507040f41c6c0720401e061000c034540c0380403602107404162125480d0501c2070403508100048070801d001c0040c9056403d0843c001c012600c2102c0120304011081c0361185401d2076031400709251140f0b0910180640d030303940e03a1035104100148040c00040e0039030182500682c400355218a401110004003400d10350009041c0005a600c034030080400502001030340c80961a03060126541401c0207500c680404000810100144030b444d43c0641ca040c1948007809400140a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996775089 1250 996773839 996773857
    0x30506040314040f171204060206150603010308030403030510031e05010f200f040b030a1a04110a0e010c0b070c140c01050414030a0c0e150618191203020102 69
    0x400c02840b04000558015807041040b0502c108a0401c0384200d030b0361054903c145040140c816654401c810500203402039040f0b40d005a01410421240d00400907090310000b1b0300700c0c0c0550440d0315580d0f507180503110050000301019246c001088102400f03411300d85c0616800702d125941c007000e81d002000d107403000540c1926076600704220640c0706a2207100b8099010500e4880118040a040300b19600741e1181104a1062004220001c0c101540001940c061100081c01103182a411401240c180e001e14964134400c525150a90148260000c100d55a40c200c5092000710841054010303225884e02d804068482ea40305010412403650000da034140305445168442c92116060700841d03912030500d00d4060200e00100400d02c605441c803084071040c080024200d40b92000c95a4494236201207940c07000d50140030503410b21403a00ea00c0320340a54242e20a403541400e28030108a481c0324902c004d080540034000607240030400082040a0002078860a4402c1042c090340d458024000c7d8451100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996776339 1250 996775089 996775097
    0x1603020c0a32060609060d05060c130603020c0604150608060108010c020106150512190e100c0203120105090601030b0d0302061005010e061c0b0a1d011406160f0605010305060403 78
    0x10444003000a40d0b54a4a801254000341129030740d903000c0c4070044202920403070b48801c00114101c0060b404004481c8500102d10880e07464038104544200529541c2e000703801450b0041c00745c040305643c00030324560320680002100300802d20b0448114001d045c9600103400c01c0c0590b40021410706d40541000180c1c41c0c0179030081200b590750790300610a03c540c091540c40003c60070070402052002030030708d80e5040100e034001500281002c0800c0780c1101c14031011004240c003c80b08002c0160580d01c500310b0712007080e0000d50300e420700341c000c00004050140520b51107500ca88003c501a6482640840880c0101a0074040a05c21034140655a03c1084440d003540740220301010416502c41c1c84a440070310302c0944507034100035600300d1003c4044c9e001068040150350300c5030305110b680c1d41c256a4000506c2101c0a245c0d840e103000310300c0140d8100c1600103980b560600403001c0d00540f0b481044500b0084003074001009841c0034933042a0007145081c0151403541440004010300c80d0206541d40602e1090312 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996777589 1250 996776339 996776393
    0x50a08060108031206040b09180105010e070c1403070512040f050321030421170f0103030f110a020a1d07020f07120203070b0d02090109120206031603020c0a 69
    0x200580e40d04400d0180100b40c0d0000e1024403c1100c0312591aa00000000d1011590450345000f2600303d05086441742001803217440f0020104800307118040c00751042080c802d11500d4032400c0944078014810008240d54003a042d80382c0138090030720680c0d600541c07140640c5c034445d01070704100203650014080d429031855642c000183c10f15000603e40001e80d0f2480c4503c02c150260390120a42c2e4000505c1607460003003045140c0304100050840f441786032601d86400c0038051070b40075802040340004120302200b0601c40c00510201b908400c5507c84400b140c60300d030303620a40582c012414002d82c0c2d00004c0d0800e441e0003000c9818440d22086010b51141c0d180c0c000c1c500c0d52a80412a82c540c5440006071745138101c50000d20098116260f0824180c0c00542101c508940d2200310020755481103413803405c02540411041e60a690200f8484020403008031449103090a5400182141c44047e201c0c0b1688030381c0ba02c17071800da00e0280c2c052b81c46045103042555459486420240d014200c6202c180c420502540c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996778839 1250 996777589 996777599
    0x3071a06030d051c020c01020d111306140f07031e03021c0221060a12060207060c02030304080d0c0309020d0f060c031820060318060124120e1501050a 66
    0x2000e44498400002c540d0004c074506103e10b20081d40002446003c0d5502005641072404190160030031840c103c505540d50744014907000e103007800e059007240b020001e00300311040321b42c8400703000c2d282c2103c4041f03103956941919140a589600488681140e00c401e41c030f5180000c140c141e80036180c80640c005410040001a00b8480c08034406c0307401614030b10304c1200c0c18102551140600b06d50015001e800747c001544c8074003807505000d28000c01205c00ba60005681010043c15003e03052014909000031811420140c0d01c46421740070300842d440c903155030b90742d6040311a842500a107010780d4000c0e0090300d54903161b01308071042402c03940c0255422803c0500042c85907109124008046403100307140e014641d2295900c01100c00d541d0030b45025201402501e080350703982c010040d4020384a00440d0040381c02070740707981c80c00c00c0016408001541c440640e51810300c19400280c100f59001403528000242e1a088010010803c070010405644103c0942285821140ca10f0b28141c903021560202003680d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996780089 1250 996778839 996778847
    0x30a02101b030c03111303021c15020d060e01080a0b07140706480f270f0b0903070512070e1801090f020f01080603070b0c03071a06030d 60
    0x5480488550403034100501400d0b880381c0e0112160241030f107400b00b00c4e240358451801d502d81000805034080b80c2d1503041003003140307419013211704c141070494001082d8a05075280d0032a4810309001b4922200d8001421a91400560344828054a42d4842003040b81d6110034101d50b80700032481044074001c9100e4045181c50b40121200ca1014010aa449140ca41c550b9101005000350010b070b02c190340342243c6110304855214801d01544842e1041c0c6d078007608680c504117000f90241181c80018000208075010107258055181389600000c0140c8109100032108040e036100c507544d000c10b14141c44030502040031690f0314006e20341c1810440850714100c1d02c850401c080c94825524801c4a07900440e010040200405d0a8030b074041000c003603000d505000c0e20200ea01356400c40008850721041d823881c00d001c501e040e415000b0a0741003803a040c4064a440c50109944481c5400360719100e0303102082103081e01104000710740d041680445030307241c55410303144024200340d010b070f601038803a00402d28402b5180e882 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996781339 1250 996780089 996780101
    0x615030519141803040e1e011e0b03270102220510030513060f0c03180c0e0c0d18030212031911040509041212180b0c070b09030a0210 59
    0x180d0903251019480344942c0000145608140d4500c134042840002280c0d8a0302c6412881344070040c4132090f12140c01603ca4402c0001600007540306400501c0d6000300341c0610900d0000d031065130100039500c0e00e40002666070414a265412070f0099210800f80d5805019000b40c01c07002480610b89020341011f00c24004880000c0c0079003500111800001442c41d84a43c005681044c1101d103580d1202c030050721808151500c0d0f0401400d0180c458032038452480d0300d4450700050312100e01030000c59405a640f8031505503000e125036480407034401c02043c4004040d03412200c004251003000c20601040281309242000508011f80141c090866002c090b58408000c0341e10400503002c6d0070141c0c00600c0c11480c010812840c41380000e03030080c400410035807140c1945034050360040119030420015400700401b1541000c0b0b0103000f8908003e200440304480881340e0b0803003907010b807004007107660391800300f081d901504c600644440e10b00c4040c030a41681c080020480562540d080d540d90301d020384d282c8801c0c2d50b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996782589 1250 996781339 996781361
    0x61505061303200f06161e0b01060504060e0904020a05040623010f23040905012312030a14070605162a020603090114160909050105090c0d0615030519 66
    0x150300100c0c405850328100a00390b40c25001d0a1b810f079165140c90b54070740c000c900107090703812034121205201484031079400700d8014451481c11a10301800d10701c1c000d00d0a50001c4805004d0351f402070106046640c2c81c1070700005080090420003036a80e0301c03500610006100700307643d540d400e442c9400003251351046620041c0300c1c14548500c40a0301c8083d45035100441300c01b000440d0440305201c007241d1415039000e042c1c020320101c03100120b20080c0018420481d40208811480f8604202104001c80d0011040e506c2d1030300103041c40564820895014070300e0b03100390003006160358038110820140310038480100c44d00d00c401c1d0f034a040a102c80b981e00b0614400d10100b240481c01010003e04005140580017554054445c3c000031034450725040e1504160401500d00000030b120f0034009007200c960000300744cc001c0c600d070101032102e549450701043c403400d0080c112110341100010b01c06102c0741d1a41210b001051001301030f0b0b61065030050024020441610081c201000101c1510100e902d54052142164 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996783839 1250 996782589 996782599
    0x2505011103071e0501020409110a08100302220f02040305060f0114131e0f0605131b0c02011106010303091a092b02121e03030f0406150506130320 64
    0x5145210145240d255440c0300715805d41d000c100101d002402d034003d5207001510151500d07155441c0010260500030018418000307110388207820009640e64074403c041074042c08001c03052803400c45a021028000c200c2840c2061400003a001040000000c2c82502c1904e4076090224903903290580344c00048204520b060b4802c0c5205d076400080361a070317844614242c2401c82c5440c00c4600365140401a62400d0410303580c070542d43c0c02e08000d03506100081c07282c81c2c00302d003400f003141c20340c0c441c5a1900800340e80d88030b8041000d414004411a40240224840f1081e00800c989075580d50307240040c10f04001e40a00000740031000c00c1180701d84006001d4401c40f40c0c0c0105892803e008140c80000801e0184890703007120240d444d4144d0168590070304202e0362032403000280c50f07210108090f00e1122030070098001440e5000700100510071040540040e007099119901151690510080c4415101030340c0046600240c00603440c00700310003545215040b02d10968810329100003440d049420711740b0303040f205030f040303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996785089 1250 996783839 996783863
    0x1f0c0507030f0b39071a01090c02150f1b04030b060f06040b191404030b1f030203061914010b0307030b0f1302030c190206071107060509090702250501110307 69
    0x1940580c070600c92501a5141c600b410201e441e644441b54001c0081d0803411085401030180c50498081c440d02100d8a00040500707070618101001d41d800001d200604400807600815001d50311442c0d5264850440582180c489440342001115110266502803059400b468103c0e19414a0380603901220104081281003c0e0302002011007140d01c09081010403800d15003980c91000e5030005480554010340c412140c0f0f103024440380c0ca00c5030354140b020f8003503018810104016a8001036845d4050307042981c4403003111450480002a01d040110010308900820001c1201241040910f00c516000d80c0c040c8001c002500600480300c02c00710303076641c01c00720310301481d035000c40b0719001140c00c41210303110149091902c4510240261142c0c4003040143c1024042c0b1107500e91202c2034031090b29001c40a09150341c40c1400240640c840e1000050050f202003000800881c000d000c0e644502490340007240380403d00c40c0e550414640140140c5001c5a52840aa89219030010545140c1940f10703c0f49006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996786339 1250 996785089 996785161
    0x60f1c062415090e0615160c090203091e0a060c111005040510091401050f0708090f060406180b010b040603380310020d150e04021f0c0507030f0b 64
    0x130304100420701a080118030700b4084201141d080100701c8040034004940d000e14607413400014035074007075001c13840d0940107000344406188081480c13586010104900c9400250003403c0324144107140e04007501c1a4a0320031500120390b01b0401482d10280d51805483c0784000030610f1000325081900c000c0c12580c8040d25148001d00c09a00194403680030f41a9107a4801190240909549049414044010b0234505003c00c0c544c0141d2401e412003a040040c3c407603c0030031030000d50707600720080010301056111300000e0345414069079480c07200360b00300100369a150b17110120080749034010f200d00000285403407403d450003200c907280314003011005540882c4500f907103081110300300510005a40c1c10302880c90803914458842c0700410360303100c051401080310084141281032900c0c141d80a1500d483c000420040182d46603200d421440c030848020381a40007820104075421228075000500e1441005c5020051000d0550240d000034446d14036a8aa680c80710700200054809490000100882038660341c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996787589 1250 996786339 996786359
    0xa090e090c0d0c050f0a0303050f0304020a090e0c0918060103120314010e100f05010c0209091905010b030106050a0e010e040515070509031005060f1c06241509 70
    0x504511454210341044219000242401c0c0280342c0464440000c001d040006050960441a20300e40466040411510710f0b14043e000d486050700e42100703050000009021035980500700000350501c0a020002c02c1c005015075652000a200d07014804c000d03100005660340c0030607c09000010701d0201030050350f480c594448800d4a40303440c01d1424546c89500b000c60790546041000d00900d501414152141081102504c00d801941c018080840b5080300900940c1d8005906800d00307681038034080b0040e507030240d22504000d1060b420714064407110351450107111054120f5101c00004400030042199070300100000c02049100b89281c040312480104100d124031004158002d000d80b043d12414000b006949910420441d001400315401141c4901e8505042128102c006c140820400032801d019000078a480d441c0c1203402e204e03204040c130200c0040700790659500c03540d034022400e00281d1200550759403404a03258504502034414800010310350040c9040c954240c03515210004501d06080500d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996788839 1250 996787589 996787591
    0x31d0a120201080c071e1203050f0114030f07150e0616020d06020d090320060910230408031e06090403030b0409020d0602030a0b0301020702100f200102190201020a090e 74
    0x8104c1e400140400c00101d045003002c4440031100106000d031104907880c0280540c41080304403410146000100f000b136a28044009054859013030166100100650001e4074180c2d503165038840e0350140b01c00c00624095010000c007210041070300d40518050402c005c0c030010b4090754081c20039801d4011889409400e080c003101190a004003005494121468451806c0e00c601150480010301d214a070386540c000002081c07031080c000c00f40905800e08144240b1540c4000c40072181816aaa50740b0b40614154180c90304201000040000e10141c46d02d410300002c039820445141c2c85207031302d0702c0e44c0004070031a5001c014482c800042481c0e17004c2d103558070110014400104e1460700191343c1c0a90001507a80c4000d00b44050b80708202c0560303640b410b0103002080e241c1d83e040c0c05009130700611800c1d0040c0e44d28240d40000004a14101c1d59145c03c141c03088a4010341c6652541c414074295001703889101047d002072240080d2204003000304290214124200e102c0d01203034a0000b11001c0050201d18801e807226 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996790089 1250 996788839 996788851
    0xa0c1e0807170106020a11030102120f10031401020d110403080f0706020904092003070501051611120c0411030c0d0b040615050c0f030408150901020412031d0a12020108 74
    0x3128600c0c00b21150308445400c1c3c0100000da480000124200a142c0302454083c807410b400035418205101e1203000484000781640703041783d100c48001600c40592103074520040d07400c100d6802c250803912601c01c2c000c1d88a80f01d684000e070700304a032505442110404450840c2c1d8030034051072034503540c400c245065402590381120115020410000980d44900448144601039911010302501c6030b010b00c521000000403079406508144010049a0f0b0007100f96080422030541041c000405494400b4039403200804095100c0c02c0e025580303a20460004806504001c1981c0070050004081c4040c24103000c11514802c00240410401c071084640383c2001c91420800b82010546645030076040e0382c0d40c1ca0140041d00092808203a10031050400c11503a8a0341405401541c50141442e54564030380d09440c00c018100003da4001c03440d6074a003581241c0041688000c45050300d071103403071b0044c00880e040905140c00308900a07080d50b180f621610b042c044a9a420200130b8003a62680191010386004041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996791339 1250 996790089 996790097
    0x8180102041701020d06080f030a0e1908060a0e011802040f06030b0c090901050a03020d02310204080d0801150e041503050a151a1507050d080a0c1e0807 67
    0x400a9007000400310b2542d881e411200140c0c549054002031001c6a00992040881e90302c000700d00c1450400c007100300c41d0b00e0400340c03520018114810b07000c10706805a10341c00013002e080d0800e0000300200d01290450180d2a5071070207200124100c085c660136a085031080111a025003010318005107000d90150340d42d40202c01f80803e5103545c0340c81d4000d00c0801100c03110080e602c0010034001c3c510307089500b2405004100e80c0740914a0843e00424450202007070001c2c05130112034020f0044e20800041d24100c81c000315100503480da15a2580400381d0410b11841c08a84505200e080846008d03422460581c1c0d440c20b13401d0b840000240c400c99010301560526a0080e0b51285003000c103030030038400c00b00a140a50000c001842d8945400d60620040c44103102085103020454003c2d180440142000480304440070001d09032003004190451080c900d00030070354402d98050214198101103044d100e540b100d1010030826005240a40715440761074000182c183d811070030110068044c1d4102e90700a5544c3c94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996792589 1250 996791339 996791347
    0x3030f0e1c2909070e101a0408012c150a050a0209030f07032105120402060c033106020304090e030405101205010506070b06040f0e03040311030705090708180102 71
    0x14500d40c03a1410751100d81030004120082203c4580100900e0f401044811400e00041c6802c07400c00046400600940c141041c4100100b49660224400da40c040c0840100030003130801900d602d88248400840c1c9a41811354007029809164004940c1d8042c046903a082c0b0840340e6620580200141001040100c03001d50a015451054604100380350003c0c00e100020000141035080c91441399500c41202c40d14038004601414030700d42d001c801c0d80c1d441007940e9416242500c442c400076482d805241400916403102003640003055100c0040040c040008060316002100305003451000c079001800341d42d002d42e1007004204040c0800c1c1d4005040303003801c80c0a5a0070180c6540004031181130b0456a08002202015894004102032250900411040706c4c03840c40d101c9295503001441030010801480b89548094100e1608038980240d00d0700039000055950703541c1c403842c1001940741440c06442c0644911280868241004928a0f008400782e849030076050340c0740e80329860810310700c004405882d50244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996793839 1250 996792589 996792623
    0xf04020f150d091506080708030f07020d150f11040819061107050303010f1e1e0e1008010f020a0c14161413090b070309060b030d080103030f0e1c 64
    0x2c403d515803584100c0750000145440c105007016170700301d504110b2441d0400c0200300519600002281e5444050101580e1030381040e0000819490402902612003403030204011025112a84120340e0001d03240010010021b070001103481c1070041c4d0007003e0050340000007007504e10306c004111001031481460049000d02c0f0008946940380c0005000712080c1e4400700c010311001c1ca88280440140502c41906a03450810255408007480780344110009400414104400c80d000c1041e408040c0c1000c3c8071614680c2480f201c04000d05801d442448125481c140d00c144d4061002e0080700d124152aa0702c40c030f4031110548dc0d212007a1002105a0340d6403107603019040409500c030810340c006046414290b05c0c80341760030301030190100203001c074803800915080205002901c002c0c0d8039600903210303160001d850b4a040c6400c0c401446800c103c203a0520070030481c000a16031200c1031a0580b40310396540c003280006030b5010352340d2141d0365400e194051011007041c060f81400701c61607415240180d0960701c04070000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996795089 1250 996793839 996793841
    0x21f1d0609060a02241005060f09030d050d14040b0a05190c200616030e0a1a0a060f03110f010c06050a141303021c020102040510030b090f04020f150d 66
    0x3000c3c0910150304140b007100020140b5240c440c24100d051507080038945400101001d400e210b03401094410700c1c0200303010894010b41e505950000c0707009400c5a104504999001e09250466084030741110700b4a2035890611350000912406603030301421f01880da44801001c40301406000700b144c072110f44080c6a840000f0002d0140c00240f60060700c4a40c1d2948514686042c04080310062250320360100041c00034018031411901c540400500c2c000600043c040c1e940ca042c1480c0c1000506070900910114502c0d0381c01ca11014041c3c2c16040e82042226034070b201401e0440740300d11000c1c0100031403030220701c8241005200c070b034140081450f080409035020b40d80d40e4110f6505a4403001e40d15500c003440f008034044440c4150f00700c04011582110300d01c403540c2c003e40d1422204d04107110000386a0000c82164001d4040d1409003000414a0304401ca00301030040c010201c1c10b407054890b4600030007184c0c060b100301c3c164034003c0740c002c1e0031012403010341402d1018102d401c4c100e00403a6582000017003101001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996796339 1250 996795089 996795097
    0x151a040e1609050a050c0702010518010e1302030f01060c08070b1e04060902090117072d0e10240e01110d09030201120605012709020a0507021f1d060906 67
    0x401070b000512400e1058028040fa6002882c109001030100400b50141c0c0e0840d043e2081c6041900c0c0c4505090014001202c9541800202d0313600400158492440e864482d00514032441002c400c3d0b800a80c0d0b11001180e805540366005008a0004c102e414085007480c1e0046611000f040151400407030000142141a9800c40c1d01ba25215605c42c560320452800101d03541c010910562450742c00e41010032050b80761812840b070042c1149034000403251a03a815480c40b80c0b0840f0804402000a646203802c0560038000c07079003041c108000c4d0f900826504414070010111075042c2c3d00118001d0031888060350103400d0720342d07a030741400003032001c890619a0030030420401e4107041d40c82c1458949180f002411480900d50b0141001e8200082404142d80c040f040100000c410103112194601e03414440d606507202c0e8202002c114000500381070019041001010070903c2907840000041781e51000c01005009101c1c41c0000949043c00c07021421501c40c803441c00900010701c95441d0051540000e4640d40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996797589 1250 996796339 996796349
    0x20405090c0418111b0f0109110a0e040834080c010b01030204030506060603060607050106080d140307020606120f15040c0807080a0314090913151a040e16 68
    0x74041c80340d250000d10500007074a6083c1c041c06425244034008400d40140180404250702e01900b41300c02650800ca03072440e8403c00784c000c0100380c03020700303100b500d00c03600444d01406500007060000380c0e1004561030f40d1103143c1050380c180c00c0090b04102c000d43d0500d401540480c081440e01403035001040f6100f0500c00c035128142855543e9041c0c1d03001429140000c031500d041c0361062000300080b0f01e011644992040c000c0311290340c0c0340e40390b80000340315015004028240d503117408008640b14800090b03c0140c41016141c146042c8540c00e00103060380310850b803080040c0c10141c0410224101080c00c1000661036009807014525094407082c43c1c82c4061b5144480011010240406d0080402c001c038003a00d440c0000c3e01d485800c00e000d150b038400580b00001d0810543c1c0b40c2d40300382509944141c50705900000c05030307980350500200030800084000400d8a07c03400740303140420505c070140300381041c510444240042111441d01004010a40c002c00c0f2070b030780e010700d441111249038400c4440f00584 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996798839 1250 996797589 996797611
    0x7060509040c091d07020105070c0519051501090c12050c090907090b0d021b070602030307051312080c0c09243c0a120b060a08030406022a010503061302040509 70
    0x125000c2c5c0000d00352403025008100384040c10341084041100030412902d215112440030700056014a0031b0f9161202c0c10600a01c0088203100125001034581c2000c260f0484c140c0c1c90300102c1c03d24110790b400710799050380d8403021000b08006180950811200150b8884c449040002c2080d5581c800003481b0780c40042c041c0c991550000d40541c6600e040c03500c54020240101c000c0031500d041210195480c8006890201404008541054803000c1884804060110000d501d010405186082c40c1590450095040d180c012418540d415043c61690203102d60510f911000c00702d9903d01024401c2c2c40342d441802c0e0045020340180080300c4c0d00749064008500c0c2c0a000c0308072804400520707511642d611007441e2140300d01a40810108100c0f201c40164603810088540d00340c0c941070002024043c4030360000703180d401b0100d030014016030007040c105688103d048100d600c40310f010160358010480201120701284080c00880d00b1030334070040421080340c50302c0006282680384c0c8001021040111640c00c840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996800089 1250 996798839 996798841
    0x3090203160f080c0d150b060d05090d18050d0302030c060405060f09070e010611010207060905031e0408030a030e0a0506090a120f1e0302120f1807060509040c091d 72
    0x3440030030b0340c4040286000c0c4054001010301038001007134207824000c003806d01c8595030100b90030b1341c80d903510a0020140c000d00c80f6940354000c0000d00094003003111150424026011903051140c010300c80b41e085006203895808540d820407040101d002081c040070390441c4400e002c640c0140c441017003024000c034003070b4000304910325141c05803c00c0120b0051002069400c0360074204075551040d00c01d80d05407050381c141603245840c2c001c0720500900440e00e02401071030410900d0f105011000c0010007000c100a483c02505401e4281900d8843c40303240700e05060743e07208000c00b69001d4480d5100d20f4000c0300c41c200350780d0003410640f1203a1400ca0140c6e4041141d80181d0080c41c00c2241c42c4100d135040c0301090070044906440b154014061700c0c00e01c00c2c5103450400d03002702e9250191280d070440345070218001001d1034a0a14035a4032202090451700030301c040f084044103442060002855400300e650aa41e040d00c0d00b0b1031001400003402c020300521060002c8072102103410302d10484501240c1c40409240c500c1c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996801339 1250 996800089 996800099
    0x30c03090f060207210e04050402060d1409010501090603030509040207060b030304080102030703140f070c031119110406030503030a02090a12050a02011e0e3a0506090105071b030309020316 83
    0x40100d141d241000c0310038400301c8140800360040d401e070b40c86c17080c02c0340c0001c0e29035181c0c000f01d4554819000100c0c0d81a25000000540030341e1810024041c200e118000c002503a00c411186040300d00600020340462000d0000b00c4d110b15103038000300201803140380301140004014003c6440d6412540101070380c1c0e5000300420070481d60510800100c0d8411105654032030804840201501d00080d020a0400c1809445601030601602e0310051038850740b000c0b25003030070b0072081030700310002d00c1c000840302030300504c26103603503072415029090589401c07602551658441c0490003000754044a006c5030810b81e0900300040322916038406d00852401280a03101c1340103544001055030007034221140e03245142715141c00031203034021440c08804805072480c880c0011a080c1501c0c4041801c010280780d1750740301c0c0003020311402000c04211401d00c5101110340c50b4481840301804d84408603000e400141c1e01401c0c2d070030190750401180641500030b040014075203685030082411b0510070101044855001401082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996802589 1250 996801339 996801353
    0x3060c080a0f0b0d0206031f1d09030a021c030915021b1b040e0c04182618010e090f090c24030402030715020a030f02030c0d030c03090f060207 63
    0x10481e16001020043e007070461001640c03c0c44201c40281c014131011000494030071f182000c2c010803050310b010039010381c0c1c2e841d1080c96003a404020708113501c0c0150804103c1036a0000240d8050340916005403202c004400708061041c00d92907900001c045e12108a80c011480b03e0a8078000b5191000000d69039086021503101038001741000b021450340928201120754400c643d00c40011032044030017154148881064900e011030060540d40d11519083c54440d15070b00d12554521a2803240344800f95544c501841e814148010708036081400800f0000243d204404e40c807210440304050411100601883d0086070100390704840440e44041d4a006000750071004102500710b05400719800c4501d90301444404903007841c031101403e6444e5000c0041011550300b0700c0020301409080c0c1100a41480d4040000d40d20b008440042d004503c41c600f41c90019440030003128040c6140e140100f05600d03042100720002c0401035500800c02d030341e0707182d40000140c20850610f20680580000350b168040c50030190 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996803839 1250 996802589 996802601
    0x5030306100c020f13091e03141207050d020c0d020a031e050702150405090915060a0302030c100203190c0b0c0406140304060914060a0b01080910110403060c080a 71
    0x80510050340700c84001079071107000c082e110f90b20968144e030b180265250008090700000c08000d040261805194070240030800e60803031f09500070f40c0c83d614030030342a800341c045504ca80e14000075510302c280000b1b03c4c158000c4004100500d141c810051414201c04821801c15107125011780040e00410701800906078848402c0764010300c480315076890540080c0019085103e504c070000c1c01405001c03d800c0c0103035590b40c2030700c00500c80603003e20301d43c6c6405080c2940300e000406141d80c140c0030314400301c0c005003001c0041030103176540a002400800c0c080d000304a5010090b6240408521040010503010103a40d003c0c402606581d44030918810000e161240ca00a001007142c460700784144410440603903c0803d00305111165600143d5945403810003501802d01c2e032401a102680c413055005a2a9000507140e00c512000e05040003820124001180c0c511001e940d42d902c0341d804a449220f004201da400668800510714520745401d59990318201602e4998280c40b002c14507040070828a6103543c0114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996805089 1250 996803839 996803869
    0x7120815012619090b070909090209220210050c060c0903032506090b010e1b03060609120a030201021207030506010207350f10090c06030509031605030306 68
    0x10000c140d0007140040d0507034400c100701d41c44110724041074080c60b40c0f110349010031481850a00140390107081607043d00c41c0c192008000103156100005952100e0b1041618080d07000300168816105e001d20540302014600103060402d507040b40b50001030f610f031803501c1c1102e15030b40c50b03440d100c110400003141051402410580c04180400c0000f40c5940e01004480c850010320056801000d074400003455081030f9503100402e0302c0c1c540300c90030081c000302031400e038104c440740d0701c07200c0c203d90b980c80200001580e44103a01540b4201440400d8191600b240603003c242000380100414022202c6254070b0030560840680160758002030f5804d8410611040d1a4001000d040c144000d08100e030000359100e086104170903410400000c886140b03010912040061505100d08881c501c0d032007a54581c450007406000e0700783c0e20803420b4040100080380a2281581d80080070150005d00e005c031b00b0f0f4003401c0d00a0072200303603010400074040c1c811000c00103402e20600880007561245841014400c88540520038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996806339 1250 996805089 996805097
    0x1020307030e1c050c0f1f0c080706060b0301140d020a0b0903010b1c02120a050606061c020712021612141c0906030b01090b0703030c092309060111060a0209060712081501 75
    0x1f40c1e54900003010034103803150300914061004902c1401c0807d002d01501c04002d085500740000001c600340305001442c1a28605000e05600c00c07681b008102e8129900f010007500b00040107410004101180c000c2c02a1240240000c070b0001e803c4400100c590300001c8400d80515181c00c250419400d0904143e915425100c0041118039550f07150140c0e554801030055220f800d00007a1072032810f075904003c0424124000040d503d404982c60712080c000c1c071160f02000184900309003441c55012840c3c1da86e04a0750480c000000b00784450b00c032504c0480350750401d07100c50700ca142807444003820140f0f260301003200281d860074025410039100600391013002d411a41001026074003884112023800031580416454107001620300380084081d074440003180d006421180c1c10300d0f0380820759007504104081e40c00302207403030316443e544030401580d0111400522003002d40c041000140e90544580c000c0101c1440101002e0038000d281d40c0302c614049840c80154005034015040c40141307070007048032451000003428 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996807589 1250 996806339 996806359
    0xb04230a06050621151e0907020303281413140102040b03070309020f0306010909060e03070f140a021e090f060619120c020705100e01020307030e1c050c0f 68
    0x190901542e00c4864008030248000000314010924100340303042c0c03110018200241b00403140c880300d0b490700000c1011501030f0b03218000040038a840841100e03c07035204011f085e1108600b401101c8031240c24404462110703643c4001c1102003030f804441c42d0b44619130102c0c90203640c0d00ca500e0803001200e0b03020a8909207a0041c88103010440c1a101543e07408840e03407600094100090000500111100d40400d406014110001c01d8081240e01700719030a6020300e00c1403018282051109951348500207028140d45030030714040700021214521012521200030403200e00c1e092a0300022810036418a0b40504111140c04a03c20b9040030544190700410340400040d05240c41d0011845a10905001600010310000700b500a01c1c0a08422181d920710628100040411208069076604441c0a1148101c4c50100e03031766210361040d0f400146c06441030303010318188001c9a80070341d510002c007010b070f590040e9440f01c49080b620405420782c895500800007012460303c2c2105011081aa03001c00d40d004020800f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996808839 1250 996807589 996807607
    0x250f090c0f180509280b0a08190b09120a0f0e0d0308063303090606060a050418060b0c0d03050106090803030c030403140301090504030806220b04230a060506 69
    0x210103204031802640d10b50015915007040540004211101050207407000c103072005614043d501c000c440c028147d13060041a91110717905917941200325905240704944011600c00031300c6000c41c83d41c002c05104101c8000850b1581c05c00002e4203c0200900011a00d008013000b07943e210307800542c13425007502c0d8200b01d8441614010f0500100070480c1e406442d040070040b00551400d45111202d481115042c1407800700c0034001666075200f40e8021040c1e1040001040382464080c044400302007003500c1e650314191400100080c02ca00e0f03043c0d01605540c0e0b03860001403c0c0040c00091550b015004080d041319269900b01074120342040c0c0190040241c0c0c1d07041404950000402c486d000300001551741d8581d600c514041782c101c070f8079041d0300110501c003000000c0c100802e60080307401a403198449000716078684041c81910140e04002d4103010043c00300300100000c40e030384100d0040b000948085204040240c02d9000400c03240d0f03682074000641000c100c4034410741d1003604c01400b030440e0346a14112081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996810089 1250 996808839 996808877
    0x28052208031b0c030a230c090a0911090c0a030c0e0a0608040203160e01060e0907080103060b030a29150a0b0a051e041404090302250f090c0f 62
    0x7400003000302c080501440c042058042002406282c4010219000c44411746499500280500060318440a121136000e01c0c0207000b16100c001414013821036202c3c0e0f5030b14112400985840d40040d01d0782076168001c0c840c2030319481541c0d88a08029600a5503800c0250b20050850726000009010401120127040d4103540d110501d40c122101441c21091584590001900701503056402e0201c0d54103117200090000000385da403504840c001d4032a40c80250b8480c060020400d400c90311400001c098500620010303040340d1081c1c0c0e0140b405000c454688079242d850050214070105c6240350103103203202e00c2400410a426040e0300200561030040c505242e4008201190118020302108036004190744c0c440c140700d00160384042c151400180141c24600d80c20700402d910500a4000103031101c2600411801c060007100d09240e80b41c0d0082c1007004d960038920380040c04d02001854400202e81b0b000a5003014920540b000d042c0d1088002054010054040c0c18010000b000d00c082c8500d04001c60791082d10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996811339 1250 996810089 996810097
    0x207090f0b090a0903121401150203090301050f0a200a1b05030f12130b060f0409061407020d0906050909070302070204051306050606130302062805220803 68
    0x1851401103800c03840d20608038040c0c0306210515400010140402041049540000f40114001c1d141c0c0c3e010341c1100746035102952070000c440028000c07030710300401100b0704403408064154424410fa030704280480340024292201620785480c07140043d802c1c070070500b45922a00d52081d5035140a410311001015406480e401039040c20740a2060110481018081c11a00548010b9210702540d554408800c440d12151b0004030040f640307400c1540004c7c01c1c101c410005c21140300d80208680b9810740d546810400740e50301d000034058010703858001200000e1820300906021444402c40300380c0c40d141843d0020b18001007064007408010040c3c404022142d0040f040380c4003800181c0341d6038519034a0803020380203481001e500940291038041040a89511004002204c030300c1002c09202544883c810841140198102040c802d07a035a00708000601d00100200503010140c4162514602c81c0c4641042141e46108060085000065142d5400c0c0300f51890016805030040c44c0d2208605100360140e503030003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996812589 1250 996811339 996811349
    0x50d0f0f02010c1406010e100302011b06060f09050906150a0303030b01090314010507020d02071a071a092803080f040f060e0f1002030412050318060106030902090708070207 76
    0x8400c24002040d64414642600c001d0342101d144940d8075441d9041a139910b07401d220f03001d621041107012980700c818490515080300d805943e410040b03540165034a116040110048451030f6842800181144080d8460002070407080c0002441e40781c1140040d00b840b0f00184507440e0505078081e801a981c1e82c50716000c082d00c0e014a000101e0390481401643c07050491340000e0441e01e6031402246500c07105420030343c49841b40f40d00b40c0c0c060020b58001030740d83d407803680100c40039403088485041c0041c04141c084c4c112103008401d10701c184203002c03182c000c200c5426a50324190350002c007014410031a000003411454840e0756401080141c054400034468400076002c044c0030b013019408181031082d40e0342003450480e0491001c10400018045207070b03132502c40c0c0500400c00d02600802c1d081c00d0655100b500c1c481c2c1d410220b51112140210f200306c4d034030f0340002c1c452516409400da001001c0c8108101840c01b80100b40c4001481c2c0450b1f004001c002c0400404480400c1007000401c01e9155012600d041110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996813839 1250 996812589 996812603
    0x50a0b0c030403080d020a02010e0c0136030c150e210c032a0103060b221a0307030b0d03020a080c010e0a080a110303010e06060904021603080103020406050d0f 70
    0x4040c444505045104592020340700c10f0000c41d012003411a16802403482c0d1520f40c0003000304843e40a1041d8a45c2496010b55000c582c00c2610b494000b1000c25141c0b44195002540b16102c0c0c0c2443d940c001086110b80050305c00c024040810b0150010803160340300700304001e040440120042c0c800094080380350310501c200c0c410b60308400c01e2484804001110001038010b0640f0004030703444405011802020341da000c0416108032001042d54042c5c8640415280914808e038501805482c4c02040711300c0585440300340d01001e032000035103604039a271074404100000c03110541da424031407001805d40324080e80041c42074580107c8000020b40000b800c0c250a94041c8009031507a48103c0c003e4010300c0702c10200803032030040141a40c104202400109a56038181d15405d80340c0c100139011590b41e000034040c1c480d028000202084041c5008000707070101160007040549452040d0402050f01d00000344106c010510042c010700c2185058050300b00a070406894108103c3d01c0c0361601003100100181c081c0c605 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996815089 1250 996813839 996813847
    0x91202010c06091a0403030507050c0a0204241410111f020405030111120708041e0611271e010507050c1206041208130210031413060b0901050a0b 64
    0x10945030010f00c043c581001a901c203003201d0781d0209003d02e00480e0200c00091405000525160090061721b0704004440014619212107900b840000e100c20700072070703480c0b40e412480308542c4c0d858995072101810316500d5800402c0b070140140716a40003860542d40512400c103a0a01d160000018a0051112550004020420600d4510300240301d190042600b42d4248400707140f5154042e0010001070380d00030881880d43c0d6074080125070012082d200282035088640010410500b468101c52900d4014400050051107000c0c010303440703a00503d0b8030303c4158029138142058404c000c45a200c0c1d850141c8400c1441c24003070460099005155002c0d40c14008086101c4003400000c0041c036840c12400350030f000031202d0740d0101d242d803440121070868441c20348040c6800b0003481409018001c50b000040600803a0a5500b046403240d1440042400c26a5074601038100d2095500f00500034080c2020b41083c020032410b016040d80c140080c000e003d01188001002580c8508841d50200c0302100521920307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996816339 1250 996815089 996815093
    0x915090415090902180c0f0a0513030b070809010606080c0c0705060430150506030f0604110a0905060f01141201030c0509011d0a050a06080a140607091202010c 70
    0x3003000714898000380d54600e2001c14804425032069008500071110000d26030a40d0081d40f84c4130004840020003680140701d41c140c050389001c083c000c0a0340300d00700700781400c103044500c0d1600c00c25684280c0708940310f034040c0403560ba004240903801a0b40c0c80003c2c040d1030708285028002c040c020f400981d00041c0000c401400034010301c01000035110040c035031981d0715500c1c066582c8114080b00964074072a12403c0d1452010351052840948540c0450041400405586a4402082e00520042c1c0502666034000104a803d00c00140305e94800d80c08a03040750185000e116419802ea04079075610b52a220610032196215000410540002d01e03089070180806d0482c400540580d12401600b40007010001c801c0007004040034095800907200342c5002ea0f6184090348e0303102c40c00e150411074100f540000c03e11200890b04000ea02400c140c078041001075445c64600d103001c2c2001e90036141845200001000c501e000d22500b80c0040e164a06060300e6410650f03140300501207810000d060ac15103e4407601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996817589 1250 996816339 996816341
    0x7080709050904060209010f051207030b010309060c2c0a0e0402120708101a0f04090c050d0308100602010603031e1403010314301e0c070305060c09150904 68
    0x20181030003400c4840c06080134076110002c3d411010400713021549070310020136414400c3c400d4540c0c1d138401060350708061300c0d406029001842001c0c003403810151160902004120b55020b6420140c1003960745410b0941713602c001e4a0000405c000a5000ca49403c6010036260f450151000582d172078a246034419850394400038101403110300c4180ca03203008407100051555004104120b500032216810701c00d1034000380038920300401450075640d014280c044654035a08140d48029241c2d40300e000d40840c0030b80c031240040c503030090008017200001c014000304010790320520310660041c0341d01c0c0001e1000906540e40503050141640c1c01c03641031141d410201914030301ca02d8a04483c00aa074035450341c2d03544c60f401c2c482c5228101e5031440d0003901c0b42003031071000002d24041c0448000e4000309c040c010004182c1004003541d000785c14044054690700c0e401400d41c41010024039070744420030022700803949145001810044024020466175805000e0a12203468a01c0500070031402546100d23074540c40d60001030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996818839 1250 996817589 996817607
    0x1050f090a1d071706010b03011811030c07020111010501050d0b0c120106050c010c08090706050c070504020a050705120316081e01030b01090b0d0206040302061c0510061d09070807 79
    0x1100b054109480455500104140781a039043c0c000b200d40325684044850790300d12003840740840701032003007004218100c013001c00e4129504c0c83d03600109803800407030903940c02c5410981d18980311020005181d411980c200b440c9007100d119200003805558500700c005a25a5001c1c08044c01070242103000071000601c1c1c0040302e214a02600507203941d5610b41c00014266000803a00a11561070308a00c242c610340250610f511850304200200100c9003020012141e82e00600584e4245100d9090003007000c0d611800608a03ca0f41f07942d9180c1c0362002c42c10000d140128030314039401144d104000f444103060405e920b00441d10030078200107000d926010002c1c0050410b0b8600e61031444546000441086070b2184200c0c100c4400903010b03c0302000e04c0003000108042944001d6200008104c01c000504004015149401c41c2009070420701c00e51441b108240c9000300e8403440540c0001e00b0070300a0581010b44940d960256102d18100c403007482002c14542d0101074205010300100400095050384074000c44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996820089 1250 996818839 996818861
    0xb030615070501020d14060a060f020f0712020f1008060934031a0913110a0603060e0a1a150f0a0903021f02061503100207050307150501050f090a 64
    0x22a901d6000341000e60007034108140c440c1d4618100b1303d0801d03403500b40101141c015140280703240e008030303c1d1150aa844410441d00b0701c003580528a135001c0102c809006260040011104440d0022264410000020134030303002d251140366591010307510746030b10420441d0320842c01c0e10070301400c0c2c172483c000540e503040301c424090010b01e20480583c5401d10381e040781710020704c0981701400712f40c2110740c0e003d00e10344420150396000640c0c4000a10040c10708000740048030f01421050552251500115104005a0f0424030129460307150030401d000206c1c0304c4591141d5168002c2184410240d110325800b1913a984062207014101c6030045520361020032030302c11010b0100e21581d1070b10000070140011080740300a0340302c1c0c03100822005d2182440c2e44403285124041d40981000e41d5800d21049a2152410700103415101d080718464840790244014048135000320000c41e1079041519001042000240101c1081340c10000104000c0c2c071514500b91059004440c14011561410148001400c442da02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 996821339 1250 996820089 996820129
    0x3060317070605060604140103090c031a010e090c090619080d090515030714030a150e0411030a02130b030c041103180d231c0510120c0b0306 62
    0x40c2403094898000034520503200c1d01d0248003555940c0308021301406184110050000ca52200408541c441c0c0c0c421032026100d40700a00c011520703500d82e0210150011030343c0c0fa401e40002c2c01480508541e801203944040c00c180107110007110400491190f40c0090040b5005103055001d81d0710301c3d0444000700028140a4044801031002d011005102c2c035124880c05000c0e2200034480300c000c2da20310044034854180c545488601011980d030368089644002c142c80c0b43d8a40d901c46020020f52800c12002c01408000c4811601d42010306006d4540001980e61900c658071041a80700142c44d68450b11610007a40e040020303580c044c05020908280c070020000c0e41c03107440d001d6021032882c0408051801154500c1c0341880000d4003800342c0f41d17607070001005031000c62084a21030101c20607405544410340f4190b0070090422400c0107401c00b81030320f800200038032591070304100801d01d01468640c40040090050a50380101c061302c03280b0607802c8a006d515185800000002c440b40c5a000500076441a5408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 996822589 1250 996821339 996821363
    0x13030f0210290418020607050a06020a0e01110a050706110f12130803070804180603080c0d0e030a0308011a19090303020c010c0209060f0f12070f09021c0b01030603 72
    0x201d180c1120110302e0400d00e11001e0782c0d44919041c90700c1003040f500c1c0789102075201010103400704080ca81029808540500c540c00c00800040e0140c005002100c0d00b54403040105507502c0000340c641603901c0a030000ca544000d01c184080b48000031680100c80041c10b140300c0c40107440c843c860404410441d200549c0c032840b00f00d216403402c400002d1101401c003408103800c40341c03500300341a1240715000c80501342910500007844903510701e401c905204c4004080008180d071b9a503680c0b4026800841c150041500720104540c080c031b4010608412002d030481c050800900655000b42800c3e606000d8420162071410140194002d03070004c0785c040310901401d0700030798042e0b000b0090141e07009000840050094004061040d40900034100c103160380200a404940e44034400e1000000c9d030103001980c8501d0440c0311606584a15040c0c00325200100080c0065605000040d0b040820690000415510401c040032400c01d5810081e00c54501d5640046000e44174000101d001e40580d41025114543d411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 996823839 1250 996822589 996822611
    0x20301150b030f07091a160c060818060705270d1202070605130512101a010e0d02030312091c050307081803031f0b2a0613030f0210 58
    0x1070091803040c4051a1009500d94a6080490303150b1001d224a9102040c0f190030340b84040299006804540501101480030a01c5a00c0c1c03074601c1002c50f4051004035859406104200004100032510408003100424143c10070002c010494418a2000c001030a096600300d0401d006a044d2240151001403000c54042000e0a00c400014030f840c1e14100584134110700065800e0048040e074102c0141c3c0014201440c1c502410302070700c904041c1c801d403498040c4000300d40f0640a2885081040c40d13000760314404100101c0c00241c0b6070348106400c24401e0581e805802c00683d800000c0759039202e44541c8045507074803a0082a407a00a100300300c1c1002011803000c4442069018018502c100c509580d145159140e40d00300e41c000e0603118040e8032994108100040440c5000c14070300040c9c00c02c2c900d54958541d915005012140c001d089101c801c01ca242c2d80d042302d40006405c9904030f184240e00580a61304000200c0011113105072001400e02c00c1c0d929001d01c8072402071009010341c1c80400018441c085440e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 996825089 1250 996823839 996823859
    0x1209080f18010f0804050a12021c03150b04030b04171c0c0e06070c030314091f1403161409060d1d0f15040c0b070c180c05070f02030115 60
    0x701003107a002030020b802a003069407040501c07500a1b80c04c8000741c040c00049403103120216200701d4901041d4843c02c9143c41d03905050b070001d5903178201c469034001030410000c80700c400d01c2d803803e80c07011542203024402030004c62100c0404540255001d460f610381c04100d5600300eaa1401645211515000024001ea01d2001c1c01e40040074a94195074a40040070052410000c0301e0288003800b8000c007210038414000070340520f161400c03050740b500d1800d04220141000481215007500045640450405941201500074051b070101781500ca40007825803400d000300f940c07809a46101d0000f0082c00c0000c1c0101d00900004440000401074442961031403117243c480003522480c4503851103440900403c0701030800108079140c0f041201c01c060101d0300380c007035a1082c4296006c0c00c1a90b003401d0008001404c1e150740c1004005a038810400a800c40c3c1ca07010740384507036005442210511900701303107245500a500c04100c818555221103000e4405c1e030707540003090040c03500c00034046940d104011302284401003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 996826339 1250 996825089 996825127
    0x20a09030c0b0c060709030f02100e0319051005010315020a030908070b0603060a0c0e12150702100614010801050d1113020403170a09061b06050c0406030b0d02011209080f 75
    0x1030000ca4601d40c84050088600071040c1c8805014107507a080c0399401440c1100e030030f031100c1c102b17841e00c9662415002c000070b0416803404440340070340014500c850100700b0184000c07070070300d050170350708000d1589551a802c3e1a1030314014000f034440e900141d5505418040d0303114030300d41500002c58a0b100c0e1950301c0c10365021181903410500c00d02c60000002c650b004103002c2c0041003031182e40ca100c8900400400e1040d00800340310300e08060701034604084210388401002e24461412940144482d8484100900441d4291340101803103094000c1d0f4030f11142d0300715001c14115201550207042002c81030a0030041000a42405580801603480d56a120140c5030090300589006041c42c4d070078003001d201004514032a03902e092020401c908403c00140f4012680016003020322440e00c1030755120b581c2d41c901100e1003281c9000810101260034007016034140700703c425a105c117403203143d40141e694001a200a5461070042505500c5d100400f00300001c280a4400c43c0040400e1903403500c0d907800d10b820b15601c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 996827589 1250 996826339 996826357
    0x60a090f060c20150c030909150a14100e060d0906020a18030f060c1806020105152403071709071406042111100f0207091e020a09030c0b 60
    0x1840442c0404403c880144801c3c00c1e1800070070351480010900e0384010346030090398146000340010f0110b42215110b0b846060708c07813404a191080703030016980412914440c1038004801d004400e0b11102c0c4d142d00d540c0002c05805103541002c20500440d48001003082c0f044559141d179041c1030200300c508000654000c1d02d010405500c0d0590301c181140141c00d080340d91444060b0640c0800558500490b1090380304a051342075610b03084075441c4402c10703074506500b503941c08400140c2d5034a0803c90181802c007400c0c64800030071500780c00d0029400d40c14131407803491300034020480780d000030104555601481c0040444011008240c403589411a10300b81c540c0440c2c82450082814400302d4071a510340b0f5000c440507180800c81a240500c0100171441e59031040002c210382d0005020082496591000c07a030b014502190b43d6040441051100b00a003000310590011070b4007400c0c016050805810003842a4991806020040e210082030034111000c80c910307030010382080045c2c00c010a900030341d4001008014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 996828839 1250 996827589 996827603
    0x7060e01030e12030402010306030c03080a03110307021e0330060409120c0314030405010c0e0906150708040e01060f110c0a0608091513030306080a020f060a090f060c 73
    0x411404010750903950726481001498000c0c56298641882c40006103030401d0042c5000030700301e0f880303a84000e0502d486820640300d00c00040740c154100ba62500a02c000c0402e502c003210308504210b0001395640c58000e10143d9041c3d050310000b1b00850042060341e201c0c252a2041c1030580070700440b02d8450170b0342502e985207411f4000002401d1808d041c028000d1881d4845801e080c1000ca201e01114a0921208110300308003044281c0c4000c288400c024600940c0a02d00004130a400070300b015042c02000314090b8003c454040c100189550b41400c141d21100500c0103440e5680507500e020b01261082d40c05c9610011040000480c0c1f81d640144000840c51310f680381c400805110150702507503006400315207540b001c03c03101d0034040b40d44100242c2c2d400c40ca00cae00803203070100051102045403140884900082d250140c00300801c0c10b034503009500041c10013401502900d100760b004540c54014412000c1d00440b000107148078035601c21504d85009020310700c00e0111841d1500001005c005d2500c0042d1030f14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 996830089 1250 996828839 996828857
    0xc0203060c041203080a15030303060e0a0b1318020d03090e07091503240303080627040f050f010e061e0601020604170f1201090c020f03030609180f0706 67
    0x45080030007190180c0c2c960001d510303040f9400d60342c2144c110078014140780309184c844040809041540220700c1c0914440e440200300142858400107105100800902d112030414003040200e88410b503100c1d046007c4e44a02003400b5013214407138084a10f07640c8009401802d948206400d05178004081380a80d4020742c040040340d205d80360200c41e007852901031544841802604280c205000e80d001034008008441c050500c1c00d415101440700114941c030580c0402c014108011907442c04c00034180f12040c4260048040c0e03500442d0307501c1e040000500c02070448004507000c1e0140542086255840741c0e180c0c0090280b42640c110711a1185403d4a0802c20101d03042619041d510854106078420401a0f00070b205131788d40d5031110f030400c5000c2c0c0c1c0c0c2e101002000300481c1314079200e0701000b8400c1d1880c0c00b070110119450403104500311003a07148110b046400480e8102544400402240e4102c60300301c42d1901551111a008948410035800800c9070380325598850490341d401103915011242591501c2c1c00b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 996831339 1250 996830089 996830101
    0x70f0501020a0c06030504020d050303160201110c3d0207030e060a0807080a0e0304060302130806060a06080a0605040212060102100c14070c120c03170406082a0a0c020306 75
    0x18031402c0000c003c291100a000611465200303600c1340f5801400104280c0040e129600d5030b6045900590b144124000e5403103201c5101c68090141c291030b6514281031030319040e86014265103075010903440294486018102c0d050310404c142c064cd9013800000006d0360305d60311000514009500020003103010600524001010340b8281051742c440c0c494076282d0b90002d90780c1c00006c8a021600504801d10f49aa5072100c150382041000030340043e1060341c8005944030b02d81e1441030b00020071503101c4181644070380108505030715612a50b42c1183c0450a0418840e10764000540140010f900990741107440401c0c0ca020100d01801582d004500a03020b0324482c0c2c0120000c1c109598a60004e0408140300300c44c1080421407481c010004076025655840d070a0303880e0a041c80359002207120951b820404601c09006010058000321443c1903151030729454186401c50290443c04024004500441c10512600c0f81060a0900b01e19224400e4082981c998145501400c845100c40059000b481200c0010314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 996832589 1250 996831339 996831343
    0x1a07030e0d082d0c16080d02030a0c11030318040b0d021012061a04030b0a060509010510271505040513020903070305102a0c0b0603031b070f050102 65
    0x1040903000000d50307140c100030907440100310b050f18005951144000e01c5041000a40d000645960034406002d45000500440d0104101a881d04501d01e281c01188001d4100da400204990803070044d030a00f659001082c1c1031455050011080003501404001510149405494001040190225410400f200740f032018066007141401d07000750403148210f81110f5060150801d04000002c80901103419a21203100400e1000600380e103510091000c9014800c211500003555400182403104000c00340ca00000134504070010b201c3e460003401d510303004803c0180700b000a2085680c40e030350000c0e114154128400b0345103000d03104140600c070440e1110380c501403081d01120125003009024500e814030031044040207500580d005a8140704003180003002400c10304c407902034a0305440b000200140100150540d0030134401211915160017115050656044106116810b8024404040036510540071901e180700e1459100d91604042504840804000130580207880385c842d2403940459031000160707 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 996833839 1250 996832589 996832609
    0x230103150e1902011d0a030b0f060303070512030a0204030818030715050f090a031505150f03060a051017030408070b0f160201090308070b180f071e1a07030e 69
    0x14010700810945070b005036100355490010003502504051820450200080c240d1203a584112042d6006400300030300d09490360300055000c03200707402842c07520b00a540c41c10344803070307a41021141050010010805040e084c3c0e054034007442d030160345280e0302c500b5140410b80c1107235402401c901c2803150020114000380a900c141034101c080c0e03240d06d4100940349112403140d401200100750481c000a2001004c50001c3d001d03500d0032412800002043e090545012031040088100b041c02015400301200180c0c50008840d2780c05000010009003d48510300c0801090b5615880483d0740078003820a803481c0309010005000712410703031040f00c545507a50309140a903800b682c84070241a1000b401000a0403450072100040f030303481450301106079910fa507602e8a082e0003143c0d003954000700040c200410682c040010568008100004019003030440004a0b0b44440c0c2d40501d2122001074508090091044020381d03001c2c4c2002480c01c440d04a00d942c02e12003c1e04400e00c142c00061408034a0705413400d00c81400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 996835089 1250 996833839 996833863
    0x102040605120c0f0304121409010c1e0506070e1810060c111e0405060109030506150f120141040f020d0b100806090c04230103150e 58
    0x82800c1242c200300b214a0148001d0050841d02d80400007400510105402148502c2c450b0702e0a40c0c0c64070281600600b60b104089820401c81d0b000c01072407a05030f0b0007101010085512218030881f9048501c00001d0840700745c540182144540c90030300207190b0b04540c209001500c241e0f00c410542121138220704440c00b09440042e1800c40150301408107030701c40d44082003490701503001034001d010350300302003501110240001c0c000c0d01040c0401080e6803401d8018650070540c00d1920850a42c19a00c519468000107410407002141020260400703840d82061a5a007910083c03c003440060b041c00154003070304520300c2d00800200c03819581c4030340d03058400310b06050308950808404120b01c080451210810301500a403000b03565001050300580e10491030300c1d130091140b105000c8900344070902e6060303004542c001900540101040010b09100024038400b034500c1210045001070034401d07214a10f0b8580e00c40c3d034205480810020041c450701b001c0080d40c4d410920700810a40c08c9a50b580c94940c8491111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 996836339 1250 996835089 996835097
    0x6150414060a03080a2a060b01080708060603190608060703150e04060c030f020c07030b1311060706021b0105071b0f06050603070503010906091a06101b060227010201020406 76
    0x1043c80403400ca400030b13042e80d20311420042c09880e440150070840340401d80c5504071041c418100d01003081068001c21000c541c081c01d08840c603043c600c0780907103018401051503025000200015001d0717489400b650701000700000082043c151149000c03503c880b400c0b1011030110342072921600f43c5290f18140da2080702c1441c2d403c03101c25212070313440d1005485160b40d0f01d01055102d62044120103118402080c03008c4003100184441459440e20b460044c81c028602031010b8800a0790101080d80704450a41b00304007158442e540785128a0020006e0103028601c00740c111110701d854501031015401240900c0060705d8454182c007400e40740700d2081d02d03002c0008001c40700c480d0040300001d520380c00a540120300142034603402500d83c408030f400c40e00b112000b62070654490b20100309000782c0c1c9200d59902a60800100d07801c1c541100444c031070000554809040190303400d1845444a40c030315075040c490394450740a40d910403200c45119822000f20740d04001c0301505100e854801e40c0148200d4046a0035511 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 996837589 1250 996836339 996836359
    0x603010b030403052107020d020f03040b0d0b03010f05040305040305011802060d022802160f24090317030603060f0402090703240e010609060314160c02030615041406 73
    0x10301168150400d001204200a035450009070f4917002440300c1e803050b03c1e2a0700400900400e000300030719204003000e070080107400030801400900409001c81e90590300d21038010800d00084400310340103003c031004880506d0300d8036041c00100366111000b00b003102e0007100244a03d100400515540c2002504004e500010401c44184940b401e0b4026020f5040d5412011a90400d00341855602000c950800d03c0160042c0c0c4e030131007101001d1802072010301100304102c1141400c1a040c010100100300040382804010750388849031034170408100e401b0303580c00603890302d43c02c42e0101d0101d9181c100360f0f0514403d0240038006800100d00b01c0c4054481d0740c00410b2040c1076150040164014100f11a08142c08075614011144000703149450000421114040111743e6162210080403100c140d0006003c050034645003099406580984941181e00e511581300b40000941d0251018420140d009405001d00d1041010320f0f13620140528000500343e80500c10038243c101c04a080c0c0c00201c0303c41d540000040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 996838839 1250 996837589 996837593
    0x6010807060c140703060b0a09061a071b140901091e150b1306021608032703100504050705011b0b090f060103050c01142505100903030f0b0603010b0304 67
    0x119544821601581480700c4414007084024103100c802d4000742c40247d20713103401396414142191054010041f000c7c08004041c1807004890360002c2a40301010158400701e18501031240851911069801c0000e94031070300da40d21078031904030212410b4054410000400001a00c0010340111440840c0503169001e02152600c00d80000300501c0c0a0040c419800031000709400a80c0c0000307280f050030040c0290441440c01030001d01c3c0c004e05404040c04082a040c0801440c500001034403003d144498080c111442c5203d02c0149513030440c11501d5240c4155105c00824050759408180918090026242e10355155801911851581e201440c600d043c01aa020003165044d0316041d00140c1c00801e483c0601c0642003c289070050a80041c2c800c3d41084138000340b150780103d45844040329010a040c00c01d45c640c0021a40000200800a5414502158601040001e0101c0d86440710380c030b6401c11003407030700b410020300a1034003c0d1440580c9280503285400b918201080c0d070304075019002f031f6510f9981d075a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 996840089 1250 996838839 996838847
    0x10b030903090d260304050601061103032208040b0c07080304051819110c07050f010e010305040c0801061e080a121211040b18100f111002030708070f020601080706 72
    0x250b20142c03200d140308035101c040c54146074403958504d40b460701c907951641054200903003082d030306030b000d4818015907043c601039a400204c00d580e404008445048440b8011108058884440f500c00400c28900084c020400c4003140d07018050340044d0204948445464000c05642da00c224000d5540c0402c910408085500719808103d90111094030317443c120140e43c0c0c420341e081d1006401c640034440c1000c541850b120740100a0103008042c1160848503180c034801c0081d250030300380495581096251b1001801384445281c030b0400610b440e0000300186a0348461480e440101c440e0410b4500d5484d500020341034000042824110b07410215200c004411900160341011984800401040d1105460007040c4003240103400242454280103039a1000d5002061015410101e094401c4101c1c00c10b0803080f580c00f5a00d0b00c104211402d24004080c03090148a29003801100440082d900000030484910b5102c00c40e41d000d2981902c5214178400c0218003070340c44020074000c501096100d854100081882 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 996841339 1250 996840089 996840109
    0xf1505011404021308100204030506160801030f0203390a05090c1e0a08072d11031201170d1e05130305060a200906040306090204020910080906010b03090309 69
    0x1200a000e5500703981e4241290900c0c0c02000465040d031f90208081040c0101401115480008444800c00d010518040603100e0141804041d180100c282ea02800315141004880c0420700854450700c144101c1a0201070403203620500c6140c2030203d10400d840030304022910f401a24001000040070b55211402105280c0040e1a460b1031141000c11012003802080010200c615032655120280d150840018155410380343c044488071504101c4100b010540d4000e01e2013044e401c1c500400c201240d8440e00345140281101c6030006030003203000140810b504c0140195119006041c0e400040c099178040d982200348511842c1c0c000003500c16101301c0c80c0705030003c0c4000b51103030007001e201c80d40302c0d1951071502c0c1d000c80d5003100320365031413a500e11105d8000401c00c510600c4000141c4c900301c882c80c00b0030058055844000c0c0442d071668801000c41d0b8594064030004100940300c0b07a2114001c800c002c3c2840c405940c004100c0c001c507000402c095100350100e901c18501c00e03004514221541c000d000e01115 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 996842589 1250 996841339 996841357
    0x80a0605070c02150703020115050303070b0a0605120c1810120503041502060a050c0f0405090c0f12070e030604020f0108060a0b0c3405090417070f150501140402 71
    0x690079010005130b0796803030708165059101c903060780c846030310345006800c40d195500030a0b8061181b00c000c00031582c0000440d060070f170707000791100507984800300e0381400303082d807600b11030b0f070002145075040348466000891b0400d108003118482e01c0545803003e42c445c010303419034004001003131848044c400c0c1c8a13080070080b070b040c1c03103070088a140c01d5403102088000c9041c40065001078200505002642d0b005009907500003650110b11480c0c00980305070344000c0d100d144503540c05101118009100c40c194002520307048a00b0010403a0347d00080070a480401200726000800b00350090616402ca0900280c902c1c40b5540c003400c1094070261345001510292401051581e0000001d40c010820400b280701514030300d0034110041ca071214200140004d074640f042c2c1d0380c0518480b242082e5034004a0100140120751040d00d001c00b075515142004035400c0b0451610100303402000444400b00100c2076645081e071809890501c0070b100340c04400d8001d4540a00c10008100d1210664144d10318040c2e0090500750 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 996843839 1250 996842589 996842597
    0xe0f0a0c0b0703081303021921140322050132060f04020904150306060510030e0303010b0f0d051003020405090309010f0e010e030601080a14030a0507030518090f0a0f06080a060507 79
    0x1982c1011f84044035880590110f5070410349c00c401c504180c0a041d03641c1d60800d01c07802c101c0078080e003c07080905a408001c01e0310000c001c0d40805c042c0c641c0d00d1010a515582d421500900040b2980c21030070311442207a00d010b60a00c10100007040740303540650350050240c10014252000601401c0c100400b0b504140d00d02a840381e9148040d600c10382d0324240785001140b0407440803407050300c2c04080120440c0b0003e0408241400d0a19109500300b0100c112410349110000030781c1c842669190f190302c0c601500c203841110078600820b01124452000c81001101e100b1a024400b1b5070b108600151170340240030205022445203c0c0020400b409058140603641c410b24080160030082070000341303050030a901c81109900b0091a9100380905800400d45800f1510015880c03c0381c1000c0043c40c0d841118009801c100c1c020400544101c1c09003411420000c006000c011b841c1400009408500350075210702a84a2404195086c2006240183c404071510f42000d414a080a078031264090007004088000304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 996845089 1250 996843839 996843853
    0xa0b06011716140702060306090403020703050f011e02190327150f0506010c030809100c0e0102071512020d060b0a1d19060c03030e0f0a0c0b070308130302 68
    0x16110103104500c501c00b0502e8801d0381d50544a0040c04140f01c000b5941102401042240b0260726404103c1c5d0700410140c411184954036420224140003071504010100d019201100302603a4054001d05008990165a00580c04a60328035608900c2480744c1d8060140c1d020811080480c000e500c21480c00d044980180701400c030040031458200418103007113030a1008020fa641c00e10040e031040610320348018600300f0403400d140c40060110000d104000b8108800480005d81c40242800100c080c04203483d024005c3e440a003402415200000882600600c1003210008041130100c800900c0310241c2d880324a4140c03a48002c02c0301a40c450200b4000c090780300d440c002500c682160081284408a503078080c0e8001011a08444203140c110b041c03441003401c0ea401c0e480c650391460310803040310014202a140d880c21494190041c002e042100310580c001c61a54584079403010418060300c520810000404548560600842c2c1c02016005000140010b0014014000a21010041500900441d141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 996846339 1250 996845089 996845117
    0x12060b0301090c150e04090c1208070219030b070201050411040e030403021c02090f160804050109020a080f0d110c010c02011e0320030601021b12030705060403090b03090a0b0601 78
    0x203011000c2c4d01c03144484641383c10503070810344c0c4404900b200d00401c07030742031141c1c111a44030910089200d010f0307035280d07070110340d0823204209900301103c602e6039000c0c0010070344607131044003029140c0580c4000e07074a40d030031340700007a1400744107105513407180c1e902c4424124486001c100380b20042440c0c260050443c44100320110246c0c1d255002060341a0740d8200000901d043e52043c00341c8000060300c50300d0485100000d0001081281c0c2c80000501c2507480c0440040e80e807428141e000d00201c52000e5004182940c02003220b40d404180078085d44401d9044030551841894101d401c080543c1d480316694100c940b00102c103601c40d8984a9031702d8014074000500e04180d245001c0306901c1c1c82c05500100b5500c00090241c0840c42c1030405442d503d0500613410b500d81680080e454240c2000d6684d8291480d04207055242c2e0b40310600c90036903074000102c0b81c40b100f07180751295032404184c4060300032408602c000910044008210792003140350101030581901c0d04d80d500c4c61442400341c60306061003c040c21040b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 996847589 1250 996846339 996846353
    0x330f06030c1513051801030803130b180607050a08060d061e150501030204051e04020c0706080a15060207060f1b11090726060f0306090a0303060e0112060b030109 71
    0x701d4024007075610b0703a60740f07003c101041607594107070300c4607006132074014203000070546560520b41103e4004c01038540d01d560703480000040720303035912000304025600000c3c02140c050245112960060300720869403161103011303083d21507001c0d01c8003800000740440c00140d420305042044804103407003000003141180214041700040c1720901e4900b014260b541c00540303165500410b00b580100020b00b0114601814403000c12400385082d9090258011002000310325900e481e81111411440201500c0c0f1090f00d0b00c81c024902807040c5c0310908094141009800d4828560740203004a92094000303290aa18201096401001103d0540c1c01d002c82e0807030400c02440010302480589110b925901e6034100c00c242000440f58015003813100f0060b0144400c0388400180070740c102d003120b0000083d4815079408002030300c1522640c95407034141c000c0302c1c103001d41c0b141c0008118000c10b110352014420241c403290001c00c1700e40709114030244000340003030380c0b00070a5203503001d0240c15101400209081a180c0c135085 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 996848839 1250 996847589 996847609
    0x7020303090307030b160507120c210c020f03191211010c0801090e0f122d0c0607020102180603131403041802070c09020901020717330f06030c 63
    0x650880d02c501c0810446d01d240c00c00310305803911607081c01420082e036615682c034010458810316040c00b0b94072440d102400300820122148400d42031003881c61003103042d801081c1030f6030000200e010b010911202b21042c40c0c0072811050180a510110f0040040390311070740c0c001c00ea01d0190303609002e0442840b00c88102c083c000c100c4102625100d910301c651400000b08200c50310781003040c2c92a0005030b4030101c1d00d400842c0210401903407164940d180d440300024000b07149014403080341240c8180014202400002c40540402019402a6040b0740d80b662000d90903441102503941d45202c0c80407000450b464114080d6400404280034448254025600c00e00d01911902000b40a5031002c1005c204000c0300003007800c900c011540c000c4d424070196a0307803e000030805014006019070003041c20340c0c25074420040301d00108034500c03665800d0080c0342481922070306e041ca2200300000c0b1060846090003e032440302c1c1443c0c15148800c520350b5480c81000100d0040117046a90705005281194a032550752903016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 996850089 1250 996848839 996848843
    0xf0c0906080109170304020a05153603030f0a1206170604050601170307020904260c01110306130b040e0d02060105030d0807080103060b0103060306060611210f0702030309030703 78
    0x10b070f48403641003040b240107403201ca0ba00c841c42c04000300030058441c4a2000120b803c2501c0350f5010840c01d41c1020203900545050503a0140e0300c4008540210000c2905045200c100c0b0080c2c0320f012124003415180e201d8441c1d11000b0700c1c4200168084244640ca00c1c02c60506034801c0000d8807a110b20f030f401040c0400c1060a003203640600c00f44404d0010a1200900408801224403282c0101c1600c0e42e480f400740f010040d200302c2d0303000d00045c144582d0b4004103e04001c424002c40401c00c2891241e4525004010300180c2076290201d0710308031921410071130303028020007000c24024030b2824013403002030082500c09a4020780c840a90410030b44041100c4070302d9070047d030003400841d0304000c181450412003880480030408200284940341d90030501840c19a0b03000310010a2409012006070b02420300c9178401080d482c5003100005810740e20403c000c03030300401c100589032000c07940454404171016075205a019004100f18410140749140d005044042c4042c0940c0d0070909100300203070402e20740d5841 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 996851339 1250 996850089 996850091
    0x207030309021207080d030b0d0b0c041d0c030103062406031d0a0308040803040c0302061209192103110301080706021009050c010311090a03050706030b0301180f0c09060801 76
    0x6480840c5410501c0d9a40003000d4801046020714100345c16603283c3c1c880032403100b0302d550b50807501e40a89410340312106190304000005254100022904540d034010f2103601003851944080628010640e04c1b424051688850b58a00316402d6071200401000702c4004012030010060041500000300000000200065200050105220811821292590943ca6040703401c0b01014034000794019003a280c2040c0c000c98501d4681c0e44d145000c2c800c000b40f42e0000b80d440700003c02d05002c0030301000d0011340b0071801801070f00c40303c0d620300341c00009418420000500340041d004029091516a040402040f07a5030302e0003081c07502070f00345d2811495000303800c90645504074640a211160701009030f00402e80412004002c80f144546999840d0040c9034102d6040544880d00c07543c032400781400750703030032180014004c65440f682c928180c0d6681809101d003001207410130502d49064501071141e0a198a40105d0f007144440040d6a480c0c07a0706007860080742c0001c000300300070914118500ca400d01604070100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 996852589 1250 996851339 996851351
    0xc0e0601031103040215070516090504020f122e05010305161505090d03090b0d0501030302010c0906021506031e070303230a0c020609040c023414011202070303 70
    0x5056481c180b240070b0740141c1c104284801615543c454143c1c44000328002c6031140d02c41d02e00241082c010401c0100c2815001c080807a01c50080d50000e8081c0d80700b202c0e58181003540c002404015040c451241c0351079006800800140e1184944518640100b4400741c8001144801010101c5800b80c10513542680b000c0101c00c040c901c0c40d0900406403201004d24182c0c500a010b00910740d12802450380e009030010080311041501500024001d0000031075901d440d18214101c000091900348010340044d824a9242e019180c0101008819924154041c2c10700c82c2050100c031030304800c0a03207240d42500c14443da80c2c204655034101c465960015038041e2030391324594207006003032019695102038400d07825002d40c402c80d403000c4c00b07d075004190341c104011f8216040c00000e40f6400380610098029040003400c0e00213550110b9400c211801489075519070717406000194019800000f090080390b4038201040c803107580c00c440d91650703c0b001490148e4110052924201c04d03030300010780480110f03171511 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 996853839 1250 996852589 996852601
    0x1421030c0a050c1003020408030a0e0109180f050f0105100c0c0f0b0a02010c0806060d0c0207090e15010b0903031605030f0a0e010e01030e071a04051206070815010f0503060103090c0e 80
    0x180103903000c1c0c8070900d015801c060608d2841d030785078800d000c4076500f40034010010045c0c41e40540c194000904041c1d84007a444901c64480002800304000c003d8121803a100c0003d81d0324084130609410f03144050080d26840000b5481550023440002e41030324581d5802200048100002540d0009040d03c05402c40d01d403a202d24010b820f5a98090300c000510510004112030340c1c44040644a66159000000c0348440398110164101001a001940840d08200050000d034100160b68055010f2102d5240e07001d03a607907c6503460a000e00859664140c1081103003000b0360b036141d080103001a016a05403840c20a111049444640c08203560303c001c1240600c2040596030032040e00781c103051003800d003805400310354610302e80c0300e04140c0a00385481403403884030494aa0000d040d100038100c0640f056140c0341196503d00c0e1388000403181040001c405800003a00f803600a140003014802c10b03146d24007004002881516140c0000b00b0703240c1019a60350785c8102142410103000005d03d0b40020b002c1c0c10b400c1c65 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 996855089 1250 996853839 996853849
    0x2040c022506051905190302190311031815070216050916030c030603021206010e240f042a0e010504082d03030106181421030c0a050c 59
    0x10284611001e1000030100b04541e04207044440220f0120f1101101003201001074410b405800046e450040041d40004d02080d003517401001400940e480d0540100e40c000f00440594030b00e000924803003030003400803603041e00e400007043d6028a5803030140c2e00e00001507e85040c1c42c4e40215140c10041e4081a0201444089074920300c028040030b60b6411440d03e4031069a48488014900c031004040d0b41e50001c086540c420b0340000080c590044c5081072920000720001ea9500c03003801040101e28504c00843d8040b00550520000705a407070202901c640c00710003c1003a0451014051500300d40c5034588200d905c160400405603981d1040002440800d100c0c1c1e00600d0280062100c0d0b042c410b04000611894a0021b00e003003008944a03c0010350031070203030041520640341c11114a20b0311001c0004108640c00402c200149820050105580755490315a003103401510400344d6085030f40c94605481512140910014060b42842100d02c2c2900003002e040c41c00e90728420588854000508200081c988 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 996856339 1250 996855089 996855133
    0x14030708150604140705091e19091d07060e0103060b0301081e030309150c0d060b041a0f18042d0e070e010e09100501060519030509060106180302040c02 67
    0x1300c001c08007245400d02c0003901c644140380c00503200b41d4402020460140340740c5801042468060a02c50080d49109a0900340d00b060740115590141092040c80d01d4506910303440c041040b0300e00040141320700c0c0031001d454103119600494105038545002161400301c1b03100450003450020020281d60403002d84c0e0245882c0000760503c201d0300108203011120000207640309401e0a0001c40d6903036600d5541610900d0301c903403031200d100d03103081c49400074200300d1800240044441c0b1441c043c485802c01e01c04038170030b07100c4c0d03560070140c00806120610b105040803810301c14030040a08006800ca81550b488400060100d9100c011740c81d080050b034990400c14064640c03044040300c000c22816040c0b14058030f000005002d50103030002140005140004200b000c201a841161402c000b1561190002885a44020300d41c00c0c22014800e01402c07294480e1042d140300c0c0301c4000140c0385a908025088550410a00243c840020040000710150740c80b4401c4150380385194000b440340c817040800485400300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 996857589 1250 996856339 996856361
    0x1e0703123e0a031e0302120c19020304081002250b0a06051503070c03021c092c0f07020304030501321b0d0f15050108010906080714030708150604 64
    0x42034811100103038004850b1302c14840344480d0762a1141e1090790440c024003e0686400300482c0349000d100d008808440107000500282c5500181d03070388070030004d90b924402c0b44200744e001c1d401440c0501035000954003406c041600310008080321254000c41403c4001410750a581701d0f00030381b043c458407220b148900401013106448456450f072648903080064003000b0510b10034800b0514180c1c0c1050700c01d00c04408030032041c0320703d081c0c40061030741c0080c41c144081c015692200c0522030000d101030300c000c0d8100004503524448440030341d0313136050a02201001420107004c1d0300c0141300c0400050400e0280e0003407548402c2340300ca01003190031070210900c2001e103120f824481d100c00074041140e03040c0e03108040440054211540d01c00707440c024500180303071038052803043c00e140c0301314090034903404807a6070112071090381c45903010f0743c8500100040722198070445040f50300034002080280c2e41d000000c0c6940360000d05982c0c2c01c507070350340c034542c203114900703001882054240c01000a80c1c641031152840c141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 996858839 1250 996857589 996857593
    0xf020106030f0b2d10050409020906220e0f06010501030b150702010c060e010504021f020d0e0a0905070216060305070f0e0a0503010615021e0703123e 66
    0x291960725060902001c101010302011440e4001034000004060b0740f400c582c0d07800d88200a80400c401013802403000585000410300803114000030140340038042c0101c22034008000f41d0881c1c55080401c980400308070426031840031211608800c1202c3c0e846501e214420900c0038101104182c03e80508003403050b007103c2c2c1810b00d004a010455180d5822520500b028007601d00c1e60f4254a00040c1d440941c0300c2d500038001d500300141c0d082e200310103401c40c50043e88246e8900075482406822140d00801e18184000103034000c022102c100e030300c82c0050a150000c042c0c5106c040a443e01000401d4403401c0f00d00c500580c2c420f8482c22276200000e8010b00040505140c100401d0a02203c010702d20011140f51310104281010143e25950740c00164100404c4000e0082000690b0b415940c010740c40310034400400740c01003c00440c408800d000412100c04091000317800301a007150346400030025800e0140040000c418030503105164880340c940c110040c0040c2c08a600d1140121400c4207480f0084048038507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996860089 1250 996858839 996858851
    0x4290d0f0e120a1b0f0f200f0f13090f0507170309010f0e090103032303041716060e0c12010c140c010902060d0609050c0a05190e0910060f0201 63
    0x21410209460034000649004060745034035408035444c6031200300c000b0784200725150f1301c5403c205150b40c0104240f449070213005400104806810b0101d001780610171381210b0a60400c030038500d0910200c60f9140710003080701d068011580c284000b00d90050b41c046070364401c403034804c4003800020880600144100d10300c0d5068020f80c0143d054580c040c60001f54140305001502152280c001d4030781000d00d60001c0d10307110b40c56a42e070400800303c460f09480c0f1910000040c11800d02d840340401200c1c45244c0050071704290010188850782d9944c84005800c00703e403101040400003901c2809144510b42e041d0b0014815006010104070f901c540e6203000e403025a00d004503410419810110b0203030001800013a9580310220364051a001d0118190001c3d88840001000c80300301c09540c1c00781d4290360b003880c010049582e540e50f40344198450011600c010a0f014441404401c038100d51010902aa03850000004809080410410702040d140450074101c50601400800d9216022000d199801d100038815 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 996861339 1250 996860089 996860113
    0x91d030307020a0210120e010b0109050406050303031609030803091507030903020a15020c25060206071d040b0913111f390c050405060604290d0f0e 65
    0xf44a441a40007401100250151a0036134028001c1d103c000d42000e0007072251400981d841802048040c29113404201000d6000c5604e0a052143c0c60681e1000f500940c5180c881011040c9803a03440406007040201d409800300000340c205004e5401980150001c00e02c0d003200d000d11541e000401170021003010300d0003007100b01096000a00051b491b03001028841200c00c0c0610150207845a19511821885504548800f1040c0210300e1119454101c21400b10b244c0c4a0004a03240c20b801c1d00c1010014114400b5654112009850321072100701c004e000082d000500000318044070b0088500c0600c0041148904041c0226400001d04054040b160021800401241100704560003c0c06408200054001044a103422040d50442108410000584510700d40080c03100c82c143d04002c480340d40605000240e941031a00400e4001c40300104030034240b03410309010a880303100c950048692180c000c9046c9000c000070100802c207a00d0842004102c00426128086c20341d200700c500300603da40144c2d55050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 996862589 1250 996861339 996861343
    0x30e041407030e1606020d170126190606031b030c0b0a0504080109052b020a060c0e130b04150b030408032827020f0622091d03030702 59
    0x5404401418000f41480412000c0341c03405804541c00c04095130899070200d00190002144048541590360340c040081e10a40250301c2c5560a1080003451a00700d000d200207100d42c2d6000d1054140da0300d0454020281c221810384115595600070f403401c1e40d42d20780600c1070041d1026030840c0c0340c12400001040c2c03481d40e41d0703032440b522884c441c103d40c1d4040441e01900a41c465001c0f02e0040c82a00004c1c00400c60754200320391180103040b20144a200840b400031046185842402420306498015200c0b0600e2a01d59402401c0040300d003c003040a51070f08201c2650381e808440c180b0b8400c1007000900396042400780402c95044008502446468a4040106400000c22668071690140d03080340c480d1580007030000102c40c3d11109954014a9641100707200c409907100d407001e001d030302201507803c501d451505140d2000d81c84011390030510040e02c4164038180705000b044c4004004090003043d050489a5001c042502e8008000c2d450303d803407036460f03044050381c41c21110002d080090b41c554107045202075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 996863839 1250 996862589 996862591
    0x7120c11100f09050703060204060e01090806011412100c0e011b020616080301030303091203110a08041e050a0c0b030708040f0302030f16060624031109030d0507030e0414 75
    0x80c0d0407903120560010014101c3c1c02c900b80b100d521104641540d80c89203001d502135001030207070000041d4504008105da41c402c1e00d90360b0403034102c0c101404443e401e00702e08003020200d10840030f401c80c032a0a22540560010458074845441e280b0300060b890340264401001c1c5c0c0c00040340b0504015481d4001111241451078110303d559040311220f9950442020001480392030700c0e0040c0c0007410110000042c1074140d000442468441c01901d08448014001a0125500050111440760040c000d418100380554081c40d049400345914100e5203c100158a0084404010468954200091520030490103414000c06400c0007800a4258504500f00178400c040041000c0d140d004540580c0e0207050081c012140d81100d1040f5695450403421480310507020700c941300b2502c4a00d080d10010784007043c1c031200080040810000f00440904030421006040321841522851500b0040e1741200e0f84c0812511504d1035141e180c0d00d8a031149810080d080c00740780d40c601070042d400c100003030502d00032540e821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 996865089 1250 996863839 996863863
    0xa03290f06153c0a0503191505091f0b092d06130f03081b0705090a0c0207050307030506010f0902030c091221040812070b1303051207120c11 62
    0x1a00503191440058103d540d121640ca03030000340940d0441d07026000314840e101182000c0304003030031000c1d80d0088450030b03c1c11520815000c00284003526080b4100d0390030905880e102c1c5190724010260b0281c00f160340d4040b0417101743c0000d0343c809600340030500120403c0c0c1000710b4907054400d541441d900400ba40c2d03403d84521030001c0c007951902001c0ea072001c003800f40d048098216076100e1510303603000d600c004400324150303184000903600c0c91000105481070f640003500740030303e544900d450712000c0c02d0034100c0c004c15401102070114041d2020401c00c0e0003107010f180107000c95450a11804100c2916401030511030b80100104800440c0c198222090020b0640e90340c805002460b2803142051254400001a17004a642000e000000b20025109580c0590161180e01c007054134020b910b84a151401403451901d580041c65917010050200d1410740641400391030100301202405034044120b401c04080b4003804407542081443d4401c80071900841e041c0721821340345180e02203135624410340c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 996866339 1250 996865089 996865147
    0x160503281a0a1503230a15021308030310031e02090c0d15150518370e0c160519110a0e0a050712020c0106050f010305060a03290f0615 59
    0xd00d51458034108401406147c2120b010402c20041d0244c20f0044e62001c20211100c4c18002070218100e000072003281c1c020382a0405101101d4038640e076450b00c0803c0f0b50141c1c1c41408103510302c480940c5428030007512615181312130640e03440084481c0700c219402d050714107c4821092009000400002c0309c042c600041038180b05458110111800d600e04442400c8150081c1916041807038007900c0080b880c0c1c5014007203044400c0c01103941c0301d14042203440d2160701801e80c20310010070f0340c90b400c80e80185000140c0482096010a058407003034500b80c480402c0c060040c1851891106106039420500380400301105c800d10102d00d003031043c0945003009000034810503500e4001c40d11040c0a000c09000f181c000c00c90941d106e41300504814000c1c500c52081d11302500018070010003e6102c0e01c1024032a82c8010f01403d8403900750744a400c110301140c501ca48900d02102181010f01000740e0b1030038401e44090350801141d07c0c2c113406000e54485100c0c528030782e0b02414042c4941c18000301250023482c44184903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 996867589 1250 996866339 996866393
    0x601060c261c0b060409090206040e100311061e13171e0109020d0b0702120f03070f1d0d0c050604090e160503281a0a1503 54
    0x4200c0300900c203000c01080015a604500965801d010010300000490011034410900c2e50460b41c0082c1c5203040d0003039600c81e8003000240080f0031268410303485e00e4000380417903040035240c880c40d440d80d001c1621009440000c003501042084004025a24011425264903080c030400c1101582c03801c60418444495000c00310303065544901c520406001031070145e0785003910031210b0a14980b03520003050409190081c0b012950b103001d0050190309441c0b90301410340b21134150740380c448000e890400f804c800d0850050182407010510880c0103044271100441120760349041865000d046c0814250800081c4801582e01c8103841104143e00ba08481c819554504070404629110315414a16004680d0080340440c1c042880c4036941c3c0004526099802250380041c03a40b03642c0e4200401c5407044540c075a002d13118000e0100014040b003a001c840d5182d0080680c2c0469540f213001c0303c5205020303d20f110910041001d4000346000e03040410ba254410500741c9070950300d8205070995601b00259503c00000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 996868839 1250 996867589 996867593
    0x190f0b040204150b0c1e060c0c1002040603021c0504170a09031707060b061c1104090903020a0501061710180c080106411216090501090605030601060c 66
    0xa003110043c000d0810500100d1a00c030701d00303501d0641150b500f403116031080001c41443c581a22424002c6645038078000e0846c1d548500b02003013107902c080544100e0b40251a801c004c00880b40c005031001c2c00c0c041e100540c07920b200038074200c440011510404030ba04d062000744030202c0e030003002100044010840c990343e48c0c1903070300702511960311030343c801003a10000c0c042c01c0c2103c0d014803001c0d02d042d5114120621810201c0d0b010048a4000d919201c400b040c2c03503d9400e903c0728002d0303122030307550110140c28070300301640c030803260b8100d480070501a40941c22085800040080a2083d070001e00420b44008901001350f0f80710039542c2003140000000c1c1e036034443c0a0f82504011901c41c1e4010b80e8409610003d440d103c0100300d0181c9118418011516940340194082c1c004807008010010070b103420b030700c0800448280c2c001c8440740c44509650005035850310303a00c820409200050361301c07501e001da0001803031401055070111241640906480da1500405120304c3c1d4002c90310b05d04540c02031400213201c0d540f038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 996870089 1250 996868839 996868841
    0x1403090a0b0d0f0903120203092b030f02032e0509090d0f020a0f0308130b0a06080c030d050405130f090b07120b0f010c0311010203090304030203190f0b040204 70
    0x9121040d6202608100025146a079640180b00000d06040700b4407000c8003400d080815660007000080202e250260041e0002440e54007841d072100180c000c4034154100c1d2001185114401c0003180c80c3e421522203581c03000c40c2c05000d00038100034814402c40c42c40c60014103481440020302c80001d40300403c03400b8071020540b01c403140b02c09050004c2400205043c0040d8407a0303104180c40445020620f208005802c21380082100d8a00e590480030100e000c080a40c1d0455174902d000b0034410400d009658240b0111f00b141d4012072090f0070041c80054043e0600c00005d03c1c05645480701d034800d9205030707911184583c2c408252400c403581510713220050540d454504000c2c201c0c100c1002005071400709070340284022079540d00c2c0281c1690716507003c182e01940100301999210000d554000c80d00c2c9100c104036501c10401c03403070140d004e031400050344000c46161609a80c800d031420343d0309910103c2d080c0b096245c01d0000e0086d00320203051400f4205490b135140c040c42102e580020303001d156101d0001c2d00355196 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 996871339 1250 996870089 996870097
    0x13080d020c0f10021338090a050d081b0a05030d020a0906030e070b0d0b030312040b06010512060603040311030a08010611120904150e1602060f0f041403 67
    0x100240954a03940a000c1040d40c03060307500610b071854070980781020f11401c258070032204030407029144510700605100e592880841c09002e140c40c02d80e00300d10490010744100004c80c0710313040f89004c0c2980d220079250420521801d16000386108005200080d00001d40080490b6600c000007002c010140200c1c03030010b42030000324a0060404d0100248054141605030b00034109603403951614024240c55035000c8048800f00c100d0302c2929480381106106143c00e10002e49040300d0000ca001c03074070010400c0846d00b0b603041a000e4588060100d02807100b040704001240e0392180b005e03c4c18508000960701008800000540b80314081c50000000c41c3c03d1522401428000041d504203c0f580c6801d805002040704c002445040c0000b030030020b146080c1c260200d40c00c582c4903c8241ca003030425a00748100b0004081d0f10700c000c2041c0c80b01c220001003ea5100d40340e01c0c826681442e0f074140c0798001c003202030300340403006140300a14403042c0d04000d41011300c41d0506030003541241c0c9003040081c002c2080c071b00e1841 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 996872589 1250 996871339 996871357
    0x60b03040602030a050c090310110d020f04051206060303030115020709110a0f1404030b0c040504180303180b0c0a021002031f090c0e13090b0103060c0e0a0e1308 71
    0x800c42402001c0d0011409007045a404102968800045002d5401a49003869040e000801c85603040e502580241440f00c0c4103d10701450540100710780d01c100e0b40030b0312908280c0070001c1810807140c5024920300700c0000d0202c01400c95480c1c0400082d460b4403050048400d00079109481d010700301c2c400c00c403080190507c0300040009030054101c28800350440ca400c0300000701c0b0301e19402d030002d108642d41011021940c4403503050034190f503260240c221008049145406090000080990b42c6026400091407c42c1201c00c80002c1802c00500362261010b06070816401d42c03001c00d000800c40300132140c0c003d124800068580d5031a82c412801c00c60031000c540a0a0300100500130000200071800c520140d515040c0c0c040c00c0d50300c070000400d541e1084804400301d41a1000180c1a00f0100e8080740c02c2844003000081403da9950341c0c01f9851001c1e002541d48540c0c0704810207540781c010304201881c0004803103e000c82ca20303146c009041d2510080400e03203000d4101410408000c00710095580c924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 996873839 1250 996872589 996872609
    0x80c060712022503050c1f03022230121d030a060b010e04050906220b1006031d1b0a0e0f101505041e08010c031a01110613030306 57
    0x250384054400c1143d4090200369081c5c0030740c00f107032891382c64244508104080c80030300e11800041000001d83c02901304000e104400b107804444a107100c00071244540203814a1a01c0190f4504da0015807002003900c040044068800080c030b400200c0c40c6c1810703800d640c2c034051a01d10004003105a0001883e00540700caa505481031f12f2421080041580001035048020781e14603c107045680700304400c0d2a17042d030f4110203680000000c581100126840c06000c640400b085460158190381c3d106a607080844035621708001028091003040e40c580903d000d500280c60200b120307050356005040e00d4490341ca10b40d440c03802c01d54800312400d0f182c810042c4000c1041320101410351406d210301e180c280d5402c030780d1000d003041107501c00b00b0100001c46413408801e02907515541001d06003440d84a48002c502403902c0400c214150000c0c07603050034000d20a1041d110b940100b05003140350b440d14160003615141a0502c080c0c1d0184003041800024600c0e80f000300ca9500c40c4d1050681e0500340e0007001e107500041c01ca2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 996875089 1250 996873839 996873883
    0x110909041a15010806040b211b0d08030a05250201090b1003050a080702310c1110180f050f0c010f1e02161e080c06071202 54
    0x4824100e241541100103005100c2180c0d4840e40c80304003401000d00b0079800700f03a9610224095081c5944000381c81d81020f1700c141000490507807451100a14600a500d8651140c414065400310300d001c4c40c05100425120141c51400541d41c480903808002d200380100e668801c0000d668070480700d400c030849422100200783c09254104020b020b010407500640b03000707081c80c01040302840074560010489410202070000c021580e581c90700e890b4005c0c1c03800e980c0840350b54030145030401280000154000390f60072020000603686800750954a00703100000a002c00c5142c9449101c501050b01c5130010900741c40001e14400ea8603148200a940c200c001e484082e96001082c10017900103003d00003014103004840f810700340c103c011a4003820380c00230800000c9640040b101c20308940b07a0344a581240034016110485058001019500559071090411036000c1040d40c0480001d410408040c100c00805005400c603c1c10124090740301c0c41c1d20050041e03003240b260700c00741c1c0d1080c426580604a8074412400c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 996876339 1250 996875089 996875093
    0x62f072a030c0f0302090112020d02010c052802030d11030306010318050a0c1703040510050306010e0d1110020c310c2d121808040f0807050306040f020411090904 71
    0x40f40d01030b40001c03401850400004901d00c1000d10996107601d5008000b40e204d105c0603401142c1c002e09041c02280c4500c18148842079042030290b00400340ca05000c00034594444070700406141c4004241800c1c14406502903100156401108882d4041c2080c240400c1c40c2c803442c910001200e0652001070034500508029800b04040c3d83c00003400c0388d002c040108403800d07071403007400c2d1a84203a00c59981c0c4880c1980c080d01c0e01900031000782d03512500504240203100e01420100d101c0484540040300c1000c25406414003d1810304514200100d4500c000c09003c8091b10215044010002c80026243c101842aa40305035140039015190424039070207010314584010060005d0004005035000c40300304440384102e12920180c8036144901a5540b9445865183c0c40304000300300c135403480c034510100f9407a0704c3c0c0869443c8006000800d0900100307424a880c040b80300e8203020f01504401d200703400a40510000c518955903a660ba074dc3c044400140c1c07481850a520b0042c410500050b41003c8980c0420003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 996877589 1250 996876339 996876359
    0x16090204150908070303030c030e2b1b020d06110d020c07050d0206030615040b040e0f010501090305101a040e010e0114060a0b03040c03062f072a030c 66
    0x4072128030000690503200164140c0798410790740507501495115240420200e80300350481990f541c518140010316201c070740c60030ba00304542e004614a01e0303034622541d0003c500c14248220001081850203c007207241e4007040c1c000f070b2408480c010b880303081c08110501c10700200c5d501130b850480007001c105a68580c030380c5c0054040d40140d2010603050146443c009100e06000d0050b90420341d005058629541d942410020703c440c84649044207500e0502c004120f1042c890000c0c00a481090411202483c00a0301c0c01c44020050304130b28100030486900304009880000c03100e18074191610045070210b400e0002881c01100181c03400d40c0141041a07008080d901035100e1707543c50480c040240320030380f42004030100418058030110f030091400c2c075040191562103000b56070468460038080a440341e0765180d6009480701034140a0030405c0c1d1150702c0100c1c40e180c0c2c0c161100c0440d00544913051101c90386900c5080c404d4040c8003000381c80400d20040c40c0c4070086201c04040d50340103548100d155250542c1c03803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 996878839 1250 996877589 996877597
    0x50a0f230702060403140d06030c140a090b0a0320033405030303060f01120c0503060a06020a08180315010b04140405090a12090e0406090317091e160902 67
    0xc02000c484004901001e00c007091192003981c00d902e810740c1c5404030481302401640405170703072401661380f01008000139825560a40040400620380703d4522100b070100044200746030700c948a02d91a004000320281c5a8103000c0045903004940c861808030031070f407803688000ca100380140d0b05001381c000086a1502020002110900204c101100c006640c80321200514860043ca54554800d000041369840c240d0403182c4a240185032441041482514010075100c10380780c440007040000c000c006c02c504201d81c00c60028103e500c02000c00d0b44040d25008100d01c18980c0c0d20380c1c16101c000360305010351004c110318480d8003007000e01c1d41020741e544c100624040e080b9008040c0d5102c04800032182520f024040e19003c1d02684025000340b8101d1750b038240d55259151420f80c00c0c08a0f04400003000001c02500034405c0740144000f140b03144061030001d0a00c41c0e81040b920000c034000d401d10102050005a440072070b520f12400c403425015050310035107410382c407200102a22444810100e5000c072550050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 996880089 1250 996878839 996878891
    0x103230112030f0e030a170c0105010807170d05030a180b04060e0712020a05060a0905030a030e1f0c0b090106122901030b1f0302060a180608010810050a0f 68
    0x700710078020480101c44280604c1038072076050f4404c0d031144010640c80720701c0c1107021018a1a442c541a85c04101c1420348000368030944154000540070003903e025102021140700c1100050514003c2404c005000c2c4e0001138102d0b030307031181d5410640e2080c621002a181940350080d002c80760700e207054940b441c00f5002d01c42e21180c032405080c00010380150f80c5a40110619030040540300f0103070620047c086c0701d400130390441c000c000c4258000544c0b510144441d402444c02a9213010040c9a1081800ba4a03810340380240340c179101150294006035401100b480e0340e907074490359642581e241c0120b0300b40504459080003111503840c40000d000c2081100d000c92030701c0b400d1101a81003e15840030741c2e42001007440054400a10035001400c409103e80c1d00407000c0b80c46a60700c21404e500c2c1e4011a1164020b840c9440109003405402d00301841e80c0c0481200401780c526141115605000134140c80305c04c0083c00941050b2514080f90803501c07150801c0032525406102000004038960078070008803010307c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 996881339 1250 996880089 996880097
    0x20603090a151e09020a031a01030b011509170f01020f1b0304061b0609050d0518031f180f0f0309150504170c150d0b060408060105010323011203 64
    0x1603212400c042e0041c848507600543c00200744000307102c601000b400c00f1160481e804604c0c800d0210015000d80100b14808401680b20303035030356041d4a071a00c040310041e00400d00c0c3c4201040d41d0004290b1004a40e010780702d040075004031107420280e80e00d10340007001131660095400826a618800c0ca000007601c1c06040d00030400050180c0d000e030541e104d20643c052a00007489112020910b02814008400d00d1442468002000710706038984a0500944540800010301c0001d524400b44110104c0c9280030030003280501628034407801446800964104001030752070b16071980c65200c0c0c140c01d903032400d9070342c00c02280d100c10001403a0001100002e038008802040c041705000c90844040d51050b07000030682e88810b4074050800c0d031a0300024407040c1d0302000500c00d184408840703848207002c40ca6010342061240f80c540c0310100240b4240c40402000e64050b680c240710401045200040741e0b41159001e007000141d5021003640b0007007107840c040c100c18114021100009040d82070541c02d0720403500a0341d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 996882589 1250 996881339 996881363
    0x20c010b01050f031f0306050702100c1d010315050a0b041e06050306132301030b06010f090311150a090302010206070c0b04030e03100903091e0f090903050403020603090a 75
    0xc01511070b4000c0108a00c40c501040c00000e484840d4071080600e04283c134110910031070b81c0d0b0380d078031820380e00c1c1110510016000054000d0b244a02405130762840d1041e424010008682803c184105a8020318a241015110644c21001c503249007803d030080c1c10090821103003d9100d55044545a1182c4100c05540000140344440f840d019803002040c0c035242d40d43c0500c1c5403034010810100501c1c041a903030042c1e5440161840301541c030640d004841006003501c00e82d40d80b45040c41202c94000034952418030110f4100009940c3e4848402c4050702d5020108a4240f544500131507910712140c50b203080307a0b0350002228035044c0e40110080003107034400d0707084171181c0e0740e142421107050540101c004c01003c1c0074030109000a009254402010f00003400700c0d040c03003104036010400c0c0c850f058410f0380800e100031000d000c4a1049891500030800d00400280102d14110702680e00d40340030300c00e200034070760354110440402d4803c50488004580003030140da1039040c0070340038513101d40f14801c0448641750f41e1030b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 996883839 1250 996882589 996882611
    0xe0f0a03030503011508012102042304060b1005121f031a2206020c01110d09020307050f09040b04050f03071110020d020d121104080109122a03170a020c01 68
    0xd40f068140c9202c00ca0a91800070305d00369041002c1070a44040364010348803100300214000842d696560bc08002c03100342c45500f041d05080080b980f40b040664094900c91500484241d0044c0403250a10b05180c1c01c04c3c40da98410305c41c038100240000100c080203108a2000046c001c0c0a851000303d101e07400080c0c40c058903180d4021000744400211082c80b420405001801318070294090241d22210000100cbd0346482d00406460f1035115582100e0483c0d554140c200540c2010040e10015020a8481e03140e013504490000789080c0006000515040c0c151000608001007030140070101400c6a0889450320300f5881e01c2c21003170400c601ca40e4021204412150b4440380b0020700f03c1041c411a8000d41240002c8007821504020421800e00700c941c3c8624001382c5200039140100000c0566500000c1c010800b8501211982466050f44003082074034000d40b5a80d461051000c403101c031800206c0146040249410384090124010b0104040d045008000d041500da030028002c091100c8002c202c0382c1011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 996885089 1250 996883839 996883847
    0xa0b0705120c0c03151009022116031a0607110109091103150d0f0320030f03010311180c1602030d020c030c06040b1c0b060705071d15010e0f0a030305030115 69
    0x2264010b4041b40d10309020040c2c0b901c90344c002d1030166112419151540707210403414200c140c2c00e0780c44011501d91100a03101c8141d0500c910241e90001031a0700038402030080008045018865024000400f000b9144141384c1c000c03003040004217521202806681003002c8160f046400c1110b50a11400703039401010302c54030b000d41ca034120b110343c0010380c0e0800c005c20740c8040b1410486022110344c2000d001c40803500c0c4503410000f0f031107180940001140e03698114034020b16070043d421582c50003000903406005c1d2088000015551000310301c61900c1c1c0300d003a00c056084140b4020a8003030f40500404610105140d408101c2c585004c00a1b82114144e6445205100d00c901c10b52281c216040003d108041300440d07904500b00d40c002049601044003020100014800c2e488004111415480b142c002c200345080c4091541800e2102c1040003824500250074107901240000d4850410021541e0601e0603542d4412455004002900b07114005869240c040d205520030701401030300480e0111203483c0c0c5031107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 996886339 1250 996885089 996885091
    0x90a0b220e1e0403020312151302030108011d1203372706050903090909070e0604090f02061303170c0f030901020d0c061407090501110c0a0b0705120c0c0315 69
    0x4c10340c0103501d004a5012545641c620141042120140e0300312424016520b201c21030720319032030f00b000050f900c1d403600c040c45086445440080d442040100103942d214040420450034450b03841100f42d41d640d5558020000c034a00c400c500f0540c107182e40d0706a40c4160000d4000890010182400b08190901d5a03021041d2859121844001c9440300c0e658000041054204640200c90001160b082c4140480024103003081264144030079886907000300720056480b100d00b90050700a4404001c4030605485603c03e8900f0500045d014450004448500c000490a0382c0000c5811000c50040300d50908203580103948540c81040325480ac40040c030003290f04c08030840e80340400c146c00510006458950584064a0000090320041d035a8049076810039417103140907200e800c10b941d0b907401039414100050401105080010030742c0c0e00151010403540c46002542c03003654064042c650320b40d041480c20a103842c03e89092404c3c01c400200c1c01d6103500d0300000b40100c500703070b049064400d021643e034090f07070a03018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 996887589 1250 996886339 996886343
    0x15020a0b060d030e0d080910210b1c120207090e0a03030e0f01090c0f0905160e0607020d080706050f0403020709020a0908060411011103090a0b220e1e04 67
    0x19018010511515054542c0000b01d0b21909102003500c01c0c103800a401021116401d540448000568030700c20300d4100302c50900340d221414025011860b0066400e140c1041100090041d6595000080c0950b1f43d00101c4040c20f161402c4490070511900e040120340c0c2030300003040b0151141200200c1c00c113050340115841d000c0a0401040000000c1d2000c03400303400301d903803034580c0c90081200302c13070483c1001e02403418001d0086003481e610614202902161021540c001400070b8502028015541030321000c042640540c3e01c3c104035010750180c0020001c0c802c15000a41c840d48400d002c004005280025091281c014001004565910b02d0030689941c011200140140c000e80c806114103500790780036101c1c40d100e80c545800e025880c0c24140745041000c0d68140d888a650010300310642d82d0106922220f000614061803d1a10010109100082c0c80c02820240003010428051104a4001554406144c0c40a400180c0e0b668081c50510301001d43d0625001c0650b104c4c0c7e0145808182e544901803a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 996888839 1250 996887589 996887603
    0x6041404051f0b031c2d02070905090a03030b010e1017090109120c150203070c0b150d080d020c12070606080303040c140d0b01080d090807050f100201020c0106030c15020a 75
    0x1c0c0720076005081c1e48500d050004c0510564040c21401300346d620600390030494004c00c1071300d0001419080a86030544586c030400c901401e04040000f0520041101d802e22076160802040003843c060060359403081203e45580c2001d40c01c1411000a81c2c0720144d20030040540c81000d9042e01c0c0d4072038036404d890503420b002d00a0400700c042046075a108044450f0220b000f007803501c000d21014100d0b03a0030f9078400c2e2048000905480070040901c05081d0540c3d4204044210409051a00c0400700d6004101440054040c14002c00c003425030780b0258040381c010842c40c1060f618643c0100c100d00c1d4050304420701c00d0300e040c1d20300880070941d03480001c1128021078010114040e240e140c60403040818296495803038006500d100003000040412580718042c2100c40c000e000500d0145400808050060780041d4035940320000800c84c2d41c42c1d025601e08be040c8291414402e586000c141a406441041c08000403580f03814000801d002c02e55910300280e6001c403564201e04c3d070fa81081240d48207031220001c0c00314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 996890089 1250 996888839 996888853
    0x1a09100504141b0c0c0301020f03040605060118140d05010612120305010605091c050f1b06040b0706020a020a141006060e1f0908030d1401150203070b06041404051f0b03 74
    0x500890044c0c080440004200c41107241c100c004603003a03802880c0304805003140802030000304003190145a80c404002c0c81c120309107291188250b10508114410f0854008001c02a10038a44920a007001182d410030024000541d450380350b002d01d0b6058020580c0c02e0284089400021840f90148504032201580d0340d82c01d00c0980c01c10003d0070300185403502c0da1843c0a15903040000d070180000c80102801c0d030301601e41c00103500d070054455800c20081901c01c0700104400c0c13100150700c3c0f00303036140507030400d00042c5ca4200d80da006030714200c0d01e00006480c0e1490103e6110358038100240e205884044030034180003c0c2d41d600e07419500c1507003030220f030f542c008007640094844891441584c0d010550a2400b08100790b6248011400c580c4040c4080444513140c00041c00c054604040c1d10b8014100070120102110040000a4503070041500c000e050490000101c1c80943d195002840b60520f40703c0944c0c02d030b08052400c1980c6a0412040c5000c58032644041000703108188110950795002402502c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 996891339 1250 996890089 996890131
    0x91b050d0c0e13020d0506010503072705040c03020d060905010c030e1506130c0306031704180e030708030708040b0105030f0309130e0706121b0509041a0910050414 72
    0x90420042c00c105034807403103000f02805a6101d107005c080c034900502c064640395060005140c1003004c6500300700c0c0301c010b03641c0c04001d840044003000a8190b0710031070300050f5130b119071030582c204066542c8080d60107504108071f002403160b0b030390150250b2407050000304803100c2c540380180e080d206641c0b003850142e08112038020340c85081800d0103a207e0802440c143c00004400500781c03c40700009a0300001940e81e40c01402000401500c010400c8040d6442c281040d140402500680100061141420707444000c0900b801400304207541401c1e6101c0c003055100d01e0060300040c025142140c0544503404508000074aa05020868802c2c403095500958682000403062000c945443d03000c413001541d031640d00c050924814003044002e04000d644034803903010440306200c1500c01c100300201150481201245029420108072150303103d0556001c034450844481c84038691034102d001c1c83e00900c8a9080101d0b0240081120007501e070100c500300309140e0100424100300c030b400c440000e403a4000d0051052 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 996892589 1250 996891339 996891359
    0x120f040c050d0213022724070321020d0f0b10030b12240702030307050a0c03031b030209120303041208100b0412060b190603020a050d091b050d0c 64
    0x41c564005006039507a00b24640014049910900840d02c0d200300900d00c03a040f07014035217000b2411b500c04491011103059100c105041e02c6881640c01300c8141000641030007014098104018000e21815110410103904441200039522510290900d940342035005c01d8204003502c2503800301c450180c4250841c407044002a40205010038069510203281d0031032640550081005082549039904240048800c4001c4007050500281654080d07401c02d00405c0b000c00c3d4072030259490000c591412000440c3c3c1c03420180d008262011035242c60853300c2c03082010341034043d0010f14179444103944401519240c1c041c4951a40801e441c0100022a8480740303400d02403040c0c10b15600f0070500e02d0a02105c03550340e075206041e40e02540c0124049020700c4564000c0c04005e00c61a828004140d6940e25451003040d155210030125014030018158003003601c00031640300b84152001040301d0342c01001940c440c2e00300141e18506002400d0050a07001c0000316060401001c00c401655200b481512818205107480c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 996893839 1250 996892589 996892609
    0xe090a1a01050a03140405010e0115030b130c0801051311011d1302120108060403090e010503060609070908120c010f1808030c25020f010503010b0417070b0a05120f040c05 75
    0xc1c2013588401c0c0008004141c0148036001d1031181000250804100c07003500d00703503003061340681185820400e0400c0440c510000e041e52000002d00310164000843c03901d0032034034030741c0c7e0041c000035071070001080409801d40c00000d80850040d560400000714080c01142c03034032a80240036480d114103640b4010141410b00b152000e6428144015082144924a0500c8401c007644540060b07403004007840305143c0c10038140d0000c4c054402c802d44d10756040401195581802a00e420301400c40c1d40002035400788100c0c0c0c4a00a085103506403600b2200442c290041604017241d150540d510340040c1030715a12031845a495092140d003038650742d078441511541420b40009000e0700201c4030801c030000403004210440f503a8011121a9900c00d2411070040c0b1582d9189899880d0500100700018050382c01d0001c02d8500b10344d9115001c50382002121201404e0201c9640003120480300443c103800d41c250050086d01611503400d03002641c9a450710380200b424507055a01500000e210b00c414441414804000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 996895089 1250 996893839 996893857
    0x71404062316030c14010b1e011206060507060608150c160c06170702070819050c12070e100311060a02240106020d020f070e10150e090a1a0105 63
    0x2403400d01010222680030328601840490020702055144000c006821017010414000f690003040705160401c042041c8584514811411418000c10020b450384944042ca0800c5c01d0914188140c540e100805083e0380c101900886449080c2480415808400101003a0214400c140c250241d00c80181046013541314802c61110100c00014200c0400c860845040013000103556900540b00384070010444400f010f8640011500008020000e40760001110b41c011441c0c0c1d4201a0300c603000e444e0041c540b446000c000d6030400444501d0b054800b0b40400c100e8111440c004d400701d001c0c0d4450301860f030314003494000148a4507000d417000c1984d0928401400c0e20300380f503004a451b849540d040c515290120390444116504000c1c006200f010317810700955001040d107000805049500918194031010306009001c182c920210015500c5070051046000607e143d0780d590340d181380c6102e00208803043c502c650f9800390804001180d0710050501c1085c4100710031004d01d24090490000464650f41300741c0c07038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 996896339 1250 996895089 996895157
    0xc0201140c0702190e0a0f022d1c0f06050d0816031205190606050a09090c02150901060501030b060c250f1805061f121b0807140406 58
    0x2000750720130910001c101c040c0c02c4000a50981d4070b0725411043c15a039144201c040c1135401070180708a000c401c8010361400c208040c1080040c81c1c0000c400c0170799401440407601e041440899420318414050740a2100d607060000244001364444091040c03002461b00020041942001150070b8605000c031203601040c800d103050010740c0c140c00310041c141d40e01521001c0500c111400d0031114500c5603c100c01c010203840c10442d0612180303a101031311035080d6100e0310044a4075000c10040c00b91090112902e215540c1980034414181307070100c00d00030305e44c42c0102e50202e494810030201a103010015964000e03211002881d281d9404800700c034031030010840b9400c40000400001c18802e4281100d4000b9086554221044a241c0e845802c161071020b00034600400340c2c51742a40380c103071681c15150305030001418030b1011403100003d40c100a05401198140d44aa001000c681403903124110794001c4600c5d03601c5460911041d0803128051140d41b0409004c64000400d80c240c680c000c1c0c1c1c96204400c82000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 996897589 1250 996896339 996896359
    0x9221202100c0807051b0c030d2712020d0609080307020a20280b030f04050c22090c0b070804170c090601120b0a090f0c0201140c0702 59
    0x610462104041068000503801c0600808800d0001c1e1041401c034001510b800d903110304002c00040e11030310400300e0240542d040494200480082000000f85201020703007140c0b004010034800038010070221071003d0000b00038600c50b0000d103948048500541d4011540c00d903c040c4980e003005030b0317102881012901652100c3d50000400c102c000a1407007090603070098440f40a4a1401280c2c10901940f074a20400009039140100c1d10f40c041c40c02850516841416a00c0c108486007600320000c550240e84403410000070466206001d003011801603109034121248800910304000340c107103079440201c50345900392035a95405c0c80680c000c51704041c001d1402c0800262038406074070642d4000042030301c811100140800401d40007c0781c5102c1d05507200060448400c220001a0750507001038042410412904102c2350303001c081b030303204007030b00708004002002c565903807a041e80151280c000c00c0040d07203281c121a007003070307a0040c058918100c18005601650f555030b09810030301c41d0008003059030015a0b03aa = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 996898839 1250 996897589 996897593
    0x80405150702061602070e1803120408180612040b0a0e1c080709060f141c0c030c0c2f13090209070309030203090103051902070b0414010b0922 63
    0x454814001e0406034050842c074030b0503e5110f2071071408400080c04542c03215208000001500c0c52040d0402c042003e140e8800b903d08110516500071045004503858148041c0810003030b1800040010030712007a9064004103400303003003001ca401a02400503000d141000024005010800429480800c02800003a0103018105203460310b00400749905211030001d1522201c690001895644001a0700d4800015410704100400c3d0b40c95001c0c08070203100d8107425800440c5400c10594165803a2600300c141205c0e60b6000100103418000711800200740740c092205281c0c0d1041813000c3c401600300d02200e154110a0005002142c540406806446005400028941d503902c1e01d880d40400d000c0c10203d080300c84c074010070940780d0740034000400341468405a4000a070300802500c480c2e4100f4203000480340d0740e054030821000d55001c1444d00151000610404014410103d90301444c041c541548410302c100d050907081312040500d5540c46040400080c0741d5003604802003a4100c0c004003c0c0507840070319 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996900089 1250 996898839 996898873
    0x130e0106082712040905010b07120e010306031a070807030b1e03070506030c030108240a2c01020a030e12041e0807060c05100510140301060b13030c0605070201020d080405 75
    0x83e0034581c0000100107000c00c40510140038640c0546a5581a02d00d403a22a568010491112551000600c03a22004984440c0c2c069400400215003011a10710b2407461800310020407682103804a02040c00500810302032803207031154290a04001d8106012004c2c2455000c0c0c14415642d00e1603031620426001041d16240d1070040d42c05001040183c648a505011100d401c00c608426040300c0080440510310100010f41c46403a00300c1c9420304d00058501125070203104039a084805805001881c4a181e10030503415802044150340c181d03410415030014078070b007c0d02c0700700c24840d1204240050205000c02c142501210024902c4680c01d4007078607540300120740c10845c4a50201009c0b400441850040c40004c1c0141503010841c144104220301c0c000181c0b10503d440d40c003410000c415445020a0261025440705001e08070300c00e446c5840d54002c400304003a1402d140021244890300040016146010720103607100030703505030060400c138440751504981490005000380d4280c17207000410700c0030f030402d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996901339 1250 996900089 996900103
    0x9020d0e0a060603032606041e0903020f15010e162303061804021e120307110312030f01090b04020403021c02040b0a0614070f0203070b130e01060827 66
    0x4540c0c0040f600701e2642c02e001d400c0f00c0080317a190090030039030011100004101000d86070b0120084030001001c10300940748141440c030200e10300843c185084203100c14190000365021901c1f4031001111001c200d0410047c054038803c0c4244074030340c0303000c0022403841e0200d215801e05007040792610103210a001d0018400d0030700b00e0300d24451410800418801142011108003508101c810040c169505042e408201ca81e013640c010340d0090295099204041d9407150206009000e40c40200d07170301e030911400d00e0300340c54148a84107407003403044880141031001d145050b244903054800070090560b20741f1141d01c01a1444030710803507001e0750820004c40140d035602116201e100c40040004c072880c074a4411311045030581d10003e4400c49044404004039075002c4038603814107141d00c2c01240c485400d840c000700480302e80c94000758140600780c0301142810750034029140305a8864008030384a60351b000301002d01c0b0030038020540001d41000020b100d4207c02a49a140700c1c0900c8030340520382c950f5629032400c040c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996902589 1250 996901339 996901343
    0x5160303120605010905030c09060609061c0606080402010c0f030203070b0109050901050a021e07060e0a031e090f031209090e0c13050601022a060d050420010909020d0e0a 75
    0x1141d0301c001c60010100d44074180241a081c24030703d00711401c05000a50391400e1000c10b620408441d0005402910792a05448000d0b0000c0c0c82c854541c00901102d100f0000c840d03241c06d02951500c1d1000400b1407094400c10700440d0180c440c420b0f0105507445960801c104000700390158801001400c001624001000f4002c0c1000c650010300b41c204000d01c42c2c2075540c00340212001c03500502580b0000200654003030360071600d88203001d41d1061545001006080841c1e24218580650031080c404d1542028010103401d6401480e0503410315000c100390390b101402e0140c2d5503209000f0300e05000041d02c05002d10584421401c0c0155010f81e00c080341c00561340c1e90070070754107a80c10000da510624148079600100700007103060244028500180001d58800c90400720030340005c20b03010420203010021081111462001e80385075a150320306060b810142005171001c45007207045501080c4c3c1d6501846c3d8a80b00a031050f526060540c4c0340200c0e5101a4001050810030340e5940c01524011202c104000c046081c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996903839 1250 996902589 996902597
    0x21206131b12180b0705090a031502220f0b0a0c0605251e031503050d020105040c05030307020f0111070e151801080a0609060e0a060f110903120705160303 68
    0x549030400d20940701072208041e00645503d00b540005100d40281d5640204e251a003030b030307c954a010004107401c0503a400903003000f505500420180b055600103185203c986000801e102010300c0040b00d80c00514031801c000f00d94007460503c00158040000d241d08000d0f403424114140441d1034003001c0300c5083d280c1c1002c0c0100303500c000c000e600c034400081d44000002d0070310640c100c11402d040c1110700d50301c4c3d071f28204141d034506180d0a00d05a400c6c1c40c42c00f660b0072404843c3c13501c40389017001c0d0007400d054405880610786400300041c40e103000000c0f100c0c815030151058108400941c01540c03614440e035041290350080e00c0c000300e02041c0c20301c02d5034841e29a12244858120340c0c042404600d00c03004515880c11440d10005104c101d5000400c00c151981c40080051040d105040580c0140008180c01585000e14003095090180d141c11080d07a030700a0240070002c22015901c2100b80b0320a00a0098268002003c2002540841c0020305001806681038030500b004000e00c4d40aa0a00b941044001c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996905089 1250 996903839 996903857
    0x180111191128050103090f0209060d05030f0a0e1219020f030a0321060f1a0409060e063a11090106110106081506060d0f0c0c02030c04021206131b 64
    0x91a880c0b011009010a0a08101c5181d00781c4900c44034100f1181c02134040c00c09140031030b00907221074000040c1c60b0b0300007040d203455141d45840b4621030b9202d501c541c80001d50b48280c8007103a00d000d40c040411410394a00901c0054001c008900618462013401d036481144041e02c0802a00d06000d44e40180b40700c1c1da1060b84009000507a15204035991030010040c5190a5003030103d441c1c001710340000d4070488100381d840c0704c07011449804644129084104541c0c01c25800042000305c0344030070790041804840c00540b05c8210641e450b8400000718040c6040201001c0074007038444440d00c1e17410305a0203030240d40b1001604801244070f5100a0344220005540382060002c052803c0c450030028100545c0640311070b10710800c0b121601e00c3c020b080a440b800300062540d461030102c1d803102400151400060140048802003d4011114000705900901130001d5a0100389414800ca440c02e030fa5080f140d181c0e03511000e044c00414556070540b0340d20a80d07645a406902100103840c00c02071001560b0b44008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996906339 1250 996905089 996905149
    0x140a080a02010905072436061b050d0e0f0307031b0807030201021b03010906050106080712050c030403050703111609061d2d04081801111911 62
    0x64442c2a50002d011002030310000410341c200310b40d8800019181745840d661030300b04890300304548030f440d40c2442c01e900207000c01007044880f40003a01f011100540c54903006017662402140000488082c0280389401902c40f07028554003038402007400b10805050100d0700115007010916040f41900247d44d62070f51200848055080000c0b0240a8000741c0042d007030640c616070010b90358401e00c0014115011042c564501a500c003503100c40203140d01301500f40107e50351840f0280c640700c405c1e01c211002a050b803011000303109841c02614050a1a20446072a550303130358030f088403160000301003201040426002c400500c0310030003100e00c80e040e2482c058401145007480e80c10445001c0c0d4003804008100110f00030030740c9035000c20030713600070100401d00110010240e1400002000710005280420303408040c042031114080c00790800402d03000c80c0000d440000001503420800504400441d0751000f50b03a2500ba00702c1242e21a12280b0412000c1245e500c900009410310301c0407406201010510861001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996907589 1250 996906339 996906343
    0xc210506030717030306060a05120f0f0702070e06090c040f081b040c120902030c03240906061f02120708120609130b0903041e03051612140a080a02010905 68
    0x2800303803400b500e41640600d0042600c4c0c0c0402001207100e21408141c00890728003810444c1c2c011500c01c011941c00349840652403102100036104c0b00000205480010290390000801100340c0f0030307610201038103558604c108003016a000f0403681000741d05004c00140042481010f80c0604030309405001e6940b030041c900d000c004020800148a141818801d6801c0b542041c6821b00c024011000460440003a00210749001b0594644541504c985480080060b04054069403078441c421100b418640320000415036880c01600c031980d120644144041c000680d51215016107072150054a80285265030001403580100070260303054030f0001010303a0001035488445501843c2152114580d085c00340100f0525165179200504001c00c40300811f9401804000b0b4400074064880020404225800c6075001003042e0f00c0103d0b542c1c4204102a40001c9007580341000740c800814600d203c1d82c4031174448884100b502c800f83e0b00180555031140c404941d4020061981407450f800100b4041c1d03003890024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996908839 1250 996907589 996907603
    0x23210d02150901090312050405120418060b0a080f070207081b12010507050301060c14010903091a25021c050106060f0305100506220e06130c0e040c21050603 69
    0x10155134500450140003d42003204840038180d00d802c000b44a0f40d03540380c12464500000301e424402c000102d0001502000d904401021425070319090140c503546001055035801118101c6022619210000307410092010345103501c0000d5104441c1e070a503549050300d0405580c00810b291200c6c07402c21460706420048650310381081a90020052450300c40c0005106000c18042c5c0b0082100b01c0203e68240494881c4944044e440342008008070303861440e000d000760f852441814144039006a4200c54013034113101703481c040264241c0e040d4080300020b065000c0b070990010100e174032008a070010500a134a2021040c000780c1b01d00c1c00041c996051160107400115025403003010181002c0800001010081f403020484605482d0240c07141d041d450042c0001681201520103003c000b4000a03051804044c82e5010320000c1e5183e81104800250510503540040c566501041311043c1000403030400b82c2c490183c005891505940a41c421070340465080300e0703000c101000c1c64641d01802680c0c54180152 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996910089 1250 996908839 996908851
    0x415020318091e060423100b0c100f0908031501021c0e12010204080f032107082403011d0c0f0108010b0d091208090723210d0215 57
    0x441030520f0000e40600440c6050340e1000c5140c1c6403c000300301961203940200c2151030401c0d4106034541646401d00722441c608071062200000c1c48240000d90100840c00c0350420201d0034050112900141c0d006809081c203010303690740d6a542c68508202050746200650300130ac803007401144044113a940028600703014200c49418a9002d0f40380d01000b17640010188001d03034020754058400e5100d808240b802801260300a40c002c1c0a418100061648040018140303601c90310410004400881200d40325076408030340310340102c0c88141c0450302032408a110200a0448000d8141c01c809030311001c6030070346000d003031010040c01121400081074101804254800442564980b9143c007094000806401d01880f82e011030703200015003440300000741c1d00b01403001500100e2044040d1100d8100414030407080ba65030400b030190f01c03004994801e0181c14038180000f01002008816038030300410044e002032106000509142450ba0400307181d041c0300d04158282e40d5005040c006d90000b5100701844402044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996911339 1250 996910089 996910099
    0x90b0c0307051213050f160807050a060302070c0923010e04050606011b0b10090c0908031b07180e2803030b0f04050c040513110d0c050415020318 64
    0x410031242d034082c05403164840702409030f000ea0b0701d0380380da0740310050801d034009045806010001d042100c800528040c007076031002d4114100517070710402e642c0c8480d03c501440341e00005400003004614442d4000c0c0980d00e006481c400c1c81c859849148001706c82c43c442924000394514409460030112014150340101481c044081e56490a0769a00c2c0e1640d100030040c9042c0050b2034640016014020540740700b09501681c0e40709603060448850149000c9840780d005498141102d0101462080348041e08070740c0303005c00550900750a104024200840410a6030440c0704001c0c0000d0003d0030f41e42035204000c0d20010000e11007000c7c407072903401d211952980310064030104e441c2d030000c0b4410080090300799405203000a60100c4e61030019a04113010320b80c02c0d0307010307081100740140c051424008000b1604200c41c02800002d80e085c800040d180ca200c0c0c9003545840600034080b0450b0705130045101c0d40210324146103016202e40041c5481c40705544c2c1000140d0000c10800e03801000c4d0030310300440e0841214 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996912589 1250 996911339 996911341
    0x1603020609031614030c0d320712060e0c01390c0f080304030807060c03112701020a0b04150608160e010911190e032b09031e0302070e070201090b0c03 66
    0x9410b508411023103002d10000300040c1c40840d0b104000b070f40800035a0410003d46d90055650400c41c1c03000e0040b40c8066801c0742c07a1030141c120002001498084422060b118400e5045010040d4000c8140c5030540c101800221041c1c24081981c0d1400c40d110540704881d541c0102d030826081504108150b04246070310b40c8100001d00c00706c0d800c80207682156511a1011402801001d4210083c100e40040b5001c0b03ca40032a142229407003004043e0035002443c1600c1840040a6004a0f91280c01c0c00300030740110200b0700070402281208912010702c203100b400c007048465a41100914003030400da442c624a22104500b88214844400283c0c010900043c2c2030240c03100300300302c1049070301c9291403059807035082c1c66060181070b00072060b91401041c014142d916440c1e0150002600f0dc06002400904400016512a016000351090000e83e030300a003203410031701c004002c1c6050085800c2d0069007544a204d00000e08021080c001e903104040079400851901c0082ca00300c4900c50001c0d00030b44031410240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996913839 1250 996912589 996912593
    0x30417010e1c03020d0c0323010501140d060302120a031e0e010c05012c0106091b0f09080303040c050405180c06070807080a08060306091603020609031614030c0d 71
    0x3526042095081e1000051802d0061007540284110301c4c203d204036080c052181c0920740c05a001104004508052100c020380300b20a081100c0000d00070640414a51410b42c0401c0b44000058044136403c3d00d00042c90b143c894000076501c1c582c09981c940310398020550b0b4401c040d07001881d22140504840b50215107001007101900c120010f550150400000380040d40c2482001d400c1003000003902400c1410021000a81d06290384050013410001d60038070000183c111410310541f000001004550503840541540c2250f0741030340504045d040014135480400e19010070710055000d94030501c000e4040c149004140310559400904000c551040d040031a6200300c408a40c01d1807000c01140c02c3c075641d015a1401c80094000c2680240c2a0700c0c010900301141500181068081c620450031510301e0361301d03090041d5072151301c5c1d0402031650314440410001801c041015103030124006081d9000c4005140002d0046403c03175001d030751405407881e09601e03035050138080075900100c1a0740901100800d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996915089 1250 996913839 996913843
    0x15040503030c220611010b0102061003020913120507060b0d02093c0a18051902010c051b0a0602010e031b03040b0309100f051e061c0302030417010e 65
    0x809419140c2c100050003503040720f003d03040403080f41c0c541400d4409541c8440c40100103105820704180319600c0c1044003030a560000942c14401c1009080700d070801415582445401c00c00902841000b1000545120024950044e00240e8250559845841d054107092003010799200c2290705000e10b046140041c00340e00c1d03d00310241c0c000541c06542c8629002e240604039284485c6624242083c031961102502115144c551401a00710040074000c810510346a041d00300101c10004107150b0016180d140f8441080213000340c0640141880030287c1019120799044c411703900c4400b071b103142d5602803c02071858880c1e00440a091144001c1004a6000c61b015940e807042a81d09800c2000741118484402d50800848014011121005480e814101c0e41c05a4801203000d401e86850b00384500005004054410345119400012034401d01c611520034448c08680041c240c15005200b16404440014403582d61510707084c440c0c2d0082d075640c1d1034554401c5100e0000c0c1ca6403009a41884c803101010100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996916339 1250 996915089 996915091
    0x705180904080a11190501091506180902061209010b0102060f07050d11160b0f07170708070306080f07061d01080f0a0923240c070204020f040311031504050303 70
    0x300b82000000042c070305150f9450304545d1804d000040c1844001d02c03080040641010880c684544014180b4060008400056942600a104102c1c60108024141d40d003d504410821400501900c0c030344100d0824910746820100c0e91244d05a440782d0702d280c140e507410403006074030500d0000344070010308220360010210b00c211001c140c88107444103058041c14a616040792034501c0200c0030006480041e141c114038480045a82c02a10001d04000500060140c1002e01f90040803503048146a03954001c00c0d0382c0958050300a400b0590f40e481c021817101400c219003c1d0030f100e62002020760f1450400c00520744c100c4ca41c80520584520480c8400c6030742c102c4031458004500c8400c013100c0c0c0e40c0e103a00c004002c0c4000c0078040d24212501c4c482c0101c01002140d0908940c40ca00c0c25958185c1400d0410340b0b06a00903000d440300c0028a0340001c41410105c0c010b0301c206c500c0100007529108690550103c0c7e074010f6002070711a40c2400000c0046887c0411129070704240700c40c141c175011324040c0c03035103522400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996917589 1250 996916339 996916357
    0x1b02060f060f0d050705090f04230d05030a0e07030c0513060b160201020a0f030906200714030115180b09070215190c0f090b09030c040b030c0603070518090408 70
    0x90401050f1041110a1260001404014100c200c1610380408440700c00c83c2c003554240d40b908045044e02000302c14070342c00f5594074000000101072241480004035515400100031003c41680c0b415840441c640034030402d4011030051180d940701c82c2c1000c081103040030702c0082c00030805240100800c0543c51503003c0d9807103501040d40304d203007071120703400141d041800100004101481e0f15140c0b004058002c0b00e45001ea1fa0b0a0380c4100c424105000c840c540034000b036a840c96194403c103001c02c010820050789602904015002181030850309800180340031081d000100b9210700141141e07040d201d50b1180c0030035080122408050781c1482c4801a40312000b25404094069000380001c1a010440105843c1032070001400c001da541d6210300102440d0007880c180300090305083d00002c1010390b54050f600c484100501070004c1161500c00c000042003080e65060305401190841001980e9880140d4866492900c405540b808181217050380c070340c44a5000340c0309951000034400898214026643c80403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996918839 1250 996917589 996917599
    0x50a0606091502010b0a081501300507050a06080901051e0c090a0e01060305061f170405011b0507030306050402031e130206040902070b100510120608011b02060f060f 73
    0xd407118400f280540b40e000b1095030880407000d8001f070000d1001a01210a2040c030307420070001d0362150050300b46c0054004104c2c0b10404c410013042400c0500f003104204e024429002c0350082c1d42d40394007103001a400350f408500450500810003040e50000e0041540c043c0b40c550880c540e8400b4110004011000940040300c080c0021036001c40d60703100c012500d000350048005020035982c0d20003005014210403a5050300400505c00b0748404d0130f4940c403603040d151025444140f0f0002c8280112485000001d0040d034042d92201081000214035103e101401a110780d12170313581e4a07007800c000d001d035100c55001d1409244100300300504200540c50b190440c1108509003072043e100c1d000811002d0400c00c1000c0d60041b0300150028a550441e030051501900c231744010840303035480313040e040c0c030552240c440d07141c210507030000e8140590304c9003800c4800e045030085c001407041d403079000c1e650131607010400d401c080002103001002c142d501001410340c040e8061031400d080340703020000700b40303410f8401051034012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996920089 1250 996918839 996918869
    0x1502070630060302011b0c1809020a06030b0a060807090b0708070c0b0405210706032301030b060108450307080723030a050706140406060801050a060609 67
    0xa44103604074824104500c050840c01102580c0030009020911049001c00c20100c0c00c00c00c00207400c8480c2d00c41c5600800d03000501c030f10304111118030ba24402c2a102000c2c1d5604050030040c0c1c2c0d00e1b206000074010964000807503458042c144034581d0269000303042404085400c020f15103511401850660f400c6112840d100c481f5442c24603032500501c03000602007108140301181c200d032074802900448100322003103d056106402c08401d0210541c80c070400c0c0c1c0c0c211480900c01e040c060380155418041000c1c0e40d8100400480b038100d8954001c2e0030445181090700103000c0755692104c4000d030018500d907644081480303071080c20840108003481c00b0890b00854400d141035007241010031401a00840152079440d0514036100b0b8207940000310481c0e14241e412607444082c46019203000c00ca001c030b00021894181094000d07111034010f00c904644098442440701000221000490700540c810040440d0042c1041c070501d09440d401804101d046260540c1000301c80d51003454981111030746d482d10409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996921339 1250 996920089 996920117
    0x11030604260409050f0a06060e0303091903050d1e08090c090612120913020f03010b18100216060201180206030c1905040e060a03030c300e03060115020706 68
    0x140103c3d40711038501490003003000301e0718900241c594840c2d00300100c100f06850315108255401c8024040c01c60301548140000d070360604140c400d19510080706c0b6403a04c441907030780c1da50515044c41640410005010694000015a55407010240642540c10405c01c00d00d04022415510201c02c260340d842507251602090803030f26500b91122840d0300c0c0d00280e404c0c02d540b1484918003a4020014240980d00011003030b0f90108042c403d6544000b10504e00d0741c507607441d144203500c070ba8019a0410b10824107502d134594071913681d901d411444a0064000d0300300141c0f5985074407441d4440d60b100c0410f69041080c2c110301006500890281640c1c1107407040d849483d20030300c030364041c060703440111144c085042c00c030780701c203500007010704129524510200d12550307402c400c1c000e152010744002404900d0250581c070000e6400164003140a000122641c1c0512801745100c034000c4180c0e0000c004521443c998038040d0406100241c090220100003010440002c04000d5581540d486400f04008504803c180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996922589 1250 996921339 996921413
    0x311030402060a032702090609100614090a0e0601081005092202040606080f01210f06090501050a15080a02060d0c091d1501110d030c031d0a11030604 66
    0x3c090040d00c08100c17600001c2d210602c0c1250714403005a2080c010200090041d14280011741d20840d8103180851003186031100a507118901c8515403400c0741401d00001c2c44584403180c01d034004105104a44500d03041c01d00000d00b5110000d044419441c0c12070f40d080c8056156180201e800c85c00004d0b0003500059007900b40d800a811402c0000c0d409810044000b0b00290301c48000c0c2c1c00384240712603014090340c0e80d02e000d0030010040800e00e402c035801c00702030102040b40c410468040d24001c40c03001c0b07a04900c2c1d039100c50031600101c1340300091968500e0320700801c19954140501402059004000e083c40035000944507028030171240030155110099000d01a03c984c00e40c40040c035000b20b040d4400c40c0c54140f0540303032180c204c984c0c0c0341031489003500d0300440d8801c0005155a8210b40060081160a0042200a41182180708007415110030300030076240c8402d581041c141280d000a49400134851403e0a114050714040c24070a510240600021031903003041030601085402c10344d000300c42640c05e100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996923839 1250 996922589 996922601
    0xf020906040b0603040c051002030a0e0d0206210103111801050405040f0f05031c0507051603020723182707030b0a140106140403031101110c0307030f0311030402060a03 74
    0x160800c43c0070050204100b600b1403410300f580c0b01214802901c14180a0481c1e0b64000d00c401c0c3ca001450044226256003002e40c141001180040e0100745454140c0e0350700482c0084407220a0342380d0f842c0c0c03c010002e104100c0c10001c0c581500321031040203150390780c8804140403810b0042c50320940c1c0d50320116041003422900807081030b42c40941e0f58101120b506005840340c10021108000034050307103101801c0851407081a00c20245500c1d414100303e500401031024408524040b000c2d8840c1800104140c40402c40c0743c0c916004094034881155014410b0158032250500d50503180e8807030360184401c10500600b4514a00410250740c4106810094602c3c5000010f40c8040d01c9030f400f01040c8101c0440d180c01180080d61000300350921070b660341e2400c40b6442210070b00c0d080020014002480041c2c8a58644001001c01c1400842c034214144400180e60780030b00c81541c0d541d4800160036040540211102903c00788504041041a61300007500c2d10300d20004100074400c4500141c01c840c118000d50005e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996925089 1250 996923839 996923861
    0x60216081b13060e0f01030c0e060d0609030908120c070b0f04052b0b090105070c210905090a091a0108102304060b0a0e150f0102030c0a0b07080a090f02090604 70
    0x54406040c00720005035404020300082d20100c1d232091000c550b44000e8410a405550040c202c041a03400646400d0000c040d14281282000302d80003000900040401984481c088011100c43c0d40b41503a125007403038000e4580c0301203044801440030760017102d0f200040e50203c0d8001c2e5158800c11003491504846a503084101000303c40d0910f80c62800d01400c0900300d80b00345800c8008200742d48810406072800074038000d004201c1584c4062004060148550000d0990002c0c105090001c1d115070010360900713001c90f41032500c10b1b138400c0b00c8400d205a608038409200007101c0061300c43e506041940c0c1e110075140005c41c0b440f684515504031140c607040c414200300305012111310031a091514000c409000c1022155106004070140828144401216075004441040301c140c0035003103417828891000500b40d1250b065000900034201c56050500203418902d00c81e183d41c40e089e24003018041d04500024049408041c07802035950005408480358080760340d012074043c0120380d500c0d0b00040141c2122407074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996926339 1250 996925089 996925109
    0xf0f07032a0801060f0501171f0911091f050f0703050408060702010b0901140a180902090a2708070b10080d050414010e0603190b0a060216081b1306 65
    0x2100744043d0f000b2030966103108140420303d80e9038001190035000c803814900b181c442e03440c0490000b4400d07004000e00444c424018527056550764107406c00302c0344554032102801c580081c865a0713616280c66107071202c001c1020070380e10981c1c10200040043c0101200440c1c4034100041d2101410701500c1079500800000c0111403152820910081c080c02003036a07240c1c010710805002040c5509680d4030410310050191146500604e40381c81d10850300c1203100001c0407e40d5400b11a40583c0f245500c19100c2c02c076003035000c18038a1944110742d144c1e414001103041c0001b1980460030010340f520044072041c50b08041c5000740c2d42c40301c0d48108092002c2d40d0059038684242d0702080d0100e50400701034001c0f5107a40c924100542401001910903103030450b1003540c011170800020708400000b005c000045200f07c5400113a844415002c00c4410403250088805a400040350308400141281500041c0c0b01703910203031592844c4001078486d01c15012031703140d1181c404140084151005580100010095006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996927589 1250 996926339 996926423
    0x718020d1a010801060e100c02040b0904080c0c010801180f1b020d1d0f06130302042a0f0503060d02011707080610020309010f031107120e030f0f0703 66
    0x101e61551007881c8a86022980e42e20001688038080d86c8510403015001c0c040c20015654584115914452404120b03071240d41c0c0c4100307500300d483d010f810910541c45031284965688010101500c4d040151004034100002c0100600441c0281850b040d00203504210200d11074203440100c0d000b03080402c1e0f07031807000030302c0c04440700d60141d00055011a01d62036455940003a01091945041449003501194201c11002d00c2c810060401500510a600c1508003209240c0d07240d034009070945002820380500e000d800e80708161880f640684d08480091141001105401509000ba090b03000041032103202d00110a450708c01e690040840d000c0440044c2901102454002d0028202000035500207006504000702400d1507400002222100c441c1612a407503800b403030500c110060034580b4100400104103100d03c00003d0b4000d805140c20759407030746902c510008040181854052030005030a40c86c0e0140c81407018141e00880c150080d02d0f00100250284480c074207411040a0b006030350507420751042c1c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996928839 1250 996927589 996927611
    0x6020d0e03180109030b160216090c11030306091b090319030206010602060403121e0c0206010303030522060c05120106020c0a0506120708100503030c1e0d020718020d 73
    0x8070050855515000402c01c051103240c00440d0240c480f0b00009140d08400c1c80442e024540a12400c903030130030544111003202d80c00d07641e010f90191459201443c91078640710a490616000728040c10b4088206004500394640740d40001d4070040701a00d40f000f43d03580480b454004a41e04000c445e608000a0200c408082c074010f544001083d241c4001c2e4011f000c0c41001064a610124050b8029030309580c83c51003940240c001340d001881d0300d1880421048841d60100c55800b20ba0003500d000c20b086402503c2c040d0300d1800c002e820307504010b0500e00031080085210854005a00b10450100d410080020b4840d0b15110191068418000502d0b201c1c0500400002c055600080010100da400c1e11044d645503505c0301405050f000da141e01802c6000d003080015400d9100b1011240d004c10103080d40d00d54203540714007007411070740b1410810a039034000e030001c50a6020300010007030140f41c0120085c0039180104100940300d1080d4011480300b0300d03040440840e00d88141d015030b203503091b0b85501080303444902 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996930089 1250 996928839 996928843
    0x111040b040503070b0f0a050c01090b0f041a0606040e091002040e0103051513030305090c190603060f060c0210031e0e0d08070e06072111070902070309050d06020d0e 73
    0x41c4182c2c0d1203449690703c04200030b0054019144c800700c480039140e0400c44203100039102d50b04810840e59080d0340e11413901e0080ba8001403417500070701000d2102065803c0a05103090380f60300b03450100345a03110780030138041203032159021030702182c13485101000d207a00c2c0c0c01040c50034000c0080300c1910a03800850302040c5581140c6500b0304032841082101c0100300e00c0790303680d0039103402256060101ca0b803900d00300300447c1c06034200541c482a280c080c2c400302c0582c1000516481c1820b10324041c0014415010301a81e5010300c02c070b1000e0420400c0984e041c0d41f42103401000c0c0300080d40c009011307945105040c805240a80c21070071190120b880071145070f900c039800c102c0041247c010210023905c5030410744411a8000c2101c103018120550355a040180311005204040d400000100e0f6180e210400c0c020030b00b062001076250090703180e0b49a0340150500e202013481c02c0310031b40082c0685e510411070200000c3d081035803481116001d8814020702d040030304020b03000740100c2e41e403084003604049800c400c00b480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996931339 1250 996930089 996930097
    0x9090903030b0d1112012a03090b04060507200a0809130236030a0303050601020c0405040c030b090d05040e2502100e121b160b040501021b01021009050111040b 70
    0x100340c80005c001045501c40d6801c3e9801c4c08242804250b45044035038031181d09140b4050081d81c0c40c01d01003018221703581c0384079820800f2203003500c0b62036072503041c80005503009040306002620060f040d6507401121010546810f5401130061100c0c2c000240100c407915007000ca600300c400318203801c54480b181211940020310003180c0405080f408012802517000042c0312043e00028094002d052061060390180c0081c41d000c0c20060540c800c0f4981c5502c00d56407405203d02c981d20812524440d070f440d601d030422200324007804012060300103050580210b64080161130444220300c80111168546442030f40040138884c110034030045d669100c0901f813540003c2c1d001c5080e000c1c45003c100030030f90005126141c1302d070341583c2644040c080250070320390340d00b41c0715440ca102010310681d4800784051351070020324980e42e88562180c80d0003003410000c43d80c0500244101109401c405503d00d825000000e440d40040b185490402d503a0341145018050b09500540d10a220150420340c0c0301e45807402c1c03a01c203401c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996932589 1250 996931339 996931373
    0xc030d0c0e060d15060c03020c2413050f010f0c030804020a050a09021b03042d0e01120b06041a09040c0b0a0201090606091401170a05060a0903020f0c0109090903030b0d 74
    0x118021000485d01d00c0b424554030000d416038003521007081240300b04002c107000084001001c861102d280c0b0119240c0d01f00805190b070307426604034201441c0c4000d1001c1942110f5840b810300443c02d50851045400c01e40444000d5031500d4200c00640d2144000307102c0c1103961b044181c03c0301c00d070352000c5441600d5500812054203407084426000a04800c21035881c131960184008031092250211411049012540010040703204545010760301c87c03255500b03401090707014050500d85400c18a0038020440803642c0c02c000f0684042c0050010841d0214040e0040c10300345016800d000001820310180ba20ba032009807601d00c1460355580404c0b8402030180c00e5003002a50110318000001440999038404c2c9003c0f00340c0c2d4110712003180e2805034240384461500c0b8000a01d8000d017604000024020301240340b14581ea003c00164140c12400d0007482c21024481c00740b03c9500400c1d003540741d680c0002080b421550090804a011500d070f02c1d044010309411400c05402c100c08545090810401861100c3e01003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996933839 1250 996932589 996932621
    0xe280e0114190b030307080a02010c080a090c150203070b070305100f030b0109020c10020c07090f1416020c210d1409010c14062a0c030d0c0e060d 64
    0x40c0e190340e0061901e090035075403074120003a84032100d03110640b2a00a07499200f8010f00366400c2500e1a120b481903540100030000041c2d40d502009004103800448450b0086503e0030100246a03450b502c0654084e82401510190310940301e042103114030030021210015400710304c04880e070804010150141c8000e48003400382c100d0080010031003030810605241103d400c240841140d03468072105030b00030351001041d080c26001d1422010034032552800104202e816100c01050301c9481e08480c04121180740c6040c00d1007a00384585040325080800c540c94104040e145850901c0310183c0e0140c2c6400c800340400c54202d4003201e40c00006049000d400e500402c1c008041d91958045010101c6445000003098102d891084c00710702d566510401c1445071440c4550014591408602c090900d010800c440c0312060f1f0403010103100b0580d41da81045403400203a1010a414074070513050054413401010413200042e07a650b0b01c0c0030040d07807251411083c0621701400300307076039240c1c1507080030080d203440e030407421601e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996935089 1250 996933839 996933851
    0x13050907050c0303042003030408280302100b060d0606120507090f12030203041802070c05030f0d030b041b0c0506130b040605070e1e09010506040b040e280e01 70
    0x36501400441d5808482c0c1c4029500c0c40c1c1c0d4650398540703014482c0000c0e2240001e080036014003a103007040280040c05125000704124051b10f10046c24072410030b5031402e0381e68240d082c00c50009800185065001c03034403880103e021307616040401d5103401162180d102107400d01800090194100c810540562103290007070115646000d820303181f1010074450300145120228081000c29208040311018078441d02c1928641aa945110b07a80040340550308108a0f070b001a840007008003544405c0700030041640a4001c1d038550500c1d403901c0781040b90a1401707042d220441d10403107540e258000070b01050340b441507483d8940d103a64000c2c90400036070303402c0f01c03640f1480300030034185c151031a2181030f030070390140180c880e07a079031596000c0c040c20016001505100047d003503001c0d9a518107924504000c12440a0400b507080c8004110600e03406a018501030070b0304100620030031091904950950700c0c0c13134560f11401d84800503500c410100c8080021104480c07083c103ca50114550400090310451030000c2c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996936339 1250 996935089 996935101
    0x120a03150e0f0c07021f02150103080a050a020120030103020111030306060d020703030b1807031a030307060b0a090f02030a111c052d0f07050301030807110d0602130509 74
    0x4010090080000344142a07000425204012030002d5014a903041440d0500c0b02c0c9a0209450110003070b80501d8440c04518402031055042081001e4000411070407034041d4035607201c2c4010b41c4a00d13a045010000c000529010340e900075003001400c24a028400310070a0f1403003071103101a030002e0204078001001d40086400650b000410340e4017400c802000030340340c2001407114500035403216608809140d281c48180740241c0c1c6202035800302d04101c1030400d64528000400808454141d01140c0381c0c4840b0480a1056480020a5800300b5500c1840041c8c05080800040d0041c40c3c203500000d030a0b030030038040340036503203940d0003550240c992a5010711041d101e05c0014507860049211a0b019502203400400301c0b01b05135002113070814150b01041000344a21008140d10300001010170042c10f5406060112400031249201e520000e01c2c9405421035065541d808024407580034042c1540c0044d07501e180300c0784d079000400110345038400002c42d030301c00b030407400d015125025100d514892075289002900c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996937589 1250 996936339 996936371
    0x1e0302060d140915150d02090a06030506060d0c031b0b161209062f0d020c0307060806090a0e1603051c091202060d0b180a05011401200c03120a03 64
    0x3c10138684200d81000d5450042d10502405d2a04407581d00080c2c1c40c0e04174016803030b19003d01c1d000302d0a000e8007258403800c50400314680035010301410700a01c00c2d5440f50007c01c120300c15420036203034010481651448041c004c14410a100d4000003881c5400180303c1440b482c44503503411940b4494040d100e0021401da40a50711810188a1744000c00d81480003400d24407005a5295070011503020124810703043c485900b0f10708854151040d000d46e200e9a41a000c0d49002c100420040000307141c0700400f403a00b00c001ca440100094000030241c0e45608914614010038400c6a11164441ca01240a1940c0e410720aaa0f00d080a00342e000c08400422000c0c00709106025250688200701e20b00c48980035a942808800e6100050040751a0b40c0c483d283c06130b543e50240f5190320116001c2e5180450304205a1880c111001030b40f1041840380302d41e26182141e42c00040307000e0503074114405594118024551542065412400c00d9414018030082c4005000003c02034002c0d45001e075400c02640075180c08802f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996938839 1250 996937589 996937603
    0x14070611011a0d021504150306140a031403070f1a1503190501020f040f150804151a0a0609081e07050904030c0c03050c040b030604020a1e0302060d1409 67
    0x6180e18030190090301060502d48440e00003c0c1c4003038000141402d003c0e4080205800c07070342091254a51401e00c1011241d4036000f0036010705002548601c0f080642c000085184d001c41c071000344001d59114482d0902002801079512094211450070310080c814072300702c401095000204808840124007082241038610380c40503080c0c901030300501c0c50f0846003c103110003d5031880103c940c1d6408020809511018002610042031508840d10559003801203008086143d40c10b034404110074482004041103002c5001860f20000e480c3c0004d0b04681d10b841c01000c8609031000e190441140180020745943c80401c0d141101c01e200296212108140c070035000d00000813078078198943c0809418081d40c80d101d1140c54005100f0b08104066001a40c0c4051510f41e080d4000d80b090f4000c042c40034101e0074180902601ca00c0220b02408035407400d580020241031481c002c07500c6000050000510b0120640502c502a40c0c00034040d90311580030421441c068514104502ca42c00c8070203010910b48000080c0030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996940089 1250 996938839 996938861
    0x91507030806061c1e0c110604060506060903031c3930050604140f0736050303040612020c281b050d02090408071407061101 55
    0xc1240e10b4820801206401108140030002103890005512030081e1040000a002c11190503048148540709441201d40c04801c541c280010000c0400951034086001c9502c41d034000f40026031901d803640404e01e0f031f01408a4441d01403000048201d83e14401b500580e0541c14200000c4c441c0340301e00041340a90b61029240313445031000341410302c0c00f988861842610100c00c103140c1901b000068003106070340100c1c24032101510807003d0980310429005070140036803001b815202071004401074500141000c9005222050724501c500110300b2580c45100c11700f51001240c11b145000030284104448540e040715000000c2c084051800589401c002c800d481c21581a0b490f50b190a078181429000650b0000d00329410b00d0159038900e5180f4214641303415020525816410a03100151030301ca240c10b4000c0b4891141111400c0c1c041212740d540c5640c0800d91a03064030020300f03e03201c51800c03281034014404000e10504c0c40302c03100740002e40c001030100c080f0358566031010743c5007202e4000a0308035200741d148 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996941339 1250 996940089 996940097
    0xc09040f1403130504050a02130f0f090203011a072103140604051506071703040c15020703050318030102040f1d1501021504020d1a1005040204050a0306110c01050106020309150703 79
    0x70800c500c0d003603100c1030b84100b4191f0058a030513540e42c45842e985001d904010305500240070700f13120348002e21131100c000d0020404c1c21403445d4180324600742c00c00f03424003c00c84840d0300010100c0c2044039402c482c19a40c012030f00350340c04039040703084041c0142060702003034480000003000166092a00d07001c4d05018403c1907440d000500c4122042c00002d030f01018055481011444419451481d594005c0d0310880c0540c0120990605181581c501c84002c200c00e9821580882c1e03060020410220444121000c407540705491071541d140840d001e40210b50200f0030103d0628400198103200080046450b00c1c41e000c041e0781c0303955a02d020548800100e2516006910100c2901c4108452006041c0c006000401203400d4544550342c00e5882c0200c00141460902000240030404c1116008000900360480f0117500f05402c00005c90003986045c0320190080d0b0321400300f419198a00e00489107218a0344000340300940c3c682e41e010b540c90744841004e50052010711003e100c580500b0017a81c50711540b42d92 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996942446 1107 996941339 996941377
    0x8040c0b07031e03090b07030e010e1002040509070215040b060a051207081c02151b0a0503060f0d02060a0e040b03030d061703070519050c09040f1403 66
    0x383c0d030000d041c1000c210100007000041880da10081d580340c000b0b6283c408203030b070b140503022102c9403005900030002c1a0241c7c1655400800a540341614442090b80712403000300c2c4e4174280f03144012200124900818001446085415080341005144401c261b4643c030004420340094642560f0360b17408440300704926041485007103070080568007006403505040b000a515110018040300d8018462070004100e00c0ea00c0704241042c2c5200d11110b516018030207009005caa106179900381c400d45104100302100c0c50101102c01c200b03640945040d0400b8000c80055440355103014141d03902ca0340303074084918503490820181451001019000c2441032400d1603002c0080695541603066410811030480854030001d150300310708081511112201081d410300a09010385204810b600071003031000e21043c000b0780c00103110b03400c0c01260500317120148551650b540380301d0000c103400b8031025a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 996762589 996942446 := by
  have h0 := BRFrame.cov_init 996762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996762589 ≤ n) (h2 : n < 996942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
