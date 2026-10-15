-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3847
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:51:49.291984+00:00
-- url     : https://prove2.me/submissions/570686d1-7c4b-4382-8718-b1953bcfb5d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691726618 ≤ n < 691906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691727868 1250 691726618 691726631
    0x1e0408160b030c0304030c060912030b120102030906070c0f1b0603200906090a09060602070501020d03060b03040809130f0e1e0303040308090f0a0503070c15020d0f02070306 76
    0x500a4640420100c020358403860400d01080c1c9001600603240b094a58107046130540d543e549040f25514144803056801680d2240e80d2001b207081491080074041c00d545007c10301483c0d030414401001a54010030003141d02c140107000c2d01c118041130594114141d45810010703000e590500760031444411000030449001600c5a251911042074942d0484015803000c00c51a100d00c815201070050301081481040010030030525036142c05000780c02d0702540035000c91100380d1901a83c00448006170010800742e072000804100c150ba0411543c1b4044c0c5580c45d06018a030b1034442003408034000540000c01c02100800c0122141e1204c200901c03110311007e0b0180701c9246030f41d044030000c10510448542902503001c040c0f4007803250500c038081100042000b07501d940d60b1510200d0340050040d2008219005076041254010070030044030100c240511b014590703415841c900103010780041c0c0d1107096251402da0048030314680200700c42284d2a46030074000703002004005c00324107180094000400491030700e40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691729118 1250 691727868 691727879
    0x5031b1608060a0b0d0f23010906060905060d0c0506160b070905031c230c03030a0c20030d05041104060303050d06080c28090e030a1d1003021e04 64
    0xa18140100f00c40f100c200035456452061050001442001411841c552501000091100d454030000400541c10005985407620045429100054000d40f401911104248000c660510503140c0100c0b088601c01c450010075a80c295103004584181885030034007141101810007a50041001e082d8400014100c92500c2100035050a40354020680a4400c1d100d000b02000110010390007034044540341d000d60003d040c8080c0307145003000d403200c0b050a1010b2108090108040001e14002c0348519000316088540010042c184140305000c0ca00c010300c035910304c03107010401004944801c90803102c00b10b03c503580c906000890a0840400b00d4001e4a008000414541d01c030b001b400442c00b0705001806080c0c0e41c2c1142c240d0b11409402e44681c08a017409001c0030104070842094462007201c080d01000d195640303060011a01c12072481c1e852038100044044503507038040e01142c60309540780c42880142c4900e0340441c030700d16490858103043c503600103481d9607070703911403015003864003158026141e445440d139 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691730368 1250 691729118 691729123
    0x91804050607050f09150c0303100911040b0f090120030a080117031c06030614010302030c0102060408091c0c080f060702010203060312071a01092705031b1608 70
    0x45800352203600600c40407502d003900c00d0088584048500e0600741c10440c000041108a0f080e10895825003e020080c10b01150002d00c0a9840b8441140c1a40130080c50072029109546020b1507130000c0040800c0140207101481e402d0b14913000c4403100d10f0fa01c0d00303210070069030100700001d901142c02000d141030100d070b00c0001004010b03000720343d91031070700690341c410514200c10103070220311011b0f40040c0284070706945000880e003421706000d480403941d2a52511044100e540d10200c1030580b2241e1001407007581002c003d200704010080c40107280e140f800d902c4400340d901501a0040c803c1030701e156180007418801d400c00743e10a070005900c503c10382c0c2c2d801d40603a4504107201d25000c01d004030700015103264011b00c2030706d01c118006030103400104c40e0410751070001e0344000c401302c0e00300f9640b201131030950303201c189900e0103881c43c8100052062200441c040e40d0608119640c8006d00076040513100140303000c0241c8e42840c000755082142c400c6444102800c0021400013100e81c005107050004002500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691731618 1250 691730368 691730371
    0x91305061009080a0f1a01060e040e0615041802040e0d0201150b03060603040321060512160302122410050a1211060c030403291003080a03020918 64
    0x1100e240103000d00c605416140c8564030b00c500003180d04184c0d16100440c01c5e1410740150030380305208961183c805980101180b1070283c101a00140410321a0312107070502d4840c200c0551410b500401940c42c1c0380c8002c00c1c6141090400600580c2c071420801542c2003c2e420b0b81c00c82d26402442400040c03801008190303100c1403045280010340c00d150000c2c00e18245009072406a990703100040c2c0ca036980d0b90041c07084503400900300b10304006400780c10010250510f100c10000c5034010b03a02280c014a050700300401c7c00c500c4821110560070903440612400108103d1000703c0e5419240f034820311100c2e40486042413000e0072420076148811468a03000d401d42d00b401032107860001c41044140380c40e00203020114410340504102c0014080c01d0101041c540300441341d030000b001b441f032803900401000b860b0464015500c110307191200910030b2528840304d43c80d90710b600079000311000340910b04018032000764072051201070511000018511050381c0300b82c0441d40b070180003070022511020060f0030030254a20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691732868 1250 691731618 691731631
    0x6100302091c0b130206031302011701171018030e0d020312070b1b310605120a050606040308030c070b040b0601083d030221060a15090c0302091305 65
    0x30543c00940800c9440045030849900509494159500c44121601120100350180d040c00007040c224021090f0020a45020340507040b04001c110140404051800040409948206040c0701005c0b00c06220480d1103142070390149001f41c0d031000d00d100491040341d00182c019400d8010340940590306a000300091148500c1010390362880c3d5100d104241183c0c0092268454844040105043d8180b403484c0d0309102e401c0780103010b03245e003213045400b40070030413664840404500081984900380041a616503881410038100b07100030314204000813030a205501008185034400b1001c60740900a400a031800b203035020b8101da0060905c1c0c1043c8000d17036000c45285000441a40c005600c0722282e00c00002418070031003828584419881160126624952079002c1d4100034250020142c3e0b20207101e00b4180315a1101e515400c060303690024103100d0000c18a176225801c1071945451003064034aa14110784ca4900002801c0c082e038901103000c3d02c02c17103101e035500090010040c00d184000741d101501030103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691734118 1250 691732868 691732883
    0x15060302130603060503030702040207060b0918070f08030304060c0504080303151516110d0203030d150b04061e0302091f0e0109051f0c0807050c01080f040b06100302091c 75
    0x1941c81d0b604500352042070240c1505030708240100030040c145134020744450303403040703a010501c10b00f5000412401e920072a82140c0c0380510704003601040b0310602c0706402600c00501140341507814141e140341e0b81e1101402c01424181d84201100d41240714a040d00d000d08000e1099a6032400c040c4003030403500100c2800395100e00d00450b11442049814011900c1316540c0348103800c2d8400480e01c4420f80607903000061034021024070340f4040140d03070520052010300002a0300040e8003070043c218045615031504401c4501b9020441400303103903003041c40c000c036107999070307010200100d289a81180603008034508641c00c080c070181c4c1c3c2824002002040001400f040d602c80380002d4000f801120300c1c3e019031207200d410844944040700d41c40c202043c00307800075a007402d0082a50701903aa0300803043d403101e50142c46517041020028003640e4801003043d0004e8641c07000003414141511402141c150180086d44130350b81c41c4280c05aa140070341c059890110008210b0040740c2c010340141c07602203112400444446 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691735368 1250 691734118 691734157
    0x306052110050105131508100603050705030a0201020a080306031207050321010b161b03050601080106090c050d15030219080f0d14070602090a06110c0d030206150415060302 76
    0x81c2602d1103018100da00040c01510400120342c0c00750014401103050b909105810117021903641e100300040c2110110001c03002410b00e2540c02c101d0b090400390380005220381c1184102c000940e0340015540503054210101d030343c0d29103034500000d03c3c0450000036107454000102d0314009202010002d050011440b07415040c1721b80030310020010401090144401010050107203040110f1080c4110560a103d42c000060840821480780c0a020341544201d599611140c01409040350078005c1c007004110740b42c014070608a600d00c02506a0180300617000a40343d9543c90150702240c0341010a0003503402034903408480400424040180781d8a00034402c072031145400303070380c50a500091410b1100744240d84131000007002c0080c00715036600091003680d44039000d0200c04044ea84281500c0001c01c0103481350702e8a1490100d0007420720b0741008019114142401c4d0141c0030075008210326500145504201c0d40c84240350740043c1c01003010611201034480289400718010b6016802019a514142c1d501d0b01c14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691736618 1250 691735368 691735393
    0x6090703050423010b03100c090602120409020d0b10050c0712230a060c090302130203090a06110d180201020f1c03090215120a05091908070303060521 66
    0x5680c400d840090100c50580364080c6000c5548882c1403410010348004510700c45c00c1000a407070545c1c0c11141a15440d518071000e800181c00c07840c810001c0030701c0c0c0050288000d41c5111840b00d03010318440c0241040c1c0010f01419110010b034007070304940c1c0c0010001084c11b80318000090040d0040740484a161107020400314480864145000c01c480c0d000503401a044035000c0c0d0102200204a4400789038440ea0f10032100017010350142e146410110303540e2850540c55401000807468800c0703440e034030a520400a2003241c10700441d1402c0300c0354010700041002802d0003032030700d0207200314107402c01d40340e10301018801c20004507446a1a00b070b00036802c8408412445001940355161041c00e65945210903000c02c41c03048c02500038030f001c140020f0205a103130a002030700301403550181211900c104001c5040144800c014490190409500c8005040c0140c0c2000740c3d450074010044058034080001c19440e0826201c0e40055015041c040e102070b450f011540c96055011198654002c0e0600543e01003c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691737868 1250 691736618 691736621
    0x60603121b0809120d21060501021005060303210a0b010f02060a090804030204021206010f0e01090605130b161502032203030e010501080f01060512062701060303050306090703 77
    0x103940d4101c0ca54002a0761403400c140e0100c1807142d000600c141c40562003400c00d0181050504058403520000002c02d5130701384101d1a02484806800e25180040c0300c1c5036400620394401140800c00000c1c03c0d260000041c0c80d41c05500e0740c2c40c00705d04102d200485405044001603020b040003001c144140280d043c01502e00054050721200181d11120000300c2460035900721b009a1801840032501e00f13070300c94000c03805036408100e0141d1008150070511400d542c2c01040391100701800e20340b11059850341c40c00200104090700c2544200700010902c030155880c0e601a1100074400802c00700c0d0350710240a442150000785038429a20b05000058540600100d130085070712412608140c40d815a052082080503c400040700391304240d590150300c000901d0910402e4040c018500c010301c07417020000d009a0a40d040344e00302034000d1071040310105c0e4000000075a503400c0b103018020015500902400c19400081712010f1550304d6081200c00414160410000d5000703840076111090380d940c03952810340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691739118 1250 691737868 691737887
    0x21031b04180f0902180c09091312090b340302010902100905030a060e0f0708061f030c0512120a051e0a120b061303290709090f060b0706060312 63
    0xa4005d00301d0780f01c00701d441500307010311079010f80341c00d4030207040c004070b8030110704000000c030f41d4a01c030342280e0003240781800000048040c2c201c00914150350120f0178441c00701298011010340e1403202c024207a000d07005403813541d520b01c030300c0d1002084840c643c100d90800038060000200142c2c0284907482c03188401c1d91140c00170344c064a1015005200551613581c4800080a406030000780398062507480c02196101030100314010609007000b05140e0400c0441070009100d8500b04520f02e0b04500030400000e20303200c0c422002c460084a030b508813038502402c8030341411410202c0c0002c04000041220809402201902e4410948900c66800350b0140740d5010407407044600c084081540c0c0c200c0032488407060740141c04000e40261a95040103081e403020b600071010798004030762180700000000e1800e05607a40c10590611a04000c0482e4201580d019101407030350301400895944446803c005c2c16402d13080000148204c401d07640e6500c10700d0908a0080282d03000c00c8804122603807814049911400c00341c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691740368 1250 691739118 691739123
    0x1e171b070303090605070c090e0609010e0a0317060d0503040306141003080711150d0e12030f071112030c13060e060406080406090816030306050321031b04180f09 71
    0x600e4080d003001405d45441d040b90340c5c1240c1c2a40d035a02c01090400e5580602240d4401c0741000f8449400c0205d4401c2c20b441c007417145c0305a01e922140c001c80c0401d03480089215150843c0301c02640070340b15000811881c1c3d040c4078000d8007034031000030000100320007a8040001155908200030140d254090102c0d4040d20521001d080184144180004540c0400c0c001d9403201c4010201034003000d42441e4004d00342c20034201c803046280e99044441480318280007420003600003030f044a1952915540c4810040d8010b4140700c10494640d142000d05403040107205004e9545890094882c075200783c008100f544810042030806d0021000000c0a80c064885505204002131000e400e1034184007080b40e46035801401525929107440c9240c01054854005000c403400008a00200e10507600b8090240c486980c0818029072041603000c11a40e640f00700d920182421442c80c03652516034200e6501c1d506241030141c3d031828000900024060707403e82c01070800c500c0c0298107025995001041070225510181701 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691741618 1250 691740368 691740377
    0x81612032403080d0b04110901020106092c10021b160f2c010801020403020a0b090307050d03030f060f170114070e010908150f221e171b070303 63
    0x1c0c07002440383d0000d02454524068000fa6082c02040040d054070a000f007a44401400014400100c1d40e0a001d2900a04200c000900c00010030200d1010304900f20b54110004c110f40000609d0008009c0c490303c8a010030082c01551100c0701d00d8140c0c03211415000c0310007070034818002c10480d58041d46020700c0840d003030054039410f41e0b4030b0551101c2c4c0c0840911005d80b00000815203201a2198a00c0b42c10701800e421000183c0325811403040c0200c0f07c0094104c5504c41205000c005450f58001640301e060b01d50980d0782d012a04014074094000c0c011116080b074a5a003071440126448658036901c00845180340c03095030b4207001042d0f0306030885103a51100f031200459140024015800303400c040078035070010316148085030380d104c00c854180a51a0706001203c829a801c2c440f80801003906180c02401c0f100b4004141307200c94820130103031780f030104009241d45421501e0300c00017801100c8118130242c01521102c41d03402d401200c180141c0c840440440b000b103800301081070800c000110401665459100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691742868 1250 691741618 691741691
    0x1615050a0510150e0901030b01092406030209120d0804050c0f030a300201050702070501080906060904140709051f0e07030509120703051c05070e060708161203 70
    0x181c10303001d03052582103d01031241907941c89801da122006941e00860044000d071001c0e504001c4040207542506a41031100c2043c81c180035480c91110419004944403410010ba4451040300030039000b0140480406050207510003105045400c0b0318076600c258810300659030416520790800c00e00764004081141c06078080e244a40c000340142d003034904d04003000e038810186419512120a44a440c051074280140d4440f818451500c1d01042000041c00c0e003424410800c0c50b01030821903440c0f41c010035091090145501003001c0c0a100594201c9400509054030340c01a100d20399640940b82c251100302554a0900c191954500c940303204805607652000d2604c001e8640c014218081d203009095000e150050003810350b89400f905c0003c1031b80a200761070711070322403c41e141408203230541c0310100c00685003070504020800743d000701030030509034048958a8a46080341010001d50250306d08814840c0b1045a145003400000301c1c01d40c03080e000c20380c3d0504c0b640c2c4200d0420412554034690703401d82c0f29520795 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691744118 1250 691742868 691742879
    0x1e1407210207060b030703050f0d0906050a031a031b0a0e0402010c03140c0601181415040e0102041d040506010602011a010806180a0e0d0c15020903031615050a0510 72
    0x40041c00c142e8000c040c0421013801c09030020341441c40540c8105c41a502000d40100780032418003403107106081038108904541d240c2000540780f81701d01240c00080542e02c2001c2240e034500c203a1040c401f0b00025086404c00100940302d480c44000c024401e0344100f2052500080450030b1414040c80b69a040e59950903800355545e05880038080302c2110031000700d0901402c2010038007040100e00030701c4a02a007041c907010301304644041b01c03181000e00002801c20f40400c420400c118005500111058400003100004001002e0080c0156007214582949030f220700c2507921801c0c20f005d0f006501900603640d903a60394000903800ca800e003280c10707080003a2044140d0002d40c0a00e205503801480601104518202c41c0e40a010034a0100ca10b200715998030107448610311000c00c25000107083c50304107000840f0341621900a0144803440007003440360001108421620306105a8640e10410010704100340c845181500d41540e5608200a0840c50040000c200074194041c00f03025041d030000d032140075410207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691745368 1250 691744118 691744121
    0xb21040201170f01060e060304050a03050f07140f070b040807090f0e0316050f01090c09020f1207020a1205040b12060319062009010815041e140721 65
    0x1082030707060040a50030b41d00c04152070307001d40d40b0030300703100c01550b0183d0f04101e00680f440c1105980c080c0206001e02c2040300140380041d44886032a0141000d50329208925940380c80c13481484401825031509201440805000103005038400b800c040c01e0b00c08141c0c40e0300e2811118000d61050390025030056104000c48007c6602601010711290340204030084a0007200780b540e40009000c14540c0040c0a8000c2441028010064400410b000030720842110b500d038000b40300c64a005642c40a0790004045007a82c00f200b08556038403d204140f84054900150082d481d96540d00c001d40311a0920603010001c079105008544c01da602c145000d41c10251807491100ca401c800500f82c0703800d032255400300003034520040015010b0710f00c034820202e025485141d1011035405200754400d4280f40900800400b680c01800666015070700503d000c0c001d1240000040141a8018081e04000c0b00c11401c24813201c0c5541100810580c0c2c64456000354480d000d0803980121030341141c0041c103202c141d0b07803845403015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691746618 1250 691745368 691745371
    0x1020f0a051e031302131503031101060509040b04030201200a031805030f09030c09060d0f111003050f0f06030d0302071524080a0206040e040f0609110301060b21 71
    0x600707501e8525200c9011200000c3c2c0d1095588012074104d08a0500440c9031901c07204802e08941c650a00114010010744542010140401010b00c507854007281c1a402c025031000b801800c004201000f030b03040c20308021020103070584041e4015401c02001e405c003500e0405a14900b084c03941c00036803400c400d06004030010240b071411004404031a01002c404104104003a00c409072010b0b003600d940d0304058080600d46000074040b07602035600c200400406a4608001105294100c0802902e0405615040405410550b40c0c141c1c000459160184007e9056020310301c2176443c98440e03205a10380c1180c50503030301800c548069040d4403031101e403206d261003a00a00041032060f03ca0480c006a014070340026580710800216400000c00e800f046110084191a80103160300c0000d41183d2600e40c020406510450040070142c0c241040400c082025880d0580c8078950440010011512185000c8000c2411000400d02c40c0d8208480800d40c2c0c4042c00490f080030165011950120903081e180d810038140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691747868 1250 691746618 691746637
    0x20301090c090b01170603061515160c08011b050c1e0c0a050d15021b03120109060501020c21010b2e050c03070209191401030b070201020f0a05 63
    0x12100c0494001550401c010005000440340200e041581500010000e07000b02440e000094550000d00002d500c02080641e003280314002101c5240c06202c020501e41110400e14281c00c0c600001c054401522111200180034411003013a0146035484030418260b510403000d2517808a0703d0004503130010b0042d001008050150760554942d24400e42a0003070400010381030310711542200030701031030b80e1800c031160030043e10084550120245050300c829400d08410018190002da001a98a4403180c40d0001c03448040302c00002c4aa41c0c500300b81e041c0001036002e118017129141400d0002c922903001050501078640f018214590b181003808481d03445001240c802c1525558070100301c1c086488444100200b29681805c82000d00c0240e80c0490340b09500001da0020420140660310407110007200f144c11240d01201c2100c1c181e01c40682d5040104c02c804442805589081050711014000302300a0341280d00514540c00345030303610002a400d0b4401c5a40c503600c001c0f0100308414690380202d01407c83d00d035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691749118 1250 691747868 691747871
    0x6240a30090c12081b0d0c171e09150313020118031703010810060f0905070306090615021b061909090606050309010c09050f04090204020c01110c12070b070c020301 72
    0x241d5400003d0b022046071030040c0c40a890000c0c2001c4a070314006107142568045500a1110003a0410014070300704134500b000382202101004c0c10f104081c00000d071062588035058016801c05525411065644070700020741c02524140c40603040c19480d002560700c58a91041c40f003260032900d45c011258840c1c560705034480070101d035102201150100e40311284140264111540e81d5042445862405c0ca00a08030b081e40d40c1403890600180d41d441c4410400c036404401c0c0031400341c5410000754003a0040c3d800c059140c030b1400100145101c0c0c441901e40380203909400741d40705099108101d403c16020889920f421000c1040f90742c00c801c22182c1d1054054819240120100740ca6008602c1039038606d9210b07100250000c82409540c00080c400e10810202508182e0301c09450003011850142c2100a50744c4030319945c210200a544541d011103000c2c0d5084d000030428000007500c150141c0e000f00c080511030b442031045580f121404074080300e00c4560809030442550361040301c1210500e6200c2da0803a09035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691750368 1250 691749118 691749143
    0x1b0b180102040803070812091609090618060b1201061212021c0f1d090c0a23030708070503010807050f06360102071d06240a3009 57
    0x89001e0014002c460711800543d03647d80800032581c44100c001400810881c0c01a00b205903294040768001c6048400c10840070a05044508105d002856200050300c0c41d403401c4d150007801c101d03c3d5406510342c034008640d0a02d000c04900c01c43c1d802c0321350b00e001d10386205082051400104584071007034a05908144116105d03141002186082303201001c0b201da0215000741d1000003101c0e009010b20010380c851000145183c070b010b00000e41c024501400f13070101d0740400140e0304480c903c50422124035500905003125040240c4949011a40c4102da424000a1100005c900c4a61003441141e040390602001040d5682c104002c0181141c41e03203100d194003130b4041110002e42c0c0701d00c0384901041c0501943d076400c42030084000c908580a18945141150081107091184c40c208214603000e103440701100031102d6950101182c42c0340f64002900303800200007000301c865500b1920081500c25132544d654040c445a0101c0c4104060000b840d010403d0030b0b468880803120308903400a40d050b409050070406c40b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691751618 1250 691750368 691750379
    0x50a060e0d0609022701090f14070f021e100f110f1303060609020a030e06061c0503040905091b030703080306060702010e061c05060306060307030201050a021203070f1b0b18010204 79
    0xc0170402201a0f0042c00c030344c1c0040100c41e029205109880e100b54400340f01d510000d006101d01203000906039000e100d206588504028030800c0305001024501c40c60f00c06508210007511360381c808000c08241e51301d04080021500c3c0c25203001d50f800030080707001c541d400e110041c0044510f51b0031500150140c1605000000080303505030040310003c001403040107940d41d4803024010256402c0c0b0f1500da03141c2d8800c4051203103a0b200e286200c91404c400817448092406e80f4680356086101c1c603403240600c94100014450384203400300341c0c2d042664041e104500402c0b1910203160300c0320380c40c2c803000e019241e0910000c0c1a900b0504c00501c9802d01c145840203a068080d000210303550032030301a1001005804a01c0c6a140e01244241904a9012002019039141c44c40010b41c0d240f0290100031304000c00494003401c02030080090b04000400444604d23102d20b00000c004200b0201c42100400003280154007801d80c219150701c43d01085e4000c0c00c421095569901088410703403c0101c80800b9640c2000b00240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691752868 1250 691751618 691751659
    0x380301080a0c170c060708091509010e090415090201030902130209100807050f030c07170405040f02040315240905060a1d07050f1623060705070b0c040302040c0207050a060e0d060902 80
    0x200b042e1010b007150ac460761100010419903804507510302038541c89083c0310205d0200350310444460441d20000c5a10389032440120301402d0b603850000d400080306481c803d85c401d401d402800d0304080644041041504240040314494000c5c4c41440105800704613071503900708204025603009120900080c90940d540c5e45181110614810100300004046000c1c01107141900441084040c141410742c1818115102c28a220407640001e80c10290f0784d4542e17882c011549070000321403610a01120201c141d4904070300b0f02801d0101c2c4c1c001e01c540306a181c0400c01140c00800030140c50188840110556647d6334150741c2603009100e041100c170418810010462a507001102d40184030301f0448a847c01074810301d6242080c0c138210a605c603080b11040003843d40c2c3c0101644d2449422007080d008545480310f0300e00052180381c002035000350a000d42c1140044c5c0000d2080202c0e44151031401146940e010100c640300c006030f034502d0348181184610750100d2080d030440d00d1468001003843c8488004c0764160790 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691754118 1250 691752868 691752889
    0x1014100c02060c1e0d12092402071a3d08030903070f061e3e0105060315090106080706120b0604380301080a0c170c06070809 55
    0x4095003c01c048940160030ba29200c1c4c1501124030081901300040e510242010204000440d42e01d0741e00c0313083c0c074144420300204d80003915081d0004504000c410100602039488100c040d00d010000d4880e0303082c1c0c1c0540403107507882052504c4aa4005850041d000803142c40e0200002c8090b45407a40514140108501d40070024a129402942d9030f0b2185001d00d81841032650020142000501c81000040e0b080582e1600e0500728a9000806d001103110981d80305c0c1c0c803a984100130b0080304410074401d08540f00103503060701c01d5900000c0c464800100751406d884040303030741076090307004440c84641401e8001030070341c1c1100300c510000c03c02540700e034245460000242e003c40001183d0f0030140040b51258480c0d0703200690b09032081e82c901800d00d0f0840007081c0c0c0302e244080d00045600c10245200c9118001d00c41103400e180b103e070395656903606000b907450100c803001b61208039103004002190240314100710041c0380c100001c2c1c802d010140080006c20f812171030080e621301c44100110b450b00c0e50b4504460 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691755368 1250 691754118 691754137
    0x402031005130b041410170111190305100317070201030b090708060a09060b0906070305090306010305011d010504020a0902030718030b1e06030a08090303070b04060204030b1014100c0206 82
    0x3d80c54408804101c181c65500c081e4038403140b00c5400f402004450050401c1c140d40d440b4003841003132010b080645005007801000c03559100d002003800c031041000b24462083c01340e4180e500744150348560f564030700742c070b5903d202c0207010b1034147c44135040d201396000182017000e00504000070b545032000e000c2760300e4072070440c1c166000501e01070030880039103003140c0388801801c030845007041101e0500f54200d031144100c1031128812140881c5a00c00c16105004031405818050165216942c3d0303451701e1800f802910040001703982100c540c50195400c144200392050f81c00510b907080041c80d1440e294002d50000c0c2948003041050014000181a14050b0030000c41c070400e840b04031484c00410640c484820911241501c06e59071040c0640340c0c2e000201100d840380c101c91a03d50300e0750034000203403035442620402400301480e1401c000502c5015405001100d0081c9920310b007540c0ca0581d07400c4020040e019182d0b10107480e038604000c074108054210307406015802d241784c0e5411035030002400745d00101c240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691756618 1250 691755368 691755371
    0x6081c0828140702060709120f050f0d080105040213090c091a031906140f010207090e01020301031e0b010e0916030818031204030624030c03030f080105090105040203100513 76
    0x942d080e00c140c407148690301c8407151000d402c0504080d0030003000248148290b0000340301c0010280240506d8007021600641c0c080200c0d15034859020380140c691211108003070100b00400c1c00022030341001e0085841d00104000311b004c419040c0100c1800401420705444100411814003140a004904e07681c5620103a901c00a0789038985020005500440345101c4000c00e1304100c0104a20200741c91665010350080312400c80000701540100c0c503041c0c641d0b1002d5601801c080d12202400c5042d0300030b5050f02d0140f403009111607000c0700620303078010809500400b000240c1e80100315109a444060f90401400002ea4a0b0302d1541c034075442c5046602c1e002950030342400540c1680c8281e503c1032404103950b007038000e016040200c04917202180103a21000d80b00f65280c9200d00c2a443c402512050f150b6482052441d100d0740300e0500bd00300300010b000403030106003d864010700080c01882c102e03040740c4004100142c580e003040240008cd42000c3c0664001200c120030205042e5103500b2081601e4864a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691757868 1250 691756618 691756631
    0x110c0d0303050919081e13050d2d150c02150a020d1b0e0a03021309110a0f050117091b0105120a05090705060711010315120c030606081c0828 62
    0x2c0d00c4500042c0303403030703600b0724000c100e1400c20040b003582c0c7c4000c89400300d40d00704212241d030920415220010b0208000c0c4c0032440d800002d07400f040c01244010502032481c540a468650056004941010380d2500250303100c0700c0300418060141e560158081e5506202505042c00f91003d5001d5403291003000300d003060540204000954051030348508490300316001c2d0074140c61a0042500c1900c1620030410b51511a101d0b042401446880c1218203140900407209040c0e0300d0440100902050080a00050b2060421a230540c41c0310f02e018090300004000d00200c0c0500d0f10114500010321103071505003c014080a0b50761042c402c1d07018418495280045064034281c68061306058407600141d11a4000740803030f1001c0341055148405040c003e08000482160240964a6400c5994440d020141c0620b03242d001300141101050704407481b0710300c18480c082d00c400b401030b00c1e041481c0100d01e1200c0b03441c991382c003200c0c400ca080039040950619101e800c05005003196200848815034016032548950307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691759118 1250 691757868 691757887
    0x314030414180411220e06070801060e0603270c1c0c1e050d030e091003050c0d0602090d0c0f0b030c0f030a0b090412110c0d030305091908 61
    0x1440c11804070840e50000c0411464011080c2d00502038405481c0c184192000c64260b20791201d01d802c0c0e1075543ca84105103c454a4503080644101d0100d004540950380200c0e00490090b202c0074140c80d45515214120354044d803d00500380c0008003910038403224004506030441c9102d9440f4000f040c0386026200c02c0380c89c80d0071b00c40c182c580580440e030003c44070040c1101061131800c000c1c0035151400002c21011a84400780720a40f03020b600895404030320441a8810150040700d0005450010baa404640360740d26a00b503000b248444c0300c050f00540200c29852600e10b4400380c160034491081d03600506000300c0f100031401d0405804c2c02107407a8003046a040c0406009601d8050040114049107451454240b405000e81c0c003980d403c2114101c004070110b50500b0654011403c00d4801038203d8445103441c2c24412241908541400702103940711180d83c05802d0007181039074060402402d0952419245c3e9800c07002000010400c00d034a0013800c000f1081400820f048045060003154003640382c00280 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691760368 1250 691759118 691759139
    0x509060720031209010e0a08010e0a0b0c16030c15050903040303080108060601200705130b1008070206060d050c100305073e150f0109110c060402120703140304 70
    0x1c0e00480c866440344001921030300c0c0c1d01c400c8074a0756a0a10304243c904440c0c102040c65948203030840324040d401c3c07043d100c203a0880000d00c17031411800382407400610f8940701800400340c492201f01d0420110000543d00c0881d000e000700a001920548090306200c9000c0c1c044400c484054504134082c1d00005401c000741a44000c88602500c90701c00034000b64200300c40003801000210070700c030140b030100e01c44200f204081031082000420700175000741c40402100904c10020070988408034420b140640310202c840780b24050541c0b0031981a00141210b4661b903041110104014004845d944620090912545c58482d0324210070320303003034901042900300441c1c05070000d101d0107030003240840c0c50312540f0002006440d81c03418104100705001220380d040c1c407409041241321a4424125500700d001d001c1a8071200308040e048641c0e401c0200805066280310038142d10814184814960065021802502d03001d400521a03525030b40844103419a0b95a80b002003404002c074241094002040c02c00c54507005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691761618 1250 691760368 691760423
    0x7080603010c091d0622020a11060601121503050304091406120715050d1d1002070837231204260403051f0e03071205090607 55
    0x1d03410710307012450818002c07416961135130b00c443c045041e0340d2011408540b074218224800860001805002101d50346202019500c404a60800a5021031810307500c20000704200380a514140e5581e020b10410035080d10182210340403030f0070b8400c040000040054400c0004000070003404002041c4841c10204d1441400401003409004003c102c10307004802502044d2072007035a00c4549102c056801c1c07400100c0e500c0c010703008070007022443d040105d0564008051001100b80d05c0e50103c0e0a152a1488040141c1c044c06000400c0c040e4240811043c1c501d07601610350381231001080c0303030250341e90351050141869040c403040c02c080761140050001c5650100301030040da45090710700a18045004030024411100140040c1441c90b040d05955484146400501c01e1118055a56629291241131181e00c560100e0314000b4038130404e289660b4412614000c80c0c1c0b00401800185040c20351a4450034541c0750b050f98900108001080715000e141d0f11600a400003901411800031650850074501c60320120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691762868 1250 691761618 691761641
    0x210d02120604060f080a08211e01060905010518040f06060801031a06090a0b030c1906081005100810030c09090302010c14030a0b150a2f03121801050708060301 70
    0x4010304c0a00c9108000034198440d030741d02c4070805640340b81002034000114524500410f85d00d101c2024402000c1800310b01e509528040441002030341d0380d03464103071400c01c0c103440342d1400300f8001c0c03241c07000148815230031f1740c0728110141c00400c950072448464801c9442035007107600407a04000044c41030101d20300b04100759905c401d48168031420120b00068040701d008004010040d01d174003040c070345030b1018802c00301c0381c2e03202402c11700840500b00024100c1c06414042c1e03c00285070300000400300c2045840d50000c23110060240d1210440b1000100d43c100802002004022420000000001c214580c241d0040076411030001c2c00c80400e143c02402d441001c41400700b0064440d0801c120070410408990300031200c10300008507400c811010545c1c001d013005d402d4000140c042030001c041034000030040c44155404040561f8218040e500411006800c2440c1e0f007140c0c010301030740c40d04111401d062074200c108084005d0350700300c01071445402d4850454161000a030f215081c0300130360509004400b800f60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691764118 1250 691762868 691762889
    0x815070909150e09010b1f020c030601050a05040213181d03030f01150210022d071a0a0603021e0103050109180f1103060f07020607090602210d0212060406 68
    0x40c1c245803482d408841500555040026600116000580940c8240c81c6160302900c0c440150304034030000700020003100d90ba540503004205880da11850040f8002d0305998004012544150600b02804000e402140810081031681e1001241c42c41c1180ea1030401c0020410740800c9240e50501c0c00c4022009003590030709680d10500610040c1c040001525041d89c807075208984000c450344204034a84119980072100040c400609032800d0141d0107100c1010458000748030000200090003100d181c40781a8014240c03440b645055903503216041020b41e00320360407039404608141c5940000d000340d8000d0f001c00019410391b4512005958041c0103103401000c0c040e82c20480c0d0071460403002d8540400001c000c1c80e0350a101100d80403ca007009a6041a000250444032503142040c210000c1c0d00086d181800503115050019008511a0f9810825545140d014041c1c0310b8010b20280c40b0041c2440c220040700c2401c0c0301105052a807480a42405111060b02c502907040000500045441c00d40208580c0c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691765368 1250 691764118 691764131
    0x609010c0f081f0b07110406050105070f200603090313050402270402120c0a0806040b0604050d0201120f06091a060f1308070f0e100503071e0815070909 67
    0x49030006446944501409640202d00f4000c01c1e8607160a106a041219a02c0020850f81c080c0703d83d801128100c014155800c1090301e0300c40005440341d02511400420794001600c4090010700b411140d0100441c03c03800448141c1030040010b030795600102c42d03180c1f080e44040380650880c0c503c40e02071801090165821840c066142022800d18905a003106082009241c1c0303054540d02e80b07904948882c41d403d03181400d141031108003da02c0da0302c0512500001130044000c5900c0d0b16043c442d80142010092065243c0b6181c0408e0018807031003600141e040c0110002c8007a9400002d029443d214a000c44000503018184226102103c200050f1100c550040b01c00101d1140c64450842d41005d445c95aa50b03114040c1d148030100d110040d402c00710050152540000e40402182160405e031a400c00010645035504080b00f4011803c621402d80c0c181c0c4540000c20a1131081d094011040c6c0b14940711899958440b14580e107802035400f40314004c0d81400d0200300540d54086420000761900b05030a1140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691766618 1250 691765368 691765397
    0x91b05010e01180b0307030603120f120506130507091d100b0309030d060308030610180608092a1c0809130921030f020a080a05040309030c080609010c 66
    0x19854200c4025050026180580d2451a820f5030200d00034a0383d4500c10766a840c1c58400180980b49074403088076010410300124007064003a484000c02c0f080241e42c0c504100c905120544003400d0090040da41006601c541d55034111041c1c01054842c8455450301c1c802c0c1840c220b000c40c1e4603080c181205046c1c07044031050054101030040c00f08200c0342411103541c1c80f51541d00703a4a0440c0f2511580100652a0010000c100010840607621813141140c03945041c41c03d00d44159061680c83c0180c03011030320012010300129000e50030442d0401c1c10542140c11030300444200c64207034402c8855041e5030200241ea007945c50328203d00c1d404c0d0b40340301110881a052807c1e50300c410301402041c182380c0c458038140d42e5101804206520108060380c000205403510300441c42c203d8440d5415107080e20010f400e10300414007540e40ea0089401d041490380e2540c50950b0b07044e05074001000068012010094203141c000040761789403848401402d6401c0c050041c0b0304284108600315080004190144180e07000c0c43c00a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691767868 1250 691766618 691766627
    0x23180403091401231b0304180b010c021c050c0a0b07060e031911031204030810060207140d110312031e160e031c020106170303090a081605070306091b0501 68
    0x18051500c82460301c030b080e10410010b0410a000f088031751840003140c0060700202c50251551180c01d5201c003040900741c0780004413101d0446401c06500300e0040d0b0b0101540c92050f40c0302c0c221903030040c3c0544000c0040d000c005803011600303520a45280c480854220240a072070b2080d262103000c983c0c015803509107104402140942c6102204042c000d0340c40701500444414002c4a041022344031805030245080d260180c84000291980c04003030814410102d8814000240c50055030042003444010303007807100c20041d000c51040340844600084011045594070300304814046100741e0084607440345040d0031801410f4109020070284c51144c1414403154100e44912007001695a140401c1070174242c4004c01d146c1a00140714035070307020b0a103c003892625810340c808401c1d41c55480c0117983c98484aa09160749000503500d40e11180c111941d07000019041400402c40300c040107403090302000c0e9a86407542000219070003500c1c05611080c00c0070401684002d44926048442e0a408009080c02d00080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691769118 1250 691767868 691767917
    0x1d0a14010311071a040c0308122409160504080102040f0e0f0408120408070b15100203040b0d0c020a050312040b0c0c07090507030227040501060923180403091401 71
    0x1c000120407404a018000701b11804409103400809550707640910b5071110009280442d155006030080b82c0ca03c481207001511002c120390030040c81543d150711020b02020140540f06054402c1c044104400034901d0020f00242004210f01d0801c01140752501a038011003080007040d1142c0003150104200014214800fa5020392003001c0308025141e541c1d2030b10114910440e0009410707040c864081101c40289140e1100c407207881690f0b2110008040501680d50340110b00412582c40000e00055162480d140c0c020007444032180304031035070344601d501c420b8159403006004e00d110f542c0900c00c1005010007800441d41100804034110719049142d240340d52603207464000c000015891f5000b05040a200c1d4041e03c1c42c00940f4002c400e04692440852003080e42903d00e45809181807000015a5a001e03924041c00c50f008800b007030010342242ca80f1074100c0440c0001c01c1c0e510042c01c000f00c00e08003217210141071040c0d110b0780f904420035003081030040034100040302c0c0d94100820300710303072441d51f50724810000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691770368 1250 691769118 691769153
    0x403030e03030118050c07021306140d020a051203070b07030623010203091009170a0b0f1e06030a1205070c0902042904050411030a06241d0a1401031107 67
    0x8042c0c1b180002e14600380300b114000b03580311541d0314030308041c1461507110340100c890300c000500035503282c0750600000e0320b003055011b5802400c240d0100800d09045800c50300858424041d81d14114440d500c0c224103400075114840025901c42040c0195080031821000446000d070340d03400f00e2442c880000f55248164180b450080c42c28010a60b4030703e005900e000701502c0d011041c0c02401d61244c01d41507469034400030549060002402040c002d80c00314007100c3c0580210040d100c0c1548d03050100c401d8007200504103d4051044d180d035a0040b4036448010300c40d403036443d0364060b80e40040d0708101c04c40ca0500d800c0f8032615481080204454070340f1002c180f12440c0611000c0001c43c1c40804103001d1800741c0d6004540250134261407280011071032300110b00c00e08070f0501c20040161034116031100310800301320103800f0b03036440450907200d58040c0410303031944902c5400340d00304810320101180b100901030b80002444000d007804c5403559a09401100c103000c1c0c844c40d90500b03105803038584100c051181d000b034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691771618 1250 691770368 691770371
    0x7020601050d111915080c030105032d030706060e0a050c0a0c0302100c080f011401020307060509032205122803110d05031e0402010c030e040b0a0e0403030e03030118 73
    0xb020001e407100300d404e421548102d0380540784d0540d608554803003002c40100744400510074000241c1140507000030f4078141c41000c0c00400d88400b1901c400e031080114018144403403140105801c0868070200018000903218190100b5810b2900c1050800600045c01410456007010100803d400e0f0300800e0710800700003864002c12a400b0340c1800c1c3d041c4078504c050300c07901318100400010b03120340251000c1c0c02529a1800c1701c030640c1c0d941503016448510b0710381c814010b810402005000c5040c1c1c2d08515004040c20054900d821082e4203040302c2011100240000204209000c0010740781030188407025660010240c0b03101d01c2c1d001c400d0034065010b00701c1205441c0702000e5600915214020740481500d4200131039101201484001d1f049800c21502822051040040580f240c002da128403030142d035040c1c4554a0414003a6025610754159802030360308290780d10410b078103990b1003410640081a4202c203060b80360815040060130b44900064201c0748c0d5000300010404450042a558200c4180e50300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691772868 1250 691771618 691771643
    0x3070804120e09040503030906011203080402040902040605090711100b0f0d030507050613050c06071a0405010e011107141501090c0315091b080112020409170f040e07020601050d 78
    0x3800da0b0600c100c0721029801800c900200020003d00000540c050f940e1502269034603030340c1e1104c28501c0c0b21403540040024141002150050625400170b40500744010320201d000ce440b0004110340310002c4070100c00240240c184020100f9091040e80100d0401200a1200c0440100807030030f944041e00b102802040d950310310005241c42881620300303141d84201900c2c03150403c0166440324540550003550f207409400c0f50340110b46813100c2110282d9078060501d2910508155248081150080090b6425502c981c81040800030038865030200c48021404035441d410036081c0008501500c400c185069804030444000e199410385105c1d04407442e07202c02003a18000048200c01807c04040c004103940b101072404518440e29400c820003d200800c0700d0800d40c0f211040441c1c44080a01c206104250030035850405802e1640164610703a0050b1a5480144003000384c2440e40c0d4898085a41004400719003032000c203403c3c5011580080581c4000d007565410000010076401500200401a16440380c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691774118 1250 691772868 691772903
    0x1905090a09050f0a03090923090a170a080a0c020606090405010213030b010e090c0a050609062221120f0c02030a030914010504080a03030b03030f030a020a031103070804 74
    0x100005100c65002003583c140c0051004007650328415040c00714049003020360701050400c010312507444541d10401c1d050300d00390040390a064812101610f20803240c06215400c502190031054820f10b032052020000d03030344400c00780000f0310000c000381c00c8000745428403030007185a542c0000c0141d0047d0f8101c803985516111490700324028420b0752030308a48681d081800006000401d07450038104d0b041b47d02d0440c11981c900010580307441a8992181d4017000180c82400b650410350003802a402026111350320b00090f8008203410200c1c0c10003903203001703d0900d1040c443c440b0000d0488608800024021100c3c0449503642401d41c811403000300e0420a01400e0840440d114054241310580c000d001c3c0c1d00c6000c45402c008050700c40314011001b105503a40c00c4a0201d500c80c0048404694410000d000301004a03503084020702503c088065240c8800d00103e5040c1441800941c003900c2011001642c07600104005002e8174405c0450340018642841000001030b00600000d41c019401410140c101403440d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691775368 1250 691774118 691774121
    0xb09061005070506040b06010e0118060e0310050c0a0f02060906040803041e0605070206090d0507080d02040806100e0a06180509121611060702150c030702040e011a1905090a 76
    0xc1d0b10180c810710920782170100748450007441e00d010360401e0b40c0750b1a102844100544010842c070b104005100024041040315034420f05096031a400c005064848075143e020005c070580713600341d651241c000400622103400300d401104d5900c02a01d9400503080d1483c0124100d83c80710070040c4080c1840a0000004003009000313039400110b65a0f21041065124031810910002c2c4800c9135204054032842d40850009600010056403031889566030500c1d000c3d040d6150880c5405c0002c40c405032035000e00c000b103544a018400c0600c030341804000b42c0c331951314008030145040009010404014a41a002e010451000e84120099002c008010403d6228201440c0c80c20b0907031040c0450458001c02c0e281d4040400c8140910001d000c3d0f5100b80b201c498040800c03034580f10369403001750b110b2860010f507103070080d1040c0903280c00300401c0107507810301d44035401003000d0302c0310304c2003c40704d0765541c4d01002100c070120000390040410544002207409007490030704403078450178001c1c50b00c03920006002441d00983ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691776618 1250 691775368 691775377
    0x1309050d05090d06050126010209060714070e0c0307020706050a0e0d030c0b1305100203162303011d07030b03030a0e0a03060603050109021302130501030e250f08010b09061005 77
    0x482e104014030b6031f481e40180700220315032244010b0442e01140d0000600014000d40313101d80700c010f0410b450284a503948990b454020404089035028031305001a25041e03034805240f2030038840703151559078a440070b0024100300c0640c0085040c88401d009081c45c995001c0e180302841780d001e41d560b03080d407101c2e81030a40c0c07450309042d8020000c07000c02c810446001032590b29422040d104000325149a0034400b05041070b0b001c2213075070b00c0e032421031444511045445041012024800d1001c4880b980c11b07001e40030320581e40309802c8041901c0445403400130307005680c034045510070041d1404015521608000903100e124000409007081003c2c84020219030761000b29200a55002d40304124040d5645400b41c007902000505900c40c050181404958201600881d000c0d007040840102c0000d040c10015802088840c600189903c524003100a400d0510301e07241c040b401410691202c203d14103c1038028103c0250061602a41040042e25450316003440d040d800060440700115400382425048415000307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691777868 1250 691776618 691776623
    0x105090c1002070f140301241a0319090f0503040806060109120f06050705090a03111008042a0b0310030209150d0b220c14040b030c040c2105061309050d05090d 70
    0x810710423031409121007010034212a11805001c003100d04000c8040043d0004403803503803404015014035107041500c2d0307103c2074285100d182c0f13105071640191280c0e481c1d9005904000ca1603070051050012668000c448030380140500f030550200d804a030b58404407141c060403130041140741c4800200c0c401c2d0f401401a50070190000d84840440769172410103019111108204a008074048420b52215611840b5101e00c61a0407460255011150440050108003018424000c005600401051029058004500840648482c0a02c4604600400c900b0001c06012014404401c3e0301c0f205071a110b030744804900a8102d0790344c0c00b0030b0340e600a041c0480c000c0c844103080d01c0000e00544004104806030b01005a49410700c07205080e500d15410300042703d80e5101c20603416445484d64070f841d450980c200c07402c01c448a282030005500303800460748a045481082251558442c2e0070082e4034100b54a003250800114182482144955201d641e242d95950940c1800c0100000f0114003030380310103045011031a0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691779118 1250 691777868 691777901
    0xc03010e060f1012030f030605090a02070b0703051308030912070c0305013902010915060501170f221b0918050d0c060b030105090c1002070f140301 65
    0x1042103441d00d900307045405481d4881e4410210f81445810703280c2005443d140d19510351500074948043c1c4500102c030700f0380e90416840d450042036644a50090303c0c0a944101005030b01c0d5000da00c0e04442e0504004c10303010805280c0720401410307035a556000155607030080740741950f82d21101100c0c0e05000100344540849200010b02c00100300c51078a40f4012071307010700001c21011910801808140101e0030444c4140120801c403040c01010002c01002d04503500d000005008003640d61341c51016081c50081041581c1d80d03081000256003149503910b2802c01d140d200902440c00c03203d4041c8588002d40b04078428261024240c00084141240d03c0070f10350402600c03000030600303200c4106241c40d0760040018180c03c101552010701c0c07045620702041644174018001145040d1011910009029404d50fa5140c545504c410745840c00c2c443c0900442100001d001d4001c50041070001c0400944002802c560285008100814182c0c0c00041a90800e4102c4e20b0715007950710009001d0000c030b14140391400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691780368 1250 691779118 691779131
    0x11060d0f021b1605011e170c130f05151309020d200304021806042c0c01050c0d202a040204060212030403090b131404090807140c0301 59
    0x4500c042c20190469210700215818950f0380008031950606030302ca8180441d04c0e0500712440001243d441e5101d1184502e803408031042031200092001c1001e540c2820451000942032105060300705900300901060b10074044000e24110100310080708080c4115020800495144801241e03010f6140041c0b820000075501d400103824034034024180080c11801100030072000799840324218003900e21454008040d2409101c01100a8040744001040ca607801070b070310701024084541d0301e0784518661b02d03205000081c0081701c0d9031040c41c0c20381c90002281408424888a50364000004000c9604501e07490b10080b09031589402c0c590880011420b0425801a603080038440703910b040010501000802e81c0901281c4100f040c8001c074802c03800f03501d0058005100c001035162040740119000342c0300e40b91828030207695480200c5c3c02d4110708440900d0070780d00c48041080c02e010003030308903440a08503000c10000380c2a41c2c80c2c1e4030354460f0385001411311405207013003050840c2c240902041a18058003d1124 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691781618 1250 691780368 691780387
    0x60a17010608010e070c02011b050c030a1a010807030f0f0c05060d02030a060b0f0406030510080106030c1406093f010b03100b01142b0b011b11060d0f02 67
    0xb8002401a002442c42003400910040d00c50301c4030028058040c1c4480101c000100c4541813402000d960540c2e00384549100303101c8640301000720b1034030140100400312003644074800c101c01e54401230340140701c5548501010b00118042140300c00d032951780312448429103106440d1002c600740141d0300c002c3d805034000c11518220b2805030015032050390b40001c2000080e40b030b0340c000a10f40c0210941020420790070712040c40042d020340d014907040301c0300c0040091403036600c907026800c0d144550400c80d244200071004003c000d04400715401044000c0b280305003003c110070041152207841103c0004000c4140700401800c3c81c202c000100801041c8410402d110801c60146000e015003004d4107020f449208401e83c48010b842c4146006648140c0d501c0c880161600249c00c025041006132015072039460b000a0b01c1076411440e402100d07904150042841c446440000d01001c01c1c448500603412071500d500300c00a4080c80d420032030101d00712005912500c5078494400203103251085a0700c031510000e00c02c0e29 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691782868 1250 691781618 691781627
    0x6060d0302070e0c0d05060a0605090d021249080703180c080d11030315120102070c03030e010f090902030a020c03031f08030c030306010e042706051008030405060a170106 75
    0x500e002040086c0040d8a5800a01000070910300c52000003910600082401c0d21703015003e01c01d91400100350326040806031001d41d061895a1640c20a0071003014140e007100700e0030340070312603003000b101d040b1210002c503008a900b002e101c04075490007000900000184014000c1d808000400701d01500c07400ca205240c94034103003900440c0100401c6c1c0c459a681042c0180c07007402c0c048484104000910f00f552107101030706141480034603445901444058000780500405d20260642502034960b1f84141d919508014000a014000060411110f180080380712500b101c3d24a0450b11000d20042e070301da03a01c60000d0000e0044030b010310218040041480004204003003035030614144000e40703200290b958100e0a0756441808200d40254205100242e03296024411036075211002070400300c2c201e0070480343c104009041a0960900c075160100000c1801401d20400e9440400c0c0c081401026041c11005070380c0b400b8610800d03204180c0020f0483d2070600c030300c40c031041c40e4095481d510340740d58452a0252 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691784118 1250 691782868 691782877
    0x1d06120d0c0c080106050d0b10050d05160b09010c0f0c0503010e010f0507050a02071814091e0f0a08030a020c12041716180902090c0c01140906060d0302070e0c 70
    0x407502810b07294007040892040c030940048500080900ca1402182c0e41e55800c8200700502d1003541d2050f00740005031540701d0100d00c6080c2e0b8450005011240200c200119000c440ca81080074913034400d220040090342c0215080c44441e420000f00c40001004e8038244001d0740c995002a03800d5420608045160703181508030501b00d5040388000d11981d919042e0440b0207001d800411001a484603500304292941d94916400b10741c1100c1011401d03891142c0441c80201096406121a034448145001f0801c00c450515101410050161980f0300b45030301c08540d00c694140c005000400c0010100300910b805074101e914600c1c48030103079000c210142e4654001078015102c0e2185848500e03010091414010809006040181a84002c06402c1280142780c5209103485100341c03030740e2080d4907405a40d40303103070240c4140c40100f0882d40e6926a8070301d1a00f55850900741c805420b251000b4010507040116540f07501c41e9040d140104440c1c01828124034040e4158000141040404280f0100f80d039440c0040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691785368 1250 691784118 691784123
    0x61e0a0f030506090601090e10150507110d02131107020a03060e070b0f030c0a11070816090e0a1e140304050108150109090b0301140a06051203041d06120d0c 69
    0x8000b40e036200414080c1e600011205680003c0303100303000f4082039580d000050b40000d0640384200c42c4548403034030141c00454015a01012803404504182000709415044124800907240320620b154130703602140030000700040d1004450b40b500070100c00f440c60031040d14801c940060641022541d2410901c0003041c02055141c40c6000389500480c108011200300d420840c001d1080300d107141c2d1441d6109041e41c100f98002400c10001804902040900b081030002511039500600501071210100400001c03003a072040c882103041c080d98a8041c000030601c00703180fa0f00003580c2d00c402440c105511020191248005140030410481c1e41007403c000406082a91020380720300c0314540711200000e103021079060170280010024002846460196040a0901c000c0a000403804480c181442d00160f102100c451300740070790707449040140d803070807a1800d000000c7d150080c610302070401d60b1040710409800010b12843d0618404100c844c0c40b000c00d00f440e071903050f03401d8950803003007100001e04400080d90709 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691786618 1250 691785368 691785371
    0x203010e0f03090123130e070341010803041509140f030708031804110301080613051002030a021801030c09030f06060f03120305071b02061e0a0f03 65
    0x21414106800140e500c007105840c8001c40c10804424011aa0300d44081d184c002a010316040001c00004c05401404841703d81d801013400d050b0924543c014082c400400c030038101810460031130110200d85c81401c04060200b00c402088404030641a0841c10500b850b00b04101c80800c000541c20380080098029924401500c0c180388680b0b113030441f0f004000c1e0048210604c641d44241200c1c0c13074203a0075000302c2e44000d02507d613160b940c1c46a40742150405240382081201b00d03044146c852825200c0e0702c6040c403010303000c45e00b5541481503d50340d0b1a402000c2440801c2000308200030320a04000015154109072015540c030b18049035801d0194000c0341c2640310007110031301c103040150700074080c014a00c07180e9580c000d0542c4c9141c40d04c031100c902039082034032a10303914903021440904483c0001c02079401003003000d903c2e2010039130080032600014002020408040190b0210291075441d0034102a01142d030f41c0c2e11a1034149203090199100c14900d60070010010303044860765000b02c1150400e138500d4a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691787868 1250 691786618 691786631
    0xe06071e0308130b0f0a140907032604180905030f09130b01080604090c03020a03210806091501170a1a0306061302160f0308040c0504020c071a1312020301 68
    0x82d4070f440701c62500c1c0051040070140001055410301428065120f082444045000d80e000b1052900e0980c00781c440f030a06412105c8140280400d04404040a405810103900b415400c441540c1070760255000d103903008070340400c104ca000581e9401ca08942c036004410749036181d52403c9201d000b503000180007170064542c08440402d6041030320900c1c1c1c42d24010f0716440b0460342d40000b000001d28403140201d415201c500000b1002d6116080c06a0103544541200303401c00383c1f100d5a044110320188610307c1008060010454907440c0c234040c0ba6004120342c803440b2100c6040100680d80000f000c150100301c50000c604005880c11181c00c42d00c000060b0090700b02e0032254400034161541c100329203064200c001d0300b0b03e02c1c902d00c800740d0007400907069205000000140da40da941c0d44d60724480c10f0940002d900d200501081c4800c01720000010f003012102145000701800c0190389400c41c0307120307100340c40c07900c1c40310f12040d071102c4412120001c409140841c0003949401c48103542c0510501d00f1780c002c1d0318184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691789118 1250 691787868 691787881
    0x5061e06120d14130b09011e2f060f04060e160b180d06020d1a0904120201061806090608070b030c0a020a140c03010e07050a060e06071e0308 62
    0x40c003008007490280080703044800050320018090400f885144004016034204525038500e100c3c0580311030392616035510703480707400101284000c2040302140d961050303040b0122070f00010b0b0a000300d52803a1001607060000b03011204071054003070030f04a1038040da404010150112540c40707842148144401c020040c0701c06548d580d6148111032120010b4103410003805502d0801000e0034102c0120114a031200164402007280c0005a1404072055500492000d0740b0b5544d9002c0c021400141040b801d02c80c0c08110300050b40601c0240000e0021480c015a004115100303402260252014201c280c0700901039410000c0142107510034290072034070749507001c80c81d602c01081250440f0070800b852810341c1c54a60b240d040a40c0803407000000d40c03003230003001e0000440d0130b00098446090f41c0013411145600d038080c1403e40340490384000d140d421511081c0078a6640c80e46603400d445036840c04104d1004410003044451190b150f029140030404001c1000c90500b42d03200050061099481503943c1d01c591 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691790368 1250 691789118 691789129
    0x3060515040204030b190c05040b0319020c07030303060503061501110c03191401050105010903030f0903060c0801030b060d030503070f03090b09071e12020d060b1905030c06030f130201050705061e06 87
    0xc500700707c00541d042008000e40000b040182d038010000c80c2e15195141c541c0021784040764014610117809400c101001c100b81901403150500524040d0003800b942d2410950000b03490703003d0f20303c15041c0200703002505041481000160041c0381c0143c1250303500600340810000001c29a4411a1044c031004103910f40b400701070090504961041c1c540d4000281540e03001e0b140000604c01000800007140d030000b0101e42c1c9030080300d041161f0394481015030750450800040305413004140c0c50113850383c910380c0c0340002d034001c0803a64031024a207055408140c2d0a4002c0b406410030000c003401c11078400c0140040b010740400d881c0d04648004c07d42a0002c402c03d168003402126501c075030030065001d00506000750802206009401e4407801000400704ca0050004a100014031400c41d84a00700c1c2c2c0d010300070740c142040705290440c01126024110301d0440030605c6100790081500b01d00c1d507402d0f400001103901580c10341c7c082035806010360300545002d040102c01080e0303000a8503007a44d800720126185041c80b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691791618 1250 691790368 691790381
    0x13260109120e06070b01150f0e030a03080a06170f070e090c040f06080303071101060504060b090d0204090b0702100641030d112503060515040204030b19 67
    0x314081c0085149180001d4440030103000919402080410640f0001a40e070401503002c3c00d59012506040160208010985840c45950070280030142c6100301056030700203032110040c0d0745031a02d0b0445946000900c006010150300480d08030328180301c1c0c81c002100100c0c24501c08417038001112081643d814080b4a003010642c0c031a55581c01040d11a903160406400800311420450404190fa07592003102c10714680c002c480000014210384a0117200302c03800c1c005e450040900710b03400d00101307040941a017a50311844a90768803400740386d042c140854440d9000288850341104d002000d03444c00281c065102c1207094603004c80e081c0791000111b2441200344e443d01c5a4000394001c1c0410107110b060020112b81c03507401004014200c00e500c0031845c3e600f000583c0326240c039503682c40c0030500034941d0700e1724100e95200c045030050b0040c42034481c051200f0020a0480780c1121010500b41c403018403000b105e400680c1a190001d00000300802804521081d8601032943c0d801d9550140661000c1203046919 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691792868 1250 691791618 691791623
    0x31209060f0705071e1511031012170304140613110103020d0b0303040906030c050d0512072f01080a09030509120708030a0906020607051801031113260109 68
    0x81040c003103a4814864409401400e20a20020361004030b150000c4202c406815000c07201034142241b6004005200c1c0034802c0400860a10355003541070180c4002400500e40c01010750303490541401c20148181b1100101080400c5040b0039501d044c9410410b044452910f08818584240404544606030b104001100586c0003840d0b0481100c1d110700440181d030000b007900c2c9a02d521913103c4415940d061000300024130807c00c00007410791a5140c0700f03111200307607400035110b10074045082000c20320104020507084029032150b5680d04a91507e01600d019094a40721a045d04200c03020400c2c615107840e01a004003601c0d04000c0d40d171030300484401e4880242009000400c2030000c05d03003504080c0c0f1407012114012040daa07080713072034045851031030b04030703140c814001001500300f007000340d03014030100341c220041349426031500d01400030241c84500407041c11810180d450205515800b0060180c51a150498040400c4280d8a88008050100042142c7c0004126800c44182034405100c2c0030b0f01d1a9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691794118 1250 691792868 691792891
    0x702070b03010f030f020619030b03010e01150b0304140d3b04200c0607030c050a081501050409020c011422020f010507050607030507090f08102c03120906 68
    0x6007196107041e0b0504450108a8007c0414044100e4068080c04407225403105540d00080c0710504904045c01e540445001c080319900d0164034030358482641e400e01c802c1e07484c00c1c031569680e500d5516000f61100c0f611406091217008032140c258a03140d225115203411030740d40400804c076038010740c04100200c120b442d4001072900889403607105420240c01400b0400b181020000c5400990f000040bc140e004500c40761154201e0000c100c44650144501c001c403490510f820b0741041040703000602076450240501c42104054004001240e10490071100640b5401c5810b64980341c10000c0c0b02e001c1c000354400303410000850b00000300403142c1c04c2d0303444c400e00c02d80c0341c200b00d600a969024050700c0501990014100b01d4204843c5000c90780030400d441c0251010754001076103103460f10b40181020388503000403070300190042c0304005c0d20710700003400303003d03420282c5c0009031110003501d82c1100d403d5080340d01410440d501308000c0e10341c1c50100c0a40140b4804e0f030410b20b07542c0c0d95006070f95200c0e842281c840c140003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691795368 1250 691794118 691794149
    0x1f090c4e1508060441010c03020306090a050406060510050a1112180607061b26070e030a05010e01060e0c1303150e06191401060f0f180602060702070b0301 68
    0x2070440f541e41c5199040d200e01171141d50f02c5a104240c004070042052038603080c50b501c101e500d40c1d4030034401d0300030b60540c40c5002c5056040c01e40004081d40d46c042d141300c3d255074403200804c0030711509512640003840001c1c40d01d6109400304c800901140c22500510f4080303614000798042d00f4101180040402036008403c03494070015074a0217000a102c0a07200f0b0f004041802040c3c0002c079548074000500e0400c2c00c004044800d003540042846041c00582e0082c24981445a0400c9038081c42507070300050780d81020b0300400c0c0050042442e00390742d204040c10707079824030030146094901944940c0c1a81c1c008250100123945800000109102d03203026200c070460a6001000440d88040019a10b402d800c00b01041d04100501007502e0a00169101d40300d0350707c528901d022801c0340f0f00c507030448c0c40d288000030007144d850284043d02000c400ca65260038004003180c504012803080c1c501f505011995a4039003400340c1c494400a6590204444807005803040c032101042c900c8050f015030303040f940d40e0320070100070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691796618 1250 691795368 691795373
    0x1407080408041206020906130806010602010b1804020111150106020c030f060a0506031c17011413021c02070b04030806011706040b040908031f090c4e15080604 70
    0x43c0d030b02c5a101a10019402e010303200a680c0d40500174040ca03031031106840c00c180d0600800f142072500c10b0703104006580c9003048200203511000310071141040d0f42401c50203a591030380010b8401c05030a44d20256940102c5420203050414110310a0688100d5821280c51048240c00d0554882405a00d05802c1c2d009400180c02c100e0307a03401541e07210780c02409840030340146044406540c8901d8100c440880c00b8855002552182048018010100c03c07900d075000e0f026017800700e01180140c0400045880d00022036100e1040b04031041c00c640c0e12404e104550300c8402c0d0a206107005020b6030f00310b00142c4c600307003c40c105603ca40c0002d000c000d40084820120b4a0310000c00c401040b914540d550096201c4440d90045203400380618400d000e140c1ca210450054100168000c3d100344d0071901606141000c100b00c00c40e0b000c0c0026080780448400c0041c0c09440042c240f0544021014038400c00c01c0c45184130000c0d00c00c0740740410899202030340511506c0320110700b40d900043c0d03500170080380c2e03404a00010b02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691797868 1250 691796618 691796639
    0x50f2d120c0d060819060f0612061113080313090c02100504050c10110601060207140105030a09050a0c060e040902090c1612020a030210020405010905190e0a140708040804 75
    0x1d40c2090b0400096880d1350b80c104a0704183c0601e03a50011510b070320300c40005201315802490708884c3e02d02c1c002c01265050900751000c3c158048030142001d0760b10118030082500c1002200c40c00f0715503c151140c483e0361080b030b03555243c0c851a003d145d50040303074000003240c8900380514001003050750050b0808070240440764009000086c82600c20340b28075642c0b9201921424806028000141c0e074100e030a1107010381c0186400030603400042190302035081000510000341d0440c2c090802440c003035580b03031250b040080c0541407400014000b40141c04002c8100b14003590000d0807901c0f40c1d150124100842e030100012140e41c83c1e0007039000491500011607031901000240586480f107a26803c41480c15145c10040303c10455071000981d220111000c01d06404100d0f4560444108c03200303519050030800000d100c54190300c0390b280501c0c6841500186032001909200240445001912143c03074101c1402014048003840304c40800c1110020440c860311802c02c0b6841541c01c040e00500d0f01d4a007060500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691799118 1250 691797868 691797877
    0x207050f1203190f0f05010e060907121104170102040312140f070f0c0305010e10090c050f0105040b0304030309031b050c011b0c0f08060f07140a050f2d120c 69
    0x34801e540d0300301e00400013254841c01c0794603c0a443d00007103940c1806843c4002c100064120380c03142481e481040200780e4411941072010a003114045210f40100111b00c0792401590000b0321842c083c403192240920781540500100d07400780215008402400905803140d03161003e440c980b51008001c10a144080320f0004c0c08901e2284500d096002c040d81c4600341c0c2710003079030402c844613511031241c0d0041c50401c000702c03480104421020015064a65110362503800503208050241e40c8a022a1200ba03000b0030980c0c004007800044959130b40303042d00d0028000d10100c0d400b100422a03a0802d44040c00519400850455100f070041102d0803c0ca030066403030300a007000d4042005482026280001d104c4c07903104009000c90110b224945040044c014100440104000071020b1503504001c200c0d61311118a5003444e90410282d540d0303a00310320080b00c192103003418100400714006406c80311000407030414140c43c8170700540178041009101641c0d00a10030540c8081d5000b1442c0b01185420b10754070f00a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691800368 1250 691799118 691799161
    0x1012150c0c0803090601050102061503071203050910031509020405131104080313330c060615050a030b0301020c07030209190501030b0f060315131103100207050f1203 73
    0x5030380c0c07003856a500c1d0320990080b560032000b9000306004220958040180c0350b003100c20640c061100f404604082962207055209072035071a1110850b64042c1402075088840e098400b0345046071900b12940058090b010744000580c444604810000307203092130b03200362010350f2001401c150250019040c4000034056011040c07441400800000883c3c54081000b0280340c041508004822403030303e0000540001c0300c103096052144491243c80311400b200092880b641a80d092035101c001c080c0c00c09400420707494010303405002c1c1200a010034190040b020704007100580d54103001c047e4911301454203074080c03a000e00d0240d5124003810303c0140f6250407d183c0c00b9520300803140b55442d4180401d0140c407000c1e80f0503140c410905050004007107980b41032035840314054005141104041000310060080140b4940d414136140e03416034100582280011042c0c000101224500c40e18180c0d000000d50000008030b919104050501180b100080b64124030002d40c0d1701c9050a650301c03102c004001881c0c941a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691801618 1250 691800368 691800377
    0x5030a0c03060816060801090b0f09040f02030304141903030801180f050c040f0b040b04090519050403050307121e0c0203120a0501090f090b150a03020306090102031012150c 76
    0x22038900700030000140c0c04c2a0444d007009516280000140030034206820200074a07082400c1485941c82d44204840001c00079a41410296143c1c10a59411410928003c0d818000020300107840c09040d520905400000c48101403581910643d0340c81ca05c3c0d1500c0018003141200004000032404000304544842000b20080f982d03801c103158202c115502100d0211a082e00400e0600c20441030ba00d441d405407220241191405082190048013402244920081c840e00e4500140302c10318440202c1c40103040ca040d0501c01400c2c10314000e0403d41040782e800002902c6151104c2c1c00c0d90650203492100c5c00004951140c103011940c00a02400300508400c0a5110070004621070004c400c450b140305040348907000401307504040b9108140ca00b41c08840201c24206480f0401144514034a240c000040d40c100798244070855000c102c000c00d065201a515000380c03c208001c13018190000c1d0300c15074140c800a889c4680f200001d90440446040c050024a1501602c960f51101980003c0048056081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691802868 1250 691801618 691801631
    0x10806160807020307020a030b1b07110906040902130605040f060f0302060a050c0f010e12030603060604240b0706051620010609050403020d09151b060e03210f01030305030a0c03 78
    0x102e02c02c54002d500071100784209c4020071013582c110440135aa94040c19841924190203030301c40140c0000a0142184160000000704410b517690b58881c1c1d000c103a004e44000b080031307500c8840b00001d26251142c1c50285c0c3c140381401d11101494480d58081e07032000c04580500b10b0540e0284200c80d081102e40c0740c1404020410480b841d4000c1186400600c0c2c3c0e080041a48000d4440f41c23404c0203108141c8038900a81801441030581d0041070050307010300e0944002540ca000c00c04088039000039441149a000010b20011404129a10040180b50b010311814410380d2200d405051a011140040350000740c3d03041068196541c400b91a091005285000855081d45801091040300e500352030440241c2e000307001a030840c94000e41420000d0080d102404c0d054080424041c041c450a01010b21940d040c011411003000301550003602050410021284c03100c1e021703103052104060143e00d404200c100f640004421604419000b41070302c0d4542e03181411a190484401e01401440b60f07c801407503281d05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691804118 1250 691802868 691802873
    0xf06092d022a2a010e030a12021501050a031a0c07120c02030d0807120e0a1a01030b160509092206020a17061f02100f14010806160807020307 62
    0x707040d01c0368814401110600c45510b0000e071460101140d441e003610340d802d42c890360407210600d0300100c4924420f003030100d1030001c0d202c00a42450710b145001440521080412091b50740c2c00038071000781103552028010750341d80310003c2141c0703501c480c80028081d40058a81e01500909618016040402c1d00704071410040581d5521141e500803014441c00a50a130103900e084d4607040081942050a50a0050103820a0407000b4060340c03150940d0310800d51500e840b080c00ba00100403070403145401c103520b000041020044117100d0042884151607100c3e201c0040b40c400030403611000d040d01d42980740c091a20266a0030700c07118400042002588180201001c014141c00e0311081d490148103110050707840c03010f9039015110041c0a01c00c081c058103031170300308411619a4146000200308920707200f4010081103504a20300030046a04101309420300300e0006600030690051240d00d01d4240d9008856038960614031740d501401c42d020452203003200d03091401c060103460140c0c3c2114291054a02c7e050719078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691805368 1250 691804118 691804147
    0x9060c03041d130b06060f0409110405190b0301030f1406043507020d061503050c0f0f18150d3002030304240905010f06092d02 56
    0x42c0d012034548000d18412141640300080e905038000079006941c6000310850300c0703594841600a0020340a0790000170500c183c0403400c81520000c08441400b40902c600d580710f1b5680d40d81080c480c0a0150224000c208000c401c0c007000c41041c1e550001a85046a19507101c10702d448841e030308241c0f88070150701c09070b07000c00d00180002d521413402503401e160311225000a100c2d15443e18016100340e05409845034101003202c074211201c26070101c0d01c1c14100c0f00f4908101d40100f0300300c840c00002121030300f000000c01201080f1046801c00031159400c9c00543d0605126098a0a1804c0e5900c0318a202c590f1520400541400e608048030007486813061180b040440c041416411041e22240711401d00c1c000d0840b4800c100440c60307184840c40c03880346051110040d540b400003410003440c5008002c43c200c2c111401d00c01c1c608a490003164180090031071803c01e03d000306211f500d0b044070281070130804100702c40203001d070600840040070100c04100a00c4c3c0e0480ba034400e100c012400c0190200600158030307104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691806618 1250 691805368 691805377
    0x150a051c020304030804020a140d02060d0b04050f0406240b180a120c050a080303040b041b0306020403050c040c09051c152909041707060c08101202060f09060c03 71
    0x1780c0381c4078210304160040051002c4690f1081030844800941e040d55900d4114100e403610b541a02c185884800100000303001c1c000c20244c4031340140c40d10302000710840f0b081c00068055400350000b00140e801ca402ca0341a960a2103000800103920500100141e00c8424000c00700d15140040c05500020140e0009030204075a034800c030450940d94840c03c0500001050440c0240b0045402401c61481c166007146c0b40c0c0030080c00504401500c4000a0500c0030140c0074000d01d200c100c1d82c5641030350701e0b864040001d403c980010f90310b0340f1511041982505140c400e041c07036284031b5110100d0151a0804020504c0e80700c4e420800100f031484140f0f000590802e1090651480703921011a03014000a10340c411030302003440602100e0308180000c5150b03221400301170b030400d81001c0882000201841c5022540c41041001080300d498142540f00e50b03070703001043ca4014500c0c401d416114a6480104100544918070040d6000108000000c1101e4840c80101000c80028044600f4407040715038950540e0030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691807868 1250 691806618 691806623
    0x20f06070507091b0903170f070c0803070b060f1807030b03030309150c04030b060d0804050907090602070512070902090a050a0806060307050405130b0c090604090605030606150a051c020304 83
    0x100c41403140e8a01d110311456130107410b001d103002c140c140d02d16200c015240010306100d15820600059240c4565922000c40e42a04e408c40369030500350750340710032481d503a52100900f600d00f070910502082d054a4007884171100c0c80c6005041e41d1420900c2c83c641107006d4400b0304041c0a141c0e440040449980302072000d03503c80d032800b8000c0d04500c800940e000d455901c3c02450104030602c100310500009540e41d03601600100c013a0340403103100665260008992040350401580070410b0f404101180707030310400c1d0341c007070300c1c0194241c03070000b40d07100c05110301c1c2c00854032000d1554010070428440c40342c25901409000c4001804116100e0362100800c500c90825046510240c00000810085003005c1040c58020b1005907001c000a1505120f054940c161150000349001880030124864030301050540c0d011307507030062080d65120ba07030f507a818000307209038481c0500a000c1c18001404a00e002103840110381080c521042c580004004129081d601c1a0390704d500010080d5000310340e1018620140d0300c90f52 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691809118 1250 691807868 691807871
    0x1803081b06220f02090c03040213020f16110a031506061b0201052b0b030118050304050d080d0219110a0c121103190308071b020f0607050709 62
    0x30005041849034035880140310680c4040305115603919200d1014411501c81c0c107400c0c018031503074030f000e48210f521000701a520110403c00d100d0000d14050045014900c00ca0b481d07204502000d1014080c0e01400c031212400310814080e26100c0c10102940c088414800c7c0c8060301404100e50002d1403401480d0800c0d03e05960088410425048510450001c2c080c14100140c00910b0003004580b40028aa002810450049a0362901c010845000300b13410b44010809020074050f00401001440ca61a0707452180d07013001c64407041005000e5032071107010703000809107103003074104001c0c8050010f501804981446c42044000382e1603c0910250120307401c4000c0360203903415240c2c4014606412910325101c2d07504084920310006122490716021602c0c10440c00c4403142c0107040000c10714038910601d6030907003c0e0070110700d140b010101c900440c45229031140d51503034455007402c80b2800302c00c190765200c07481c020b40c28101600d0b155401d04451800280480d2500303080da903400e81020a19400310f0300e00f5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691810368 1250 691809118 691809127
    0x30303050405190c061101150801020a1b020a03080901050f130303030e0c010c140a050118021011060601051c0e15092a040b060f180a03030f0e01180308 67
    0x304043c00802c10101425005400c1c1203100d49410542003654801c803c24040c1d10840307a081000203411552084400c5a619800340b036489031a60701039402118020001108100d54411100d09102003041e9150050030310441a402c1d81c0d00c0f00e01684c003d030300703c50600c04280b1090106180d11001000c20032054441000c1c03007840c519000c1d090303a0643c0d542500940000c0c0c14007403240da22460001c022500901e04070265210070300c605040075082d02d00540340394208070320280c18103044d03004c680e4124829115000c3c0149840c008076020b00f9501c00301c01d819000000491120b43c1320314040c149550302201c10440480b00c5500c07e404030f809118486245401c840f507002c43e201c0100d600b030390303011905101a00d0007440c050102500b103040a4524031441c40442e00d81003540d01c8076441550f42e41c001402c002d50300c030b44407070039402150401040c5251040d42c45c600b10b5080c0c101202c0c030504599141d251030094030f02054041c0c90800c001d44084c4e0400080008205a4540001c8402d00840c0106c9590390349 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691811618 1250 691810368 691810373
    0x5070203010b06093010090c0609060516032109030215130303090804030501110309160536070302120a060f1206020f03150f04090221010b0a0303030504 67
    0x252034009640c544948401c0c0070381421501c1d503e8480200355014000d80d8101594140002000c01a250040c5c1c81480b51164262501c8040d5001303c260a000f00c984080095031803208951800c100e01030000080d1007480078211034a0400650601a8464103120712840e01c0c201c489882c040321003c6584e41b680d11010407209154060001c07816503200540d60410b05d2802e0140d0004e61500041d0050415549203d1202404005d509440181d9031100081c0030300481e55400c5909034000383d07540e100c64000c13041200320410103083c3c401c0855602400441301c040050000305c0304e40340960414030f00618804e0807030030b5507950f06942ca881080da64400503101c01000220b00151040140041c4243d441c03d40140060400805200700f1621041e081a8181c08180f8248020b4002c103401c1c202c0140011083c031000c0d03448081c1500303042c0c3c0243c030b54007444170f048010070003503560842e000ba42003c1b4403005447c001f0303400300c1c440d81c46208880c008162110494081607580ca03082e071060340013903668070a0004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691812868 1250 691811618 691811621
    0xd14032503290f0f120a0c051804050a17070609030306081e1e15011415070b1906032f0307060e040207020f04090b0402010f170613020903030301060507020301 70
    0x101954800035680380395100000305409031002c3c1c2c0c2d102c1c440c5506143c0d0694564030403001c09001c0200030185c600015084c50200e021501502500340700310756190b02d400303440c8040c01c2c0441c0310301d8004000704004170540c1c031100d4a80c154005007080c400700801908010410754002d0102e043d00c42e43d8009401c0b072800b1426030520b400c0000e0700d841c52a030260b0b00202c01c080015409103092640085030040c10b16401100d16102c6591a0306040404200c000124100302070506052004152102c1549400140541449214a142c001c00a110002c007288800c1910300915852107244d88000451989030340300c01c4010484400c0700a81603c3c1044089100c02c4030840c480d0507614180d000f000002e0606801a1840c0000442c0314019540400c44500799a600c815440740c1d00700c0035000304101c01d00b03030502c10070410044405901040201011000c2c81d8801d58800d041480c555841c00381c1c170303103070f030700030400701d40148802d003500148c0074000c04496540a2004500130034460b1241c69807040709105050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691814118 1250 691812868 691812911
    0x60411030c03030418021c0b030c060f07060e251a0c10090f0b010605090301150f050d0807061401090e070617190c0c03020f0d14032503 60
    0x14041c0e0009592100703142c400106450a031140320b003c0a04032500140d41d03e00a009810030081e8400140301c01b4a4826183c0e0300c40c1040082c25000c1d10072024481d01441454804d0046904040c102008000c0108030039a010324a00300c0088217990415003000382c104144a200e010b01031b4202c100147c02c00003491140420303c2c0c80c0070082515414440441440740d1500038100c940000141c0303904802003000801f007043c20b40e003540311901c00d000d943c6507a4001d200750498001c86000c0d40c0f0301100c05c23000343c8006407140c00b102c4e1a90b4840c3d500f1410f0005102c103150078400101c07244001401144000742142c050b00e01c80e20506007070300e00745624040d483c070151030b03548000c03400c590403900041c081103a2151200e20406119030309550562507800d00c080500b1511001d0741c1926282c8034005000c55230201e1410181800b95084400304213024590585410348991070101280781c681907005096044005580d00c07451504000ba0703d00c1504030108404845480030200003a6500c007400000840385041c2d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691815368 1250 691814118 691814153
    0x1206080d090e1810230c0307080703020408031207030b09041e0302010b06040806070807030606120207030e0a0801150801062402030d05100e0f061005090604092f0f030f0a0b0904050604 81
    0x15242c80c182441c403c101391001425990800ca2703480e0004207000d0007030701250010203088080702d9135410100e1f40c0315404403050b5408400241000f0100c41d881c80c03d22320380b0780103035000145150340d8441c414440c01e01d41a000360450540d501c4035a440090303074031200038000402c1d072240600b800d072900082c000d03c070300c3d00200300c1401d00d85030542c1071204562140940300500700c3d034807005030307544902d04055071511410350041c1c0e848040e19401040000341034202640e00c0031420b50100c81c882e105c2018070f090711001d008000150f00c082d8a07800c84640f5816041040301028016a032924981581c0401601c01c212482d030146e40c25510108441c0414400b80b940c0b09003000898025402d03d4000902e01c0101003056108005d0049210102c65079540100c8008025100040143c0c2c01c0814401e103082c400942003606184000c030070340824651a008544564501c041c07070611b1695055030024400c44040c00d014030a641d9020341c0b805035100e448031580221300074001401c2526040c941020042c041010310f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691816618 1250 691815368 691815431
    0xf03150f0423030304030819020a0f0305010f0513021b030304050a0b160e01210e2103061309080d1416110a0b1e01061206080d090e1810 60
    0x820b030420310048141c90700190300d450564525212050403042c4058440030800c0023074030004490500310380010103c06900c05c191030900150307907104030000d024400f038403400340c02002c07140c00000041c9031507001f080c007080d1200c50007003a2054401141d1450300111404c491650059400f1000e05c00c2100c0303403941c02801000f05921038030392028020034550040c000d4a052180c40702c809640202003031a82c100010b58400204420301515007655070390004245008000080c81003d1001402e0342c1c800c480c802c903000b0708522084200c4900a0004111407201038030091402c0c4070400c49418540299508040e803042454410b0a00340d01c4003c0070820046420180008288490711b114800305d00400c03950340041c0c2c0b03d1225940c440d66540c001c070118100b599400c400070300210300e0303a401401080b40c602814500300300058480d50400d503102c00207008180132821008003001804002c00e00558000a0510b85102c0b00d0308041450f4a01b0100e00072081d2180d456540c085103443e45102d4151030054200310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691817868 1250 691816618 691816673
    0x1d010f0b0604030305030a0908270904170304050307060204060c030314060102070b090a0f03140d0207080c0d02041803050315040219030c1b0b07030612030e0f03150f04 74
    0x4001c0d1107544801000c1c00310100008000008039441040b25503000300081c2c0e580c0c030000101c1140c424000c102034110341115240c0d00c0d4141800d4044500c1281d21101c0d002880300700b11042c1903035810042045074640300401900c40002c0043c00544001e0216407519040540645001350a0340c00c4070303180c184d10101d048100441caa034009081380494034110202c9035500c1445012039950701c116005900400c1c1c06100010802500c0700c0c8412101300c902d0203850f4643c03105501280c580020f480740142c0e81e8131a4029060300d107007031440b500016200820003e039455285000350352451841d042600422408010800302c4070480f4022001040120b038118a07114000984440c4088025025420035a032807170070a041601035003085410314004207107852031a039980b80c50800c1c5001221405e002904004002030b1403410103010855580c1d141d21100b41c1209440f0900024070544400258584030312000c00240440920199002d400c48030210364040c680350420082540b0180c0112250006468 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691819118 1250 691817868 691817891
    0x12060c030609022b061a0901020f071a0d060905090c0f03030c19050a02030f0c18071e090b130e0f040c1205010605040c030c0e060f041e03061d010f 65
    0x18940b4031041c42c03501303e04100c07114280c044028040c03504160078000607000150310032600340303001e4480719000341e00b118548034580c142c080e00c40103c0c4c440c4001c2100c010b01040d03410300031100500b1200c2e110602c00102d66584191550036100d080d52031820390f400101141c3e03820700f049081d0444111060740294a4903101c1500c240d030780d03101c0e41016402101c9440f419030070010107002510040340c005085500710b040d024041902d130744042a4461060b0b0004507030140440000c4c0429104e440c4680307903001034807151030103000b103881e018140e1001c00400b8440400d405e141140904444e058405140a40b1814060b40040340d600180070180520b1a010401c000604090061425586030b0040c1c0c0c450f440322490514007510701600300d160b1041c1800728440c4d10f0f50b17243e44405000c0b0b02558400c001c2072141000c1c00322500c03a0701404940c502c0108002e000320305940c805240c0e481c044504408401d50740e5210b8408840070310352038501031024401c00e509045400d024210344050b012070100440b41d51170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 691820368 1250 691819118 691819147
    0x9080a170709230a090e06151503010605030a141905010b12041403040e01062f060a0207170c071818020d03030207170409110c07030f0c12060c03060902 67
    0x80803043c82e002c4070810640180d19800f940c4002400e030b040341401482d01a84001d61506411035100d0750070100008010990b250206c4070107203540b40e44d0460f40c41c503400d018046403183d1000702110312640d12078191401c4101500b8406200b1020740c000743c0400d0003c207100304250386040c0c1c4104d106103c00c0c008200ca560070301d444a5040341d4401c00014100c2c150450392800d5002d00d170b02034114001c5100000030031940292480b0301e40518a2080711214900c0c00c003440d0240e10080748041c103680320030b0003c2c40841a650040101d90f010300c0c604215041d0803014100d082c0d000c0110313000b45030440740c8200b00300351401c0780d00d11891103000c03001d12000811403100c040008100348040d119443c02c4e5003d1040c076000f40d04a80c811500004a0305032201c5000c40c0003640d40c400d01c04c00c0c4102d89800510b00030803841c10f05031007050303403500054000145076445040004801034802d44694904500020710a00041c8801e03000c01d03c210b0011521032140c6401608903181da074444d070034440c0100050510749184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 691821618 1250 691820368 691820399
    0x12a050f01321003080a090501090501050a121d0a12020d020f0c0d060e010f0c121e0209010207080a0605010302211c02010b0d0803101e06050d09080a170709 69
    0x702c8114441c140c2d41c44442222401190f03101510b801c030002080000303668040703004000c0c0da0080c0c880e014120b9503500112003911841c4201c800188500505944001c1c040d0030080d204070104032089102d51301600c0090402481aa085030b101558040076043e5540500000c1c1c0070300311a00103072540440140035a502c4918000c10b00344241680c1d0324810407c12250301c901481c2d440c140c02000b50400107030141006180c5031105101140054164001c0c0d0549402006d4250440a0360b92000001c00144100070350805440e05041d030142d14404101e1079810440030a1840c064100414654510b005101ca11203401010000004020103500c140b94000507140c418800c6d1148003407042500150203d00601804000359842000481d080e0700b8044104c024600505415084031440c0c0e0761114401c51560f1690310281116500f010200071b001c0c000d40140600300c0c58880d01042000c01d0303580700c294035801510203102245414446000c010040031510340c5c40443c03814450711484c10000c281c0807480e0f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 691822868 1250 691821618 691821701
    0x1f09020105190c0c1202090f0106051c0b04020304260307050a120e07181b0f0f030603080403080d0b010804051c0e04050c040614040e0105012a050f01 66
    0x5902e59580e0001e100301d06a425850700000204103241c0c8032580c48011690350300042e8401c2c0750a03000b14141c0d8100071540d81c103c45030303500d88626000d078101403071050080e00d50010101c140e4031607014001c2d490b21700046104602c0f680400d4000c2513080020307034408043c0c8245a103400018020005440c1c0c0200c01c0340c60304003040c103052002c600c4070301c0307484003030101d05014038020b01550700c001800003104d1100102d4040c2c0450280191180742c0b54031855024a000c0140020340c000c866146402e000c1c2000c020650002d20f80812410b0326a00c1d00e41c090f600682c01240c1144000926482e00707081c5102c2c6106c041d6003480d1071802070910380c441d25170313540700c4510007541803804181811080e07008150115420002270320911003450405400c00903034000e48158008118140e103545211407a080840c0d0585154807141d209903420000110303584078100c02050307280164007400c1154a41c4641e000700394a84a000200592003403890035030b0079075081003100503406c681c0b040c070038900d0302d070780300385840300c01c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 691824118 1250 691822868 691822897
    0x1a03070503181506010f1b12050c070f030218062d091005091006051207051b06060a050f060d09032615010c050309091f06021f09020105 60
    0x1101c105540a01c0a22400302d15968400c507034102e848400026422441410240c0720440d203d62907500076a5204624030503002d0703461403540002c001840d81c944616811899140c140d04000c03415603042d280c0800358004011900c03506004004624043d09028a840c5506280c0d01c00c0c0d003001c0300404e00503080820303a00303500c2e0340d810030311000c107440d01c40d0764a00d000b070090800701c860903c104000c681800c2c50040900036000e00c0009409a0050502c280840d4800d40d580c0b454644403207001c020440010304071f601003000400031042180c600e1030a0307420103501200a0081760078a00200302012415901042c0100e551110b4003c45990300401d0b070b42040f030580710100e5808800d01d011900b581d41804840d0140312140c0a0b441001000030f1054420404c4414a81c3c01803914001902c404c0c40c041c3d00241030f03505c20401c03030040741080f00903290801c000e000d114074400540120280101d040350864801a840800340d164184000b0a5905c904100306001700074040198000070080d200b034043d49103410303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 691825368 1250 691824118 691824121
    0x2220f240e0d144603030b0102070308190206060301110a030203092817030411010c1403040611010614030c060a050409150608071107170109060509070f1a03070503 72
    0x2091078500051142441130340ca211181001030215840c240d84107103080c48484540d403d00c1c4c10500344c82c4004425028030070304110441d54084020b0a50b00c81280d04501520200100080000d03014084442081102403d0750480c048001c0c41c2003001040d9910076030600ca00140118020720440f102460b40b803a015940340e0711002a0346c50014002a840c0742c1041604824441684003004c400010f8485c0118a0300240195a03052103404291030140203041c206516848640c05444a68406407062084112009c201450781d0b0541e00031394400f4000c02d66241e40042c071031100b881040c000d40316040c2d000f050445000e020941d2100480d10640c05264000340540e606401503081e2402021036001c00e10401c54001251007003034115100b040b010800b45408900b199018a85100d00c08485900400c6601d10f42000f5140c44140741d4001c2403103568030b0070004041600c50143c0d900c641031200007000325615001501c50800c1c03950344a0305940c0300b00c2d19001d8860b040802100d82118052811075200d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 691826618 1250 691825368 691825373
    0x406120b0604092a080f0f060a0902013f2c121b0106090204031112101806051005031608030901030c1b0c0302130c0903020402220f240e0d 61
    0x305004e90010051449035031003001e00c0c11030005a03100010b84440542d5050380710200e40c06c06840d0800d80003400708800c100c14260000064905401c4d40315140480c2011103c42e003174409030843c40000c500520360703d400024800f0701e40c8034082112610107040040103185004072194503145444000c800c48100042c01c0442e000f80744806061062102000b04012592550707400c0080d4880d1200b140c1c908654036200720b0700d24045655900591801c40580012400a40c1c070b503000b040d60090038256400100d10a0020a1042c89018480e2840c0303000c10b281c490602c81050328181015010034599500e4400c1800100004410380c0c0c9448001c3c200070840c01075100d821b0341d0340110b924200549141c40c140d41428048800c0561080724026684643c626189542c1c001c03d480c194503071100411b04ca91400c00040c286940141045800240c0e1004800310051518000c82102d41c040011603102100a028840411810321254444001e5850011102e000301a24a06020103050b108007902c1266805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 691827868 1250 691826618 691826693
    0x703080a1a0303120f0a061d0a020d0e01090614091c1e050919080c010810030b0403110607020c0a06050d060b0c1e01060303020a080d0b0406120b060409 67
    0x3880350000b0306603510f82410200104c034a007000c40780c1e0742901d034441d4082040403140340701e81002d484804103070b0070884e8105440c440401001503e022482c6500300030711020598184144455101d071200042a04174260a00c038080d034440c06910b00d5054040000d1140700c0d5000101d808040b06a030301e0501600d80140c0055860300450044c0341250541400c0000d21a580903005081d001801c4600c0003282c521801034400c2e09a480c056003c0c243d0211440d00d451b58082c0358a140d20041c542d10107900c19841b03035103100c4070701300586003140401c00300350300c042c019101402910703442040e520003003a0143c440b00004850801c40e101d6403042c0280066505030110180d00f0800c09400d001e40407076507800c90050b04a5507085604000c590b41d40745440d0045640c54103005600c01c8a800d54010000c0d688103449076082507014a2001441941d0b42d20b524070240c48034000c0600030305e903002411010102c141801901541c0040400344240e02d07042c450380029480290742d00f02c031b04209144598079800b0004100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 691829118 1250 691827868 691827911
    0x4050619150e040f0c171006030b0a03020d0f0b1503061b0d0501150f05211f080703030305090303091e07080601030b010f0605040f120206091804050c060703080a 71
    0x542041c1000241c0a84035842d411804691049a071340100c41040585040d1a020050300c0708203803850b075407c08000c2144070341c0040400c444010050b81c00d080d0b4a500048a650210108803803092920404000344260b190019901a4075582c40d06a5190f0203000079440c1c1c00000c000703c6683c40041213110202c00d61009035084880245800c00280d6103800707505103030581102c00e0070001011407214580380740c4a1000d48074019162440442c4040c0301803d4021400d1000300f0720035420040710324220304c0004000740b0b88010810100034010b802d003141001401e548008056a102c1d42c010414006040380000380803400f031980c1c811441c030706490000301e542030401c0b9512482851003220b00100c2449451100e40e4100c8001c0301e0150380c015a40c034016250b40c0150312940c00405507460b01004141410344022414501c0100240e03d42191100058a020402095441c020003a80200820090200f0150443c1041229400c3c284009903400230103a03e0002c00e858807860300e03004109001402c00e074001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 691830368 1250 691829118 691829147
    0x3030305190504052107080301050904020d050d080a1508030a080703110a050315030610030b060d061a040c0801050f132a0f09050619020c04060902090405061915 71
    0x5020906184c10318940c0d4007100c1c1c0383d4185490710744c055085081215421594030942c4080c0683c1140e113400108100c4000060050740c0040d900ea4144d0300040043c0b040e9802c02c49113403100842801e21100c280219a0000c400d0034041d50402e41c00d01140d40d00105503001d420140c503104c2110b40e01c1d954101c0140a10541c100081580405c0c1c0d00c1c00c9640200c09144600b5045103a50442c01009003059910103040c0d80706000d00c04541000e1000c2807204034000d5100c0409065820441e900340e030703980708035000c4162784440001125001c1280b0324207030044040000c65881d044600b541458001600e07440801256071044d02a0107080b10715600c0380e001044480e2140003c107801c8031107803a01da50720424404240e00059001111250014060070f0540243ca00180c4001c0c101011441d0b000890660500d41c80154418540c919640b0350b51344c0903800180140ca07002684030340019040c0304c140c40018000d80e208012a110402650035111542030480392654801c0e0341031080984140c88500520400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 691831618 1250 691830368 691830371
    0xa09081f1d0d0903050111030f0601260403030c0e04200c0c0d05010c17091c020309030d0905030d140313170a09030c170a0b0901240e0615040303030519 67
    0x1c610003283c022207400f003100d004000a201d010706954484095200844204103007010f24030201d8101d51041c0c01c0040400c5900d200566000001c1c0c400c2440f0035002c550450000742c0302c108170b010460340010a00c2d40010705887c01d100c1050b814900e02e812230140302d001f00002c0c40100d42e815a002c401c10048031f4503140a02454a40d98070f070f05205003c0c104002c4401c01040c440080d60a82805400405110342c41006c00b50002041d44440100740052a2003170078114402070000c0c80d81c07903905006007016214030351100074410f07142030185818145102c11103014001c44458540c682444482203a40c0070340f101a400306030b5941c0c0d10300b1040300105413464141480000c01e4400b66203420501040940e0b014600c40000c1c240c4e074914400c441183c5000f03020311900080e29020000740c244d2040c0380c01040311310010a1600516000d488000081c0954130300401241c175003005017609280c0d00d25004a0240d410403503103018034807005800c1c429884002e0406589100082011a800760f40c01c5070040111030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 691832868 1250 691831618 691831633
    0xa0f030b0a170309210304050409061d010516021504020d06061a0a0314061e060412050c040518120703050909070309030806010e0a090203061309080a09081f1d 70
    0x46440c2e8a400c8411158041d8801d480b1450b40598022514605c14001c42c0c0194a46405c1005000141c003100c0070444445403140e0b50003070010880148514841a08000040d20789841484189016407420200c0295004017004d0b10003d417000d42c8940d40613805403840c1c2d00d95407441c03a0030310041010740c0c0144445400001c80c040d070409908000e140010310b9903230910600c5e04500003600327141c400359003443d8400040b21134901d89103400034129030400c0004140500301a500c40750300c448000d03128011038072a00141107204140c0740c0351003595001f0080141e4650080c004e0303440c8642da03641400d6807124500d00484c0d2441010700c10402c0700c0380751101038404011400e1551000d005442c891000701c0c0807408010009003554810f2140310a01c1200034000c48c807213850f040c1040020b41c0040c045a0b0080d2064000040e10100c80c0206070025102d00031003541c8424008006011040035080203100f504a182030300a00100030b2030300c0941012200b000520ba00d075104175040d04c0750491845c0ca1150003202e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 691834118 1250 691832868 691832909
    0xc02010f061a0c12040608073b0f0a0603061a0301060503010b03131209150f02120c0a080a0503040c120f020f0d12030203090c09040c12080f070c030204110a0f030b0a 73
    0x20340a000d4070329030b11a00149c0c0305819045400100ca0502c1c1a0300911070140303504c119100a41e100e00c0c11102408982c03192070810041442c240254201c240426150f102c00c204070014000704d588208103584e03090b4150350401200400c0c0b07200c18400c001e405100400810407200c40b40c00500c0105600034001305084c000040090700d241614801c500d2004e91602000341154040c0c503c00f010469030ba800f404910a0122208045402104d0f12010500c00c0b1100325001030342c454014581101c1c9625015140d251510b0210030f00394650304140b45c04101c12201c036001070240306c165010154100c5040039200e9101c00803030150f00000201809aa0031181c8100c04180c00da4000d5000b032081d0401d842030740001f40f0a000940700d044c1e40c01880640346003020401c0d00101404140d00768441d08160b85080c000080440050b00003002c02c0e644080518020401c5241c58400e51840e150020102130130300c002050060440684041e032001410340b12111621256260300c2c0c03003805401008500781c41020041e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 691835368 1250 691834118 691834127
    0x50f2d060c0a0b0411030a03020706050f040b0d0b040b030f0703080d0b06030a0b0901050307030807170405060a0e0102100504030e0d02060418060305011d03070303150b0705010c02010f061a0c120406 87
    0x16034045d1003458010b107110303019040c0443d6a200903a0580c000340403c0345400001c6550750b0040c51010620907003400080b46485044004261800b07851a02283e0b40d01000b003000100c4400c5101d031842030b031041c541034242c0480828250200c90b04a001282c0703803403801403130002034244001000d601040020070044a4425940a81c1a0000a664182d65680c1b12410f250352803200d40805040c07194107100e40c0c000124201d51950132220b108640038240b036660340208180d50080b000c46400b08182c1c100074042075034100714210150380074007400c2c029400c05440241261080008080c05455140905002d5490b40b20494000740001c040380891050001d40000c0141728502007281c00e03500b00385075070501402140342c0390248181500030b03520705201a0340c1030300104010484588049103005001a0610350350303000c1c04256015100114080007208070090071100b035400881802440c015041c04070240180404038141c03410300c5a5642c8802c2d040c6058580411410229454000007501083c01c80c2e11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 691836618 1250 691835368 691835371
    0xd0b06040305150c09030a06110405030601120b09010b0a121a0c0706050c07020102032512030f0c030504080904020c1f0204032108310c050f2d060c0a0b 67
    0x4040d1682e0f010b0b214005a00036030300c22118070755815404015028046a013039400500c0c0e12143c21a09032800c1c1d950700111341411f100b607004440d201c0020b28204107202608008a41c040c001ca0000c0103506000c10024918158a000e1103160f01440c8081e84100021701e00c581e400c82908420040c464035010305800a0b50740400340c1100c025040c5000701c1c40340065442074480c415816005107060404100c9407a4000f030b5024140c240088038841d00e40041065586c41c680b41c203145a5000c980300d9001c5400d4000da800726225101014a018204404226a035066034002c0d001298050b94441070000c41524002040d46001c4140591200340c0340d01d100f441d40104212841400d9004254480d0280f90f801d42081e0380c0070502041809002a4090700c00c3e521408a8007040d19140c42e04601c1c1000851001d84c00c10412168400441020700051500d241c1c0c0c1048503000f12442c807081c1c0e924403000c410064081f00c4503200103420000240c1d507a910b020543d1040c2c00900100e4148c10258100240120b50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 691837868 1250 691836618 691836643
    0x6181509010e070f0e071803060f0b09070f09030213020c070b04050a0e010f03060203040f24270b06030c10050d0c030e19170403030224011a0d0b06040305 68
    0x1550f640003d0303001c1c09420030011660b9403003105c2260b6980450555400d070142c0240442d010100c81d0200011310079200d841200054030a0000d0641421303002d000d41c9540c05440d00007441104491586001e41c80b00c8100300b0b40f13506039154907041365403907074400c068003480c2c07001c1001e800b910301d01060410781030010700b044660485000c1201c554a088100c0c815a0038010707000c0303003c02c0700030034008903d09400a607009845075844600d42d241a85400c1c02403c54244600c8100c0060086ca501454a60003000458a80480c02454800f031120b0040131015040b040106540c00040c006480c0f590140304480c402a4050807a040200031406d0003401644460381410442d840d0050108165100e442895080e490090040200b9006502c4000001c400140100d0321201d050810641c544600e0010b040114801e0300100b00800f4a2074440d480411003022841520104500410a21a6600c01125002d980340c0c062540e6080000c040300190280420091f00010700040c004200400004e034000c0108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 691839118 1250 691837868 691837873
    0xf0f150c1b0e04150b241201060c05010605040c05161e03090801050c03010f140d1b051503040c030212120703110f0703080301090b0a03051005070f0206040506181509010e 75
    0x46912050030403980c121560907041048a43c0d08101700d80a040c821248412541400d0300b0000d00c1c00fa5503401c40803d03001527000800742c074600000c0010034010000508011241400300b040c03424002000c074011201c0301e032001c051050a4006104141e080c5d80b120b411014040d600032091401c014180140c64482e560b041d41c030309000580c00b4080401a40e05a0348040c031011400740c134190303000d40c070801d0503000c29500c12506d0f2002e4000851304010b54800d440020b880c500e5282c601820005580c03209800c011600408100b0480021081030f000d2054982c1164a40800e13506601002c4c5048640502c481c41c4a80c0003544806160b0060544017525407124101c074200112071803500d0b01c5200f907100c014181c0e0002d1005102e1800c00390412002c150717001c0c000b954556602d80f1803501c0e010303d40c01e04084141e561828092034650002c0102003c5609000030401401c040e82c8480d55000d0050008900d007402c2c0c071b5581200d100600030000c4003400c5080441c1e1a00b001c980171402807000c40f84540103803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 691840368 1250 691839118 691839143
    0xd020a090f05030c010309060213140114041805090a0f260a120e0f100c17010308070b130803180c03070f140d02090408040f0f150c1b0e04 61
    0x249180c00d5a042502c41c041d002e011010301c41d50054000d84620b9030200c03221502030040e05c01d06000d0346120030041c50382e004020b040180000015010000804540000307010801c41030002034005c42c0e0103850305080b040005040d0b600c00c030803133044c010040002090840c1c0000300900784280c490b0b00c4050b21008481003c0c005458604481e41807061002d000003180408207802e2a612050340403030840341d10042911041a40c4616241c00d1020000031000442c0e501c6021001c010f5000304c4139220070321840629446941591506e00a5018001006080910400021b80d10000078905403003140e42c800f205c070381c8070304044070100c00000700481041c0c0c3c1131154811054803498001040011a8109a09505140d0500c0326480240e5500000150401188001a0010b8843c07107806480f4600813000f264070b03181401c800c641e542c1441d91081d00c050412140c00e00000d041e40d21400c0d440384031800d0203d0810075500d01608840010310201410841d02100040c0750151b44441e1445117110300300c8032071034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 691841618 1250 691840368 691840379
    0xf09211204081c0c060e120f03010905070203041a09030a0f0b06181005040902030f151f061202070f05030c0709050a14060d060e1e0d14031b0c030d020a09 68
    0x2c00000c011039000084c0c1284000c030104000e5071000d4280e00b80403084e1641001d50058210403984044540601c45600000402c85400140305054112947d88003842c07030280b42054555a42684145035001c2a0000402e207103190350030004c0c003ca455101e0440480340e1850f042210155008540c001d004400c4401403a80d00310160380014800d01c80180710380107460614041c08010000240201d0301445042201607040314200408588420181c4a89e41a0316245d030f40a51454401580025000d000312010300c06035030420b10070440c4d03866644e4016241c913444c1c14072500040c81050054080d000001e01180068008242002900c59403002408a0344421220100722895212400075800d100c0010030300a01e02051a640c0490151078046080080c802210341402c0125160f036000100000c6411261030b418003524400080701d01300f03689002190181221240301c01000510528040083c424003150b480701520310030004107044036240c0701c0500010000f9030105245002003071100d5800180b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 691842868 1250 691841618 691841653
    0xf0b040c020c01140c150a050106090b07050d08281b051c0b0315150f10140a050d0608060a05060a1d06120d090501030c050f0921120408 60
    0x44403106035280d0002d19101130140c081030b0000181800c1c24095611642000031064a0160041240c2480000c1d1540b500c200a882c62400380d0003200690300510401001c1580419110500c800c1404c2189559882e45d40050807001505240c54180c070608030344980d801d585901012503615140f1102844810b24a025991401241445960421440190000d54515070090310700d0f280090222801d192543c0704414030100226130880c008500c40e4403640462820420100601805a40d6018101c0c1d8400d8002d158045c406400d80003007000050080341c0398815012294903400c001e00420031241c45a441d1741d210401942c01100303403400d00000c01e0903407901e80141000c80341409940502e107208401240d9410300020561a400603079030720350f1000d105c0c003030140000010580c0c2d5540c01c25410500050215440c442d00c101c100a13050000f5207400755031504603905410202c40314682d40c003e20984680c1d1100845450b0044e0003440482da82c1003100002820545400d1001e960703910200050490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 691844118 1250 691842868 691842883
    0x506010c02031f02090901080a06060501080402010f0f0516050312060f01021009080f0d1d03191101020708040e1005030a0308010302010c171801020f0a050d0809010f0f0b040c02 78
    0xd505400141d07115101c0615902c4043c88850600c0c03015040030202400105003200980c06044240c2101d0150401c212461041c400500004d00b0130440300d0400d0f400003054014002c02410070700942802d0321503002d004806a4107840c50581104040f5071851a0280c0c80c0e820501d82c150508110102040c1030785095041442070910681c01041c807000d0005091024141281059602c9e00c020814002041d1030000104003c4d0030405c000318402141c00030880701d03103503945c11014680c1c105125441c0d01c0d881050003049a00ca40b4030301a1018082500e00c80c3c0240329200d801003188a0000380010041c1801060302e01c165050f42a00b400701d0798a00038161900d070403000040000c0d1640006200640c00b9815550707207640140c200ba21403000c043c0a0151603800382e015a20020707a050040c4150750703410403940118003c0c440c0642422605030751020381da1a80744090b8828031000d08000340c4080700951040d4004c0c1040b400500001a1030403001c0002d02d000f0602074051410400020001400080c07581c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 691845368 1250 691844118 691844123
    0x121b030f0f0a0909090602041e031101030902041b0e03070807030309060f2303061c0c051210051005090705181005040e0103061d07080a0b0402150d050702010506010c 73
    0x194909200300c0c0c40d07110180d00100120092140340c1c440821110303024450322403094132545005070b85900381880791071031240c0828107a0b00c8142c51401840003510008440041100070b09010400380c40f1480020b000d40f00301e0a08e00141c85484c10315018030b5500114680c3d0242068041e032f11159201d2000a45441d00d41c000540400c604d950200b0507a1f20801d00c8208402c00c900c0d0200c0c0e0b011141c031a00c9108542d03440b180f440240080180715092502d1200505900c00034400c501c1c14494954401040b084244550740c41560444002c09220400f401803580300c1c000307640c04010031301d09500040310440090164501449a000000f01300a0040044400940c40192119017185001c010802d690342c50142c82c2e001c11405200c0026034482c48180c80340078500c41c03800440c40000c00488800c05d02183d4034201d083da840080c040140b04404a0b1000f45183c02c5050041c0565440c004500f513410380e810010244040010700f030f03e02d000940e220340d002d54035a6000748000d4903594011540c1400c8034401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 691846618 1250 691845368 691845397
    0x110a0507060e0d060903110f010c09031205040e09070815061c0c3506070504090506061902010f0c081504020315060f04032f0f030708121b03 62
    0x5001850155181e080321078001020351500000f1555041c05907101e2900c00c90102d821003051184c4084117000c04041020600020803865100007002404040c59110140006000507100210140302e02c1c01c40b806400c09101036181810308000d850b949442a2041000500505480140f442e8000034603c1c06400014a4200c02a0030005c04e0b841d0010721940440310284280301c0050a51a041e80c03410b00c0303da4000001c91000030101000d0800c1002c01149845c40d00910304012400390030000741e40984a128200003a42d59441c8080f07040c1d0b100c1c002c0000100c010a03001c858016605402c400c06e0000a00307024020842000c1d015900b80500f90b07445004139001d40c50b01c1446007419806903600100b80c034142e8500101103c04601241c0c400582d003000c9620014051050055500901840921030303902150350103a605054007619051448030b83c81865044042810f5550030021140905800c90a8501194200000c29665845040314030001f081d034010240ca15003001c0240c0c1e941c640b180c240b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 691847868 1250 691846618 691846633
    0x709020f071101110d0314010801060614070c03171b0a080405040c030b0405041208011a09060f1c051602030f0306041d0d03020d0e0a030e100e0d05030406110a05 71
    0x11000c08503040009928104550100344d5000c0c030808001020340d4980f2603c0005251181d0302d980e10580740b05800c00300c007580c1042da040003103551005001c01d40b003080c00d088036200d000720711700450301419550000d001c0582c2e1000075418050110001c100203003501000c00d402f03101401090380c8a45082c1c0010341740410a00042019040c103800480e11456185000039400307c0c1c00c40002c1c225803080d10183c9100303040352000c445440d04071070f03641d000d081c1f10038404003031104814204002c1c0c4a030619a074001c071800708000f401241c401c02514003625003501d180c00221450aa02c80c01084200c404010a17041c1084038609240080304899400c1c0d1200d0482d80707140e0314102480040e000e0101c10002c200911f007014001d40d0414000c0008511030740e517025036544100500101500c140c0d0304450303166004081200d0011350021102d2240700303000e0b200c1c0e0301a02d2240714203039041c05804140c0e0b500301585045407410482d010009105440560f02c0715500c42004805d11582c403505100c00a2441d03100d0030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 691849118 1250 691847868 691847873
    0xf11010c0903080a26010905220f15050f060411040506071407050d051609110a030507030e010c030905060703090c1a0f180405010b1c18060603140709020f07 69
    0x4c2c0903100785424146441c5540100104408004911410200a0400c018403849145008072a0010005500c0b52038900c2201c2c5642925a00494000d0090061000d040d04004c0c5100340440b942c0c3e50700d03a08020390314000da4001590803089031124440da00c3c0c83d15075040000608151020741750040c0249050038072075501c101c0da100e000ca03400f6009206504000400b80d440b00300300c40420b4400e10180458880704039a02840340d950b50402c40d0f0403420403c42480c03000054003550b8881c500c0c0c0c41d0207d030079154400250300500031007151f00c1c4907500b0011405061a09500295809441030046a50710b6446030380031001c840c41d94100410145c5c2041c0304120a2b00c100704044030b00c1c960048428a006074001e12080307164071036101e00d0360581c50034009d10154901441030740e0050590202e224585000305100600865482e40452401941e0300c030302129103e5415140641e8640c451410802e0944a04116144001404040100b80f2815602242140d050300039a18800b01a01c200c0d4103000c0903a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 691850368 1250 691849118 691849133
    0x801150824090304050619030b041107020f300616050f071a13150b011b0c050306100821070f0812010e091203061f1e0f11010c0903 58
    0x20b4000d500c1d0b88010310010a242e0f07a40e070001c1c6615070b811a28150f0682c090400030702070369030b00c04885120b913103095000e000e0601600103d9072419070403100d00350f0101504000401d100101d140704a901100700b800c1c840c40d454550a01007601e100c05045850300c4e580c1040308406101000e070b0100c0000c0c0140000652405048080c0840d54424200c000001240d07480c40e9503014804c823201110001d402e0000b0050040001c01e015040300c2480c4180710001890f0700117000c6d40000d100d030344002c10100840034144060300c11000c015200080681d45e050810442440c140801802211403038050b18080d112242c0304d003055000300080b5a1962410a8044e8079010751503041076106692014080091003048840244081d000c0c280301c00c404001403c00c802058606500c03844040040314bc00c005112095440300c181e4140482d142c401c000d4070222254003141c907900800038804090b0008a50b00000d03582015141c0300e041036035503909664204c001c6119080c1d800590070400800e08011013480072542c01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 691851618 1250 691850368 691850371
    0x3071208040b031501090918020f040e0703120306080d120f0e030c100c051206040f1b050d050601091203082e050f06030c03070e0301090c0801150824 66
    0x3400000e041a94544081040d0341c011500d07141c00f2850358030924020340e00301607260040c001080042000e00c4c5072441c1020f901c001510043d10454203554001c04e1590780743c100500c0360710aa0281e55641c0c2d500c0c90860b01c80d55241c007139000440d0808002055031200050300c81c2003840e166845007050034041c071141c00208041b900400031a600c03820503074044101000180f00300d0070400010281032803164101002c80c0c1e404441c0d501000410460000c4000100c400c0a4111b081194001034a00403150050001c148100001d0a1044415200004150882d0281c400c1800b075007000c0c0442c0c1c0d50346004440018042c040c0021044070b4101c01d00200344210390481d031200002804844a00070582c14002821582800c4417200500000034869400c0003052007030310203010381e90a4250b050404001d001804020319007410005a510742c005241d070b0075003044040d9900304060079641d07900c0b220014080c00b100300d01038a010101c404002100b00f4001841b400244990400180c030031015074064140340320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 691852868 1250 691851618 691851623
    0x5030a050d110a0c1e0b030622020c19060c020102030f15010c0b2e0302030703020108090304031b060239010504090e0c01091508070c02011b0507140f030712 69
    0xc042105001480d00c19604c0c01500f11101d0980d688105014074241c0f90f085030304076940c010310500c1485490b807609064400c1940c20381703d41680d00c3c803910300d5100c02400361032080c070340300d114400c00302d0003890038807604002c00c0d4080d01c0c050140b41d06262040e0300340e102c1988e4904202d41204001100200a00008808980145801e080141c400c2e11080a81030040e207102c44c840d80c56105d41010418064007002c0704010720310300c24520034610340004c1d4503104203100190501154000280c0c08450920480e009158030408a15841040849a1a003007103180203900140c815881c040703551700c22034410b0301c0b00714922003221031400c4a007944140c00c1c890100942c2d07040c01014400420702003180c2c0502a034620500c0020f108a6041c04001446942280c0c418036030700c403901d40141d00b100d600114141d0702800c41d003000130700f501540c40120380120513100441080001c1144017002c100340462440c04440d00051140c000c000c001c0c0c20028001100726940354103034801102003100c1c04108031502603050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 691854118 1250 691852868 691852873
    0xc0f050111010b010e01271701061d0109090c080a030c020406091e0b01200f0610150f110a0c0527060427031e050304050d0e060c0d051305030a050d11 66
    0x200301041400c40c7c0d001904620a2990a6407401140308001d1203060010045000720034208600010304481c1c03800103000720303062542c44410b2002481308520011006006c14000c403100042581002080f003003540354200d10840c14528000703009603050054284000795140142038032068119018018030150305810705021410112450000c003d05140d400e040da080050410340740380d11622030910400405050b00c1042007201849501c40d1840303103c0d09440c2c6401d18507a14218000d0030f0706d28680511307605030305200740b19140c01045851010501200d606840c0300c1040c44c2041081200c0300100d4864101c1030380041e0002d901880c16030812041c0b41a112011403164002c0082481e180d540160160f010500e64001c0a51032401081c580118030901e29146003582400d50b07460f41c44002d121400410081064070b0b1455960b900412210340250300300c02c48400c0c0d103035104060300e10380043d0f6800112040c003440c005010300b0301040032100306034414090003d0301400318041e101c0482010600c105d51 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 691855368 1250 691854118 691854167
    0x321010620011e0501090c0f08070305070e12010e06070e0f09040c090623011b0f1a09010c181a160807110306060102010603021e0d0c0f050111010b010e01 68
    0x4000140e43d50141c28903000001c11298140116041130740c031105545400c0003c8200e40da05d440750300c8008913401c61500e00e00891030703445803070003100c050185c500d0390760784201d4a840702d0399801415805085071007002c0d03003940c01c540e491140a4515000c01c0c081e06420078071943c0e0410091a02c9800304c0d03402403080069030341d0706454060100072102c80c0d13000700d40760f1750034802c0c4464107468151445040760000d00c0c00e01c0504800080c00c00c0c1da0030400d6002400200d0318408503080043c210305080060f41302d012071030590f181c140071150290411180c0c2001051940c51800e00840e203c1c0f86203002d84100500071040400e44089260b00d40e400b4030800c042c804a40071004000480800003001c206000c0c1c034030100340f12801c0d002c060404070003401e0641036a2500c7d00820040e110800c00101c260b2904103140c450490000200340400d4407800000d2a5180181020480c10035007140c0d00d05803003080e6542c0090407481c0f01641c2c22100102002400b017004240103480075885641c407100f450350a40610300d01d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 691856618 1250 691855368 691855391
    0x31b010f11060408070c08060403091a070b070806040e060f01030b1906030c1418010905091e1b0303071106031504020c0106050112060b04090b060403050708032101062001 75
    0x510b08190703012103003507400045210a0040c00900f0f80302408110f4040c0c4181d00745036902500416140c031603400c9002c09000c010144070664002d03249a0790304503030900350364500600c009140301000c03129184503514080035031044403c00284544900b0041c0c00107a010b0b421501e8800c0094401408002e4100340c001c2d0050b0304d02c01c01e00585009507c64042000c1e140d040417030f0014801c0d120b120701402005180c007100c07909540e40400c5811258110700c005160b4a400b10700e1810111f850505041c0c1c58020764044544c00c40005c0c40c06d00c1c80288400b01d18104090404043e145e100d0810003034103412074406c0c001c5c00c40ca41440215040400c80454401991850001c5000e03604200c2a044143e55070f05401c120701d58010000d12280448103000300425810710482c1009030045024800a041d5916541c90303c649400701110040c54011003103401407a500e2841680d20b920802c00194410780c0110303c60110700814107124181c60050f1104640a00304410040da0104145040e42e420b64803001480d00c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 691857868 1250 691856618 691856623
    0xf0c0803070803041a06210c18010f060509010c030f090e0f19020f07060213050d20090106080c09030a1e1115030103200619030506031b010f11 63
    0x7a01c0307102e807000c01e84915003401c00711a414410302c14409640e41001c00c10003195220408900136281c0e4076202828034081c1d07039001d13140c0b640c20a401500041e05a182070350152032403c6c007034100c07030400c07000c459001d45402d4111024002e0042541c00709112200e2040040d01600c182c04a20346c0311315010031040e43d02d0500c00301600b02510301222805450040c4a600341ca910030f07264445210700015880c0c094145140c065500c0317500c401804c05076010404025001003110000300424009200340314044460600c2c0c0c40e103105a18458001700020703411081c427803c003003031054104e50300b5441d41c9009d0b90f9181c403035806544c4000c0c25a641401241408400074152028141814003c004070007003600070303071030802e2401c03804c4280e05101d42c0c00c050181000d50804802c4a040d2039020340044150a0040845207148813401d042a6201394040f40922010040700d03040011207185680a1010703440b030b4403e15407200006460542c0c0150040d030200c07200e5000c0e00c00c507507a280051074034140c420141a410307030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 691859118 1250 691857868 691857877
    0x50c16080f070b1302010806010905151602060408011509050405060a090303020702090114010f0203040e2706150a21060b0f0a080a050f0d0503160504030b0f01080d0507050a0f0c0803 80
    0x64400b100413a10015540e00c0024240c0c85031081c00c1144405083c100040c0e007a480703c1040362006440081c400c103110380c581e0b680c640015801380c60b00d07480740d0301c84882ca80030740340c0703040c590501c030a0030400010150018058107000745d81100c0031341850745075034a4090207440040c80a5080c15001c00501006840ea1440f460007071a0b040c210700c43c40328202c4001003003022070180c40e5045500c1070106016030081c050095400070040004800c403415010916081c00e02c580409046501a02041000c40180c4200b132103480c04c012a58400c1003526000364026041c025000d090540b00351015104c000780903640407015a443c0182800c04404410000a13070300400303900070f05096042a00c0c03070001c11404005e2240d80145039000f500f43d2003800b400c014074a0000900c2d02c2000300d00988800c08440c0910101c4002c0c54006660b401c043c940134100328a041c400788110f9940b40300b40340c3c0f4852414845c1d8203548145038000085e00c03c140c882d4881c01d042100013142601c14188240000031540030800040c0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 691860368 1250 691859118 691859131
    0x702060d150603090c120302070f18060b0721110a260910080712060b03180105010605090108040c05040c111b010806090a1103090709050c16080f070b 66
    0x10440404160408031058481c2c0e2018007490b00340750391440050f2000c540001503a03882281e88840e588103040032843c000745584400c40446c089200842c07049101c1428241d82c921940c400d0020503a94008036400740710b4503102411100500c031400904243d0307500c400c104419a468981c0081d10115031143c10000c1c03d5100f10348490490450030401c2c04031a07405c0140d07410200c0043d00300b0203140c011940c50913010300f1400c100b00f0f1200010701030034001c5400e080c06014500080081980741c0240705c00b00e50098a114a0400e0300c20b110020500301402698180d510030341e40c1608041e0344030010b40325024003600454250010a60104031600c40344a90940109655982501c1c8680da00700b01e814100091501060100c0010f141e0f4036690300304413910340041041d5202c190a68803c100d030001000d4145d03580c090000000140040b14070005111426a4404a41000f144e103139a0714000182c4900603891070f040c0c0c040746402c0081203000e00500030504400980d64038040441e0b030341949400782200e03030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 691861618 1250 691860368 691860371
    0x3022214310822090506090f041415270c040207020102030c1519062103030222050102010c0306080601090c020304030b07051b0105091015050306131103031303020906060702060d 78
    0xa0701c0805800e01d020f0010f1402c4c00007008130342402c401080102c40e00812898040c5d5213000403804021050220781c0d007003074042094420062200c442805092021382d101e0a00300c2c14640e450281e00383da542c030142071030456001850030000b4481400081e410207902039055003c02e008070f4000304424400007800c04082c620341d01d880c0ca000c00b243c2d141344400104113400d0b645008020710002030840402403071200548070429144005140450107845040c0002da1640e004000c03c0900406551010040e500260001c1c881c0309010704d0110b013141c101c0d1003107414a52002004000b04051680081494500d40c41900d1429031641c50300089620b0640b4003000180c800280740c40700d91150703800305010303800c140024005820000f8515546283c00c60316a942e45540307410030401c2103122100000140300140c10b5561034500040c1d0112034a100d00c01c00e441028604140031460f00c0d01001311410b801d41c3c0d0b1103040d021410f640a11120040051150307401c28402c10001000d60b4440014144c1c410440d00d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 691862868 1250 691861618 691861657
    0x110a09020309010e0f1b060f07080a1106130308040b06120f0a05010c0c050c09090c030a051c02061312020c040504061d0304050105071b030222143108 66
    0x7098640002092409159001000484801b10186101d0000c10208a4210341c032401c58404448041c0309101c00100307007000c00079848407403540203c0301c20482d60300407060b510140d5901000380941e40801000400103201c541c00540091007003080140c101c24040d29103d81c072011001c4541c40c02008a625030120707440581d582c070400809002d00c0c2e180c04140d103413800c43c0f85100c3d43d5155480c0c0d20180c00d0361040040d000058401c0344100f006102c0080000e089500360102030401c030b0740700c03400914170501c40300f51040b104c1ca86074000191240541c4108804001c81da0464940c031700d06011868606046000751a60503806680c0c5001f014022402008000303114040c1070f2005004180040960ba259002440304010036078220095600c005e0300603070500d0700e6070803030f44004031102c0c4690002584100c00d036000301c445200c0301500a0121004a40800c04181c0103195440420740881c2e40d5040d100e0094120f842c0e46800d148022003040005201d1034603411720b0b82e81c00c00702d5000010b140301d40e001d8412 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 691864118 1250 691862868 691862891
    0xd09060f02030907031e0506090714010512070e041506030b1302071a1008010c05040509100510050903010212101d012106410903040302191d06041a030a110a0902030901 74
    0x2f080755800306400d00380305189c41c04030080160395100040090b4103000b180918407030603071601c5c1c120041030350642850150700354455001400801e51010a28081c81d8030380356030150003925200300c5040c1e0741c1003da40580c0a1145142d1140d041c0c0080a01c00000b094100004000300240a401071089030b5807569901d4500301020300041030340c000c00b08e484101d003190301049140c9a00000c420f240f00c5519082d6982c0e8460030200e400f9100b103200003800030a1031000c200d20880300c01391181c1580e118603079401d124a01c0311008000d40e8000e0103400602c4103003031100c0ca40011074000d0907000e9480303100c002c00c40d01c0b442084001444c401081d005c86a4190312200009070107003da415006040b0000f090469007000000e840c1d4900a07400028001c0c0340782103d1181c10621212010020b04090161603800b9000400701c40700c401c3c06a0b15107000703900b06030031070910f080b00b90144090040060028043c21407030340c4900c4107a0000413040d0303410001011000c20b0803a843e000551041e041c91002064070740070322 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 691865368 1250 691864118 691864139
    0xe070f0e01020115380301090b0307030302060c03060a080a0f1118131b17010f0c080604090c1205070e060f06041e09020d09060f02030907031e05060907 67
    0x3416030440e4500980403601c0307aa240b000780103403204261500303040d14450100c03080da01c03620b92522402242d1303080d092a040600c1401141070381c0c081001485003090a800780342d0f548403a4080180940c11030800104c50483c410f01459211100609900443d0380d80c0741d6040c244000d640c000d40d60b4201682e200c0342072080003100c054054a041d40c2c000e8142c40c002d500b1044160000e4035099660342c14070207203400c1c0302c3c0054110400c8184099245495552200c85501780d00350b0603d00041c03942403d03841075003d1403511810325420719a440e4400f9030341d1582c041100820b1403600440c0d0020521802160028805201400c05440740c0d00078140c160803e10f1040b17061800400c06403003038881801420300c54440d21300751000c9620943c040d440d0b90142e2031341144921030640155074200e1000c80e4000310520b03182c01c00035030b2074055001040040c0013158054103070311044640101c10b50102c08104001001c00e2101c003900044000f0019168009550301801e00f8020790307940c00150f0040d6810b00040070b01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 691866618 1250 691865368 691865387
    0x911030708060319031d090c070c08030405130b0307080106090b0315060d0206070311030a080a150614090a091b0f03181e0b0a0e0d030603020a0306050408040e070f 72
    0xc400a003107a6021014080840c00c030810024204940500c075006d0059148841c032454410040075a02c05140c4000120b446800c00780080d542d00051590000d42c0d0a004421602500c0b4060044215031000701610005000411000768251117840760008680c1d4082c860000503010100000c00d80c40c201800b010301c0c01042d20740b5824140100c40078481c16a860100b2400980e0341500c8494682d070040c01c00b960507112000b600d101c180070005a5203002035000400301e10a10300c1480801c00f1802030f80100031200450b018440200b07940c0c2c2060620020004060b0513220380c000c100351606900d03a074440043d05e00c100b450035140b0691220a510654100720400040b6003989020000400081215016442c0d0081d0180c40d29074501c0802022108042d41c4041858100504504a04201803682c1c0240448010150180120710f8007080d504d01c41e00841c02140c0c4c000b07041400650540e121100144000b61013160340140400001038400320140040d88241c2d11910350042d40e40d000000507122810b07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 691867868 1250 691866618 691866631
    0xd0c0509030f0c1003150b07031e02060f011707090f020702011b0c150e0603090d1b021f03150305010c0e0d0210030518030d0510060309051509070911030708 69
    0x104810a4450b80c072488040304e4050514500460f01d00151340a440c40d89a20341c11040315204d0029224083c944c100301c1c103082c00d401c00c21081c54080007090041741c80c0c0c1401c0e101441c010416200400040c0e80c80c45086041e44008401d41e0140c0f40d52320070300b0003280c0d64041c101c207200d5004141c14003590703046403812401c8410445070b1000c01140d5a1410360041c0c0c680a00d10030030304041003664045100c1c0b80a07000f90307034014000694905042c0321040c0c0c1e401e00c8000041c002403104480c24205940d60803481040d80c1c2c060030200103401c0c0749144010312180c40314910201a501d00f9842c50325000310010a005502400c00065507100541004091400c10b03411903001e9103d1241c00c0006840e20743c4000007030b00a44c64005259213980711046000c2c0c40c8900b014001e840049242e0304400d6440d03001c0c2d4051400b030703485080f003142c1d02c000540650703040e200090011703000140e03100604440c1004481d4090007600a036512940c51701c1000003140d03602500140010400310070030a032a900000f00540150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 691869118 1250 691867868 691867873
    0x90105010902160f030903021c050f031c0207051c0801080c030105070c060c03150b040e0a1401050d030c0203060106120c0212030115090305011802090711150c0d0c0509030f 76
    0x40c10002c40540c18008010014184d40b00803803550203062107100e1450117154004c1440d007000d0300310101d0404481184505a0382030055a1a14105120000440b007041c00c611101032850601c1e040014000c0d007202d2000c6e01c150041c2c610094052249038240ca6480f406a00c6400143d410a841c4520307244002d003001d40030743c2c075000c244480030b0b03004071039008842e07449240400c0d110f038141300c110080c012040003100b8282c90380802103031040b041406071041c4d8400189032002a0307151b60001003a0f409a034081000840c501005008500b0710030002000c441c024107042c00384040950201e8070b03110099022000007404019010f414036103a005520580980b840248414614402480500d20041c459510145d1400d040c28841502178000d41c8011360b0840020030081d07034101c1d130040d81119506d1040f485946036000094940740140300140c4241c04050003482185100d2100840f41c66014105a0001d20280201c080780c40a80c042c00403401d000d923403080e8581030190f041c5441d28100c81945880b64 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 691870368 1250 691869118 691869127
    0x203160305190e1603061a060304021c0819030507031a01020d0e150706060626010504090218130203070f0803090910080604030806150301081903030f14090105010902 73
    0xc040004044000200b40c0c0c00059031110320751501e13180903810305084c0150300e0400030000c103000056000850801ca901c40d86010740d50400d00f08030640c4400c81c7e009500906400c0d241040d140001840f6042903c5462214030f042c030781c1e078480c0030310550764482440000d440b10208916554107000e204420000034421595070901c0b900040d444410104c001070820a007075102c4000c60f40c54803400c0c00b2549500da2811780d107054500780300c0003916050150b28041609049000c0b000030a0100c101061144822404941c2c0d00304020031002e44103048090b43e1001d00203036000c611001d0315841c03900656480e88aa1070509661050500b02a059840001400e095200c00c1041c884040112949182c0445101e00d140d9504103c45910813101c2e0440001c0f4480c5004200400d9000010309000314011240250f041c10305c81d40c035180070f2009001c0e0030350540003030850300703036600010703500f0000c3c14071904005c9010f0800f1050711086071941d40000f00110081001e20003003002c2841454090051351105500c0d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 691871618 1250 691870368 691870381
    0x905151306092102030c12012307050a080423100b06130504091e030512010902091f09170a0303050f0108120f22031b060f0c020609030109060203160305 67
    0x111016111084141c0100f082e034000c540d01800041c4d00c5640040400304001c0a14507024024454601880c074205410b040203807079038217001000c901c100c1d030340e40d28640f40410b6004112015440680111941c540300012006408900419611f080f40e041c0014000c0c01120081c02058401c0000c0700d900800c070811000c5c00c42000da90030311094400a54022840b040d6518041d40108040882d0040000c1d0824580d002c0560080060902803090801103100380d1b03d0341c080200700d00c00e4a4210360b118140d000300c091919111810743c030280c00203040840c0410380e107442c900080d110048021401d900020b1240c002c00d40c02d4413940d078202080d12b01d43c14156040426859581f43c4008449141d058003003008455585040e00305c03000c84100c880000c400d03003407410300d041c000806408102c40b0300c10740d103c44000841c0104200f1048031055034a1040503c60300030203848004020070b0903600424100001034694400b40151075825102d81401a603d152000d010420b4800c1e15070b50304209400c01043c0040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 691872868 1250 691871618 691871639
    0xf04021e030a0203010c030504030809030408030301230d06050610080405150408130f031505040b0a1508010207110906030d050306040b010c02030d020d020d140712090515130609 78
    0xd524010410403011421140000e280a2809100a5140d0b0074000c130501c50301e616070031132030195200e07072030303040b20764813040d144689074020b80c010010341da401400100010031074240740010004051000c00341c203086282c0805c070817400c0c0220668482d920748052102130304103440b00d0314030307000ca6203040446800d0650b25035840e841c03440b141a5071808038801003010300180b00c00f16804003022212504e80241c1c1d51003030440914191005880c4803d45500350f09551a040c043d46214030303402a03d220503070b6604125100242120700d110308014858000105901a01344010030449003d090203034900d45d50705080004040006041500035005802e404032070a40010030390340c000004039008100f0035800c600407a20a45500c0b006541803145015561201c0e401180f000d007000082d5098820307240184100b130700d400300400b0703102c0d103001404c20900d00856280f031a81520500c04d850101001b668034000668141e0080d00840c511620003d000c05031544800716501c02001607050010380c071864001d0400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 691874118 1250 691872868 691872889
    0x2060c0a0c02060307030b0a03050f240f100f2301020d09060c060b0405041103011a01020c06090303070b10060e01080708060d060f020a030225050705010f021002210f0402 75
    0x2030281402001051a16001f50005030920101400e0003405541d6030419680d60003000c40142011b014a22204040e891949141d5a000704050011441600c03480840d074a6280001c0100d103403031030350080200c3c07100426103555000342100c036199499900b2002003004500d80b101152815540800c031402400d40c1c000703038940e048401d1818540407001d854109070f40607018004000794468074200400003006504040054603001c242c2c002c02084040941e122100c2c1c4104080c170340960b011150005d200d00c0d014009107241c100240940381013003d15660182c9001d01602c0c04030280e454180184040d5900c4480107070314a800b4600803e45083c0311201410400c405402c240c0a14031690300c0d6401c0c40704a03007008154000c0001e04554403070003420014029089400c024141080305400b20740301100b00444801c0264011000c0c01403546401c00545800d07a003004a1019070181000e010f18404a62000c0c18403107814071485509400420305010300d1801c0180202443c0086d8020312026032600980c80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 691875368 1250 691874118 691874123
    0x30c12070507060807030e01020d0501150e030319020a1220060f0f0702150a050a06050d080a0302030601120c0c0b07021b12010e0a15051014040218130c02060c0a0c 72
    0x3084e43d5210007004801030012000e1440c121b41c000113100c200078055902170ba049841012450f07100781c4a102044030b40c10303505801141e143e401403104010030900c020f480d0f0b80d2a000740c0125641c00c102035031818a001c6e18000d5800101c1c0b24615011440c0000301500081c0119074000340645180502c40190301d40c00141c899149010001c3c0001c507614000c001e000c1d079144074103d41c60fa840c900410840b010301800c6400542c5941071500024143c103100c860205400da212900b507060140205003100207400041110f030401c49102c003d001c00340c2c000e101354201480c00b6910654079001500348104440b4014003804215403010402c040450101d0313035600001c0f1000c40340441403010480c8031071b026101d031552040080c02804110010000031411041d0b807060b9a10302400b01d0307520f480144000030318a1060b013401200c6802c1c142134a16003540200b80d44603000070300321103c0c2c0702c3c000411030802072050403c007030603681d01200e0882c03034040100d69031000e4590701841c0740615803000200301c3c1d020134400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 691876618 1250 691875368 691875377
    0xa05180406180c15200709060918120915020d08161b060e0708070807050f0105030106030e03070b0c120109050601050f0d0e01231f031506090e030c1207050706 70
    0x350480280302d0a1041014880b17104441081c040d1440a180c840b2003a00c14581707040d207402c8001642c82e92a014007042d240da07094901c5032450f003039203c041281444000c0c00c0100810342e600481c08168080102a103200c0b5a4018200440000350280551030050801c0080310950800075102a0303110382811110b041201e070805248000b4500b03040a0144000c3c5552075009039a00442c2c0050001101011500080e041b504501d64403810302401e00b80b9000041e000500c104018044140250060703010006844101c0380b510f1510345406030440410b445c1f1305100d980020789004812806100d25000d881009020003a07410301e400080c00307070700c80d00d00d0340038101c1e5000c5040d0201803000d612040010b0000c000901094071902e00c0c0f04c03810803108da1020b8002d0302c0140824160070850200c108050591041d00d000903003940c4506101002101e01640800d41f901c03004034545915015401c0c644050030015070301d80e030a41d00303005d003840b190200c440d4030140c00740602000b2541c005030120840b421801c0c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 691877868 1250 691876618 691876649
    0x110a0503150618041d0105010602010c02150f010618031506050f0415050d150e072903010909020402070204090b060f01020a02090a0b2b0308010806040c0e060a05180406180c 76
    0x25140010104440c101c07155503c7c141c000030710b507074040d00a0705209100d40e0a8400c0f518114514094544050342c14425141404005100113801000000f01d821000c0b07041089182c0d607550340034020141d00c0e510114035901c94404000c582422121050300140481c0c0521550010b41003a00d508003003845001d1140c08051154803d00460300d020001c07031040300030305001d800d041c4101c10b40d49116911516680380245004582210303200300044030380040d0790031018690f034a0076002001071304a45c0c00a80e0310907820422240141d41301d10440400174407a922803001450118100080e00700850309480c15504102c0d40701e801a6180e81c0140d07805100d002c000940c4c45d4003003002c0390b500000c4252541076003460550400c00b82105603804c0002d1440f950b585142e50303880e01c201e29101c0c0b8090310010210f05050720305011031004101c0c0070360305c410003420705100c0b29964070004030003888040c0495040f207016028041800154050703681c0c2410180040c69a280c100d6503540c6540320203100f128907089007180c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 691879118 1250 691877868 691877891
    0x409051c031401080d0f08041e15020307020607020f0c06031915090209040f14240307030303060f0e1b0322030f020d0906140d110a050315061804 64
    0xe1002c0401c9012415050140d0b8503441401d0707450000b000c081011900040300035646a115603212071080d40c2c4910210f1400d01042c0d0b21b41c606ca41c01c1201220808a0085807080812641c030103544109a194010045801d003c0406818804c41c0c9150560ba900003518152454540c50202c0f900255079541c140000450121498001d003240c510440c800403c25100058203180790b00070b00350700d600488007000008017200c4030740704031a0f840306030303982901d05880024541d82a082c140c00c0811044252103050640d0080041c4c1400307081e801c12404240d443c030052106d01d849400501c042e0006110700d1040d0701708103408003d140805400205e0382400000001c504800003000c20400246404110240380e08901d00604085000344200c0014801c0e000b2541c6d002e44200340076022100300d5260250b44100c02491032442c0d500c010b65042d10a5215003441c1c07003840c1d180004204d001e091b0f81d2a00c2e168101140369400b858803041005100c1c5009122600000c2a00031003002420000c50300000c014000300c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 691880368 1250 691879118 691879121
    0x702011505010509061603091e0e04150f0e0709050a0209010504120510060603021804060302090a0b0a12050d02100e0c2815170f040308090a0b040501020a0e0409051c03 74
    0x1c2081086d0003040b04802e104050b040f109420603075070030f07603165109055141e1004030366a4644c8920b2940640315404580030421489004c1c50900079200086880e0a24071b40b00c0064640400542d1160342c007071001009850000d115039a00240031500035454a40242d0000709280114000c1400e51204102801d00b005000c205141d02c154405909110a6a5680f0054000c2d0081c40c40d40202c515100200d2240e4941071152030252940101190b11035280d030000f00009115105000b0b410008801c07000c510310500601c411f0000e481840100000590030380000d090140c1c800740b000d4580d0410b800c0d1081c00c44045108480c1c4113058405009500405101c1198054044114a5141c002034808070f500030550754041000c5647da101c1a481001461459030281f10444082c503403098400085400030f4829000c023600400720300104c800000761600c1d1082c03101c1c01903808441980d400952103507100e410140c600a000070488080104001940f18180c0325010344041e10000d00070140c148000c103010b03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 691881618 1250 691880368 691880377
    0x110a110606182d1e06010c140109060911040b090103031b06181b0602072409180e1c0f0819110d1808041514070f0b070201150501050906 60
    0x41a074030100103400503540514014003984c0101c4801c0d000b9034010203140e120031260b40a9030040e910109200a00d490b0016007090344246912195203c0c010b880102c0c00c1c6000d040060f034040d01c503040c5201800020041295881c1d0041401003840500400200f904004c5a1002462405a452105005143c0000100a000d15120811907402c00e14010302101000c4002901440750000f035440c1d4071900c0a0342d0b1101075101e85000c03640c0003030469280f91401d2614074944051810003a014548070001105203030048090b40488030350380d0044c401e0340710080144a41d141c0e822490943d100d402c1e100000c203c0364540b1502c00511011070085042c6c24007a031204510300d00c49150070002075042d01e580803550f42c401605c03600141d003001400250825054403560203035030321808040c6010310b000c00b400345032050307080e0042c20300080303070509103000320040c0003001054407805446102041500d403219425034050540c00442e031411080d4100010303802040002e1341c0003420103a80300d91030840003a416206 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 691882868 1250 691881618 691881661
    0x60a0203090a1e02040621021302071205120105090c03060906010c1e23030a12150f08061b0a1103040b0d060608090a0201090302040b040b0301110a11060618 69
    0x502c0311443d14000c0e1200000451085405104141d66a061078522054000c0e411111a005922400040ca0050502903800c1c6807200d0260902c1401d4a662004045c486802d00205900003140080200220760513800341004540400c054104403030900018040242503600488500d000b00d51560b00452004840541c000c0c000b4016442103002900c10b580905412244a0000c01e05c00c81d06808035442081d9003160b440085040185101c001c83c0c403409101d50707001e0340568404040311006951440c44014283c0406003080319403800024510701034005001644031407001070b40040c42c20300ba00445044490030302e015401051086034a600758130580d4000700c001a00020003a04111698000c84201e902e00c2c0c440501c03a0756480c82c03194440d94950402400030b1108841400140340c540c0c0240c140c01ca001d0000125203425202007030845120313101c0c0d80c021100100d9078484680c3e00c00848010403640340d001e00781e2414224046403080000c00c0381b00705034010a00001707003c041c0313040502c0326080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 691884118 1250 691882868 691882883
    0x60d021308030c0c030a1101270801090c060f08061002191208130b042d030e0a061701091107020904030c0309120b0612010e0f030d0608060108060a0203090a 69
    0xe03a9901119500c0d84241a0078800380a04a11120030349030201303840f01081c1d0811341703420701f580b555001100c3e100d004180074207041511005406141c18a0b01219000c0c0201d0300000030380b0301341c03414444244145c0c2d038060742c10040c1001003103000c0b41c0c0c086007440c0c10004c191050041d06c809050184e080992159620300341041c20312010050090502c4050290b10b101c3d07e500400e03403034015030001c040000b040d002c3c00c242100f0011800243d03020495081d900303141c5504103003449a1a28aa64024040c1015000100604510a26450080d02000040c541400e008c4815845060030451960052207242d10440d6994014010b2040031812034500d1540204000f01a01d0725141c09040c000a0b80c1c8241c00141c0c82ea03c01240306040390000155481d0004050001c03039803143c003040400b05c80455070009954881602150307403102042b003134005010500c090360f1241c4581140108442c03e035400b00c40305500040c0100a03924000c81d9090f00101c08007000359a903550300e005140341a055800040184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 691885368 1250 691884118 691884157
    0x11d01230d11090a051c15110a110601060509010c02010e0d080304140106050f0109030b070905040219140a0e01180e010303110c03010b03120d150e01180e0606060d02 73
    0x4048000a20246204a501c1c01419456a00340901c0b0190f0138207442c1d4006030314441c1c1c004100c7d40d4402c07500c1840c20f8000032544103646080c40c402030b0000700b2003802140401c41164101035007804890b0142c81c1e2450a03a0904106800007020300902030740190502c2408414141544c4442151011f07064200c91110790b2820a07181200e0f11800c1c20b42c0701004c0e946048000704a51800c00004151030b1070594409100904580704d100035520042d0218003804907852001a4a498500160120240200891040c040c00c1b4602502407070040312182a0100e00b00041c4003403582089008811003400c0c83d001c40114a080c0c58840c031400d440d042130b944032203068000002c05501c4948901020203410640b4a100b404405260036030303500c0160356031325400880135003203860240d102500b034106040401003900b90755070301c6207001d00007150003445d240106000148150072822090100055150400700040316240c00451784585000d0000344c8100c7c40000c00700b22601c400c0d01954a0795006c100c0d40d5825 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 691886618 1250 691885368 691885391
    0x603080405030609030403080906030702010b090901020d060509090709150f0806041703090a0605190203041b080a0c12030507020316030c0f0b040e04050109051b011d01230d 76
    0x2950090310032103101e4416000014800740c008020750781241d900010307480c02c0070710303500c00c010054100810083c1159a070b020b8000c1c10780c0c1c41080b2580211907800005075100000c02c4544266115908001d019039548020302a804000050703050455010540c0000d13941e0390801e5420b291409540000f18055008801003001040403440d580114854465503005806805542039180812a000714080e0807124070710020400c0350b04007550001c0c0c00200003030724a01c21002501242c005603000c2e11203030361205c10362200c0c11035400301d0b0028042c56801800307888142d80d00c1640c042d41c640941ca1800b18100c030501c04040c061002e94000f15401016a41a025684c200390244d284502c42a203986d2610100041d50054841d45501560400c1c1c07402c9140509007582147e04080241c002c0f2910340d640c1101c1c0c80401e10510420741c000c041c05031140e803e002288001041c1c0c40c10085058036012410385c08a905a8204c10b01d52842c852150300c140d071851450a200c0b044d4040c80c142402e4bd241803000b060032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 691887868 1250 691886618 691886633
    0x1080c03090a0c1508012310021f0603050d0c0b010603151502100b150702091503060705211303111e030706151202060d020408100b010f0815041e0603 66
    0x4c80c689543c0e541031850f030741c50140402c500456540c081c081e0440b040d0a80560602c2c110609442074a80111507030303d50f4010642e002056080c10100f880e1b50340d081c00388200301060000c0c00e100c0080e468640c2c45008162100d044198062050005140c2d40d8411603940c40c120000a50050402400c442494119000c029480d0794070801c803d80c0ca00c2c030703007142e50b80030b441c3c108220100c00016070cc1d45403c0400310703401e06c040030304058126a0007101e140040f200361740e03041020328402e0240c0e54510b5280c98004191a8901420010300410b03c010b50080008800c83c01c018024000c0e054a0401503454410019608001221100744c08010105a0b03818542c880000280743c3e151040f2010000e110440d26140c0c0000031030700420802030340d8000c012000d8078010000c2d002d4091200b400604d8a0356a200081c5005140c0b58014109901c81a0307075606c0e9a001400c000c0443c6d22418450018a0104103c0070164041d4000c144201e69907035085003000001c020300040209005000c00c0441e8990600b042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 691889118 1250 691887868 691887899
    0x3212d0a030501090b10090b09280e013003050c01050405070f0e0108060a0b21070f092307050c0a0507030507380d050a1b0207030201080c03090a0c 65
    0x540060804144181509118400d500c030392006d651404061030130044503800315402428600c1e0700000c030008108040340c016006c54003807940141d85842061804c0c010903500e440591101203d680c10503542c41d680e1410141c2c00b0165000000d000507119564070701990940a0001c014005620b00300803c010448005201e4003592240102007910507911041200003203401d0040c24650f40041c0701141c0d20440c150828403038000e008108003e04012611000c035011410981e2203a030b540600010400d4641d8842e0120260618036001d1286210032051000407041845003115031034200000511040d200b5000d039000c6500c4030090b51692006400e0059417004240010b0326079000b02000000c41c10795100c0c807001e0040081c04903441c113039800381581c500c1c0c0c2491080c04145d08000c001a1041800d02e1045074411240160f0001d10b6144502007481000c0c042e106000641d8440341c01480942e81140300340d540703ca4584d140903520381c4d038180c81e03500300080e00c58000c02e4540c1078000440c00300038034201c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 691890368 1250 691889118 691889129
    0x3160b062d031e25050607030806150a020a0b0a0b0310020706050f07090b0c070b1c0609020406020c091905070c031b15051b0309070503212d0a030501 66
    0x3582e1501c2220b00601c0100e040c10100e540355800305081c2000d20042c070035003819003c1451040813181d070b40d900115881c0c1d03005040c201c2c00078000e2000c024880c5400751114200c8000121070300d003000ba044401030f646801940e8003529141000001415040b01038012502103400502504d061820040241000c1d41007a101140c54030b040000150301c4c1c0c411300d50b4051040304113075a91441946450107043d0590311201e5006000d008542d00425400360b03005c010100e4141420803802450106803101084a4031504100c2e44140108810405203600044007241d040040310280400c0d11140044c8004600e5503201c000d195042c0802c10204c02d82042121384610300948940c408141c5200035110044a90400101090040c810328140300c0381e0755000e5540801110300d41041d4021004106489400c11601c1d15030540c001d040a000a090600803a40e840030504040c1603001b0307840b001a20580100e901d87c0013286040407003070f0031010400c1c804c0764107540046d03045c540d69110400010702810090088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 691891618 1250 691890368 691890373
    0x90c020c150a14070c0f0e061806013006030312060e131103073b060d1a10090e0d350f04120203160b062d03 48
    0x4010007410046500c50101c4921100d503480d1140040059407a500c40386502281070a0074001400003400310f05126014103180c40c1000c10962500c81956a030070401000c044c064850700162011480d0700d1211550400002d003440c0c00c4031050300041d82c8903015504540e402e02c0c8032005c030003003081c070083e8028011750b03001f0740e5501c08140822422400382c03890303031080f07500c00750130f130380015044411064a200130075200d84010480c050350080041e01c0c02c3c81541140384021044840f405c5401c56007c013403e010440880c60030042803581243c0440d24500800250151542509000401c0701c41030070586064154210300e040c0d42042d03140094140b8050084078500e03460150089450706000414050b07000b40755a400e043c01580125400115411711020301c41c0c03503504440a840c5800e1002c81f1407069240c0a1000d405241c282003200ca402e110b11020029500200402c034803070480040396400041d000082420305803100c00110f101010400031013031181c4039a5043c9207481030341c442c041807081d008404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 691892868 1250 691891618 691891633
    0xc0e1f0f080708120a0e060c030c07090b0f030a110604081c0201180503090f0f03070603091e0201021c050d0e0d02070b040b180d21020d02030703120e07050a090c02 72
    0x15010380d1140b120341319414a40c0c0500c18500c44505c1003e005004410107007080d401c18509144240c45c0d40c10102002005070001d803414080300259100300c1034024001c407504002020001c022036140c5044040c0500300076101400c5400035214441200e00400c401d2003203400100400400703d1810601c484220019420a406540c1030300460058011081e00a80510302d4040290304000c200c038081e503034281e04070104007201c90140c0d0b018402040101032680700411450b61b240380c121101c1c0300304010008002800c1c40c1c1a005030741e000900703074074113801840d500c2e091b6600c0c2c080c1580d05019001503948407505151500c09030200118141d403000c1038680842d05000d48880d85806240601d00680500d95818424804446803503c49020000ca010345503141240300d5844000c0c02d5001d003024540203901d840d00c4a010540d0400c208140382060344051410070f0039640d0010301c101139011900b00100e03218008400c44000a1181100600d002080f50082c02d60340d59441001d03108a2451740050f001303120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 691894118 1250 691892868 691892879
    0x801050a21120c11090f0109051306110d0e16060f091a0415030506061903090204020d0b1005030105060d020d0e071514250807140709060902070c0e1f0f0807 69
    0x60419000300035210286e00780c4e03801c02a00500600340100040340c143d0b00565a035012480d0381c401d8111080944030003954400b148007584041e50510a000007040d8030807405640041687c00c110815510030b07190000118001c442c00f110b100100350004062402d0350107005a048104c0001031007150b546850042202c20403c009a089803c102e45103a0440d104114101d0004446040c1d0055101c881c180011800e94907004101281c00803680345890940d0f92a14402a1505231450520030039a4503140b480d640c10080495070074017030b520413010803d0b0041030111007039100703030031100035041841c0c211100c071651603411003625074002000c2d20104803664140001211418111807a550350068092003001504a69103684811200184d401105c1403110900042c80315480f103980c00400340050082500707240d40d01c02140c00b0ba61006c03041d0b900c10016100011020040b40040303034169203240b082965410380d1140a202d8428020030156510800852b03403500e5405000243c61000084031242e52312030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 691895368 1250 691894118 691894129
    0x20403060e010e1b1810050117011d0417030f040204060504230901020f0c0a1e0f0605060312130305010c09120b06030a021509100801050a21120c11 65
    0xc4001401034121025030b0b0b1001001e401c1e550140c81019004109200303450340c2000d1004000e480c00321046c3c1c00080c00300002d603405458000c0940c8105005021945020b030b60108205040180b05003645480d4001006c0c03142c0c142000750000059403500b80e40f468020382500e60703814101c904910552034401e010800d810513104540e80a0114007205061801c00034081d5180c28008006414564007080001040c020400140500790f0b1908024003450503140f801403000e003000c1400c6003001c41074503507080c0480d099091002c1c03010340220001030203403101c1001c40d08ac1034440149401081c000a0100303030902e9964405e5040b02c0c0100300801c00501e241c0ca0458500300c1760f00c00d081e82034912030000c0d00801c090019851300400002c0032502d00711066030100d960542420f00c2401010340206030700c000d504000303152400b2182c151811424540c1440000384001c5041e0090000d1401c1c05110400d020001d4024001c2068012010210204c500c8800401c504011542210440c0c03101280c0e19003410234 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 691896618 1250 691895368 691895381
    0x509060603120c07080706020304060201050702010203070807120b2106150d03200601030b012301141809151c030f1b150b0a080c060f03040f050d03020403060e01 71
    0x1d000d0010040c0004081410b500100794581090041d02e00010b030100041041c01c0040c071003900a90703140e0b440c1402c007a007151401071101c0f0659004000f008100d603401401ba03680f2174900d04190502c0780e1040250310060040481a030341140f103270140c0c060981c04c52400c651908682c0c81c02c035041a070351b400c01c09003841012070007242c01c00c48000c50100060b010b510098528000c580c4005112524170718414904003081c1d1050381d8001842d0014401c3c08074542881c0080000098154829131004000a06000000e40200428207003c41c00400c50030010b00e0703031003441d80b001b00004103d00380182c420404c0640c080300342c0c1c0710345400d415509003d40c100b0000c41d41242c0540f50201000180c2400f5603102c0569075084d2110380000b03c4942c00180e074003ca941e4005244280051b207000800103100721540e01e900370070b40d55800103c204105907141e6080ba1070301d588024816407aa200c80c034040c480341c11043c80080007800390300b4103030054692603030160084074000d5005000043c800ca0045089481 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 691897868 1250 691896618 691896631
    0x7031d0714010c0f0506250f2c060d0209032e09170c211e0a020a080d05190204050f040903020f0102160b01090606050406030c090317030703050906 65
    0x21121640380e9600a00f030b150250340c015039100c09082c40590f19941401d00c00c9410404600c40d5044010346900704d149611041e01942c00d00841c1c41030740d581d005e0310301e00000720390068800751407040241e0b150420700110f501c1100580040c3e129851118440065001028054000e1141c0c0903200000b81e80740616940810302c00c4000301c41c85810b12070319000b03415100d4069410600290440c094800030b0401003180583d0040640300400b801c030101d0803002113001c1e00d281994403d020350401090400c500081c11400c03500c2450756481010000d9041903070442d000b0344541360108101400b842550010b510820f6502a4242034050300e800801c104d00840c003809420084641a64100d03060907400030310407500078012208616003800760542a6170005141c0d26148500012510800181013801c5016000c400d80a00c100b0f230030101c0042140c0100c2c41808109502d40050103c010302070300c0404003450704046008485071410300c04241d0f0754015588500040c2c40c0ca00002e6841c94041449405981c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 691899118 1250 691897868 691897889
    0x503010e0a150b0c01090c0b07060c113c1c08070c031d091305010f020a0f14041517090c01090605130803030a0b2e0807120507031d07 59
    0x1e05103d100b031034a40003e00800381641d80c07100c0e5000402c0d221159240241044c5403541e40d511468074140003035540c103d400200317008a2121100c9010300c0400c1c0403008648060400440442d401910301016980510080c803d881803030111143d650045584400c603018854801901c10145d10101c1d0710803002c0b5031050003c0c4030f0000d07040010b403251840d050300080318100c42d00c0e940402d0000800c1c0f0a0184c2e140d1410b8107800305040c0810000303024524503450a00300c114100304c0800c0001e01069408032010007040264600581c0f075210850681e00a484031003400d000445503c403004c0d01052401c0c1880c0c04424a5070001502420009030302240c540e070607914110054a400c9003543da5400139003a20156251420300032601603010800b0b1403044c0c1721000049504142801440b0f00c48003003682c503501c100ca0081031a0941c00d0301c0000c000400d0050b00d030034681940d0b03024085030419101486005050b040106208900d0b616401c8500000d40800030009030b0404040035a81d00c6159100340c0c070307110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691900368 1250 691899118 691899161
    0x41208040510090602120c190e06070212070308030a0b0411091807031d0123040b01030b0604020904141006020106030c090b040e0601080d030b0a05011b0201110106060503010e0a 78
    0xd0b419500807841ca40c2c42030b4000f5050451001d51106540c2007115002d41c20940032401003c100c80c0242c460b418130141c0d080c0310308800d9021003c54540d01c01c03604040d01501c08170b2080d45a8420800102008603080740055840742000d04000c2d01a19148078114401c4d4244104504034401c000102e801d000001442001c00004e0800a403400703c1006088105041e654001030130003503c0c00d403004401c0180c200002031800403800704003114074644421041c81c011040200800105039101e00e50640b90021130344816561100000f501a2050b075801d1a0024146843e0420328041c07500c440d806880c107604800a1141c4030300c003c030b08842041c40301a0000c05040300401044c48141d006845140c0c1c080c0c40414080031a480c018178111007a03010751442d500809000d02e07100da05103d02418440700b1103110140c58036040000300000c0005403050381c40c0c00d100349203408581c05904c51901c10300c50310009007c5150303180c41c050041d0b0001d208600f10441e50900244414400f48030b1140303080084400084003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691901618 1250 691900368 691900393
    0x30b0102031b0712031107060c0210050903010f1b1706010c021905030a08042102090c18040612170702030d110703150606030b030601141302040504140412080405 71
    0x710b2161000042c0070380959400450900c481444c02c41300c06010b92035020400980d441914540b200350b034042d4007000b4485543e000181c2d03c3d03408110b690051454419152600c1c1c234000b80c010720301e03e902d061031036141042114180d0b078855020b22030043c050b145c0da403500c00140004800c030001210020b00140c0360180c5040140b41081d43c0f01a0118210340e01c84989840c2c03800b10340b82c50903842090322041804a01000b00c02070000f801d03200c419085100349070008203a0f0204010b0780002d040320003078080c00300b4488041418103500050391000108180b0025035180c0146466942c10801614401480c100b140402c40c42242204e00c00c1d0781c060000c1020b0440320070100c41c0c0200030340400300180606100040420544c080c01800710344203c100042c1d40d490320074050300b02d03080141014002e800ca10010040d0381ea0103040310050740c0c010360300586040101e1070300038000e1003540c000c2e650040c981111210069041016244220720564200d518180c2c000c205546204040314003c4c4603034020b0384020031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691902868 1250 691901618 691901647
    0x507180c02160f2903130506130305071e0c090203060a05040e030912100c0e1809121e0706060303180810020a0318051c09060903110a0e0106081006030b010203 70
    0x21342540102c0c1c851580402c581218540e078002da40c152000c2400031144030a1010a1190303507046804a192500e01c90f800b81d80c041d28501520700d014003405450343c81070741c1c1c0441400d00300b4001d9a21010352164542c83d442070600030340081e10840d010300c030311450205aa04151050380705403140c4200650400c04c4035400c008040c00560000d0b0f0450040241e45d60454082e8021242401d0366512a005400c4600b400c1c419a803007025501c20410990801780005403a000c1041d0f0021030103111650341d10480910011204059182c8660781880009400340a01c0902c0c0d01000239a4800d0781d841d4810952081c0fa03000440090140d01c0c9a40c001844480030000d0a5008110007038003403d01207244900c01e22500f0040d1840b01c4c0554207508003030000743c1d4100e01000c41c809041c86908088243c60b00f00b1000030003400c01808018207160754060128016503803800410000c1c20601c401074010360712600c0040448400781c54600e05080d8203500800c54501901480341001c4041e402075040584480e203030301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691904118 1250 691902868 691902899
    0x518010c0209100603290d02031e1513020a060c0f12050901020c0406080a0b18030c1e15040f0f060219180302060a08040507180c02160f 60
    0x506008800c0032900040e198603840c030b84200141c80980c1d6015140040107425140d41d80d814408003441d4840b80c1000b6070051003400c62400c000d507081a1000f02900c00701b03207410000040501020714082c00460b42d0000010301301c8011104825104098540d8040140d52051084000b544840d0304031051003078520074000c1c400f075039005440c690f040b400280c5030000301102080300300000071300003e880111560100074281c000b40c2c007554208001803400141586920f80014020032800011f404601e4003807a1f115840070407500502900d5940c01c040000c984c0e12561480d0701c2080c2500c0750085000c0c1100402c041c201c03004401c51140440d5941c1e83d405140030030020303003159042e80b0000094041015071015100b6059004801801000d03d200040d00900d10010042c1030701070b240c4014801030b11844180c4600c0d202c4c0f820410222f449a1401c142840d615420081803192500041c501218042d0400740d403980c0280c0aaa41c6100d85842c0481c14960500a0100340c40c0c902400b04080d04000c604c89 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691905368 1250 691904118 691904167
    0xa151a1b10090f110d2102030c07060314010b0408190515071d09010b041a0408011b12021201270203010f050414040b16030603150f1b05 60
    0x22021116104001c6049425503282034480e8a01202088104141e00d020005402c078120341c8244924420b07500c203c2e020203100076201d0711180e07004107900464001c10035110310440b5034080c0c80c003681d200c0800900030008251000c0d41043c809c000054402c500504035010340310050f0251041141442e503004148034204011100c5100302c0a04540681138068120301451066841100e010340c818031507101d1344c140c01d00c5207104802e0440100202c82072042100c048030240b224800c100c4038450500341302c40c0269482200c5a5080105081040c1755601001c0b04294080d10780c1c805021103030705403000f08d000d813051461b41500b1800c0180300483c400c4110340d425101c20780780d0b41c00c0311071885914030903a0000c5c3d03c50340100b00d20440620092806000d1b212424015041891b075610701921180c11071000a0100c800034404005d24800b540e101c2e801c88006541c00046043c08140c0001d0800d00808442d00040540d91800f10348840c01100003070b150040c106a582c07a24146240c00c10320900301000c80802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691906474 1106 691905368 691905373
    0x210708090d08150d0f050f060f0621010204081009050f030a05030c0f090a03050f010b0109140622030c080f010b1305060a0306050a151a1b 61
    0x82c80da012080e00c40090090071004080340da1350303540b0500540b0300070600c0d803c10107000d40002d0b030100d8409501c08a4032595160301244007a140203a81141d031020f120382c10a01189141c41000c450041514001450203a80d102900d2500315983c10002c1d0440d00e0f1940141405818442900c940c0d1030880503514104012000504511004001c500004030120340c10000c0c0c504242629650400a0a0317003503025102c0c10266a540c000c00341d000d00c075601785501200c55500c200b00b0b03541116180c81c090035199290204200f0140c00184000000182d400340b0703941c5440c002400040214010103482d074115007000b80680c1800700d80360f40c20752039a040c0200b51049840382d00342580a101c079a540003440f5140d580005080e00301c0e640c000b420442c00e00017401007640c0a0351220440c614108442084240e039541c2410402a50003082c2c10520024010408170f02c1112000d0020b54095406 = true := by decide +kernel

theorem cover : BRFrame.Cov 691726618 691906474 := by
  have h0 := BRFrame.cov_init 691726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691726618 ≤ n) (h2 : n < 691906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
