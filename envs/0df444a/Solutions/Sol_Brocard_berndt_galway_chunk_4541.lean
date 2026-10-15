-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:56:48.034176+00:00
-- url     : https://prove2.me/submissions/373861dd-0135-4a6b-9ea3-f78491bba85f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816546762 ≤ n < 816726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816548012 1250 816546762 816546803
    0x21e0c030304020d0f0c0623040308070803190e06160c020f0918010e030d0b0303070b0a0c050405040e1b03070e0105120f03031006020c060403030f080c09100804 71
    0x6a41102521034100300001405800d001000e40031140c402c040c26840401540c4900c0d880a52540150000545480048484031005d0081c500308000480b80249018510b80ea0f118261240070f00081a41c1d0b070101c0001d89181c011040c0d880700000e2454180840240401d40f030ba1034110454415003004010394841c05014400c2600c0e140301540600f4240441c0e0202c0108500ca030001403100404d803000c40c0c1d62540d040002c1c0030348804410050000c641314900512888103861009500502071351040c0003aa0204410b040d956810117845e10780056406079400342265248243d4010035002400c042460500680004020307481200b010307a9401c001010504064941c001481030f5000400054010300c11880c10315150300503000400100c980c114081c00d901c0341036800c101c0718041e0f00c5d060325100300101501480101208402100c90500d01030a43d44e019140c07108005001080080d035000044a105c2c45504413404680018011081d04200b0309001300390300b10448003205c03203c3d402900101100b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816549262 1250 816548012 816548017
    0x9010b180c0306041d030f1306050f040918060c0c060b040e0c090c091002061914150a0806151c020303190203120c030a150605090f0a0513021e 63
    0x158070390681c1c1c503640b501410040035148400b010140e501c1003000d400740414003000205600d208a4258603140c40c9803174404569881254082c1052240030481142070241100444003500e14050000401300c0303902960741c80500003810020005032402100d1021030360420900c121882c13284006025080e581010700090310400a0070600a92110078083c881e8504481c0460f0303c1450800d54504010b0000000b03110405000e600c4005604202c003404400d00003111401003002411409128403c84503210080c9820000c10603030b0302e483c01107024805a07542c08003e60041440d00202c0e201400c01460f1000351903010701c019841410402ea010b0241c1c000d003201e0a00c1240c000b8081c50809041b00e00740c1c05a0780c03002040301c3c1140000c00001011070400c5120300e0207108440040c41e209d21b402a00e100458141a50080e504015501c0c00c110345507100c030031100b8070641035820802000305007005c903c4044440d00050362104030788900420a460590103862400c00121500c2a110600c040c2c9803480d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816550512 1250 816549262 816549271
    0x20910230307061209020402182706040e1912020f0118080f160b160c0c0612020d06090b010314011202060304150e01051015231209010b18 61
    0x182c2000308100001d60103030140c039500455002000c100314481e6030010b022030380314290b0403110350030360f4010610a08104040140030038000c0d1914568028000d6040d000500041805104a450b1441d8113900442440262882c0085242d40c04074916289050b940d088100c180c1000184210f400031081c10105001d40720124950740c56029001903180c6031340d4810750120500c0e01c1412001c01421001d8800000407402041c080d22481076a41003040d0300c01d510260112510040010031611640448c8070301c0c800e0310442d840fa06045120b0304000010401900400c0c95079044640b40010001d03000d20f5542000b400c60307001340c0e420052400f1030071003459100c0003800f418042d10b003210f540b40d0040c10068021a00103009007458002801e5148a240903108028006011a5120010302003074807110340640700031382007901100d400e1115020005020820400c00680e004107800000e0b03031242114000c903111056a035404040600e0071a501c1c078060312840003071500641080001489126214107d14000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816551762 1250 816550512 816550519
    0xc0105041b03081801030e0708010c09240e010e03010f09020f0901030308011202041503081804051501141902030703080109060b03190f0204092301030201020c0d06060302091023 78
    0x20300c4c9984c2c140d44088010701d0413881c1415a610030140390302c0f1080043c20300911007980040741101400d500240101866407040c062180c1c0c80800503c409040700c9410851030031071600c0005035081b81c0040302c081c010321b011143c05500e0002c03108840c007682e0b0031a00c00c003402610484003141c0000b06000400c40e092202030005a00980140a0a16242c01c44802280018404544c8038410b0a00e54182e00d00360340101c5019200241d60302d450381c10041c5c00142c0b2003044904108070701d842c1508502103e03401072414104141000341100e500c140300181c0c0d40b24074220300031151000e020b040c013a50720782c458172044c1d010410f81d00c00040ca50350180201425542c1d0950f03050304685580500700074190303804090715060b64071000e07020050021440608001d1155150108500f04816200240c105c10b66040014040303d0200610260b6000151a44410020345490761102500c1c20408002e06c0941c20003544050b005003440300c800c238800409804d449008040880d41341c003204001c107100070543c01c607641 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816553012 1250 816551762 816551767
    0x3100510030501112109030732010b0105030105061e04060201020c1006510e0f0312030402060403060603151d060105240705030711010f0801031113020c0105041b0308 73
    0x1064801c00b0f80141e08013103210107c0f0300700340c071955031a0076034083c0c0700d0000c031048910300380c11101d4003440011810244c458002080701003046000201144814000c1c0c0340103100c009032038445120f9440104042000c11000c40c0d40740c0e030f2640c1c0700a0113544060740e400c40a2042610803010700030244200011921502d0860010342641c6440c0c60640119200713041e02007026003000510a07406010703040c18080580381c00e41c0c2c6118894800b4011076024165140101e815100c03085141d03d0010f481090011000592503e0303a07107910020720789120348d0b007006014600f0440004100704210a64944a0200380b00c14000242640d00350f9503400741600c0441c10940c8685d00400040c107001010300000281050007002802144402e01610f601440080f50030b98000102c1009001c1440b5070300741c0725207003441d10b10b80c554098900107003104010301001d4055807140000c20701c00e070307901d40c050401040030880039510f60003604110b50007840201d0b41035a01024040446000c00781e550300d06003d5a520404460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816554262 1250 816553012 816553057
    0x8090a02010e0d081b0d05040e36060a050a0504050307030806041835030703180b190e031903090c0803041502070b13030f020310051003050111 63
    0x101e145801242d5550030070441014400820103600042590042c84044143c241031103852041c50108031300d0b416010400c0038801844072110800c0b01e00d401508290500a1528540048544407040a0131707000354100952400003290202040d02c038810440c19101f0880d40d81c5e400300d4401036550407030300100740d90020403040b40020b014540350394010b8400780000440c9503041c0030507030540410380c000360f81540c50f8a2030520082d400e8607161303813003031040b8502c242d030401302c0c22003140329010140200c8149500c2e00081612001418100c4c0c41a17508242d100c262030514690500c002e00300c600d0740e801d0b1681044540b800c03041c400021503001c00028103503240c1c01d0011460403401003088070412240304a1030400040d241070204007404c082e2401c1040700e031020002000191812034181e01940807018103001e000900a01c03642500c0860341c0101101f00c16503030703d00c002800c141000d503a083c2128036080a000c0d00701e00f40f010150550340f00f0402004192800c2d01300d00c865010b00c807024049050490981c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816555512 1250 816554262 816554267
    0x10050a0504050403110f0120041202010c03050c0304330504180e0303011d1003150504110406080705011d0a0b0a141602090f0f0c030c04030c090212060108090a0201 72
    0xc2c0d601c51301078a030041c0c2145c00020100c2c240301650300c2030300060f916641e143c001d40c01c044604c141c00100500b00103290614007005151101d40080019046c00341848a850901d0b0149040f594890810016603036200d484624200214007401c4803070301c400d944010310070f1126019012600036030f000c5446281c01d0914180940e00e94011035090100c80540315802c0c030055410070009035010340303051864569410240640d131000d00900800108a03421100070170000301350320540c103400c400f40c3c2c2400410130307a40e030303003002011000900801d64000d8608a030005040d071000c00d050040c1e0b41c00341d0742c1d110500355020382ca0701401d01e40c51001e40d00004840080041e07044010007810200c0843c10940845490390095041c5900214401c03064443d0000d281421460801001540040c2d01c40160020341007020150b003907414010b1503c8a1a480080454a480031810a40f40116400910340308160b8903801d04070007a4000e25007000f83c00042c440816030035130055907882d10810845000700032042064004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816556762 1250 816555512 816555521
    0x90308010f230f031e0106092d0c1b0c0503100621240501030219080d0e12070609080d0c050d0509220209030708160e0603100509070e10050a0504 64
    0x101c0384d26100340700b486100703603000809003080b582d4000c0c000540e19107414900c4083d1540102034040c031007007007802c40b900c0b1580c180d10880000d074540000603900400407001d4680362038044114107154074000b0681d040002c0b0307401040598000ba02507542000d00211210b0544206000d80011010580c40410f0805260310808184a0047c8414070f0100d04840c07610611019080f0104201920b840050003507003000050340101415202c0400b0a0501d0150015200c3d4006074840c810010800740129140d43c0d4600d640d0101d001c0003042e20780c8155214805000d2110510404e0001d00480344845001801aa0700f01d5426400c5005030400c040c5e406004c4400e42c8c411032900e90b010700c0c0d2a95041500c0d44200b00c010b4600c021030001a13035041000201454542941d1010000740e01280d0742e90b02442c228028141203813401d4101d0849a1550030000c4d04200b403010000340601e03d49000c0000b0110b0000303414048805a8481080980340c0494041400300c590190981007000c038001000070341080c3d4403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816558012 1250 816556762 816556789
    0xd0e011e08131b0312020703020a1815090e0f0a03050307210c0903060509070f140105160c05150306030703084b120708070210090308010f23 62
    0x41040100e507650348095940380d0700c8408944000d01030741413040141c81a1a041855880e0008201480c612350001d03c4040850103144082d0221004a04040602d81c020344204e101c8240001e440e9034031060f0040c018400e0010710400381c891140d056040580200d07400c1881c50b09541d405145656501e401d64540c4840305d81141c0450501c002c1003048840e900c155507031009d165076821652491800d100341074500c00750140801e50444202003200e5064000c030314040340c0304031260100503107040005032128003c20700000c3c2600300c0f10010347d0070030441c10000c00a46404541146980a030002d2440740c900080300c28030740550100009102180c00311000d0074001155a42100884400c20a0490032a900d10034540c41c80e4035410309a0711206048248900500c10100344a080800840020b400403001910340001d10070b100021071360075842807007150032021442c6024040141ca524006040703040c00d200c1c0c2c03040704d000c0380c8010400068200c9000c02800581c3c030180380c05007401080054142d001803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816559262 1250 816558012 816558031
    0xf090c0a120917090a0815010e0a180611090a030f02090c0430050a03020601230a120c0f0b0304060b090415240902030108010606020d12020d060302060c0d0e011e08 72
    0x8001800e660200300100307107e81000c0b51840903501d49050810500340c007502495035503051054501a0f40d2551800c0e510140d0442c0c0049016299225031140c0b920030488001c1e04442e00120220030300410410f50000d940c801d0301c00d52016075800003c01124003540c0202c5102e9007111103400011142c900e600c1c0180360702c9841d42d2952030390310b503a42e80ca08004401c007100980c120f00b0042001604c02e201030308110640c050b0410008410f900021000c95440c0580390100440c595440240705000901d20050194003240070350090301e6400f00304841c5c000710703030848040c0c0c10030052031020300307090141900440d4000c005450360041c203548400135042c12401d0340840103908066000758000f40441e04003d2003616001692941003486003400d5031465000401035502c10b0ba041185240d0051030078681c14001d00300180c81d080607042d03144c060441c545c0040d41c410f101107a00f503440b50000c540000990072941b245c200d05e6844000554012004e0400e50b1000ac0c02c400c1004a1303280140d00d15540300308000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816560512 1250 816559262 816559279
    0x3060403030b06090d060e010c1e03050c090301090804170a020a050d030201141e010b0f0f0d0204031506052701050d0f050a0b04030f020703050d0309020f090c0a12091709 75
    0x413008034658036400c000a480b020388840300c590201900b88902003000c5242d00e0400688010685600240000400581e0806581e00b0004944c9001d080c16981c0011004000384100308045c203060946400501034009000c2c480036101410100005d00300441c19406004c051003d850f001c01c015245110100070f40c259502e91207460400c1c032000210314072031004000941485403000b8455944064160001010850204524403291030000b00b039851100300340f0f0311555200c419604000c041d0065510081c5210f429641c42d240310440c5401c07040945609490503140d010445508054510324a0403071409048407000500c01c0742040c24032140702d1409200508006a500d984003480c00c034440c201900c00c292035100f48010554020300101030000c5a100070030405041d51101900d1382440960724062541d104200e10854440050502203001e00070045102882e042c00020075541c041440d490005510341d64400080c80b880c41107900140e04412001800102d1103844c0400c1e40c4040c42c110341c040c541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816561762 1250 816560512 816560527
    0x20a0c0605012306030c030f0601020a0b0108101103131e0b09030706060503030310060e0f1f02010609090b0f2502030a0e01090503151b0c0f0f01090203060403030b06 73
    0x340d01401e8000c01c09a400400080e0b82d450300014080010f03482984594400c0040c05105000365066a07004900c06030b40014a403580300050345840c00529005001518482c0005000c0c8000314802110160300c150500c4411350b17100c40f40804c5c0c442107510110010100203c800440c00b1500c41e5860168101c40303a100001c515100d145540c4000c5403410440e500004003074003004440c2c02054001c0005400a60a41c2065400e900c0ea600ca140154000c010099400701d00039030380c0b0a61900c44020180148503000985850303090003008100c5c030500950f09062000600c4005032190f4020550003140d44034440d2500005604120405000030030074240b40b400c5440004806400d44032801e07202e40095540e01031450b4090100d201c600421414440307508010026a140803a04d1000c254007501c440c66160ba0714807000b078221030031500c096034803c03003c12003d0000790700003052054032000d031045450300a01e4100150070b0311001d45c0d000750160032080108000a00030740089462503001024241000103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816563012 1250 816561762 816561773
    0x31209120705030c010c03230a140906070905101713050d09080706050403020a050105030702120c0c01080115171b07031706030f0705102c030706020c01020709020a0c 73
    0x102a03420390b45500b0004000304900b8003486104000503990070180b00004080303c11440700c45a014a60105241c3c0a00040c80555182d10281e6085005070980b42c190910b4202c0a640b40ba080f9140d8000c202d444201084d03500d44007010380c0d4003441e01e40c1c5981a4200c207601d0303400020800f400440c01c0c03115035120310340000d4050007204c010800c0caa807010080ba160000644c9045507641c449802c6c03041c10030040c0302581f03c0c0d208103000d65000b8240b40790b0360344500004034030300a05100d0f4841c160764046108805034a0109040c055007074261394005035031740c03150b401030810b110360865040800c10140c00c003401d100d81071005651043e500c0000e00400045800b03000380c9a80400c10850000d145030740e405211000a07500f01c0d4114205030014240300500e030310040c2d5178104034020300740f0a14410105071156482440e61000a40c100b0094131080d101c007581000c00f10a014001920a00135a040030914500c0041e403082d00340c030140d0040050345d1803c155540250b101c4a4490104240c3d00d01da04003151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816564262 1250 816563012 816563017
    0xe0415180b0111030730142d03010503010e01150510050408030a0f08130b01033914031506220c020a030906030212151206090f060601090803120912 65
    0x9021b4000d01501c00c049405038225071400c010320500704aa8100e142c00416071109054070003841510f9001d5071200810400300b14417007200c0c90b189403050031100035100c1800c4000a035040728004d90090102c44e03610a100303030985801019580510241c11001c000b1494001d0103404800140c1c03c00c10300c1d05407541aa14150307404550000e0102e4000151111040e5105107410b520081180506181c0c0d01765944136882050706100180604803c0703402034040d50030b038444084204101458400c03044045003405205240c9170320071070b8502c4101c01c4501c03172581404030f01100310b180b00039040c08295840000304607000c0044801000c0c5e0050707403140c0c400e01040314440c0f40403142c2075800505a51200d45002840c80742c02d90024000c046c0180b00400303030000502d2006411180b242004024100ca4001141498580c031709100d40510442c8284000b40340082807070b180c15860740080e02d1456940c08015224140184624000f55008001660ba6040c10303018a90f040090340090792166008462071980703a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816565512 1250 816564262 816564277
    0x14090609180f16050406050307120e01140402150306030a03113d0608120d020c0312010905010905130605070306051002070e090106050d1b080703030e0415180b011103 73
    0x252075a4140402c01040f80b0300281601e1903490300501c1c20f030405070700a0043c0400b91020051140d690503003141d000c6a034000000b80000c4500811082203980794145890f0700a8400f42e01400d2941492508100340c0c0046a20401000d0014108251385a40031500b0084d040d003283c2042c000d085000e8940c1d00e40342d0013105080140030005803c07002e041038a40e4900341c01c4030200c1821b450001d08200003800480c64504402c0b64901c00381d100c81604801c04007030b00c11120740540500000804000802d0100004c90588900b0341081005030389400c600c0c03045034000d075400c00300100380300c0e001305c0090895040945d11a141b480c000c1405a40c0341b01240b0503039044207102c00581c2202000340400e409042105612540400003400003030714106c0800c80740b0081400c00b51400200c17400400718000d00884000c000c280d00f50485410070744c0e0f0b080c02446481003020640c4101e0038508010755440c500481c10060341c0f40070074001a400d240721200d070000c121a0740414140101c982c4036001420f803e00140c142c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816566762 1250 816565512 816565531
    0x14010c08120a0b09090d0f26041b060309110f040e060a0b12150609071710031e030e0609130905031b061e070311190f1409060918 57
    0x11010101d040100c4c00c40000c0443c585548502c0600700100e50055040c40f091400d41082903040169281c440344000c2001140e403103146180d03090004106c2700000400804207103081e204981e58507101d00b03c5c10344004100c05000c100c1150814481480c10542451070000d0090001800b4000b80f02d0780390500b88115003900c0200e9881da5840c6840c05d0004181c05501d074040c0c09000c4403501089000e42ca010f01402c1603008111034800a5985400391500a0040407142800c504070701c0c4c120714940406440e40021100c117442c10800308120248111010039081e4142c444644103070010051003404d070400485a941316102c1d045110722008644114401c0d42c1c0204042d603034951050105e4072102e4903102c1076822030ba11403410031804d0802c03054201625801d240c4c4020b200d40f030f00320b802c40c0505458070f20510091700c0040c42c0020100049440c10190301c172922035805641c461082035420900e001003800c40d40c1c1c0c0810001d0f810b458100c0080c00074000c020500d0307a4200b0000068240380c441114040d41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816568012 1250 816566762 816566771
    0x80615010915030e012f0307170a0902150703051905090a0b090a082e0213120c0f06090b0705010f02040f0806090a0f03110c100c06050606030114010c08120a 69
    0x14650081c05040810400340401c40c4500c024003207003d1008004400d242100031b008804601018800d0310052000d850028181d000c80c28a2000d4600070710ba10700c1c1c05c0307107c1e842402c41c00002801d01c100369400660540c0b01c03582000d0511012040c03070081080260b080180400182c85a5524400500b02604001e011103031a10958818890000c0c5a60010145603110f2910308140ba90725010f00201160a410040f151050547e00040030740640510086180104140403440713140401c514a0014099100500c005655400f0400c40031094001c0d4000280d06984c00c0c084600c501008101c000d11400000460a22980c1110b040341c00c16006594078401b5100c00700041c8030100400d1b500035000740041e00200300d0b180d6420b9940380c400c680040910008203890350402c2000d200614004d90064201070407605003100041c956080030501b03c448500e0b01c4042081400c110069905860841451a0701404184019605000302c2502190b218008004680c0365046000d00315000348500c21000c41d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816569262 1250 816568012 816568031
    0xe1207030606081f0e03031f0b030a0c030b0a03050c010c0c03050106120c0e0c07020d1407080123060a06030e03040906090f0e01140f060f03031c060f08061501091503 73
    0x32414107996005841003424001703c00002c01010040303039007004606a0b0f000480d101181d40c01c0001c0e4080e030001c004e400010080100008440d003003000c1b401004c2d9410000d60b8100030420420040c1ca0002402c203500c04601140d1650080c0784940c4c010f8040c03201d4444890340c2c0e41e100c0382500c016030082d064525400515604100c4008000c001034182c0300c040200f01d240c0b0400d42d4000d4091b154000c0d118000c403c048000740560b502032030360009172280a035808036848040185c007a1141080c01d00502100700141240d0000c91070106015007001085601c90a00d001030803000392030389500820450104000002e0b100031a07110782c2c4001c0c045510007040300c800d9424002c0440d100c02800030000d904055480103c2030301244026441624803030006566240c420104c1c1000c50306a00c600d4141c80300168803501c1c0720801181268000c28414280081c41d120f40b02c03880b414245202c2d100440c0c1c0703c10b02242d030034119600f07032b464201418540030b010729940302d0248030541074550030340012a0b6101c4090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816570512 1250 816569262 816569293
    0x1e0a1e0603121d0906010504051f18030201050304060f02220305060c040b3a050906011410030c03180b0f06060307020a030309050115181404030e120703060608 70
    0xc80b81d15141080380740152182035002c04401d850103c01c0c840e404440c0001c107a40c3c011000e640103448080c1c11007030010358102e00101c40c60207001250000c9007540341812507610440c02050141d0390b041e50740a0031500c641d551500034204128012500343e40901486107512210000841e041441c4071841001504c0d5003002800c1000241c9140e00c04441000140110504c0901f2a11122810a610100e0740300300c011845540d15800c0300000740d081021503c594560160f00700c540600190025101e1907640c2d640030442802c44c0012441d040312040c803105001d640264803c000120003410041351165241d11200c1511500c00c1e03003100e5040390343c424000e607140c10001c440d90180d01524a03e185080c4804043d40d07540442200404064680420f80c04024080d0003245041c204071007070f100015102c0710308045000ca1641c0c4080c00a1404103142c450045900348580102d805480c0d245214000b00284182c0f030070700d440041418416900000000f40c03103485104020320504000e06001c3c09887e218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816571762 1250 816570512 816570533
    0x605070504030b07022803020a0606081b0301150611010204030c06030507030c0806091b040e2503090206070206071a10090c021c111606090302181e0a1e0603 69
    0x4600c02c550104610350100301100c0300241b9030406090106011030910710b130885c41c04030380f070354002c2126040800004042c1130003d000258410314a51402d011f40c005800c3c58203c40d8451100203141c005104100401c9010781180c10310290210005890191240c4410780310304d840354005000669907131b0401907203a51612a000c08e00c0c00313900e0f0034035580c140580000c100d50006499420120518144c41112810000c2102d008041c1e40440801c00e2038581c00500c0d06095401c18540018017040c2c208595038400e00c507550310a54000c10090a140090302400b8403600405400c60340304c01082cbd4981000702c208031109114503c00c9884088031407d02c1705000558440901d29000e6611186018421003451440b10b01480d5031880c040554030100d03541645407245407003401c402030002501c003294081d44002c4110949009980080780314100c40704500c59008100c8405115035030780d1006144400c030400c1125000340c2003840100d81c2c405034220b0141900d40c4180506c1e096942d44400b00b0422689400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816573012 1250 816571762 816571771
    0x10b0f091620011b1d1e0111190302060f071b030507150501090b0f1807090b0a0504030c121a040302160e0a0b04020304020321130b0a0306051203090d0f0605070504030b 74
    0xc0a00c1c0c05004172021801c48000000480c8401030300c6c20400c4243c3c0d2050785040c84022102c8c080721280c090502d081801080091000c9d001070140000040c410700ea01411240100403aa4807200d01c0107040709403a000c14a804000c40030080308115060110342003e80c040082d60865030001000c0d49000b100004590303d01103464081d20001ca00c9080c0c5540b41c640020a4645840b0440710030364540d00221046161600503000500b8003040c038000b1160301402600c184c0340f043c42220384143d1209280004600b020b00010b003d00f84800d810881926002e0b031040c1c00a10a00480e030810142c002c01d1202c5804030382144071001b0034803013080080c502d40d0042c4000c1000c03e40e400c40c51130420740c0200b52601078038004148542c440d40a210140c65246080314200f03140c684032000007035124101c200031540282c4c07103000083d0801e0004210b905d400d60910786007204900c019864007140209101190200c240b090310195540514030011a0003030080c0e5110303241ba5550f146c1c0d5039080d442c264544840151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816574262 1250 816573012 816573047
    0x102010b0418030e030309060403050604053c2a040b0f1809070b1206031c09090c090902120103050d090311010305041112010b0f091620011b 62
    0x4100d000110404588581c82e601031a111101c10103072030103c0d18601c12000600d400501c0000c000084c0400800c0031070007288244155030f080da00031844507420705805024640c0e00001c500300190b1701c2994003800040300701507200fa1024044489040c0c0740848903581c3d2980340f140ba01d1030902c100e02e0944a407456000c0708403a500304048010300480c404560103140c1d0051004c404001c60213010307040000900500801440c1662000c100b205c120243c40c0540d009400303231103034804442a01c5040c02c03400c01c241045503560411b05160460081c0948038080005040c010701d110041040c004c14001801c04054103620f80b10b03194994a00036280c0719042c00100c003008500d0106200042c25031450903007003e000d00e4003150f45d459074101a21000000240107030b104d0f90041c0008805041034020001006086a9145003441c0c12820302002c420201d504c1c1c50300c9000741c0c0c599410750b4001c140410211030081441785000360744e059880d0071240c00250031000602070f404032000182e803019000d0740020700e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816575512 1250 816574262 816574271
    0x2070609080601170708010c120606051c0f09020d05070e010b16150204180b09010803070201021903140f091921031b080301030611160f2306060102010b04 68
    0x1401916041c044c000d00b101034105a005104180d41044a50b0141000000030007d02c20400c501401440140c0210f1802ca030408a0000d0a140104151145543d01c1405031910b4401c0170308080c000e00203c13005e0044541d0341c1e0610409a12207164140456100d01e00900d200d5003885c510424040c416400b252032014100300c0c0410b070524200c0e481c42003d5000b440300d00030111104038007002e03014680009030072044160314044081c042d9001150150f505807440c0c50541d80301c1002d10340324403d21310b002e80507a220701d0003016a00200e0049031405d5000c0d25100403020640380c424080707a801051013008403103010508041e1071401500425006c07640c480c0c070200f00c82c074002d6100c3ea5800162403440c4e0024289100000b810701401c0345a40d507150144413002c10410b6440c009005404c280001d0700c4151500251041c0700000c43c04507403600c58801c0d00826202942c0e070703820070301d10302041c0f040ba5099042c84440d00e40302c0355454040f10003070112028042500d00342000908642ca46a0010720440c1407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816576762 1250 816575512 816575519
    0x3010513081903060b071109070206060a050f0d05032101140d1e051c02071a0f0d020f0a09030311060c03071b0206040b360111101b02070609 62
    0x40000302c64107194541c2c00d00c091212001030940c0108074030752200790146400100d0008001a001c0c00c608103200031a044161902d440c2d40480e035400040314600c5e001a11140e040c48180751081c94107038940702c0105034601242d03e50380e40500b150002c0841081c032183c1100040b40c1c20408921607405400001103138200c2d0341070980090100d280282001d011884488100003001c0c03c18814030b00d0341508a0120307550901da1021228804c445c9880c60001030103502c20100c1c85503c0151400b0342e1601c084125400c0c010b590a03030030425440398038840b103116030800c44c601006401c440a045a00345a4540205440ca5400c0c041c091907002d02035000b41e90804010071410118100a882d08200185070070302140c150316a0030f42a40078880e0f4040d501c011b0200340094a25070140044c04540c1300042c004026a40d840030381144180842422200465841c6000d41e46510550000030035000c10703411103002070382c0094948111031750400c102c040807020b0381e4103111064040090070002e0840b40340c0031120a01c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816578012 1250 816576762 816576773
    0xd050309060a18121a0403020f0601272f040909050109060b010c0b0a0b031504060e0d020706080c16060c031d0c0315090106080613120e0105030f090304090c05070203010513 76
    0x3502d4118540d811317501012606040c400c01200d10703109c00d404101e0b040c41d4ac503041004441040c421030005101a400104210412580208181d0500b2014648001d00400120a0550402030341c13003c458207003031200150260a40c00f0740c0c89900d02030720001a40c1d82140c00c201003a5299801110f06200c0c1007140c85000074640c012041c6d12141040d000100b00c030403900003d00300107040344602c4545940c42c0502c000c1c0503040c6d020b40c91103030300807080702d111404520040c0e8440700d03240300e80d1012402d01c00002d4040c208800050055400c5400f100031628900d90f90f9004075039200340a40c0010b030352640f917448980414000803400740e440c80020b10314005400000b07552203070780364032003501c2506030400700305c00c40c800b5000740015004000c243c2c0d02c540b81000c0e0189030207800342000e403104032000342d24652250041c0a80401c5030b1041e07460616548c1c495600c03101120f0301400030015881b0800001031301c3c200c00d00c030b880005103441c5c0d10b040e9140c14500401d400d4a101031f1a41c44014651400900080d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816579262 1250 816578012 816578033
    0x909110a12170c0f01050907060e06120c091c02131e0f020702040516090b040f0603180203161d10060f020109060c12050f060f0d050309060a1812 64
    0x16401002d4110503040e01e91040000d000c0c0c0c0800301c807588103007508100310010640200740715030000c0040700c02c910741d900800c44400030307102c0c030840d08500100981c41400490340d0b040c903032000c25640154904440741000c00d042c001d0a900100c00310103003039081030071480c0428038201000c81c001400d0241c0e0b0303149280c0c40307100c0e28a0081e00380d01a90300d4100c14800d00030b076015a290749400403c100030030b280508400c498100c840461a0008400c03950204258070220162170640f51031280000242d030404c54194001c203030f401c1004484c0082c0206030030040e50f08020034800300e600288215209858842c801840c080320f9440700b40255507a804000d419505da540040440d109403601d980d00244c0120709a0041c04003038409003030a0b090082140946401228a00c81800b40013020030541c1c0d520800c03098098010f850056026a02c03d510700d05619294495800c100d00800c00d0300e03c1c0c07107046000250541c0c00f04440901150a612440c450325110140e9080107001d002207400e980000c65540c200d190 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816580512 1250 816579262 816579299
    0xf0604020307090b03122d0309031245010204030b0c091302070305030f15031209120609010b150c060a0504060b030303090f2116030314010909110a 65
    0x80341d0f43c1c41c0f604c00560341005011320070154034180755aa000c061180c03040724069424a80400406007003141000400001168415910789000e1401c14070813178010401120701500070074420b600780900d110b038007a520b200c00c041d0011703130040b0003080742d00c01d1403060403024207011050403648188401c00c00701c0d00c03d0346c0c09a0721075542c0744074a03a60440741c40011002c504403c1d200c3e0f449803010900741c040641081c000d5002340842031041d0000d50714003050101511000c00a01d416401c10001603ca805500b8064a944c1800030300121070380c1c140c1d54007a0310300030003121005060fa450350988256400c10b125282c80d04c0290850b83c41c80e00f64007011181d03560001500401c03600780d481c07001500788001940014200a001400d0380d5590810210303103550354901c0c00b24181c4900460030700b028411503082e8214084200ba1440c542003205000454400c10b41c844419018580c9404074184038880c244001da0280140c1940054000900d0a100480340811700c03040d0300030004c2c80410700801d8a0b4200d40c0120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816581762 1250 816580512 816580529
    0x2d0307020d151503030903020f0904053d0614030303010e0106050904021e031f150809071505041802031005040905010906110c061006050304021002160f080f0604020307 74
    0x5201c201c098860003070160140c0340e9400d50790400d004c000c0580c051480340490703000310b07040006101d0311b0080180c15072060b40d00900030350004840c3c0e50b8103802c075410803004960780c000202c41d09a000d0f8030241c07000038144510101c55560302050041c00c1d80c0d0703202e251641740141c00650840d81072001c1184241410300400051040100d403424660796240c048500c1d514009180c10409006505680b00c42d0300151099000710064100401234403040700843e00c01c0741c1200c02a4100c0043c405400c0e500c0410152000d200750042c0d12000c107521658a4500a4200056644c90340d02d615000c005600d841784034230020001801003090080405460b401c01080c0c4038200c6001a90f0802c1e850517070300601d501400140f4850402c2c03004d10744000090050704160505100743c600031b5461726050a0019224000c00000c10002e1020a01509258034483e201c0c800b203004079405903a5915685100e0b1803030350f102c0188130a0405060040c1101071000300715048d40ca400401071410070307038000383c0c44d1b10681c050403d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816583012 1250 816581762 816581783
    0x10c050306120f1b0103050619050f040f0c0203031f0807030b0a1410060f020f07030602030408070803090d0e040c020d0f20012711130e2d0307020d 65
    0x100c0220a20948040e070402c00111011080009440316038581c1d0f49010301c0c00711f45410002015414040d00d03000110102c81044654181400e0801c941d103002000e5003030f04070b50740b000d105546078807030f1245903000c1c50302d80c00075034032460000c000701b44c1312002540620400303e0100d0f08202d800c9000036410181d90780f25a20490380e555911404005062680036881a10344610034800d1110841c2c0c05d40b0f0586e0110340e41e002e210007440c0d009030b944002410b02244980d009034800c1001c110107901a603046803144424a16064403030b11070000a400c1030702c1c1480036401c03000d0710410290f049155154803107406e0310705002183e8180000703521220b880c02d1402c1170080540b41da00766a07101e0100e08810030342080603201510441d40d91a4002c1c1100d00c02c110034042c0d44008003540c185aa081116281e034031a01ca000100120780501c03003030001c0884000c1c462038030752580d0401d01380144800b0030801c1060b041411109022a402480544140c00b010345503007007080804090380f60500000280c0c1e401c04038100f07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816584262 1250 816583012 816583039
    0x503011808031b070b15030708150126070b031015021515030706020609011a0312090f0406031b06050a02032517030411060310050d1a01080d11010c050306 68
    0xb103282c03180c0e007130007400480070404200d40c1017644500310344003071300a03003c60303641a858035007243c1d50300100078410f4000c0b80e0a100401420b10b41c0201950f6a000f0b10070706501802800b000d0078681006030304001800c003004804c02045052840720300c0001c0101c00c0722620300991000001e510350103032a016a03031260840340000c200c002c02e030700000b41c21f58014040350005a600c000094135a94180c902007a01e500341014840a085020b001c080844001009008e440b5090051100b00b644401511900460440d6a501e04ca50352403042400440c001c40300d80403171000010341481c00c105150400b2040c040d051040b000b0451303002060300c691558035600e4071202c00201464901ca64070001c0c0003410010314039461142c007052035000e5400360b0b1040401200b40e08109007001640d00040359440388940c0900b00800c900c1c90865a4140014055001c845e540040c3d01c991051000098100a903568040741d40f09040c0303544606084030030f03403801008001c0c0040c0030380002c1591001504103803107100c0206046 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816585512 1250 816584262 816584311
    0x3010501080406270b060901030c0b07240501360b1201050a230c031314120405030c03031c0c110a11010311090a180902040f06050301180803 62
    0x6299540134005100d00341800c074104940102840d4040b24880240e00c007007001e5003050003195050325840048404541d00305172512290f5002240c1c155403250310305070b50701204d40c8001c007880d2401c819001c0c08541d96051410a5002084008400880780780e01440d1ba020b10400024900d003080443d0004180101c110f03000035a0301c103000c0c07460f03010742d460a02403025014259005a521350800300d1a40c4200200044681404030215282510030108000240304040d094005c081d8148c41800d50040c10240b07090801c0c94040014102941c1980c0020142300701e14082000c900c01100450082d8600321915540c0140038010031134008002c1c0c2c41d1600c4008082c000c0d20b040140d01d040a0846a1041003810207104405403000c06a0100c0d2411455580a00448040b5a40048041c0c12001e900e0700d009074680a4940d02d2600030041c0c1d980c0c19040e00183d039280a038001c0d6104c120800700340789040008060031910024462400014242100b40000d01c01000340d9500c92400fa410303510400586941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816586762 1250 816585512 816585521
    0xc0c0e100603181a0709150c08030703180b04031404050a05100905060a03140112120f0e060d0e070806132015070501050619090b0d0c060f0e010201090803010501080406 74
    0xd140c40c201c21100c900c18075807084c80034460b0610341d0303d080c10389555004401c1d04042e100140000140b51b01ea101c00400c40d83e00042d9081041450002507821070021054400b00d0b80300e004580041225052100b031550101c1242502160b1105451401c1c0c544800100c1101851048a000700124034221110b140101002030082c07001410341640d030001d0f42c400a00a00364100c1709080d1400b60000480c5020400644080096004049802c0040c08900c142c2d044c20070f501502c01007043e002c1b440c40c07294640c1c40103044900d507002d0b008102000c00155440c08d00d00d20340c004004692240003041591901c050b50100c0680c2c00c40303101050031000542480e1691025409560002d640f904803808892040004040c514001c02c0200802e44a0380e0421605151071540500050b5103103100b84000c00d656070040f0122800100b02d80c4221a070b0703a40da1030a80380545e001c079010820010301d0820791508136030b901d50411024402080000b00c281c2d01c100b481c1c001030240a040203191070000701008040c2e4003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816588012 1250 816586762 816586811
    0x31501111c050304050d0309020904060f2703080a11120901020c010603080d0b0a050a09020f090d1a090606061b0a060603050102130609030b0105042a0c0c0e100603 72
    0x41c00041140552000e48154404d540c201e4452041000c490711013072291103007940f95079000300b00ca0000d031500c0e11011702501c0e400b500510103030f640310500a402c004ea04448150424516034107804030440703040141084400400451586003850240c0840b1585001107031f00301c0c1103040da020a542c469022060080c05042d04104813580f034101c0c04000d1180d544060304442e1a020f01c1403004010080c10310000c000c451044541110284205002351145134001c0c08014810080803070914495900041e0600083c8505444401c42503a0002c3c48072095841290f022881d41c1c010300c11410800301082c0d091049a440081001c010030201038094402e10440c00c0302c58102900340003903602c0e418038038000c0d4441008030061484080b40011154042e82d2402c0c116600a00320902030307840c100910000c0c0c24000245800090391446d0b54038100704d5130307402c583d001800e5074607480c07440800d19166842d0368054000c03c004222040403c0601d041081c1e140003076400034a4045040e403500c107008040c0500342c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816589262 1250 816588012 816588043
    0x6030c031807080f100608010c0e06180303030a02030405060609010320150a27030c050904230c0108010918060b03031e0c0706050a120203060105040302180402010e030303150111 78
    0x2950540e00c13400081070301686000c181e04000c1169203900d0b01d401c90710040031000204503008920012443d00d10013402c1405001e02400a68801780c0d0300103400d40e0b00440d140450300d079001c0180000e0200030000280d01c814142c400e10310725415a114480024840307503d000418140200c003680d161a01680e400d00d000c004a10503403540903141e0050180e039113400c1c510704155040400c24400d191410051000c60344c2140003210b2084c1070a0600c804141c000300142c4000681d48100130881c4551048034994003403500180144c0d80120f4001403a084043c3c0c841d540303890a0510040c18200090880400c46a005800080350f03030a800219066008904014101c1d01d4151811500549090010304901c03003080140e0b81201d44030b200603900360007051900740009182050f10001800ba6900130758001d1014180b00c0d04066481d40003c1c801f0000000440c12582808180701c110f5070801201454070304201e000d10704500d0035034440c212011404403010304000141400c0b40b1020001c5c080f50f2540319807070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816590512 1250 816589262 816589273
    0x30305121f0626063f030c010c020c061213080c07031a010609180225060b040603080d20160317010806060103020a020f0d031a06030c03180708 63
    0x20140a4141c20400b41d90300364456504020010f00e44242058920520008013210b84c00c05a402c07902030101d2890001c0f440303802c0f0443e4440c91000c000c200000032160ba031401560707204488401c05003540d07802c258a905550202010400b030307070303910002e17580c0c00d40000210040300d64802c0341030101405c00c0c030000350020900040c0ba205160000c1808030507240180004000401c09582640c407443d000d20416001803140324040c80407400c10541c01922101c1148054204261803800c03414490760907100d04051601c012015007008403a0040d989112070440302080460f03d16201c0c060b01c2c0c407810007007040c1c046d0344030148d1301c6a002d5003402d0b451401e82881d8a035220b9002c200e03c132042000742c440c00c2d000b090841600d04d08900c200041c06049c1c03458000502480e44078900150069040360b11000b00354010030502404d0000200305090030200c4a644c04221240d00103014070101c1d500e080201d005040c100304000d03803403e4007401c49030008095041480b21003a4030110504040f081e800008240c01003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816591762 1250 816590512 816590519
    0x504020711041e0c0806030a0b1b030a090c05060703020c0103050601050417010c1704210e0d06050f0a060605030c160503040b0405031006030f0f150f091407030305121f 74
    0x84410450310100141c042000c04040c134815100301d030080b52590341c07503403200000b4000681c0c3c0031000390300401820003d000d91408820780c80d681744c00c01c40fa40d101c03007031f9101410030600105c24080002000252102e030300d02495518001d441c2c9003940c103000d040c0742e00d41001c5070f440e910a00455000b4200b0310028001703101d2101c851070281045400e40c00c001000b01c201015840d4001c0740d9103014030390092800481501604030150780b4a43c0c5008401442182610030950781c56180c00030910300e01c0307a00006002d00e0455002c245290703010b800c64510510304003003072020940040407250071040c1e1446140c0c075492000b09005440b910700c0d01c000c0c00b80c000420300050308000a800b92055540c02c809960501d060b1380301c648111601c0b8480a00006c001c8010b11000c00c03807881d50003900500950b0b940003020058100602a100f249040c4206d03135589040001c18000d43c80c1120f01d00220341005007141c5884c6450081050080800c20490b5100c00c2005c1640700c1c8a181c4c502c101600034500f404801d41d503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816593012 1250 816591762 816591791
    0x1b07080a030504140a06081b0f1818060a090203090f120c07060e0d06050615041716030309060813050118060e0c10030f0e010911101404050402071104 66
    0x2003071150149520b0881400c1311907280840010080da10950f803004041e035a400c0e203510181c001d045800d6851641003203002030030404c0c0c2c002040591800007441c0341080307804050100c02150341c00c10110f103420b0030007804125581d150480007121408140035880f51104414603003010783d091001490346c0b181c14111480e80c1c0d241c2000c2d00d030007040d0340d0a44a074680e50700780a55401102d80c22072540b14420340b0301030f000a512a0720070f1f500024042c01c070041d0303903504800c111441d0340190407004c042e5160b14802c1920040070442c604000b05996010411075196660241c00032200c2e000700c0050080c96400030f1000d805403e40010046d4222000b4030052051002d01403605440900a443d02820401080100203001442c44d40b18180900000100015900110f00408584103015a041d44480012550361f07030034020503031a01d0283d405900340c800040c080021003030f10710395003001380a9403c1420047d6454103080c0e4080342d1003070343c02503500e032018030700340a034000398140c82c3c0d1340140b034a000092200f9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816594262 1250 816593012 816593017
    0x91503090d0906030e0307021e12010b040606030e15070c05010c120b0d030c15020d060f09271104020409051f140f190e0403030509010b12031b07080a0305 68
    0x20b515041407180d00c0d0841202503500089034030b8a10b40c002c10001005040081501009843e181d6a03610151000070004ad0a04242084900242c0d103503408143e1610700307446141e008101c581030400400c140d4079180c47e1917502e182c6080034564032003800109064024500d003c56294040000c12079900c418201400003c5052401d5009501d000c00d503207101d08122203203440c01038050321820002400c03941c40c1c0008100e010080d000d801e80a110301c04a0b002a03028080c050058844400e40e41e50424140c28206d5a10f211188203040ca00c2c03001502403001c1c1c01d030480070503030440c091300418004480410081e1043c0c0d440000002c2c9002c00300401033a0894615940c0202e0841d01d0802554451a00c00c007407800c80074007640040414041c1c4103a1038070520005000e40c0301ca0381110a50340c0d511741661403960441c0e0036008240c59404001c0400001e2280e0715448104803200070348040d07414540380d580e00400c1c50b03804110130700921001d040481002804000c0c0a90400c54510400c14980188540c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816595512 1250 816594262 816594283
    0xa0606030b0610021015180504050d2c0316060206090f0f030f090a080303040302031c050408120604090b0106050405090109020f030619030803040809030d02011b0509150309 76
    0x1408041d010a98600c1e240d0041c0b0140f002c640d000344124480c02d01008014000a151a0408104100009000c2020380010071001c0c0400900042915090510b1410b1010310002c0d07c0800070125450b884076a200710382030440c2e846000305039030708001d0000030034a1700000b1280010340d0b6180d004001203140e07000034840d00c14000e41040c0c0c1c14028850301410f90b6010041441c020315002131014071403081b1403601500c801c10f4000d202c1c0c6015039071460524107503403041c0c8095005030000940c000307160070380902c1d44108c1d40e2120810811842c00c0d03181e402ca14000e684005113107131500c4020500c55a960741242000540107039000390031356501e58014040303503c18402d4901480c102000040c8400b041d100f03403072050318402c044501d16a1880108030102d0000b182d940402d28041c0d0000c07003c03418020103144590b105500280d42c0718003c0c41014a070400700e001d6a02168145050700d6890300581422070707c0501c040c188541c541d04101d000440407068542c2e2603a84000c0801040329a400008104004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816596762 1250 816595512 816595523
    0x2121206130b0913030e10021e0c18040f020a090507020c041506112b11010c021e0f0a06050739030e0301020304240c0c060504020307080a060603 64
    0x100d00c0d014100e9095450100245038005070450001d09000c4d500c0d118410380901c00e1500e0080a00454000340c200b0200140610050340001c1341204003420091100c0d035013a5410000300742c041d10300d60001d120081135030040e907010090140484c003000306002220039041e900800101019445101200c002d08080300c043c00144200240034603030381054070075061940c58030380c00358445034240202a1480064603141030140c1c841c42c40301c2820a92000ca0640e036048280100e04401c40201d8001402c4d09109480b0b444640d14000000002c50b40001e5030b104078400d001d181921036822480500c1c02d0545488042c4034501807904003004016480e031025116025a440b0240b0009110f4070400da000c229080d00c10354041c1d00100c0f0720508151980343c0c02040e2081c6000108409100c0200e807d980040d102126000d607001c0e802d828007200313181740300310450405200304021001a840140040c4600b440581950760b140081810342d01c05100c1d040150800f4000c2703a004900c9450405d000304454030050390b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816598012 1250 816596762 816596779
    0x20f09040f1b0c0803010e091f0902090a051e06120f0a0204110a0525020418050127081303020306010e0103140601060503070e12060901060608100f1502121206 70
    0x528600464000410344e400444907821a800c0100280d00410040d1100440c1d22130342c07251b07030401c000c0b50307201e031641481290010626088074810f1005a000242040300064200810850700212014500398040e00c80d01c0c0380c03800d54841c0780105204000780318a950107030040001480340f81c1400a03621901c5842603400304120100350042c0b40103402036904400002d0002c000280050710180710141080c400035100c100303140303607541c00101252040d0320014007602d80040307401c0504c44203200b02103168076940034200402d010341015418503213070790100520b19107010800a2280d002c2c2c1d01340c1805594058202e802030b586860403a010440244801c84081250b500500e181000200d01141202e0b019203034242151548207040d01d8100300103c0c4107420104100c2c2004c0c50201c108045e901461a0100015480303080c104020704c00000202480301a10381800208050a0f00c911041e088900144200c0f001c00341d540070407030a180d00c2d6207480103000c8003c075400451442842c41240220750441e822907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816599262 1250 816598012 816598061
    0xc1514060613120611070b0402030f0a17070c031b080d03090c06030b031515010917060403050c1608070501080a050f0a0b04090215030103061419020f09040f 69
    0x1902c2109456001c072003031242c0030003140d8500a41d40f0100c81c4612004103400d840c1c000919a50b400c0340300d040da5040c19003402d00003503040512000c1c0b90900500090001e050740d030380303d103200c568101416881c00c0a001440e4001c0c80458218807001c1c0d58050a441c0c8807000281c1e03180626001ea028000490080700c01d1809254000e00c907162800c2d500c800d05840b11072511134141d00504080c41300d0383d014007928481c0c00031000303640170480c842e80c1000f0150081310345000005224180c1c5410000e1a2042e08114000107a000503141d032b40140e05180c06581c40d0400300005090442000c1507107500c209420f004101e25101044007400d440080e038a800042d170b5900288130541d8810f42e2031043d108141c4020a40010315900400740140d00500b02260900b92a03010031b1500d0307040314000315200004401070081024a0041c0300c3e010343c10b80c140d280181840080004800302035600440c1496000865007502c0140d001a200044d0004104011414003828080003400c5103002045100e48010b02e42c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816600512 1250 816599262 816599269
    0x50f060303071a0402040b09040c231f0905031f05160c060903140a080103060f0203040308130f2a08060c090f030313030f0506090307021f0c151406 65
    0x11201150440c103100c801c0407078140803c2407030401810036078110381c40e040c40d03c4071a02c1e403100b140d006611465910b1255032900310007024840e000701510105800e01022a121545c0f0f50f041c100c017840e44824403c0181284101c2a00c02401c0d0360b200c2501401881144040700b0954880c1404444843c0c9050042d81c0d5140703890048814000000c1000c900d034008000c1c0400e0300d641c8440e031b1417486800c00580100511840c407840341c201641000c0003d881c40010f00803c001c60084031652202640c0c1903045091613030f4040d0064070010a69070407286021409414000e180d55907000850300700046c014900080d104030001c203000702c00090045540c10724001816a4002001841000302500c00d40c10070314004d041106a0580e4a5280c0d814032042c440005403a4544160800030351282e8460817840c1c6c110324102381000e00040500042e50000e10051015803506100400423011081d41c041c00d17006000019109240c03010740140600562107824507180c020381d0f10080410588aa080303046030fa59400f007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816601762 1250 816600512 816600517
    0x150f060609060f0c0818150702062b020d0c260a020d06081c1818050415090b06031501030512032a0706050c122e09050f060303 56
    0x35000080c00d0804100300c400d1042c109040c00415a1400b1106036100f5254400329800060401420181d070041046213807400e03140c100801420250304030f0801800303800160f00c500801b0b0054564140c42011070140702c2c1081d13580408900072031400c64803140e4400e488401000c200d500140890803905400710043e810540031041075513038111003c0c00d0350b035802401c0041c0d00000c0714103001e56268a40420303030100601c04481319155480038418145096040100440b44420012610700500101404115031001e000d100120b0384250100d10341e1280e107007441b00022014001c4102d1441e1018a10411008180c1180141c004400b00e800407552401c54080d406401e00c801001503100c50798590490030710801841c1e000c0381c400c5140c0070895940b00b80e010081042c1c420f0003034500000a8160800000f44105038001d40780d084e805d81840c44c02a543c0e81007540180802d00d6641903180fa44040d003644890103050300100c0c40900500980c1d070400d07840a000c0640d13a12414030212800900e807030800205 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816603012 1250 816601762 816601769
    0x30213050303130b0d09020904120315320409060504020f0a0803091c020901030303060e070306080a06330509060301090b04060506130e0303060a0f1202060306041503150f06 76
    0xf840d4002441c1030380b890350b1648022280148240c070b0f815003001503580c81c403143c0c0c4038901981d203299640040c4030303004040346d20104a01c01ca42001102c00e000c0d41c0141e00b03403110440052800d0210910010281304400b003540c41407d98440c0c1084079100070010541c10040c0180d100381c9085d4081d100302e80401402c5031840c001c0903042d60090202c0c40e11807804441c08001942083d4418918081a0300032402c6401e090300180d02003a200c5000f0081011a00020303680042c2c249010030000c4c0c1454074841d152410308802600840c1c90b0622012101035441c846484601e282410286809a0071004048103101c1d1260601c40c4d1000710002c0c0a034141806100c2c08984e1250050946545550702e140c014000070741481c0c0c00655a90100314103848910454648800b01303c001e64a80c5020001c0050700c00c06600452031011420100700103241040d5202003116604440d4192255038850210b4001c10040055041c5840c0d449c200105100790b440103480000b003c00401c0c01164200c441c44401d03100b0790710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816604262 1250 816603012 816603037
    0x7080f070522091b1b1b05041d060109061202131b0e01090902090d1e0f032c100311090a030f02091509150402070f030f1205041703041a07030213050303 67
    0x250800000396030785034030007940b070807202c50031b681c0398461010400720b0b0003203900f00b40154080c20b000b407143c0030200304aa0051225400500020f8105130501d5151100c1c068000e014409101e28006a010f540d00401541016448114158032407000024030b40c0030420041030204e070040001182d9078009000310f40c0b0142c00645103c0d00c040c03155072540b2044060031401e84c1714183c1d80040800003480380c1d4044250900a5840c0030100407406030b03038a50480800c00d602012000d000c49000942c40d08100c0c040003212505000031400305107401075541348a800d01f0194001c114500c040100034920103900841c900a03130300b0090607512a8070440504d050012241c0c0d021541f03400141b03d4080400100316180800f400140c20300d217982e919203a00f10ba081c6021000301e0042640f00054590003810358102d1020000c00703200c00e040a442e1024000c0400c1b1402c3c4040b10001b00007000d000d0000443c00300050446501d240034640320b94024001c0d0401032060a800c00d6a40002640e440c00000303482c249010744 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816605512 1250 816604262 816604307
    0x10507031214040b0618160c0203070e240609010806011d2e091202091e16020111120a093002100e100515040c08010e07080f070522091b 60
    0x3c09058400e00e08e224400c81e07143c41041000b040c4040d44251042c041c2c9450b50361045113441035800c12054000194050340216000c1c0711070261aa8040f00907a0880e00c01c0c24041242460100c0402448116401e80e50300401c04617118013540d4000c0c00c0000b40c100c0c1940000c0060b0219031030880301c10741540319848200c40301c108144094a85034480365040705102040f9031107540b1690715100d48200c21203c0400307a040060300e4100454083c02407207204036206001030306c3c2414a4008504240c1f007e4400c20440d542c2c2c00035001040404000d05d40c2c081c0c0704401048400c440f04100540303891081068000501510b100620300740418000c2e4590b070032401018240c2c242000350090b0060400406203408810004545006501c691103045c1010400e40d60358500d1350304115401c5c080300f202404c01000c1084000401840176003201581c1d4101c43e02d4a8035554448045512074010001514051045071191000203501c2019510090340d10300b503c007040044503603001d000d48441c0d5464181d40c0e05c17060311 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816606762 1250 816605512 816605551
    0x120a080909072f010f090813060e15031b03091b03120301140a0906060c0302010506090f07110a120c02010f030522061409160b09010507031214040b0618 67
    0x624a46110f40305002c000250020090803041c144c2e140300c5401e45803a540040d421901c2610003540c070020348041d00b0000f510030100c01c04507694451220400d2620300c4044081800d074100650201b88403980345002c60740fa420f0841440b81c41d541210b40c038032422401401400040d00380030401c80040401000108d003141e290007441c44030311240d01c102c0303a03001031803a00202d02e510180c0700f130074050b041c00e0f50b03400c08102080c0b034040d084a070041d1035030b84038545080400082c41c281c5041107070311004515000086007085207465190030740240b002001303010450065581c0c0c5a020100200700f5000b640c2d242034020345068140c049a90613201e606641300b503558043d100b011204860500684240740008892424082486a035031003502c2020081d006807810200a41600d42c0c510080c04000040d5441c00e5580000030307080782300f50b81009050002000400300107588980c00b20404103402010042c0c545070600d040340c0440812100c0500c150001e0380c00a050704c0c005280c161141c50101503507044102c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816608012 1250 816606762 816606827
    0x3090306050708060a0941010f090b011409062d0a091202030c040c020304030b090304050906060f0d0f0b1f140901170c07050d08071d030c010c02120a08090907 70
    0x2c000c134940c40d90000382c0d5556800e0a1147c4866030082c2845036042c440c440c201b69001d801da5155680c03032410014244100c500c1c0d40306550440e2440d2004a880f5036958141220b030782e11100c0103094960642d18104401080d03440198000d2500d103030b4644d41c00d40e1030380e155035038503d07102c81b0b642c0701039090f500032661300d44141042d40c040458071840c0d004481c00d080c2d4170358400d0018407084580310120741010504004071b0900c400a42d402c0a070840340541800c0044840071990f026001c4103454186d143e150a501e404040d03400300b4075456000d07010484144050468a030310441c0101c440e000150b070441c0590300458202d00351100000705944200042d521654a009000c82c0074110300c425040c104440320000300100040c441d52203c6e902c0d010114a04840003800010004250003c4461402c2060100b1f0fa004a000b20ac0480c00342401d40c19400d00307001052001c01400c80e0754400340f04001740002408a081f002d44040e102c200c4003010340d0307a40d00d03504a60300443c0250040e41a100318021007a401d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816609262 1250 816608012 816608081
    0x10204291209101d0d080c1206010c080703050316050903030901031137030c54050d051203130c030b040201020d03110301060c03090306050708060a09 66
    0x46400c210f802c5601004020000c84441e034040e80d004120300389405010041c00e010110000105040003119032401040070700301c0703119a000200c03400e8540c20004559a0041100541c2c3c030382c00800558a44059107800b408650043e50185101d030490740c601001d46200e01d04540407400d011303016605000c048801900a0540442c1001b5100c05c20b12042501c0143c0c4070090071031101c01e20000d140030618000c0707902d1141c2085091420542051001045140c029021085c0b041200c21050012250042d0580c42903100d2010f4241c2010780741000e080c1340f064801508030107a40002080c0001c0e99400412035441c0b60180020520703049100b010713050240040285034041505480e40802c03d020f962410400e016a400454910f803104040c4400d5581c100101d206000b0107040404c80700362011040c456900051040c1c0d010000d001d40603200300341c1701e5005400210762111080c0101d00304080040c0c00c955007107869500911001c0d40014468140d405080c00c6130703600003a01d207950040040b4a80518 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816610512 1250 816609262 816609271
    0x327020102071509031a221211031207030204090b031504110d0804090f0f05040b0606090105130801020d0c02070b0702150c0d03090203100e06010e1b0403050102042912 74
    0xd04410008003083c18616080c8031110b02d1403440b03205182810001c0341d081c6401c141000490540c001840010b202503460015201050a0989d00c0c002e10b4140d10b80303144281c003280203e18183c00700b48400d02d6050340251080d962140024000c0e035103450140f52390b0b0f0362055079030034222900c0d00204021501200c42032000f1840135001d180e43c1152a02d414100354403c3d4054000149c0e207181c03526001000d071045140b0b040d490b0345c0030f100303509042d10751004182000d09101d2180c180094041140e0380580101d40070002004400500545ea03000307102e000350420b18601c503001c0c1c1031050108045101180c4502615000340d265401e08041e0f4090000f6031805070021014000208000d160340b410421100000000a6802140d0b10066205041c06e103a04900320f00503080c1071a641c070080d000c0103c0c07260b0659844140d031130102e585240c00514074006000c44500d40c840005004811700806400900c161001003112042911200d9855119100d120748060101c100038401c6040f200d00e1652802d811 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816611762 1250 816610512 816610517
    0xb06210703110703020a1e020d02040f0e010e1605010201020c031606021b0102070c0918110d02150a1403060609010e040608060709090609050609040f03110d03270201020715 76
    0x280001c04542c0368072181040d40541d006410f00802c000441030400044590407581c078078600340e1540841c03441e6078020b000030b115540303c400c050900f520a5101401200c2240000d014000038030040341c3d2a2002c0c0e200e503a020341c503560b1000c83e007540140210b4111500e404010b42c9418810010090f0300c1010710401c035a890780070000da4105c4072000007900d503224020400180d5868040c40e00700346080c05a4000b04500d41421302c07000c000491011007030242d603000788440d14071051140c00a503111940610003544110b042400400364100c060151044c84ca25840b80f01544429a03680100e900040310740580c4810100031411007540b090301c000342d9110000e8404140c06444d00340050600b1012500c0c040000c1d01c00e14204107a11044c0030300001820120010007060600001040001c100204081e1103003442d10058020141310744a515419000741023591f101d14260500100508410030348800362400305000e4a0380700d145008000055130781600203180003454206a10004007119051405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816613012 1250 816611762 816611771
    0x1020307021924180305030405041d030307020a2009010b16050f0f0d050c1002210a0c17060a062303010b0d140c041214030c0604060b06210703 63
    0x2501491103020702002e50091440c880f00708400702004000b41800264070039201c0020104002043c40403049070309485041d00c011a4440071840a1980c044642c1000d100e14400001048925a408a884c0352858030031100441e8094400c0c030000c0341c10010882066000e51706000401695441100031303c001c0480380c40542c0d450880f600c96908010003009194407a4200d02c0f03540a03600414814403291030790754100300713082421900442c1ea444400c50700b8070900f01d03030000380c031810102c07101402c07440308400c0d445001030352400740c00f03038000343c141c2c00000004036410180300b01804280045051003810060820081546001011100001078120b8003400140404602c01034466070170065002c0c040c0e2400040e80ca40174504080304403003122140011945640060000d080da644003198101c81d02e0361100c40d281001800e100e014480350a849401c03a03c400511314401c403001040381449540101000c0191540c2502070050030321502d0586c0c1036507041250303e041c200399101050b50300584a403a0009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816614262 1250 816613012 816613019
    0x706110c030d0b1503090a03020d0c1505040503070b0109091b0311010c020a050a290405010903110103021309051503010b13021e04080714031f022d040314010b010203070219 76
    0x480c0755105590313116803030b00300e0b003968400d241c9c0402200c09400302c14a0126902c80054541550416200d64083e40b00e81d200d0011a003800020803d403044640c001c408034089503903901502c40205900c410441d040e006125049000c0d980744400310f000c0300e8001c2c0c605080348051400442d0141d20400041340e100105010110380ca8660307800403c064a6030002d1000a12174070304080c04c810191200303800c05d00307108110510103030b42d21507121400c07a60f028400b010030045100041c4d01a006840c055603448000040000c0ca8054541000d4003900ca84c0907582d045021b402c0038142600c0d0340d03103507051300310800c031408000b000000e500900c00c002e41000b2112000501e0504140254402d910900559018010500942040510b000442d0343c0403001010070f03240e1a511741c2210303288030758112841940490800c2c0324090381003503414905500c0040001c84c91030809210581e03042400161410f601a941444a49070148a208a1548c0580040d400d01580b5800c1120210060072011491005c032200007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816615512 1250 816614262 816614299
    0x4021206131e0c0612060801110901030c0c0b1305030c010f09120807020705040e010b03061602071406030f220309030204050c12010b13080f01020706110c030d0b 71
    0xd805030401e503004901440050a001e0069a00c820070407066010b914401c1000459200450302152054140195843c0c4214001e03001000540e1110071035500388805060000000c400800508000740c8080098a05021003250b40041c0c40b01c0c010310358142c1001003019103d0090000714010300c9182101d00e000c1100c0c01b403509407070076441030b004159110030080c0f08010070041c1000700000715103400405c0f460b00c240001d43d200310750300c40d04e402917a42d901d00305410102900300703544404000d01101c2d00343c03d108214221410708c0d80c0c0c020b001401064800714401c640783c5a030a10a0300014072480c03e40e22000c080c206681c0e00a090f0109240100704500713610903100c6200d0348407600a85900c1c80991450043c081075820040140712031100400014522a20060506043d2488201000e8035540e02401c2c0f544210103a0700001000d22503155010303403042054004203600391148105210040c1c19051a1010340218140100103030001d10002c240c03400d040d0320070408200300800c0705150546004da00b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816616762 1250 816615512 816615523
    0xb15030a1403121609030b061c1a070905030c1309050601030602071203060608070c0507080f01050a11090a03150b0405090102090306090606030304050d020a0906060206180c0a030605040212 83
    0x76489160000715580c0c94a00440318450ba02c00c16101d041c02014005100c01050a011400010030f480d105c000441c640d40c4039060414014018503001010240c401d0400c02d02d9100f05a9100c04030092101c005614103118810607412108054014100c0d00000f0341081000010002100c44490703844207058003241003040154001c6004240c0140d07500364500b07002828031000b105150901d410208204410f9901590443e84401d06151a80740a041d915120f810031646910456a52107071507216184900194801e50107141e042034204030300310003004814100e020345002d0030b0b840f446038003042010401268070841107181c500000101d5281031800601143c4c8151002460390b9808125100e40341410000c3c650042c810f48000c0c001440d109001a40d00e200707a00486000340210445041191074613001d007409084072400600600e0f0f01e0b0000213560716011070b503c02c054800f01c00c0d000d40301540815140003150000d404c0c480c0090954480c0c4005e03000142c4201d811568a0680d01c4007850705102c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816618012 1250 816616762 816616793
    0x180201051e0f04090c142512032315130b060711010201050630010b040c0201050f070503100e18120901120605090f07270e130b15030a 59
    0x2d980e03841e40e041c041240200e034600d2108906100007070752103019000f08001502c61403002207501540641040640e10b2504082c40d03001484190944884114a90160480003240c01c14191250030800030841500c10140301b03641601101c050b0014030340e041e041100c03180748802f4241c080031495081c500c000c640258482401907540316202c0349100b005680c280192904800c0c201d9041039080a07200d03a107003a00400004500d040300d0000c0559403284001c2d0440382803041c004000304910b08100c80c0281c082c2c001107030700c10340b1101c1000018100030b02890503240a40c141c40c011403c3c881c2000c0e26109114030240516840c0c020300c00007859600700800003104a2040b0f084825220a0020300240600e100380760b5100c411814200103200c0ca4071001031003603200300305039558902030b01c41d141c0035035010907030302d41b5203a0081c41209581210a0030f46555411100c10401003a040d0780d074504003001a5981003002014612a2004120040b6400100f402c1700b120043c19500c0d0300d406a0b481180768811842d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816619262 1250 816618012 816618037
    0x3090807061e0806010909020d0603050a2001020307051f06050306160e0f010e100c020604080303010f0b0307021e030c03120f0130080702062b180201051e 68
    0x2400c000e1600b41d1a01c0d08403040d060308105100e410403400182504050b0300441c2000d5502280c2d000310070104e60404802140c00c001039440100181c101009541068810215a54074446110406520010032165040c0e00003024003019035480074100380b507440401941203040d445100c04980d41d6420311150340214000e54143c1d414010b61003020300340507804954a44103010300d42c101011660818117000c0c00341ca04075040440920002000e44403e80e00c41406500200d0128010400050010086050b12180d16032030300207603030340c548150081c4000c54a80340140c00210741099a05268050310340202d9000341540c2c14400e95000c80781c0f4540207490481900250101402000d010205a05014098841c400600c28070b60340e07080a982614840c010400f00304082442040c00180700079141e4882d4000c00080c0d03030304608600b0805004841c1c1e62080c0b9500416030b50000c007420391141c0b225030000700b0103a68505c012038005503400c2d0098240400b01d40c501e0244842c89034010340041482002c4078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816620512 1250 816619262 816619277
    0x70e19020f07080f03090105010807061403190501150201050603030f1206030c060c030703180501023d02041508040b060f0d050a0309180519020c0a0203100c031104030c05010c0309080706 82
    0xc000a081d5232044e03010070300355008444103010080d4030030864000c0124100380e040e9a9180c603030224042c0c6c503519103000025450140080744888940c44403000382d035010303402403100d900c644040640f6403055582d1306006440c00c0010035450032070044001c2d03120303000030140c03900c014103803011900d1350744102d00006442d000044c40e0710406800081c480b0102d514441845076150034040042e40d103090303040c1d08000481013080104c0e2510152030000312501e260112650b003034105400e0a0000e500140520050351084000340d888040c4a250301e148140d4001e0304580d60b540342c00341400342010030022000d41020310a241480800c07010820301c4800c0d8407a5440703000c00344c0380c8038900d52038440304c11882180c64240340c1400114000540140700090700700da00144d4071203580030032524090080724020f401d40503440300c55448000a50011540c8802c0d41c030140320811904104281030311641c040184031210703090040c002035201d0b00311204290300c203050418990351640c0d2040d140c0007032580460000b9408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816621762 1250 816620512 816620521
    0x3071208060a060908030703030b1c05100b030d0f12020906030412080105060c0307110105090d03031b02011503080d0e0609070302150313020f01051e0c070e19020f07080f03 76
    0x20180b2100601d501c3c540510b1190a00001030348920a5040150415440e080c0c440381c540e4640f094000340002c44210090064050700d0102d8491428100032002240341043d51070040c01c020079505070010880c0e90354501c01101034415103001840c075040c0c0030965424440703240b0a8543c040214000c90142c9442c07500390f543c100c0024035901c0140c0019010702c00034400d5005242001054452a65000c00180c841115410048509014003050b2075404140460701c2024980c0603481003180d040450b600d101c00c0344040806a00f62065100d80e03004007852007000308049000f50018045248240c040810446038a440309450f044099078118265000300e4020400c40c07410403003003039000d4144520b42d815860900350700d0141c0602c034400a801501e5144c0704501aa12030300071141d04003035007100301e00a6042d1001d4000c90390840030700500d85102d0500d020583c0c04c82401c03010b12981c1c5031102d01442010701303603000c0040d40004110000e039600501100e00092017200c041c0000b03c03860502e4a032203103072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816623012 1250 816621762 816621769
    0x70605090306150d140a390617151207060e1503010902072a03300c06020f0301090207031d03060601210e1507050a09050f030307120806 60
    0x700035145042e04140c00358a0462a195400100301340707a0058680e650b45003034048154103182e0601e2004040703101210700e5100c4d60b94450340000404c240e0031a4510a1400c00310072401c00c02c060b008910218042d0301d0b807100c2c2061100c5c11a903000c0016003103494000040030202d00c412140c407140300d64035040b072070040c841c2c66840b562849001c1c00446100c8810040d60020f40c0b05071006000b140304582e0001840418400003e1038401010800c0c8035441c0284200a404c01075000240001c4403a446042007540ca20900c000b101210741c2c0a0410f1504103061005040d1262242d0354800c41d540340e003e120658106034241c000d180241581e280c00f680d1a10701d03150050801c61158808010750301031a442a0303264400141c0ba48d4020402e007072581102d4131440b1001031540c8002c4030110442d04107100c070705400402003505601c0d0016058415429241c3d20420394550180d10440e600062111070208107600d0268507038040b61300c02900b56807806520351501c02010400d0070100300071070005002d0010701e0a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816624262 1250 816623012 816623023
    0x1b0f030212031303050c0a020a0f090b0d0c0501030b01020f1c08160f080a0605090406020910050705060708060a03080c070305070807030b010b0d0b0d1b15120e030c0706050903 77
    0x1085440c1d654614070380b4014044841010f048054204000411010340d198400c1044400468005214004455603816502c21550890064880090510701c2c0d01100382042c8588022141d4442840031080741020011030003010f10845036411407060030055002003005200707910803a90310090f01d004903030405001030210f0354040e0a032985070205404074902907034410003982120b000d42c940b00089868804c50200649540e800150303000b0724410500040000d543d0017021558800d0341e0700341040101003010b80742130080d01e00c0438010b60802030000d0602481001c603541c1c8031400a2198021075166103414900d904450410201c50703002c26000d00600c0070800c081c100030514030b801440180d08680d0b5501c008001031044000410f40890000848250340d044590300390b40261000c113a480d050b0504d45040c0710150b03034100b031401030a00301107010207008140815107403482c0c6503012a5940002c5140003003030888607103130031800140712503c058842804120014816583c50a131900882000c050404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816625512 1250 816624262 816624283
    0x501080c06040518060f031e07051c03030c1704110111010219080a060e090604031b110910031e032a080d06151d100e0d02011b0f0302 59
    0x2590140300420260b500d4136102400c0034035540e0700307801984842010503c01d820f04120b070b40e4113026903004050109112000120440300d81402c49a500c0d90356001c1c810081d511820350310131500780840010100c0c1c000d0704260070407a007614029452908800c0520301041e03058408a8900c1c2e0020500f07902503a1003c2c050000f60008002180313040d10454801070000e02d90424102071004010005110480c03a0b40490001c05102c0c0e5260210b01c2c2208070076495480844049000c2040c82c82c8800110140c0142600100d0344035500d807545034003000411a4070740c8014600101982c030102c010000880844811410b041100c00001a1040340e18001e8812800d40001c0041d81a40c0441c0034450580c0c810101c8601d42c22a4503540c2e9113803110a6200506a560484282c00048003d00c0c0a036a0b440304000105013004e443d40c04040e6403101c10804010221200c40c00040c040340b402501e181390036148041c1e15841414000040e500c7e42d120401a041800c60585074129030f81d6200d02410340500c13940c0e0030b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816626762 1250 816625512 816625519
    0x14190906270b060d0e0a06020a020304170307030c0312180305030a0c0512040b100306020c030d0e0105040201080f090328111516050d0207060911030102090112150b0d0501080c 77
    0xd048210b0120f407060259002c01071140e03071901e03404d4030320110921000e40380a070800e60955980d03440f420003035580d034003e1103080003e501c0c825191140000120a455425516556a100c0070265448c00c454012018400c004080c2d502c800b40c04100e215014180b1040e0700c01d03182d0305d450703140c0010000101d5115059100034032000f0007a6029203840ca560303080e40141e00208403001f6491f082002c10450710b007038000400301e03840002e442d0240c0740000060112040061303007d0020702c01c010142c07030a80e0002d46000f400715074040040f8410301b16513a013042d8032500280c104c0e414602d000c00d00c104003464900c22419480d107010f01c00d680082d440940c80303154041e0000100f4002c4214000000c202c0380041c507114115900c01c0e80807040354071660456840d800a820305640b15100c42c242030004142c507042c2140c03000541d908441207800c06000b958410f0308161295441a035207140903c0242c20000c00342c50607442201000708043c0300340c8028105c107100c50640040d1035810b00c002e55203010702e45a0035510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816628012 1250 816626762 816626771
    0x30b0a050a08060402300f07230108060112020a0905090a02160b0408042312010b010207092a050c0f0a120e0103150603241419090627 59
    0x41c030029510740c00583c103442c13642005044103883c0034881b6400305101c0c24218280c003034003210340e03001035000c00180d4148241c1d403c2384c0c1e03280c292118000000c4c140a2003800d032411201015030080d404140d10178410b047c10300114024801000881c3d21421181c00407440700c1605010900740803020940c0042d005100710b14101c0160001e03103a2041d2800002d21104146001030300f0844240c1c00d0310001c04802c0001001000000355950200c003802c0a03680c0184207449000b4009601401203008512040e0003034207540f8180b881d424080c0c6281c007484c0c500b0302ca40714542849008501c1203404620a5640d4154a80c8081807100d0f080513604c50b01130f0025403195460f0760200749078050540c418915800c1c24030b40301c030064005801901c02a100300c1c6c01402404400103600c1c1d01500404aa1040d40c445012508080e018140b80074072680244441291940400401428408849082114991000c2050070350303983d290001e0b11102d0b04220400c030fa410f200c00035036000005842804003500b074410300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816629262 1250 816628012 816628019
    0x1f110a020306061e041404060f06050108130303091703042307050108250f0917030f0a020f032106091306150e0a050601020d0c051002031b0703030b0a050a 68
    0x2d03541c86010700603e2040e150184005100d03411240c00780142080a4400d10800001d2040d5407141501100c0550310503080106040c1e6100c102d200344000e5031016102c00441d0744a03807054508981d1303144411000d00d40d0b1424082c0200384130010206131502c000381425600d241c90311b090002d0820f41020455030141a044a00d410000032a045040d11000c0c030b06441180e54007450b040d140c03084558103501c019840307124600416480340c84904a044140c84450780c15644180c0d10640b0400e1b205210a1500300384050301c0e2004186000b00b50440c01441120b0f83e00107010400750565001a01d101a14000815111f00440001006e00c1d031006003110441080e04d81210800708000700c600c03004003926540c05441d0703040500c40e0302d004042e000d20301c00c54a841c0f800d40c803c1c2c0010b14055900d640544100c8000803038040c464217021100581c0100078111030000d14581501940001e07003c8410030901e203010304407804008000e0514140031341e03004942c0c1d05030581800303820210b03904100d0050f0407062090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816630512 1250 816629262 816629269
    0x5070c09061d010815040606150207050901120b010905100305060f10060e010c141f020705120307021504020a050d060203100b040501090512030403060504050a03020d0c230c1f110a02 80
    0xf4090f915444001940329031700d034602003004050701d0704825001124810300349d410f242e000500405441060b10400c2650742c842035080c0820441603001400230844070018840308005811083c0c0150013281d80d240311703d4880d641d0030f00300007080760304a0840004404000c0013618040928006010a0404150042c26440001c04240003120040c0c200b0142c144966601501005418100c0310b4600c0a00c203034a4136800c03a180a0750280c0c4050b5007134882c2c0c90070391001c8901e840c116030084115400074913440200c0b0b016218814001841681d11906a080c0082d43d034403101c1d44100321320701c14240180c0c1c910f08043c5501c110061500840d80601e000e0000b4407050360003c6602c0152082100e1080d001400311203c02d1651241e600020402400d00c011f200400c00009900c1d20060b01c65000d0f2005884402021120b01148030005003074181c00c00401113105066036440a4a4a4030b402075801c10543d0401085141203076110003501240d00304102c07003115a10042c001c10403801c0c280a030001000c0364002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816631762 1250 816630512 816630523
    0x80c010c0f0f05130b0c070302040e060907030f050c0901140108090a3f05070c060513030b060325051e0a0608060636040b09011505070c09061d0108 65
    0x15824003900246240e45030400f0709104c1c00902c0c01151051761500103109840d152282407000702d01071400c1940c1301b8219800840c2d054403884500000f050740c20f1a40c1c813540200c90403020191018003500ba02c03e01540c842c1c41200f4040c103003000710100640c9020000401a000c02003882c4d6a0b90011440d660001742c17131045000c2c019410024015280020000c8007150300c01c28007026412500c000b482e40745158014020300b8001d4060102c204a450f070b580810fa499204442c052882c040200c01c091000500c00d10802c1d421120190807110588801078000d4030f42018500c02580d03403080e820302002180391400c91480040780b012102c94050080b00045800102140228424003003544009041d0f6242c00058881c0307004205588c100c0d1120505c00c03040f200031080f0b01c01d44a4000b0304000c04046c01c0501507000156800f030040482d0703a28000058907901605c1c013060701000402c0086a000c6100707000c0d03107030203003d1161001542c98030b010291001031107007010107010000104010042c52401240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816633012 1250 816631762 816631787
    0x111010203090d080a141f0605120406020a1101050f04050d0c030206060f030a080f0d050112050c13060b070c0906060f17043003050912160c12080c010c0f 68
    0x80002d280d803180400000034040080755405000200300070800041f40c0d042e41c01900d482d00a0504d09007984032501251284114684104071401c21404100000e400c0d50040043c3c2c0910318101c0825204400d0307840c04c0d69803d650b460815050002800144201841140381040381802c180c00740182da564040c0d10b07188001c10700c51251549a80d10f2038143c405000b03140c1c034294403406141c6d50714620482100f00783c010b8500d03d02c9081c6010004101c0d60310000303404820b02e400400800090024400300301300c900c00c0c140e00f0000302e40c071030400043c01c00301c0101410303880d0300c600201401103003808220011141581d001004110000c04100d2000c5c0c2c00500c03c2441c4c144150100405545900300310b43c060350550b10300c5040d000780c0b070035a800940d00042540a0341c1c071f2039a400d04c02c1d0340310b00c00c8069a501241e000900800800c2000d940d075420301d17201003545248100400c4140301d030b681301404044c1c4062002590035040c0040e0141c6058400e1080f482450850304084032180780c6c0a0004150854105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816634262 1250 816633012 816633017
    0xc060b040204081f1d0f0c0f01140a0201060512030c060c0f190e090a1d1606051b07062111030402060313140d111c0f11030406020a020111010203090d 66
    0x1d00e13141c2c1000c590440800d94083e4400c3c0f001215002202a503a2030480d00d0020260148680d624014584104002c00210f01655000c03440340e4017001680703a680c403031004402590b684540008580d165025003540e0380031200081c5446444164000381070000007401109180d80030040ca0004081c0b00003922880809d800c0c400c03c80c620584000c2c0d4802214070340c1e55900000134800c1102d8000550400c0540491080d50300028052401c1602d985800d81d0701c105c010708004920901c9620b00c508080c2400e68000d1210702d038880b19209400303040c5021600001c00084c00b4801c03401c0480400c000c10468400b81ca8020020035a000765241018000030f00001e00c5110000007140b100d607003d91455105e02d410012642c481414403400c81c1e03079880c030b40a110b0045581004d42500b00b01022030300540b094a210981e800d41101d42408907180407406107410b06000c0d64881d0341d2001c0100300090006000303960002c0c03001c20b68034000508500c4c1c9803000d02d9150f80c010000c001022802040d12000145d4070b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816635512 1250 816634262 816634303
    0x1021b0a030f0807060603111302090102100b04060f0b13050316030303050a09140708061e0a0e1c030606091a0706050421030902040b12060106080901060b0301060c060b04020408 78
    0xd00d48010701340b00d6008050a1a401d045001c414440362002c2d010300e035130080302e0b20301c01c031509443c80e4001e81c0202044030340507802803890403110a5050300856042e0400500000340c00c0c2d1242c00204c0030760815001001000700c04656084126051a141005010110003c1412204480d00c40300b01c90290b02000341090b0300c3c2c5021a0302c030340c46608541010341c1d0201c1034004244040c01115a1090148518641403260754041008012955452034001c0070044074890030b82e54109925001e44000c40d401700700f034462aa80d00b03940e00c840380060303a01c2d4401c0d82d601040c098034101d401400c92281e50442c5185070720f036010300b0b2810180c880442d882c00e5030111020595603143e04100c02840004081511420280000349220560550003082054401c41d01003002c03000c100180420040c00010300e08071a07008000506c00300340503c0505522800500010038450b4603401c4554a642080e0300403400304070001400310821005000f120355040e07054601b181068070b09584075a441404101d2517000003000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816636762 1250 816635512 816635543
    0x9020a0203041214121606090206092805010f0c1e170a080c040302060720100e13051521010501060e13020f03041203020c150601021b0a03 61
    0xd0090760002e00484180481500f00750429000b810000342880342540500600c03240e4509000d41510b03080c6080d0b034031680c0c21000075583c0100802c3d1030341c1c042e40d000c8801d02606c02e2555952008025134082401184a070103110141d00605900940255061200010000e000e0561041c00305d10a183c018020001142104621468650052030058031440d0484000350b031140641000300040629969107808558030442e00039000d00580c04020345c800c504024104c085142141c1c00010700311000110310f000055000024049440b041c49200410440e001004a515141e1140c4400c0180b5510074001850141c0c03640d0780c030058050700c0c1845000040c42011300005004100710200071010000c01603541c60740c80183c451101c3d068009d10641010401c034005507003038000d0301d44082c0c01210305815600c42c3c1e900e0a44030840e0303d400004142d420b114500c079510341000800c6c40600c20030030030415420100f000904003165010040002010498600059200c0000708411a0b13000329403402040d04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816638012 1250 816636762 816636767
    0xd0b04140106030617012f0f0c0114060d030f11100e0606040c0908100902040b0603100618030f080717121518190e0a140106060c0c09020a 61
    0x1902000c03041400510011516a8155115005581004025861060460703410900340d0311286c3d610410403071010404446207004581d410030b034500346042c00d0b0402c003418240c0f0b1000d030007902d000a116912502032069003a404080c060700b1010980345400b1130311041c2c0740130340100c02c4822000b08114400484100d5500c0a1100410030041904180301940e05000c2d4507944802c00c1d5000c038801c5103003039070058009000d04000000c680003100507140180c1625404801005042010398005441e08485c09440d03640100941c81003440c00c0016010f1414124010b02625040102c00003440407001c092001c00c4410f8600d850540d880800c8581d01c07038aa1816016408541c018210f1500f000709880b5030500203500500d10a0100d80b400345074122a0f58104011110403403008141c130b48010011907514803640c07001c0403c0d1034a40c4800300b1840e03400f8010074649070400b4411b8031019180c14085003040070038008c0310020042c628292000340c959031500150480603108020095900150031141d590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816639262 1250 816638012 816638021
    0x1106121504020c1009050601060806090c090301060f0603020a170c0d051b0a0c1205120105012007090b01080a06030809010c0f0210050a02062518030209010b041503110d0b04 76
    0x600c81c40680340d040d229842132002400c0d1582046489002e03010011034503d100d00320f00e910410340201070b403005403100c01030f4440580c07040c02440d4065486510103c0e50b0f40084e0380c00340003049079a0340169529004840244801c8071465003015070141c44d000d0000641c580f130243c03960301c100e40d00005290f0300c501ca5007c038001c400d806031050111001c0b9100408030f41010742c07003014178040d4014400d0150b103802c048400c1c0c86180c01442076200b0034001445503520400b41d00062510309490315003c1120035110600d400311582c0b1002c2c4481c0c07208030315a42035070b0000041d501b28405140500101d429503640e081c6900600c1ea40604000e03950001205201c50b4428140880360064450324010311203040041050780000800d002610842c00480d00d281c0070710424034031006d941c908c8038900d1044c51108a401d007007159142841003401d1000480036a1392020b99030f0013080f14401640e030350f601d0408082c2281440c950110281864150410742c2100c0075401c555402c42512800194a501000001c0c01031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 816640512 1250 816639262 816639277
    0x30f110405011a310617070207090e0a0b010f0906080102041a09010c32030903121b061807080a030f230c0c030f01090f060f020c0609010207110612150402 68
    0x4001c00e502c02c0308113082e00708680540350240d4a90204014503c2c00c00030400b01504c81100603888444c0030440c00180e6400070b00241c4481065075074500c52521880e226a902ba0081050056044420060320402d4400c0000a15404009606062030301c9000700c070351425000d204502c2400080c2c055410780c03180c1d03cac4a400c0b5a03c18003030007601b05c14103e003a00b668100892003102c0031b4543c0c845507021b900003042d80c00301030000b0000c2c00c507000328441c2c402d003d070411400c1d4122404980b000000300700c42804101d03c2243c48840c880790380a428451030b0704d044807690090070150010303000e02000c40e5014031141005d03111410403095490084101d407200d103d07a02201501144040b440303114480340466802000030080b1708030b0711b05505525202d400c80d43c481c04001c2088084600800008079a60441000000d5425005050110410f800d5040103c100d4111324140d40c00140b03102000300d4035030038640c13000c800c1e00c0190902e40e0524981e1100e0303a0190602140d6111080c002c1c91643d12601218450b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 816641762 1250 816640512 816640567
    0x8241012051c0801050618030c040609050f070309050714150307050a0923011d1002100c090b0304060b0f15130b0a020d05070c0807030f110405011a 65
    0x2180c0c0d003802510350b200000701e60140080141c0344007000e8880c41c88241a50740040000385808142e80c100740030b03100d2941186401d409000208051945e69101ea01e0040c00c01e284040342505c3c00341c49106583c1340091003c8107061600c64264089840012084203803050515048000d0020b000015003200c0f024501e4400e0701f000100f00706808d80c0c06405490a403409031101e0717030510b80306c400e040e800703100090002c403a250102c400d00f0140e40c8602500c40944007040021400520580c0200307502406900b180809070f4171035003070034510183c2031141140d4421075180c40c0c2801401c0600b0042a0300c0058009841c56445017241c6150360380d20580d4400b013040007000c040610080c600603601030b4020103080100c4444d003000001c0c080c01303401d044488044240c1d024103540803038090155a40e400440d001e031140c4646120120755401c080103482d001d1801800362594048892400c1901c80c408281602d000e1824440100328200c0c450700d40040c0c84405031605510303050040004610580e101c4042000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 816643012 1250 816641762 816641789
    0x6090403020f1204140f0319060608030d090311010c08040209180d18061b0f08040b0406031b170403050a050903060c07020f030d0c0615150810082410 66
    0x30250301c1ca0f4010000c440d182d06200e40d8140b050410801c005011040f10f0340c064211594030340404070701048804031240318260015510b9101c904546c40c50308a5404c50642a94905044080c15001052049101d0002c0001c2c094900c821400510b07840000e00003c0c007a001d0080414080d00c0340745155010032500c41d044401c1704007007034030040002c034a00d80e4212000c002e0701d0000c02e0040c42800b41205080903020340303180c42d46255841501c802d01c21207094071869000e1001040485c00240100b0050003180c0d00400e48802c460078160102003844158424829000702502c02c18140c5142540c1c00b9401d42070072030715803081c000c3c19202c500c0391208080c3c1c180292403c1001480280001c2d00c40d282c003d841d410001c9183c1c100f4155625808040c1501103078a26103032400003940394115011200c00410b4038403540d5a10900c0d140c4030740c58601ca90011030806010081c201a01c05003c2d402011000011303c0002e40300107000072041c246201e5000440140c5001561071032850003480002e003454420002d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816644262 1250 816643012 816643033
    0xd0605070c0201261f180519020c1c02100603080408281509020612250e0f030c180709090209011d220f0b150306090403020f 55
    0x2030004144401c220301140f6480c040791001074180e00c05100c1034603281a1901d40f5180c0501d284461007170410920600c0008560200d4810409200014158591240400c1604004000d02008200d0120903041c0c40c5c814400c540c40c0c0c620018580301c840c141802c1f500103003a007001d022818050394001e100b1a01d070a0075000001c0040787d00041048422036802d490301d1100340302d00c0070740c140f000b0200d47d035421110700c10100c045001a1015004002d40c0d80e00040c0c0280707642c0c04144541c0000d64507001c44242001001041d000451021013981f01c0142640c510012281c0060030070300c0901129802000348841d0610f0540b03080025001050000380b420300313041c40b05d9450781d41d112001c55011000503080c0a0002e01c0107510300944010000507120710b01024508043d03492061601c8560b240e0081240380005040d4240300035102400106070004121059500c9480b02644c030b0302c0c0d80841c028841d480e1358501e541c0320781040da50001d00881c3d01821303e8a99060891424040000d0649140107154510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 816645512 1250 816644262 816644267
    0x28110d02060a1d0a0303140a0507150e011a01091202060f12042306060907031806060f05090103020a0506070503250b060d050a08030624120c0301080c0f0d060507 71
    0x5403c812021032020042c2100e080c244042854140301c020701154049040600c07400c0300c08041d0049103264034115081403c282c40b990002220700003100401540c510514000035000c1c0500202801b408035041c50f0348182c000000c00200c2e2900c02c85e0122048034000c54119500c45040700c120020300141039883d0b10f640451515120001e44007100c10140e0424280003004040c11043c010302a00c10280641742c0d11903046c0040da00d001000d0300101a5198044003003220804841d000050245038002400c40c10b0600e003d03100c02890700102c0c8110390030700040006a580f1f201d0882a100259036141d1510340a145c55491130248250034810741c503050071542c03000d110701c071103640d00d086c003030003050010303032124010302501120a0b4006042c3c1c3c0c1000b2803000c0401d00f500f0003075070040c1e006000c0b0f5007080c0d042403c070f0741d01402e80d40c119010000000780f10286038031044001031b080710030388070824074551400040503a81c00e4030043c11406400c8a600f00402c0340d4500f401c03400c4054000c803080c09035292a0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 816646762 1250 816645512 816645527
    0x13090804050f180112080d1a090a020c030f0a050c0303040f020a1202030604030e1f0c060b01090506070b0406020d0905030702040e0303102304020c0f28110d02060a 72
    0x80501452098101034030b1440d02d2203140720544088044031200c0e0342040d601c1030380015486404d80b142030301080340c03110300c10444c0705200d01102191084082c0e6a00a410040050f0000e481e0f00350080c014402001c5660340841110400c00104205941d15102c5007419141402031049600a83c00084100001c2c030410b0100000e61500c215401030300581c4504070060480c04180c4042e4169010800150000c0d02429542d801c02c10024004030500700312161040890f08840001c800107160340e11044100042c6010b907103007001c401d0030090405814203011030024018004041e010070000c0740400c0a0200c81d504461000b05885030034400503205003001c1c0d03030f20fa1019508900403403030440b503100c5194002c4150380c0a03460302c0680080542c90f20f810b4540c10b0400d843c07450910880503200309210b540718801400e140b00e569024150250030100c99604210f80f58010b10000c0c1611210344c003209140603400b152041c1e1182c0315019080207130010410741012580d0007500114002100b140651f08503a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 816648012 1250 816646762 816646769
    0x8010810021623030a020d020708010b31050a020702120114060d0c05190317040302090705030c0c0a08031f030206090409050a0b07030c171005040b13090804 69
    0x8585182400040c184124424030344075600c80755003421200c00080d2550098104202042091045200061040f505652202400d003000d68000c2442e40c0403a5010f20000e0300030820300e00208a46014038000c15880d482c2d819060301c2400c8000011500e4464030500500c40c1d103881201000549040c0808100035404a08164030940c3d614020070384a050500407804240701030590241c141c0c480780140014201031420890700541124000b01e21070f26086c40384004c1d4060300c0c3c0c501c3c81c42807440c200965141054140f5043c080010481400942c0721986519006021898030710703525684c0541e000014000c0002d48030007402050004d90500c0384020186009110b011555100d40c0c2080c4c0049070740c0e5400340b000a4000200303004c14200d500d82030740060341a41c0640151100c448095407040346964045900f44003095448422041d01c552181051040c4c4a4041180308107041c5405142c008400a1003003601c1a0344419503070000c1e030ac070301050360820801e000e0240482d0541d8900b0647c0c90b0440d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 816649262 1250 816648012 816648029
    0x8030406090e06010e010f1b08030a0605031b011d0904060f110405011d06070b040503030f3411030c061510080a1107080304030305061503070f0c05070e070801 70
    0x140089616690b803208680201030584810110304401c40040d100400701e148104188a0701e206c00d4a4200e984940001d40c0340e200f4260541d90b0f142c52014001210015002503000b03030310850542c200186119444c0e540e42000742041d51050442e56a150241e500260495400a0010381800100501900140440300d0145001e11034010115252000d034011072281c140083d10681d52404880f5402c03400c2130a10102400c0c80d854005117445541e01d08109542c00c03140c03544004100600c3c82c603001c6c00c50350000070107041e0a41095007810344400c01c2d0880c0d407600781601f0311441a07600c11030107800d82641d0103d46c0000c0d241c42d03110308501135441d0501203a00b000c1103604440d50032200d00d800c441444906049840d418042d880e2000ca02e00145051002903010031030400054011894072030145100314030981d004a40ca240640c207200d8200c990400803600d0b61007d20610101e9904501c14030708041081c50400a01000e90405514014566029003c3c03904400b060013107031039004200c14182c90605 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 816650512 1250 816649262 816649277
    0x3130516180c02012f09061308060a0b060706021605060703020901030e0c0102030708161a270c120307080a031d060705120a020903370515090a060608030406 69
    0x142d06a090720382888544280e0a08800030314402d000358000c142851105000c401d08081450001c1401503000b100452404c03560f036a41048845000c010161340050a418140801c1040d540840c1b414040d04000a1100b03401044034503c61416800070300304a46c000d0219000c5007000580a40258001441980042d041c48040440d080c40010000256041a4000c5107886260b84809800d9041049024107499030030300008003191041c05003030b040c01034003000500c80d4103040d81055105c486212101c01c102c3d00c05c038103540d4140f81c0450810707007011082e03038141e2541a8000401d0305521404000600103100464110b03680c0d9455403100c0d00c1030082108555850a009081c00e41e82c3c1c4044030382c0d0000a03010030050220501c00b40019801c05000a00542801070013400a400c09084801401c0c00b0452030745032207549181c2d60900c41220041c3c0c0800764582002d500c40c0c2c0d88866204c17024039040c1d100800810403041082021061840d08084108501c0c1d889020042d1250302c40e200d02800038104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 816651762 1250 816650512 816650531
    0x106030c0807050906131d0d050417011b08070207170c01110a0c1e030204050a051009020f030f0709030209090a02090604060503060f0a1d2109060313051618 69
    0x82e1315aa002d2a0f0080184038900d40581c41200a0004c04000030041175007501010f211103410010481865901e4950384d1310f0350305210b40c147c1c8519900060315400d03810055101e410004012044404503d146080030f2507582d5043c041c0e18100d456403080030b403100143d000d404005804925075104110907a21005407082d5090345503600e00d0490809480c09619600c20405140d080307000c1d0004110402501030600d5a170b400150440d001115248081078031082081600c1c030301101140003410540d0700442c05c04106219030445d600005010002d119480e60100301034034043e0880700c000b141d005024040925003032440355200c02c2202c6040303019145460100d4903510701030042c80141c4d0005001089075545103d002d01f60030074050a4002c00c0380c1d032a10080c080710714a60404038019800b8008241e80160820010403190198ad6031103c200c00070b1040c000540d803104100c0760007030503590300c25030403020f18100340d030404a900c043c1d500c14070350010002910288100c51140900d910b02c1042066008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 816653012 1250 816651762 816651769
    0x110703052205090f04060b09090f0705190603110c0d02160608040f022e030b0108090a05060c030a0b0d0309030213060b1912110702090a0606050406110f0106030c080705 74
    0x4850188a0b40040c80b80000340f00810101a00c0740c2c07050207003001103050456071008c034040b00020f803601700c01390300007003c0340304142c600f00b101500a00059030840c24015041c610040d00c040180101c508041d00c1d040c001e07402c0840340040c3c50000c0140019114600a26003010303503515005000310f404d01c1d4220700001170380c60048004038800c07034110076101c8082c8032950070804800340b01c2c1c1040c4120441260407441e003c0784111817510028144d140015000c0d2010000750641030000c0c00803c1e10380c414820303080051004114a504421241c04503500c0341c03501620300014081d142e41d000d41040c40702e44000309040d403141c0320f5021a4000c1d01c4061300c06014810f42c200b6142c3d0360150840a160800c40244410040c02101c82201c0d414075280840c840c1043e5590b040d1007400200c095084004034685d4154607208051542140318a04100700251a124019005000d10321406089c80000111051520024091000480c094034020003006407207151800c081c6090b03010350b0300c0c00c3c4a03004001c00c0909 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 816654262 1250 816653012 816653077
    0x3020312120f090a030f0201150807140904080702090c12040302010231050613050d050703021005130e0612030c01091101020a050601030f050307021804063b0111070305 74
    0x2920f200034100002c03150f1026a031180100d03000204565a035000c03900d10b100d440603800003601250015007001d41c94048030340140400460312034481d041100c02d10000652030340c101e40c80154165a01145560340e5003e1130400d000380c0140325003144904042208055041d03004001440d4052104075031a00038103a03c1d810480c0084203190040c0c00741d84144100d18249001d071044000070b00c0c91240c01502ca00109012216200c41140e0961004405100b10f00d030010307201c3d10486403031402c0342c108007100d072503408105c900c2c0c815030142c54001c2c0081861500d445000da034111a80ba411240e03204002d4100d903008142030a42500d441289100c000342561000c2012443c9941000c0213105a9003181c907000142e071074400c0112000d100800002c001629450490082d4034001489000b0620305801e1940585100300c1003500355246017885003440349a240c0c911003c880104806010f0381280c041d0340c070700408003e490480c0c200c101090a404255100300103010f0200141000c90982c085d81c0c1d44494500e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 816655512 1250 816654262 816654271
    0x1170717130c120b0703051b0c01020c0d0e060d0207020103090c030b10080318212a0f0904081617040503070902190c0317011d0609010303050f0a0903020312120f 71
    0x26131401041c0002e1080e080305401c4566070499014090350103210b82155404202880d03101c3e500420b0346294081c0c02d2000614101c2a030030f1001e000c585c0a8000b410f0340c4505208842c25640c00704805081d6442a8008400c140d40304091498044d282c0c1001001000d0490f00101c0b641c1000b02c01194000303002c410f43ea200161000540c2c003004043e002c10100c40d504010007910403034414451440d540c41001003200381d04900315200c00101b600b08055140740486d06600340124506107603d545072302da241540707a00c02c0d0400c4e1000d40f00d84d50203103e18a100107044028100f09400076489001507010002013085030800c50031a003006940e0b0000ca0300307a0003055203c000079145501e00301000da00540c069a0406d101340b41078101011840c172180f80d038800070303084082c0400c00c264481508580900c51039801031800c50781c4203959803455900802910400700d09000040300442c2a80090323019500e00c0001c1c580c01025210207d144d030840000701e400c840c00a0075805545008140c0c5803008044407400b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 816656762 1250 816655512 816655523
    0xf20030a1806020304150911040b030f1605151303021018030305090f0f1c0309030507061805060c0a03110a02041e05180327060c0c010306090b01170717130c12 70
    0x2441444410800280001440a502f50188000d00340b03460b08280810350000490f4a80c100080c2d0a1200b4041c07400301c4010000d001e40401c001c1801e00f010140910300460394111000603074154001e10481e0711811055a400003518110408000c040d00034000d849072500549802206c06840402c011140c01d4040b03080c0d4202469407000144100540720100c1014000d0404040450752903075000d2a04013603500000011f044c0e003d5042240c40030078810001010116000c1c0d05042919084940381c0c8035100c0000c0c148040c1e110342900341c00042c0b12303240040350000e004215150f014881040c0043c01c101800320028507140004001802d809000f45e40c16100d50011820151030b00c00300c42c82c0d400c40036040d280118035002140c00c2951101c0051150303a000a0140240707864080000d4155840d9030000c1c055039017040c408862a9920840301e03c0c1c442c5030304050309059107503020192002a1381480742d1002120304810085d04858001c400c1c9507851060303d501c44050394403943c0e15009060114024034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 816658012 1250 816656762 816656783
    0x6030c1c060902040b060301030506010e0c0a050316090b16060f09030f031a121038040605062107091512060b030108010f0f20030a18060203041509 65
    0x4600654003101c42d651020f840000c840441000007511034009078400c443c0c0740c0c00780005002c051004c555803030700010f00324055410b00f0380c109005002070000600d5804007074119a00e50352904c5c481d84003d802032409800071580c52042e1250b40d0209080c1100075610503060851842c04000c1c284034000900f500b42d07a9145408800e5201100980400c04910102e81d50f00000d220309940c550180c00a02d407a040020403d44c46c541740688182d075102e25072644008078594402039510b06240310a24600700c005000110f03203038004001401404503421090308044041401084028070718101c44c01c1c00e90120500a00355540c490850315244203015105060011281c4038000d58000c1c0c03562075010208030000b24a05403188446c0c1e01e250000d900101e603589d1102c0c561184110144243c17013841229440501002407030100d01d090800242d41c45902d01500040011720300140d0b5408002103039440f0200680c080041d003800c101a4009035429140390401035071222001c0d507a0311030500f031281c0c000031104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 816659262 1250 816658012 816658069
    0x20c03040f081507180e0c0a020d08060a060e040915060810090503040306020903031b010c0f0207030803060d03020f030403030f11010c08360d02210d0203070903021806030c 76
    0x2503130b0000d00020354564545805e000300340030480c207000da4440c018800169880c2c0c10003100c000c0c03a0164202c149014890f4420a0003055142c00a84030255604e0b4101750f00052444000b02d4010940b5071f02c0905504041c0c01c042c10302c201560004011144241c0880f0345110309101240200e400c1d074134000703201d64400c00081000501c10b4028001901009090340e040039100188102000328044010140365526040c100301540c008084034003400c1b00f0710040810b00c0c00c6a03140e841500c0080e020320b100710584503001003058420401d098460340e00b64166502c1d0341da01d140203440c804000d613071240480e40b8022010303010340c5e0510442c4803c0d4601e9648518a803200c412070000c2229110300039004034010600c0d042a038548410300c0c60323414801d00080c21804a807400007414005030408015024405035084056601088140c9000409600005a0341e40390318406aa5440230f80d03000035080700c028148440700c024a2050103201d00703010f0f01030310211441403003044040000c0941c1803805013540c0d401c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 816660512 1250 816659262 816659267
    0xd0503101e03060207030f031b1d0307050a0312021b03060a11250b06041b0e01030617010213081f020f2218110d090c0306020c03040f081507 62
    0xc610000c038540800740340e22a240d1406980c00301a0030f5020036100d409000745039a1500c29040103400400b444403107150401e5009141c2c100300126141c90b41c807c400d900d4007941c0e080c006940100300041101030869640c0c50040b810499440311240907004081400c20108a030023448145210020046c08565441c08100c1d8001d160085c0300004a540504c84425054880740a803c4403802c001241e007805001c5191280f8116001842e0314042c0b8105041c0c2c00384201d07a40c0e0307503151492150529003001001c02004070001c0c91f455110007081c00050020107903018065005055000c205070308115903070b890745040d030740d5805000c1040f101c42c41081c2a4440081300c0382d010f00341c9040848155860003c54215070000002004110004101d1100c1304006aa0311007140c08200c044181c03041c028031032880c060700e0755409a100100100d9480728103500c204486011184040d552001c0115110724490a2550740c0e41c02c680115040050700120114150304002141d941030350344543c05665039620200c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 816661762 1250 816660512 816660539
    0x20310093902010e060702030d1a010c08030a0e010204230a050a09021804020307030212090c090115031404060e0d0509100f020a080a05120a0e100e030f0301080f0d050310 75
    0x10700119540c440a0303400c0c02d181840036070301610b01a4002c46d12614031100c840d0461700e44480d8507445440c0101e4040072030341c0040801a21640050219449585402c800c601510920054801c5540f00041c041041c8821413819007410105502d030400040c0c0d07070002c0c0b2095044500556502041c501010440510541c00511030711801c0c0078000c41da00020350109050780c20984400c0f010035008039502c03a2003075008856035030141404c4000c07c0301c65181000708014131018083d0304480c411040c40c2003d80b5000340c120711254024541c90440500d0306090550040c00862415040c3d406a1f5000d0390b245880741c01a90703603c00005001d40c5030200b200d04180c0380710fa81e01403044154001caa01c0031001c203000c0000b520300d8040e541c45140c1c1e602240d011030b40d0501e000510700c803801842e00100c000c40c0d0000045031517203401500000030b8159944200b1514601030203c420580181c000004901c2e810041754021b854001c4000711041d543c100c01c000d880b2400200c0e203c45400e07030f035500c0400c49011080030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 816663012 1250 816661762 816661871
    0xa0e040203060a030b09250e060609040230010501020c03100b0f0306070503040605060409030c0609061514030105071412060a031a24060f0304021302031009 69
    0x20052809642c0c0c0d841071007100088401b41c890f80c00801e809416084c1d00000200f00103e00316020b01624204600d4044031700c4080c00880c029400440d102459858a0381180c1458403240c0c1101d140790400780c000c1c40c1280d018001800081d0a0030000140c3e94000100c0254201c1c006016008a041c54144200101032240690b82e00c8490005507180c651401d20240d03004422070342d1001c0d500e2a003820200141d4502400d514080c0346800e5004003c668000b078001e0501d41e04c044085103405050912a001c2c183e407417541a40c16050540000d49041c1c01c860450607c203054000380030954418105850a10f10840b00c260b44407801c1014146903140b16400c198441402468641c4064482d180c3c1c84515800d110a4403d004800082c803100b4190007104403038807074520072202d03266024440480d596016003000045941c10100c0854115902c05001e2a85400145800c42d124a070900d901481078485100f056400c07464a102140751402c05007045507902600c092640703114543e40b000c1100c880040301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 816664262 1250 816663012 816663019
    0x1315020a0e27041127150a030f1407060504090e03042106020d050c0406021b10030c030e030c0d120b0a0e0a180b090f03040e0601050a0c050a06020703140a0e04020306 73
    0x200b402455030302e540d0114517000041c00b6090700c1c0104040341182c0703041e000e01003515a40c0c0000c1041525500e010014080d40c0c1e00440c0c542e40c952183c540443d03004140b404500a80c080d8420128009500c000500700310b903e05ced001884000070a400341074036441070f40036401c0d40110b0034400c8e101183d421450801c07030620820f030052400901599100c110340055840000074040000c042029942c10803c0035000408a004403980c0c503180c0b00007940f11200b050180091607103881861000070300903842135503040e460005032662600c500c142140c941d12914184000310318101e03010100c0a80510412840c40c070094071000305103050503003511000900030604a01c0903240c1d40c0070f0a984e0401600701070180d00c41c541da0786050400340030780703800c0c440c20b002c12003029802404200254483c2e0607615800003030030308000d03942d105003a404441e14502c44501804a2145940100030800030380d0007001400d002b07946540c01a4902c000610701d921640301b00000007000048011805e00e802d80c0110b41246005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 816665512 1250 816664262 816664283
    0xe01050a0b09190e01031109091509010b090c1902060106050d0f061706040c080f030d0b010c1a0106030609060305150c0d1104031208060a0e1315020a0e2704 69
    0x841d1a0f00004250707800c200c1c1406141c0c00100f081000ca01d11400c500070003128200483e140c00000c05641d5001c00c245001c885120001080030502c081d4401e14011078050004c06480c9010740c0c2d503a0881e489907203400220701d03460003030382000d610100700141070b610640d40740345ca400342442544010f01240d500000e0380c5561490001030001c240c6c01021041a0544003508083ca040c0c02e001e004103a903684207a106e608494428554108003104031282e491541c42c0010b4266a4880100c1c2d42421f4940010aa05031032828129010780e42c0000714100e41c0950340c240b01c41034a500c844000c0d902d40c1d10000b8031540c00000707103030801c40740603d610358056101d004441c20107240d070039804155074444140079a45180080c062050041c400e0549a0380c50417410001071b03a05080011840c0c4051501c220071505646034041020b4551565824520304d800500e0700340300c0c154200c4520008d50000c8150008550380701c82a05460801001102e50f0200d1388172800d10342d0020440890306860f004008480b80d4525 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 816666762 1250 816665512 816665539
    0x2030703050f13080a050d02030310030209090a0f03095307060302070308180a03080408120a0624120903050909011d010905280b100203130e01050a0b09 67
    0x9400041503013200501022156042c182d080600349228482190401c204120025580c4542c140840ba81610b9900680e5a86041f1030f0914070303100c40041000611100e54030a140e8440401003d4948444080254070301e03400d010583e160034680c40108841d0080b1400000700789901040ea0800d40c4001c14440f100000c8103514240a1a5003008c00442c4c3e01080100505520448a130360001021036100e40c14014108442c0e911b1150f21070003000c02004800040030414050181e03a40c80840310f0003c001070912004020141000340520003418203c80f00d0055488c040e054074412110301c4e900c98481410a810304880a091403400c1902408010018100d00382c4030040c1d000e000f014a00050301807401d04260465495034180d12004900c3d0078141402080501c101881151200042400038450b00d18080da20103080c2e5181400e9010081c0407100c000d0300e402000414400182c44080b40c6001e03210b41c10f43c0c0c5141001e001e11074001684440034024005468000c00317200d040204002c4c0341901 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 816668012 1250 816666762 816666787
    0x1020313060518061f08010e0307060902010215011d06090f07030b0d0206130609150905010e01030f0504210c0b01180e07170c0a0303120504140d08060f04090302030703050f 76
    0xc2c181c810705c40e0000308040304420780184995500c098078001c0c0003442180c00100c2d20654070f00411801138545665030080a003160300030803c40c11401742c0282c90620700c0da91100311402418145d130401d221000958002852450407900c0648100031a0b182c21650343c444080480c001c04072130759656001500c00c00c03d54007583e0307030710701401c4400c00c1900d4003a0100d0804400a0995825034412182000d07504030500240343c0001c1c4000940d8820300c1c3c603000120304034004134064256480103080c20741c40c00040c030052101354140700740c10420707603c10b0301441c41004400300c0c0e00e8082e0388000303801d6800030300052000491804404000c0b5038807050100c0d203444011100b80c10222203911003507003410041c1c00c07003c020340b00380300c0030004100444031659002c1c556100030301440071800b4250030481d640c40000341000340f030040032000520f030f80c022a103150016440c0903265580c10748410b4810108504008840e281a0190300d045a0f8564007850070129a95002c0d50190003941c0c5030007110005020100c1a0714 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 816669262 1250 816668012 816668023
    0x70905060c0a050d0906080a020901030b04060801090201090b0f0406110c1f0e0108011d040c09020f0403062919031704180c08190e03131701020313060518 68
    0x501d45405040b02c4241403400d02d2a00084a048400b4803207103241c100f00c0030313400801040d40000721280140c0da0b001d03104c2c012402084005021035100d850410b0214402ca0150b100c0700040c2c0c400e8a8482071907484100c0c80c180c80c080c54401d01d5120a040006102d0180318084600e480c042400403191070040b0800006c60080000a0400d00d001040c60526181540f004001b42d00d200203003401da0300b550404000102003008942d02c02c00304c6401d840420100420402c1d0382c4001d110300c2404645800d1400c14070038aa5202348015a8190702f00000c607481040c1074112841ca050ba90103004c6005105a0280000c0350428400c104440d0201000040440c100c000c2d0340c82e6015182c032000d9541c0741400400420406010720188400d0700c0c0c1080350600c81e800005030350300424121400440140d40b03404400281c5114220b50f8420301000c20060030019801c1c101c0b005460568407050040390090400b10300300d01080302c4840400c080b51a06c0c0012400e1940204d4001c0c80c1d0400d40c00c0aa204605001e2900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 816670512 1250 816669262 816669277
    0x30908070c140109060c03020613030507150c020c0402091e0d0c080606100f0206070e0604181a01080c030c1305030d1101061a090622240305010509040b07090506 71
    0x2034140180348002d942e80509884043c01c11410600160f041e5510029035526004051180810458440c00f091500400644105981c0311511b00a0060b0909110002d131002c03917034250142c0301c1c9a015440c40c5c5040c1c002d40b000c0b44000b07048042c01d84483e030000c0c2080071500030b0301a00090040c0c0070401003501c498603030700a0555400149442e0824500b481054000801e5250420800030f846035012940480c0340780d00409a85001c011441842e4000340291199501c0104540301810480e03000c950242c000c100004003030090b020b54104110b0044da11203030100e5046004c4801040014410950080600740f2240ea6010012500c1d03110303c0482c0c607091030140700f01301141ca010703070301d406241003405841c01801c9101010750100307036600300f002114001d450030309200d1813021800003580440400d0b40c0101e044110301c41c1d182035a0f0380c024100064811086050500007152031684503a010f03020b807a040b100301906500e0a40d139140c50384280401e01520040801c8100203000560703079100781c040c0184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 816671762 1250 816670512 816670529
    0x30d11161a07032f1b07050a0602070b030a0c0201060e190516051e21180102030c0a0507060f021b0601140108070507140303010b21041101030908070c 66
    0x201d0100071040352104000b8200b0003014146280c20142000c0189540010b44001c44628510080744854600c14000c05404408460210060003400840010340728200d48040d10880402504da0750308a807100c4540c05030701020242040402c116580d45d911000c00c48100d8400002e601d0340380c00800c10307080c2003903441440c1c41a24a000d00c829120328030540c1e41102040c030500e003c06da81590040d016008050141001070154104400d80081700400c0319040030b8802c2e02c02318030440d040015664400103440803201401c0d4183d1035001000140700300d0f0300660406000d0390804030041011206035101800840e042c4e525164114085801c038000340c4105101700110390b8102c0441801545011310503841781032001c11030765a0000903600241e55a8000e00c1030710340103548400c2428a0b05001070800500440c0380b100000002c0e42c0c00d40c0501134190341c24482441c0c011000c0d81e107400c8425810584015200b0043c0da42551240c0d8040e81c491f204892144060360b090000c0c0f6100d0801e9120704c0c0d80210308 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 816673012 1250 816671762 816671783
    0x10303110d1701150e040207080a020607080601080118291003060e1b040f03050c01080601020114062209080a0906090f030f140102030a0603031e02030d1116 69
    0x240d101403008189040c098906034804081c4030b0b4402d1140c03201803107400e0700442ca034990186414460b0100c1d160380c440241c0309540d01c00161618103101e078401424140140a040040740d800d520480ca41c5004401c160340744441642803a40c0c0358244c1c0c1604840b4002699141100706907848000388079a400e0051070040c810034940c00080c0120102d0841e0300a080610b032590501c019074140700d8050700040340364030440c4e200180c107200c03075240c0c4a550451809041c071b5184c00020010005000800c0850070390f1008007a8640b0070059080c0c89030310410034815500c0e00c0000d00d440c180300e00d0a0366250741008203554000301c0d001d0010100c0b030300e004055803950800560064101c1c0c21400c041c00820b150b00c1d02c0740c40f0320324044061400745494040102104400800501802094a011140c040c4810000c5580b4100491030300024420b52008802080b801031008a00d05550713421701400300e030540c000e58034100070007180381c00909220000801c48001404104841c0000d00d511181c0c1e54460500c061 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 816674262 1250 816673012 816673037
    0x81602130b09060d1e050717030403060b090103030f030c020c15070b0702070e2404020417011104080c0603130803040b010303020c090705041422060306050c09091602030909010303 79
    0xd850b000600141c0a40d1840301200000350104690b0900540c0340e0104c001090003500e00345007880941e90144050f250864181c214007035001c070081048900c950300c01c001203903185080c0f0589040912016000c1039180510070002c0d4002c1d0004000e818452040d42d030303082000c0c0d0005180601180799400300c038101044c0300041100718801a604258940001c0c0540f0b86001942d21a03140000d0540c184001e80c84e8052444184001e00403071a548002d0040d900ea544506542000300490f900b01e44440d03080c041a1182481081c04403000d5451810180c408040782e04140403a41d4000340100815003410a10701011807078030703c080c601413440343c00d200195501d581802440d15503c180c4580c801ca010310f040c8810a90480304031011515004000c0c561880401c00140e40108203010b00c65101080495095070241d141c0c2c820403c0e28884c20081013991070b0b10b50351120a00840741903580003054000451b01c0703551a05910688504184102c2e8a00f442020110700e1210f4282d00885c0411000d24841 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 816675512 1250 816674262 816674269
    0x90a030206090102070f0f0c03150902100311030c07020f040e01150f0b0d05070e0a06090f09180204020702131e0501050603060a030b0a1d0c090121081602130b 70
    0x2e4000040c807000354240b0086448114050b103241c1401411840c0c4042003a04108441c0a490011074000300c0d10710b8880180c4520700050208850103d214121099155040d180244209416402d40080c414255550f035030721000b040d0310203402607030306c000001c00300340c1c0c2030390b990045040c60540e150001c900719240e03d030503100221203031308102e0480100050900c0010003080c291a103001054901150a07160b55030282ca0210a81035401c1e0844000800030540c81d0700082204103c03507546100844d4540e8854000302181c8000c184800c1e098030f0060301d0405881c054010f40300b003d000a00b800b0040101125600c100d0700119211034029003002e01d41c0c0e108245a10945005280c1a150356246140c201d000805d200d000d8000181442c2001b0086000c400350b541c0a0302140c24848075000c11460400040c4bd5162801c2003500d1080006030000724101071582c41c41a040341c2c0c9864026201003003035440440d140c0042c00c5100c030211001c1640405a6545285440711910455000803903a4492090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 816676762 1250 816675512 816675523
    0xc070b060a1a03060406170c030d0e030309100926070b07020d0b0a111b0d050a090905071b0b04020102070b090d110a0b040e221101050a0306030803090a0302 69
    0x4152041410820420004841d19480400101c2da0b6600326030f203590744400140100100c1d0031140720701039103c500710301d656800607411003184000ca086030201c14078034504079800d00e0500990364140d0007d000141c000c2c2403070701c0e03101c10010040c140a1801038491a06d00c8400f803a00007a1035254040050b9582c8844060000c180a016225200c516010141d004105147e5840d040104910400ca0002d408801654480d1120350300b81c8500030398039044604110a1103041c9010004c0c0c03801200c6a80300414065400c4030175241103501c0340d5092518100095000f40801003205041c4100703188600d2016045405041440c1e1040341c1c07241c1d4904050000901d804155040410000010040c10540395190340d4400c004542c840f010048a2141e17101040c070840c0c0036071066110500104000c1220200c0754201e500c210204044204000c42010300c1140043c07081d0b00161030203a101120400c41d51240008040400050402040c00c0d503072a5155000c6610445583c038413034000080038010554103002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 816678012 1250 816676762 816676771
    0x1d040c1202011b05010b120a020118031a0c0c07060903050c010c03050f0a170a0c0f09030210031a180a0606050711011b0b09010b0a0806090706031d03030c070b 70
    0x368584000c0095002801c01c440e008680d00c043d6000240d000304202c2c0942012003034401c09054001203108000c841541c0b07440e5443c0032400704655000c940100401c1e241c0410880760403840f10054050040401545040054000c000044080094065800c0704001000040c43d5540c0c2c2d140c0172610354106541440320304002c09040054104244011940c01000d50300660310000c1071654a629409054a001c0c801c1c10800c15000d450f042040072217900d40d404080001d1060300c1703481e0b10313080e030100841d90100280802540080c4c00805004c413a44240d2200340904031748110220814090070014008803120f00a44100802100030048070b540c00d03018803401841107040c61810715506603581b502b6a64109011410054245090107110b83e101c0b003000380070b640000c0302d006c031810860921390182450000380c81c0185610600042d082030001034103803240103140050680710781018011000340c0600500c20383e000e0f00503812005c3c00c130030600065004201c0d03105259501c00c1c0302d14060508140052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 816679262 1250 816678012 816678029
    0x3030d0e060402040501090b0307090b030f070b03100e0c0d0b04090206131e0b0d0f02070212010e010c0e0d0f020f03150105151912021204080a02060c160f06061d040c 73
    0x2688c40605480028018080d640d010343d01080341822100441d18001010203d849244610207000892851a800442c05000d21220100000d9147c920400c006582510518440c0008100500c510982d0f0f0380100019a070003040400d03840c840390009640794005040c20440422600700c10050000d1100c6c900e08a01284d1000280c160f01c3d041a1000501825203812030f9162240e4081c882c01c0015411103440d00d60040040c0403a20100540d04c0c006c0070742c503145d048a98600598004894010811030320b400800030188030384130aa0b5583c900170010540790480e0051100314000685035420711008580f26140036058502c1d626010801c003214110381980e4403050390030440c40d03210480c1c0c0704041c48030385014101031219050900c000b030f0092003000425880d08111806001c10480c803507005160440715503085905503191241442c22521882c0c600c481d219070110208070008401e40028000e40d0b01070440000d2142d52000341c0d045001c203030071240c940b22030700c0030070402000020360b5a4405440110b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 816680512 1250 816679262 816679271
    0x1404200c071a161707030909051321140a0f170412051303020a06170f10121704060903021c05030904090f060c0f090b030408160203030d0e06040204050109 68
    0x1064a0b8144a120098001c074032044010707500b40091034205009460034905220f0b5030b4665820001e00b002024082e000c0785a092a0200e01c2d05000011407040c11a0070100e8051481e10403103c4440958a0f0321301c030014409c0e03440d0070f0092040b4040207000481c40303588940e41c10114130900204851000341041801d10945410301020610341e04c0350300e000403811304201d581d42c6c1e8001000314000b681903000035803060641001080969108034401c44441c0b003201d6410381e94403910380440601130200e070011003841c03220804121103035102000c2c5201c1e5015025010384a040000c14003c00e03030081c0c1020010420503d810811803c05108401c2c1d651405100c000096a03582d5030b294907441004034051080340c8556840d810302030344514101c0303000c1d404030003046040e403a5540584120009481c05003c11103500000580122600880348a20303403000c0c40c186001c0d0030786901c1ca02840700c0b031403d03078040c4028403203071600150070300c01c841000000c50020305441ca07192041105880050b0807620015003003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 816681762 1250 816680512 816680549
    0x1209050a121d0a1d041e0317061e09070318060b0126062e03050906010522111314190509040209091c0309020a06050f041404200c07 58
    0x242203042c1c00c015150400e10204e504c5070b084ca82c0040d650860350408403160318507414200350304249000c40c010b24000178840c0c0b55a5500c208070084001c20010441c16403504d000c81c2c2140f80207a50203501c01d019060020311041866084035079800c0b5044119003a40c1e440c0207050789581c105e0002c01c21185202504010a005c1080039040c03440c0c060200d42c041c041002d0419403d00948c8500c00f4001c10036a01d120b01c1c0700341510000c0140005880701000c0d8001c0400102c1e5604110001d0156840c0381d8400701568002e81a125000f492500001c0c00c00c2082400381a1450b04910100c20048c000c1d42c10f200c024030401c4082201090b14180114030a03840300d40d04106645400e18000d81c000d0301101c503840d140d503c9041090420146043c40c02c8141c06e154201e000d2244c26601042c900c0c1d00076189a1034198494100b07076200d00c18610480380c501e2003071004110070b0302504020400079801030004125034194103250543d1304120b540c0f0f40f10b1580b0108000380340d04020015840208110707800321580d0041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 816683012 1250 816681762 816681779
    0x9071703090a15050d021606020304051b010e0d1b08010c1706271302042d062103050f07030518090c04090903031d060711010c1209050a121d0a 63
    0x20f0b00d5885e61000d50003181583d600c00329141010010f540080c0195504d1601d0301d8240c1c0c85441048c031510181d440c22011000b1544600a1034000c180081c5c4603181091013515416158901041c0048030000400c80100703a001d001e000d048007014a9407611a03c100e0a402000202c01000b003400b401000414045440300004144034440c5034414240403c00340c0f02d4655078401d0f02444d01b000394000d420a40600d114507a4034807480403890603070401e404d019404440314010b0318014803034141481040204070840300324007a1420032961182c00c0091400c8114402046c0c01d400c14a402d8010a00104200c0342d00b29000c2030611a4801c100ca80300818500b85528a015014a000381d034111075803810705100f090301a5002d580c5070003402c0c1940a1258402e10040d988075030403122000000ca212070103285090f0305000f10860398005840780c03810312074842e402d10024441d50005545912800d007451011820a64402040c220150784e50702c0d0042112680745c00030403604140d40e02400c07442000f00900d52 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 816684262 1250 816683012 816683017
    0x60d170a230723012a021009053406030b0f060c0703060f06051e01030c020a1a100b0d05040c080304290702090c0c010c090b1209071703090a1505 64
    0x186018100150f010303003200c2c0c0142880c0c1c00d4003c00c0810104071101c0c0a000b0a02e84015850a0342106c541022800d4204165140c84000510a5000318107c0302c2004903401c0e004107440044031212880e210f400c0d150141d03034004d0b5001a001c01e681d03280d0740246080a4045e69048c0e0400e0358280d240c00364a5682c507945410741e00c00034149541d00c0c0340c2040040040c0d084540100001445540c0d000c02500e2504041410300c032210380420b280c1060201d03140d0012805501c00c40d00301070080c0d40d02041da0f202d0140040028840d080c0b040c8400780210340c002c1d180b409001035020000f40001d031460302e864283c0d98081c240d0404120755200f40020407041c1000104104c4050003183c040750412518071002c4054010803170000d41c030802010801c01044c8000d00502381c1d0b11821402440f805018900659411281d4014500c0a22040041a1081d0180044250484400001c07509010742c2c3c0c141400240c4007040040c081901300154203101444d210120700064001c0c06941c45503034411800150903803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 816685512 1250 816684262 816684293
    0x30a030c030b04021305031905070e06062a070501050c0c06070212011103150a05060703180305011805060a02030c0919030c12120305060306060d170a2307 68
    0x1500c8031200c000661080e00481084400070b0402c0d5100c40029420554000c0345001d820b001e0b11442c1202c6502994080020981c95049006000c0041c105140b14260340401030225400900400c2036400d21a03083c0c001080a42d0754088002510180b5070311341c4e00b4041c0070341c4924100901405244940362002c10150343e50241210040ea5840302c0e44041000c84104c1544094194a012410000d403035603000203611600c0c0f0040d03041407981f85a400c000c9807002c240130b0079030815414003d1070b001034020324220002c0c2e90519480182c055490366410f080d29041250f00c035900d8000d080d41010401c003004a10b1308201809029410341c64104c454642501400c56100d00c01d5885080e08101d51204600b0000516000040142190740701c420b0f200c00441c44400c200e40da03001c1c11031451402c0741b203482078a008441c01400b0b0000b6861b51400c0102180b51000c0036070350b80100082a00008010900800070002c00b07450b44c2441100d085148809035040f420490440c0c0b0042000342d00051247e1100c0040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 816686762 1250 816685512 816685517
    0xf0f020304090e19080a090906210206070204050124030204122603070c121b06110f030a09120c0b060409061404050106170d14030408191106070c0203030a 68
    0x24140303c0c1c1034030391412244d2030362141d0034060948400244416a0010501d9034000c0e1290041c1c29503a028103421171300988201c140ca0030030884200c81104440c601003120b01c1c0020846414800c150300042d0032104c00707a01c4990300000d0710791400130008284c81d84c44481c205c14241141070070318010031034030700b21108200142081c2000c0c48184030345052020345011610401c05051b201c0c41c0c51030002e0620340151805688612644d0180341c40c2603c1142130b8131140844030329064980c1000d580c0d5034007030003003444400307154081442144040201d42e40510b11503011042c020174111041d0502020910303048004d51b04001da00c3e801d0202151b10340900940000c016640001c20707070498104440105400b0008204050485c1b051105202d0305401040550b080c060004e9003141864442598a09213400000007040342002c03204081141030000c0d40c0d01070301075801c16207051515a8400f0003100410b041d50003050041021401c0301004001080e44002a41000d140141c41c41d0006541ca005800400c000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 816688012 1250 816686762 816686771
    0x20d03091a0618040b090723011103040902072301110421020d080706060902040609050f030a0b0c030f010914130201020114010603020c010e01050606192c010f0f02030409 75
    0x201a1200c03c0a1004080e060400c15118100303464103079110300e42501d040102c0e1080c0d0401003031520011039440c0c450a903004515400d40072840040d149840701064281c4607020074080029030356414002011858030038025010641d00011a00d51010320045200403103a2521420702c1907100160200c80944a105040a0980c0c800079850b0f104a09140c1c0c1c000d40042000e0111800c10141030081e0004c0b034420740d82032080649400d015012130040f40f00e210f0018007021010016420140c040ca2030002d005000da8100b041c460321045040344050340c1040003103d0020410002c05100120a07015004000c030900c80b241c1c080c0512060002d0260041300c2e0505641c0000c1c003103a001754411142242241902c162560395200c000e0001c0d0020821325005500782541c4000d905410320400d40b0500300100701c0307030a001482040d42103c1c528110286d00384100f0403011071071308540c0756240300408200030003100c90301d24440005005111283c00b01c0d0600c5100402103074902d8000c0b06072002d6031115200000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 816689262 1250 816688012 816688021
    0x70c06020f120103030807020c0102060115021507050405150f0901030f0e011103310305030c0c1605040e1603080a02030d020f12011d0f060f18010501020d03091a 71
    0x200030311600300003006000e00064810b1002030448000750480303021341c41d440348a60300d499003661100300c00f200c2c1c60b00580202006001002c09074902503800482c82c0b0496490f00c0c3c11584c4003103a000203688443c04103e0105081000b441d00344501a1701c1142018564185186070308055250301074451030a0505488007032280d0340780100e62003108c02d0f88010000788840d921112541d0000e9109680d0013100301c000103070252070000714000740010f14584068281885015880450b103c7c0c03c00b50414484040402038111301d076504001200f029503020006061303c0d407400c0304010840d0301018849040d90001407040054002d03246c542011030740c100d0380040d036500c0c02e800120b055200e1301480ea02440d1002c92508140301440b400340c01c04100781c030140035581e600c0d00c9814080250310742032220082d046500081d98070520b48a800d4010f8000f4180350f00c050f04031000600c8024000418007001c504090041200b9070341000032803000ea501c0d040401016505454403e1142c45806e040c2d0102c210314030114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 816690512 1250 816689262 816689273
    0x5090705070210031e11030109020703030605150309011a0618010918090c0504060315020a0309022d1c0f0f0206070b09070503160e13050105070909050903040b03070c 73
    0xc0d51070a03402411840b031070a403020050000c0c808445c998106002100d040d40c2004c60622940c68480d4404c000301d81142c1c601242c0c040030f5405103030b08904040d00c0710700005160f116401c8041449803c5903d0b65100d140246441d821100b00402c3e55200702003803050854552284811a00400200883e0740d1a5000d000010381d02202d0f0b55000c034640110000d85000740d4141640503c0c54507100342110034445a903401008282c405070b00001d003940900c43d542c41701070072442d0300600600c4c502d800d010903a50180e80025244491511941e010b5407840c0e10f00304207540210b4000c1c1600c00040764410007a51981c011503a030180011002401034403400f286d00144030000d1480d206580c0d008100300d030b43e40c8051400f410b41d80c0e029500600144203442021400c1e02e00030075403880300a501400c43d140d0514144680c01800c00161107e00c0c8904060004404140c00f130064034800c41540e1240740380241341c0030320201103a5004084510640080c00107100704408072041301d410001c5442c0c4008140c540d030811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 816691762 1250 816690512 816690517
    0xe0307080706020304030204110c07180f02070809040509070f1a0f04030f1209140f0607120305310303150b0d060501081e04021e06070f11011805090705 67
    0x400180705410000070b0903680000200140c034400c3d01c0512468281d8011401c280c013070b400c2010340c1c68011550601a6101140c000348480b0501c200100e460350b0618001c5007242c0c06003a090f905403c1c0000d450700b803814180035070360b00404402c00070f000c040d151000c11640720007103001c0c01c104400c0003030924150045e21801e072800713107071500040707550f556403860040713004140910111250503840e0040c04020380101701c400221a04202c000c030f2040c050604004944d401f801000c1c1d0310030014071081c6c011903050181610260016100000e850804d80244030b103034001500354071412082030f00c0c116520314030109040441d40c0e00d0308010490320500c001009140700e65400a1202410102d004011400309400c4001141d0082e00e0780b03001516031110345124400e5450740c074000020700e540800c005040140d17085410764603d4501603003070b05130080010b6250f404040c0940b8480206c203000d40600c440494402a1000d09080807101170904e00d07202712400140b4491188100c6039600010700d1907000f03004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 816693012 1250 816691762 816691769
    0x180405010b0a03060e0903070f020a030506070309051218040b04090b0c070b0a0b1f030b04020c03030604050105030a02101b0f060525090308180301060305030a020c1f0e0307 76
    0x10501040d80c4071200101c154000ba0440d000080c203090700000d12880001c0c1060052100b01c01031440d1890b16120400d1803004108101e8115440c1100003010601c141b2a6900030314595401096948903802e049281c150b4540f2100b14000d004c00c14a02c5034211400555a581d00030f96011030240c903102c000030b00138a003041001e08458105070821000b0004a800ac1c03000b40d20400b400303001c80d01c540300c00d00700b110740001580d03410618003005043c0310ba000140701d0200c00d80d64540414004001c00c081004c0e0303040300000066640c8088144909031903e801642d0141805800810001c5015000100c00380b820903010400e105001010400c07000102e80b1076808070307801100745c02402001e40b810400170441106d00110312840242207000c100003080b0006e1164100d40e940d261014250788481806038000c52a10b0740070400d050b200c0c011ba46003230081c1d0005500440140d61a516036410203401c004035081c40130b20508002180440704100a2040c07050511280703403400d203000e40340d008070380f8058080d007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 816694262 1250 816693012 816693019
    0x120909130f03020313140a09090606050a080f211606060b070c080f0601030b07050a02160f30080d021b01200705030412020328060b0303070b010b18 65
    0x360380c1414140c0010040034a40c1c010010301030001e94801e01800130016085580c1c6d0703c1f0141150030080200030750084c4001c6406040002221591580020485512a0b100200380e030000d400f0200c00c15414011400c1c400800c0c02108025614404809014400d040542030088403aa4402c3e0a00c055070f80800090031650b0307201599400e42d0308050828007550700c98000144035401c41102d10030310104003d8102e030742c00103040343d140e19051400d8900785c2042d403070442188034078101c0b8a1452007001e14840200b414000004900e400e041c83c1e1042d41281d521100201d815078110081c2c60400c0b030061100327079070b0001101a1035444d0031422801911410701e0400c1c0c102d41c20245100140010b500902880f80e02042d00245029840381609841c01103080280480e041448100310600e0702005001031248014191201c10702020b1031058905903000310905c0319050040c004003001100d2050306491030048009500b010340ca0342e40c00740c940304140100728091030f0100742c00c0b10721600c51200629140004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 816695512 1250 816694262 816694283
    0x16050d030603171c18020310090605090a030906080618090c10030b09010905060a03120f021b09040201140f0c010e1603030903031b080f0a090812090913 67
    0x1124020050091030000303850784001980c01420100481d022601e10103907100304000c008100d00d2444004040d41c044101070245100d24000c0140d03006d01500c84000460700300000c030205171307040c444112000281104140c2d40500880c1c2d003c80d4200c40d030807003129042c0c9000000369607104040f440030240031414484904100040c4034003c0342c081048a03240b81c084d60b035080007030241c0004a09681204d81ca081d0082c0402c0b0040c029510240c1000342d01040c041e012060140e42c983d62285500114142400055181e292031240241d050141440045002601401c1180050000348640c0400b40009051100300710307055006070b00c8841031b1600e5010726100c032078503a2680d0f1100e42c060420800e854145000d01424203440340b5948040303030b003580e405a4450308024215030301540c0c806480d0b03a0101c1c0c0526000e020364005840d020003400e409a140d69250388403082d005020b824030019800180d10f50304900d5400b401c8510050075142401c20403100104140c0340e4400007107082d80380600180190a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 816696762 1250 816695512 816695533
    0x60206091b060d15051c03021204050f0d080c0303040813080c1305060d1b06032306060a0201150303030c0210050c1911070e01030b011d01031101180303110723061605 73
    0x86d91241c4075400e020350291401d201c0003a40c0c001d031601c154001d1030750150140252000c9401d149520800c0c5c0d41c42884001c1ca440c10032600c4a2458004490403a0700c8400002c4c0e0b01c01e001980c42090b00188400310003048004c0110001400044a0702001078086548000042083d91403102002202e9008140f04580b082c100a03040807140290013800003090810540c044d40020264102c00952a8540584070715141c44d41046129481a10020304542d2a040f41c1141e200c1070a5011009501c6601c0c005184800c20101900b440180a41c415060303180c50200b04140c04814200d41c080e1092055100e00749141107804d803444c0c60301500c03402d4503204250b400b10f140780748110400c1c140c038001d0010281c07581c2d98400708042d0901d00710340190800000001000010400351010346a140141003640300d00d03a94400c0d10361040c8599100b9400a01503401b40848000c0500c6200c0140107004695802000076007071080d45201950ba106005a0001460410083c482c1e1500303d440d030350040680c1d080751503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 816698012 1250 816696762 816696799
    0x5030901150b0a0906090308121b0f090a0902030f06150d02040b03010504110c0c040c0e03010c09061b030816020708070e011409090d030b0613060206091b060d1505 72
    0x103d4000380c404111510030100b4040e0003090365504882e8001c0390185011082c2d5100415480c001d4104224440c60040d402100394143c406010905004100540c64a4020f4200070923014103600c1041c6003481042445400401040d059511101c20303500540c0d40384c94113078203480c148510f00721265080c1c4003060106520382010011030403518200c41c14400051600040c1c02c4ea03114414580845da0300611a44066080c01d405c880d80e05800c5091140481c05514040389c20369604450140000d01030420070300486811215003822120140509580034600f030b500502086070141014806c1801c031340e0a690b00e58030811000014106d46016980b4441c2c0d81ca00702544040203000d0341e03000540751a07405065041c0109401d218bc1c010b90f00a0003400d03240b6405800a0402d030b80d606801c040200700d80100054103864100040400b50700911b590318140000d1800c1100710001e41110362001080c5c00300c0c07031f1f1b141015600c1c40885d1520000e4004050a00001d403600b03954062500075406030000b000035203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 816699262 1250 816698012 816698017
    0x16200303040209010b0a120507020c0d080a0f1b0803060607050a05070305060a1a060306210307111c021c0614012c07110f0625051905030901150b 64
    0x62081d0743d9042140d0300ca4250a415006546075200001c512202030f100703411072604825040784050040da18865014004207500c03080900094400c4000003d0010740c50703a0010301c40102c0401843c2030352601104052402d52100780900103046501c010010503800d41d550f10803542c00b264840f08071852a080e07031412030f031200005d20060320540030b280700192100100b40584100303040f10482547e04c4421f40760800c1225000644a20740086a02c0101d002588101201c03034480c014100c001c50725100307030303141c41520396110070b02041c01841d9200d83c000d046051003032070503040b96040300c20080b91000e0911501d03902c001200c000e0400c03403c04041da02c0130420080c0c028107890300e641280010300307856034032010f800c0304460f5103450074001980000c0100d84152130501c061401403003034404050401c60078074640301d000d86220002c04d10000c42c80c0800c5c982c1c0381c0e117591159141d04000c0d040c1401c1110080d005000c0c1040c0c0c030180600000010483c1c5000e40c80605a5440c01d0328000300c85459030b111480b141c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 816700512 1250 816699262 816699271
    0x90501230711010507170702031623010b090a0209190f090b010302161101050f030906070e1804030c08040b030a0f050a200714030403030e01032316200303 68
    0xc54508402c400088180905485202c1a40314000920260110b80802003c000e203204214081070004240031400e05034449060b500400e090506d0011145040c00d10482d250a060740d0790380362004680c815180c92201c00d6005240300c500588408000021801c95140c4002d40408140317820000300d80d83c100d607000c000c180c0d0000c0c0801c002009a2200640407482074000c4062600c41441c40c503400a4400c1c0ea06028140c0103242190500c01c03010600741039500192070001d00ca070084410812056481034100001e400700300c0d02c110b03142d0304150b8130662440303010700f0203001c200203000ca40051000c1b1000719030003000c1800302ca561300e2400c0c401890007800070b41068030003c0c0c01e0a001c100300c11451b0045209480185c2102060510f501c3c0d0180700c40c2e840380c141151042d40c200c2c08148604c2c0240040d00c015802601c4540c15003c2e801c0005088561140c0054601c0f00f400104445a906d81d004059100d94a0500c000b08040743c000305940c1c0c00007040503c001d507625400d041000070008030195008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 816701762 1250 816700512 816700517
    0x24090a030c0816052b05120c07170a1205130e0702100b040b0f1c020301050403021615120c020a1e02040f050702060c180613061706130905012307 64
    0xc82d114810800e28211740c4102c3d610703608176110760703000000404991a0051340b203501100c03030360340c0c404000e0550368000c6120b10100f0742250600708103da1184c0c0600d048800c6180140c82c2c00001a6a562101280408a00c0030000b0200342003204c40200c0f240f510180080e504908501e18101000170743d05c2c00d0030f01084040c18102000d1504506140c05240540b0500510358110500700d8014070182c280c1d00c2e0302103020498070301d0750440941c50a120311400340303020761301030240034580d61090145521580d00072403030751115012030146240c6c404801405a14520b4020480700c1440800300d290207112500601400400c0e100705005065800407050389620984003031128a951003211000c94808885040258003c00002250120314078010404120200a1032200c0700209000c15102d030000e81c1c0740e03107100891400a00c503ea801400305400d00700040840c100c24074010002c10440301803980c0c000e00043d06c81e10781000308072081d00306041c19001c20420100c1841010203030762a450080e51154003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 816703012 1250 816701762 816701803
    0xf02031e0a0318170702060913051b04030b041e06060609060210050f220b09030706050901051b03100509130201110a0b0103150f0c0c030e24090a030c08 67
    0x7083d0310708810280254010354a800a620158044810740d4844035040360f001d0b00c01c014244140e03460f504100c540100c0030f040000c2c20301d0101070f0803040c0000c00c50329542d140c400740400c000003030350707807080540c030075070109000c0382c00424019058240380f00e000b4010241d5041280c0800c80c10761018075001200c103140e0072684a840000007030030440d40155103880d005921000080c11002840718111a04d89100e800c400e070401d020307241c00e05412000d80d0000e505420004070802070040c280911504140c0795802040541040d0400e40410a91090070620005012000034182c1c00e580400c1c5008150141017402540340a00c1c0540300c1c00c4142100304c0c02b0501c2d20703158004000c80001e00c940c10542c0407454807696401d50300e03040034016201c03140c044480d8441e071014aa4003000c1c0500001148282c4450100c242c1a01e009403c2c0c2e0204820366001d64440700c1d440e81014000241751040b981e441342c60341d076140a1807012401c41c42d02a000034007544000074000801e104006014a00e040326480c001d407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 816704262 1250 816703012 816703031
    0x3030610030e101e020a0e0f060909010f06030b06030606271801030b0903120a0b0418030314060906030d12060506041509230108090c09010f090e010209100f02031e0a03 74
    0x8040303001d03e109020028100b021f1070300141c02e20789024510842c0061456082004020000324084000d802904100480c10810004950180940a076402c006c807819030451030944041840c0d13000d011100b01442e09100c00c806092855080f541086060261108240021648481082c82428130045903200c601c4000954007401c04016544080c0c0c0402c010300a07a103c140101003e446c129680340d902c42e03038400300c0e03007449201c00c051400428825100032a2914200705d0a030380c0000c0040c501e6000f00c10340400c02c80319035030109140809441078104440f82003014004000204030030740244e034101000280100b820b9190210342c0d1903000d0f09959040c001e6840302c9040442001010000000250001c0382000560040700780b01c6d84400750004891a5900650004000c880c00f07030301030100308012031800d0100e404540542c8240c0c40200c0b0084d0719244020700425814006100c03044104203044e0001008a4400d10484980c4445072445c1c890302c2a840b00001c9940d071155041034003180ca03010407c2d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 816705512 1250 816704262 816704321
    0x1140603011503080d0f1518050103020a0515130914090a0201020604020904151b17010f14150a021c080702121b010608030c1e03030610030e10 63
    0x8040103111850b1010300c0300d00e55990803ca0342c00120b0101481500c0305200160314940348941c0309400305c1d851f05264840d1501d010074012074100d07c482104642058018000342c0c59080c0040c003101e405035440e1480040b5250f43d030003180600018815107640c00354001402011507002050f60414840108001d516000c041c1542c580d815080240540c00100014026280050705180c0c01400381100d44002810b1003a0041100c5400d69406445001003e2a1078455402000d4070030914110302111119410b04001c080c007001603101b105402520003024811540f602000035003060000107503d83c581c0210203029484048007140220203a900e890026482e40c45544014003d1100c3e4020f0b00131500aa03014040692004055040258903007a00700745400e024031556004143e01270241d07032a404103c01c400d003803890070108007049009420048808003000300c2103a4000204545200f80c400040800768003030202802c0f02002402999002007142100d600f100c5030f02000100c50060b0443d019845 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 816706762 1250 816705512 816705521
    0x615050910061d03241807180207021801090f0b090414010e030d060e07140f070507051f1709280c060513060320090d05060106020114060301 62
    0x220155101c14000800a0360701030040404582c00c810082c40c101c3c002100440d2134901d07000d000704500c40301c000058040648034440320760000a0004401d0a030710b01d0b105015995030041c051058401010510031030b07403a032594116a9603982c0509580d91102d40240d075444204800d12402d20101c0c1420551040e0303595511525011a5005019035216221a1500088459910320b09070044d90b849181d86109a8200085c0c400e003541d061002c50414240603c1a000e41d03006803000c003c2c80400d0554541c0300b545481a1540b24141c59003a64860005040841c0392000a510440e04405081000c503400042d4240c2c0012805054071001c43c0d00304a990540147c0404482514240e00b044055280803008c5d100c0ca82007400000c90030101c400490b131500310001d150365200e880030443c0000d0040049000342480c000902060404228050100c01c0ba021103584d0705e92200e203140000120302c041565203120110755250010300320381407907850758806402000c200c100a0564542c140000e402840c05008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 816708012 1250 816706762 816706771
    0x1020703050f0304050c030111130e15010f020312100905070807051801050d05090c01021204030209040803060d2001020106090213060309051c020a03170f1b0f040306150509 76
    0x15460301c0c0402d41d111400c4150009001242c10340140007550569035002d02560a00f0340c490ba101c42d50b15003000c4c4ca0f12001001c02c1d8458901c060f15001040588400080c080560100c2030034518080b684400080342036100e20046844180b40070400e120ba00394088440704140c844102042210b40c488070002c0d0350a1104a41040018030300f04086039111039005098040844181451030402c4c4283c4078090903500f00719407086042d40116a545855030b030400401080407d4040f0f024605801c580104002040091010780301e01b1001004ca6030075114503055111154101000c44542c0c10b00c912010444001d03500c03101e0043d800c1c0072022030502d020b442204c070700351006008824444c1c40d19006030b003d8a42d4200607a540e0150b00ba070107070811940c110641882005a0250804007900c0c50041c142040400706080c5424540081182c1d40850201550b0803545003105003140210069442c0f01d00c1c421440c0c103132000180404d0002c20400700760004510803419a00400e8099100e209100c810401187e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 816709262 1250 816708012 816708017
    0x6150312110703060e030403051203160c050c240a0306090c09050d1104060b030c03011a03070f08182e0e0303010306090303021306081506090120010e12040906060201020703 76
    0x110100001030807540400005845c0c0401d4a09244d9a600d0f41c0381400c0c4403071a00020980c00100700442280303100c0014500d401e01e420854150101505e07100d42e0b514841e030255001d82240b994040032881060443c4030405510310341380b6515000010000c001d00003910540402c03504004c2040754060181020b01d09541028281c0c1940003016150014102011416107400507590308001c240000c40c40c004622030424440d0320369a0754900b11000c40403940b289005030200c4402d1080c44203060380055490b0000c1c080d483c008500da01c3d080c13401a4080e0050798150b0030340c0f09095a10740d00c50751490024440c6ca00600c0803000d00501c00c4064000d5031440141c0d107030250420001400000c4241d40980c42c0030f4002e25005040c00b800c080d200c4601199504890081143c0c8010401c078400081c258401d5000b00b80c5083c0d09200c004000a84408580c940c04400c0d5043d03940c16410030042584004942c201d05821a0b403416207517000c60030035500034000e102c3c3d913900780180400d42e40d0050089800302641503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 816710512 1250 816709262 816709273
    0x815030d0305250f0f02120912072301030b030f0d11030f040608090c0f090703090f0c0905060a0801090c0510020c0a060503060f121b0a030615031211 66
    0x160310071001030100400c08440e0341d882d112804402e030005050240f0389a00c2d500d903524a804c40707400141c440d0200c80700f41e50840d48040101c5a02014010907101c4120060350441d0f4448023034001103060034004d0300070017440c07081019020b0025400050617052100c00380c03000c10111803100189510b80001c0e28541c080703030384500c280c02d60b403d100c0da012040c90341c0241c09581c14145030291a24607580250301403800140c0385018043c1001c0c0520024944007000c682094484440f580468841a03009100c1024140d9420504052150080300c401860741e0081a04020685808480004010545480d40145011000418100d40520030300c2c00864010101c005950700e040100290040340d0b44426045000d10300c00d0350055118005a10302820013603e03030b251a8601081403160310480300c00e80c0c502c1501e0200360080d10020119605481d1840c6040b8040741c440135101044082c0b45070f6100801c101c0c90180c0032442541881d90707500035a03104081c1507562406441e030451300e00048613900d81d85500407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 816711762 1250 816710512 816710533
    0x11030c0306190803030408030f15010c200a1d0f040308042003010f060806060105180405040317090615011d0f0102010f06080c1527060405060c0a03081503 68
    0x80e030580180a002c0c01918a40c40d2201c24503803c40e0804d031011515108040203210142c0680700040350b0144142d0940000340c502d1200080c454518064007a02c003032881881c1110380303410198450304001e0003400703400d2840e84d2215844904e003d004c0b018002d0629070800b00d002c800d560340159005a0b0581d540c2c070502c0e110383c0c58026a05a94140044000b42c034082c40341496182030042e4201c04048100000c0c43c103103003a40700c50905e0001080181000020440c000c2d038011401c80c00007008209681c000f80c40c0d07480d45003d44030a40f01e880301e501d04000304400c0007605100010820712400012580b10710021604005503055895030f4800c07104e40707141800e400c1c0e132810102d888102d0f8000501c008500070444079504d0040319843c0d041400b458110202c1a00a414003c00d0300e0b070385a0a5140c410b261582c200e101d001c64140c3c103080c0075090995460981c02d240d50b80000d0310042c1c2030003425241d4400c200c00285603181c02c00c1c0d41c11008603559000045160301c40010745800c510001d0044c102c0f080c071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 816713012 1250 816711762 816711769
    0x207050a0b180d2a030609060203090f03040b04060e271006080c0301060309060f0510032a05281d0f010609050d030315060c0213180f030e030105040c0911030c0306 72
    0x140140118041d120300b400001b14610340213070002940039100050fa607003050007400c1d051494205112400758000c204c1000a5030f9000704032000c41c0d66901d4500654003440c030004a640c2e1400620b01695004203002c02041021005d486003e0300c1461412100c0c2076644405591550b07049a40308120502800104085806504a026118420b4200150007008191000e0446d40d05a909081d0f0103803a003014402c201c00010840c0c0c50300d080446820b0f08a00d00d0703074600301c0d000e52405040d01921001651511402d14185101035102920308410001030300e40542c145482d402001007800d14090a010462601103490b215040c1c0300d256441000c0d842c01d01c8140855040c0d2071000b141055540c00398001c841c480c215061001d49000c2d940d410081065004001b482071428402d0302100e450039080903c080b056a404a2169500807040050300e1914142940c80c4040c0564503500340d4280070800c020001441442c0e8240e680305002081840e08007860042640130403500200d03401001c1000c0350503440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 816714262 1250 816713012 816713063
    0x2011e031515050f250b191803030e0a061b030c1b170409060e25020607080a0906381305060d020d030e0f09040f0308070207050a0b180d 60
    0x504031500400103a0b400145017801143c841000d0700c007900395809104450101046101c1200c00c802c0c014414031921001282c203c00003040b008041c07650382d2904080000c000c0c06412401a00070900b00030740b03801f5810842c210440503c00b08000b0f031400001400311401307240a40d1103aa0240301e019507400050307964001788404c4a08807084400c092100003180d503a18041c803000382490480d2015981050415100b0040c800b00040c4101030f0705540caa00c42c55800600f040e4445001e20b40050b0586403541008028881c086020740164142030402400c901c0901c205030000e00f1103140001c05480c840e41012203030500340503241e88039003050324403c048070442e0481c40d08400d004181e0003900f17020340d00007003940c911800c040300451220030354200d552408100550f04c110050711141c0782443c00b69203811f0440b0000c40d004040c01460720200f00380d00d10820649005d4030000d001007890755143c1c01c0b00d4002d60802c48000e605d070104584805458145403101581c0290f10900b0441c1c1502001c24140c94030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 816715512 1250 816714262 816714277
    0x1206030715021f1d010f1a062d1612021227030109050a1505010f171006080a0c2114030f031e090105010b1602011e031515050f 56
    0x181d0b114180c40c0c51341c14200300c00080c9a065100005481d60010300d03c0400d490290204a84420656007000f00540300c010403a641301d03443c40b0705aa50240500c85504030507942c01c41c43e40000702e0109004062841c2e10941c2c2101e940104111a1043c120100483c6c1e10303080540f01c446044814050307a2508400500180800181c211001612856110220342100e041800c1501c0c141d1001c00b04805021075101c5c41c2651802400051013150f042805054948542e44941d079000102c1041c1740c0b00a0009000310007003956800c0c1c041c17100b039a40c0c00e0800d070b540d59080c0082d50b8501641c1e500040781c0c03140c41001c0008619103d43c0c804c0205013a25100003d0040111801e0300d40020000100d5007015200254801c90364502200b40300801c1020704065801c005041d1410740c0e141000511084a00009403101b0401c580403c103446010380c401240d101c043c840d01b8501d0f00f641035a41e07400c0c66400d5045150751842034400c1058440d50703902e008219141c50020400400c40401c070394810000d0403001094071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 816716762 1250 816715512 816715573
    0x301140903041413090501050708070903020a450b0303070f081e04240309111e060f07111807050f0405030607030e0601090c0e0607060e03120603071502 67
    0x2814a1300206442c1800da04a446941d9001008002c41e080441d003500042585090340900d804c684c0400c0b80c811003405003041001d540b60a200b0542e51004095803445404001c40c0402c915018502c692440e407128200355850a1105250280c140042550541c5410000d11411100140c507100c1042d444000c400b40d85101c2261004203070080003004000800c45c20f500450714000e06403d0404c00e400a009200801d400c0c200100301051518003488040d40e03048a0000d44040a10a03020381c5480641c403086c1c10080116001821240810141100d503006241c014002d03d2120b0802c0509180000c0d03c10400c13812030041040320348100068420130012400107440c0c41c0c0c441d07001a10b0320301d04445a0000940341c60f100042d0030402d212160040202541c1030000790010301d4050048a42805d039903005050101d48007080c80600d41021a00007064010307030340c0d1005078100714200200c0031101c02d80070788604800000c0c5480c0da403501c003d500040d070b03020f400c000390500420702041d041c2c2e0007990300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 816718012 1250 816716762 816716779
    0xb070b010504061205153409060f080a050a1b0c11030102130e0403051e1c0203010501051e0409060f080d05070f080c0114010f030308060a0b070b0a0603060906090203011409030414 79
    0x42c08a080c0398001107800d581f660308191058648402000445c06070000010044840000002250030070f880c5078200344020004a100c0c0d40d82c100b040300410301100d8100c801c404550005080e1a0030852280c0128003a983c04600b582c02c1c1402d2609034480d00c841203c1c4016010820094040003100c200e8001d4441c3c6007203441c105040e400800401e00c0368005041154000601c2c6804071006101c0f84082088800d083d030030366260500203031030b5000700d440103844c0005030404505501d090000b1500070342071801c000c1141f00e8441202085414050207195118815154451240740c000c3c002c0e00e607140c0d4413409441c200d00040d40c50040540045030448031329922441c003200d031000c0300113403a4060b01c1c0116820715542c0c0307541401000d628000d40001d000d11203c950074800714444004641100390440c02144040c1c1307901d01c1c08170060090b03034070290055191204400400c40c3d1604100f420794005c500a100224608540c240f0740803007a104d110155204120030002c4060040c1c5141002500514119 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 816719262 1250 816718012 816718051
    0x80a0512030709091109040e0106030b22051c021002040b04060c150501230a0b070311030c2a0913140111031303090b0705071e0b070b01050406120515 66
    0x800e80b1300700401c804441c0004203c83c2e6841c1020b108d03020b0413402540080c00702d18a140c80e54075003040080c050311030180c542c640d080071440d5555040c04140f507005d02121543c103d104620005202c035005820010300600b100706901a00600035038041d65901c4407040c0c90141f4081040c0d4800608450465604030241c1c7c080d0b20002c02d501c5621b000708840d42011034100c1e0103415a02d072900007060741a12940040400f030191003805401d0340da5035036050401c0c61110031041c1c5041d245003d20b804891413842847d20a030a001500c40e45440b01000c0440703001da0600c035030400c1141c06101190800c080034001003101000c6035901c9030008603100f000000103502407020a444c0d070079074011940c02c443e566034034070300808041e0310502d0f00700200f0445807443c1c1010701540d205034561400740310700e90b11103810440b5848a4030601380350400514141d10b05d030b0b64a00d2079140c4502d0400007485058413031403520000240c0240740c003000091560380032028103004250b8401c26400000054001c04140c0152027205 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816720512 1250 816719262 816719279
    0x3060603042d020109050d050303040f0519140d050415210212010e0606070b0703020901090e0103030201140a2d0b0918120708091c051e07080a0512030709 68
    0x10b00340b0b503003480ca03040800748180005081650140d01a502459044001c0c002158010007940e401035840601020100b4850070700b689410017041a00500708400e4807001e0030403c240084800400c3c5000984981c0f2135080300544550040e0701c91001c040c2401d0492095107442074240310691a07442580d050302c0740d000000380089030440d003142000c602c0c03800018047c0345209021540c0c804400c80780e00380703002019070b5218691a80a044007080c5500402d02c18001d0307010356110b201825040060790029030350b9080080c00f130240c041a4465500741c24000c503546d6010350080d44041c0c480c005c410f0140c0075008001c0441d0702001c1140b081e2503a56481c40f02110340c0c0701c00c0d04c240541c007409500c42034850f4000d0f0042c1441041150203050103c20040c03900010255401e80d4000030040b144034049005c03000d246a0922007080d8005c2480c020364000303090701a0501140002c9608180031505100d0310b507200c40c0d980d8000312a014000c0c0d8000c21035000d0201d070b00c200465002460b480c14040240e901c034400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816721762 1250 816720512 816720563
    0x1060b031005040b0d05030a180e040f0614010503070b1b0a21051e030910050a06151115100f09020414010e1503070c050a0b040c1a0306060304 63
    0x35040c0079100305008101c40c1c9042e014a00790424112607041400300b00d6503c140c3d0743d1040708244001e00c030032240d1030f03010b620b4000c001400402090610b041a89042d242c80400c06044074022103c0500d004020028010080c44903030584202400400845003032041401a42c1c1044c80e80500b0009006c90903400d2007400c1c001c03841034510903c1e60b0351218443e1001031982080541c00a8200a828020084246600000c0e008400420703400e142e9252690500542840c0c48500071f81d44042c24441840b402d0f003081c0d03001e81c04031980e01404480c07492080c9400c941e028010030710300456a0103503d0715814102e6020398583c006030014140030b0156a82c3c030381030b60520030650140450540c0030508102ca0403640c03ea41c29000030902e800c001624100e8002500c1e00810710500561640c0440020a950301070304005000b25080780440b049401c0728903000654030003c60b4101c840082200d40001c040c3d442281c054440081800614210b07540d640c01d105460308001c0080d5a0075262202ca9000b032810b0006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816723012 1250 816721762 816721771
    0x324191a0f1c140d14040b070c030503030f090f070b0f03061809010609060f150c080d06080a12020c0306070f020712061514030c04180605091c030b0d030e0301060b03 73
    0x300403c000d8420300c1007802c1c40481d01489040c00f043c20844a940380440c41120155001c240506403507008030306040b0341c01d8130281c0000301184400014000580d0303a10302d6081c0b04410200880d00084158504240c03074400074421880c15000920021803c00c1114015680c80796025180801e1200800411035080c14182d0350078045135503075002030003550842d00030480034050302c803c40c0d441e061510380111101c00248440104010007140c26108200d00c0c09e040754034130b28000308140002d540b5240050345910709040c2c100c82e184900d00c103456045001091181142000502924580e83c03108000e03100c07924110030302d200318080c9960102e45e019041078540c0650b4010000000c00301042d12038840d40036101d802007580e00c1410510b182c2c00ba54001031a020721042540e0208420104a003900c01039498604001c100342d080c6810003610002c0002c94a4411403000c180385500c075007446003501154184010603402601d1000054042800b408501070550405000022900c1d0707a5407480e40c1c10f810588 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816724262 1250 816723012 816723023
    0x14030109080a17010e040c03060f20040807050a0f031b031e140a0503030c09030c10020a1e0809040c1101090b01060f02150112020324191a0f1c 63
    0x642d00801202c20307503c1e01500f100070b001516420143c0703a503085054248401000662146000412258250811280c4500c00a0300007000000d48509855903001b50083d904036100d41100010941340c40f0441c00308441c281c10700c3c40500c03410754940032807001c40d145186042290000d00000002c5c80d03006d1560b00081c010300070002c604194035180000f0b07441c1d0b900c40c07152a808141080003064020007181d401100c0580c0300d9030340300791810120341017000c0310141e10350041820351007040031034021a050301020310414030305081c20100c40c0c0e02d02c80b11021960283c02d1080920003404281001c0e40044191071103800d060540c0da030307204001803c1d5076049000b00d6081e00040d00422045030801c0403000e00701038a0000c0c01e07541800c140201c3d0a05014031a00600b51075a0030704c6003d43d2000e000d41151584540e403126845282041200c01c2c900c01500d003041488150390038032206141c14800c4443d0b200c0b04103965440898003204200b03448240c1c0d00782c40d40c400103206140040c8003254213007078151442031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816725512 1250 816724262 816724277
    0x30c0304060507061a2206240201050c0c031c020909040501060305070b0a05030a0c1404060f02120a020a1b180614010c0c031b0b0a02060411060a020714030109080a 72
    0x3440d094003600e26051311500c1d10000c0030041c490315074030301c00001e01141d500d080746c402e60084c5140f40c00241c034465008642840d0040c1c00d00c444121140a40701511b000c0350020b01443d201d10304050014441c0349000d0031203800510a14100b145903201c2d0718440c41c482917000d03042c03a40500002d08101801c1c2d5003190240c0d0340d004100304103c82404150000c0c03007008076490a011489001030070501c03006208143d0301e40c0c2c030081c8c0d03120140100b08078140c9825440415464980f2948040c03c0c2000c4400b03241d002d44513880701da0b460352a03c102110a06461640504452603855a9001650903c2038207100300c0303410f40c0d5010801c0140200300c251240749509022800701c1c48d140305203e400007621b0516041118800050000c10307030708821582101e03440401c0b43c04680c0500c032090410441da42000007030407400294aa08103a0010f049801030f40584400e147c072500b400304004c080c0c440c0c00d55200158004103010016555640c043d03007030811001d0004154050035607a011031a9204c01d50960108600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816726618 1106 816725512 816725527
    0x905030409091a09060c12090a17070317060307150e060a0c03111f0c09051002030301180c0c020f01030f060b0d0c02120301030f0203030c03040605 65
    0x12a074003042106080c0c0b40260a02880c20040301c0501c0d100008070f40c030404041282402050108090703403501500440456156070020b2003c0107500030314200342c0106010182010600314402e240c507640b04031501e0044e055100d4070703001980c1400000100300342910009182c9044d145281d40c5856102030070181116110050800300d034120b1800b0465103127190708120a40b03603d0784039441d09100820503407a032641e00c4070048002220120b5100145686500c541e101131404619450000601074507840405d440411003403425005a000100410541103085080042a130a00c1014000c40d07045050040102000f8400039106100302085002580c3c0283d10240707424442e82810b0103510307170341da4210140760072601e202d451260504000200c40751000c2562040c0c980c1420486040d40d017540c69800642018940c00c03038151104010400105000b080908000e04069603580c2e40c0300d04 = true := by decide +kernel

theorem cover : BRFrame.Cov 816546762 816726618 := by
  have h0 := BRFrame.cov_init 816546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816546762 ≤ n) (h2 : n < 816726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
