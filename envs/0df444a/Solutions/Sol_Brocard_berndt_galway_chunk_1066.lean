-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:05:19.461801+00:00
-- url     : https://prove2.me/submissions/e7c4c319-039f-4296-a34e-7ac43eaf001b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191546762 ≤ n < 191726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191548012 1250 191546762 191546767
    0x30403120908160308060607210c0503030f0a0b120607030c1116030201081005010206180f060c04090617100b0a0f0801061706060a030201030b0105040e100e01050105031614 76
    0x19a039000145035440700c242c0d80c3e06120000b032a00804940c4040d02082c4200814800100421424990408150301d0710304018440e00d15001d064032180d10010f405461070002200700002d21403401c400c04c0c403880d072003881004850b100500f001b201410b08a41712040741d004c0d1002904a9000e94030141040300c880c03c1ca0302c18410080720301450502258044405114041401c0045582007410160891095600c500215080c40d00007542c1d850014122502d0a48100e582500d0407028080c1010207203404007501c059250100c0344146a601c03600c035219030300c1d140404c0001d045c69421800c226022040c0301400c1d00d41d0038104000e0260103600d80f0f55a01000045000a0304690490390800030003540001040d0070381380603a0040421459183c850680c1c2011b81044090369480020006032642400c0001b414503103080102c1d0240901d1304400c000c0c02d401030a000a1000c4850141c003101d4043d86403a045030b898900450765400241c0d05c9084070404a00b15a0b90349014500301c04071220f46400160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191549262 1250 191548012 191548031
    0x6080a1104090b04050708010e04080f0705060906042306060607050102040509071701050109030b0f0910180b060a06320f070228090f06091d0d080c03040312 69
    0x20996120b0340c00b44074010ba40f00403a4201e030405003d4a1707400320490078141e000d5850300842c01c03844800144024065000043d0481e0380600607002d0b6820250400c08440d090300d010035506a031480c0c10399003a10003006000d003800d1406413400032040d407106c0c10000741c1800d40700c00701401855000010100d910395004c0c04046140c0c0c40e240c032000d02c03445540c1d441148209811840b10703096070042c1c00107810000070304018004200e51040141d004040394905080c0340d0794005209041c005c400342c3c004121401c055030110440e60080c032800740a40583c039583e5541e180c070400c01002041e648264404590010700450740d403102075105075079800030102070510020701060846100c2d8030000c0211150748000c14100f043d410300c4000341c3c0d032960600040c680242814102450208024030030b1075101602c1752404034007006640c000d10010080003100b030001c414640082203039401807802e00840c034031030300421100c418495050180116880c140d09469610342d5201100d00c401f401440c58191a19400c428 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191550512 1250 191549262 191549291
    0x4060c210203070b01080a020f0906010c0b010602070302090c03060102120d020f070b01230108190e062802070206070204050402040209090c0c0c0105190305040510020711120102070c06080a 83
    0xaa00e08a00c0d54040d590350360180c90000c4041c4810b03008005550720228a050050f10380000401d0010803c4881e03610f19070f00c0c2401214580303442c8400400f1000b4007000040c0603500001d450381924030845041540e59030700305c02d0b075449000440340f00307006901c411503041502181a00170941c0680114002d494440102400e2100360300070401100c1e0351051400402c0145425008902c0015140213a12402203641c00020420400541400102c1660a010012140b66a0b20203005c4500d2030080d11001e00d84990b80400c42c000d117850050000c40825145500500d051084419030741c3e000308014100324440e020300c00144001001207802550802041c41c46030b5802c00307203034030070028041069519201124503500b0949850308540c144070003403042003100c1c2d1440810002c113066614002440e03554a040240ca0202005c03030706420b02d1710004104041c4240c032405140241025602c0c030f0960048401014200d02c12050080d0842140c200c050140c1c070320544880360058002038004c2084c52207000c02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191551762 1250 191550512 191550563
    0x305090c092a07050f03030117010b0d020111070e0f04020306010e040305030a0f0e030c0d141806070303180819090302010f030c050904020409020d0b09010b1615020309010504030e1504060c 83
    0x5010701030340088010840c627049058880102044c81c4024003881c0782c441c0224600311904e00000381845036155010801e81000c000000c0184500440b00e0083d0404040c004c0302e5640c10f5500340c0c041e008180c00882d84100c0c1460082c06180c0c16980c19181d41d444881070700003000c50a5901e9842502c6048000e20345008101529400b10f000000d4901c0c0c1207500700152030b030030b07002000c0161500144401d41c00070f0500d00c180c00d071030780059881d265501101e141c11030090441d0514911020ac440f0445024054110083d1920481c0e04465900003203090006036580742d0741c0c1c1700082c002414034221241c0a0300c6900700e501032044a08281d418060b0250024007641c01c650089009558003080b0390709403851502426031042029119181654140700030100070b4803905240f0040d00060f5403205c000c2010209102000b00801c3d5421916400c10300c160328040d020981e030030350018840159154036480c2250b050601d40d180c11520301e2501c1c0c40e0803015213418202140640f00c0d8580c40d50b100d0b0144149000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191553012 1250 191551762 191551783
    0xb0a0308030702070905130602090a08070605041d01031203022812050f0103080703050309031c020d0e010b100f021005040308011701060308090d020409060c0305090c092a0705 77
    0xc05440e441c06803002460a00340394000c1e80181d080030706001500e840f0361603241f0800c3c0c1124000d643c440b100000b16009210a910503000e074400c0c03600000b5401d40c40740282082e11210604031032012400c40c0a80030a44080c00003914291401a0354041c0c81c1c040c1e4010300074043e8070700440c0c1007003030b541d130716007415904c841d940c2c001160302a00842048001c5104080d070251980c2d952541c3d550541d110f0000600440304002c1c2072000000205043c0b680400c01d4a1280300d440100110b403280c1c0078401d402035007050400320109030030610b4050000070103008980c91640c0140007150408580a8101c40800e0401407030010760040c50351104103041c1030702480344202d01031f495204513945030a40e111000102c40d00035502036450b014043c00012480e0701102d541c0e4004641d03003007400d9464000900108a1814010180c1e4174040f0140141030701a040144507454980580c0d5a0385400401d116200108480a000480e0400e46030310304181e4202035001c0035050b04c0310702800c0201c40c1d42e5003450b1528000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191554262 1250 191553012 191553023
    0x100305040201020309333109151a09100c021503070c02041a0f010206010e19020f1315050c070905040618030c0c06050c0c01030c050c07180615020703150b0a03 70
    0x1501d50702407220000640341f550402c540009000403980081050501c403802040003203a00d4070000c44208007035a0000c0047c0080b00342c40b401340051019041c0301c1d41e000e940010300400100740c007007014a0042190b001d010303030060201407604032040c40d151f80aa100800510a01c40e10700c0341800540c4883c03107048a6841c1629002e2402c2070300c141081078070010510118119440305005002c46400841c02c907801c29140048a00e0201c481c1598001034099a28000b113911408101c0c01c101e4940450504100d94180c00741d456100c0860404851074828620241203583c49800f08024085095015a81c8140281000586881204a001c0100f400a1001d900048110940350140421080381400400d410301702585400b025130841d9484458221441d03044c0b41e41d07010280202405101150250382c03131201920300c9a611205414039800c039111000a0300c1e490100003040495040c88000000c100540080106520315078a120700c0c10600000521100c4d210302c9801c803561500d0543d5801b440c400c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191555512 1250 191554262 191554267
    0x90f130f050118060b07080d1416030c0206010807031b0902040810060602010b010c020d0219090f1a1503130204060b090f0d17070821040210030504020102030933 71
    0x20f68540680c1100c00e8608009881c00b0010801c0c2d42d40d160031600c040e903200701c04075120706031900710000901650035680350000024041100c0b01303136001018440c0ca155900c0400070346c074032088102c0e03544409008624040d48814002c0c4003141c0d0315001c9512008000c20598082901c44e00c0c40f02c20f0360482d51042007180c2c8007001c1081d8843d0107005600c00380440348001c129166406000801030100001d000c4c1c010540584040150740341c55000302c801c00d40c1c40140001c415620802c81d001003580f90344c40440c680ca840385004403603203c010b940c425510010070482c0b140000d2aa5588194809406a42d101a00f4011100161900e00949005080c0808096107034074420b0140001240302401c00c0313110705041301858002940d07808540071000c8520f120152070300070501d40502c16220312414035400d50141c00c0d01801c0d0400100039248121320070303030701c4801010450001340d09495040d10001c4c051f81090052095030300740301022060f181240340303155080074a03407804580c029041804904109000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191556762 1250 191555512 191555519
    0x20c01021b0d08040b06100c061b14120711030c01060801090c29030c07050703052506080703050406060e07020114130302070e0a021e13090e03090f130f0501 69
    0x2d11010491091605011803107180590301c0c110356a0005001c0d91203108242c810840051040e0210506641d1100040000e80132510001e941d000200f580718000410840013450407034004401d981090708030081070700c00c6458151040d20281186a04660036100900c2000c40d901700134001c8400070860000001007100040c04c0400d04003150350003801c0002c25041409218409000784060710a014400e00e948940340d100d0b602d038a5200c0d100002c1c056200d003110200c2440130228440c00440350301825220001229102107880407041d10440e0040342d5907000282800c1e0090b04415881403040301d000a11589802890900550650307000005079035505162001401c209a001d8008141080c4c00f0000c080599000f591145240540782821000c030b000302e02007200e00d80503a403000300a4003005041c4004e00c20800ca4942000301402c4900f04001c0001800c0e5200c3d00c6901140702100d00510301c2c0070150010b014240304112982600640c500d404096049154460a55410201c18010a180d4903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191558012 1250 191556762 191556817
    0x20301180602040e06060403150c30050f0c04060c03090b07060c0f020304181e0912020114010617090a0c0807090b10050a0c050c031209030f0105040c0b0706020c0102 73
    0x70020f10903401090100018004101801c040302781d42c10b06604041b88050b1000e000f203800c10480b45008440000d41000d65200040c250800201c440134010208000d03611a0034109a02c00107a68251034a0003c00090211394850104007034080c0c000c0c100f110403556110201916540304140580d6a1560b0751400d60500b40e221111000f004840e100850925060616101050080d0300e02e0302ea805035101d040fa00300020550448085902c810300820504161f420407100f4a41840e040600652918486008403160308028a0581d28a59941d13000f6420080c0a03107c108000b402114032485178000e09000100c1032400000a00030040140413001d01d0041e10700c0917502010f0b0310911a00c1c00036403490b24280d00c2001d4454031072207481d1000072190319040031410304102a0400d9090f0048550020150141c1c40040103000000e40803241e40360b034101c48182c01c075141918014181e1104036820007408184034094244c0b01d000f214018903100c1d41c4c1c42c14500720b034040c20302d00411403031424402500c4034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191559262 1250 191558012 191558039
    0x1e0201020c0906031c020703020301021305100302030f0601050a051201060f0219050303070807110102030a02180306070804080901030e0610060215090c0105072d05060c040501051602030118060204 86
    0x801602e660100d0304141002a45400702c5020104850703034090400d0106a1007001164011364001d00210f5882e03901c1303400a92503946500446000d500d000d1070001035540319100b124030803100d040720880c95032590001112a1340c0006000803c22600784403088e100000d00c06154001c0001703883c1c50907a4012210081d09058034281003503141c00b006010003000c06d0001c412603030b03c40c00c82d1070400c003036076502c0c48140d5040740d00909518440d0710100030042c8108403513004101d00b102c55109114081e80e98003c05030361340c0d41165582d00150075280440c0010300d13450003402414005040101d1f4601c50340180501e415000c4034070502c40c01156000f0401c2036014001c0741881d007001d010401e0035282150741d040d0b840703002243c2c00e41003040000e801001e002410f903419000c0381c450200f520405800c021404103d020801c025220780c001d0b1000318492803101d008840441e4010b8440500348800d440c0310240d40c000b01441030341c255403540000e0501ea5420b108141c025441090700507202d43c01e15854142c1003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191560512 1250 191559262 191559283
    0x9030b1e01050102010905030403020f011704060204050307151d1c06090b0901020310060e03010207151a10140708090d080a030b0306070912050c040c0f140f04150c1e020102 76
    0x1179240080c03d0303001c508084100c43c141e075015600011000c2488004848032401280d00404118500317040c40200320304e076001002210021000c4524080c3c45400800208108a5190002c11141d01800c128982100c801c8240b84000521002a06144c0d54142c0000c1121400464031295121001d40400100750001c035040600030000718250b15020100c85042d039024018030302440312488000d071150340d0940440310314540c049159040a01d403000c540c000340c00030100b04030910661b29540040c50801082c61000d101441d984e1f00058441006a0034071640070b500e0030b85500504000d8050a6101d180c0c410401c584602e1003296141e004c178a00404640949400b10b10070b8000d07206002d03070250311500704070035074030041103c2442d03000bd403826903d03008034101c0b596007050a05800600c2142c000500f16100c0034142c13641a204640251410841d00c42d050015008503030901040c03103180465214036041c240307103041034142c0ca00310b5141c594103090113103240e00840961002200c11541e0520000c03100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191561762 1250 191560512 191560517
    0x603050d180b090f130b030106030b1e07050307050c070b04080a2607020108070c0b04030906031d1207240b040608010e0604080901020a0218160809190309030b1e010501 74
    0x30b01c00e01200081c0c00070744114106118078180002141c05c0340712030707106d0042000020020480e07a696441c042000300000c9a80241c80d00c110311500100460541015100d03081d030380d50301d80c42d56485003420b8a5a4008a19502c000d100e40c0340d0226a00d000c0000a00162241000070443e03002c071864030b107400700c44154054a030407003480c1e4520b5040800c001945c1441c0d509007410307a210b68440030202c84030301d000c84010f054280c0b910148420b040d00222100203031011540d0030322003034401c850616400a144032169103507030302645041005921500c00307020000d2140b00088010981c2c5854403c0c45000e403055202c62550700c0044e48094a41403041d0002020100000e00180c580700c6185030301c2d8103000344060400c0360000b8051450b82e01c01e100042016900400396a105c1c20b0401c101040440c0485d8091624151650900c04036400f03102c08604c5031500e0401800c0e401d101d41882c05401060b0401101805552040400082e540007400c612540010310021400303c440c89a9038501d060680c0400d05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191563012 1250 191561762 191561767
    0x302040e1c090614030a02070b0709170115120201140408030c0709060b030a0b060903010f021306030902060403121b0503090102060c09130b060904090804081b0a15030603050d180b 79
    0x42031360050300200409241e1401c1e240c482d03444400038400381c401c04000034404011602042071035500411000150f800142c80c1101a0642c943c034242240c441c0607040f010b590090b0400c00c0344811243d0845171041c410b1504526440d45220780e815190842c0c0c00003c0c4903000490300c00e006400c200311103c02001b0b2407006010051802006055174800a00840c8409480742c80c2c40c001515480210744100d00003070020004030b040b40442000a40090081082c03641d81c40e00c001841030301c603004043c0041c1d00182054a094030310750381c0b03900107008681d200d0140951081441071121060190070001e42c0a20091503960075280c0009090090050001e003000c5018805909651030b00d100411041440d4200092107240060015034280504103100d44c0c8203040000c0201000444805001101c01c1c80003220620355480c0c11541d8501d040904440d004446810104850154004006080c542074140040c1140e2280c94280c20291100c9041c0081070b500d40f1620041c00a05180c04001c0600303002550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191564262 1250 191563012 191563019
    0x1050f0901031d06070c020f0402030121050c150d05090d020c04020d14070302041806050108040803071112040f0509040f0b040c170c09070c0302061f0302040e1c09 72
    0x44590103940115810180d0341e09540501001c240098094000004100c0e01c0d40e00c1c0601000b0420198490200c1c064040c0c10060708070303424113001b6a8165480b6000107010500e03213000c40e041c5e0300150309094405204065680c059501e6403a001080010741c01c0f0324a6403900c90002000c03c0c2c0e42d021f007034a0780c0d6500c00f809220a0f01c0c0c2c0440c06240d0f00f4011074000d039542d401c0c014844040c15548914941c3d86042400780a21a901a401003088035900d036160355400701018940011034489109041c0840c41e08030002c1c00040703607a4021544003285040c11595103441c0e804a030b180c450204c904500366100000e00384000c0c0a50f08410004100c21143c070304030380c50182e80310406034035a000e004111008140100d401c009822418001420b20600c0030700301d400e96030710103d40e20202003043c58003400429011400c01071080703e410040a0301034000780025245c144242c9040d511100e841c002517004020044010799540c000c0040e03a0845000425480c60b8440380d44907120380078515842400354160041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191565512 1250 191564262 191564287
    0x3021902031201060809030705030313060c02060c0904200d09110301060501020a12030b03030a05040f0f0e06090604110a0504091802090420100f08010504111c0b0901060c0b060105 79
    0x5041d81c01601d8441560341b00c01c00540d00c0c500441000520f140400b104000b00408030f185417080d43c1e40a2001440960f0f043e0100f6070315000203403034484060b10200020161824203405c0000d01050702210074201c0c0c00d00e40c080b280140c000480310398002d6101d10700740c801c2c0418045041d03800c0d04110002c1215134640030001c0c0d178401d200c01004040c0c003c202078000710703103009620003a203d0501400341c07070b80c90445000081c51a8424098040c061b100900007040162000c183c00b030a450030908410b85c0e03515442d0410401181c01000c1d1548107840d1f402d80072820708000c004e010528401e44540361114106a0854142c50300c505405903080300071480c2e1400760342d0301c1c80281d80142c0c00442115180700003071031203011021600ca60b180c110111802d14000301e6445000b060708035105d40d40360b00090341c031001040151800ca41c0c0e0b031981e600c010b03c202032000c000342c1013001c80928141d000040c0064110003181032500242d11200200368003c001c14180a100f02d01158000000d00e80649040340d03e0704903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191566762 1250 191565512 191565547
    0x60609060806060702040c0c0c0b090f041508010c0e0f1203070219030b10091802030d050c07050405010305061602010b0117040f050f0105100602120414060d0204060302190203 77
    0x1584108290107010500603110a0100e441381500504244030610414001410300c080d01c00c0212a1058100e03070006100400c2c10517514002c42c001d0020180106290400014004c802103101640c0300701031000031842024031680070790003031544a030072703041c200e00080107484080a040c2d18091032844210040118001c400c494501d036044031000c038083c00c25891490007040d182c1000304442111000e0041415101040d5401c40e82079940600c80c0d01c0002540c100c0926041d800290143e000220031201c95010f40090710403039070020210b4103282d940c1c0c00002c056070350030b910585840c2c1110007070080302c41d944d1541c10401503450000748281c0d0280742c0000d00e80c0142044501081010801013020003104095100c561500207080310f51030680441580e0081000340c507414100c24041000041d95070000c00c00e00d00701400c5001d09400e15103042540002c07040d6500080d944078001300003646441810348013400281c1096900180ca8450f910426050840d26030604800e65006009003818403180801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191568012 1250 191566762 191566769
    0x7031d06062407050a0609061b0e1002100615090524070614150103060609030209010902030702160605120c1213060b030f0c0a1502121602150319060609 67
    0x1001d080b203180030700392949030340502c0c04010402c3c041d40c5200400e00c0001d801c01c5140d5070058001f040704120030150705803614078091440b80450a0700d4241100d510b4400c031000906066401a1011800d1700600002240d5458100c2c1d00c4260314615202071244c2d200b8414005031100b6191007490440d540340120a0700e03030620703250540480c00500b14042210940110a1000c0403050310700f0b0605240310820109400300e902c2500203860b02200140c50761003186844101d0385c015009890300d9082a00c0d902c065807009020500703500c1458000340c0b2040b01c02031414001c28030396591540b80d1401107403e07040e001c4060021189450b050054551550303000b802c0a4100c21144001c2c98070b41034074580400a0111643d003107a05000300d90740e6000140d40401c4006012000702c6140c2c0100d030321a503900d181d80144083c61401644442c00001401c4051802008446a0140c01c0c0d10148416070010f10078200008000e448000c01005101d0107206903184100c5071070740d81800b80320850904000808405140c403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191569262 1250 191568012 191568049
    0x70501051603230711060301140111011103130303050604050115110a0605010807060e0411091002070513021b070303020c100306030206070b0105130b03070e0a0e0607031d0606 77
    0x1140c80d0300b018003442410304418101c0e0f00c0c2291400c03032001d8441441e00b00010560b94922040c060f0f06262406004481c140c1d21090310900180c41d00700011982400c1e048100507056503034004448401003c540914071498030008145c4241c009460001d0680b6005000940514200401400b2a03000c00c85901c004025600d4202003400d0f000c0c203a2840c0c804058400f038221441c010001c00c41c014003140d800144d84454551901001007035040c4070494181000001900000344480d20301841c10703590b00ca41728030301441156440303510358000a00500402504442c07140e400100e000035020310300d40c0319921442500c00b40245070303c5c0d610040d403079124041100e0310800c04486859015030080c0c0c0481c000d0742d0054981e50300c03201585040c03041d046003030140303610644810903450912411806544902c0c6d2001d00600040f0345060b41140d1098805003e01c8511919809204410388080000300d12500d900c1e0340218603102c070549403a18a600c0c40c0054030140c0c00c2001040015182c03c140e15248241e001e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191570512 1250 191569262 191569297
    0x80f060604021c06060e030c0105070f0219152d091502070b0f03071803080901050a050c010e15061518010e100e15030103030804031107151e0207050105 67
    0x6481251403c101225019180c50060045052a40710522201c506030a400302d40d1160340080041d0381501444000a28081d208a03920006080500c3d020400c01c1c15850750700b02403a1591140840c401003800000b00061001da1406103803102c44002c24660001e01c61511000324950100911494440c0a02c03031213200706034000c00c031851080140380003c0c402204aaa10340110352910340c120b5105889100000d540102c8440341c1c3c0440d441d89034112544403140d10310300400f040054846401494150003404001d21514a806d4001c0c06180520742c1c41c980548480c08900c5158010903102400190041c04c00100459a440c2158110b901c0d0300900410840304841c03031300c0100d6000f00b80e44c000d513422502c44102d0b00011034100a15141e080c0045811002842400c003205000340400d10001d00040e100030082004640034100c0e404007901c2e400d090b00e40141d01c40d00c94010030340c004521100083c0d003920048144401602807220590014400303005441c0c038007c0003c000313000744400d14031001e0340c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191571762 1250 191570512 191570527
    0x52109061302031213080d08010501020d0c06230702010c21180503040f06020f0d0c06150515041a0301050d03050d090b0a060612153501020c07080f06060402 69
    0x300501d518013510140010b40c0d54813410090420002144646251440745c19610380711075000300002d42c1030f2903060740103080010010404880c0030213021802c0e940d8540c0c403485d4425401c00780d1010384181c0c03881000300c0f0302410080802401c50740c16240c0802080400f0103a605508202180f17005401402c82000c540000000a0041e851140305001406440001000030328181102c0c0312800b101c0160b009d0310882c070041d06e03c0d240c43d400480d0039000000d049401d520000b9005902084255007108010b01c00340c2d440b400860150403044d2012001da602c007040c10415060704032845c585041b00c50207110b0441d45841c010400c2004600001002d10002140e4400b0b54109981300d1140c10743c100d540b00c5540d00344910791100900881c0504400030303c00700543c01c045807117030144401d011130703203602545000e15001d41c940b410501d000345145e02e603804d080800305880f111040401803034144000103989484200703100703180c2015a44140b101c0e410607a0355130300a207004500c03564000c038150340c0503a1341c100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191573012 1250 191571762 191571769
    0x8090a0228080d0f090807030507030b15191e0302030c0d03021203010e0402181b090d060e0106050f0a03080d02090f03010c090905090114010311031c052109061302 72
    0x10715005240c1c1071152844480b45907070f01c00c6550f111004141c450001541d2aa0755080d102d40700c41c040942284d21401d410030005000c0208154401d00243c81890100306e2880000c00420f0300381c0d00f070304400c40000424003243d41c1c41e160383d410000744902640d028510f168042030300c602030102c5c030510032580c0c0c007030501c181030090042484420042c0071440d6a9130b114503640c001104181c800703030b00411755107691a800c80700c40c000c0e49004480108815210500c0d0801c8458194032200d82c02d504031610903c8200003034428001e07111243c0302100040340c000d0401d0107000703079030400c2c2004510036485004200007007142e4908030703003580000c20700c0035036180841d8011072031085050000399019072074a031035214031a82c00901c0f402030b44d0101006019a81764040701c20b09035000c02a0981c0345420b1100108000f0f05140340079007801790007030180c41e01010b00c040c001070003035040000100882e000066010b001450018911000c00880c0f00e4a4081d040902e0426660080102402c00c000410304110f4203658 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191574262 1250 191573012 191573089
    0x6060f0a151b050f0706050a020a060903120f0b040c020309090109020304020406170a02010809010b100e0301110c0303010602192f0907030209030c0d0305190302090a1508090a02 78
    0x500071010b01d11102c030946811681c924003403803407900394040d00750041010b510800842e00ca00d01c1641c000c1c80e19541c941c0342c1d400200302054003141801040701c1c442240c2c80103030088000c410f41e08070000410180c80010300055400da80d488404541040042014641d102c0c1c0041e41503a5906d41f0060700e036a2244045401480c01d5085010081032241c14044101070015102c40690300c02c5c0d8a94005403075140c542e50a84003080c5070300d47d01c07078881000b41d2500f91150310348622a220050003c1003552001000c21082c0d8810098090150070000c014003180d070b01000040082d40d80146940040d40240d22010140d10018034018100c2c0f42c080402b24034009441204003854200818030f01840c100400043e0082d445000503d0281c0255102007190b46400000c00b4207054041d100c0c1481c1100d00074070102400047c0052409055082c0401c3c2c0e02502ca041809010303001c1051403c40e114103e01005d0305880d40141000d546501040b507500c01600c601c1001080300019404050700350820b07040880d41d04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191575512 1250 191574262 191574287
    0xc2114090d140f120c1b0a120204020f0403051e030424020102091807030e0a0203070504180b10090f0c0909150e0f0406050c0c0a030e0f03030c01090506060f0a15 71
    0x52050309010300104100c40003c2089642035400c44950946c40c43d0b00c1c0d20107211507102c407a8000d044138410800a08582c1d446080f4610043c00180b40c03104009000c1000c0d08030780c0090384c2d01c1e44030a194503000c0180d8000d044200d50300301c00941c1090300d0400407a1802c1150428000710390710140070002134078000d40644514403001444e074501e01c10325032180880c10f44101ca000c40001e09103040010701020205010019540103006409000d0600c4180400f8003560180c001000111400b400045010780603140d000e03034a0030000d40b045901c1d18800205079800d40440d02440343c5011200e4400c29080007000d811590075a102140c0001c001c01f9101c401030300c4e584010000f41902040203038400170300e1801813042e8440c020400c1940c60740045d882e0b4500445201e0b1101d0f41c80a82c1140c0401d006415164034014010300d00c1c8000c1051801290840d0403100344810145e444e64141c0003040018800140c4c03240c01540d880041c507281d100000c044d5000c030b01c60741d924035805017010010700b8455886070407030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191576762 1250 191575512 191575543
    0xf03030c01140a06060c08070f0b0103030c020f06030f06150c030c01020c120a050a05030a060f080f010c110d03020f0c010203010b04030b010803030103020901090b010c2114090d14 79
    0x440c0d1103500490302030401d400005242d8011000020071800b010f204090540722035540e80418035101c0d6840e00303095803094a0940d8685038031020a40000d9800800f580a54800da6824202c5000d9105100010400d08001841804280200801c1d00e5036121080e502c030340100e8402200302c1d090090f81001d80310740070266880380000111080d0f854015001440b440020004031406241c40c040e001800e40200181c5d140010010054541e040c0c2c414030142d500310045d6000022615940c072242da400d18001d41c004003844d004951401d14403d0700f842982d8617a040c9040000f410002d140b41c1035180c207541987c1c00c0a043d0301045404401d94400c0030341c2d542c01c08501c0210f580703584038030509900d900103100c101d80303149110002250b01c0d0408425207040302d5000c0e00b5001c0507400c200d84100500703074002c0c9180c10000900905004a04143c030501c40ca84038803030680c100d00209038002880702441c00f54041e080e85007084a0042602d0b080f601007207032600000f20000250b030746007030107040c0b000a9044401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191578012 1250 191576762 191576767
    0x15090f03160302010806040c1b21031d0105040b1303120c020705032503031116090218010e030a030e120f0d0e0f030d031a06070602031006080c0301050f0f0303 70
    0x1a1403075803104041c241c90003601c460f0358a50380c800c100000c2c0d900d13922060000901008200c0104103c00845a803000e10803039070306a21049910580d442d094008084400180c1c0314a03414826014000307400118031041d00c003d00552400c0c1d201d0318010217015010a0340e403034441c404001070510405656507022050b08050000d2030300ca0f44001c0d030314484d0703004940c424003d036441c02060f80b440320106840e5854024400003121701d1a2000d4604404d0f90192182502540030700510b4102e00c8404c100162025100058440703107032074580792100440781c001c1814015036000d0b217200c66800140351001d00d03501d86420b403159428000402c000c52125441c4a1051054588902c0d4249c80850b0100c8810910395501e03280c10402d0040002c03622840c48240d8042d00040c0464105600c44d030810ba00301e05654000714504070084010a000d81e101c5032041d00d1043d808404e001e24003604200c000000d0000d4585240c05082c1948000b0742840103100c1c07144184001145c1c01c5c0207858409010a03c01402800c1d84d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191579262 1250 191578012 191578033
    0xc0c030903152003040303050610020c130219020d09090b0a03020d0503090306180606040b0603041b0b042304020a05031305070b03070507060c08090d120e01060626010515090f03 78
    0x701c0b04d030803c0d02c088002c00e080500040460801d0b865040c03c0315503070b82c02007004141a800f8002034010942d0095450741e0200405240070300d00c140c405840317003032039401040c0c01031820000902180b02c641005000b94104448600256600c00b80a420b4030380440d055011031905103851480d5116151b802a018000d81007040306603007108d0119020540f0460583e010b507a1414104801c507884003000303c1c0d02a0084c000300d008140d415110200280c011900d0180d580e0300d4020361143d5030455401003444204030807009a0403007130300c800c2428602d020340b415424052943c0000d0610f020050a00744109181c507940401e000301088007200034800b600000c0e44d2810070050040440c1d01403c4151102810844c1c48404c5512640d42c0d01c0c45a83c1c82000380040f031140039422211144050000700183d0788424010380b120341c0a10a81004108a80342c2d000120000d07489100c01450700450316001c500c102004216948698956410f040207500f46250386016400008110f20121090260140b1403c15040b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191580512 1250 191579262 191579321
    0xd0609050f0f010b0f0406080403030905070b0c01110307140c01111206040b0d050c040f090203060112050d260c070b010e0702010e0111090d0510021801030c0c03090315 74
    0x2030141c01c402018030b60503030720350200e118584240f010315800924100310810101d8032485949800c00d01c6894081514210358481e2031402c00e1582040c000c0b50000540e1503410703e024815580b4a0289444050075450002c901900b0405a06480f0810303000c005801d80d050350081d4407100040202d007401a031942c000002d112113081e41110072500503450072990811a14104001080702d503402030041c62020008014000070784000f9840c410882d0704c0b51105401640c0c1032102e54083c1003800081d840c42c100c2c0b420498540021881e0741c90602941d002c4800000b00200d50980d041020f03000d00d064280c640e00840100d42c0b050520281c650a000c40012a41c150700565141c0501c0480d4001c3c80086a007542c03803402ca4100d2101140c5003901000b10b142c16050545c4407440c80380c0910195842c014040e50701c0b90590b80300c40c03022085407041d203406100355a018803030803469006902e421040069199006058000c5900001d40045501d94004001150a420045481a29031580030030814103039031f076 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191581762 1250 191580512 191580541
    0x31308030714210c010f0603060b03212d0d140603070605090d0f02030d0816050a020307060f0b0604060c0510090b07030506060d050124020607140d060905 68
    0x220b031007040b400e0303040e49400300000d91035000001c0c1001144864503501c01c07041555000c494018007a5489070080190035040e8030074040154002c0c640460075400d6501010b080605240340b40420f0724513420810b40d84441c0106440460f403000000d05016018640122001500c4510054010300c0000d59a2003c030302c0c54106101c00015014499040e031180410180c40303070058052540040c0c424032607031055261a0080b069032901a00410305c030340c1d140c2c3e00030a0030a81c003052554042400074040c0a00e500c0e083c0014110b0102c83d1034903508021900400949900c01c500c4050300c89078440011080c0822140d010412841c001400c03243e54641d41c0c007000c2d000c110300c1130081d11580602c440d440c601c814180582800e03198400d510702c0260340d40840603401044081d00349900440280702e0310203051554403c2e1806450120b40324090121507180781000492210290400c41d04001d050040050b0012074640d60420940da15035244c80e118102c84005181c0d590000890b18201410300680c4026103c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191583012 1250 191581762 191581777
    0x40b10170705090a031b080309010c03050904021207110d0201020703050703030507020c060c0a0606050307080703030f020102040e0c040305060a1407031a0a0e060307080c010203030118022109010b03012c03130803 93
    0x403412651f40c4c600201b03450380560b10b14280815141c002c5040000c0c07082c4000c0800c0b110003800181084000b0b180003004a2049481c8804625000050015034000300030500300180244001e40c40c1900d959401000c034042e444009042c9034440c404500e4140c000d1100d0380e0a0345d0080c1c00244c6600e50050320540c0d52040e54010381c0d00524002c0080b41e0340c20082440f00540e8804001400003d203542c3d801c54000d403080900004555080c00007259400c594400603004201b070a08141e161402c5080090030044050600d40c446480d00001c6281040303884081c550200090800061506020131410810410042d0099000100600c0480c03074951121409015400c1034044402a584869006941c0e51110070a603000d6030040c401082800d55026001650b1060a00007506006031008001800758845110744101107000c030401c214400244103081003460120000e100c0860b000400300d42a0061406000004078001c24085086004000716100032100c90450b9035805d81d5891541e80b20b402c40741d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191584262 1250 191583012 191583053
    0x7060e03031e011d0c0415030b1c020a0b030604180506010905100b0f090a03081206032404080a1b03081005011d0904050120030105040b10170705090a03 67
    0x803004810702c1803203040c505030f440242082d000000e00c1010b8494010b4000c003110f811600070480815032a9035054495408440d546000c10074020b0b82041088180302c0c0740c0d43d111145402480c103005079841c29800822101003a60302942ca40300c2c5004140034100c10505109002002076502082140000e0001e0407034100c101c040080b512039480c091b00307070813841c8500c62442d0002d00400c80c103012081c0082080d0329000f00266002966a51002c116401c01c45030305414640010030080181001e00407020380000144801c074890303151601d0300c03941313080c0030340081d00607000407800c000418065400340030f0005510b241c00441c1c41c07452900410300b100c101ca04001e041c1c0003400004103035018010b120f40c42c13021a120451100c010348203000c854000204295540e40d03c48483d13201c9140c81c0301d041802a1400e207440766030796050009200c15100b6080c4a035000d44240111006171a0f40051107008110a01c40d942400c1c0d11402c03000c450031b00484804680c020580301001041000380402c811505440b503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191585512 1250 191584262 191584291
    0xc08040911070b060405040206071103011e15050a050307060806030c0904050717061015020c101808160509040c1d01060e0a140d02031002030c1c06060507021507060e0303 75
    0x101172105655050720003c0d00048103100303800c00503015021030030500e03102600000e004503104100407d400210054118940c0e990300e10b03c0000800c140d0000060031080e03490070f506626010110f83c0c1c818403881040104403010011a0351030703405000302070008800608122039810542005a02e1f01000c2c0301c0e6400903000b21090849015001c03540a10403c0c01480345804149031014915420341a83c100070114004d0445070708040e030300d424481510f16001c1e9607011102d6080b414280b007030785c400e03040104284d11000da40c20300d81d100c50300a041501c800740c0d100c042c6900d07607107840403564003242c109070f4042241d0346400d10018282c0703405604845d1140d4a110100c80c100051100e20551402003000d02204e10040000905044c48010311480c07000d000c81d203031111484580b0f0101e03042640c01c1c60a00340c6c000f030f141c0c40d1010040a901100c82c40c6400802c0194a002c00141c4284550030300280100c4c100d81f0380c0c100702c4503a00c0c140c61203250007460a001d11081e006090340c07260700c2100c05d40440c8021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191586762 1250 191585512 191585521
    0x13260105010e040f030e1306050109081f02090a0f09020307140306090f0c090402030a0507020f07080c19030204022a0c0612040503070210020a020a0902030f06010c08040911070b 78
    0x501400e81200e500320350141a0380c507580c840181c032005030402031301030000c0d0b1103110341d030780d110324420079200508040300082160501000400740711aa500c40c0a0542c0070141210120389000c102d041e034a25180001a0303500003150100750340700000d6001b150540b403c0341000408a00e03e40041d0300c618155a0f0b01a882550048408075502040c0d4019411a407100001001c15001824484d002071703140703005078102501e040004060340d00480d4000b003900c0c0c8a009100d8125010041e40a40400e00009031011030b0500003036541e10b04084e41054410010090a00b0441c03403c1d20512014503000340040d076aa0840042502060b00e500000c9110000004580310402e10080b8000417940300050049251084440c0c0841c1c540703102820503038842c001001603400507950f58008038900041500540101551030042080220899100d82031640c010401c00c00603822155100d94481e000f420300c40f16014241c20070300f9060250740c01c060009464034160f0b1110381010006020117911036052009180d54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191588012 1250 191586762 191586839
    0x60f120609010f090f020f22060f24080402011e1d060f090603040c08010c09081204030c051002070924050607170319060308090f010305061507060213 66
    0x140e40c4c83c044c00e00321042050300300602d00032420690380300c1d000b021900518a0750310549216600401d0841d00c083c1d80d0b020070008060503010040041610000c0740201ca0a25050b0002c280142c0803101d003017085500010302160702079a040301004080c0d2011441c2c0e00c1740140050060405414682088200d204420340136280400480b17260118401c402810468a042840103e400281044031900440c90700464000d10920466094542d10382d10380068500d844a12814154801680a0882c001f0030081c00032914594944046401c180d40150036402c41c8a0201d0030301c202504002d007950700b002e04a0301c00c0148041403c6420540101c5290010350302d504001d00e51080c8400102641e0382c800e40088105a088060b581c04081d80c54144909080740300510112001600101c540c54408915110181031400c07032001010400c2c00c08001d94245200080c0110350103903a201004400060344004100490301696405a00700940380381c015180c4048a0020760014406900e400404403500070820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191589262 1250 191588012 191588021
    0x102061303120c020a12090e0c090a060f1b0605010f05180703021c050106021e06060918032215091202010507020d050a210e18060f120609010f 63
    0x603031607220410b070107403410306a00c080d2807500390032010b601466941401140003d84610304107a42d50340c0700b040b41800c140d814100080d01401c1945c41000c14444400345440b03d1352403500340c8809081c007101f00704400d4011540264108603d403010010000e25104200050304074905031200740c2800c000540d15242804501540105220b00c0707010440e01240b9094082c0d07005015000240b00c2484009240d102a54255031003030307001c000160702400c00003d000141c42840d50404180c0405850341d800c0080019080b004085e0032039075150b0090a80b0746918004004413204122011250b01c0403401c504106081c0c0c0c0001e2003130000180306450550400b5101e003d400090310412405213400e980c25030011541c03a005203108a070000c8480c0c0c039074804980c0400106564510a6240000300405822160000803e90001e4000d200c4201103070103c9544480b01d50485440c0005045203a03a192000201007891504c1d1a035042000b901421001c2000800d00301e10500720903000740050400a401881143c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191590512 1250 191589262 191589301
    0xf1b010509190512032a061b090d1a07080405070332030315030111160501020702040e0a0b0717010b0705010e1c020601080304052b20010206 62
    0x480410840e0352510700580901c02c40c00e00e408a0031071180d00c58010915000850025089550010840780030082c0e50900382c2d05111600100300c1000b440020540760740781d4001d042044a0f023640801300f20142a144151404403000038a4a0249101400c00040480b25400051094241071000030009405960603500071b5501000400344280742d61200040d4074170080c100b0345060a844581c0e5031440c071420040003080e030a040030716a20704040d041c0c0700151100030540e074083d906103811030721000c1d0000c2c103440d001003125054000e44265450038500a11031500000e60080c030304944029880c1b8001104d0392420b01c00d02c845101030301c03030710f105680c0e2464520812504192000c0140210080c920103060924425000032804d515402d25403800d100c0c40c200408170846a05070402c014660400480d03005001e1040a94581424107000c07440841600315018a0f0015060560400010f0301c0800450541c0145e6044001e401080181c0680f000c0e241c0030038014810040419070041c64443c503440302 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191591762 1250 191590512 191590517
    0x41d120702030d1103090d03080610030c0518180f0601121802150c0114061003021c0b0d0503070305091203090d0b100b0412030201060e070c170d0207050f1b01 70
    0xb110755401c0111080303c204002c4e02e4131804284500300300340d00c0743d20a400e0190322a8a03070140f546054424884501102500d440070541844bc41241060300a4202c2e1551508040900e00c4c01040030086084004036070f00c944504030260003040807070f40d200401503010b54003d9031034000a407640b01c0580b0640305c1d656050f14400e03c041600c2c4005291064508a4042c1e4480c852382c100b0b034544544908580450200140e08000c80303081080d245094044e052020107141021814400490007000c0300800d12030344a81c1081c0d58441161a503070310b003102440c0050b4001c0480359a019076140007451500060701c990b000350900c0c0000292001d000c001d8503901d94024100d940641d00740e0315845100800517018030000211900041035281d1408024009060180c0f0400d842c03180324980203085039140e81c441d030046504c1c40c040c840c8143e0300100551005400c21610300c0f0f901020466070442380714801c0e4403103c052002684000300180171582110704105541520800c0c407001c44613001050314020010b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191593012 1250 191591762 191591773
    0x14060c030d020a1404082a0306040302011e0212060d0804081f2711041e0515010206160507080d0c0e0a0b0f070602180301092102120414030a02041d12070203 69
    0x102c83c81f0401c0e400c0000541d1241022800c1b0720360702103424101b007650141d006075151000c04d051100d814624074002c00c4040800c45c80c149000080d0030710b00f00080c000501c1881c030208050140007005040c1c0f0064103640381512507620000003000c90714000180e005103002d0070b01d03000e03000407003401030781c05441100601d6a0007551540d0303688620010a61741445d40c800c1d42e569a0036080100d44844140380302078901c0c00102800c102c24520b401d44003106109045620a100704280e07200c0b00c43e6a003420760824200b003a01c0d142d641c41c0c40380c5103000c0c3c1c0b00d0040e4000e00c0e001c4048615507016081483c1101e050380c20101c800c0d2103150082c2d15114504015090100030400325000540c59401043d01903c19804c0a804080100000742528074410050300d190111103c0c48411403e0402000e01080c2070740010441c441c0000480c0d800c0340554403030180c007000030304910b603c41d44090248040961b4014005c120400c103503000e400400e0302c1d407110a0b84500c181100055008010801c403110b00d03400600400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191594262 1250 191593012 191593033
    0x1611010c05041509081006091409030405060c01020d090b0f0a200c010603150212100e06060a020a0c0e150910030f0507031b0501170f0114060c030d020a140408 70
    0x1010305001c110b00008001040d000050720405c184035583c095002035002051075403400401d402507401520540d10130f000d0500a20041d03540c0001241c00721481540c44c25101c4e00d80c11010750082c0076130500709220350305106940c000c008040010340c2c4299869506c0380034540303c103e80e5000b04c400d02c200554210080c0c64030f601c6084640400781c02000f21490002c10304c99241e07542c0a09000046100d000a83d80110303415107031218040d0400d50180e090419000302034a000810800c3c01000341000b070107010000703080c10041d4401c0c000200c0d8150001c4209083d981d441c81c601d520443e084460170342c5a40c0d151249482481d082508070b00580395032800c502150f0540c2c44a00400c85613200c00c540610410300008002101c04240140c0e0300c5414810a141616040c005003000100c1c1102141c61013a85080000f00c1d03011002031410341d400c3c1040303040585061000300d000b070311400402315418800464510700040040e00200401000d40d502c0000707200d103403001d070703601c6004d14040c0f401d55401150314203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191595512 1250 191594262 191594279
    0x8070311180f0d1e050c120601050103021315080406060501030606050403060f06080703051606030501030218190f05151c1205040b07030e01090b04050a0b0d141611010c0504 76
    0x145101240246a01c0c000e8a40e03580d500510309a50041d008200007014800702444411b002c070803000b440035180400d504582d00e040c940c840b5014000e141c103255022036450884070601a544018002c0300300e0716480b403000031501801900080f201295050b01348903001c107680d48a40140b5049130351948800b400d150a41e035544d0f02a00c2c10030206000c003541c0d1440011303034807001c010740b50045004e8000b034100801400580480381c8d8107074121038281820072004100684500c000126810080d40e400001900d42005006006004281b080d000c9800c00e0380e100079042d40c0da402680a800840d0a40c2c100c480c85405210309400c4103c2b0702480301e5004844100442d5130701114030011007031450310302c1c035242d00e555080205400c091000d8001485166803c1d6095030850803190140141c0e204c0641001d05d02800903c1f010128000c81760000000304039803800d210641c00c00b8207900c0f4081007411051030904102645400d41d8440440001c2420b0a521440788042c8580e5403044407a58400e41f40c81e00300b0101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191596762 1250 191595512 191595529
    0x120a030e0307050625020c010f030e070b04231806060309010603080d0204180b0604050609030c0d0501090201080c0a0207090506190303030204090b0f0607300807031118 74
    0x81010502080011000041041c060300b07118441e1701140c004c010039014240d129010305402c4c8582076502181c2402002c4c1c0c1c110070200303407220440c60040b4000b10240e403501d003001d100358018100d42c02c0121340072407400326503500181c8140104482c00c21210a1508115402c65107404841c03c6100c05404a605400e00d04001c6501400c0070002051980d92a070f40c015103039100d6842d403140542e01050501070207554020744191890303500414000c00c3c1a03000051400c0c8241d10680703109184c0003504000070746090004607607410f40103004000c8446603040581c044c00e80c4503800ca00040c90b80001540c0c090501c0151654040e0a030700070080242090b811500034080500440d41c81200484000c04003800600c80c1c0c0051031203030b500035840381e16000c0792000f5a0340b0014007900c24522264590b0158030740c0e106480007070750010256a0b4090600c040690119486916120f44a0480b806152083c1e08144071340d000c0d11044c0d41c1040741e081c08410010450003403116600c1c808400711054445464000e05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191598012 1250 191596762 191596781
    0x30201111504050d0e0d0b0c1b1c03110a050d020310030203010207050f0d02030c03030a0f110c070e060405091b0105092718062a03070203030f010503120a03 69
    0x301c03581881c40084035040d0800072101181c5540c0b120450f2000c6a51103540000507800c02e8525020120b0b007070341c829280b00002004000e0105021a400c03400c0319841201090545034034041c0c500380382140e0174480100c21814104004242080300101021412000320f84121440e0307550141000d4080c004e2101951010301060480c11101c400071001d640c00388018251141303d80c1c010b10040080d008010b0500c2050fa070b4520a54100344851243c100012003282d5001c40b80e80304c00105070100018010041c103c011002282902c040b0711901030780340025481050702c45111400d4929920a401c000a5600889411000f500030780032085a00415001842c0c41e040141000360410581c0000b00e0b5200c00000354180613000d00b9103000038501500d000c1290003902980c0701518108641d86002e5944401401c0701205900c00c3c680d40a40401c2850390b2000800b500401c80c0c0d480c2001d400017540c94000366503807081030f03508500000c0e440c9400200a11410700c41d402c0e8508213180143c00381d0040450f0302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191599262 1250 191598012 191598047
    0x80a0b01120c0c0b0106080112110a1a0406270605090d0b13020906060901230408030d0e160e13020f090f0417070f110105070b0a050115020102070b01030201 69
    0x44445000341c40d01900c103402219907a0b2001940d801d09180f9800b1006030b11220134002c0c80b0300180700c2407170b24810203035202d038208100110b8010000c0100e0001801503110410850348007035540075045070040100100e03000c1d59250a032502d20250100b900c401c1003106400c0d07006074800c08000f4a405040030380200c1e40c000746642041c0a40f5110b40e26511421640c03c200f4003903800c1d00d074003140780000e5034a030000030940710303242071104000011300b050030000101d81351210500c05030b0002c201104c040301c01401882007941c8d02d40c0e1a00758428003034210740310004d045e4050400802e00c060840c00704981268800c2010100c1034a032018481651070300c0c0c0034240e81207550011181c1d529142c9411480c003411340e0b00512221490039091007000300d03403613996410102c20104504408030740c2d50400c510780c039a08140d102d60b403902c0d9480107841030310500780e0040c1994010820400071110070f6000d141200c4000f44940e000244c1c00746e080b4203d2042c6d82d00182010100001070000d940b00300c000304049034a00c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191600512 1250 191599262 191599277
    0x1b030f090c0d060e101814190302010b090610090b18030a150b060708030c03060d0f0c0807080708150406020408060408041a04080d0305060123042301080a0b01 70
    0x50002c00c0d00701c40c04a1007034a2681d151546200d0a020400c203403008040006410800c00e0b054000241d4004500703c005000440740d16070000c1c603500c0034856843c001244c00901d40385807280f407801a01034502180b40d1481809030301d00240342c50522001e5009240c1d003541d100301c0c00b42e00b0114003103816000106100c0304410700050105460704c0c10484800c02a015645034566881381007031810070750b005148030300e0046005101000020f600401602c1d0000d80290300b07562243e40300c1c0c1c04600040300d20440904402c40c0c004818060144c290ba0b0501a00d039074400340e482654590341e00c0341d62414144181040d581c0189103015005e070019101541051240c24090301d4107960b00611481c1c0907041c0c405483d1500e0001d01008202c035490102d07030b940820401e50606013490700c040c054403900d160b583c0740e040c180c40303400081240e0b1145040c0482030242e4140c4d00c90004141c0a41a01d43d04280a24000608101402801007698815900d00ea00d4140e4800c0e0303180d915080b110010340100e0390f500f418401c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191601762 1250 191600512 191600533
    0xc0c01031a030a080c060709030c0e0601030b0603010311031b0a0909170a0207210b0622020a020a060e0c090c0a050f16032c0d150501060c03081b030f09 67
    0x10f200307040361540201515620389820300700c8281003060181c410020700440810400024000c5c40c101c0d41100c00d0080c421400359910300041c0d020704506403140b64494000400441001003007140078208190580403201841103e68800c480101003d00702940501813010800c495002a0071040c8407501c00c1745100d180d8a01661280c05c0c64000000071009600480400e01c100c104030080b44044610110855a0240c0f16844030000751901030074180c0a00000510002d285082c03850080403469900801c5640740c0c5040c40082d12a41015022074000c1d0612182442c0580d0000300900541e5008010702d41342e03144c9424a9000d544821401414402e003440b0340c5902e101c0343c0c4080e00105008114444180c1030900e0018a001610029100c0c040003028169201088c0001240392801044c0d59a2111a0250400d2143d274056815070b801258245000442c00d83d600480c5804468440e441d160300c0c41d103510b03002c0c40a26000200400d88c8040600c00203282845601009400c00004400d98111000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191603012 1250 191601762 191601769
    0x80406030c2a2a240909050c0702030a03050306030d0306030c060806031c0e092401050d020f0309070e012103080c07060c020601080f0705060d02070303020f070609060606050c0c01031a 81
    0x60f0340060388039450340c0f5100300b000d1030800e407840080303992032a5040e100003100d54001c0e14038044c501541c10a955140c0000355400512403c40346241e4004080300c4000300a4a00141250300417102d180c060301400d480e111095001c0d025a1050b04da0116195840c20306080084070708080050100307506208001e4000c142c81004401d0a482021076610a0600c0d0f4034481400300b2940081c02c0341109000b41104070005005440c04d0f07100b0b10b0401d2030520b0f80e540792090b011020740070701e8440c0b0324203080000c2800541003001544004440c1d5101c24500c0c540ea840a00c01d10301c0c910f4580840b600304040740c0800c0000e10608100d988040c55000560a260980d1611800c030b583c124020005a03200a0042c84050020010840140001e0005000303243c2010003040ca40d00580b654491110740201e9204105030003601900d2600600c084500e4072081142001c40150440e000c0c150386103480c001c004240715115008803407410680c1002001d172544141c00440081141c22200c91010040b00f564882564 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191604262 1250 191603012 191603063
    0xc090515040e180c0909031801021f0e0f01021204060c03060906030302010e060609160c051203070c12050906030708040203010609020a05090108100302010207060c1a04080406030c2a 80
    0x5440c00110455100d00c040a04d181c50710080185216078290030410208500020445617181402020010b8803034410700180c2c90440c103910a000039450a41c0d070382c41c900042e540030150782000e04003154010420070350040e080307100f41d040910a03000340c1d20004e408141c0540005950125031715000948a0341d4611400456602d0381080f00140d444951001652508001003608101c003260080c11900b00401802500e082d400c10701c1d418000c3d07545ca98010b0000501c484100403401d1b1000716078910308860020400f1010310401c41d465076074109981c400704c3c812030a030365004002410503440c0da1540001500d43d0b6000520403a4190b40300d14010545900d940090204141ca07134840c1c54450b1031017400540080d000500c03140c1c500d1111b490030001350b0790005104084400d6414944156910360800602d648080014582110203600c1803004000e41d0400810072207450f5071b402c102029800340300b190b01500000c0003020b000310162080d078000116100c0780150714451808008001c002140a00803030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191605512 1250 191604262 191604271
    0x9030c060c050c19140f100915030e07060806030a0c0303020606040b090603060429010b03010303030f02030f0c0c0708011104050906091e2e0312030c090515040e 71
    0x981080070640410804016103803400ca4100c03504200890b8000007000d00440138429001c01910aa0032007100ba120a0390840560002a0512541005107400603042c11414820611809089030490328554031030701c100741d074154813840542101e0345402811517480c94081d01d825494010713280e5000008400c94040e50003144290040c1c40b4900e801800c0000f1544c0c404021360082c80c0c81410030003e41da001c142d82c2d07445507100c00b40344030001043c20600400c0c910f900506c0035030080b02002092800912002d103048038405c0d9030603c162a03080c9540e200340c1c001541d8008030714000707002064089038204040c01c030701c406110445240a40d241d001a0035a00d06407001681c8000c006003d00240c1407000c40c0385d502c50030640d055401414281c0c1e2600000c028243c1c000c2011059502082203140005c3c030700c81c003280100781d04209855480d426441c0c10a80742c81b040340c00843c0000e82c0212a802400b401b66200c04948444810760310f00418800518040400c00005080400001c504102c00240c3c80b0f005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191606762 1250 191605512 191605517
    0xd0207060c290601140a120504030c0510200702100c031103040e04060e030a08011a04090c020114280905010b0604150f0203040e1f03050d11060f040b1609030c06 71
    0xb1800e0603c005032440b68010090222000104100041150030100e540030100d424840040d0540d500c0c1001c0307640ba98840c0009001f8000c0540b1a0015902600203106a0300224254000d0391840760090100b4402c1d448001d40006012010503165809081c0c9019810301900701505151100e0720100d0443e8800c0d044640995081c409100912105100740d031044007502004501d8269210b1025104c0c0c50140306044030740065002c404d200d0070000099a0080412031400d0240000c0035001034040c01214540c0004101110300065043c520041f1a01a001802c8824940407808032401c00c003403c10003000b540c0c59034840d10a40140d80307545001f00000c000404400c40544100700d4010078050312400d034042107500c107000c248502000602d00a0300400c401c1c0c810801040c1d2500110910f4246600240542c000c034108400019005080428000204804ea80d079984e030703a07880c91010303401c00d44000d07245810f07060010326203031080340319030389a0b0383c0c603043c80e41c4420390780d50b01c110240803160002e000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191608012 1250 191606762 191606843
    0x1002030a060311040507090513020c07060c0b06030a11040b010c33020301080601090c030b0d06060f0608010b180d0b0106200a0f11010516080306030606030d0207060c 73
    0x62145045400c0f5542c4022078052046003040f260042440d0180d001d075a2180c1020090750500240560464100744c043d8400c0e240b109507200c5c805005a541c074103080c0c4403080f6210001741c0d00d00d40071840d140c00f1075011210500450708036046c00028442641e02c64140204003441e41c01042d00c0111351810014041720188070345000350514a410050f400c0c201040328010b02c0103105651006c22400e05607030840000150f61103414901302c0141c02a003080541150080300381ca014003980c5d4111000b540c00303241c1800d52103a0340d4103003101e40c15802d11558140e11814040101005a03042c1031150500005000200b0300340d00b601d900800080030392100000c100056540c2c0880903c45920400940c00080600004401c80e101c42c1c0380c000311540010305502e48001900c145a02030b0b41901d40800603241021030200c01443e10040301d80c81550400e119104100019066180025a1201080656014010140c6441d0094515840f004001c450300f202084104c2501d08946c004030140c000407500850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191609262 1250 191608012 191608019
    0xb180a12200a020d061b08060a0f1206050c09130f1808071b0807060c021207120f03030204030b04051e0f071a0c030705060f07080123031002030a06 65
    0x3402002540c40019203030400c924204560303280030840e10001070301a5a04c0000750102d14005d0f004007005008003001d020140c0c5040141c65106a01d0342c420802511000301454541c5040f0300d041c8551710815941c07021000b1650002051500000d0300140d00c0150703142004d00b0000006d0071642c0d0210300904180da070b00102c83c2c2c1c40256000d02480c0385900040349011141c5a11800007900c1441030203444000ca071050b010013442da04600c48011700301001a206407549804000303004900c080800d0b40b00c0d0310f5084040720040c40c003040d0311086603140010011350031466a9504162a80c450090303060617400e22000020a074001006031040c1e2051000c0d0401c1c1540e8007142da01c01c5400005045140c0c480b43c0032046522000a22406403444056051031008268508000078420a821000c1a00002c1081170403c00d0001302d140c081d1149545207a0725075510300c0308031410700c000d03c1400701c0b403c001814940250041c1002300f07103407540a0140ea50031200141103600342d03401680c140300d1982d1b4501042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191610512 1250 191609262 191609267
    0xd0e0319051806030115030c09050316091a0102060103030f05070213270b0c0c0f0312010f060c0302070b0901201b030118140709060b03070f020f0a0b180a12 69
    0x42e00c030901150b5250440d41410300022518142e42008018940d171070b0501fa201c1c90050304000002d05005003120030420301c0701640421220700d8400ea2913828200003010b1051404000c12030308424042e402000c4580ca1514121040444107025000784201000110b000d0388404106940c009400e40c40401d0b80d00a40300c0208041c00c0084040e00414a041d181800091000e800315170082c01071503a440d21060001092800d0054000301c40b1810301c000581605040f40d101d401d02e040340d05108a8104099950704107640340d24440d040200160030081c814040e425403440580082c00c0c06250031200034462031500c0c00341d0700d401c0c000d01086a200030b80d80103544220030703421164a1425002800000c020001c1c00e100c08036400002040241c1c55034000c0600881044040c000b4203a11a0074803684e951001400e0302540103850500000e0000028030203410300001c2d02c00d0f266041e1400406d60720800352236000c41c80b0b0000d0465001082c811007c441e0b03001c82040750704141e9016440a07000041901c602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191611762 1250 191610512 191610547
    0x1b0f130b040312020a05060601030b0402040f0806060f0108010b0904020a0324031e031e0224090c0109121b17070f0f050d060b0609090a05061203030c0d0e031905 71
    0x801c41198800030040c030000344c6c0030400300d411134030a0801003150b10145001802074081ca0700100401c2e900b45a00140c54035001451500411050319108151801d02004440c517030024066881d4101003005005e2041c20641d005100510301481d0004440141485410030040011302140030184112000e00502241500c4451980c004401031098500f40b558040c044010070042c0020140c1c000c00740f0041107000b40400007200581b206440c5502250181031060b0380070545007098240305410540f00030754014608542a25102e1070001c09091311945e9002c001c520102d000f800c6800c40d202e0006c1c0004d002d041c2844d80000900c003a0028070f003400c21a0f5811038540c0e01c1140a410380400c108040e4441c0e09550a03210340286010442001e1200400d2580c482c0c08a140d030003030f030180200002000a0342c811400b540c022580f99034501c0b100200300303a490100707070f4030401155000c008410908280350301045240308814252424081702c00c4184401028140700da90100300d00281c00031418989642 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191613012 1250 191611762 191611793
    0x9191b0b0d0f0c0903021c050601061707030b181003020a121b051c0501060513050702010e0a03080105010c0f02030703060510061b08031807090608010b091b0f130b0403 74
    0x104040034404034000c4c40d41c40d062002030b002e078200707080000f03512001e040c4202c80182c2001c211072065a4500d0000c108081f82000c032600300350250040780c0c840d84a405545400031009000d18040240713426a10400c60000c1c2c061010184a544000016160200a20000c00c04102c9040e0707600b40ca07003410b075485a031034024a8448809842d01b40180e0b60303001c0c014060420b1840c1c0c0d01e145450f207490814010146c2e0342010b0f5209030081d882c0005000c0ca0342140c1c2c840d0b0780701c1d40248060f1160301c50f150360744c031007010b4000c0208003440010b011a51081002d00c9103075018031030483c2030204a40200741000c0850f003041c1da0190311031f000c0024483c49020104010030903413030701d01c20140140282324140004070400a05440001002c40d100d040200c0411101c0380400c41661559607480d00340b0f600510051150b0001942018003c03c0640307004001036102c1e9203800c2081d04c018030303680ca18400590000036412040b01d818007200010f00e000e0f18280000e4617008000c16a5107040d4100141031144000c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191614262 1250 191613012 191613041
    0x10f060816091104091104030201171306020903030904020f09040c05040609061d180601032409021b030c060106140f0d0b13090302011d01020309191b0b0d 68
    0x500709211081c1d810708410860309801000a41404051000b11082c4610740c0004a49801c000010340f03c03030b00e14070080045034806d03240d1795201c00d4800707020804010100c0d6140741c8402c2c0504000c021441c01c2d00140706d030b0200103084c1c03072030411f284000a0480c0c000c41c850f981c0d6000701080c100b9071418240f0070102d0040140c203000742040e14100c0002c000c10403034040c00c0100300d800e0810301c03450245d59020742c01c0040014101000244091400f031030180044030790600080c1030000a101c050f642c1e04043c3c00c83c2d203901900038203180c18040b02001030b51040241000030200c1c403001c140c2c424001d0001c0d0424002c100054209949420001888210000700003d0102c0c0104001c0303100a41020072a07401c03c07100d80c0007051102c0d00400040c6500552700442c000141442d6002c0e04069040d40304c200c068907180e8042c08020141c01c0750a00300d010407501d00d100c42d03005060890b0004001c4e010007040d90b00c9a02c0720031404054810036440001d803940002c5000a01003803040411009000d2a801c000084c0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191615512 1250 191614262 191614273
    0xc0c08070e07180302090403180e090c0909030d0203010e070908060606030105040e0f03040801020d180c18020412080406030e0105060913020a0317040512060105010c15020c0a05010f0608 82
    0x40c4038030700c2848002d40060140b12454908441d1000080b021000540d0010414401031406040103014617030b10302c98038030440401c5034000c03c041500d40e50080c0140c000100510507043c415052049908001d030010109100900c10000443d404c1d00045018200740d500d05c03803d40c100847c001d410f07501c0d550488086038010f8420031040e91901820b603811117004031000b046450103842071034200b117100c1c5a00311041c080080c02140c00c01e8150010310080c004958100300302c0618488000703850400707910062030000ea200040080102e1403844440038001c0c0800140f602c0d90300c2840342145851540c003103c42c004081020080e50760144100702d62007800034001e005d1440c00c0307000039850200040601e0750781c5107518101019034aaa02c0e150f806554401010202008034440390382203508548a002d00c14001d08901162007840410300340d04035013040c1c54904503002c0075602c900444848081240c0680e60a00c034092010034104141c80b0443e005e44000210008194106070a40780560800c1d00640e016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191616762 1250 191615512 191615519
    0x2070806090601120b06040b1305071805060a0302030709180903080604090b04200d0b011a0711040f1b0918140402090405010b0306010b0d1a010c1502190c0c0807 71
    0x5412090325560300c0382405d078151b91142c1c000b40041c031181220f19003100181071018803584013035001601480390340d220201c40740000018280d901049004030351300608140140d0f40031501a8010791f40084250401e400050744031680382c420015014580300c1e003952a05906401d058100d185917402034800d807410b10404000781c4401c0000b40016000038a40f1419480591242c0083e580c6e0210480c0d0060400d80b9070746440c105160a0002801881c5022000150031854841c480b801c0f1205079a01c04240c440004c0b1503001c110044c10508030140a00352a081e81d03140911000585210310b1140d5118040000c0c242802400e4164540c041c48086901d0210381c3c2e201c0700c00c0c011040c4c1d440b503411160681555514500503000d050049115a018403440d800400d600d420000604220f1180b80402c1104584110031040452005003070030340401c00d40e01c10400800ca5000d001d0902c03110401c405071805010b8402c46c43c5a4100741d000400198040c4d40f000d04129400300c41100800d0020010b061007800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191618012 1250 191616762 191616779
    0x9090a06050c0a0f14091309060b04090302070608070c060f021206150906090f030102071202060609060108040b250207090e06040b07080414010609051f0b0d0207050f0d02070806090601 81
    0x242c6090b00140042032207241c0c5c1c81e0000304200d03a0107400c090840d03c203000744150f01c50054012203104131a042c0c1440d078125003d09091149214a41e0968020b00d505071608070f06451030342010300540d080046c0d038202c000101d82207005034056821721450059983c8824500001c15040187c0300c2480340003a8a50b681c084000b1700103a030868032003202e0007543d4120020000c1ca4080040012f10b81550001c515402032000c0036005a180c900d681c2c09a985680c1c50400b0411401c400b10f6036540801e00360307004140803030f841200b401e0b4000f00040803100602200c0c01c42030805280d00c800c010059114030303024424a81c0500920038604468802082c05d810640d8074210040c130028507020802600400080522032032041c145c0350001c5040003007041c903890b00020ba01620044811039075000d60310780c0c03a07401c4c0711001c00c0c148200da410881450401c03135a1902000a0340c0510b90641e554880d10310780041040081c403490801d000740d50001e200c418a4500e50340d01f07001000700711801c40e800c020010020384a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191619262 1250 191618012 191618027
    0xc0909070f140a0c05070807150c0503030117010906060f050a0e16050703020a0b01030602030708130210270b12090d02030d0903092303010f0209030c0d03090509090a06050c0a 77
    0x84000d00d61204010030080700c00c040f0030200901710344504000000e180c0c40100e05441500c4e42d81c000301103090507241c800c1c1c500c840c20740030040440c1c4c002c00040104400c15152001c8041c04007001107000d4469841d148142d446640080d55505d401c20703030800a0345003681c0303440020103240030000c031246801e00c030a4400100c170204403014404000395000c1014070a01c00001103d0340309110040558403421300350020341003281d0b040d002c80c1e003030700119424030800600326100036030040840d03586e189601c1d012122101078520f8100c5803a4103020794400d075840580071001500c3d03950b1189032251f8442e013003441045800707405480c1c0c03900310480c40341245030b0100459214a21004011403041142d00d4101d503012800d52040a074a48454444541741d42403025800016000b01e0081c400c4514003070a8404030710604410030343c0740d84508d5041d480c0b400c00349a111078090003820072450565941c800305400d10800c45009400740c03c4a48401c0030001d451080680040050107040e00f0004075560182008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191620512 1250 191619262 191619287
    0x9050108010905060f060d0f11010e01030608030a0e040b060a0c11010c050a03050c0a0812090f0105070e010305090c0d140d09050a06181a1c0506060910030605090c0909070f 76
    0x100c6010000441071f80740c0d403406898199000b9481d9100c000d0ba4103080c180031075020035080c000340c0f20540c401032542c42406005c045d034941401031072030030390000e00940d40c074002051031981194403044118400d07903c502c06400d40090680f950500c5002ca842c001e10040d466455840c18092110380c0c50f0003082000422800d6940d05041096645c1e80202e62130b8034000303240e480203002400c005400700c2c100b0a07465801e402034914004441498030001421b9090b2402140d400c40059040c000003113081d03200340c0000d50400320440c00d903030284000300045460250ba6120649950501d00b0840502d00810017000344058160300d03050403400c1c14100040d1003903407103101d80b908122518041002c01d210780740c0540024404086000400349480702c0d40c1d205074003c039507442d90507107910500e203040108038000d582c03040c100140450305e00007406042160202c4090384c1c030020180e0740c00c0c01041644404c0111809001c1b503000c4030b41c89090b0ba000700004144024140c00c100802c0c442011085500b010280144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191621762 1250 191620512 191620531
    0x18200c100912050f0702040504140c010305070827030a0c1e0201050702150d0c0e040c090503070504110c06040807170711040c0c17070c0f0b07020105030a091a010905010801090506 79
    0x7241c41000c98441c0c0f50141c5c81020754050f01c0c200030b007c00c12811284040070124117100307841300c020054005400300c410841e00f81c0086882c40d0002141840c80c00d403900f004001d50708402910212051016107142c1000c181e000116520848503010b10a4a01c46000d4048660603280c4020200b9400249203011b0140d000f3301500110044480640400c0184c8102c0588410700300b01030400c0520080c00901d00480403801185094414226103220f075512806035400030700142089841d010a000042c0301401120701603003030900106603600340a01506d4051400341440c5902c641090070400400703450340000380060381007000503500080208070248900c070002c4400040e54076840c0d070260f075a07030f4070f224000b00080c85040b11003c04500780c5c400b401c40180107403450764001d0345411000c4520038017030042244003401800b95400641c8550002c541c0207084800c0400d0340c00c907d07900c071090510210081080d5805c41c00c01170201313024500c909070044c04850020700200361507840d0b080d11080c0c050901040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191623012 1250 191621762 191621767
    0x8030c090118030807260d0b1005040608010b070f21090e06180910020c06041a0103261201031203050606031005060d0e06070810060c0c18200c10091205 67
    0x801c0002c10b1060740a01d00502c1ba030f9030480b52010100400e50302d0225032080c1a2422401019803260042d1000d850709130711281d241d40d0a1000400c003e800c60941241c01d90071051082c800650942c2d410024150b004c080b1802107004c40c140070304108500e411962269540c242009000d035a1190341094040340c0140d41941a15040d1455050282c4484280d42d0240001074000215800044440c403803170260103040001014201e8030703250707031500707120140c1102c909440b1242c8481990140d0002080c920f008070346000300104803900e2905090b401a175050340201241c190154050080c1035101e0812035480c0d01d12f1501416452840143e40601c41c060380d03011420541508241c1d0200c84500c001c0c1d07044400c180341102008104001c11920860441c41f000000140c3d58011120320450650209119146038102442004806621110f0400e0280c5070112210350600d0b2110500c1e00c07104c42c5200e20340e00c1d03404846252030f00a110014204080c178000c0c500d8003140445030200034088051038001e5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191624262 1250 191623012 191623043
    0xc080117030a141305030106060909060e01060504150512040c0905090706020304141302031003140d050904050916090c09050a05060a030e210405180f07030b060708030c090118030807 80
    0x12000c4031030345c0146030150302c1e0002c081009900007103000121140c42c2024060552580c040d03018407807080c42000d000c94024032003448400311105c4903840030649480c1840c1448101c0242c4c9001040c02d640135034512117103480501680e060350041e0f66104100c038004219840c03905100940d244124403840020070010641d492035581d030350780f8480001c48991803e5403070b410213418103200200c00b4803003100c42d900d45c95409039541c400802c5409400700f41c1e40f030345c40c1811004010311000d0a8020300c2c4280f24051003800525200c4003045100140400a0000130322030b01a00e8080d1014032031750003032442603811080c01c00460380d50804071041040c051401040e200010003800349480c2440300c01c0800c861401030710f0311003803000320054000c4038000c955140c0c031030410200d611090031058865021404800740020a00d50180d00101700303400e0042c1406161000c580c40e0031426030800e403459031404000288549441d80d200d10a801b5030042095450f540c1c52031a5109a110b10820b0001494542c85d1044d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191625512 1250 191624262 191624287
    0xa0b04091101080603120f0c070e0108060a0f060503190606270c0e060a0c02010e0d0209060907020c030a06050a05010b04180b031609022101050d020402030603030d0c080117030a14 79
    0x1042c0b4441c05919081c5c468071100947d184540223403460200d5071141c00302c0000c0c821204143d0b6070489542401a150f0340d112200c20001030800041075803d156180c0c0400200c1d520200315000d5000391082c009141d0305018030348042507595503400415003100d030254000c2c1034000c000100c010131000040001e03900b20079400c1682c148407048010760f0300440110703a20410b10307004401041d10034400d913140c0003805401d100b0000b1842401c40302a411070340d41d070300040030b604042c3c98207a0880010f004540030b40e485000000c0c6444110302045813860344602c00d0006020300c6000b10743c058541084400e06060500d06030101111a03c2d040c25404c0f078030342c90035505503201808480180034160006603030360354441e662440a0b50101000d03000a40110400300803403003465001d00d0603180018404200c0c0100c43d0208800703904041c2a09525000c01c11590481501a1240c3c1421a207242c40e41021766250111f0080d80086001440d200c0b60420030418400e90ba1103201424003a14101b0f040362905104800ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191626762 1250 191625512 191625523
    0x307030209040c3f0f060f0b03060a060608240604060503090c120d0c03030f1401030302070b0319050c0909040b01050a0914070302070305070b0a02030a0b04091101080603 75
    0x181d0050300c403009020a1240300302d41c020070340740c0c24540f100d00340c1101c88600601000c0c1100018103641c40c820741070080d2181440360b0008a004100c00404040350713485640c100c038840400d110000e941d9000c0c9000900701801100d5000411030000c0009030301c0e200014050500081c10001c681800c03c0010402080144078241c0d00310019001d131341ca541e00c40002401759441652003492138890f901084880b0b190200c40f1007040000d6030040c204100ca40302d82541d2600001c4003c030103058890009079204c0c405031003140c0d12a5008080d00450b5459410040d08007280d40d00f116410382003c00411580b0015500050110b40301d80f8000201ca64901100803198015024071030703400f1121605000601c0701d0340f060107050724012034600e12510741d2595650308960148002c2e02519100c0790000e50b500c0e000b030f0302030302045010b41009860f00c180fa95445840e1a81198101d40f03096020090203403040381d0f41314842488000b50740810038000d00d515460100c028102009041040c040001030030340c2c0303040c0807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191628012 1250 191626762 191626769
    0x8030702030a0b0c19030b0405090a02100f091a070606151710080604121413030b062202070b0106090b09040b030f070807050306072c0303040f0e1f0602070e060307 72
    0x2800101d02c048114014081c11004601f01d11441c1400c0c0032070303042c0d200811542400d650003400b0528603035895800340ca5404114403500c09024003100005440750002c46c5104c0240110100c6980e150891f00e00581254901d40100307002e0246078041185094100007203040500c030602000c102c0d1703640c0c1c910360b408a565641140b4054000d00051108001c030300821075810a001c1c2d10b0301c0d0400c100c50002a9090300a007201d140003451104c000b0008038180714400f680020002c5d01811000c400b107140010104900c41c038070446907600242030428031030004800ba01600b4203160208a01c1d24141d04905540100200700f84190307503d0040b100b080d03604100b01c800030680704043d10007940d981c8021036214020791040d1030180c05070030300040c2c07080d100b00e00f1400c00c84581051f00420407401c400c0c569203200ea20012079054841004003280c41100082003134018202c00f100340c6290314191600340201c03040d007450303004a200484014401640c002c03032094207403a024000c080c229610000000d00d000c4440c0d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191629262 1250 191628012 191628037
    0x61107060f020d0e03191d0303030403020d0311040b09060d0b15301b070b0a05180109080f070206040e070e10020610030f0303020d0f050a0608030702030a0b0c 70
    0xd0210000c8006070b00035182881808008114019400f8003090f12071090007070410341003c200b80c0c800c41c0f140c010862131081003410143c901c02145c0c5100401d1665206032010750144e800160030350b0b0700a80c14000c170302c0704040402c9040e08092800e1412281d900606028510600c000304000da0304031442d5004504d003010082141003210707440c0e83c40e0012a403106180d0020714903404140e61500f00c0c1481b002c101101c0b05200301c5101d55804a80d1406801d0000082e1440f030307410004100414118804c00c0d0080c00302040004144c20701c4900c114600403003508820b8182d041c1b104081c0418000419200700520b08090346070b49084520008039030784180e80002112010301c5040c442d545038003143d002100d000c2902c21103c006d0b04500242da0f00c0100301c80c048bc3d40f001c09001440004d8911a440c1900c920908026044c80051001c2006440b20807100418503541c030002c001c0713048070b00c1c088c4c3c03402007411002131860149541c0200f6201c0c07680c080081d1203100e403600481c80f42d00022003140c032602c0464 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191630512 1250 191629262 191629271
    0xb09101e020f161b090603170a020712052a1e0f0303040308030a2405130906020c2803020705090c1303030203070b010b03060108070e03071d010f0801050903040306110706 75
    0x5140c1031407400a42e042c40c624a4138000f00200701301c21184101415640c000b010601c04d5100c2030303000b000d01d503c070041fa031045001c2c6602c00145c0841c01804101c0d81031059010b001c08202014a480300035040c0f16207a0070a4400c4103403d442600c81344201c0070039a0441100703604086440b8045489030090f01034040d09844000741c000180081e19001d14055428032805000072607041200040f1005070362080044190076450822403071603c90401e00e01d000b209080030800c0012606e03480d040f070b04080100441500000c200202890740c400300007100802c10902c142c1d47c405a0340b8000d5135007181e4042c046c0186c4807100820311a513201d5050b40d00001c0c0c52010721a0f604e4413464000d440760000c26080390300e403a8a500100d41c0c28440c000303032407003010181d4441145a07903074002110507490789105150540114880824802c152004000700c0000060301100294501001031030060321507031104000f41d142c00113201d812072011040310116600708402050004100c5050079180c4a0390000420580c40c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191631762 1250 191630512 191630557
    0x607030306030c050901050a090513020604030b0603120a1b020d0203010c1205010501030c0807080403090f06050a120207020904261206010f090f090e070905040b09101e020f 76
    0x160040700580e0710800c00380300316990b19070521170149000c0c00344542c404140396041c890040a40c1c802540024182c0802d01c000107250003080040c0d21540080d220341c00b0000400205050400c6a000c9504040c07580c0c600c1d00d488a4001046903041480262072814800c1101d03056650344460302c1a41600180200f208415001d80506003d0004910351035050401c400020384c0d6001e8454000c030380000d512441d44035620404100c5011000403c11424040010b2011840004e40c0c11103134060103450b02e03100da48a00b4154003900841b500b40c194000d1900400c51500181c64010200e60800d034011214003100c40c00111a01c081c00c1840e064403110380012424489078644901d08a0040900383c9a00c00c00c3c00360603004175180d10303460264512050000008000900071a4442039100a120059842d0b045e220303100f403030585038140c1d0190b500e030501106103c6580401c0c07040d40c0300c80c04122010072441c00b2650303118403600b035592120080c0c5640402c4404c0303c002c0100845a48041c801d0075003044414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191633012 1250 191631762 191631767
    0xf030a172808011502030c0d02070f0b070c03030c15150f0602011b1413090204060e09090703080a09030f0c0e24120a0c12020319030f0c020f060703 65
    0x4140700428240005800c03516941800d401002010703500e101840c0e0030820440d046080310f00c2d02e0b20441c4401c01c004550444140445400d4481c01d601500c801e51030000c0c02e4403690a2074000b00200b400402a48001540c020500c004581d814242030701d90303110605198400b4809621140100d031b00308000648203410f050b010350242c030302d00c2c0c1207010a141c984404900f21200c0040407280050401e81d00280540500c503400140c18541017424940101c000d08813103400003d80c0851f12440c0c0100742400074580000354040340340ca0545511b0860300d041548565118203920004c1c06550b80029849100e600c116109070107075811079444104500b4503d030068180c0341c00d10508480884000119004005203008600d00d003101034501d01b01d10701c203c410012100c00c0701140300464402c202c204800501e501041c0c1000340f02590f9013900d4031003180141401d1040248141819203503000405000a07040618041589043e1801d981c000d0920b10210b80c13158030741c10150b07501200100d00c40d400c056 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191634262 1250 191633012 191633017
    0x402090303041514190816020a0f1403040303031509020f070308070309080f0a030c050405010207050105092b0c0b030106050f0d1e020a09050901050604051207090c0e03010c090506090f030a17 84
    0x1701c2940d243d41e22550ba144404210000c8001e8802c0141c0140c46901c0109900e00c0c5000d000c54010711311440c0c2041e90050052855000e60310031804070ba01c2c0d81c61080ba81501c08440700080c10052004d515211a40d402001c2512603440000d003402511804039401a100e5807090808584c01281e00750b880c500c004040c90071340c000d85a8000040c0c01e2004a00495100e80241c0e81101c0c1c1c180c00600b00c0c5402d01d00191003a401101009402101d800c09405c0241d46001e559104107102c580e02514050103401c16014021032034215960f1280100010088194050129200301700c900c405c1d2070f201e1030000480e0025140f01e1305140e045404446500d49020159801400003000681b01e0000c4181d4030003d0102440c0e0034800d01e5481401448100301c070f4240214000c140c620b0708000e90700d461741c0f00c40044c1d08992002502c5000200000005402030a09200d503075074141a45c1490107900d4036100025400d407041c01ca041d030041d1400c604c50b1580703840070006004501c1d0322240c6586120300c010705032003958 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191635512 1250 191634262 191634307
    0x180a0b0103051e0d0302090f1c17041a030403170903040f050405061507230d03060b0c1b030c090109050f10030f0828021b0402090303041514 62
    0x3e00035486546044045100303c5810400b011016207480032141409030001c0d0441d29000c0e400c0a40c0c031200d007100d9a110541c600d0f511000d0264080520100e040840c4d184034858942c0e8801031003004240074412660b501c0e502201e01030289507a076a13407584bd08650403400041c40b41390141c0365400703010924101001510954250101c2100040d61f14410002078440984220303410503030384c0c0303524580141100c1c01002814002c000d40c41e00320106000d007151164802c2165020f42c1c010403c6107510356410700413a802403154981450034451580781c0715031982d0280140310040c205000b401841901d082c0b1148560b03460080c414415982c0d031300d0f40d0001074002103030840a4480003400181d101c500381805a41601e80103e0b40400c1036002c0e50f151044c2e5401548411102c0d206a1450f01341c80800074500001c404403076000e4400c04c891005080d0308611006400751169005000c0b41c13060b5140042594101c942c42d000d103100c0d2000e403840c151510014800c01c01080b280c00070b030079007201e84e02164640c0300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191636762 1250 191635512 191635523
    0x20f1b061009151721070b0c1803030d0b010305060901080c010c020112060608091c1b020604030f230f0c01051c05010807030302160e01031202011121060f0303070803180a0b0103 78
    0x902088a0174031600e00c50034600401034158000410468402c42024180002240b800700c00c12801d0340d00040d145800c04044036407403c0e21100441c40550303141c000ca0317821000c182c848074a254141030f80b05840300080d0745000e042111440c400000e580c402c001e158840585418100a45a100c02004009600071030342d82c042403168030f200b4004000d400c158807010f0140e599036441050340c0800300001102c200d0006aa002c041030001102141247c000b0600e024410723414042400241491605400c203041e50780001034010305004040380e60701103598030f5100c1b02441d10b95a20f414803801d98032640070500d10014941e00d400c00210364841c0000d9480c00f9a80240c00322000000c12241c00c00462180380030f80107074000d01000400000310781c1d040500d0928051b0001141c2d90031840f00800068200d1200e0320381c6040c00400004000c45401f5905411400540e5891242400000425078920595100078035600c00000000c5c86254261300700a0541068802c0c1d0340c03103100034280554246001c0c0004d555 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191638012 1250 191636762 191636803
    0x40b041e06050114031219080705121618050105030c0a0302071703060a0905010605070305210c031008061e040c030525050d0f0605070c06020f1b0610091517 69
    0x4040c04c001f80d44180b41c100d02c2d40214009010812582000f0203841d00d0140f000034068801c04000303000001d480b6468001c0500d0281c5103290005000e1600828402000000c0701e10600c59030741d1001c1241e038407428040902c1c2d50b58036100fa00b1402449040009001e105440c143c0b0382c219200c5c0310066000d0801202c40030510380d12140040202c1c2c1083c030904000c520208000c2c030003e40990050101c0d50b290381000c201c1140300032204460303c942210103800d034602c0013040103020510800340d2030117810711100a00c000c1c42c0804050001141c540f603010030030703601a4005401c03c5203442408000d075520400751004440448120100038903500182c80c0f545507159070126090400d102021b02c42600081d1300780ca40d0340075848080003010082c0040c400c2265060a02c1c0110301140020061009024011580e410f002e4034403104100d00102d03040c0172030700b203c014403220a01212410081e40c2ca1160006107000c0c0c0501c09106415560f03010074440503042c1403035200c0c6440851651410140422080c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191639262 1250 191638012 191638033
    0xa0e09040c06030b100c0209040602040801021911010e030d0203090c0a03030302030f0115080426040b07110f130e0a14010c020609030a0f0e031e030c0d0305040b041e0605011403 78
    0x1000c40c0d00d0641c2c05c0010701c05024410152814802c2e00790001c1c09074000501d003545030250765003640c0c000352407100c1c551084410607d80300d900c409103049251320300c4000c08c0007a10714255940c881c4961103008103003035004004207459001c00d200f0300805441c0104081d184a55900e0054041e4001300c5a04000661030750001603a40110640b109001c10255036016890341c41c0e984418071003031407a040e20600340a40a00300c801d004220300410240100ca802a038131468207181030381c210854422802e0150201c02c50411344d40d100c0c890465000846c9a001045960b1401c410358a050b440c0c80029051601b82c440e400068601940b010443c40e04660a03168a0303520341015641d05d210790680200000c1040030081ea0b650310450605250440081c00d641c8002c408080041070103a6107002d92082d0b42002030541a0300e203040103c0d40c288070550a081c491450903032510131002c0001000a0700c200700034040d8045e2141100c49052010740e02200c200200d5840d0340544585215110419000344103112010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 191640512 1250 191639262 191639269
    0x4020c0a15090206250611120a06060c080a050903030f071223090301090b010807060807080105130c020307061e180804120201121a040c230a0e09040c06030b 69
    0xd026540d009130056290003406020711104824100c0740808514420035080001102070141040311610145090b846100c0d040b0054401c0b800989020b1a0524020080000b035030004050006550880b000f1a192060503c0607503491103007080c045e0341030000284143c000300703c0c0e00203080d50714060005080002c4ca500000c0d901508212000203005c02031a0034002d0350800c100003080309800107400030039540b00c0ca9840301420402030308080c0c6184c2001e4810f01003d9441001c0552114191500181070351505004c210109200e00300800070035103d003030300f81c5898000c004840c40e00d80d004004200c51001c800e00225071900140c401ca01180c144140c002d0180b00a00702582025080b0110601d850f181c0f50115500c0415484200d041c4a07146000815204207807103080e20200750f4222144c06590603801300b00c125484040040e06000030810321800303061119038080103600c4200c60141c0d41302001e00041d078000011400b2658070584040c204020040c031500c0030000c451058900707104150222003007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 191641762 1250 191640512 191640521
    0x11060a0819060909050a0209090d090e07090b030709060219320a060b1504120b0603010e0a06020405100e1026040f020108010b03010b12041104020c0a15 67
    0x4aa0008044202141c2040c082002042804240340c0c00010240d0340d601e8008180c1c0c601100c2520640c10040c544810750400219095000341c442014007000e81603010b003d803c41c0e17258001c00d1a18650200010021802900880050a03044500c01e85a1400680050004240d40980801809214040240c002c0582900400b42c1d620a8000106096407c1948107421070361003000e946400741c0b60740502400041c000f2491103400342034041001da080070144065030481c1d041c0412032080820003000720024440c40215200c0c3e2001070090344e91a0040028007404030882c91001a00645100000300400d6900410455806540722a02000c0040c0c09560200c00841000d403c030502100103c0202c0c845d966008941543c1c0c1400034680c01e40440600300f002044a0459032140f29407000d07410343d82c1001f030390750046c00240c000501c1e42d81031090740c0526018100d40c1c8035180421001140030840340003081880450054001c6440c0e007003420405503648038003401074522100b455035441418105001c1e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 191643012 1250 191641762 191641777
    0x1e150a0801200d02040f1d060303030609041101020109020a090204170102030402010f051c0501260636010f052208070f0212010606110115120b0c070506090304031106 73
    0x3003491090820782d01055440042030308481c0d54200000702e4403c00545580d0003400c540003600e03d5601500d800c1c00f03074800010303000c24483e5000f0320422500d035544409145e400f80c0d00004401c40047c0000041c1d0151180c800000d5100001b50004607584142d6405842119441c006140038106414289402c030307c42920060300140300382c0c0684181500034001070141800d200130095a140300389900d10203c0d8030030380108151400f04000940c0803c580b0640c3c1441900540c05408142012680360086041c04040c5106c020841000c040c0901d0361024040200c151001c003e00012000c1c0300c6000040c90216582801644189101545040da002e4180b0000e80c1c400c038605c0c40c09802c0c2c2c581400041c1d034000100d9010940820700481031000703001c3c000c01042075440d207540d08003150844d0b5007940c4120b002c02c5040111000b081207601c44100440103d5500401c501c0c1041d215011403800d2446031a00c06090383c0700f10380605c141540d00100400403030f8000c2c510765144102d440e04200d0144202d68 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 191644262 1250 191643012 191643041
    0x90403052b24122301020307360504050a020c010e061f0602030304080d061809060b01050f25020a0807060f080f1501031b0c021302070b0408031e150a0801 68
    0xe040c034000500050904e01006403182c8940aa6502030800a09903441100c04100240e10740b01c2d0100c1c031140000c1c074005020300d40301c1151086061030b031250240004503c03960784541d8850022510800c0241d0450740c461a2810080c0041801c100c1c01d141c1da402c06941c1e030800032078040e035800080510301d03125006071610395018503d9502c681c0c48140b0301e504401c10040710a86c0e2020001244590a0071a00e008590344201207401000c1c0e003045412038508000080c140b081c100031154420740e402049414803421681e1210030012444003072068240c2410000b5008041444041100040003c0c00e02c1200c5103551440b07005500300c40115802c4006880988002c01044042809202005090a4030201c18540001c100d00e0f0090301c2280c1c45510030500c0c5c003080740c2000050a40c1840c0c0210100f40d1100c0134158500061740d6540614854001c00280c0130131808408242c03000d1404508200714142c41d02c0307450711800c00e0032030940d4030210000c01e50b20030030840100054082060140010240008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 191645512 1250 191644262 191644289
    0x1002071d041110030e15010f1806031b03050c031203040308062409090604060501020601050108040602040e010b040905180c01050c0102070b10080d020c090403052b24 73
    0x40c00004809034041e100721507070180c40c2c1d40103003a40c07100385100005483c640c0e0003103420f11455141d5420010644009417038444144014080780c001c0d083c010f812101054040d14046c8851480c0d24014000d5030070042c280d4800031800c8401c880d1059103a002d0300d000f102a10003607119941056507440170020f50302c0b00542c0034000140424001c042696128501030401c07100e154028020094840d131540184224020100341d0b2200da00704024070301d0b407080c01510200929403d2500103035580e04140314550421160704006410840550180c40051050428207001c55848401c81403a0350080d0040f115294074110001c0d042440800384048030310541000303448003940b20401140d140c0c0c00080aa03d9964082000700b000078402d0580074810702d41c140308c801d8860306101c0024149801c601c00c4004541c024803110480340d0b81e500b03081c0d8010364182085a541e440c921840c0c81c030040b40072103a1b07004202d54004078048031416000b035501c00303c2541c40d01e201d080714402c0f55418094a401040b60301030310b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 191646762 1250 191645512 191645549
    0x1080307020d11040209040c0915020f030712090308070b01140603040c15110717071211210109060f051e0c0306030c190501020105010f0e16051303060209100207 71
    0x101d580710f4103202e0010b0f00140c074144a044c04039040e2045807914a000a1400608202c052911178000440710f1540c070281406070004016a5a64014188054020046e042101d0f40c03260289180c1801148d00c4080c280d100c22041c2003145441c0000d10550b41c41602207080581c4501c0d112045900c44d560000c074400c0310340d04290030000c44880c1e8850b0081440f07810b410004414070200b00c000010205050422900b10782c0c400c090f420451164800003030302080903211000600d001200d0141000160f50030f034284d10100c1004020700c0740000e801d0f8015480c00345060f0903c02a9040419140300d8110140540e44030b44100e00303040c018502e845805c4601460200785400fa070b480046402940080c101e80e880c05200001030070465031903507149000c40d9282c3c410411942c080c02001c1c0103152040f81b56403154541000800b449100906c545d05003201d16444005013030040302034402c00c07010b2080b00c103480344d16840d00c907000350300901603a80328400301125800003038400520481035130440815100080c60 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 191648012 1250 191646762 191646773
    0x6060a080703150305010e12070b0f0606070f0b0a1a0307050108191104031401020306011407170c07050118060c02011407080a0807030b01080105010207050d0302010e010207060b010801080307020d 86
    0xa446007003055181c03180801c2c4100c8518031040a10b000d440001f60007030b030b030301e102030f2500340303080b4441101e00410300941002c01c400305112944590901c80c0d1200381c0d0b40328400907400d4030418400418007401100c0c140d083c42040342c0102d10804c01348400308521080c444088842100152899078590b2141406000a510076003003da00500905070504031006000e200400741d032803280040781c0e07110011508009016080e40c0948035014035000031807440c01d01c01e0008010018030048404000000104d07442002030a10241212005504010362284c1e02000540d850780d0721842010b00141040e890716981441350701c046411200c00e86c0b00e104507404075a0055444810403802110070b001d080c442d0384040f0310584007c00c204c10a81d66031603502d00d4414409003c441000003003904110300f4000610069030001042c00c1580c900300c0b00c1600c09420351404030f0161118448038143c1c0d500110700001049565008036100c042e090321410110f03138a84001e0b6a6034014000080d600510344808070300880c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 191649262 1250 191648012 191648027
    0x206030c0702270a15050d080a17010803040302010c14060405010b131a0d051c0c020a09090b0a020d2702010f14070807080405041e0510030803180a1a01090f0506060a 73
    0x2500f0f10b00c40141e60340700007030380c0030121240c01c0d96480b9000514031182d52b4003288680504903110500480b40d41805c80d020340c0d034000d80c00024140b202001400c010300c1603400010740003502e000110350052500e813600502910500d003100c1d0207490304e20000418600a0300580450380340300528507007a026404100080d000d4200b2042d40c5070701a008100445904101d441c02c0f400403252956885010244103110304000c5650080015034a49501c800005080c6144d00341c200000000142c0c840d40106c810b88010b1500104040482d0310004ca0302c86051018940a180b49000340c0310050b2051b100501514103107000e411784104d03081c08106000005a646001e8040e807406804054201500d51000c9011119801111203040349003952400700448640601540702040300e1081c8982d07440d50703455440c84c1c000907020116044514603139a2011004101600741e042c2c0204400b10b2070711440d021854031000c2809140c1c4032070306005181a05210600415000300c0d000342c0000c4c5446007200e011521503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 191650512 1250 191649262 191649281
    0x120a1406010f080a1a10020706020606040e1b0a08010c020a02040c050a09030f0f0b0108102a05030603120714070812090d0c0509090c030601080d0e1003090206030c0702270a 76
    0x4000800b40d08000346c03954189820300608640041c00c90a04040000e4600310340104a184503030304098a401c0411804100080401c808421540c0d9124082002954088041e00300340107640c40d01c900320008550001c0c0d00400c80d4001d40b010000d50000a0003251140b043c0102da00119000c0c0c1410400958000001c3c00c015001d00610074002900d0f82c1d0788020704000381c0c040e00095000f0a0f080701680003510480c406410345aa010744207100c20f100324414860040440c0d006d10070044000351207500c0512400f05040d40e5603405640e501c6507403911800200c0d1111000300c4030f10610b1804514480700044820442d50b03c4d030666401e16060300d08102c03241504500803110301c0003101c40015143c171a2503102c0d00544004010702500041c00080c14506001640080c041d640480300070901140c02000c502c0c0c0d201800d80309112605400202a00a0581c926000b500190000704002112988001826945108450010320201400308500e203014100c1300c05040d101c100008280a088164003598a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 191651762 1250 191650512 191650541
    0xf05150607050f0a030305011707080c100318080319050601050d020d0e060c0309160509010603020a021603110f030d0e040f0e120d0501060804050c0411120a1406010f080a 75
    0x12400f0001400c3c208642004c0460100c1c1c2c0301c01c0140310038903414044c001103280e8200140080e514015002d5541c101c1010003d02580d49984800e0702c251090708160ba102881004006003100c041c600a2116401184e0300d403010702b0603a10480044016004083c000d01050f515203080000c9403204100940c000d4901004d940e0340d0f80c0004403600d000344801d52240c20564000c640321314142141c142031021003607103a000b031414079005018030703951056564191640d40c500141c613140007040507841c2180f403034225412807901d10400002c1085c04001610008429945403000c02e03600014180d0f034111002d04a00450703d02c450030103040c1480d070b0082000b140c0c0d1410114540882c01c03501e42c14030550f00c2c00c840a50400090100301e0030f54501800d80101081e140003141450030351100c50f01c03242e1a0180d80d20480d10703005000010304000042e11f030903c4501c0900d20ba21705140740300000800011081c445040d0b507040c0052020f600801d4a114003042945075580310b55605907050740103050242c1d00581 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 191653012 1250 191651762 191651773
    0x30f0f070f030f0b151804020f06040e0f280501050a1211120c040e0109120206010506070308040606150203090109080313031509140a05070509010501050706020a0c1209090f0515060705 81
    0x245c0c4e0361a110800d9410007207072102c0354541024014041510303012141140511030800c8100140c410071110150703c0442d1155184594583d0484400d00c80d0451803c40c2c881203000038458041c01071584454100c070400c850b0015503540c2d48100c03407004008404040c10b11480c0780030f1744c0c006041c410110300307806141e00c2c10b40e01581c2d00703080054211a4881041f0301c140c1c1d521030186003040541c2e0340000f1000c04a0008015540c90701c0e000072010702c92080010f040242410104040165981109000e4004070400384504220302c40020743d00d81000040034006244104005000d003004801c5980c1c4000c030280f068641c42c1941c0390b1812000c0030360304030340f201d551360402400402e09202403042000c10382c20140142081604103585420101d410440c4103043c840010080d6a03000800c036045e9540c0700c0000768035282e07000401d840c55205c046000d0503d0300b040140d01c2d026075100303251500b95180b1110800c0021074001441040300d6040310004104800a170361044035142940241c02a58411006c448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 191654262 1250 191653012 191653051
    0xe01030209030c0909070f09020c0304030f0812040f06150510050a0c020904110a150f031d0703121d06040605030405100603210203030403120e0c030f0f070f030f0b 72
    0x2010030700102c5d829152504050b40c24081d840000501c20000c203040764082d07007801035040d0f00303580743d00c02d070b00c0001c21010014500c80104a04030341a5080080d508088a0b00d03485e09046c400c482c034145107400c4548900d04000c3d9489403607008014015500080c1180c1074030b1a000b80180c81648c0705e05076074006c0c090b20724513600060b80c0320400e251189103c0c03601e15150f914000300740310140d90140c1000908907601d01c03004020590282d403010840744640b40204038100d1200c540921500700c02804c0400f401542004800d104820300c2c001440102c2d55641c0c01d44100303503c4040c20302d22862a03010b904c42e030200001c0021030700c201c01454100d8040c60a5905044c0c403604507404842065104452001c14402c032450210351440c0c1381c2c4004030890010314a1441c00d9980200b1081c4010185940580d48250348500220f04010700591454042c003100c2d52203990b144210b940300c610900c4c420301441510401b269000302c1c1c1400307500701c1c0da20901202d41c2108a40d1013143c0302d400200780900f11050121b03040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 191655512 1250 191654262 191654269
    0x10201060906082119031d030d05060307230907030e0303130c090533040c081b092d18040b220b1801150e01050d030e01030209030c 58
    0xe03030040030311400914001e640d032030310484910a13100e03031240c2840c01840026400703041100410520f18561400080c119900307441c3d810b100441200f00346d21880049107503201030340e6070b5010f00d003c3e000880c200e5203150394400300407400200d8481903a401505c209079080340c50901e00e5609401081d41c3c10301043c03c11071900c0c0285035802c2103030802203105054171000c052046480c500c0d0054806a1424803a52602d9030944104000850740021404500c2c2008017070400030543c24045040c004105100400303030139000503d42c1c0c2065030080006102400b0110740d401c0c00004944e0001e02c081c00202800114800800007014050105580340068269808807a990020ba0310141a100d040b5801d4504060420b02d058003001003010b138604251a5010081002a2543c502169403040b807551180d82c0b40401d0070710200f5000030110701c0350b007400008c503012401c102d4150280c032031886502e4a1607a0380c0041040d91441ca60018000ca2072104540005500c03c0d0010b041c0b0001c060100c90580b0b07942c8010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 191656762 1250 191655512 191655521
    0x1005090309100903030906051e1605031c050901050f04020d060b0d120e09010b0f0a02070302040e0a120302090604230904030f120911270f0f0708070903110102010609 73
    0x1040c2c0020390078a818030806070800700317080140465103444d5042800c104d5a080300f0860001415440710004180411262442c1105030300c0c8036071140c04d0300c3d00d90305009070300c014818040e00320032982030400c1c0000e403e40c0700500c58144901f00401c2c1480700758035160240903507255000f009039500c1d0b80fa06014007054542c21086800705210b800d68403410040680002c0505001100e954807945500004020b5030318040b0a540c410898905019502c00c00d4040603490201544c2c4003e411505141c194200000e001c10005403150103664a001e000f40031400c2102284074410309603901180901040c00401c0c40030010080450242400d0074603030a044001441c51741040b28118000780700c41410094480c5e21020078104418404424801c40703819546030480100c5241815010340e981a180d40c051115940c0d0620004034105802d02e80350801080d402c0078640c040710440c11b28080c0342c0109a0161084040e00e02c912a41e07600c0c140c2c500c2c110703900c1013450504111038030304640d00d410703004c03030b030707403d0318810f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 191658012 1250 191656762 191656789
    0x13030602120a0c0c020f10091a040e0105010504230d0f1104110720030a0f030504030b07110a0b0c0f0a2102120f0604111c0515031005090309 62
    0x307880e0031403500c0103420003981c0081a0b071108114104002e0001a00c1760b00140102000032282c1c1e443c0707d51030440489071400c5661240f40800310070b0ba01c0e90445411400240306444a603c807170306081c3c0c1c0321300040d1103030310845c0301d084055903441502c05c4800844044852174090000c1016840180ca603c5801c0f000c0c2c1c10300402c0e6180c04465948845a10385403044400c00180840100c3c182040e5494001140030103a84480c0d480c4000204054aaa07080c466034580c0c5611004046c0c02c4680c0381801403041d0000c1c04116a04030358000402c1e441c034002e03407a45241210840c010640c5050700c2d5240740e091100544000350303465080c0300c0000e101c0301100140c424088517640d0081e05e840070015645c801c917000145491021b2040003154884c400d08100c82d41c0c4105047d00e10100b5898820200c1d00070038407100315205140380402c8150f089a81d802402c1c00140b0f00344003d01c419180c502e0f81c0b101d85403075111f4055145e8404140e0030001902c41e00481d030702094440943e8141003011000c500340015080c3d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 191659262 1250 191658012 191658037
    0x20d021b0414150f010e0f1201061205150f040f02060724020a1202090904031b05011d060a0e072c010e091b0108280c0905010e0f03030307030213030602 67
    0x41002d82e90a0000b110ba041000918041540d01c9042c004a52074010b0107005032300410f07001220700c025420035007122009194062000212407040d061980d1102c1001c41d1005801c1100008039003240b000f0003402d8091504240e8074201469550f08020407580a104103e40306c05100d1000360b03c244c8508083c0155140b02540540d540f00280700051918405080301d068440c8180030b86a0503486a40d1200c0e0b006034182400c8a158081c2c9203810b002c5219201c0c02402582800c404034030008081208203e50b88400c0101ca03417a488410b00c500940b406d2071109406a40301041c02c025242c40716101410080d014400b0001d8103040107854120301c1d000b43c01111046284005203d24000104581c000c01c058a0703e0309000004c102000030002d08000d0800b800c8012a03940003a100000d040b148441c4003440c40081001c0d1013080d1b0058001a0b19104950118034181070550031400e221603c1071801c80c000f00954079550320302d04240d009401c04403180030189144c0e000400050041e02c0100409501c22 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 191660512 1250 191659262 191659291
    0xf0d03060512070b16171603090506031e0a0906060b040317040308071104020d09120f03020a02070902030c04080d0207092706270c0f06020d021b0414 66
    0x50103110740444058480566644402030030000880c80c3c0c015074007881044c501017046001e0380e0510075215035126000901c115800034502900a1040540e00702492003511100c1240d656002001894041200e2403a000760313040241c2c401e50146400c40f03030340c00442e0100010b181c503000e03120f80301254500d41018030b00304800103090041c04104000c00c1820100120b640740b900313095a44811090040000c01064224024514851595035070191480c40d40f9500d020020480641018852040341c5c3ea030503000f0804403281e02550a11138003c44003e10311a40003400d03d9450105401c009500017444e100d0700d40000d000100e00c0300b2042c082003005000d43d078010414241008402c0049511310182c00401a003141044070b002d00304d01e0500d072040d9030046000036074000c42c448080c4000f88004009404500c0da0780301c00703007000b00d50031910f000e565503103880c03039404e903100c079400da0b91440500400405640800b00701d003400c0e0031301d030348215000c0406030012034059103000c4028004c540503500701c442c20159 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 191661762 1250 191660512 191660519
    0x5010e0a0b04061a060d05040201020309270603011a0f0a0305030f19030204030b01050915060a05040303020c06040f0510030e01020d0b100e1012060b04030302010c020607020a12030e0f0d0306 84
    0x5008030048448424100ca5144c3c00700c00019000b882004807080c02d40740c07170314002003d40e8000c0c0180d408407040641540000b141030802000500f40d4207a000c1090700002c004903105080511496460319940540c042c0f104682074200b00380e0581689156900c41c0c4000d40100000c0d6090000c1c0103440e42c4901e8032034950110452103902821403503410400c052040c0010808111499003541c1140c2c4103490032001c40c1c88007890845920407800005400501c00107543c00074503802401042141c1c060303420f550080c0001030400c006480780d072264440c003d01200702400245000c00b02442246014200081c0c602c225009082c00c2e0381265004c0000b5a0f6666401e40c200d04000e45003002503041840c0429045940c0030002c0c0d48100224100001c00c201d2141610400300261303c200041d040700b201e00343e110340d42d03460020b010345002104a8014017807000415245400003070b540b00c5960b88888400e0708800122021030007002d11400001440c1f249100007507050740300f80041600d074000c2d42d4010600714203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 191663012 1250 191661762 191661773
    0xb07030206070813030816020307050708060709091a1c0b0103030306051f08070302090112091b0f0807140423070801080c090412090b030a02030405100c051605010e0a0b04 75
    0x8001e00c402c00f020030140c130880000b40e0059046620001d40940c003018110300b00c00c202e08e18050000010b00f14401c4282c04905240009005e07072198001d275580041d569160441d80c0b059546c0c0010000c0c2d1500440501005071070a8100703c42c00c8140c07032209400216403521403001c0341c4802e03442074001c00c0c2da844003030140d07003890403003880041d60421452140001c0110b0050040030000c0c00c1e0420190f02060002e09684100a50a07400644176800c0c00a00580d083c0350503026418a81440e551024800c0007480300300c41d0320300104a504107000707030610a14060b82e4031030700c60009603095031056a441103008140c692030b450703400c0e20308070b100115810300c0c0440019002c124181c12000301c0707a0102840e1400e40c5c1c0c6003140b45903c2580501d5209448680e95070a480b980580c1d0040c50b90b07413001108119900c4101c2c0d01440c4036030b001d2011100340329a912507041c100c960507051140015001c10a01d820340789901e02c21268284244000030310031103c4c01d0b00d68240800034408964040c41311091105016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 191664262 1250 191663012 191663027
    0x4060609050f04030c050309030102040906050906150d0c03020409050708090f0f0a140a0c0e0a0b0a060906080613020408250803072d03050405040c0311090d0203070b0703020607 78
    0x1440ca020072103800c0c211542800b00d00001d0000b810000d40080c00804c000742441070b07511401000c0c000399116030f1101c1c03081c806010305000c1e20b07005902c1e8a00040e03407840c002030a420440140d102c114542984030890001620400f14600c092680030440096501030074803540e4400d0304940e60300000e0707003003401840d4100503080902d006190b0000240c0c20003c0e1010503c180c00e80c0c0d21540d07440c581200121a1410000d00e140041c11100c14400700080c0d032803c00304101d104220042d01000510400400c00c11000441d0140c900012903061090084500a031070194100000408194032849002d11a40a80e0f00c641c101c001a40c0004021080c030440d0b43c11170151400405040410700ea0429510704c0c2c1d05d024580c0080c0c1784150b070110341d011000666400c4140074540440440c00e02c040303402c001e80705510510829004078601041340c40380d06d229129005611014407405441d21a5000c10003203c80541c90090307906000750140051004004401010224030a4000d4045490144005003155 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 191665512 1250 191664262 191664269
    0xa0b0a030b060f010918180f030206072d0305090c0d1203060803030f060f010c140a0b0c090306010302042012091219050a030b03060a090b0711330f040606 68
    0x1d0301c103206111812000005004070b0050980000300900c487d00041c03004d0050140243c600e47c1d020701a1030506a001c202503100710001d881c0d031048000c04501c02c800c82c40c40c4030a4400e41100103400b0b035454038400d80040740c200070701c1d104880c2d0381003c130400511035141d4020f0445140c64500c00030030340c02e41c140c002c0400a01c00000036608618000c844809800c00003404284200e0b4010b22100ca42d0707004541004105402c621104030101440d940207589464018080d40c07039054100000301c0c07400380d00d000c075445842e014026041a03440c50f400d1201030019076201301c4000d001300403615010302c0000040c10f42c1c0c0e002c0001e2150141000c826a6041003c001360700c00d031b0410204040c10000050200c4c0e44070b01e03003840c581079a80e00c1d0011803c07002803a10a1220b6810f00829007804000b40300781c1c01582c0084e02910a0b8401c0b600d035100140e0750004445100c0029801c00070340014422003400a42da903110a00785481030340c04100841c09100302c0d00300c9601002c6900c98007070100348419846400041c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 191666762 1250 191665512 191665517
    0x3010b010f09031b03120302090411190e0102100e0a0c1a0403080d0b060c03070c170c041d07030c0e0a09020108160903021e040b100503010e0a0b0a030b060f01 70
    0x466150281c002c10314055400040c011603500d0b401c4c002d040209020000003150455a07540306000c03403400050281d4084980c05220394100304440d000d60314000c0458400030510183c25150302034440c000e0f6900c5100d01a91419401200320070022404140034500c0211481c002910120100b840c1070000c0c844d4941008138544c4054585030042d061400454051f00d8000c0011500d1702d08454601005c2e020b180010f9401171004601d004030340788000b000d044000d100e001c00c6280162542c141481d10440003902151030740c0240040400c1d4105130f800f18901c41c2004151107401e02d00b000b00c2c203240c000315600442e4541800c1c07004101c4076210380a0b10390811452a03003803200f440f1a400082181001508500710070105620300e800040c002c88083d401544d010f0b00807174a02551103212202d4807a2002c0550081d4144592a4034030715105411b0f80004845486d02c60459003001052081c0c4040140b01006d11541c4035800700c46a900c62030f601c00198458942d4004525040c414400c1c4c440314490014103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 191668012 1250 191666762 191666777
    0xb0405131b09181b0809010b030a0308010303080a0c050a2001061d0705032401020c0306150a14030a030834030b09070c02010e0a030611040306050903030408120601091d0603010b01 79
    0x2031003240032020310b2010b01c0d1500d01c501d80c44841d1b8032401048603000b0a80d1501c00e105000080540004600f41280e000741c4034111240d948401c40303002e40b40b003208004001078041120409141c0100b00c0300c040c4581c10f007503000b1001401e807070140c08c440503900060501c081022095003020442044a907001d040ca01d0440c0c01c0d030405880014189024540c0001662160315240100764030822030103007103550040407036109007131400c0078015107003011000ca4000d0b500034a0101c0d03124800d103084454038401400500f120642620700300ca260f03c024104100c1011560030900d0111030b00d1056160740d0010380a03402d0f540d46e03294009411612031640c2540612415030400001d6904070032600c1a150b020b0a00c82c0c8817090750f10010b503640311170343c000601507454200800103c2d40800050070999129000030012615495649135a038042140d00501020041102c210070751071268800340c100b00306040800039140c0350804650507000840580b4401140c0c0d2080003000d181c00d004082070b510f001e090150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 191669262 1250 191668012 191668031
    0xb0901080604020f010c0506220602161b0501050904051509040809180402010f0c1707060b090601050304170a0909020c030a0206060a082a15030f0c03010b0405131b0918 74
    0x1619000e009140542c08a181e010ba00030340f032a0078103a0300710540cac403950031940c40c22521042c001098910100341e0724000c45055104104040100c0c0c81c0642d00141c6174141020615401c2102415000300249032031032424050382c00c580c41b408503072405540300c0c0324005d1329410041c01b40032000302d114203215050500b132002d00000d80d0300280b2040f9100312900d0a2444039105040c4048480ca003078030441c2c40c0b4040001c3c0340081c451541e100302404141100d40780c00e69210040111414041520080d04602c09440d26001545450004104416103420128003050345c4203900b00c22a00300400e0341c9015003002500e00e0303240e0741c14440190705c02e00c11102c0030801420103400f0343d0f42e400c00c01d9101505a40041103c0011440308690f08141c0e40b008040007090081b0152032007194105072440d030203c2800c0c50200c0c0141c1c1001c42500d05031030744070028500307141c07a0900b00322281c0d54400d514980503603140d40d081446900342203106140642d03500c030000490716007510320310342140b10f0399001c1281d8503200002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 191670512 1250 191669262 191669273
    0xc040f0311030a0210020c0312042105070506120f0601140d020a09170106150305090d0507060f060b0c0c010c02400507030609090b06130b0901080604020f010c 70
    0x1aa03070040c482040a151070404039107801d0301440081d5208041c18040c4804641c0001d19068103001a0286c5000744455100704c4124022405a00c500409020140340381c55058071142d14803d02a404580f14981c1d58004181175600c40c2c80710b003440550100030015480284a006134111a0070704c3c11211304801400030300458002c00d4880c001c1103400003a03000c8040d120b061090040d05200380d03a055040f001c01207150080805100380e20700d4901c16940c2c0c13480329000b44586071294010002411502c0c0d0100000c0320389030311803013003240e003d517450100300b1a0030041e01c1414081c211070070340144d561075082d00303e43c900800001ea490402595150900050315408890342c42d801040c01009005400016441a200d4507180000340d00300d0032a030740805866564001760b002d000542c90402009071581f08480c00d49103031910151480300050003007031042c00c0c90310804005d0424005e00040684102e4000b0b5840142a0700c01952580000240015860050019541b41000342009a0008601d51341d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 191671762 1250 191670512 191670539
    0x90203090c0f0603061318050616080601080907030b180a0302070503010e0d12090c030203160f0f0605120a0f020a08010302033703020a06021207090b03011a030405010608010903050a03050c04 84
    0x2034902030744846c02404002c2c5207480e40c90387c1c41e40c004240c580d5850644013101e01e000080f070ba40707000140b845000c2101940070b500054054030300080a4100d0343d0560701e45003c4100c000d40382e5040469404c45045070710b1001e001c0c00c00c0091181e4081c103201c0d89850b080600303540c5402001d00d80e6800242c4072007409500a120314624851481002c203003500b080c1040c0710401819070010b0740500030120980071003000705020006540a03d62000003c0d41c0707070050000801428094480416010041150011041c480030340d4000c4c3c0da15408560520f10441603000d036008a684040443c410300010310862078140306d911103203050792091b0110307a01110710900440414140035020014400d55a0b401c2c18800d000d2551a10741100e8159a034400500795140d5209013103540d440000c144c2080484d03945501411a8102d500521040c4840300d1545c440001c03940c400b8204940941d45c0380d8002400395000e0007207440381402600d8054403010081030240560340c3c000c0204040070301c100400d2040c01d0040c80d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 191673012 1250 191671762 191671789
    0xb090a090b0109060c0215030708100f06270314010207060e06090c0607060609020f0301050111150615070b1015020d050304030f03021c0509010e0105090a1209090203090c0f060306 79
    0x505e04808182c50011454010750745024040240001080014003a0020041c4d8000c9d0840381031844480d50742e0090b0001040c40e030181d000001e1007102501c015200c80f04042c103c0034070480303844030020380d070b0f9803030528441c0c11121880380c07650040303400014442c0f18030540c41a050407001428040c03512128040d12008407040251160b0340100760a010300c8130035803100029000c01d800c210f540300c02c2c81014843d6074000340702e41400500c0c02d8017202451100400c10601c03403060345021003150780390f1200b0407030114058504004051404e0000c0c2d1701240c4000055805910925804003607181005809003032140c10154070029580b00704510341380c840d032140403a5030040d0545800c440800c402a8120064480c45480141c6040480100000190705034001c41c011140b850017008000888a02c0c41e0980b41d0441e10001039412a0754080d020030b05205d411030500103580b500d40a03054469420200b00e800c103640d45130855200303040241e46800c000d040d0044040c8100c030003a08620340b8100148040c40030b0305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 191674262 1250 191673012 191673017
    0x5040206030612191110020102210c0c060c04030b0c0a0c0b0a020706020c010b0a0501091a0901020a050609011b031a01140c01020a18050604060f0305100f0b090a090b010906 76
    0x34240c41c2d5042003030040400380c841e400c84c044090603440c10b1810205403075022480c41803c10b030b0f001c0c50301507005200710b810080840500101ea0001e0000b5881d07180c000801400e0602e0080008241d00c030405d00c80248903921600c0b032561150b0031414445004035008141c02c1e0034150402642403da500407010b00c1c600ca034072800000c02559102c40c03042c042d008889004241a0022070212203c1506402000c0c0038107041c0c808404055648004450700a000d100e03003404400020b00100b00340500200503d25114180116400d280340350351242c0c039181045504801c00d0b5074800000083d00b4001d019101601303061f2400b48961003c001000c2d01d104410401e09041c0103a141004420341e00c050160745080d69014003c6444065400703000c2c09481490000b03403000c208486010421b864440300b502d0644415649400c0141741484042d4010580171b440b50700344195a034400101c000c3c00700708030006000039800e5591150a02402d04c035074142c643d04801905801c1400c1c03014140d074010922400c407603861 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 191675512 1250 191674262 191674279
    0x20f060f0604060e04080307030e1204030311010603021504031104022113051c030f09080702060f0702030109080406020c09040201020d0c060e1209010f050304050a060914070e09010f050402060306 86
    0xd40041d0080c0019440380050130b040310200000d201100340030314455190f03a1003d1001c00642c800c1035890702004040d50081007414402070000c03034820300c0880c5e2144c0e154000011981d03100e800040c0039042903900019004d00c0000c090041240700d0400780141603003a5419800c2000301109811504100c075001c1041001e03403c0040c18100c810410035000f51b0304181540e1280c0341840341108001d8208901e40042810f00d000c006c0d4001341c41c0b0032022880e0300114428186100d40e4200301e1658403410080b241c22906110000c09a84c1c28480c02d1003071449480501d594503d444d10290074400c408100610030311131b4004120150340c0101d00d00030120820b191002c4503000d81e2810500428842221500301e10603100040210003214000b89041c0d18240c8900c40460f4800804039800d0ac41241e00a00360b0300418050b0f00040c0c91508010922446903205103484190050414a000c01d180c0c0600c40c1d5001c00028001d403030000784601001c482120701c0c140941d2410b6000710307684e80700281c101c50188988 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 191676762 1250 191675512 191675521
    0x90604030206160209070e121c050307021e010c08061c0b0c070b130201110706090e1305030a0e0f1e090a06170a1a07020c010c060204080712060606020f060f 69
    0x3c00e614807249540101803620324184140004c01510301b03ea5441d0180e50717010b01003403982000180b00d8540d03034480c030807141070310034956400c031010b82018001e072065100744403024036011001c601c2c1003480c4c2902800007400c100140001024034001078411805a800b40b407a81c03020401151b0b0301500240c00201302017860b128640061510b118149001c3d107509000b00c01d20048a454403007070380d1100c2c000d0f40da10100420f0391501e40d07125400c4d0322030500801e2007e10200000c00e12001c030b01d0343c00001d0792010f440154080d00c50506541c8400b000d00b00007048510f07460120310f0010541c0701c03072500684861030f04001d001050b401c10919a89500d1091402c000001c5018034540c2114024100707250904003030280c10781c0b07026aa5015200200c603211011203202c0300c1c490f02101807920a070110750080c00f03000504801035038440400103081da403540c3c08200110754035004000c141e00420910b100d10aa0400909081c2d04480d929002001150002d01d13807209000400150582c02180d00401c10102e42c68 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 191678012 1250 191676762 191676787
    0x3050c03070c1205090607080403170901120507120603050105060103050124140c010c020f0f0c0109050d0501060b0408070305071706010b0c03250b0609040203060109110c0f0c15090604030206 84
    0x45d038400c1d0741c1c490070000e03001c0700300002907000c1c0c000c80344030f01d82543c40160b800001015600842c0ca40314006000c0c03085400c950451504041c0d045811810611022541741e4078089c26a0001e8006803051384d111002d110f6196490710946004100d904a1039006c5082c0700b15030a50600d0208540d0100b0001040f20100c0c5801c802c115403226054100800a640c58090003030340740c1405258a8003503000c1e03c5210312140d0381c082101000401c0580d2211001410f1078100800c0c0d82104901744c0d455981c0c0c0078085803030480400104094074001d0002c00f00c851440c50540e29190b403e4112201c8034040034004040c09200040c45810340e41400201e1703403500c110149203850744c0101309003500c0c3d4005191103d60000d009000c4c82c1042c2e400b07040d84803401d540d91820302001400c1a00e00941560041b4010840034040f0341c040340703008400741c040500d883d2011300e0705840c000c00e46c0450107264100030000881441d000718000001102c1c0c0d807505082c00142c03000102c2d24001e42c880a0700a21002558040041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 191679262 1250 191678012 191678017
    0x5060f0f0112021e0d060f0e060303040905040524010f0501020a1509020102033901140109050604150f170f100209060705101505030712020423130303050c03070c1205 73
    0x4c0d9003104494441c0e0050b100c005c041c0900f44074585182c1c000c00c0010a0b0500348070000d0303200300b0b8007800552401c1e140c0401c00c001004010410f480328019940c0307488038860001854080301400030038031151541025009400241d01da486a41554050b0440c00002480041d600490030021480000c0080305800141d065101c1d03444900e8400c48001ca400030040012003003452000109012811411927100038076003242ca642e10302d0000c0214180c01005240005e8010aa001c0d07405400400c4078410300401d0007413100d40d43c01201c031031251081e0605c0002640521030783c0010307503c0000c00745414421405034680002c8541c1080003030700007550307000544545088502441d402021107030342c40e116000c100d008004004a0603411950000006514900058100c054070303a03401c03620310407192a03400c1000800b511820b685800d82d6403007111b24680782c084440e40c03081031160910315420085140040403a14010408102040e050080c40f04050b84004841c1415030700040104050030b40440548850 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 191680512 1250 191679262 191679307
    0x6040c02070b040603062103230d0f0b120a0f1101170a02090a05040e0c04050a06050402070b070e0904120c0c09110a031401050f0d03050c0102030a05060f0f011202 72
    0xb0380080d0024200340e140c0c0c01181101c10b40086200d903202c04c0310398400129007071000a800120340001140003405c000468420f6040d003600300528103402241d0100a039511000720800450303550800d401c0380c0c1058100e210064030503201820402e47d507980d440c20302012080010f4580c618041e0035244590080c0c80555122074500d940c0581c9260101c2c080d0042c0d8419600c2600450000030700180d1030030f05008610003001070b0701c003811915803020140001410000c0022191640702c04001560340c40d0b45c03000b0f00d4920b0040400007103600d011080504005481c01c2d0303480c0116403180070000030449140304161a0750092030312003c1c070b0010303080201c5038040e1a006010204c1c5801c01e4445160400310041604070f074a911705121909001c500f200c0040d070244030301c41d008200c683c074035030f41494119050038140b407083c1852401c0c503040510003401c98204840011296960b5014054a403602034010040740c2c1d0200c540c60050200040000d0140e000600f10804080e008605286d040324a54014400c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 191681762 1250 191680512 191680529
    0x70e07031e0e0d090807300803100b0306012c04140105030d0206150d021306030c05090c0c0a0312092109060c030e0913080c06090606010c0b06040c0207 67
    0x121000d81c101c207008007000b400155080c410f0302c0d690111540100450b004035030650014000c0c06190082c4800e284451311113115004a00b01920300300070070a03456084105000d10078058a03443e020110700e80c1448140c2210554680500030032905a81c4002929490700c0d2000b0954403a0107440110b600740b000140026501a0516511102591009c100c0604032042181251103800c1c0c07801c01a0707213070ba10690f0b4495a0201800c580145030400e14265084a803002e00f80b140c1c030482e201007050440b0707810b8000300c0e03403808000f20800081c5808042c85811915031446545040c0344111204d0b91440d90007401018000300742c07150b640c0c1d010706502404c215500300800b06032a80c1c1000300383e801103030550f4003140854407480000c94800d00c6641102055071303050311a041e0780c804080c208840002c00a02601c0c1c100c0814030f0070300004108070040c00e641540080104042c1c202244020b040c201c001303180c04d040108071030791140441e01c1c614607503800100070703580080c100000d000201c1c104035494121003803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 191683012 1250 191681762 191681801
    0x30207030903140a02040f02040e04080c0a05030a121104060c0f08040801110d0c030e060106180909062003060114090414070809071a070605060109080d0f03050a0e070e0703 76
    0x18860020a184c2802442210304001244502c1030f4002240201d002d004040f440711400940054403040081c4400b2000200300d0b850b00e40700d0b580f40c6103180d0203a0501c000007198508a02800001340c01514207000400c11501d080ca0b0401da0000c0c0329188045002e0074080c50300c003a000503c60744070111005450041c00038011a5103041500c2c00c158800141c541c000c1c0c0c50800d103542158031074814440c814041001a1a03da40791510440d4240040186422001c0b840b15001410804902c603004119101c0e11010440e41c43c0c0740208800c42c2654003140716001000c00810030b590f0b80c45503001c550010480451034880b00c5001c0800c0060a0790b4030b008130045c03054400d0041c45c40d080f1014034891030210045415003920b9a12210b16075044490000f40c1c1c0c10240586000110603400c0154003482c185460300c4241da40d81070b01480c201450a0301c4000c594100101950140c1c540941c07940306100a00501c00388d24400c500940d42e074950301c20601c07011005004a606948a03400285191010755103041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 191684262 1250 191683012 191683043
    0x904090b0112030e0409110105180a030b0108061803310608190e0c0f0103090510051602070b0d05100306150626010e070c0b04140613050607030207030903 68
    0x2e004041200b58040b40d6100d00780340980c0340a008004002d54019880302c0f815000c54010b640b2500481c0e8030321380503c4003904020243e110107030000010360050340500065450f01d00003034203040001d0001c21a5516000400386581000403c90303945803124904420704e101782000c9524041014000010301007005880003132242d5200040c00d0080032030003a1400301a08080c008000c4501d1841c5001d51600700d02c203110240d1074000280100c00d0018100424000419640e580c10b20b84030000300340f4170340c1d9900144011130100c50b00d40340343c861150000346203079403d01081c0c0050740210490701074119150800103010a51007042880159070041e01800000024095a0f0004000d4003401e40054503100000c0481c8004450086510003030030008400c0ea401d10201700a4030800810517000d2140c002409070000700d80c514000c0c4641e000301d0f2500c80031142c001c501c81c20804040d0250100c003001182c0200800d002054417a0044510304005944440d03514090f40c40d00c04a81c40038181c2085c0702c01c0030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 191685512 1250 191684262 191684279
    0x815040c0503030412060b0f030a050105091c0e062506090303051003260f0a030212060114030f151203031603061a07082a07050a030b0601050904090b01 67
    0x1402148035003200802161034009065a0313004c1c82c4541c2540b4859a404d10020482d640d1000403803d80140c400101390782130802107813605904200494070b582d0341f1010400041001d001c03c0300502c0320300c1032130100303510340000c028685264802e101d8414400060040040c429440358507840b100114001e1400e14070714100b50b8000e15591500380c011904000004071900316032100c14050381e0b40a42c14481034080e1429051034040080c16002001d4820040c8201c0c0d10004409008800c0c040e98025a9070081c071510408607110145c205818000900482e01c01d03d40e100068951048400014040700c0e55118a2040c41000c10f00710b131508030385c4059141000b05404402075210310744500c00c0c00181203d204003101114030600c05e294206444c4001446550210300044c041d55024102c01e50506200381c00b00f075841d081d00b0b030000e903520080b607140c03120343c000601c480c0c0d00404048035001c00161846e00c0e1072202000042c007240c108000000c20300520343c0c0e0b66000e410903a40012010947d0b684a4412 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 191686762 1250 191685512 191685553
    0x5041104151701090c081f090f061403030301122604060c030206060d05100b0a050402030c0301030302100207150506130e010606020f03040506300a2007021806030708 73
    0x82c2400d07403244000030815120700d00540c04001081d98500c0d240e83e03503900f00045038082c41c80a542c0a00c07243c1d070380020510954040d15182402c181e0b00000d20303d05d0f000c6025904a12802220f000f50404d000410084100c4032803041c5046d0000e00400a03400d01c00b000400c0d00b004020945440c00020401003403444c1d1240362150018841d80031250f140c1c8903c8100260400e62080040a5500c0280030844034415030308010341d06100505a96001a201e8001906a07001101c0a0145100100c010010705504202c01046c145864808601c0c12400341c0720440c00407a4107104201ca10344400c04128162a1141d0b03901440c085072500304003484010708468007900b50307031285400511031a18101a403010100032a400c4910050680c0c0c0381c015010154078108a8540b41748095a044164200c075602101d80c0891049505603400141c28001503019a0130402807160b500c1701d19400c3c040707500161501d08010342c0a440160030620165140c3c030001c3d180c074030b4a8101c0291400707584100310082156404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 191688012 1250 191686762 191686787
    0x17010b220e0a0b01020a050706050a050c03190e0a060903020409080906030a1a0a0605071401020912010c09140609090a0b0301020a0e03060c0307021009020109030b07050a0311030702070504110415 86
    0x41404090003c500490303481d5940c00000d8500d4100c1c003c2000218007035001000070720f6003428000d00305080c815130581141c00288182a03e120504607118480740d01c07801e080e0190b2400c481100405040c50340017001ca4801c3d00000380160781c0e84202a0520034108241c07903211034000c0c0b450303541c0e10b400400d000240c40704c808062800c0e5107441c4107604510b40302c0c203104240c5a09540e298100070054455125a08444d0210340b04e6540c04c004513041a00c5800b01d9444041b0400000308298424241c000e0050000d07900c1861948182c400c0008596034102c21900d60f12400c880500700c03034503600c54000c000c000b030064095066200280c40403030543c000440800181086003507451603070ba000b42081503444112a100d0058208030910502c4801a5101640380c500600d405071005450380d8401c0b05003034041d40c5078000302e000461483e03191b80d41070091b0f80554104e11b903020704600f4680006541c1c1c0a0f68000e452180c0d442d00d8450010388001e4080d50001c0081905001414000c40c5000c0c0c0100e80c00d85 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 191689262 1250 191688012 191688031
    0x703140d0e0f010b1c0c0503030313030f020109030e0904061e0b01030b1e011413060908010e0c06090d020607020301020d0504140a05060408030601020a0c06050306030d17010b220e 79
    0xc0b640800b42e80180b0a2280e840e82c0900750710130982c0f04400504940741c1009085800d21070a82020a031920108040c603c1544118400c841c0300d1841e080180c52102180801002c583c1000a0b20000aa1010b52481c4044040d600081c990f207451a0031006060541c0b9075403140807460f04104501001c9400c8060074031001e88003084550034050500103250f040990a000382c2c482c95501080951140b00c0700e032405414400514181402c01c1d5881150034040e6111000080b1007a0061210f08400e04c240b031540c00000c0000c1c0100700010002c1141070141c2c2c2d08103841a02c28140a00c1551a940202c80f0030700d40c028001c40da912981e03085000245810744069480105512030070840035400100c400303505401c203006241958640d0781e8182da0340c0c0014400c40c11801084559400900740b2601407010704400d444103512890450145441c1c2110255110200108850700842c58141c291045041d501030604090340c03081c0c1a0040d6903102c0c18109c00d0105c03103521000011300764000000a9010701700c8003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 191690512 1250 191689262 191689273
    0x200d02070b1b2a0102070b033402061e0f0703020915210f10180207060507080912121b04030203061504200d05100f080a12030606050406050703140d0e 66
    0x10303c012a941ca030103000d800e103403020800118500c2c80e0b80c10080c803003900a0700c0384901d0207100c0351030303450724a0030205200f000b5911007420300c180d02c00410b059040c410a00a0714440178640b1020310a80701c4405440c100600d5400240b94015403160241e100d0b060241c02642603030f503000541100c0c4280d102e4060b00c1c0d100035190b008100e0711184032642e2400784185001c1c49190781e0802004069910100c02c4201744258208103101c0002e90034001c071031103203085440d22003040c5050b040740ca00b8001c00290700d490303012040208030700f202c42d1542040d40014102d0004040451005043d000e188200d800182d410300c251810400c03d10401c0301c9080750b0f4001581c00740260b84024800f0041c08944000c01600e00f5400d001307241c00c40d40300c3d0b07004950040da0312400001c05559000200c1c1c0f004115002184607030042d4803000c003404006a020882c0c0c07070300c0745803c210383d03490121300a21078002c500505c4208000080e80700203045c451045548400740b003400c0156030380350484a60b03004100706c541c0d602c501d000c0d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 191691762 1250 191690512 191690593
    0x506090f01090503040306020903071a0a02010b01050a090911070c080723010c020108070320070209061c020603100b0a120e07061407050a060c200d02070b1b 69
    0x107000d10303442e040d4014001c504042c2190748690180d0841010a034140c030036100d000400580d032605000f601c06405800541d41c40e2000320080c251180c018000e81800703000c02601005076888451041100c802c0c43d400107812000101740c2005109200b0003405442c0d42c100c01181105010440c0404c0f14082c4a01602a071001030366041030400001c5498040b4605045a40c099400380c103070585d10804501d00081e004c446000304904150000d10031003490700c404a40d40e0304508011040f070342c10910898656a40307a030640e5500c0181e828202000b8010f0002101003140b44810104080150011640301038442c1400d410040c02500d1400c01203409908151200c4412000440c4001c144c8502d81c2e1801282c02d03000e40f50840c594440c03101114107204420807040840c2c414400d402483c1401e41e50b40900e03101c040c0c1c1e00410801c1c00c00d050ba040f900044030900c0310b84d8001482c20125001442600e8680f191800c00c40660120b448410b1168001c0c0d00d040303518980006a81d040d0141d6821101c4031903e030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 191693012 1250 191691762 191691793
    0xc0309100908060f060d120210180b0a320403080106031a0906010e03060a0b09060306090606040c05070204090f0b010b12011701111602150a0c020906011b050609 71
    0x35500c00c0e1520b40d009a00440c20405070008500c1c0e001c440540303483d070842040d03901e442d86541803160f008010303001821640c803116014000c030001c943e080981d1420402184d1100d1604c2d00000d00200082a943c40d802002c0000c20751115003003c80e4031150858400254000c0e250504044a084001400220000c20454000d100b104800c0b80d1404000d0f5600c1044d100344000380c3c0002e4503030b078140440021814400d1703904010440c410700b880324002c104008044244400e0a1003e040c09220f50020410005c4000000412990100d411140442c010850368000e4515101e0390300003a400c141041c20001c180031041c403140b000140b007003041c050140e0740e8a1420070b6902514103d1805142c58000402c4004000d90091802c2d010b000000034400c410054a05495170000403403800d110605502070003907140909240b0f106001080c105440d000b04040000c01201c19028028412848580403030a142d200c2ca0024444141c0403070030034841c0c4580d0030425510307141182d401200740b1480c00e1102c02d201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 191694262 1250 191693012 191693027
    0xe1303120c080a090312020a090503010b04020f0f031b0301080606030d0813020603180f0d090801020a080703020d060f0803070b01052b050c030d05120603280206040306020c030910 79
    0xc40d503070b40b42c0548800b1256409000090000d0342001118113a01500584520081c50388001980f6811030403440c2001749420b4504c6d60865611641c41803200400c42c0100e901210a10340308080c0c1300c1d13a01d60b201d010003207510220008000d0702440100010458480008450380900000c4080b940e400785076400450707201c9411070700074920288104508005041c04006160054101c0707898410801d0499000c41c0380c0003020001d500750358440c07420107010716044204103000d0304022000703604e40102c800300600369881c0504903104050f400141c8a001c0110340c0c1c808000b130714a806c84a04107039500c0c40295034941296600341c1e070441250f80001080d20b0f04910003010118011104544800701070480c1802c0150608190b4407406410b080098a42e81441400e6244406858140d15500d05c0360444060010044c81da5000e54012440e101c040d030350414003140040c03480200b2210b43c841605c007080c01d038000e5500080100d030002c5030a040341000030010f449140070a40d482114021040380c21980c41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 191695512 1250 191694262 191694281
    0x702070b0403030f27150e04050702071802040e0601051c050a0501092304020114161a0901200a02011104030b0105030c090f04020603180a060501080f07061b0c0e130312 74
    0x112201030701b003203042c044034082e180c10401c07800d04401840d201d0b008102502e80807240700300160001c810520007d20b8000c4c21892988013180118285814005088030422010384801d044c814040780c5101c52062500441c1490464194240094140f550050700035000a018400000e81422103040052200c03050711b1501c102c403081e450714036840e145c005507142100ca607009100e84508120a18800c00020010b008062103031005a0071140801e0b400c1d115014060311f642405d0f4141481c500310400f4215092200780407203200f45036a152901800ea0040c4031003100c050b82844040380c000280800d102e610b0f070498a080c0c7c02d0f43c02c0703041040108914150100d41c0002002004000b107009410000003031030317109451440c5100405054402c0700d19091100b007045403042e403a4001403000c804240451914441084000c061050414001400700003e206c441004c1e008820140c3d002d10004001ca0002032840000c90440307030504455020320484041d60960108164140400b4260b0310f07445280000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 191696762 1250 191695512 191695577
    0x20307020303030606160831051f050c070905090106060323040f0204110901020115080307030809030405090123011b0b0a0f1a040b0603010b0a05030702070b0403030f 73
    0x85039604010000a80c1203c501c900064008488450018500900514030201208c00010044c41b5a241075120541c1144800d040d0b160514400c101c20746540f02c1000c500140c40c01e00214554449508481d02d00a00380580700c0b034402d01e800028028641e91089018000100c001e0003204d44810094040da0b00e007001c40d464007803041c40d0380441d5003031034070995802501c5080c4040403421142c00107029241070905548807940d0025914420307680901c030f0000c0c4030885510b0000d0840c68640103e840b405142009014020075100003094a40184119405044021301c08400303540c40300001600380c4044041c1c104e01100d01c0a541680d903001d4406407045c000000c0321104880d4160740c605d07403500c0c0054aa644450307100d0450f0b013020601da0140c0e041c0c0015003603002c165181c054003007005079690952410700585041005004407000c201c100e503a4105030303062191340c944030403034100d1414500d1b900c0214038000c04100442016800a480c5030315602a94030000604804d0f0741a03008803c540c03541500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 191698012 1250 191696762 191696767
    0x115170307031b0f0807110405090609030301180204210c060509030706050a03091709040b010801030b06010f180f06090b0c07031403040b13091407080109050421030c0f020307020303 80
    0xc00f04007000080c0c88039885200c02c0428001da0340e03a4100d441c0c100f41c10458221707140008242d030f981050310445070301002d44001130419080104070286c580c403043c09202c40c0c030082e2507030100482030650115001404c00414000c04543c41d00c0e8a603541116101d4216020705402c240028060711030800c2c0c80c01c2d400014064100c503841d01c41705407501d0b80510303c0c070b0083c142c60700340c881d0100d28441d00c951840000344210980c0d458246003080111a0b0781303224207051003901c0d401170001c62640b407001d0b0744c4071100703080486000c049c01909590b03402c04001d1248006040c40804a101c4052680740b8088805a80380c0414080e1a00c800050b18081c400d540a00c940c028002040881d28120511200c2402c100c01d47c3d28007070316012005141d52042044844201c22a03508003c210428494501d01040c0c02040d9969800c2600c0c0050241130180b160300d8203141c56201240a00407440700c002c0c481c0f8651030780c1c03040315101c1d0032018010b03082c40611107000c2280e25004c0300c0418004421540d5480e8018051031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 191699262 1250 191698012 191698037
    0x40b091005100c12121521020303190507021014030604050c130306020c0d0201060315050601050f0a0305041a0115030e070306020a080406050604020403020604180e011517030703 78
    0x1031410410000c10041240307500801011420761842e942114609a450341c80300301500c40c01000340d4000005a11602001b00302c10032130a500b00c9001090390040d03440321403c050490000a10358004c800e1030345010f60003081c030000040d0300701c0000c0c0f030414400d6840ba81841c0714881b040d65240e04515600c2c29822041000603454985540300943c09402000310300c2c117100b407215940041d00501c2d0411242e02e5400580b6289405c1c040280c4101440b240c8024450300c4d056548001f0f22009100d00f00c5031750f584400100d01c12703030b00640a99480721602d0408907282e85a40c0c500401406060310266804500e2440d00201e48200404482c1a202c00500064050800000480040900184903040c0740600303080800001c141d800200120401e44c2d960960f142014180350086900241605124900c100402c2005840341d0060381e044803180444191800d000f4031007000540200c4c4c415602c254a8618144e001c04d0303120400b10700340d580d41d000b003005840100c034500f9501e04c10000054085200f4603500c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 191700512 1250 191699262 191699269
    0x72603180913140a05061005150a020106050d06021209010507140c0a141c020a030c15090f151415150d020301030305030a0c0f0801141206010e010302040b091005 71
    0x8a030001920849001c1002c0140c0707600380c502458159a02440d0041ca9504060100c2000015040300c88a440301c01d45070319000001310030800b809284030324904081441e1190a000794864030090034050b00462160880d490030318020340c0246140010200c103100491230141051040a210300900e480d400c6018201c00202030040e0000c2e401c034100c0c0e10804901d003000a10800d2525104c40b146001828083e0b421400400c0c0400911343c842e0455100101010110758412144c110381c94028906402e140403403100000a0b140e0a0703806408810144054010800713002508260b400e8074840400c5814a08460642626811741d845900140314803503d0310285011403080c090542914015031915900c040791206a030803d81c41a0045180413082042ca80c140b0702988454119602d4046000c000c0500b01070002c1c24180941810403d50700500071264480d54a11048090800210745880d0394428810a9900302400201c0c01a802c03d0044201410108101030060003000e503401c010600380f1051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 191701762 1250 191700512 191700529
    0x60e04050a02010302090409061b021c1418040c0215090102090a03060f02041d041a04020105030a1a040608030d0c032c01020d09060902102109050c0307260318 70
    0x1b00e584c0160364280300800140688101090328941284108080c40c4507070000e41000e8107080d40201c422003000c01c00820329442446015101040c070b0713049071141345c4011100c04840749211546d41045c60048a04c0c1243e400080300d54020100c03285c081065500c2d600712500341e020340c0030450780190204a0620000b08030b5008001c4034a40000014201541e801000083c4070003da4040707242255041800240841342008818003011103c00d44890306050340020210301c00100001200c07551403007181c1c40000d2110070301004880041081c0886911152816100d81c000400d0850541ca0314407140c500341d00900414280300c104189104812032506904001080440070089080d5802c0000084e050901d1203011049405444000b80a40c40e40c8140183c0451941c0440240020201074000c0c0700050312900040d00f040c044041111140c40ca004da03c0c05011401e820f5050040b044042101a90b0343d01244009060009000400c0140350590f91a88107400146803000c03401110a040c0e81840c158 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 191703012 1250 191701762 191701777
    0x200c01052404091a0c030103050c030303040b0408070f0206040b0a0207080703030207231305060f0f1003090218010e07090b04030209070509011704080a110f07060f050705030a080604060e04050a02010302 89
    0x440c1110070b031304000d10221902048614611880c0c01000500600804001100d034018098009602c0c46c24141c0b1040070201000308000d218810000344441007092a010303441c8540c2c0d0150410762607a031140d150380e9041d0010305150b03005125180c80041c0b102d10000d0114110f03030b0540c02a18403141044051008807080a0080300300000300352076040562281d600c01b5090320039070400054541065410000c1c040b012881044c0305c1c003403400132030109607601c6640300200029410000780c4d801c5144080b907400c40c1c540640103100c104000c00040c2c0c0414201449105100c00c2d524000c9407501c2d8010b0b0301840c021400301940280d0f8940004940ca801b9030000c001c0d61005040102c0020344110710341011100880d821540c0c8030020034082c00d40b80c0c1005109038041351200180001c02280c0d2030040d03807174429100e51810026091103000703050f0b001e070048804080c0c1101c01d6950700c0b02c0100f03000d0009034041d100580511b1400300e0014881402c40c525034021a40b04019203250049070300110040d4100c1c07007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 191704262 1250 191703012 191703023
    0x1052208221a04030c120c2616030614040c0308031512011a01210902060f1303030e060c0d0c0501180606140604080718200c0105240409 60
    0x1c1c004a903403008029400304a0b10407088441c0e6a13800c51508540f0817009a100341d1400a100804400050030840440f043d1f1306c0705030703010741d0303101c86109818185c0c82da0300c0341704005024600340007100b0585440000c003900d00074182809041c481807610207448104587c0641030b4045a40306100003000d03035005640264280c0d00b20005072460f500040e500c1da0030b809212115079515095640c1c200d00e1090221800a000d082010f0166000d01103c030a2011045a03803010f25600d9200348119075400055643d9084c40ca480141c584116484a45200341c042c0000e8001c02d0b805410071049142010454028100580c05090b003003d0145064500c0d480151048035155201d01d80d2082c040c01d58502c42010602039440841e4151510500d03200003041c1c0c51499015030802c00c010b0000d2038001880c0c1c011170701d0039031a405001440540c1000281420641418040248035900c02d08000a401410248096000811403074a81009115920101c1c413100d490460403c4902009890160300001e4014040c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 191705512 1250 191704262 191704327
    0x9020d02130e1b01090b16080316021203130b060d02091608010f060516080c01090c03030f020606030d0f090314030408100917031f0801052208 63
    0xa5001545055103840e55024056a544a0030020300041285110b0300b6040043c0e500328810a400080600d410b600445090b6403000031001015400210b01201441d0032080440e01c0f03040c0107a059041c07102c2526900011310401d141001c2307001d8440112401914544402ca018110070399400c6514400241030700c2c0c1c8000220b480314003588030321544611601e0100d0307200029508111010385071200c10f07044862031600f0640e05012494000f01111300f0000c0c1d80e040c0741030410452805624510507050050002c1d401c02c0015010084803c50303040650380f20791240c00c1c0d05c400003072080342d8409007140c01740d501d0351013107144a107618040c10700c0013a806030500e0314a80c5561251958420b6451885004640c0d80c4002410001c0704000c0c0824815a2200801403010030160703191145602500c4000881150303002002c00c1c2d91084103207031070000f401c5070507030303c010300b40d07034440300c2d40202400c0710095050f180e0f600c03840c1280341602c051888040d500c07080060401c7d4601c1c03141045000705410146054040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 191706762 1250 191705512 191705539
    0x60c05160b0909040212010c0504050a0e010302031203130602070f020a1410140c0304080703020910030804090c110604030e2701031106130b04050406060908030d0b13180c05220902 79
    0x20b00030f8500c03d1302c2350b444080d0303218034020500a2007a100c0c4e00460511018000520069401250750380762200c09514003178407915003031050140822a400c00908251002407190300b0070039100c1c90f41c4a118000c40716820040e0390340e0031180c071a100c54140c01c1c1d84000c84c0c48c0c01c41480d07409038000440c0c01c03559401c1c03a801c1c5400c03024094034603407207504042e030a680400420021441c001012070760069003841048062440e5554144150080d4012846120b440d009414082c0b442040d900e0031400024040342d1040c01c1508000c3c10b01f000002803103000314401d00b0403c441000310000760480c4001e0700e0440080e0780c655100c07020b140c000030b042103a006004110160180c106800e0420140c4806c030482682c0707900e45000c00084400303951229007030014201041000300000f005507240c0704c2040c0d00118a90f1305202c00600b0382602e103000c940609141c8a0380300480c0a41d80070120310a032040c0d1310941c1c100c2d2140e04002038465144100d0a10b00056500001101e602d81c1180f407289102030280c0e20809107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 191708012 1250 191706762 191706799
    0x709020c01150902070201200c10111b0604050108060d0b04030809010c09050d03050d09060509010209040605030601050a03080c0c03030712080a0903080117030d0501060c05160b09090402 82
    0x122566606440c0e4460000030504042c0c0400b0034018683c2ca00d045241649560018002ca42c08804032528024000d401e03009460084c00440800300004086070203401e2240c10142c55800340c5201100d29200b5450300d002066001610410300c428010512410903103820011038580b50b00801c1e0641000401d1032010005113003a28807400b40744642c41d411518030b0000452821103201c01025402c00540c0041002903403184a0009030098041c070780349036200c29151185003d401011001415140791404102107a00103502900c48200f080b901804826541c104143c0c0d0303060207005a9038000d02c4032404000091241009062030300d0000d090718041c444240000b421500301e1907040c0c40c2100c0070702e450b041080e800010141e2125001c4420040c0f00c44c0c64800411040050003410080c888808608220880070000d498028111200c180269a105e510003407420b05035102c22a01441064001d582da511f002005105541e91020840e00b412504010402c0c4540301400c10f903004042e903d4805031815 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 191709262 1250 191708012 191708017
    0x906040b0406080402030d080c0403020103110903060703060f0905040818150309160b1e22080c10020601140f01034a100c1b0b1f080a02090702070902 66
    0x1c20f0748a81641c0c1c50680141070500c03001c079403200c080040400410200d0ba014105440c107403502071030001a03000110809008600c40c186071a60b15114010801c0300d80c586c1070308101c1c240c07a11204d9030b200a41d6500203001c02d036101a600280883c0d41400301e03200340346c80082c0c10198084010144e452000c1a0900780d0000c0c2d100341c0b2000140d4100662021604400010f420002c0204d00850303440c0040701600c0005941c090008482c485070700040d0070509520b0f410142e0b100000a043c0c840582d0b82d83d00d011961aa07003441c0013402560480c4601c8003440c00481c00701c0c1220304046271403030000b04502c00c00070110f200005a0f418560f88080c80340e050600a030383e81014030700c64040070341103035235440d01559002d2220380d540a0b41d4944003030380081e031403011441c1251004160804907958080c0030040d40e080070721822074290405007090b44014411895a014040c160145510040c0820b148031819071182c0c90041c001194410150380006080c83c1d100740c0d034059500d1054603001d5888100c400140c1c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 191710512 1250 191709262 191709269
    0xb040602040e07050702010f030b0f030d080f1303090605090411030c0901090b03060a0e0c0d09030512090a0c05010c150609020a0206091b0603222d0305030a020906040b04 75
    0x85034041414041601d9031142160000f2860914504203041580024865106d014000c010542c03030342c0f89078445031241003846a004800030b0541d159041440c03402420000110b8041c032496000501213603141001a41e081343d0140c03d0395803080384a00307104054801344c0c003000f41c240e0840e540759044070641c15a48040d502420301151419071783e04c000070004000c820607400c040721880081091010035a0340c2d42c0d030a0101c400c01c04000c1a16500d85181e0748460065042c02c0407030724201000b1070200b40e0300000410380d00003108003440580c0c0f101d4604599614448000274000741c09000c0c240029805240b24840142c420142544840034071349480058421540c03144114640101e1841d00083d01400a142c0c060526401020426400b21101080e5072607401c903503005110002c0800c0c007a0b000d01042407007684802d1540ca0440c00140760070311101101d04400c0c04e2715040445040700704140c117418441103a4260751002d0540d01d90361103c10080d408907046c1980500104800651810503a02401c000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 191711762 1250 191710512 191710523
    0x180b09210c0913050d0f050913020405090f10080d080c0903010b03010e061905060a141215010e0a0207020916030e06091e0d02030d0c030207020d140c0f0904020409030207030b04 78
    0x25500c2c0d85810380c0b0700080c1170b03501d0060010003081c40d01c00561010648d17003d004101c9480c1d10041118402e48000d10454100e04e070090310140400050b070ba0700000d1a400b6051741d6141038840e943d41c40005445100008440001991100200e108660039802600095600030000070f0b0b4241d41c100045e084850000c8001025003000d01000011401e0329030b110400c845c6150309000f61310300704000420700b10301c0e4010042d4211010900390400c0d1140e40414885010f45000c982a011107400c407606080001d1040510402171030000419429050007520281c55029045030455128401100c0c0780169000c1100704041c2e5aa041002e40f14040010602a4684202030704100c141c0041c418540ac110401101066200b0030703003903142d103a00004075031300401090400544860107a4007180a840f4082d40a544030a00d100031105003c0501c181d0600c91038802e0884810309014024400380355003004120394045070743d00011b0f000d420250410500581b191054505542e16603590b880b10101c117482c2900d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 191713012 1250 191711762 191711791
    0x9040c0504050a0209030a0236101202010203161b090b04050a270303110408030d15060c0b0405011103190c0804080712031b180b09210c09 61
    0x16003000d00c5196040031111030f00354903050718000880c2c1e886a04003402409840c0c1c4061114044285800810070781000322640345164031407409040380d6000c269110300300201c0740c410002c0c8010000c0d078400800c17541a000740d400c0c0104240b50702c200711030303e0350b00ba24401c5021200c030f07030080307400e070300900103015081000902c1c3c590180034441140c400a040c1c2c0456481c00c0113160003140c2951028040c44600750020500b83d41d1842c0c00c501411114072201581c19010401040e84a000f10251880d01802e100811066225145200a120303082c0b00d4240450300c258800e0b408244480350307441c5d1050151001054450300d004041c070081d030040300d410500700b500c24034110a11645008400d0340e001c40d8036110043d418191501c2c0a10701c40c0000060501d0004410b04c01c10600940105d600e00d000c0d009885401d05c0c1d40c480180040104c1c840d4284441016400071446500300c00c2038030000c00c00039058004000f500030802c1d1001c40607c810403524400c83c00c64031105e550710440944158a880a041c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 191714262 1250 191713012 191713019
    0x1052401140a1805030a050712060f0c050304050d030b150a0504080303040303050103020918060705030603160306020a0306050301060b04061121120105010c030c03080c0720030c01020d0f180509040c 87
    0x300485442d008184650403a400c6c2401141c00010b1640650f060441c01d0318200c1440e1038084001d00f181d2900d01602424600030740d1607140c06c9000b03540b00306d000d031003660a044208a0b08908a40106004941c0055590100120680700c2c8015002d00e4a0908050303240c07075160f010007803440e0401c88040b000070b61940018001c50070080b540640000007140c0c10708804100d1034045488100040c146c004205001c0000b9009680c10024036400801c030583c40010366841e0708111005e58004000c640209042c8940080c05050501c80e280482c0c410440041c2802e007000c100b2203010f40d178610700c20414424284503d15604016110040c40c01051114555806a03942010000c1d04d0580c040e6040c0408801c006020940007030041c20107550515240380b050b40c42c0d00d000c0b44503025007034000d48103010969140c42d40c05170010341642a03550486c00c8a52a0401400481c0d40d508030100c55000141c802850b01c1b6018050440710720300010507048082d107140c46d04042000010105c0c0d042d0341900440c0001c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 191715512 1250 191714262 191714297
    0xc06041b0816030303061e0e1509040f1407140d0507080f030409050610050712111221270a02120c0a0905090705090411030307030908070801052401140a 67
    0x100003442c8210b40c105001306030382c201f605440314034030035804d0322039072000000e00c08406000c00f451070f000001c280203000c0c1070505094441c422040b008a5403581341c1080198000c40000341d11046401e2040d0300e4114400c2d04c0244002d404994200316890b210b0b13224003042c1c041080c0821014280fa2800035030304d50b4034001c400c0d000d03a240030f40b4040c0206107445620340c0305580310040341e85d080d401c020710000240c1e9201085031484080c1450000500aa900d0310800c440c208005064042203402604182c840a211180005d01d0959610200740060001c034042d006914511205210004090314070941035038010490f40c04800c1406691038108030f090300f5540c503003000180003800d21380a04010f0740c5400f003d17a0b42c1e201c0c000d00500d0703c50615040001e0400600151079906004040c00303480e20343c40d4a10307000d02003020500070100180941400403540c201c1c14840c451148050300301b01c0c13001c040c1c01500a83d21044444c01c982c1003200540c00100182c401034000d00490300140d803030385886107846250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 191716762 1250 191715512 191715521
    0xa11060702120a061a010c080c0a080a03020702040b04020c1c0c080d020304140601051309111306030203060f0403050313020105090a0618090e120a0917010c030b0102030c06041b0816030303 83
    0x110569100d400d21769509a680884864525940092143d0741d41c4000201c2c0340c6044101d8000a01e4800c0001d0300311001c941c9a0050810548247e03414812554000108002da025408140c00d0f25400000d41440410500c400c3d2144031045003080391441211782c0301d40c030306a40151034071030750242c00100788001c010100c03401c1d6540c00240c0010300025410140020300e40c3c1c41c000b034070861850701c5104d04000d10448440503c195130000b80b1084003c0340140b06100070703180c103200030381c402e000b00000500e48144001c0300a00c680d034103944181c90f50b070700c0d000185d21701440a2400d034104103050000107003c1e1503c0401001900d0359846681b03042460b01003640b83c54107035802c41d031051410700c00c0354100755030001a068411512003900c6510342c0200340040320b21210607444410a100c01c814404007a5806510444c1702c017180b03942c240308840c0c83e5001a40d40e84a00c1241c0c484a0f0701500003c1d012407005040c09102c01c0c00310107401c5207199251000c0385040900f01c1c8a043e10700d0300e40340400c1056054490b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 191718012 1250 191716762 191716781
    0x20d0e0103050601170a06050a03050708070605120a051b131511101d070608060405010f1d22050705031629040b0409090605010e090a11060702120a06 66
    0x2070074000b03880c007000024144550384516003d10716203000450b10040242d00310b407028010107000900a1030752030809a955011510680f1900e0094890105510740301d4000c8540312000000303030350000e440e540b020030020035000342051198142c1810003a02074031f00d10300034140020350304802071403181420b00004400b040c6502210501101340866501c0c00d101040211844401c204000340c5016209011f004407601c48418240c9070041c54008500c15030456511405040107130350400244c0c2c2c8401c0b144296007590301030000c510050a442c1d842140e68510001d5200318181c0c01408903c00340030f02c030400d00c949030204880f02d400c0280306004a08042044e0401c5030380c0d81c5007a40001d45882e5411080c80ca590940401001e5405070f0003210610203070803034004186c0ca000c503903622580c48810400400032000d0495140303051074000291100301803035150094940401904400c1c0c001c0e80c801c0040c840c68016590000c1003800384101603624990700d9010a1200405000d503581c55181c01c1c3c0466103c01c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 191719262 1250 191718012 191718017
    0x4060605160204020904060e09030304060606090303050405061e13091b0e10051e040e070e0a050112090b100e0f160807020a200a080a1509021203040303020d0e01 71
    0x8001c5074040c603001050040c0e141c06450050b0303959081030104001d0400da030040b02c03624519600b406103903000000211320460050340100903260311090b0848010300644005000a0340a0000b03211610b070410090600c2c00c00c203c010781c07100c141c0b413024850f40e41040b5418914000c04034402c124030300803402015200c001080e01c0c5500220406006044510761340001c0780100c04001d040d40c030b014090401c0711401e07044101c9110b411014024140c0d1598400c0c0141340c884051403003c03402c0d882c0200d03130b00700c0100d01c0204115841403c1000454483c480c210703054080c0c40e1501c030b07088041110740900c54002c0c021100d001e4402d904080b0308402040001e05010056000c1508100115100010f084040030803490007890984520300100c5c0f5004a5170006008906400d400b8000e202c4111144440808183c81c80f00b0301c95034580e411758035003103d6070b4060301960028011148010059100f1400c00b48010010300c0c1382030100079510701d540c10a800c00c801682c4032100b103200c1c854021001141074002403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191720512 1250 191719262 191719267
    0x90c0304060e0a05060f07201f021b010207050d050c0303041104022215030c020304050f0a0b040801060513090503070b151002032107051b1204090b04060605 69
    0x14451405480000d00103000d0559407411035185010610080310b0058020048505034240f840e40400e070746e2015942c03800462500801ba82d00142c2410003060702111880c058210046901d40401242260b4440d040360242c1c204a95601c404c006480c2100341500c8100050700c40700d00e4a0032a03d000c28030ba0050041c802c6c00e1144418444000003142d91141c0d20581281540500901242c041d00030310005a40e00f00e1006001d0024849021212003280c00e0405c4d0012521000c0384140c04540d00207542c980107810400050049080040001c94100c0b809401da040341c3daa6001c1012041d04203030450b000c5a5111881000b9500e0480c080e25185100341d10100040403440e501e4694a104030400241601106800540b0032410f05511000e4010302030701c0307000d9002d2503240007034a80d40714022000c004008009400030039004203c0c00d511074501916901c1c600540795140c030642c1c0c10000c00a81446c4100040d1210440c41c1d480944000d101c000e101207000d10341318042006603451a0480307130400009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191721762 1250 191720512 191720521
    0x70902090a360b04060515041707032f0105160605040c030506010b091509010c030804051c030614090f0105040b06090a12030801121203050a0b1302130509 68
    0x2410003a0007100c01c0b1002c5210a5610664100c03255600002450004002102c01203510616038000500c030703503002c950802034943c440d0200249200c2c88918001c0742e140c18003090007241143c4c50070313a400a64050441c0c1c02c460ba6a540c1100c2c403880401484910754142d00c400744d51782584040c0803404c440900301241041e21900c420000e5052031840500502c1d140c0c0003040c140150b240d4030201442d000300c16280c0d60368587c0f84075691356010001941c00340e0703c000f419400341168030040c0c6180c1d0005a49080e441007694408440e8107002038800c3c0e91034040c84480b09000c0b40d19120444034803a454501140082c0350088242039007401d0500b00f405403400e14108551005803802c1181510320403135000500703441c400c01007902401401003098000104050100d00c0300022401d90704000d10130340d0740741314607a2100a95040600c819800030041000b10f001220700e14081c1e00302c0340c0e000f04901c07400101c1c00400000203205010380058000710b50380c00038081100056000c0800c000e40b8041e204e1001d142030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191723012 1250 191721762 191721769
    0x70e0402060f03060d0609030503070909050c0d02070312020a1d03030c1c2303010f0b07080d050c0705011b081005010207050f010e061c050f060603070c06061e0807090209 75
    0x1038880504142803000000411580d41c4944201c8919081b82003040b41e240d882c9005010f540c4242c8490021039541c0034005051045801000c2c40382250f0f000190411100340e96500194002507802c8040c440943d12040d4850070a1010b09007410440c1c0e07502541e490214000c0c0140000d401040340031350410803000c04000000298103410480420300300e90001184031044480d844e05d128050201100b4121031300340c1ca050760000c0e5040e50305000810301280e0340c41d0845070051044800040c400e80090003000714002c0707140c4c0566407028031207840d80e18040341c558130182152a41c40c113214000c0c070302c0d1809801159020b408141c3c018130482e24070b8000303410080081c4d51a0303000d03c40c29100303140030b44c81d2605692184080381740c07140d0080c0083e502d902c0400024a080c00c00624011001c2d440c000000b214202c018400358081c180190403a80343d9100c0c2002210f0490024406585807921201e0000741801600342058180c0c1803001c80342000c6040079205814030707070b807580030804003801449811030a80c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191724262 1250 191723012 191723017
    0x171e010905060f1915050301090b2d060403020a0b0c06070203042702041d070e01020a03050301051c0b0a02070b0f0106090b1b0a030c061b120b03210408070e040206 72
    0x1c0d021914621408007211000703c140e071881c0c20280e1085c00c106071050006130060041c5040c0e4003104014010b410301c070018086000d90640c5100c000c115032948100200d40c0c00004c900302c208003c1c1402d403038682c998000ca030000980b60700100707103848002069460f2140500c84103400c06000c2c80554a002c0c50181d494802041080072429903141e00f400301c03a2386500c1541218000c0011312918441c4910110429680440480310040802c0b8110b03950399035507201080781950507502d0307101e0505590034403082c816181d00707a84c545060a0050340e01580031480402055205d040c8011025960b614146010a1522030207480c04032920035a40061012640080030135054480c015101c0c0c0c0c49070081210b500700c15680c0c8a40c0d600c64010b20200c0c20915a004d44076003540c502400c02440307840d00000c04a2542c1c15080040000a40d034403403281c0d4102e04a4100080300710008003180c0112034024190028100b800e00c40c00301d4481d00017020020344100b4419240148204000c0e2042d42c40d05402280701d07833 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191725512 1250 191724262 191724289
    0x1020f191107150507021804050d09030b010e151201020a14040b0a0305040206190f030501061d1c0506010e0a0c14090d0c270b030f0c06030403171e01090506 69
    0x1041e440e0303c01021910580541d0400368008103850704030801c3c0340e000300301014140d4080d00c00c1e0080306010794105000d04040021294040000d80ca5a031030480b8426200c0e001038074244c44007075102e2051049589489600380d401e0781d28400103a4441c0c504030301078140e55500703842e10890310003804104002500c03001941d00403002e80c01d011a15640790710000c0c0251040c00442803008042d18040d4524640c44115005c41500c0ca48080180f662100e00640d10102c420703008030442d0642d800038050380c1c01c0442010360400d4440c3c00d07a2944403100e43d512810141c090708958159044981040070b825024061030780300000509200140e0209001d004900d8850310f5241d07030098402c40c15920400609080b175600501140c1e5841e80c0c0300c60080b180b005a24003881c0c075a440c5508010103041c00c6c2c4ac0206100e8901c1100100071b01c44404800300f0700c0685e0304003c0080e42400482186854040c0300901140c0c45031010001044024070301c1c607a940303500203041c2c1101c05081d2a00c1c1c104144c0352500807604405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191726618 1106 191725512 191725529
    0x30e011104080d0e03070801020f0d0b0a0e130f020d050c0117010609091125030201050106020a0809090423070509180703120c0501020f191107 63
    0x481c001c90144465079000b22403092034450044180101e1910f014098840031980d90310b01608a0b041410104150280040c000399408042e100d2890380c40c0d0101c03044d0006070304015280805680092100d024070340407690000510603004e24800c0b12a0303005214003110307045441c001ea201d4621000540c00304015455aa48030b020a1455034185e84143e0741e0385410174940003610028009140c02001c103038204219121742807104090341904091500e46400d0f400401c3d00e402801c40368168020802c54101840503400241c99400311071080504603000489601c0d40d0404601800d8900054489400c400b0103140c48110081450011144c003102d240d10199a44034210b13402002c00201c008041d04045000d0001500e1151181000807092603c1d40c4444e40c40c1d9281c50032684104108541a00301007000c07140c285009812100c0201145455511002c0d030142d00c075900d0b01c0500034200c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 191546762 191726618 := by
  have h0 := BRFrame.cov_init 191546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191546762 ≤ n) (h2 : n < 191726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
