-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1622
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:54:38.736008+00:00
-- url     : https://prove2.me/submissions/7b2c7b11-4d74-481b-a077-ea55d73e0327

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291546762 ≤ n < 291726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291548012 1250 291546762 291546797
    0x5041d01110f030c0a1e020d11060f070f0c020409030801090f0e03091302090301090b070f02031305011b020d0308090f0c06121f030305040609050105071208190504080a 74
    0x1c0ca0342c22010500050000410601441c1c0091141c01341130308100c0494070130742e036a90083d22098040800143c10080d031680030380e50041305c809c2030250b880c00a40700d14648406a06190600100100100504035000350411401004644a42d41d009001032100b6100d0341009050fa044c280315102496142100340000e483c1a48100540c000c2004041c43ca46001d4200300454995a072038003d4480b41d00f0046c40404c2d903024410051801d108002d01261890181c0000d4001c5403242081d505540080120f69488000354004406990003401c005050300400d0b00740c190f0b004801d40c0c1c000d4100030303940c0114080c1030700241c5040c4103084413400c440e00c444154500c03913144c1916402c1503403c84424008000708802c1c101c1500d40c04404000310102d0040390114820640100c1d034001e50200d100020700b400301c0c603440276806014100070300b0700714a000460703522642d442c40704100d0081001080303408649900c00c060510141503861040500150034a0304010085034000c01680010441403844041c2400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291549262 1250 291548012 291548017
    0x2d0f071b1d0109050709080a0b04030f0503010f031b18050406060b0c06010b07140307030e03010501050d030818070801020f1902240903090d080a02010b0f0d1b05041d0111 75
    0x548562100110340d10300419407000c0e04c0044d141d482403103081140440c4609003044940b000600a40c80140c4505103820702030250a00340d10f80d8801c100301000140100c081c01e9980c01c04580d4040400f054524960702c0d031410300310b055008800c0e5850141d9441030480142d4000e40d006501800c403c2040c550380d290340340c0442c45020300c0301c10140c200100400c00003000001818079180913801e600404c070100c2031400d0856009400c101c0100d20a1a18100141000d100d014054001506c4020400f078403a00c0280044a0050501d034191001403c0c03c200800c0c2404080006c0c141d0351b0096450305058003c068040d0020700d2003c00703865900786414041480010740c0503c036200121035600e410301c1040d07038915a000c0240000d5130743c4020040d09245840e0300e440c42d1461405885032503200d141101c8000d0070756080300501d80c824135400544185c107a030b4103100801c8146e4018540c011800f5132407400315904035981c0c401360b03016241c89406d0703244600281001c0902c15805c0002c101260b800c020402460 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291550512 1250 291549262 291549299
    0x80a0e0a06110d0c060b0901060c0b010509040b0a020903011d030403030809070608071b1502030f0a050c16020f090c0c0d050f0909071808100c052d0f071b 68
    0x1d0f07104502042269000b01018031a190103a6004580c20200d10f000c5002d80f1020390200d80000d080b0040b460600035968040c50240c0000c903071502d20390505807a080c420420142046807410360000d802c0d590340e6825400010030800c1680710380d00e03102008a0071501c81c0c00c68482a03012131041d0f000204d070004042288000c1c0d581a8031600c44988803c08210b0720f004251564060206070005454082024200d60704154003c117440941d036450542c00d26046542c018103500c004604240c184040070703841c0000d41e4407000e610b440400722903055000288100034005552500151030000780400c22200c600100703211841b080c100d80c0c1c0f0201c4520216101e111b03052070202044000c4c840d0000910b418000190801c08524244441070720500341d80b1028441c6a0080d805544054008640c1155030b000d05103007091076003051170500c201071115600c41881400c040c0200f031343e124104210140c1c81c9041e51040340070b4150280c1c0f1041c03a4a004c1ca9000858980542903008d0a040080d059102003071102c6135 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291551762 1250 291550512 291550547
    0x504030f0e0423061302030a15060201090b06040e1e0604020f19060c0c081f0c050717030414030a03200a05070318090c020c0f0402070507031707080a0e0a06 69
    0x200d0b8085103030004001c9014103031507417001941c074002200c0c1c58180040c0d8094210082c000446000e0013405040d040b90950049056904041c16140400e41440985074025800c1e1030100e080321026580b182024916148400c00210b003050f44c8d1030701900012524411403003611901400190701041140703011030945515561a20700505000e0188a09022520755105040c485501030b220304c84581040c0810052028144840d841c20005000c0380c0680c4041d80c40b5424103a14104090300c03151015004404029040500000031400304981160904101a8580140c0361181d81850006000d440d0904e801408280324281c50322001483c40c084510f0262030f5111640b41882c030b40e4055800c00500300303524121400c000340008010f6818003d02d60415540da000c0c04891b15640304010409901261382ea006a20610800000400000b62202500d82066a1080d004003030380b100e01844c860140021b007696408608a90341c15006280071805001c00c03a40a01c099031100c000b00e880400303d0f00540e05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291553012 1250 291551762 291551801
    0x30c0304090905010627110a02030d1806060611060105010e0105071202070f0b0a021e0706140906040b04091404030516050a0c0602150901020a0c0201140903010504030f0e04 76
    0xa81d56400142903c2c49a000491226a03886614502d05095285841040b0010001500090740c1c1d1090740b92045c030b01180c803801d2080c0914000c0d5030340540001c0b070386100d07600c01d0300c180c00707000c0c14952068480c2c1c8500e0a01c00c0503240c00d402070150240350902075a45c859100040744660003a003500c440214180e45403810a02c1c140c841d100c0c80301031800344509500500c0c07030204406c501c46080364080e100030b07456103076a080f505030028a81030742058010001b0189503c00060128080381c94801c0310b6540c0782c280c441942900d41c07941b06200e03c021540c3c0c40400024001a41030402e0081c100711802940c00700030303455481c1d003100740185d02210000c000542c10010080c21b461385030320a80c06240101c00b00d4451413010354a5200442c0c02d0342080b00540e1240910151895100c464140d02c8003810700258104508140080c5c0300d5280b00400a060215407188400c80c811401c0648004400060080c03046081c2420007601501880e0300764000a1807509a4120a082c2800707495240d030301c0fa20304002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291554262 1250 291553012 291553019
    0x70c020324100305481207080c130209030d1107051206060603100e160912240603021801090518030f0901050c100509190c12060b191d04051f020d0c02031803030c0304 73
    0x2b804901081c0005a03480c3d090040d0012514100b01c14075660910362038060386110000c950300c1c60f05074079500c882d00c110245020f000b011140851444e400030010754940d07440380c40e544083d07507110041c0e4011181c1840e00104101c41ca40d03000c20ba1912095043d03c402455039241c003d010006101c045018085a0b0307901e0b000c40014210395500d5507044d201e03140c0000d585440b64005040300c0380075400702483c4403c480052048001034414650031008004580c400c04140d501c2d5240c880c040c140e130300f418040d00490b10ba00384d64010421150400d40d09001c2d5908042e0700c813502d0300105001c0e0b51400644c070039041034414440c00c001b50721f402150800f03140d0081e00c0c0741000c00400d4200000084450a4546210030029120140c0404017408647d6485210b10704190303001021150840c02000744181f48800c0c040401e001142d2228880c0c02c07000c0629500c0e0032410800c0292140a030302e4034030700346420101c0c150710741d000c4094102602484049139000080c0b0342055070307074007402800340d00035042000b080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291555512 1250 291554262 291554269
    0x503041103030409140402100e090c09040b0a17010f061802030a180b01061b03050301090b0a0b03011e0902180108070c020324100305481207080c 64
    0x340011004044030302e0a501c4941e03103000e90364284c0403c00094840020b000440c41c10081d40c102000071440c0c0100d010b852100080c02c418030242038a40e002e900002d0305030342d81d15a90400c1c2d41e01d90020708115916607440c1c1e5103080c2260300f0100900c15529110962043d5100c5004120440f11071b1402100c00540fa6a4014001d40c0f001e07140c0804140d079040c1c80c5d100070102d0101110001d004203885011980341410107000c00c400300e8009049100644442d00001360424107607815103058580c0000c02405003000b041c15055980c0140a9485000c000082c00060341c0074144410604920041c5019545440002c16800f4100c840791000c043c50362031200b55486500d84aa1161141c94070b002c401d01c0c01e4010a00301040b074004003011964105403c1c100c030185c900340c1c1d40c200507003c400211841c6580c03101030b281e100b07120780079611039031550010b403000082840007030440168000b5a4090410003048802151050a00f01d004901c03c00b0b00e0354a80d403010078a02c04480c0007030f000d04400040e0b4400c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291556762 1250 291555512 291555533
    0x4140c0d1101050c0f010617072709020105071a1008030910211104090c08090d080c090306090601061403090d120e060708010509060d021516021801050a0603050106050304 75
    0xc058052040010855110170f0901544e8000e05500500b1600400c05105081c182105170300030541f0584200c1c070300c01d210000650420021510103200040b29071240c40103e81da480303801409130207020341040103030303564080b140018042c02060a500120740e40e00e0640030344a0140038201540071108416890006008945030803020415000c00c1c806e2040304401841280c001e2040c48160344008241800b0340e00d9288204407035101282040803103131604004403a90b4131414021351081107160404030302544410016a10702c040c00070305461a62404442c1240c2e60720091207010300290032030403e1041d210340344c0200c81c05a000c41c80038000e98200c0010685e400c40c0001007040c2c046595131183c161034501031028500413100c0360750300041540340504105890070003800842c400c808c49c1583c000160b45179104e00303418110410b200e43c0c80f80514035904101006490003e0b4100801c0283d0301440440040041e0586000321100060113450f540120100e840901070340e03000c11000c0000c1030116603040070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291558012 1250 291556762 291556777
    0x709080a0209150a0902030708180a0f02010311070b040606050d020109150905060403032001020c0a0f08070209090a0317060a140a0f0906080c040509060121020904140c0d110105 78
    0x3e50b903001c00e01000c0490042c030b8103540200e0076254040288810194023048042e0004c0100000c002d0220b2080386c0642c4030383c10090020030f80250158a4011640240c004844503000307909080c0d01da8401c1d007004116944100c0d01101d00c1c07803510001041d280782501c44280300c0381e01070f5103e034981230420210180d48080880e06074184070502c6000160340c3d03202e000400203103101c1d40c0d6a00400f0340e410b104005606084000b070280740d0040c0302c80740501070002001c0700d0494025006540340e007290300b071442e00e038400c281d000794000203000100040030b2000560200c90500c0380c1e0301d00980440741042030141c14000d6807010361180740070208011164591441e1590b862000f060802d12039540c2e9650440466252b10201c0c802d40c0300c08007080b00520a0000140040d4265810322040c0382c09c5198a4645405005491405402c202c102040380b5022100d04203e42d405402c6800c0780c10107040a00602e0b8514100700710b07902c204c04c1c0040c002e062003201c0301c0d4074a078405c4a00034050314030341c01590780d0b801120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291559262 1250 291558012 291558031
    0x108070b2203150f05100e0a1a0a0305060402030d0305010f030215120123010c050616110109030c150c020c040e0a05061504060b0301211a0a050f0709080a0209 70
    0x51002c4045a00c543c10000303c202d00010000b6000e052003c14000c0d540001d082d29000c80003240100039a031290641e01d64400b1101400080c1100b0307064905000500d0340241d1500036440c4480841042000900203000700c0c0201c1c01c03031345a035215080440507200c090044409005246004100600f071604a00e8505400040b2042c205a58441c1860030103209a00213212010706c03002a480003502e0128103c0042c00a00c4c010402c1e01803622002c2c0d441901030149107203070200d001c81044031841040100c1420500304024440c40109080081019100840950b0410403150038007400860900c02c10b02101040d802500300e00c0c000004220060800f260b0340317402d900138080c0d41d1700051004c0c0500740c4190308041c484403892498005010488085410101078044100018816140184003003402801c2c4600c0c1c1e40c00c0a00031385495141902c80641462861007800c0c24001c85804e150001442030031004a0380c449503680c2001180c810000b132003210307160340083c5241400741c180000220303403200444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291560512 1250 291559262 291559327
    0x7060b0f04021305010f020a20010926010506040b0d0605060a0503070303090918020a171501180e0303151e120303090d0207060906030914030d140108070b 68
    0x310201c0e05a9006400643e00c010400c03d05110541e042070f84004840350394402841d29000307036541c4c0d00e03c45440911041c40441c003448140410ba103d0341e0000c010b05030088c00d1036000e04841181410781c5891290035a5654203040c0003c0f146d050130700c40c40250803001040340b690401c164841d0401050040d00540e0012220032010840b51010020040114800d41d0b40415507440c1494480442e84062102140c85d2810074000001d17984058150041d5100c8003405c120030303002c01c10010302d4011105514024030030290300005403851555111013410401020a1003082407884502d40c5070300c001c81e100305100030045207400850500c00a41c403122480c00100d40040c001440000310310800381d18000040307a000004000d1910320034440b000d00d603000360004008860400c50090300500751401228200350f5180f03a0b0301c09200385640b004240a20308402e40c2c5d40d421160850303901428800b800152100300300c0c2c0000600c180700140e180201d40824240e07030300304602c15800705480c0122040200c031540c0c6a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291561762 1250 291560512 291560539
    0x170304030f0f0e030f070812040b0f030a0e010c0c050c03010501180903050403080705010203100803070201053c031b0309030d020901020a0b0c091f0e12010603230f070b07060b 77
    0x700030707200582074001700602045140846261505440d81c8521051140c144030802c00d440211064030891100c20b442c8544a80d0b48102c103000904245034440071a40c01c0807490012903800440718030605008509807071080d10050240740c2603172404e10600b2030100c045c84807401010110380c02400d4182c860b01d0614905a07681e11042d001d50010f450644640e5800030500152500000c010401881c501000d036081005a0300040c1c002d0181c1009007480c01c481c0705504c90769482402031000702c1c000700f14080d0002050840950100d8001b211245100c40b0f1745c006e2412018a91020f6038402c40040700210306e494810f0390100d0180d00810ba055042d88a00d544640008007410190392181030f80b00800f0740c4504400c0700308040441c0d48542103d5030701800022002d442d9104102400c4940103a406075100380340351183c9801403545900141410003c220f401c04099aa00000800d504840048070304028445c065140c84585a1050341c00c295410040107000940a410810f41208000d041d1f00c100c988 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291563012 1250 291561762 291561769
    0x6030e03120405070e1f050402180607030c020103050c04030b01050d032d0e061626040303110f0c030a120201060e13050d02060106050702091005060c0307170304030f0f0e 75
    0x801d6034103c483d9081200148119031900c41000e07840703240d08a41061401e01c814a810540c043c2d0b0154601550b000141c1e81030b10700001015030305201001d40050f6441c001c40c10020310b801d01c580f104a0009007400c0115003080034050a540607030740c00c2416400d461b441c01042054004000e6000c80c244900d07690381304003503844183c0d0001c890405140d03140a40350f020300c00411a904240d9894441c017009e112070201e000460f12405c490300c2d0710140c1d0840c002e21a17001c0d0002005c8454203c0441c0030b00140110400d030740002d41c4a007046440c400c0710740ea005090502926102c650200607055030040395414040b40144108060f40e07030490000040e4a502d680c0000042d480485842510b040b46440d140c0c00c01004115201410803640b0203002d06504000c0c1c02401441025800303445440d034100454010b44411000800030040100901d84d0380a04040c2180c0345d411214094030800c042006000b41030302441c080300c0c41190306a8982c80d440360503440a603502039000102c3ca080120025a0040988 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291564262 1250 291563012 291563047
    0xf03010e0607110c0a0b03010e040203120d0b04050a0e0d05131505070b0a05070f1d0a0e100902190302160c09060f0503010e03090409022202070b0603061006030e03 72
    0x4059a400d6660038040d4a000d10304180040c3d481d0217140032031010000c982500003038174195101a41c0345131081d01d4a000081c42c0ca18403244c10300b04081c00055410012400c0d5005003c001c03016902880741e41d0725103255104807152080c1c02800b0b5003082c1c0001281c280304d0300c000c000703910840d81400304a40d100e0030304e40c000195241c481d90200d00002070110500020b00440d44e031110100c0000d010718986500001c09007a500d0104009104181c400e024010100d10752100030f01034080c105040b581e40ea0042c1130076200040e908910181c1c1d1245010802000318003c6030302a543c034822000c2c501310312a9085000394400c2c910040c803180d2240358280011804d540034001010256008190981404c010342d07507240302c65100c148a40c1c581050040241c00103c251a114074049030f000881e000300b800130590140c0942c100c030500c0c0501003010380850b50300380d01900c1d0b0300b4002c20103100103685480a1640c1c0e402c00f52010440c4540140b0100301c0309229811650308555058141c1c0e003040c0070030640c070f009030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291565512 1250 291564262 291564271
    0x5090613090b062107060806040f0509010204150503040503090d140d020109060c0905031c030b030a03270303050d0903021e07170706051b0c06041413020301050f0f03010e06 76
    0x2500c0d02c0203201c3d840c034004d0380300012200d0b401800000520f100484035a100e107688501130a0060071000954513a41e1079004a414000b48a000d11040c5800400a8000e500501880340e070003004c901e01d40400c611502c08c0d41d11139a03002c0000e500e008091004c001d2030145a000407140b08880450011465405002040100d6000c5e0008198a4510324003a029282044000303010440000e10801141d980060b000740c4081c1c101200b0700c8101e210f0f007400c070041d1030801902d40e050721810641c03404240e0311901c40c0c40200030003c44034424080b1110080300c036401c14840a000517206014031802002c1d07652041005a03c41d004445480c1300f011101c880340c1184a0b4000102c0c4c0000e0070400440c10340c80242d028060340b00d40907203503903030a0060180c03950182540c41d800c04401c2003903040c80028108080d000c440001001940c41d107590703454600c003072100f860b4180e000300424000750112501c20f00a80e4180c5800a2030030580f03030080f03418004004041416142c0c190340b01e00054032242070902105002c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291566762 1250 291565512 291565523
    0x30402060405100c0c140a05040b1201060303051b1b0103020a1e050409050606030906070507030c1703042001140d06090e030a020f16061b050607110f07030206040509061309 76
    0x80c03c9080101d040d0740381b0b40c403283c40c0b04404035807800c280d5581034031241920001c0390009014100d0f2804030303058928922085206602e0a0400300c2072680107405405207085a2aa054821a000303404585803042c030742c1e00c0c0f4141d11b040c7c05190041d41c041d03006012008111328103880c2c040303408003940c1400c1c000b42640d40045140084c00740f2008074180074550344000b050321000d1940c12700c21001c0381d554100921801c208079010511000301840782000400140c2c003c06000d0000540b1b4a010050346c1c0f0558044500003000300c05c1c2c072111a050071070710b80c0c2540c058541f206100341c010010310041d0301080c2c00502c0c440d81d0b40c1001c510b201e4103210300b03070107504660f004513141c040041c0017a140c2071400d024880b099004904146e00c2d04403241d80d89003600c0c04c43c54418040b89405403e22004448050010460b00802040000c5258040d0b0340d40c0440000c602160310f06002300442c0c90721307130815003c06500410304000502403030918281842c0c12840c0900041e6078001003100200c22945900d200311603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291568012 1250 291566762 291566777
    0x5031b031011090f0307050607030e0303040b03011508160c06050c1605010608010501080604080702060a050418090b070e0307230a14030721020d060b1804050f0102040305030f03040206040510 84
    0xf05003031102144003c4c85080d4020084282001c0000e43d482c0a0104001e04200801b420345c3d5803034900340305890040c050a01d2190310780d611000c2208100b0314000c100720001d45200c00213a00c618030b41d40c081c2840c00d07603034442c5030710f0000a4690300040c2c5070040400702d43c0c01042003c0c4840c14003071015902c5140c0620000101c0030b05004c119825118181c3c012401a8054418080810540800c0300e8207190b04548207a55440304400964040c010783d80b040c9000000c00e1400000022039400c0500613510a80e200b048950300e200c1b040e618110350404168042d8010b003001e001440c0d9108059160004081c03021080d9071108002a00e20900d13600314a050100340d0800c1d180c5800c08000c00d0300900b03040c9202c200d540d03600c40034a483d50000100d020f84921541c0200000f44181d6901a00d40244040c05480c00512080c03a0894442400c0d00d0403903880c031521002180f000c0c1c040c801c0e5810303a41d20074065843c0280c240101d00c06608040c0090380c4c050b40c1044001455a20400c81c10100011900c4960 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291569262 1250 291568012 291568027
    0x30503070e0406081617060f181c051909060e12011107031e0306150e01031d0d0215090a021e0d030e01031b1202180409030e100905031b031011 63
    0x8110071b41c1020040c5440e440f22050026881290b0112940021400b60186170050030110391882c0c50305030380c0c1d003410340c1c4192200345860560110041c4041d905034445620442080b4004a402c00308a10030803000611004000c20740e440c1074103d507440401c1c82000880c8041070080b504489a11001c000c0b03012840078200d540d03000910300d81410246c0c942d424100001868241c5410b01c24030301da00d405080100c0102c400020340e0182e4823007800341e40504c06150b01e1084003409295200b200ca214600584100f080d0403c5071980b803186584a550300002400848070a5401c0c0040c031880708080c80c2d130310b100c5244401110b8885140040215010342d48100d01810703500005000ca0786140d030340d0815141c3c0c1c8009900083d13040b40c4001c40200700d0700c10041e661503455811140b030501ea10182a40641484903140501d0f9000f008118140c608403024241074902070001c1c2d030480600d100d46500354110300108802242095010700381624041d060311020004074201600301c855800100303000c500b0119501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291570512 1250 291569262 291569279
    0x22109030616120504030207050d051603030201020a18050a1401020a05011a121c1d060403151805060c07110310050415060308040902030a020412030306050f0d030503070e04060816 79
    0x700d200710905020032045c14182c40080d240c1e034207401003e005900c82c2c40c100741084000c0102d060075034042c04111140e56140d1400078083d40c40004a540099481c501c01541d03e464881c2001c201c50f80180882550352814840304444407110450b40c2c15800303040502e9004c0380081c040c210341200401d04030007000c080103040142c40750040d442600107620928800b08040c0602d0407070b440d068024200034607412019030040008010045a4540000d000b20300041008070010405071711f6a401e20040c0300b51b0111301c50340000120102005032484d0b000e0b40218102010f003100600c030860060b001c3c00e9800302004c001ca482c4c05115290200099520010002031204000e910010240414400c1c0001c03880c549554003940154040c20701d010b80d0000100303410600a5040740c0c0101068500d0000303104407030070041c3c000c02c540e12445025010030782140e519032400340c0700003102591649070396003142c81d910021612080001d160942155907120b02186000341042290040c3d1941840c61400d5070912920 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291571762 1250 291570512 291570527
    0x8010f090203090d0e04061e030605010b0a090b07030905040e0607020106090213051c02090c0c06010b0708040b07170d09030e0a052428020f0d022109030616 69
    0xc18a1050090162800e00460481000b43c0c1d00c0c41e0010650075031000040041c0850341c0800e00d400b000030f8000c01412440c14030041101c0c0900810070070303a07903280201c160510078000e109000801203001445120745449c058280c2c54000d00c0c01007021030b20751380840d0460326601c2d01c1d944503038070141c10045d485a090180c400940000b000c25424103129201b00f5281c003001e400ba2910400707079004422006210320390505c203a1b68004004d1070740c030b08055500070340d9a030003200325003000e005a500200e0812020403c0f220003e40c001c101c0703460716103000e4458901f41c01014085484100300000c03040510b06640242c8410403c02c08001003081140c580901001400b14000b80034004081007000310742c0d190f800080c2c4289079800300b4206511451a0301ea1700f0300c00c841c90700c0d08601d036588241480c0321012402c030710940c8858084407880c0c201c500d0501d0703880501092810040e03120300b9042e2034442c00c8206090f003098407034402d10306111040300000d040100032200d00044103009158210002d034170401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291573012 1250 291571762 291571769
    0x118060911150301090e0a051e1504050303072106080c030c191401180f06080f0f0106120b0d1104050c0f0403080f0c1509100b030c0d0602041508010f 66
    0x3480c500d140300e0060304080e24041442414085c81d03507600140e041c800c045c0b104204440d4400180c94a40744001d138039054101100e9040c2e042c612884076a40c1902d4034102c0144e0180d60014004c40c01c5035102b40003101d0074541c0c40c008a00705490310102c8440d0300e415011f44000f401c8034602911108000d10181854a00c00200d02c510031010420700124000b80380c1a01340680d0f8481d80c0706c81d02c1c0c0d005038005a40c000f000d001c202c5440c0c50041d00010303003102d4040c5500190303050759a80c07400c580c07120390400024400c141d50a0040f51254070040101a008901c6020b000201311404100d0000020008841e00c40c100d4054481c005000e04134a581e1034544200380d4000c0c84020800e05160302c004030700400d80554007009020140c0080d0900700b21400d10b0070380383c00481c41e00854a03c410f000000416208090380c9100040c441c0000710182244030b0700865a8200001e002000344103041410001a21fa800d507007521503690030400800c400035942c1009040d1912a100c05107254941221000c104e00340f82d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291574262 1250 291573012 291573019
    0xf060702010b1e09040303090b100f141c02011b0b06040606050703091815031a1014060d0f1d16030c0509040c15110105090a0c12050118060911 63
    0x7624000c0300703542e100805a2601c0144c0d004900c55580745020390041014510151085000c00304000c01c00c0c421070006410341d54450741c60000c0c940d480710587e8401108581e2240c0c000100e000010821b0068454080d41600504d01400c900c04080203005c07085c06012810f9450b401c0e403004001c0e030b0381050300a060050025150403031600c2110b440c01800010a40240c001000142d00d500c0a80d82003608011071988140094094065403445d00d0354104554045010b00030f508040024100e40d20f2441d50000c079030b100d005586458188108000303a681c440000da105043e581c824914229900d4030489040200041d060230503200414041031030180b01d10000300c40c4004070a07040c00040c1001c00e640045440c1a01c881065441d64076108040c401581c1015001c0a41d0b0030301240029480005005442103280007040a5121890600d45603042c1c50009410354401030750811426503c18120704103d4052000080c2212002881c5082d40203150300c00d03160f003611248118180007902c0e018601078130046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291575512 1250 291574262 291574279
    0xa0b0a12020105040b3f150312090310060801050709151b020d12210212071404150f0f0806090103020f0102160b070b060105040608040609030e030f060702010b 70
    0xc0c1d00003440c9110f24000d44903015008940c0140c0d503448007652480e10307050308286100c59010780c019002c0c200c070400c0c09031240d001a480801c0380c8402800311910f03501c5015000e4508001d0100003052207034021407409426114404104402e07900510440d4003800590001141d60709166070018084034080c0c0050300c0031640ca491000d405a00f00582d03900c400340d5651041e4641c41c3c0c0c0d00020b0420112800090480381214001c546126800440030400d4010404100c111413800c0c100e0344201d0240c0c901680e1404040c401040955005544414051000c040b02d0742c645074840e2400c840070501d40048401003442c850b501e40340660000698220302c0345500d00540c081c0fa00c2400074842c11010701c0081d00a62045144120f264230a00103a00d20396442044030510507030712a1f00c000f030740c0c3c024801079a41040c0c000101c1c0082d0b2041045408441a66580118131340b15a12035100400c00c9180841c14000d41e003030f654025440a1100242840c500000380029141001c4081d0a44000024081c41810312 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291576762 1250 291575512 291575549
    0x150e370e180307020d0f060203100501030f0e0a0224070c080d080603150415060609090c080c070803090709091103060f07020a150605030a050a120201050601050306041806050a0b0a 79
    0x60340c02464040385d01c1e6011034aa4100b849809a41060203030489000004001c61290a03140c0c100840302d0a907010080ca0f2030301c6407410b08480c004040c014403504003883c51000740c82c1440c1000a51804401c0b515011503016004002a80c80114225204084040104030340c400c00c1c0311460304a50103083ca0031a51400c600041d8aa401c0c480d50440c040f80300750081003c1c80405c08903807407040d20500e0100401a11644007815a4080b4800c0e48020707401c08c0c0c101203401b8802d18641e4005c850b6028410300300003040c0d580c000e0580001b0840c0c0340a10400710001101c0302e540c0204040180503c811a106c3d030040414181000402010403510ba03c42d2024405010b13800102c1c0c481003600800d08081c981d488843d80805001654401e90f410f2064800c2c2c841840000315407580300521400c40c110383e440f0020010390a03a8022503c86020070300a00005d4020305045d000f501c84a200c4040b0301150202d55a603071300486c2c40c1920b011066a50710080c00c01a400c00b110301c0b0000e00048031450f00446103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291578012 1250 291576762 291576811
    0x715030b1815102d1403090307060204060e090604060b0a050c190b1e01120602071110030e0f0a020f04021b0a060f06150e370e 56
    0x300440700c00c0c1020008000603030141c0d0381c2140258000401420f070f040b42194442c00400a0f00a003400c1d2080c002040d403003031400112220020f003002031584a09228445280c00360580d608010400003090001700034000008043d480100090003060b110f410380241540140130180c0710051465024526056090242d01d800b00f05035400d000450ae425641e81040c4401d0302c7c2845000300c444c144100111008400704074288140500c82c203161509502c49a1101c9484401c2031380c00c0c481d2a2415142e448100f0116916800074a003180c090500d8504441c00d04c004a03401000c0c8202c0c00000030303616603201d29159020f1081d0000c0c46070210040c10f00c01d2243d0006461902100c580520a580c001550100004006444a0001c00f034005684020040313040c00c030007409041c818001e8044c074003100442c2c0d540f401c1040144c9490702d507540501d0b8943c2c4200b071090f041160f1003030b500340001d010042803141c01c20320444251110881c2016200607e0941d403090012805407000e607900e0b01c880b035407200114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291579262 1250 291578012 291578029
    0x1020d080c031503011406120312191d06040c0902040506030a091412120f1302010c080903160306050603060402010c0b131406090c06031e09120c0715030b 68
    0x2500c1940c00d50b00e403a040d5045040b5021812510b405500f00102c881c00402640c103c1480741c0c5059603c20303403101e50308900d039071284111504c2c828401e0f0003001084241829405c00c1044811070040000c100881c88000310081c2c07940c1000380c025502903030400041014400256008103c1003009504090410340040d8960000804603100d0503900d080b0b003401c0c00044500e111000c0400c03c241c40180d070001603c0d48196202e16030260740020745502003000a60a040c6d1588101404040a81880c2c002c2d0700440e000035030810280c400e0641407010318007a070340030f2000001d800741800410f1226131562a05406544c00107102c244217401c41000c210150341c001e203400694a612a40c600e50a59480015034501c6107889800b820480c111032882030302113030000d00d040c000c1c4034020441d00c1208441c0104140351000b114034204c4a03c000e0494012001c2c0e8988d83d07600b200a21080e03a00b0b060608800030b40135040707158003c0503513000707580803c07080c0c0c180f0800001e100d509240500208260501240c2100b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291580512 1250 291579262 291579271
    0x19200c040506030c2706030a0c0501110106090629040b030403110a0b0103060204290a030207061d0102070b070e0d02010503040807061406010906021603030c020a0806040506070e01020d08 82
    0xc949a40c0041d01c2c41d43d0a001e00c00d4640c500800070031580302c21108100c44101c0c078050384020a104c2c0e80105010b072030001207905e0640e921460305000300b805c1c44011036420901c050310300d42d15900c1d1007002c40c21042c00e014400c050001c000c042140028413002c5a182d01681819000040d07204120a114140182084942c0b240e0181005090a4030f8021a0381c6010503d18000e804040c0d104004020001d060f001041107851407544600c003144413036580b01078005042112840c2c0c0c1410850070020741e019801502c3d006000742000280501421103250348440320381e02d404c18995001034118200402d00c110766401c40051f107003505100500c0c0003c03c4003c0c0007c54081c2c14068044001010480500119040c00d1750000040c824680072440300c8828643c1600c0081c040f4400e800d0200d0380910014040481d0030400104400313061071f58030300307903807c00132681c0c1660800c0f00c4510106045404200c4031b406180710b08020949858004402800e1012a0340c540d4111740022444035030f040d5000b400c05800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291581762 1250 291580512 291580519
    0x30a0f02031614040b0301060945060f03110103140405030a0c080f0d0f050601020a1505040503190504030201140a020a0308220c080606040501051809030d0219200c 72
    0x4950141601055500132580004c541c154004004140c8503030242090302141c040c075079151340c00d00c903444900441c0c140358141204031040006040008a008100d0a03210f80b00011000404580300c030f401715130000031900103440007012030540e56507959042c03160440070905020401c0c8642850b0351074076107078810a00070404209504080d40240300700c04c0c084404010402c1a1603a407501c0e41410303103014240002e1085191480c0a001400b90b50002c5091030341c65501c55030024107074030140c0b50070004003005042a51503200600c502100f042c801d0340307405a01e0700b4039102e25444138950310005108546204100c000e0232800e0040c1608aa00001c803060050380c1410b18000a40c4c40241703140d88a840302c01c2c02c074986103490034180140f002c60040002030b2200102651102e54840c4188810341d02d0a02c01c0da600a0305100032030340b55030178031041d60b60800c0d1001c040d00e10f0000328006103002d030303000340300d102800340900c04801201940020306007040100c0103521005050b407131042d060300c4204100c0203600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291583012 1250 291581762 291581777
    0x3121b03040b0f0a031803110708011e020f07050105010314100b0f130e12070b0f060d02060d091a01061b0804051e030f0610060201060b0a030b0103140705030a0f020316 74
    0x5018000c0d0081b2500000400b03203c482d801443c20014030500d8582c80c014054010300b40040789010044c0208800e040303c0031018100300c5400c2c10f46200a40c80718100c140303255018081000015800e004080c001d6005202003c0c200031002c071494142205c01a00c2a800c514040c00039010b52500751420b420541c0c112080f801c071303280461040000d13008441107580300c0c0c01030b12210001031090300064048940580744210180d41c501000403022403085c1d6400c2d6011b820030000b02c0c018a8848020320100f9002e40d00810220440e42d194400c00700c4082c40700d0560040c003c01440044c1c1d102c41030081c3c1a03042c1c1c49000d2a607169885000e5140714600a00340141e420038108103800d6a11f4100d03c0300100043c007203c1a0401c1c00a8181d2920710a0b80c1071049100f4201c40003490a1050085d6400e444103c22641e190020042c030640007018424406030505403510706148501d1000c410b09840345a43d07032100303903680c541500d4000441d003070b22071881103451051080c008101018424202c180005003483d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291584262 1250 291583012 291583027
    0x1112406030102070c0b0307090e010e0a1e09260702010e1e1801060806010c0c0b0307090b07030c0309120b010504020708070c080c0307050d1a0a0b03121b03040b0f 72
    0x2c2c06440359400c084c283c068001000101d10014a0041d0308c6a2001d9035115481c0e621000c00c018160700c00c0c0300d00640002c101c3c0101d42c04100d2030b4050311264494155004040c0b02c510820720079601a000141c0d00002d6240070052002c08142103c0d41e01e502c00303403800c0d01d0880240d001800c140d010030381d030138061031001115504043c1540c5081c59010001403c0003518078800c0c00d4520600c500740210000034010202280d0b45500480070f0742d55003581b1801d00e600890a00f01d200e00c00c1c2e000201440100801d0110016400c42c0b044014141680070340d40308011315000e070801400e0f04200358050300240784903591890100d1619a08681581c400b140c0150b90b81c5602d0a114480c0c0c003944a014056110011001403102400904090510b030290300b030340e2180341d8034070411808914140024006008400c114121a6220942c40d68406102500095030000c0100441d10f44040d6404524400200003145c248640c801030b800d04100201c1c0c070040d4170b414145814120640a00258600c2c110b00c08508034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291585512 1250 291584262 291584269
    0x7050406052b1a0f030f0604060207020a050d060917030c1204020d0b10180c0905010305070c080a030b010306050402090f0d0312091101110c0a050f0103110a080601112406 75
    0x250340100c000c80306000d88500f0f4030500503450140160a0300c40d42a00952000904010a03420f080403c134030040c00c4555150349908000c1e520005080f80d101c5040320011955980f4554036401c020301405d8000b844c1c1065242030842505034445113404682d0070f00c2000200340b8020100c1e0400039010244a9141e21a131001c903950b01c0b2082c0b801000d65030709408108100920420300b108940310400b040c442000303402d202e00c0031584c0030100f000c0001d4406100780560750090700990b411000d80d2034813041408442d1250080b0f41c114110500010303803500003400781c96070b042c043c201c00b50404403004c40c90039041400090308180001040c60084000194020a2502481c0c01c0100c42c00508024040e000042c503010060342c645c4c00311580400d050b180c1000301002e00080d000346185010304907a01c120704003c1000794134900110840e040685415541c1462466500513180041c3c56842e04562824280005028400c01e0030340100590f000b80c585203802041c0b101042181c400d0744811102c981c6440011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291586762 1250 291585512 291585577
    0x311040f02040f060e03062d04020315090d0e010806240705030f0316180501030f020705010212010501020d0c0302100f0f0e070f050301020a090302100c23060705040605 74
    0xd2010f01100000001ea05500140c40c40b91a103800c905582c116a15116080c0c00c41481e000900c86440f01c1c004006821a0480d0001d41c000d40010204c5066071002c12240500a60440d4020140e80000b60040c181d2504003031030b410360741750034200110396117880c1c1c0c0864022250307081040300090901d4030007080e20000c9421620015004001d07070b9503030310905c850401d10307034800c5d00c001809200c032040c1c040020f031184030f014801001401b5400307002071801d40110003274400c0b1119140c0d819801c01a190025100b4401003403c5070800080801940c0f4050000e810304541001c0310302800480380003540000d50114405090b241c0c000030000b016400450000000c18042d40c035200c4e2903241c080c103407048100c00101c0d02e04035000720801010054840051601780d0050100c0c6038003241c0c41100c10b00062400710300486801c0c1235445c0040b4080310300c0d1200d000e11904006030704003089900500341403a4000740305843d404ec40310b042241ca0030345041c40003091403003440c0b03140c2d031007200202e0a1004019003052 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291588012 1250 291586762 291586769
    0x70f02062a030703091a060d141002040f05030105010603050405070e0403200c030d05130b0d11030412020d230307110714011d090402090408090d200a0311040f0204 72
    0x5289031640f81c95203000c2c2c0200965013044e9090106a8081814410441d802034445c00300609100b087c0060f580e40d10090030041440403015004106031154000398a2000c0d00c0102880585041000d241105140c210344061b04510109404c020400000c6034000a4031411142e0f041000c94255841e030404031610041c15405886100f5540b420061846001a034024640da0482c151001c0b150007880541da00c0c4102801c0c1421400100010044109003a001e40b1159041c6c0c0408540ac0c08100e03e01181c96004540c101c517a00040300a100880d03904100196013207580381811013220310300700c0c2c00155000c1a5100c0201f030000010000e141c0c10f100340208407034907d00c0e8049603c09904d0782038440b40b40c507401340c1660015190101c11401c16009100f10114100054802300340c40e1a00c2c0c0030b1261404000300227a8811600300544c0c02540c4034002043e90980c012110550740c1c840b040c071200440d03209070303900d180305580e07030303901400031415844035115122000c0b500010b94840f240200d0001e4090f692 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291589262 1250 291588012 291588091
    0x60305010f0c1107030b01060f030207120503040c0e06130519090c143708030c0d0908061009020306010e0a0e0702010e030310060e011403130209070f0206 68
    0x14103140c11041c0c240c0211006841a8554401c003a45400101d55106070303520003d0300c0e0548150041010a004203210030b1040c10501e400340c41d00741140c032102c0c2218404504071000800000c10803040c0194010300034068440c00504035210b00344040001c5000f0407110080c0030003992640400d8548582003c2c00030718081c40d980a001d000fa55080021103102544203d904044110300030b07081c0d030f240460080480c1900c0c81d0000e18101c01d901040403500c0f80241081b02540623a00020541c084100302910b075450032000100040c042c1c4640c0213200820550211910354044410b1101405201d911141940d0f09a10010b84a071303207001c0100d8407208540304207608080e00c6900810b1400100c1d800c24420821500240003104440d00510359912040741e034140801a200e409001e02841200c680700640c105160449c1e61500d03800e410035480e8016100142215400040340003182008190b0960064150611401180303004034084d464030b10040030700c02d030314074142c00710122100308552080c031124100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291590512 1250 291589262 291589271
    0x30d050604320c07031e0504080f0c150c0607081005060c330f06041104060f020c0103050907061404030b0408030a050609041703090f100b040b04111c06030501 70
    0xa00d109070380540b2448400c40014054000491155000f003c0b41e241c42e0b03056840c1c85038201d0100310854020752191102041120801002603201c000b0070003510407220079005084406900c1d420010303100d03044010001041818404100c440601140e042c0d44507600d8140300c2c24694443d000c2c07100c07038035150300050f91200000c00d000032100400182c09694240b64014030b0140c0741d03030002e0b44005d00510140c4d44920300700e1000243c09086052401c9820210140020a81c01980c00d4000c600da00540c008000145039442070030052603041000000200013800d080001d8244052900c1d2600f1081c011603043c0800f480070134080140721001c9070015034000b00456114105468594200c0d44103586030a40b060500b00441d00c10f240814045001c0c5034002003c2d050507440071008071403500000e0203045e45000b118040d20300c44506010b10b03114440c0c04075002411074591401c00048400030011103019910300003910000811170821910b040300c0740a540800250341e040301c04050701943d04010919400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291591762 1250 291590512 291590561
    0xa0201060b040801060f0b03040f0f0311030403060c0216030b1b040807290a05090d05100c0806120309150c031608070b0a0902030a1e17040e0702070602030d050604 72
    0x194030070006e58400c1c84003c103200380d9a2894000d0b5020a40700a805503001491100c00110254070a4003580e12a04203280c220079074403c01401c5411503482600e049484031045005c1039414408013950310303090300f00c0000707031800c5407034000900500178100c015401d08070351020320722403001c410f07500100181c00440c0c8603552a420190303000d1980e815a0042c00301e0001c83d01c01c40c1c00d040c400342c40b041060399035a01d082c800004204400410b841d4416119801003040c894039084050003410001340b043d8550440c60308200b024010101a8003900c00c10310f070170a1281070940c0d52103500d0768901403450303400183c86070301e03103421982140301e5440c0403200c00004036800802c100c00c0033b01504415016042e4001d441d030710190103005551003850025416003159680c0000141180d40140903010b6400e505003a80718640c0d504000007002d0391551854940c0890200501c1081e00c500c83c2c4d10008520141040500c2c114000e9074034021101d00307d0125440d0b400003a41612640d110745a084144103504400010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291593012 1250 291591762 291591779
    0x1060306060f150f1d030d020d0210180b090325172508040801290f1f051228111e090402120a06080a170a0201060b04 52
    0x50600c19100541c00384080025140000c0040304443c490756154104070380c3d6281c00071a8071100d00d01c003071441c20300e0503900c1c0072a0f13031410805c0003c401c070139400810004400b00b00c00382c500498038440d4044103081818200740c209894505d0051583e2012842d0b403d5150325415038254022001c540c0c45005107400303500380c0383e241d118000c006a0300a0120300c000103607070702c2400413921405014a2440c2036405003511202282c3d50310800b418010079055003040e8903500d032542924131015200901101007c020303143c9030758001c108410007000301c0703100000b02c0e00301d408100e0040c0b1204515400b041d0a003040e00c2941e005404542c61212061400c8a6034500040007440800744001010b451500d80d1203c00b403038200702e100302c0000c61500c1c002c040c10401940c05010f440c96800c540070500c5a0103000b592121380342c1c0e0010f40708108004010309440d01d0003039007540031100c0c65804418540d0143c8207840104000303840d081d08001c051070501e030360f4541e82c8101340d0150005610003080b101001800045200307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291594262 1250 291593012 291593021
    0x31805060f0415060f05012f0102090423040b04051c080a15080601180603020306010b03061f05091003090506040507060e030102041404180c030b0106030c0c0312050601090801060306 80
    0x91052070107007100d070841183c1c0000c48240b8010422003c40e02d507418801c542c06000300c400192080224141c001c0c10075030b24070200300e4484c3c5000328940e4010801c03040615050040031800d0425a4110040d0955540c60344104800944013174011041701d400308051150a0003140100b03000801c02911148464038000e00c03ca0007125610140d5280c07800c00784c20103000d401c0000803110200010040c0b41d0818456103044030244c4040e102e06c0356554800001624240203d60081c03100070502c41d280e2624405000d01200100b41941d0011183c0800c64140350300300060750340d00d0384240d0302d259510a02c03038003da0003408001000340803407084404110821400103410400d0354159601c0d035012aa049052500740d020714010b06c0141c806140d020b0800e81070590060005480c0011030f01c0b84242c0944075102c561505810a403600c07014800140f2046402d4019a40fa4000d0381c17500b100c20b28015200240032494641511400c00d84071401308406a00c9210380301e000c0c1807044020060301c1d98030301c0c4c040000c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291595512 1250 291594262 291594271
    0xd0f0c05120405040c0539070b07060b01020a030807031109120609010e071d070203130b0901140301030320100e070302030d0e0307030b060616030c02011d03070303031805060f 77
    0x160b040420300d0200e0341c0711b2000e940240210743e8103020602d02088404082e50341155428950143d80c0d1707826031280c02d040201d0001805520780d0305980340d88908001050710301c1807840b541594440e81c84040000c2d03000e070009601c241a0700c2c000544290740c00da80215171080c0021581d00c2240c01110352510080829040d02030084240200b0040c680a81045e4407101948180e0b07406030b01d40d07280003c0c00070054480030740c001c01034410f4a240c07100c804403100310300384140c002120204010562803041e5070059103200c03102d102ca4003590b040d50714555000741036400101449a54010150140c1c0303494000f00450002c82c0c031078801c14092245500b401c0390b500d180b1480242d100307215185480040c28010441c0742d2000d200540540710701070440d110f0085003500030f0034140d002001000b82d03640b2454100720080d80c0900c280e0300c00040c02114000148001e2800110300070b00c1583c3c0382c1000f03030341d0780c00110001201c1d03150402080740c1089181803d08140c401c1c00180150160b10b041041c81c03059050f6140c400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291596762 1250 291595512 291595519
    0x30c0a090329060f0303070b06040e0106030b0a3b010902040f02130504020301050907110f0a0309060f03060f060c0c0906170f0c10141603030e010b01020309030d0f0c05120405 77
    0x403507484008100c0701c10a404d40300360b0107410800812020481e150b41d019413080f0003800c0403500d0f0398000b144500711400396000307584a035104014800201c01500400040390860f046541c03a07200b400300b613a280c1c1400c00c0b801c6050121040200000b02c102900a00390f5150010003c0100440d90b01692001c2d41c084000c070109190407000200b12803802d0f1007641c0c10390348098004115640c4100060380c00060300b440500a91048c2c01522401800c2007003c00340d5184030b59600ca446503c0c001c0c01a01165040c0300c12010f050501d501445101c0c0800014030840e100d915240c01c06541d2400d000d106011903400c403c3c409410f00c4004203014810041c1250011140030407190882100b0035102e3304d90b20200780e00c90b0311550f035a00c001c0e401440b4288400c2d8800d40c15060503d4900c0882e00390080030400002103001c245c0b60018104440310070b00c10fa944202c03003170014620b01038230000060340742c030740208000040c464501070f1802c10034841c0c07a40f2100c8940c0b14040300c000c403901422030810f580081c800c0510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291598012 1250 291596762 291596843
    0x3060406120803070302090607140307110d050c010807090b030103080c0d0f051215060307091a040f17070b1b06011202090609060f0a12050d03050903030c0a0903 71
    0x2120329000703445032401c1d42c2210b455411502d03400003c030041d51007035240c164000c03070900144001c280c5901e001902c40100740f000390f540300c203540390003107400071012070007480344601100c60404944041444404903c0034a0702e4941070340d80d503000f520610120b4121030000d440c044008410061b0700c0c0d0041c06240070b104202e0b107980e07071a440300715014841415107800107002402284100c0024116140d004011840c160884160442c080382d0690411540c0346d002800781e14040212400c2c081042030344608039184107181905043c001e02d172050152041d1039558101d11070030780c0f8545c010b100c0e0f540507110800c0302c55658001c00c031101e81803598165030300c100c40c041e0b1800087e80c8200941250300003940035003100c000d999200100061140014805508003d02e21111300b2503a41d521590009411380c502c80c903235416414100b0901c2d0503414a0500107051803c000c0c0300341c280700041580d9102035103c0b10030781d60725249841214102c25950004006800c030300038403a600000d041401025445094a045 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291599262 1250 291598012 291598019
    0xa0210050703061d010939030612061d0c100521010b030106090806040f0b060409060509100b04020a1b080f040e07110d08070c0f050a08030117060402090105010c0203160b03060406 79
    0x1c0c8421403420854480030100310150900d11f248011a0704803824140020065522044c03001000e24041e8100d91050395246c411032280034001c03c080c100ca503031030020f003098180d81005c00c0320141d6012054041c8807010841540081c8510300701d150700416040c00c4046545c0d00c800e119001c3c0c100303000740000f060214201003900c0e0300005d5410300c00c1e500f01c801040c0300d01082d125000060303c05014950020b44854403280030450301d002c2c15025100701002000d10810481c06902141d1f10084400d2055004020843c641540722004085400d0351240c1d1101d01c0866140c4441e131840b4103038984203004404600012803848445010344100b489440740e4250f42d0614182d5900d175000224404045040c07030f408100c0c580e102d03a034102605441003d0080c00b040d91034031403a00e09031480e04200d4001c04008014440001c4904641c000340700d4010007014541490380c0040d003020b030140517550400a40c052000190341d410011002c60f81d155105c08610203854009480603980300700c0304c8038042e504085000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291600512 1250 291599262 291599291
    0x603100b030c09040615080d0216050f060a090e0a060303080f10060e0f28171c0311031003020a0605180d06060f0605120c0a0210050703061d0109 64
    0xc1012004020300280003000c42040719290025006685070399458034003200c910790307009000d0003038a1000c008000000d10743c0f4000345420051820480914030908082040e51140740d0b82803007004040303402c1034982c0c0c4244021142c0c01e00382d61291440380b0316142403050a8040303511280a480c000d80c0c1c0e0640705e9a030a0b010480c1044240c0303194001c4001c002c41084500d1164046c03030060348004000c600254504400035141840010360407418000b03081083c00d295000540c5240181890310003424202e61504006880f820580c0580482d40105aa003140b15407280c1d1201c8000c0c281411401d40b00c0c10184c900b076600c00d445020890103240001320100c0d08902030400d5a03041c2401c8405002c1e400d10010901264540300181261a1034540c1c40c08182111034010071809000141c2d51385e41c84a4844481444041014100b00b044210400c0083c02c0981d020403441c211001d115004180e9454403c1d046004006503800024580100c62010300c032a211003000d24100c400410003403050403081ea0300d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291601762 1250 291600512 291600521
    0xc1b03021306030803040201230d021209070605040611010f050414060603160314070803030103031106010b04060e04051911041701020901020601030f050106150c060f0605060f09060d1103060310 85
    0x50807a013424030018005610170b101c0c00d4070034801f82488042d2840780d41c01e01500c0c1d4015205c0906501c0c0c0110302c030101d001103411090b6101c28210000c1001c0743c0341070343c007070301c544218040c00b010800e1020342100743c0c4030250041c2400b080c044900300142d03c3c2c6030034100d0b554481301c100070f58a8003841003c21094900050000c6000c030192501e80341c0e203803440c0d892341c521020761382014205015004000900d00c00501c00b440c004c60007501d90300c0c248400c6001d070600300b500503003001c2e10455061105200392540a03515045d078003400e4034005959181c1005012444468031084081541041020403007846104080c0080b606900c169490440720030707100d94281d0196903440390050307005c3c500420101b0f00000600c07540e54011800091f07160344404101c10711480d280420400b040d421001d48040003001e00c684040a40c49020400c5180e080400080043c8190202409680302c00300e40d006241d40c0b1481201c45101004038104021a05218420001c0c4c0007294105c1c468010b21500111449a5024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291603012 1250 291601762 291601769
    0x111c030206091501140406080d090501020712080a1b0c06090807051c0f0212010219080c0c060c0a030209091504060803040e0613020705012c0d1407030c1b03021306 72
    0xa10f51503a82041d035017484e40f642c0e0344c02180d4440e0b10782a001916000c248011010b004c8690703260480c160418002910300407250703020704a82e10680ca03004004c144100e00351900405140303051840c946000d10503000310f070000980686009a1050001074054100c0d6102d401c490100d002c2d58086c90341c500030030000d14251100312408403003204081001a4012600e112503504c020003403c003d00d0846401400c81c3c01010507002c41800d0030b007e0700280340e00603400f280e1085921494078a401800c2c00f285444400c0a4105a4501804100c03055841c0c0690151041148060301d81d801c240f03041c94181030300000c070304142c6000c1d5140050220710f2050210444081d00c180e4460080369072280d0b42031014010380201130030300c3c0d90317401d00040001500a0090b1140300303d40d45e8082105040d40007803400c1c1800c0c00c01508510b6030001d01c01c8900c1c40d800c048050803904e92422440d84803c0c032800c06a0b5100310701d050051040d628004400440402d00c1040419240241e8004142401e400328510454040c0d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291604262 1250 291603012 291603043
    0x50343030e0d02120304021c06020711060309031909150917010c08040f1a040501021215011b0204090507061e1b0212070302040203090c0108060d1e111c03020609 71
    0x44210a0700101d080110340142c800b402d080e08c4c445905245000c08070802204940c003540014440042c0b0050328400d54031440116555031460410f144065501d104e60030801c410643c0825002c00c0c0a03005094400c01002202c4c200d584114400100a007502e42c0c40c01100100c8002c0403882802110501c0389a085c201c1544031a101a100c6480304125440c59103030442d81e0f000c4c0001d055882203150450f032400b543c49100003507211180a411151220801032000d0709a20090310207030400e03030780161f9a08035850f103c208204800707042c0c00410060b00c2e6814000c3c01c14032580781c000540540c4030b0b040194100c4903c4034500350b00081202240d110b00c20307010361986445954200800752030036410700b004581c840021100081c0c0c2d26404a4180c0c0c0080b0740c07004081c0c001d00100360540d41c00103031450b40301c04101c40191715640a0358900340500d1030801811003010415210804002c0f600c0b00651140c60021321140d8008914a0743d912103240159040b0011b004010200300100e0002030a0f030700408544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291605512 1250 291604262 291604273
    0x4030c0b0a091a0706090b040501050604050405070603200c06090715080c0a020a0b0a020306120601050612070903061503210818070f140a06020a03050343030e0d02 72
    0x203c040310700c01d0f4594052009442003000c3d0002032228400c0052080c070510842c2a14034060914908448008000711700450404040200144000c00c00d80c0503203d1a090000340f41464192170203805802d459214424040040c0008550100140c007501c01c4444000705c404281d155808140001081c0d100c0c807000c929881d010948040c98500581102c9a55204075800040c643d101c001d0007403000c0d16000d9460341d000061011508201d29003003103101b551802041355500d440c0204940f4881d01d4800340c00b406050b00455651441407451600443d0010b90600040c6101008145402e800c0e1000b00c0c1c001105244481442a41908842d2001017030b4071070034580e917210400402d80514003207040049005038000458000c0c1c080e81410041c120102240f08400500010b000703100c880c5810480035544000d0b414000258004102c990010748000225400080054961340308252121010b50407035508509008079803601c0120b0204054070f135020300c81321822006841c0ca821009441c400141c008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291606762 1250 291605512 291605519
    0x316051c05041103010516030e010b06070f08070b010602010605090703181b0b0d06090f0e070b0706140c0310061d01030509100c200102030f040f030c02041104030c0b0a09 75
    0x355000315840b034000d00034402d00940b00720029003142c000700da0482507181c881c401ca940041e803621030382ea0340f040d8010080000c400040000b44150041d0301000744003404954034081007002c05ca00b51080141d000515114558444601034080c098601810303000c0c014031720000f01071030b1082c010503584407440444d0b2107681c02e60303843d150184641c030100780d0204540d01d41c00040381c254a4008041907007010800090b0f16040c00035000940d1402c1c0380011b101e41c01c180d0085045180030130600102d540c2d030000a990745545145c003001408005a8141d03601c84250104400c04140c40c1c0114402c04012500121464840101b91840701c0c0940c81d100e4448480b40d41c643d85035019912143d00840400c1c21500d00000701917070700c0c041c1d8150311050300008810744804034407500115412214802d84070b000b5411842c00d11280e803040318004001a019003410001c00701818015020310854640150003131100c0607100c2440d49241c0c0c40707803208550600062000054110504003510036141c01581e036141c15920303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291608012 1250 291606762 291606817
    0x70b07030f021e07050a02100e090105030604080919050a03081b010c1407060b030708030a12020c210904060e060a0f081002131d0a050906040f020909100908031605 72
    0x140744d0840f00e92152880300005a5a0301c04070300d1400305035030ba440076080034000601c80d00c518180d01c881c0c0a50f00420230b02c00004d4042c03080e40c103c00d83c240c418078650340000340c4154881030170ba440315800c07151410f008402d000040300244030002040002c21001c0c0001d00354182200c802d5940d08000401540e4000c08501d2280001c15409014000c040385807148400043e00304920741e0300040c4607500019800c0f9406412054159045014207811400c008400741e03c3e984419203403a030200d1441c2214114400355001100341c4924640241c010449a45c441650740c40d589000e90381c0508c54a00c45a001800d11141112081a502d15030702030044407240304440e00203504a0441d0b510700d01500c0201142c03100e1004d081058410400528076401d041040d00c4034200e40e80134044001582091080001007103010b1840c1029980c1550b46603238542d24a01070a0a1441c10300911160604105808040c082c1d004007442c00340500511104011044000c291110320881210450005444494030b13030307804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291609262 1250 291608012 291608017
    0x70c0302240408010c02010c0f08010308030705070b10061e020a06180f050105060f0a032316061701120f0809010903060212090d21050a090206070b07030f021e 70
    0x41841d1401115650352105030a941c0c100760400d0205a5660743c0c20346110341c0c240103440600b20342d41440d0100c1e004034074000700340c03a00502020f05140310000c0811000c511030012075080540080304840d10b030034901c00c4429110440c0c404c1c0700c0042d1000703404800344409421101c105101503002004203620540d15007024004080e144120005489504400f02e0012102d55100c2c9200380000600bd00e801010810100c0002c600d07140249030400043c00040c02040340c5503895410081e9114074800a194075518200c10403071910015100c1050010340c050300003826a0140e41c15103501d1034141e8179050341d005646c00d46d0f01e0250519601464003c00f040c2ca820007000540c1c0c042c94a5507100d80c580d103400d41a070b84071490070480d4100c0300c410040b4482040c40030500d409150710340030030310000c0312031008401802305d5144a0381035034a0303001c505600d07502d90008002c02d6000c2c0099440c0c1d01da5040040002d1012a40f41c0003003420100d1450300c54601c0d100715041d100c034405d003000c00903501200941c0c0c0c40c3c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291610512 1250 291609262 291609289
    0x1e0504080c1c18031227060f0207091407180f0e010503010509010905030d0f1b05041a03040302030f0a020c0405190b19030204051308130515070c0302 66
    0x2210401088040c0740e0305100a0041218080703524082c45486035004140c0f445000501d4140400041c0c01d10015072101740a00c0c151090b40b03801000d06040051680001d006850045984000b5800016241e078100e034281916800640a4130851551220080192003002c0414810b55081000045c9800d0040c407241e45810141054260895220240c03000d4a085c2d030f81107507061000703020040001c0d1409006180c0d00054950081c00200503179602e075075907401000d13411452551104841c1c00c21046a91080301c0c00c41200902994060300040d01811075400350060322030302c0340b84101c200c001995920072203000d158141d00030b605e450441015822260450f200e143c086005080c52900180d4450044501510081c01400c01320030102e800d100403546460f5501d8000c0016100c0040e5070b400003600b220440b90180d401190a9031002100503074054030780c03801002c2000201d0254080c60443c10064191f0300e0650b2401401007210f00c88a0050140400040007102908030900050608241c4010710 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291611762 1250 291610512 291610523
    0x40b0409053004091e0c020703020f040f050c0304060528021c0f06090608070e06060c030c0d02060403020106140d03120b13090213060b0703031a060a0216091e0504 72
    0x10b010b800c0b20854056441a480b5800c010786410040d05160100c407501d00c1200b20000080100340d864800183d00c0340d10340e100280c4111510013014010352100e400c00350100b50565001c110703e140524040140c0c1d0010f5605a8209240ca0300151060410030344603925041d030b101c5080c0c11400081020400b030340c0305859014200b60b500d0b03180d2501c01e516010301084c0d0302528030045400d504010f641400c80341d042d070110220b0f50000f001000502402003071160004002e990f030603070358180320991516500c150742e050542c034801c00b40e00e0300620340e0100d0502d000b1446035000b8410b0031b5071241d140c41c82a600901c2107511042814500000038000c9400000458280c0d40228030922a000010360032109003c002071115100c0340c10900718505081c054040301107045c02040700c241018070007a45c90041e07c034000e05050340c81d108044400690804440c2d003050040580380d80e100d10441c02500d13099a145030294000341c0321804141824603008240e0394480b0034082e40c0d044400c1d2860040076040180040c0ca0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291613012 1250 291611762 291611833
    0x601121a07020604060e010209011202090d05240c040612020307020a0c17010f0504170d060f0f060e0f031b06070f030504050a1505031b09030a03030b040b040905 71
    0x314034a0351a82240706207181c2d005040c45150608280c0e09443c0d0814404103540d1041003450b580341e8101175810f03001d070001400140c91b801e40c1000b1410f40c00c84444054807910850005a220a20210030304146400144410040751241441c50301d40e405240108404a03451140e0046104c00d103a014681c07081c100d1049070201d010303540300c4416640c0c5a0700721040010b1174640c0c88000040034041c500f084840010f0410031307442e003600c80401000104002441c1c9000006460b4400a11500100043c01c0543d0030306880c299126040000400d06102c0c4001117000300780040c8032890081d050100e01d840c0a400b61954001950780010681191500780e54810014810040443c00d050b004803135443c4241c494031b9646040c20304000d9183c100d0b07070190150256100b040e000341580b1030150380d00701840c44a0700000c9481c512220055006040700550984281d104200500d54190407005070718030150360400024000308140000d55504103005050742e4490801c0c541819012850104441d40113030b46003d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291614262 1250 291613012 291613043
    0x606090b0c01021201080f1501080a0b0714030a0c080f061807020111070f0309050a081b01030b120a0b060402072114070b0906060919110d0f050a05060a0602060112 72
    0x4c141440a0308a184254010390202c0d1b1b0f8004204100340b490201610404150742c5800d001c507603601925800200881d42c0e030700c040b803400c5004081e00c080400c1c01c055100d840b45800034802004054560410001450355000704031000760400300c4501601c805080260640c209680410700100c02070074400c00c640d614840920134001d000d011b0540e0314414002d007804021241401040c3d021160031551140b00c046100700074000c0c00040c0180c0c24089490065045c80b6079034010f90060415544840d008148007001510000c030203d0403400440c442e1440e4012502c2c0e900c00d1000728090702c03070014100c0303102c403002901d030820100d0a806088031510742161500d0051202c05030030340184c0b00854458500e0310511000c0c800500c00540c1c455400c1d222042103140200c61180110780720700d00c00c2ca60540d6600c40300444c2007000c0440f2400854403009003d1480526199002001c044541d401e1003850100429400d26058a0707d05c101d4040c0d030300801c826401c0c10942e24801c10114800c44541008044c0d05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291615512 1250 291614262 291614287
    0xe06150f13060f09020903060708091f0e01150b120a150b0c0106080102120a0504020a08010623041401060818011b080601020f1903020f15010f06030606090b0c0102 72
    0xd03220700030040004030710145000203056003580d203900a0f2a80500510050803552000030320107170702c03000c02d01d040246074691403403103030625031182120310070b0f00929041002c0850494002035840c1c0c58000082109040450501c000c0d200d06000f036903800c41c4100807041600c1400010150440c0e10020f00240305107550310120b40002c51580407103032420001c211a10100c00030700c5031200404040c0c000b503240c0f49481888100380307000100b002d000386681d40045405d5449019450010385a443c000700f06580d02ca10032070031030650b010000710716000400d4150a039403c00340a086040000034002030141c1c0d0074030b4420f8601d0200200707500c854880d14078424030352190901404509400c0d9035030400c0081003c1d400142101e50040415055600260000300e5036100002e1122a003201e90030614015462031070101d050690702840c00307005200340440301000e20088004141281e0640d03020603002c5a0700e02095003510031611550010603103602e410041140e892004209081c51180018900390050441e0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291616762 1250 291615512 291615529
    0x11206050f19090c0201061a070c03020d1e050c03160308041a0f07030503011805040f020103110d06030605010e1e0703020304151a0a0f0e0402060d140408120a0e06150f 74
    0x11310060f9103400303040149060071094800300d0403405901518200d096102d40d0800461484000e0007150b0618a2030140907400944620280c0b0f0401d05030789240560074100d40c0d43c600034003014400c2c0682106003414812002d5143e003165401141281460714004400300c1d200018410074480e10030400400d51402c02032030040c1003481c0720340c440580300d5040c1010024460144403446000c1c1d480c1c0f03001c0c80040b6028011312031080350f09181c0418001001c01d21b450700d900540060165060600340084100081c07a085641600c4c401c0007012000d40c3c90529804450340001c050005814991000c0f84a180c441e4004551050017054031f41500c030b034040c50110031550942803404c01c0b04800c1c08003110919010300b80c000101700d0042414121410030200600c2c0d440080c1000f4858840002c20030021002500039540d03141030112100301c60314050030018003552185803240c4507070480d43c00050540501e84601ca8030661600024503150703031116a900380001c0c0d00c02e20035a00c40d00e000400a101d07541c0640 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291618012 1250 291616762 291616781
    0x1030b03031c0c0804020d11030c060d020304050d020a030f0c050c090f06040501140303180f0a08070311040219050c010908030109060311120c09040c030804090b011206050f1909 78
    0x1090b1800b0074840408500700e8280c408036400300030f0f5840921000d81c0e2507011a540043e000001e07800411080c0c000285814000382034103801c07036400305030040c0701070140d40518480c41c010000c0d22413211034894100d88a845034131000b00418289080c1480643c480e5008c40402ca00c91821100500b80e82c20019260741c0040710704801081c0507904000c1d003800c00740103030f50040c0803030110b0501c900c0081d40000e442e401540354001101804181e840070942c0c44402155071100041c064080c0c080d10380f01101e0311001e107400142e513851841030705110b060410b44226030781d4860000e80702c1c2c46003c1c01d10302245d080d0300c8800c440b11150b40303410082c00410414001140204140d600005190745036240900b9420160891103201c0c0803448030b941d611080c08920030056204c11101d048044d41c45d03150581048000c1c0c4c1010f040220040b50210301196164460101e807202620b6030158580005821801c1c3d90030ba01466820010140c811719860038000c0c1400844442c107071070a003001d911070f50740c01c0c100d418640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291619262 1250 291618012 291618037
    0xc020609162c25090e01150302160f17040b0405360925050105070c030519020906030a020a05041a0904050601090c0906020705010507080c061305010c020109110402030601030b0303 79
    0x805102d043c0c00319103010580041281002000343e4a040d88407044190305224a00041c25010160541980300b98126114665140907481400400f400c0c680ca06940591080301c42c81802c0c0c0600003890f83c0c0c001900c0403030700c698100740d140070304050902014030340442035843c1040701041070900c0d654000c104480c02600e60000361800c0d1902d000d009241c81d40b0f140240c4811440c80240c41c0c80000d1403401d14064070800e087c4150b554a141c500081c211802d640084e0583c0244910804000f5010400b03210850003200d410b951a12902c08140e00c03001c40788030003980701d0040101002030f41081d8104604140218402c1c03401d0715007400224000c0750f41250102c0380b0b508002d0052203030050600c1080c1c1d0001c550f14114080c80d080900c065501c4450f4001c80741441004540f80e001c000e00e900460759550800d905841c11420905080402800644003c0321076509040d407400c00c00d80f0521446d0030403034000410007940189001800300035400580900d04058a81700c01d40703a02c1d141000181145840c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291620512 1250 291619262 291619291
    0x1703040909030c0803390403020d03050c070f05040b0f0319021903060f05091501170a060c0e2b03050f04080703050d1b0b0402060d06050907030c020609162c 69
    0x7400d91b44c0019101603140c014040750044c048960b2610b80c81580d09599054a2030054075040341000d850034002d003030700e07050244952400498070081c070300d190b0801c03264162000d00620f244001002281e16121401c10780580c80480b5142c212910302010181aa001070546010803139822074202504402c4c0d0819103030b290300c4030109031400c05144245644600c2000141241c002d880352408100d0314103202e1451040c00008110788406000c0c0600601940d1103481004000e401ca08080d02191402c1441489203105456418418007000b83c419601400ca51190003074504541d015650b41c1c00000115090036003d020106010408000d150080d6004400500019040c448024450007006407804080ca90344c41c01c003000200da00d41d80c80d8225904036001074841e821450898024841580219030120500341404000b541580c01a400d281455003900d01079600c141c281661441403030300301e041c1c000802c8001c00141d2124400d09614100303071802103101c8841200d0603103031036074241c45181a903003a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291621762 1250 291620512 291620551
    0x507120c0c0c0918030f11010204090b10090602030a0f0e0909071a04030201090611010b0d0c0602120903071202060d02030415060e0708040602030a1103040c0f1703040909030c0803 79
    0x2180324030340c014000d1241c24042c120450020013407040c6100ba00406000141188884e018094140408110751000003152075030784e1412104040c1c8440fa035514004c2484012810019216074400c6007904c205030021440d00020401c00c035100418111241c0c00c0080d040c060752200e650b15141a80110b88103801042c3d4a424804c040ca00d0b1410303a149018011410041000180d0b00a9040c1c0e003125402e04204806000d01c150345805070602400b00b551001140b51884100403068040304203561843e4216841c0340303902180903109114890300540c1c90b51207070340100020700d50840300504141c070181c0300b142000c0b0001010f000380c0e0400e4404130b03151a000ea0086200d00f410384038802c02800c035140750020904041c2c101800d0b01001400160849400000041c081501e070b400000c00c0305e082000f10341d13881c5850300300040308814034081c40c1d0310070078103130400601ea142000c21074000806160107145098541041c140040044003401c80034040c14440344004581c800c80907500c140925440800301d90322 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291623012 1250 291621762 291621773
    0xc090c1801050a080a0f1107121e09050d062415031a040f02090a030b06100e0306070c260705010e061003230f03070c1401120507120c0c 60
    0x111410303450304004041c42030071682d80c0d101c2c1207242c201c01000000110045641e5024003d031242e040c8546103900f001582c5003c0040320340d0444e0384041c040e5180d0501c002034540d2080324008800e130500004e0481c0e0014001860b0183c0f001d801944580300c0000c0000e203000b035440c1c4a124031440803242e5282c6060800c9031080807400b5031140c448914041145040b8450151044401c110340540141d6a0780313840c06604030301d541114201c0100412855a45a9174a406001c106044031440d018022074800903280c01e0107007148080c0c0c0340e001005032000c0c2ea11000c2c00c07104d0034003245060b15040c0c0c078003081440300e40015107c1c584443c18011882d59601003401c20703600351403a2400450141e445541008500707000c00c00c244050700d03800030000040313524100b0742c01425001802800c290b0700813451110780400d00000200310303a5104001000c0c41d580c2c0c58010640d6103511903040340c08503000740d05034204001c00b039110300d500042c14201074074900580305082045404003001c0b240031038400f00c0c0082c103021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291624262 1250 291623012 291623047
    0x1e0f190f0e0105120a0209030c060409060f0806073014091605100f020f15060a140607082a1f020c100c0917150c0703021e0c090c 57
    0x450030308016251814800300e60704c0d803040050000c0261980800c000b10196024003003140410801420103480b0307602c2d000e5a600904261103400c001c0c41e4102d000040c40755010560a00c2000e6680755030070400000e041d0616070f01c50900010036540001c1d200300300015118890600d881c40716080081c118030b0a40445440d040c07600c8682c0300b03418954030003005940d445c50406000944540341180c88940300703400591400790b054024903818020815510305040c214800f4034800c0030111550554241d598035080b032400707180b01c019600038004110003000309107000000d10ba540c0000ca504001e0b01a1802c07403642c1c82c00321402105240e008498541228a12070007080d8480820400440c40c0025444080307603500c4403000c260b4900c80c0c444c403005102d035016074940070060a030b00000c0d002a206c0011086e4071125078120900040ba034003004030b03075010491801e407010580d1503001840c064038030005a80c50410310b00741c5028240310301150341006488002c402c90142440e660710640b038100b01d0541140703c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291625512 1250 291624262 291624287
    0x100510020309031e0703080316031104030512070f0f1505061207031202010b03161503020301120204050907080a06020c1509060a0b010903290109021e0f190f 69
    0x154814009203990380d4000c500310054a80200f84d004003901c086483c28140b0003694070241c2451804010042c00400045034001c8000349a44c04100c1c2010b0031401054034040c5000107880340e03008043c0e80c60031000d03031001800110b0194010412111050b540e0003442d041d950303411100e8480100506890081c0d03030003015000401225000c4241c0000f4000b256207100505c40944803011504140c00458004c0d4480051076001905680c4080381d00c03121007420085d6445241d0aa4105030800040c4610034402c3c0c81c10385410012000c0c08114a40801c00540409400400580905140090304450401c405220386101d444007580761070414451604007161241140034038140001086141900032030419882110194009020402d01c00100c40d846c031150030080c10f4902403c412111070403541211103009444202c010560707a01c41e4004000d900803000030301c0868540e1110b0381310401c007900140c001c5d100c2c0380e0001030500700e091242564044254405ea00800d14580b03000c140c0a5014141c0c5170070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291626762 1250 291625512 291625517
    0x2150603010c020309090c04050409030c051006050a0302040b040e012309010c080403050d0b09040c0306051f150212030a0209030d031802092d07030c0c08040302060901110303100510 80
    0x8000d000300c00030b504da11a2098542c4600c1172a000150070340000340c1520040c0501400421044c0c03814507025104040451050350244a01c2c04e10200c40852401200e00303691010341000b80076440c1d50300303010141104120003944540c03521079506505500344208040da101000916500c40c1075540b046022500151002c1482c1e410702c424111887c0c0c10100c51a005685442d0055440010024220003840c268800da0b40c04041b20b0244000d101c60703810b20380103482c000e600c01c0101d43c075140410098138440381101100e207004810100054a0b01000400e0b01e00850700580b28448441c6070144d96039801184c43c1602a0b0b40410109100c0c24200520341078aa10740c1002c005030845d58200b00321000c1200002485404250005500c04010401a811202d4001c110803541503142c00c203012100003c4030080000303032414802111aa00c14071358a07100a80040c50a8a03050a6400b80074140d48000c0d005810300150316008440060704000551148408002021009080c00d04125440d107910b000e2104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291628012 1250 291626762 291626771
    0xd03170c13060e0a03080f0c030705100b03060f01061103090901171c0c110619020106090e150a0e0a020a0e01180209130911030106260102030708010b13030b070215060301 75
    0x545803191341e440d0040d41e82140038240c0300c041c001c0c0100e02c0d078480c0401c001078500006c2444810407031f002450b0703451044c807820103021407442c4000303040d500d00080b0307920303800c13100e1a400410601b40070b640c0b1800541420415645041e16040220713001140c00e0b0300000307800c0780322041503103410800c2c00490784041c662440340000c0310002d00d00500c135000c514405072041e0203517034000c2c0700d50b524030b401caa640050f1030801914140d50005c010f8020510b501c1121103160030080d42d0441c1942c0401c5802c2007152986140e402c07900d40303807020b500905d040900303200d46101e005401805645c980303c41c4002803d440740904950343c1040c00b4800c1503201c1c0f180e0100428018007006505503500c07400e00354085540300000030051703418180088908505482540c2651078020086090070454041d0001c103941800d202407290004031045080f0701c012a2684000381c46000103228041041004000c0005225050550f098681c0c0311041030b10f85c180c5107000540e01408028215000d101701c001e81c0100210000c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291629262 1250 291628012 291628037
    0x10f0203010b07170409061205070b0a1704050109230d030c140702041e0b041407020601120305041e0905060f010e0418050f0d02060a020c07050d03170c1306 69
    0x14503034002d0507070081c1601945104c091140c1c08540c00e03200100200744007407020300c2d0b503000d00c0a0041320b54542640ca502406074003142d90001c0340b080312018121030b91420101c1c440141c10713110f00300303028008882c3c95403184072000c00b080500e0403520003403425004440c8005807552802d45000500107000c420305041c46450104140c2040d9122400c0c0d0002c0405a550441c80c40064020300003040f9415460806401c1030703454822640c051005070b681035504100301081070070001031041c4200d400e080140e10510060000030007a80001c07407007034442d040040c1410340714100c2c00480c022044101c110240480c1c000c10035120346000d85038001c1f2059980ba0155110070000802c60400c02c1c008038000c030b031542c0d035005086541c0c150070ba01c00e580005c1640c1c5100c08261155032640b2003c600c0b600188205c0020604110562080303650003407507800100300091801061004003d4545002d038103206055001220318115800312a10841d01d2510281d580c0d03008016039a03002d011504045c04100c82d114099 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291630512 1250 291629262 291629279
    0x91809030706090503160305090f0409080306041503080a0201020a0801170a03050f0c1e070e0f061e092a0403051902030c0a0303020105011a0307050711040612030809010f020301 78
    0x880d0744640018002c280c05166051241ca90b11501d5002c1404103844030f004010f06034400c01502042c1412104602003418440401c41510410440500711550820208143d4942507000000701010300c98503d041036500c0d281d010f11342d001005442c0140c2d40004e4800d00c1998060030701805081211050030303016941488965a40c800903c000f02403000001d02c030311807074424809450300c1c0c0c80000c4c00c80f030341900701c200411400c808070303803500b07a4a114007a00498601e66030441c20b403144405010b845080c0e541c020800080a100c09100011040902d40c084100c0d2200e0f00800d1080d90103003820b0b902001e0307110030903207c40000315904000120a006c1031001400c04142a00405d0354036840c0d030340070801b50000904142800d062554050800c0078008100354040d00010f04a642407919007400c6008051400d1642c0310495112002420400c44000010f1407200034540600c0003500005030387c1d442d103071455040054080b00fa80800c10035010841c1c0d01c2c100b4040c4050703e4004d50000d5003103500d005081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291631762 1250 291630512 291630517
    0x10110c0a031e060b0607081201050126060a180b1311040e06060f0301180b010216090c030608010501062a031709010e0102030a1a0a032f030307030509180903 69
    0x1d0794416000c0200c002c0501003550071076001d14030000d02d075a0791880070345041200c950008400910415029000083c990702030320000040c0c2080032a215803034002c0c40010351070408020880f95104100700c00100d004030761801d003000381d622030210004035000d2090801080e91008002078050a027401101c044110b21101601c00701c030401c21070310415844030301c00240503004001c1c030a04441004000003443d800c41c0245481c0019003070f5000c00c245c2203144012070311050090050512443c04440c01c103c49803590b40980342c0c01c0424580000d150b5250000b20f07094400a88c00300c0300050100c0c01000e0440b0041c0e903499034002225094468541066602400707110308800c2040800d42c41c000042c54540d8203402c0012000c0151008541c0c84c034000314040010304440184000d681d0712100900300e541007240c200b10603690821044045041d003211000d054044103080303c8030a04001c0d40080180e2020401740500601c00e445182d210003c420034001444410882a1400c807051030a201103030402004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291633012 1250 291631762 291631793
    0x181a0f1b090a03080d0b0111060105060712030f0f0605030d0302030105090c0309330c0703140a030209120105060f18040204020d0b220c050a020303130c0510110c0a03 73
    0x4a581c442141070005000281c0703a0f0b1014203da00c00050009002c078240d4840ca2000c1000d03220000c079051a8500c26684081c2406083c3c0c100c2010480c4101182c41c030700e4081d241000505d008a80c2078035030f14554080c0c48a140b1098881c03501d40c071003070103e490288050030344080705140c11403c56240c20002a540300d0050700d448908203001010843c0381c0c04c140301072802640702011000d0b440070180c050020341c001c0c21001905401405002c40c0b90205284106c0e01600d80555032182410400000f6220940c0002e0400d424554200f01400c00b98030388a48000380c2e21100d100024803032401c1414030281084a0b0b1415200703956135070350b180d41d034428103c2c082d4000350117032030042c4c540303561564150081c00c1014940740c0c0840c501700400b090041c41e085961000ea5400000d0195200208040e2030301e000d494030b01c10160b0002c1c07002aa0721034204c070240c1001401100e141c0c2c03e990382c0720081100902c824820800003580c0c90001d40d80030000b004804001d1600741c0c0c200c01c0c2c3d245140c44080540c1105003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291634262 1250 291633012 291633061
    0x9150510030902061303170f0d0b030f0f060105040c03060308030f0a0204090f0c020f160e0c0d050705250206070809030703051906050609040b0403050a03181a0f 71
    0xa000c40251031090788452586030703010780840c1c5e6803c50303000c024548200714402280ca0b401e0030b0b58504082000c001c2543c0724242c4101c0c6c61030410362440c2030f540103000700000d61509407090a0310304114000c2088200f100036800d01c05030001d94140810b0000741d0b100d0603201c10626081240400024811000b269030004209a2081d000c0c0c4070003410300041d2050b50b0003202e0250030700c1c0e2245103100c4264060582e9040c1a021a00c8413110709013401d482e4007605c90070400a1240103810030442d00c49660032540300006030103851070620103600345011100285c8100300001c60104c0c06d000c004503001c9003170b072014114100030300c00a06590f0000f8014424250010128170000c1210170551b00c080143d0300213581d204003560701032030b003502e0901e0009280c158160381140c1403401040c12401d080140340e0040b600b00384c4529207035690741c80513100d981c420643d1004041e9101c0c0500c18103105400e001555500c01d10080e25124043c0b0350200714250042d0404204c0e03403000080c01000c00c0c12442840c400c20154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291635512 1250 291634262 291634279
    0x110417030c0327040f05090607030b060313060e010203010801321620010c0e1e060708130e040b0109020c070612020d0609060e0c07050a110d02030a030207030309091505 74
    0xf42410030303a0b00e698012150090304080c00c0402240c22038202610421a0300d04030340311540d40b0740c0200c040d00c0c41400c02e00d401140c2000820040d01030011607070825401541d001c1040301501c0005400c90f842680013007001d941d124a40001d08540800b401b025100c0c0840000d04000d900f14031011110014214210b1103040d10b0034102154060000080340490007800d0030347ca00c5400010501800007070103c44005140042c000782549001c0107090f109440215a413141c052041e4248030301d81c3c0c040030003615240d405210020101c10388105000107406140c4081035070f410103207000005124180c00048006006010107030070f00500091040456540d4513200d0414681c0c100d00c88002d106034091a2101800e1400c0400e14030b9050300600100c0d101103861100503691609104c200d030103001402422a0803a806450215542c4418082954030082603030703040c0f001690003e8a020113514041b0050380101408000381071f0410140e4009181c006002c0c03010440200c0413003a2130525006003840741c4e846 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291636762 1250 291635512 291635557
    0x10f050a0e120312070906030c08040b100b1b0c101d010302130e090d030209010f03090510050103140d030e0d05211906050a06050d0c1101110417030c03 67
    0xc10b441000900303140400d0740d0760b03155800034120140404031459030208200140010b800d9100e80320310030b2042c00c2c69890280c1d41d1a0b0b55a9a008000c000d000b01082041400d804a0b100d00d42100a14070210149000c500c2c0d148610001400c210307820039090b21916a00400101594000c0641c00d03180e0b204440d0000b0b0414481d0059009005a01d000f0300d00244044000ca000003c0c00e11490262466000300c440f0303645903050440c240d218a04513240014064403c0301c0845020f5000340e41c456206606664840c050b014007801142e909a0042c0c0c0c1d15125901110b0701d0090a200c6803440c3d000d0362406100296081c00525943c02c2c85114603000c000c000a00301e03004d440b21001081074000c80d2003006099041081406ca4040c41d03c01e100070a4034500440002c452074400010011542c154031414184000e07480500300801c5194508020320942030301e84495000300784614111b151406079038680b00d07424120800101d129075440000e07135900401807240034440020941f0074024414240c1c042c482c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291638012 1250 291636762 291636769
    0x1091a0306040f0513030905032103040f12080601030b1e06070201050c06070504080607020303132907120e01020405280305070602070e090d09060305060f090a0504050705010f050a0e 80
    0x8201110118074004c10b00240000c1000042c4149029a60748032240c0d449908240c0c444c241e0400c0700d524000d40d100c500c0a220310410185030b001f4020005080c140d010b54070b07040f000d401030140c3d0500155004040003010768051040d4800d1040544000c2200e40c5280c1001c0120001c030002e40b8401c100208004045a11800403140443d50100031743d45182054003000d81590410700865500b40905130009a001348004203a9118440704c080007523000540d9100e81c0301e1040c411645650702d2441e004400b58800300c2403441e6004803020b40c0d41c000c610501003000d8045500308210021140d00400007001155070b0f100481484450603c0c0d04c0c450b814160303c0d00d9554481c943e00050a50185042c0014880d802007000812a00d0103502040c00c2d50b240003502d034031192281411000308d01d4030103041c42074911907032100d6030000f005400d50101509400005044017000c413980da00680e290020801009024080c0358018042801c1103581403070120000b600c0c1d4022030181c00c04001d00a041250039a8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291639262 1250 291638012 291638021
    0xf2301050418020307090606020606060a08070c1a0702060a060501020a02090402042d09030905040b0d0311010618090606052d0301110a030f0c0207050303070305130f06080405070501091a030604 85
    0xf58000d04032040d5603581d440c61405000184980009809424006402801c1c150b049405558560352003084a41e540413069a9890041c0c40644000002c005620180b085000025014030f130715400804c00ca16018141100f44c403115000700b8115045804282e00584559203800d0700581c0c100d401117006c0c03400c003100e404045c007200441100500f2440c40c1216a1403180d014200d95406540ea03000c25545880c14403050355901c125294024601c0c031f00b00700100f40714408917080030103000004140c3e150344071080c15129803c0e01f0ba41228a960362400800c10107640f0400c0002c00090b6070340d40600203005901c00305001c280356514041c40c0c041450b0580c036078083d4095801040002c1032107480b194030803c000c004100c55940c4080c080d01e003100c0308604500000f403000490b80002d00852400703a0542d0304039001d17003149015800000034510301040c2211008020f1001d000c00303603210011752525081031440c00e000366201d50b040c84070200c0103022403541c90111120480b81d50300980d689450f0180880c0090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 291640512 1250 291639262 291639311
    0x501020c030708040317040f0306020c010b0a1502070e010f051915051209210717030703200f1e091f02010e2a06040e09010f23010504 59
    0x2400001070000401000b0310141040e24001d246002d03e0300800f886c91100ca2282e40038040c100300c00070b1070410000300b0903001001c038849060000300308048402e0100c0c9210400c0d801001c0c140c3c0705900c1c526600c0b907041040ca070085c050301003c0111540350034096091a0030502455005210704901c08014500c4040c3c81d1005240305000c16403444681d01006109411440380d80710b54030503001c0401d488400000f03c01041d11a4001458110b50482118208980c0711680856503800c2007402e90281e40f010202840c4214000d07100460040c4ac542c5520090540000c1085da07034010a002020400c6c11150036140d5400c410465403002c10b400c484103c006021703d0034410361101d0450042e800108104040341d9445400303800a2250211820002d510b4009502c201400b0000c8407001c155007440b0303000020303109680648110701d81500c80c00c0891000744215560042c91b910352091030030078041e0380300e2785000c000640000c1c130704043d040c055031900c02010710600c1d10035501e91103088000d10480c5903e107000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 291641762 1250 291640512 291640537
    0x20f0609060f030106020102040f05060705070e0a090611090f0d4b0b0603191e0f03020304081605090403140d240902090307060f02010f05040b040b01050109080712050102 75
    0x8941c0d45200c021f005c2e40c402d008034240d0b00344d040380004040c1080419500c0040e8080060b202c0141040c1604814202c01000042480d4555100001041c054482c002c030080d40d40000365503032a0004103111143c9240c0300c1d00c81c003500b070340c4072020042120036241c091407400341c00c2c1150740c0c04103250462040082d900781d125552a0413429200e150040c1a85240040b40300340d031849103d5a611081644951901d00c500350401060048400004c25005500710203031440014413041460580315411400c4080320f08502681c00000c0c1840300d4401004044070381d1038071880c240c0d2040c0c1010045605128007600040030700801400c1c1c44514020041510908580c02c0b604003c622815440d2035500b010f00260202040d01005002c95644514002c5414810010300203000d451300d8980e040f60000c5074249003404556966002241501d00341c02035a000301c1c050414a8483e0616061012034800181d100704d050000250040210604c0400c030141210202003040d101c000349030501c140a8440c400f4058807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 291643012 1250 291641762 291641767
    0x100203150406080a0303141605131a0301030b060d0f0201031a09090706090807050a12030c06021603200613080c060103060c080112150504020f030111030603010f09020f0609060f 78
    0x407a038200003903003404c1c18000d0750103100d442106a14088144404da0308020801403890710580c20350300840080c0469131a466990031810340c4d4001300c00003111000b040d04a07a10f000001001030041c040d40d2950886400c48000d1011011a6641d5240b402c240d113000b81495118146204003100c03a480c0c0030403502014103601141c0c50010382d143d444690758060940419204180030070f044030006000003e8880c0500651009400c00c680c0c280c405400230012800c202c0d8aa81c41c00008a0500181ca1a01c601440c0120280010302ccc018050000c1c4400711036400c282d01801c00600f0320000340140c1c1021036904000f1004150341000c60040c4500710b040c4900d0300c901c400020805c203059102484c00307002c1c1d560350501130b42c031000d6010484a0400e00a0040740699a101c0c1240c100d60707011033b401c50b2004220039404006c520220317080d902001340c0214412004400c002c102e08080c040c182d070400ca41c48040000904d50360001d003201c5407000019000d8034010645152035165141210f0302c6c16814042c182c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 291644262 1250 291643012 291643019
    0xa0911070c14010906030e0c060717040603150b1315090801050c0409060b070c0303050912100c020606181302040e0a0b0105011707050a0f12090f23100203150406 71
    0x402d000c03200c0c00501d000a841c41c0380042c20501c244110030240c001c03030014024105444c810000540c00030030301610030702109508081ca0307111000045c40207244a403004644030340c131203011042c91079982d4003104220380b0030890f0f1140000c0001b41c0b2815550360164010000401600032110f401c0070b034005820310b40c40e000500038962509006003088a000100178055542c944a400200f802422001800345039519024000640200302400d21200d0240c54920302c0d5482101c080d161451150792040803c1d43e822070a0651a81403100d10782c88403003903c109041810082d4078850408005219003100705240368420110768503500070001c1410144200e0340b8810503410500c412003420301c0b645001c641c543c80018101904006020b2150300b071512018103190b01441e06603100a00320361008100b0410404009004001e807007103515040c019a010070482c1e429107000d81151001d01000500c1894880106c0b001050000d4683c000c0318101b04c0141c0c40c0e031680c940341030b45208411241e640c45402c3c0360005c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 291645512 1250 291644262 291644279
    0x22e03050103021c12080a111c05091f0e0c040504080a020708060c0406081008010c030e010b041512110418020f0a081207020a0e010b04050a140a0911070c 68
    0x21410382c0c0c02100d02e010044007000c1108071041000350001c00b8003c0580d040c40546008000107a403080740c9000c0424021080c03082d000c0135501440d007c04411030040b041c0020b000302445003030b0f0b000499500510242c600814903014807120140000303c8640c643c0680d010303024040c0031030400b11170042c1013400241480c2c03510740120380000342194014454004000f0300d03180b0024506000d40700c201e00840c5040c0c105030040f200d0107030003001070340300140d8002f001403034420074031490041d46203980d000600c240f481c0c1d03240c03400c0d500408551442107050910009008540d039440200312550400d504003500941e1400700d00803c8103103d4542c1c424a0244181007001080314241c0310144215030446424084c60100507016000380034000c45030b840150b10341c50000c4004020601e2a00040c02d090385103071b807800e140a4555098015101c800404202006141413028440c0041c1c030100041e00a60710a24002c07030000c80c418401c0014044d26412400c540100300c20441d0303001900482c07219450307a15081034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 291646762 1250 291645512 291645521
    0x4050909030712020105190f02280e0303030c1b0a050f0105040c1e0e0a0b0d06090b0903070b0a050703060305010c0f1d03030f031f1202040f05070c022e03 68
    0x2a24100610300c02030f01042e10600c9501e02c07447c0702e40d40c0c0d182da001e0101004001001c2410300d0110895080002540880c5800d00c0401204240402011064102803005049160001816001c0e5005006000304146008180c0305108450b0140c80d0501701c58203801c510303104001101078800e00440c1d00040e50200103403c064492401401c80300c055640d00c4008544c6040c280c103034600d501290a1040c861506c640d6800c0d5009411180049098240c0b400010b005000d81141240c2156031403a031042001912000d50b64050300d900c010314203180c0a52141030003c08001c1c0030041440c0d42d400059411402a40100d000d15004402088489d00c09040a059920b0001411010a220030685402a00c68105034001e11101501850030584d809684d1801d03500058801c0315840c80400580703060313801118018004244400d00340542c55142c0c014001124030b19000410850304020805c0142500440044181a41901c2c0d044003020090003c8080f01d50320040120312001d0720303600d0410154550030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 291648012 1250 291646762 291646777
    0x4050312370801060507020303121902040e040b06030d090312050f0403063e030c19080106110303071b050703050105090a021504030314030a0b030712060c0305060f10050405090903 79
    0x2680c040c540d0300c0300005c0d14140102030000358194020489500340c600881c450350342211541d601e003000c900003c1040001da820580040d141e1003c0c02080000b40800c200710903030084002c3e8007400003070600f61802800d82c0c026000151441c900c0a60090404e44140125485a03040790f8040c0d03102c0d83c90f85008409806140791681c00b41c0203d602d01c046042d000420600c00302d4549a080c049451031541c8010190070007000c1080c1d0301000d1041c46000044060514a104680d035207101081d0304007180500180107960f44102154400c0c4104151903030050b400c200c080e000240d00c0d0700c6444030b5103422468510a900020800d50908080c061401800120384414034401c548102e00c880c02d000c15406d1500591001400041c4420b00409240c0b80a20082d900b0451209002c0795202e80440401d29203800340e401040148600c1002c4428041c00c0e20035114100510f203020b20050a0420014210034900d0352000d1150001c1c20b18100214096002c8034020200584002110b00d0080c115540b207400014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 291649262 1250 291648012 291648017
    0x210209070905030f1f0b1203071202060106113712090806100603020705100504050a11040c090902091306080a02030105010b12040807151d0c03030405031237 69
    0x300381e41c2c2080800325100c001e104028016409451805a4170303005004190a00e54209100c0031107054416418070080408600848180030301c8408818000e25041c01648103c0401000d21008000e80f803001c10baa16101500301c50110305c0d01d60318494844011041000070740508102c842e00c6081140401401030301d04c0c06901c458102d603075215419070311074008480041c59880f0809090200c24040d6000e86807a5000e82c046400c1d80e00058880c408036401620241c809501c0400e03130b6070401c83c200302414226281035809110392042c048003d8802c030210300070307c586503401117541c010325110030301c1c0f1209941c10329070b060040e1031b540e02d8007a072207103441482070b8081e500b080c0c000318485618604031101400c108080081c180c1d696143c10340b80740c00040c3c1c211030311280304e42c102080702c2c1d482c05034100300201e4006c0040e581008151044c584a203108910303000c0e0704248401c00140c1d0b004109102441c21400500d961030402c149080d543c40780702400b06551000030480c2020350240360001001c45040f94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 291650512 1250 291649262 291649273
    0x20d021611030a02030733020601050f0406050916110703062903060c0d06091b120605061803030906070807030e181315020f0903010f110421020907090503 68
    0x2107092640b10502ca2074081d415a100d01030400880308803000100c030182038041c607590004a50f202c6540104607102d40f40c0010b9000d1030040c4505e240181c500300d07990313000310342c204012441e01c004144020002060349000c9a10134003641101405088450a5241d10805076600545c80303280000003030103a180c0c2203000200201802d5100d071030b440c0740d40078807900040003804aaa0750b4118015540d00490303851181540714940013400002c54010301c02c1c4000542c40c1c0c488195034400c4018600a00c1c1c6c3c040c1c0d1306c0c003400d0000030050303038542d90102c0d40144010000f004180b80f010700400c1c079500c134840c081c940101c00054044103009002e4060860341e48070303640b81e03160740e001d8104210b1058038401c6465100382c40403000c02c0b06848103105403c110b0344514854918006180e001004982200500015107000010803c0440c90b0a204030007421202145c00c103c4c24110150402c554020b601441481d54420400fa01500103c40c04031060254000c01151203480c110800604980355889103d0091144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 291651762 1250 291650512 291650543
    0x10c020109260f0c100504060b010e04092d120503010611010e070b03040302010e0a0b010f061418060706050a020d06060e090601080703060503101a030307081c020d0216 74
    0x3146041a4040b032004026050040712883c424641d44840e21550f00c074402e2007006001c5c10424003c3c1c034442e03030207200c00240c03010360540003408240703004039814492403508462000103240406201e5030712421500c0845004030310320394005201074000c40501030000c540300d411242c6038072100030f5044e61303040c0e61001f40e40543d003a01a801d84814211080a9030070030343c0706000c0195807001960307115000348000f0524072190300e02e882c24000d010609480070f01c0050014000e845861511400811462920110700f400494080c242400f41103014101c049040c40c00d80d400d03580d100161102d0f10303080311041041c1d040c030500c460020341c4a810314800e03181c10440002003103405401c1d50716002c10041e281c040d00d41e54050045654480003003076101895a07503034003c1345503101080300c244015900f03480090034524080d84d201040c41c0e518000c45c400c2d4010445000014090000c0c0da40b1201c50180d45020200c154901001034014480081c0e2840e10100b955280c1d50883c100a41c403890142c6e00d4041074180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 291653012 1250 291651762 291651803
    0x219060c18081203070302040b0304050a1101050c1b012a150204080d0c061d15011e0b0309030f07110906060301140d0809100c05010b0108070c03030b0f03010c020109 73
    0x2a0b0700ca90300d11038100910f02014550520011a071203512443c0040c035298940c449000181c0041c0d90a4915621284640007080200400c0040000003420314a003004110340c10540e6888416191208607481160b0190480e4040d0036503802400a04550300051516200e00c81e00c0007517614000c2d1018132503000c2501c0c050801b4802c5800342d0303a41e80043c00011252800554264101c40d2003101c18581e240b00c0300e040415030f480c81900059102c030140055039002c00b1859000703c1d040c0c120f140140440174510b8182c0b0350214407001160900f4417200c0d00c0755900784c0381c50300314000c4101e00146250300258007410400a80d010b491105012512080e50303484100a11130307140400d0103071180140980d80480c41c2e41c9020000c00000c1c910860a0301c0c90712505402140e030070032541d100308000c19400d02a01040040030300605041c01802c0c03070644c01074034181500a085650020380601450303036800107001170b51684e00400d000107101800074400b025134002c0003402801c0107002038680380c407807900d8915150f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 291654262 1250 291653012 291653057
    0x40b0f0106080c03040c030506090709061e0e0a0b100906020d02010c05090f03010f0f021201060219030e0111060f090d0905030a0311031209060f070206060d060c0219060c 75
    0x200590b444015641c0c4000121420381e1000d0001d60301101030200c0000010300403c15244501000e501820b07403180381612560544c1d000f40c10a40241c1c110381340c0b4404520081c488030040f01c580d1205080356442e4040004024015250b40c141c1109044400c107040f0354000400d074080703800f0740e4202c0d41c0f0401002d604a00702c919070260000050701c10440c2e00030a00d420520a65089401800001c4150742040034034200c8841000fa104159008280641001c4060240d140182040d001420500d41b103075401150b05216880010705120003098206a00d07482140d0101451100604595407410b00c00241c4d04458422101c0300482e12580d509031042c0d912409a003000c13140301800901c1801036680d02603030003485545001809100902014240743c2400d50003501403241d03003000e04041d00f01888a141680c000030956400e5600c603c09009090301d800350032a18068210710300041203030104008a0a1083c01d00321b80b103406c070111410209010042c0c0c440707108521141c40784105055404030000518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 291655512 1250 291654262 291654269
    0x15060807020303070c030e060d0e0105010801140c0d09060f1406030c042309011806020a0807171302030309030109060501080c27061f020c0103110c190203190b040b0f01 74
    0x948002e24005c0000d00503c8035225032540240344604094900040008540400543c034400b40c4d1600010440c0c41c2c030a206003600c1e442000c0c089180c6140400d0885000d1040080d0fa0105039610078984050104941c820031481c010040144104642144d902681007810b5400070702c64054210210500d180620551061083c0e40900d07a0700508010680c0380020001002c0d481555200d1046c009401d80781009011b07098815180180c80c3c0d00c440a0091040100815400c20700c1407101c264140280441074041d4801c4100811104140162010a00390301034034408175095030030401c001c01001201c0d08424141c1758110210740080f00020200203107182d02c4034065500d440560b0503d0480402c03601600d6100707001602441c01781018031f104251701d0005032840340058003d802281d00e0b56034140511200e501c10fa41e001c50801c021322041588600461340078105c15070111044034110b440601c6200c4152685c940814090702d12803c00c5100e82c581200d04880e002101c20001b10000c1507410b03400d059 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 291656762 1250 291655512 291655517
    0x20607090f12020105030405070509040f0303150b0403120903081803100506280506040e070e010315120c0e18190b070c030e0406090209120102070b0c09131506080702030307 76
    0x40241a001982c881e41b01600950311400340c0c920102d0a52602c550560256116513942c0e001e00203141001401c4a0b080c2c1503002d08081c2c80c2004010f8451810140c03000e49401c50000300c265401e140c400c0c0c0b103140da10380c0700600e040000710b001c05002403c80102e4210440a805641c0500429507a002c1120b01c101c2d800b0354040d58404200300700302c400c0041140480c2030403407041c451540310b100141031500994806401d00780008100401c0641c0030b10510b600c50405e08061025418012580079405d29078040c44264201c4485a24207001c00001d804004100f0050000c07a03a0a041408100480740e00d011074589203d5a000e4082c00e02202d800480302c41d8112803010a01e80392240d04a0740410b01c84d00c00e03030411003c81001503140e511446400000c1008001c01640c402c03595060107882c00780034100c110140d20510290010030104842b20354408010104039586403025000100c0c0d503d01c8c140d400d104240744c20b40400d12540c0c4202003005403100c07519074510555407a08226034070710040350035000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291658012 1250 291656762 291656789
    0x8010609090206030c09030a0503030109020d06090504020d02130b0a03080403020f06030103030e0603180105190605120a1b0f0905061503040503162a031407150e0a0510020607090f 79
    0x1c05c0e030414009840d182d040201a034081480c0794580e94034640003078011248546d8000fa46c00d210304483d00c00c0d00c0042488030810705c468a0240c0002e505111402b501038019580d00b1607444005045911242180d000108500c00060300d030b00707003c000707900706020480c01171140301d480c800c5a281c0381003a02d0490342d06a0301d504e41250300c81c040c001940c0001d45084000c81640c40c110f44528028001c55200d400f006504c49114460807089005990055020303070300072001c0c0000500ca50b5404100c01a83c00c0e002480503400c040d0003440b20080a5030b50b8030006001103038400c080760520440c1c0000780102d104a40b50180c1c2c50040d40c4603505031102751001481540704020004008505000110000d40103050309059034031114100c0243c1544801c04525170303040d40c2000d00400002c5000d002c1d010580304000c28106080040780c440450080049106112001c55191102d50f0b6079006540545005810705548105890000c2d5071800c040c4c8503400459142c00b8046030800600302d1030b030219111a080d044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 291659262 1250 291658012 291658021
    0x42f0a0e0c0714030418020306190605090904211d06090105070212070f0b04030b0c0703020604021c050a0606050127060f0302090301060308120a02040608011703220801060909020603 80
    0x35211002c3c5207555100c1e000c203103c00100c407490724a800e02e10130800b003000359681c075040b001c0001c00443c51420300c2e040880c1901c10f01c01103074400103661080300c0c19a8200e800e074455090900042c0e4900181808402602040207030300744e40401804c0b004811101011522400c44c0200081c0d4007401d000c81d40015001d1050001501e0100540003c20b0305031003e490080380c94070000401e242141d0403094550f40c0004041040140542ca119030000902d404076041c80703180d41e002034607910080c2c4080d200e180c0d81ca041d13900c51903640e004192425803080c12941d01d200b1520305003004e001c80c0c1c41110302081602d501da845040424024031090800c000c0c1c1e1103025400c000007a50480d40c01411502016400d10101c40d007511b09114050185009800c0302d5110f400017511120344200090071460298014002040100c4e049464281514400c0d10381440020198200500d54090500300701c450162a00001101030150500e003400c0c0c4484200078400c40b6250603540050b43e00380c043c001c0d005141000000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 291660512 1250 291659262 291659273
    0x21218032a0d0207060905030304030213090201020f010e0d030c0f1e0302090616050106120c151202070320030406120b0301020906180a120b0f042f0a0e0c07 69
    0x107599000450900540004185001450301d5104424180035a01030f00081c000030b03810140000052804800440c42c0c00c4c11a8086050580c0d0038106001503912001c0c617034116070080c0304000305091560020004010812151581d45800d0220540401e00d404107a209451041c0c00315660074081c0d4680500d55400340710344c034032080c41e1a008074082503070a0058142790394610000b8031008440101003a2061b00c5414490300f1540703507034040120461000c410350000340702c0010103022903012814078101100006170030303103a20341004010040c461000400e10101074110740101240b050742c107203001c03004c0c4050402e5a80c1f4400e60003a140802c0750014510032800343d0342c0003055018000b40003d4104040302000c40e0b10b90304041186070600410318071080080c03c004104038000e20039405500b0020a503a00c40680802001c1d010212030040400000e09200150724481070045180340807855204099080951205141662078410584104005856841e41c001d550107882c5d43c0f80142d2402030f503540c44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 291661762 1250 291660512 291660547
    0xa060f0602250b0d200a090308070606030605040b040b07080c040509060f040212180a030e0603040f14031e0a0e090405010905060c030a0b03010c1b0c030b0a02121803 73
    0xc0b003407058007540801e02014070405401140f14240c0702007462641c0012000324209800e0140d8920036083c01a851013640c0050034904490b000142d0301e640b80010f00780b18001c0c24103a080a0162401d00c803e00080084803136440f40b00d6401800200c20645621004a90100041e12803045040050006100da071503d20b0f0785681040d00204001c0305004544046816a04156224a10b01c0b1144040240a0070300c510307503030a14003905021740900d68041d9001340015000314401805001c001c0002010400c0d0304141035112900b203031460501e01e40d40e610303040d030f84c0e4014030340f03694107000107284510407028400603582c144155031200030a108880c028821500002401501d00c1d40d03d4400d072001003002808424020001841300795503d00d8609580b034140c807030f4028900c0c06685486610742c11b544d4017078055009002903404611141e00700703042288514440f17400c0581812000c4051040c200d101e640100b0b00070406c0a409075055480c0d42e207440070308480c683c0103481c40d0010400000714a6013040d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 291663012 1250 291661762 291661813
    0x1150621020903150601140a0c03080c0d0e0102130506040b030105010503280902091e0711030d050c090a1505030627040b0105091803090f0a030213050a060f0602 71
    0x103040428020000b45031035000030006141c201c00d13009000017940d12070382e003010040310b001741140b0f0040d114400901600c80c40d00003400304007001000c1484160381004071661031405403000d00c140883e0b109803e000390300c0780002d09901c02090100140c5400d0500c1603400304c41c54106130a085070318260065030203078401045902c540c03d11880c1c500d202124141c3d40749400120803000200c0e075070035105000551901a00301c2c044542e1181c40200e001d03028150480d4064000d20381019202000320695146009084101c80d410f400c1404000030b140c2890050007c904084078024045561507a5001c0902c002a0503074001600410000e0014140241e403000038200e0741c01c180c1c680b403d42c800d410315030140603101201c00f007100e40010003180c5000102550031807912465101c00c1c60512240c180e5074450713070000d18003412100c207804d2569031307a05c4c1c25800115005811541078845190840b0024001121505446440c1810210f80f00300c010140e8411785a10340c0040540310203503ca040e80d940341501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 291664262 1250 291663012 291663077
    0x1020040504020a0c170d11070506150f1e0a0b07020310020304030c290603190f0212060106020706020f010203040b0403030504020a0503101d010c0c1209050409080c011506 75
    0x11044400200c40b100c0d00a1104910010b01e034846146c0441d070000e480b01c074038091a216005006500c0407130303004103e46800444008220000d4502c48000c1b87d10880031030200c603486140101101c01082070b44403280d01030b5000722070094125865615402040c020f54801a4140d0f02a095118a001041e8000d54020340039080c4200d80041584c0ca00303a00030321194141000700a01d01e034444d600d1100c08080780c1c1211089018200114101e200d0320300708142c250024041410914800c801d64a841d410100d0b402c202c1e00568420317685801c40696900303460b1150000502c14110700e040c075280b0620a4a001c2c503484100c659881d1603607203048002d4900500160fa00040c0c0c4030300000d0b2a43c0030890210121002140402e508480302c1c110101041d107403144440c940d040030f03c0c1c0c03c48180d004013400b00c8a5070001e01202c1246465000303c030070012503007020741c0180c50500d010f002e000a140282c0a035100e000000d001c6031030030700011501005103110380c0003c01c800c41c01c946410f414111685500c0126007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 291665512 1250 291664262 291664277
    0x150f03020d0609061805011a0a0c0204090c1a0f0a080405010e07060818190b04140708100e010b130f14100e011d060904140f1020040504020a 62
    0xe005402c840c515484400403503a240010444100f1071a500540070103101c0e07080000390303d48015a01a12001042d18032a04000560140e0f100d009550201030f00c1c0d00a4401c0151aa5a2902c052048114018540c08910385003540004c0c610110483d0000f0b44c0c0000c0403400c0400d05001554014409002103ca030754840d400010070900c20840c0030000c0c141030380d480010742042200e40851558150842030141c0143c1a818103154981c8114070400345d006841450581c3c030b80c104003460000030407408065000341d40001802c51000906803803102e8008601304881003922441ca03080f619540065a0094200b002d11700070003040c0e500c18013902507610030101c0e885000064115510b80c04840103400035101c51814003041c25030b141003d0140080355001594030892104019411400420491007030809a000404100c0e040d60b400300e12400c0c1d0001ca60314042c2018695403221882403081c10f8461a2032243d03185074101c3c00366401c0710004038030014a09400c00d024400650b21405c0c0400601108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 291666762 1250 291665512 291665527
    0x72304080f0706080606090102122128140403230c070906060912060504080405090403050a080702060112021905090112050c0d0b06061303080c010603140601150f0302 73
    0x7070000c0060300c860440a415042d041c40e40181540e1406000e15004910600c11001680d80004482d0450441e0ba04202d40b0380603900104040d0328044070350804000b99250520007032801c05500b400303840700c1842d02d0a040420700307803000c01201c0c1700c0c0304ea010544480801060200f4012820400c0204080c0203c0c000507480d403040c2207680d4003210701010710341e101180800107a00c10f40f150310094503407071401c101014034014480c0050806000081c00503a0307654046400c10030303200226002000060718074480340c60213080117070603504800140d03408660060300103402c442c030100c2c646044c1c0c2c0081e2010481403c85400303000500070180170340804c0148050340851141d452188040c02004c0c07002001c441c50304946404d601740b0704803e040c903000b03807002c8030004002204c219025a0115080d50100d458201380c00032020940004c0e80043c25900001445032072003407049d0402e0b025680a00301d11000b007010248807640c1e503d401d02c12050f0740f03108109070310721191040381e401c20540580e20700541000f20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 291668012 1250 291666762 291666779
    0x306092c251406040602030f1309051608160504091517030c0d0219020411070609080409061409040f1415040605060607030905060904150e070e0306072304 68
    0x200c46400501408464410005240c0d03035040740784190003c0d0740c260b0070a85401006542d90041c240084071141d000b01e421030013007a9900841004002004081c05203040c03181e8241001665400001d0002310303040e0006050440c0403014510342251aa42c4610300791405513810300810f150440a01805140b550000b0200d00308c82c0e0400040400c81d001d541d880d034101c20031500e44075516282030199001050103c0d090301e90f16945e840c0c0d0030b4042c5c0d00480e02014a0320015a2440b42510007480c03580f404d0200c07001c0c403248001038020380d04003a60404c03113039480d01140c46512801100c0306610807000f80008001418503800203049510a94881d2516081100c44608000d42c100c3c5089029065100b0001446001d0203105d030044000d0301d800c1d14284003a24018803010181c0103103402910000b0700300d480e94896901404200c1c00b406100304000d83c0701d44e008a20380e4030a94032000000d509036400c011074036020901c0e50240446450300715520344e4a00740481024001d824038480c40c802408001342811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 291669262 1250 291668012 291668053
    0x60509040e010b0d03080c071401050114010206091c0309050d030e120903070b280f170114013b040f0605011b0c1d2a0d05190e0d0306092c 61
    0x50380400046002ccd030400381c40e42a0648d280061034119401901880070046010508068a9400200030007941d00c3c017040603001b5144003000100a0310403d0b02c019261640b5034042400e0100d80c0e401d80b400b085d180000c40704240205030304160300d604180000c010342c0d000c400040254071480c030314204116a2592002100b90b8280c143c40002c2890b08000382103042e40070f014200d1034075603a0b0034400c440d4103080c100e40344907070401030345414415405040710a0036000c0950441d850080010144030121102442000f1150040110b0282e401c21520001c50303180c0d40100320640d241a510900710441020741d0308160850800c040e01c0104990402148140c1d034091640300c008028501c200c02420408194040c0343d00120549000900c5220010a10f040c00011a181700c9032580020071315072101c20015040c107041100f03c0310850b16002d158004041c02003080b090a4510340c40402c20140d940c0c4405e42035910010300c800c3c2079000d10700845403d0384040c1660707104103103440842c1d07404400b21003404604c0c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 291670512 1250 291669262 291669293
    0x220e0a0b130c09020a0e09041b060e01080c0c0a020d06110f090f04060b180f030d02010c090e130305030c0702040e03030604180503070f1b060509040e010b0d03080c07 73
    0x41016886290074014200c612100a2160f00e40131460007402d110001d100c04204c407100c61050508002141c02d1200c02c00285844660342941e000803240e807480701030b2002403060806404211a10700140780e00000030241c8140800c403002410400409508021494040712022214180c0d40d2104a40101802003d00490444443c0065540e480c00082101211030000307000c1c81a0b08000d41841440500000d8a441c2d84101e440d4540c0403091000042621604680c0d403601442030015160f030341607054001c0044840551101d81c007140e10b51904000c1e4040c100e0b601c1200301859012100068844c01c0210b40c0401000f01c4141416070302e078006025140c203402c40c0003040d0b1010081c0300d528a007902c1049040c089134101c003912000165581c544900038901301801a03c02e61034284c0c1880002c00031159007803410800307001c0d45500c1c2d41c030243c02908440017181c003c0b4a002001c90104c1014403444640f420020409a460302441d0341c02c581c9203c0090012446040910038000000c2d9507000003e642d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 291671762 1250 291670512 291670531
    0x191707050703051f1a010e041d030c06040b07020604030f050d06090219030606030b0108010e0601020c0315040b0c0720042c0105220b09010b1309050c220e0a0b 70
    0x4c504501c000505490100c1c0d05480c8450303144100e61040d130380088007102c4500d410748002c00d610070000080402e441140540000c14040040c10102414011400c0c600c00e030311822066a86441c1c02401702c2e03039600104d4004000c20300b4802c6800b02140224080d107001e00103800041522a158000c05003070380c1150032a4000c902c0342c7c0c10241c48181d0140550303005030046160030400000d410000a01d000c1061080c8103100e4140ba02140700c070b0b4401d01c41103904107000760445610002c000d114110128046030280d580b2007060020903442c69402003242c4a42c3c1d00129544420300001520307c143e00411b030080e540c040e6031604100c18680c03600030103100f000407404009a0f00381d8010304544c00d564000b408078205542031426541100880c666409003150000c6007441d456840b0058180188106551254025428003038840c02c075107190000c030364282c890015185107400c458140241e40b42c0b041c48a213040b480d45400c4480f219900e81c003590560f01e140e4116104010180c462030007042041da4200301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 291673012 1250 291671762 291671803
    0x90c0411030709080d02031e1e19020d08040210020109050d05070605131211151501031b080105120a0206073e04021813020c19170705070305 62
    0x31403a0b0080f0800009120700c2d009800d4040f8940802034480c03041c001010302d025481449000c11850a109480841d824075280004540701421b030036043d030b00070600e03298041a4420310f4041e01880401c810807800c800341c4400c015038595500b0071050b200301c51408811596900000e1001c13a800b048090f428107401d45501e40c0d6004c0c14200b18041d20001040c8265402e2040300800000f008091415041c84492803d00e502c0b079404a007081c1041c101c007804803409541c10081c42070030a0001480310f00040c098134104007450701d440b041d6299103180600c060204029400400ca681400811840780d2a40102030360040c0c00180e000402d584c0000d0402e0341c0152007a00d040d03000100303008104410071801c644440c03101d19600002544010300c44180d9005507008944114520040300d0840c200703103402070007000062012481c8000035005441e40e03000302d20443d055494114004c8c0f20002105420114801c80740d04180565505540036a600b02c03428491440c00002082040c04038160604c00c0003034108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 291674262 1250 291673012 291673021
    0xa0b040303050a0c0c0809040504030203130f090606022a01030e01020309010207060c020601081b04180f26160314070308040c0f140114040f0303020601051f17090c041103 75
    0xd041302c080801260601c20010310a501141155041d00c0c2400030403100400c1d00c2d501ca01c0d08a040d801840252003c0741018900410328100002da040c007615103081c002c11410781d8410341240d5400c40ca2454210018605101c1c4584000390240c903c507144040c1000701e902026070b41c1c0707142242c0c0704852800c0165030200d145801c100c074900400ba007031041d6100030140355042001c0151a0380d43c1e41030360801030150f45014503603521180c01c00c14210302095208038441d01c041c20300081ca001e4040e4100c42047d611400040060a11340708201c00c4018070723048074145502410740a0040d040c1440c1030b0213010020310502002c5000070018008580300b550303540c085040501c4c213458089056044200c80c481c1c181418040c0264201c2c0a01c02114240b03032451200030035030481e60240c0300f1f07a00241d166601d03400000c000d06800240d40742c1204c0c0240c904080303044003a05100034076541c2c00030b0711001400d003143c02c1c1c107540c5240c40c032035030400c480005903650303030b51114000380803220421400d00c0b40d13010100811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 291675512 1250 291674262 291674281
    0x706080a0f0e06070305040609080f0721020c0f03070b07051605060a1e0c12030e0708070509040b15030604060b010e030f120c0109150b100e010203030403110a0b04030305 75
    0x60750008010620086580d07000458407124010701c3c500805607030b00c00090901245401000800ba0443d8000e035079200c40780710400144d400010140d03460a007880c103515140d1151014140d10080a90150103043d00c1c44e01002825116240002c0c1d2600c00c0510214050307904c01c00510009205600418002c01110400c1c4014101e0754003031442948180005030481340c0081990300880112014041910f15400040e202c200004101034800aa03000c03e071402a40c2540c429001090140b044902c441e6544401707591b43c0e01c0c2c9005490708401c1e4480450001401407603c65045510092000c1e1150346201c0401e140040031507085e50348035240c0580b5140b558011080503c54141603000e049114054140c82d56912840e1071340390040c800015128000713403c04e50042d1078483e40000394030454001c0701716900c00b070045110090310400000640c0e18031b050040f45100f17040c0d141a0051360840d030b5603031416111001c0190540c07050340246401c400010b0140e80040d481948241c8000640c2c0c02d04a2a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 291676762 1250 291675512 291675521
    0x5090a0903260c030910050705130f030f060209060705010c0903020f091003140f01061d01060c0c060509120d09170706020a121e053a0f0e0706080a 65
    0x9500903500c0c02e40401c2800004840b00c103601024015070310f55a83c403811940c0d03107801400c2012620081c60801480811544080201100c0c602040d80d110407544550a104071142c451100600511017404440c0006581c1d4015020203031000f008142000425105d5900b91550000c0d40710001d001c40c44140300f14509080c0100180e007040d80c0100b05803612400702c0102c0300840c00050000d869160705518070b40010031041a031140c17210003c2c000c960350343c031150031105500c1d015030f20905d600c20000300b42d90384036007002c208180d0003c030380004a80c9400320580d11980f10801c0a50042c40da590b0304100310504008a102c00351281d40c84a0f10386141c070711102a000d840700a5440c00d41c1214404110040d80025901f4085401449418040c0c4120300141c1d9290109414510103440c54201583d54903008000340007020400d60036184a60007146024105260461421924802c3d03480d0503044c804140e401f0ba01442900d039000900b2003a40f1001500d0046594403c0001402034410404003500c103005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 291678012 1250 291676762 291676787
    0xc0206010b04080a0611040f090902030609010b01020307060e030702090c0a080901290f030a0f060c020601030c03150f06090b03120f0417011e0504031716050c0705090a0903 76
    0x2115030034030382401d2030f198440030345010141c8102c0c1c907000c08210114401040b103004164021b00071401640d51041400a45261802a40300b80181400980c0001d010b000380d007180c006c140c1c00b442c601801c1d40c0c1c0e1400102401c041071030aa00c0305028220058503000342060003611555469912480d02000003040720b10010210401641451802084520404e00458040c040885001030185540e000b180c11804a00c0040340d051003064091018020b2400083c80458020700e0240074a204603802640c0c2e49100388002815400d860030b0400210702c414114441d1052024008100c441c4203110f45400d54100c1d4028248c803954819820800389000c20149030f40b5a140042d0341c1c02d01d141c4002c141018051031003200b01c070050700c518060031400294451102c07106201802c0c0350a01344420380030000c01c012142280858108012841c400c03824407400c2e807103403004c035001040c100c40701e00c0c00301c1d556000b0b4940044940b10301080072440b07907248902144501200600000c80a5103410020500b040d41076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 291679262 1250 291678012 291678029
    0x17060f06092211121524191a180103020703030f06031b120b131b08070e060301050402030d050c030c010e0d031116021507081c0c03021809150306010303030c020601 72
    0x2d041031110600c1c0074419440580d0070b51102c1d013842d500746c03007050001c00468090b5100314113a0690104810443e101d6003039414000301a600d006030342c0034075010340c4640340760300490300c248501c41415580329030000c0c40040d21070300d0007045070202c42c40030340f065403016007045640c00004180c03c405940e46240f05002040c003030381504886142d0344ca410340040300142640358440b203845d181c602400850721207030640000e139140c50300380726580da6070058907941c2a024001004031204041185860305015450159800402074540308200c0001502d05610441884140740030520102c01011070a1042c1c00d0240700300d0014110a0110001c0101168480354590342d001c1c00501c09004412181103010040e83d6054801e01c0c210801c41311085124012040c000b840c80f10f00049001054516041c3e9130050303e0340c4c030804d000640301d181d4246c1c26402006804c02d8221089242e01c011481c1c0307282c1c2d8a402031483d494691501d610000401d00f004000d070070a60220341c880d481c1007a50355040041c0350051a80300c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 291680512 1250 291679262 291679273
    0x203060a110409050405070e01080d08070c020f090619030620041208130e13020a0501031e051b160b0a200d0f0204090617060f0609221112 61
    0xe4100c07214034090b9004102e0720a640d5000202005001c00c596400b52180e401200d40f0780d03035200101030366503c40d180c03807100040480d00444d0006010303052504000758028111040c0d203100c4020b0003400b0a0003450303641e010142d2200c11031707018000400e00e400766002d03141c003040a440001201c490101030716070003115030008210400c98500210324045030590320810095a030807100d03440d0040400d298102e40c1d05044010188180106203420004e0944d10036106441819650340054040f039694000805841410b4500407013940d503a0707030142d980018001400300d181d0740750010340200383d00b2441c24000200002001a410b1000c0740785c959501100300e010030300c420012008a81181c1a40301c4000e0034085002c07981c24480301054020144102e845a030840d22250b45102200203060b8912503440321a8030740148031146600440c05511903c0c0c203071640c1650f52036180500608080041c9503d00c00c42c40f420013170f002e2001d22441000707000d001b03030450200480301c04200314403002c00c5010400c544c4c3c2f01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 291681762 1250 291680512 291680531
    0x420c0307110a0e0c03040614010f0e0a0e0714011103030a0b241243050c0309280303090918110108090111070c06090503030a170a1107050a0203060a 65
    0x1c10f10029031202030003140a031280c4481c540a03020f003c0502e545000c110a410000c0782c0030840682e080f0840d40103048000030780d120700070740400321007001e502000b01c1c0e0130100091244000b04540c007298403906142203582c07040f07004616030441d00181e0310840c815841d00b030032514914001846101200c1141403403c114800740042c001c19100321183c1c191428020400134200302051200445046140031094109130351805005503013031441c00001403003030402d080108403a48140107861040049000a41c6401689030400c9000c605030000f13111071602e501c0d000004000f061046100446c42030715981412400d00c4e1010040c0c50b0700e412800c214082d45550200881d1040300c00b508849401c0c246201c007a03c9014500e405024401100d003101200001c070f00007005034144150049500f940d84856a842d00c5604050b140c0c410010078800040c88800c00da042c2d50010b80880e03030440c003408030005403040d403204c0450180c0c1060303c00303440982100da81030302075090501001d03501a80703034107080000008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 291683012 1250 291681762 291681779
    0x20706081f080a0b0402030111040302010e090402240403110d05030d0e07080f030711040501080303180c09041101110c0d0f06140f01060e420c0307110a 67
    0x203004040e034100c088000c600381e001140109040000d0103044090300c00300c1d1098140391a200074182d500700e0082d031810609800c041061070650b010340342d0580d80c44800c0046441004400309028000746e9010310400c803d030004d41c15480144044000311040c7c25212465070401c20612405214064003038021146e00c080040c10110494192401c45040003030564085143c02e45812140d80005440744210a82c091261000102901c40c0cd4031030902046044401e8080c4816250203102c1c14203a83d000b4400700d0008100c1800104585106004039410720080300006140f200d8159070581d11600c0c5000d4011441d6880291406040301000080600000050200b8080091810041d0004080100e402d0030011140c000b841c0c4c40d07880c2e12112402d4100385010ba00204000c0c4280404207030403402c41d03000e600301000141c980140d0b981d151107003e0a00b2541c803507081000800d10b0300d41c281d4900c00702d610301d2540f030142c8203008451004646811151405040d05040c03103100504c250700d08581008180d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 291684262 1250 291683012 291683027
    0x100903080a0507030b030313050a080a050c100c02090106171e130503070204021201050a1d0a0e24070f08191e0519060905060d020108060d02060d0507020607020706 72
    0x70110720001500d039501d10080300100341c0f96444550500000541d0b2001003205e00b90101034483c115800b0f0507042c0d0350359815682d03100b41c000050a43d0810b4542c6951450540c1d80400c0e000310a06088444e01c8482d070000b030990300241c204034003007903030441040e5585262a822503448000d070039810408002404400006800040940401100d1504010108101401503e24650f4003070015903e4400c1d601032100032940c00d0040c903004840046000560804030540586071081c603160320142c1da04c400100f00007a2102501564440c4218100e4035028150300b201c000322807081d0300000407503061110b001001c0071901c00c541c20405c10345100f80701007168000c945c1c00c5840c1c03066500003000c0c4401c40c44131007100745d035505c0307601e071246010100301c0210f140855181800290741000c01007180c407000814115a0140c0350b003504451070501d000015400f40b030305030f6080800100281280382059000460642c8401880c81c0e541e5250342c1400011501004040d4200b0002d001500219007488030082501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 291685512 1250 291684262 291684271
    0x6070e030d020c1309050609060114010206010b070b06040204050d050d0201150807120501060e07030608011112040f0c05030307060b04140106021b0103061d04020306010b090d030e0612010f0810090308 88
    0x641d0042144d0040c11007030f44c0104803166100c0113035402d515140d075429441d044240f0a0001d00b5900b400445509e40c40172444034103881a1402441c10a10541ca5074007030355100404154000307030b003000041a16a43c0e00b2813119114410b0b001401d8000c65420020309483c02c100e044058200c00ca2030034043c145000c900750701a19405010300d0700041040c10042d01501e071642c004807001da102c030b06100340c00307034160852410740c4c0001c00240482c1c00410300300c0c000c0388140f0000a400c00007200c0401c0c00902010458440b00340170b901c01c1820700d621a4002811944140d008440709903640d46201034606060181032011000e8a203691b102c0c1d0714086010751a1000f031040a85c242030007141030103060303010f544240e014010284640c90766102c2800081c1c07009405850981c443d100ba580006035000302d10f02140d61084020b030520031024039a9605664995056507a01c0e41301505201005440e903486201d01c1c000c003c06683c1880103894860142e040503920000c0c01c0560381010000400300f81c104e54000d400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 291686762 1250 291685512 291685519
    0xb0f0105160515091501080312010b16020a0b0d0b030106211b0306021b1204090c020a0f05070e07021506011103130e01060f020106080a06090213060806070e030d020c 73
    0x1c52441c1c50440c0c2444000400400c440107034500f840003c81d0001139040c0800181d600003255a44c0320346000f5581d009503034182c4184418000184480301001020304042e404449446900100c10750014512900c103030840240004040380c00d22800c00203001c1e0300d9041d0070030b41c02000795905000039007000d049101440f4070440f00c1c1c4a503550030028010b01403101c40c66016034107800c040e01da1404d8800f95020030260240d00c883c0d030780c800903421030214000b20301035025048a441e040c41e00b5400005810410341030025401201000000301311040700e01726000b072048002e40991410032605040c1c0b000c02421100c119846018031241c0c500440c84007a405c80424240318030341c061440205480c40c85105004008030552000000342249480c1d95141610019250035030060340400c1c0c2242222510311500707489501c10104500800c0403540304402c51750000d4008024543c020f000a8103031125a80050002c0c1d10550400c5a041e80c0f05401048141c07080340680342d42240c9500082d603900708402028803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 291688012 1250 291686762 291686797
    0x180f0201051c050703090b06040c1e0e0d080904061e030602090f040e01050405011d2802060403050d02010c1d0907050d0f0e0601060c0b0c030a14190b0f0105 69
    0xc5800b1036001054031030150000388880e1402d640e0040c0034004c1e50f00c0172188429407901051061500d4041c01d5070b0611503070380e0040224034030400301c400d5200180c480302c10721803400c02401642c0c480b825070f01c0c0c2082c0143e40c450b5440c3c02207030a00046505961041c03190180f01240030a64503030401c41e070021240c20010250302c4581400020350066400084207901c5881c1000070140a00103411081c8580d0003600208060141c007265403100c0d468480c0380b2540740d0004040601492213000f1014140d20010032011003244290740414030903801a001600c05a00070000c045d0340c3ea6090040c0d0312900214038200001000c2c01549420703044040030601c0c4140000d100060034507100f1000c1c1c81c3c01c0b02c0d4641d018400184400140001840d080800c0f45040c0101e1001050890090b090042c04992002102e05c180ea264510407500d03400240249481c1034840541c4000d0225a0400b6070260129030310b0ba0903c0401c140e00c82d411079a00c848011701070a40c00d0760020340c1340e030050151841685c40340702c0e404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 291689262 1250 291688012 291688027
    0x105040603200a0c0501050f07020312090f120c010c09140d0201020c0406170111030907031e15050924071214070c0b10030f020d02030f0709050604180f020105 70
    0x350504241d001040720100701141c620f203000e9010b0042200c5900a10082040707440c0e00c43c003503510000072502840036070300400008905a05c110303406903001146405403207110003076691460602d05a6491500d040102013030403040a68280710b071550030221070910000180c44c00c0c2c0d030104881c01c00c42405220707000c0c8a18050540e4001e02c6208001c0c1002002000000d44600c4850001c01035440c42c03585562810f514a200008240e045902950041c0028401945544c0e510706c00110051010b03c120482048000002002ea0340960f21000000700003142618024007294541030f0000000300782d41030740c0007581c241c014851030550342001c900d01d40f11030a500691101310191440b1104440100c10541c100301c80d407940100c00201c032510802c48551240c68400c40c00381c1b071007014000a8038019105140d01e0040c589041d0015240d031029056038181c443c2e4100d903a0506009038080c04690b52540d04020152400b8800c400580703424200b01c90070540c880d11140c101e4400700c0f8000341030160015041c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 291690512 1250 291689262 291689291
    0xe01030f020c010501090608100b130e031c02030610080601080c180a120605060607050309040c030b03030a0804030207080a030e04150b2b020c030a0c0201030204080a05031c0b0105040603 82
    0xb110301d80c4010000303001c0355a542c82801e0040c9035a21a043c0103008156243c1c40300702c40b0f4098041e113940014541c00c40560303110301c010b004001c040250300e8584801c000118501c02a004030b0046920b09000041e12841c00c03030140180b002c5001c1001c000c0100090800400d6038004001303a41045446d900aa2500c25003070070a81002040e0b02c0303403680f064940f4000900c141820440c0358129201e42000c2c0026202c003002c0c46403034000d07101c008010340c009001c0c4550b85d050a51103011080c5003840c0202d43c804003000403d0641d40252000800941c040d0104014560100a064003c0c24818018100034440b0740300103001201c413900710b0384515114070281d0748050000103101c01801100c03032200d5031400030490141c0424500580c4200c10401c104100300460114802c0d00d04180074040074500d001f00140c000c6841440c010422414035609210105400900b04802c3c0b08140c8100001c1d55138604000c4a4040c42401200081d80141820f40301c44031360740d1000c1600d04841c06070030302040007100381550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 291691762 1250 291690512 291690517
    0x910050402061b1e03071b0609060c0305090901150305160f140f1218010204030b010b0a111207110301091115070b0c03070e0102010902090106110709020301030b090d09060e01030f02 80
    0x12001980c102c504c00c501c001e0004030081c00958800d91118011400000d90211140602c0c421000403800140c020800d845c026645281900d00c40d11f4101d217828011400210307900301c00c4c1c01140700050822a811040b41d0548180f03500000c0d005400300c880241000014182d031410f407405010801c82c01a1039400360740080c142c0e4035800c9034040190300e0b0030340e0f004641d900361000c460411110b002800c9044885406100b141c0940b9040400000c960382440401050355200e40300349020030000c0302e2003102c1c0300340038419803181034050312031980d03a07105509043c81807000c04e20410b817082e4500400b41000900d61803042c1805207003603c401d02c181c1c041e500c02c185a0f009440c009002035040000300220010468000c5204034842d03180e1202080140340124200c41c100500207400c01c0c0024010301c5054000c03594807802003c1e1904640300503803a00101c02c26a0400c1c2d1003119141100780c20301c4075484003132003120a80089840c10b012400c0c83c01400914402840c03104505040c2d407958101a260142d804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 291693012 1250 291691762 291691783
    0x2070f02040207081e040f090b01050c010c0522050315040f1202010903270608100902040b0d050f0c070b0606071208071103121902070f0b0910050402061b 68
    0x46403266907a09110085511400c0c42205100364500400a8107918a0555080d580b4031f80607041d070315080085420082241000143c1800014803558100100034003401c400707581c265541c2900c82c411450314800c0041110030810b800502400c080c090764070006000c02c0c0c051503080c162201600e0382d040c2060701c00300442d0301820501402d80101d002070380541020136014400d0b40c82da55411100c80c0b582ca00c419041c10017503001503202d00304000541c495420140c200542802e64640c0d190b0780c3c0c58810403680640d00c1043c6082001c90011110001c6100742075000c03002254030301d050300d4590000601403003002002000805084080b681c02c3d216071044d0303400d17194440c0100c8141680c0400c0901880012243d13000000e0b0b900040b0840314030040181c130000107510004000c0d07601c80310302242c10f14110125a01da0305500340000001300310f030306004038407180c002e4240314061300300040c086040c502c942881d54041d908100510005860784811240103031048440d04a17960000c41e0643e00380380c149203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 291694262 1250 291693012 291693019
    0xc010c0215130e04020f01030e0a020904140d031e090b070507060b06041404050a1a0105030a270c090510050f040905030c010b03010e06010302180903040b07030903060e0105010308030a02070f02 85
    0x1000401c3c00440341c040c00d03000700d008540a0100d460000300440079954080700e18156038000d0f5291000500708006460340240c880e0315101c0c0884501c441c818504540070000304006074850000e0440c1401502e405074000203001c80a11000c00b01d40c0701d42c1d008000c0a002c9004001002603841e0521109a0000160140040406aa03259580c42c0401000829100c8a101d18a42004615042e0241c82a0507512100064100f080b0305824015102c0303810091114041681359403511030a43e008038040e001118091020000070300c5141020741c202c441582241041b5827901091001062603018800203da800311108045a40100c0204010f011421070003007440c80045201c3c5a450410b401040c44440309800030014001c1d003d0041d6512442031201039004880d0200d5881e5290381803003459400ba101e501242c1c901a641c002038140c0c1c0d4461101a00051800c200500800106015043c4d0070110302000340500c0d415a22003072100d100242198400c29400201102085032102c049000ca54005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 291695512 1250 291694262 291694297
    0x70c140309030a030302030a0c08060f0103020f090607060c1709062206060f1a07121b141606050310050609010e03011d0610060c08160f1a01080c010c0215 68
    0x9290107401b0f50400d0b544099001d081c0203811220340d10070440c140c418440141440b504140b0074005400a46c0000740000e10f2000421680300c403034a51000509142c0d108407000100c018440400a05000d041c4040000e48075200050103440c0400203039254000f08900000c0461850780d2406900c41074000030028101410401c0014080c02070324952000ca58290600360010701c5900d058004074811000000e011030b000724903100c03400e482401c0d0304282c1160042c0c2040c0500594468024a8100c400411042c0e0b000c1001101c03900c1b4207041000052195040041c2103040c030030290703088020f042c05084c0c0210408a00380030280c1c8209151145100d0180c001c20269a8030607445611840481c400c0101784a81c40100b040399215041c4c07402115030380e9503000081c1c039003682c8103032440e413040b40d1035103640c500420b81c1408285841c5004905920550b5071014030300c000c101c018031070344050f030082c6125041101401010f980100050403c04e604941c0300f009050840034070b0320300d402662a030901850b102c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 291696762 1250 291695512 291695533
    0x52205040c081204050d1e051002190309110f0621090d020304180506040603081210061107090e0f0a03210c1205060f090a060303090806070c14030903 66
    0x340785408003519003003000d48410882110100700c040c41148a843e4100801400d84c10116030300780180311505202c12155100d101680e00c4051801c50304006140d030003540002c1e09400345404039948000a440c80c10103000b03084030341d01e92504841c0720f1850035000300810030392000c03940d0320302c01240c1d603d45900d01102c25901c00e0768030701c0c1000311b0216018500c0c0e1140b0009120300500001c01e0b54220b4101314203460085807400380c4d14001d80005840350b03801980305d4002000048a61001e0042501100410b0303070b1500c0c0c43d0596005c80c1c11541d0122080c00013072144200d40d028081a44d00070b9400082c4081a01d4000040c0b2601c0c200151060174414000c0f00c02540425902421264640d92900303a002c2000990031503160480d1551400d00f03001c10b2420034042e021503001d410070341c1d000f40020300c80b0040d40300c500085001c604003250501e01d440d9a030788052003055007000c502c2c800f5192110044c40346250030680544502038009014044000a0b8001498010100116003482c0300c00350a80d0b00507030b00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 291698012 1250 291696762 291696773
    0xf010513090b0a0c11070b0405011103040b0f03070e09070f050c07030b04080310090e1b0d170c010f1b0809240f06090403020c1017090d0f0804050705220504 69
    0xc441300204001910041d412a00c3d810004e01c03074064600c0041b080340307014a04001541d556a1115120405010902001482c034808c8805000601c0441c441c0c1656842c29400080c041c50031b01c4002ca200d80c800c00d05100078281c3c0104000101c070014100341d41d4995484050614201265000a25403022002044100256040030b14000d1a408070900d91003512031100c00300b43c800c0a010013040e03a0084810b0381c00c62001442c18502428040d2039902e00840ca500d0701030b03c60440461680302d1000010300d018040c0070034882d1600071314041d0340400c65440d12200c9102080b41c8a121f00003000388031008224510380a0200520b61158240f500208012010241140a0b0100c4600400c0800940040c99600309443c40700d20695141e1b000d0b182c1d9245400c100080030a406110600700031550742d00b0000360543c08942c40c0590381c420010041f09a203001c0040100c0110103940c402c1200d038800b8400000e01c00944a0186d450803666901c40c400c1855a150b14617801040341d10b0341a042a050100703005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 291699262 1250 291698012 291698021
    0x30b0c09090a09020319240e1603120504081f0212090609160e0402040c03020c070b070b01080c09010902090d06090f05010b0102030a02030d0e030d06031a0a050f010513090b0a 77
    0x604c00d40549480d43d01c408001a8800c89828014003481103058028080300d1010000e01d0b410709400740c0005240380510750640c582580c1c80d00c81b040c2d040411005005212071032044070751603031003450700c0385c500b03402d007032615449840b002c1070712500c032a00803000d824000c1c00ba019101c0e04200c0708014043c9160500c20181d0705d100642d62a0200d001da41d2016000103240015607060f03030040440083c454035158240002401d107000d12a082503424080c10404240134040d041c010138002ca903007a1159401d08140c0b8003080181d100100030f5000b1400340b00d00b522040c46680c1140c0e901f100060b2901080c102107102c840390900024411440d000c000307c108100070701c52026681c0208002c0082d200c0700c070700580e681e02c50307031120303030090ba105010b10241d40c403442d0031510b80381c0404020b507070802400e4004007041d14140c1d041150078400300802000d82e100c0d91013060f030380100301040501080c00c0c01b54081c5408030060286034040c080a800e2054400d155410031500c2d6907120107401031518082a0100081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 291700512 1250 291699262 291699281
    0x11060304121b0c0605031905010803040302090a0b150a090b4b0c0f07090c110d090603090218040803011701050402062d0304050705091e01030b0c09090a 67
    0x119281e908400e005605126401c2d160b6222000c50300c15414820140c13125003000305030381500d201302d081d035030f0044529000f014000c00e4034030025900c0701d0445c410007200010091070050001d2a2840d41e905668680c00030340c9030b098032583c540f55210451107040300d4040954000442d00303c00000e582e0a00031140040342c9101c8100200704440301d070100c03100741c23405418102d12510300d07a03050088144050440000c200b80d50340c0d002241d880c9101c0c501154100741d00760303210300812a543c00d00c1c00340c056003051348030101c0f211560243c0003400c6d01a41c00b400130b008600070031040503a03403141f03403045440e402002954040848628019403a25162a100c142c1c000d0046444c2d006048134542c0ba0940140039060103954010410707401d00d0209002c00700421000d03125100701c01d220040d400e0303150018400841c092800340015108480c2414188401c52001400021180b024410a810012101d1140c54156984180604903a803201580034180f4042c919007982e009a4803070500850002c1507000d0f00d9503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 291701762 1250 291700512 291700517
    0xf0f03020117160503060f090c0d0b030d05040308030c46050f09180f01090c090501051e0904020a03050a05130b0408071b0603050402030c03030f0909041106030412 72
    0x500801074102c2c241440b090315690409205925034086460007800a1a440350001d030850a00d203080d180060001c03502510f017020365160000d131401c0618000c1c02544031004086d00142407480180900030b01c1c030310a520010300b005601002040a941460044441da010540342501c50201050318031040c915030282c0140304184982c0700c81890395141d03901d080d604002a210a818411410542241580140c500e00d40c0104e03040b003029401508030058034000c810305628600d40f9810446030700d0440b4201c0d00f10310188441c0c07040401403680d21a04890000b220131081803840303d030350150385d00790b0300845408035441400810039070441c0b64181d1110b40320702d5100500344141e841c0c440208170241d82d640400740100007500001404034450782c0062900b0380c40b42c80312081c200c00402c40c850080c1c0d0960450b800003a00c803002e000643c5000c00102c003110004401451402540544605041c421144005d0003000402e0008007030020a0701040721240c80908030b50307501d2909103040c01000c000f50b02a2001b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 291703012 1250 291701762 291701777
    0x210090813090608100f181a28090f05190b01050a0521070504021804050906070f030b010c021305010501090909030c060504060912021c0c0b0c07020303040f0f030201 73
    0x5180307409005074000c0b60060800740c810364800c0f9031080060142c030340b00b1802d0540c03036025504000c05510403411b03603a4040d521071041d11420238a804d00d15040603202c4245886003074202d80301d000e2440102c440b540341003940001c000c1050302d8110207954010201800c01e008039282548d41004a451343c29410744540c0e9808140e030b0707e4030100283c03580345000342c41d0000312122041c0741e50717540740c2c0000035000e00310403c07038018543e5000001d050380e00840914103d1800c3e41c072140002c1c180340c0a1190001c2d5040c0c0640744924001d000140302038080703040e07041010b444900c0c03400141d000d82110304000750080c10b220702c0035880080c0c040143c03200b80300f842c6c0022071a120002d07201c2c00301d106008800340e2541d05c1e0301000f1065103440c009800c0240058908945da510400c00140c01065118030340c0c4016006050840a100d00602d070542c0000801404e00040042a80001e1111440c4550080e004004036803240d046001091450091b078100c800c00750628400420032050640c1d480702242e01c02daa4164 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 291704262 1250 291703012 291703019
    0x605090108060103080304140f0102091003020717030a020909130c080718050709081506130b0f2106010602070e180303060f010e0d0b0109110c0d050702010210090813 73
    0x44804024812145690000b00041c000680d00f10011500300d801035014070040b103210504e0600385040e880b200300c5980c0d4002034103441400d10899101c80605141021810181c0a4071a08030041c4510805610242c0c0000051600402981070300c01d90700010f4841c3d400b501e44650613060461110f80107460440e94540e000070062130000704030042c0c1c0c16008281045c074491426480c0607050241c018000d10541040c003041400301046104442101403240d44501d050610920802d2003854042102980c10021040c0b40d0780c403015042203050400381c2d580510410284c01022100c10700842400b0b00b070041c8000001e50660000d46901a191000759180c81500d9880305c56041519900e910703005a0018070001c2c03990b2501e11142220003206040158030700426030b00007560a001c1306800c4400408617030051042c251544030342d24003400500c041e2450045080881c554030442998101c04000b0001a5103046900c24004407114140c2d01b0300602c2009141c6c54150032070380005007a000e44c1c1d03a8000000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 291705512 1250 291704262 291704269
    0x5011d031f0f11070503121e07030906110f090909030d0510031202010212010e07020703060204061116050303070b040f020607080405040b040c0e0d020102120a080702070605030906012c0405100605 86
    0x84130410340c030100461425010f0703a4849084000140b403284119001c029100540c01e04079442031003130b2451395000403105954648002100d201c090320000d1084140a20b031791804001044680e02e074422240c41583d41e40310321071140f03507110300680f040410382081c041c0001c1d002000360140030303030348a80700000440b000b540080b0300300d00400c1294001c045510004024201c240c100280e00541648140c55203651603484003816039006600a02c0000c4e40d105465881c110140503020b02c2030440a24180210301c2c000001e17a0704d000d0001c0c054207c0848201140030082c0e1070f080400000d6018010075120500b6081c10f501a40061080c940036505002c50030f41280b50034424a54001040d44621800401442c10311912140c1480d04905610031140c18a050140e4000607040034201d96581ca0854034111100a00307000c61588003c080c07207010f00c140200d0b0348021443c41d05581c43c004001000a01c2d29040103820303078507841006070178035085040c40b06000003c1000c03414006d503410103101c3c0b0356840091 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 291706762 1250 291705512 291705517
    0x80408030a09050a0609030f11150109022203060c030609020309070303030b040e060126032b110c0c090108160302040b060717031f05011d031f0f11 65
    0x149051010000100c0441c495807010a600d07000724212003400c1d0f120742e11101180c1182074147e002c11015100d1140040e4002c912400e400c6144001d00201c00c009141d040c2c41d60410b025040059401140480c5150000e901e8410910ba09180c605070850342d0341041001008240f5031100083c1c101f44021403081c01a000701c030302400b0000c00800c1c8840ca9510114000c160500c119603005031180c07261642c90b0303400c01006002e851030302050104684c3c001044460100000c0070a41190424081380311041d00c1d0560345070040011901c411040d030440040c030401042304510b00d8414010104000e104028002802050700c0d9058510b01902c0e40c81e036115641d9525000405c0c81003c1486900b880141060b82200c10022006030032907042615680e140399041060300001024500040100070084d01c032080714003a44070300c4203081807959003403900083c040864161b80301d02c40c466540755200c00d07403020040c000d0151004950100740074000880c06c40945480e00ca0030420f01e041a0040000b1036801c0c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 291708012 1250 291706762 291706771
    0x60d0b010e0a0b0a090f150e13090615080d050d0510050904060203060f1509040f0b030f0a031416030e010908120d14090307031b1a0f1602070501140d0e150708 70
    0x441c00074000a0001200c07900c8c0301c40041d03600021505900960019540035004a05200d0040405c082c80381604500e041100da50103492654018801540c1031358104044902d00b610b0000041101d40d02d401740c44160f100194001c94000481100700720500c42c0700d502450090000f01c40ca07400242050040081080c02c00240f03050b5180c00b008a021503140592144946019010021a4041d4181c0000c3d08244000d1000702c4140c02c40681c1c0020140c1c00100e9485580d054071005082550320007042c4000320311a00000c0c203120b8802d111040580c0100680f000401091003140e5040c0c01da084101c3d4190412049025210b0a06650140741400820300ca0b1040d14140011820410540c8003120b602a1895090345600302e0940240089061107400004902440d10554540d0500001001c400100100640702862003180c0c42c04441d0350101c2c0c0728040340ca0034078220300384800f5004183d4142c4034195400c41d443c1c3c03810b0103820400701d022805001d02c2d403101505404035a83c045041d5080c0e0800c0701e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 291709262 1250 291708012 291708029
    0x10b030a02010f050a1101021b060a060f03030e130608071508040b060f210106060e100804060c0219210807050d092a1e05060d0b010e0a0b0a090f 64
    0x3c80300043e9440b4130083e0079810002c1c64003010fa5049401c419007203a1000f03031600140e4121540e6001e0400c820010190000c0441c0000c0180c103160000e1807a80c1c0010f400010201300c01403500040f0755540c40b40c007a040610843c020045a96500c001a0b540d0040d031060b80000c01030104064407490180074054440d0ba00040040f046546007800c0180104015000c0b50303002100d42d581a40d07580400801021a001c0c01000240d12420b050000c1c240d15070001825110781e5940114000c1c05611180442c0c2165118501052000d4902e205074280050142011010300a07010f5480c03d001c012100e21016100480c3c921403203500c004022140c0c01e038110340d1200455010031040c0f410034454ad1180c1d510302c2c01081241ca0404000b042103816040d03114a501c00340e8200d4009001c02c038895058a40e0300702143c06415220b51400300419110b0182c902403c169947e5103194005076405107840f90230040d00240140134061312680546000c1e00605d46450001c6c0440601090204020941106941884 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 291710512 1250 291709262 291709277
    0x60509030705040e031b011a06090d121b230610060503040f080c0607020d2606040204270c0c030c0609060b040e010905010b060a080105090408210603010b030a0201 72
    0x100380000361841c084e8240a52204003e03506180014900001002c030003040045010b188044426074010400c010440c0f0610f4204844140741e80e40039222000c0e02e41c81070070450404102001518502d80b10201036401245241480042100c011201c4081440c0c810700160540001052581e42e010304035910021654000414060a03000e10b028562007485541040880d20b800e558054140c0c100d801002c00c070741e00180911150540600200c40745030b4880c90b103070312564001d03400c51003c00c0007105542a001c03962400304225403503580440d0b01134052140c2c0240000b58204c0000c1a941e0307100c441d4900540340402c504100e034499107454007500c2d056a968240d6212607110480140580001182c45607510310401e1b404c2d44031802102418014000001017003000c900700380782510341d03021820348208820030143c100c1c5a0000502070641c0c4003900c8403440c80c1d03190300d0292002c2c424000031081c542c0c0154060746a0b000300300300c05445540240c0c000d02c0341402c0c1c14145070f601e214032003000740070400700b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 291711762 1250 291710512 291710519
    0x2505070b070f0203030a03050f0f04122105131403030402130c050c0a030503070f09050901060507050f03030c091e03120c011d030a0806031216020f18010f0605090307 73
    0x16005003008070b024840d090031564640c0d000a00c1d40d8080c0c41105c01094503101000804100c80075550307400121000f200c01c0502c0c00f0754402c80542c2c0490601c00a004500754141d91010000340c0140740e803101c0440400640c100503481c20719031141910b00301ca10035003115030006001d40100940340220380c0502065946912000030030090070b0701c0c107260802c01105104c50714130301804005440b0724902a0b00c5a40d5a0b08195000400d44003024400c2014450200e034108901c4e10f6010003541120f0241c6070a0b51034401c1c914141c1e0030310003010f20010407840b000c0203001c0184035080081400c0d01d400c48012644d135140684014104049511740ea916404c0b0201029101d62200000e18410501e280009a507000d4200728803c00307038007003c0c2216154004100b00100319009424150803110840040608200b000511200c41c801c80d07600c1c070740041c1d500c85440119141d519901c3d0032050000d221090590a442542c60038003c248101c00c080440c12000080e50381c0140c0403500e241c2000740140100d00d09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 291713012 1250 291711762 291711779
    0x90518100203070509060a0c140c09010512010e03040b180405010605091e15031608040b070309230a0201020c060a0c080c120703091d01050907030f0603020312250507 73
    0x8010001c0b0f040c0103040100032000d41d5003100804880c805921001030f65035041c01e101517024100c00c1d180e041176100c0d1548100d29951081c0b400d0459400b25020750001d81d05283e114003418402540c0c0301c0900c400708001c03e6580202c806000840920611680c10b91415020403050760000e20a040204008100308451402c1c017003c801d001007d69201850a90003c0011a40c0c4400340e0303441071042403001c801c0c8038074600345481d100f0358001245051461800c2c0380d2144070366842c0c041c00003014599941c4a2a0400004202c0c00096801c9184020740101440006030748401d16400102d006000304507403d941483c0c4141076400c5201c1d00c2c2d40301104101d07a40d40f260110b6001c0d441240c240d01c10860b200f10100300850041603074510903587d000300d06140040c1b030703010783d0001e90402200303083c80f01c018012a26403640d04da43c0403466203004100c402003050004000c14903078001030b416010380c03140d8000704541c10005003621102d40181c01403880b04050103c401030007031a8024542c0d04a82000c04c114072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 291714262 1250 291713012 291713017
    0x1f060b0d0902010e060a050a08010e012114120306040c08010b0a0f02010e010f0e060702060f040f1b0303021b0103020c0a02011115040c0e070c0c0905150406030c0905181002 76
    0x240b0606180801400d40000034199030400c064480000e03030001820040c8a500c41285801480008010b0000d0b504000e888541c1d0308002c010741400400c41300b468010700c188c0c00d0f1070100d409407000907030701c039510031482d01d80040c1e0080b03580500407030a2003800b01c8201c0c404c080040c1211519040d40341803800307088003161002480b59001d000c41d0340b10446030448843c00c0c4101030441c0084140001c0e42030360641c1c21410080b0080403c4190341050f420032000f03810941b041503119038000403104040c0103914020642002c03054901e0030130b40c984000801010f80004414200000450b003101040a03401c0045050b4401d003040014250007002c201c40055000da60422008041c00003038480d802c60307401200701d10103c1154151180d9109001c20842e00b100c2c1c5a4158004a140c50803d140e140d9503142c0d207101400301d104410b1020703a43c00c00a2071103141500c042180b2907000308240186940d0b070030120565003040c021400c04a00c1d00c0042030050061200b0940d00040c6080500035040b081200e080094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 291715512 1250 291714262 291714281
    0xf180115050f04140301060522020708190807021c140307031404110406052b020a120503070c05030c01090603050a090215070309050f1804110d051f060b0d 68
    0x7040c00c0c024030312081c0c5100d028201030491002002d50030000d410801d4203407521980805c1c0189a0f01821401d04040314520884001000001603541d450740d1902508911400c200f51410008000007404102d41c007261660289506608650160300070b6100214105240348512010500d514403070300f0400e005601850740094541000a1a4800d07060344060070b4400711012034000210301201d207880c0ca024400c6034045c110650700c1d01d5039407d000014a081c40c1103112000c40b1454510382410856960f0071240029146030a0825a09030041c0b919543d29040001c00301e4401074050030200c0d00d070500055640300d10b50169079144109180c6841030300107101c041c058250050310340b030703e210158907100701d03400d00c40b031a0040c0c29690320900d00340109004c0d0700da00b05030301c00c40f0712800c10240d0b82e40d10060f1000ba011203c03280b407440c0c1ca03a4540010f2800840116a401410b80c42d1481c00740403000c250200c01c0380501c19030500910780c50340c140c001c442d80c0d406580c50b40d44041c8516440001590301c07040c0b2a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 291716762 1250 291715512 291715517
    0x606042306041221020624121f0f0203150603040c0b0703050703031b05180105070c03050c09070305040c030b3d050315071b0b010602010b0f180115 65
    0x102522042a14008072090b2010b07a0041450241003004803050100480024645d202403c45801d00031090844c40003016008003032880ea54840d81d8082c0e50b40f40c0414900041801103a0384007440c100900c0224004d2990311070240d04d00041d9220f151101e008403031084002c80c00685c0c1180d202030800030541c1000e04291100c100000001c2041d0350020000c02c0441d002c0e480d029159602c0d0b213402010b03110402e00d154002c10b00104103080c02c541041c1560001405101c10118010682c00101c8590007034440250031145100c0380001840070104440c02c07203002c00ea032481025511400309406545091b10014591058801c0c1040440c000d020701319040031031015070f00c4240c84103500f20a0f441c01802c46211000c0e413080140e00e20142d40c0c0c00050b00500040d009002850608503d00001d10401880e20080c451040b100e83d544c4035800e840300700d11036403000c84000340e035840d640000c0c002c0c1441d0001da40100c3d045035181d481d0f03282003038090120740001ca82d400340d1603080a003a5440d0010b4007800609 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 291718012 1250 291716762 291716767
    0x6020106080309040510030b0a0b100c0c1a0c100c08070c0803061302040b1206042304080a030608030c0a051e10110c0708011b0f020d05160f0f06050606042306 70
    0x8c01e0b0030720290194094240100d403501307000007041410b500b4075403c01e091004000310000001c1c0c08503d45022511960500c0245402070603527207500f0301c00c4184420807401010109420312800303611072020380ca499920906e60380d03a08182034404e08494800500842014400120103141110700900508603000300035003030170b40d1000c0001c03650300112980049040007c0c10801a414a8811049044810407909000b64183ca6480540340c0c4003400140404800142d040c80e0580a900100d00400e003600840756507000440c819a120544000c0c122072034082c64488440000380588501e0b210f140402c0034220841c0c4884003c2c00904403a96101c2d41d013841808808107404082c401c5200600e00c610000c10f442d403a41b400b0007800780800449030309001041c419021a1a030010b00aa00c3d54941c1c01e1469139221841307140c0c08000c142000040000e0300e50300e000802c115000507040d6025101381e00500c040d03110300b820005180507074010041c050b001000c0c801c4d03900030340d140c0a0400c090060521071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 291719262 1250 291718012 291718019
    0xb06040b0301030f1506060e01080a15171002090604051c020a18060b16020108090a052a030d020309060f0909090c01020f07030c120311010c0e040606020106080309040510 75
    0x1581d08264820b032141c849041c01e10702401428001444070b0b035410783e0300f00101c2c0d041010140134030500044d5141000600b85c0000c20301080c1c0c0d408426643e440c0d21600108640c0d40142c0c00542100400c0b0505a006100032201281c11600030303200a40e0f0010143e0307042a084c4024000898003505142400c402521002e40240e03c8464a860151110000a09040607100c0100042e10441e5006130180704003003003240100d44001c9903820b13042e582403a10001780d0b2502c0340c0c204c1c50001d1100c2c015101d405011070301106856050300c45c10400e0151005411094003441c00c141d01d4416a010000241e00200700502440c03402000030a00700c41400081400c0c0100c1d1404107400c01e1080703514031030342c0e1312151102d00c9079a01040700300200708108008111070307815a502e40140da1502e1140c901d000f101084000f003014003e00b214550350362004003c015242141000408100104071094040d901d401300205d00d8a03c1802054140c030141001585403160b440180130003400001c0012944408050740032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291720512 1250 291719262 291719279
    0x6030540030302270f0d1502030c03070f05070b0c16050a390b0304080c0d09030c060306081504140a05100f0902030a032a08030f01080d09090b0604 65
    0x9040550180e900183c1303400c5040d0035041c45140307184c20308110a201c041c03200040d0780c941c000303581c4503001980d84644445842c40e00706c0c8480e840700000c00e50580080b04000c0c0c1c5054020140d4400c240543d03601c00909180c0c01c05890a106c4d0120140c0907a0b00580050300b5994880000c1c10303000600c0307a0310544800d00d501c40c50300708550150203c0325002050341c0000c901ca01c92416034000d560610f01124000725170301344508809240d01c01c2d0003001d03001000003001d0107044230985e4401c0020805507090140110380c002c150104070300044074032400c1c0b0079001c120a8801d100d1b80c01900c682c8001081ca00c44c2000040b443c603603000b04101c031140808a400311041d0400c1c0548448984543c00510146101960075419103007030744083c40300d85260501c40805698000f03140b5030025054185043c140c0403c070101d0014840001c20120368041e0031228008000b190b4000b58410b102d0220194801d90701c90704030503113a902c5030007408002104581c062054514a034012122030030004c06940c50107603182c246 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291721762 1250 291720512 291720631
    0xd05090c19030501060f050618060d020304060207030909020a050a11070305160e07030c0e010e010c120c03080f01030c06050c070306060f080d020d050301060315170d09060305 77
    0x659070000281c000c1081007040034091000544075150804400038244004600c088c0600c900e0881164100c86020509445800c00c8401c5401c1800c0f0655a07440d05080030f9019512003030013200011003603000002d0482d55403003920f54050306035803400d12701030351100d044a030109580a054000e014540300040010401c024843e0780c0d2940036100c10100f841d00751040e0301c85000410640c245414a48140095079003c00502503000c024282119414007140040f10a08120903000700307010740042d0640d60b01c03a0040440c10840748680d9541440f40e8841050010000080c80000d04940c0810f0b000e00c000c50203000588408030b80c101c12159541d07601d449000a4500950060f0260382c0c898509002e4050107114507448902280006c4c842c6d980700d400000c000b0712051003020201580d50300d1780042004581340c1d00000f802d0540c210109007210381c000b41d486070b00d809000e0f80440c0109000045080c064040c4a1081503405100751030b8401c01c05408080206541100040159104071070311000c040011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291723012 1250 291721762 291721789
    0x71b050901090f02160b01060f021c0809031e03091603020d0b040206070b040614010905270307080301080d18030302150403030902030d1206090e0a0f06090803040b061005030c0d05090c 81
    0x6c2e0003149514242000e400401c1c1d03204150304541080400c0d0341e81f01c024140c806000041403405410596401300d4090a600802d09151342c00340184065210030460940654018050309041d00d180740c0b4110403402c010981484001c3d0440f1a0341c4d05c581c041010f40d5241544180007a02c0d0510382402c0d81d513103210b10b00c03089401300d51940ea5035014a650020061960340035100c004000c00950804840c010940000728401c100701851100c5d1a04550300c00384180d4041e561b000020302d4480d61258522030311100c04c1c2e4030480010f03c0350307803000111546c001710300411250150041d00542520b10b0708180d04000c020400e90505880d081c031200162030400580701c921a90703a44205c5d016a103041c1c0f070300648901c2c1c0c0c0507500782802c2911642010b080481c4905505038480750081d1b4440b118600350014140d40c140142078040040108400c2c413240c0300da030a204a4084600b0b01b03c000300441e0686643c0030130348070b04103425014051605e00d29030303540c001a0852900c03412500400d102c80c1c00a00d00c030300c5554 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291724262 1250 291723012 291723023
    0x40812070c170d0e010309030804060b010905030102070309080c0d0c0e220f0b0702070812090d080f030106020c030604150e010b060a02161211061804060b071b050901090f0216 77
    0x3000300f0314555100d0071516581d8002d1a040c00100c1c2c058400611105019001401d040d07034429001034540e014400d09801080c02400a6460317008906024103801c3c20340c41601024058074000008070300d08100c3c070022440d440350a0256441c1403001d4035a070400c00034038103409079031000c110840d0b01040304840d0407034074425403160403005413900d07140b491500c019000000b0355105440600c91440045444038100d1024051561102c001c040052400034104030080c1902d540004e90320700803a80c400040d81600d5407030702103c0d040f03490f190501d590b401c0100d902609641060141249543c41a086185600644000401c20403480d40008e100d80d44070f49000009a0320034540800b0400d8020556401444c0044006884540507190502d840e101d0740242441010000f0300e990015881c0407031650511405881048800c0e151000038402d98031404040e40e0718503440e003401a01ca00012900000c1e075801038204c04042c4d01c3c0524920180000100e6240720b55002d02ca10f0362498400d200c00c902d000d0140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291725512 1250 291724262 291724273
    0x803220b04290601110c04020403030e090903030405031903020c070e06040f020408060a0c120615110309130f02041d0109110412030f0e0909010606020c0402040812070c17 75
    0x24600b5040340441911020007002058040c1140200300c5600507034485000c2c2007a90360102940c02e200c0c00d01d00c40403800c69120f8404507011040c980c3c081034004640d0130540c0c0400d00d07074580230505660390000312402006070784204806a5903090180c405c0701d8648007820058101014505034a0a048650708142c8442c014201000400e1030f00e4001c20040c11400b100851600781403001654a441004006010280d15880a9544d681c03264011281800900d5400c003c10b503112924a10640c00510310003002a5a40d81da40600c0040801100c1e41c95200600040300c0313110f5400c180028010511105000540c00d020000b0700c0b80c40c44116148805141300c0028066040c62075400031104c080301c1145852006100c1030090451064070804040d4046c140506c00c84486001159040b000a030300541040c044802d100d4542015001002070b100300741c080d40c440c010a00144822405244644003007903004590302d1b00030b038030b614005000c424000c00fa01c0d101192206000f040c0c0c1c00004001c444140c2c440c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291726618 1106 291725512 291725521
    0x3110405130b01090b010f0e010c0308250201020405030f0d0c060f1e090204060e060604030318050907020f1203130b0a1e02090a08070b03040803220b 66
    0x140b031020540e15a46190042c0c0040482a07001c1659490504c3c0d12a025130060015900f040e07450b1110b000113524100d412982c0544885400001249400d14030b241444003418043c90603000542e64520b0081450726200e141c1d24007400760f4200b00b14000445a00a513850041d5401000203d10304070300381e4480d4001c00421013030228400076441c0c54840120135030081e0310780700d0080300e08200c002d9030f8074040c0c4d103207110499001d50301860070003042c00041d0090b03480001e00341e081d82042518a840384049002c0c044140c0e68200076a0207041d40140945040001c0c01c240c4410040c05400c50500c181030700300040c2c0e5148020440103462000913801d1816501105000c1e040460f40c0900d503101203913a40003544001862400b8118009000ca0704910010b034110485519507540d6180d90f451b62a1414541c04c0900304010950b00c01182d04220800d154a1a03851400b40700d04007e1801d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 291546762 291726618 := by
  have h0 := BRFrame.cov_init 291546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291546762 ≤ n) (h2 : n < 291726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
