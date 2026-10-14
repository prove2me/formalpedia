-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:13:04.191981+00:00
-- url     : https://prove2.me/submissions/e7b6b32a-b19c-41cd-a136-3721b3097701

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267266187 ≤ n < 267446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267267437 1250 267266187 267266189
    0x90302010306091b20060f06100c05030a1b020301020c03040f080606090703020d141f090509061b07051002070c06030b030a060c0e09040c091401080307110f12010501 73
    0x404079080503004210aa29400342040740c1c0c048141c1c6020103c1c1c0590103c4507541c48000b01034464100700c2e2509040141400118455101c42021071030b103040ca0014443d0803107110300784208010700d0912410010300c010040380e41901e0245001c48007500b1042100071250b01d2031000a526620000f2a18604c003404800360088031000807030b884081c1d554980c01a02c03030340215181c80c0c0c011544d100161007540280e000d800340745094200010040d44642c5000d82c0340c1c00a55941c0095005200d00030017024001da4120042c10b605141402207003440c03180f4a683c1c0c00c025003030302000340d010790a54404c01c100c0800d560400350480c00f181c554626009010009603c030718010ba503142c01c04a00412040d0082c09507498480d00500107100c101c1d1640c9503503005104a0090320200b24140c200c7e285e0a943c0d2141c1c02e03010318020403010050700d250101010491700100c0c1401c0343c0030111801000030f0381c80482a0f500c540c3d00018a1100314621800007660480602e50701c03503104104138600c0e28040070540c8414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267268687 1250 267267437 267267439
    0x614010f0518091b0a0e030607030605031e010225120903051e010b030109030203130e040305040b0a050d0606051903060b18180c071205030105060301090b120d090302 73
    0xd4140c5400c031045071580b1450403402c40b1001c1d01c00911400d41882c070340d019401282c0d0f402d00550784c1c920292500c3c80d6031240d0440700c000b03581c2c41c40728411b900d01804282e4110a0b181010001c5528005c0840e451b51021200c1003074604149208150195083d0103d070125207000d2101d500f002c0c20000308401e01c2507488016140c520082107a584018020a94042070703035007100081c044d05488031600036960304406183c9056540350500c1203903507202406000015072003a00650b0701c403102200a2107506c030f05070344202d4814000000b44000310f50010110340941c2c8d42d007a403141e03072019902020380c0c003480741d9000415614034081c8002003466210000d0725154296260005c10303a04184022420b64045008102c0340c031108000d4500c3d0f18000c6c00c4070720350014003c0c2c0b000c1c4e090002a120b954400f2012a00095407403400120001003141542c0c00030340200141c02d0032401d550404003c2a40d0340814024600d9141c1d5036181140c40d036903124036500d81044000126260400c001100801605c5244422 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267269937 1250 267268687 267268697
    0x1a07091701050124090506031504110307050301050108090f0d200105060a050f0301060f140907020321070c0f06020a03060b31090e0a170313060b13061401 68
    0x31200d20300c0c040c01914101c80d01c00308004450441324500680c0442c4d4084101e0601140c82c1d00003c3c80c0d140e0070b001d10b216041d00142c0300e0211200d242804203903642505a100030280820070442c4160700841524190703002171a0054203951943c203058901812a5038805170b62003216502c548190b0b001d040c4c842080c4403a2906104181284085e03801ea88050342c90341d07404441c016044c092410685052401550000c0c00490b203203548480384a03c09406402521142e801c0701d03426956030401701c810642080c0184015031620644019184542e42004501c5944801480210349503d110340c0990008580104070548440c55625201740250b002d0b0302c1240200741001400a841d000d803000b61412903e4070242208400141c181c20000040c140841c00d100b0355001c0700c0854805682d200c0c1104841aa600410100400d8148104548941841d20050301307410410800351103078669044a60907400303070021400c0882e03c0c0000b030604007010b040d141140e00c1c02d040040c00701d41c0100b030544011070a0700c1e6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267271187 1250 267269937 267269969
    0xe070b0a2c041a0d080319060f050f0108150904060b0619080108010606020a0b090708030c0309040609020703050711040e0d030504060c02073611030717100302010c1a0709 75
    0x141c0d010451100c03550303c0641071300d101001c80c000030f005540c05810b8180032903a0b0102000080c0444016030000b08a01c03400800501031420f03e1110680300042c01d082440d0070745445120700180d40000001c980c0901c52010105040240c136400000d00b138400144003035224440d034080c03164280c0c580301019000039035800c00022601c00600c6003800b83c4006a01501740f4400c681c0b540034403113034050080b042d00c2c440c80d02e00044024090010308045800d0101446d0303a44c035000c3c10001500c01d01e8100408140c0704001300300020b80c2200449082c00d07400000740c0380318600c03500000c00500b83d0312654500d40c041d10040d804040d5059100f40c0c070a40c0724110170000b113500220100e81c0c030030300d9021340c1e04041d000820340c110748500ba240b42c40c00e0003020900d2100c0d90450b40c1c849425268030740041c01070b43c1000b1042c8a00c1940000d8903c1404d16454039001d594030f0705071074100c00c0d00450b20029041c0003000040c441032280c4441483c410703a100108500c910304000a0081480c3c1d46486141c2844040d030078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267272437 1250 267271187 267271211
    0x1120206071221020313170409060308040303020d032d1e090b0c040e04022407060203070f032009030c0909070e0711030a0f0215040803070908010e070b0a2c04 70
    0x2003500c6c00f0b40100c2c03007030220a0381c10365a1344044108006580b4040310007132100107003c0084d4029400035503c54246184c4451440ca00685041d05040c2c42d0020f26003010803403151845e590742c9008003410a141030300d00c102152150140113054192903200c1e100455030f0040700c11500d940104950921038000c3c1460f60b905c48040f80454003807400f1380080e441d03070440420302500c3d010040003140030810410100b030100d81407584105c0d9201843c211141500401040700c020740000462807800d0701c03801c06011400386203003d140317040020f000e041c0002002048004d40354508100400703d400001d0b11002032801c05509079540c820701031040c6a0350415900001d60176521030103500a401c1c0f150740044d030900340c03d54016110315850302c01060442c0702d100c85018040b445030f0001400b403801024066503a09045800a00c030392181d8206110343c1c1c0c1041030085001500042c0c5408860140e05e0168035a6810392003100c190f41c1e011254410310908040446803103030004a500404a0704403000c01001051030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267273687 1250 267272437 267272441
    0x105070203100b030f0105011511010c080f0907050a1e060c1a0c070821090706090b090a0f080726100b060d02070501050603210301120206071221 64
    0x80025096000100741c000e18110a03045036070359010080940c0d00000700013880c5402c4400907440f01c0384900010f48031070003481d001811400a50280030081c44a03255040b0007422501d0041c00c1c1b00800e14080c0d0000e842c4c0d00c01840124080c00c0014014240340399180c1c552007407094903801c949403075129540300040703803030046c00c14510050b4881428040c814815069803a030340001007103480c1c4910104006000941c80800803d8a500c0340381d8041003c06049560328030741000140110610b40c49407105000f082d0b00603d405048030034500c50242d88141038408280c81c804075502100704011740c0000401d04080100d0a0790503100c031031903000c161400d43c3c08201c41c123010700854070030340c0e03008918821400e4143d03401410324820b001d8042881c055040803490100e034001941a01c4a9546800b4059640303808e000e110b4004180501c0303501d00c281820345424041c0700600c500d010444004242c0c8003107444e90801d807080300c0d410990000d500001e10001030328400903010b47c18054480041084007080c2e080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267274937 1250 267273687 267273697
    0x326040f0b2212030f03111209010c08071d0f10110c060a09090513240b04020f030f1308030a05150109030506010506071403031015110a0b04150509010b01020c0105 72
    0xf01d403290020b009507201034030f58505082c0c45604040d03e600404c007082540c007000302a2a903983c401c50030f5900d0003088050855080800c00e10400801809001c0942d900a030b916480c558240c94050680041100240140034a2481e041d0006140f17042032980a82241100703884000305810354940c0c0049030300b0080c0ca2300c07900c0c6524011600b1200188049000c5900480d4400856004452100303d0740d01d030b580c0301d0300096841d1905003065003621210359000e405207041d40d403001d5905505001300411034201500000340346040d0742c0b00d05000030319080c250b000d4074059140c01010351035803810715140b054080d0404944525010b44440d82c504202e503c03407010503080702d40100151039a80d007000c00300000341d030000d402501d0030f00319403c0941110900b40001e40c01040490040303403900c0c2c6402964044002d00c1c0d2002411b109503240070000010340840c4190265a02030004131955403141344c14220081c0c0c1c030003480500b0785000108201d00905511010800170700341c086070060440c91004444c94415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267276187 1250 267274937 267274949
    0xd0e01020912120409020705030c0a060c090e010e040b040c090c021b010804150b0d0227010f08061b1909050a05040921020f0316020f0a0326040f0b22 66
    0x104200405c441030307280d0b000c0c110083c441d0703040c2e0f403500e2240080a0b2801c030b2803610541d4030b59070f03801407000069040103415005241a4110460561520042d000003a03801840a0100b24240300050200448076070b594000d008180410041d89541010096a0f010700c0e2000e0075102a81071341100503980510f800a101d41d6001d07490001c10312095500314054041641c001c3c0c0c0110404001c200103940b038002102c0c070038807001c00c044940e818106620158020607800008003c0070303484207106180c13010030036039409000300c0c1c0342800c1c4151501c9040c01500c15548401c0014a500070712014595000114800700c0c0c0088036803841541e02c880412044812041c030040142c0e000a24000400b0b030181c2115600c0c02c0d160056602007001503280904581c0281c0e440b0b40101e030351502c41000c52601c000c5590060134261014000e2505541c0c0d030320107003c0325070081d0302040200300d181d0031104249000c032000303403100c00001d4040359038451b0002110740240307040031488080ae00000994640c3e184041049580c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267277437 1250 267276187 267276223
    0x1060e06090409052e0b010503060a0303080405120f0c061b04030f050f0a14010e011a01030207020a0f0b040e060f0109030b100e071e0f0f140d0e01020912 68
    0x4041c9040200900e203461044509018481400b0720744542c41c012007003024400c0d0b21681481c1081d01e144001c0703500280c8018103001040c414480c458807412540020341f681418464007980b61800c14174940780e0080c00000d101a00062440800e43c01d21000e800e24001c50310459002c0c3e22421f461040d0009602805001d000d414481000490b0800780710009160040003910031980078108550b0404260b030405643e00f5118946400c25000240300e0424140d400800070003040d0804402d10021012130a600760416402040e400c06541d100310005000b4103000700000e0b0390541e0303076840001039013040c89412a6240d440c400624541815110800d82c4a81651020a80c0b4159525042c0c811400390440d01590a140d001041505060ba42c00e802030049403529590f41001c401107020311040400300c401080000080409025004016071600122070304024480004103540307520140180b000b00703c44203046c01c44d0150304200640c02002550340a4950794681120600d01d981d59221080307815010074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267278687 1250 267277437 267277447
    0x516030b06060d18030201050618090a0b060102010b10031a01030605090103080f1606050115050a0801090e01111603030b03071a0310030b0f0a1a0102070b0a0908070b0d0501060e06 79
    0x12410030300501e03d80400e0600083d04451003507001072070307403040b840480150b0340d64130078820780e4030f0040c0c0b41000504140d00e420502c0d240082582d51159290b04008010042078000716010f40e00070f4101848116000d03040d004d1803541c0a00050107011901e22108460308008600c3c0f410754030234003501c0196080684404050303441c0d5603441495074400b9141041a500a02001181c280e22014480800e40240000302e007550601c00ca0440040e08104950140101040001d144039080700c0703418115038038448001110403521031054013402c0408000d00c1104400a08810000d01c0100303610a0240250303020411009031406140d5164403c1c002c48100315400c1d0380192160301524001c5500100010009035695500c0d80e0b1106807400c19a16034801d041d440c0100042400c261245110418040b9100b0031200000030010751104030fa4021440194030010b08155240c1c0110918001030141e00100c4109903036a5400b0665170700910306118540382480c00002d829032040c00031490010005140d9481c007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267279937 1250 267278687 267278689
    0x1c030507111f06320f090f04020a0e06090a051b070501060f05060403030516150e0606010f0801050d08030c04171e0703020901090b1207090c080a090b070c0c0506030408070516030b06 80
    0x504d0b000d00500d52200414448510790b0301c90441c80d500422264406102c981014810003144403200d4101102c8402d6400400109595151000341c1010b001c440001e0262180590522502d8014080c05040301d400540003080040540c0101d04584004214845d010f440703404116291249210140014070b05020341c1c0040c2240c0802c02280c0c921800f00c401072405140802d000b595501c040041054110108100361540c11800158170500903160030700540d814513000410f1031303c2c8418058141d09000c00000ea0344804102110007038241c40501507903418240355050313641d5100403028855940b0800700480c802e00700140c03103002c1c3c80c0e00801072542c507030030609880000c00c2d040511a0f48401501e5101c1c40480052180750044e1805880c0420290075000b0040d01e4200c0150461000f140b410180c640801c0c0004085a008000c41c6031040700342c96a8203003101400010b400851744007000105100810070a00010001544104207903100f1102241d08045a92034a2002030660322140c8006011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 267281187 1250 267279937 267280019
    0x60103030f030204030203011104082103070e012006040314040b0301050112021b0c0f0303090d030e01090f1503110c0601090b040f0203010f0302121c030507111f06 72
    0x10820680c0b4005051550b6500002d0a64101e0240e14801d9070000400340103070b901c103001101d4007010b01c82c9626801c0c01010305041c1d6038400203110808101d12254030b0703503050f2f10582e800c0160308020211507120190207d0000e13181c0b8001c0e90100c003c81d840c0402c00325810461810385085402a0502504580c60302006450803200350007506503041c0d0030450183c1c40e540c2c10902006040c03058000f403001c1d00d40d8900f0301030150b0440c1e6106100740e00c1804065078690710601160002940341c40c04100b494130060041e9128101c80e000b0728001c1445140210b00c2e201e400c00340c60403000203030b034003403000c1940020014810721035202450126005580180b0815a01d90404c2003602c10141c00041d803c0b01d0107401c90708903002a00a40c00c140030242c001c00951500c041c80034045a9500c016001410351010702006040840da030f04028151140300062049004200d5100f001c030070802640d010440702000504880740d40c51300044000c0c40d000020a00c1c0415501f202010001d1090700c070f11500340302c00d01c58a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 267282437 1250 267281187 267281207
    0x60105120a200105090d0308220b1f030c0303020d08070504081b12120315040203010644040c0f0f050918010204060c11040203040305070b2e0608090d0206010303 71
    0x70600c0400c00c2005c109440d15115460700d50f01a966140c11070408200b91200017900c2c010440030314000100f40008114000e401641040301402418004542c4095404d05841180d0014280611924000052540101e941201400240ea605c2d03c0d40d601c004083c0c0b0240514007644080d039001c6607a501074407800e001c440400500081181c3c00c40c5807501d60003031401b400317401801c1d0807139000320521414442e102c0e00191814001c880650541d1304146000f0409a040100061181842e200302840f0180e440c0d801c007510401440b02d2640314001c5c1000c0c12100340243e0301115440040d100c0040c249200b64805c5c416501c0c03180d44445060b103030030100a8900f0740a03040960080c20103080000c040000d1000f48014150b68540191010560030020300008441d841e00340514010020440080e030b0040889041c140d01c4140c03101c040e02c50480414100b0320380ca10310000c00101d8140400c110303103111500700490701156503d03000c6945550306c0c15103501c0030796a0403015034070007001440080c1c040c0151030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 267283687 1250 267282437 267282439
    0x30c06030b0f0a09090203060906012405070f030305011d01050906060a090f0e0105033c1c031b1d01050c160e0106030e160513020d05010305060105120a20 68
    0x3440320b040a000140d0f542c48140e104034039403a69681a2421801d06000c42d03a030008640b0054840d81d071610610b404401e0a08081900c10f160b0301e64081c007100e002e1800d4648080d0080350001c11050240b4019000708001c2c0a0008507070700384140e403001c280c0c41114007410b03140060007244071502d40d01d050001540009070980180111407102084122200324014018100f070604070140d075140c00103040c00e2402111159441e4425024601907000d103140d05d14030070b83d4917000c2042012604c0800c080c203140e402045106849150013002c248143e043d008400c0350b10b400d0010a4440c8515075003601c1d450860499402440c1d052034404c900c645c00303000034050040c108419a40803020342c42848c0880131050304003002d11144040180821030f8103210f01d821800c0c4540043c08900c070b089022440c0551103114051083c1d40c000444090a0000c1c0c06a0b902c28220000034040c1e541c40e880e250b1740303c0e5824000c890041780c4d00301e17490310800310000e441c5502c6a003284e00c0d88449411008042d41400d00a0303045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 267284937 1250 267283687 267283699
    0x50a030e120102120103030e191401031e0e07090b0a050d020406030807080c0d080402030309090405010612060e0606240306030705100309020108071404090509070807150206070801030c06030b 84
    0x2100700c81003e00050000200022850010303604500c2d01070800c14011200601408086664401010702481c1031015181c160441c01031180444004070080c1007112002c1c1400303c0040400c045aa00a030818403d4550707403020307511000c3e00d540301ea41c2283d440080050f88104420000c010300d0901c55150342c5120b002510100da00c5440f9210b80c641d03540802d1003180e04040010b00900144021300c85200943d00c0351411030341f141460380010b40d0f68000c50080301d03c07034404507021400300002540580c00070b016116202c1c2d6580c03118148a0014410b6603903156450240c3c074001039181c6840d502e01c100e04000c0002181000c0d00c81c10315040300b5003004001d903030103105002010407035a8407450022100318031943c0107c1da5110360300c001805090301810035006d000140101c0a040000b10301514140e43d40c949001900b82e031141c1a880ca403410581c400101070242440c041401e83c958021521240c042e40c0885034039440301401201d102200344005440030589120070700941e4400d81150002003401082 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 267286187 1250 267284937 267284959
    0x6060706020301030813050907170702010f1d070902040f03030c060b2115040503091c0b0702061e0402031906021b06090c0603060306071419080604050a09050a030e 72
    0x4000c00c9034000e030003c4c1e841400102d0714003009020428154040e001c20344070103040d0304202c01c010300b11340d4090f040c0c44c1840e18020002040c862003548100c0d00d1804480c400e200f17281c2c040c8001840350f5000c0d02e0881503400b5000700822142c42d079008035803c40b1812482902103e18503203003141da0307a03d05501110000c2c1c907400c030700e40181c1d2502e03c0c0e5000a82c002c4598195000d80786140c514000d14050042d02040c152803c02001c01c40100a03100c60b07038010303100b040702108402c1c8070603101c081d031503130040c0861020400d110807541c4c001b403454801c2271851000c550091890000304581c4c901194000d6055008003154100c4003a20420080c0d864441c2e10098201403041101c51415415100e8010160780300b9003c100c40c00d80100000c1d01d00c07550507113072607295080c8007000c2511450024450303003d01c00707a1a13007118941481422610000f02c0c064581003508603800c001816854207070f540e45d11a501305801326024030303070500c101004581e008005003226507a5039001d60380381301e03640021980322640c00d00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 267287437 1250 267286187 267286193
    0xf180209041a010b0405010f020a020117090f07030b06030610120320010216150b0d020405090304050d060501050f06030c1b0c04090308040203060a060312030e0a02040e06250512060607 81
    0xc0c150207445013060703540c0c460781064001003160340761600c90811036000480d004d000d41d0700301000ca91742c0351010216100303658541588610381614400300ea0260700c0b4601c80042401180b098041c021942101a01c0803038440405508031065203014011250110341200400203009481c040a80d0001c04000c1c1c41c19600c4200340ea08a801c0410340a10340140404000c041042402c2c0b40b00e9a220752110400c50420780c0b4010400e92010104005d01403030b620700101e8240c82e001c02c151001003000030218101e9011070300d0040c014140030312409000b10310034a4010700714a004e134142c901c1110280303080c1c2d0400c400201d40f0b103030603034070b151085c1c0207802000181e903180e44542c02503221045c043e40324800203091510605241c0a0000e01c61807a07a481c00030103000040011049450903500c0e4500440c04074201e2401508009d481da0000b90b20074509030780301b4001100483c041b88135680840b00703010289007000c0c40f01542d154080d80440098000c1000140c012681044c950701300c50060109400c0003603550b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 267288687 1250 267287437 267287483
    0xf080706050d0e15040f05061812160222061d0a020a14271002070e0a0b220506041505011103040807090e0601060201021c021605100605040f18020904 66
    0xd00c05070340c0c0071600c1c102c52050290400140d60403d08240b11400d090300500f0340d52b500c1d0003180500780f46082000071b512030844140809031000381d400030000c4008070300c24821001b120700200b6500007458104000020503664007000800c4402d000036150001d960340100500003036008407015010711a40907200c11002403034902030101280380320300b5043c1c03402241d150761120f107202d040b104c0e10134031000d40c00e6000729038003042000841e0245e140c01c015645803000c228000d000d1319201030b900001030464070030004c2e409555400303001d5845141004980c40f0702d0180400c1c0e07840c0c1c2d0003c00b05508002030070402c9510a400c186075401860003504d04161300c41508071300b8450942c0c0801c40f00781d102c821401c0f002c403050104900409144c0021464000341c00000d03210103618845204407180d010070002d1203002507450700f0400302d41c080151050b107407420301e42000500d264003400e40600c3c500702d0030000640c941d02c602820181013401c071400410f4540c1c00c204c00f032840144200c03019001c20704440307420b03100d0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 267289937 1250 267288687 267288691
    0x9040312140c0a0e0a0b040303030c120c030204050906012c01030204090905030403020312044202010c02100209031b01140409050601080f010b0d0506150c0303010f080706050d0e15 79
    0x18840d9890381a000020200c40c480c15400c5c2c41180380040c01c00c0665070b076908460440303500d82030200d0701000004003620250540400e0080c0641010603514407203500d07074000c00907a00b0842d500541da444160044515810724902e0b070468450344803444054008400110428080c1458050710301070700c036155481501d4558070308503002e500c042800c0c130440c9401d100c904040c1072994416400c0a01c0c1c02980a0040f01b081c120f5962094001c44021030b51441c041182e08075600c541d002a6401c8841200038001e20303510300c04100602440c0341136072810510340221707031304d180d001001000c0070380703403203c00c00b61041d00c00000d0b5062000d032883c001e26086a030005040181221200000d0340c4c50f10744000360601302c00506070003240e960b080041c081d003050501070300d198940f49400015203584039000706607600040070521010302800704540c440c40e00004000c40c1a1400001940c00003030f40d51142565600d040e00400c1d01044013400404440402580103040e188003001c12500e085d400740801890820307007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 267291187 1250 267289937 267289951
    0x209010b1c0e011b030f050a050405030f0315060a0804110a05030c010806040b04090b0103172104240608070f1203120906180201020105090a03020613020102032104031b020904031214 80
    0x2c64006e0703411a4660300c07034144e00020b00d01050100d45040d41e82c2d280c40e1b01c510340728003c2000c0c01001060182101810081d419a800b90006a03602550741015042d410200e4007201c0c0e000180a48114900b0300b808030008854000c2d00401d10b4003090001511f0b0b822008000d950010340d545105003007030b038440c018042e0300c81c02984419029415400c2c500d003966002d400d43c5417083c03410441150380c803d100f008903500b01000400c503005a251440c06032056031a4445140c4851144071030000c1ca1411980200e084520710300440f02d07125a144583c01d40d680d01481000d030040740c0680d0000119000d0007450984201040c000111030704180c1d40c803400c40b0310340c582405030740b040d184a50046580911072950444010b0008020004040e50000d640f03030030007480d03030300c04180015404007164020411790300e20102d1007003d01d40d110b99000808100d00300481f03003a070014200c1072001800d43c402c0e101c1c51064540180c4001220b82d2203441c02d0f9444c01003900364034009079a4032070720030840462540543c01601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 267292437 1250 267291187 267291191
    0xe040c031b0309140601061205191104170f03120c0705010f1505040216060e0109020301020309010c020705061206041505030609071e0f030f0201030e060106020a0209010b1c0e011b03 80
    0x498100300d86404e1140c440d41040780d000000510559803c0040101e84d081180404246130340c5090106090480c003c08044219060506100e00852640050400c2d52904100700050084281f0762595810074402c00010b81d810420501c04c81d1002c0c403411541c403040a554039881d00d00240d03605400c588080d40340c90405541c500010402c2003011a114005007411a41541400c28081c01803258501d080401410907640c5c912041140034290804038200390000c0085490345003681140c0c1c0a0085039005ca00103001e0b080c400f040510f400025103103109000d050100160fa1850280f00c0205801e10360100503801c00840086c09030340800c5460300c5200780b0fa000d030030400c3c60543e900c2c2d541c0c0e140c800d80301032185a901c400d005602d44e980b0050102c03500f008024040c0c480900060300206040107c010b2280900f03030000c2141c0b50000b1704101c52901c02d44404460342c0c1d99070006802c600480d0400e28500344c02043c11103c184080d0820348039154803000004019561006192682c03007405001c03008a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 267293687 1250 267292437 267292451
    0xe040f050607030c020316060f0e03070c0602030c060a0c0912080a0e010e1c020d02030a14160501090303110f030a021608150105121603150b010c02010e040c031b03 72
    0x119062000581204283c10144580103554401075101d004040c401d003203410b43c40c068007050140c5500152713409a0051000c0100b1070000e0203940d00c0381d020181c00d590651b016100091441e00c0042196441c40c3c140000e084244c0342c1c50b10385400313451105410010000c0b0110007050340e1580c4204040240d00c0b43c81d005541e20a1807501814900003140c550381404426004ea00711a01c80209180c81040c0b01034036440b16910510014200c100b0a40c4013940501c102e010a004006400d03042c42101c1089008440441400c3d0740e100240340091b0084900043c268081000080e02039040e03031120700040c9003a41d540220344603403a8a590041c5000400682c0104517405030010b040340008003425002000d00307107000a1200c046144001882190b009009210319131800403010300000701d18000c412042c0000d650360303041c106150b100e503880c140ca40619010390740c13101f5030084418181080e410f840380100401504200002031001c0e0364a1000d05480340707104500e140001d075000340f0424854034000b03461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 267294937 1250 267293687 267293693
    0x30103170c0d1205070206010602060a0e011503110a09233d090911150d0c02070e0903070b0a0b0301021209070603050f0c070204021c090605160302040605180a0e040f 73
    0x213220050006000d5400400040c840d450380460b80542c08010301c1c201081e00c030012403500f8010b15540e1500100f0740c0c100c100200800000b1078a003c0711481c2211032410080d11b485806088607940d62031a40c10f2040350000e1400d01440c0d0110b60b5214020440284002c002c10b9610741d065038071140e0600d5492855100091207030301c0d00403828003a0a85110401140440d036644910603004c00030711134820300c3c8050344402d0066400c01241c5943c4a0500188440c0b010050040d50301c0c48540103202c00c2c0d44802e000140307031030000415a00030313a4100702150095119001d0240041080111039500742d5000c02c502900a101c88107064019a5020010701c0398503d020401411110041e0607401c600e8602d80038842b0300c0e0800c0054510480e012900169601c4039050b042241d400305030b0740214401d0418900760140901075009601c5a40c9605142a001c1c5491070110200c1c032880c040c49010a5007804005250180090718404000c80a040c10324004c3c3c43d030741c82e80c180036802c4804031246012042c0030420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 267296187 1250 267294937 267294941
    0x403020d2906040e0c0109140609120c04060b36030a03090e0906010602060f060a0f09020d0b0a080304060c02030312090604030e04050112020d0501200c070e0606030103170c0d12 78
    0x1c3c02a84800340212070090b000081601a10740306032160760000307151218452782c8200840f001800000e00d4281c40e804a10004ea45840650035014480c0d440e042c000034130b01c000141114020300803c002c84070144456040a40900e002990042c5005c0210104c070900391020072507141500d00984505032000c0c6846011005103000400c5410960807401c010402550000383d06034200500d044102c40944d548804141107020740d9126130400d81d91014001f0300c011255000f4100004814010710000c0c05103800c2c08011040791081c00b20991040104010191040d8550b0300701c10320081c01c0d00d01e415110b880050381d480050350300d80000c1e00510705000806801c20b421500401d070035102400f180d1301d4416030f079481e03080010001e80103038654031820301003040a40c418848403d0304240c41034118000c5000c110306810020070090f951003050408103060304801c0c1384c903204100040100703180d0f80c20740d5617001c1504220710000300e503102c050088145841044c0418403518900d541c034140303014404100001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 267297437 1250 267296187 267296201
    0x5030c100f06120f08222111010c080403020d030e13141501021006080c01021015050f013c0e090708101d07030c090b0403020d290604 59
    0x1071440e0150030001d14180d2810605159004510b401c009982ea042c0414a403182c02c11140542e02d2800b40305a440c1d00c0f4540d22010341c0c422140c0b44400c411418110301882c035800f440644250740d0b41200030920342c4030f405d40e40600c52050b0340c401d061641e01c0d80400c003080c2da8000101c0102d250111141c1c8141001058815030b140c12110a01c502400d4264003044aa80609610b54466190300d100419900810031030a072061400c1c020082d003503031808401d40b20312142410300d00502400b42841d41d00c81d154007560001e0b4204482c00c00d09585048204100d600074038040d507050000c0c0c103040d01c04440c9401c5d035402c45012040d041950200c140d400181c0880000c10001051003810410344000e5100c0644440c1e0182880c1011001619030000c4d81c0e5510744c0070b6000c13055101390404450700b2200498040c6d8083c035103030f850a0100c08801c00d401d8401c1552405107801a81080c0010005441c0403c03074171281b1030103801e080d407102804400d036052020300d0b1184203031030040103000d21000c1e0605c0e1241031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 267298687 1250 267297437 267297461
    0x4020708041a040e01060c03030603140f010b010203090a2903010906031707050c1302040807090e0c0108011203080a0f0f2a0c0b060f0d0b010e010e040201140a030905030c10 76
    0xb6107020f081000c00124004180603a0301009900d0040f041050700a0b40054083c0d600003848801800f0011115076983c01320325021225542004d50071421540004240d80c0c0b86000189510381230341c281038000581c1441980350204403000b80c00603040e030400b40340041d8060a42120013050407821418450b0002d45e8800b804000c8010400a9101203038012801d40540c80d030446906500c1c0e81107194150190050750014000c6024810001502000341d90045010170006015103050860113001074a10380070034450308010f612800340d0040000e00c1115026484450b040e40015903d1503a403142c4100c07014480281003040d80d44882c3c42c610040140d40b41c0b00c0c544204020f100038545240001c04054145800500c00c403030104c04110b1507511003060100100000c1e2401d40c8050385400c08201145081c81201d58a40c040300020070380c1420102114484c07501038403040c00041158200b1300e441c0d0b100b40c80c40f404266844100c18006241800140111a000030052001114082d415011906205144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 267299937 1250 267298687 267298739
    0xb19031a0705030403200109020402040b0a080609070c2a06050918060f01031109030102070b010e010603142d010f09240605070201020709020c10051e06100207050402070804 76
    0x40b001a6015804c0003d02040852000a1100c001041b501600180400952203030001c1008219021058094924460280c4c0d8241494544405020344500c0c05e07144c1c50005020842d6141c04540c8907030700210f1484800d46400e0320019100c03804074240d1520b80140c000207000048501c0a80303000b101c41101e0400c2900d21310024144400014a549802e440042c1450340740c1d8103510f021405401695007448002e0025940d85649252040448809015940000c0b140c60004507103a40f0920484500040b5564641701e00e844120340c07000001612501c07046c1c03030720811004141c0400c5080303809000301403402e0b031800c0c11800c28610314192690410550125400100f452805e0810002002c040b201c07a41402d650750080b500040f400c1038000c4d0084030307425000080c0940f002e40700050030a0202e905450420080d26001d1302030381c1c0303540c01c01c801c884001800d03004141036241005c05100084a00d00459a10595850100e07040c1c4e0001d4400b81da10140c081400c00c10340801942443d101c2100b000a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 267301187 1250 267299937 267299941
    0x603050a0e0d0c020114071b0f06080405030412080c1009050f01090203030313080f030903070605150603190e011505030714030604060203100314030316051c0b19031a070503 76
    0x100400207100f42c10080d041050011a0001d0340901d0360464440f00e401c00700380505c20f41030342207488911207544510004180401c50000f00e141c410324206008035400f20245240501d04001c00300c00401a56007030750150030070484040c82c10410050140809903a00300400c0200721800c2103800d041c2c5060814007964103100e03104005a902101300d030780c4591103241c1010000207d0420b0b140c0350045490703606850400006001d60701030000064081d140c07190400384000c5e44c1e0740c1c0710000c50308584c0d1400341d0482c00503c08100760840c2c2c0030000c100d10203d001c000a06440302c102003400d4807004400c000849a2100041c880c40c01c00f0300419002e06551100200000003140c0401e94a0100404c0074008580c0800032612149040030844010b40c0c0000c00d105099085824650f1260b205450520880b500c3c44010500d150140043d1003241c84c800190700494100020118007804103100c90030707405a40c2c80d000010004520f20081d014600585101c800c4000c0c0500300700001c070000d02640240841030003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 267302437 1250 267301187 267301213
    0x1050a0f05070e1c062310050a05270a15050306130f1e061b030b150c010f0516090b09130903050c06040506090c190e0711070603050a0e 60
    0x204030b002d850001c0e0341004407140f813030f0110720708a03201200c000d0580f401c1c880500d4100701103d401d070700000c40c12081200c85854000082c00e46540512406401c00c040c818108100d180c13881c0701c08240d04241551100f400c41e10801c00038100030441c1c1c150155552441c8514605881c0d82c106000741100b500248164203026041c0f018107070300a1002003409050705503000030000c2c008940c021201c055a2100e0218205140160180035030884c4038040e0781e4100700d89480f00e8030a008070000000040c02200d8220b11294a45c50b8590040189a80540d00d40c9007034441188240720740ba2294610382c000419141c05040c0040240e20154820309544105105070025a502c02907161548140004001046240c510701070300c0c9400340c1c0780009141e00a040422061000104001d0f200b410b812003501e203559a24800c01049d0751041041030b00c0004014000e01003040c0f0120b030740750413000d0707400c1010b42c00c0e4102a802d0310b8216590090030010351a44140150361190303003d6882ea04001c00c010700b858500d200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 267303687 1250 267302437 267302447
    0x806030a0807140601080d03051501080415110304150506010503010605041e05090a0b01030b030f1c110d020a020102070603050c03042a031110021501120510020c01050a0f0507 77
    0x100c4007034011000001e40030108101d03c4000c0300c01490300000c1d0380d89507a4a412058a4038400704a8002003030920340058400c00003100d2180174203005844904180c3c0300e948801d00180b100910050b04181d9611f841003001d0a0300002e10710852062100300302c941c4214a2484c280c40000d410365042c0310090005100f601e40140030f80d0305407451402c519802000f98481c0da04403010701d500144d04070046d2402d01107041000d4120f451440305c203807020b000300e9118109060703980010b8084004035030007026500f04075800a82120002e441545848160340c00410501820041c040348040f0143e07000c10090411960180305a078024086418100410710302aa5a0f10315403000070b0008242000042d0a13541d400c030740e00303c1291009a5180580c0c00e140d00c1c1c0c0343c03074052450140c900743d100c1e4440c1401241030510006054080c4411410381c001181d1803c40e400c0440c4811900444160207101a1703180c42c01d03503510207001d9203044200041002d0500001c0e640031990602e036807480950400c001c00041907000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 267304937 1250 267303687 267303703
    0xd0b0a0c0806130222030812010806061315080312090f0a0c032a0803070b090a03020d1d090f010e090c01021c050d0e010c120504020f0918070b1306080603 68
    0x590000d40d9805404240e50791482e845807007170348200c0c54103502009110400b8050003d5102202049800b641c803594210381d203940c00c65100d03501c003030903131200c0f0000c00f010b400c500d524002c800700000c0041c2d268280316003150802500503c0a0074480100032402d070081103c0c030803480e095000b9001e159610745511400700d480d800301078100d004403080c4000101000c1102c0440c17010703010301c03045080d4075428866206e0b8826003003510b8445035880810780300c01d404581c02544c90b5058005048072100404140c0b2450f00d1075000104100b03500c0300c4810a03482d0303200b4a40c81031a510003d1510b96041c00d80c50001d0392400b4001c442d05510180000703120303076000101c481480b900f003c2c904140300103085040302c0a205601d041181c0381d003424001c451184054101000003ea40e0b2540c15a1002c150b03800c000700d031011038019520911803250840e003414501355040d009100e245070399220404001000d8600815940482500280000d82c480140c03090809200980820b1503c00032500b41100040e076a8019 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 267306187 1250 267304937 267304969
    0xc0213020705030d05012d121b080109030503060a080c03060a020d200a0306061119140604050604020906061c020a020102091905010314160c020f0d0b0a0c0806 70
    0x800507020042c440100180ca0030301920301000c0c040742d0f03100d00c0c4e0704074200310340d80c51070502c0040d4504210004408003506010b4403503000e840b24104103a525405d140c2003211502050783d1031300f4100030401c14801c1c00343d95102e60182c2c4426649041c420140f114200542d44004d9064104003040132899802040c1315421070302d000c0300580c03998080691040100080040014014100c41c501810850107801a0044c80390399102000b4580e0742c2c1000391768444482c19844800d80142c406030345c4100e549205103c119000d9a807600610248400c89840c00109580c103039603d50003102000114545004a203601c040243c2d4194103240c004100c1119800c8801c5070340c80e0194001c98504207843c400d5050360102007004141c20481c890400008905007018010309000a003003900a040301c90721740a2050280c8491802e42c1e241e005c40380c074110b411601503038040386d0002d603100c0506599940c4850004813940241c840c0c000b54200002d125080342c40b0381d9051360500680808025240d507600303000c01c1c3c1c1400c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 267307437 1250 267306187 267306191
    0x305070203160318030609150501080706030504030212220603110909060f060f1206010c02090606070213060b09030f01090c180e070b18010305310602070f02010f0c0213 74
    0x118502a00c4401c041c1019900b211340090000051140b66001508003a009145448041350070494850a0b10001d0040512981c4640000c000441c0f00742d0216611034061320542c1c01e0101c4088081c0100d070301c1990703001101c01c1c200c4030f400c0d0035440c030f045044002c14084c04d00b0040c000c80600388c12818022500b005102d035580d040002c04c0e5442d54903010a000c0320042603da51568540b00c03091481c0c22001040c200c406840e400620294083d01203c801181c0080135891141e881c44c081007a07690080710204e8100720b104420300056402401101d024290281c081c680700d1100b5001e140c85c00c121503252018070382c18000183c0c082030581d5081c0068826031480151000901c244100142000d00030403501446411030000c2e001c0040d001074406d9032420740c014032101b46600011816600c2c00d80b00907200c48601c4407034481c0c9071701400850619010ba052043d00d07200e0542c0f1004102e0b008207005075181c0f034450344204111360380b050311f0544401c0503003059440c204d480c1d00498403180500303001c0c008450b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 267308687 1250 267307437 267307477
    0x7050f060f04050d1a010b1e030a0216051f021206060c0a08040906050a0b07110609030f24060a120204050402060d090c0611030a0e04110c0613050d0305070203 70
    0x71080800c480240a000d00064904500341c5440145528161020b80c40911110700124184555000702c422500081e0300812915010a074050103e52029003540c201c40d42c01c020b40185500d200030a06a0035004102401d15907079a00d2404005c1e00b02005121581da104000e0740003940c60700c1c803103903402800941c0d02a440e080011788642c80e05002d10030162202001007400500c00010380c0015056030b100307a50400c50a940c81070040d0f4207000d0004002c00380c02c2034256401644c200078000d86241c1400070300304c6103c181611500d03402d0007161409182c440301c1c038151002e80c52488040d820380140080d41c400d001c01d807424900500b02d50001c40024070998403000810203665554007a14140701414404010107221841c000b400d01201c0d10514000c03903005a0051a607140c048183c400c4d0f820983c0707070b00694005610401c802000005828415008140162146200200a6030f84540d17141c4035a86c810300d01c541060761070040802002030805041a00f000f40d620f41c0030082e41d25800504150403090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 267309937 1250 267308687 267308707
    0xf07061104030f060c09060e010c03031e0c020105010915080a03080705040b030f070e030304052b1b08100b0a090510030519020f0d020d031d0402040311040e07050f06 73
    0x10700c101e50016060540701a1043c0500c403450703200182c2d1104130b0300c075285202e40e41c1c2030079660201c0840007103000c01c0c1c40d086000c0100f030181d00010950f03d06801c410241581c00030644040340c04603c14000140c0d035800040c003501307800384500d040d00c2410b00c40402c8030034a007551039907641018201c01020841c0107000304850600035019200500b2507036540c1a100d00e012200c1c003010400c01c450320743c00107594000805041c20048112410340d240903140c04120030000c295440000f0385070840c01d90f0300d075030000b0020100720680003441240c01600090100d142c85d1540491900d4280088501301502d0008880712640c1c8a181100458281d1040404c9550380da41c010681c0c852145d002410038050010301d41c454076600c500814106208469800c00c521801050083c3c1c0d0308071110080d00010f46014540201e0300071070706401180750703001d01282c000104002080990f081a8012030b111000000d0b41c5240d8503050080f19010a81c6400414040749041c0000c1c030480526185240a00000a068001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 267311187 1250 267309937 267309971
    0x240f05060f0c070b040303030506030d0c110105090d02040c0e1f02190203010f06060f14040305032203060c0507060507111f0f0204180b010908030f0a030e19170f0706 73
    0x60000400131501c944d0b8905001d005007000706c0b0102d1003400b40c584010360079070140c40809051a0041062280c46820b03000640d1542d1003040e51682c0b203445d803181200169124055041c0c1100c0ca036546c203800015140030f100800c411003141554020103402d0303000107940e0004040000801501e640803a03071005001180c01840d039613420004803030502c90b02044c80b07900141804020740303d42c0d58a10103d25610a280580d0042c4c1c0002419a04100646ca065840c1301d50b418142000000c58041550b80d00c1d5149800c42c2c0210300f440c0e0204001080b6002400618410244d000505040004150191065a0741c03100c0c802c41050340a0050103600e150490315507440030940c1102400e0466aa60311000f0044001d20010710036143c084c20548010160b5110b100c1d05800c0b26000320080d4105030482c2c0764420107403c0114084209982c4444403041402c04004106d220941d2000c0002840c5141c2040c0b5043c00d0004116400044100900805180f00d00e0840b66407981240000448503810032100fa4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 267312437 1250 267311187 267311189
    0x8040506062b1a070e06070204090201110f0d18030b0612102f0406080f06030c040c0e0f12100e0304050901081b010201090b061c06240f05060f0c07 65
    0x1a0701001c41a0201040f581e0802c00011000e050000c007403507595004100d501020719402c0c00d811060600111006003403540148105a10504200800505040ca52490050300050486c1142c0c01240800715840e00000310000983c40880e042c01428190386816440b19400b0380710b140500c51001c0d8803003c4c00800d01080d412000400d205200d100440c07a01504035445001840c81541140e1102c41d50703400f500c01c110750840c1d010340c545800f603079214010505404d0000380b0054042c0078a0b120b004095459103e81c2d01d00015607151402d1180d054400d102e48008214032240c001c041c035122800420400040d840403226094030b021680407082d007203003811405103074402904548203c0002c14842400b1403840c15414100b4014207120b07003500012804e0796820100642000c0700c100203c2c0c003a0038044114403003011101513500c07800c00155204802c440c0c1d000e201c903c0540d1000795050710780c0845110500100482d1150040c940c1c100710008030244502d1031105500c0c0e10004040c460080c040c85020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 267313687 1250 267312437 267312499
    0xf270b06031006020616020c1302130b040303030f060803030112020111070b1e030f07030b0607051506040c08010305100b150c010204090608060709090c05160f0507060804050606 78
    0x2948034104248200c8450b0307041d003d48005409414006100e91a01e0000c020482c2c90300c1c1d00034010784406c00180150361100d0070000c2021034080104419410800221400602e50001050340d40c03461803c005040759601818261140d080c40000c110701c030b5000056038191b030050310302d07502800454030040c1c491801d0149012140d0041c0500054020400c6010308455440844a040100e0440034921102d00c001c60f110f842c4c0180300c4001c03e10541c0f0075400307070f04a5180034014601e88561911494941003c7c40006503111840004200c1d460406000e64003111b10035007040e41a80d411691080e0300c034114802c010b0341943e683d03c0303800402d179181040706030101020f400c010360790840385c04258041e41c010302035610601c3c00d2802c0001c0142000071054071030303455582c0da840c28509114442d800703419042c800004010060180c015040c0003508054101c5210340d00c1450340700342d24075081b410200107900c8039080c000c8034001c020114402150132644040700700c5659540c0502445a50750008a6100c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 267314937 1250 267313687 267313699
    0x604060e0901020304050c1c08161a0402030c041406150f07030302030609060a2402070512150a090812250c03020c0f01090e061c12090f270b 62
    0x100100c1d0360190b004600846c050300588240c03404c0101841140000500700e17560f91001c8548040200c0d46000c0503002240790400304200381d03011a15403140d4071080300c141080302d00007441840f0840c5820403099050300030036182400821140403841c403420b04014001402104c45014030b12900403117808688103400c114150310384614960170010300a400840d001400350040c40f000c100323145482e40141e0100e900185045103001e054400c280351054402480c00c05611510f2004645503907000b808030000507003640140400140382c101d0340d150100c0031b0510141c00c3d1a020782c641c0071403c2d410845081c10148008010700c4d450345010001c204d049a100c2c1140150314002c441803ca501c90080c2d0381c000c0c00f960864030214511020021080365201f10b6902103000c0c0c0408100800c29203104581c0b0150090560b4010b141e0309060100403000d50004642d1748020f0241307040055048120b2001810300021042c42041c10102d94600308203101e01905005c030441091004291103980200840f0b84005d408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 267316187 1250 267314937 267314941
    0x1020f1609020306040b19030b06060921070f060c030210060506160813030c080615030615300f07030305090f03011e02030601030e01051603110c0615040506030307020d08030604060e 80
    0x28030481f0380e900d8002101c5203070404010030002e1400609554401100601d84030042c40c186038401d07120b045840d4070684600486c0c0d4001100c4600f10680c030003c242c0754403900129801c1b850f0080c1000d804020201a5614152091042d5240c0c402a1400e01e01441c50303800742d980c001d04014440340240c2c1d084405100c12001c0120030400c40d98090780c00c540d03681040f40d2150316400c9529000b0907500c0006038059201c070000615002c6810b22410494a0190580313503480030407680c1e04580d924010403142c1420345010220b50208040010621001005000d050194107540d0010124418084c601e03104101c0c00703010101e241e80a512020b4070383d002d080d501e500c9900915600010390001c0340d00d940820702e0320009502d0010180034031f910881c040791004600758841c22043e401050000d600750403905051260054000082000c0c3d40104102640004582094010030040e42d000500150003a00b0500c2038900586500035801da01036401a2010b44940d90080400d00a000582c817943c40347c0060b40c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 267317437 1250 267316187 267316219
    0x40206070b09070f060c03210b04060b0315010f0819111306140f040306150506030703060311102102090d03081005060f07260301090b01020f1609020306040b 69
    0x14400f8200c0304441c64940202d5a103540950751001e6821018011402c881a0103011600c0d20f2031107034034044050b1000400c030211b1404903003211010b0700030300b1b49004000b081c414145e05c590002c0814030404d180105202644410052840401400c04440f21104581c81e180d005180d800810700281003200503504d80c0030030100d1240c05501841410b02240030144141c2e6815602d00071240b000e5900b41000e4a00340c596500da000901c4040b8070003803210810b82c3d01181c15940c0000860051500341c4d000b050050a40c1800c0c59149420310f1258400c01643e82000542031b0003410300481c18541041527985064a0f41008002e031080d0940703940d00502d032024280400d0340145e00c40d8020300c2e40c00040703c0070585890500807684030b1005006140d24080c880100081d030645c0c0c94085401000402600100600282c03641d00e8001780c200c1e8001c0f944449a03840c05503130412241184d044190000c2075100d05031024007601c100d450054000d03c1b074000000684944954010034a034000103402d8440540310b0b88 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 267318687 1250 267317437 267317443
    0x30408071d07051930050a020c120c0304091d0d0302040612050702070f171b1f020102040b07062f09100c020307170f16050d0f120e0f0406030c030b040206070b09 71
    0x5d421701801c07620703040105020600030f20030703280849101e00c000d105078080081d20440310b412a16403000d030761001300004120242c0d80d008030450341c64000030303103040506490340150606e83c8142d03400c0101072040c041080f040790f02c48140050100c001c18002255100c14804a041101e2504025401d11a510300054412404013510024140c0201952501071a0500745181249c03540c0c441948890005409900a044e0030706001c0c420909000040c601907440b45003031640c5e00b001105030b8001780c1d07454a02c004401a2001442881c004107805a0440d10780b21503034001d802020340031800742d90b07a2500030042d14012075403101156001400c68500031381d00c0c500d0440010759485d0b101c40340e008401c1c0000c040880050500b02d005400310000700013138100303001e2041c44040b010041c0c8201c0e88183c1008046064440030350302026881d0340d00b410350184101409514041034075018080c1d45000402c2000c0b807490b0140000741c0341d02000c3c0324250f84550001030355038094a000a484002040d080c409410400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 267319937 1250 267318687 267318767
    0xc0a06110901180b04170712051b060a21090206160c0e04031e2c0405010519050d11030f0a1a0c0306040c050408030408071d070519 58
    0x360f03600381d80100c58140615202c0d619115460013040c0a00c010b1040641507045a10f00b07001c41001c07103824650354103070010030350740e01d40f401e6846800044404151081e408005d070f44800050340e88074a4200e00010050207010b00d07031803401d9020700c2408510b1042a0f1f40e00300c1d030a441d400030400c03902e4030940740303030802d00d4032440408032030220710160001603035409140c00f244541d0b05600c40d10329a0215100c29024503000045000c1007100301da0305007a640d4600006600076000201c804a581c900ea030060004842d8113802c4030780708204517240b20009800909084041d503000752a1044040308500d090039040d068420070b140d01d40a849140d803400d02c0c001500042150080040178540145445010443e0f001603a041032203420400025200c0e003401d0b008920401040d14041d4a0690303945026421600550440c5403541c0040b0307010040c041c1e1b100e2074cd60320f982c940e0030b0007417032401c04100151440c1314204502c030800102c1c810440c0214015151003509004481c081022031079852811a9040c0b80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 267321187 1250 267319937 267319939
    0xd050609060301050103021e040908030a0c0906080105240d090b0a060b16020d02030f0102030c0a0e0f0f010f17011203030e01140621031308070801200c0a061109 71
    0x40e000000d40c0d40d14050081134101c0307402a00081113003070b05034440408400d101200582003501e540c50758000580141c01180b14000f20310000504840c5c40400500041403940b20304208284500103010315030b50081001c08104150007005001509080c03074442078001c2c2c01740402e220f40303000081000d01141e055128401d0100040070020310740c41c0c4c000320070340340607080d804054074030105034a00060078a51500c2c040280020121100420b0024001e42aa4001c4a603c00d200f03c0c00300700c1a400300e411810780041c501084551440030790003500814001c4540717004650402c0341c0f54410305a1140030300c002240188044281d400d4a60310307580c2c0c9003180142c035002100003a20300403ca840c1c054040c854001c03a01c92420104040c0c0c1c4520003000001440c00a00f20280c5481c40d204d020307080c03001c100030070b98500a00985100c0d00d1400304220300b0311100d50300c5150181d040051410010300741c0010403c0385d0780a0b030100e6032107422034401c013494403807007040c01409980f4100900d1800b03108030b4081d00400070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 267322437 1250 267321187 267321199
    0xc03140d0608070f03081e0903060411030f0601050d0308061f020303011a0c12030705120112020a15080a0515030d030f0b0d0f06050924071202250303110d0506 70
    0x3035590111403004620f440301070320b1190280084504c074030500310000700d5180d2003414030b403c0004108c0000d050500a0b02c0854034840c102010320000d007414407002094460f03803005460341e503140501040402c925603000500700301c22000080c105076244114991025568100c0b4900b204100101070740e81d80c0203002d140c01d0040c0b031401580420000000321a01d06111001901181c02403d9482100b80c0010f80316000340726003484440d1715000e140403040c1c0209800d0038844000503c0d4014010540c20b03e400280e0003070a0380c60780c0c030400740d0403000c560340145040400281c04d82d40d402d901700981950302069989806181c41e2140074543c941c2148071404010300b010030140c1c11190030001c82000000e0b0040107900003d15100106080f41d0143c0d600458002c10780300f650400c11142c0b190060020456160b1468a00038001c0301d9511070b42025540d11903010861800b100f4148030600a50049901354010000c8000b100801d8400e400c070342c0b119480c41100e141c5803940d44420a014000441d0740b280685 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 267323687 1250 267322437 267322439
    0x61311070c06020c0d150e03090d0c17060c0a080702160e0a0b19380a0305060102010207020f0d0302010e030a0c031d0f0607050a0c12050c0316060c03140d060807 71
    0x450302c0f6060100a562003001d04131a0106c0511150142c800d580420315580018004055142c07100300d00714018501c40d680300c200d002c0c1840c001c40d000088071014885c041c1d12080030082c0101258044412401581c14111080c0d0b444060481c47c00c80d601c0c03418200f40c0e0074071500044804c110309030140182c001c40b1050140c5805030302071150010411801103255584d0312410002c000400394040380300710414510420018041c4190b00c919002e48054031030081000440d42101607151042a400400900c029440c06013a500020b601e41082d00845204e902902020f81c00c041c000d50046004601c1130301540c1e1140c0035440301038803d4041000031f48c08a820092020510340d101400c030310400c48000c0c41c800003a41004140b1480e900180011501807158030044408680210038000040c20800c22406590246103001c3d414404e50880f20342c0280e001804a00e111600c0013021820b6030500e161682141c0902e00f41280c5540161200c00d0000d000040c0100f035a50b00c0b50001000d8130603000841c0d90031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 267324937 1250 267323687 267323689
    0x1020706050601032a050a020a0204020403080304020310050f1501030b04050106090602070504090c0e0711070e10090207050a020126150405010f0e0a0902060409140f0705070b061311070c06020c 85
    0xc44401c0118001d00e0401405d801058000c202902c1104c0d05c81c41210024662070b40400c049074016007080d228420040300b04011450200000120055202c00a00407414403640c121307007603003010704800403003621032640100e143d11a6100f40240f0300d00500c00d0019507958000600000020f004400060103425000b046900b02400740001c1d5541c0019044103441c034187c542021040064440e20402c4070140509000f060204500c3c0064810240d8a044038200550b00c034010001590120300564010320a0b503010507000710700c84000a8080c00e00b86403064500e6403024940140c0f10006c841041500184540e07281c03800b181003003003d0195010003190b600d41410020510103882075081c0000e104002a0b036109036600f02124441c40a40700500b41511240c0f88015524041c03449030024140700c0c100958008030300f5840b40c10090904000c0e03d40362060b12084168040202240d02400701da185000308420300f81d100d88004003015801544910715803a141110a201d071103014014807d0358402646 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 267326187 1250 267324937 267324971
    0x3180c060f120c040b220f0806040303050601120903020a120905030a03050d110c0c130b0a0b160f03080403120b1324140a0b040302150309010e0102070605060103 71
    0x5459a8450000c0c00c0c0141e048060b041000014040039003824103000000380c000140000e44103007003020740080300e801440043c2000c01d56043c4e004001c29001c540007003140c80c0e0045011504290035246c0402e20340ea45100588100b1941040c056140349494150403e15601003900800d00e07100d0f90304c1c03820300c1d01d005030b080746c802ca82c6008860341504052001000039000300d0081c2012603803200046140459000003d0140d0485255440a9040002050154030702003000d440003164810303040104024031004079520800f01e001c1c5d05281c610005d40c0400045503290700c4981c0e1507001500f43e40c82c00c664030300200f0f6840155421404074140784410180401c41d0300440080307030303030142030b007144d42014048100161803142c032004010850400400481c485464205002d0314110a9010b2115a1141441404522640f1894442c3d0301070005100599608020030340b607407420b0030303841d0316902e60f103d54600420581c04d5640c5590700c001340e2607003081150380042e031090600362002c010a00c0d1328902c11308 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 267327437 1250 267326187 267326197
    0x1f021011070203151b120403120603050c190e04030302090108010f0506070f030302070c0e01050324060411040b0a030b04050601020d0f0f030e12072f0405071403180c06 74
    0x3d8181c03c5103103060046529560a140c0c04141031500b0420280600c0c0310040f9940042c624441c80400e800070401415042039011403011009502002443d1450300d51589954440019521034080259880c684070070b88000c9401400b1fa07165201014141031801900a5009444040c0411010310000421007001d103513030000c50b40050003540c036080030365982d90540180e562088050641c02d00c6008081907060350780745e011300700a488180c52941018209440d0000210620412003120031030291544084060182c000070705860214480010a5040300940540e420080b5861808692880c2456058104240701d0000ba10301300501d44485004a8071454168400070108910f22001805d030351242506802500c0103103000154004031825841c00c008100da222107088001060410a0040b50311019840681402e174481c0d100b04245824039100f003800c0074003481250b941c000214800d004110003010b8103490101c1ca82d0700d01e860303180b240c01c028540400c5943e500ca0145403018034201801242c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 267328687 1250 267327437 267327439
    0x3010b0a0f0302010c03050c0313080f0c1e04090b0a0f0c0306050603040f11030f030304020a050f03100906060e090318040209011202090301060b030c030f07090b040b091f0210110702 80
    0xc20a02c1c00d6800645400801d404100c041280c100b00c0410040f03424005003521110218807109a14904800c0e586440b2051601c404140c1100701c29491300c0e03403001055240c0054090034124150b94201c005001020450350281080c0440c1041013024502d0b544419075142d4800d03002c10000e1010708045040380c180e40225a000501040810085801840e510310614880e06171142800c0c00c1c07002007400c2072044a030020080e440402800214940f102900f0f02400d000d84d4140c141100000001e9501c035002c3c66003ca4055461898805201c02500b145024141003801040181030027002640e5a901c2540c5881004813008000c00c420f02c0c0034003c540082d00c1c140d40b4a180c490410a410000b98420100a42c0c150b41c3d58100182c0070310128040c40c0306010940c0c400d40c90b0300d05180074100180d0001d014004200154038103000601710740064034140c528210150fa195040c10010a05058400040000c114104a80000c0459001a0440c440146882d0a020f000211072aa0206018215000f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 267329937 1250 267328687 267328709
    0x3050d080906100e09010906060906031a1509090703020415030302390a0f0303110d0f0503040f2301060810020c120a0215041a0601021903030e0c0306090c03010b0a 72
    0x2c1140c046132910381900140500c0c00041c081d41c0554a81c4211641c90340014010340e2552420028003005821002036140d00c8040f440c2e10b440c001c5190322005045814840c411822a404606140d1041148401440d03020748100928501955108000c411034401140144142114002070308070211400c8039071a4107102c1c180030f60501020401400b0b660342400c82c0c01c0841c0070340004003100c84a0034003000358020b45560300039030121a0301500342b1600003071003402d01a00784901c1d0082036000c800c49501941104503103e44070503038900401e005e40d004071000301600b80810166201c08042d400401140c2c240b40441d0155a55001c91500380e000d4140c0c801010b4100150310048055103e0017480442400c2c4159060604886804216954103170703002d50341010800419408900200c0301c442e0042001d00041c030700508007688088918101c0b80008003010349446001d148613804001c40b8000c800001c041d52068601105070701e9481105805c41031003913003450313551300d00d0f4201014081c050b2360111210b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 267331187 1250 267329937 267329939
    0xb0d0b07050f07150203150d0f2301051e13050c090903040b0703090503010f050f1302060418050405071203090e060a03020d030e01020d050405030c21010603050d08090610 75
    0x4241c03001c0e000741072000754150040062000143d02c011200c4503205010b5801616402c043e9400d402d280106107415020760000c402d20000b265113085901203482d44031254000f24200d040c5032030303032041082510202540c208000c2c08820b50303402c1080c0702c003003521a2808051356290780c010184410320300b102401c207400046602202c1c0c144078807042e82c04002c4404483c9825502c100e8240240d001940070750000707004500620580ca82030065a91802000c0710a00c02d5081034860100a90405840c25018a1240d00c807542151500400c0e203000700b01004214400f40701564003200a02170888080b038050051142c00300d50302c140d803030012107401e406650300c0c1202820b002425031030610103001e03a40e000c402c2503400030040c0d48114880854511070352301d2400d95002d00002914001120b142c110901030b00340400e008a8500150030420003208443c0c6039885c1e841c0580007680d5004d039910344c84255083c42c0010040c03010004d40c013104104240d4900400347e9030f80c262541c84d8001070381d0088078800c985c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 267332437 1250 267331187 267331201
    0x20a11041107031d0a0f0e010608100902090d051b12070b0306060a03150621052e0e010306021308010504020303040e0c12010f060e0d050c01031806090b0103060b0d0b 73
    0x440b80d1000d01c0f880c4c00d400c2c0301005036001a0411490740c1c070548955100071414411140c010500c180180030b641481d28240c10940802c951030b2210307010f0450004c0c0e011440752195075031a0100b450031908035050302c0c0440d072804545d0030034811406034580101004081d000e0b20850000324181100c0c01342c2c0d07006046803500e40400980340c1c0080c05c100308150319840d0710880c01e407414000d04010129500c999601403100400c10201e038024400c0043d420717241004002d80041c010565610030340880c000f1301018403010309010030200880c3c1191005041c580008410004140c1c001d10b0300c51000b04080c1003059445901d40e00f0303100101c030000c0d0107400600007080f407200400b420642002c6560341003401d1980c038851a021150307090b13001113005100c514081101540191140c0b00710f22091782d0301c0e0405004c0b51902c0c4e90701c01d460080756040607a2a103001d040c4001a1000303810302c0750300c28000c5c4104e02c050304144603955000c1c041520001c0c070f06642c200242c036201e0140e1a030780d94040c08a0001e952220 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 267333687 1250 267332437 267332447
    0x2006090d030b220b0a2103050309161509080d1407030905040c093b1305070e0a05060603011809080f0a021501120312020a1b03020a1104110703 63
    0x1062150840542d8240b1526103c10b640c615a01c40b190341800200442c2c0304082140044550b804402c8055204225501d03218007403041d40e8165415007031540e501e4981100c0c0c0c07803406d580d178142540d595807030420118840c2d140e0b425400d240d01e803564820b456141c81f00301198680079401031b1803010903140c18240003d440c440c0e019084190207030500451140d91030004c907094950720300e031000c0040d600003030500440c1c035403001e6002e003100100c00ea500801d0410b000340d16826082c420741c0001ca2a004001140100310300c41501d203c95115017502e081c02d41d941b032203c0d202803041d50711004150034038001171036908041d019a41262803a02c050f550000e1070301140350040116040640d025003040020303005030501e84001307241c181c40550007007040c803841c48400b0800c4081a040f070803100c0070740180880482d5100300c41c060110b005200042c3e884040c000240c0d100c40980d502d0007480880d0351085000d060700490f0440303600d40030b803140705102201001080304a0345c1c4259620302071b50050101c000882d01c54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 267334937 1250 267333687 267333701
    0x1200a0e0f060d02091f12020d06170a1401050c0405010c0201230c0705030f150711010606090608070e090a2309010c1e02070b030601021005072006090d03 68
    0x41c048001c14440a008507505900941c003d850040e0001280720b078a080c442c06990000c0d81401a0a502c0c8100b4000140000c0c4009100e03240290040b9101c011141103510000040c1041d659410786041005042500c1d044031302420b46d03000c1000301188120308010f00600b1310403801c11001c140303020300700320040d60310a28451040c0e04200040100c11140790200d000f001c14a1044e5080a03203806038202d0141c50020b481e00502d010b904410060850383d0340000301300e00150b82469180040d40c0d00d4190480b04544a046250030175030820b2030000e00d96030441c002005440035550b81440a0791100c0302079038440d45aa8603680c1052001000600c0c1101a5010b4102e42401801030035030341542c207191072402d04060720140841d954802c21181e070150051108580301c6220012103940040011010b07485503914071814040d801c0010001c2c2a40c1e101780300c0c20741d4840118004100a003031070380c401842070303aa514400c480410207100c5140031840010301984a0b01510000b0503d81d05500c0b412405000032b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 267336187 1250 267334937 267334939
    0x60902030d0905310608010b03070603151205150411180f07031508010e01051f080307240c0f020601050312031302010507120309020f0405010503061303020c1207050301200a0e 77
    0x80202804d810305a000e0300d8002c100180000c101e6210060400d1700709202540a20b06041c034000d101e1029940401c041402c40d00001e054041044d0341c0d081041c1460b4040464004c7c60b00004100820424007102d20b641020007070302c168980442c45c0e280109034083c1501c508211200c3c000000e02e4080c0f03e0303008594080e002d43c455084150b0740d00300d035a01303564440d0b50281d5107035111030130005c20302c06008421110120354412017041a140c5141c040c4c40f440b80180147c150f0001038604414842020701e150300e0413034130b484100490340701030304020b202c0c500f80340d59000180250307000060b003071070300007404d0b4001c01a5810092564551200c852078078500203204030705001082c401d4130041070a401c26541074240688000c03a111344d5034810000c4811101110511451901c401800030780c40c001641035015004191208155046040581c0b8180040c078440364801c4107440481446200440c2d80070460740d00780c0003031214a00745040c008400c054443c042c42030260510400c0c6205200701c0c01d0945000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 267337437 1250 267336187 267336259
    0x21c05010e0307080d0c0c0201050d020903030f0403080a030b03030c0706110a0b0103140c040606080708060120030901021606020d0c0c08070e07170609010b091c060902030d0905 78
    0x960841c80d07040d0b41100600f55103028000c42d441941d0a842d0043c9288420b0501e0407400122440e40003030818019040031410080c0d0201d10102640c0b400c00407070b004244070717440b01d40e1526030741e1905040650210f01d0360800281080b404880c0707400c0000c00c6e503410001c3c00000d407841c1818141c0403210b03000380344182c6107140309a4030341801007000d25460602070741c0a4000960340311050650340e07240c0b650184040d80258602039003045001d902c2141d954000c081e914119031030380c07500e60040700e01c0381c01302d150740c1c041000d020903029035028000001c090111003030b0252460045a51039070034002c030142c820f01001d07800004600003242d22401d01125804d1251683c000c0c5513460382140741c54981150001079102c0980402e2101c2e09403c0481440e516130b140e040c01c0d0b1140350120100f03a644406102d1070b00400c01c0441d005a841e0f071817004110050000d003462842c01d885034140f1700c02502c45184180d0190042c49851141d0f40e114a0503201507a4024010720200310307204008454000c5c81c46032000c5564 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 267338687 1250 267337437 267337451
    0x7050c0f1f120507052a0604080c0f010f020d1103011802090102030d020a030614040507020d0e0607020d200901030c06050904181103011a090c09040b060d200304021c0501 75
    0x5115204583c0244c241c0e542d62521003041c003005c0c0705240700f203020403185100c05c07a118407080240081c1840d03103d81e004003411703294070700030110788d2600900c00303030148284d400c00703802481c0d03004140e01819040205a0040c072402980110030307901844203004100108071600405510307070740c803600140041035040c8112840c01c00490724150407030b0803135020140040e8499408100c100384c0f050381144600c0b81164100610300342a88065078801800401109002c641741a4002540e20442501da2645c2c000c0e00c4014401c1c01d03403600c0000307955202054030f00c0e00041c03071202c00241490b9058034140c83d07000d0010600c0508041007a11581c0041c3c0c56140d005445005072040d03842061080b010451150f40071212540800c0101425100c0c0403503000400b041c10707142407c1d603a0340c048049401c101062061a07807000c890010401401d4000340f1705403c48800207442556440c0d9034000c802d8440f402100c10b070b8418042c4c1e0159464481910041d60081d019040f007019a01550f0740c05144034480c01c0002802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 267339937 1250 267338687 267338717
    0x1a010512060f090c0a1202121512030c0313060309030c030e04150303120c081303080a090b0907090f02090d30020a0b130c0e18060c07050c0f1f 63
    0x1240304588490713000070042040e07032429410813125404404941020744c02e0641c0800809907503003000701211036501c405031644100351110b20820155100c0541502d641d011120b903c0742c1c3d254403e1251408940031900d00080761440f9100f03800a29a00d0ba0303460012600303a0b01c045404a103002c3c02d0586c040d5807092090312104000d450003005509c281ca8030240e04070306d80d10742c02c1194600540207040c8840501040f840100089000c41059498200300e21b10f502d0b914820700003404420720090018050302d05104520f900002c1800440341e10440034400c044504030054164000c00005542118000103c080040c084401c5001012000e4516909180200414410140300c03190700d180580c100e40c0041703050259200c84a0b502022107043c40091031899501c07400700a40621610302084060004038444a099003071800e000180c2004940d0700382050782c2040301356400040b00301d0f0300f4825203d5410860801207054554600000d28414034500795900c007441c0058200c50710f200300440100c01e1000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 267341187 1250 267339937 267339949
    0xa0f0e041b080a0c090b0d05100e12070f0c090603031b0302150106030b0103060807050d0809060c0109081c0c0819060f12050105090a0b0604090c0806090a05011a010512060f 76
    0x950b40c0111308034010589004a4881112126803000b4010b8542e0341411012520006030800080924032001072419204500310b400c0427102c6a1540186c8000910042409040d2610704400c42c050091110b44035610780720402229002e100040106003000700030f0440c118040710b80c07000640280180d032807803103500803280c182c100c2c01d81148001c00c0d516007d02c1c0311542d061017184003408800000f001d503035003400c0c00905040c0081c040213085140015101c20151110800c0d038821440d000f0091140e00c000c1d24042d54250450001140c56840841c541c1c0300b4110310f4025840b0204954654031901c2d110066030707071030070020000f03000c0f1755035214400012400b120941081c001e12440640c07011112281c501035007540c0c00a0840d100c641d1244a00a001c40c0c01401442d401c040100d4002501840f85e14010008140c20b07440700d041c0e8000e51007000180320300403a110300500e00c120000c121040c1320030300e0504003030810030215002030414805111a45902e92101d500301c0402070100c04124540740c00a48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 267342437 1250 267341187 267341203
    0x6011a0c031c0e030c1507030209060a0c030f0c02090414011d0601150503010302011b02150316020f01060620012004080d0c0809040504030908030c07050a0f0e041b08 73
    0x5000642c085080285241407180f07031482c903552009540b034400d128501c641c2e60010445210000303840030001c541e40300d02a504503581d1140c00303003c03e9254040e0300301c040d00070b5220b0341c41a0b01103030320560015007051003500c003000900e41c000d00c840026200c507141c1c03111f402d1003c1c80720b0f59031b0740d40e074001000820807440c2c0c00600403c2e070030018a01e40d81001e52210760510324946513814044c042c401440180e80003400e11007450864100000745416500002d90b5021400001c0460350000005000c1e03400c14000f111056441143c00311411003052017203580c201c8600340721b00e50004840c40c00c07511843e01d910b2845c00600a00f00d0004c20b52040c9201c0e80d82d000e18840410420500b000141040408410300c61400704480a0401000b481030980b92100c103031103034031900d038840c944c1c560020302054002c450600c09040100222a11828449121950f41d200d40c01002d1084803005000030381c000400001c0c0d81900c6482903600c82c0c640301c950761040403601c1d41d54400d84441014401040500c82004205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 267343687 1250 267342437 267342457
    0xc0a020901080c1203250c030204110a0e0a0305030a030f20070b0702060f07030207030c0b01062c0d060207050a170307080f0421020106090e010207030905010c0506011a0c03 76
    0x18004010310400c0314510002544d40c2d02e41e0014414400d00250321041035843c00c440c0d81020038020720500e401c038007104180d00001d50003850100c1060340c450614000d0210034107280c5541c001000030000f04071f403400700c2d448020075550040000040c400e21940140b001410360300c0002c1007442441c0c84101c0c25400d02608008003460200c2c00c2814030503002d61755908040304d40058106400c10302d280c804580710040010f018160009100d4081510030b588054585402c24544c100071358442400400c0900041c584004240c030308070f01201c100c081540003407285000103140fa2241c5020343d84602c081d4100c0e5409603100e0141000c40030204d9007a0548003641900400460340d80d2910042c007034184180a410100031201c90810000051250b40c04900c1d42c004014908240e98500c10049016140b183c101c070b108070341002e0282d6007815054000d4841c06104c0e40b039070100691507800441c2c01040c200e001030403030340c02400100210010f0300c000f1801c1c4850518128540688a000b107403a42e44201070038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 267344937 1250 267343687 267343693
    0x120d020c0604080c06070f090b07170a08190b011b0507050a06030f061a122206020405100203030609040f05011805030901020f16261c02010510030c0b0c0a02090108 72
    0xe5418a007040c0482d41e48448107003040401401000c50080c440b81450241280d4500002210b0060001c01600152090103480be8a40ea030041803900074900b00d0240d0380080084021400c8aa045865008900c00c036441a07445010808041e018200c0c1049980c0c020784113402030000119003911224482d2002e811551070101d080c01050b00c3c2a030464280d980a6540c4103194020511290f502c0001c0716032700e0316030261a0743d180e11140540c94501a0901e003102c00c1c03403a1441070a0030001150058812500c0c03c1311203507100c1b100c41c5000c0c3d03181d103c125505581b0440650000300010821030450440a000b04000205101d5003901001007030002d03101a260359002041070000c569040104040c143c40c0c250240c00642841d1001c0d81303ca5003180101c020110701111035036003c040e40b00f8001680c1da8000100c60550b0013848110030602c0451807648019420f03c1c0000d0b90031034003280b01c00c0403654032201a003607803860004c800d801a0801e48032104140240b03402035002d42d0380c13450000d019010102c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 267346187 1250 267344937 267344947
    0x1080a15060c11180c18040510060201110309030406050a0203040b0307080105121f09030c02030a0c0f1a04030f020301150f060921060e0307060c020d0305010801090203120d020c060408 81
    0x44110f040c440c20401900c01e54100880054000028860582082150466a03103813208090307066900602c810361241c02c06d140000700582100c04980000840b000d07070700208075000d01c424404e8814401107401c05680c0d84104020448c0078803480c020461202c013841500e08150b15071841c10050b510075510706000a00c410014080f500d00500c0007070b00250524000d04d5032000414016150407100002001c680c0e513240d080005140c0904031b2080050f0707005058481d0045145446044001d06000c0c40c0b0030800c0250000c2a0010042042000c0c0405c0c8100340382000d2466407840b24070341907000c1c102e8165480e500c4a82445148a100801504d00e10304091020760510000500c00d00c0a40d0060702c0c01d01c500050f8103141c4680200d030162440e009200820080c0c0c110b111140b851040443c0201b0540ca01109070206990101d203001427074410f5070b820701207039a030350700700f14283d50000d1006076058109100b034550983c004401800c0d8000b08036005030901c07c6801a40d0706005c0102e606590306600016 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 267347437 1250 267346187 267346193
    0x20a03150b1201020a08010303260f2502030d02071a070309021002190204110408060c0301291b10020a02031e070503040e0403020a0c03030e091602030901080a15060c 73
    0x20407080c50704042c030002c500304604071000402c034550610015003030280c00c00b0700345542d0412040311a014645100c0c210020f0424144400100c0c1040ba0300e010035144006480544210500440ca02d9200075401075084c02c1c12020b0030802035020380703403ca4102e80a031202c50516030303281d10708034271034a01a14002a0096103006210f0040d91050000046401510a4903e010120401968200c1d0140c6001900b0202d0081e950030034895034119000902c01c807010800510b0f18000114181c610490f04012940ea2001c2100502c403800008015849401c2c00240d0b41c810b10420168141c0c11140700315260440d158900340100d80c00741280c01c005800000707450074a00030741e452586200c0340840c41c40d45404020380320f403034130ba005502485c00412404004901414401c0048240032600407150101b51030747d919014258003034407005180910881400180c07440140c2070380300310000320742c7c006d0b503c0c0500380b0b4011120004010660803002e6a01c03070380103000d00080c0412f003002c3c1116840b2004880c1140c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 267348687 1250 267347437 267347449
    0x150e090d0801140a062003040f0f06140a0305060a180c020708060c040303081b0f04080c0f010e1512090d020601140a0302060a0e0306090d0e0d0209060d020a03150b 72
    0x103000107000811286540e40181c540c13518082c11591545800030300c1e83d40856401040d07000003a649680e0744800701d40842c50340400d81c281c030704880c004542c00050540d03610040e600a404020618048007007072240031002800794014660104004020001c001c1e04c808400c10350341981024480c1844e0b0320b0b201c0140054040024030302401c0310304001c204a00d0140d030500c60314170403800003c0801080002043d000000809003042c000e0401e00c4446d181c0c4442004050160814483c0100c035103d451503010070340c1492415045500310682d03c83c2c446a03511428818020040b8145034080c0e00c041101c03c04c1c90101503580350141e80e030301c0060203104101001c001d14010040e0000f20b150503400385803040350f6480b0245001103a5040e91156211003d08405417062880d150080e5050301805040100030000401c010010505035140d8441d0b500e0f5074410300413080d50b030360701c000d4002c412400441e1441c03502c0f2159816851004080c0c4213540d880b07036201d1690744800346002528684410040030145884 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 267349937 1250 267348687 267348689
    0x6040e01060b030a15030b181906021c0515041805010e0d030c08010f15110a0309050102060705070803152d0901090c020c0114040f060c0c0e060d06150e090d0801 71
    0x1080c0c06000d1b0458880611f200e030040c0190440c0300484440c41200e01e000c1c050b441d00352a4a000004401c0300c0e0b4104040a0340c0400e0a1400c090342034082c10032074500700c1c4102230240c10228107160094451109000080c10002c0b000458448109200000100e0034003410b00c982992001802940500c6400603003619561031400b414441c09100521000c00480b001e1800c6a0200540b0b80380903455200c20383d180e100000703440c080f40c0207145c0b0700e105040d0805507034400c03100c080e070881d0461713543e4030002c494078024614014420725080001c15120701800d40d0749240201d00810011040440b181c5086010201c180c2a12120034100401140d07803801150007401041000c900748901d00c8040c00003511100f0860101341800240c0c1c00301a5200c1450044e10054001142c0c801c05450b02d42c40d01802803584c0c41000c83c0c14610f00407000c00c8031880d00400310700516015084200344030302e0f65107420141c41e91004900c40040d0840c400030340368036102402801000c100c0c3c0502465504020001d20f50001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 267351187 1250 267349937 267349961
    0x1409010b06030a0513080705060912040b0702192111011e080405070506130906080703051c0c0602181002010506031e0703051501081c0905040506040e01060b030a 71
    0x1600c503a405041e2641e6084a900046460002580d59100100700303200c240e9800d0040d11400010805100700840064060b0160294000311050003007407000032b00d06031055000d0200c0081092107010b0050501034042200c00403881c000d00a1207440e5140341888404610814001003d0b0303640d04000d0100d007070079003020b110083c07a1602c0521502e10501c140e081040d001c0804001e00ba0001805001082c080880507181c0140ba483d900c914001c0100021072150148c182190300d000e0f4000b8a02900080150450307a0000c083d0401e0302d10040c040d505031200d80802001d201c2c2e070781108400035a05100a000d00e848411301402e00081035003d20500d40f04110200b001e580c94003091245555000440c0c44020f90048440d80303002c4030800c1124200300817a800100b00741b0856005181a007680100305051f510078004a07a014a00260f0180500032000f804401103000142c050101d07050a070001c580c46507000d072000c200f00400d01400b0782100d846a00907070301d0810110074000c0b00b1355103010708025585 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 267352437 1250 267351187 267351191
    0x7051312020a0e0c0c0f0c18010302180709080708150a0b2409090411181014010509062101050604060203040e09010b0d03050408010c0813060f0b060706140901 70
    0x80d2070303000c14003a4216028621001c080d030000500112000f000f110b0b01c541c5024255030048070030b12001da5030f480e42e08910a00c43c1c1c0c2c041400780c074902a81e102441c101c0350000c0504244510002c00d40c0c08180000e4101c07001c201080c440800c42c00303802c000d848003e1202c0c034028501e1881e038486028546101405410b03116003400b08910140d03840301c0c50b6000f04403802c11856000d45022807000e07003030710400c1132194004070040204000d101000c24440741201081e902c2070b000514400e8a181c07026822124144501000c0c034040c010341c80c0031002480100e9040c10f1084c81c000300b860020341e00307400901c100c1c40c8940c3d10711000000030404405c618014038041d9002403c050600b500603440e0b000d1030094500600502000841030007007500543e0585c1030103081d0745250000d80c14014116032150240580641c2480102d00b6450b03c6802480d20820038450040c100d50680d0756144017401104c0210421a62503034544a00351341d0701001428810320590000601c2d090319900c00801400082c8000c006034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267353687 1250 267352437 267352469
    0xf160306121101021f05060a09050f070809240a06080706020c15040b1b011104140108090106080303010b13050402190c051f0207020117090c01031a09070513 69
    0x11081c40d40c40c1c002c1c0d021600858030040c410040346040c101204001003000c11002001903520143c3c00391380602c0003952640740c180d8a410020040d07440986651540310881c100240241c1d10440c0f525810041c010162408681c1700301000d2800c8546d0356500c0a001055400e00001411521800004100303100103010310601e8041c0103504c81c00c0c00c1781c0a80c001e070307050440d0dd040f07540301c4000c5501805201c40c0d150740700c0c03c144620481160018410203003079803070001c0031241a4120000e80381116102414038482032a407100440344c000000e400611170f5034860703901191600091000d94080d01c85590200d0b16105c0504080c941c0500e254449809940b0402500703010a50003840d4801070303185820005c0c0e50340c2d00c5150140c0f40404516107900c0b1000d288082c5848201103400912046000b60b940080c2c5903101d922071483c0580139130b1006500da002404845280d400b903048002d000748104807030f0f4882e1042d00003003240c1c09421240c0a0000e01c0c0001c41c0502c0301c1b4200c80c5000a01194180e4174994 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 267354937 1250 267353687 267353699
    0xc011410060509030a05010c020a0510061203050c0a020406030327030b06100203041e0e0f130201030e0307020a0f03030809160302011407080d14070e0906041a03060f160306 76
    0x16460103150100b20000907a12415107040190310400d643c4000200480c4a01c4c0c2c1d4000d4445141c00002c64240c06034800410301c00105010344070542c0d00d00c0c0000001000d5554080d6060351204c0e030458210701030342ea041005a5100c2c03249000441c080e441d00038a02c4040070125401852800c49604141c3c4d2241c014404181054141f650048050781c40704800818400180d2035030095501161080340841441c01d42004c512a80703000301c5102080c1143c0c5078171082a40c00d406034084452428904040041c2c10140d882500603480b1040c05d8020760f8030f000400d4020440010b10340c2c000c02c00020410000f0020583d10417072403a03000a00f032028006040b6001160194440c0d02d02c0080d0420000311500320340d06014104582c18184d000700d00c1a62400d485030000040e203071450386845c00070f031003400050035140944d400741c43c07404006040380001e94545e002c000003841003808040702a04a0585601d5035103042140e14005c40c1c0c0e500445102d440c0400c0d02c0203000e240714800c1001c143c10140e0030020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 267356187 1250 267354937 267354961
    0x2010218040e0304081f0c111911100e0f060301050a03321f0501050a0b030c1201080a050d0318020d11040c050a030b06030601090e09030405090c0c0114 67
    0x4403400486012030b102107000b103003500d14080c0707070401d1042d0700400b42e1110f81d00100c03440d030001001e00d0300710030300c032602c5421400e40c0c4c0c9100d50400c1c0040da030071072000021480c00e10f208582070b50b84607060041c034203220000800d01d403100407110348000c03415203124060b481c54000f00b4600004021100c0030302d10340c14080841c0901000e07110040c150205101d0880745142c012406601c250b0800700f142400f00300103a00c1d030350740e010015040034910805000300c0080e024203003e00c60681d00d02600f04200145480b04904e00341e03000502100b00c14206120300e0300c440c0c840c016410300070038940c0001c1146541314142103042019468507541410301e0211211081130185d0f400c491101d804462103011040141000da48000781c401c3c481d6802407a021000071000c0e0400040c201c0b549482c0c0d0104052030240003841146d1005856050100302c0746081049600b00e84802968030901c1d07441580c0c202039803903000c1100510207490701c0d03050090100b400603507084240304081c4040709007c03240d180c2e420a0b03003e80107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 267357437 1250 267356187 267356227
    0x210050715020a0914010c0506061917010b1201020901020601060f1101060e0702010e060c1e0705060a05060f040203061f2319021209010503071205090105010312020102 74
    0x414050003082500c10300c1041c200340240000035840a6643d41a0448010204e114900031000002c04048000380d09501c500d80b02c0802030340c841c000345042d4540300100480300b03140c02c201c1c40482011140100b4400c0c01d0b00300410f8020240000401c80c8070221042007038100384180b0045660b03105111001d083d0b84d00207446811200c00d03041c2030f0540120b5110441d0701c41480186983d00398241303c0001081418100300b079100e8a000d82c002c00441c486507003c01d880ba035094410419101c0203005c0380c1c00303801603100001e401d110540c804601e00705007a541c01b4200101103070211141691101000000c1c01c00140705040040c003200c0451842c0740000028802c122204840c40c04030624020b4199180d001c1c19044640080400c103401800e0031081184c400d070392280b20508501802c10600580060000a0000c901516850781c141001000801110650001028542000b00800542d4038407292441814043c2006000104640d030450404a00400d16601c8500c00c580c410811095400c2d20386103545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 267358687 1250 267357437 267357469
    0x1150c030807050909090709150e04021003090c0f0302031002070218092d0d210c17070c05010e12070b0c04030602030906011a0a090e131202010603150902 68
    0xc0700d521051021221402601e0f603d54000d810034043c00101c010000c0e904c0110398292109000c034442485c2840c3e4843e01920681c850400b801380070500510307054132184800081c5140003e526000c5071601c840c1402c159100c106d5004102c04180b0540c1002e21903040e01c0940385800b946800c00a5000c01d220a00641c110301d008ea11000101700e4205051021004019044135400c980d8092101000300359450804484442e05c180390b07000c8040d5006a0034580b2498032020100046809004400c0240001c12002410852142c241c20100c402940e02c203400741200366588030000c00c5529019003112064007600c10b01d41c2c4000c08900145690104540780305501400c3d1009940f40c41c0c1e2030070b0650099810041c1018004001c00c03201950024065040700c90703ca0001c01a100c4048001e8000c1c40368168450006810217002e01c181440d1207509a0441041640b110300c4841e1610743c00c07047d01c2d4001010005075102d080804c14081810b00185401041c020200044003866002513407100c0c04100e11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267359937 1250 267358687 267358697
    0x102161e08090105031f181b0801031502220e0708010b04060c1a1f0b030405030702010309110a0906140306090312041a0109060f080a3201020d06080601150c03 70
    0x11000003200c200121111308180807191b2007511501c2c2c0040c040094100d54a845140400c00502d10007500d417441c030104150b807035400c0755900755103490a141ca06110360361581034080042040e0420b058a821a1564902c01d1090800c2e0811200030007102c00a051134040002c1900180037044038441110b0454001d414501d00b64421841d183d080310241004030310100c500300c1c00704104a0501c00383c0141c810017515200c4503c54681e68081c819001c01c1c0c0e00035080303607c1400050010b50080d403008203003900502c80610800146400280140003d07005078041e951a004200034144ea10300303500c031104400b14003814180c40c001510750750324041c500c0381111741419000880d00b4449030286c0070b0342145203899050041c3da1500c0e00040680070520031121541c00d04600080c4c20741c0007090051900d6404071843c0400184a58400111201c210038800c0360000100760600d000c10910040201c443c2031080807238031302e1404000604020b0140d0004421590180c2030400e591791089811005ea5418281 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267361187 1250 267359937 267359941
    0x103150b01020c12070b04170c1c08090d02030105130b0a0605090c0a0504080708011401091a1201110703020109021c0302030d0f0b18042a090f0e0102161e0809010503 73
    0x139051800c41c0b00d52080c061a200010b020403a03000741c150310000d221030082200d02d018101c1c02489000342d032882040c04c44030480e0408000051201c0e0040044100c000e0042100c00d441d80c001908584094606652455602d4016410004c01612055000c002d103001080302529210100314a80750007407001400301000a80d43c3d0483d4017131025030740a000200c3c00c8414250b1528200d82c020204010010b612802520002940f40c01030b002d00c410714101510340c020381020384001e00460011a10382c90700507540b01c400b2400101c46000281900b18001ea00110b520030550050100c0703810240142071740c80040c031120324042a000821603002410741c1c00005a00300b0f840d050f480051003072182c10b03980042c0414000341900c0d51048001d000f0390241c038030358501c075010070200c0c000f00d200140841d19021900204018201d1075034004041c403601c0400104030028800142800c9a00110201c1c0009540341492000d0000072604540c0c1d641c500d0000400920494480c08902e000b83e25980b8100840000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267362437 1250 267361187 267361219
    0x130506090414040803040b0c030c041401110d0c0b180a030f020c0604060503180c0a0b090301021b03210906180a0b0a0f0f0908030103060207020604030c0605030103150b01020c 77
    0x1015603000c15100b407610003281042d01e401409540152020350700e410085010070809036854084034000c0000c94081460149808103500b1040c0c7d04004150512002d150709450b081820701050910058580e5903141840d494a010b4101e804080c08107002c4d05a185854601c640700000c0c80c0c2036403601410302180481011000301d142c044880d030103c1d000755020900003140d64100000d91700489001c507e80c08045c40c042e609595441080410742d62101c150310042001030f00410081010003006400507180030074884002241d528880304c1c1c2d8402e54400240225910f000728070100c0d48038094003094046051030b450346c0f40d6880d0041c020810301c0101e641d03170341401c050812210702c2c2550300640360340c0180b80402000d40140b5600e1140d42055003081c0400d03075403181a100746c0300d0155001d0840c034290703401d64950300d0003500010401c03600308508100101c04105940c0300580148156502e181d030300d40c11840c003185407400e0300c0004800142070449a2149030380100c0c40f841b6842c025111440e0300c80b4011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267363687 1250 267362437 267362441
    0x40b0c031603020c011b02030607081b1801090b13050f01110d2007030f1e02060f09010207050117161202042d2306040b04080d080603031305060904 65
    0x21003544040c40c040d030312107000c0580102d24900303841401d0b00d405030b00c0743d02200302c1c820111906034001d41c5504150700284155026900700c0340c11003041d8071241350f41190b0790408a01c6620440826103681103144102f0040d69001500c2c001504c4824140c1b410034030854804010880300d402982c0c03051040d6005ca500d203901c80c2e600314480042c00b034121400d40b01e4100024003e141c03c6030802080501000281c06c1101c00080d040088130340c40b60039160011755544811005e14140203034200080c61003168180943d4074440544241c1032040d40444e41d690702517001900c1d0400951080c0d050109004000031800e044003d115401900c030101c042920700c0b00b0004a03034081198076940030251001ca80401d0181603614810880c4001400c518009000e512890000b00c0980c031858040000103540f0030702d01d900b06081d40c5195440585280e003000c4e202c03400504142c0050304444416840111100080c070b511454003a004002500614030b000144a050760250340d0328058640601d80019415260b0f031159 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267364937 1250 267363687 267363697
    0x50a031709210d0509010c1e0506010e19050408041413020f0715020f03011208070503030c22030305191205091c050a021504030507060f0f0f0203010308040b0c03 71
    0x1d025440c00e0150441000242c106446400c03628854001c000090078001d0044807009903050310b0314600c0c2e4450382d030380451000c00b0540c0007141c44110285d00d00096410031041d400380c07442c0e455288003440e001c1c240920b12113048900072170036401c1405020204086c01c0031541a5403040100b0100d440b143c4020418840401c55400811031000805160103203030304024080c81c82c03045020041927070211100c4020780c000c4240000c00d101003080100050241d00d075410000500c14100c85040a00941340e290950300f00300c4011600d0400065520304070f00340f03007102150f9401c3c0c0000c010421b60458400401a0041142c0c03490001001044c0e081e001f40074136000a104241c0c01000c0c49149400b02c1c11980700c0c0030105d5010006451003242040e20740c0200161903a01e4515030041c8680c40400420002c100030182007034051141c01c00c10080800c005005200003009842c60100e0100c610030743c0d45084444005518100901c1840103100082402040700c0072038464002c11074494003020203890841c861 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267366187 1250 267364937 267364939
    0x50607030513390513051e071101020a030212091903051c09060b030705092503090204020705010608070f03080d020309190b0a060504050405060412110d020c030f07050a031709 77
    0x50303800c0010b4107150071203c8800751003042c0e03001d926039480400740c0b500362002034841001e019860a10004818a5640d60b42e510262034540744103209000c0d181c1c2070890b0302106d04180080c0e000030703003905020107002c401e07a0007494250050072890340070902c14400d030142e1500102046000111207080340701a03940690900701c56a02004408100d1074a900207080c02a4490b02a002c3c070800050280303440e0090b18800c09488419080700269605078071a495031800300c070030901d985d55200501507100d500c05040040e2140e00002440c2e03082400541c645155940803070030f02015007406100041b044401d950340e0000300d030005a1683c07299001c0324181010019450254402008204140003030342401c240214031820003002842e0701c420901081d501d049802a010381d0104002c100000c3c1c603800558041301c07040c5481d011800103100014200840d0800c0940142c0c49100700d4440f51500b4005000340102e44802030686070300e0b010214648503130600c0060491580d4218030328040307030003808585482c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267367437 1250 267366187 267366263
    0x1080a09170c0a152a0c08030415060b03070f1416050304060806030a0804060e0103110309030c0c0a03020d0f06020d0507050403050c090121050712030c050607030513 73
    0x480040e802e076541040640540c1c150b80190300c11500442c640c481c100c0803141e00303031540c104c3c0c0c40c510f469400443d0a0600440802c03004010b410045a201000355000300d204021011041d00c0d00c1054005980c1c50b030f0881c800058042084c4580203030403c280c0d01e01c900241c00c1c00090071365212000030f541c2c040c84032240c802401518050703040207004802032098580d95103580041f0b880304014180d4480c07010000500b40701d002c000502c286030040c00000701d5104140f40210380c0c40c00e4183e9141d0395070000c3e03550424503440465191007445041c05204171600342520707520f200030300c1c50700010036002d81403a01905449540d0750301e5040c00b01e035804417485401b000000703110504000c01c0c0203180d80c0c018030064400e4000c144c0f10300d5840c540466547e0403110310402040b43c040885640c1c040030300700242d007151144105200000ca0080c100180603040d8007903142c00d0040081810240e05180c4014444010103207403504002420001100480314980c101c080010740812021050460f1002603080d951451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267368687 1250 267367437 267367447
    0x81314060f07080f010509010306020d020d0608030a0f0c0f0605180714100f02060f0606090316031e0c0902030c0408010518010f06060504050f04090c0e06030d080601080a0917 77
    0x3a221118a80c00790b415550b809040d90340705501d401c5042028001e00d64000b10400040000c100319401402d590300d0602001403500014510a40440300943d019a80f19040801c0788200340e40c008000f8004414142444400f105c1c05030f80b161004d8611020082581f40d996000c18500d0300d0014001c800b22800c20100c45c0e0403510b072140c042441c01d807041c10074410600c2c840e0f503200462190320074401212454009003443c2d00c45044800315200700401c08c640055051001c00d040343d504100d20401910b4425034080340ca401e50a2145030401c64404c622881c5110072000030006030b07500905411501c90301d4006072641c6811030442c43d141301d03d134070070a100d608010a104914480d00a4603c4010405008204048000b800c0d04295a5640300702c20100d4424082040f00342480f000305219813000601c0024a01e82554510b002201d031508400c090040303800400c62607003010480c555840240c3c0c01d00781003500d00840002c00400380100240348003030b1900c0c3c0344001c1141c0390a10020608104811715190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267369937 1250 267368687 267368701
    0x30803041401060518070c020613060e03010e21031b0d0f05101508040204020c0114181501090b12030a1206050a0e0606070c08010c050403020f0a0608131406 69
    0x1225101c0021180b075103410b000151034076000c2c444c2c1441c1c1100025202c00c69452a000f40c81c5468000802d98001301c2c1080300700c0da0788840341c0c1d84001610507511400b11501c1900b0505084807540c00002c04143c1c89a500452010201d601c1000010401c0d0081684c0b41c1d642158101c181011020001140fa00807607400a2940150031016000070540801c00c040c9c0c1d200c082e82d4032803100300d01c102000703c0c06072400024010320a40151340c2c0240060700c00743c9084141c001903400c4420f0b00c1d818030104840007042c000e00003a00c0c0c48120403000e11000a0541c50200d140c203103031500061003526560750b07480c1074940780b503150080f010703603c001c400701607075200c1281e180050200b40d00c041614020524040000c00c062030021030510a48202c100c00b80342550f221004e03c00e169119450960b00050036010028240500b4000d08103001c09940d641511079255205120141070f45101c114801d502c080c10034450300d540721000c1035001d01c40c1c440924031001a4180045140c0c10310711040c400b40501d00402c810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267371187 1250 267369937 267369953
    0xa0302030402040c090b030105040f0b0619110307050c040207110405090d030e0619150e010f24020a08090406030501060f0e0c0a0f18080624010903020f04020307050403080304 77
    0x400c1d40207490500400d441d000c0103c841003d1801001c0f0346850500040c0b041c1c0c00c055000f85c2da0710301d80090005100001c0c20005401c3c1e08800098502c9074120035800c40615032004a841560741824001d50400c01180c3e00c5984801940b146140903613408038014007400b086500351895090080d00820050034241549916045015000400300f401c20f480800c1a002c00a1144d115034602058140c0801705a43d40d00042c00030001442034842410001050030509501094020300100403c0003d452800440720842100050001041c0305011401c0456503000704000c00000e50140010b56151103e400082c01002c494001600c19860000042000c0128400c00419125403603100382c5503540e00c01d680c216620948e129500002c070441e41e0414054051000160f0200203481c07420501d5440702200c0e031178003100300c2d1003071400c55a6002000059082c190903ca504a003880c01e070104506540104012200302254980aa82d0000000340030794420400c0c1c0b4003441d40b00380c07219070324180350501c541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267372437 1250 267371187 267371191
    0x60f0e060703080f090a0305031b070b0109060503100c0e0d17041e08160e131205030f01050108070e010c140105010f080c06031e13050f0304080105010b0f041809020301020a030203 79
    0x204c80d20100100d60040d1002441a103001c2c0c1c035540380d6185640304901010240512900d428011100384990400a103240441034041c2031800e400107100e51810f81018509000d055031040307514586010318404030ba000c3c84280c100f0105543c2d9134010740356464298030b2041c100d003140c51743d604089008100101e409400030711081011624041d80d03501e5651254440c48440c1c1d00403074200c0705000c108000d00203410340507030043e15a0040107155990b61904ae0b030f000c600090642c0000d000000f0881c80740b01101000c1e01505003031074100f0903841d00040140c52449444c078a41c0c140032050a400040060203001c003c00c1420000003807005595521142c0ca50420b980101140c9001c2c0c1041e0000301d061040680707210f144006600c0701c08042c20820700b6503414000c4d101d4144000c6100c2c0c03400c04140c01700075258101c0e085400650f60b941c0f0b0541c0701805c485c0103810501540d882089940200e00c80c030303000e88003960008050a00c0f90f241008400c401809841c10007505540041080a02d041c1c06901540c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267373687 1250 267372437 267372451
    0x80c070609090218010c0302010b04050a090b1e0c090d0c03030207150509030a150f090813050105031302012d030c030b010516141005010801052e060f0e06070308 71
    0x50000d81d1200b1400040c0d0060500c1480d01004032240c003074031588511268410103000c0d000018400c511078011800784c4004036090070003e621b402880b010048460740391540000d000845004091011901860941c0c015010180c03000b40452803420540c2e9601240705100c2e030144513540d95035600d1a020351a4450740c4182c0012512108a40b00000d024a04031004040001c0c09082c00304020740d034261036040070f0340540d0341403543c6070100f4517400000c0c4941c0c56103034010144151108011001d04403000c40581040741000010b0003072000051040c81c601e0f0710039a0900705008039044c1210142d03141c2c1c10520b049008010724240d200e00d59a0513500054502e48240d401b4030008640200541d41441030100900c0040c402d24403c80c0030603864244002041d65400039102201e400b41071802c180c940070b80020000343d540301c0512213010500705581c003955200548118044810b015005562110751280d5002d20031245910094148146404061807100030030154850b811420010400c0700300311090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267374937 1250 267373687 267373697
    0x71409070206010f030b0a0608060f0405010c090614030a090209070503060f040c0e10020f030a020f06010e041505070203070206120402040b0105040510120b0a0e0405150c030610020a080c0706 84
    0x850362407480414020f042c2c0c0c0c202d000748214980340d0f03611805c141d43e00811800c1966542c1da0041042c0c2400c1c41414000d240755105444582000d0500c9421580300010074014002d28200400440b90054207440192503440701d51a140c0d941c040014000d440f02240003544490079108015500340c20402840c000c45003030312416628504c100c1808111440301410201061a50092245c10700d000260603684108501c195580000b0582c0020301d150040340040700560456901030300c085c4010414036006102d480c00300845402c082c0c55045582c1850207840d401c0300c1d22900024490ba000300b0495082e90b0b0b000d80a2907072480b1001d0812054941520100c2c855400c00c12081910761050041c6c0c0c05132200201401140788100a040d82c01d50001e11094001070b07101e0010700480d40d00c00b107001380100044c000c40c400918091a0031410546c000059440c1c0081d40024840d02c0c10881c400e03258000001d032400350301041032000a034900100658020140800014015035084011601404070b90072074441d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267376187 1250 267374937 267374941
    0x81b0703020a0c0803090a0e04020307051c02010201150e13030c0b010608060306060f0f060706060f090204150504120213090f082706121305060c03100b09030a03031a03071409 77
    0x49685c880c801c6802c00c0380e02681024081c8940050540d00d260400d10080c103c0b2400c40d80c61010900312081c0c40f40101d2050420403118003956020300503113403c48090b00000161609106860000b01d50281c0090748018014035001c08150086080082070340d0000c105848542e900d01e40140b551104840e803238064042c1c200400d1032814002c0c61400001001059281c003421030328140540e68001590540d69240c032214000350360391088680a000c1c14111401590700c81c208040210040c2d0005610810400208800c0007070b2000d0051070400130343d040f10349070040408a120a0027410b05000003030220303c201e10341041003081c100000c2a2a040c2d07000c00f0310300c2c200500740080c0c030b04400540c0d280c3c00000801c86484401645414143d200307402c02c00d50070091074262950352810208851194104a0000600c4503a20303400800d400100600c0081c5450580c0b808042070710b40040b120001c050503210640340042e0120091024010a0007800b2a08100c2c3d81d0882c0006e8030302ca101085000c3c420b8400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267377437 1250 267376187 267376199
    0xa17101e061e03021201021b0a020f010212090907030b04021c06050301021606020702030106030f0c211505180d03050109060b03060d031215170705010519081b0703020a0c 75
    0x150072030b00c0e4204a1801c00c2d40340b40d6003d202c003440d004001948695420007140d030214102e4080100701c010020003d188020180c41400703c1c140703e039101507048d98080f5403080007440c4503104584030310f0001d52751442e00352100b56068021f480c002d00025030040c004565110184a40c3c1e1b81c0d14116490720805008143c0d40d101030500b01e00c0f0f07030010382c0030440091030400c0120300c4540040118034400307000012050754a031142e488400c5d683d0b40890391102d43d07050801c01d00103022000c40c41c41c9801013100000140d02c1c0e956042c0c081100d0441c07030303016484200282c041412155811204109801600c9500c00c078030341d000300206000d01034101c03003a190a40209201103802c041c0c0e0b2280d0000741c101c002d20700d400d80301a00c8824010500a1074162194003940c0710722081c82403280241586032210359001c458642183c14101d040d0880c504104060080400d511511001a0225055818118416110030210f01c01d00640303000b100c41b0590000030b04030209640002e942c2140780c0111040c465442d10740e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267378687 1250 267377437 267377459
    0x105010e09190c1a03160207150c0c26060108160317130e041202010515010f0e0a0609060f020a02010c0204180209090319050301050a17101e06 63
    0x524800c005074020720440b000c041190120242e11409072400d10f00312a552440540200c03118203000c01466004828801c00504070207030101e10300e90600242c80d1641c105030443c4600d4040c1c00b0440300700141c111401c81400340301c0005001070041400c0e54241c10000c105078090400140c1c8407001d041c890880001802000410750085010500c08101100781c5542c0f240c1d607440c1c4d202008484d4400c4e04201080b60500d95074002401030a0b0101610103a02d00b0f03090044030300340b03050b05c2c0c2425a414082006540d0034414242002c1d0802424006142252a0002c42d01c1e013001b08941d64100e401e450012070620342001400c8100c035071544d1a0440802041412a00da550070080280440d401144c200018549030700154411100d00326070300c66140c02600082c0d03280605854003042504002052900c1126599400151180c10305282d0700e0b40d4540404218001e645200d0550f60b03e50190700b00b10080b006002041c1100b00101041c0856540c00d00d8940c001000c454001042500d0110700280c143d02c1c0c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267379937 1250 267378687 267378691
    0x9030708150105010c050f01061202090a0203040201090302100320040f1203090306020f0903190201030507090b03040b091c1805040606020d0f0203040812030f0108060103020607080c07150c050105010e 88
    0x48000d001d49070b46810015158152682403c50740d80c01403441c04d8091800920924008084003410400c0c511003d00500c030f00400003800b1107043e40d0040040002603600098501d040702e40c16a041103900500a208a0045c0341042d000480c141652a248030a507500102910030b64a45581d2400019540e00481401075024603004002c240140d00c1040890030036070141034072800f0f02c19120303e00b054100000e82014510b81c5480308c1034003103a49603401d552b814407a10742c0c00441818804685801d2420109141c00010802007581000c1c800044d11450207011400d000d030700f00010440641c0303420b8000f07410004a0600c1050200418400088610b0540030b10401c4903c1e5030042c0003006203c840444199250004800642c401040300040c2d2071020040e4000d81c1411080c01c680f00e003400c1004500c4e00806074080d8209510502c0144056650181192141030340041c1031555004500d14190420f01c0783e038000103003e0f60b040300425545030415607550103030340301c0c2d00200f03e2603887d0f5100524000003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267381187 1250 267379937 267379963
    0x90c0405030a0f0f1a0901060b04050d0f0206071a04110411030703091a070f140a2705060a090306140702061302040204030b27070b0a030f18060209030708 68
    0x700d000e0300040f0b01d0f40c403030560b26076008041d84e02c5140c1194441441906a00350f2160030601d03250108144440280b2500f8058410386c001c903840d141c54040011040251b004015128030f41d901c41c02c4045540768000c0741ea1081e409142c401354092007030283c000d441c104035025a11081c80302d107016841d14146c820641e207000003441c000c2c21a212400e0844c0100304040c0129500c88071200c6080180d000f00030450300c10242e59403250654140e403007000b0a43c070010005506030420a1000c02c0300d03036400051403c0014502d00000c034081280015540030401c007a070006800c100c001070318a580f039070301004900507079000b802e080c88020140c22195a0b264421030309140160443c40c046124a50004030b5140b8407400280b0150600b5281c2d103070419a6682652560703c680340f44000441c03000030610102131000b030301c40042c002a5217010742d501094494005010304040c4c1c1c07906a44044a2aa44007000041400521924500321843d16600942c00f42c90f81501ca886811000250544000350524050b25 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267382437 1250 267381187 267381193
    0x152a030f081605121e0901060812030907090b01020a0f06060e0f060901052412040506060a082d10050106030609061a031314060a0f0614130e011a090c040503 69
    0x40a03c044c54030300e80c0182ca08400d0001118000b040c048a501c10680141c0810000284442c545a80c451500c7d60100c050303192030b9402c1c4104012807401007a440101c9803c00b1020030350520f500c0040341010080b031401444064258040020b0200aa00c0704090703582403e05000e2980b6a0842c00702401c00403281a40e1003a0742000522150074610032001d4080f80c480300309456400c0c50a8111303800e40042400b101448400001c110038481c00b04110354001d0404e9801003c240d05080040742c0b45d02415a085601e4001058060400c03004a282c180b00d0340c0044007500c0d00820020140d0340540002c1c82000002402e15074040340c0e800c2d5a1180008407101e203100700403684452955400250001841100007084500b040c0000c9210410100d40c0344016402034010303441c1c1100d0f2401120b141c0c071948006d05240c00e006000d80c03020a140014625022128040d036600b502d00c100e0701400e10071500400715420030243c40d03c500b031000c5a01d400b005003140c8400040c3e580b40c01e45196401641720361903140e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267383687 1250 267382437 267382447
    0x30a14011401030e1002040e160c0b040609052d01110f07020d14070b1902060708061207031502040302010e0306150d06151203020610152a030f081605 66
    0x2601a900a0018004504c20741e01020500507460040340c04c590701c840c50400e0607e003009501d041c0c02141d03c0c07007004c203802c00303046100382070f2540442064001c20061100d41d91700319003014040c1c1002401010042c0000981d131200124444440d441210002c001d0301d91300303042c48400e400c40c02e40d0075a0003081c2c0b542101410141642c0811001d4000d504050301e150381491003100191100b0310441016026110300250703607054007803111180411041c41c1008542000043c4a11140d1110005801c54801c88002c00c54802ea00c481c1f034100300203a8001024248100200682c0701e40c01e0700504200c1b4001d0302c50506642c040030070305459580844500e9000f11030240c41540500d000c1030740c448400e02402c80024070090761141100102d04680000081c6018079164004042d810043c80b030f403010100040645007071400c5501c91078405217100000500c002c00c1010042a00c10284840f02c0e000200c44905640b522030502504101c07030350742004001200f07040081c0403a00c1d8501c03d21003015056072a14036107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267384937 1250 267383687 267383689
    0x1d010e070302090c160f06060e0711030a030908091008070212131505041d1801380a03080c120307211806060524090405040c030b010605030a140114 65
    0x3d917204414030302d40c103560303d514a80840e00300042c0c90001c600c01c1740009011420004144801c3c03d0080c81c00e020842d120303181e12001e480101c1580c40502c100d042c041901c8526240101003809814141c1c1d40041a451600178030980c0150028000c0c0000c4d000d0b54030b4101c00e807207005131910910030703582c4c100e10317244008001c01441c4422043d00c00c0c1580c900142850b40354600b00100d0300021a10482500d5030005020820381c0c154081c0301c040445000803c5144041c0011959015004110f69501c10306400f00340b4410351019000445c4580003000c0c40213840d124503081c900c42d080a140c40c200c502c50786441d0600c04458404880c0200700c0b0f511030b01003400b4451885103804400c5240d44071825103641201c90720325001c0006c2009a40b04401c08615181000144640d4204000703051203460700c000c8080b058100c0c80000c844d8644c1d425a07010a865590341440c1440c08480d07400203002c0c4180c600009605a0b004d4040d500407004000d060004010108038003501e040e0a009449030360414002e82495 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267386187 1250 267384937 267384961
    0x6020c0105221508060f1206060405040c0906030506090607171506120c09280608060d1208070314060906090a0f022b0203101701020c011d010e07030209 67
    0x10250401c2c00c0020030607220044200d51005502903840800c000c8000d025491800c07602a8a1105050310411148656900070345d9030f9000240689000d035640f4400320b814400107118002c0039100c42c41c818030030345030349251140d55604205c4850005004041c04980c0f5144141200460b56414020446550320fa0000c0108450740e0503a030070b680001c0420083c0400b0001040c254850754801d40b689455049040c1440084020081d10724102c2c00c60300700140901c21014818000e540b401d152403105662100003243c0003980d0a20f02501d51140309104e070080780c0c3d01844d400e109994582c4d06208a005108101220a00a881442d40440c20f040000c0c0c1c3d50a0810500341d01142945010070441c00340c172007040803603211208490701794030f1079401d00d640c020040180c8a01c0d811403100440ca1494440601110f400e101d018a04490480055003e00100250182c584d4506010001c01c469803c0b01c185030559948104107074020b508003112580301c1ca4000c1142c008480c0c000e03059524554440f412210b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267387437 1250 267386187 267386227
    0x230403080c0a0204090c03030215090d030b0310020d09020a14010c0b1e010608070908032a0f031206040f0507020a1e1406220302030909060f1e0a06020c0105 69
    0x100380c854444002c0240e03446014528171280a80e03080030150381035040003404d00c10180305040f1045020b00138441151000100300014400324a0002000405000000d003048107101c247c4410390300216002d2035609003130b805110194400c940f1301805544d101e90f0044045107500289010901034100100400c092030b0400e03511403201c000c048802d191150032502002004e8100c013001909030001c011299420500c0200075110b1000110304048a220038000d83e40c5440c0c62054101607040b410403800d080811030380440000c20701c01d4a859448d0a20701c0340c40d4540c01c0720810301c00c2d41860980700514009108050040900354090300d407006280d1175140350811500b002204800921341c1000225110344645d41141020710003070081810807010f120f0500380c10f05030403030750310804103040c900103070b000021203203800400c1d034401096036030300d000040d5042c02c40201c29070014101c0702800003410210101e00000c0c482103580020440d1100e204994660748885950b001c101e003000380703503d001810040c0c20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267388687 1250 267387437 267387457
    0x4030803011e080f2515020d110a0f080a050c12070c0e090307060b06040f091e060e010e04080418090b07020705060d0203090a14030d050903030c0f0901020a0c1523040308 75
    0xc0c00c16a40c0b4054850416810b80804006800c202000c4071460b03403014452710002104801020303840d4240e100c02e815104031950042c171701440000c03c0c4060901807010380d052507000c0f00540c1c0482d126a00d0b04102c0d0f50010328100c4810658900210303400000314003050040010304020350822060380c4c1c0313200c002c04500083c1c50307100e081070000185e500c6410103010f001d00410200418804c038030705400401110421040022242071032070601c0030080a14400307046a201582d843e100c1d85503030900d15414406c1d60440c8000c0c0070700c240300715034000e10350304048280340c4101c0070ba84041e03130750082c01c98492445005d0958000005c1249a4000c0d00300d401458104035140c040c1e854088075070380c508603110540804c0103ca43c001150320b240204032486003581c004c400f8400f071491441c1c180352181141c400c80500001d0a100460483c1943c1d01c00c002085555a20001000717245450f5201c10007051610311640c000070f1003114040001c43c0727091076001c521400d441c0c0c419050600f1980c440400d0b400c149401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267389937 1250 267388687 267388753
    0x30c0702130f14100302100f1701030305310506070c091805060a0504020105030c07051905160f0f050d021918050703020a1d010504030803011e080f 65
    0x1851034a841c5104481801c104250005a000c5441c110003450400040a050508000000401c0583c5a2601600e4005d5036460003070001a1014019a440c030381c0385141d80741c0c0300f41000000c020150400300800044002e0380001540021011140300950a03805000f0a83c600800d02080b80d400c1400140c102140b15111440c03440f41c40382452021248854524000c1416401d01c0d41f081c00018000b83d074000183d0a0140014a49900040c04501c03001d01a1004c0000014400b414030900b80b100c02204e40c1c10006810524202d4204580d441c01d41d0030001512840e0b0080c0000c601e00140c110000700d410012200c92018030b018100071411b02c51900a98014062403000302c88441400c080c040070700218088285520b8075144071000b260303002480c00050603c1000302c031510a40040c0d6001c00d41d1400181000d502d01c02000403181c6010704d40c002026600c02100104200e4400d5107400c61880f05448841400d03a03644111a0340c2d0066050b0800041c0c0000c41e980000040804410891140d00000c0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267391187 1250 267389937 267389959
    0x20714060f0c0a0215030f06090c0909040303050601031503020f04090321060609050109180c020102250b0c040608040b091903050904050a05010b0f03060d0c0e010810060605030c0702 80
    0x74a01c8580e110340a88505604010000d07030031031500800ea405001103c030701ca141035203801d0358855551007010340054462105180007030748020800003213031060000078150030703002c2c2440e10300600501000d8a105000ca402d04001040c1e40402024403421680c00a214010403500d0106101c01442007104c180e081103401c0b000d0000c1c01100180c0b461414807000720014a25160440041104000340c000c00e04201504070100a001e00b481c88809a40788232060005903000c07100d030280d0091245c880103d8942c40766038000810290201c8002640c603010b07179051542035488c0d141190301445980144800f00d00c2d1980410302084188003450b501c0440c410072119020b1540728540d204800c1d0000440025100103029001030805015440c1c000e0300c0c007070301401039504000c440c5039140100130502c2c840200120000f911a0740d05841d513450036401c0304504180903110040307440402d0090040c280d042c400c8114032610329805210b4041282c0082e81e800341551a011504c500c282d01448040c0c2c0c0c441030a0039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267392437 1250 267391187 267391207
    0x11e0f0b030d0203071511090103021308010507050705060f0403140d06030c090501061b050705042f0c0d0c0308070c0f1b0f060c0503040506031305030703050403060b1002071406 78
    0xc50715009102d40c008544409251904000c052450140c5280281c10500d140300981848401d4a0059100342409030725880e030001115640c11060303000c44199801d0009100e01d494011000f012114060410303980c065640861007507041038140d40040004502c402a200c0343301086005d0304540650f0030002c94403550300d03290020707110304907004129815682c000411640350405c1c924140d00144403020403149116803516600d81c078071807103250b004a45549403402c204954070b54107004010b41c6064078004030341c1580407030625007080716000340761b00c01c500e00d090396139000765040741d050ba5040d40c54032429620414100c2d460002084100d0302e000041002400040710201d49841a66582402c410128a451134500c4e42e000c456028009000d282c145840115001108a800b0380304192003c0d80d0303d440c0c0010703090302031403080720161890002140030810540e03c5402001100d00aa501744003001091081002040d6841454000b59010b070000f00002d00b01d513001c54480490081c0301d941071440c01c038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267393687 1250 267392437 267392443
    0x3070201080c0d050903270906191206020a080c040e04061e02031620061b040b040e1005120d0e040b0d031112030c18030a06021c0509011e0f0b03 64
    0x1036101240e40d04040781080a543d00d120030386801001900703801c0b00e07c800c1c040104080c0d02c00170744040d000d01d04074812074107414400b001e803d00030100e180740449150410b04004000f504901460710019424202042c00518800c040e80c05803441c404009059441d0790b6684802070461070035503c074841920038408990034032480a9446020210f070080420390506038000d04205600380c2102041c004000308481d006000143c0030360141c4009130290804210140a00860041d54001d0896041c0080c02091050b000031b1418000c0c03c1240780408090f071600e0820205200c02c401400c05540141e0390001c01500c949078141d1482c4000c0d20026101014002196071013802090541c0070074079204407084469000c06c0b10140c22008011501d04509020101a481e0703c1448505443c00e40b094904100710b98050041400781076000104641e1408101c62651030b6003003402c14004180e00d840001901010180640100103207590344402103882d6031003200300204081030841c1e070299a241c80300e8031305072010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267394937 1250 267393687 267393691
    0x20c03250b0403030302070215041805090a0b1905010e040f030c0c091d070504050403050405010f023a09051f03020d0207060b090901060e06090c1e0408160803070201080c0d05 77
    0x1945d405a5260701c02c0c0140a6100800c00c00401d00c034804000c104003002d04403540d40811401b441e4041882e445175076045192049208020b00301064420a0000204d0049400c0504040094050045030f0b60f030311018080c6201103d02510b003101921070180042d11540c020000c2e20f110760180c0414907242c08450040300c615a501b014643c0b80511040c0100320104070900083c5400c079000d01c01c501d4a6a0014002e0141d8411141030081c8191540d003014002d204044c5260317402c4034004c42604c0d030308850b0100e41f064540c10019441c10244100c0e010b501c00d0300008140c0b14064484e50f000c0d0300080100d80c0b0388580d09900e000b01a42408105000c000c58001001014003519010031041d450b07508112a40c24003400c01c0102e0786c58100c041160b8914601c59980c08881102c0f170b03c45681e0741c0001c0c1c503810700c40c1d0082403840e80d51240d0314031040912003001c0c0050710f8003d0116280c068410303001c880e440c20140500d413540d502c10b0241c86d00544c407070f0365140c0c0d200f0380480d001c42c10000044042d8040d1407003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267396187 1250 267394937 267394943
    0x606020c0103061a04120c1a0405010306140117070507171809010e0a020a050d2c0a03020309060903030c0304060203070b060618042f04090c020c03250b0403 69
    0x6606030005640e414090710000e450310b80703c142d88034142e03550078001d60300c618031400130851100101c40045c046040c034203500034800250800105501d40100c1d030011390050141d10301080c60720380041190030f880c084c0288240d1040e141c1c04141e90101c5001020250010b04032820071104008860000700e21840c40310315076030612201c80e100d4800041c4441c0c01d044030012640203c048000411000d07070403134510354002c1400c18005a4a81c6d0005003100c0310b1085ca030304200c0383c50802c1c8248401d00c0350500710b198040c114060142140d9282c5c148517499a000c058046c005900c240403d0f041450210010940b4a000908403458003240c0c001490030754105901260160304003180403c10f1111501c0e50562215084643d030b881e1044846415003c041200d417030500a6a0703420f104000c2c1c05000c41da011030182c080a03603558801102c0300840041e071240c02107800e214140580750a00500000320421940230040240030100174000c0000c0022813203903c0642c90741403c0381c0000743e110360b090081002e140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267397437 1250 267396187 267396193
    0x1121b0809010507032009030313030b090c0306090a021c0c060809070b13030b0a06180911040605180408070b0f0a150501050a0c020402040503031810080421030f060602 74
    0x1d440e040309401c48000401030f406040c2070034400080f5403540071081c884402101c0f181d0ba01c540c030410219256005d003050400e07408030002c00100c240a00420028030400303038102140c0d40710030700700103142e1038003000e5134029004ea018241c0c0b007006280c000507460b06883c603014a04202c1940d901d0ba00c41d01d0b00980e00902c046100a42809281d94050260314003030000340310180e190480310b6118603a00680c501c0054000c018403004103000c0b14098100c540181441c19405102c200c1c1100c04900900d0a58411180b0110100388060141024024801118401071400e012242007480340c021122006004a6035140204503110014601c000e503180210700c6264883d00b0792600c80c403d01c00b01c0d9950400d41a103613199060421481e07074450200d0700e1100040c42c112140e840d40d032010801070b000c0d5800507903060001041400c50707290b0041d00c1050f8020101c51f4802050302c03890083d18002420f6501401102e0000c1c1000d55103034041d0f0080321500e03241d190004620030512809403c0751803d0b0004001a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267398687 1250 267397437 267397441
    0xa050105010207060c02060708160f0302161e03080c0a05030d061505030411060c0313121703160521040506090106080309090103120302070f0803011d01120201121b08 73
    0x5681000800003504c130314201030b11080c2d40b940003d01c150080d80001010031400040801d10b218940c260901d1082c0d01008500301c1c0070541c81c01030748405000d40101c03000100301d4000501c050300f80a04c40b002405008094500909603160800c25a019941c0294588103c1141c1000a44100010130b40f80d050780c01c001840301c2c14520001c1000e4807100b41841042410300600000c1080c180700342d200c002d4202c1d101035444001c0b1240c40d066000c0c1c01c40e4408100046a000201d60b40b40724200079184d44034103000070580c0b4004694405034081914106006004000c80302403041c0204000d101c4041e100d8511038003089540d2a03a9404441180c0444080e0880418803060010900800e0003804066016604243c00d03407010a180d0413052001900d0945802c0446000350301960440d8038468028525201010650400c03551641c8203120308407211110380240407815085103811410384501d040c05c911200340c1ca400460703400c0801c03800501580d43d5035a0300c0d40c01031011602c0e200c0b040b09503145da1810b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267399937 1250 267398687 267398689
    0x50706030c2604020f03010f0b1f12020901030603080301060c15020a0e210303010b0703090501080c090f030f01021603030f0506030703031409060318010e16090e010e03030a050105 79
    0x5101c0701c9560005000c01c04200710a0550000090090a442905020030981d240d000040181090000240d01946007049145a04c0c0e000e030009000e00310250740250201100d01c420a00703003100110800c001903018000b03c401c04241d40c0050460b103005143c04a0015141d4441075201d80c0300b030780204042007980140c1020482c603183c4680003514400303403c504054640c14064a5a00f003100803034854005105000039241a41840e4060038103048100c036165a1a03070901c0501c1e501a0b0002d80121740031440c001101d6126524492003600d030500c140d8200350306481440141c044018180783d15000380c0c0c10b00d6600c400d092014100c82803140d40051030513141e508014045400714984895440e0078041005080d44000a1007011243d051501118925101c02c4500c0039008020a89030b000e034000050001138003d40706010300200e000300080084504010f085540c58002102c80d000041c01d4000401101d00749a0069035510882c500204038400c01e5410103003580c0c0200c0e200044141d8520040c452 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267401187 1250 267399937 267399941
    0x11409180109210e040603020603011a07060e0f0f0706090e060d120503010611030f041a04031e17160206090a091401030b0711060c030709031401090510090206160303150305070603 79
    0x38130390150340c00c211031070441c1c01140d018801401010445e66200f543d1201290301c20086400c0720340c02041c1001070351040a4410b4075047d075501d401c0300511070009842c0c007844d808500f00c01150300740d496102d02e9616150104601c403500174160341d40803082c80591000310703050168000c0501d01380e0351003942d04e40c14558040d24800e041c2501200702c0e801842210620303803480040780c0941e843d00340e4801141c0c16071014204248180d800080000940360f81401c214203107004031b980d0309445810501d40017442d0035100f00c081d000c0d04070782c4213904600f0685200903050030001083c0c605000b030805242107488154400c207aa1803c000e081580c00d007400100300307000b051140c041d04450380d0f2030081d090400e450070851342c468000d044003164100c000040740c00240110f540300021540000d0101c0343c00c1240054034003c2c1708010702030740e86015000a01c4402d0440d031081000c0554002c2c080350500380741107042280b659968908500b45582c91102503041907400c04254010b52180005296213400c3c2500182 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267402437 1250 267401187 267401207
    0xc32070915030f0b040f02060f040810091208250207050f0604060804080d06051018171009080c03030c07060c02030f1b2107030801140918010921 64
    0x4410501c1c1c80081c0001004000c0101c1c426404c11904a035540b102c2c20502c089180040c0d00940c85640003401d6504400060f01600c21100700509484415030710080f03c0d01070301c1c01140000e00b5031342c200e1030400405002e401403a810040ca4680100e070007010101c40203024003408a59005603221a104200c24600780840400d1a242912034a00b45407030484003a080c910040c0c0001c1c07401d100414141240b4920394004401048000e224100c0003508240151020380d0005038500f035885420341c04110001040414071590042c000100101562400301000400c0503140481e0884401c0041c290241410000303507002d0a20303101c1030343c0c0c4c1d282d1743d00e0103070200c0d00200522000e5410070300c104281c1d07124000c1680d40c0007502500d1b64511401c0c83d81854240400d002603501e41c42907295001d00f1166010025201d841c0c8a42c50384070442e41c0398074141c148404803003070b80c580c09500b0304c00143c080d00714110728000c81da00e0400045510380c40d580e240710303403a0440c0450080301000400d4800210b903222500070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267403687 1250 267402437 267402461
    0x1b1302031906060e13140105100507080307200a0b0c1605010603030e0901080606030c042703031d01110d090314190e011e031107021e0405010806070c320709 69
    0x10130200340c080000300a05100f494840d425050380545220b010350115032442d50b02c14481903903444c0ec068040d007084206003411605520049d0103001002d00002d898014540000c040c40e40c59a0b0200801007075072014a03449038202c2010b0741c150004100340210000396109490b48445221b02c03109011642505074004079240c0d0000e4240a0180c0b804500001c1030350081d100420604008001d42c00300a4620800d041c00000603107001d02410b605a00074000c40f4586a0038600561200c4102800d941201e010741083c00c0040119100090003a8000d07480c103480f80c100311030f81e441c818092407840c0d0059001480040b808500742c2c5070302ca60121a81280c8030007400e146082028010010580c403001031902d405050ba60b022105800c800c800945000a90041038851900e66010489685134021180303c1d0046041000201d095040881d4041c8102e0899a800103200040d440d610b0022650b51002c082c980d20840161040c4801d8a1003042d8007929000241503c914000805040703a1340070b0600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267404937 1250 267403687 267403691
    0x9060d0204141f050912100e010608370807050c09060a0b03360703050f0111030c03040c03171306020f0a2a030b0103051b1302031906060e13 62
    0x80030304045038000c5043c1c01d452901d0000d40720300c95480402c65081d5854110312071031050083c5000d004183d0380007061001d0301c1c1c0c0001d2002980d240c0344240c2d5004103d01c1d200500007040c5016454003402c4160302104903506a00c481120270380c0e1181c0007582d2006400740c540d900f064040d04481d0500c911180d800c8801a41c000c512035240c012200100c0c00082c000154848442242c031090604412400d0030180e60f41c034000344002094840e2a942c0e44140c8411035840c05484003050580c4010b1160b4015803280883c158038540c0c0b104c142103109d50004000f02d800b060041004008a56080120541428001c105c155120701e400350300d800000560384800215400040b00f0480c0d05800300d4004c02990b8800c5c08d980b224a4910369144024041016032201c010300c1c05000424440720340041c5040320b001e11b003a10000e03180396507108990859920fa0641200d00e1200003c1e000182e40d0045074010850300d414408283c4101c0300b0030a5038015030041001880c0008006400e140100d040700706401c4158007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267406187 1250 267404937 267404959
    0x30f1e0c0405040e10061203021e03070f03020a0605070507051b030d0e0102071e170d050a1d0904061a0103020c0604061e020a080f0a2f09060d020414 66
    0x24020359071240e800780740d015513203030408014110020420100c40807100c110902c180d0352a0914013196000d80303139095005100310486840390044103220310701c0c4001c051028500e03200c0c541d100d1604102400c0e80440461160060b110702107a103d01c50705014840969071760380d6544540c1441031415100500403950341e05990301d0708815540000341c1200020840c10480c04615420005030f041c09000d0744000304410507015001800a0b840c01c284041c0d60100d05002207090f8800c99549e504d503107a0b041100807030b0b010404400c4c0d19004c2c41c1344818941c4144920454491034901041d01024180c404803400b6458110034144002102300c044c1401340c3c2841d0071400c1012600810b40d440310050b00140040e9501c3c0e00c884518800d03c10b190000c007140e060306650f00c0c1c0c00e45a009000240881d00b10079204228004580707548064090049807034007ca6101c50a00d8502201c1541c00c00180b5003884105810481d81282d41c9802002d0140180301120058581d45443c6006801a080d0003401e4072034110018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267407437 1250 267406187 267406201
    0x70206010608060f1c0b1602060f0c1b1006090903080c070f08030702060a141e060a0504110c070e0412050d0213080c0a05030d14030901060506030f1e 66
    0x5845811107505250580b071544418022841e05104400c00d0341d00304400102040450f010324400f10401031145d4842c01d65561078a40300030017407590710701d060010b80244000c034611607801b03c109a080740340c1d40c500a03d000d80e2401080d080408104000e5800c1d042000d142c04034010501c41d0000801c0154424080d00515a4004100000003001c500c901840070600c881480040b05a00c643d540d4407a048503684c0c14140c1d40a550b40000312050407083e4103002c00803207010305110303810380a04c1140300841c003416a0100b03d2031117850010009504000c3c0c882c80018180e403140980c000341d918095001d81d035000e800059074101403082c2c01008002140605210005451269000c14640b0f04e00c0c20039203500300707891400e010703110b0b400031441c0803401d196000c00d4503a4046070341c00c45058100c442e000c01503030b11414541c69104400d5490040b9210808405101d84060300450f4080061000058415140c8000440d02d17003003a10701088010001342000540241400d0589030070317240c5134a8280c2c0d0300d4112 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267408687 1250 267407437 267407443
    0x70201051612150b0703050309061521010b210c0312040506030406180b0106030e06160c020604030501140f1e060105071a07030c030b04090b0f090307080a02030a0909050702 76
    0x4222500d25643c503103000c102c203038558610801800300e800c58660748404d00d040080084e0402d842440d454064100410481d43e40310342c01d103c86d090003074500210031000001002c00e068041e042803034127540300d050707043d01d035601c1001c0702c0b2007100007864003a569090380e26001d180c03040fa5007402c2c1c082d500c02d00050318440c9080040d00c2c2128030480d21180c0d6039a40b8540800541f40f001070080c8a07400c4050b4490400c00071081e89030585642d80d40c108044a0400059a0741d9142613454946400c40d404121010300d1181507104d010f980040c10a903e40f40e965030300c0b18215410f44900310303040c000031010701107510306000406410441c940c54604171004821059402e2603009030049040c030030700003103810800184141000300542504001c15803490a0700780a0058141c954a0400007840c107428025140382034401c801d0b01c0c941185c0080c645658076403111005500140906045100070f100c0500041d581c1c1d170003040c025031168051500c1d42d55825002d031041d140c036017000b8842d40c2043c0070440099800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267409937 1250 267408687 267408707
    0x1300e100e07030b27010510030b0606070c0b090f1309030e0105040605030a150302030d02060f06040216080702120604120206060a08030d0504110307030c0e06090f040303020d0b0a0e0702010516 85
    0xd84070118005001c100f4004085e6a05000d00c10782d401e140401c141c1c5420407007000200c034040c40d8240581e030380d0f050410081344100c403001405621382c1101070003c5054000500300107138002d030151003450402c000190340303c11404541407811b0703151001c0104255100301440e900d43c40a0818600f810304203400900780e80401000551029903a0b030205d50005156120341c0c0c002d64001d4252510f94005403030094480c20115110860203a402d40840c41c141010f1003103ca202c00720481c010302c6002103694042c0143e10168050380d10181503074409842c0c40090002d10b0081d0302c034002103404492581000f0782060390043c1224824100f14504114040780481201e100c002c0882000440307940d9860803240b400111a400d17a090f2181c1c0e10080104a0404400c4055415070080b5004a0751070104004041c00304940f18610705261002103000a8004c1c8c000e001e10106411001c0350040416004c076042100d035a1214070762800950a00281c16028401c031900121b81100303561080c48100e4020f4404480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267411187 1250 267409937 267409951
    0x30f0c0904030f03110c01020a0e0108090a020103090503040e010f030c050118030b060d05070b0406110a0f0f060b0d030f0e0102010e120d09060c020303090d0e01300e100e07030b 78
    0x3080c5200300c154405e0f0301c1240313948465082141c0b1080328042450007500555440d80102c2d00e8122041c00e13075800748103107612948940307000740800107071540114040d101c4010100c4683c07005000c08501c1800306514180038040910b00040010b01c0d6041c102c0c0c50640310b80c0001c0c188071f0403040c4503005c2e52800c3da0700c5080e650040700c08030580d15450301040c00444a0740c4054036074003074030001180365508240140102c0d56195122a450102620216102c030368426004011104031484d25000480c0d00c095108418003501c000a85038075400c01265040d04a51821400602c8400080c0e110303c3d00722961640745031080c03008026101c51480540c2c0e50b410703052440c103884080442c038141c10740140c1d045090034603802001446040002c050107035494000342ca840d00d40d4003c03004040c0c2d04510415401e21440d07030594600c0c602c840e60000c02403140038902c680030302100c00c04001d2040100203000d00d103150320000b030060503a5140a210341c030031034000295181c0a60085401007001c070750341e081c005800c009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267412437 1250 267411187 267411197
    0x32412030912030c02221a0a0602030c030403061d010c0302070b071d04020904020f1210051509060d020c19060b0d0314032509050102060a020f070f06151202030f0c090403 75
    0x1c1c0d8079041798082d00f03a210311b00100700d0030601c85c115412110aa07030b813240030091340c000072080d444038026a00c0b0f0040042d0094a6407007404100b0114005d50409c21b4140801ca60540f0528604000c2d1803d607001c0c003c000012075000102d68081080448405500c400b07507160112040c0d003450001c2c2101c1a016450710320031500401c601d08a599158111340090f04150061036076440d03100d5214030510b004850007066240354040004160406070b904140b82441da06005150601502c1042016005401c040d40e94507403d00c0910449402000300452a8440c070b910050302640070b10b058825180701c1c4820754010f000e0b1002c1940001d030400341c0443d00189214440c1d48903500e00001407210200284040e414a039111301440502c0c2d000343e9020103503070080e400e03150070340d071660440d005034496410a981044002c000c3c007804150040001d088144c41554007207054081070300d11090444413500315a1100c56610202c000710f00c0c0c100709003824081e0401c0138001140f003220000d49180402000682885 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267413687 1250 267412437 267412459
    0x201050a081f080c0414190e2109090a06060927060e220b0f042402040603140f040f050c030a060207021806060307032412030912030c02 60
    0x10900c000501c01c0d4450b1401418059910034a0503611419400e2240c0154540b04400d0032041d406c1d0b04a901c00c030001c4401440ea001c1a85000006080c20344001b03070300d03000320031860000f020b040d5040c00591400007902603c0301440c42c2001007028005d00000210f61030b00904008250700107940500310340c10a003190b0440340c80030714510404000112820301d6540f5210700440d44035590381d101c600940d40d501c41d0390303108410b48400e0914401d8001001e44041c2d2654000b9200e02c6592408a0b801413055011058540242c0000046103031003141c401d1030150040b80c103100240c0e0501c0341c0f4a0401116810104500f0441486507000700e0140c00604440c103039104c04028004108010b030340c1250090116584000b01e0f0800344001e4011000480c800d00c19540c5045802c0c1c4e40e500c2c0c280c02280010041c51964072006000c1c0d00a048420714210021780e1001e201225400c4982d4680040048441d02d00c0c0340191403600400384681e503005811850300c440004404a40c0c01a00030404540c162001a041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267414937 1250 267413687 267413701
    0x12618031309050103121103030c0901031e0e0d03140601030504031e0305010e0c031006080703060f03080c0d140906090103060e040609110406080a150e06090d090f030201050a08 78
    0x3601c6282544000440d007440001180d030780503071041c0d0482e0300950044158201c00001103c01d4500380000e4220740e072040c000b08800040100c014040e2280504001034103095001040b001046124060707032030144d0710140415407138420300007090800d446150811143d10342c22410003a00d48090007150406a50320f00040c1094007480ca41c4204910602d052000c10a00100050182009010f0013a1081c580d10100f10038885142c03d5034060404040f42c507000030f0034000c084844041c0100040300701912650002031045c1498290000f0b14014902d0a58415580e42141d25000001001004010f0198600714400c00c0503026508499811140650b40e2405080120b000e4416600300f40e81060022050104002c403d07445088880d2069000d003d00c004080104406c9840d83d12400b465a0880205240012070184240c0700c01c24801000040c51030310a0b15103850701c80201c1d030090240d8070103102180410f405c20a10700060211000c40300f08a811680000d0590280070040c5007800b6202001c1500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267416187 1250 267414937 267414943
    0x306090309080304090615031e0b0105040f0b030a110a090b031e0108100608071404050912042601050c0703120605031002181c020d1401090f02012618 66
    0x240b000e20210f030b40b25034032011120020045481403215540d01c1e071400c0003040740240107810480780c404818101010314105494003400c502000030307040050400000c5074900c040c04030f40000c0c29164485580300e00d06003130b6500484004520400c202d1360248941490241e100340d0903004d48088280c015280d4561908602040f000c2459000004000f8400404c3e00080091910760a4003002824421182d071010b54907250301440c02105c406142c2a200c448042c02c0c56000b45402040d42c108850360313102038540124035034000c1d820131204561554100008041030f59105101c1c105180000c00c901d04140c0c0346c88100f40b18450740207041c0b0003004501c00542c00a43e00c050005d28015095840e01450790712060029884010041c0c01c24400c400e2144003410325020250500c1040b005140e4031034007035000c0181032040200200c4111140c03074440106c1180030300580c45194854040c507a8942518400542480640c1c03145d01401c8812070a501d00343c054292103076400c100b55861604840c2840d031183c1e81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267417437 1250 267416187 267416189
    0x9070b0a030f0207030e0f010801080304091104030c03050303040b0a050c0d0b0607060e03031006031a060903030c15010f12050d0e0d0f050307030207080703171804050a06090c050a02070306090309 86
    0x202d0b142c4042002ca003850340009840d0034140c0201c401852450f81c810054428280038003441c4c04a03401400240003a91840d4020100030b04110b0085091503038a5a60142c40c41d0a03030000c81e015000441400200080032043c15001201c01c601800540303000300084601d800354a43c00705d505034484d111000c3c15160b1104580d442030b0802d406001c4100080c00347d07680d80d8000c0d12113131b10b11500c0000000c0c501d0310034401c2204408440c803100c00100d0341002044096000341020b50740c0b40c0800c00034107030301d01400c00010305402c050f82250011507240c00903045083e030356a0300118807020a0300c200c20006a012034410350500c0c0034181b408880e0004404500018400440101305891640400041c450008090151188607034201e034986520794044540314200c0e44801040c210000e522125005501400361200c8a800b170180900000c1b010001415036001f40e03240c810703542d590107080c050010107000348034580c01c0e90f0400c0741c5000d01e507541c02940d03400140b0010b01038a41c4c0d80050400c051085510f08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267418687 1250 267417437 267417461
    0x503070b0306010f0c02101e1718120c010b0406050a0b092101090503070209060109080a03050a0513120611040609050f0d060e0d0206010e0f01061b05011d01110309070b0a03 76
    0x440e910f1407050081c14548e8540b1801e00d0341d50288a210f08041d00c02e01525200100500440c4a2501c0f107660069004011000c09040d0340200508035481e0a00784001d0316500c03800c14004164001101c0502c021640550426070050108210910216480c04200c1d03040b554217540780c00c07110f000c440a038041d45904a034095001c0d42800220300a01000101402c1c6440c0221080103a83c2c40e0100155130302c3e1070912415003260032121440001ca4041e4000d0160340109040203490030343c1341c84004003034040d950030010442c40c8011103002405013902c0340074401c10340c0041c150318280c1003030340140c00d07242d0a2140c14030407003660380080300c01c1e2251003060311510380c040c1042c01a14140301d01c46884403005010000107203c0c407400003415003003110740340e8002d25024076040d1140e4200001191150401d1070803400c030302140e07905800010400d1052414118007207441500320354144c0100c80c25a09020700c1e03205402e0040c81440091000401d00340101c0d0240c2c4913842d620f000210054001d006110200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267419937 1250 267418687 267418699
    0x1406070c05031006030309050a1a0703020f0604150e0c060f070201020703050610032006161407080322031a060d14010510080d0906032714070503070b0306010f0c02 72
    0x9400c03210315500800b06172072003500c44900d000e40b14011f01c0710340710483c4100050f9000c90300f40c42944a01000060140a010b8030640d00715206d40340304c1c64030700542542e044a002e2070845007409001101c1c13184141c0c6c000b85002034a41d00380c0340c0c8000365030f601034026070803000c020005961045a008101040041d68803c0c01e075070300e9180c400d00058002503184015604090070b00c444031000c1d10050b40b0444000d200410240c10a094040c41b40030062a5800444404a0348440c0340c903206802c000280040880790001c55481715410403140030985221100315140481d1001400018840083c2600345c801030049034034540d864800048082503404806070091885084600c418441900103a1150381140b44d201007441c0c1d00c0c00070b1503030741c8a000040d0340090306178481400700b41d110750006120b5607005c1c004092000c4002d420506100300e80082103c041d89030b0b014040e0041001d01c2000e0003006c045016200c1c2510f4603c01040d90312000300007504203d045850310101e00d015404400d102034024000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267421187 1250 267419937 267419953
    0x9060f120f0d020c090f010902160204020d0c020d09030b010509040515011403010507050301050904060504020109180b09090307032010110304030e060903030711040f0c090f0602071406070c0503 85
    0x4829242c0040307110050060195148099036070902030303049030084c4400c05004c0c119038a8018800029080b0550240842041c608014050b0b626400034103042141036800190600c02d40b20042c0c503000505810000f84a002c24082021035416400503045a5055801a42c00d903134520340641492080c40400702111010b5001107080c1a0301c962840ca1480107500070001d5403a4020241c07a9400244200b56111000340b0005000030341a80045810610606012021589680807040010f0003d0001c1c40c2c21580c96605e0641343c91b22864243d00f0820540c040c40c9000c0098030014070b01c0c00d2080c0710030481408000480000c140802c5100080e07400442e041020141c1c13405421035540c4161410381c00100c50540c081c1072031400c0c0044984250001700198940441c9076101c60301d00d0040300540364055070720310010ba26440300d4080d1800003807266440c80703071150a010b5204d8114239180c0020b001c55102c00d0080c001c0b01181600300e400c1c1c00b01203c102ea01c0d124a0318003103010003800d401282d09402400a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267422437 1250 267421187 267421213
    0xb061b0d03050a05160507050f01111806090d0803090c0a0e0103050615010e040c03090b130c06180911070512091e03030306041509020f0306040f020909060f12 70
    0x520034aa0035059800340659100c002c0102c081d900c06940d8960040581210300c841540502c0c000c01719240305801392030030160000305141c01c654803090b803800c6444002900700c000540881000001100c21100d503400d0a24100205650140340e040c020200f440000110307025800802540d43c890100802c5101ca00303813502a0f80c481340d8404c3c4407c0320248100c00100f021401964002268200c0680d200160416400100406094080c1c5072501303150f5503107010030100b008820b6042c8100405407406030424850700c3c0c0404e00195541c410030401c0501402813466244030405001140c0b041d40c0046540220070b11015940e1081e9600144a445204050152005036030050042110708030380c003039035606241054000489941c0e158640c5030f002040003903031034540b9611403042d001e040c12281c17590355102c040c10803c03a41300340000c00c0840c101104128041c0f600d4060041c22503294101903040c0104200424502000500300383d1090031004045405a02c449034404010011103007182c500102c640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267423687 1250 267422437 267422443
    0x7090522120807020a021807050408010203040602130602160909021206070e010206060d02032802030d08010e0112110d03030b03070603150602030715020c0a080a0305060111010515040b061b 83
    0xd51030740c045888540001d01050010624001c15030b0003905040e0307018400030a142030010000c2006080c080244400300f0105000d1026612992280c1801a9a00b01d04111b88003000b989510210455102c13182007954000d03c03003d90011034482c5040410003584070320010340018102044548540b08580800a00c1680151102e0030400280c091303034820344030b0109120b100489824044c0d015030041250180c038151500016002c6003400c0c0700007030101d0080d40084e080c19214507408000544aa0051040c4004080868014100421001c0074a14941d4034002d61400000740c5500c11440301c0010000d15019801a4021510040a980b10903440e0000a0001c144401098070b422450050204540d4000401c076023205410000600501800001c000065407150140d8a041c3c0203074204000003a4001019181c8035115031004070707040c6004000141079000c80300c0a01c001307038140410b025440c907040d100000c1d800b00944000c100816050040b030740d1845171300e00929801c0071441010040340804 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267424937 1250 267423687 267423713
    0x3060121110f1818010501150c0606270501050a120f03120e010c022131060905010318080307030207030c020d060207120507030219060e010f0e0d050c07090522 70
    0x5190214456519070500b02e088800234080d0807204945069001c0689000ba0788002c412403040002280d540d0b2903100c6928424005c104a1025076902404c13030b00901c4660107100e001d000140c41e161034842c6403004042a0300030300d03a0043c11b29030b0000000003c2c10f01c1819030250395080345c941031140844001d0703c24000e007031149240004ac01500c002c07040d061035001c0f064100c40901c090842c10051544480300001c005c408051111b000c1c9001601e608528401d141002489661201891b40d41385c40c002500380e800c04c0071081c0300910305241c0140002e1000c001e494010304640f50050b00c55a0b5071805881a00c00d42c48080d5000c0b07214600401081940d8000b441e00790700c03600f400e21130041e81a10503203403409007050080160304040c108400d040741700e190001c40c160203010701080e2000c040c6141421100c0f509054160341c0d40700d000780c9400305000c110920170400c50f450001d1801d4802e0b00815180ca249006400340d03152541d000c101590525605890441c100041c4c241c41070048c0e20388543c007003041c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267426187 1250 267424937 267424951
    0x9041104060f05150708090f010c061401050f01020f07060e01051e04030302120309150415050702010504020109080312011509030503030f07171306090309090c020c03060121110f18 79
    0x42c0506408101300104140c600702940400303018141124a002c0054004141d281c0e68100074003081000c0220309a801000311038040681c6200d0035504101c103024074515051146810b560041900394040800002c1c03910488540345031080310500c181004990720b100d11184012100701c11034490211803900c1c0000e004a0340f0070380881d21903006000340211140401c03075070a2031a4110350300351381e5101c10b0031000b294418442c85071304003a925024000d00496400b9204100141c1d5140100b004650f0009051005060100b008500304061079071403013640b007014000c0b100306011410710b0001c0d42d400f89144101456001c02507a407a8540503001c562060822503950300017880d185031200600d8401c410150050703842e108a001c80d5207054440d200582100302c8200c00300a2603000006d988401c82c0700340d0701143c076103a0141c452040310408240c030340401030700010012426040c1241c0300d84543c00c0ca46604a0f44240404103540707009001980d180031040c001e036081b40150804810301041c444000d403003844 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267427437 1250 267426187 267426199
    0x915031505010e0d0311010b09042004020313110f090c12070e090a0c17130203061f1502030c120301170604030e060c0705040c02030a08010e04030e09041104060f05 72
    0x240e240011140096080f61003a0050840410308000c079210b0100d5540c1c5114600000c580301007440302041e0701610488094581200b0305c0740c0c2480e83d5503484090701100c28210b90a45c1103040502e0144448840018000c1503a50004408501c0f5160a00500400342c0d00610100c030a10b4002000070310342e80014610800003d4100002d069180200b1080740c0e001006080c85d0700541d100384a043c01480024046800c0c0700784000a140906041c0900c5407080e44881010440c5591600c14907290200280c021940100c080820b011001440c0403141c049501c0c6203040c0d02c04109500d0103034294032601401695600070308800002d61022071000314125110100904c01c842111000940c4a001c15140200011410b44200354107113000701c068101d0b000780400380c8860b41e540b04001030464110403400005a0000306441d08816004101c85006100107201d5a07094a03155500600c081c1101c800d0314401d0005802140900c10046400e2035103800280c410005103850717170001c2d40002c0c0c0e03611400703108131 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267428687 1250 267427437 267427439
    0x60d1410150c1a09030d0f0e12030c16170c0c0f0303030403140a03060503011817070b062205040b0910060b030c0d15030602070b060105070803060d0309150315 70
    0x16129580c0c110841e5041028100f02a03180e40750440d4001002c2c203800720a2200340955681c1c5411481504043e9181000c000b0f12036241415880c00d008040071144c0f0004411303c1040541000700d812508103a8030000343d00440a124030746015901d02082a4011440010407070896820340050806400d110440d00c01c8001c2445004040e601e10040714024001151002c44065078015403000c0c001c03e13240c81c1004106c032901c5d540803900719042c40b80c1c074402004014502005210444034446031070401c00618a00e071600b0358035074030181c160280c2070301d0041820400c09042061608001d80c10070010b8003050065083c1030424610754801611003c160b0300900d52280c01080e041d200d010f080307450b404130082c1145d6034400207a1403504000041c0c025592103100740c03070443c482c4c40c510b400614455040181c48070400e0500c0c014070301000300f1481c14058200305200c0400c5001c015264400340848a81240c800207140c1100c12603050340c40a2a00e001401e042d07081c144e0142c105111b206045070071284c2c1d07a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267429937 1250 267428687 267428729
    0xe01030b010509131203091103030d06090506191404020d0e0c031c020703020d0c031e1509030e0d060603080301060c0308090c06030c0a18030804050f0904020a05060d1410 75
    0xc5407011401800c035101100d940c45d4003402500000549801078040750342d00c105601c0420300b194000e40c9456502951130f80e007801090f805100d060340014007903c00c0300703800c0c5c1a0301e81c035808800f240c043c90b480c4000d401103001c00b940d1103404581300300d10465820300045500080007a42c82d0b80003155548640204100e95441c0741207d00d8900d040b41300d0344e0052940078616024030485698242040c2c50a100400e4080003103251054110343c03103c44440014080051414110820f480d18201c2401c40b03410500080007180c1d02c41041890041d045800b02141845481c1540040105601c002e10b00b034004400001c50540069034007500714003d441e095842c0c1e6554070a0342d00d82d44210701c4503501500c00d0001c1808800c00d100a03041034170b07050070000540c217480101c6c075000c11225881107c520000003428000c9080218180c0f108440a40b10304807641099030006650001c9802902d0041e100490685100f03412034004444212001c50501d84504011020502044440c003800c6180380d4107404a10030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267431187 1250 267429937 267429961
    0x11505091302060412080702090f0103120201060308040608130b24040e03070f031716030e0c030a080c030f031e091903080709030b07120b010201290a0e01030b010509 73
    0x800d40d00030445131920b0f081000c03144102452010580701d8860601110005885880199010b4503003030800004540c5103242c0828240d035054030701c1c0110390410300d003000001c40c3c00c02650b09407402400c1611403a903031858020395460380f03a0b40107000085140c05104000d258420404030720140d000585c85a040000c092006680c0d12032151a8140d104210500100b02d112501c800100d110303291002d0b44134004800588000c60139100c54031103207100d5401180701038040c403075020380301840d0000d1300c10900705c03038002074541441d90b0000d403005000050104d1103d200b881151410600f4803981a16418200480038208401c0c05c0c083c04680b20800120701200000100b52400e8800703030242040000d40c60b502220070501c068065000e0011400010000031040c007000c80c8148682d54440031306600c0580400182c2e10307180840c9066915010f008007106103601101e418815007180c00b4240c4403040c1700416940d10447d4810758803001132400200400030061130b850304980c411a181c0720140c454090800d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267432437 1250 267431187 267431221
    0x120412141926010501020c0a240e0904060e06130308060d020a090c02010518031204080c0109020a090c030b040e030d020f0c060702031b0c0924041b0206010b030c0a050313020301150509 81
    0x110300d0386825800e40014011600b41140e8000c9d034688100c00d00c0144000c1684030380107403030858015840303194074030551600b0081d1942c44048407644503444043d80d10040c5c42c1c01030107071a040c000c0101c15542415074450300e032210020041000b0400440b04c0100d8024001c20082ea404860240d40000c1020141c800005540c50280c103901c15000079221070f52000e5440d80a880e5000455407299000809039843d60411401401d0340302e4081003020282c90010200c500035484d05215500d0000e4004035000004117503140007010080040c0c2c2c400301150041c1c124002c441680b02103204010820903440d6000c00984911514000414010549044140d40300c80c402c00115401c02c05080000e10080f120030140100e80c504121505103414044010030b0030307100d005801e0288a00f000341c2401c4d559504214060051101c16005411414261860b609034443d0540034000c0180c0807012031488410710030780d40411940103008101c220104c00702c2184052251140c507100791901000510a0320354001049 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267433687 1250 267432437 267432449
    0x2b090c050a03080f0d2a0314090c01031a030d0215010e072a0516081204180b013f05040302070306020f0f120412141926010501020c0a 59
    0x790130051000b08202c0c00c0c0c1c02894504c02c2e50341d1075131b24048100c03a810b41c0b4900f5805000b083c08544c0304944101500351280d8031440940c8003c4402041040c400c08244a48811400d203804501e035007161412107484526041d06950500400403203c400039000106540700e0240c0c129680a103070390307030400101e003940c0448184012030403480003a03010000640e41d060103c00490001408041981c5a0710720b000e1700b40240400842c103070131302400000c800304078484040b000c281c6554602400c029041152082d525542595581c541c40031140c141c0c020703910540c80c4100d411104048140340501c000300c51072081c503054444450900c1d100e144500038040d0901c5140c05400800e03070f080c616600c8000a50000805040f0140103110b501e0710318803040001d0100c1d9070069080d01d0141040d043c000001d100303021004080c041030130300164402000409031448807000d1501c41c0d00d201c00084043d1841e070382002c142821000f03990b6114031481420140c4505840b002c0e0308849440120800380040f05c3c80c140101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267434937 1250 267433687 267433703
    0x7120e03181c0b040b04080f191b050c24030703050403030609090209061002070b0a0507061103042006041214070f050a0308090607050a0f200d020103022b090c050a03 73
    0xc4c01040c14100001e4101d031103031407400d01d040943e03c403000594000400c50b00c1c03110f100359284003400d82e01c2050500310050000c0d2900c055012aa20161307140800c0c1c07103043c01111056a4207035142c070300304250802c1c1c26080503819920326000c0001401004100e4088010910300300000c10624078a00c955024150301030002006070301c07840704101d4001e14000410085116011f0042207101400740549248003a5440f4a52511402c0c07400c10280d500060b10307205581030510800000c1204d00070144030702403054485e440c0158981d0702142580c403e542000c661282ca5142d81000c01481e000ca14a881c0c40c04030689822a45076112444034031340c0340c0b055030b9000300e08a00510101314050024141000001d0031113107014404c2c0c0c0d402d82891280c06c0300b9aa0540d400c1141e1003440020241007084006e0310740e000410701d1001d400144036291098029040540c0840d5441d03140702110225601d601842103114001d8170120442c40c017900594001300c07148030340c13520000380d80d00b13141a960b0300b500d07400f140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267436187 1250 267434937 267434941
    0x5030109180c14120c09130c2106150501050f16050d020123010f0e2d0714070503040e04020d0f0507090606020d0807120e03181c0b 58
    0x508405000c488100480c800580301c880d000080c81c0700700c1240141200501403080d40b070848100a050004607800c4500d942169207070700c6082d40e503d0f54040e0302c5000e513035592240d0300d51810700c04001d00d90f54000540c9508407105500025074103a9200b84610b00c14101401030312802e000c070030a41a114130955021810a0180d03900d40e08150018259030715a07049030000d10103480d1503042c42d001981c00500003503551030040751f48142801d040c4c3d0800104912404c00c581d49024a4a00790400c03511800364003082920206500105c81c500300c50052418058030714104c0050910711079624800c0d1075640120380020000351075000d200c42035481003504500614182441c0000f0040b01c141c004004aa22030f00c080d0702d1500050b500302c203144017940200000d00b00300d420305006404a480a0b0400c40940d40316801c00c0441e41d80c850380495008202c0d20304803510340100903148000e44a00c2694410310300010456032003e40f13050800b4011807104440a40d014034034001c0b65000b102070074601034840340403500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267437437 1250 267436187 267436199
    0xa0c030305060d06020f0c01060509090a02041d0105090c0f010918050714070605100b0304023304140306060103060807060804031701060807080a02190c06110724020703050301 77
    0x2001c0c603030100000c0c00d00c082c444101d545400032031780150a07050312450041030418a111007481000c01a0105444c1800c00782020000703960755504004000703100725118040c8c1c124018500c21a24040c4015500074485401c3c82ea41282c0c99000901c040c40c000e0801c0296240191302c900040022204031000c032405844039000003801801000346084140101541d0156040b007007a4014060381e4001d040c0020709080001c024010a00654440c0c105603000380207000150b5140002a00360144a40c0c0c03154400780641e0303600c2a0041d009200085403140800d0000f13495000800030414030208500703070f03011a56100019012200c490051021541c440001071007010301030340d00e064005002b401d10075550307007074844c2c03404001100760021400a80d100f014440000c0d0007640813034004032019030139400d0048000f41c01851540d030005900412044041c40001e000480c2e001c160820350280b0b120b40d445203b03040207100b01c0708071500c42d40300911140c40c6400c80070b060700c203858040c2e07071669606143d039103000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267438687 1250 267437437 267437441
    0x10180c0314100b0a060c3810060e01050a140f18040c090b07050703020402031311010f020c0120010c030b03190b07050304021903050d0e01080105102006010f17030a0c0303 75
    0x41040340d030240d04d050600c0b44405041c171a0746103000c0b00c55003964a0010347e503015035550b8003e040c000074900354174010300020740c1000b40c1c00d0048d0000e107401900d80045000488550000003001d0800140c009404107120240f48010314600481a84c0d0041484090042c44201c6903501520000211458000d1281c400c2400040c030006020b01c040310041a22500090200da006035500b203071342e000750342d014402c100003600d04168080c000d080c022003150360341c040a0340325074042038010304219103803000618001520340182c22000800c40200020381101401034007c00b10705203141d02c46e03c2070300007844a4030001c9000141305c540c0501409015102d03160241e686800c05042240c2c003408039581c50360f44844410f080002140a10014000d10442d520054420840d44d0503182c10044800018405600c071810300300702c100c545150031900b01010803e4600c10640418000c070f486d018a20000814a203070214a5094502d03040030143d10503007aa42440d9030b07100da441d4132004070f0f002d1491a00428041e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267439937 1250 267438687 267438707
    0x70308030c1c0f020405010f0c02180c0408120a020613031d2206210c030212010207050f071805010608150102100e100b0402040810180c0314100b0a06 66
    0x503819a02c4100301d08160406859400c5012541d45a003c03804120f690380c06403c02c40c2145050400071802c40c0d1720f40114a04070400f01c81c4884002a080224100c1a807032030460700104002c03003d40b4442c0c81e0243c14980d142d48850b008800521501000c24081d4914502501c081a0325865050304040b030302c030004048a101480080d40104031007031003440100d1220100d1b80011004500048550621208540782c0701407054101c2d052400e6003c400028002691650640f80c04a0f0701a20b44202d0f00f660a0281c85654402066405404002c0844990002d00304065031074000c0045c14100301c2c00e854004440091140f00e00140b8000e0110750311401c11500082c50b41c0c03040c415501014126406241941d13011342109045600004644100000350b124130354a09004903025490140391480c1c1e2903580c802d8404104229689074420000a041c040c14404c04540c003a88054010741d5a04042112201c004050035980c059107200500d05500d5119603c03010340300916102c8800c0c1405000c44e05900300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267441187 1250 267439937 267439957
    0x10201110c0a0b0106050a1d060403020a03080c0c04090309090c09080706050d1a030601150e0a0b040801180c120804092f0f03010e040206070b04050607020f070308030c 74
    0x103a21580406686004018541c100881d002060301c00241d10300b007109198140d205a0410105200307600b6155400b01d4569044924804055070f0310031481c001a80c1c61142e540000d5002442001c0001085105001b03131410758070810942c1c40c1c1901000510060741e101c0000200084c2000c1d0b0244030100c003a501141400a40707184c0401825214544681361000640000001c100302265190300032a80c1d010301c44003003048098440c0032803200350200782d58031010b01513541030a40e0010b42800303091085052152148008068455032030707881048003031552143c0180c038000e500305181070075801034084210820562200341081070507c0c0c19000d0003a594400001c0f1050302d42000000781c50036540c083c04241200301019030500c8072048048600a82c2c220900c100c00b0101402003034001d560f00c2056a044440000080b0180e603160310008540788a030117401055075602d178090105201001850030310405054089846c83c4e01074190803696001107120080001d03004200040040a020b406842d80140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267442437 1250 267441187 267441191
    0x30a020702040903020102220312200316020405070e100e030a020315181b060f0c01230c0f04090c020304080a08030403120509100b0a0b0f2709070e010201 68
    0x203103580000d09540640c0c0050300140e401092503e024401412011441c242c0e05032804c00b41d47c51580ea1714040c201001741c40052091580400c41d20100b41c69001c2045003411003642e03961000c3c214490303000c03040440c2c1640540d02d04000680392900079414a100a400101514290320131142c0448150006003013207501409468a42801a1010040320b121491a04040e000903d08581014109040c410240d40d00d644040b0f1034503003001c500351408a00480640d60203594480303416400a40d48103011900d88150700c0e1a44c8500d25155003642d02d42284031004005159403681c400011030f40c02680c900c00440c507000c1008205604140c0d100b07019501180c0152401c0c55a603002a50911a021205030b80482001042004241e84038100c50f0700e1090f002d50400c03c4d8107140407040da07103ca05403008251540d6070040070503240c3d50285204001c00c0c80305465a5140080f02c48074246070030041c0c401e02040303646009070144d03030600d242d80504000c01410130800341d43c400300b04940340c0e5100714900c0e0543d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267443687 1250 267442437 267442447
    0x121a190603140111090108011406070b0703150503160504150b0309030414030106060917010e0d0e04060b0a0c021507170c0f060411060d0615030b03070f05090a02030a02 74
    0x204a0300485000318010710361a0454140a421107003510301c0c40141552107502002110a16030b0170120f02c0c3d064616101c00549003626940104010b07200710b42000d400303101071804002c2c0459040d00400710701c3d001f20380c03100340d0f07242d07a80d00345580d503000c40740b150290520300e00080c011810540c0c4401554802c1a515001440d621005610164016158050540c2001074140140ca000614071610000240d008000d03141c5054001402c0c01410302440c51b60554040f00b40c0c0d1411400d40000c14101310001c29031ba8000e00408000d411031140350070ba28051400c0200000740741d1100303005e46250260740d4070340d4a82c81d0310550800c01ca25108044048101d2804d228007808164140f03401220800c0020640e42d0b02c442d140096444c04030080d48038401075011008210005460480035100d1071819155140c03100581544200034044a80222401017003650b4820022945600024001c183c05e9090702c0c0c5142d200e441c40c140002031030140f180c0080c0c901740414850107490f070045030320440901006082c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267444937 1250 267443687 267443731
    0x150408190c210c0206180108180703030521180d08160503250503060906040e07030809061b210a0206010326030403030b090907120f1b0b0a0801121a 65
    0x1540001805801b5000c3e40c00504405507004500560070609025240c900b440c01d006c86581d403500207000040401c00c011503034a400348480001180000e05c040e00c0907034603242c180d1001c5021083c2c44003d125910a9801100c8070501a0b940b040c041e00c5c5903416402c40c160180d9064030b01e0781c4007414900d4000c2d030740200048104041492900d17140a1541c4480da40e040c0340c400c00c044120098081c03803040d40b6001c10071000000019415040303079030003905a03884450b0070000910ba0700550403030601440782c1d10030035140050086412508a0040da4400e9010340420130036910502406082501507840030b801030022070801802d081d26203d40c810b519418160740141d0b00c02940040e50118040382d21901c400d0b00c280380030819164071500c003400500c0c2c011301c0e00c400c00c0c9090130000300140008180b10a01001e000301040610900e100104d50799140594031540850a44c1c40081c031000020181c000124000e40b240249400054020601c5079060701c2d01c0b8580081e02002030407254503000c040c400e021003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267446043 1106 267444937 267444949
    0x4050609090c0412030801031505071b210c03200c04050c040909050a0c06020d050702040f060e10091802010503040f0302150408190c210c02 62
    0x1e0744444516071654071590f007085021040c07a54240c0e0070b250308500703143c1c100c900c51420a07049a00c101c0005084036030548840c80010b024480302c4d21000020080c5014140c0a80e80c1e14446400081c400c14040c0200910311001c0740ca00314807603003856007206460500800c0000001c0c004044035500350784850380401c25600c910396410100b541002c006c000d4a0142038070031010414601103041aa6403001d8100c0708540074100b14902040300c0341301240380d8a600b40561202ca01380200c690810028210081207040e003580d42c1c0100180e20641c104240d40500710380721450400600785102c0e0f00075989088040d40088000d68680170050360700000b12980725800001d2420101040d140c2207050400b0b1a540e0045c80300068107100c20712602100816890261441e4244280600da405644110b071503c0c0c05080d801c3c116031031103190035000b5808c00013449a458000c1c49070216a0014070 = true := by decide +kernel

theorem cover : BRFrame.Cov 267266187 267446043 := by
  have h0 := BRFrame.cov_init 267266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267266187 ≤ n) (h2 : n < 267446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
