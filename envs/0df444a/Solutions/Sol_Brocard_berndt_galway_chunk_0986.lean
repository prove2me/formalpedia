-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0986
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:39:49.5501+00:00
-- url     : https://prove2.me/submissions/d48e4973-40aa-4cd4-8426-714ac4c0f515

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 177158273 ≤ n < 177338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 177159523 1250 177158273 177158287
    0x100e0c011103030109050a060b0a0c02030c1207140406080d08090d0306060c030806030f030d091a070801031202120304140105090c01050913020405060a080103030f02060f040303050c09040908040911 87
    0x7000c400c032819100c00c0c050100b080ea888071601c0c8094013480d4403401800c0c10000310644140c1c1c0c0407200c107056502c00c03810b555404001208202c8085820010385490b0b8101d550b0400c512030014241c11148a409000441c5035030352000714030b052100121140000c01d0100f41044040d10003408220710360541802c08110305414000001c201030f0411100409115014010600641e810002c840c0c2044800080300d554410942d000070180c01045401c4421081c103411030380851000c1c000031441400650b580084981c610340f1100100ca2030f201040713055020312050a038205500300c00543c4650b01a40c00000010500c01c2e00608440c0c00400f001020307000098012200c0c0e90085c212407080900b2034042c0350326000c0c1280d840c003d1103141d00c0282d1007007000845098240c0c20404560480703000741ca4031b51249003002410b0f40c55540c01c4862403e001e00b0b1800040c00280203501a68100c0d4080ca21103017044010008641101c5040100351900b507070106040116082e2130003032003d41004540001e0405034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 177160773 1250 177159523 177159557
    0x10909080904020307051603030b0a291303060510030b090c011e110102070b01030b06090108060c0d09050d09030b061203070b070201021606020a1d0603060d050c03100e0c01 76
    0x3070280e0181c441c607000808180428841c60949104117402403000c001030900d1719014009015403c0000d0240b140b448000542003000790325181d10200b00e40c60507400c0d00015241c3c8405034040451030508080c2400c012010414602c10030388150071000b03102c0607041c2142444107055200070000d40031544191328100050740d0004d8407641c0340c81c0c0d80c1f0641280380c00701e100569407101280d48003101d56101183c5d040c207002001d50550b0480f40660318070425501d41c0f00520900349030074041c21400b03500c1341000c2010303808064001d080200e61028002500d281d15604c00c0e003804504200440040c05569080c000c0c07010624601790020001c9451509500603140703c680c80e40901c2c01b000c1d12030404400000c1a4a000307404480e649038803060800d0940311140b42000c0290050082000001e0300380050341402e11040f00000320a2400410715800c50752039030200000320808490440d400e018859610204d6182003140c22034020340c03440042550b11600304050315007641c0364a641e0410044d503440300d41c00340c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 177162023 1250 177160773 177160777
    0x60a09030e090603030c0d0302210f0118020405040207051c02071401140f031021030e0d0311340608071409060d0b010f0c05030a0507050c090a0b030601090908 70
    0x4070705658940060780d903200041d00b14000d8440c20100c60103a40d00324251941e043d402000b00340801101d0943c41260f207030100d900801d080340c4445a5080c540014480d0b040c5640940b903000ca0402000b40c5841e403a1000700e0143d8010a00c211a95800285010a446100034001508808510041c520f55140049015154035040100340c180b0034015a199100756610044034501c07003284858956902b4081603450740b420462080c4c0c0711860018115100580e1301d41c042464290b0140c0d0340c0041d18504e1020041848642002242842000c600b00c003407100c0140034020000200390f60020000302800c0890310005400300d00c4106829208005001140c0c20004882d00444149001c00c1108580c0034091028414040e06643c07010001c0f84412400909411a0b80c00307410030307a40e90100c1004114152081000c8450080c00340c7c0080c00104162032051016041d401d01279001c4520060b031480220707140e83c00a86040d2a01034070341100c85118102049101e004151000082100c000300c0c0c4c0f1070742018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 177163273 1250 177162023 177162047
    0x30c03031e0408010c02030901110c130c02190308060a06030e06040f0f1b0f12030e0103020d02120c0304050d0203031501030b060c030a080f0108010b0f0603072609060a0903 76
    0x124001c10300000d000c0074005a034054030304007000300310703500c5030100c082c1d9079400c00044180042e5101c070040b018034501080d001d1f002e0380043c0100075002e1543c54104003070042d47d8081030440c8038000d0340c3e000c0e0580c2c0d030002018450103508d03040b2550500d0000c0c440401c41c95080340d0b0504d8100740041c0254000000c400703034403a130082d10600d440712141c5003040b540c0e01030200190a5501c0f84040390720b0328004008500c2102c1c407031650451000e81c2c4041e0146108124a00640498507103000071240c0d5009400a00c1c490700d40080062600a40740b08241d001a02a00c100c40418000700800c000c02070100500084400341c2e0004509604d44180300034480c80c1c0210394181011344a060304080c50f1907500544613510002400c0e00d85400c0503140040c0309080440b443c0110603049800040d208506118000000070003520040150600c5828061140d00140c00f100c10071001d4810204078000e6200b03107114076103640071106440e042c181203a5140050140080d4500c5107802404400250840040700744 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 177164523 1250 177163273 177163297
    0xf01080f0321100b040902091003050114091008010603050c030c0604290f030f04110f1008150402070b0103062009040e01140a061a0a02030a120f150311030c0303 71
    0x15030340da41941e4114045541e071000303501303000100700030403014850b4029028641050315011030f0b0b4460342908a0960341d0a20821200c2400901c0540c00342c20807101a560240200b603455182d030b0398a0b002942107a80550055030141c1004940100b94541405150b03515841101c1d80f03070030141030040b002c00d0030360b203100a0340786402d0041d002c00042258500342c902d4603109181182d01d82c81c080982c2c042c004800c03501100c4040c1646180e0841d4908507d40b541c4444000d00400040c00301c080701652a000d000c2d08074000540d80180c0000d042d900c0f8002050094400e090429180d4518900001941c20b40414403040d17080750420303401c0801104050382c800070422035006c01c000c991603031141d004154881c085c1a030f90303855808114500240340c00003001c0302d540350414010000b420751401841d008803c500300040e04200045086e0f28401e03550303d54110301200000800c0071088410b0401c491a42c4200000600707070810810611520000c0d1402c90390341903000e000003000301000240c40384142c3c5030a1034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 177165773 1250 177164523 177164587
    0x120303061d01031e0b0c070c1205010903080f07050d23240114030105190b071112010b030c010f03061d06030105220f030302120f01080f03 61
    0x141482504810028000e0002503040641440c0600440d40824001540d0a0003c02101103c651215803940151604802c03645480c4d25464580802d0b40e0021000b5214400480b401142841e03400800143e880e01c01c8000007100812894060001880201250001c051200401c0545a004021070b988040915800601450030240c1001c030030440e080380720f0400c96a42c1c10042440b8440c0c03a00c0c0440e8100c03c0c0c4c4402804a800c004503000300140041c60f1098070180010130650400b8440452a0050f05070f001260980f02c4801e4502508040c030151420b10803020301561a05081c4079400c10300ca0300800038040800c004002c03da81c1c59584840a04006c0a10341d401041c0f48a540008080e080b085049091340542c0c401050740b1281c03d4034620700c294a4100800c8024440c00c0601e50303207400c0f141111035002010b80701e40402d044030107016000c0c11b030200101e294242c040600c40744103111948903950785504101d038091a080c0300703680b020030341d50003088a14405080c020038540403503c0c1000d102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 177167023 1250 177165773 177165809
    0x51006090602060f1e04030c06050112020616050c06070f020411040501020319090803070501150b120c070609020904260a021e030d0e030a0815010f110c03061303090807060801 77
    0x201c0c09140e003060345d6296194039044c401003640c420800c101c0d481c0510814081640c991440800313000d076603080203511003070421848003003500071074a007900306000f001078540c200100c4000c500594040c00003280c4041c141c0c0340100c214541881402c4c0c241215400c02b40c18603040c040007135030364803d04c6245a650130000c003440c0c8a5130702c10316603600a4000f000c00c2d40d441e0031407481d10901030324034080b003100c0a00d8101c80204031344560382c059414003a0b103489402c18581714034010081c10f030710901e4195150740e1130304403a4000da01c0c6c0484080c01584181d207925088041e00d800110782c01c0010031880000c500401030110700c181d00044814800000782d0801c2c1030310315904c64652452040c560414080342c1401149c0d11100310102c0908404c0600f41c454030b8040d658003400b00f044a516072100d601196680002d550f01a04c0b5004400c1c1100f400821101c0340382c45200042d145c000300310340c50603050380d4100c250380816900401000c02003040c440203200c601e0500d24013400310441401401e000c40401220a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 177168273 1250 177167023 177167041
    0x280b0f030d020d03050a0207050a030c050a08030f0403030b09250507060c0905100f0203030c0304030c061e0f0b0904120909110a0e0303030708010b090d05030409051006090602060f 79
    0x1000218000c0c01c4030001d8080c0355010b900c5008490700303000828a001c00041641006000300d40515510202400210000e075800f0350f200d104046050380c0510036071810342c0029281e0310003180502c2c001144c069491400380b900409031100350355141d0240d00700d2000e00003400800700c1602001c1d16020400154900f9014045849000d2450050f10f51070500d44030108481c0c1103000c039400d0b0340080c2c03a01102450107400549010740741003824001a80100002131852410101458105206e0f18080404140d580c44440644106119a81d60340140d00c41020320040203201e90313040921904824451039800c90001007200381e0040c00500303000380d141c8100081031300c2204108041c1000c402c0800290b04d540182c0c0c81d258018040c406d001c200400e50180b09032074000142d9108514503a102c40c056030070110000d01e9500080314a0307410401070b44851000030014000343c030241510200c006aa86010038100d041c1c0c805552044040c001106024072040d90301150b0f00b030b88256605820035090302c4a03900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 177169523 1250 177168273 177168289
    0x181503030702041a1807091a0f0a09050a0501090b0403200a08060f0a0e030a030b0604150206040c150210020a050d1404050d11070501180b0a090905280b 67
    0x700039030051402c00101d0004215400f102000030301980e20541c03083d8541c0c102d1500c3c0d0342c155090000701c2d1038800108101010081e141c8403000700c0344a10743c01c103000b4000c0001c2540202200001140210100b0710260415540001c02058241f030414502403a12074100a20722480c007004c1c0c00422810662400e000145902c40707075000c8040c1420315200d17a01c0b00002d403502c00607107100c08000d0714840403d21020f014058000c049003018042c515080c0b00c207038260001d0003212161034129070144400136012038400c0c0c001444a500e900a000076107080c1c1b40c208a844240c5e00800d80b81c1d0700942e032044101d58002460851120707036150040c0d84003203820054545004d000c0c0421811801c10402202c540311800b0454000c900c194220352503011860400c0e210702c16422805281a4040e0304100030b03640c4203090512401344201700c034004a40d141c498110306507115034603500c08102a45410000012076108003a8025602108000850800082071000000d180300f03030800c41d034843c9403c2c420365480a00e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 177170773 1250 177169523 177169537
    0x30f05070b0c03070605010b0f0301270c0201020901020105061906051809010b09091602190807150c091401080106050c03090a03061d190f03090b030a09020f18150303 73
    0x140141d201c68109154541d80d030701c44c58084030203038189000054655071040c1a6203100302928690741c116030030480c00c040d640515094402104545418114010000388070b400888000742d400582d84886000c00a802d54902030000c030301845500403000640300c51442920305440f201e14115681700c0114034044111400528040c0d44003000303900009195032400e0050000103015a000d8185640f15541076141c00340880411015801404440d4030141102003010225031044880320704003107640e164102060745805800c0e544903990041c407004541c120708100300a045041001c0c0d40b415021000a240181c10300c654014024003040074407030703c1418400c1c0c4818030405458480c40c1e56503414950040d141c0d01210a08021103070a20400b001f20214144e0244409040d14403003111281d960f204821038810410703002c028000b074001ca04032038228021400360f04038080100b1600440d00400c06c080c00a5210b80340b081d10401d10741109051410b10742d81d8485690355240700c1c0405008040303030861060701 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 177172023 1250 177170773 177170789
    0x706050a021606180e13060b010c1b05120708030906030601121406012312060109080d05190e01020c0409060f140114040501051e010201060308030a05180c0a030f0507 73
    0xd60120b445640400340b0384e034140002c1d4001c00225601c01c042c848004040e501130341c040340c0c01814a004207034907400100b04410189004050b0070032035112580560082c5204821703401c0d04100030080761a00d8484020b01c185071001030318a05180c290559903a10079440307120300419001c0300052050780078480c0b50700c040c0c000140901a10301e400722000301c8958111603050208554080745115508001d500015414030689103d1a101203160602c41c0f07068001c16090400003511004142104280250b07030503040c0c00c0d260340d0b840d202d0294170544000c207210055810003005130018222a0790000d001030100b03100381c40014408045080c910081d1070020140503000741084c441c11401c10705002c00c43c0c12100e079101c01c18401c200d48800c1006491081c41141c0c1e1007090500d0210ba041003142d80803990400500000810755503e9581c3c1415800071166189030654410400041800c8107c03018081c200103c041d10100c0e40f5200012003000302c50001030024448000c0c084200401001010081c0c074040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 177173273 1250 177172023 177172063
    0x10020c010c12020309090a0b01110304080709020706022802013903060801063b0402010516060516030b0102061006051c0203090a02100207120206030a09140606120601080706050a02 79
    0x11f548010141450f0510715002031120084250074850100039101911185005410801e00c0d128199020b904080400d4420795820030244000422310040da2032002c003410341008160910307000c007a00312044c501e400c441440005031020034a114242c810059240c0d800d140058040f070003032007180100000c0d08500980c0d860400085031000c40f00c0c140240d2004e0301507007002480c1e8103030052040180000038022500040402042c0150b00610280007484810321710310308110307000e071180310a8440c10740d007525140303610111380c00d80c3c540e250146051082c1c0c203000a1040d0304040d0b400151202003886030208211011070600501d045101c00070421145080b000d40d143c2c14180c03841611500c40c401c00f2031084080c03464134100c460022820f82c4c101c416443d0204d41e208419020310201c1d60004001c000b0302d40c1c0e1000340800080d0311602150996011000400e846d1a0003410b001d40244540c1d04100b080c0d100b5001001703810400940202541d076246032454442680400030380c907181641c601c2494800709 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 177174523 1250 177173273 177173281
    0xf0d14010906150501050c1018081303150b090109110c0609031306210213091e050105010509090c09010e0d0302060702070506030402030a02040b150f070210020c010c1202030909 78
    0x14030f400085541c034100032485441690341d0019112881000a80101b9030004541107000c003015900c045031591403068940c020320303921b81e07807204280e01080e05028600403161061040c8100310310344d0000c50352044000c001d054592000506160014801d0501490700e03551150f80b0b2030207000540352040b008034103c40036400e20301000e6441e03401807012135880382003c80300011134070322410313029803018011081c01d4140f0f08200300180c080d43c8411951020031000307140001714068a072245841e240b0140c100a0001d131249202ea00548070181d200d18100501445508140d40d205045541c100204490081d0380b6404e0800595a0300304000e10140c7c42000404100709164010030071510a61503507090300e1910380c44504100c01070200b620061341560060055400609081c1d12240480784000c010901244d400c00d20614560310418043d105084085810b6046040242040b107610300c450024040c47c0301d40400080c04141d036044090304085003015003200071030090086602102000d00030701d0481c94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 177175773 1250 177174523 177174533
    0xd05071407030917070e01061206151e03050709090506120601060f02010501090525020f0d0203120a02030105010e060f0903060f04030f020a020924190e010b03060f0d140109 76
    0x2000d10a000c031144152002c440101400700f902001da801400c01c6c80744603400c06100b1590f180714a4041100d0990b2202d002c503500c806582005101c503000e5644c0e01c0101050705149890108184004083c10304260a02c043c0d03030b420811001c00e60f03401c00c200103050f50f50000058440300c2030801c1c45440c0d000d10030000c1000c55011031030070180d02441c0c0003404180da8480e040021510202c07064050b04a10200c0c40d015a00c04c800040320206c0c01d44101d03404000c16844c010b0820310158079078005a480007076191039074404050740d140d11501c003001c00c50856160030006410112140c6904e40300d041c00088050000304507100f925903004014080b50389074508032001a84c0884213031001d4001c02d0b84000640743c042e2000541d8038280341c0c00341459256486030a101d4410381100304c0000d92001c03042c3c50105c85516440050032900d007032040c00c000b4a901e00f4001209103a07040c1c10120b1100410410082280c980740080c1d0070b540d02c281d40d0051410b1903810b0012400340784c21a4040103500b05588001848 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 177177023 1250 177175773 177175787
    0x31e0f06051c02210304051002010b040c0806040c1b0201050f0d0204061805040903170a0618021201060c0804050603130609060605030c0301020a02070905041a0a05070201051b0d0507140703 83
    0x82c0c0f0036140c0040701c9001c000307692030a6840280b800ea950340300304401d014a040950900500c00040d00000c101c100b4070100040541e00102d03001d80c00601c0c1001086039501e014002c1594200a0f800c02c0c1c0d440c83c8414410000e00911424060305002c400902c0d0340080300e0010440350401c0000c20119110382c2c580500802d407c20a001d2101c0b420074a4401148900c0c0900c030300f0284c41d6054603441e020b0400445291180980107015400d02e07503840b00000350030100820450224000a2401a035400c0340c4458040c503030340e06800c490200101520480f0019141034200d405071041162803944a9440966014460680460090481e41030280a03400c201054006209950b003c505950102a4103410b150823401707506003403801640700460070819520154001600103026200300d030420201811002c40c0580d0503105030b461a42e944042004aa40c280f1a02c1d4101d00d0300300d1000c2e490f0f03070841c0c0440f005000d0402105032265403a80403443c41405003510345c02944081907403540741c0045042c058940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 177178273 1250 177177023 177177079
    0xb280801081e030706050603010b06180a0f0308031305070504060801090c050f0a03060518010c3903081504060b040807050402030124030e16060f031e0f0605 69
    0x10303201d103260890007100440c1e49940900c600400550030300c005a205c00c406040040e000507095541c400460b503042e00c600c00207204201000c0c45e01801120a04103100120109a10100c80c180b00c0c00000e10002d40e10004580e000044c0040001080039a41042424411315a00865003c5c0c646200001c0000041d0010503865004002e10070100e6a80c0c010b204a03c00d42500d86135100702211424000560f082c2d01c035a40002440304040c0c02d030b81f055241e80c4e0850700700d02400300108403c415502c00454110030020100301d82ca0060030000030907074280202e51405031078014140701c120701c0000d44940c0110f0280e40c00580003001446071981e1400e0b900c0443d0700a000e00d000074001e45102059030300b00350089034101c400110f424640d031460943c02e82d4113501c140e40010708058903104103202140c1e00f001b002c81d040d031181516001092400c100504048071400c0340c20281418481c3c09440e10004058000c09808042c00c04103481c800e4401d64001040b40e40c02c01941b00c8444002150b510900f01d0941da41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 177179523 1250 177178273 177178289
    0xe09010b040507091e1a0a050d0204031110170406020721080109060e06100503040c120602030709090903200a170901020f0316060c0302090402030f06280b280801 71
    0x269407690742c00071800000f21b005c0d64a00d1400c2d44080d2420000303000040040c0c0c8014500907080444941c0d03c0e00507a8015401903a12420008003504140f0b4800e684507645d081a040200400381c04000103030880d20000c0c0050101940410000d09224000020460410710b51401510b8810096405040d1400a0203505445403038090042100c1c600200c0c202e01845004201070403440c1d6103403084940340e100800c01c6070000c10001c0006030a510b61a040b560b5244a81c1c03000d40c8a160040d001040c200655001d0210541054107000219801003120090101d1602903110f0f9541c0180f50b180c580509a6801000d1246840d200c207080030408003c0c0035500c200340d00360b8000e5031a00c20080d0760390040040c41c100075144800050005207050b84008050304050601500f0031440f48000b03401c9030000c0381c0822981841074104600c0c2e18080d020f482c1c2d840c00400080c3c4034407059040c1c03051030a40500440503d902c002800304100c4108071407101e02c0b50301c510000c4891000da01c000410107132084c82040030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177180773 1250 177179523 177179549
    0x60815090d030b01050d020a0201140a0b0102010b060304031b0303110c03030603071707141c05151f05010813020a060903051903050306010c020111070b040623040e09010b04050709 79
    0x20440c443c1c001c080740414160340b01800c2c00c1691140354000d6000750340c02c030159035031507107207038031049030402924450440c241c03000030190004c400281c292032802c4002c41c0702e0b210410401001039000100788440c50130703049801b1207a200c00c2c90b09170000d140b60403502e8680c41c0301082c404100c950000085118800030f0b429542200e0f61080d8100139000e00d84080d4125401c1b06c4001e001108a4288c0c203069510700614200c0d51b5071103010303403011002140c002a00c064000618070031661400b480400d401807402e8100002c415075000d2a403800a1542c040c480c104504880443c641042104d51800d02540040070542c030076540e500043e05203001407000b212280140c048410600040c00c0c0c0500d00c00d901500d8852941e034030700d001111180c0c885c0b40100d040c070130741001d0800c2440e401c00550b0082c4c401040c00f82d903610b0a08001030440c06142c80d09424002e2010700020405141d403050350304444402c244c000c11a120050014090040c078148107030054604070401c0006079011004901302c0310f655170656 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177182023 1250 177180773 177180793
    0x3110a0b0f0d0b120619180b16090b0a050901030b0402040b19030506010e010e190801020d0f0b0a03020d1a10061106131401020408030310060207080f190606081509 72
    0x14800035106151106500500e00160407070040c484503c1d000da040c3d800001e0070381e000019400d0404101d00c0c055071303583c2c8c2c00d03806c0010051000c1440b42c00b00b061424040040703481d00c240085584207080100d030030003002242d4071081b40d0003908280305440740100b065486070744608402031180c00c08156083e10078200d18940d200c0030300900c0b035140110410795814900042010054a00c000d40c0b0f002e5a03001040d42c08005500200700300e0402c0074080703480026982d1850407940e0401e4a032054103110b1a14074001d8044095900d0035130308001c0340d84c140c442c030400c01c0e0181041c10350901d004803d90b20900d0800c0822001080810301903059880c02d0725190303141c00120000a03134425003103078546c0d500c030400d440e00c5000c1000024034003034110004001525060326810f40c00c0c2560401c0d50440e0541c811007006000081c1c060100001030100382e4010315980302a80a05591a03800138501d44c0c00b03541103a440c00c2445026040500900b1012003103400400400344052500030b01100c8502e02801214254 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177183273 1250 177182023 177182029
    0x40e24010503070c08070f0807030e030c0609030a0b06040219030203010e07030501120b041104150e010504020304030f030207060b090103050309040f02190516050712061b080103110a0b0f0d0b 84
    0x600e02500450b138500c0000002c035a280902c2e9032220000340c9540340300c0070902c80000c0c072840c02400d11900c25174a400c00244c100d03007418541003110200b68440e600502000c2030b2170b02c0001e80004019008070a407403039a110714010030024404c547d0700300400c07041100c80c00300703441e0150015812141a04c16588403503840d0002141121030030300801008090b102040130100303d040302c840360454040c0520580000c003081c005000c07640b465a8032408217803030103810021f0700c0f08040340760700408042d182075103980b805a4008010000b00f12005081c5580400e19109000c0e20794095820318002a11006240d61607080850b035903080f84d241548100d040031300d880c02440c0300740259210903042d4082e02184004a001c00e80350350704407001d00540c048803a08844040b6500b0040180181080d1480300c40342031440c00c01c501a81c050482c405000607019085141050b80403412a0450746c00c403a0b40078805888100040054046920113072100e400490354614040c24030000380700713011803000b0030480d900f00d210074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177184523 1250 177183273 177183277
    0x90807090204060f050706270203100b030a021203070602032e030507090908120f090d02070806010501050313061a010306051f0309150c0806090708091c0203040e240105 74
    0x103420006080c1d844ea2018407402080901240b40c415100810b98526070b14082800b6860a124007000200c5660341605505040c0104400b0f1410f92605200318480c402c0469514104840024000e41400580c0d0b102c00c0340034801d8400035070f4071031410b658030f040c50700340001c000d903510080141b80c0b0181c011410180300000c100c0d004480d0f01ca009030444903d0302440000811101030191911101005445582c840b040903242c2701d01003055013201c1074144280e48619005a0440f16001c0d540481c1d405e00007040300041311411164241307440c698aa4502c8802003220051801c014203031800d19058002c103d104004580481c0030070b070303001c000b00d0b80c0d103d0400425442d440f441102c1911486080300c007042c800d4011480550103121500071180701c4e41402d00c2140c1c40804e4540003d0f030a0814000d491030442140c94100c0ca5510f80191a800e00488064541145c0710007000301103400400d1701213070f034003c1c01902d00800d0a80030a40151508078000034000c01d0241c18441001d20f0002c003440a5030285003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177185773 1250 177184523 177184529
    0x603030909011505040315060303090e010b030f040f140a03141c050402040b0307080a03080612060a091b0f0305010f020316031503081c0501061d09060409080a090807090204 76
    0xc0e40c01d032640380801a0b900200d05480c96020090300300408004164030283c40541b62076141c1000070124a1800d00618003000741d0082c00100e0101e10040020106240503a0303004010f10004104544070b42ca0484165503440710010304100b080c01524030a04c2c0c0128604040c1070107921142080c001102c07000019101344040b0700b041204802d41d071558400307164061948540701904c0051002d05010000b85000f210368002d80c156400f44810300c00f015030000442d90002c40c10394001490a1000101c03e4030386030014290801c0c2507079604280c091154000c3d02c0441081403114500c03da5890300158441c07491345001c1501e41e5802c0c20500000c145882c800c44c1c0c401d800d0710740003000c02c981c06075044015101804401d050344000913001701c00300350400024200070b01581241c14445280c3e585981c1a124140d0103030045c01304000c400c40c4074040c1d002280c80741480c00c403110700e100d40c2c6945c00a4010071a6050240c900d4401049031940b154010700c0c0c050941d00f0000032614181d0f507420071a02a842140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177187023 1250 177185773 177185779
    0x100e01050f06010519030504050c0301060e1605090105030c16020604121709030604080c031315120902011d120703051501120309050103020d0e0a06020d29060a0c0f1a06030309 77
    0xc03100c5c10f001c41c03180c2d02c001c0d0064800d4040e12484920000002e0944403140c01a41340b609100f81405000700c120b8154842003800d5040c420308203e07041002034160700000b401240d54260005038200b4600908400d100c5581d801032050b5242e5440310900c1c1c5500030a0300d4110390522403c050741100c40147c0e0265100d00794020000c1203030340e236507640381d0400350000c0b91640211701c01880300900042e00c075000d41d0050005011000704c148106500100315880c0c40c00460003251502d903503040942d1b80b085900c00c20102c6407180440d130101c4d4801050040741001010074680c081d0150100810070041616404403006614040150740c07a01180f030440000362000401007172081004115550198028008140712500006400030914810712f0030401055022136110380d0000c4d66800d410994420005c44118460407000c01e04040c040024140c02d040d40c0c114072135040454520700d02489031181144060b0701c80d410302c000441c1450210680100c02034000d004e40e954400059290030f00000303541c2808002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177188273 1250 177187023 177187057
    0x8010612080403140a0b0106030b1011060a020901051c050f0108030a0203030a05040f020405043c060213050303071506050f0d12022107060e060106050d0b03100e01050f060105 77
    0x15580f000e50100050009400500a1709a1341000c21540e4035514000c00e02c640b0301140203070f40c050070000748440b0f1044540c180800e0114810720900001841e590004001000594400464005913114041c0305c59082601c043e8043d80110b16015401207400b801102148420760703621813144c03035100d0051006440060740203000258a00c1919002190401c0c00b581c04101110b565030003150a48404a41c161f94a510004600c9242c42c859443c42030f40345070465035005001e154100701c4040100c2d081c800b4050507000b054030075135150351494030401418002d045035658411440d107502d4020340e028451081c68500b441c0024a814a003050080c3c5141c014005888014203940b00180a040040441c046100e41c01c503030000444121111101e000b80c04941603240d808038a0000151500b600c0c07181c05942003100108503558204041d20011801c3d44000701c0d040c810040805c0c5401e244102d0040d519060503032521080406502031030189009180d610301c2c0c5d9490741c0055500e4450002482c07540f4502d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177189523 1250 177188273 177188279
    0x303020a030c151d0d02030c070e04060f050106020703170307090506070c0308180901050301090203030702091902030c0d05160509060703030b0414070206011212080c091801080106120804 82
    0x200d110300c4444103200c3c1900142c243d02001506088600c60300c48524203190040300840034440811449090800c0d6100440c60001801030407521002c40f071052043c4421407002203010404030341c024203041002200d04110969449200a43d18007051000b9a021b40c0d081141241210000c400c0703911410450b26030201c0075107480140b042d298003070b42c001c0d1481240b01102000140b000001031100c15803c0c1154a0860000401c0003000c007010b03400030340b080e0b14003c0c201c40180c6012041d034400c1070b0100c0b81001241d6034440500781070780c1c0701c540c9050044c0c070003c1048180c024600241c00b900a90741000c2200340d0340d184038010790790b48203000000800d074144900001b030701d4900018a40b0a10910b0081642c6042c003000c1810382c0d00e154404401c0c2c51a407402c101c4901c0c1e04211480c01001840900000100d06403106042c00346000d458000300403800d000107004414600844070104406003082e18a810305550303c882d510b07802c0c06000c2c00b9500308100090141605480c003c1565007100303a040c9407a203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177190773 1250 177189523 177189527
    0x11090108150c0304030e040603050105100504020301080d0f180b0304120509091504200702040e0a0b0c0904060323190c05040f15030503090411120a05060f030d090e100303020a03 78
    0x4003c0080f800c006c08080380660580f00d5014030030017107119000100742d80c01c3c4200c1130a08001c00c2c3d0071050040d8414001000700c203d00145031021030301c40d820800c01050034841c08580d0315036610414101e21400035000a030002010300214820390180341504a008042101100d540c03203001100c40d4080b00380000b02d9048983c08005214101c80140b0018040c1110f00300600324510500c1a000d07940004203081040d0300b020301500f201c081c00900984042d040315075840e40012005030191000c618007142400c01b0785c41d03da00c110081c0d60040c01c103200c0b080300e13042c400f01c1051582030981d1041c01000040d100c07070200b203e40860110f03801203d50404c2c0e414501400024580010403121541e00c41d401140c2e8048118181400b031400391300690b40e0382c400d45017404140d45002c03021a242d1241001200d45003890b0000450b0810000c40000c02e90b42c590b0000100d003421042e02a6a250042222401069801c034148a048901200d081007013661120038040700040b1b944009009a00022810000a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177192023 1250 177190773 177190777
    0x1e0a1205160302090403120f0c023301090f090b011202010906020601060c0b04050c12210901050403060c1707090801150b07080d020c0a0c061b02030c040b0f03010911090108150c 78
    0x40034458001515203506005441927a482c0c41105000d80c002440e0150404400d884c044a110000d03100000035a51520380d8440e440c80c14070032308202e555922095032852503c1d81144024907001064120256107407410905501d4000000b01d011801c0c04100049040c00450028106ea82030344459035006c21580b1030b4000990028821111801000c000520640d589610304102c03c010000400071340440424819000c107401d409024100d00c00d002003091070717078007808940590354002000f0a129107802e030251800511891042c8581554004000c40d4680c881c2c803440403125124024804440b00c0307100300800b204203000300f2840b02000c205100100e00740b0340040801e602c00101c01890010303040542420301d80d105a007101c5400300c034541000819441100703a001c031981e0154040103010780c2c2c1e000030341e1142013141250140e601c65143c002240c0d6903004101035110301030b000348815680d6183c1003000b80502401d4a2140318000000b0491840000b07150359440180c546d8080c5980340e040740602d00d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177193273 1250 177192023 177192047
    0x16020301090b01030305030f0c040f050d0f050d080613021606150e0903271f0c02090c040303020d14070b04140a1a060114091e0a1205160302090403 65
    0x50340d218403403000003401c05620240214000d9880d00d0312801c001e201026070b488094150190301c0410310090011498120302c3c00d04a0304101d40c0c841040f02c940c41e0a0a01c004286000f515901030311000f041d48a4104070614403800049500080007141254040124012504402a1080b110303050b24006003007030b03100c90100941c44001e810784543ea40104031140c2001c0b111051070f6080031650000192a54200d021040440321600310701d052000080741542116982a110054080c400c5202c0305001d502c000d940c2a0700a0f020602e1441e08140c1d41403958050703c400c4005100b01059080410b1242d03c2c008880e00140c5403c0e840c000243d101d21550180180040d1804140d9010058540c03804200e249182d03072244145550350440b44001860050006000c64144003100c1c1d06c0c803504500400c2180c040000445015604808410080020b00422001e0a401942506022502003140c07055110000d105404a40400c108020590906030003403000940141e41000482c0019014540c88006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177194523 1250 177193273 177193279
    0x18030705061503010e0604081309110702091009060306090c0605040e041106160b0a0e030c031209070f230a030804050105091801060f08090f0c06033313111602 70
    0x10065140817500b4a401984c1c100c0b40881c00142407000758a0700d114520003020112410070041584a000555500c10284006d00c81c2400b0800185050030301c0652401519034a40100001603c80c907045008003001001a40c07126040c110021340039101e00211000c1d42c0c400341101080d900d940d99040340c0c0b17030183c0060340e520010a021350071030700319569038002c1d4280c0034296880090400020440449003258521035960f003003040610b10711240042210403400100000441c075581c1c140c207490410002e81c00c4860701000061001588030104200c1c0c214022006003800101007078801000b0840110f4400100000341c140030401c840c1d8081c0700501007101001c0d01c0c0140081411168002190007608450013069800c007840b0341480e408a00d0940c41907030030703005000e4083c0c0d02400e10364440f400541c1c94170561700000000c001c0c079240b4426035000c00c024125100c1c0512001095070120079607005c06401400072480c5920100081d020f07241112146290307a61600c004080d034100504250388040e60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177195773 1250 177194523 177194531
    0x80d0c05010906050a061412330412021207020f04020705190516080115140105042309070c02090a050a060f090509060c030106090b03180f061803070506150301 70
    0x220f041e030b005a42c4556114000021084c3c00c1440000d90000307843c00250282140d80d54031204070100103003440342d84075003001c1c5915204031598580150761066903680b424000e041d040c40200814040d043c1524500d0703400b6200c02c6010144c2c100c5840c02000c90103944044a00d02c03014041c2030a078000c2040500420582d03c040c501c0312020034118010050449466101c1000780f903000c07800c141c94130003400940d0020b012110300710084400032080c6000c0c0c200294427855454507284e000710101e4004103003050300d84501c1e0324458010701c085400c2e032441d01c0c01101200001010030344980064240f00781c1c0244020495100c25100d440100802401e46807421758031640441c1c01010041090000c101200001c1914038101c074640c2e042c01c1004c0c2440545080600040c00110b8001801c00240c46420b07141580381d80e80d4214249204001400c508928001c01d007015a85d21004511248500b6010108001d00f000c246003a40da0b034420700a0150168201d180429907140780303480704c401c40307a00c0140041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177197023 1250 177195773 177195791
    0x30403031b02071a0403080d0209040905100e0d0c050a1104060512010504060f05043306091a03061006080c04030b010e01061403040f0305030703091425080d0c0501 72
    0x1012000031001c0d81d1015038058403080004074000d4103000c40500302d8850140c2071602d5503940c003402d0302940c00da00302000d0b000318582106da02e4646c03051625640001c120340c0204041101d10000700002501900c1da0f025800b109144540104111142c043d030200042540410b0307a00c03483d0006240c282c2c0d255101c1c0d2038040000391542c81e004138a46500c07159000107480d04151030a0302c00c031043e0700c0904005074141801c100100d881c05400d1030ba07c00100034005400a013000e541800b20030003041202e1194030700b002c0481c183c001980b10700c0440308100001d00e090580c41307080541e138480c100e03040742d030582d110041400158490341c05d4541181e5441c8807641002d840f0f0703031001705041d4240c0062560f010b041e0010003a0030781c4034480d1415500122035081c170b1410552504c081108150b00058144a0000b02054465100f0360040403c183c00c0075011400c0d2100880180d100d0304510309144100e4003032801d07244035000c0c2c2d09441003102d40040040c030b0b84400c81e4405940b070200004040c0c8035556603d8443c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177198273 1250 177197023 177197051
    0x8030a140711010501080f120705031201090501050108060301090c05100507060c082509050904020d02040e010606140c0d140409050702030a120e06060f03030d02041e080f06040201030203040303 85
    0x34034000e07001925911400d40d1071403030345403c44005a00003420f40d400603116280e00e90021070f090004a40c080807442c1da904a9050941c61841080b100e503162420385c200029400300d080d407005058a0091381d0350700c040d454060030142a00c50441d0080d105440b00c2c1030401072450310201d500003242203400d0940c00c0a80c1911240c085903900003e44021030716501c00c0041e91101100b140700d0340c0900c00c9501d41003c4440b00009c103051700794010b01c0c1c000e4001c0300101d0150340c3c8454031000080e82c01401131095102810040b0701824507480f810300880c04841107882d03140c15500075100c112803510020840000c00c54002c44e07080d07124140f00300144008000c0880e00d240f9a01507248180c00c103400655030703000c0740381004088041000fa400170951400c141c054034090041082c58000500300c90b00c0d0621060040008e040d446003503840405240b00050010b074a109800030300f00c920204100b442002d81c1c0e58561152905451101ea4400307403c060000307401036000c0e502035038029019240003c1d503d0140162 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177199523 1250 177198273 177198311
    0x12084602070b0313020109050d0507140607061e0506040209030c0f011103070303060614030f0a0b03030405060a0c1a1e070c02090117010501090216080f0d020a2c060708030a 76
    0x40804c6000a00034450305658108080c88001d003030541d0b00c2c0c8010030103901e035a40c9070405c600450105002c3c08801c0e1100780c1d1018142d400380da0300500f0070002d811400c2000b124452a8200308401c250420001947d1458a4030031b4510142c8050301814544030650b0030082d46084000a4a06005008254440d140000c20181c00000e20941307000919900f003d001806084c041c800303d0721380c0c10b8100304001d00820541d03440c5800400c2c4c0400400c545084600090460046800560300040d001c01c143d60140c6c0c2c8a040403d00500820800d02914003840c5c1c40746200070210341020107031088031645015140ba082d24503034001c9452801243c40101540000c82c4030000307134400c070103010861000030807601c020301c81c050050079071010441c40c1c070b5014102d66000900c0300708003900f4a1004120120744800c03107411101032064a0904540d10060046d000e005070b114403840900291030b107001103980c80111070540fa1007010080c038241c2400300641c1c84000c40da1004240410742e58403126002084080302e02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177200773 1250 177199523 177199531
    0xb100308040806220210080405070504020319050606040b09090705040305010606110d110714010c06141602030a020c04020f07020d060c0e010c080901050c0712084602070b03 76
    0x101503c8103040034071034112258140c002d010448110480901c0040c1c0e9081c402000352035540c1460078266885040c41030030076416502c025081f83c0000104220600b8105d103a510000303507a901000583c07180414400c7c1406a80034440d50904100140a035a10700b0481c0c07658045114a0700320719240d20790351200e007034503000e0380304102044000d01000c282c860b0901400e1418401c2c0e1800481d075500d403101c03280d611255881007604010b9015080040341c0d120710765891010341c0041d414018600c00184c408404041141d070300d101030190003601c03040c00f03101000302c07900300800ea401440c013a4991404c000096000c1e0301c502c04030201c208410360042e101e5140c000c4600b4040c10000455490905000d0b000d80c5480303240310304114181d1000320002e02c1e503a054442c05102171a00035280d55010301c0c00c514118007600700101c0110700f10501c0040005490003025007924070f218400b4082400390741c0305801808455103d8240790840610384e1411403004414070408524030484150591b900d41c581a1a03005071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177202023 1250 177200773 177200789
    0x9060501060306050409170307030f05040b09060112111e0301141008010c05030a050603030c0a0c0303090b030c1b1929010509190917070c140a030b10030804 69
    0x21004000301c41d0103201d000020304007554240182003541c0e46d0f035490301901030b1040100d0680800407411652095000780c940a084803010401400d00e41850994000100c40101881c400d41d400401c01e204035001c00032045602503000c5494800d20010000b00070080d24800c0e109050409810507e076609001d40f81603041e1540c4c10f00020b04214150100500c0d0701d07000001203a04008480314080d80c41000c4036401510a4400602600c3c1d1100181c01c620900c03d04040c68400c03010b000052003045551041140d10036210800d41c2c558920b4041c0580c00100c401e6266204280702404446003d4014640c60b0221030040d00e40c4045002252800b140c3c2d1a5402d540c8009200c4503294070024178542d0100c0084c0d040d07095180c40d850b000c0019280d40e001400480b03140b6540f2040c03e8408904d4011032200341d8010407070030500c00c3c0e0603040161900b15400c180c425401800c40080d5414111446040303040010b044191044d04684401009a40141c460f4810089140c6c001001c900300c6806840039100c4a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177203273 1250 177202023 177202031
    0xb130e06220609110102060907050f041a04090c0914040b06010e0114030106090f050301090b041b03050d0e01032f0703050c030406020a0c0602030f12041110022a06180607060906 78
    0x940c00241f800b50300805804a0b0341c00f1250900c216921792040c0012150f003224082847da2410391807034410351020304100d81050910f0100710420840044c0c5405907561004100188140c0d6840070000e014103440250a221440b80819207a51140d05100c0d5405010304200d0314030442001a1885603200341e00240c00103010b0b0109101c03c4056403620742c0200002c40082c80942010f844800c141038003e400141200000e1050b1510240c012100b000255003020680c1c4024080c18800380c64960200b0031140000d18100c0c846558050300503d50600220f840c4c4c040740301e442201c24504441e800f0b15002c2e0280541407002204004003000200054845035026144c0b104013494810041c0465070021030541d00103000d004110000c0c80c0955910f18880c0700c001e141a00e65052410b200c003101c16800d50004214174103507021030340024040c1205d5547c0c1e5105141e2820f404800f000c490280105554001c0c4100300781244024448102040f03008000d090314a0a515680c400080700c410304401c4810300d4403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177204523 1250 177203273 177203303
    0x21c0b0709050d0809010e130e0a020a08060403120e01060e0108070312090b0703140c0a1a09070501140306030f100519020306010215071b060b130e06220609 69
    0xc030041c5580184800d951810f19403985035200459409507181c07a0741001070792030550600b60b403400d4500403034507403030714040000f40710340b0a003540c8540b14118142e000b0305680e2400070b2880400210a442143c02d6510049100301020035840030b4031700c0f0180c0a50540d00d40c0c0d004504483c02c1004c00e40240303101001001c0a0345140703804021100710220039801c2c05804075007080351281d04c0701101c0d50141c4c50301e443c20902019651030300e910300410511540510610b5038440c100541264000d01116000c62040003660700d0035145e40e0b07030310311602600340006c90800484500180c058040e64000100505030780b000b2801030341c1d440c0303415982180c1040c200d40740c10500001802080c80c1000d4114600410340c5149440e00c0040e6550b0a145044e0b18804010f900191504d44103081c0c2d10465500b0801100c641e6400f401c03c40003400c1025041881a01555a6234800701710b1032040840480c11350780a00030503507c40100c040007000120500c00d400c40726640b65000141c062003070001d264840c500c010b0010711 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177205773 1250 177204523 177204527
    0xf09140702010506011704030c080d05100e060a0308130b03190501050f10120f180c0b0a080c07061107030c0b0f0f0a020a0210180b10030803070804021c0b07 69
    0x1802410301819645840c040c01000d0740e00010b400c0c1224034103c4a000d19860b545011039505074001406001c0c5c0c4030118440346690003680280c0c0c0038401c004100c0121640b11000d44045010030346090b0380c082e014800070000039a03e00040c0504504a8201240040ea50300d0021b9056200315030342c104014181600007609802841045d0261074295a8076015140450106220004280c0f0800c00c1c82000c5144034000240340c0c1246200341c402120610007180c0c1c1c484218940040030504171107011054001207020101402911800280d40e90340e400c0540701c40700243c20603404541d0a403003203519660b9961110000c03000070a40035121380ea03504074102032406d101440a80c007030050103000540c4020b007d000100081182d411989103040160b40d0100204180e03d41001e03405541c69042c103000020300c03000e00503280144160b020301c00d40322a90390382e15411b5100d9101c5001c01400c07030f9010f10200e0b6007144241d0030380354024130140c11303024000000210044c0008841c101114070384101d42c2084511a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177207023 1250 177205773 177205811
    0x50a031101120207030909051317030603010c02120a0507080c06010f0f0e040f030315050343030f06060b12012d0302090c040b0705070618060f030b0105040f09 70
    0xb07001000443c1001d8030303660000e1050b240c2c0c1c851446095200d001041c2ca020700d00c5610003d035a44150301d50f0172841311a2121000e60402c80340746100e5480c02c98140004d50011400d9062100c8841040c1d24000600f042030f20304d0f4108207000d40751190284aa068070807005c01140340a4403c8400400b49503203012003100c0070140365000504090164010304c40080c61540c040a1006d034103081c04034200c91003801031008a00f080d4805580342c0f041c0402c50580e070402d512003554154507003412025040c41a05a00c0303040c1d0b926100001031902071030041020818505c81125400d101e50800b05120f507560294803203030703003107000490310030030f52180108011158580041b8481c03289100300e84072a80c0d070f8100d9031942c503041d04c000303030241c440c180000d141d09102004031800f074021004101d4a810721428100da4459890081c03001281015500010a41005950408954032650780142c84209020128050070b640354a0505011050002082e250408036440300a44405440080c8403030411071040009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177208273 1250 177207023 177207047
    0x206041b080708060103150c17252007060207061101020f07050d0816050403060b1206191512081803030c0c031006120b2203201506100306050a031101 66
    0x704c2c0c94101340041190704035500c148000d4100140c0e420541d81e012811a41c2b111400810503a51406803030f0441c5550050402c0c480f40314409581c1458020100e4074550f5001240079100241e13104890030050284078562139244440618000340c141321042c891a003040c0c00042c003c89098101000414009500155880d0302c944181c880c001140e42044016010344541d00005e82510340726025030f1807684078401d03c24010106501100c44500c0e000702d0700203039a80320000903007d05060202c11503241420b10407410540d4840400d400e840c0040c0e580b400010340c441c4001041c020640c0031801400e507024009080f0021584d0060a8411300c0c0c0f0782014107000b0210858080c1c18507201d014000e91802800c003400056100c010800396442d51548001400f0b51000e1a040d8070303450707100c56030815604c9a2940560360420821030041c80031440c0c503903140d00c000700505e0100f0a100000401a14101e60070388600991400c0006001d40c4940109049540da030b041030790210200d034075460103564030120000071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177209523 1250 177208273 177208313
    0xd05070e01020f010507051b071203110d0f0f030b0414010b03011505030c09060307170a0605151c0b0d0501021305012a0201140906070c060e010f0206041b080708060103 74
    0x105c0e28204602600c00e0059800071110003d803405030081209082080d8030103440c480e12440b5900742240303002843c451204444419a000d07112202078460702462046120800e2a101d0203903101000d00d08400404442c480168016120000b0140b502003074074800e40682014545913591358108003c1e941d185803003244013800c00008000300058400a603065800b80c2000700c0b0015900e8848030341c00c0719609078899102c0082101641031003131b124040e070b00180840f80301b910349900f01c4125460300c0c2c07001d000303101c1d4908180b00301660241e151a201c0e8440c003144800100021008a065280c83c0c0c2260801d2030285001441480c05111668101180c0d00c50b81c8824041494045401b1b171510030700094040009040c00901102999061a01c00c2a40c1d0b002c140a040742d074558070182030000c483e441500c2000e02082d0001e408d096130794410901010748100780d03001040e140d2120364461090556941e100d81d500d4100450201c0c0c201c2c4140320200c0245403a03030080c4102e5040d4200110903400300c1c111810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177210773 1250 177209523 177209531
    0xa0c05190807120e15040315090b06040f06090213050a0512100b0105070f050105040201031424040b09010e010f050d031b060e1213080102041a0c030d05070e01020f01 73
    0x1000601c0c08080703902407640100e82e00da107a0042c000948040d80140004c0d580804c0d00d0828007100c0039040c1c0508120707130044140760b81100d02d184540040f01c2010305c014103480582e50001d403090606401c2141d40c01c10018002a81596030a000c5080760400c409110500c49951003c000350300d010011680901400c81e02c15503500280d42c940c654030308414821026032a290200382d030781c5a024030291035080d41c1105889107101090325115000b410100c3e8100d002c80d10b0140300c1410701000400c0320388103201c0c0e0310020700c94a01a5400a20240c0d20984040d441034403030300c80e2038050b00c900380304038000e1140c003410044c1d950415464220b000b0850b08581e008185101c901404280e000c40b1285008100501d0b0301c10307030406030404201401d10340d100d403002403042c03d0315000c1c01d5034524000c1403100202040410b0f15510383c103c0c9400d0348500e1242d102c0110041c85804102e28480b0000c3c01c594100c40100c1e49003803105003002090303500071591407001c20741d034a04811041d60103010480740b512540d00208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177212023 1250 177210773 177210823
    0x181201291c030c1a0c0307030c0c0201021002070507030f0803191a01030e1e16140303040902032d011a0309120904021e03071404060c030c020a0b0a0c05 67
    0x21840c20165001408111440300900180300d0340d5403042c0f13400c90a0341c960b41164900100c4000455005680c8440000c0ca84403495070f06500c20f2408080070b9505078007a10750845c2e0b1782040c50103500a40c0c0203032140e001c2c2100000c002440c4140c0c4040072442108144d48030710305000c10020f070344004811102d01d5420088a01c0001e540340561002076042402c00060812041c80440e1a04004280b1800d00341c0703954003950b0304460001401211407064030000210262075000f503000c02d03080c0c0d212240d0990f0040c0424003800d00c254026503402440030900a5000c08427440d42d0810b40d00510841c210300384e50100602482da0380ea42c802405200024102740745081000c0407558401c10042c0d1440148000b0500500f00d07076960301100e8200030740985581c0b080c0051440c07a046a070003590700c0e40210b0f1910f802101c030513101206503001c4070356503140c0900c01d10030717500c081e034002c01d2458049901041400000c0385440441c4040d0424886c0e036581c05100403824a03046141c41c2111b9841e5480d008800400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177213273 1250 177212023 177212059
    0x1f0e0105130e0403031805010609060812030103140102071a07030501060c0503030a0b0103112206092103050409021809010b1312021903050a1703010b18120129 70
    0x2240450349101c42e206515641c3e400d08600801c0c8180303540d00404a0311070002c080c8001504010155481f80300f08022003a87da202c555035039010620346030404d180501c01080031943c6030211303074912814032001501d0907405640c0d41c0500385030740544142412410090020031a4140300311030252085080074150b842c52511080d41d42c4c00024111200191192070380c1803141d03c2a0080c88550b12165000c58503031800401312494803d4040c10622450000640001c041c2c0c400c0e610a0203d40c1c518074000c607014412031403100144480017040c1d0510104000019410380540700030401501281c1c00204200c03c20410024884c81c103901242c503010701800403c0c0e40c00004661003045034040e54405000310501d202085042c0210421031103e10103c20b0004180100401c03000d810b10b118144c9030b4648101007101343d10302e01080c0148440802e0600101035007000d400f450700440c5000400c003202d044a0304062500355001e071546c4000500c20701034511070303c501090b00e03892040c0c8110380c0d01404e4640002d078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177214523 1250 177213273 177213307
    0x20f01060e0402010c023c0f0f0a030b0c070503030c0903010f1e0f0b1906080c0a08061c15150501031b0c08040306020a03090308090c10080c091f0e0105 67
    0x1074030821b02c0148006031307846414124400c04050001601f481401107064400f400020300300b030750082c0d40414100f00c252828121703001000740020031400c8410300315220402510001485942d4003c420405003000c01c0d002c1020310310645e541d4040d9580e6410000c241420346251841a0403003600b0020701c9242d00c9541040d50b01c407203550f2200002c03038124140ba00da01420b103100300b6581242c0e00400d09141104000c44003c280c46c1d0b50703203c1c614183c8440708020341e03511450102ca80025004c0020855520740b04035582c0102c480070144441c0c0c0305a079202c0d80c0c011040d2805e03d01d0030300d80c0d502091420216400032070000308403d00382000070030104112500405041050320040003007640034002007007101d1095038050340c1c0184045440703c1082c3e9024004042034001a80801c014000040c10b40b1000500d03c9035507900640320007100160703400305407049000608031510400043c0300401c0b941d101c02141a18811034182000d10450364504040c080c10178011a01d81000300800043c0090755071166 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177215773 1250 177214523 177214547
    0xc0e092205100e0d1b03171f0311040b090915192a090602030301090e0a0f081216050702040b0303160302030405090108010e070b09220212071b08070f050d020f01060e040201 76
    0x8050700c0d142c1c3c0d0224009180318036151180e1801520310b0020083c003c041044d600c5090041d601000007038500333002c112a40c401180d415440c1c0c0d2081801a04488502c4151a0002c1c0c46440d80700c0b80c4a0000116420b4499540c424040e08950210682c580c0c140e40d1024401d1104070700b4118801d0341803541c000e4076031105004000420780c942d01070418152081100c0c6000a0700600f0b01c3d0704c411203c1c60f080c00300f0790002d4203a400840080c00441d00c200c40300c10a61311044180e4940c00c2c5885125030912003e004503004541e45408280445a0717814541c10304011002c0c46903015540c0e881c14202000440e00068100c9a1207078500064034121450004010003516040d001c3d03652982c3c02d40b0000f8905640c01c8407040d0b05043c11034180c80e02503000c1e8014040f000d001c41c0c50f00c2c11903621201304039400196860751045010b0804111008100040000c2104174000c1c0910680d44441da212240b86c0900804038200682c0984500b183e0709400f13106d920050001070f80100c40c0c40c00c0640000300000d030700b40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177217023 1250 177215773 177215807
    0x411011b03031a03030703050c0106090209060d0507090806010b07060e060115050c0a12080105031c0e06070c080304030803090f06060a2c07030c0e092205100e0d1b03 73
    0x50380541d2a41c10420000036003c0003012295a103407a4079004125420480143c2c90399070920f54046040341d0180203461202c2c1016010300c2c10030300025994006880c0280070a8140b01c80c100000c11403840034020301c0d010300420318256a4962461625108070b449124141149404c42d81c01400100325511940101c1d0040e8a08180c61340554034900f41408510200101500a660074000d05940c210810b141203c004a0603182c40401420341360700c0e400c089001c0840080d50701d07004000c03945080c07809441e1f52401602800301d1941c541c029185144c2c056001a00c0c3c2c41c501104014205c642088000c2003103098601412541c10034001065401490340100c140080013900e140e82c0700c1000d0054041c8a000300d2044891a00b42441d0180090403c40007807800070303800344e860044608042c5401801070b50b003800281e0002c0070081c1048619205003000f212180101c020740150341c1500d005504013401940040c0c080f000c000e14000d00080d008480340000768500e100101c1c003094000441501261140e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177218273 1250 177217023 177217031
    0xa060e070b1201062006090d0f03020a14031f0b030406051008060609070e030613030f090e0a0218060315030c010306060e0d0212030408030d0f050402060a0c020f0a0801050411011b0303 81
    0x4591721403200101c48801c2c1c110f215002c2000b01c17070300c00007419856015a5840d840a40707608408100d040e441109291404210048141d03014011351300300641c0d000c40b851980c1d010001d070080e480044821103034001c0d10071103800310a0000f8803500f4031826401c00c024501040460345410862600c50000030110352150240c280010390b014021084191604002026038032107180902440c94844a60f08043d80024011100200d003540075030300d40c009544030b15164100030364607424101c01942c440c6182480044502420504507140c0b90302850165075140088100b03410386101749031904c0d000c014002c4c101820043d0820000c0e40103080b510b00310601391184481e440c014000b0420004070f030991031130f203813200040c00200e104012000d4082d07034102407818420307184051402c00550300169006035111070200a2806405d0041c0503545100780b000c0c20543c14000c420b4005039014017540d106820a9450310100020450340c00c2550b0305c011000d00740381d4010b00b5170501d500c281d910b860000030700341555 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177219523 1250 177218273 177218297
    0x604030c140303040e012c09010c0210050112020d14030a0801080d080f062e02030a08060d0b180118030e0108060a0612020c030f070614100e0a021b0a060e070b120106 73
    0xa2181c032554011540304404402d4123200b01e03024002c00d02e007906034005024500d050002a00180503c504840d64807101d50303002c10860b0200160025150001c03509881d1042c07102c40001c0041c0f01a10ba49100c0c1e813210400d946c9480400b60030300d264810f0003810801c0107000c00c0290b41400304c04580025081e5103003844e0204860300c203491141e040200c06552003900e15500e0015038004024440207401d941c0c0c8401f1130700d52000b8800c03104103c90005000c40b411400145601c002d1b81c0000101c0e0200c0750000c1800784102c0c41048100c444030000b500091030404040341f04e9608030401607004082610302480c0700d071505c50000c003101800d080134809542c0000300c29084100030029a00082031300d581c0f280da141983d01d059030080410b0252840c1020484001803115402c03680c605046500e1132500c5241640d903028210000c2d4010305076103442d8110100c1c07140060204200814002c2d1040300001030705640070030b9a62401d03810360701860303001008008041080c68603503e40e40c1141c110742448c03500040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177220773 1250 177219523 177219569
    0x51e0906070b1f08011b08061309030c0b01080f0c060d1e020426031c1103190b0d0201020c090601020309130203160507020d110307050604030c140303040e01 69
    0x314400001c1c184542c1c1c0e0081c4500d8600c24000340d407205040195103101c482e5116542ca0a0380c0300805028189003020203800d100e54095445154452001000b034071182c0040d00940086a050f140b0a400040c00e52003481e08100d00004c540340076158110041c4608040c04181039510b64a41804034000d060114142031150311a401c11240000c00d40c1c010f440003080b03070000c1402504107100e13400e008484d04100703c0207441d905102541120048000c0c40c501030300e1002040c00c06071105c01587c4110381d03c6103000c00038a42e00c0c0256019140c02c0060520860203200d001040ea55809030141c0700341065215000140c0e00012045042d01040d2820120303a6a1748005070b0650092040441d002900024104480d240030350056100760083e40e0f00b041001c0c2c50031821200e0740100140250411b424246960209000740c103d4250740800500f110903207038a66010540c160040d41c011103000c0b0158a040c03180742001e840c00c00c00b080d006c0d0001d500f003c0c03504200e036103441e9040c402c258002119a08800c1149 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177222023 1250 177220773 177220777
    0x190b060d15060b0903010f110a03111303030f02011a0105040501080a1503051f06030201090902130801180212060c03071211040b0d0506040504051e031b0c0907051e0906 74
    0x10080384040003403654843c181c20707003607003d0160700b4403035441d1000901441403544210b4504414503e003aa0604035240b80075402011100006002442d09000e0001182100c2d0421401342d4441d50300d600400100030313000703403d55004800a440c5a012850100c2d403d903030100640f001c41d103007440d2000e1075480c0c1d07043d004000c00c031107019900e07004040c2c00e0100034010002843e44540c40c4200c041401107009054180883d03a280c00001e000410315501004400c5060b0060000007038500312441c030003541c8440b02c070700315202d403250b024040c1c0c212400d00702545402c180341d00c400c036800c402411141c40d144140c2e121500c0b00610200600c55030310b1642d107a00240b0717032155180c40001540907503526251300703070828181c01c2080b00d20410781c14003001032405d0525004642c06503900070000c1c2825086400d040103100c546481c3c2c1c1445200502069200c61050f0600d1003a01100002410400c1c480c070b411721503070300d4008242006100e000c111503034000c07001c054a0145000342c002d0168560540e400012814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177223273 1250 177222023 177222053
    0x3031c060807120b1005010e0f0102030910081f03110103020309120a03090c05010c0507030303020c03120f0702010b03030c0606010309020604050402030a0506030f0a200411040308040602190b060d 86
    0x500c14442c021035004001c031029400e890080283d070710142d84d000080f6030481d2081c0036290001d46c403080c1d19461810980b83c031940c103540500640741031920b035001144480304000111030020b403d0000b80508081d40b0001385040706c0c500b0700c3c402c503903a0844d1580d02c03807031103800c01117810981d0001c0081c145c16018401e54a410303610711303440b582c0c0780d4070083c009000c1c000c604002d480082600c00b0000740f5601031240c814902d9407081c00342800c0b80c41c545040d0004d400c280da0005150200700083c02142029550981c45824650090006810b04103002403c5521984415004e58170030082145030380e030f000554982c010301c00d20b00450303061f25510201e2043d004541c8202d80060010060044848050304030340d200e9a4254100c0303094595035008141e4075502c1240240078400c2d50392003055110440144160709a801400100d5903d0020b1039400c00c0d0b601c180c0c0151080e0b00046800d00070240e040c8512000c0e0700c0c421000c2104800c4c20388504102e99405481903104004c000c03031920812420410003159 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177224523 1250 177223273 177223289
    0xb0411030c250501020702011701060c03110c100201020409050703050c041401050702060c0a0201020105061909050c0702030a03020d090f0513050a0e06151807080609090a08070309090b0f03031c06 86
    0x30b00480c5006400b0307403c0b403c0c00324041180c2c4110100e20b010020f4040e4121021030703a0355032981200703032019500e00c8c490035000c40d4503004041c0030280c02c0c0c44699084c2c00070440c503800180d07210300c0c00c1106030482e200034001108050401c8107000b071a00703080041c0c0d0309550020f01403081703020011005843c184a41140250000d00210340e200f40040302082d0440214005c0c0c00a020f1692100b040001300300c4900c0c0c0d0a6601c0718002c4c01841a0b41c1300ea800300f03074000303521050380f481c142e40d54000900d003100b901c9041300140e110b41c04201480d54405004030041005e1040300000c9130501000400305c1c0320b41d003600e104403651000000c0d446561600656940a203520a071142c908000e0503601300040508021409400c0e0074400c2d115400450300c0403880b84003166517520641d1220420010341c08005400c00900740328510709440420b07180d00003071200500c82c1c3ca032805010300d00412107007510f20b03450255102d00a43c0d0031012550b20084202c928083d881103100490040c00c841c3e50000740490340103000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177225773 1250 177224523 177224587
    0xe01030f050d031b111501030503070c061115040f020a0311040606020f062a0f0a0305010b090904060c0c0b0f04140a11011407051507030b0411030c 65
    0x8103004032031a04004550050040c2d4004580525040d0709480304d1004059054813a41842692548580b451030300c00703078046050741c0c611002c6200d00901c00c0340a0304141c500d600005044010030081098601c024087c0c0d00300720341819a1994195111503c449002822602c0f000000c3c0401002c01014542150f000300184507107a01d07405c0410300c080078401800c2c0201e1074200042005d41c000900c20041c10003500c01854030307030b807a040004041540030341c81a082c045007404401c500d002e400050708101084800f89a11000707140c9004040d1601a1b21070000b483e0108081c2d8441c2d265030307c4103a03200ba08080007242d40030b141c80c0112203030504400003034140302400301801200410007a05500450144204080000d400c10040341c031044101f500070a480100107698000b9401a4014a4490303e9954094200103043e11a98140649030000d01105c65040c0104100c581d0103109080302c04c0c00a45040081100e071036524103441c800548058128000498030201e40092280420300700955a00018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177227023 1250 177225773 177225779
    0x61e090a0b101809060f09020703050f030a0b010e0603070804120509041503051216060f02160b0601110303160507020f030d02060106170709030204150905161d060906130e01 76
    0x8008100001580107142c0d0283d6001420901d0303809244161512484130000541c50032131907600940c0425022406d00400303000a0319071b00800c2020f5131003202311400100b4111701c01400102855242000d0901c5080144180520280c0c00b80b40c7c1350740980d02102144008005410540300e601034100540d030b00c10701300218044048400a02c0000b16445030003128542d907611500c149880c01500c00b1100000b0224401030f000c00c81540040100c020401c81c018544110f07a17450b80c106400c010300995480e8440014000f00d9680581c0c803550328585840694110f08020310f545034690b02c0300c00c1100c00c001c8041b030090203542d107810402c030302c4940050803150380c400ca044001c0c1d01d0b442e00744a80000304100c0d01504200001080565100300c481d581c44401503400c540c2008010016400c071004000e10107031001c24001140d00c2101c0c0100b1621140341661400c18000406c01e03454544681c0f1508124a0307502c40e20b0320f603901541e00803a002c0750104d40b03490002e42c034250000041c1c0e001c440400c981d00c1c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177228273 1250 177227023 177227027
    0x3070c03030e0d053420040203010905041208040305040504200301080105090706020a030822050d110c0427050f190c0b03060a090203090102070b010e0a05061e090a0b10 74
    0x8081c400e20740407244406410480240b800c604034040d44140c1c00300e403000448005059407003c0981003035445210381802ca1b8010102e42260400d07000803851558802c140002d00544490842150082303160140c0e0303c1c50300360f4004015024520500f4021911840f14903e90010031084820b0014499070f0b050701c0b0741e50348903454040e1005442d500300d503024031070011582c0303440825804d804c0e41e05a100c24115454102141c56401c0d41103c0d000307a2042400c2c1c2c00400182d05000c0114025070507507490074001380710f42000b03082180c0f07100858443d500e0200f0040c018003043d030118024020f41d100c0c1400204150170040d04021030700056003500d004441c0c1c2c00c81d603810407980340b0558600440010b0300d920348426400c00544001d03504d00c0c1d441030180d04100603851294004691101d8144000b40c2001c01b541d40700b40c1607000030780204150300c14000070802490b40d20b10441d82e0241040700c50380826045c540c0a950401c0307d0301030141c0109040030018418045607017100e0081c0c3c03406069041848284040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177229523 1250 177228273 177228277
    0x9050102120105010f020d1b06020a0f09050d02130b0607290604060e0610030605031005010e0c070b0f060f0a080a1209060e0f0414010e01090f1103070c03030e0d05 72
    0x3041d0345804000d4000310f40c0e94411405480030054580045c80c45111280c800ea40f250384200400d00c0502c05610700d80300040285c000b0742500800ca07101c0c1100000310403c083c3c044c207481d8101500403005031030f47c0400f603540c42d0340c4010b00e13050a100000b0340c12aa000450380300e104d45a00542030308102c2e282c1c0d02122110308450091003c020b140000f81d6110401004180c582c20302c1a00a249032b1140441c007140340440344e404a09080d0309000400c0c03a9500c02203402c000e0881101d00b1400d90300c02c0100694045c4600d160341c804c041403102440c003560b40e074504204d20f0001e419500b03100318100004105880c0c52014142c002d00085c00180703096502c00729503640d0000d10700d041b6504014045201440c6015200440540d629074452040c0f11240c00148146005414000d6912a0321480c00300c00d40252022007602030321515001444a40c100700c070b80810b440320080240170051a00e200002e07800d4422056903002050f84c41e0510040146040440141030136800c0c01d00705005001e00344035501d80002c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177230773 1250 177229523 177229537
    0x60c170412060615050318161d0901020906041203090e040809041b140d09080301080604031107051c02040b03070b092103040501050c10110a0e040b131e09050102 71
    0x2d01070051644a1121001d8458035800300c1000c2001440403e5061541c282c000c21079040c0c0c40104c40004880611141c00c5050540c02000754110817108228480802d00da2540d0200c4200700a6103400d43c0e041c0403a140388200e10802281c86401c921200405108066400080204400212403802d2a0828445c554015405203204515005501c20541c2d500703468030590016a4451078040094002d400306150b10030300d940442d06a48105240001d2180c0c4080d502070030701000240058503040c600640214281a02900b1940c0820410030032542c03948101d0703001d50b181d07080180300300400744045030240c0b0b410414a80d242c0a500030204000385080080c0840d81003c940c00c504044103207a40b401600183e9161160f160420441070111b94001c01c01007850001d02c40031150049c4d60010307050122641181e8208504400103400500103074891000110008102d408101450b42d0000003141440501d049040a54580089072000c0c018488100301c13881646605100e80380701c43c0340450003540504c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177232023 1250 177230773 177230783
    0x1113020d06060e0415050603070c051e120f031302040b0402030f0a11090901050d0f02090c0d0606082202011e0818030f0d09061503031806020610060c170412 69
    0x100e64502d5601e440d00038005140400e171007215091382890203012450340b0041446091040300d44103c0005941044103599203000c01d1810341c51a1318030341030917060203d904103046018000740320840a094420f01242d421280c10100000818928804a00038207407a51002c0c1d801031021040080940450b0a480c0c426003400108101e20914038407001120300079081c0403900414038500502090511035007454085000d041c070070300e0800c1d4a60002c0d155140844100c07010180100c0d00102c400002c0c084c14010b01840d007461002c07483e00010920f44040007440682000d0744440020096900414402844443c410050300ba141200300b4041c0075144191201203444082c00e62408800c00301000355110000501072052402c90040c196101401144009440142d138402c1e0380c8400e203000740d107408010351084c3c5401c0e280ba00408584110f10700c607a07000700155040310f010410495043c14514058030802d0400945038420340c20507c001c0328107004240e4101e0710010700400c070504988114403401c0c1c410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177233273 1250 177232023 177232037
    0x140307090c170c160b0402040212070c1b05090c0d090507080307150605030c12100c121506021c17040c050319030c0f050f0607030506030106080303131113020d0606 72
    0x40f0b034001e40d0f03074452408502036841c041c0c070204000640303a000701504a400148003500300900b0352210f8890000588282c1c01080c100905401004000b410003404a03201c001c640119901e410007140048000604004050783e0014031020400880e82c440300c021508041241d00b81529444801d40d03036804281d05843e500c0d01d80c0ca0014085500d806910705680c00940900007904890091041d0ba1402c00c280080e54041c4000218001500d4800d0003044c0c5800d554141810805040c0001121200c5454102c4070201e5101844000d800141e00003000c803032040445040c14000c0ca0407281c02e40740240c0c4070050507030f2a080c001131004000242080c0c6200310180c0f64107441e04221004110424a8007c0104d520480c41030f001c00d103074078800c44a1034003800541c0c12019580e441c05003486c40845c4d030b050220b96144103018440c2030034030940029281c0c02d4001c51a60421580e07803922143c0b40c1d6001000c5501003207101d0030039211905102103c1662040c00d546802c0e5000900e00501014000c0c0c00024501c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177234523 1250 177233273 177233281
    0x30b01020c060c0d030908040e0a05010e060d1a130501060e071707020c010e04020c01050a05090105010609050f0f030a020a17060f070e10031e0506100216140307090c17 74
    0x410ba00700c5400100381d50042404940000059001e48041e010035078804405110000700e04a5000080b40716400110b00098998104881080d400c40301400c407a00032481100740c000000c410711142c0c19462056003400100c0d503208510001c001000c0c20008203e5424000c0000d0032603c1111014020412922403249010301d980805a031140c00b00d0f064030050b0f0042d520280c0a5010300d054100321100948090f150600600c0f1250940d04159150b04010340d0710350412926903400c0c41454050200303440c1414902e0324220004103180d0300110840d108071103d101540c007540d802c008040b4400c1d40900011b142c40d58940303401925094005185003c0e020b410002044140d000443c01e00c59081920303408024042c0c80103004034800c6442c002000d00d940c40d40c407041c0007000040440114a250b00010445260100500c040140f070401c40609540c44210841c0300360002c60b00901c16502d1a1500e03502544c04800000c0c50407289078421060546494014100d1729071001c2c0000c10400d00c2150741c0c04a8503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177235773 1250 177234523 177234529
    0x40c021e06091f0603140607020106061e11010e01050403020d030b101b3e0405250201060302060a0306090c0806100e03070b210a02030402150f0705060106030b01020c 73
    0x900316800c03442d0b90003000d441420480c54041e498a0340e4400c800015001d40c40c1e82e100802110480421141c551007041008501e41d82401a000989128940488800b4818031182c40b202d08407016901442600c62541c4c005103025448030b80d40c81c0701103000b44a103080a003806912208807002c412300207410140d4410050816141c60b2603003500c50350380c03580e0400301030b400000301200c1c1c0203048864945404020004040d05200202618103140c3d182d030100070242c00103200307009080b1000e40560700348020031520004e4205100c94104031844012442d8045000c2240108005d0f080294864404150240203aa040d480102a120405c1c0308108821544c8020754554030119010759000303000904041800344680382900c420f0a01808880400340c031030490070055007040d42c45195031640c0a010048000d0f501b44810f0b04000c2a0000714610304068002c03400da17500141d4a08400c0b6400070346203601040384403c4403051900202541c645585030103008002d402a03000c011b00520490701c8154842c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177237023 1250 177235773 177235783
    0x2090a09080405060f12070503060414010b03130203070f0b34060e15090a050606010f0e010c020a0b030a060306060512152d0105090c16110a05040c021e 67
    0x41e8000260a041c1442d0000300300c9a0f5100410041303c8140c01d001010350540075206107401090551205904c91415505000407280b41c00c82845806810b00010050003c01401302d0307400401c410051200c1c2c105600220340361903056400400d0380c0c1d004c1900010802c0081000c0e1a610003150b43c1e04240c15802048840c2920180e81d4014120010441c00400076900781d100480b500d09900581e011901d10100704c400482e03040303491540c150805000c1d041007060600007240d119109003030000311604000c2000b001030341c54030a82814000142d400d44155a501042c0d08010700d600d801c10b50707980c640a01a80c02a00035440b0464100303040c2003001c01d543c41c01145e056000490040240440b001500408a03164070103440c906e000c03c1c0c604a01e2504c004120030350000c0d110700d092106036035490201440001031000b06610902c20041c041d803814541300c3c0d1607101000c3c1c0c0100314100c50003001d0001031207000203a84416070042c50211159000c5d500468424440c2c000300c0310a03403845018810580c0ca803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177238273 1250 177237023 177237041
    0x60f0d020c120c03030a0b130903031b02010e0303010306020c030909160e101b060902210d0c0f03050a181706010e090a0212100513050c0301090309141302040905010302090a 76
    0x2e90410300c006203000f142c0380c0c0701e407901f07034001004602d5004128000104503041c418081d0002074941c404e4052488c40c0c1c000390444004548000c0100381000c503c0180c0fa070006000040880da0001071410210b10100700383c40350b1510050140d401030a0030845006d814500c00781b2030700070441046003091035207130103d01190900f566455548038100c4440300d004994581d44801c9400590b01d0120a001d611003a0201a40890951b400803464540c01a4145013020306c03403425082010703044c1a0f10005120b2240000c4142d8181069515100e03c40760a40384100f1801a00880d10401c013000180104404c1c0003800208d941002c0c0d50a5036201d05181e0f2030404100c2d5030500550205040100600f018010589200ca00380160703007000c011407142d5000d071801501d03200300e9148402000c509200c014090044490000c90080048508696014064010a20441121040507500e80e04143c80da9109550701e2a001d420071590740e6100c22900c002400300f800103901840504001426150640c4110a40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177239523 1250 177238273 177238297
    0xf15020d021c120c0302071b0303020c0418240c030204140d030c080705070e0a0b010c0b060111060103120e030d0219030905040c020a050f01060e0411060f0d020c12 72
    0xd810514100074040c00c40844580100801c1581d43c040c801d003580301d09461582c030350798050b0750356425042c42c07203664506500d034004000036100d040000940004002c01100400e580100700b4901c040c844512156a5000240910000c074090030310079480e002c8044418082840c0401c0480d410f150110100d000300c0c0078061240c1412541384400d480c204c034840d941036109180c03640c5c0c0d62509948100b504e0300404e40884413070744407c0f0107100b901c10000c0107a5000000d14010421740c0700c120002403c1405541c0c0143c00c40404502049040c2d1061156604422281d000c45825507581e141420f0912a0225a88001502018404104d190105400c1542e001c0707176008040041e01c00200d0007410110312001c07000e0003289900080c0940b00c9006500c40d80700c068018110351100c03400c100e41400446170f44440c1c40d900d042020300502e1003000c8880e8103c0c0d00050942d003020030320800300325680b1540c40d008489540200c3c24841d07036034240e0000c01d2a103440364240d80d8408688401c0c080503000e41600010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177240773 1250 177239523 177239533
    0xa0305040203240c031015050703033e0d1406100c0c0e13020a0b0c01110f070b09030c03191209030e0607020f04060f091508150907030204060f15020d02 67
    0x4c01d541c0041c2c069a00403172507101c07078140176584540045800c082e48001c04086040442c6040074903801d842000c581070b400c0b080c0e40044181072503418880b4103040d240349001c5142c2c10700900e16181040103840c43c01000340e1040050100085402030400421101c0d2441082004006101d1500c2600400381c0c0d0b65100407014062401d02c0c020b200c0c5408020480011502d2009241000d03a031801e051800501c3d2250745d49035100c1441030aa4203561418001a00074141041892116040d04088556558000c4086082c41c5c80d116591404c40c03041017640c40f9503100c0864410030700c1800f401500310025194950315140d400c00c102c52000e80d000e80b100a00481d004080c903500e0b500b08030005203450ba10040c454098030110600150480d110b40d001403607a0704980100f80106810340c0b18074040141c9040700a14070a2400c0b1a540d954801d5050700d41c158008400404c4808604003c440f001d1a4014020300c122a03d0340e4010103480c9662041001c9486024110446c4078000319403810a14540e9010302 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177242023 1250 177240773 177240781
    0x24020d0f060b070b091f02070501050a1b050906121e070806060711030f07030c1401030209090705160b1e0601030c1e1808010203070908191e05030a030504020324 71
    0x403550000180302171314901580c025600040c4220207030040c3e40d0b2400c400161501c0460405070308407a80100b2051030940340c0700358140340300e0b2003800510701c80056180c4241c0d00c14004010888602074100c2003003110040800b8401c800d00800400255440d0114035041940d0726600d08840030380c0161442c40e08604100244404940179021107000c02c0e038082d040f6030036011800005450403d60303034802d4410280c001d50074000000264058985090246015420003801e02c0015104101c044c01d00824403030009444012003040c03c42c0a0751583e0032200403041c41c03030310a214182901d1260002c400e0f40c4103440004007513600074801c402c84210740da0703500d6410102d016010101c40c038400c10507800384100400340b42e00340e0782e04d040024050000000056103074240050082c2c80452290000001c940040000c0d4842c203046e4581c8180b988d170442e139284416161000b101d070b40c180c00c01c01d024001c0d01002800c3c443e0603405410290055200b901104c08a0880c00c60480c0e041904205403204590904003103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177243273 1250 177242023 177242033
    0xa06080c1e0310050a0b07030818070506040b0a02010b0108091c050c0304030609020a050402030c0a030c12020a05030618010602120d0f0501080a0309080111030601030924020d0f060b07 81
    0x6030403200081c400c41141c03610841c1c8101e100741c00031100e410b2010101c10b4140454100002550000d0018815060908440344e6000d410000e00030084d0880c0c0e580004442c405007000c1003100002e203009032a255543d03403030f1040050b10764000000c020141d820500d003110594460111280308109610252003002000340e4010b0407120070721580d80420a0602150581072003d100a0004510a4400080140123031050046001071075000386e12403441801041074406a00c82218071403070503484c002820094543e000d41c0c0d0300d04d28002000d44180702040c80804c0d260040019406000111030039507070400d0304010405964402d01800b401a00300c0c00941c1800310040002d0a9082e0300c102010507040d00c801c044004035842640f0011460340082202401d00d80c003c0001e60280c0a01002800143e0581203400030502c4082d144904156844001c0f07803d1007515100c00891824034102011018820003c0c04060740140d199404100e140000c42c62030903c0c984030b28011109d0522109003000401c0c0c4072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177244523 1250 177243273 177243277
    0x90606030a200d0c0906050102010b060a081303020304030515190606050a050906190c0311010501030b040809041508030a1103131a04122003150103022715040b0a06080c 74
    0xb0242c01003040302003500000c840c2040c4401800c188440010080d00d40310009003501d040c0b1032854007501c0c0800825030003d41c090406503100c03013006c0e06c10004c0d407a42d1800b246944100d61018026004d080721054502e402201c1441c007480c11152000400451184100b048030554400c0c1ca0200c1d03400c2025501c460301840c09803070810300007400f042c2440440c010584184001034040400520040010300c10150440030024486002e0350017000f60f03605590342e03100039540162002c0c11946001c18500b4407a079958104441c981e1121001d100e049588210300c82c0d5030307044440e003140440c1810f400100109400015210004c02c500b014140a9140c0164014212214103c0e03d041041c1004042912030814007000e5500c1d100b01900c1d0b4040d5451072608001d180a4840e05104e41c01c000c001000080039100d070300d4150b03601200d089590764100d07000c1455004030741004d10700c640e00d2041000740d0032040181c078401026099505201d541d100302c04020036050715002e4071011911001c08500000b64440c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177245773 1250 177244523 177244583
    0x21020d120c02160b030a0606080103150906090f0b060f06130e0903090901060c0303050a05061e0102010b030d090e150603010612060e0c0c01060e1b09150c06090606030a 74
    0x50300d0702c0821100c005610301d07000d6040207034135160000511030700ca62113204100080800e13142450300765056a42d40c0442c503200d42c11030b100e2180c480750041c0500c8030f580d0000700340650103040659000d441c0c0ca0b103041c0515045800512030340720026101d1260409400701c03550071140740d440c1c04074039040c6a20408020805003501484c0d11040c80300f00c50b0781d281c0d0292103002c2e040c140c0701c40030890200d182c0241a80e20082c040141c86041205100d0141c80b54000c80040000c680c0a05400410610040340144011103c0c80d0f40f500c55904607102083d0401c10400c255941c40e401809160398120603191040c285250403a040081040100321131807080e8244145000000030204038a562010038060595081c1da42841000c000241054800024801c131380003001ca5410691561400c1c10390600002c4a942d80c810490b84002070654169503101008990050202d01c40c0e0b848001e80b61141d5503a44c011200610705204600c040381e0349103400100b00106036449004580c0c9040b60656411050b040d01c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177247023 1250 177245773 177245777
    0x403020c03010b010c1e050322150c030305040317011409090f07031b0b0f0a110105010b04050409140708160608090d03110c07080c01021203060d0b10030f21020d120c 73
    0xa40030000141041c07008014400d11036454040300d01104030089814004ad03030290404464040d07230000003980280c0c1001806030141000501c80e92182002c2d00c50304107140741140c030b4180e100d0000c900b00040c00051b2910840c141c4d041c0405603507804042b99070303020030030000305070382c1c4444000c000041c411065544500180c0000c1d0750021383c2c3e4031451900340c01641d04642c40180120301c480c1801e43c01100d1184d15940d035802800154900742001d40e20b4070550180314091904c0711511003d210a8100310050400392400b100e8905541d0300340c064a584004020300408001070000045a078414440306006a241d07230050305036890424410390003440c0c3c400002495540600c044000c000084c02181c00401001010341030024a030000281000c0103407004028118003030052124030f841e00815a8126640300041c41c0040d200c0b08440c84480d40d02d580024103901210190b18200281e48001091003212003011103035800c0d2881042e81c6500d0b04004010014040407410740c8071041d19003003403032544403038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177248273 1250 177247023 177247073
    0x4050d1a07080105100f090e090111030f0105090603030f0d2705070305010e0d0e06071e03120f020c15100b070f050601090e0a03050f040e040b0403020c03010b010c 72
    0x961044032120340c00315095404514144010041c0b403c00f10301c1d0060f105100e01c3d01e00f40d000c020040240034082e15001d81d100020107400000c51340340b02507012126284013020003a0b103a14141c07080b2981e44009009050248040038041401800c001056902040a0960711410070000000d444006e003030b85141c445012250b58601d6129140b007541c84148503001c0d1014040032415810700b1405c0da09481c0d440f16407030b4041903d0120540c2d1051071803100003000c80e4035030741e98180f07820490650280c819929418200541802d010190044101102c08081070750900c003a03141c0008203012405442c0e6400000c0c0c101c40b84210880d00c0350f40710150b00200c008600c0310311507150021102c03184c010200031580c08402c2d811000a01c0f84c100070703460041407449014403001d112000004c1c0c80369400c0000500380a00801d4042180c2000f00642c1d014000c40c40300e82c992860b0604001d03044c41001c0d10140d01601404407030000504040c000c0460f00d44060f103903c01c3c00078040d510311510480740c000a0314030480c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177249523 1250 177248273 177248303
    0x50d020d02040b04030515061e0d02031c0f030f02040b0405331305040513021207081006090b010932060307020705010f020606031203090c13021903060b04050d 70
    0x43c0300080e202543c007900c000c05240d0301040303004029035000303071055204150429009109050703440c1c50345400701083e240407242c20300502c080f03483e0840c00b205403242800b207480c08508040d80054130642c403c00c19681408081e40321003811080f80708501030041c01c082d0420040c003081c1008520842c0782b0420070580304a02d01140c807800b5503400c01f81083c0e04204400520034001040d00c0c0004c002030041114200114208822040e400c0006400001e008001200d5400c48403c018492000180344a030203880e0400b0104000b803008051502558081074034185064100f94858051700054900c0002092900c00c0c0c14840302000110201c100e81040091401c01052920340b00301441c000e00b26600201071103810540013504100070b5041150865110108010316950002003150a01c21a1403000340e480d22001c4100d410120201c00c0141c00c40ca00e4101080ca001d1540e00900008003036407108402010a45030486c145e41d9070703110740c03515050140418881d43c40c02198040019104034524850108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177250773 1250 177249523 177249539
    0x291903050c062203080a0e090f07030c090e090c0406090c1409030708120417030a05160f050607020a1506050d112701080c0f0303030711030c0111030a060b0a050d020d0204 75
    0xa03c1d600304551440b004204814242e0300082c041201d1041202e00b02514a0161030070a64540002e041c3e100301a240c1c42c20100207070040c2c4240024010340d0702c1c0100145020032a0f0ba5941000c1c00c5450300891a026002485c0766027071140200c1010306540303400700c81c00400112401030b0802030056a040c0902000043d00c01d50802c100c0040a4004001303540f9249402c40c030041004008000300c03082d4004000903c1c80b640d1180844030048001c605000c0846d0050030528800c0500c80002483c070f200704d1040c1310005800081c0310007011b20a082c44101000141c0001e01951034030301c501d64029280c03006405c0050610340e000100c94038080d00e0002c0c4101038070005c2d07080d08116580d03110059840401070013090070520100d202c42c841a156403540c0c100382701c082a500d1000902a00808c140843c40041d40d00c1e0a000304e035407017030054009001808901c40c090794280d00030340703480b2289458120005000420310b82641d580d045107454030344c03e24200e080c48002030b501141c100543c0035803c00012030441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177252023 1250 177250773 177250837
    0xc0e19080102040e011703040602150405070f060302030f0610090306110c0703150b040c120b0111030a02160e040302120a0c0c2304090c05060c01291903050c06 70
    0x225104d28801419407600c1d055140060302c01101d076200e81c108110600800742c002800146050410484d050b0607665800d0090810342e850304401c1954100d4640007540300c3c0c2c0354004d580504213141003a9502d031203200c104055030719251020f00205140300810000f15406074415912500601c03010340c60103a40310a41810710003544c00454102042e05003004200580d4414841076400c1602c04000600354503401038200100da82c2404113480c3c5811101c0001d13442451400455040182141d8640c100d90320040c0d20340c110102c060f0940612503900043d0700411a607443d004030b8164015000340b001d8213a20015903030241200c001400001e0603542c0000701d6100c0124028001c02c0319132084034240b001c0714110f460541d1200c600c10703801e1403244000b141000c405041110001c81d01c581d034511b8200401805040103180c00510355a01c101040da410441d8030310641d030000100c40c0d881030809503103c00084181c2d01e00020f00280d0082c0c40005007418104000c0290794a00d12a507801d2100a002580000f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177253273 1250 177252023 177252029
    0xc060c1c110708010b0306040618060f0605040e01020f03041b0f18050c180111010b27060306160e010504050d060605030f190f0305090d0507180c0e1908010204 70
    0x44910389009640c5005000c2d60002c2c00009009005031030a03039000a03503510000e4000317800365583d81504007000150082d0706024030340c0013409100980805107424004d004c0b45c81442c0c000c83c100001c0c025070480600c201c8542c0818803c2d928207607159601c46007980c04001c51070a883d01074080e00869403080c4031012000600207281181440c02620314007100703555000d0002540910103004107113041d1024411140b994200b0328100020b002d1100c06940548100030396950403515820003038400c1700b950f142083c014108031000a01b10b4450200b410750b40c9404032003000d854a030400031100c80521603881c503000c40c101450b20310b0610362601d000480703003620003c04940d115a580400c02403805c0034031007240300b540c0761400f038042d41c0c040303c01c0b4039191941603000030031907210a00701c001094042c0090324112480500344032a000c1991070000d55611031750181c0340581508142c41c04056019014880000341d055455440110700c003000e00c46008403490070f400111071180004580c2e038601344090402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177254523 1250 177253273 177253277
    0x4030b10121101030b0a03121404181b02060712023402030105010b0c07060e040603060e060a060b090a05010c0317090a0201170403170a0e0604030c02010e09010501020c060c1c 77
    0x402c024003800542280c2d10b1040c000d0042c00419020004030b000081c500211024a0501d02154010300018410510a42e0845040402c20302c083e140c14120750f0707022002d59104600b0128810042200c01c1c3da6400c1d00b00d07240c20000780f40429075030507141341d41c001d00820800d1001807000060680c070305140c1c800c40c00e40d05201d4030711040781d0301c415442c1c00d009450040c03410303010301482d1a400360300441e26040180520414846554041585a12968042e41c01549c00c2001089040440442c1301c0e21032800b42c8004984034140000802c400c80150219540702e000100b400d820a0b2408005591410340390340d081c0c040c0056400001e1912a1000c1d856110740a80005001040b149100241c100044902068504102d410400c4002900081070b5180600c1d032840c8140155540d19018020300060381c07004903907000304420f00c41015000b04031105004d100340c03900c3c440c608111090016282c024454140168000c02008010741001e000405510401d03505894001c00401e130b9514001c0034140d81000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177255773 1250 177254523 177254543
    0xf010b0a11011e23060f01030b0a03020a0308030403020d02030901051902150c03060a0e06240c030f040501030e03070b19021e03070f080130060f0905010c050c0304030b1012 76
    0xd500c00e01d51500d20410813524141c070500e0030b00c0408241d5800c00d420b91681459a81c059088081e91046110303c000c5070f004040c2400c203900c81c07914808036002034404401612450f01c4030800180003200740c50094406039110790400c082001c040002c40410a0108203500030f41100c514244043c1c05002d01c00c0b241c8a1a4075502d0404900303110307401030181d2005040115507800c1c0599551001402042c0400b41d1001d0805c495600c52075865070b02c00c60204200c28840051044900c0c1c0c06000130f04200c6134240c07070070000d5441019400340c8134410508018981001d0100054140a01014000c40701040d001d0060070040411030901c10707041d00c04400306903020007204114189030720815161500b2298602114654541040e061003071000000a000540040002c019101400d240789100030b900f20381c0a0050200741c09190000b8008a07005659030b50821040c3c0d038480340640200c8400c00e192000840c0345c1407454944c013003076a0f4050500307010811506000501524400c5500c0800c0740070b520821 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177257023 1250 177255773 177255791
    0x2090414010e0c1002030f030a0c0302040b0310030501050f091519020d0f06050a0e04330903020d08011d040206071b09060806010b0a0809010b0915090f010b0a11011e 73
    0x82130780c620700d18184d421580f08001040c03013080504150b0750040d03980d2502103801030503143c00390043d0080303800001d01c50f100070003005145065412080116800740000708495240e1003a40305054070101c980e48203e0703003d0b1003a0844128440c002581c0032825101e020300c441004d00541d42641c0c0004a41d032115a01c0c3d00c0407411030401446454010f2008644544c4114641500c8050300c2c10000d0016207100300d000021404043d490f607201c0744032414920107000b040540040c080080000c07600c260010320420202a1565004e24070042c1690064550800d041c03000010103034250702d0050040760007003c2400b8480004221044030040003d40e03403c882030305400e10400004540a0354040320150340081d0040141d29a0341c0c04a03604c60545140c0149581d44035110385000d0007207400740d9500101c0d11410403001d0940c1003415100000304a07031100942d2143d84402c54482c40a0280340c0d4580000c00c04640482d001d0034424250564100010840150086011060144500741d500c00320391100090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177258273 1250 177257023 177257029
    0x106090b04020901091e0302061903050a0e1b0d0f0c0806160807050919030308150612010e04031e051308031201180f0912020106050306010602030702090414010e0c 72
    0x418200d0107680c00c500300464180000d040115500c03440190001c109040c544201c116a00b860103507401900c03c550395801011100b1141d03208542e03810020b071810f00800c04450031030048441c1c541049000344043c200014501462072105004c0c1c03036000c00140710100c005141c000310520141e0280141615070ba1416020b00e0130680c0c01044641d000300c2c02d031000410b00c0e0f003100c0e01541015162a03c15160004000803a001d600320f1010210f4030040000c1c00000c01d640410110b200710410000c0401c2d080622060102c0c90003000c00c1c51a07002200070041c400d4141501400c1d9019000307103003103071240c070302c0c4040c20080f03400c003031700240c001100050b032010003203040d68010300102f8980004501d4100d001d1000011048103006603002801007064138040040280c00422001110200400803841386150610345d520107031000c0400f5508040002885207004281c1074100ea910f07401651070036081c1c0e0b08006240d04000d004440c0680030038403104c0b07290400d1203030004681c49900141002c150f040c0c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177259523 1250 177258273 177258281
    0xb060c0f03040303090e100b09010e032b030207020a05120114010303090302011e02030909060307050307090203010e0606090a120305210f011512020705030d090803040b0a090b071808070602010609 86
    0x6c88010b800c2400144980c440050343c04508840c1147e600c2505d80061800480b44035004d000700c181c0c14030a078090340c1e0458110041800340680e0410944c991010500e1007a03007039028040c0302a6104450100c10841c50400100201c0c1c2c400d034181c00012001d800352071940220b1003c0e00300790700107078044405204558001c0d200c54481445258107000428840340025902d106a0380c41038019010030010038215102003018802a040040c19a40c11648031f407140c4009400c00d00c1503414050315140480e03194240807046a50000d409410401024100340c0100c6203442172105c1101041000c200c1600b4410340c94180f81440f0413810304050032030034a41c240b09086141a08020a04007810344c41000d03071070b0050800200c2e40302a003c090303111045414000e040d030090170300601881342051080410014050001d52055104100c8240d1a855007101c400c06ca4040c4680104400c507110042100c0d5400f07080560080406c900115001d25101c0c03807401e00303004103a07000e000581e4581030148040c41d07203401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177260773 1250 177259523 177259529
    0x40308070b0a02180f13060801020c0c0a03020102120703090e010e040b0709080d1b080c0703150608030901141b06070e0108090c04091e050a030807020c090105040b060c0f0304030309 80
    0x6041d4240020700d0074410760407026040d114485e452948540ca640c0e150040c180402d00c4803210100580b6030b66038285800b030740c003102d200c0302c81d030080f101804440c0c50100c030101c0549030182c0c000d110201c540c5012300c000391302c0910140c0601194500004d48941000c1c03146029040749100c007500d0b81030918103541d8a100c0031784104144410310308107009009d0001403425001d0842c0c94030101060601e44407050740e000803480030f807016400150103010000006203010440784505508001c2c1c1e6115003800e030403101e05000d484a66001049090304561003218036405020003181e42e5807404c2103c00c48600300d203481002d00c0020790004810014203641060710039142c0302007828222224070f00301030030700d03110300da201c8000d84500d95070b0301401c0911480c80480f01b602e0410560307442100c4043e0a009a0300c2003200d101310f0004907e17400050b08580301258200004102401d0240340d81d00300400c000c0980b00742c00d0401c3d0405014416040c0034003013000314007001050140910f540e40e0440c00c00500000d01a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177262023 1250 177260773 177260791
    0x30c0303030b2e0f0e040e010e0c0604060212070c15031a03010b010804021005130305030408100c08040303090206190903060b011b290408191b02011b08040308070b 72
    0x1e01d00e880f0301192440e19161500306031500c1a41c607001e407072080d62004262160302c2e40143c500003200c05c58007815400b081640e12401e0840f040c401d007100c1003080d00c0c45036006007001600104200780c0028204000340075190b10644118540130f880c1d1007042401d1590140450000e130321118007448c04c0200c1a2102c1b04648150000d0026141510001e00307c80c00181009005402407901042c2c1036104070305541825640c0d91003841840e030791b81082070741c03504540505522805000455039201c00ca600c00c40ca1018550348501c50b1a40d15032700c042e401042c5900301603800c00d2040040402414520000c2074a22107140c440190701403d50408a0480741c03a0403440b814010b800c01e0203059411500000c141c6e0580c03004c25428001c43c5055040c4c02260039001b150903044000e010f00041084004c0649181c20121580e2514031014a00c101c131200c0350200c0300c4074403071507000501c80035521410741c0005440c401d4000900050141d60340d1459a40554070130303613410101181711020440030030000d6400c10846 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177263273 1250 177262023 177262069
    0x8060f06040e060415151409011b21020708010b03011401030b150307140102210d0e030c0319020f0c0f1003180b010801200403110a030c0303030b 64
    0x502159451241c0d01070030b100c00b00c078140080e070340b9502c0340c10003010410812100b00e00c0d02d0ba04c4140782c0740300200e03035488008038488945000c14240f604d8140c82280405948101012049550446503019415019034461489564910980e68107000b000c8a2110070b81c01000040d142c00d085034212070250340201c1c0700c2d0341801e00c1545403c50840031541034a8002c4641095070303d88031020728030302d40032804454050282860000d030340300286400e411041c10a03025100c072401c1d440f905120010a43d03080d100d0999062081a00958280d1b004a000114030022a450141e03074440720f0346942c025141c0402124030340d40540c0e1516030306000c0f0709029512040184414864034001410302c451000c2024007039088070846602c96031298000c2c8041002e0310a41051007090760034404040c3c6001d02407844550300b44106100d41c0c1d189001c1c9224141c1500b51018103041c103543c2c9104400420444a0f80d00004000000c4081070040b4455001184070761400038040c61180d081c08011002c0303225191170b000d10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177264523 1250 177263273 177263299
    0x180f18100602100614090702150702030a03140405061504020c19060c14190e0603040b010e090307020117100302090f041a0103080910120f0207230d0807020c130c0806 73
    0xa2031412171040d05089400d03c6880d85c1c2c280c0d0803850104a03038511a0b205100c00207200304650040002c1c40702040a980c20b004c10034041a01c942c13408001d4900911640c07004000a08001e0801840344440d0307001007001d803504400d001036900d4405600d200140301200c1c000b60108100c1e607882445c0d01a2400d0501001404001c41d404043c0d01a04140b07583d2401c00e10080350701a40f040300c0000508900822013500c1c0c0c201410142c42500303090080140500c55580461101d000002c2980e5000381e0503952002c0c91042109850346070000036146240e41c039001040030006036a0070510910844001000304490301e030a00b0315681c2c91418a036030052100b00c41340103001113a0074004a482d0a04182c0d00082c504074400411950501c881140b1030031140352454682000445400408a0301d0003001c400c039102c0c00e07141424480c1900ca195058a0350702c0321081c681c059000d06140d03580417400380161510b0004802c08141806a00720703d8801d240d075180252904a5085481a40c002506840b090341e8606 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177265773 1250 177264523 177264539
    0xf0f140109051006170a091211070501090b0d020702030705040e03070506060103110403061a130b010201150501080f090f060406020714060106080a0e07050a03030305040203070605180f181006021006 87
    0x881c41d0240007038404280000380d4226036a070400d982c8184d00c08c0c40002e50f0200c5110003807000d00d0754400803942c0e0213080750025142d80f0812615081e40c0c190340f01c130740c038041d81008130308029400100100d8140c02108000211951a4801d003000b059104002c0c69a0f4511403078100d0408030001c1c241414186482c00c0700300650260400e0740c0c01c4e281d0001000804c040c1c1d0300c0c00c0440b0b1122403652964888842a450322108140345c101804800084e0001e0041c00c4245c80703000c0d15012180200341c0004c0c11480055100540f40305125080002103003511410400c22088030b040c0003084405458564002400c0c1040010300228561402008400341c103984d418043c000709680c0000c8c16440c11962500142d101c126800d0107028000c0c180103101d04039079640c03850007401420003103400364030038040c0c070300b00060050144007240e4411384c031940c1d502c0d5007035009405c002d1031500c51450150403c0201904000d505030f0071270302074021503903868940030b003900c0c005000f46030801d080c00c41c0079510f003810802c000480c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177267023 1250 177265773 177265787
    0x10905090a110102030c0a08091002011b180b072423060121060303110604030507172205090702030702030c1512010e090601170606040f0f140109051006 67
    0x59400b00155501032400341c0100e1450040e440341080c1801082c10300ea04200d281c0c1c00402d623680e41901c16002d0030580023026801c8401e80001c0a08240d1416505104107204000210910401c5000c03520019200c02c41b104c1180c00019080390b00030030400040b50044110301c6110706c4a00040c0c001d1040300903100d80f4900944000f0170039500c10300100b02141060b07008201840340304c0c40c605481c820001d90348000801a02091100b0b40100b40998401c0308140c1000c60031130f2060b0740644400c3d18141c825542c0c03071680344941100c008404401d0104003aa00c181a890448038031014055030a114144800c0103070040c00a4040030955004105081c01030301d012659445540084807009006001e0384101c0320b051107900c00c0412080e0b200c8001003038880a200400307004610442c00ca03a01a81c03910b030000a0740c0c0c01c0301d0001c51075512250000d1054234094000218003c00e82102240381c83c89c0201140a490000b0300d4141c0c0c0400900060002c01103034420a0f0340311407001075030129680341c82405403140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177268273 1250 177267023 177267043
    0x14010303021e01020d02070602030f090705150c0705040c0f030c02010236030303040813060e06040e0a090203010216021302090d081b030304060b011e02030306100903080a090e01090509 81
    0x90400b0404940c5030b00c420350507281c45089150066558850501e08400294402c941540310b040d803030804160b201c400041c658041d00c0c400341903e0f00c0d5000d011103020440c2c00101180b86140700f144004141c503201c0d03016984501505460b030044804140b030b0090140c0d50089640800c580c4180008521b031101291245c0048050800e01718002c0e88401310168051001c2103001d8042c8000000d11040003042001048075040301c7c2e449100003600e4807400c842a0604e0550039070701c240700b80b0042c04001000100590003104400300040d2015550340482d003a84c02c04242d0003075000b10b98070103c1c1941800b00c0001502d1040120840c07805103850001806085c3c5e03c031000e4003c51010800680320f1f1200280c00e403400c10042c0c1100d46902d094500340001d407101c88a114001a10b601d03091030600c00c0300e4000040e400442e0061740c01d43d51218240040802d007401c48104209e6150000001701ea0350703200401200c0807555a0946071424140c0c1202c4140040c0d00c0058160300d031204005c6c0c401c40100b501c442c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177269523 1250 177268273 177268303
    0xc27200f0d11072001120c0c0c060e03060a050601050a0503061c081b060c07290a050417310302090412020123040209060604150903050c0406031a040302160602101401030302 76
    0x9007021f90103c591013003413000108503440d5107202040c860780048541011907000c9040f0780d002d40d00c01c0000c0e0281c0e68183c8903d070210304240400f80c0e206025001440c5d0149001d80141070709580850710340b0748950182001e50312010009540c240070751310403400b900403049800081c413417404c052201420780d10540c44007a00d11085000400c0a030448094241c410b1601c2c241202000d0500c0100d007401880191003c8400f5103c0400807480029118203440c0c4030701c1402882490521000d1011007000c45001d0031501040d80080c01000503668155101e009a000700340c07040c10324444650103801c40c2d42a030002d0f00201c40340c0810100031003200c2d400c0303030384198180d5198015031241ca010a00b540519040705022801d01c003104506541e00900080172640100103c90f8009580e00c01d000803905103001c06012205148030958074064075020713840e003161103441202c0f4070800c6503000c00781c0080c050308114010303007094015013441c0500307004441c2c02001c1c001000c01107500d956800303907032846100080d00e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177270773 1250 177269523 177269531
    0x1b0d0302070b1b06010e0402061206010e130501080c030a050d0315150509010906080c0a0c11060307020d0f170708070c0c27200f0d1107200112 63
    0x40500c2800070400600d041d40e84251a1000400d0440a00390a0005021207205010000500c1c074100103090340640c1d00500050314000010400c4d10341650020b0101c0e051200c080c4245845d9103603200c0c01c00314140e90310030020b429410448030a040c024600d000383c1c82a0b100b4401040401c9012502000280703150400180382c2800315203c203071441107544198007189184400100254100004000d9800266600c1c022651284c02c1503441e08000e41f02481c180209100c10800c2c14001d19407008003500078a0340700440401d240005145501c11500f0340c0051704507168500009400821360300a0000d10301704800b603480803810690003190001c009104021801380440e00303c60007140150b034104d800c641448669615100858500804010000c1441c036200c100550200c01c01d01c650303a444251296003034000b82d55002200c003507404c81c2c0d0300454440c4042000310074034440d600c1072205d51905159800d03100e2003103040a131135010750f211042c84654514011030030759070b0b480b0580440b580b40e1400c00003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177272023 1250 177270773 177270799
    0x20d120605030a0c180e0709020a03090609120206011d0f040f0501110307020c0a0803030a020306120609061501050c06070f020a170d0c0504030803150f030a0b0609091b 74
    0x1002800305503000c650107018204600b000d01132401c5204007510003000c0b01903098180141880219141c507001c101e00303504211000d020941040c0c000340762000c194a0045040d2109031150b00403900c0d102c00c1190710340c0c3c0104400401e42d80600c1028010600c03004003e070481e00060492a0702c000080c840004586510000b6040000e190070348581d06800400800c0b4040d10307000024242d52042d112000903100b03030349071a070480c90041c01420982c0c50b400c0c051800c42c0c8400f65420013075000980001d5212404801140c0210b80070003481d449444998000e1215090401241100351408507445040050070450040d034600c1c001441e58004016245c003090b0141c1261040342843c40300038000f0580d200b58120039034601051005031400c2c1940080401015480c040191031a00c110b200040c40c000050000500000b1040400c4c0d10000b006081180c0c250840c10002c2d0825402c0c500c200d4881080c0010303c06282440107000e41e02000d86c00c000d19800c1c900c401d040d103440005400003841840254181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177273273 1250 177272023 177272057
    0xf060203040c15120b0f1305090f150613020708070b04030e130506030c040509060a0e0307020a0909140d05070809040609090b01030605100f050123030a06031e03020d 73
    0x5900030301d1402220200c0c030b01c007001c006200043e00d2132406551030600402c1c6010346420a110360640c50000e0006041f4a18080020080d100041c00c0c4041c81c01404681c078500c1000b40645c100d00c071102e02045649103070000030090050100035805460724414049940058081d02c100d030400b6810507180019075540f440c0850341d61340d81101580d0032140303407203003588556140d80004c3c0c0100401c40903141c00603290b8042c0402c9800403247d45015a100901240d00c0b01c4142d800078140c0c90313030841942e15180b810b40108050380308691144824555131040344040c404040303c0e25000c03104180c080d001032a50510018440d000d61000a000f03094001440001551564000e00007408243c00034481c418060500c184500c1c0244002d035244d0342001d0020b00044104642e00d4240d58a00000a0740c0c40d0400004403194004030030350500d501d014443c81103542081c2805144514001100403403000e0561401003665421000b4118094100c80110b800003034002c2445c0541c603501303107050070455035481c0719 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177274523 1250 177273273 177273293
    0xf0207030c0311281509030f0c170a050a020d170105010f0302041d060312070209070807030e060903090a0611030301061107030b01030308100608060904020103110d0204091d0303040f06020304 84
    0x40e50412000c00300d002c0b05110310f49903942c13840c0111100c2d000780300008030700e000741c0f80e1500d4001c0000380550500c46409000740001281d090040000f104a800185c600307040030341c4405c80300004036401081c00c1c5500e590402503190b4606440c074000e10b1510f860801083c14107018041c45040c81004241d64407590721a40c184d0307000704030b00c4449548802c0305039448000070038107503107803800383c051002c5c0c8d10428002c601c21503032000e07405440b074a103954034104205c0d92941c003d0580402c145d2210240b0034090410040540100c203000042d5550f0798580b010488400c9146d44004244030540b481c05c4044200801030780e044400310b05002d1407003007002010360308191054000800e10300610740044185a404020948241c1c10018821900c90702c030703001030722518000c403001c0d039001c1250400640154071940291100e55013409406013041c848405510583c1c000f44c000c8104c01d0b0355038145402000e11140300b07101c5204824007561450410341c1b40c89a0079601410083c04164000011504000790040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177275773 1250 177274523 177274543
    0x20f070b0d0915020301060e1518041805010b0a050a0b040e040302011e14010f0b0304030c0c090e15011d0a0213120320030901020c120c0d0f03030f0207030c0311 71
    0x42e0903e0840080d00e1020000d400a006410004041d4400350390030303041280700c81484280d428591810001e100c58403800300c107a8104516001170f126140d02581500d41400070949030310500011a4a2080c0d40c00e0041051945e40075034812a41c00c60100001c0002c0d204540c2541c48071031618103259164101a03000d001108100c45285618040003081c1c001c450b400342c55000a100030601f0303c1e907683d2400c00c003148894028229a0b0000700b01003000a0b000d1054503000d28031401760113100c00d688600c0c6201302c801d41201c00c0240d4001c080004a2404549401c50140c107080e00ca400060241c2c44441e41104d40043c002c0f80882d500150306035405050b06090001040b07100014840104d5900d0700800482c3c0c2041080781100d9072000700c552400000c03064071101d11040c0d0042c25010805410000c4407203910020350014010000c0c03115582e100c4034900c1811a004500c602039510845c5030080845002540180c202072061000394002584248130641c03654151901086060341030390301e41d0a0a44d011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177277023 1250 177275773 177275783
    0x3110901080405341e05100908060903040801050c0301080601120311030307030b120606090a091b0602010c0207060801080703031d04050a36020913080a170601020f070b0d09 76
    0xc1c21a00401c214002011002400d00c4155408990f582c5180d4105519807901135180404540c1c0c280001e044c0600302147c01e0186140218503136a03510101c030305044080e0303080300c0c0035040090700348690381e005d02035141c002900c4040c1c0d5180d03600d0700480a031520418041e403103c41c0e840394030076000e0503c0b8030244001506150142c0c1c0d0b6904101c24054020081c50b02024041e440309200190303c010b010503040d10a10300504089884da03550b9099038024038040d00b0442c0c3c1c85c0c0402819903e840d160300c43c07400245c0081d800004501c02c2d6a600a4680001980100104070854005002c1004041303a8401141e906082036000811031030030002c4035161000700c03650814500401c22007010101d0b041389042c03194141980c2050304a0007030f40504904a00e00c2a1002c2d00000550801810b1004035281e1190700842c6148003802103540b50525a40005003c00c001040385036481e681d20010080d031608000240000d0022001418007aa2154158400c8100252021424040a16440d00482d107110352007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177278273 1250 177277023 177277063
    0x3070c03180e180d2304090f090204060e01061d0103090506190507030b03280203150f13021e0114040605120114011704061e09050c0103110901080405 66
    0x68400316003182e0049620545010001c0c1c403d045864021032030030404082d0f0b59603280e2a030038102c0308040750380b03101d80d004441c45810880001c011034148515900204210004900742e552401008160740c1180c01c140803450312500100411074021880c21046625254003103048805600168000c0800e00b8003e022401644100842c560324031000a000f00402c042c1000961140c0004178202d4205240154065109039842d500c00c1030344d8050b903100c000000c8552540c152a03680440d04140708010480940c7c2060400d0194040c8410349840d0b00a60300d11030310700c00c65030036000290b80700c008051174079029110001c2c90589901c64016554400c80800d010350351960f07101d20040082e030007111000b20031088280042020880a12040c00e9500144e440170190349584503242820100a001182c220395104e20a191010a4801e2844030043c40c450024906080c1d090403410310340c890000707a04043ca4030003840304240701d039016508050000c0c83c01080030355640c50094a007180540785e6030b10140e60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177279523 1250 177278273 177278279
    0xb06041a0d0c0e01020a020906032410140105040501030f06170321010308091504050a0902091003090b0c07050c06160c080303010f231201020a020114040803070c0318 73
    0x540350040129004402042041c5240502d08860b4000c040c002e9500503081640041e0143c9004074420390840c0005050703c8507214460354046805400b2071822040b0034440042104070480565610000e0480c10b0003600d1284030000001c05910881c007699041c150f070350012140c240703525489080a0440e05020384203105184199560700d40011440d89240040e03168408840c1d0854500a4120f81c0e06c221024103080e071010420004070040381d40050001d41c02c0c4000500c81c0c3d10000e40000a0000800043c3d0b0780c1004c0051100d03403a007944c400c01c14103040c8a850701c002580302d217801e94442001008540c841c44079203086810513146020817984440c001c00c0540712801c906400249803803146000060007951451290340701c0c04248521052914184800c000345100040581a05e4003440100c0c605e0310100e0000030700b09000c0300341d07010180e0f41c04600c1e450081e4091240026006403e4011031452a1654600c44603110041400d400c0004030b8400504241c0913070440e03980ca100e20354030700a2040e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 177280773 1250 177279523 177279569
    0xc0f08100b07290a1109030c0603040302031201061205070201051311040f060311030607110a030503040303140a060305060903090d02060a0302070837020a0609030e03010c020303090c030309130b0604 87
    0xa000d81c0d003c03130521300d07258100500d00d10702412101c0c4810041c0291217014030140801c00703203800040042e011741c04204071040101486288580c0030344899181c8080d185602d44000080b00c90080540f029a07242c4400d0118030813000c103074a02e607143d01a801c42660340720750700828054640b05030b80c14080c508140c0080200700408100714003600741074084800b1907845240403a050355043c00b1200064100c0d0b508000030a21680086500c1070081c05d01154118140400c2006820116801e14000365550010b204000341030100d29007051b00500210b00701001c1d0400184411408007009100d2140010718140c014084e030140c40c14607802083d0b141d1030b2502e240360100a031015500e42a1403980f840c2e19107511072081c160303c00c00c4e0b0000354001d04d185a1260b48141c024042113009805008458000d010203942c240914894034400c0da01454030303801c24111803450300814a6080d4400c0d042480014503544401e00800205100001e0203e014180710780803c40c544210380010310401c05026040524171 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 177282023 1250 177280773 177280853
    0x4091409120f0a050c4912020c0c0405010b0a09050d030503040807020102010f050c0a110307030f1409030a03030b0319020a090e03090d03030c0f08100b07 68
    0x4201069604049641503a240207210300d80001c03211803024444001d10510510240294561900031940d51b0051100c00030b11000d000d01468a5601515400780308400000d1401c5210416031030741c1402040810f00050f184c0a048880d0b409041d83c04181d2105101c400c1201e6041c142000d4800c0040756102d0103410802d43c8003020190105500420000b0b660802c100c0464200d47c06984050540d03e8655411180b0b600002c01a8119900ca191841c040c481d50b104650107034600f41c0e18680d0381c8821050182c564040e04201c141c00e07403c14052000402d400c000e007901c0414440c42c04a0f000000301500540300e0250440c03071034143c800c25090b0f004050305039000141e80b001c02c4040f580c140040809220b00b040c04458020341100c103004080101c0c50654004810003007000d016641071900e44030100d180c40550a00686c0080e03110034a40400c541c01c04400c0300001c14a223003450040c0361040034640221464070840e440388600044407001d000f13040020740c0e03a10361450200303d0081c5803101050524 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 177283273 1250 177282023 177282031
    0x1104050108100f031401020d1d0d050909060402090a0b0409021b0f07031106040902070b2e2907060c0915020604150612050d14030f040b0408040914 65
    0x1080745800440d2440c400e26a4403000c03a006051100360460559030b810409550420b0302140964082c408418140e985000e46080c081e0014440039904080d0072941d480c1444124102080c4002000090700ca520740701030580d44440709450241e91000c0741d102050f02d45050758010a8001408900811300c00031a40050a00c600f041201d0700c902480c02c0c030319a4449a035684900803641c0101402c20000d40230000c59400e041e0020300450419541c0c0c41d8030b00030303030340040030440b0755104040401030030510628000c0d9107125151740040312031240d02d8030505108064003030810079000404c914040c950849030524030070401000d61584070903a42c07400101803c411840100420a01c03e8007007026403001302003e920034032640c000c003855101c80d1071724422a900f059481138404d45442011031071400c050302c1c070640d40744501c000b0138800040f080018000200c610948001e04030410901001000c80c80034260816001060741130307240c54516054501e4031a6a1211440506000c410317005000e0003994148a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 177284523 1250 177283273 177283277
    0x8030a0903030605220e030f0a09080d030c1b06020d09230c030a0602031803040e01090b090f060405070e030708070e1e01061101150306060603140c0912070911040501 73
    0x11035500d03181000a145510300b100c4c41240345c0321070b1a120f0034070f503a009285c0d850141c605403840d180f0150148c04040d4015500880403600c1c0d640100b14400c01000528180d640d1860304000c0d80c4654000140030002000b800145c44809405202c20301c0380c80d604480046420820401c5030340200c1c50500000500d070b41d2255850006140600e1940202140c0b28031030701801030145c032524038607944640007900090403400703000d148042d03081054001000140701401c122580110b5541c0350412000c10b440d502c603a0700e4000c0c401c2d03009224100788a1040c0341d800202c102ca010689640b64542143c0c50000700c1d04050341403061900003d104a0082400f40a40f4103a8040c44066615500d10484071108101905203c07000d4000403c4400d110f00500071000316200000302c0d4110301c121503d8112815504240e4485949040411030f0781c3d0184944071031501a2444201c0a14100f448148075010703054001c4d000314204220051148414804080074000c03117081007052401c03854441842c0e070068000c1c540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 177285773 1250 177284523 177284531
    0xf06040b010908100c0e0a030803100b0a12020a0318080a0e01021209011b150b0909010902130c030f02040b1b2b0c0b09010b1903020d08130308030a090303 68
    0x21640d40b1030301d8080700f82e440b4480100456448034001c3c000a2011040c1401080b5980305003103200d9403002c40c120001d500990200f40c59040c0f075220170125200c55802044070610400c05d20380c16039040801010307c1c294403000180c4440c2415030503006020340b400495401003020701e106007005039120190000320095540c40c85400107080069a0742c04041030111401302007440800025807060403142c0d42c00000c2c1100c0d20380d22035140c0c0c0e8200c621840b070035804071458032800750f41014241406000e51240882000f17103d54041070f000b184e44a90324005440302c5a80711109040d015000c2d400a00c070018140c04d0441d503d0759101001403c540005000c900380140c00390360303081d80907400909050000c40f29400381c0352040103850310022000701c88010b48140602140e022002c80d0750440603502c1100a01c00104400b90884104014020340000b0314000715049142030000d600c2d80b010040e00b0b594003401090780e55000304956454003110381d1009040c0c40e400010440c1400d626048210a14401e85080c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 177287023 1250 177285773 177285791
    0x81b2703070b0909060307030516090b010e090a0b03071805010e010b2107142a07080c040f060e04050304140402030c030f0709030506011e090b0303070f1401050f0604 73
    0x951078030000c0c4111080380c0010b10000c4802e1901c0ba80345034002000a080b20003c680c1d03039a40a0401c14160088100021424003c1000c1442070194802000d400d1070141c085040b1400040c2c00403034041c061840c00c5580750740d000420b88040258034081d00d0b2100d0301d0a01c511107403240d400508401d01480c2085240840006841140c12054812039522041400070f2200c50740100c800d00403006042c201003190340d101c01c2c20028032400c020900300a204640340702c2f8204cd00403811040912080074429035000003010040600003003051107483d6021900441d035500302c4004240074100d603070070030300508a06000b0722042250000c0208100c0d000301e2445e0348007001d00b40400041740400c566071032084c501040001c140d0000e003008550302145500385001c0031516510340c5c80c6021401d82000c0610401d10080c0020517081680540080c90340b41014498040f11030003182d01d80c041c0003002021040c5811400c0d040001034425407003403c014030001c014902d032255143c6034820040d1192070045190120030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 177288273 1250 177287023 177287029
    0xd0204080c03062a040f090e0c09071e17070915020f100b06162009060f120304090e0706200a0b063001060e070906081b27 54
    0x5100c2c10007509040590080c031030903094401c84c60b40c82004510000c010109490b07110052420103400399050001d4030b50201054149804414001d05101c0d01c07010040141c030300d5103c0c41c5210400014401003c1a10358168141d8000380e40c02c2c0a1400c190500d401c0080c076642c005e07904402c47e003c0e5440d000d80b182c102c0314142d84440e0303803205481c2240c01c0043c0e2038000460b2a0022510814040c101610702170001742c0c241d50f0303044c90920490f05030507515900348010343c10780344e8011004021240201103041c460700040364091546159401882c00d0400c426151906006542c010711241c5418880020f070300c4059929022140940408201200d05c40072418154801c412a03140d0b11070010300324105c141d207405005400003031400c1d070b000085c21003000b0b954020000c040040320701c00d403a180d080300300b40c2c2025003560300942040340d62080120410030400da03c040b803041101d009080c1200c854990355541103600980d9281a01c0e442c0d000900d004009000c0c035a0f00d04800000706032500d01d40110420 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 177289523 1250 177288273 177288283
    0x10e0d050403030503041b0305010f05040c05010314220c0915060309080a080903090a030503120a0c0f180e04150c0302030108030d0b060403050d050403140601150c11060d0204080c03 80
    0x7000d0009003050000900047c046031000030030704680b000d041e1034155285da5450a6641009440c000302e500d440906c020030022501d45030191034242410f00041d025540c240c0d510710f5004003a9681d40e0540d04410074680c989891964000b50890341d9207024944070580a006000480380c002c40c5900c0a05001035824820320603490034a40c0f01c03440e00e00d4a00700360030444803101d02600441d801d020070041c88105640b480340e003900645c4074002035a00e44803c0e00914a4080e00203202c150160b0400040e14521603204200d10310b00751003814910383c1504c9400403050300c4050b54000910312600101880f00b4442c10110744102d141400b401800343c1110964102c047e40400e1048407040e40c000d00003004180d040d60005003035180094a907030704103652919203920300249643c800000c110005030510501104418581824602e8002401396516040c20440c4c00100480d07440100951385100707000304541d62841403400880140500d40700d010f414a000001d5102d846424035500c02e00c64103101a0501080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 177290773 1250 177289523 177289529
    0x1b0305160b180906030c0a06030e070510022107050a0b0a051e13080d150611030903060712140c03060a060c02090a02030702070806090703150207260408060405010e0d0504 75
    0x800b01c01d400300030010311048103001350143c0e5050003004d40550898803055608070040190f50f9000c14859140055030b0f003002c40f41c3c1c008900130001c2e5500c590310650002040e100003407154410811419000c070705c204c2d442c016104020704130b020743c050050620000000c1030b40215003204041041ea2524440460020280f01480000c140340200155480f40509a070910317841c0500d440364074000210712020121840a02d204407125984e0b40c080c0040d0b5071100440040444c02d100541c90b03c004400060f0b590000101b102040241001c3d91040c00d0006420052400c0307001e03120550941041040d02034103400850f00d41d8060400ca14000820318401c5201140d031540243c44004c00e902c0d40300c00e18010f50700082104081d44a500c0000403080700810404e0310440c07885000d0301c40f070b40c110b10301040009111001c80850a00600110010990038150300d00c825510143c4800382e42e852080781d490764012a0302074850382c00b0b040108030a0007419000100313000005000d5a980c0d94800c0010b4616000e540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 177292023 1250 177290773 177290797
    0xb09060f16060f1a042021070908030301050603040212340f171e0601180c0503130201091802030f060402030403140c0120070b060109080a020405041b0305160b 70
    0x2114051060600d603004041b044030001e0f10007240c00521140f1180da91000b0a00c402c503081518000b024420b00101ca0740c1c10248501e0000c030024500104595a80018007a0130300c01d0704d00101140c219a41d10441c02d0404501d0740c1691102d0f007554145c1010380720544214000c14503070142101920040104c5401070f9514810320304950340c24034010703c030441801e010040c010301c030700751028680412012603102044441c1000301481c0d0b051810304c101d0f14440b00302c00c40e8081e040400341380702e686c3c029042d00e5101c400000301220404441c00121104606036104262400384449202c000c6100b40e001144501c01c0051b43e401300351190360920040b40300c121000b07800180211046140340c6012002004940b4510001003420f0445601d4a64584203c0c3c0c4410b0070200001042e00401c03082000c03403544200300342441e08403986485c030325a4840d100070900a2256075160300240420043c1c0127840c2c2038000c5050801680354491a01565941060b040700e0b80c45003d18400042c0341000504451444040c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 177293273 1250 177292023 177292061
    0x904082d0711040603020409150c020102130e04020103200d140c030f0406060b041716081905030d15030302060a06050d06020304050c120105070306081203010b09060f16060f 76
    0x262216040c410b200010640e00a44400000003d6940d40c003070030382c002d4007400c1c0003070b0040701d24001042122000c1412905690040c0031440c40f5041090701c0d8402c48220700c0c80182150744d00d00c01200200a03079907421160002e4807050042c0c024110010700602848002c0c1005000500035002c005800101c8030303001400d200b000060000002066a603401520907800462038035295140c01d1150b4100e074100031101d00c0c408a0400446c1001c0011414000c0012002c0f8003d5081c12075039911803180010554040062440000030000100b04640511720128070401481401e21a82e06242e1000d1000341d00500c42c2e00d001c200a0300030f03031040c1c8003114801044800c0d440350a40d07070000a500001c10594240c082c200da2030040c2c1d182c2010090203510410300000b0310740380280001d0115989030300051407503072140b0040d8407003c00c181e0031281956080c0c0e806586528514001070401d11548ea2110540300d000308524000c50f040c078204a45042c45404107128078190040c44c0012161248807400c4c00c0849 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 177294523 1250 177293273 177293287
    0x130f1706090d0507050f0303010902090a120308040305180414090706020d0905010f050c0d0806031608060411030a0f050109060b06210603030d062301030902010c200904082d 76
    0xa48014103160740f091060346c1108250345141030554009034064144141c00164511661401d000c0960140240c90101d2202c0151510001d0804100400007070500c40005510b6803400c010f01c41904680038010014480c410040d0b2b601c2c8050641615804020300c0744150104105001050360700800845030b88000c4901e161200450764882c031a88581c050060030080941c0800c014446003c6130030303490b110300e81c4038144081850700d48018001c0c0154115408041403101c000080380c0c0a4000e030304000e0003811503003000e00080c01c0ca005013200078010b4030524206420480107411081e06c0900565003040003c4420701030040d544140c0789030030498401c10041440d036050410780c02d5080b00000e0220390808440144a0307085502d1504030018000242c010005909051101194485400c1c601400080072a50028020070100310004100b4a19081d02c00030401c405030a20241c0313100105012400c0c20300b03040250b00c0354010354040000394001a40c6504121201c0f540c4191601d0605c0c17007900d0240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 177295773 1250 177294523 177294527
    0x307093207052101090e0f03040b0d050603030d0e060a0c0206011404050403140a02071a0a0c080a030e03070b040b0f09071a040803040b03060a0f0524130f1706090d 72
    0x4010b43e80d10880d105400120030340f0300d80708000c950117404200300014400142c1d81b0b40518024103015003440651042005101c2d112100701034400400e0b50301e502160b00d440d110002420b40c01005403090040d8a020807640c1d00f540c0c0040c6090080c0c0512508001d040418802203031110024040c2400c42c04410031000c1050a043e44a5503105001e8500703040c2039811404888050741c0b1210f0102c0c01603200100910845824140501d00003248901840c50706128203c05010392420180103804424003003070320800da5019030840c0745003900e14400d03171b03640d0038040c503101031141c00542e01039448105203030001d1440004100c40728052030a5a000b8204c0304d00c0d1401c00203c00520003040700a51100340000a51094200040d00c00b400301860640d0b00d900c3d0040a101d083c1c0c0c0581d01800b140d45c905e403070401c210f41310f22440c0f001085005034080328060824500c41140c0c49a002644190020440d0019a03010040c0c020020f591012166220044840340904c0c2d464a041d02e4544194100c2991408514 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 177297023 1250 177295773 177295777
    0x20c25030c171603030e0a0f0e06061b0d230315060a0c0b160e031b040b0406031a070201060801092d020d03080a06062606040209030709320705 63
    0x10302d004403100004100484048107405500490106164021061080c42c00c000d6003005441201c801c01002132804150a111010241c12103001e200e0008001c0b0b84c0041c0b007900d4043c0c41c55160100c41015400705401001d001c090b0500c002a00c9003103c003c081d028009041328001c0c1c0708a81c4101081d092081080300c2544001d1141c4148072074891045e000a110350304580c820284c8000007400b440d071950000c4d140e034150112052290300140550740031180042400120360606441c00510030681c3c5021030004c10040c2c00150045c5900c44140089912400c4024494446980248203555441310300c2401c3c1d50860000030448002c0391000f000c1e03e1b54401151142401f01640113100c90216000b1a0880c07078039070002d900050040041003641b040b5409000000e0003240380044054540315014840081c4002e4072000c203070b90b0700001c205243c3c0c8507010b540300c1210040950304015900d00311880140380303940462011900c40e140c48c035007141010010140f1007001c01288003103a502c80b0000c50740c50b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 177298273 1250 177297023 177297059
    0x903050a0e061c0b03060915040b0a0b060c01020d1104050d14031e0406020d021501150c1707020301050c030c0307111f0603030809010c09061b06020c25030c 69
    0x802024040c414640640718074400f12841c0756000020840301c1d00c0d040c18108034005090041603400307041912043c071744000f42254090b401414010640d1598800c24010305100d0070655402a008281440034917410360082030001c800400030000d10840010f0304500b03010304d04c00c16038020f9000b40c00f000890b446100008034240703072405413490820328082ca914140b00120055030902d00102c2c007409a583c04004619600c0b02c1400201000c6c400b492a90040f660140108078013980e02c40b030146246c501580c01d00407446e5000814400c42ca100c00301082c2903400c040341c168481e40c200400b280321200d821040701d0080c4401c500c0c443c6140c0d108a0203458100c007000c1500074a1180350742c460042d0000079080440d01060f2040450b00500d1410000c05200c0c001e03110070001c1e45030456180c01c00e81c11a07800303c100c5015060904401c1c080d07424001c0101012540900344c00e0001a183c030a400000c0741d5000050851440c0d0000b000708114039800124007404010b050601c4a0001c0c0f002c1143d88400320ba403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 177299523 1250 177298273 177298279
    0xc04080d11061b070506100f0906051f0e21100b030309190b071101030f020313110120010f061e14040b0607150f02130b03041b0e0402130903050a0e 65
    0x107040c226903175141c50404121007080d482e00c0303034502c248801d0702101003640c0180700c48881401720f10705000000304260f800040c0c1840491200384501850750040015004002008144c004800450040002e041310440c00002e20f0340550083c0000707244203441217220201010300114100000075060020400804111540800d091400050160034203002041e80724800c0c642600800103800c0090b082d101443c141c1801540144200b00c00c42088403048200c40303402c103008203a03240032500141d41c4000703406c64001d542c04101070107081800e01508903012401c60300c2c00c104000c655456500c402c44d403941d040b0350200c00085504022040f045410504041e0b40204001076075081c450004207160b01042046620809030f02844803540864440d440b0007810701d200552800e96890046e0003214483d0040e80f10101010010a040c0a00d44800801a03050f4034250007a050726040d84d960701020843c1d04034401e240f61824021070248034041ca1b5000c0340c0c103465560510f9000b1900352001c1d00f005c549260 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 177300773 1250 177299523 177299527
    0xc020c0411160507031101090506090d060e100509160602031b16030501050604140c1c0f02040e04050606031209040515030303010909140c060307051309050c04080d11061b 75
    0xc1d1a410035030310b4140340f04100410183c1e00d54503041c0350108006048505000342e10030100701d030b070305c9081c1201c0000e00c0c11105101888014600301c801408290b076145031510030408040c1e81c01e412070f80072a0007401188211828180454a000301c43d050f11300801e00160424820041c07044001e0b00070b40c200301c0d554019203040700e1105580b01c1c50400340c2d030320580e138682d155014800703a0b081621807514403840301e10300446146002800b030035161140d08107034085600407034880712000e03400b0360289032a03070500b2390190764a5540c1d00340010000000e803000d64441c0906004a000c601c0e0005200e1100342460382e03804e04051036241000001d0000400030300c401003486010f2402568280015030182c480c1950008450150f410090300640b81900300006c194091101070000e6074034442504e9100c3c0980c44d246540b03051444a0340e0803611298404c00d031040c200001d020741ea400c6035010b041070740c0d000021202400220f5000722280001250913401716000480031481403000c2078180300d542c1840150484c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 177302023 1250 177300773 177300787
    0x1f0c020105031e190e0106030809010f03020409060308040f0b120f040f0b07030f0b04060b2d0a030b120303100b0306062a0f03030702030307211803090602010c020c0411 74
    0x260300403c040b200702c0f40088a14180c5040042c45100d000018034105000300003a07410f50b520f4000611520361010b05000c0301120300d0b207101e40310340c0486010b4241810140055540c1e461700481c03981103401103940d44224000c005c1074040280068a00340f844031110141d643d120b208100b00d12181c00381058800c00141756008000c13034400000c2c2c034046d071345c50340c0c00185c5940c070115100c08942c0602c02d19403003039044c100100080c51510051f1140b44000003021074048501c46819400b050842c081c250003031380c010030070f41141c81d05940031074198081034400d2128142110306035a16840104ea03003840703030307107020800b484003d0141000e10340c04100581a145882c41c030168184800d1000513868915075001e0641c1e0762091000c0c440701e00e0724400030000718154201030802a450303020042c059010802d400482d860b1002d80e6030600d44841c4290305040040440e625007186182707003030301002d80126050b8440041c80a105110380055540640d0142a02001440801000c1c2c548420b0780c1140c0c0c00244115 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 177303273 1250 177302023 177302071
    0x20315030a0b070305070e03060a0203060301150b090118080a0f02040b181902042103030204090203070c0201030518070308160605090a0311030310060c03021204060c021f0c02010503 80
    0x140c80d106000c0d44040c215843c0410004082e507100078071200c10040503405800480c2c4000400c5d68000f06500d40140c1c40743d4400340480d006002100c900010b19103c1c3c50001241031301c0c20028070a0500a0f0381d40c07a038031041e1100f000c8491420340700f41e1300140d10014000c4003180440008107600c0b4401000400c40c1080c4200055065281440500341016940b040c041c48400b988521140800d034840d0641c241840e0840c6c02620944001c0030901400021810b20b0030144654100d901900030307140e0464890500d0307a00180035044840089011901c0c2c00c0106140350304d0381414800303100f90180100f8115041d6612000c8642000d0f400e21070130040f03801080f0000301c40380202486480031100900d049902410010a04050030b100c0c800250010014003542d07000c140c25240566960303080c416021512031400304d20b00450b181d101028004d0128001ca00564040c1d0b5003c0164002c072000008440c1c01001d09103508081404a8082280800d030710005500480c040c0d0780c400c0081a4000a1072054580c17 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 177304523 1250 177303273 177303283
    0x70c030c080127020d17120403050306010210060308041a04050402070b09060a05040218060d1a0a0f0608070519030501020301062f0a0206180d05030403060b0102120d02031503 77
    0x7080d07019035110b01c0881c020007422440c980108a10b0b0070210b001195640104900c98140b5502078410444412500c0070380110070200e0340d00d000351840c0701034107103018200100107400c00e03038826005004011042d68a054280500c00680350441c421900c0d16190580390300070040c0c2e004417410514418400002c190f9954401b80103400d00401041d1540c2c5044868181000340040ca4641d505280c00148000f43e21425101045460a1204034600d506c403800000c0c1307880a40c100007040306004140b402a9040f20900050154648810500c6081f9250b0740070404e682407405901440d42c0f000300104914946541c1d5a10b44590302c00000310b030b00c0c1e140c3c0c0b585030999000740c01140104042103407625075007550380802c0410079000546070118040004506489204402c4040c2c454480401c0074410360943d402001d07100c0d4401069503a45650750702d03101d5120b800a00c400ea403001d10386004440c840d400480d038410a040244071a134075045040002000039003000c0d203a1a540099107c8402c803a84082003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 177305773 1250 177304523 177304529
    0x70e0a15140f04060c030c0209070c0c08030a14030a11070b01061409010c0201120e0118020312090108160507060603060f05010807080d05160c0f140f0a0902070c030c 73
    0x10a49880c008001001d01005003042900110200800080d0a00c0e04044240c07000d031402c518100300c184d6002e0034201e800d4032540c54040c1d40b0450010510146035003004481d032490b4800c843c0c40313038140d1340c0d86c458680360b000d2405002d02103178445400d0700840302c0c03a01c02150f000c02034180000c2d040c01607102910a50300040700c12140c0e261000c005100e843d4210002580d000ba000880030b14084903040001d0800e80210802814031a0b0401e0549140d0407030342103200c451032444003c0210b00201501d20018800085042c3d0190080078481c0a42540707440495280240607107400300907440c0e80700380000f01488400da10341007280c1400320100203502c501422004500540001c2100c03c1000d43c080304448040c5d01c2014681d0000710208074904000c60b0f0842c140090741845500e5242c500c1c180d008080c1c00f603d004007505103030300c404120480100c805005655090701240c0300d2071038440a019060403018100c0b58400040300042000c40142d030024400706104141502e04207035650350f4080c464040360 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 177307023 1250 177305773 177305789
    0x90f060c0d0206090709020a120f09080a02150604020703020604080706091b090b01090501080c0903030409050a1413030504030611121006110105040b0402210a05010603170a02060f070e0a 82
    0xc0e0074800058020001c2d1000f5221b400c5c011890507041920181140300a00d007140c00147c0c54010003c0102e20740c0d400700703100d0b0350803103202565103078107040084d112500c6001c60001ba00f040c10103e070407418148241d80c00e81c3c0e490340040c01aa01c0b103490300001038000e06000c46000b07481c0c000100010300194000c1d4440440d903001d9600350340c10203110106441e8040c032101d041255901c401c02040c0e901554285d0007001a0320151b50303e001513408a070851040d5004644010f00300400d00c20348880350b41c051009164040361003036242c2c50b03ca0b0700e0502000d8030040034001a5040c0424004285542d10210802d080d030010340f49032100701c06100d480000d08607890411461621401c005e0582c2041075000043c0c5458000c0080d0b2525541d03910800f0700280c0040d0142d0a00007031055100d00101d100d40e4241d813018111480880c0324944a40a403000e40011140b1408940c240d03038000c041301d4251030724a641034000d0b00207565020406003011000400e01010040d021581e4040d64842c81c0024001e82080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 177308273 1250 177307023 177307033
    0x6070819020c0f010c03080712090b01030c0905100803040608070306090504230706050f070503040302060313051209010e13150603230112080a1709030d050c090105090f060c0d02 78
    0x84070400440101042500307040c400c403100100000782d4443c030b03150341c02324560410000b0791400340700d0030008050189005162610312000481031000d00740040702140c204203418445942ea03d4160f91380307103069114113a103d80c4140404c1c0031803801a8000d0b6880a00c0346400109248c1c1c80804a007070710016282642c04010402c0c00b078180681e05000880c1c5940d040b0020280b452421074020a11711816403031b004c903c00c01060000810000348121801190024000c949074180000c180c0907001e40c064044a03d845044000c40e03001c07070f07802c05440c0b42100584030f40c3c8480d11644180000001c00d22107814101d6610a0164a85030f03084200902070b101c5c91354002500c840e00c88401082e072314000609000031201078010010080d0368010440b070b199000c0500340c0c5552100e60242c6005004c15041040c2803651400c014449a00101038500c154070b001d002d001d42d841e11007414016200b61103a560000e04204285000c904001e8404084400050100f925201083c090030782402c008103d07400040e004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 177309523 1250 177308273 177308293
    0x3090201021612030c020612102c040b130203030a1d03010504080a1202120c090f091012110907020109030212120106030b0105130602070810050f060607081902 70
    0x4100007101500c0b10300010b0010311820510f00d800d0310071000000500300301913508034408540b2624103035a58500143d840001034180340000c1100c00c41c00740a200c0081d45107000f101914082c0403040d80f051440324048040c961129294280b402c0380040881c040001c40c2c50241006031410801062614000e5580081e012500541e00f26400e5004d9030081c403d0b810305081c000810020021201c3d410313002e0526101c000603000071070b03019029410b58400d4031411752040103041060f00d801404051021500c404418102204000b41c02c4c00030f540b00304814200c003030709000c807c10840b00c120400b4090842c9035405113669002a149080488610005035100d80d500003c144d0100034418140c8080c40c03483c3d04240b21210304070300900052141da03040644074145c0d82c119900660031151100d10178110742840d00c0d103d0034042d569980500c11301a152203a00e0003440f21040d00d1060340d0050380b00c0c107000d0300d65843e14010440b06411240c0150344a0508003c0b01c0340b0b061401e100c000e2048101e40143c20303010380c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 177310773 1250 177309523 177309527
    0x3150d030e0103060f0f0b1b011812030509100e070503030715051008060402060d0b090901050f0106030b15070c050a0e0106020607080421020f10020d05100803120601031b03090201 79
    0x300a074401001c50172100024800420304a07101c00548a00c410069110303800702c2c05058903060752150304020b079440d111705103082c00100b4400d40c22490207005000000030408004030219803048480c100c1c1f035000001c4602c0f4001c443c1d0400d0780740c850300c0002c031940c854840c80008c1c00c40c2d200805c12104a501c4004101c192a8640229603000b801d08000240541c40c250b6800e840b090001c0009208810000344e551954849502004100074098010070310740c07414a013240c2c001c2505480084140300180b00015a0a1185c01009480c002c0030f40000303030703290070300c10300800e1900904da04807000840448042001e07146e00706980020610132420030000c2d450110040d040000280081e02000307078503c00c100c0490b801d44440138101100c400406501703104000220704040500d260840180907429003d0000c060036005412010100c2e00b017007089441c1c00c214501c0303500003803003076000303540081c89004d03003194101d818144e00c11381c107040214000c84444030a1203242d074040900c4001c29540c0700c600056503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 177312023 1250 177310773 177310781
    0x2120c0a0203010b062a0a150c030b040501080709020d061215051b03040b0601020f031909080c01090608090a02030a0c140901030203060a090203030f070c15020106140603150d030e0103 81
    0x4000c5d21494034000c1d4a4a80c44d1101e001c460103a91181440b24889030803203400c00c4200c3e155504a064462040e0024000030f02030a24400d030b00000a05010214030a0b14051003041e0483d030341d80c001844054540308503140650001c3c0c08082d05181d50712400240741d500303144116800c42c07054074a04280d031035030394130407080301d201910018a48211001e00c1c0d00200b40c050480b0703041900303d1451441a47c0b1040100d10b4242002c8210b141800085414100130340462010f04d8049503603141d40c44920b03190b040042e40c07060400201c0740041c0003800d08010540c050982543c204404209980e20050b054012038680a2000001c17640401034007800c12200c804208160501079088900c5d245552442d0002075450102a011388003140ea2500d088046603010070850b22510034500c2c040d0740311100e504007252042594851220101c0302000f5082c0d2062061003400161032190300e400903c510340105000322500024102941c8400303034250700026990301300c601803c182c840c0e84c590101c5d6100c040014156 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 177313273 1250 177312023 177312041
    0x20405090405030a0212030c07020609041e020d0f0b0607060b030a050304030c14040203070f11010902090408030103020f0102163501060f0501020d0219170c06010509330102120c0a020301 82
    0x10031b505005024100b461001280d0b400c980490301c168039000c2c0000010700401d08111000d00040308419a00141c4000341c025202034680038004019600c2068007900076208500f6a85900c03003001c104410006c0c140d544400804036020b01281c40c01c503056a140351440d4070641003a038600554040070000011803403150307280702c00207940c00d500354101544050400780c2c40201000c1413000d9070a402c288030344c09502a02525400070040071082c00c281c14031540540c020300041e80911a103c6d00350b40c0070f5000042c40c540c001d01e942d6001c0d00c07080c5010440c02034080d00b0300c20072038044950640600c4c9280d2006440f450903100c000002016898040c0d2402c02c403c65901c0941035401400401d11280c5e00410086400148501007a1a01c002842c151015820301442d035440d9441c042041502400c002601c241618820754180398942c41d5103062500e4069000c404844180e400303800000e400110301d030400012a0b0600490340b281d4204440389045030029400032019a121803040b0080d441c0900559181d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 177314523 1250 177313273 177313303
    0x507180606030b18090c0a031103190b0103080a031b110f0c031f06080d0507030f0305150d02010c0602210c0a0207060c05030910080f1e061201020405090405030a02 72
    0x3c0039082c40480c445001890382e40408501c01d100140b100c1d58184a00580c8500c0209080c40c1302c0e486c0d02c0e2003801c80085145840c000e104580e14640825658000c2103c410380101940d20103a01e55500c10704070b980320400c640e04040e1100601e9001e90031a40784003d0f0b0501d0f5444045416130382d454082d04d00f031050b02d51007295600c072104c01e14032a00c0c00300301c80c00b02ea50100c001c0d540c0031861440000141850b81d11945640c8542d241702d003400396000001d0544a40729036030b0421000c0d42c003030f004c07000d65100f5515080ea03180d4420406285240c202c100782842e92041c1403007407201a894454030100e801080e078087c1540d40000c0500020750080018a91240f1040307000c0e82441c56200c2c0c02569410709000b48014132400313034002018840204141c64103000010250a884405050000c010307010a4a020340d0050815012983c16100c0c5441505c45402403030100d1880c2c0e0b1110104a00740d801c1c0380100e0010f55003048003003051340341d00121610450040c0300460703951504c4880240b4100002c080664 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 177315773 1250 177314523 177314531
    0x60905010f0506090a020717041d07090b040e04030210061401020c010215070804020a24030c0c0f0b060a03050f030711010206010812030601050409020c0115120201020c0402070c03050718060603 85
    0x619542c4104e64a50400030240e001a16000c861030b00130001407140040e022401c60105001500c0300505060300501107001030403034800c0e141d028007a64400b200d40600050f150381803206200f40d1450100e03135917015000c1d1044808200c0c00c94001001c403145504440000310060b401342c000d5507010060a002c03124281300034500c0312071120801c0e20981d4040e0a2104102100e07022405540d01d40f1040c50103800c000615015045080e00c1c8588812449180c600c003083c01c08040380d56082c080c04080300305c01d8001210610340700d13003580c561003a0134006000f554090911400400440c40c10820f515034090007000a43c3e0394540303402d049038a0410520840e04560204005000e020300104680507441916215151a82c84020040e9402c0c095a0003188009101244107440316105401c0b01051402400000030080d071189100e4070081d03030300b00c0041d0269020204901c00e90400d507005009803802400c0f00700000d526903403101e040003c164480780d190498204841440030481c401c4000034100b0b424104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 177317023 1250 177315773 177315781
    0xd060e060a06080f040221030d060506070f1203060b040602030702040518030703050307170a09020a150203220302190e0f01031112160b070c15021f02070609060905010f05 75
    0xf0400240100640d228080d282c01090031034a40c0008100000e003003400a960b86076458048031743c2c0340c120308894007800c0e04004001405043c110100c0f9095900042041078000e0a920740231a000403c50280301099521900014015010000390000e0004d69010350b64507285401044151030307001d03000100086d42c1801d000c00202c400411210312690508040b62030303030303101c1780c041d50300001007102e03030780000b5880c02009000002e030340c0300458507842102c08003811915580c41110310b1080d149100c0141c0d00030043d407401f02d607485911058901140c41800c150545950100d4514184090740d40314107020345400f4000c107041013640c03580c81204a00f500603150303d1512520348000203c210140581c50100540c0b4100d02c007404480c0841100b06594103800d0350310a1010502c0d0710681c000e5401c144001000b00d00d40e000c4981101034101c2a6008007240c5000c2d05184000280f41030620740d400c0c0d406c101c03200c0024002d001d00103030b9a01030640051000c0c0141003050945480d000003002d00c6180800b04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 177318273 1250 177317023 177317027
    0x309210301260102090a0308040501020f010b03030306280803090a0909020307120f0501060e0105010e030a020943030e06061305060402040504050f1512191104020d060e060a06 77
    0x19000314000c80d1100b41c480200442c4442c024482d103000507401200b0f420002c814030445030028000c68800303a0880c1c8190038003491003401c0301d01088595503d0380003003010a00358030300008203901d050304580c00c402e0408041390740030078044002e600403d2607810101d1402100d103040741c041e10040005200505c0054810b84c0000d80350440c1d80a4000c2c101c0340c0656250900c02d10302059510550300c88000c002d56920307440c0407000c45509109160010320541c89040842c100495402c0403541e02820000d803070b46554031040400c01900c1000281d0004140200324108450315450386a64091000a650b00d4002d2000400b43c40b010031482c41c250f80b084007402425106e60340301c0b0141701101007000403591141d10000380030341300300d0748250f030b005082400703211040d541c018001d40a4100351042e22004250481800100d842d403152038040d5401c003000c0030b4002420410710310b07041d0f48540450034042035a6070014049030824151100c205550709400d011420710b6003081d640121040301d608468501e00100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 177319523 1250 177318273 177318299
    0xb0f040b0403120209120109020a1a03063d0206070f1209031101110405090a1806020d06030611090118120615030b0c031e01060c080a02120309210301 66
    0x70040030801c00303826540c140555a810f0702c040c10401030412030640340110896020b446520b0041e4070461140a002a010071035040e192012010400c1c002e0466903128108410705c80e408401d8440310300321000e00103c240481c0d18842081c903450b55800052922501b00a1518074000d20510601083c440c1500322a900005049412b5180500200300d14009240455900c0006044001d4640c2071181e000140c074410400b50080d10011348201070301d907031000d00500030b840c07030140c6003070002100c07404090114a1a4008102e07900721190085001d580c0da54820301100c0c55581d03203000143e80424540309a6a0203215400d1010380400c42d4a0020b04085065507504000c41c00200050703a0b510007881603c02e05900040116046a1804402d2603c00c142144a92046528040e201c0030501020488000c40c02194160744031542c90b070455143d69980c01c1c002d0b81c0b04c2d1101c14250710403a1004007510008000551040d10b03010b002d002440e4110030000d051001318040f0200408081c001170000c40c80f0411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 177320773 1250 177319523 177319531
    0x2030903040f090c0e121609020a0e0307050d031b0203030f03011401031a10091707080d03022712100e0c0103050910051f030c051e0a051002010b0402070501090b0f040b 74
    0x1d010b1b0720041d4000c00c0030729000c4010b241b50b26100744003c000500c3c02150b0302030b1031000c020340c41d12081030201400309615180c8900038180d00645e0b0300c60744070200b48280a1800035244d400b107101e04989864001070b155400c05078100d02c01c0c5100000601c8100048180e2501ca00c000382010301a50003002c401100b4689a4600c00d070180c100c0a2541c856188680d140710000d01003039104520201030030410544840306402005814819215000d249174441d20031030f80c0303000b54264045070080313150b07101c00c4c0d1409a00788d00d20f9002044419103940c0781000c1c0a10264660601000602001103486050600e158091410706040c5080c080060085000ca1000719649100400003001c1e903e0200040c44000310583c00404005044408420803002003548419510100c91001c003008042c12010707070794075904841c030f60400c5020608001130700744491102c0503254140008102500344401003030480e0025603054030b05a441c2e503204001d100a184555421a48014503003d50345820346030180f00540140c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 177322023 1250 177320773 177320779
    0x6010e06040f020c060f07050c030d1107050303090607120204031110090f080a0c0905061f091203030605100201020f032a040305030a030606020304230f0402030903040f090c0e 77
    0x1550603540d56120034a0b2981c0c00508640380c84014805613940d44080ba440541025500c004c10704003802502541c0094130710000561400c0c035110307202c1018150380e03200d1400110040c00f410000540c00e00181d40b1942c03486004002c1da20b0181e0380280b103110800211072140f8410042800410711030070304400e4100040c1c60010610b143d0880485080059a101724020030740c44001003048840468405032990040020b102019204c0e202c2400700e40059486603844888034140410110074010f800c0c3c0b0481031806c0c4070b18865070741e9940d03c0f07820441400845c000b07952410140858508861181c2c501d000a1000710306012404600142e548400380ca042a40c80001d030321380c172011b201c0d00c86600015561061290b101d66491622a07aa50404074155010909009000c2440340c40002a6000c440b00100c450f8490741c2e54a5015200b2064400c11340d0304484a00c011071a2a1210b0004600a14001c001542d44501c0e243e003041c24440c65421030341c3c034241000c94418020b42d012409030b416840c21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 177323273 1250 177322023 177322049
    0x31b09090b0a0504020a1205070509010806130917040501030e06011406070809030a0303270c09150f0b09031c090e190f0b040b060c1c1b0b060109060309050601 70
    0x31000281e581d5809078005640517000040000b011540620100011750020b04180001d84407440b00313990300d000f6402003e000610542c00280ca6152103080305618000220707001031301444548500209444043d41a544401d001a0030041540d141c85107889480c0607101806180d410107411606213100a407c04e4440c00c404542d550074440c0c10403c490b4aa00010120780a15525240207005814946e402440010b00f010b00540e0303060440c1c0c011090154000c18110f40142415183d0b0001d014144803a41c08015610300480c0100103008850080c1c4105e44603551035031300460406140821041070f250016405040d241003080e000341c690002c0d1000305000d40e0707080d0b503100121400c40d40c1031403a4482090400310540c00301c061582c06014031030002c1d901403040d64414030030310911b841828600d42c200e07400303016500044000d20100c85001180c9180999a0001150b52680b107a03460f0441a075422012100340551076030040d40c1c59004024a040620000c3e065441e605d413600b40502c0384080c00516 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 177324523 1250 177323273 177323291
    0x10305100506010504080f060f060d15110702040e1e0708030301060c0807050a0605090c06070f0605071b050106090b0405060607060c020102090a0e0a0b01020a020307090c050702150a031b0909 84
    0x50020345d0b0161a031001103500c50040382400c541d807a0016a1000c014501001c04151a42440c1d04c1e11000b05400c421800d18000c48248807100402040f11003003503080c0207014000040c3c0d42c0e400b81c800c128015000501103085002d0701c240624115400c690903a0744100ea04202403c004000e8074112001c40c14003441403040d9040c1017000b407003500d00041c00c90141307005240402642e54402c0c4d020b450307860f0882c3d0841802e9410f006681c880c0d000084c1c000ba02c1d5061003000100b440c0c111640c802c00d186000c200c00c811500310260314602c0c0c404220340301d0351136506c05d010b50002d03881008030900c070840e0244658200740001c0358081c400c4540291040e03403107624004002c1d0003501100c00c00383d000b074941159555902e2400442a80a481d05100d9a0030280d2180866100040d07d4803a260003d0241c03580c5860248030030014144002c410041c0b00060003514003503655168608070368040882d5a5a5072000b8100060850300049070b00c00250146140700300403968060078030001e50760440e07000950707107107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 177325773 1250 177324523 177324527
    0xf0c0c110103060b0d051f0b090405040812011d1b0706020304030e10050406140403081b0c220506121b0d0206040906051509030607030c050903060906090706050301030510050601 78
    0x300d801884c41608001051540d41c030303080c0d220740d11403642085100c0300001e40b10350b540d401007214890040140c10a02003120f8601c4c0950100f60018400c3c021585440ba0865280d9481e420907801600d0b1003d000d001c1e00101c0501040f0280c0c0b080040c05420310123910100041c182e40203241c4060302c1c02d58007000003030030180540b0810500c00c1c0001c1000150140303c100080142d030103070007040d0004108600040314400c04000f50f50569a0112480f810103c00c950300b0324510303003602e640e000a84590317070742e0101c1e0f0384607648001d0001014000b168000c0041c250800d05035040a80a2402032090a40403025803030301040a02c03c2c0d4501500c4a040e03040b5110000f604400e10241c0a5844200021f00203403900895000c642213400c1a07840b9825618610303041c6013103008a108181e050b03007020303000880741e6119900110b81c4000741e0400b182811500d801080c035188040f6485962a840364062080014042002c070b00107180904e40740345190305650710543c40d4286e044d090310f0b01980b101c0119185078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 177327023 1250 177325773 177325781
    0x3040b0703020a35130314030412150c0f140c0f071d0105060301031a10090906060306061e0512030c0607021515060702010806060f040b04090f0c0c110103 68
    0x1034002e075418401d02000344a08000b10000910b00c085140d414204051000c81032045d20181d146042585510b80d141d42c8070440a440a890300c4038403808204004a151107171170120845181c001c15074150556880e0081d5003c0342da00e0148842032155804d4070480d8213600102001403480210b00c034684030301040709110700d441031194503842280941c0c400441c03404900c1c42c17406006030051000030b41903603076030090025502c42800081d00c41c0c0d074204111190801e020401c0c030b0700450151f0303800c3c0b00300387c0d200d41210880d625110b04035000d54483e8802c00c1403010a0280e400640303003110402030703000b4000409902040d480d10402d030203000500c1121902a00600503500c4c3d050300300c1c0c203903445441c110380025100c89400c214266004c0c0300c90003080040c0081c0c0c43c01000100040c4c05545400312507001510b07800d00080c2000d611030010814500c1100720440540700030180c0c1074500b61254107115026054580b101070605410f8902442e022516602c0b0340341014850b00070036040c0003100c0d95401200a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 177328273 1250 177327023 177327043
    0x306130c1508093003040c0b04090b0a05010e0a0512010b0603070206010611060105060703030e0a080a02030423090402090403020129011101050c03010b0c07051017010b0a0203040b070302 82
    0x1010214440001c09904140c505100c1e0300600155928071a040c00f520200e103402e03181c19498026600e943e60800c000c10001150007038001c1d8583c001d460341c0c82d003a4000540c8140c125041d10b41d00c1e03220059081c01d180c80e43c0c20140c502401c00320b59041c150004907069160760b103e010301c90760306900504403560080d480448196000360040da901d20b0604d5019607204001c0c4070316030005440325440036000f540032075001c0c165900104058500811070b2005c502910302c0300250112809068002c00c0040e046400038920303403003590040c540340c0380f911010300380c42000c0384205205050b07205030000b82c2e80e481d8500560700030350480341003c864485040c00c900514111003403c58284020b0b075548200210b42d40c9100c100d82c002da9810812082c9500181e0a03140b0984088020031801c0c001072045d050084058601c680307004040b104030b45d40d82d80c0096480c0e1100c0e51058081101440585896130f00b5407855405000d03040000b078500240b600c4001c2d1b4922440c0300303070041048041041c0080510a008844007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 177329523 1250 177328273 177328289
    0x3070e0f040c0e030d030603150b01030e06040302160501020109050a031430070c050a0209150a09061e0608040206030403090e09010c030506040905280b0f0402030c01030b0306130c 79
    0x4400001580501148a090800d51280c45005171a803010391190040006513a48044138004006007070840c48050200b04800e181459200c190605242c03404100f980c0c4076030f009038001c01840d90050034110640c10103820407411a4102503084000c544002516002158549044001000b0043c807615050040d04c4094900141080000341c10000105441c503a900d07481032044003a03169014282c581045121008009030003480c80316025142c04040242d0040600f00350381c013070322003082c00642c14480d0794110410141e6070300710a0080001d03084072012044003500f615100c1c1410400058614403004000910603000003001404051042210400401448880000505108403103074041d0000d42c0c0564006403a01c00000c01c0b61401e03004a0b8078041d00706002d8144842c1e804040f1804c0111031400c2d400c20300280080400103407150807100d20504031020400d480b42018030400d4103024942034080d04050800121310500e54010800d0780c2c000b034590b1401140c01c02a131400201900391944a449 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 177330773 1250 177329523 177329531
    0x2070b07060b0d0303060f091413020301020c100218060723120714062404020c010209030a05150108150c0711031606080a0203041e03090f030c0501031b0503070e0f04 73
    0x810141c05030401c5090307d04401d024107109895000d25001c441c07560b4003211000f4000b07804900b22010b0010001150350020b00050716100448280501d410000840c90740c1c1c445d0b000030f012500d00f800021000703440608440302d510f040581d40b150050004102080f01d20003011680c980c000c0c02c0100400c591801402c407003140c641000342044003000d80881e4810500c1d01649001800f61800d0f12000d02c058030802440200c10840c20050200a4100c920083c1c143c0d9070030002c00010f50790400c58003003010320644c01450560b0011100303c20480041e4488100c0c0c0e4020f0013204185009411240e501451601030540c8600030741c200030a6003090660350b16010300030f01c00a06490410b80165034155080f9454018680c1c0f0b1b9000910200e12044030f000c2c00e40d40f195901309044149400081700c1c454007d24081c00c0b09a2501101c0c807044140e41d000f01d41d0003a4641c410482560540610321054001c2400318403080051f00d00070f885480020000401c02c076048526901c0c0f80d4440300e0300c820540340038000304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 177332023 1250 177330773 177330799
    0xb030c0a093501050601050409110f0c0a140a02091501021005010e010f0816030807021f0201090311061302011209050114070306120c03060f0e0102190e010f02070b07060b 75
    0x41e0304000d20204081519207a4041070000b2001401120302070181030f910a80780c64982881c4100604102100b251034090800c2001c0c07100316940094503079501d0b14000781041400c40d00d495a00d01d4403921144540760400165103000d0798600000d030b580a4012503003002001035400040f42802d1080c0141c036042c1d46408004541c4604080400b8103940e4490124940c0303a072030341c08081c0d562211202c041e091481c84c4400780300040440016218251024041010030b1261069006051548020704c0e070050390340b20005020315170711002c1040030841e1400900302a05000b2041d00340d03a224144042d0611130030380700015010269a125054090b00000200041440010810004241a039048000904101000c42d000c1c1c4644006100c545c4c0c00320402c10703a030346150341d248064044806010300541d40c0d5243c08009420a0004006c03218441801c00184d011401015001004008901d070421602400c0703c1c48983e00010780c4803d45110102c0c1036103c000a16124000c0e083d0380001d07503000020071540d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 177333273 1250 177332023 177332069
    0x70809030118140336060403081306050c0d0e0310020a0804110111061306020403240f0501050303070204050c07020a080d0908010524030a120c0b010506040b030c0a09 73
    0xe04501e201d44011800030066400c20fa659002d4281d00d5911702100c15903a50308600a1031140c42d220f10800300000d40c4250050000382c07550000c0d8404d50720010300082c4848070002c0030400102401d11030400a042980018640e6540c0c0c4201850b03000b4030090301991401b950302000441c0400c00036207000d540e1a17010400050400d04290b038201e038551408946540c9540c0160300c403e11414400b8010701315603550400d82210340c81050803d41d40254200404008910300e0b5042d45200f0303819140c01401442c1501c0404115910800b0301c0d0a040e03d0240107000079136000c81101c0c0c1050b0103d401240315180c0e034035003400c64031506200030b500c48100400003808010208407540c951103142c603505550750356045024240e4004541c014641e03051103000c581020629000c40f018090050111801400a9500c2410340c4140107101c0c00814a0b407550a001c0080554960f409820180c0d8000e0070680f40030f10300025804090669128540045403480301580314146200003003c0380c41d4800031038500e808075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 177334523 1250 177333273 177333311
    0x605100602061501020a0b18060a0501360b131503030f08100e07120608010506030f071a0915040b070b0108010902010906051312050c0f09040312020708090301 70
    0x210005030192030001055110f100c2c3e9066050310060b0050042d0841981d1120140c1d01d00908400c0b07030400c500c1980e0f40c403140800c07116108142c010b00018a40d410701c0b06c130311182c05050250210050106121004104040b1182916018034031000f1422007000303400510760f6241ca0140c20780c007501d07080d503445044001301c2c101c074102c0e4042d4552aa0501c4800800c4406a00c200c498420a140310742c0c04010719140c41800c00d5108020349030102d040c4400a050310300381c4e041a0b10035251a034641060222516050142502000100300200b180c82e01e4064060f80d00c1c010310803414114440400d1208540d200c0504903202c2c046820802542c540c4c5407000380c1c4d85600401025a1142c3e4032400104e500784051145006042c2c0517181d400d03000e80f52600031200c0b603110703401d420482d106d0350f10001400203105030b00d450164861000f41180008080601c04091450240d140c49048140c0a0102233038102c1c26000140030f45140c05a9207211030704103a131183c880c9045054156203410700c1089203031507400b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177335773 1250 177334523 177334529
    0x60e010c0533010b16020609090f01031b0303020601170c100903150204051e040f110702041103010b1605070b0f0c0606010f050d0b03011b1106090313050108060d060510 74
    0x1c2d641e40310801d41c40b45480d40030742401201900001004007407280d441c0001e40e0350b17549100030001e0745816030040101c4e4400e0b005403503d1000004000041c000c126141042400e00141043d920f03440c03a2440c2c400941e5802e0600c41c10860314510403060741c0b0349006000c403c80210000d0000c42412400840040007500d16110a59281c800703800c9807140f5088a000304d50807107400404841c0d110700312000c0c241c2603840386480b40747e002e036030741c1d4110b02188060700603c46000304d50b41500e2f4aa0910340188826288002c40050b1a0b200400045c841107001c44180e403810401462100604a000d240c0f441c6445025040301100c010089040d0f031110303000b0002000301d52010001c1c4c55003902d07502c0065811500e50465007021504c18064100300e0940e80d440f000444d00004d0010a0032810081440d80c450414001c1e8400500401d520400c200b10401001e600701542200951030616220346901229025000d03050410100b030012542070340d1080078800186070005010021407c2c140300303484078100944 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 177337023 1250 177335773 177335833
    0x80304170c0a060c12110106350706050c0102040f09050402040b01030902060301050621130210080708060d03180915091119110a15060806060307060e010c05 69
    0x140d001a50381005800001290f031262982c00192100c0c1c0d541001c01000421242d04003d0000441c224459090040c90002c10111a0001e241c0e00407844481c0e80b04c05c148150390300c8080022442c142864002244001c9400310310300349440342d040605070b40c06031243d0b034440c00d0b10003180708012a058486034441e40c081c80c800c48040000340c50700780056058139080c52029500103414001000300c1d0414100820748240c903203442d0200108540210400c180c82a07618003440e00090750701e00c0450401d03130b0b45034510b2410b80c20840c5942c034084600a00c40207000b00654010204092080c0416005070300718140c0c15061010700d50425140c0000c880104070b058681c45c101d5803814030000341654030380700300c5902c400d034800034502d80308001c01e0b44880511948820f10410000078902110038006006649001e8030503000342d54044020303143e000a441258015040300e130404400e100c0c4541c0d0004d454004c81d0740c2811b0501060001c0801603d56070040c100242c514080c1081050203000c1a9100d20402e40b411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 177338129 1106 177337023 177337033
    0x71a19142d0a06050405010b0f0d1802030a050c1f05090609030a05060c0408010c090627170307120c0201090306020304050a08181201052e08030417 65
    0x8982d4001816990241131129152601881c0e004002110116040014200c5444114440d0192a0380100c0c0c0c1c80d9404103010500c1d28041000780d80003801e40c0d0358580e0900f4184e807035040c1c1004942c402c25441010f4000c440046000b104001b007559100b1b0b0510f9a03a0090000c0e552020019903414403075003403010001a01006072a200303c06c501c5401e603d482c5044185802e54a11007445c0b424843d03041001e0000540c040d041d01168100c101000d00c08400c80280c02494044070740203e41401c0001d4044010b20000200400d0031921642036000c00c0d00c0d02c0f00c4115080708480000038001070300740800700003140c40c0350091078010b40182d050360200081e42d51117460b140d000c21041e80416100e403409955600d0941d100344410940e4400900079450121321540007400c2108454a105141c040211616410b0300d003044040c181e5901265922501c0d843c030300d00c0c501d41007a4050480e100d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 177158273 177338129 := by
  have h0 := BRFrame.cov_init 177158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 177158273 ≤ n) (h2 : n < 177338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
